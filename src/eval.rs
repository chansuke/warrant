//! M0 reference interpreter.
//!
//! Contracts (`:requires` / `:ensures`) are checked at run time here; in M1 they
//! become SMT proof obligations and the runtime checks can be erased.
//! Effects (`:effects [...]`) are checked dynamically and transitively: a
//! function that declares `[]` may not reach `print` (effect `io`) through any
//! callee or closure. Functions with no `:effects` clause are unchecked in M0.
//! Integer arithmetic is checked: overflow is an error, never a wrap.

use crate::ast::{Budget, Module};
use crate::builtin::Builtin;
use crate::profile::Profiler;
use crate::sexp::{flat, quote_str, Sexp};
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Instant;

const MAX_DEPTH: usize = 200_000;

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Str(Rc<str>),
    Vec(Rc<Vec<Value>>),
    Closure(Rc<Closure>),
    Func(Rc<FnDef>),
    Builtin(Builtin),
}

pub struct Closure {
    params: Vec<String>,
    body: Rc<Vec<Sexp>>,
    env: Env,
}

#[derive(Clone, Default)]
pub struct Env(Option<Rc<Frame>>);

pub struct Frame {
    name: String,
    val: Value,
    next: Env,
}

impl Env {
    fn lookup(&self, n: &str) -> Option<Value> {
        let mut cur = &self.0;
        while let Some(f) = cur {
            if f.name == n {
                return Some(f.val.clone());
            }
            cur = &f.next.0;
        }
        None
    }
    fn bind(&self, name: String, val: Value) -> Env {
        Env(Some(Rc::new(Frame { name, val, next: self.clone() })))
    }
}

pub struct FnDef {
    pub name: String,
    pub params: Vec<String>,
    pub requires: Vec<Sexp>,
    pub ensures: Vec<Sexp>,
    /// `None` = no clause (unchecked in M0); `Some([])` = pure.
    pub effects: Option<Vec<String>>,
    pub budget: Option<Budget>,
    pub body: Vec<Sexp>,
}

#[derive(Debug)]
pub struct RtError {
    pub kind: &'static str,
    pub msg: String,
    pub trace: Vec<String>,
}

impl RtError {
    pub fn new(kind: &'static str, msg: impl Into<String>) -> Self {
        RtError { kind, msg: msg.into(), trace: Vec::new() }
    }
    pub fn to_sexp(&self) -> String {
        let tr = if self.trace.is_empty() {
            String::new()
        } else {
            format!(" :trace ({})", self.trace.join(" "))
        };
        format!("(error :kind {} :msg {}{})", self.kind, quote_str(&self.msg), tr)
    }
}

type R<T> = Result<T, RtError>;

pub struct Program {
    pub fns: HashMap<String, Rc<FnDef>>,
    pub order: Vec<String>,
}

/// `[a : T b : U c]` -> `["a", "b", "c"]`. Types are parsed but not checked in M0.
pub fn parse_params(v: &[Sexp]) -> R<Vec<String>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < v.len() {
        match &v[i] {
            Sexp::Sym(s) if s != ":" => {
                out.push(s.clone());
                i += 1;
                if v.get(i) == Some(&Sexp::Sym(":".into())) {
                    if v.get(i + 1).is_none() {
                        return Err(RtError::new("syntax", format!("parameter `{}` has `:` but no type", s)));
                    }
                    i += 2;
                }
            }
            other => return Err(RtError::new("syntax", format!("bad parameter `{}`", flat(other)))),
        }
    }
    Ok(out)
}

impl Program {
    pub fn new(m: &Module) -> Program {
        let src = |cs: &[crate::ast::Clause]| cs.iter().map(|c| c.src.clone()).collect();
        let fns = m
            .fns
            .iter()
            .map(|d| {
                let def = FnDef {
                    name: d.name.clone(),
                    params: d.params.iter().map(|p| p.name.clone()).collect(),
                    requires: src(&d.spec.requires),
                    ensures: src(&d.spec.ensures),
                    effects: d.spec.effects.as_ref().map(|es| es.iter().cloned().collect()),
                    budget: d.spec.budget.clone(),
                    body: d.body_src.clone(),
                };
                (d.name.clone(), Rc::new(def))
            })
            .collect();
        Program { fns, order: m.fns.iter().map(|d| d.name.clone()).collect() }
    }
}

pub fn type_name(v: &Value) -> &'static str {
    match v {
        Value::Int(_) => "i64",
        Value::Bool(_) => "bool",
        Value::Str(_) => "str",
        Value::Vec(_) => "vec",
        Value::Closure(_) | Value::Func(_) | Value::Builtin(_) => "fn",
    }
}

pub fn show(v: &Value) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => quote_str(s),
        Value::Vec(xs) => format!("[{}]", xs.iter().map(show).collect::<Vec<_>>().join(" ")),
        Value::Closure(_) => "#<fn>".into(),
        Value::Func(d) => format!("#<fn {}>", d.name),
        Value::Builtin(b) => format!("#<builtin {}>", b.name()),
    }
}

fn values_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Vec(x), Value::Vec(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| values_eq(p, q)),
        _ => false,
    }
}

fn int(v: &Value, op: &str) -> R<i64> {
    match v {
        Value::Int(n) => Ok(*n),
        o => Err(RtError::new("type", format!("({} ...) expects i64, got {}", op, type_name(o)))),
    }
}

fn vecv(v: &Value, op: &str) -> R<Rc<Vec<Value>>> {
    match v {
        Value::Vec(x) => Ok(x.clone()),
        o => Err(RtError::new("type", format!("({} ...) expects vec, got {}", op, type_name(o)))),
    }
}

fn arity(op: &str, args: &[Value], n: usize) -> R<()> {
    if args.len() != n {
        return Err(RtError::new("arity", format!("{} expects {} args, got {}", op, n, args.len())));
    }
    Ok(())
}

pub struct Interp<'p> {
    prog: &'p Program,
    pub prof: Profiler,
    pub contracts: bool,
    effect_stack: Vec<Rc<FnDef>>,
    depth: usize,
}

impl<'p> Interp<'p> {
    pub fn new(prog: &'p Program, contracts: bool, profile: bool) -> Self {
        Interp { prog, prof: Profiler::new(profile), contracts, effect_stack: Vec::new(), depth: 0 }
    }

    pub fn call_main(&mut self) -> R<Value> {
        let Some(m) = self.prog.fns.get("main") else {
            return Err(RtError::new("load", "no (defn main [] ...) found"));
        };
        self.call_fn(m.clone(), Vec::new())
    }

    fn lookup(&self, s: &str, env: &Env) -> R<Value> {
        if let Some(v) = env.lookup(s) {
            return Ok(v);
        }
        if let Some(f) = self.prog.fns.get(s) {
            return Ok(Value::Func(f.clone()));
        }
        if let Some(b) = Builtin::from_name(s) {
            return Ok(Value::Builtin(b));
        }
        Err(RtError::new("unbound", format!("unbound symbol `{}`", s)))
    }

    pub fn eval(&mut self, e: &Sexp, env: &Env) -> R<Value> {
        match e {
            Sexp::Int(n) => Ok(Value::Int(*n)),
            Sexp::Bool(b) => Ok(Value::Bool(*b)),
            Sexp::Str(s) => Ok(Value::Str(s.as_str().into())),
            Sexp::Kw(k) => Err(RtError::new("syntax", format!(":{} is not an expression", k))),
            Sexp::Sym(s) => self.lookup(s, env),
            Sexp::Vector(items) => {
                let mut v = Vec::with_capacity(items.len());
                for x in items {
                    v.push(self.eval(x, env)?);
                }
                self.prof.vec_alloc(v.len());
                Ok(Value::Vec(Rc::new(v)))
            }
            Sexp::List(items) => {
                let Some(head) = items.first() else {
                    return Err(RtError::new("syntax", "() is not an expression"));
                };
                if let Sexp::Sym(h) = head {
                    match h.as_str() {
                        "if" => {
                            if items.len() != 4 {
                                return Err(RtError::new("syntax", "(if cond then else)"));
                            }
                            return match self.eval(&items[1], env)? {
                                Value::Bool(true) => self.eval(&items[2], env),
                                Value::Bool(false) => self.eval(&items[3], env),
                                o => Err(RtError::new("type", format!("if condition must be bool, got {}", type_name(&o)))),
                            };
                        }
                        "let" => {
                            let Some(Sexp::Vector(bs)) = items.get(1) else {
                                return Err(RtError::new("syntax", "(let [name expr ...] body ...)"));
                            };
                            if bs.len() % 2 != 0 {
                                return Err(RtError::new("syntax", "let bindings must come in pairs"));
                            }
                            let mut env2 = env.clone();
                            for pair in bs.chunks(2) {
                                let Sexp::Sym(n) = &pair[0] else {
                                    return Err(RtError::new("syntax", "let binding name must be a symbol"));
                                };
                                let v = self.eval(&pair[1], &env2)?;
                                env2 = env2.bind(n.clone(), v);
                            }
                            return self.eval_seq(&items[2..], &env2);
                        }
                        "fn" => {
                            let Some(Sexp::Vector(ps)) = items.get(1) else {
                                return Err(RtError::new("syntax", "(fn [params] body ...)"));
                            };
                            if items.len() < 3 {
                                return Err(RtError::new("syntax", "fn has no body"));
                            }
                            return Ok(Value::Closure(Rc::new(Closure {
                                params: parse_params(ps)?,
                                body: Rc::new(items[2..].to_vec()),
                                env: env.clone(),
                            })));
                        }
                        "do" => return self.eval_seq(&items[1..], env),
                        "and" | "or" => {
                            let want = h == "or";
                            for x in &items[1..] {
                                match self.eval(x, env)? {
                                    Value::Bool(b) if b == want => return Ok(Value::Bool(want)),
                                    Value::Bool(_) => {}
                                    o => return Err(RtError::new("type", format!("{} expects bool, got {}", h, type_name(&o)))),
                                }
                            }
                            return Ok(Value::Bool(!want));
                        }
                        "defn" => return Err(RtError::new("syntax", "defn is only allowed at top level")),
                        _ => {}
                    }
                }
                let f = self.eval(head, env)?;
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(self.eval(a, env)?);
                }
                self.apply(&f, args)
            }
        }
    }

    fn eval_seq(&mut self, es: &[Sexp], env: &Env) -> R<Value> {
        let mut last = None;
        for e in es {
            last = Some(self.eval(e, env)?);
        }
        last.ok_or_else(|| RtError::new("syntax", "empty body"))
    }

    pub fn apply(&mut self, f: &Value, args: Vec<Value>) -> R<Value> {
        match f {
            Value::Func(def) => self.call_fn(def.clone(), args),
            Value::Closure(c) => {
                if c.params.len() != args.len() {
                    return Err(RtError::new("arity", format!("fn expects {} args, got {}", c.params.len(), args.len())));
                }
                self.prof.closure_calls += 1;
                let mut env = c.env.clone();
                for (p, a) in c.params.iter().zip(args) {
                    env = env.bind(p.clone(), a);
                }
                let body = c.body.clone();
                self.eval_seq(&body, &env)
            }
            Value::Builtin(b) => self.builtin(*b, args),
            o => Err(RtError::new("type", format!("cannot call a value of type {}", type_name(o)))),
        }
    }

    fn call_fn(&mut self, def: Rc<FnDef>, args: Vec<Value>) -> R<Value> {
        if args.len() != def.params.len() {
            return Err(RtError::new(
                "arity",
                format!("{} expects {} args, got {}", def.name, def.params.len(), args.len()),
            ));
        }
        let mut env = Env::default();
        for (p, a) in def.params.iter().zip(args) {
            env = env.bind(p.clone(), a);
        }
        if self.depth >= MAX_DEPTH {
            return Err(RtError::new("stack", format!("call depth exceeded {}", MAX_DEPTH)));
        }
        self.depth += 1;
        self.prof.enter(&def.name, self.depth);
        let t0 = self.prof.enabled.then(Instant::now);
        self.effect_stack.push(def.clone());
        let res = self.call_body(&def, &env);
        self.effect_stack.pop();
        self.depth -= 1;
        if let Some(t) = t0 {
            self.prof.exit(&def.name, t.elapsed().as_nanos());
        }
        res.map_err(|mut e| {
            if e.trace.len() < 16 {
                e.trace.push(def.name.clone());
            }
            e
        })
    }

    fn call_body(&mut self, def: &FnDef, env: &Env) -> R<Value> {
        if self.contracts {
            for r in &def.requires {
                self.check_contract(def, "requires", r, env)?;
            }
        }
        let v = self.eval_seq(&def.body, env)?;
        if self.contracts && !def.ensures.is_empty() {
            let env2 = env.bind("result".into(), v.clone());
            for en in &def.ensures {
                self.check_contract(def, "ensures", en, &env2)?;
            }
        }
        Ok(v)
    }

    fn check_contract(&mut self, def: &FnDef, which: &str, e: &Sexp, env: &Env) -> R<()> {
        let t0 = self.prof.enabled.then(Instant::now);
        self.prof.contract_checks += 1;
        let r = self.eval(e, env);
        if let Some(t) = t0 {
            self.prof.contract_ns += t.elapsed().as_nanos();
        }
        match r? {
            Value::Bool(true) => Ok(()),
            Value::Bool(false) => Err(RtError::new("contract", format!("{} failed in {}: {}", which, def.name, flat(e)))),
            o => Err(RtError::new("type", format!("contract must be bool, got {}", type_name(&o)))),
        }
    }

    fn check_effect(&self, eff: &str, op: &str) -> R<()> {
        for d in self.effect_stack.iter().rev() {
            if let Some(es) = &d.effects {
                if !es.iter().any(|e| e == eff) {
                    return Err(RtError::new(
                        "effect",
                        format!("`{}` performs effect {}, but `{}` declares (:effects [{}])", op, eff, d.name, es.join(" ")),
                    ));
                }
            }
        }
        Ok(())
    }

    fn builtin(&mut self, b: Builtin, args: Vec<Value>) -> R<Value> {
        use Builtin as B;
        self.prof.builtin_calls += 1;
        let name = b.name();
        let ovf = || RtError::new("overflow", format!("i64 overflow in ({} ...)", name));
        match b {
            B::Add | B::Mul => {
                let mut acc: i64 = if b == B::Add { 0 } else { 1 };
                for a in &args {
                    let x = int(a, name)?;
                    acc = if b == B::Add { acc.checked_add(x) } else { acc.checked_mul(x) }.ok_or_else(ovf)?;
                }
                Ok(Value::Int(acc))
            }
            B::Sub => {
                let Some(first) = args.first() else {
                    return Err(RtError::new("arity", "- expects at least 1 arg"));
                };
                let mut acc = int(first, name)?;
                if args.len() == 1 {
                    return acc.checked_neg().map(Value::Int).ok_or_else(ovf);
                }
                for a in &args[1..] {
                    acc = acc.checked_sub(int(a, name)?).ok_or_else(ovf)?;
                }
                Ok(Value::Int(acc))
            }
            B::Div | B::Mod => {
                arity(name, &args, 2)?;
                let (x, y) = (int(&args[0], name)?, int(&args[1], name)?);
                if y == 0 {
                    return Err(RtError::new("div-zero", format!("({} {} 0)", name, x)));
                }
                if b == B::Div { x.checked_div(y) } else { x.checked_rem_euclid(y) }
                    .map(Value::Int)
                    .ok_or_else(ovf)
            }
            B::Eq => {
                arity(name, &args, 2)?;
                Ok(Value::Bool(values_eq(&args[0], &args[1])))
            }
            B::Lt | B::Le | B::Gt | B::Ge => {
                arity(name, &args, 2)?;
                let (x, y) = (int(&args[0], name)?, int(&args[1], name)?);
                Ok(Value::Bool(match b {
                    B::Lt => x < y,
                    B::Le => x <= y,
                    B::Gt => x > y,
                    _ => x >= y,
                }))
            }
            B::Not => {
                arity(name, &args, 1)?;
                match &args[0] {
                    Value::Bool(x) => Ok(Value::Bool(!x)),
                    o => Err(RtError::new("type", format!("not expects bool, got {}", type_name(o)))),
                }
            }
            B::Len => {
                arity(name, &args, 1)?;
                Ok(Value::Int(vecv(&args[0], name)?.len() as i64))
            }
            B::IsEmpty => {
                arity(name, &args, 1)?;
                Ok(Value::Bool(vecv(&args[0], name)?.is_empty()))
            }
            B::Get => {
                arity(name, &args, 2)?;
                let (v, i) = (vecv(&args[0], name)?, int(&args[1], name)?);
                if i < 0 || i as usize >= v.len() {
                    return Err(RtError::new("bounds", format!("(get v {}) on vec of len {}", i, v.len())));
                }
                Ok(v[i as usize].clone())
            }
            B::Slice => {
                arity(name, &args, 3)?;
                let v = vecv(&args[0], name)?;
                let (lo, hi) = (int(&args[1], name)?, int(&args[2], name)?);
                if lo < 0 || hi < lo || hi as usize > v.len() {
                    return Err(RtError::new("bounds", format!("(slice v {} {}) on vec of len {}", lo, hi, v.len())));
                }
                let out = v[lo as usize..hi as usize].to_vec();
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::Rest => {
                arity(name, &args, 1)?;
                let v = vecv(&args[0], name)?;
                if v.is_empty() {
                    return Err(RtError::new("bounds", "(rest []) on empty vec"));
                }
                let out = v[1..].to_vec();
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::Concat => {
                arity(name, &args, 2)?;
                let (xs, ys) = (vecv(&args[0], name)?, vecv(&args[1], name)?);
                let mut out = Vec::with_capacity(xs.len() + ys.len());
                out.extend(xs.iter().cloned());
                out.extend(ys.iter().cloned());
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::Cons => {
                arity(name, &args, 2)?;
                let v = vecv(&args[1], name)?;
                let mut out = Vec::with_capacity(v.len() + 1);
                out.push(args[0].clone());
                out.extend(v.iter().cloned());
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::Range => {
                arity(name, &args, 1)?;
                let n = int(&args[0], name)?;
                if n < 0 {
                    return Err(RtError::new("bounds", format!("(range {}) needs n >= 0", n)));
                }
                let out: Vec<Value> = (0..n).map(Value::Int).collect();
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::Vec => {
                self.prof.vec_alloc(args.len());
                Ok(Value::Vec(Rc::new(args)))
            }
            B::Map | B::Filter => {
                arity(name, &args, 2)?;
                let v = vecv(&args[1], name)?;
                let f = &args[0];
                let mut out = Vec::with_capacity(v.len());
                for x in v.iter() {
                    let r = self.apply(f, vec![x.clone()])?;
                    if b == B::Map {
                        out.push(r);
                    } else {
                        match r {
                            Value::Bool(true) => out.push(x.clone()),
                            Value::Bool(false) => {}
                            o => return Err(RtError::new("type", format!("filter predicate must return bool, got {}", type_name(&o)))),
                        }
                    }
                }
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Rc::new(out)))
            }
            B::All => {
                arity(name, &args, 2)?;
                let v = vecv(&args[1], name)?;
                for x in v.iter() {
                    match self.apply(&args[0], vec![x.clone()])? {
                        Value::Bool(true) => {}
                        Value::Bool(false) => return Ok(Value::Bool(false)),
                        o => return Err(RtError::new("type", format!("all? predicate must return bool, got {}", type_name(&o)))),
                    }
                }
                Ok(Value::Bool(true))
            }
            B::Fold => {
                arity(name, &args, 3)?;
                let v = vecv(&args[2], name)?;
                let mut acc = args[1].clone();
                for x in v.iter() {
                    acc = self.apply(&args[0], vec![acc, x.clone()])?;
                }
                Ok(acc)
            }
            B::IsSorted => {
                arity(name, &args, 1)?;
                let v = vecv(&args[0], name)?;
                let mut prev: Option<i64> = None;
                for x in v.iter() {
                    let n = int(x, name)?;
                    if prev.is_some_and(|p| p > n) {
                        return Ok(Value::Bool(false));
                    }
                    prev = Some(n);
                }
                Ok(Value::Bool(true))
            }
            B::IsPerm => {
                arity(name, &args, 2)?;
                let to_ints = |v: &Value| -> R<Vec<i64>> {
                    let mut out = vecv(v, name)?.iter().map(|x| int(x, name)).collect::<R<Vec<i64>>>()?;
                    out.sort_unstable();
                    Ok(out)
                };
                Ok(Value::Bool(to_ints(&args[0])? == to_ints(&args[1])?))
            }
            B::Print => {
                self.check_effect("io", "print")?;
                let s: Vec<String> = args
                    .iter()
                    .map(|a| match a {
                        Value::Str(s) => s.to_string(),
                        o => show(o),
                    })
                    .collect();
                println!("{}", s.join(" "));
                Ok(Value::Bool(true))
            }
        }
    }
}

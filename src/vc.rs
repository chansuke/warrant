//! Verification conditions (M1-4). Each function body is executed
//! symbolically; every property it must satisfy at some point becomes one
//! `Obligation` carrying a self-contained SMT-LIB script.
//!
//! Verification is modular: a call checks the callee's `:requires` and
//! assumes its `:ensures`, recursive calls included, so results are partial
//! correctness (termination is assumed). `perm?` compares occurrence counts
//! (`cnt-VI`), defined for each vector operation the first time a `perm?`
//! needs it. A construct with no encoding (nested vectors) becomes a fresh
//! unconstrained constant; assuming something about it constrains nothing
//! else, so it is sound.

use std::collections::HashMap;

use crate::ast::{Expr, ExprId, ExprKind, FnDecl, FnIdx, LambdaParam, Module};
use crate::builtin::Builtin;
use crate::sexp::Pos;
use crate::smt::{int_lit, quote_sym, sort, str_lit, vec_sort, COUNTS, I64_MIN, MAX_LEN, PRELUDE};
use crate::types::{Ty, TypeInfo};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VcKind {
    Requires { callee: String, index: usize },
    Ensures { index: usize },
    Overflow,
    DivZero,
    Bounds,
}

impl VcKind {
    pub fn name(&self) -> &'static str {
        match self {
            VcKind::Requires { .. } => "requires",
            VcKind::Ensures { .. } => "ensures",
            VcKind::Overflow => "overflow",
            VcKind::DivZero => "div-zero",
            VcKind::Bounds => "bounds",
        }
    }

    pub fn to_sexp(&self) -> String {
        match self {
            VcKind::Requires { callee, index } => format!("requires :callee {} :clause {}", callee, index),
            VcKind::Ensures { index } => format!("ensures :clause {}", index),
            VcKind::Overflow => "overflow".into(),
            VcKind::DivZero => "div-zero".into(),
            VcKind::Bounds => "bounds".into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Goal {
    /// Asserts everything known plus the negated goal; `unsat` means proved.
    Script(String),
    Unsupported(String),
}

/// Which part of the function being verified an obligation came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    Body,
    Requires(usize),
    Ensures(usize),
}

/// Where an obligation is attached: the call or clause expression.
#[derive(Clone, Copy)]
struct Origin {
    pos: Pos,
    expr: ExprId,
}

impl Origin {
    fn of(e: &Expr) -> Origin {
        Origin { pos: e.at, expr: e.id }
    }
}

#[derive(Clone, Debug)]
pub struct Obligation {
    pub fn_name: String,
    pub kind: VcKind,
    pub at: Pos,
    pub expr: ExprId,
    pub site: Site,
    pub goal: Goal,
    /// SMT constants read back as a counterexample: the function's parameters.
    pub inputs: Vec<(String, Ty)>,
}

impl Obligation {
    /// `(vc :fn F :kind K :at (line L col C)` without the closing paren, so
    /// callers can append the outcome.
    pub fn head_sexp(&self) -> String {
        format!("(vc :fn {} :kind {} :at (line {} col {})", self.fn_name, self.kind.to_sexp(), self.at.line, self.at.col)
    }
}

pub fn generate(m: &Module, ty: &TypeInfo) -> Vec<Obligation> {
    let mut out = Vec::new();
    for d in &m.fns {
        let mut x = Exec {
            m,
            ty,
            fn_name: d.name.clone(),
            decls: Vec::new(),
            facts: Vec::new(),
            fresh: 0,
            binders: 0,
            out: Vec::new(),
            emit: true,
            inputs: Vec::new(),
            site: Site::Body,
            clause_depth: 0,
            vec_ops: HashMap::new(),
            counted: HashMap::new(),
            defs: Vec::new(),
            perms: Vec::new(),
        };
        x.function(d);
        out.append(&mut x.out);
    }
    out
}

#[derive(Clone)]
enum V<'a> {
    /// An SMT term whose sort is `smt::sort` of the expression's type.
    T(String),
    F(FnV<'a>),
    /// A value with no SMT encoding.
    Opaque,
}

#[derive(Clone)]
enum FnV<'a> {
    Lambda(&'a [LambdaParam], &'a [Expr], Env<'a>),
    Global(FnIdx),
    Builtin(Builtin),
    /// A function parameter: nothing is known about it but its type.
    Unknown,
}

type Env<'a> = Vec<(String, V<'a>)>;

/// How an i64 vector term was built, so `perm?` can define its occurrence
/// counts from its operands'. Fields are SMT terms.
#[derive(Clone)]
enum VecOp {
    Concat(String, String),
    Cons(String, String),
    Rest(String),
    Slice(String, String, String),
    Lit(Vec<String>),
    Ite(String, String, String),
}

/// How deep callee contracts may refer to other contracts before calls in
/// them are treated as opaque. Stops a contract that calls its own function.
const MAX_CLAUSE_DEPTH: usize = 2;

struct Exec<'a> {
    m: &'a Module,
    ty: &'a TypeInfo,
    fn_name: String,
    decls: Vec<String>,
    /// Assumptions in scope: parameter ranges, path conditions, callee
    /// postconditions.
    facts: Vec<String>,
    /// Counts fresh constants. A closure body that creates none can be
    /// inlined into a `lambda`.
    fresh: usize,
    binders: usize,
    out: Vec<Obligation>,
    /// False while evaluating a callee's contract as a formula: its own
    /// well-definedness is the callee's obligation, not the caller's.
    emit: bool,
    inputs: Vec<(String, Ty)>,
    site: Site,
    clause_depth: usize,
    vec_ops: HashMap<String, VecOp>,
    /// The constant naming each i64 vector term whose counts are defined.
    counted: HashMap<String, String>,
    /// Definitions of those constants. They hold on every path, so they are
    /// never guarded by a branch condition.
    defs: Vec<String>,
    perms: Vec<String>,
}

fn vs(t: &Ty) -> Option<&'static str> {
    match t {
        Ty::Vec(e) => vec_sort(e),
        _ => None,
    }
}

fn fn_parts(t: &Ty) -> (Vec<Ty>, Ty) {
    match t {
        Ty::Fn(ps, r) => (ps.clone(), (**r).clone()),
        other => unreachable!("type checker proved this is a function, got {}", other.to_sexp()),
    }
}

impl<'a> Exec<'a> {
    // ---------- obligations ----------

    fn script(&self, goal: &str) -> String {
        let mut s = String::from(PRELUDE);
        // Quantifiers over vectors keep Z3 from finding counterexamples, so
        // only `perm?` goals get the counts. Leaving definitions out is sound.
        let counts = self.perms.iter().any(|p| goal.contains(p.as_str()));
        if counts {
            s += COUNTS;
        }
        for d in &self.decls {
            if counts || !d.starts_with("(declare-const |counted ") {
                s += d;
                s.push('\n');
            }
        }
        let defs = if counts { &self.defs[..] } else { &[] };
        for f in defs.iter().chain(&self.facts) {
            s += &format!("(assert {})\n", f);
        }
        s += &format!("(assert (not {}))\n", goal);
        s
    }

    fn obligation(&mut self, kind: VcKind, at: Origin, goal: Goal) {
        if self.emit {
            let inputs = self.inputs.clone();
            self.out.push(Obligation { fn_name: self.fn_name.clone(), kind, at: at.pos, expr: at.expr, site: self.site, goal, inputs });
        }
    }

    fn require(&mut self, kind: VcKind, at: Origin, goal: String) {
        if !self.emit {
            return;
        }
        let g = Goal::Script(self.script(&goal));
        self.obligation(kind, at, g);
    }

    fn require_value(&mut self, kind: VcKind, at: Origin, v: V<'a>) {
        match v {
            V::T(t) => self.require(kind, at, t),
            _ => self.obligation(kind, at, Goal::Unsupported("a value has no SMT encoding in M1".into())),
        }
    }

    // ---------- values ----------

    fn fresh_sym(&mut self, hint: &str) -> String {
        self.fresh += 1;
        // Warrant symbols cannot contain spaces, so these never collide.
        quote_sym(&format!("{} {}", hint, self.fresh))
    }

    fn binder(&mut self) -> String {
        self.binders += 1;
        quote_sym(&format!("k {}", self.binders))
    }

    fn range_facts(&mut self, term: &str, t: &Ty) -> Vec<String> {
        match t {
            Ty::I64 => vec![format!("(in64 {})", term)],
            Ty::Vec(e) => {
                let Some(s) = vec_sort(e) else { return Vec::new() };
                let mut v = vec![format!("(<= 0 (len-{} {}))", s, term), format!("(<= (len-{} {}) {})", s, term, MAX_LEN)];
                if **e == Ty::I64 {
                    let i = self.binder();
                    v.push(format!(
                        "(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} (len-VI {t}))) (in64 (select (arr-VI {t}) {i}))))",
                        i = i,
                        t = term
                    ));
                }
                v
            }
            _ => Vec::new(),
        }
    }

    /// A new unconstrained value of type `t`, known only to be in range.
    fn fresh_val(&mut self, t: &Ty, hint: &str) -> V<'a> {
        if let Ty::Fn(..) = t {
            return V::F(FnV::Unknown);
        }
        let Some(s) = sort(t) else { return V::Opaque };
        let name = self.fresh_sym(hint);
        self.decls.push(format!("(declare-const {} {})", name, s));
        let facts = self.range_facts(&name, t);
        self.facts.extend(facts);
        V::T(name)
    }

    /// A constant standing for the i64 vector `term` in `cnt-VI`, with its
    /// length and occurrence counts defined from how it was built. A
    /// constant names itself.
    fn counts_of(&mut self, term: &str) -> String {
        if let Some(n) = self.counted.get(term) {
            return n.clone();
        }
        if term.starts_with('|') && term.ends_with('|') && term.matches('|').count() == 2 {
            return term.to_string();
        }
        let n = self.fresh_sym("counted");
        self.decls.push(format!("(declare-const {} VI)", n));
        // Only the length: equating `n` with a term built from lambdas makes
        // Z3 give up (unknown) on goals it otherwise proves.
        self.defs.push(format!("(= (len-VI {}) (len-VI {}))", n, term));
        self.counted.insert(term.to_string(), n.clone());
        let x = self.binder();
        let t = "true".to_string();
        let (guard, body) = match self.vec_ops.get(term).cloned() {
            None => return n,
            Some(VecOp::Concat(a, b)) => (t, format!("(+ (cnt-VI {} {x}) (cnt-VI {} {x}))", self.counts_of(&a), self.counts_of(&b), x = x)),
            Some(VecOp::Cons(h, v)) => (t, format!("(+ (cnt-VI {} {x}) (ite (= {x} {}) 1 0))", self.counts_of(&v), h, x = x)),
            Some(VecOp::Rest(v)) => {
                let c = self.counts_of(&v);
                (format!("(> (len-VI {}) 0)", c), format!("(- (cnt-VI {c} {x}) (ite (= {x} (select (arr-VI {v}) 0)) 1 0))", c = c, v = v, x = x))
            }
            Some(VecOp::Slice(v, lo, hi)) => {
                let c = self.counts_of(&v);
                let g = format!("(and (<= 0 {lo}) (<= {lo} {hi}) (<= {hi} (len-VI {c})))", lo = lo, hi = hi, c = c);
                (g, format!("(rcnt-VI {} {} {} {})", c, lo, hi, x))
            }
            Some(VecOp::Lit(items)) => {
                let ones: Vec<String> = items.iter().map(|i| format!("(ite (= {} {}) 1 0)", x, i)).collect();
                (t, format!("(+ 0 {})", ones.join(" ")))
            }
            Some(VecOp::Ite(c, a, b)) => (t, format!("(ite {} (cnt-VI {} {x}) (cnt-VI {} {x}))", c, self.counts_of(&a), self.counts_of(&b), x = x)),
        };
        self.defs.push(format!("(forall (({x} Int)) (! (=> {g} (= (cnt-VI {n} {x}) {b})) :pattern ((cnt-VI {n} {x}))))", x = x, g = guard, n = n, b = body));
        n
    }

    /// A Bool constant defined as `(perm? a b)`. Facts mention only the
    /// constant, so a goal that does not can leave the counts out.
    fn is_perm(&mut self, a: &str, b: &str) -> String {
        let (a, b) = (self.counts_of(a), self.counts_of(b));
        let x = self.binder();
        let p = self.fresh_sym("perm?");
        self.decls.push(format!("(declare-const {} Bool)", p));
        self.defs.push(format!(
            "(= {p} (forall (({x} Int)) (! (= (cnt-VI {a} {x}) (cnt-VI {b} {x})) :pattern ((cnt-VI {a} {x})) :pattern ((cnt-VI {b} {x})))))",
            p = p,
            x = x,
            a = a,
            b = b
        ));
        self.perms.push(p.clone());
        p
    }

    /// Runs `f` assuming `cond`. Facts `f` learns stay known afterwards,
    /// guarded by `cond`.
    fn under<T>(&mut self, cond: &str, f: impl FnOnce(&mut Self) -> T) -> T {
        let base = self.facts.len();
        self.facts.push(cond.to_string());
        let r = f(self);
        let learned: Vec<String> = self.facts.drain(base + 1..).collect();
        self.facts.truncate(base);
        if !learned.is_empty() {
            self.facts.push(format!("(=> {} (and {}))", cond, learned.join(" ")));
        }
        r
    }

    // ---------- functions ----------

    fn function(&mut self, d: &'a FnDecl) {
        let mut env: Env<'a> = Vec::new();
        for p in &d.params {
            let t = Ty::from_type(&p.ty);
            let v = match (&t, sort(&t)) {
                (Ty::Fn(..), _) => V::F(FnV::Unknown),
                (_, Some(s)) => {
                    let name = quote_sym(&p.name);
                    self.decls.push(format!("(declare-const {} {})", name, s));
                    let facts = self.range_facts(&name, &t);
                    self.facts.extend(facts);
                    self.inputs.push((name.clone(), t));
                    V::T(name)
                }
                _ => V::Opaque,
            };
            env.push((p.name.clone(), v));
        }
        for (index, c) in d.spec.requires.iter().enumerate() {
            self.site = Site::Requires(index);
            if let V::T(t) = self.eval(&c.expr, &mut env) {
                self.facts.push(t);
            }
        }
        self.site = Site::Body;
        let result = self.eval_seq(&d.body, &mut env);
        env.push(("result".into(), result));
        for (index, c) in d.spec.ensures.iter().enumerate() {
            self.site = Site::Ensures(index);
            let g = self.eval(&c.expr, &mut env);
            self.require_value(VcKind::Ensures { index }, Origin::of(&c.expr), g);
        }
    }

    /// Evaluates a callee's clause as a formula about the caller's values.
    fn clause_formula(&mut self, e: &'a Expr, env: &mut Env<'a>) -> V<'a> {
        let emit = self.emit;
        self.emit = false;
        self.clause_depth += 1;
        let v = self.eval(e, env);
        self.clause_depth -= 1;
        self.emit = emit;
        v
    }

    fn call_global(&mut self, i: FnIdx, args: Vec<V<'a>>, at: Origin, check_requires: bool) -> V<'a> {
        let d = &self.m.fns[i];
        let ret = Ty::from_type(&d.ret);
        if self.clause_depth > MAX_CLAUSE_DEPTH {
            return self.fresh_val(&ret, &d.name);
        }
        let mut env: Env<'a> = d.params.iter().map(|p| p.name.clone()).zip(args).collect();
        for (index, c) in d.spec.requires.iter().enumerate() {
            let g = self.clause_formula(&c.expr, &mut env);
            if check_requires {
                self.require_value(VcKind::Requires { callee: d.name.clone(), index }, at, g.clone());
            }
            if let V::T(t) = g {
                self.facts.push(t);
            }
        }
        let r = self.fresh_val(&ret, &d.name);
        env.push(("result".into(), r.clone()));
        for c in &d.spec.ensures {
            if let V::T(t) = self.clause_formula(&c.expr, &mut env) {
                self.facts.push(t);
            }
        }
        r
    }

    /// Calls a function value. `fty` is its (resolved) function type.
    fn apply(&mut self, f: V<'a>, args: Vec<V<'a>>, fty: &Ty, at: Origin) -> V<'a> {
        let (ps, ret) = fn_parts(fty);
        match f {
            V::F(FnV::Lambda(params, body, mut env)) => {
                env.extend(params.iter().map(|p| p.name.clone()).zip(args));
                self.eval_seq(body, &mut env)
            }
            // Requires of a function passed by value stay checked at run time.
            V::F(FnV::Global(i)) => self.call_global(i, args, at, false),
            V::F(FnV::Builtin(b)) => self.builtin(b, args, &ps, &ret, at),
            V::F(FnV::Unknown) | V::Opaque | V::T(_) => self.fresh_val(&ret, "call"),
        }
    }

    // ---------- expressions ----------

    fn eval_seq(&mut self, es: &'a [Expr], env: &mut Env<'a>) -> V<'a> {
        let mut last = V::Opaque;
        for e in es {
            last = self.eval(e, env);
        }
        last
    }

    fn eval(&mut self, e: &'a Expr, env: &mut Env<'a>) -> V<'a> {
        let t = self.ty.of(e).clone();
        match &e.kind {
            ExprKind::Int(n) => V::T(int_lit(*n)),
            ExprKind::Bool(b) => V::T(b.to_string()),
            ExprKind::Str(s) => V::T(str_lit(s)),
            ExprKind::Local(n) => env.iter().rev().find(|(k, _)| k == n).map(|(_, v)| v.clone()).expect("lower resolved every local"),
            ExprKind::Global(i) => V::F(FnV::Global(*i)),
            ExprKind::Builtin(b) => V::F(FnV::Builtin(*b)),
            ExprKind::Lambda(ps, body) => V::F(FnV::Lambda(ps, body, env.clone())),
            ExprKind::VecLit(items) => {
                let vals: Vec<V<'a>> = items.iter().map(|x| self.eval(x, env)).collect();
                self.vector(vals, &t)
            }
            ExprKind::If(c, th, el) => {
                let cv = self.eval(c, env);
                let V::T(ct) = cv else {
                    self.eval(th, env);
                    self.eval(el, env);
                    return self.fresh_val(&t, "if");
                };
                let tv = self.under(&ct, |x| x.eval(th, env));
                let fv = self.under(&format!("(not {})", ct), |x| x.eval(el, env));
                match (tv, fv) {
                    (V::T(a), V::T(b)) => {
                        let term = format!("(ite {} {} {})", ct, a, b);
                        if t == Ty::Vec(Box::new(Ty::I64)) {
                            self.vec_ops.insert(term.clone(), VecOp::Ite(ct, a, b));
                        }
                        V::T(term)
                    }
                    _ => self.fresh_val(&t, "if"),
                }
            }
            ExprKind::Let(binds, body) => {
                let depth = env.len();
                for (n, v) in binds {
                    let val = self.eval(v, env);
                    env.push((n.clone(), val));
                }
                let r = self.eval_seq(body, env);
                env.truncate(depth);
                r
            }
            ExprKind::Do(es) => self.eval_seq(es, env),
            ExprKind::And(es) => self.junction(es, env, true),
            ExprKind::Or(es) => self.junction(es, env, false),
            ExprKind::Call(f, args) => {
                let vals: Vec<V<'a>> = args.iter().map(|a| self.eval(a, env)).collect();
                match &f.kind {
                    ExprKind::Builtin(b) => {
                        let tys: Vec<Ty> = args.iter().map(|a| self.ty.of(a).clone()).collect();
                        self.builtin(*b, vals, &tys, &t, Origin::of(e))
                    }
                    ExprKind::Global(i) => self.call_global(*i, vals, Origin::of(e), true),
                    _ => {
                        let fv = self.eval(f, env);
                        let fty = self.ty.of(f).clone();
                        self.apply(fv, vals, &fty, Origin::of(e))
                    }
                }
            }
        }
    }

    /// `and` / `or` with short-circuit: later operands are evaluated knowing
    /// the earlier ones did not decide the result.
    fn junction(&mut self, es: &'a [Expr], env: &mut Env<'a>, is_and: bool) -> V<'a> {
        let Some((first, rest)) = es.split_first() else { return V::T(is_and.to_string()) };
        let V::T(a) = self.eval(first, env) else {
            for x in rest {
                self.eval(x, env);
            }
            return self.fresh_val(&Ty::Bool, "junction");
        };
        if rest.is_empty() {
            return V::T(a);
        }
        let cond = if is_and { a.clone() } else { format!("(not {})", a) };
        let b = self.under(&cond, |x| x.junction(rest, env, is_and));
        match b {
            V::T(b) => V::T(format!("({} {} {})", if is_and { "and" } else { "or" }, a, b)),
            _ => self.fresh_val(&Ty::Bool, "junction"),
        }
    }

    fn vector(&mut self, vals: Vec<V<'a>>, t: &Ty) -> V<'a> {
        let (Some(s), Ty::Vec(elem)) = (vs(t), t) else { return V::Opaque };
        let default = match **elem {
            Ty::I64 => "0",
            Ty::Bool => "false",
            _ => "\"\"",
        };
        let mut arr = format!("((as const (Array Int {})) {})", sort(elem).expect("vec_sort implies an element sort"), default);
        for (i, v) in vals.iter().enumerate() {
            let V::T(x) = v else { return self.fresh_val(t, "vec") };
            arr = format!("(store {} {} {})", arr, i, x);
        }
        let term = format!("(mk-{} {} {})", s, arr, vals.len());
        if s == "VI" {
            let items = vals.into_iter().map(|v| if let V::T(x) = v { x } else { unreachable!("checked above") }).collect();
            self.vec_ops.insert(term.clone(), VecOp::Lit(items));
        }
        V::T(term)
    }

    fn builtin(&mut self, b: Builtin, args: Vec<V<'a>>, tys: &[Ty], ret: &Ty, at: Origin) -> V<'a> {
        use Builtin as B;
        match b {
            B::Map | B::Filter | B::Fold | B::All => return self.higher_order(b, args, tys, ret, at),
            B::Vec => return self.vector(args, ret),
            B::Print => return V::T("true".into()),
            _ => {}
        }
        let mut ts = Vec::with_capacity(args.len());
        for a in args {
            let V::T(x) = a else { return self.fresh_val(ret, b.name()) };
            ts.push(x);
        }
        let sfx = || tys.first().and_then(vs).expect("type checker proved a vector of an encodable element");
        let t = |i: usize| ts[i].as_str();
        let term = match b {
            B::Add | B::Mul | B::Sub => {
                let op = match b {
                    B::Add => "+",
                    B::Mul => "*",
                    _ => "-",
                };
                match ts.len() {
                    0 => (if b == B::Mul { "1" } else { "0" }).to_string(),
                    1 if b == B::Sub => {
                        let r = format!("(- {})", t(0));
                        self.require(VcKind::Overflow, at, format!("(in64 {})", r));
                        r
                    }
                    1 => ts[0].clone(),
                    n => {
                        let prefixes: Vec<String> = (2..=n).map(|k| format!("(in64 ({} {}))", op, ts[..k].join(" "))).collect();
                        self.require(VcKind::Overflow, at, format!("(and {})", prefixes.join(" ")));
                        format!("({} {})", op, ts.join(" "))
                    }
                }
            }
            B::Div | B::Mod => {
                self.require(VcKind::DivZero, at, format!("(not (= {} 0))", t(1)));
                self.require(VcKind::Overflow, at, format!("(not (and (= {} {}) (= {} (- 1))))", t(0), I64_MIN, t(1)));
                format!("({} {} {})", if b == B::Div { "tdiv" } else { "mod" }, t(0), t(1))
            }
            B::Eq => match vs(&tys[0]) {
                Some(s) => format!("(eq-{} {} {})", s, t(0), t(1)),
                None => format!("(= {} {})", t(0), t(1)),
            },
            B::Lt => format!("(< {} {})", t(0), t(1)),
            B::Le => format!("(<= {} {})", t(0), t(1)),
            B::Gt => format!("(> {} {})", t(0), t(1)),
            B::Ge => format!("(>= {} {})", t(0), t(1)),
            B::Not => format!("(not {})", t(0)),
            B::Len => format!("(len-{} {})", sfx(), t(0)),
            B::IsEmpty => format!("(= (len-{} {}) 0)", sfx(), t(0)),
            B::IsSorted => format!("(sorted-VI {})", t(0)),
            B::Get => {
                let s = sfx();
                self.require(VcKind::Bounds, at, format!("(and (<= 0 {i}) (< {i} (len-{s} {v})))", i = t(1), s = s, v = t(0)));
                format!("(select (arr-{} {}) {})", s, t(0), t(1))
            }
            B::Slice => {
                let s = sfx();
                let (v, lo, hi) = (t(0), t(1), t(2));
                self.require(VcKind::Bounds, at, format!("(and (<= 0 {lo}) (<= {lo} {hi}) (<= {hi} (len-{s} {v})))", lo = lo, hi = hi, s = s, v = v));
                let k = self.binder();
                format!("(mk-{s} (lambda (({k} Int)) (select (arr-{s} {v}) (+ {k} {lo}))) (- {hi} {lo}))", s = s, k = k, v = v, lo = lo, hi = hi)
            }
            B::Rest => {
                let s = sfx();
                self.require(VcKind::Bounds, at, format!("(> (len-{} {}) 0)", s, t(0)));
                let k = self.binder();
                format!("(mk-{s} (lambda (({k} Int)) (select (arr-{s} {v}) (+ {k} 1))) (- (len-{s} {v}) 1))", s = s, k = k, v = t(0))
            }
            B::Concat => {
                let s = sfx();
                let k = self.binder();
                format!(
                    "(mk-{s} (lambda (({k} Int)) (ite (< {k} (len-{s} {a})) (select (arr-{s} {a}) {k}) (select (arr-{s} {b}) (- {k} (len-{s} {a}))))) (+ (len-{s} {a}) (len-{s} {b})))",
                    s = s,
                    k = k,
                    a = t(0),
                    b = t(1)
                )
            }
            B::Cons => {
                let s = vs(&tys[1]).expect("type checker proved a vector");
                let k = self.binder();
                format!(
                    "(mk-{s} (lambda (({k} Int)) (ite (= {k} 0) {x} (select (arr-{s} {v}) (- {k} 1)))) (+ (len-{s} {v}) 1))",
                    s = s,
                    k = k,
                    x = t(0),
                    v = t(1)
                )
            }
            B::Range => {
                self.require(VcKind::Bounds, at, format!("(>= {} 0)", t(0)));
                let k = self.binder();
                format!("(mk-VI (lambda (({k} Int)) {k}) {n})", k = k, n = t(0))
            }
            B::IsPerm => self.is_perm(t(0), t(1)),
            B::Map | B::Filter | B::Fold | B::All | B::Vec | B::Print => unreachable!("handled above"),
        };
        if ret == &Ty::Vec(Box::new(Ty::I64)) {
            let op = match b {
                B::Concat => Some(VecOp::Concat(ts[0].clone(), ts[1].clone())),
                B::Cons => Some(VecOp::Cons(ts[0].clone(), ts[1].clone())),
                B::Rest => Some(VecOp::Rest(ts[0].clone())),
                B::Slice => Some(VecOp::Slice(ts[0].clone(), ts[1].clone(), ts[2].clone())),
                _ => None,
            };
            if let Some(op) = op {
                self.vec_ops.insert(term.clone(), op);
            }
        }
        V::T(term)
    }

    /// `map` / `filter` / `fold` / `all?`. The function argument is applied
    /// to an arbitrary in-bounds element `k`, so obligations inside it hold
    /// for every element. A body that needs no fresh constants (no calls,
    /// no approximations) is inlined as a `lambda` or `forall` over `k`.
    fn higher_order(&mut self, b: Builtin, mut args: Vec<V<'a>>, tys: &[Ty], ret: &Ty, at: Origin) -> V<'a> {
        let vec_ty = tys.last().expect("arity checked").clone();
        let V::T(v) = args.pop().expect("arity checked") else { return self.fresh_val(ret, b.name()) };
        let Some(s) = vs(&vec_ty) else { return self.fresh_val(ret, b.name()) };
        let f = args.remove(0);
        let k = self.fresh_sym("k");
        self.decls.push(format!("(declare-const {} Int)", k));
        let elem = V::T(format!("(select (arr-{} {}) {})", s, v, k));
        let in_bounds = format!("(and (<= 0 {k}) (< {k} (len-{s} {v})))", k = k, s = s, v = v);
        let before = self.fresh;
        let out = match b {
            B::Fold => {
                let acc = self.fresh_val(ret, "acc");
                self.under(&in_bounds, |x| x.apply(f, vec![acc, elem], &tys[0], at))
            }
            _ => self.under(&in_bounds, |x| x.apply(f, vec![elem], &tys[0], at)),
        };
        let inlinable = self.fresh == before;
        use Builtin as B;
        match (b, out, vs(ret)) {
            (B::Map, V::T(body), Some(rs)) if inlinable => {
                V::T(format!("(mk-{rs} (lambda (({k} Int)) {body}) (len-{s} {v}))", rs = rs, k = k, body = body, s = s, v = v))
            }
            (B::All, V::T(body), _) if inlinable => V::T(format!("(forall (({k} Int)) (=> {bounds} {body}))", k = k, bounds = in_bounds, body = body)),
            _ => {
                let r = self.fresh_val(ret, b.name());
                if let (V::T(r), Some(rs)) = (&r, vs(ret)) {
                    let rel = if b == B::Map { "=" } else { "<=" };
                    self.facts.push(format!("({} (len-{} {}) (len-{} {}))", rel, rs, r, s, v));
                }
                r
            }
        }
    }
}

/// `(xs [4000000000] n 3)` from a solver model.
pub fn counterexample_sexp(model: &[(String, String)]) -> String {
    let parts: Vec<String> = model.iter().map(|(k, v)| format!("{} {}", k, v)).collect();
    format!("({})", parts.join(" "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lower;
    use crate::sexp::parse_all_spanned;
    use crate::solver::{Outcome, Solver, Z3};

    fn obligations(src: &str) -> Vec<Obligation> {
        let (f, s) = parse_all_spanned(src).unwrap();
        let m = lower(&f, &s).unwrap();
        let ty = crate::types::check(&m).unwrap_or_else(|e| panic!("{:?}", e));
        generate(&m, &ty)
    }

    /// `(fn kind outcome)` per obligation, in source order.
    fn verdicts(src: &str) -> Option<Vec<(String, String, String)>> {
        let z = Z3::find_for_test(5000)?;
        Some(
            obligations(src)
                .into_iter()
                .map(|o| {
                    let r = match &o.goal {
                        Goal::Unsupported(_) => "unsupported".to_string(),
                        Goal::Script(s) => match z.check(s, &o.inputs).unwrap() {
                            Outcome::Proved => "proved".into(),
                            Outcome::Failed { model } => format!("failed {}", counterexample_sexp(&model)),
                            Outcome::Unknown { reason } => format!("unknown {}", reason),
                        },
                    };
                    (o.fn_name, o.kind.to_sexp(), r)
                })
                .collect(),
        )
    }

    fn assert_all(src: &str, want: &str) {
        let Some(v) = verdicts(src) else { return };
        for (f, k, r) in &v {
            assert!(r.starts_with(want), "{} {} -> {}\nall: {:?}", f, k, r, v);
        }
    }

    #[test]
    fn arithmetic_obligations_are_generated_per_operation() {
        let kinds: Vec<String> = obligations("(defn f [a : i64 b : i64] -> i64 (+ (* a b) (/ a b)))").iter().map(|o| o.kind.to_sexp()).collect();
        assert_eq!(kinds, ["overflow", "div-zero", "overflow", "overflow"]);
    }

    #[test]
    fn unguarded_arithmetic_fails_with_a_counterexample() {
        let Some(v) = verdicts("(defn f [a : i64] -> i64 (+ a 1))") else { return };
        assert_eq!(v, [("f".into(), "overflow".into(), "failed (a 9223372036854775807)".into())]);
    }

    #[test]
    fn guards_from_requires_and_branches_discharge_obligations() {
        assert_all("(defn f [a : i64 b : i64] -> i64 (:requires (< a 1000) (> a 0)) (if (= b 0) 0 (/ (+ a 1) b)))", "proved");
        assert_all("(defn f [xs : (Vec i64)] -> i64 (if (empty? xs) 0 (get xs 0)))", "proved");
        assert_all("(defn f [xs : (Vec i64)] -> Bool (or (empty? xs) (> (get xs 0) 0)))", "proved");
    }

    #[test]
    fn bounds_failures_are_reported() {
        let Some(v) = verdicts("(defn f [xs : (Vec i64)] -> i64 (get xs 1))") else { return };
        assert_eq!(v.len(), 1);
        assert!(v[0].2.starts_with("failed (xs ["), "{:?}", v);
    }

    #[test]
    fn closure_bodies_are_checked_for_every_element() {
        let Some(v) = verdicts("(defn f [xs : (Vec i64)] -> (Vec i64) (map (fn [x] (* x x)) xs))") else { return };
        assert_eq!(v.len(), 1);
        assert!(v[0].2.starts_with("failed (xs ["), "{:?}", v);
        assert_all(
            "(defn f [xs : (Vec i64)] -> (Vec i64) (:requires (all? (fn [x] (and (< x 1000) (> x -1000))) xs)) (map (fn [x] (* x x)) xs))",
            "proved",
        );
    }

    #[test]
    fn calls_check_requires_and_assume_ensures() {
        let src = "(defn pos [x : i64] -> i64 (:requires (> x 0) (< x 1000)) (:ensures (> result x)) (+ x 1))
                   (defn ok [] -> i64 (:ensures (> result 5)) (pos 5))
                   (defn bad [] -> i64 (pos 0))";
        let Some(v) = verdicts(src) else { return };
        let get = |f: &str, k: &str| v.iter().find(|(a, b, _)| a == f && b == k).map(|x| x.2.clone()).unwrap();
        assert_eq!(get("pos", "overflow"), "proved");
        assert_eq!(get("pos", "ensures :clause 0"), "proved");
        assert_eq!(get("ok", "requires :callee pos :clause 0"), "proved");
        assert_eq!(get("ok", "ensures :clause 0"), "proved");
        assert_eq!(get("ok", "requires :callee pos :clause 1"), "proved");
        assert_eq!(get("bad", "requires :callee pos :clause 0"), "failed ()");
    }

    #[test]
    fn perm_is_proved_through_vector_operations() {
        assert_all("(defn id [xs : (Vec i64)] -> (Vec i64) (:ensures (perm? result xs)) xs)", "proved");
        assert_all("(defn swap [a : (Vec i64) b : (Vec i64)] -> (Vec i64) (:ensures (perm? result (concat a b))) (concat b a))", "proved");
        assert_all(
            "(defn halves [xs : (Vec i64)] -> (Vec i64) (:ensures (perm? result xs))
               (let [h (/ (len xs) 2)] (concat (slice xs h (len xs)) (slice xs 0 h))))",
            "proved",
        );
        assert_all(
            "(defn rot [xs : (Vec i64)] -> (Vec i64) (:ensures (perm? result xs)) (if (empty? xs) xs (concat (rest xs) [(get xs 0)])))",
            "proved",
        );
        assert_all(
            "(defn id [xs : (Vec i64)] -> (Vec i64) (:ensures (perm? result xs)) xs)
             (defn use [xs : (Vec i64)] -> Bool (:ensures result) (perm? (cons 1 (id xs)) (cons 1 xs)))",
            "proved",
        );
    }

    #[test]
    fn wrong_perm_is_never_proved() {
        // Against a literal Z3 finds no model for the counts and says unknown.
        for (body, want) in [("(cons 0 xs)", "failed (xs ["), ("(rest xs)", "failed (xs ["), ("(concat xs xs)", "failed (xs ["), ("[1 2]", "unknown")] {
            let src = format!("(defn f [xs : (Vec i64)] -> (Vec i64) (:requires (> (len xs) 0)) (:ensures (perm? result xs)) {})", body);
            let Some(v) = verdicts(&src) else { return };
            let ens: Vec<&String> = v.iter().filter(|x| x.1 == "ensures :clause 0").map(|x| &x.2).collect();
            assert!(ens.len() == 1 && ens[0].starts_with(want), "{} -> {:?}", body, v);
        }
    }

    #[test]
    fn obligations_know_their_clause_and_call_site() {
        let src = "(defn h [xs : (Vec i64)] -> i64 (:requires (> (get xs 0) 0)) (:ensures (> result (get xs 0))) (+ (get xs 0) 1))
                   (defn g [] -> i64 (h [5]))";
        let (f, s) = parse_all_spanned(src).unwrap();
        let m = lower(&f, &s).unwrap();
        let obs = generate(&m, &crate::types::check(&m).unwrap());
        let sites: Vec<(String, Site)> = obs.iter().map(|o| (o.kind.to_sexp(), o.site)).collect();
        assert_eq!(
            sites,
            [
                ("bounds".into(), Site::Requires(0)),
                ("bounds".into(), Site::Body),
                ("overflow".into(), Site::Body),
                ("bounds".into(), Site::Ensures(0)),
                ("ensures :clause 0".into(), Site::Ensures(0)),
                ("requires :callee h :clause 0".into(), Site::Body),
            ]
        );
        let ExprKind::Call(..) = &m.fns[1].body[0].kind else { panic!() };
        assert_eq!(obs[5].expr, m.fns[1].body[0].id);
    }
}

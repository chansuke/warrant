//! The M2 interpreter: evaluates `ir::Program`. Values and errors mean what
//! they meant in the M1 interpreter, which M2-7 removed; the outcomes it
//! agreed with are in `tests/runtime_diff.golden`.
//!
//! Contracts are the clauses `ir::Program` compiled in. Effects are checked
//! dynamically and transitively: `print` fails if any function on the call
//! stack declares effects without `io`. Integer arithmetic is checked.

use crate::builtin::Builtin;
use crate::diag::{ErrorKind, RtError};
use crate::ir::{Clause, Fn, Fork, Node, Program};
use crate::profile::{ForkTimes, Profiler};
use crate::sexp::{flat, quote_str};
use crate::value::{Closure, Copied, Value, Vector};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

const MAX_DEPTH: usize = 200_000;

/// Forks nest up to `log2(threads)`, rounded up, plus this many levels; deeper ones run
/// in their task (D30). The extra levels give work stealing pieces to even
/// out an uneven split; past about 10 the forks cost more than they even out
/// (D31).
const FORK_SLACK: usize = 10;

/// The threads a run uses. One runs on the calling thread and never forks.
pub struct Pool(Option<rayon::ThreadPool>);

impl Pool {
    /// Every worker gets the 1 GiB stack the CLI's main thread has, since a
    /// forked task may recurse as deep as the program does.
    pub fn new(threads: usize) -> Result<Pool, RtError> {
        if threads <= 1 {
            return Ok(Pool(None));
        }
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(1 << 30)
            .thread_name(|i| format!("warrant-{}", i))
            .build()
            .map(|p| Pool(Some(p)))
            .map_err(|e| RtError::new(ErrorKind::Internal, format!("cannot start {} threads: {}", threads, e)))
    }

    pub fn threads(&self) -> usize {
        self.0.as_ref().map_or(1, rayon::ThreadPool::current_num_threads)
    }

    /// Runs `main` on this pool's threads, forking where the program allows.
    pub fn call_main(&self, it: &mut Interp<'_>) -> R<Value> {
        let threads = self.threads();
        match &self.0 {
            None => it.call_main(),
            Some(p) => {
                // Only inside `install`: a join outside it would run on
                // rayon's global pool, whose stacks are small.
                it.forks_left = threads.next_power_of_two().trailing_zeros() as usize + FORK_SLACK;
                let r = p.install(|| it.call_main());
                it.forks_left = 0;
                r
            }
        }
    }
}

type R<T> = Result<T, RtError>;

/// How a function body in tail position ends.
enum Tail {
    Done(Value),
    /// A `ConsTail`: cons `head` onto the result of calling the same
    /// function again with these arguments.
    Again(Value, Vec<Value>),
}

/// Fills frame slots that are not bound yet. Never read: a slot is written
/// by its binding before any use.
const UNSET: Value = Value::Bool(false);

impl Program {
    pub fn show(&self, v: &Value) -> String {
        match v {
            Value::Int(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => quote_str(s),
            Value::Vec(xs) => format!("[{}]", xs.as_slice().iter().map(|x| self.show(x)).collect::<Vec<_>>().join(" ")),
            Value::Closure(_) => "#<fn>".into(),
            Value::Func(i) => format!("#<fn {}>", self.fns[*i].name),
            Value::Builtin(b) => format!("#<builtin {}>", b.name()),
        }
    }

    pub fn main(&self) -> Option<&Fn> {
        self.index.get("main").map(|&i| &self.fns[i])
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

fn values_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Vec(x), Value::Vec(y)) => x.len() == y.len() && x.as_slice().iter().zip(y.as_slice()).all(|(p, q)| values_eq(p, q)),
        _ => false,
    }
}

fn int(v: &Value, op: &str) -> R<i64> {
    match v {
        Value::Int(n) => Ok(*n),
        o => Err(RtError::new(ErrorKind::Type, format!("({} ...) expects i64, got {}", op, type_name(o)))),
    }
}

fn vector<'v>(v: &'v Value, op: &str) -> R<&'v Vector> {
    match v {
        Value::Vec(x) => Ok(x),
        o => Err(RtError::new(ErrorKind::Type, format!("({} ...) expects vec, got {}", op, type_name(o)))),
    }
}

fn vecv<'v>(v: &'v Value, op: &str) -> R<&'v [Value]> {
    vector(v, op).map(Vector::as_slice)
}

/// Takes the vector out of an argument, so an in-place update can see that
/// nothing else refers to its buffer.
fn take_vec(v: &mut Value, op: &str) -> R<Vector> {
    match std::mem::replace(v, Value::Bool(false)) {
        Value::Vec(x) => Ok(x),
        o => Err(RtError::new(ErrorKind::Type, format!("({} ...) expects vec, got {}", op, type_name(&o)))),
    }
}

fn arity(op: &str, args: &[Value], n: usize) -> R<()> {
    if args.len() != n {
        return Err(RtError::new(ErrorKind::Arity, format!("{} expects {} args, got {}", op, n, args.len())));
    }
    Ok(())
}

pub struct Interp<'p> {
    prog: &'p Program,
    pub prof: Profiler,
    /// Functions on the call stack, innermost last.
    effect_stack: Vec<usize>,
    depth: usize,
    /// How many more forks may nest below this point; 0 runs `Fork` as the
    /// call it wraps.
    forks_left: usize,
    /// One per fork this code runs in the later arguments of. Set when the
    /// earlier arguments fail: what this code computes is then thrown away,
    /// so it stops at the next call or builtin.
    stops: Vec<Arc<AtomicBool>>,
    /// One per fork this code runs in the earlier arguments of. Nothing
    /// catches an error, so a failure here fails each of those forks'
    /// earlier arguments, and their later ones can stop at once, before
    /// the error reaches them (D30).
    fails: Vec<Arc<AtomicBool>>,
}

impl<'p> Interp<'p> {
    pub fn new(prog: &'p Program, profile: bool) -> Self {
        Interp {
            prog,
            prof: Profiler::new(profile),
            effect_stack: Vec::new(),
            depth: 0,
            forks_left: 0,
            stops: Vec::new(),
            fails: Vec::new(),
        }
    }

    fn stopped(&self) -> R<()> {
        if self.stops.iter().any(|s| s.load(Ordering::Relaxed)) {
            // Never seen: the failure of the earlier arguments wins.
            return Err(RtError::new(ErrorKind::Internal, "a forked task was stopped"));
        }
        Ok(())
    }

    /// Runs `f` as code in the earlier arguments of the forks in `fails`.
    fn failing<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let r = f(self);
        if r.is_err() {
            for s in &self.fails {
                s.store(true, Ordering::Relaxed);
            }
        }
        r
    }

    /// Evaluates `args`: those before `f.split` here, the rest in a task
    /// that may run on another thread. Returns what evaluating them in order
    /// returns: the first failure, and the profile of the work done up to it.
    fn fork_args(&mut self, f: &Fork, args: &[Node], frame: &mut [Value]) -> R<Vec<Value>> {
        let (mine, theirs) = args.split_at(f.split);
        let mut their_frame = vec![UNSET; frame.len()];
        for &(s, take) in &f.copy {
            their_frame[s] = if take { std::mem::replace(&mut frame[s], UNSET) } else { frame[s].clone() };
        }
        let stop = Arc::new(AtomicBool::new(false));
        let mut stops = self.stops.clone();
        stops.push(stop.clone());
        let mut task = Interp {
            prog: self.prog,
            prof: self.prof.fork(),
            effect_stack: self.effect_stack.clone(),
            depth: self.depth,
            forks_left: self.forks_left - 1,
            stops,
            // A failure of the task fails this call, so it fails what this
            // code fails.
            fails: self.fails.clone(),
        };
        self.forks_left -= 1;
        self.fails.push(stop);
        self.prof.forks += 1;
        let before = self.prof.callees();
        let start = Instant::now();
        let ((mine, mine_ns), (theirs, theirs_ns)) = rayon::join(
            || {
                let t = Instant::now();
                let r = self.failing(|it| it.eval_all(mine, frame));
                (r, t.elapsed().as_nanos())
            },
            || {
                let t = Instant::now();
                let r = task.failing(|it| {
                    it.stopped()?;
                    it.eval_all(theirs, &mut their_frame)
                });
                (r, t.elapsed().as_nanos())
            },
        );
        let wall_ns = start.elapsed().as_nanos();
        self.fails.pop();
        self.forks_left += 1;
        // In order, a failure here means the task's arguments never ran.
        let mut mine = mine?;
        self.prof.merge(task.prof, &ForkTimes { before, wall_ns, mine_ns, theirs_ns });
        mine.extend(theirs?);
        Ok(mine)
    }

    pub fn call_main(&mut self) -> R<Value> {
        let Some(&m) = self.prog.index.get("main") else {
            return Err(RtError::new(ErrorKind::Load, "no (defn main [] ...) found"));
        };
        self.call_fn(m, Vec::new())
    }

    fn eval(&mut self, n: &Node, frame: &mut [Value]) -> R<Value> {
        match n {
            Node::Int(i) => Ok(Value::Int(*i)),
            Node::Bool(b) => Ok(Value::Bool(*b)),
            Node::Str(s) => Ok(Value::Str(s.clone())),
            Node::Local(s) => Ok(frame[*s].clone()),
            Node::Move(s) => Ok(std::mem::replace(&mut frame[*s], UNSET)),
            Node::Global(i) => Ok(Value::Func(*i)),
            Node::Builtin(b) => Ok(Value::Builtin(*b)),
            Node::VecLit(items) => {
                let v = self.eval_all(items, frame)?;
                self.prof.vec_alloc(v.len());
                Ok(Value::Vec(Vector::new(v)))
            }
            Node::If(c, t, f) => {
                let b = self.cond(c, frame)?;
                self.eval(if b { t } else { f }, frame)
            }
            Node::Let(binds, body) => {
                for (slot, v) in binds {
                    frame[*slot] = self.eval(v, frame)?;
                }
                let r = self.eval_seq(body, frame);
                // Release the bindings when the scope ends, as M1 drops its
                // environment, so a dead value holds no memory or reference.
                // On error the whole frame is dropped anyway.
                for (slot, _) in binds {
                    frame[*slot] = UNSET;
                }
                r
            }
            Node::Do(es) => self.eval_seq(es, frame),
            Node::And(es) => self.junction(es, frame, false),
            Node::Or(es) => self.junction(es, frame, true),
            Node::Lambda(code) => {
                let captured = code.captures.iter().map(|(outer, _)| frame[*outer].clone()).collect();
                Ok(Value::Closure(Arc::new(Closure { code: code.clone(), captured })))
            }
            Node::CallGlobal(i, args) => {
                let args = self.eval_all(args, frame)?;
                self.call_fn(*i, args)
            }
            Node::CallBuiltin(b, args) => {
                let args = self.eval_all(args, frame)?;
                self.builtin(*b, args)
            }
            Node::CallValue(f, args) => {
                let f = self.eval(f, frame)?;
                let args = self.eval_all(args, frame)?;
                self.apply(&f, args)
            }
            Node::Fork(f) if self.forks_left == 0 => self.eval(&f.call, frame),
            Node::Fork(f) => match &f.call {
                Node::CallGlobal(i, args) => {
                    let args = self.fork_args(f, args, frame)?;
                    self.call_fn(*i, args)
                }
                Node::CallBuiltin(b, args) => {
                    let args = self.fork_args(f, args, frame)?;
                    self.builtin(*b, args)
                }
                _ => self.eval(&f.call, frame),
            },
            // Only `eval_tail` meets these; this is what one means.
            Node::ConsTail(..) => match self.eval_tail(n, frame)? {
                Tail::Done(v) => Ok(v),
                Tail::Again(..) => unreachable!("eval_tail returns Again only at a ConsTail, which it evaluates"),
            },
        }
    }

    fn cond(&mut self, c: &Node, frame: &mut [Value]) -> R<bool> {
        match self.eval(c, frame)? {
            Value::Bool(b) => Ok(b),
            o => Err(RtError::new(ErrorKind::Type, format!("if condition must be bool, got {}", type_name(&o)))),
        }
    }

    /// Evaluates `n` in tail position of a function body: a `ConsTail`
    /// returns its head and arguments instead of calling.
    fn eval_tail(&mut self, n: &Node, frame: &mut [Value]) -> R<Tail> {
        match n {
            Node::If(c, t, f) => {
                let b = self.cond(c, frame)?;
                self.eval_tail(if b { t } else { f }, frame)
            }
            Node::Let(binds, body) => {
                for (slot, v) in binds {
                    frame[*slot] = self.eval(v, frame)?;
                }
                let r = self.eval_tail_seq(body, frame);
                for (slot, _) in binds {
                    frame[*slot] = UNSET;
                }
                r
            }
            Node::Do(es) => self.eval_tail_seq(es, frame),
            Node::ConsTail(head, args) => {
                let head = self.eval(head, frame)?;
                let args = self.eval_all(args, frame)?;
                Ok(Tail::Again(head, args))
            }
            _ => self.eval(n, frame).map(Tail::Done),
        }
    }

    fn eval_tail_seq(&mut self, es: &[Node], frame: &mut [Value]) -> R<Tail> {
        let (last, init) = es.split_last().expect("lower rejects empty bodies");
        for e in init {
            self.eval(e, frame)?;
        }
        self.eval_tail(last, frame)
    }

    fn eval_all(&mut self, es: &[Node], frame: &mut [Value]) -> R<Vec<Value>> {
        let mut out = Vec::with_capacity(es.len());
        for e in es {
            out.push(self.eval(e, frame)?);
        }
        Ok(out)
    }

    fn eval_seq(&mut self, es: &[Node], frame: &mut [Value]) -> R<Value> {
        let (last, init) = es.split_last().expect("lower rejects empty bodies");
        for e in init {
            self.eval(e, frame)?;
        }
        self.eval(last, frame)
    }

    /// `and` (`want` false) and `or` (`want` true): stops at the first `want`.
    fn junction(&mut self, es: &[Node], frame: &mut [Value], want: bool) -> R<Value> {
        for e in es {
            match self.eval(e, frame)? {
                Value::Bool(b) if b == want => return Ok(Value::Bool(want)),
                Value::Bool(_) => {}
                o => {
                    let h = if want { "or" } else { "and" };
                    return Err(RtError::new(ErrorKind::Type, format!("{} expects bool, got {}", h, type_name(&o))));
                }
            }
        }
        Ok(Value::Bool(!want))
    }

    pub fn apply(&mut self, f: &Value, args: Vec<Value>) -> R<Value> {
        match f {
            Value::Func(i) => self.call_fn(*i, args),
            Value::Closure(c) => {
                self.stopped()?;
                if c.code.params.len() != args.len() {
                    return Err(RtError::new(ErrorKind::Arity, format!("fn expects {} args, got {}", c.code.params.len(), args.len())));
                }
                self.prof.closure_calls += 1;
                let mut frame = vec![UNSET; c.code.frame];
                for ((_, own), v) in c.code.captures.iter().zip(&c.captured) {
                    frame[*own] = v.clone();
                }
                for (slot, a) in c.code.params.iter().zip(args) {
                    frame[*slot] = a;
                }
                self.eval_seq(&c.code.body, &mut frame)
            }
            Value::Builtin(b) => self.builtin(*b, args),
            o => Err(RtError::new(ErrorKind::Type, format!("cannot call a value of type {}", type_name(o)))),
        }
    }

    /// Calls function `i`. A `ConsTail` in its body runs the next call in
    /// this loop on one Rust frame and keeps the heads, so `(cons x (f ...))`
    /// recursion needs no stack. Counters, effects and traces come out as if
    /// each call had nested: only the depth differs.
    fn call_fn(&mut self, i: usize, args: Vec<Value>) -> R<Value> {
        let def = &self.prog.fns[i];
        if args.len() != def.params {
            return Err(RtError::new(ErrorKind::Arity, format!("{} expects {} args, got {}", def.name, def.params, args.len())));
        }
        if self.depth >= MAX_DEPTH {
            return Err(RtError::new(ErrorKind::Stack, format!("call depth exceeded {}", MAX_DEPTH)));
        }
        self.depth += 1;
        self.effect_stack.push(i);
        let mut heads = Vec::new();
        let mut args = args;
        let res = loop {
            self.prof.enter(&def.name, self.depth);
            // After `enter`, so the profiler's frames close as on any error.
            if let Err(e) = self.stopped() {
                break Err((e, heads.len() + 1));
            }
            // ConsTail is compiled only for calls with the right arity.
            let mut frame = args;
            frame.resize(def.frame, UNSET);
            match self.call_body(def, &mut frame) {
                Ok(Tail::Done(v)) => break Ok(v),
                Ok(Tail::Again(head, next)) => {
                    heads.push(head);
                    args = next;
                }
                // The innermost call failed: every call so far was open.
                Err(e) => break Err((e, heads.len() + 1)),
            }
        };
        self.effect_stack.pop();
        self.depth -= 1;
        let calls = heads.len() + 1;
        // The innermost cons runs in the caller of the innermost call. The
        // profiler's frames stay open so the time counts as this function's.
        let res = res.and_then(|v| self.cons_heads(heads, v));
        if self.prof.enabled {
            for _ in 0..calls {
                self.prof.exit(&def.name);
            }
        }
        res.map_err(|(mut e, open)| {
            for _ in 0..open {
                if e.trace.len() < 16 {
                    e.trace.push(def.name.clone());
                }
            }
            e
        })
    }

    /// `(cons h0 (cons h1 ... (cons hk v)))`: the conses a `ConsTail` loop
    /// deferred, innermost first. On error, also how many calls were open.
    fn cons_heads(&mut self, mut heads: Vec<Value>, v: Value) -> Result<Value, (RtError, usize)> {
        let Some(last) = heads.pop() else { return Ok(v) };
        let open = heads.len() + 1;
        let v = self.builtin(Builtin::Cons, vec![last, v]).map_err(|e| (e, open))?;
        if heads.is_empty() {
            return Ok(v);
        }
        for _ in &heads {
            self.prof.builtin(Builtin::Cons);
        }
        let Value::Vec(v) = v else { unreachable!("cons returns a vector") };
        let (v, copied) = Vector::new(heads).concat(v);
        self.copied(copied);
        Ok(Value::Vec(v))
    }

    fn call_body(&mut self, def: &Fn, frame: &mut [Value]) -> R<Tail> {
        for c in &def.requires {
            self.check_contract(def, "requires", c, frame)?;
        }
        let v = match self.eval_tail_seq(&def.body, frame)? {
            Tail::Done(v) => v,
            // Compiled only into functions without ensures.
            again => return Ok(again),
        };
        if !def.ensures.is_empty() {
            frame[def.result] = v.clone();
            for c in &def.ensures {
                self.check_contract(def, "ensures", c, frame)?;
            }
        }
        Ok(Tail::Done(v))
    }

    fn check_contract(&mut self, def: &Fn, which: &'static str, c: &Clause, frame: &mut [Value]) -> R<()> {
        let t0 = self.prof.enabled.then(Instant::now);
        self.prof.contract_checks += 1;
        let r = self.eval(&c.node, frame);
        if let Some(t) = t0 {
            let ns = t.elapsed().as_nanos();
            self.prof.contract_ns += ns;
            self.prof.clause(&def.name, which, c.index, ns);
        }
        match r? {
            Value::Bool(true) => Ok(()),
            Value::Bool(false) => Err(RtError::new(ErrorKind::Contract, format!("{} failed in {}: {}", which, def.name, flat(&c.src)))),
            o => Err(RtError::new(ErrorKind::Type, format!("contract must be bool, got {}", type_name(&o)))),
        }
    }

    fn copied(&mut self, c: Copied) {
        if c.alloc {
            self.prof.vec_alloc(c.elems);
        } else {
            self.prof.vec_elems += c.elems as u64;
        }
    }

    fn check_effect(&self, eff: &str, op: &str) -> R<()> {
        for &i in self.effect_stack.iter().rev() {
            let d = &self.prog.fns[i];
            if let Some(es) = &d.effects {
                if !es.iter().any(|e| e == eff) {
                    return Err(RtError::new(
                        ErrorKind::Effect,
                        format!("`{}` performs effect {}, but `{}` declares (:effects [{}])", op, eff, d.name, es.join(" ")),
                    ));
                }
            }
        }
        Ok(())
    }

    fn builtin(&mut self, b: Builtin, args: Vec<Value>) -> R<Value> {
        use Builtin as B;
        self.prof.builtin(b);
        let name = b.name();
        let ovf = || RtError::new(ErrorKind::Overflow, format!("i64 overflow in ({} ...)", name));
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
                    return Err(RtError::new(ErrorKind::Arity, "- expects at least 1 arg"));
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
                    return Err(RtError::new(ErrorKind::DivZero, format!("({} {} 0)", name, x)));
                }
                if b == B::Div { x.checked_div(y) } else { x.checked_rem_euclid(y) }.map(Value::Int).ok_or_else(ovf)
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
                    o => Err(RtError::new(ErrorKind::Type, format!("not expects bool, got {}", type_name(o)))),
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
                    return Err(RtError::new(ErrorKind::Bounds, format!("(get v {}) on vec of len {}", i, v.len())));
                }
                Ok(v[i as usize].clone())
            }
            B::Slice => {
                arity(name, &args, 3)?;
                let mut args = args;
                let v = take_vec(&mut args[0], name)?;
                let (lo, hi) = (int(&args[1], name)?, int(&args[2], name)?);
                if lo < 0 || hi < lo || hi as usize > v.len() {
                    return Err(RtError::new(ErrorKind::Bounds, format!("(slice v {} {}) on vec of len {}", lo, hi, v.len())));
                }
                let (v, copied) = v.slice(lo as usize, hi as usize);
                self.copied(copied);
                Ok(Value::Vec(v))
            }
            B::Rest => {
                arity(name, &args, 1)?;
                let mut args = args;
                let v = take_vec(&mut args[0], name)?;
                if v.is_empty() {
                    return Err(RtError::new(ErrorKind::Bounds, "(rest []) on empty vec"));
                }
                let (v, copied) = v.rest();
                self.copied(copied);
                Ok(Value::Vec(v))
            }
            B::Concat => {
                arity(name, &args, 2)?;
                let mut args = args;
                let xs = take_vec(&mut args[0], name)?;
                let (v, copied) = xs.concat(take_vec(&mut args[1], name)?);
                self.copied(copied);
                Ok(Value::Vec(v))
            }
            B::Cons => {
                arity(name, &args, 2)?;
                let mut args = args;
                let v = take_vec(&mut args[1], name)?;
                let x = std::mem::replace(&mut args[0], Value::Bool(false));
                let (v, copied) = v.cons(x);
                self.copied(copied);
                Ok(Value::Vec(v))
            }
            B::Range => {
                // The one builtin whose size comes from a number, not from
                // the vectors it is given: a stopped task must not build it.
                self.stopped()?;
                arity(name, &args, 1)?;
                let n = int(&args[0], name)?;
                if n < 0 {
                    return Err(RtError::new(ErrorKind::Bounds, format!("(range {}) needs n >= 0", n)));
                }
                let mut out: Vec<Value> = Vec::new();
                if out.try_reserve_exact(n as usize).is_err() {
                    return Err(RtError::new(ErrorKind::Alloc, format!("(range {}) needs more memory than can be allocated", n)));
                }
                out.extend((0..n).map(Value::Int));
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Vector::new(out)))
            }
            B::Vec => {
                self.prof.vec_alloc(args.len());
                Ok(Value::Vec(Vector::new(args)))
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
                            o => {
                                return Err(RtError::new(
                                    ErrorKind::Type,
                                    format!("filter predicate must return bool, got {}", type_name(&o)),
                                ))
                            }
                        }
                    }
                }
                self.prof.vec_alloc(out.len());
                Ok(Value::Vec(Vector::new(out)))
            }
            B::All => {
                arity(name, &args, 2)?;
                let v = vecv(&args[1], name)?;
                for x in v.iter() {
                    match self.apply(&args[0], vec![x.clone()])? {
                        Value::Bool(true) => {}
                        Value::Bool(false) => return Ok(Value::Bool(false)),
                        o => return Err(RtError::new(ErrorKind::Type, format!("all? predicate must return bool, got {}", type_name(&o)))),
                    }
                }
                Ok(Value::Bool(true))
            }
            B::Fold => {
                arity(name, &args, 3)?;
                let mut args = args;
                // Taken out of the arguments so the accumulator is not shared.
                let mut acc = std::mem::replace(&mut args[1], Value::Bool(false));
                let v = vecv(&args[2], name)?;
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
                        o => self.prog.show(o),
                    })
                    .collect();
                #[expect(clippy::print_stdout, reason = "print is the language's io effect; M2 has no other output channel yet")]
                {
                    println!("{}", s.join(" "));
                }
                Ok(Value::Bool(true))
            }
        }
    }
}

// Values and the compiled program cross threads in the fork-join (M2-5).
const _: () = {
    const fn send_sync<T: Send + Sync>() {}
    send_sync::<Value>();
    send_sync::<Program>();
};

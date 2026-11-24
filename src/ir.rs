//! The executable form of a `Module` (M2-1). Locals live in numbered frame
//! slots, every call names its callee kind, and a function carries only the
//! clauses `contracts::Checks` keeps: an erased clause is not compiled.

use crate::ast::{Budget, Clause as AstClause, Expr, ExprKind, FnIdx, Module};
use crate::builtin::Builtin;
use crate::contracts::Checks;
use crate::effects;
use crate::sexp::Sexp;
use std::collections::HashMap;
use std::sync::Arc;

/// An index into the frame of the function or lambda being evaluated.
pub type Slot = usize;

pub enum Node {
    Int(i64),
    Bool(bool),
    Str(Arc<str>),
    Local(Slot),
    /// The last read of a slot on its path: takes the value out, so a vector
    /// read here can be updated in place (M2-2).
    Move(Slot),
    /// A top-level function used as a value.
    Global(FnIdx),
    Builtin(Builtin),
    VecLit(Vec<Node>),
    If(Box<Node>, Box<Node>, Box<Node>),
    Let(Vec<(Slot, Node)>, Vec<Node>),
    Do(Vec<Node>),
    And(Vec<Node>),
    Or(Vec<Node>),
    Lambda(Arc<Lambda>),
    CallGlobal(FnIdx, Vec<Node>),
    CallBuiltin(Builtin, Vec<Node>),
    CallValue(Box<Node>, Vec<Node>),
    /// `(cons head (f args...))` in tail position of `f` itself, which has
    /// no ensures to check (D29). The runtime loops instead of recursing.
    ConsTail(Box<Node>, Vec<Node>),
    /// A call whose arguments include two or more calls of pure functions
    /// (D30). The runtime may evaluate the arguments from `split` on in a
    /// forked task while it evaluates the ones before.
    Fork(Box<Fork>),
}

pub struct Fork {
    /// A `CallGlobal` or `CallBuiltin`.
    pub call: Node,
    pub split: usize,
    /// The slots the forked arguments read, copied into the task's frame.
    /// `true` moves the value instead: the forked arguments read it last and
    /// the ones before do not read it.
    pub copy: Vec<(Slot, bool)>,
}

pub struct Lambda {
    /// Where each parameter goes in the lambda's frame.
    pub params: Vec<Slot>,
    /// `(slot in the enclosing frame, slot in the lambda's frame)`.
    pub captures: Vec<(Slot, Slot)>,
    pub frame: usize,
    pub body: Vec<Node>,
}

pub struct Clause {
    /// The clause's index in the source, as `check` numbers it.
    pub index: usize,
    pub src: Sexp,
    pub node: Node,
}

pub struct Fn {
    pub name: String,
    /// Parameters occupy slots `0..params`.
    pub params: usize,
    pub frame: usize,
    pub result: Slot,
    pub requires: Vec<Clause>,
    pub ensures: Vec<Clause>,
    /// `None` = no clause; `Some([])` = pure.
    pub effects: Option<Vec<String>>,
    pub budget: Option<Budget>,
    pub body: Vec<Node>,
}

pub struct Program {
    pub fns: Vec<Fn>,
    pub index: HashMap<String, FnIdx>,
}

impl Program {
    pub fn new(m: &Module, checks: &Checks) -> Program {
        // Inferred, not declared: a function is pure when nothing it can
        // reach performs an effect, including through closures.
        let pure: Vec<bool> = effects::check(m).0.inferred.iter().map(|fx| fx.is_empty()).collect();
        let fns = m
            .fns
            .iter()
            .enumerate()
            .map(|(i, d)| {
                let mut c = Compiler { frames: vec![Frame::default()] };
                for p in &d.params {
                    c.bind(&p.name);
                }
                let kept = |c: &mut Compiler, cs: &[AstClause], keep: &[bool]| -> Vec<Clause> {
                    cs.iter()
                        .enumerate()
                        .filter(|(j, _)| keep[*j])
                        .map(|(index, cl)| Clause { index, src: cl.src.clone(), node: c.expr(&cl.expr) })
                        .collect()
                };
                let mut requires = kept(&mut c, &d.spec.requires, &checks.requires[i]);
                let mut body = c.exprs(&d.body);
                let result = c.bind("result");
                let mut ensures = kept(&mut c, &d.spec.ensures, &checks.ensures[i]);
                // Clauses run before and after the body in this order, so a
                // parameter an ensures reads is never moved by the body.
                let mut live = vec![false; c.frames[0].size];
                for n in ensures
                    .iter_mut()
                    .rev()
                    .map(|c| &mut c.node)
                    .chain(body.iter_mut().rev())
                    .chain(requires.iter_mut().rev().map(|c| &mut c.node))
                {
                    last_uses(n, &mut live);
                }
                // An ensures needs the result of each recursive call, so a
                // function that checks one recurses as written.
                if ensures.is_empty() {
                    if let Some(n) = body.last_mut() {
                        cons_tails(n, i, d.params.len());
                    }
                }
                for n in &mut body {
                    forks(n, &pure);
                }
                Fn {
                    name: d.name.clone(),
                    params: d.params.len(),
                    frame: c.frames[0].size,
                    result,
                    requires,
                    ensures,
                    effects: d.spec.effects.as_ref().map(|es| es.iter().cloned().collect()),
                    budget: d.spec.budget.clone(),
                    body,
                }
            })
            .collect();
        Program { fns, index: m.index.clone() }
    }
}

#[derive(Default)]
struct Frame {
    /// Names in scope, innermost last.
    names: Vec<(String, Slot)>,
    /// Names bound outside and copied in when the lambda is created.
    captured: Vec<(String, Slot)>,
    size: usize,
    captures: Vec<(Slot, Slot)>,
}

/// One frame per function or lambda being compiled, innermost last.
struct Compiler {
    frames: Vec<Frame>,
}

impl Compiler {
    fn bind(&mut self, name: &str) -> Slot {
        let f = self.frames.last_mut().expect("a frame is open");
        f.size += 1;
        f.names.push((name.to_string(), f.size - 1));
        f.size - 1
    }

    /// The slot of `name` in frame `depth`, capturing it from enclosing
    /// frames when it is bound outside.
    fn slot(&mut self, name: &str, depth: usize) -> Slot {
        let f = &self.frames[depth];
        if let Some((_, s)) = f.names.iter().rev().chain(&f.captured).find(|(n, _)| n == name) {
            return *s;
        }
        assert!(depth > 0, "lower resolved every local, `{}` is unbound", name);
        let outer = self.slot(name, depth - 1);
        let f = &mut self.frames[depth];
        f.size += 1;
        let own = f.size - 1;
        f.captures.push((outer, own));
        f.captured.push((name.to_string(), own));
        own
    }

    fn exprs(&mut self, es: &[Expr]) -> Vec<Node> {
        es.iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: &Expr) -> Node {
        match &e.kind {
            ExprKind::Int(n) => Node::Int(*n),
            ExprKind::Bool(b) => Node::Bool(*b),
            ExprKind::Str(s) => Node::Str(s.as_str().into()),
            ExprKind::Local(n) => Node::Local(self.slot(n, self.frames.len() - 1)),
            ExprKind::Global(i) => Node::Global(*i),
            ExprKind::Builtin(b) => Node::Builtin(*b),
            ExprKind::VecLit(items) => Node::VecLit(self.exprs(items)),
            ExprKind::If(c, t, f) => Node::If(Box::new(self.expr(c)), Box::new(self.expr(t)), Box::new(self.expr(f))),
            ExprKind::Let(binds, body) => {
                let depth = self.frames.last().expect("a frame is open").names.len();
                // Each value sees the bindings before it.
                let binds = binds
                    .iter()
                    .map(|(n, v)| {
                        let v = self.expr(v);
                        (self.bind(n), v)
                    })
                    .collect();
                let body = self.exprs(body);
                self.frames.last_mut().expect("a frame is open").names.truncate(depth);
                Node::Let(binds, body)
            }
            ExprKind::Lambda(ps, body) => {
                self.frames.push(Frame::default());
                let params = ps.iter().map(|p| self.bind(&p.name)).collect();
                let mut body = self.exprs(body);
                let f = self.frames.pop().expect("pushed above");
                let mut live = vec![false; f.size];
                for n in body.iter_mut().rev() {
                    last_uses(n, &mut live);
                }
                Node::Lambda(Arc::new(Lambda { params, captures: f.captures, frame: f.size, body }))
            }
            ExprKind::Do(es) => Node::Do(self.exprs(es)),
            ExprKind::And(es) => Node::And(self.exprs(es)),
            ExprKind::Or(es) => Node::Or(self.exprs(es)),
            ExprKind::Call(f, args) => match &f.kind {
                ExprKind::Global(i) => Node::CallGlobal(*i, self.exprs(args)),
                ExprKind::Builtin(b) => Node::CallBuiltin(*b, self.exprs(args)),
                _ => {
                    let f = self.expr(f);
                    Node::CallValue(Box::new(f), self.exprs(args))
                }
            },
        }
    }
}

/// Walks `n` backwards from the end of its evaluation, where `live[s]` says
/// slot `s` is read later, and turns each read that is the last on its path
/// into a `Move`. Leaves `live` as it is before `n` runs. No node runs twice
/// in one frame, so a moved slot is never read again.
fn last_uses(n: &mut Node, live: &mut [bool]) {
    match n {
        Node::Int(_) | Node::Bool(_) | Node::Str(_) | Node::Global(_) | Node::Builtin(_) | Node::Move(_) => {}
        Node::Local(s) => {
            let s = *s;
            if !live[s] {
                live[s] = true;
                *n = Node::Move(s);
            }
        }
        Node::If(c, t, f) => {
            let mut other = live.to_vec();
            last_uses(t, live);
            last_uses(f, &mut other);
            for (l, o) in live.iter_mut().zip(other) {
                *l |= o;
            }
            last_uses(c, live);
        }
        Node::Let(binds, body) => {
            seq(body, live);
            for (slot, v) in binds.iter_mut().rev() {
                live[*slot] = false;
                last_uses(v, live);
            }
        }
        Node::VecLit(es) | Node::Do(es) | Node::And(es) | Node::Or(es) | Node::CallGlobal(_, es) | Node::CallBuiltin(_, es) => {
            seq(es, live)
        }
        Node::CallValue(f, args) | Node::ConsTail(f, args) => {
            seq(args, live);
            last_uses(f, live);
        }
        // Inserted after this pass.
        Node::Fork(f) => last_uses(&mut f.call, live),
        // Creating a closure copies the captured slots, which reads them.
        Node::Lambda(l) => {
            for (outer, _) in &l.captures {
                live[*outer] = true;
            }
        }
    }
}

/// Turns each `(cons head (me args...))` in tail position of `n` into a
/// `ConsTail`. Runs after `last_uses`, which it leaves valid: the head and
/// the arguments are evaluated in the same order as before.
fn cons_tails(n: &mut Node, me: FnIdx, params: usize) {
    match n {
        Node::If(_, t, f) => {
            cons_tails(t, me, params);
            cons_tails(f, me, params);
        }
        Node::Let(_, body) | Node::Do(body) => {
            if let Some(last) = body.last_mut() {
                cons_tails(last, me, params);
            }
        }
        Node::CallBuiltin(Builtin::Cons, args) if matches!(args.as_slice(), [_, Node::CallGlobal(f, a)] if *f == me && a.len() == params) =>
        {
            let Some(Node::CallGlobal(_, call)) = args.pop() else { unreachable!("matched above") };
            let head = args.pop().expect("matched above");
            *n = Node::ConsTail(Box::new(head), call);
        }
        _ => {}
    }
}

/// Wraps each call in `n` whose arguments are all pure and include two or
/// more calls of pure functions in a `Fork`, outside lambdas. Runs after
/// `last_uses`: it reads which slots are moved, and it keeps the order in
/// which each side evaluates its arguments.
fn forks(n: &mut Node, pure: &[bool]) {
    match n {
        Node::CallGlobal(_, args) | Node::CallBuiltin(_, args) => {
            for a in args.iter_mut() {
                forks(a, pure);
            }
            let heavy: Vec<usize> = (0..args.len()).filter(|&k| pure_call(&args[k], pure)).collect();
            if heavy.len() < 2 || !args.iter().all(|a| is_pure(a, pure)) {
                return;
            }
            let split = heavy[heavy.len() / 2];
            let (before, after) = args.split_at(split);
            let mut read_before = Vec::new();
            for a in before {
                reads(a, &mut read_before);
            }
            let mut read_after = Vec::new();
            for a in after {
                reads(a, &mut read_after);
            }
            let mut copy: Vec<(Slot, bool)> = Vec::new();
            for (s, moved) in read_after {
                let take = moved && !read_before.iter().any(|(b, _)| *b == s);
                match copy.iter_mut().find(|(c, _)| *c == s) {
                    Some(c) => c.1 |= take,
                    None => copy.push((s, take)),
                }
            }
            let call = std::mem::replace(n, Node::Bool(false));
            *n = Node::Fork(Box::new(Fork { call, split, copy }));
        }
        Node::VecLit(es) | Node::Do(es) | Node::And(es) | Node::Or(es) => {
            for e in es {
                forks(e, pure);
            }
        }
        Node::If(c, t, f) => {
            forks(c, pure);
            forks(t, pure);
            forks(f, pure);
        }
        Node::Let(binds, body) => {
            for (_, v) in binds.iter_mut() {
                forks(v, pure);
            }
            for e in body {
                forks(e, pure);
            }
        }
        Node::CallValue(f, args) | Node::ConsTail(f, args) => {
            forks(f, pure);
            for a in args {
                forks(a, pure);
            }
        }
        Node::Fork(f) => forks(&mut f.call, pure),
        Node::Int(_)
        | Node::Bool(_)
        | Node::Str(_)
        | Node::Local(_)
        | Node::Move(_)
        | Node::Global(_)
        | Node::Builtin(_)
        | Node::Lambda(_) => {}
    }
}

/// A call of a pure top-level function: the work worth a task.
fn pure_call(n: &Node, pure: &[bool]) -> bool {
    match n {
        Node::CallGlobal(f, _) => pure[*f],
        Node::Fork(f) => pure_call(&f.call, pure),
        _ => false,
    }
}

/// Evaluating `n` performs no effect and calls no function value that
/// might, so it may run in another order or on another thread. Calling a
/// function value, or passing `map` and the like one that is not written
/// out (a lambda, a top-level function or a builtin), may print.
fn is_pure(n: &Node, pure: &[bool]) -> bool {
    let all = |es: &[Node]| es.iter().all(|e| is_pure(e, pure));
    match n {
        Node::Int(_) | Node::Bool(_) | Node::Str(_) | Node::Local(_) | Node::Move(_) => true,
        Node::Global(f) => pure[*f],
        Node::Builtin(b) => *b != Builtin::Print,
        Node::Lambda(l) => all(&l.body),
        Node::VecLit(es) | Node::Do(es) | Node::And(es) | Node::Or(es) => all(es),
        Node::If(c, t, f) => is_pure(c, pure) && is_pure(t, pure) && is_pure(f, pure),
        Node::Let(binds, body) => binds.iter().all(|(_, v)| is_pure(v, pure)) && all(body),
        Node::CallGlobal(f, args) => pure[*f] && all(args),
        Node::CallBuiltin(b, args) => {
            // Each of these calls its first argument.
            let calls_first = matches!(b, Builtin::Map | Builtin::Fold | Builtin::Filter | Builtin::All);
            let known = |a: &Node| matches!(a, Node::Lambda(_) | Node::Global(_) | Node::Builtin(_));
            *b != Builtin::Print && all(args) && (!calls_first || args.first().is_none_or(known))
        }
        Node::Fork(f) => is_pure(&f.call, pure),
        Node::CallValue(..) | Node::ConsTail(..) => false,
    }
}

/// The slots `n` reads, and whether the read moves the value.
fn reads(n: &Node, out: &mut Vec<(Slot, bool)>) {
    let all = |es: &[Node], out: &mut Vec<(Slot, bool)>| {
        for e in es {
            reads(e, out);
        }
    };
    match n {
        Node::Local(s) => out.push((*s, false)),
        Node::Move(s) => out.push((*s, true)),
        Node::Int(_) | Node::Bool(_) | Node::Str(_) | Node::Global(_) | Node::Builtin(_) => {}
        Node::Lambda(l) => out.extend(l.captures.iter().map(|(outer, _)| (*outer, false))),
        Node::VecLit(es) | Node::Do(es) | Node::And(es) | Node::Or(es) | Node::CallGlobal(_, es) | Node::CallBuiltin(_, es) => all(es, out),
        Node::If(c, t, f) => {
            reads(c, out);
            reads(t, out);
            reads(f, out);
        }
        Node::Let(binds, body) => {
            for (_, v) in binds {
                reads(v, out);
            }
            all(body, out);
        }
        Node::CallValue(f, args) | Node::ConsTail(f, args) => {
            reads(f, out);
            all(args, out);
        }
        Node::Fork(f) => reads(&f.call, out),
    }
}

fn seq(es: &mut [Node], live: &mut [bool]) {
    for e in es.iter_mut().rev() {
        last_uses(e, live);
    }
}

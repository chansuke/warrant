//! The executable form of a `Module` (M2-1). Locals live in numbered frame
//! slots, every call names its callee kind, and a function carries only the
//! clauses `contracts::Checks` keeps: an erased clause is not compiled.

use crate::ast::{Budget, Clause as AstClause, Expr, ExprKind, FnIdx, Module};
use crate::builtin::Builtin;
use crate::contracts::Checks;
use crate::sexp::Sexp;
use std::collections::HashMap;
use std::rc::Rc;

/// An index into the frame of the function or lambda being evaluated.
pub type Slot = usize;

pub enum Node {
    Int(i64),
    Bool(bool),
    Str(Rc<str>),
    Local(Slot),
    /// A top-level function used as a value.
    Global(FnIdx),
    Builtin(Builtin),
    VecLit(Vec<Node>),
    If(Box<Node>, Box<Node>, Box<Node>),
    Let(Vec<(Slot, Node)>, Vec<Node>),
    Do(Vec<Node>),
    And(Vec<Node>),
    Or(Vec<Node>),
    Lambda(Rc<Lambda>),
    CallGlobal(FnIdx, Vec<Node>),
    CallBuiltin(Builtin, Vec<Node>),
    CallValue(Box<Node>, Vec<Node>),
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
                let requires = kept(&mut c, &d.spec.requires, &checks.requires[i]);
                let body = c.exprs(&d.body);
                let result = c.bind("result");
                let ensures = kept(&mut c, &d.spec.ensures, &checks.ensures[i]);
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
                let body = self.exprs(body);
                let f = self.frames.pop().expect("pushed above");
                Node::Lambda(Rc::new(Lambda { params, captures: f.captures, frame: f.size, body }))
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

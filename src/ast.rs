//! The lowered program that static passes read: names resolved, clauses
//! separated from the body, every node positioned. The interpreter still
//! evaluates the `Sexp` bodies kept beside each declaration.

use crate::builtin::Builtin;
use crate::diag::{Diag, ErrorKind};
use crate::sexp::{flat, Pos, Sexp, SpanTree};
use std::collections::{BTreeSet, HashMap};

pub type EffectSet = BTreeSet<String>;
pub type ExprId = usize;
pub type FnIdx = usize;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    I64,
    Bool,
    Str,
    Vec(Box<Type>),
    /// Parameter types, return type, and the effects a call performs.
    Fn(Vec<Type>, Box<Type>, EffectSet),
}

impl Type {
    pub fn to_sexp(&self) -> String {
        match self {
            Type::I64 => "i64".into(),
            Type::Bool => "Bool".into(),
            Type::Str => "Str".into(),
            Type::Vec(t) => format!("(Vec {})", t.to_sexp()),
            Type::Fn(ps, r, effs) => {
                let ps: Vec<String> = ps.iter().map(Type::to_sexp).collect();
                let effs = if effs.is_empty() { String::new() } else { format!(" :effects {}", effects_sexp(effs)) };
                format!("(Fn [{}] {}{})", ps.join(" "), r.to_sexp(), effs)
            }
        }
    }
}

pub fn effects_sexp(effs: &EffectSet) -> String {
    format!("[{}]", effs.iter().cloned().collect::<Vec<_>>().join(" "))
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: ExprId,
    pub at: Pos,
    pub kind: ExprKind,
}

impl Expr {
    pub fn children(&self) -> Vec<&Expr> {
        match &self.kind {
            ExprKind::VecLit(v) | ExprKind::Do(v) | ExprKind::And(v) | ExprKind::Or(v) => v.iter().collect(),
            ExprKind::If(c, t, f) => vec![c, t, f],
            ExprKind::Let(bs, body) => bs.iter().map(|(_, e)| e).chain(body).collect(),
            ExprKind::Lambda(_, body) => body.iter().collect(),
            ExprKind::Call(f, args) => std::iter::once(&**f).chain(args).collect(),
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Local(_) | ExprKind::Global(_) | ExprKind::Builtin(_) => {
                Vec::new()
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(i64),
    Bool(bool),
    Str(String),
    Local(String),
    Global(FnIdx),
    Builtin(Builtin),
    VecLit(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Vec<(String, Expr)>, Vec<Expr>),
    Lambda(Vec<LambdaParam>, Vec<Expr>),
    Do(Vec<Expr>),
    And(Vec<Expr>),
    Or(Vec<Expr>),
    Call(Box<Expr>, Vec<Expr>),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub at: Pos,
}

#[derive(Clone, Debug)]
pub struct LambdaParam {
    pub name: String,
    pub ty: Option<Type>,
    pub at: Pos,
}

#[derive(Clone, Debug)]
pub struct Budget {
    pub wall_ms: Option<f64>,
}

#[derive(Clone, Debug)]
pub struct Clause {
    pub expr: Expr,
    pub src: Sexp,
}

#[derive(Clone, Debug, Default)]
pub struct Spec {
    /// `None` = no clause; `Some(empty)` = declared pure.
    pub effects: Option<EffectSet>,
    pub requires: Vec<Clause>,
    pub ensures: Vec<Clause>,
    pub budget: Option<Budget>,
}

#[derive(Clone, Debug)]
pub struct FnDecl {
    pub name: String,
    pub at: Pos,
    pub params: Vec<Param>,
    pub ret: Type,
    pub spec: Spec,
    pub body: Vec<Expr>,
    pub body_src: Vec<Sexp>,
    /// The whole canonical `(defn ...)` form.
    pub source: Sexp,
}

#[derive(Debug)]
pub struct Module {
    /// Source order.
    pub fns: Vec<FnDecl>,
    pub index: HashMap<String, FnIdx>,
    /// Every `ExprId` is below this.
    pub n_exprs: usize,
}

impl FnDecl {
    /// Body and clauses.
    pub fn exprs(&self) -> impl Iterator<Item = &Expr> {
        self.spec.requires.iter().chain(&self.spec.ensures).map(|c| &c.expr).chain(&self.body)
    }

    /// Top-level functions this one refers to, called or passed as values.
    pub fn callees(&self) -> Vec<FnIdx> {
        let mut out = Vec::new();
        let mut stack: Vec<&Expr> = self.exprs().collect();
        while let Some(e) = stack.pop() {
            if let ExprKind::Global(i) = e.kind {
                out.push(i);
            }
            stack.extend(e.children());
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

impl Module {
    pub fn get(&self, name: &str) -> Option<&FnDecl> {
        self.index.get(name).map(|&i| &self.fns[i])
    }

    /// Whether each function can reach itself through the call graph. Their
    /// termination is assumed, not proved, in M1.
    pub fn recursive(&self) -> Vec<bool> {
        let edges: Vec<Vec<FnIdx>> = self.fns.iter().map(FnDecl::callees).collect();
        (0..self.fns.len())
            .map(|start| {
                let mut seen = vec![false; self.fns.len()];
                let mut stack = edges[start].clone();
                while let Some(i) = stack.pop() {
                    if i == start {
                        return true;
                    }
                    if !std::mem::replace(&mut seen[i], true) {
                        stack.extend(&edges[i]);
                    }
                }
                false
            })
            .collect()
    }
}

type R<T> = Result<T, Diag>;

fn syntax(at: Pos, msg: impl Into<String>) -> Diag {
    Diag::new(ErrorKind::Syntax, at, msg)
}

fn sym(e: &Sexp) -> Option<&str> {
    match e {
        Sexp::Sym(s) => Some(s),
        _ => None,
    }
}

pub fn lower(forms: &[Sexp], spans: &[SpanTree]) -> R<Module> {
    let mut index = HashMap::new();
    for (f, sp) in forms.iter().zip(spans) {
        let Sexp::List(items) = f else { return Err(syntax(sp.at, format!("top-level form must be (defn ...), got `{}`", flat(f)))) };
        if items.first().and_then(sym) != Some("defn") {
            return Err(syntax(sp.at, format!("top-level form must be (defn ...), got `{}`", flat(f))));
        }
        let Some(Sexp::Sym(name)) = items.get(1) else { return Err(syntax(sp.at, "defn needs a name")) };
        if index.insert(name.clone(), index.len()).is_some() {
            return Err(Diag::new(ErrorKind::Load, sp.kids[1].at, format!("duplicate definition of {}", name)));
        }
    }
    let mut lw = Lowerer { globals: &index, next_id: 0, scope: Vec::new() };
    let mut fns = Vec::with_capacity(forms.len());
    for (f, sp) in forms.iter().zip(spans) {
        fns.push(lw.defn(f, sp)?);
    }
    let n_exprs = lw.next_id;
    Ok(Module { fns, index, n_exprs })
}

struct Lowerer<'m> {
    globals: &'m HashMap<String, FnIdx>,
    next_id: ExprId,
    scope: Vec<String>,
}

impl Lowerer<'_> {
    fn defn(&mut self, form: &Sexp, sp: &SpanTree) -> R<FnDecl> {
        let Sexp::List(items) = form else { unreachable!("checked in lower") };
        let kids = &sp.kids;
        let name = sym(&items[1]).expect("checked in lower").to_string();
        let Some(Sexp::Vector(ps)) = items.get(2) else {
            return Err(syntax(sp.at, format!("defn {} needs a [params] vector", name)));
        };
        let params: Vec<Param> = params(ps, &kids[2])?
            .into_iter()
            .map(|p| match p.ty {
                Some(ty) => Ok(Param { name: p.name, ty, at: p.at }),
                None => Err(Diag::new(ErrorKind::Type, p.at, format!("parameter `{}` of {} needs a type: `{} : T`", p.name, name, p.name))),
            })
            .collect::<R<_>>()?;
        if items.get(3).and_then(sym) != Some("->") || items.get(4).is_none() {
            return Err(Diag::new(ErrorKind::Type, kids[1].at, format!("defn {} needs a return type: `[params] -> T`", name)));
        }
        let ret = parse_type(&items[4], &kids[4])?;

        self.scope = params.iter().map(|p| p.name.clone()).collect();
        let mut spec = Spec::default();
        let (mut body, mut body_src) = (Vec::new(), Vec::new());
        for (it, isp) in items[5..].iter().zip(&kids[5..]) {
            match it {
                Sexp::List(cl) if matches!(cl.first(), Some(Sexp::Kw(_))) => self.clause(&name, cl, isp, &mut spec)?,
                _ => {
                    body.push(self.expr(it, isp)?);
                    body_src.push(it.clone());
                }
            }
        }
        if body.is_empty() {
            return Err(syntax(sp.at, format!("defn {} has no body", name)));
        }
        Ok(FnDecl { name, at: sp.at, params, ret, spec, body, body_src, source: form.clone() })
    }

    fn clause(&mut self, fname: &str, cl: &[Sexp], sp: &SpanTree, spec: &mut Spec) -> R<()> {
        let Sexp::Kw(k) = &cl[0] else { unreachable!("caller matched a keyword head") };
        let args = cl[1..].iter().zip(&sp.kids[1..]);
        match k.as_str() {
            "effects" => match cl.get(1) {
                Some(Sexp::Vector(es)) if cl.len() == 2 => spec.effects = Some(effect_set(es, &sp.kids[1])?),
                _ => return Err(syntax(sp.at, "write effects as (:effects [io ...])")),
            },
            "requires" => {
                for (e, esp) in args {
                    spec.requires.push(Clause { expr: self.expr(e, esp)?, src: e.clone() });
                }
            }
            "ensures" => {
                self.scope.push("result".into());
                for (e, esp) in args {
                    spec.ensures.push(Clause { expr: self.expr(e, esp)?, src: e.clone() });
                }
                self.scope.pop();
            }
            "budget" => spec.budget = Some(budget(&cl[1..], &sp.kids[1..])?),
            other => return Err(syntax(sp.at, format!("unknown clause :{} in {}", other, fname))),
        }
        Ok(())
    }

    fn node(&mut self, at: Pos, kind: ExprKind) -> Expr {
        self.next_id += 1;
        Expr { id: self.next_id - 1, at, kind }
    }

    fn resolve(&self, s: &str, at: Pos) -> R<ExprKind> {
        if self.scope.iter().any(|n| n == s) {
            return Ok(ExprKind::Local(s.to_string()));
        }
        if let Some(&i) = self.globals.get(s) {
            return Ok(ExprKind::Global(i));
        }
        if let Some(b) = Builtin::from_name(s) {
            return Ok(ExprKind::Builtin(b));
        }
        Err(Diag::new(ErrorKind::Unbound, at, format!("unbound symbol `{}`", s)))
    }

    fn exprs(&mut self, es: &[Sexp], sps: &[SpanTree]) -> R<Vec<Expr>> {
        es.iter().zip(sps).map(|(e, sp)| self.expr(e, sp)).collect()
    }

    fn body(&mut self, es: &[Sexp], sps: &[SpanTree], at: Pos, what: &str) -> R<Vec<Expr>> {
        if es.is_empty() {
            return Err(syntax(at, format!("{} has no body", what)));
        }
        self.exprs(es, sps)
    }

    fn expr(&mut self, e: &Sexp, sp: &SpanTree) -> R<Expr> {
        let at = sp.at;
        let kind = match e {
            Sexp::Int(n) => ExprKind::Int(*n),
            Sexp::Bool(b) => ExprKind::Bool(*b),
            Sexp::Str(s) => ExprKind::Str(s.clone()),
            Sexp::Kw(k) => return Err(syntax(at, format!(":{} is not an expression", k))),
            Sexp::Sym(s) => self.resolve(s, at)?,
            Sexp::Vector(items) => ExprKind::VecLit(self.exprs(items, &sp.kids)?),
            Sexp::List(items) => {
                let Some(head) = items.first() else { return Err(syntax(at, "() is not an expression")) };
                let kids = &sp.kids;
                match sym(head) {
                    Some("if") => {
                        if items.len() != 4 {
                            return Err(syntax(at, "(if cond then else)"));
                        }
                        let Ok([c, t, f]) = <[Expr; 3]>::try_from(self.exprs(&items[1..], &kids[1..])?) else {
                            unreachable!("(if) has three operands, checked above")
                        };
                        ExprKind::If(Box::new(c), Box::new(t), Box::new(f))
                    }
                    Some("let") => {
                        let Some(Sexp::Vector(bs)) = items.get(1) else {
                            return Err(syntax(at, "(let [name expr ...] body ...)"));
                        };
                        if bs.len() % 2 != 0 {
                            return Err(syntax(kids[1].at, "let bindings must come in pairs"));
                        }
                        let depth = self.scope.len();
                        let mut binds = Vec::new();
                        for (pair, psp) in bs.chunks(2).zip(kids[1].kids.chunks(2)) {
                            let Sexp::Sym(n) = &pair[0] else {
                                return Err(syntax(psp[0].at, "let binding name must be a symbol"));
                            };
                            let v = self.expr(&pair[1], &psp[1])?;
                            self.scope.push(n.clone());
                            binds.push((n.clone(), v));
                        }
                        let body = self.body(&items[2..], &kids[2..], at, "let");
                        self.scope.truncate(depth);
                        ExprKind::Let(binds, body?)
                    }
                    Some("fn") => {
                        let Some(Sexp::Vector(ps)) = items.get(1) else {
                            return Err(syntax(at, "(fn [params] body ...)"));
                        };
                        let ps = params(ps, &kids[1])?;
                        let depth = self.scope.len();
                        self.scope.extend(ps.iter().map(|p| p.name.clone()));
                        let body = self.body(&items[2..], &kids[2..], at, "fn");
                        self.scope.truncate(depth);
                        ExprKind::Lambda(ps, body?)
                    }
                    Some("do") => ExprKind::Do(self.body(&items[1..], &kids[1..], at, "do")?),
                    Some("and") => ExprKind::And(self.exprs(&items[1..], &kids[1..])?),
                    Some("or") => ExprKind::Or(self.exprs(&items[1..], &kids[1..])?),
                    Some("defn") => return Err(syntax(at, "defn is only allowed at top level")),
                    _ => {
                        let f = self.expr(head, &kids[0])?;
                        ExprKind::Call(Box::new(f), self.exprs(&items[1..], &kids[1..])?)
                    }
                }
            }
        };
        Ok(self.node(at, kind))
    }
}

/// `[a : T b c : U]`. Types are optional here; `defn` demands them.
fn params(v: &[Sexp], sp: &SpanTree) -> R<Vec<LambdaParam>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < v.len() {
        let at = sp.kids[i].at;
        match &v[i] {
            Sexp::Sym(s) if s != ":" => {
                let mut ty = None;
                i += 1;
                if v.get(i).and_then(sym) == Some(":") {
                    let Some(t) = v.get(i + 1) else {
                        return Err(syntax(at, format!("parameter `{}` has `:` but no type", s)));
                    };
                    ty = Some(parse_type(t, &sp.kids[i + 1])?);
                    i += 2;
                }
                out.push(LambdaParam { name: s.clone(), ty, at });
            }
            other => return Err(syntax(at, format!("bad parameter `{}`", flat(other)))),
        }
    }
    Ok(out)
}

fn effect_set(es: &[Sexp], sp: &SpanTree) -> R<EffectSet> {
    es.iter()
        .zip(&sp.kids)
        .map(|(e, esp)| sym(e).map(str::to_string).ok_or_else(|| syntax(esp.at, "effects must be symbols")))
        .collect()
}

fn budget(xs: &[Sexp], sps: &[SpanTree]) -> R<Budget> {
    let mut b = Budget { wall_ms: None };
    for (x, sp) in xs.iter().zip(sps) {
        match x {
            Sexp::List(v) if v.len() == 2 && sym(&v[0]) == Some("wall-ms") => match &v[1] {
                Sexp::Int(n) => b.wall_ms = Some(*n as f64),
                _ => return Err(syntax(sp.at, "(wall-ms N) needs an integer")),
            },
            _ => return Err(syntax(sp.at, format!("unknown budget item `{}`", flat(x)))),
        }
    }
    Ok(b)
}

pub fn parse_type(e: &Sexp, sp: &SpanTree) -> R<Type> {
    let bad = || Diag::new(ErrorKind::Type, sp.at, format!("unknown type `{}`; expected i64, Bool, Str, (Vec T) or (Fn [T ...] R)", flat(e)));
    match e {
        Sexp::Sym(s) => match s.as_str() {
            "i64" => Ok(Type::I64),
            "Bool" => Ok(Type::Bool),
            "Str" => Ok(Type::Str),
            _ => Err(bad()),
        },
        Sexp::List(v) => match (v.first().and_then(sym), v.len()) {
            (Some("Vec"), 2) => Ok(Type::Vec(Box::new(parse_type(&v[1], &sp.kids[1])?))),
            (Some("Fn"), 3 | 5) => {
                let Sexp::Vector(ps) = &v[1] else { return Err(bad()) };
                let ps = ps.iter().zip(&sp.kids[1].kids).map(|(p, psp)| parse_type(p, psp)).collect::<R<_>>()?;
                let ret = parse_type(&v[2], &sp.kids[2])?;
                let effs = match v.get(3..) {
                    Some([Sexp::Kw(k), Sexp::Vector(es)]) if k == "effects" => effect_set(es, &sp.kids[4])?,
                    Some([]) => EffectSet::new(),
                    _ => return Err(bad()),
                };
                Ok(Type::Fn(ps, Box::new(ret), effs))
            }
            _ => Err(bad()),
        },
        _ => Err(bad()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_all_spanned;

    fn lower_src(src: &str) -> R<Module> {
        let (f, s) = parse_all_spanned(src).unwrap();
        lower(&f, &s)
    }

    fn err_at(src: &str) -> (&'static str, usize, usize) {
        let d = lower_src(src).unwrap_err();
        let at = d.at.expect("positioned");
        (d.kind.as_str(), at.line, at.col)
    }

    #[test]
    fn resolves_locals_globals_and_builtins() {
        let m = lower_src("(defn f [len : i64] -> i64 (g len))\n(defn g [x : i64] -> i64 (+ x 1))").unwrap();
        let ExprKind::Call(head, args) = &m.fns[0].body[0].kind else { panic!() };
        assert!(matches!(head.kind, ExprKind::Global(1)));
        assert!(matches!(&args[0].kind, ExprKind::Local(n) if n == "len"));
        let ExprKind::Call(head, _) = &m.fns[1].body[0].kind else { panic!() };
        assert!(matches!(head.kind, ExprKind::Builtin(Builtin::Add)));
    }

    #[test]
    fn result_is_bound_only_in_ensures() {
        assert!(lower_src("(defn f [x : i64] -> i64 (:ensures (>= result x)) x)").is_ok());
        assert_eq!(err_at("(defn f [x : i64] -> i64\n  (:requires (>= result x)) x)"), ("unbound", 2, 18));
    }

    #[test]
    fn unbound_symbols_are_positioned() {
        assert_eq!(err_at("(defn f [] -> i64\n  (let [y 1] (+ y z)))"), ("unbound", 2, 19));
    }

    #[test]
    fn defn_needs_parameter_and_return_types() {
        assert_eq!(err_at("(defn f [x] -> i64 x)"), ("type", 1, 10));
        assert_eq!(err_at("(defn f [x : i64] x)"), ("type", 1, 7));
        assert_eq!(err_at("(defn f [x : int] -> i64 x)"), ("type", 1, 14));
    }

    #[test]
    fn finds_direct_and_mutual_recursion() {
        let m = lower_src(
            "(defn even [n : i64] -> Bool (if (= n 0) true (odd (- n 1))))
             (defn odd [n : i64] -> Bool (if (= n 0) false (even (- n 1))))
             (defn fact [n : i64] -> i64 (if (= n 0) 1 (* n (fact (- n 1)))))
             (defn main [] -> Bool (even 4))",
        )
        .unwrap();
        assert_eq!(m.recursive(), [true, true, true, false]);
    }

    #[test]
    fn parses_function_types_with_latent_effects() {
        let m = lower_src("(defn f [g : (Fn [i64 Bool] Str :effects [io])] -> (Fn [] i64) g)").unwrap();
        assert_eq!(m.fns[0].params[0].ty.to_sexp(), "(Fn [i64 Bool] Str :effects [io])");
        assert_eq!(m.fns[0].ret.to_sexp(), "(Fn [] i64)");
    }
}

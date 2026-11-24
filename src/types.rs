//! Static type checking (M1-2). Monomorphic inference inside each function:
//! `defn` signatures are annotated, `let` and `fn` are inferred by
//! unification. Polymorphic builtins (`get : (Vec a) i64 -> a`) are
//! instantiated with fresh variables at every use.
//! Effects are not part of these types; `effects` checks them separately.

use crate::ast::{Expr, ExprId, ExprKind, FnDecl, Module, Type};
use crate::builtin::Builtin;
use crate::diag::{Diag, ErrorKind};
use crate::sexp::Pos;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    I64,
    Bool,
    Str,
    Vec(Box<Ty>),
    Fn(Vec<Ty>, Box<Ty>),
    Var(u32),
}

impl Ty {
    pub fn from_type(t: &Type) -> Ty {
        match t {
            Type::I64 => Ty::I64,
            Type::Bool => Ty::Bool,
            Type::Str => Ty::Str,
            Type::Vec(t) => Ty::Vec(Box::new(Ty::from_type(t))),
            Type::Fn(ps, r, _) => Ty::Fn(ps.iter().map(Ty::from_type).collect(), Box::new(Ty::from_type(r))),
        }
    }

    pub fn to_sexp(&self) -> String {
        match self {
            Ty::I64 => "i64".into(),
            Ty::Bool => "Bool".into(),
            Ty::Str => "Str".into(),
            Ty::Vec(t) => format!("(Vec {})", t.to_sexp()),
            Ty::Fn(ps, r) => {
                let ps: Vec<String> = ps.iter().map(Ty::to_sexp).collect();
                format!("(Fn [{}] {})", ps.join(" "), r.to_sexp())
            }
            Ty::Var(n) => format!("?t{}", n),
        }
    }

    fn has_var(&self) -> bool {
        match self {
            Ty::Var(_) => true,
            Ty::Vec(t) => t.has_var(),
            Ty::Fn(ps, r) => ps.iter().any(Ty::has_var) || r.has_var(),
            _ => false,
        }
    }

    fn has_fn(&self) -> bool {
        match self {
            Ty::Fn(..) => true,
            Ty::Vec(t) => t.has_fn(),
            _ => false,
        }
    }
}

/// The resolved type of every expression, indexed by `ExprId`.
pub struct TypeInfo {
    types: Vec<Ty>,
}

impl TypeInfo {
    pub fn of(&self, e: &Expr) -> &Ty {
        &self.types[e.id]
    }
}

/// A builtin's signature, instantiated with fresh variables.
enum Shape {
    Fixed(Vec<Ty>, Ty),
    /// `arg: None` means each argument may have its own type (`print`).
    Variadic {
        min: usize,
        arg: Option<Ty>,
        ret: Ty,
    },
}

/// Checks that can only run once a function's variables are solved.
enum Deferred {
    /// A variadic builtin used as a value: its arity comes from the context.
    VariadicValue { var: Ty, builtin: Builtin, at: Pos },
    /// `=` operands must not contain functions.
    Comparable { ty: Ty, at: Pos },
}

pub fn check(m: &Module) -> Result<TypeInfo, Vec<Diag>> {
    let mut inf = Infer { m, subst: Vec::new(), types: vec![Ty::Bool; m.n_exprs], visited: Vec::new(), deferred: Vec::new() };
    let mut errors = Vec::new();
    for d in &m.fns {
        if let Err(e) = inf.check_fn(d) {
            errors.push(e);
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let types = inf.types.iter().map(|t| inf.resolve(t)).collect();
    Ok(TypeInfo { types })
}

struct Infer<'m> {
    m: &'m Module,
    subst: Vec<Option<Ty>>,
    types: Vec<Ty>,
    visited: Vec<ExprId>,
    deferred: Vec<Deferred>,
}

type Env = Vec<(String, Ty)>;

fn lookup<'e>(env: &'e Env, n: &str) -> &'e Ty {
    &env.iter().rev().find(|(k, _)| k == n).expect("lower resolved every local").1
}

impl Infer<'_> {
    fn fresh(&mut self) -> Ty {
        self.subst.push(None);
        Ty::Var(self.subst.len() as u32 - 1)
    }

    fn resolve(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(n) => match &self.subst[*n as usize] {
                Some(t) => self.resolve(t),
                None => t.clone(),
            },
            Ty::Vec(t) => Ty::Vec(Box::new(self.resolve(t))),
            Ty::Fn(ps, r) => Ty::Fn(ps.iter().map(|p| self.resolve(p)).collect(), Box::new(self.resolve(r))),
            _ => t.clone(),
        }
    }

    fn occurs(&self, v: u32, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(n) => n == v,
            Ty::Vec(t) => self.occurs(v, &t),
            Ty::Fn(ps, r) => ps.iter().any(|p| self.occurs(v, p)) || self.occurs(v, &r),
            _ => false,
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), ()> {
        match (self.resolve(a), self.resolve(b)) {
            (Ty::Var(x), Ty::Var(y)) if x == y => Ok(()),
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                if self.occurs(x, &t) {
                    return Err(());
                }
                self.subst[x as usize] = Some(t);
                Ok(())
            }
            (Ty::Vec(x), Ty::Vec(y)) => self.unify(&x, &y),
            (Ty::Fn(xs, xr), Ty::Fn(ys, yr)) if xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(&ys) {
                    self.unify(x, y)?;
                }
                self.unify(&xr, &yr)
            }
            (x, y) if x == y => Ok(()),
            _ => Err(()),
        }
    }

    /// Unify, or report `what` at `at` with both sides spelled out.
    fn expect(&mut self, want: &Ty, got: &Ty, at: Pos, what: &str) -> Result<(), Diag> {
        self.unify(want, got).map_err(|()| {
            let (w, g) = (self.resolve(want).to_sexp(), self.resolve(got).to_sexp());
            Diag::new(ErrorKind::Type, at, format!("{}: expected {}, got {}", what, w, g))
        })
    }

    fn check_fn(&mut self, d: &FnDecl) -> Result<(), Diag> {
        self.visited.clear();
        self.deferred.clear();
        let mut env: Env = d.params.iter().map(|p| (p.name.clone(), Ty::from_type(&p.ty))).collect();
        let ret = Ty::from_type(&d.ret);
        for c in &d.spec.requires {
            let t = self.infer(&c.expr, &mut env)?;
            self.expect(&Ty::Bool, &t, c.expr.at, "a :requires clause must be Bool")?;
        }
        let body_ty = self.infer_seq(&d.body, &mut env)?;
        let last = d.body.last().expect("lower rejects empty bodies");
        self.expect(&ret, &body_ty, last.at, &format!("{} returns the wrong type", d.name))?;
        env.push(("result".into(), ret));
        for c in &d.spec.ensures {
            let t = self.infer(&c.expr, &mut env)?;
            self.expect(&Ty::Bool, &t, c.expr.at, "an :ensures clause must be Bool")?;
        }
        self.finish_fn()
    }

    fn finish_fn(&mut self) -> Result<(), Diag> {
        for dfr in std::mem::take(&mut self.deferred) {
            match dfr {
                Deferred::VariadicValue { var, builtin, at } => {
                    let Ty::Fn(ps, r) = self.resolve(&var) else {
                        return Err(Diag::new(
                            ErrorKind::Type,
                            at,
                            format!("cannot infer how many arguments `{}` takes here", builtin.name()),
                        ));
                    };
                    let Shape::Variadic { min, arg, ret } = self.shape(builtin) else { unreachable!("only variadics are deferred") };
                    if ps.len() < min {
                        return Err(Diag::new(
                            ErrorKind::Arity,
                            at,
                            format!("{} expects at least {} args, used here with {}", builtin.name(), min, ps.len()),
                        ));
                    }
                    for p in &ps {
                        if let Some(a) = &arg {
                            self.expect(a, p, at, &format!("argument of {}", builtin.name()))?;
                        }
                    }
                    self.expect(&ret, &r, at, &format!("result of {}", builtin.name()))?;
                }
                Deferred::Comparable { ty, at } => {
                    if self.resolve(&ty).has_fn() {
                        return Err(Diag::new(
                            ErrorKind::Type,
                            at,
                            format!("= cannot compare functions ({})", self.resolve(&ty).to_sexp()),
                        ));
                    }
                }
            }
        }
        for &id in &self.visited {
            let t = self.resolve(&self.types[id]);
            if t.has_var() {
                let at = self.expr_pos(id);
                return Err(Diag::new(ErrorKind::Type, at, format!("cannot infer a type here (got {}); add an annotation", t.to_sexp())));
            }
        }
        Ok(())
    }

    fn expr_pos(&self, id: ExprId) -> Pos {
        fn find(e: &Expr, id: ExprId) -> Option<Pos> {
            if e.id == id {
                return Some(e.at);
            }
            e.children().into_iter().find_map(|k| find(k, id))
        }
        self.m.fns.iter().flat_map(FnDecl::exprs).find_map(|e| find(e, id)).expect("visited ids come from the module")
    }

    fn shape(&mut self, b: Builtin) -> Shape {
        use Builtin as B;
        use Ty::{Bool, I64};
        let vec = |t: &Ty| Ty::Vec(Box::new(t.clone()));
        let fun = |ps: Vec<Ty>, r: Ty| Ty::Fn(ps, Box::new(r));
        match b {
            B::Add | B::Mul => Shape::Variadic { min: 0, arg: Some(I64), ret: I64 },
            B::Sub => Shape::Variadic { min: 1, arg: Some(I64), ret: I64 },
            B::Div | B::Mod => Shape::Fixed(vec![I64, I64], I64),
            B::Eq => {
                let a = self.fresh();
                Shape::Fixed(vec![a.clone(), a], Bool)
            }
            B::Lt | B::Le | B::Gt | B::Ge => Shape::Fixed(vec![I64, I64], Bool),
            B::Not => Shape::Fixed(vec![Bool], Bool),
            B::Len => Shape::Fixed(vec![vec(&self.fresh())], I64),
            B::IsEmpty => Shape::Fixed(vec![vec(&self.fresh())], Bool),
            B::Get => {
                let a = self.fresh();
                Shape::Fixed(vec![vec(&a), I64], a)
            }
            B::Slice => {
                let a = vec(&self.fresh());
                Shape::Fixed(vec![a.clone(), I64, I64], a)
            }
            B::Rest => {
                let a = vec(&self.fresh());
                Shape::Fixed(vec![a.clone()], a)
            }
            B::Concat => {
                let a = vec(&self.fresh());
                Shape::Fixed(vec![a.clone(), a.clone()], a)
            }
            B::Cons => {
                let a = self.fresh();
                Shape::Fixed(vec![a.clone(), vec(&a)], vec(&a))
            }
            B::Range => Shape::Fixed(vec![I64], vec(&I64)),
            B::Vec => {
                let a = self.fresh();
                Shape::Variadic { min: 0, arg: Some(a.clone()), ret: vec(&a) }
            }
            B::Map => {
                let (a, r) = (self.fresh(), self.fresh());
                Shape::Fixed(vec![fun(vec![a.clone()], r.clone()), vec(&a)], vec(&r))
            }
            B::Fold => {
                let (acc, a) = (self.fresh(), self.fresh());
                Shape::Fixed(vec![fun(vec![acc.clone(), a.clone()], acc.clone()), acc.clone(), vec(&a)], acc)
            }
            B::Filter => {
                let a = self.fresh();
                Shape::Fixed(vec![fun(vec![a.clone()], Bool), vec(&a)], vec(&a))
            }
            B::All => {
                let a = self.fresh();
                Shape::Fixed(vec![fun(vec![a.clone()], Bool), vec(&a)], Bool)
            }
            B::IsSorted => Shape::Fixed(vec![vec(&I64)], Bool),
            B::IsPerm => Shape::Fixed(vec![vec(&I64), vec(&I64)], Bool),
            B::Print => Shape::Variadic { min: 0, arg: None, ret: Bool },
        }
    }

    fn infer_seq(&mut self, es: &[Expr], env: &mut Env) -> Result<Ty, Diag> {
        let mut last = Ty::Bool;
        for e in es {
            last = self.infer(e, env)?;
        }
        Ok(last)
    }

    fn infer(&mut self, e: &Expr, env: &mut Env) -> Result<Ty, Diag> {
        let t = self.infer_kind(e, env)?;
        self.types[e.id] = t.clone();
        self.visited.push(e.id);
        Ok(t)
    }

    fn infer_kind(&mut self, e: &Expr, env: &mut Env) -> Result<Ty, Diag> {
        Ok(match &e.kind {
            ExprKind::Int(_) => Ty::I64,
            ExprKind::Bool(_) => Ty::Bool,
            ExprKind::Str(_) => Ty::Str,
            ExprKind::Local(n) => lookup(env, n).clone(),
            ExprKind::Global(i) => {
                let d = &self.m.fns[*i];
                Ty::Fn(d.params.iter().map(|p| Ty::from_type(&p.ty)).collect(), Box::new(Ty::from_type(&d.ret)))
            }
            ExprKind::Builtin(b) => match self.shape(*b) {
                Shape::Fixed(ps, r) => Ty::Fn(ps, Box::new(r)),
                Shape::Variadic { .. } => {
                    let var = self.fresh();
                    self.deferred.push(Deferred::VariadicValue { var: var.clone(), builtin: *b, at: e.at });
                    var
                }
            },
            ExprKind::VecLit(items) => {
                let a = self.fresh();
                for it in items {
                    let t = self.infer(it, env)?;
                    self.expect(&a, &t, it.at, "vector elements must all have one type")?;
                }
                Ty::Vec(Box::new(a))
            }
            ExprKind::If(c, t, f) => {
                let ct = self.infer(c, env)?;
                self.expect(&Ty::Bool, &ct, c.at, "if condition")?;
                let tt = self.infer(t, env)?;
                let ft = self.infer(f, env)?;
                self.unify(&tt, &ft).map_err(|()| {
                    let (a, b) = (self.resolve(&tt).to_sexp(), self.resolve(&ft).to_sexp());
                    Diag::new(ErrorKind::Type, e.at, format!("if branches differ: then is {}, else is {}", a, b))
                })?;
                tt
            }
            ExprKind::Let(binds, body) => {
                let depth = env.len();
                for (n, v) in binds {
                    let t = self.infer(v, env)?;
                    env.push((n.clone(), t));
                }
                let r = self.infer_seq(body, env);
                env.truncate(depth);
                r?
            }
            ExprKind::Lambda(ps, body) => {
                let depth = env.len();
                let mut pts = Vec::new();
                for p in ps {
                    let t = match &p.ty {
                        Some(t) => Ty::from_type(t),
                        None => self.fresh(),
                    };
                    pts.push(t.clone());
                    env.push((p.name.clone(), t));
                }
                let r = self.infer_seq(body, env);
                env.truncate(depth);
                Ty::Fn(pts, Box::new(r?))
            }
            ExprKind::Do(es) => self.infer_seq(es, env)?,
            ExprKind::And(es) | ExprKind::Or(es) => {
                for x in es {
                    let t = self.infer(x, env)?;
                    self.expect(&Ty::Bool, &t, x.at, "and/or operands")?;
                }
                Ty::Bool
            }
            ExprKind::Call(f, args) => self.infer_call(e, f, args, env)?,
        })
    }

    fn infer_call(&mut self, call: &Expr, f: &Expr, args: &[Expr], env: &mut Env) -> Result<Ty, Diag> {
        let name = match &f.kind {
            ExprKind::Builtin(b) => b.name().to_string(),
            ExprKind::Global(i) => self.m.fns[*i].name.clone(),
            ExprKind::Local(n) => n.clone(),
            _ => "fn".into(),
        };
        if let ExprKind::Builtin(b) = &f.kind {
            if let Shape::Variadic { min, arg, ret } = self.shape(*b) {
                if args.len() < min {
                    return Err(Diag::new(
                        ErrorKind::Arity,
                        call.at,
                        format!("{} expects at least {} args, got {}", name, min, args.len()),
                    ));
                }
                let mut ats = Vec::new();
                for a in args {
                    let t = self.infer(a, env)?;
                    if let Some(want) = &arg {
                        self.expect(want, &t, a.at, &format!("argument of {}", name))?;
                    }
                    ats.push(t);
                }
                self.types[f.id] = Ty::Fn(ats, Box::new(ret.clone()));
                self.visited.push(f.id);
                return Ok(ret);
            }
        }
        let ft = self.infer(f, env)?;
        if let Ty::Fn(ps, _) = self.resolve(&ft) {
            if ps.len() != args.len() {
                return Err(Diag::new(ErrorKind::Arity, call.at, format!("{} expects {} args, got {}", name, ps.len(), args.len())));
            }
        }
        let mut ats = Vec::new();
        for a in args {
            ats.push(self.infer(a, env)?);
        }
        if let ExprKind::Builtin(Builtin::Eq) = f.kind {
            self.deferred.push(Deferred::Comparable { ty: ats[0].clone(), at: call.at });
        }
        let ret = self.fresh();
        let Ty::Fn(ps, r) = self.resolve(&ft) else {
            let want = Ty::Fn(ats, Box::new(ret.clone()));
            self.expect(&ft, &want, f.at, "called value")?;
            return Ok(ret);
        };
        for ((p, a), arg) in ps.iter().zip(&ats).zip(args) {
            self.expect(p, a, arg.at, &format!("argument of {}", name))?;
        }
        Ok(*r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lower;
    use crate::sexp::parse_all_spanned;

    fn check_src(src: &str) -> Result<TypeInfo, Vec<Diag>> {
        let (f, s) = parse_all_spanned(src).unwrap();
        check(&lower(&f, &s).unwrap())
    }

    fn first_err(src: &str) -> (&'static str, usize, usize, String) {
        let d = check_src(src).err().expect("type error").remove(0);
        let at = d.at.unwrap();
        (d.kind.as_str(), at.line, at.col, d.msg)
    }

    #[test]
    fn examples_typecheck() {
        for src in
            [include_str!("../examples/msort.wrt"), include_str!("../examples/sum_sq.wrt"), include_str!("../examples/effect_leak.wrt")]
        {
            if let Err(es) = check_src(src) {
                panic!("{}", es.iter().map(Diag::to_sexp).collect::<Vec<_>>().join("\n"));
            }
        }
    }

    #[test]
    fn wrong_argument_count() {
        let (k, l, c, msg) = first_err("(defn f [x : i64] -> i64 x)\n(defn g [] -> i64\n  (f 1 2))");
        assert_eq!((k, l, c), ("arity", 3, 3));
        assert!(msg.contains("f expects 1 args, got 2"), "{}", msg);
    }

    #[test]
    fn wrong_return_type() {
        let (k, l, c, msg) = first_err("(defn f [x : i64] -> Bool\n  (+ x 1))");
        assert_eq!((k, l, c), ("type", 2, 3));
        assert!(msg.contains("expected Bool, got i64"), "{}", msg);
    }

    #[test]
    fn if_branches_must_agree() {
        let (k, l, c, msg) = first_err("(defn f [x : i64] -> i64\n  (if (< x 0) x true))");
        assert_eq!((k, l, c), ("type", 2, 3));
        assert!(msg.contains("then is i64, else is Bool"), "{}", msg);
    }

    #[test]
    fn vector_elements_share_one_type() {
        let (k, l, c, msg) = first_err("(defn f [] -> (Vec i64)\n  [1 2 \"three\"])");
        assert_eq!((k, l, c), ("type", 2, 8));
        assert!(msg.contains("expected i64, got Str"), "{}", msg);
    }

    #[test]
    fn unbound_symbols_are_rejected_before_typing() {
        let (f, s) = parse_all_spanned("(defn f [] -> i64 (+ 1 nope))").unwrap();
        assert_eq!(lower(&f, &s).unwrap_err().kind, ErrorKind::Unbound);
    }

    #[test]
    fn closures_are_inferred_from_their_use() {
        assert!(check_src("(defn f [xs : (Vec i64)] -> (Vec Bool) (map (fn [x] (> x 0)) xs))").is_ok());
        let (k, _, _, msg) = first_err("(defn f [xs : (Vec i64)] -> (Vec i64) (map (fn [x] (not x)) xs))");
        assert_eq!(k, "type");
        assert!(msg.contains("Bool") && msg.contains("i64"), "{}", msg);
    }

    #[test]
    fn variadic_builtins_take_their_arity_from_context() {
        assert!(check_src("(defn f [xs : (Vec i64)] -> i64 (fold + 0 xs))").is_ok());
        let (k, _, _, _) = first_err("(defn f [xs : (Vec Bool)] -> Bool (fold + true xs))");
        assert_eq!(k, "type");
    }

    #[test]
    fn equality_rejects_functions_and_mixed_types() {
        assert!(check_src("(defn f [a : (Vec i64)] -> Bool (= a [1 2]))").is_ok());
        let (_, _, _, msg) = first_err("(defn f [a : i64] -> Bool (= a true))");
        assert!(msg.contains("expected i64, got Bool"), "{}", msg);
        let (_, _, _, msg) = first_err("(defn g [x : i64] -> i64 x)\n(defn f [] -> Bool (= g g))");
        assert!(msg.contains("cannot compare functions"), "{}", msg);
    }

    #[test]
    fn ambiguous_types_are_reported() {
        let (k, _, _, msg) = first_err("(defn f [] -> i64 (len []))");
        assert_eq!(k, "type");
        assert!(msg.contains("cannot infer"), "{}", msg);
    }

    #[test]
    fn contracts_must_be_bool() {
        let (_, l, c, msg) = first_err("(defn f [x : i64] -> i64\n  (:ensures (+ result 1)) x)");
        assert_eq!((l, c), (2, 13));
        assert!(msg.contains(":ensures"), "{}", msg);
    }
}

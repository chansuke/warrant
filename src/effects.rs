//! Static effect checking (M1-3). Effects are inferred over the call graph to
//! a fixpoint, and each `(:effects [...])` declaration must cover what its
//! function can reach, including through closures (D17).
//!
//! A function value carries latent effects: what calling it performs. A
//! lambda's latent effects are its body's; a named function's are its
//! inferred effects; a parameter of type `(Fn [..] R :effects [..])` has the
//! declared ones. When the callee cannot be known statically (a lambda
//! parameter without an annotation, a function pulled out of a vector) the
//! checker assumes `io`, the only effect a builtin performs.

use crate::ast::{EffectSet, Expr, ExprKind, FnDecl, Module, Type};
use crate::builtin::Builtin;
use crate::diag::{Diag, ErrorKind};
use crate::sexp::Pos;
use std::collections::BTreeMap;

/// Why a function has an effect: the first place in its body that performs
/// it, and the chain of calls from there down to the builtin.
#[derive(Clone, Debug, PartialEq)]
pub struct Src {
    pub at: Pos,
    pub via: Vec<String>,
}

pub type Fx = BTreeMap<String, Src>;

pub struct EffectInfo {
    /// Indexed like `Module::fns`.
    pub inferred: Vec<Fx>,
}

impl EffectInfo {
    pub fn set(&self, f: usize) -> EffectSet {
        self.inferred[f].keys().cloned().collect()
    }
}

const UNKNOWN: &str = "io";

pub fn check(m: &Module) -> (EffectInfo, Vec<Diag>) {
    let mut inferred = vec![Fx::new(); m.fns.len()];
    loop {
        let mut w = Walker { m, inferred: &inferred, env: Vec::new(), errors: None };
        let next: Vec<Fx> = m.fns.iter().map(|d| w.function(d)).collect();
        let same = next.iter().zip(&inferred).all(|(a, b)| a.keys().eq(b.keys()));
        inferred = next;
        if same {
            break;
        }
    }
    let mut w = Walker { m, inferred: &inferred, env: Vec::new(), errors: Some(Vec::new()) };
    for d in &m.fns {
        w.function(d);
    }
    let mut errors = w.errors.unwrap_or_default();
    for (d, fx) in m.fns.iter().zip(&inferred) {
        let Some(declared) = &d.spec.effects else { continue };
        for (eff, src) in fx {
            if !declared.contains(eff) {
                let decl = crate::ast::effects_sexp(declared);
                errors.push(Diag::new(
                    ErrorKind::Effect,
                    src.at,
                    format!("`{}` declares (:effects {}) but performs {} via ({})", d.name, decl, eff, src.via.join(" ")),
                ));
            }
        }
    }
    (EffectInfo { inferred }, errors)
}

struct Walker<'a> {
    m: &'a Module,
    inferred: &'a [Fx],
    /// Latent effects of locals that may be called.
    env: Vec<(String, Fx)>,
    /// Collected only on the final pass, once `inferred` is stable.
    errors: Option<Vec<Diag>>,
}

fn union(into: &mut Fx, from: Fx) {
    for (k, v) in from {
        into.entry(k).or_insert(v);
    }
}

fn unknown(at: Pos, what: &str) -> Fx {
    Fx::from([(UNKNOWN.to_string(), Src { at, via: vec![what.to_string()] })])
}

fn declared(effs: &EffectSet, at: Pos, name: &str) -> Fx {
    effs.iter().map(|e| (e.clone(), Src { at, via: vec![name.to_string()] })).collect()
}

/// Latent effects of a parameter, from its annotation.
fn param_latent(ty: Option<&Type>, at: Pos, name: &str) -> Fx {
    match ty {
        Some(Type::Fn(_, _, effs)) => declared(effs, at, name),
        Some(_) => Fx::new(),
        None => unknown(at, name),
    }
}

impl Walker<'_> {
    fn function(&mut self, d: &FnDecl) -> Fx {
        self.env = d.params.iter().map(|p| (p.name.clone(), param_latent(Some(&p.ty), p.at, &p.name))).collect();
        let mut fx = Fx::new();
        for c in &d.spec.requires {
            union(&mut fx, self.eval(&c.expr));
        }
        for e in &d.body {
            union(&mut fx, self.eval(e));
        }
        if let Type::Fn(_, _, allowed) = &d.ret {
            let last = d.body.last().expect("lower rejects empty bodies");
            let lat = self.latent(last);
            self.require_within(&lat, allowed, last.at, &format!("{} returns a function", d.name));
        }
        self.env.push(("result".into(), param_latent(Some(&d.ret), d.at, "result")));
        for c in &d.spec.ensures {
            union(&mut fx, self.eval(&c.expr));
        }
        fx
    }

    fn require_within(&mut self, lat: &Fx, allowed: &EffectSet, at: Pos, what: &str) {
        let Some(errors) = &mut self.errors else { return };
        for (eff, src) in lat {
            if !allowed.contains(eff) {
                errors.push(Diag::new(
                    ErrorKind::Effect,
                    at,
                    format!(
                        "{} that performs {} via ({}), but its type allows only {}",
                        what,
                        eff,
                        src.via.join(" "),
                        crate::ast::effects_sexp(allowed)
                    ),
                ));
            }
        }
    }

    fn lookup(&self, n: &str) -> Fx {
        self.env.iter().rev().find(|(k, _)| k == n).map(|(_, fx)| fx.clone()).unwrap_or_default()
    }

    fn with_locals<T>(&mut self, binds: Vec<(String, Fx)>, f: impl FnOnce(&mut Self) -> T) -> T {
        let depth = self.env.len();
        self.env.extend(binds);
        let r = f(self);
        self.env.truncate(depth);
        r
    }

    /// Effects performed when the value of `e` is called.
    fn latent(&mut self, e: &Expr) -> Fx {
        match &e.kind {
            ExprKind::Lambda(ps, body) => {
                let binds = ps.iter().map(|p| (p.name.clone(), param_latent(p.ty.as_ref(), p.at, &p.name))).collect();
                self.with_locals(binds, |w| {
                    let mut fx = Fx::new();
                    for b in body {
                        union(&mut fx, w.eval(b));
                    }
                    fx
                })
            }
            ExprKind::Global(i) => {
                let name = &self.m.fns[*i].name;
                self.inferred[*i]
                    .iter()
                    .map(|(k, src)| {
                        let mut via = vec![name.clone()];
                        via.extend(src.via.iter().cloned());
                        (k.clone(), Src { at: e.at, via })
                    })
                    .collect()
            }
            ExprKind::Builtin(Builtin::Print) => unknown(e.at, "print"),
            ExprKind::Builtin(b @ (Builtin::Map | Builtin::Filter | Builtin::Fold | Builtin::All)) => unknown(e.at, b.name()),
            ExprKind::Builtin(_) => Fx::new(),
            ExprKind::Local(n) => self.lookup(n),
            ExprKind::If(_, t, f) => {
                let mut fx = self.latent(t);
                union(&mut fx, self.latent(f));
                fx
            }
            ExprKind::Let(binds, body) => {
                let binds = binds.iter().map(|(n, v)| (n.clone(), self.latent(v))).collect();
                self.with_locals(binds, |w| w.latent(body.last().expect("lower rejects empty bodies")))
            }
            ExprKind::Do(es) => self.latent(es.last().expect("lower rejects empty bodies")),
            ExprKind::Call(f, _) => match &f.kind {
                ExprKind::Global(i) => match &self.m.fns[*i].ret {
                    Type::Fn(_, _, effs) => declared(effs, e.at, &self.m.fns[*i].name),
                    _ => Fx::new(),
                },
                _ => unknown(e.at, "fn"),
            },
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::VecLit(_) | ExprKind::And(_) | ExprKind::Or(_) => Fx::new(),
        }
    }

    /// Effects performed by evaluating `e`.
    fn eval(&mut self, e: &Expr) -> Fx {
        let mut fx = Fx::new();
        match &e.kind {
            ExprKind::Int(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::Local(_)
            | ExprKind::Global(_)
            | ExprKind::Builtin(_)
            | ExprKind::Lambda(..) => {}
            ExprKind::VecLit(es) | ExprKind::Do(es) | ExprKind::And(es) | ExprKind::Or(es) => {
                for x in es {
                    union(&mut fx, self.eval(x));
                }
            }
            ExprKind::If(c, t, f) => {
                for x in [c, t, f] {
                    union(&mut fx, self.eval(x));
                }
            }
            ExprKind::Let(binds, body) => {
                let depth = self.env.len();
                for (n, v) in binds {
                    union(&mut fx, self.eval(v));
                    let lat = self.latent(v);
                    self.env.push((n.clone(), lat));
                }
                for b in body {
                    union(&mut fx, self.eval(b));
                }
                self.env.truncate(depth);
            }
            ExprKind::Call(f, args) => {
                union(&mut fx, self.eval(f));
                for a in args {
                    union(&mut fx, self.eval(a));
                }
                let called = match &f.kind {
                    ExprKind::Builtin(Builtin::Map | Builtin::Filter | Builtin::Fold | Builtin::All) => self.latent(&args[0]),
                    _ => self.latent(f),
                };
                if let ExprKind::Global(i) = &f.kind {
                    let callee = &self.m.fns[*i];
                    for (p, a) in callee.params.iter().zip(args) {
                        if let Type::Fn(_, _, allowed) = &p.ty {
                            let lat = self.latent(a);
                            self.require_within(&lat, allowed, a.at, &format!("argument `{}` of {} is a function", p.name, callee.name));
                        }
                    }
                }
                for (k, src) in called {
                    fx.entry(k).or_insert(Src { at: e.at, via: src.via });
                }
            }
        }
        fx
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lower;
    use crate::sexp::parse_all_spanned;

    fn run(src: &str) -> (Module, EffectInfo, Vec<Diag>) {
        let (f, s) = parse_all_spanned(src).unwrap();
        let m = lower(&f, &s).unwrap();
        let (info, errs) = check(&m);
        (m, info, errs)
    }

    fn inferred(src: &str, name: &str) -> String {
        let (m, info, _) = run(src);
        crate::ast::effects_sexp(&info.set(m.index[name]))
    }

    #[test]
    fn effect_leak_example_is_caught_before_running() {
        let (_, _, errs) = run(include_str!("../examples/effect_leak.wrt"));
        assert_eq!(errs.len(), 1, "{:?}", errs);
        assert_eq!(
            errs[0].to_sexp(),
            "(error :kind effect :at (line 9 col 7) :msg \"`add` declares (:effects []) but performs io via (log print)\")"
        );
    }

    #[test]
    fn pure_examples_have_no_effects() {
        let (m, info, errs) = run(include_str!("../examples/msort.wrt"));
        assert!(errs.is_empty(), "{:?}", errs);
        assert!(info.inferred.iter().all(|fx| fx.is_empty()), "{:?}", m.fns.iter().map(|d| &d.name).collect::<Vec<_>>());
    }

    #[test]
    fn undeclared_functions_still_get_inferred_effects() {
        let src = "(defn log [m : Str] -> Bool (print m))\n(defn twice [m : Str] -> Bool (do (log m) (log m)))";
        assert_eq!(inferred(src, "twice"), "[io]");
        assert!(run(src).2.is_empty());
    }

    #[test]
    fn effects_flow_through_closures_passed_to_builtins() {
        let src = "(defn f [xs : (Vec i64)] -> (Vec Bool)\n  (:effects [])\n  (map (fn [x] (print x)) xs))";
        let (_, _, errs) = run(src);
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].at, Some(Pos { line: 3, col: 3 }));
        assert!(errs[0].msg.contains("performs io via (print)"), "{}", errs[0].msg);
    }

    #[test]
    fn effects_flow_through_let_bound_closures_and_recursion() {
        let src = "(defn loop [n : i64] -> Bool (if (= n 0) true (let [say (fn [] (print n))] (do (say) (loop (- n 1))))))";
        assert_eq!(inferred(src, "loop"), "[io]");
    }

    #[test]
    fn function_parameters_carry_their_declared_effects() {
        let src = "(defn apply [g : (Fn [i64] Bool :effects [io]) x : i64] -> Bool (:effects [io]) (g x))
                   (defn main [] -> Bool (:effects [io]) (apply (fn [x] (print x)) 1))";
        assert!(run(src).2.is_empty(), "{:?}", run(src).2);
        let pure_param = "(defn apply [g : (Fn [i64] Bool) x : i64] -> Bool (:effects []) (g x))
                          (defn main [] -> Bool (:effects [io]) (apply (fn [x] (print x)) 1))";
        let (_, _, errs) = run(pure_param);
        assert_eq!(errs.len(), 1, "{:?}", errs);
        assert!(errs[0].msg.contains("argument `g` of apply is a function that performs io"), "{}", errs[0].msg);
    }

    #[test]
    fn unannotated_lambda_parameters_are_assumed_to_do_io_when_called() {
        assert_eq!(inferred("(defn f [x : i64] -> Bool ((fn [g] (g x)) (fn [y] true)))", "f"), "[io]");
    }
}

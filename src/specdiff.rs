//! Spec-diff guard (M1-7). Compares two versions of a program clause by
//! clause and flags every change that could let a weaker implementation
//! through: a dropped or changed `:ensures`, a new or changed `:requires`,
//! wider `:effects`, a looser `:budget`, a changed signature, a removed
//! function. Body-only changes are listed apart; those an agent may merge.
//!
//! When the pre/postconditions changed, a solver may show the new contract
//! refines the old one (old requires => new requires, and old requires and
//! new ensures => old ensures). Such changes are `refined`, not weakened.

use crate::ast::{Clause, FnDecl, Module};
use crate::sexp::{flat, quote_str, Sexp, SpanTree};
use crate::solver::Solver;
use crate::vc::VcKind;
use crate::verify::Status;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Weakened,
    Strengthened,
    /// Changed, and proved to refine the old contract.
    Refined,
    /// A function that did not exist before: a new spec to approve.
    New,
}

impl Verdict {
    fn name(self) -> &'static str {
        match self {
            Verdict::Weakened => "weakened",
            Verdict::Strengthened => "strengthened",
            Verdict::Refined => "refined",
            Verdict::New => "new",
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct SpecChange {
    pub fn_name: String,
    /// `ensures`, `requires`, `effects`, `budget`, `signature`, `defn`
    pub clause: &'static str,
    /// `added`, `removed`, `expanded`, `narrowed`, `loosened`, `tightened`, `changed`
    pub change: &'static str,
    pub verdict: Verdict,
    /// Extra keys, already S-expression text: ` :old ... :new ...`
    pub detail: String,
}

pub struct Diff {
    pub spec: Vec<SpecChange>,
    /// Functions whose body changed with their spec unchanged or not.
    pub bodies: Vec<String>,
}

impl Diff {
    pub fn weakened(&self) -> bool {
        self.spec.iter().any(|c| c.verdict == Verdict::Weakened)
    }

    pub fn to_sexp(&self, old: &str, new: &str) -> String {
        let mut s = format!("(spec-diff\n  (old {}) (new {})\n  (spec", quote_str(old), quote_str(new));
        for c in &self.spec {
            s += &format!("\n    ({} :clause {} :change {} :verdict {}{})", c.fn_name, c.clause, c.change, c.verdict.name(), c.detail);
        }
        s += ")\n  (impl";
        for b in &self.bodies {
            s += &format!("\n    ({} :body changed)", b);
        }
        s += &format!(")\n  (status {}))", if self.weakened() { "weakened" } else { "ok" });
        s
    }
}

fn srcs(cs: &[Clause]) -> Vec<&Sexp> {
    cs.iter().map(|c| &c.src).collect()
}

/// Clauses in `a` that are not in `b`.
fn missing<'a>(a: &[&'a Sexp], b: &[&Sexp]) -> Vec<&'a Sexp> {
    a.iter().filter(|x| !b.contains(x)).copied().collect()
}

fn signature(d: &FnDecl) -> String {
    let ps: Vec<String> = d.params.iter().map(|p| format!("{} : {}", p.name, p.ty.to_sexp())).collect();
    format!("[{}] -> {}", ps.join(" "), d.ret.to_sexp())
}

pub fn diff(old: &Module, new: &Module, solver: Option<&dyn Solver>) -> Diff {
    let mut spec = Vec::new();
    let mut bodies = Vec::new();
    let change = |f: &str, clause, change, verdict, detail: String| SpecChange { fn_name: f.to_string(), clause, change, verdict, detail };
    for o in &old.fns {
        if new.get(&o.name).is_none() {
            spec.push(change(&o.name, "defn", "removed", Verdict::Weakened, String::new()));
        }
    }
    for n in &new.fns {
        let name = n.name.as_str();
        let Some(o) = old.get(name) else {
            spec.push(change(name, "defn", "added", Verdict::New, String::new()));
            continue;
        };
        if n.body_src != o.body_src {
            bodies.push(n.name.clone());
        }
        let same_signature = signature(o) == signature(n);
        if !same_signature {
            let detail = format!(" :old {} :new {}", quote_str(&signature(o)), quote_str(&signature(n)));
            spec.push(change(name, "signature", "changed", Verdict::Weakened, detail));
        }

        let (oe, ne) = (srcs(&o.spec.ensures), srcs(&n.spec.ensures));
        let (or, nr) = (srcs(&o.spec.requires), srcs(&n.spec.requires));
        let (ens_gone, ens_new) = (missing(&oe, &ne), missing(&ne, &oe));
        let (req_new, req_gone) = (missing(&nr, &or), missing(&or, &nr));
        let suspect = !ens_gone.is_empty() || !req_new.is_empty();
        let refined = suspect && same_signature && solver.is_some_and(|s| refines(o, new, s));
        let weak = if refined { Verdict::Refined } else { Verdict::Weakened };
        for e in ens_gone {
            spec.push(change(name, "ensures", "removed", weak, format!(" :old {}", flat(e))));
        }
        for e in ens_new {
            spec.push(change(name, "ensures", "added", Verdict::Strengthened, format!(" :new {}", flat(e))));
        }
        for e in req_new {
            spec.push(change(name, "requires", "added", weak, format!(" :new {}", flat(e))));
        }
        for e in req_gone {
            spec.push(change(name, "requires", "removed", Verdict::Strengthened, format!(" :old {}", flat(e))));
        }

        match (&o.spec.effects, &n.spec.effects) {
            (Some(a), Some(b)) => {
                let detail = format!(" :old {} :new {}", crate::ast::effects_sexp(a), crate::ast::effects_sexp(b));
                if !b.is_subset(a) {
                    spec.push(change(name, "effects", "expanded", Verdict::Weakened, detail));
                } else if b != a {
                    spec.push(change(name, "effects", "narrowed", Verdict::Strengthened, detail));
                }
            }
            (Some(a), None) => spec.push(change(name, "effects", "removed", Verdict::Weakened, format!(" :old {}", crate::ast::effects_sexp(a)))),
            (None, Some(b)) => spec.push(change(name, "effects", "added", Verdict::Strengthened, format!(" :new {}", crate::ast::effects_sexp(b)))),
            (None, None) => {}
        }

        let wall = |d: &FnDecl| d.spec.budget.as_ref().and_then(|b| b.wall_ms);
        match (wall(o), wall(n)) {
            (Some(a), Some(b)) if b > a => spec.push(change(name, "budget", "loosened", Verdict::Weakened, format!(" :old (wall-ms {}) :new (wall-ms {})", a, b))),
            (Some(a), Some(b)) if b < a => spec.push(change(name, "budget", "tightened", Verdict::Strengthened, format!(" :old (wall-ms {}) :new (wall-ms {})", a, b))),
            (Some(a), None) => spec.push(change(name, "budget", "removed", Verdict::Weakened, format!(" :old (wall-ms {})", a))),
            (None, Some(b)) => spec.push(change(name, "budget", "added", Verdict::Strengthened, format!(" :new (wall-ms {})", b))),
            _ => {}
        }
    }
    Diff { spec, bodies }
}

/// Proves the new contract of `old.name` refines `old`'s, by verifying a
/// function that carries the old contract and only calls the new one:
///
/// ```text
/// (defn %refines-f OLD-PARAMS -> OLD-RET (:requires OLD...) (:ensures OLD...) (f ARGS...))
/// ```
///
/// Its call obligations are "old requires => new requires", and its ensures
/// obligations are "old requires and new ensures => old ensures". Helpers
/// the clauses call are resolved in the new program.
fn refines(old: &FnDecl, new: &Module, solver: &dyn Solver) -> bool {
    let Sexp::List(items) = &old.source else { return false };
    let sym = |s: &str| Sexp::Sym(s.to_string());
    let probe = format!("%refines-{}", old.name);
    let mut defn = vec![sym("defn"), sym(&probe), items[2].clone(), sym("->"), items[4].clone()];
    for (kw, cs) in [("requires", &old.spec.requires), ("ensures", &old.spec.ensures)] {
        if !cs.is_empty() {
            defn.push(Sexp::List(std::iter::once(Sexp::Kw(kw.into())).chain(cs.iter().map(|c| c.src.clone())).collect()));
        }
    }
    defn.push(Sexp::List(std::iter::once(sym(&old.name)).chain(old.params.iter().map(|p| sym(&p.name))).collect()));
    let forms: Vec<Sexp> = new.fns.iter().map(|d| d.source.clone()).chain([Sexp::List(defn)]).collect();
    let spans: Vec<SpanTree> = forms.iter().map(SpanTree::synthetic).collect();
    let Ok(m) = crate::ast::lower(&forms, &spans) else { return false };
    let Ok(ty) = crate::types::check(&m) else { return false };
    let goals: Vec<_> = crate::vc::generate(&m, &ty)
        .into_iter()
        .filter(|ob| ob.fn_name == probe)
        .filter(|ob| match &ob.kind {
            VcKind::Requires { callee, .. } => *callee == old.name,
            VcKind::Ensures { .. } => true,
            _ => false,
        })
        .collect();
    let results = crate::verify::discharge(goals, solver, None, 1);
    // No goals would make `all` vacuously true without proving anything.
    !results.is_empty() && results.iter().all(|r| r.status == Status::Proved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lower;
    use crate::sexp::parse_all_spanned;
    use crate::solver::Z3;

    fn module(src: &str) -> Module {
        let (f, s) = parse_all_spanned(src).unwrap();
        lower(&f, &s).unwrap()
    }

    /// `(fn clause change verdict)` for each spec change, without a solver.
    fn changes(old: &str, new: &str) -> Vec<String> {
        diff(&module(old), &module(new), None)
            .spec
            .iter()
            .map(|c| format!("{} {} {} {}", c.fn_name, c.clause, c.change, c.verdict.name()))
            .collect()
    }

    const BASE: &str = "(defn f [x : i64] -> i64 (:effects []) (:requires (> x 0)) (:ensures (> result 0)) (:budget (wall-ms 50)) x)";

    #[test]
    fn body_only_changes_are_implementation_changes() {
        let d = diff(&module(BASE), &module(&BASE.replace(" x)", " (+ x 0))")), None);
        assert!(d.spec.is_empty());
        assert_eq!(d.bodies, ["f"]);
        assert!(!d.weakened());
    }

    #[test]
    fn removing_or_changing_ensures_is_suspected_weakening() {
        assert_eq!(changes(BASE, &BASE.replace("(:ensures (> result 0)) ", "")), ["f ensures removed weakened"]);
        assert_eq!(changes(BASE, &BASE.replace("(> result 0)", "(>= result 0)")), ["f ensures removed weakened", "f ensures added strengthened"]);
    }

    #[test]
    fn adding_ensures_or_dropping_requires_strengthens() {
        assert_eq!(changes(BASE, &BASE.replace("(> result 0)", "(> result 0) (> result -5)")), ["f ensures added strengthened"]);
        assert_eq!(changes(BASE, &BASE.replace("(:requires (> x 0)) ", "")), ["f requires removed strengthened"]);
    }

    #[test]
    fn adding_or_changing_requires_weakens_for_callers() {
        assert_eq!(changes(BASE, &BASE.replace("(> x 0)", "(> x 0) (< x 9)")), ["f requires added weakened"]);
    }

    #[test]
    fn wider_effects_weaken_and_narrower_strengthen() {
        assert_eq!(changes(BASE, &BASE.replace("(:effects [])", "(:effects [io])")), ["f effects expanded weakened"]);
        assert_eq!(changes(&BASE.replace("(:effects [])", "(:effects [io])"), BASE), ["f effects narrowed strengthened"]);
        assert_eq!(changes(BASE, &BASE.replace("(:effects []) ", "")), ["f effects removed weakened"]);
    }

    #[test]
    fn a_looser_budget_weakens() {
        assert_eq!(changes(BASE, &BASE.replace("50", "80")), ["f budget loosened weakened"]);
        assert_eq!(changes(BASE, &BASE.replace("50", "20")), ["f budget tightened strengthened"]);
        assert_eq!(changes(BASE, &BASE.replace("(:budget (wall-ms 50)) ", "")), ["f budget removed weakened"]);
    }

    #[test]
    fn signatures_and_whole_functions() {
        assert_eq!(changes(BASE, &BASE.replace("[x : i64] -> i64", "[x : i64] -> Bool")), ["f signature changed weakened"]);
        assert_eq!(changes(BASE, &format!("{}\n(defn g [] -> i64 1)", BASE)), ["g defn added new"]);
        assert_eq!(changes(&format!("{}\n(defn g [] -> i64 1)", BASE), BASE), ["g defn removed weakened"]);
    }

    #[test]
    fn the_solver_clears_changes_that_only_refine_the_contract() {
        let Some(z3) = Z3::find(5000) else { return };
        let refined = BASE.replace("(> result 0)", "(> result 1)").replace("(> x 0)", "(> x -1)");
        let d = diff(&module(BASE), &module(&refined), Some(&z3));
        let verdicts: Vec<&str> = d.spec.iter().map(|c| c.verdict.name()).collect();
        assert_eq!(verdicts, ["refined", "strengthened", "refined", "strengthened"], "{}", d.to_sexp("a", "b"));
        assert!(!d.weakened());

        let weaker = BASE.replace("(> result 0)", "(>= result 0)");
        assert!(diff(&module(BASE), &module(&weaker), Some(&z3)).weakened());
        let narrower_input = BASE.replace("(> x 0)", "(> x 5)");
        assert!(diff(&module(BASE), &module(&narrower_input), Some(&z3)).weakened());
    }
}

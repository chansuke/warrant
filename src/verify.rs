//! Discharges obligations with a solver, summarizes the outcome, and turns
//! it into the level of each contract clause.
//!
//! An `ensures` clause is proved when every obligation that came from it
//! (the clause itself and the well-definedness of its expression) is proved.
//! A `requires` clause is proved when, at every place the program calls the
//! function, an obligation for that clause was generated and proved. A
//! function passed around as a value has call sites no obligation can see,
//! and `main` is called by the runtime, so their preconditions stay checked.

use crate::ast::{Expr, ExprId, ExprKind, FnIdx, Module};
use crate::cache::Cache;
use crate::contracts::{ClauseLevels, Level};
use crate::solver::{Outcome, Solver};
use crate::vc::{counterexample_sexp, Goal, Obligation, Site, VcKind};
use std::time::Instant;

#[derive(Clone, Debug, PartialEq)]
pub enum Status {
    Proved,
    Failed { model: Vec<(String, String)> },
    Unknown { reason: String },
    Unsupported { reason: String },
}

pub struct VcResult {
    pub ob: Obligation,
    pub status: Status,
    pub ns: u128,
    pub cached: bool,
}

impl VcResult {
    pub fn to_sexp(&self) -> String {
        let tail = match &self.status {
            Status::Proved => ":status proved".to_string(),
            Status::Failed { model } => format!(":status failed :counterexample {}", counterexample_sexp(model)),
            Status::Unknown { reason } => format!(":status unknown :reason {}", crate::sexp::quote_str(reason)),
            Status::Unsupported { reason } => format!(":status unsupported :reason {}", crate::sexp::quote_str(reason)),
        };
        let cached = if self.cached { " :cached true" } else { "" };
        format!("{} {}{} :ms {})", self.ob.head_sexp(), tail, cached, crate::profile::ms(self.ns))
    }
}

fn from_outcome(o: Outcome) -> Status {
    match o {
        Outcome::Proved => Status::Proved,
        Outcome::Failed { model } => Status::Failed { model },
        Outcome::Unknown { reason } => Status::Unknown { reason },
    }
}

fn discharge_one(ob: Obligation, solver: &dyn Solver, cache: Option<&Cache>) -> VcResult {
    let t = Instant::now();
    let mut cached = false;
    let status = match &ob.goal {
        Goal::Unsupported(reason) => Status::Unsupported { reason: reason.clone() },
        Goal::Script(s) => {
            let fp = solver.fingerprint();
            match cache.and_then(|c| c.get(&fp, s)) {
                Some(o) => {
                    cached = true;
                    from_outcome(o)
                }
                None => match solver.check(s, &ob.inputs) {
                    Ok(o) => {
                        if let Some(c) = cache {
                            c.put(&fp, s, &o);
                        }
                        from_outcome(o)
                    }
                    Err(e) => Status::Unknown { reason: format!("could not run the solver: {}", e) },
                },
            }
        }
    };
    VcResult { ob, status, ns: t.elapsed().as_nanos(), cached }
}

/// Each obligation is a self-contained script, so they are solved on
/// `jobs` threads at once. Results keep the obligations' order.
pub fn discharge(obs: Vec<Obligation>, solver: &dyn Solver, cache: Option<&Cache>, jobs: usize) -> Vec<VcResult> {
    let n = obs.len();
    let queue = std::sync::Mutex::new(obs.into_iter().enumerate());
    let mut out: Vec<Option<VcResult>> = (0..n).map(|_| None).collect();
    let results = std::sync::Mutex::new(&mut out);
    std::thread::scope(|s| {
        for _ in 0..jobs.clamp(1, n.max(1)) {
            s.spawn(|| loop {
                let Some((i, ob)) = queue.lock().unwrap().next() else { return };
                let r = discharge_one(ob, solver, cache);
                results.lock().unwrap()[i] = Some(r);
            });
        }
    });
    out.into_iter().map(|r| r.expect("every obligation was taken by a worker")).collect()
}

/// Obligations shown under `:slowest`.
const SLOWEST: usize = 3;

/// `(smt :vcs N :proved P ... :issues (...))`: everything not proved is listed.
pub fn summary_sexp(results: &[VcResult], total_ns: u128) -> String {
    let count = |f: fn(&Status) -> bool| results.iter().filter(|r| f(&r.status)).count();
    let failed = count(|s| matches!(s, Status::Failed { .. }));
    let mut slow: Vec<&VcResult> = results.iter().filter(|r| !r.cached && matches!(r.ob.goal, Goal::Script(_))).collect();
    slow.sort_by_key(|a| std::cmp::Reverse(a.ns));
    let slowest: Vec<String> = slow
        .iter()
        .take(SLOWEST)
        .map(|r| format!("({} {} {})", r.ob.fn_name, r.ob.kind.name(), crate::profile::ms(r.ns)))
        .collect();
    let mut reproved: Vec<&str> = slow.iter().map(|r| r.ob.fn_name.as_str()).collect();
    reproved.sort_unstable();
    reproved.dedup();
    let mut s = format!(
        "(smt :status {} :vcs {} :proved {} :failed {} :unknown {} :unsupported {} :cached {} :ms {} :reproved ({}) :slowest ({})",
        if failed > 0 { "failed" } else { "ok" },
        results.len(),
        count(|s| *s == Status::Proved),
        failed,
        count(|s| matches!(s, Status::Unknown { .. })),
        count(|s| matches!(s, Status::Unsupported { .. })),
        results.iter().filter(|r| r.cached).count(),
        crate::profile::ms(total_ns),
        reproved.join(" "),
        slowest.join(" ")
    );
    let issues: Vec<&VcResult> = results.iter().filter(|r| r.status != Status::Proved).collect();
    if !issues.is_empty() {
        s += "\n    :issues (";
        for r in issues {
            s += &format!("\n      {}", r.to_sexp());
        }
        s += ")";
    }
    s + ")"
}

pub fn any_failed(results: &[VcResult]) -> bool {
    results.iter().any(|r| matches!(r.status, Status::Failed { .. }))
}

/// Direct call sites of each function, and whether it is ever used as a value.
fn call_sites(m: &Module) -> (Vec<Vec<ExprId>>, Vec<bool>) {
    let mut calls = vec![Vec::new(); m.fns.len()];
    let mut as_value = vec![false; m.fns.len()];
    let mut stack: Vec<&Expr> = m.fns.iter().flat_map(|d| d.exprs()).collect();
    while let Some(e) = stack.pop() {
        match &e.kind {
            ExprKind::Call(head, args) if matches!(head.kind, ExprKind::Global(_)) => {
                let ExprKind::Global(f) = head.kind else { unreachable!() };
                calls[f].push(e.id);
                stack.extend(args);
            }
            ExprKind::Global(f) => as_value[*f] = true,
            _ => stack.extend(e.children()),
        }
    }
    (calls, as_value)
}

pub fn levels(m: &Module, results: &[VcResult]) -> ClauseLevels {
    let proved = |rs: &mut dyn Iterator<Item = &VcResult>| {
        let mut any = false;
        for r in rs {
            if r.status != Status::Proved {
                return false;
            }
            any = true;
        }
        any
    };
    let of_fn = |f: FnIdx| results.iter().filter(move |r| r.ob.fn_name == m.fns[f].name);
    let (calls, as_value) = call_sites(m);
    let level = |ok: bool| if ok { Level::Proved } else { Level::RuntimeChecked };

    let ensures = (0..m.fns.len())
        .map(|f| {
            (0..m.fns[f].spec.ensures.len())
                .map(|c| {
                    let has_goal = of_fn(f).any(|r| r.ob.kind == VcKind::Ensures { index: c });
                    level(has_goal && proved(&mut of_fn(f).filter(|r| r.ob.site == Site::Ensures(c))))
                })
                .collect()
        })
        .collect();

    let requires = (0..m.fns.len())
        .map(|f| {
            let d = &m.fns[f];
            (0..d.spec.requires.len())
                .map(|c| {
                    let own_ok = of_fn(f).filter(|r| r.ob.site == Site::Requires(c)).all(|r| r.status == Status::Proved);
                    let kind = VcKind::Requires { callee: d.name.clone(), index: c };
                    let every_site = !calls[f].is_empty()
                        && calls[f].iter().all(|site| proved(&mut results.iter().filter(|r| r.ob.expr == *site && r.ob.kind == kind)));
                    level(d.name != "main" && !as_value[f] && own_ok && every_site)
                })
                .collect()
        })
        .collect();
    ClauseLevels { requires, ensures }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lower;
    use crate::contracts::{Checks, Mode};
    use crate::sexp::parse_all_spanned;
    use crate::solver::Z3;

    fn levels_of(src: &str) -> Option<(Module, ClauseLevels)> {
        let z3 = Z3::find_for_test(5000)?;
        let (f, s) = parse_all_spanned(src).unwrap();
        let m = lower(&f, &s).unwrap();
        let ty = crate::types::check(&m).unwrap();
        let results = discharge(crate::vc::generate(&m, &ty), &z3, None, 4);
        let l = levels(&m, &results);
        Some((m, l))
    }

    fn names(ls: &[Level]) -> Vec<&'static str> {
        ls.iter().map(|l| l.name()).collect()
    }

    #[test]
    fn msort_is_proved_entirely() {
        let Some((m, l)) = levels_of(include_str!("../examples/msort.wrt")) else { return };
        let (merge, msort, gen) = (m.index["merge"], m.index["msort"], m.index["gen"]);
        assert_eq!(names(&l.requires[merge]), ["proved", "proved"]);
        assert_eq!(names(&l.ensures[merge]), ["proved"; 4]);
        assert_eq!(names(&l.ensures[msort]), ["proved"; 3]);
        assert_eq!(names(&l.requires[gen]), ["proved"; 4]);
        assert_eq!(names(&l.ensures[gen]), ["proved"]);
    }

    #[test]
    fn a_precondition_stays_checked_when_any_caller_is_unproved() {
        let src = "(defn pos [x : i64] -> i64 (:requires (> x 0)) x)
                   (defn a [] -> i64 (pos 1))
                   (defn b [y : i64] -> i64 (pos y))";
        let Some((m, l)) = levels_of(src) else { return };
        assert_eq!(names(&l.requires[m.index["pos"]]), ["runtime-checked"]);
        let Some((m, l)) = levels_of(&src.replace("(pos y)", "(pos 2)")) else { return };
        assert_eq!(names(&l.requires[m.index["pos"]]), ["proved"]);
    }

    #[test]
    fn functions_passed_as_values_and_main_keep_their_preconditions() {
        let src = "(defn pos [x : i64] -> i64 (:requires (> x 0)) x)
                   (defn a [] -> (Vec i64) (map pos [1 2]))
                   (defn main [] -> i64 (:requires (> 1 0)) (pos 1))";
        let Some((m, l)) = levels_of(src) else { return };
        assert_eq!(names(&l.requires[m.index["pos"]]), ["runtime-checked"]);
        assert_eq!(names(&l.requires[m.index["main"]]), ["runtime-checked"]);
    }

    #[test]
    fn modes_select_which_clauses_to_check() {
        let Some((m, l)) = levels_of(include_str!("../examples/msort.wrt")) else { return };
        assert_eq!(Checks::new(&m, Mode::Runtime, Some(&l)).count(), (14, 0));
        assert_eq!(Checks::new(&m, Mode::Auto, Some(&l)).count(), (0, 14));
        assert_eq!(Checks::new(&m, Mode::Auto, None).count(), (14, 0));
        assert_eq!(Checks::new(&m, Mode::Off, Some(&l)).count(), (0, 14));
    }
}

//! Which contract clauses still need run-time checks (M1-6).
//!
//! An `ensures` clause is proved when every obligation that came from it
//! (the clause itself and the well-definedness of its expression) is proved.
//! A `requires` clause is proved when, at every place the program calls the
//! function, an obligation for that clause was generated and proved. A
//! function passed around as a value has call sites no obligation can see,
//! and `main` is called by the runtime, so their preconditions stay checked.

use crate::ast::{Expr, ExprId, ExprKind, FnIdx, Module};
use crate::verify::{Status, VcResult};
use crate::vc::{Site, VcKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Proved,
    RuntimeChecked,
}

impl Level {
    pub fn name(self) -> &'static str {
        match self {
            Level::Proved => "proved",
            Level::RuntimeChecked => "runtime-checked",
        }
    }
}

/// Indexed by function, then clause.
pub struct ClauseLevels {
    pub requires: Vec<Vec<Level>>,
    pub ensures: Vec<Vec<Level>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Check every clause.
    Runtime,
    /// Check only what was not proved.
    Auto,
    Off,
}

impl Mode {
    pub fn parse(s: &str) -> Option<Mode> {
        match s {
            "runtime" => Some(Mode::Runtime),
            "auto" => Some(Mode::Auto),
            "off" => Some(Mode::Off),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Mode::Runtime => "runtime",
            Mode::Auto => "auto",
            Mode::Off => "off",
        }
    }
}

/// `true` = check at run time. Indexed like `ClauseLevels`.
pub struct Checks {
    pub requires: Vec<Vec<bool>>,
    pub ensures: Vec<Vec<bool>>,
}

impl Checks {
    pub fn new(m: &Module, mode: Mode, levels: Option<&ClauseLevels>) -> Checks {
        let pick = |i: usize, n: usize, of: &dyn Fn(&ClauseLevels) -> &Vec<Vec<Level>>| -> Vec<bool> {
            (0..n)
                .map(|c| match (mode, levels) {
                    (Mode::Off, _) => false,
                    (Mode::Auto, Some(l)) => of(l)[i][c] != Level::Proved,
                    (Mode::Runtime, _) | (Mode::Auto, None) => true,
                })
                .collect()
        };
        Checks {
            requires: m.fns.iter().enumerate().map(|(i, d)| pick(i, d.spec.requires.len(), &|l| &l.requires)).collect(),
            ensures: m.fns.iter().enumerate().map(|(i, d)| pick(i, d.spec.ensures.len(), &|l| &l.ensures)).collect(),
        }
    }

    pub fn count(&self) -> (usize, usize) {
        let all = self.requires.iter().chain(&self.ensures).flatten();
        let checked = all.clone().filter(|c| **c).count();
        (checked, all.count() - checked)
    }
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
    use crate::sexp::parse_all_spanned;
    use crate::solver::Z3;

    fn levels_of(src: &str) -> Option<(Module, ClauseLevels)> {
        let z3 = Z3::find(5000)?;
        let (f, s) = parse_all_spanned(src).unwrap();
        let m = lower(&f, &s).unwrap();
        let ty = crate::types::check(&m).unwrap();
        let results = crate::verify::discharge(crate::vc::generate(&m, &ty), &z3, None, 4);
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

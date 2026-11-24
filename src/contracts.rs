//! Which contract clauses still need run-time checks (M1-6): the level of
//! each clause, and the `Checks` a contract mode picks from them. The
//! levels come from proof results (`verify::levels`); this module only reads
//! them, so the runtime does not depend on the prover.

use crate::ast::Module;

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

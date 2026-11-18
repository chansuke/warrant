//! Discharges obligations with a solver and summarizes the outcome.

use crate::solver::{Outcome, Solver};
use crate::vc::{counterexample_sexp, Goal, Obligation};
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
}

impl VcResult {
    pub fn to_sexp(&self) -> String {
        let tail = match &self.status {
            Status::Proved => ":status proved".to_string(),
            Status::Failed { model } => format!(":status failed :counterexample {}", counterexample_sexp(model)),
            Status::Unknown { reason } => format!(":status unknown :reason {}", crate::sexp::quote_str(reason)),
            Status::Unsupported { reason } => format!(":status unsupported :reason {}", crate::sexp::quote_str(reason)),
        };
        format!("{} {} :ms {})", self.ob.head_sexp(), tail, crate::profile::ms(self.ns))
    }
}

pub fn discharge(obs: Vec<Obligation>, solver: &mut dyn Solver) -> Vec<VcResult> {
    obs.into_iter()
        .map(|ob| {
            let t = Instant::now();
            let status = match &ob.goal {
                Goal::Unsupported(reason) => Status::Unsupported { reason: reason.clone() },
                Goal::Script(s) => match solver.check(s, &ob.inputs) {
                    Outcome::Proved => Status::Proved,
                    Outcome::Failed { model } => Status::Failed { model },
                    Outcome::Unknown { reason } => Status::Unknown { reason },
                },
            };
            VcResult { ob, status, ns: t.elapsed().as_nanos() }
        })
        .collect()
}

/// `(smt :vcs N :proved P ... :issues (...))`: everything not proved is listed.
pub fn summary_sexp(results: &[VcResult], total_ns: u128) -> String {
    let count = |f: fn(&Status) -> bool| results.iter().filter(|r| f(&r.status)).count();
    let failed = count(|s| matches!(s, Status::Failed { .. }));
    let mut s = format!(
        "(smt :status {} :vcs {} :proved {} :failed {} :unknown {} :unsupported {} :ms {}",
        if failed > 0 { "failed" } else { "ok" },
        results.len(),
        count(|s| *s == Status::Proved),
        failed,
        count(|s| matches!(s, Status::Unknown { .. })),
        count(|s| matches!(s, Status::Unsupported { .. })),
        crate::profile::ms(total_ns)
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

//! Discharges obligations with a solver and summarizes the outcome.

use crate::cache::Cache;
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
    slow.sort_by(|a, b| b.ns.cmp(&a.ns));
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

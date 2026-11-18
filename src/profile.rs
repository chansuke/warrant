//! Machine-readable profiling. Everything is emitted as S-expressions with
//! unit-suffixed keys (`wall-ms`, `incl-ms`) so agents can parse it directly.

use crate::sexp::quote_str;
use std::collections::HashMap;

#[derive(Default)]
pub struct FnStat {
    pub calls: u64,
    /// Inclusive time, counted only at the outermost active call (no double
    /// counting under recursion).
    pub incl_ns: u128,
    active: u32,
}

#[derive(Default)]
pub struct Profiler {
    pub enabled: bool,
    pub fns: HashMap<String, FnStat>,
    pub calls: u64,
    pub closure_calls: u64,
    pub builtin_calls: u64,
    pub max_depth: usize,
    pub vec_allocs: u64,
    pub vec_elems: u64,
    pub contract_checks: u64,
    pub contract_ns: u128,
}

impl Profiler {
    pub fn new(enabled: bool) -> Self {
        Profiler { enabled, ..Default::default() }
    }

    pub fn enter(&mut self, name: &str, depth: usize) {
        self.calls += 1;
        if depth > self.max_depth {
            self.max_depth = depth;
        }
        if !self.enabled {
            return;
        }
        match self.fns.get_mut(name) {
            Some(s) => {
                s.calls += 1;
                s.active += 1;
            }
            None => {
                self.fns.insert(name.to_string(), FnStat { calls: 1, incl_ns: 0, active: 1 });
            }
        }
    }

    pub fn exit(&mut self, name: &str, ns: u128) {
        if let Some(s) = self.fns.get_mut(name) {
            s.active -= 1;
            if s.active == 0 {
                s.incl_ns += ns;
            }
        }
    }

    pub fn vec_alloc(&mut self, elems: usize) {
        self.vec_allocs += 1;
        self.vec_elems += elems as u64;
    }
}

pub fn ms(ns: u128) -> String {
    format!("{:.3}", ns as f64 / 1e6)
}

pub struct RunInfo<'a> {
    pub wall_ns: u128,
    /// The mode and what it erased: `auto :checked 2 :erased 12 ...`.
    pub contracts: &'a str,
    /// `None` when run with `--no-typecheck`.
    pub types_ns: Option<u128>,
}

pub fn report(file: &str, status: &str, parse_ns: u128, run: &RunInfo<'_>, p: &Profiler) -> String {
    let mut s = String::from("(report\n");
    s += &format!("  (file {})\n  (status {})\n", quote_str(file), status);
    let types = match run.types_ns {
        Some(ns) => format!("(types :status ok :ms {})", ms(ns)),
        None => "(types :status skipped)".into(),
    };
    s += &format!("  (check (parse-ms {}) {} (effects :status ok) (smt :status skipped :until M1-4))\n", ms(parse_ns), types);
    s += &format!(
        "  (run (wall-ms {}) (contracts {})\n       (calls {}) (closure-calls {}) (builtin-calls {}) (max-depth {})\n       (vec-allocs {}) (vec-elems {}) (contract-checks {}) (contract-ms {}))\n",
        ms(run.wall_ns),
        run.contracts,
        p.calls,
        p.closure_calls,
        p.builtin_calls,
        p.max_depth,
        p.vec_allocs,
        p.vec_elems,
        p.contract_checks,
        ms(p.contract_ns)
    );
    let mut hot: Vec<_> = p.fns.iter().collect();
    hot.sort_by(|a, b| b.1.incl_ns.cmp(&a.1.incl_ns).then(a.0.cmp(b.0)));
    s += "  (hot";
    for (name, st) in hot.iter().take(5) {
        let pct = if run.wall_ns > 0 { st.incl_ns as f64 * 100.0 / run.wall_ns as f64 } else { 0.0 };
        s += &format!(
            "\n    ({} :calls {} :incl-ms {} :pct {:.1})",
            name,
            st.calls,
            ms(st.incl_ns),
            pct
        );
    }
    s += "))";
    s
}

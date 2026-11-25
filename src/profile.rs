//! Machine-readable profiling. Everything is emitted as S-expressions with
//! unit-suffixed keys (`wall-ms`, `incl-ms`) so agents can parse it directly.

use crate::builtin::Builtin;
use crate::sexp::quote_str;
use std::collections::HashMap;
use std::time::Instant;

#[derive(Default)]
pub struct FnStat {
    pub calls: u64,
    /// Inclusive time, counted only at the outermost active call (no double
    /// counting under recursion).
    pub incl_ns: u128,
    /// Time in the function's own body and contracts, excluding callees.
    pub self_ns: u128,
    active: u32,
}

#[derive(Default)]
pub struct ClauseStat {
    pub checks: u64,
    pub ns: u128,
}

/// A clause as `check` numbers it: function, `requires` or `ensures`, index.
pub type ClauseKey = (String, &'static str, usize);

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
    pub clauses: HashMap<ClauseKey, ClauseStat>,
    /// Indexed by `Builtin as usize`.
    pub builtins: Vec<u64>,
    /// Arguments evaluated in a forked task (M2-5).
    pub forks: u64,
    /// Open calls: when each started, and its time so far outside its body.
    frames: Vec<(Instant, Span)>,
    /// The same for the code outside any open call: in a forked task, the
    /// arguments it evaluates for its caller.
    outer: Span,
}

/// What to take off, and add to, an open call's wall time to get its self
/// time.
#[derive(Default)]
struct Span {
    /// Time in its callees, and in the forks it waited on.
    callees: u128,
    /// Time its own code took in forks, on every thread.
    credit: u128,
}

/// One fork's times, for `Profiler::merge`.
pub struct ForkTimes {
    /// The open call's `callees` before the fork.
    pub before: u128,
    /// From the fork to the join.
    pub wall_ns: u128,
    /// Evaluating the earlier arguments, and the later ones in the task.
    pub mine_ns: u128,
    pub theirs_ns: u128,
}

impl Profiler {
    pub fn new(enabled: bool) -> Self {
        Profiler { enabled, builtins: vec![0; Builtin::ALL.len()], ..Default::default() }
    }

    pub fn builtin(&mut self, b: Builtin) {
        self.builtin_calls += 1;
        if self.enabled {
            self.builtins[b as usize] += 1;
        }
    }

    pub fn clause(&mut self, f: &str, which: &'static str, index: usize, ns: u128) {
        let s = self.clauses.entry((f.to_string(), which, index)).or_default();
        s.checks += 1;
        s.ns += ns;
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
                self.fns.insert(name.to_string(), FnStat { calls: 1, active: 1, ..Default::default() });
            }
        }
        self.frames.push((Instant::now(), Span::default()));
    }

    pub fn exit(&mut self, name: &str) {
        let Some((start, span)) = self.frames.pop() else { return };
        let ns = start.elapsed().as_nanos();
        self.span().callees += ns;
        if let Some(s) = self.fns.get_mut(name) {
            s.active -= 1;
            s.self_ns += (ns + span.credit).saturating_sub(span.callees);
            if s.active == 0 {
                s.incl_ns += ns;
            }
        }
    }

    fn span(&mut self) -> &mut Span {
        match self.frames.last_mut() {
            Some((_, span)) => span,
            None => &mut self.outer,
        }
    }

    /// The open call's time in callees so far, for `ForkTimes::before`.
    pub fn callees(&mut self) -> u128 {
        self.span().callees
    }

    /// The profiler of a forked task. Functions open here stay open there,
    /// so a task's calls of them do not count as outermost calls again.
    pub fn fork(&self) -> Profiler {
        let mut p = Profiler::new(self.enabled);
        for (name, s) in &self.fns {
            if s.active > 0 {
                p.fns.insert(name.clone(), FnStat { active: s.active, ..Default::default() });
            }
        }
        p
    }

    /// Adds a forked task's counts and times. The open call's self time
    /// leaves out the wait for the join and takes in what its own code did
    /// on both sides, so with tasks on other threads self times and the
    /// inclusive times of callees add up CPU time.
    pub fn merge(&mut self, task: Profiler, t: &ForkTimes) {
        self.calls += task.calls;
        self.closure_calls += task.closure_calls;
        self.builtin_calls += task.builtin_calls;
        self.max_depth = self.max_depth.max(task.max_depth);
        self.vec_allocs += task.vec_allocs;
        self.vec_elems += task.vec_elems;
        self.contract_checks += task.contract_checks;
        self.contract_ns += task.contract_ns;
        self.forks += task.forks;
        for (b, n) in self.builtins.iter_mut().zip(&task.builtins) {
            *b += n;
        }
        for (k, c) in task.clauses {
            let s = self.clauses.entry(k).or_default();
            s.checks += c.checks;
            s.ns += c.ns;
        }
        for (name, t) in task.fns {
            let s = self.fns.entry(name).or_default();
            s.calls += t.calls;
            s.incl_ns += t.incl_ns;
            s.self_ns += t.self_ns;
        }
        let span = self.span();
        let mine = t.mine_ns.saturating_sub(span.callees.saturating_sub(t.before));
        let theirs = (t.theirs_ns + task.outer.credit).saturating_sub(task.outer.callees);
        span.callees = t.before + t.wall_ns;
        span.credit += mine + theirs;
    }

    pub fn vec_alloc(&mut self, elems: usize) {
        self.vec_allocs += 1;
        self.vec_elems += elems as u64;
    }
}

/// Rows shown per section of the report.
const HOT: usize = 5;

/// CPU time used so far by the threads of this process that are alive, from
/// Linux's `/proc/self/task/*/schedstat`. `None` where that is not there.
pub fn cpu_ns() -> Option<u128> {
    let mut total = 0;
    for task in std::fs::read_dir("/proc/self/task").ok()? {
        let stat = std::fs::read_to_string(task.ok()?.path().join("schedstat")).ok()?;
        total += stat.split_whitespace().next()?.parse::<u128>().ok()?;
    }
    Some(total)
}

pub fn ms(ns: u128) -> String {
    format!("{:.3}", ns as f64 / 1e6)
}

pub struct RunInfo<'a> {
    pub wall_ns: u128,
    pub threads: usize,
    /// CPU time of the process's threads during the run, when the system
    /// reports it (`cpu_ns`).
    pub cpu_ns: Option<u128>,
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
    s += &format!("  (check (parse-ms {}) {} (effects :status ok))\n", ms(parse_ns), types);
    s += &format!(
        "  (run (wall-ms {}){} (threads {}) (forks {}) (contracts {})\n       (calls {}) (closure-calls {}) (builtin-calls {}) (max-depth {})\n       (vec-allocs {}) (vec-elems {}) (contract-checks {}) (contract-ms {}))\n",
        ms(run.wall_ns),
        run.cpu_ns.map(|ns| format!(" (cpu-ms {})", ms(ns))).unwrap_or_default(),
        run.threads,
        p.forks,
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
    let pct = |ns: u128, of: u128| if of > 0 { ns as f64 * 100.0 / of as f64 } else { 0.0 };
    let mut hot: Vec<_> = p.fns.iter().collect();
    hot.sort_by(|a, b| b.1.incl_ns.cmp(&a.1.incl_ns).then(a.0.cmp(b.0)));
    s += "  (hot";
    for (name, st) in hot.iter().take(HOT) {
        s += &format!(
            "\n    ({} :calls {} :incl-ms {} :self-ms {} :pct {:.1})",
            name,
            st.calls,
            ms(st.incl_ns),
            ms(st.self_ns),
            pct(st.incl_ns, run.wall_ns)
        );
    }
    s += ")\n  (clauses";
    let mut clauses: Vec<_> = p.clauses.iter().collect();
    clauses.sort_by(|a, b| b.1.ns.cmp(&a.1.ns).then(a.0.cmp(b.0)));
    for ((f, which, i), st) in clauses.iter().take(HOT) {
        s += &format!(
            "\n    ({} {} {} :checks {} :ms {} :pct-of-contracts {:.1})",
            f,
            which,
            i,
            st.checks,
            ms(st.ns),
            pct(st.ns, p.contract_ns)
        );
    }
    s += ")\n  (builtins";
    let mut used: Vec<(Builtin, u64)> = Builtin::ALL.iter().map(|b| (*b, p.builtins[*b as usize])).filter(|(_, n)| *n > 0).collect();
    used.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.name().cmp(b.0.name())));
    for (b, n) in used.iter().take(HOT * 2) {
        s += &format!(" ({} {})", b.name(), n);
    }
    s += "))";
    s
}

//! `warrant` CLI. Every output, including errors, is an S-expression on stdout
//! so an agent loop can parse it without scraping.
//!
//! Exit codes: 0 ok, 1 runtime/contract/effect error or failed check,
//! 2 parse/load/usage error, 3 performance budget exceeded.

use std::time::Instant;
use warrant::ast::{self, Module};
use warrant::cache::Cache;
use warrant::contracts::{self, Checks, ClauseLevels, Level, Mode};
use warrant::diag::Diag;
use warrant::eval::{self, Interp, Program};
use warrant::profile::{self, ms, RunInfo};
use warrant::sexp::{self, quote_str, Sexp, SpanTree};
use warrant::solver::Z3;
use warrant::types::TypeInfo;
use warrant::verify::VcResult;
use warrant::{effects, types, vc, verify, wisp};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // Tree-walking recursion is deep; give it room.
    let child = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || real_main(args))
        .expect("spawn main thread");
    std::process::exit(child.join().unwrap_or(101));
}

const USAGE: &str = "usage: warrant <command> FILE [options]
  run   FILE [--report] [--contracts auto|runtime|off] [--no-typecheck]   run (defn main [] ...)
  check FILE                                     parse, load, type-check, prove contracts with z3
  fmt   FILE [--to wisp|sexp]                    convert between canonical S-expr and the Wisp view
  bench FILE [-n N] [--contracts auto|runtime|off] [--no-typecheck]
                                                 time main N times; enforce (:budget (wall-ms N)) on main
Proof options (check, and run/bench with --contracts auto, the default):
  --timeout-ms N (per VC, default 2000)  --jobs N (default: all cores)  --cache-dir D  --no-cache
--no-contracts is --contracts off. FILE ending in .wisp is read as the Wisp view; anything else as canonical S-expr (.wrt).";

fn opt_value<'a>(opts: &'a [String], key: &str) -> Option<&'a str> {
    opts.iter().position(|o| o == key).and_then(|i| opts.get(i + 1)).map(|s| s.as_str())
}

fn usage_error(msg: &str) -> i32 {
    println!("(error :kind usage :msg {})", quote_str(msg));
    2
}

/// A positive integer option, or its default.
fn positive(opts: &[String], key: &str, default: u64) -> Result<u64, i32> {
    match opt_value(opts, key).map(str::parse::<u64>) {
        None => Ok(default),
        Some(Ok(n)) if n > 0 => Ok(n),
        Some(_) => Err(usage_error(&format!("{} must be a positive integer", key))),
    }
}

struct Source {
    forms: Vec<Sexp>,
    spans: Vec<SpanTree>,
    parse_ns: u128,
}

fn read_forms(path: &str) -> Result<Source, i32> {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            println!("(error :kind io :msg {})", quote_str(&e.to_string()));
            return Err(2);
        }
    };
    let t = Instant::now();
    let r = if path.ends_with(".wisp") { wisp::parse_spanned(&src) } else { sexp::parse_all_spanned(&src) };
    let parse_ns = t.elapsed().as_nanos();
    match r {
        Ok((forms, spans)) => Ok(Source { forms, spans, parse_ns }),
        Err(e) => {
            println!("{}", e.to_sexp());
            Err(2)
        }
    }
}

fn load(src: &Source) -> Result<Module, i32> {
    ast::lower(&src.forms, &src.spans).map_err(|d| {
        println!("{}", d.to_sexp());
        2
    })
}

/// `(types :status ok :ms T)` or the same with `:status error :errors (...)`.
fn section(name: &str, ns: u128, errors: &[Diag]) -> String {
    let status = if errors.is_empty() { "ok" } else { "error" };
    let mut s = format!("\n  ({} :status {} :ms {}", name, status, ms(ns));
    if !errors.is_empty() {
        s += " :errors (";
        for d in errors {
            s += &format!("\n    {}", d.to_sexp());
        }
        s += ")";
    }
    s + ")"
}

struct Prover {
    z3: Option<Z3>,
    jobs: usize,
    cache: Option<Cache>,
}

impl Prover {
    fn from_opts(opts: &[String]) -> Result<Prover, i32> {
        let timeout_ms = positive(opts, "--timeout-ms", 2000)?;
        let cores = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
        let jobs = positive(opts, "--jobs", cores)? as usize;
        let cache = (!opts.iter().any(|o| o == "--no-cache")).then(|| Cache::new(opt_value(opts, "--cache-dir").unwrap_or(".warrant/cache")));
        Ok(Prover { z3: Z3::find(timeout_ms), jobs, cache })
    }

    /// `None` when there is no solver to run.
    fn prove(&self, m: &Module, info: &TypeInfo) -> Option<(Vec<VcResult>, u128)> {
        let z3 = self.z3.as_ref()?;
        let t = Instant::now();
        let results = verify::discharge(vc::generate(m, info), z3, self.cache.as_ref(), self.jobs);
        Some((results, t.elapsed().as_nanos()))
    }
}

const NO_Z3: &str = "z3 not found on PATH";

/// What `run` and `bench` execute, and how its contracts were chosen.
struct Prepared {
    prog: Program,
    /// `auto :checked 2 :erased 12 :verify-ms 1.3`
    contracts: String,
    types_ns: Option<u128>,
}

/// Static checks, then the contract plan. Effects are always checked;
/// `--no-typecheck` skips types, and with them the proofs `auto` relies on.
fn prepare(m: &Module, opts: &[String]) -> Result<Prepared, i32> {
    let has = |f: &str| opts.iter().any(|o| o == f);
    let mode = match (opt_value(opts, "--contracts"), has("--no-contracts")) {
        (None, true) => Mode::Off,
        (None, false) => Mode::Auto,
        (Some(s), _) => Mode::parse(s).ok_or_else(|| usage_error(&format!("unknown --contracts {}; use auto, runtime or off", s)))?,
    };
    let mut errors = effects::check(m).1;
    let (mut typed, mut types_ns) = (None, None);
    if !has("--no-typecheck") {
        let t = Instant::now();
        match types::check(m) {
            Ok(info) => typed = Some(info),
            Err(es) => errors.extend(es),
        }
        types_ns = Some(t.elapsed().as_nanos());
    }
    if !errors.is_empty() {
        for d in errors {
            println!("{}", d.to_sexp());
        }
        return Err(1);
    }
    let (mut levels, mut extra) = (None, String::new());
    if mode == Mode::Auto {
        match &typed {
            None => extra = format!(" :note {}", quote_str("no proofs without type checking")),
            Some(info) => match Prover::from_opts(opts)?.prove(m, info) {
                None => extra = format!(" :note {}", quote_str(NO_Z3)),
                Some((results, ns)) => {
                    levels = Some(contracts::levels(m, &results));
                    extra = format!(" :verify-ms {}", ms(ns));
                }
            },
        }
    }
    let checks = Checks::new(m, mode, levels.as_ref());
    let (checked, erased) = checks.count();
    let contracts = format!("{} :checked {} :erased {}{}", mode.name(), checked, erased, extra);
    Ok(Prepared { prog: Program::new(m, &checks), contracts, types_ns })
}

/// `:level` for one function, with a per-clause breakdown when it has clauses.
fn level_sexp(levels: Option<&ClauseLevels>, f: usize, d: &ast::FnDecl) -> String {
    if d.spec.requires.is_empty() && d.spec.ensures.is_empty() {
        return ":level unspecified".into();
    }
    let Some(l) = levels else { return ":level runtime-checked".into() };
    let all: Vec<Level> = l.requires[f].iter().chain(&l.ensures[f]).copied().collect();
    let level = if all.iter().all(|x| *x == Level::Proved) { Level::Proved } else { Level::RuntimeChecked };
    let names = |ls: &[Level]| ls.iter().map(|x| x.name()).collect::<Vec<_>>().join(" ");
    format!(":level {} :clauses (requires [{}] ensures [{}])", level.name(), names(&l.requires[f]), names(&l.ensures[f]))
}

fn check(path: &str, src: &Source, m: &Module, opts: &[String]) -> i32 {
    let view = wisp::print_all(&src.forms);
    let roundtrip_ok = matches!(wisp::parse(&view), Ok(back) if back == src.forms);
    let t = Instant::now();
    let typed = types::check(m);
    let types_ns = t.elapsed().as_nanos();
    let type_errors = typed.as_ref().err().cloned().unwrap_or_default();
    let t = Instant::now();
    let (fx, effect_errors) = effects::check(m);
    let effects_ns = t.elapsed().as_nanos();
    let prover = match Prover::from_opts(opts) {
        Ok(p) => p,
        Err(c) => return c,
    };
    let proved = typed.as_ref().ok().and_then(|info| prover.prove(m, info));
    let levels = proved.as_ref().map(|(results, _)| contracts::levels(m, results));

    let mut s = format!(
        "(check\n  (file {})\n  (parse-ms {})\n  (roundtrip {})\n  (fns",
        quote_str(path),
        ms(src.parse_ns),
        if roundtrip_ok { "ok" } else { "fail" }
    );
    let recursive = m.recursive();
    for (i, d) in m.fns.iter().enumerate() {
        let declared = d.spec.effects.as_ref().map_or("undeclared".into(), ast::effects_sexp);
        s += &format!(
            "\n    ({} :effects {} :inferred {} :requires {} :ensures {} {}{})",
            d.name,
            declared,
            ast::effects_sexp(&fx.set(i)),
            d.spec.requires.len(),
            d.spec.ensures.len(),
            level_sexp(levels.as_ref(), i, d),
            if recursive[i] { " :termination assumed" } else { "" }
        );
    }
    s += ")";
    s += &section("types", types_ns, &type_errors);
    s += &section("effects", effects_ns, &effect_errors);
    s += "\n  ";
    let mut vcs_failed = false;
    match (&typed, &proved) {
        (Err(_), _) => s += "(smt :status skipped :reason \"type errors\")",
        (Ok(_), None) => s += &format!("(smt :status unavailable :reason {})", quote_str(NO_Z3)),
        (Ok(_), Some((results, ns))) => {
            vcs_failed = verify::any_failed(results);
            s += &verify::summary_sexp(results, *ns);
        }
    }
    s += ")";
    println!("{}", s);
    if roundtrip_ok && type_errors.is_empty() && effect_errors.is_empty() && !vcs_failed { 0 } else { 1 }
}

fn run(path: &str, src: &Source, m: &Module, opts: &[String]) -> i32 {
    let p = match prepare(m, opts) {
        Ok(p) => p,
        Err(c) => return c,
    };
    let report = opts.iter().any(|o| o == "--report");
    let mut it = Interp::new(&p.prog, report);
    let t = Instant::now();
    let r = it.call_main();
    let wall_ns = t.elapsed().as_nanos();
    let code = match &r {
        Ok(v) => {
            println!("(result {})", eval::show(v));
            0
        }
        Err(e) => {
            println!("{}", e.to_sexp());
            1
        }
    };
    if report {
        let status = if code == 0 { "ok" } else { "error" };
        let info = RunInfo { wall_ns, contracts: &p.contracts, types_ns: p.types_ns };
        println!("{}", profile::report(path, status, src.parse_ns, &info, &it.prof));
    }
    code
}

fn bench(path: &str, m: &Module, opts: &[String]) -> i32 {
    let n = match positive(opts, "-n", 10) {
        Ok(n) => n as usize,
        Err(c) => return c,
    };
    let p = match prepare(m, opts) {
        Ok(p) => p,
        Err(c) => return c,
    };
    let mut times = Vec::with_capacity(n);
    for i in 0..=n {
        let mut it = Interp::new(&p.prog, false);
        let t = Instant::now();
        if let Err(e) = it.call_main() {
            println!("{}", e.to_sexp());
            return 1;
        }
        if i > 0 {
            times.push(t.elapsed().as_nanos()); // run 0 is warm-up
        }
    }
    times.sort_unstable();
    let mean = times.iter().sum::<u128>() / n as u128;
    let median = times[n / 2];
    let mut s = format!(
        "(bench\n  (file {})\n  (n {}) (contracts {})\n  (wall-ms :min {} :median {} :mean {} :max {})",
        quote_str(path),
        n,
        p.contracts,
        ms(times[0]),
        ms(median),
        ms(mean),
        ms(times[n - 1])
    );
    let budget = p.prog.fns.get("main").and_then(|m| m.budget.as_ref()).and_then(|b| b.wall_ms);
    let mut code = 0;
    if let Some(limit) = budget {
        let over = median as f64 / 1e6 > limit;
        s += &format!("\n  (budget :wall-ms {} :median-ms {} :status {})", limit, ms(median), if over { "exceeded" } else { "ok" });
        if over {
            code = 3;
        }
    }
    s += ")";
    println!("{}", s);
    code
}

fn real_main(args: Vec<String>) -> i32 {
    if args.len() < 3 {
        eprintln!("{}", USAGE);
        return 2;
    }
    let (cmd, path, opts) = (args[1].as_str(), args[2].as_str(), &args[3..]);
    let src = match read_forms(path) {
        Ok(x) => x,
        Err(c) => return c,
    };
    if cmd == "fmt" {
        let default_to = if path.ends_with(".wisp") { "sexp" } else { "wisp" };
        match opt_value(opts, "--to").unwrap_or(default_to) {
            "wisp" => print!("{}", wisp::print_all(&src.forms)),
            "sexp" => print!("{}", sexp::pretty_all(&src.forms)),
            other => return usage_error(&format!("unknown --to {}", other)),
        }
        return 0;
    }
    if !matches!(cmd, "run" | "check" | "bench") {
        eprintln!("{}", USAGE);
        return 2;
    }
    let m = match load(&src) {
        Ok(m) => m,
        Err(c) => return c,
    };
    match cmd {
        "run" => run(path, &src, &m, opts),
        "check" => check(path, &src, &m, opts),
        _ => bench(path, &m, opts),
    }
}

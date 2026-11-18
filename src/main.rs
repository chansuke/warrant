//! `warrant` CLI. Every output, including errors, is an S-expression on stdout
//! so an agent loop can parse it without scraping.
//!
//! Exit codes: 0 ok, 1 runtime/contract/effect error or failed check,
//! 2 parse/load/usage error, 3 performance budget exceeded.

use std::time::Instant;
use warrant::ast::{self, Module};
use warrant::diag::Diag;
use warrant::solver::Z3;
use warrant::{effects, types, vc, verify};
use warrant::eval::{self, Interp, Program};
use warrant::profile::{self, ms, RunInfo};
use warrant::sexp::{self, quote_str, Sexp, SpanTree};
use warrant::wisp;

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
  run   FILE [--report] [--no-contracts] [--no-typecheck]   run (defn main [] ...)
  check FILE [--timeout-ms N]                             parse, load, type-check, prove contracts with z3
  fmt   FILE [--to wisp|sexp]                             convert between canonical S-expr and the Wisp view
  bench FILE [-n N] [--no-contracts] [--no-typecheck]     time main N times; enforce (:budget (wall-ms N)) on main
FILE ending in .wisp is read as the Wisp view; anything else as canonical S-expr (.wrt).";

fn opt_value<'a>(opts: &'a [String], key: &str) -> Option<&'a str> {
    opts.iter().position(|o| o == key).and_then(|i| opts.get(i + 1)).map(|s| s.as_str())
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

/// Static checks that gate `run` and `bench`. Effects are always checked;
/// `--no-typecheck` skips only types. Returns the type-checking time, or
/// `None` when it was skipped.
fn check_before_running(m: &Module, skip_types: bool) -> Result<Option<u128>, i32> {
    let mut errors = effects::check(m).1;
    let mut types_ns = None;
    if !skip_types {
        let t = Instant::now();
        errors.extend(types::check(m).err().unwrap_or_default());
        types_ns = Some(t.elapsed().as_nanos());
    }
    if errors.is_empty() {
        return Ok(types_ns);
    }
    for d in errors {
        println!("{}", d.to_sexp());
    }
    Err(1)
}

fn real_main(args: Vec<String>) -> i32 {
    if args.len() < 3 {
        eprintln!("{}", USAGE);
        return 2;
    }
    let (cmd, path, opts) = (args[1].as_str(), args[2].as_str(), &args[3..]);
    let has = |f: &str| opts.iter().any(|o| o == f);
    let src = match read_forms(path) {
        Ok(x) => x,
        Err(c) => return c,
    };
    let (forms, parse_ns) = (&src.forms, src.parse_ns);
    match cmd {
        "run" => {
            let module = match load(&src) {
                Ok(m) => m,
                Err(c) => return c,
            };
            let types_ns = match check_before_running(&module, has("--no-typecheck")) {
                Ok(t) => t,
                Err(c) => return c,
            };
            let prog = Program::new(&module);
            let (report, contracts) = (has("--report"), !has("--no-contracts"));
            let mut it = Interp::new(&prog, contracts, report);
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
                println!("{}", profile::report(path, status, parse_ns, &RunInfo { wall_ns, contracts, types_ns }, &it.prof));
            }
            code
        }
        "check" => {
            let module = match load(&src) {
                Ok(m) => m,
                Err(c) => return c,
            };
            let view = wisp::print_all(forms);
            let roundtrip_ok = matches!(wisp::parse(&view), Ok(back) if back == *forms);
            let t = Instant::now();
            let typed = types::check(&module);
            let types_ns = t.elapsed().as_nanos();
            let type_errors = typed.as_ref().err().cloned().unwrap_or_default();
            let t = Instant::now();
            let (fx, effect_errors) = effects::check(&module);
            let effects_ns = t.elapsed().as_nanos();
            let mut s = format!(
                "(check\n  (file {})\n  (parse-ms {})\n  (roundtrip {})\n  (fns",
                quote_str(path),
                ms(parse_ns),
                if roundtrip_ok { "ok" } else { "fail" }
            );
            let recursive = module.recursive();
            for (i, d) in module.fns.iter().enumerate() {
                let declared = d.spec.effects.as_ref().map_or("undeclared".into(), ast::effects_sexp);
                let level = if d.spec.requires.is_empty() && d.spec.ensures.is_empty() { "unspecified" } else { "runtime-checked" };
                s += &format!(
                    "\n    ({} :effects {} :inferred {} :requires {} :ensures {} :level {}{})",
                    d.name,
                    declared,
                    ast::effects_sexp(&fx.set(i)),
                    d.spec.requires.len(),
                    d.spec.ensures.len(),
                    level,
                    if recursive[i] { " :termination assumed" } else { "" }
                );
            }
            s += ")";
            s += &section("types", types_ns, &type_errors);
            s += &section("effects", effects_ns, &effect_errors);
            let timeout_ms: u64 = match opt_value(opts, "--timeout-ms").map(str::parse).unwrap_or(Ok(2000)) {
                Ok(n) if n > 0 => n,
                _ => {
                    println!("(error :kind usage :msg \"--timeout-ms must be a positive integer\")");
                    return 2;
                }
            };
            let mut vcs_failed = false;
            s += "\n  ";
            match (&typed, Z3::find(timeout_ms)) {
                (Err(_), _) => s += "(smt :status skipped :reason \"type errors\")",
                (Ok(_), None) => s += "(smt :status unavailable :reason \"z3 not found on PATH\")",
                (Ok(info), Some(mut z3)) => {
                    let t = Instant::now();
                    let results = verify::discharge(vc::generate(&module, info), &mut z3);
                    vcs_failed = verify::any_failed(&results);
                    s += &verify::summary_sexp(&results, t.elapsed().as_nanos());
                }
            }
            s += ")";
            println!("{}", s);
            if roundtrip_ok && type_errors.is_empty() && effect_errors.is_empty() && !vcs_failed { 0 } else { 1 }
        }
        "fmt" => {
            let default_to = if path.ends_with(".wisp") { "sexp" } else { "wisp" };
            match opt_value(opts, "--to").unwrap_or(default_to) {
                "wisp" => print!("{}", wisp::print_all(forms)),
                "sexp" => print!("{}", sexp::pretty_all(forms)),
                other => {
                    println!("(error :kind usage :msg {})", quote_str(&format!("unknown --to {}", other)));
                    return 2;
                }
            }
            0
        }
        "bench" => {
            let module = match load(&src) {
                Ok(m) => m,
                Err(c) => return c,
            };
            if let Err(c) = check_before_running(&module, has("--no-typecheck")) {
                return c;
            }
            let prog = Program::new(&module);
            let n: usize = match opt_value(opts, "-n").map(str::parse).unwrap_or(Ok(10)) {
                Ok(n) if n > 0 => n,
                _ => {
                    println!("(error :kind usage :msg \"-n must be a positive integer\")");
                    return 2;
                }
            };
            let contracts = !has("--no-contracts");
            let mut times = Vec::with_capacity(n);
            for i in 0..=n {
                let mut it = Interp::new(&prog, contracts, false);
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
                if contracts { "runtime" } else { "off" },
                ms(times[0]),
                ms(median),
                ms(mean),
                ms(times[n - 1])
            );
            let budget = prog.fns.get("main").and_then(|m| m.budget.as_ref()).and_then(|b| b.wall_ms);
            let mut code = 0;
            if let Some(limit) = budget {
                let over = median as f64 / 1e6 > limit;
                s += &format!(
                    "\n  (budget :wall-ms {} :median-ms {} :status {})",
                    limit,
                    ms(median),
                    if over { "exceeded" } else { "ok" }
                );
                if over {
                    code = 3;
                }
            }
            s += ")";
            println!("{}", s);
            code
        }
        _ => {
            eprintln!("{}", USAGE);
            2
        }
    }
}

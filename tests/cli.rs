//! Drives the real `warrant` binary: output shape and exit codes.
#![expect(clippy::disallowed_methods, reason = "these tests start the warrant binary")]

use std::process::Command;
use warrant::sexp::Sexp;

struct Out {
    code: i32,
    stdout: String,
}

fn warrant(args: &[&str]) -> Out {
    let o = Command::new(env!("CARGO_BIN_EXE_warrant")).args(args).output().expect("run warrant");
    Out { code: o.status.code().unwrap_or(-1), stdout: String::from_utf8_lossy(&o.stdout).into_owned() }
}

/// Writes `src` to a fresh file under the target temp dir and returns its path.
fn source(name: &str, src: &str) -> String {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("cli");
    std::fs::create_dir_all(&dir).unwrap();
    let p = dir.join(name);
    std::fs::write(&p, src).unwrap();
    p.to_string_lossy().into_owned()
}

const ILL_TYPED: &str = "(defn f [x : i64] -> i64\n  (if (< x 0) x true))\n(defn main [] -> i64 (f 1))\n";

#[test]
fn check_reports_type_errors_with_positions() {
    let o = warrant(&["check", &source("ill_typed.wrt", ILL_TYPED)]);
    assert_eq!(o.code, 1, "{}", o.stdout);
    assert!(o.stdout.contains("(types :status error"), "{}", o.stdout);
    assert!(
        o.stdout.contains("(error :kind type :at (line 2 col 3) :msg \"if branches differ: then is i64, else is Bool\")"),
        "{}",
        o.stdout
    );
}

#[test]
fn run_refuses_ill_typed_programs_unless_told_not_to_check() {
    let path = source("ill_typed_run.wrt", ILL_TYPED);
    let o = warrant(&["run", &path]);
    assert_eq!((o.code, o.stdout.trim_start().starts_with("(error :kind type")), (1, true), "{}", o.stdout);
    let o = warrant(&["run", &path, "--no-typecheck"]);
    assert_eq!((o.code, o.stdout.trim()), (0, "(result true)"));
}

#[test]
fn effect_leak_is_rejected_by_check_and_before_run() {
    let want = "(error :kind effect :at (line 9 col 7) :msg \"`add` declares (:effects []) but performs io via (log print)\")";
    let o = warrant(&["check", "examples/effect_leak.wrt"]);
    assert_eq!(o.code, 1, "{}", o.stdout);
    assert!(o.stdout.contains("(log :effects undeclared :inferred [io]"), "{}", o.stdout);
    assert!(o.stdout.contains(want), "{}", o.stdout);
    let o = warrant(&["run", "examples/effect_leak.wrt", "--no-typecheck"]);
    assert_eq!((o.code, o.stdout.trim()), (1, want));
}

fn have_z3() -> bool {
    warrant::solver::Z3::find_for_test(2000).is_some()
}

#[test]
fn examples_pass_check() {
    if !have_z3() {
        return;
    }
    for ex in ["examples/msort.wrt", "examples/msort.wisp", "examples/sum_sq_ok.wrt"] {
        let o = warrant(&["check", ex]);
        assert_eq!(o.code, 0, "{}: {}", ex, o.stdout);
        assert!(o.stdout.contains("(types :status ok"), "{}: {}", ex, o.stdout);
        assert!(o.stdout.contains(":failed 0 :unknown 0"), "{}: {}", ex, o.stdout);
    }
}

#[test]
fn check_rejects_sum_sq_overflow_with_a_counterexample_before_running() {
    if !have_z3() {
        return;
    }
    let o = warrant(&["check", "examples/sum_sq.wrt"]);
    assert_eq!(o.code, 1, "{}", o.stdout);
    let line = o.stdout.lines().find(|l| l.contains(":kind overflow :at (line 7 col 26)")).unwrap_or_else(|| panic!("{}", o.stdout));
    assert!(line.contains(":status failed :counterexample (xs ["), "{}", line);
}

#[test]
fn msort_proves_every_clause() {
    if !have_z3() {
        return;
    }
    let o = warrant(&["check", "examples/msort.wrt"]);
    assert!(o.stdout.contains(":proved 39 :failed 0 :unknown 0 :unsupported 0"), "{}", o.stdout);
    let merge = ":level proved :clauses (requires [proved proved] ensures [proved proved proved proved]) :termination assumed)";
    assert!(o.stdout.contains(merge), "{}", o.stdout);
    assert!(o.stdout.contains("(gen :effects [] :inferred [] :requires 4 :ensures 1 :level proved"), "{}", o.stdout);
}

/// The `(smt ...)` line's `:cached` count and `:reproved` list.
fn smt_cache_line(out: &str) -> (usize, String) {
    let line = out.lines().find(|l| l.trim_start().starts_with("(smt")).unwrap_or_else(|| panic!("{}", out));
    let cached = line.split(":cached ").nth(1).and_then(|r| r.split(' ').next()).unwrap().parse().unwrap();
    let reproved = line.split(":reproved (").nth(1).and_then(|r| r.split(')').next()).unwrap().to_string();
    (cached, reproved)
}

#[test]
fn cache_reproves_only_what_an_edit_can_affect() {
    if !have_z3() {
        return;
    }
    let base = std::fs::read_to_string("examples/msort.wrt").unwrap();
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cache-{}", std::process::id()));
    let cache = dir.to_string_lossy().into_owned();
    let check = |name: &str, src: &str| {
        let o = warrant(&["check", &source(name, src), "--cache-dir", &cache]);
        assert_eq!(o.code, 0, "{}", o.stdout);
        smt_cache_line(&o.stdout)
    };
    assert_eq!(check("c0.wrt", &base), (0, "gen main merge msort".into()));
    assert_eq!(check("c1.wrt", &base), (39, "".into()));

    let body_edit = base.replace("(* i 7919)", "(* i 7917)");
    let (_, reproved) = check("c2.wrt", &body_edit);
    assert_eq!(reproved, "gen", "a body edit re-proves only that function");

    let contract_edit = base.replace("(:ensures (= (len result) n))", "(:ensures (>= (len result) n) (<= (len result) n))");
    let (_, reproved) = check("c3.wrt", &contract_edit);
    assert_eq!(reproved, "gen main", "a contract edit also re-proves the callers");
}

#[test]
fn auto_erases_proved_clauses_and_keeps_the_rest() {
    if !have_z3() {
        return;
    }
    let o = warrant(&["run", "examples/msort.wrt", "--report"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(o.stdout.contains("(contracts auto :checked 0 :erased 14"), "{}", o.stdout);
    // Holds for gen's output but not for every input, so it cannot be proved.
    let base = std::fs::read_to_string("examples/msort.wrt").unwrap();
    let unproved = source(
        "auto_unproved.wrt",
        &base.replace(
            "(perm? result xs) (= (len result) (len xs))",
            "(perm? result xs) (= (len result) (len xs)) (all? (fn [x] (>= x 0)) result)",
        ),
    );
    let o = warrant(&["run", &unproved, "--report"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(o.stdout.contains("(contracts auto :checked 1 :erased 14"), "{}", o.stdout);
    for (mode, want) in [("runtime", "runtime :checked 14 :erased 0"), ("off", "off :checked 0 :erased 14")] {
        let o = warrant(&["bench", "examples/msort.wrt", "-n", "1", "--contracts", mode]);
        assert!(o.stdout.contains(&format!("(contracts {})", want)), "{}", o.stdout);
    }
    let o = warrant(&["bench", "examples/msort.wrt", "--contracts", "sometimes"]);
    assert_eq!(o.code, 2, "{}", o.stdout);
}

#[test]
fn auto_still_catches_an_ensures_it_could_not_prove() {
    if !have_z3() {
        return;
    }
    let src = "(defn bad-sort [xs : (Vec i64)] -> (Vec i64)\n  (:ensures (sorted? result))\n  (cons 99 xs))\n(defn main [] -> (Vec i64) (bad-sort [3 1 2]))\n";
    let o = warrant(&["run", &source("bad_sort.wrt", src), "--no-cache"]);
    assert_eq!(o.code, 1, "{}", o.stdout);
    assert!(o.stdout.starts_with("(error :kind contract :msg \"ensures failed in bad-sort"), "{}", o.stdout);
}

#[test]
fn spec_diff_blocks_weakened_contracts_and_lists_body_changes() {
    let base = std::fs::read_to_string("examples/msort.wrt").unwrap();
    let old = source("sd_old.wrt", &base);
    let body_only = source("sd_body.wrt", &base.replace("(* i 7919)", "(* i 7917)"));
    let o = warrant(&["spec-diff", &old, &body_only, "--no-smt"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(o.stdout.contains("(spec)\n  (impl\n    (gen :body changed))\n  (status ok))"), "{}", o.stdout);

    let dropped = source("sd_weak.wrt", &base.replace("(:ensures (sorted? result) (perm? result xs)", "(:ensures (perm? result xs)"));
    let o = warrant(&["spec-diff", &old, &dropped]);
    assert_eq!(o.code, 1, "{}", o.stdout);
    assert!(o.stdout.contains("(msort :clause ensures :change removed :verdict weakened :old (sorted? result))"), "{}", o.stdout);
    assert!(o.stdout.contains("(status weakened)"), "{}", o.stdout);

    let o = warrant(&["spec-diff", &old]);
    assert_eq!(o.code, 2);
}

#[test]
fn absurdly_deep_input_is_a_parse_error_not_a_crash() {
    let n = 1_000_000;
    let src = format!("(defn main [] -> i64 {}0{})", "(+ 1 ".repeat(n), ")".repeat(n + 1));
    let path = source("deep.wrt", &src);
    for args in [vec!["check", &path, "--no-cache"], vec!["run", &path, "--no-cache"], vec!["fmt", &path]] {
        let (cmd, o) = (args[0], warrant(&args));
        assert_eq!(o.code, 2, "{}: {}", cmd, o.stdout);
        assert!(o.stdout.contains("nesting deeper than 1000 levels"), "{}", o.stdout);
    }
}

#[test]
fn names_and_strings_with_smt_escape_characters_are_not_proved_wrongly() {
    if !have_z3() {
        return;
    }
    let cases = [
        ("pipe.wrt", "(defn f [a|b : i64 a_b : i64] -> i64 (:ensures (= result a_b)) a|b)\n(defn main [] -> i64 (f 1 2))\n"),
        ("bslash.wrt", "(defn f [] -> Str (:ensures (= result \"A\")) \"\\\\u{41}\")\n(defn main [] -> Str (f))\n"),
    ];
    for (name, src) in cases {
        let path = source(name, src);
        let o = warrant(&["check", &path, "--no-cache"]);
        assert_eq!(o.code, 1, "{}", o.stdout);
        assert!(o.stdout.contains(":kind ensures :clause 0") && o.stdout.contains(":status failed"), "{}", o.stdout);
        let o = warrant(&["run", &path, "--no-cache"]);
        assert_eq!(o.code, 1, "{}", o.stdout);
        assert!(o.stdout.starts_with("(error :kind contract"), "{}", o.stdout);
    }
}

#[test]
fn a_proof_cache_shipped_with_the_source_is_not_trusted() {
    if !have_z3() {
        return;
    }
    let root = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("planted-{}", std::process::id()));
    let (repo, home) = (root.join("repo"), root.join("home"));
    for d in [&repo, &home] {
        let _ = std::fs::remove_dir_all(d);
        std::fs::create_dir_all(d).unwrap();
    }
    std::fs::write(repo.join("p.wrt"), "(defn f [x : i64] -> i64 (:ensures (> result 0)) x)\n(defn main [] -> i64 (f -5))\n").unwrap();
    let run = || {
        let o = Command::new(env!("CARGO_BIN_EXE_warrant"))
            .args(["run", "p.wrt"])
            .current_dir(&repo)
            .env("HOME", &home)
            .env("XDG_CACHE_HOME", home.join("cache"))
            .output()
            .unwrap();
        (o.status.code(), String::from_utf8_lossy(&o.stdout).into_owned())
    };
    assert_eq!(run().0, Some(1));
    let user_cache = home.join("cache/warrant/proofs");
    assert!(std::fs::read_dir(&user_cache).is_ok_and(|mut d| d.next().is_some()), "proofs go to the user cache");
    let planted = repo.join(".warrant/cache");
    std::fs::create_dir_all(&planted).unwrap();
    for e in std::fs::read_dir(&user_cache).unwrap() {
        let e = e.unwrap();
        std::fs::copy(e.path(), planted.join(e.file_name())).unwrap();
        let text = std::fs::read_to_string(e.path()).unwrap();
        let forged = text.replacen(":status failed", ":status proved :was failed", 1);
        std::fs::write(planted.join(e.file_name()), forged).unwrap();
    }
    std::fs::remove_dir_all(&user_cache).unwrap();
    let (code, out) = run();
    assert_eq!(code, Some(1), "{}", out);
    assert!(out.starts_with("(error :kind contract"), "{}", out);
}

#[test]
fn report_breaks_time_down_by_function_clause_and_builtin() {
    let num = |line: &str, key: &str| -> f64 { line.split(key).nth(1).unwrap().split([' ', ')']).next().unwrap().parse().unwrap() };
    // On several threads `:self-ms` adds up every thread's time while
    // `:incl-ms` stays the wall time of the outermost call, so only one
    // thread keeps self within incl. The counts do not depend on threads.
    for threads in ["1", "4"] {
        let o = warrant(&["run", "examples/msort.wrt", "--report", "--contracts", "runtime", "--threads", threads]);
        assert_eq!(o.code, 0, "{}", o.stdout);
        let msort = o.stdout.lines().find(|l| l.trim_start().starts_with("(msort :calls")).expect("msort in hot");
        assert!(msort.contains(":calls 3999 "), "{}", msort);
        if threads == "1" {
            assert!(num(msort, ":self-ms ") <= num(msort, ":incl-ms "), "{}", msort);
            assert!(o.stdout.contains("(threads 1) (forks 0)"), "{}", o.stdout);
        } else {
            assert!(o.stdout.contains("(threads 4) (forks "), "{}", o.stdout);
            assert!(!o.stdout.contains("(forks 0)"), "{}", o.stdout);
        }
        // Clause numbers match `check`: perm? is merge's ensures 1.
        assert!(o.stdout.contains("(merge ensures 1 :checks 21587 "), "{}", o.stdout);
        assert!(o.stdout.contains("(perm? 25586)"), "{}", o.stdout);
        assert!(!o.stdout.contains("until M1"), "{}", o.stdout);
    }
}

/// On several threads, a function's own work in the arguments a task
/// evaluates still counts as its self time. Here most of `main`'s time is
/// its `range`, run beside the two calls of `w`; it counted as none.
#[test]
fn forked_arguments_count_in_self_time() {
    let num = |line: &str, key: &str| -> f64 { line.split(key).nth(1).unwrap().split([' ', ')']).next().unwrap().parse().unwrap() };
    let src = source(
        "forked_self.wrt",
        "(defn ones [n : i64] -> (Vec i64) (if (= n 0) [] (cons 1 (ones (- n 1)))))
         (defn w [n : i64] -> i64 (len (ones n)))
         (defn main [] -> i64 (+ (w 600000) (w 600000) (len (range 10000000))))\n",
    );
    let o = warrant(&["run", &src, "--report", "--threads", "4"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(o.stdout.contains("(forks 1)"), "{}", o.stdout);
    let main = o.stdout.lines().find(|l| l.trim_start().starts_with("(main :calls")).expect("main in hot");
    assert!(num(main, ":self-ms ") >= 0.25 * num(main, ":incl-ms "), "{}", main);
}

/// The exit code each error kind promises: 1 for a failure of the program,
/// 2 for input the tool could not take. A new kind must be added here.
fn exit_class(kind: &str) -> i32 {
    match kind {
        "type" | "effect" | "contract" | "overflow" | "div-zero" | "bounds" | "arity" | "unbound" | "stack" | "alloc" => 1,
        "parse" | "syntax" | "load" | "io" | "usage" => 2,
        "internal" => 101,
        other => panic!("kind {} has no exit class; add it to exit_class", other),
    }
}

/// `(error :kind K ...)` -> `K`.
fn error_kind(form: &Sexp) -> Option<&str> {
    let Sexp::List(items) = form else { return None };
    match items.as_slice() {
        [Sexp::Sym(head), Sexp::Kw(k), Sexp::Sym(kind), ..] if head == "error" && k == "kind" => Some(kind),
        _ => None,
    }
}

#[test]
fn every_error_kind_prints_one_sexp_and_exits_with_its_class() {
    let cases: &[(&str, &str, &[&str])] = &[
        ("parse", "(defn main [] -> i64 (\n", &[]),
        ("syntax", "(defn main 1)\n", &[]),
        ("load", "(defn main [] -> i64 1)\n(defn main [] -> i64 2)\n", &[]),
        ("load", "(defn f [] -> i64 1)\n", &[]),
        ("type", ILL_TYPED, &[]),
        ("type", "(defn main [] -> Int 1)\n", &[]),
        ("unbound", "(defn main [] -> i64 y)\n", &[]),
        ("effect", "(defn f [] -> i64 (:effects []) (do (print 1) 1))\n(defn main [] -> i64 (f))\n", &[]),
        ("overflow", "(defn main [] -> i64 (+ 9223372036854775807 1))\n", &["--no-contracts"]),
        ("div-zero", "(defn main [] -> i64 (/ 1 0))\n", &["--no-contracts"]),
        ("bounds", "(defn main [] -> i64 (get [1] 5))\n", &["--no-contracts"]),
        ("contract", "(defn f [x : i64] -> i64 (:requires (> x 0)) x)\n(defn main [] -> i64 (f 0))\n", &["--contracts", "runtime"]),
        ("usage", "(defn main [] -> i64 1)\n", &["--contracts", "sometimes"]),
    ];
    for (i, (want, src, opts)) in cases.iter().enumerate() {
        let path = source(&format!("kind-{}.wrt", i), src);
        let mut args = vec!["run", path.as_str()];
        args.extend_from_slice(opts);
        let o = warrant(&args);
        let forms =
            warrant::sexp::parse_all(&o.stdout).unwrap_or_else(|e| panic!("stdout is not S-expressions ({}): {}", e.to_sexp(), o.stdout));
        let kinds: Vec<&str> = forms.iter().filter_map(error_kind).collect();
        assert_eq!(kinds, [*want], "{}", o.stdout);
        assert_eq!(o.code, exit_class(want), "{}", o.stdout);
    }
    let missing = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("cli/no-such-file.wrt");
    let o = warrant(&["run", &missing.to_string_lossy()]);
    assert_eq!(o.code, exit_class("io"), "{}", o.stdout);
}

#[test]
fn unknown_or_incomplete_options_are_usage_errors() {
    let ok = source("options.wrt", "(defn main [] -> i64 1)\n");
    let other = source("options-other.wrt", "(defn main [] -> i64 2)\n");
    let cases: &[(&[&str], &str)] = &[
        (&["run", &ok, "--contrcts", "off"], "unknown option --contrcts for run"),
        (&["check", &ok, "--report"], "unknown option --report for check"),
        (&["fmt", &ok, "--no-cache"], "unknown option --no-cache for fmt"),
        (&["bench", &ok, "-n", "1", "extra"], "unknown option extra for bench"),
        (&["spec-diff", &ok, &other, "--no-smtt"], "unknown option --no-smtt for spec-diff"),
        (&["run", &ok, "--contracts"], "--contracts needs a value"),
    ];
    for (args, want) in cases {
        let o = warrant(args);
        assert_eq!(o.code, 2, "{:?}: {}", args, o.stdout);
        assert!(o.stdout.starts_with("(error :kind usage :msg ") && o.stdout.contains(want), "{:?}: {}", args, o.stdout);
    }
    let o = warrant(&["run", &ok, "--contracts", "off", "--no-cache", "--timeout-ms", "50"]);
    assert_eq!((o.code, o.stdout.trim()), (0, "(result 1)"));
}

/// A panic is a bug in warrant, yet stdout must still parse. Any input that
/// reaches a panic will do here; today a huge `-n` overflows a Vec capacity.
#[test]
fn a_panic_prints_an_internal_error_and_exits_101() {
    let o = warrant(&["bench", &source("panic.wrt", "(defn main [] -> i64 1)\n"), "-n", "18446744073709551615", "--contracts", "off"]);
    let forms =
        warrant::sexp::parse_all(&o.stdout).unwrap_or_else(|e| panic!("stdout is not S-expressions ({}): {}", e.to_sexp(), o.stdout));
    assert_eq!(forms.iter().filter_map(error_kind).collect::<Vec<_>>(), ["internal"], "{}", o.stdout);
    assert_eq!(o.code, exit_class("internal"), "{}", o.stdout);
}

#[test]
fn threads_must_be_a_positive_count() {
    for bad in ["0", "-1", "many"] {
        let o = warrant(&["run", "examples/msort.wrt", "--threads", bad]);
        assert_eq!(o.code, 2, "{}", o.stdout);
        assert!(o.stdout.starts_with("(error :kind usage :msg \"--threads must be a positive integer\")"), "{}", o.stdout);
    }
    let o = warrant(&["run", "examples/msort.wrt", "--threads", "100000"]);
    assert_eq!(o.code, 2, "{}", o.stdout);
    assert!(o.stdout.starts_with("(error :kind usage :msg \"--threads must be at most 1024\")"), "{}", o.stdout);
    let o = warrant(&["bench", "examples/msort.wrt", "-n", "1", "--threads", "2"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(o.stdout.contains("(threads 2)"), "{}", o.stdout);
}

/// `bench --scaling` times 1, 2, 4, ... threads and `--threads N` itself,
/// and compares each with this runtime on one thread.
#[test]
fn bench_scaling_compares_each_thread_count_with_one() {
    // `sexp::parse_all` reads no decimals, so the rows are read as text.
    let rows = |out: &str| -> Vec<(String, Vec<String>)> {
        let body = out.split("(scaling").nth(1).unwrap_or_else(|| panic!("no scaling: {}", out));
        body.lines()
            .map(str::trim)
            .filter(|l| l.starts_with("(threads "))
            .map(|l| {
                let words: Vec<&str> = l.split([' ', '(', ')']).filter(|w| !w.is_empty()).collect();
                (words[1].to_string(), words.iter().filter_map(|w| w.strip_prefix(':')).map(str::to_string).collect())
            })
            .collect()
    };
    let o = warrant(&["bench", "examples/msort.wrt", "-n", "2", "--threads", "5", "--scaling"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    let got = rows(&o.stdout);
    assert_eq!(got.iter().map(|(t, _)| t.as_str()).collect::<Vec<_>>(), ["1", "2", "4", "5"], "{}", o.stdout);
    // `:cpu-ms` is there where Linux reports CPU time.
    let cpu = std::path::Path::new("/proc/self/task").exists();
    for (t, keys) in &got {
        let mut want = vec!["median-ms", "cpu-ms", "forks", "speedup", "efficiency"];
        if !cpu {
            want.retain(|k| *k != "cpu-ms");
        }
        if t == "1" {
            want.truncate(want.len() - 2);
        }
        assert_eq!(keys, &want, "{}", o.stdout);
    }
    // The ratios follow from the medians, and the budget reads the last row.
    let num = |line: &str, key: &str| -> f64 {
        let at = line.find(key).unwrap_or_else(|| panic!("no {} in {}", key, line)) + key.len();
        line[at..].split([' ', ')']).next().and_then(|w| w.parse().ok()).unwrap_or_else(|| panic!("{} in {}", key, line))
    };
    let lines: Vec<&str> = o.stdout.lines().map(str::trim).filter(|l| l.starts_with("(threads ")).collect();
    let base = num(lines[0], ":median-ms ");
    for (line, t) in lines.iter().zip([1.0, 2.0, 4.0, 5.0]).skip(1) {
        let speedup = num(line, ":speedup ");
        assert!((speedup - base / num(line, ":median-ms ")).abs() < 0.02, "{}", o.stdout);
        assert!((num(line, ":efficiency ") - speedup / t).abs() < 0.01, "{}", o.stdout);
    }
    let budget = o.stdout.lines().find(|l| l.contains("(budget ")).unwrap_or_else(|| panic!("no budget: {}", o.stdout));
    assert!(budget.contains("(budget :wall-ms 500 "), "{}", o.stdout);
    assert_eq!(num(budget, ":median-ms "), num(lines[3], ":median-ms "), "{}", o.stdout);
    let o = warrant(&["bench", "examples/msort.wrt", "-n", "1", "--threads", "1", "--scaling"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert_eq!(rows(&o.stdout).len(), 1, "{}", o.stdout);
}

/// A value that looks like a flag stays the value of its option.
#[test]
fn an_option_value_is_not_read_as_a_flag() {
    // `--contracts off` proves nothing, so no cache directory is made.
    let o = warrant(&["bench", "examples/msort.wrt", "--cache-dir", "--scaling", "-n", "1", "--threads", "2", "--contracts", "off"]);
    assert_eq!(o.code, 0, "{}", o.stdout);
    assert!(!o.stdout.contains("(scaling"), "{}", o.stdout);
    assert!(o.stdout.contains("(wall-ms "), "{}", o.stdout);
    let o = warrant(&["run", "examples/msort.wrt", "--cache-dir", "--report", "--threads", "--report", "--contracts", "off"]);
    assert_eq!(o.code, 2, "{}", o.stdout);
    assert!(o.stdout.starts_with("(error :kind usage :msg \"--threads must be a positive integer\")"), "{}", o.stdout);
}

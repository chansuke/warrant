//! Drives the real `warrant` binary: output shape and exit codes.

use std::process::Command;

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
    assert!(o.stdout.contains("(error :kind type :at (line 2 col 3) :msg \"if branches differ: then is i64, else is Bool\")"), "{}", o.stdout);
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
    let ok = Command::new("z3").arg("--version").output().is_ok_and(|o| o.status.success());
    if !ok {
        eprintln!("z3 not found; skipping");
    }
    ok
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
fn msort_proves_everything_but_perm() {
    if !have_z3() {
        return;
    }
    let o = warrant(&["check", "examples/msort.wrt"]);
    assert!(o.stdout.contains(":proved 37 :failed 0 :unknown 0 :unsupported 2"), "{}", o.stdout);
    assert_eq!(o.stdout.matches("depends on perm?").count(), 2, "{}", o.stdout);
    assert!(o.stdout.contains("(merge :effects [] :inferred [] :requires 2 :ensures 4 :level runtime-checked :termination assumed)"), "{}", o.stdout);
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
    assert_eq!(check("c1.wrt", &base), (37, "".into()));

    let body_edit = base.replace("(* i 7919)", "(* i 7917)");
    let (_, reproved) = check("c2.wrt", &body_edit);
    assert_eq!(reproved, "gen", "a body edit re-proves only that function");

    let contract_edit = base.replace("(:ensures (= (len result) n))", "(:ensures (>= (len result) n) (<= (len result) n))");
    let (_, reproved) = check("c3.wrt", &contract_edit);
    assert_eq!(reproved, "gen main", "a contract edit also re-proves the callers");
}

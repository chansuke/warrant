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
fn examples_pass_check() {
    for ex in ["examples/msort.wrt", "examples/msort.wisp", "examples/sum_sq.wrt", "examples/effect_leak.wrt"] {
        let o = warrant(&["check", ex]);
        assert_eq!(o.code, 0, "{}: {}", ex, o.stdout);
        assert!(o.stdout.contains("(types :status ok"), "{}: {}", ex, o.stdout);
    }
}

//! SMT solvers behind one trait (D14). Scripts are plain SMT-LIB2 text, so a
//! different solver only needs another `Solver` implementation.

use crate::types::Ty;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Proved,
    /// The negated goal is satisfiable: `model` holds the offending inputs,
    /// already rendered as Warrant values.
    Failed { model: Vec<(String, String)> },
    Unknown { reason: String },
}

/// Solvers are shared across worker threads, one query per call.
pub trait Solver: Sync {
    /// Part of every cache key: the solver and every setting that can change
    /// its answer, such as the timeout.
    fn fingerprint(&self) -> String;
    /// `script` asserts the negated goal and ends without `(check-sat)`.
    /// `inputs` are the SMT constants to read back as a counterexample.
    /// `Err` means the solver could not be run at all.
    fn check(&self, script: &str, inputs: &[(String, Ty)]) -> std::io::Result<Outcome>;
}

/// Elements of a vector shown in a counterexample.
const MAX_SHOWN: i64 = 8;

pub struct Z3 {
    version: String,
    timeout_ms: u64,
}

impl Z3 {
    /// `None` when no `z3` binary is on the PATH.
    pub fn find(timeout_ms: u64) -> Option<Z3> {
        let out = Command::new("z3").arg("--version").output().ok()?;
        let version = String::from_utf8_lossy(&out.stdout).trim().to_string();
        out.status.success().then_some(Z3 { version, timeout_ms })
    }
}

struct Session {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Session {
    fn send(&mut self, cmd: &str) -> std::io::Result<()> {
        self.stdin.write_all(cmd.as_bytes())?;
        self.stdin.write_all(b"\n")?;
        self.stdin.flush()
    }

    /// One response: a bare word (`sat`) or a balanced S-expression.
    fn read(&mut self) -> std::io::Result<String> {
        let mut out = String::new();
        let mut depth = 0i32;
        loop {
            let mut line = String::new();
            if self.stdout.read_line(&mut line)? == 0 {
                return Ok(out);
            }
            for c in line.chars() {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            out += &line;
            if depth <= 0 && !out.trim().is_empty() {
                return Ok(out.trim().to_string());
            }
        }
    }

    fn value(&mut self, term: &str) -> std::io::Result<String> {
        self.send(&format!("(get-value ({}))", term))?;
        let r = self.read()?;
        // ((term value))
        let inner = r.trim().strip_prefix("((").and_then(|s| s.strip_suffix("))")).unwrap_or(&r);
        Ok(inner.strip_prefix(term).unwrap_or(inner).trim().to_string())
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.send("(exit)");
        let _ = self.child.wait();
    }
}

/// Renders an SMT value (`4`, `(- 4)`, `true`, `"s"`) as Warrant syntax.
fn atom_value(v: &str) -> String {
    let v = v.trim();
    match v.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        Some(n) => format!("-{}", n.trim()),
        None => v.to_string(),
    }
}

impl Z3 {
    fn run(&self, script: &str, inputs: &[(String, Ty)]) -> std::io::Result<Outcome> {
        let mut child = Command::new("z3")
            .args(["-in", &format!("-t:{}", self.timeout_ms)])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let stdin = child.stdin.take().expect("piped");
        let stdout = BufReader::new(child.stdout.take().expect("piped"));
        let mut s = Session { child, stdin, stdout };
        s.send(script)?;
        s.send("(check-sat)")?;
        let mut errors = Vec::new();
        let answer = loop {
            let r = s.read()?;
            if r.starts_with("(error") {
                errors.push(r);
                continue;
            }
            break r;
        };
        if !errors.is_empty() {
            return Ok(Outcome::Unknown { reason: format!("solver rejected the script: {}", errors.join(" ")) });
        }
        match answer.as_str() {
            "unsat" => Ok(Outcome::Proved),
            "sat" => {
                let mut model = Vec::new();
                for (name, ty) in inputs {
                    model.push((name.trim_matches('|').to_string(), self.render(&mut s, name, ty)?));
                }
                Ok(Outcome::Failed { model })
            }
            "unknown" => {
                s.send("(get-info :reason-unknown)")?;
                let r = s.read()?;
                let reason = r.split('"').nth(1).unwrap_or("unknown").to_string();
                Ok(Outcome::Unknown { reason })
            }
            other => Ok(Outcome::Unknown { reason: format!("unexpected solver output: {}", other) }),
        }
    }

    fn render(&self, s: &mut Session, term: &str, ty: &Ty) -> std::io::Result<String> {
        let Ty::Vec(elem) = ty else { return Ok(atom_value(&s.value(term)?)) };
        let suffix = crate::smt::vec_sort(elem).expect("only representable inputs are read back");
        let len: i64 = atom_value(&s.value(&format!("(len-{} {})", suffix, term))?).parse().unwrap_or(0);
        let mut items = Vec::new();
        for i in 0..len.clamp(0, MAX_SHOWN) {
            items.push(atom_value(&s.value(&format!("(select (arr-{} {}) {})", suffix, term, i))?));
        }
        if len > MAX_SHOWN {
            items.push(format!("... :len {}", len));
        }
        Ok(format!("[{}]", items.join(" ")))
    }
}

impl Solver for Z3 {
    fn fingerprint(&self) -> String {
        format!("{} -t:{}", self.version, self.timeout_ms)
    }

    fn check(&self, script: &str, inputs: &[(String, Ty)]) -> std::io::Result<Outcome> {
        self.run(script, inputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn z3() -> Option<Z3> {
        let z = Z3::find(2000);
        if z.is_none() {
            eprintln!("z3 not found; skipping");
        }
        z
    }

    #[test]
    fn proves_valid_goals_and_returns_counterexamples() {
        let Some(z) = z3() else { return };
        assert_eq!(z.check("(declare-const x Int)\n(assert (not (= (+ x 0) x)))", &[]).unwrap(), Outcome::Proved);
        let got = z.check("(declare-const |x| Int)\n(assert (not (> |x| -3)))\n(assert (= |x| -5))", &[("|x|".into(), Ty::I64)]).unwrap();
        assert_eq!(got, Outcome::Failed { model: vec![("x".into(), "-5".into())] });
    }

    #[test]
    fn script_errors_are_unknown_not_proved() {
        let Some(z) = z3() else { return };
        assert!(matches!(z.check("(assert (not undefined-thing))", &[]).unwrap(), Outcome::Unknown { .. }));
    }
}

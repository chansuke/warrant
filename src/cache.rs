//! Proof cache (M1-5, D15). One file per obligation, named by a hash of the
//! solver fingerprint and the script. The file stores the script too, so a
//! hash collision reads as a miss, never as someone else's proof.
//!
//! A script holds the function's own body and only the contracts of what it
//! calls. Editing a body therefore re-proves that function alone; editing a
//! contract re-proves the function and its callers.

use crate::sexp::{parse_all, quote_str, Sexp};
use crate::solver::Outcome;
use std::path::PathBuf;

pub struct Cache {
    dir: PathBuf,
}

/// FNV-1a: stable across Rust releases, unlike `DefaultHasher`.
fn fnv1a(parts: &[&str]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for p in parts {
        for b in p.bytes().chain(std::iter::once(0)) {
            h ^= b as u64;
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
    }
    h
}

fn kw<'a>(items: &'a [Sexp], key: &str) -> Option<&'a Sexp> {
    items.windows(2).find(|w| w[0] == Sexp::Kw(key.into())).map(|w| &w[1])
}

fn str_of(e: Option<&Sexp>) -> Option<&str> {
    match e {
        Some(Sexp::Str(s)) => Some(s),
        _ => None,
    }
}

impl Cache {
    pub fn new(dir: impl Into<PathBuf>) -> Cache {
        Cache { dir: dir.into() }
    }

    fn path(&self, fingerprint: &str, script: &str) -> PathBuf {
        self.dir.join(format!("{:016x}.sexp", fnv1a(&[fingerprint, script])))
    }

    pub fn get(&self, fingerprint: &str, script: &str) -> Option<Outcome> {
        let text = std::fs::read_to_string(self.path(fingerprint, script)).ok()?;
        let forms = parse_all(&text).ok()?;
        let Some(Sexp::List(items)) = forms.first() else { return None };
        if str_of(kw(items, "fingerprint")) != Some(fingerprint) || str_of(kw(items, "script")) != Some(script) {
            return None;
        }
        match kw(items, "status")? {
            Sexp::Sym(s) if s == "proved" => Some(Outcome::Proved),
            Sexp::Sym(s) if s == "unknown" => Some(Outcome::Unknown { reason: str_of(kw(items, "reason"))?.to_string() }),
            Sexp::Sym(s) if s == "failed" => {
                let Some(Sexp::List(pairs)) = kw(items, "model") else { return None };
                let model = pairs
                    .iter()
                    .map(|p| match p {
                        Sexp::List(kv) => match kv.as_slice() {
                            [Sexp::Str(k), Sexp::Str(v)] => Some((k.clone(), v.clone())),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Outcome::Failed { model })
            }
            _ => None,
        }
    }

    /// Best effort: a cache that cannot be written only costs a re-proof.
    pub fn put(&self, fingerprint: &str, script: &str, o: &Outcome) {
        let status = match o {
            Outcome::Proved => "proved".to_string(),
            Outcome::Failed { model } => {
                let pairs: Vec<String> = model.iter().map(|(k, v)| format!("({} {})", quote_str(k), quote_str(v))).collect();
                format!("failed :model ({})", pairs.join(" "))
            }
            Outcome::Unknown { reason } => format!("unknown :reason {}", quote_str(reason)),
        };
        let text = format!("(entry :fingerprint {} :status {}\n  :script {})\n", quote_str(fingerprint), status, quote_str(script));
        let path = self.path(fingerprint, script);
        // Write then rename, so a concurrent `check` never reads half a file.
        let tmp = path.with_extension(format!("tmp{}-{:?}", std::process::id(), std::thread::current().id()));
        let _ = std::fs::create_dir_all(&self.dir)
            .and_then(|()| std::fs::write(&tmp, text))
            .and_then(|()| std::fs::rename(&tmp, &path));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_cache(name: &str) -> Cache {
        let dir = std::env::temp_dir().join(format!("warrant-cache-test-{}-{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        Cache::new(dir)
    }

    #[test]
    fn stores_and_reads_back_every_outcome() {
        let c = temp_cache("roundtrip");
        let failed = Outcome::Failed { model: vec![("xs".into(), "[1 \"q\" 3]".into())] };
        for (script, o) in [("a\n\"b\"", Outcome::Proved), ("c", failed), ("d", Outcome::Unknown { reason: "timeout".into() })] {
            assert_eq!(c.get("z3", script), None);
            c.put("z3", script, &o);
            assert_eq!(c.get("z3", script), Some(o));
        }
    }

    #[test]
    fn concurrent_writers_never_expose_a_partial_entry() {
        let c = temp_cache("race");
        let script = "x".repeat(1 << 20);
        let failed = Outcome::Failed { model: vec![("xs".into(), "[1 2 3]".into())] };
        std::thread::scope(|s| {
            for w in 0..8 {
                let (c, script, failed) = (&c, &script, &failed);
                s.spawn(move || {
                    for _ in 0..40 {
                        if w % 2 == 0 {
                            c.put("z3", script, failed);
                        } else if let Some(o) = c.get("z3", script) {
                            assert_eq!(&o, failed);
                        } else {
                            assert!(!c.path("z3", script).exists() || c.get("z3", script).is_some(), "a written entry read as a miss");
                        }
                    }
                });
            }
        });
        assert_eq!(c.get("z3", &script), Some(failed));
        let leftovers = std::fs::read_dir(&c.dir).unwrap().filter(|e| e.as_ref().unwrap().path().extension() != Some("sexp".as_ref()));
        assert_eq!(leftovers.count(), 0, "temporary files are renamed away");
    }

    #[test]
    fn a_different_fingerprint_or_a_colliding_file_is_a_miss() {
        let c = temp_cache("miss");
        c.put("z3 -t:2000", "s", &Outcome::Proved);
        assert_eq!(c.get("z3 -t:5000", "s"), None);
        let forged = c.path("z3 -t:2000", "other");
        std::fs::copy(c.path("z3 -t:2000", "s"), &forged).unwrap();
        assert_eq!(c.get("z3 -t:2000", "other"), None);
    }
}

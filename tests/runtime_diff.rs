//! Differential test of the IR runtime (`rt`) against the M1 interpreter
//! (`eval`): every program must give the same printed value, or the same
//! error kind, message and trace. Programs come from a fixed-seed generator
//! that leans on what the two evaluators do differently: frame slots,
//! captures, shadowing, closures, contracts, effects and dynamic type errors.

use warrant::ast::{lower, Module};
use warrant::contracts::{Checks, Mode};
use warrant::sexp::parse_all_spanned;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len() as u64) as usize]
    }
}

/// Generates expressions over the names in scope. Names repeat on purpose
/// so that `let` and `fn` shadow outer bindings.
struct Gen {
    r: Rng,
    ints: Vec<String>,
    vecs: Vec<String>,
    /// False inside `helper`, which must not recurse: its vectors would grow
    /// without bound long before the depth limit.
    may_call_helper: bool,
}

const INT_NAMES: &[&str] = &["a", "x", "k"];
const LITS: &[&str] = &["0", "1", "-1", "2", "3", "7", "-7", "100", "9223372036854775807"];

impl Gen {
    fn int_var(&mut self) -> String {
        if self.ints.is_empty() || self.r.below(4) == 0 {
            return self.r.pick(LITS).to_string();
        }
        let i = self.r.below(self.ints.len() as u64) as usize;
        self.ints[i].clone()
    }

    fn vec_var(&mut self) -> String {
        if self.vecs.is_empty() || self.r.below(5) == 0 {
            return format!("[{} {}]", self.r.pick(LITS), self.r.pick(LITS));
        }
        let i = self.r.below(self.vecs.len() as u64) as usize;
        self.vecs[i].clone()
    }

    /// `f(name)` with `name` bound as an int inside it.
    fn with_int(&mut self, name: &str, f: impl FnOnce(&mut Gen) -> String) -> String {
        self.ints.push(name.to_string());
        let s = f(self);
        self.ints.pop();
        s
    }

    fn int(&mut self, d: u32) -> String {
        if d == 0 {
            return self.int_var();
        }
        match self.r.below(16) {
            0 => self.int_var(),
            1 => format!("(+ {} {})", self.int(d - 1), self.int(d - 1)),
            2 => format!("(* {} {})", self.int(d - 1), self.int(d - 1)),
            3 => format!("(- {})", self.int(d - 1)),
            4 => format!("({} {} {})", self.r.pick(&["/", "mod"]), self.int(d - 1), self.int(d - 1)),
            5 => format!("(if {} {} {})", self.bool(d - 1), self.int(d - 1), self.int(d - 1)),
            6 => {
                let n = self.r.pick(INT_NAMES);
                let v = self.int(d - 1);
                let m = self.r.pick(INT_NAMES);
                let w = self.with_int(n, |g| g.int(d - 1));
                let body = self.with_int(n, |g| g.with_int(m, |g| g.int(d - 1)));
                format!("(let [{} {} {} {}] {})", n, v, m, w, body)
            }
            7 => format!("(get {} {})", self.vec(d - 1), self.int(d - 1)),
            8 => format!("(len {})", self.vec(d - 1)),
            9 => {
                let body = self.with_int("acc", |g| g.with_int("e", |g| g.int(d - 1)));
                format!("(fold (fn [acc e] {}) {} {})", body, self.int(d - 1), self.vec(d - 1))
            }
            10 => {
                let n = self.r.pick(INT_NAMES);
                let body = self.with_int(n, |g| g.int(d - 1));
                format!("((fn [{}] {}) {})", n, body, self.int(d - 1))
            }
            11 => {
                let body = self.with_int("y", |g| g.int(d - 1));
                format!("(twice (fn [y] {}) {})", body, self.int(d - 1))
            }
            12 => {
                let n = self.r.pick(INT_NAMES);
                let inner = self.with_int(n, |g| g.with_int("y", |g| g.int(d - 1)));
                format!("(let [f (fn [{}] (fn [y] {}))] ((f {}) {}))", n, inner, self.int(d - 1), self.int(d - 1))
            }
            13 => format!("(do (print {}) {})", self.int(d - 1), self.int(d - 1)),
            14 if self.may_call_helper => format!("(helper {} {})", self.int(d - 1), self.vec(d - 1)),
            14 => self.int_var(),
            // A dynamic type error: only reachable without the type checker.
            _ => format!("(+ {} {})", self.int(d - 1), self.r.pick(&["true", "[1]", "\"s\"", "twice"])),
        }
    }

    fn bool(&mut self, d: u32) -> String {
        match self.r.below(7) {
            0 => format!("(< {} {})", self.int(d), self.int(d)),
            1 => format!("(= {} {})", self.int(d), self.int(d)),
            2 if d > 0 => format!("({} {} {})", self.r.pick(&["and", "or"]), self.bool(d - 1), self.bool(d - 1)),
            3 if d > 0 => format!("(not {})", self.bool(d - 1)),
            4 => format!("(empty? {})", self.vec(d)),
            5 => format!("(sorted? {})", self.vec(d)),
            _ => self.r.pick(&["true", "false", "(= [1 2] [1 2])", "(= twice twice)"]).to_string(),
        }
    }

    fn vec(&mut self, d: u32) -> String {
        if d == 0 {
            return self.vec_var();
        }
        match self.r.below(9) {
            0 | 1 => self.vec_var(),
            2 => format!("(rest {})", self.vec(d - 1)),
            3 => format!("(cons {} {})", self.int(d - 1), self.vec(d - 1)),
            4 => format!("(concat {} {})", self.vec(d - 1), self.vec(d - 1)),
            5 => format!("(slice {} {} {})", self.vec(d - 1), self.int(d - 1), self.int(d - 1)),
            6 => {
                let body = self.with_int("e", |g| g.int(d - 1));
                format!("(map (fn [e] {}) {})", body, self.vec(d - 1))
            }
            7 => {
                let body = self.with_int("e", |g| g.bool(d - 1));
                format!("(filter (fn [e] {}) {})", body, self.vec(d - 1))
            }
            _ => format!("(range {})", self.r.pick(&["0", "3", "-1"])),
        }
    }

    fn program(&mut self) -> String {
        let fx = |g: &mut Gen| g.r.pick(&["", "(:effects [])", "(:effects [io])"]).to_string();
        self.may_call_helper = false;
        self.ints = vec!["a".into()];
        self.vecs = vec!["v".into()];
        let req = if self.r.below(3) == 0 { format!("(:requires {})", self.bool(1)) } else { String::new() };
        let ens = if self.r.below(3) == 0 {
            let e = self.with_int("result", |g| g.bool(1));
            format!("(:ensures {})", e)
        } else {
            String::new()
        };
        let helper = format!("(defn helper [a : i64 v : (Vec i64)] -> i64 {} {} {} {})", fx(self), req, ens, self.int(3));
        self.may_call_helper = true;
        self.ints.clear();
        self.vecs.clear();
        let body = if self.r.below(2) == 0 { format!("(helper {} {})", self.int(2), self.vec(2)) } else { self.int(4) };
        let main = format!("(defn main [] -> i64 {} {})", fx(self), body);
        format!("(defn twice [f : (Fn [i64] i64) x : i64] -> i64 (f (f x)))\n{}\n{}\n", helper, main)
    }
}

fn module(src: &str) -> Module {
    let (forms, spans) = parse_all_spanned(src).unwrap();
    lower(&forms, &spans).unwrap_or_else(|e| panic!("generated a program lower rejects: {:?}\n{}", e, src))
}

type Outcome = Result<String, (String, String, Vec<String>)>;

fn run_m1(m: &Module, mode: Mode) -> Outcome {
    let prog = warrant::eval::Program::new(m, &Checks::new(m, mode, None));
    let mut it = warrant::eval::Interp::new(&prog, true);
    let r = it.call_main().map(|v| warrant::eval::show(&v)).map_err(|e| (e.kind.to_string(), e.msg, e.trace));
    let p = &it.prof;
    r.map(|v| format!("{} calls {} closures {} builtins {} allocs {} elems {}", v, p.calls, p.closure_calls, p.builtin_calls, p.vec_allocs, p.vec_elems))
}

fn run_ir(m: &Module, mode: Mode) -> Outcome {
    let prog = warrant::ir::Program::new(m, &Checks::new(m, mode, None));
    let mut it = warrant::rt::Interp::new(&prog, true);
    let r = it.call_main().map(|v| prog.show(&v)).map_err(|e| (e.kind.to_string(), e.msg, e.trace));
    let p = &it.prof;
    r.map(|v| format!("{} calls {} closures {} builtins {} allocs {} elems {}", v, p.calls, p.closure_calls, p.builtin_calls, p.vec_allocs, p.vec_elems))
}

/// The outcome with every contract checked, after checking that the
/// runtimes agree with contracts both on and off.
fn same(src: &str) -> Outcome {
    let m = module(src);
    let mut outcomes = [Mode::Runtime, Mode::Off].map(|mode| {
        let (old, new) = (run_m1(&m, mode), run_ir(&m, mode));
        assert_eq!(old, new, "the runtimes disagree ({:?}) on:\n{}", mode.name(), src);
        new
    });
    std::mem::replace(&mut outcomes[0], Ok(String::new()))
}

/// Both interpreters recurse on the Rust stack; the CLI gives them 1 GiB.
fn on_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new().stack_size(1 << 30).spawn(f).unwrap().join().unwrap();
}

#[test]
fn examples_agree() {
    on_big_stack(|| {
        for src in [
            include_str!("../examples/msort.wrt"),
            include_str!("../examples/sum_sq.wrt"),
            include_str!("../examples/sum_sq_ok.wrt"),
            include_str!("../examples/effect_leak.wrt"),
        ] {
            let _ = same(src);
        }
    });
}

#[test]
fn generated_programs_agree() {
    on_big_stack(|| {
        let mut g = Gen { r: Rng(0x5eed_d1ff_0f12_7a3c), ints: Vec::new(), vecs: Vec::new(), may_call_helper: true };
        let (mut ok, mut kinds) = (0, std::collections::BTreeMap::new());
        for _ in 0..3000 {
            match same(&g.program()) {
                Ok(_) => ok += 1,
                Err((kind, _, _)) => *kinds.entry(kind).or_insert(0) += 1,
            }
        }
        eprintln!("ok {} errors {:?}", ok, kinds);
        // The generator must reach values and the error kinds the runtimes raise.
        assert!(ok >= 300, "ok {} errors {:?}", ok, kinds);
        for k in ["type", "overflow", "bounds", "div-zero", "effect", "contract"] {
            assert!(kinds.get(k).copied().unwrap_or(0) >= 10, "too few {} errors: {:?}", k, kinds);
        }
    });
}

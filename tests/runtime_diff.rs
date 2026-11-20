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

/// Counters both runtimes keep, compared on errors too. Printed output is
/// not compared: both write it to stdout directly. `vec-allocs` and
/// `vec-elems` differ on purpose: the IR runtime shares and reuses buffers.
fn counters(p: &warrant::profile::Profiler) -> String {
    let clauses: std::collections::BTreeMap<_, _> = p.clauses.iter().map(|(k, v)| (k.clone(), v.checks)).collect();
    format!(
        "calls {} closures {} builtins {} contract-checks {} clauses {:?}",
        p.calls, p.closure_calls, p.builtin_calls, p.contract_checks, clauses
    )
}

fn run_m1(m: &Module, checks: &Checks) -> (Outcome, String) {
    let prog = warrant::eval::Program::new(m, checks);
    let mut it = warrant::eval::Interp::new(&prog, true);
    let r = it.call_main().map(|v| warrant::eval::show(&v)).map_err(|e| (e.kind.to_string(), e.msg, e.trace));
    (r, counters(&it.prof))
}

fn run_ir(m: &Module, checks: &Checks) -> (Outcome, String) {
    let prog = warrant::ir::Program::new(m, checks);
    let mut it = warrant::rt::Interp::new(&prog, true);
    let r = it.call_main().map(|v| prog.show(&v)).map_err(|e| (e.kind.to_string(), e.msg, e.trace));
    (r, counters(&it.prof))
}

fn agree(src: &str, m: &Module, checks: &Checks) -> Outcome {
    let (old, new) = (run_m1(m, checks), run_ir(m, checks));
    assert_eq!(old, new, "the runtimes disagree on:\n{}", src);
    new.0
}

/// The outcome with every contract checked, after checking that the
/// runtimes agree with contracts both on and off.
fn same(src: &str) -> Outcome {
    let m = module(src);
    let on = agree(src, &m, &Checks::new(&m, Mode::Runtime, None));
    let _ = agree(src, &m, &Checks::new(&m, Mode::Off, None));
    on
}

fn error(kind: &str, msg: &str, trace: &[&str]) -> Outcome {
    Err((kind.into(), msg.into(), trace.iter().map(|s| s.to_string()).collect()))
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
fn fixed_cases_agree() {
    on_big_stack(|| {
        let make = "(defn make [x : i64 k : i64] -> (Fn [i64] (Fn [] i64))
                      (fn [x] (let [y (+ x 1) f (fn [] (+ y k)) y (+ y 100)] (fn [] (+ (f) y)))))";
        let escaping = format!("{}(defn main [] -> i64 (let [mk (make 1000 10) f (mk 2) g (mk 3)] (+ (f) (g))))", make);
        assert_eq!(same(&escaping).unwrap(), "234");
        let deep = "(defn down [n : i64] -> i64 (if (= n 0) (/ 1 0) (down (- n 1)))) (defn main [] -> i64 (down 20))";
        assert_eq!(same(deep), error("div-zero", "(/ 1 0)", &["down"; 16]));
        for (src, want) in [
            ("(defn f [] -> i64 1)", error("load", "no (defn main [] ...) found", &[])),
            ("(defn main [] -> i64 ((fn [x] x) 1 2))", error("arity", "fn expects 1 args, got 2", &["main"])),
            ("(defn g [x : i64] -> i64 x) (defn main [] -> i64 (g 1 2))", error("arity", "g expects 1 args, got 2", &["main"])),
            ("(defn main [] -> i64 (if 1 2 3))", error("type", "if condition must be bool, got i64", &["main"])),
            ("(defn main [] -> Bool (and true 1))", error("type", "and expects bool, got i64", &["main"])),
            ("(defn main [] -> i64 (1 2))", error("type", "cannot call a value of type i64", &["main"])),
            ("(defn main [] -> i64 ((do (print \"callee\") 0) (do (print \"arg\") (/ 1 0))))", error("div-zero", "(/ 1 0)", &["main"])),
        ] {
            assert_eq!(same(src), want, "{}", src);
        }
    });
}

/// The IR runtime updates a vector in place only when nothing else refers to
/// its buffer. Each case shares a buffer one way and then writes through one
/// of the sharers; the M1 interpreter, which always copies, is the reference.
#[test]
fn shared_vectors_never_change() {
    on_big_stack(|| {
        for body in [
            "(let [v [1 2 3] w (rest v) x (cons 9 w) y (cons 8 w)] (concat (concat x y) (concat w v)))",
            "(let [a (rest [1 2 3]) b (concat a [4]) c (concat a [5])] (concat b c))",
            "(let [v [1 2 3 4] s (slice v 0 2) t (concat s [9])] (concat t v))",
            "(let [v [1 2 3 4] s (slice v 0 2)] (concat s [9]))",
            "(let [v [1 2 3 4] s (slice v 1 3) t (cons 0 s)] (concat t (slice v 2 4)))",
            "(let [v [1 2] f (fn [] v) w (cons 0 v)] (concat (f) w))",
            "(let [v [1 2] f (fn [] (cons 7 v))] (concat (f) (concat (f) v)))",
            "(let [v (range 4)] (if (empty? v) v (concat (rest v) (rest v))))",
            "(let [v [5 6]] (concat (map (fn [x] (+ x (len v))) v) v))",
            "(push [1 2 3] 4)",
            "(let [v [1 2]] (concat (push v 3) (push v 4)))",
            "(keep [1 2 3])",
            "(alias [1 2 3 4])",
        ] {
            let src = format!(
                "(defn push [v : (Vec i64) x : i64] -> (Vec i64) (concat v [x]))
                 (defn keep [v : (Vec i64)] -> (Vec i64) (:ensures (= (len result) (+ (len v) 1))) (cons 0 (rest (cons 1 v))))
                 (defn alias [v : (Vec i64)] -> (Vec i64) (:ensures (= result v) (= (cons 9 (slice result 1 3)) [9 2 3])) v)
                 (defn main [] -> (Vec i64) {})",
                body
            );
            assert!(same(&src).is_ok(), "{}", src);
        }
    });
}

/// Only some clauses kept, as `--contracts auto` leaves them: the kept one
/// keeps its source index, and `result` is a parameter in `requires`.
#[test]
fn a_partial_clause_mask_agrees() {
    on_big_stack(|| {
        let src = "(defn f [result : i64] -> i64
                     (:requires (= result 7))
                     (:ensures false (= ((fn [] result)) 9))
                     (do (let [result 99] result) (+ result 2)))
                   (defn main [] -> i64 (f 7))";
        let m = module(src);
        let mut checks = Checks::new(&m, Mode::Runtime, None);
        checks.ensures[m.index["f"]] = vec![false, true];
        assert_eq!(agree(src, &m, &checks).unwrap(), "9");
        let (_, counted) = run_ir(&m, &checks);
        assert!(counted.contains("contract-checks 2") && counted.contains("(\"f\", \"ensures\", 1): 1"), "{}", counted);
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

/// `(cons x (f ...))` in tail position of `f` runs as a loop (D29). Values,
/// errors, traces and counters must stay as if every call had nested.
#[test]
fn cons_tail_recursion_agrees() {
    on_big_stack(|| {
        let up = |spec: &str, base: &str, head: &str| {
            format!("(defn up [n : i64] -> (Vec i64) {} (if (= n 0) {} (cons {} (up (- n 1))))) (defn main [] -> (Vec i64) (up 5))", spec, base, head)
        };
        // Six calls of `up` were open, then `main`.
        let up5 = ["up", "up", "up", "up", "up", "up", "main"];
        assert_eq!(same(&up("", "[]", "n")).unwrap(), "[5 4 3 2 1]");
        assert_eq!(same(&up("", "[0]", "(* n 10)")).unwrap(), "[50 40 30 20 10 0]");
        assert_eq!(same(&up("(:ensures (= (len result) n))", "[]", "n")).unwrap(), "[5 4 3 2 1]");
        assert_eq!(same(&up("(:ensures (> (len result) n))", "[]", "n")), error("contract", "ensures failed in up: (> (len result) n)", &up5));
        assert_eq!(same(&up("", "(/ 1 0)", "n")), error("div-zero", "(/ 1 0)", &up5));
        assert_eq!(same(&up("(:requires (not (= n 2)))", "[]", "n")), error("contract", "requires failed in up: (not (= n 2))", &["up", "up", "up", "up", "main"]));
        assert_eq!(same(&up("", "[]", "(/ 10 (- n 2))")), error("div-zero", "(/ 10 0)", &["up", "up", "up", "up", "main"]));
        // The innermost cons runs in the caller of the call that returned 7.
        assert_eq!(same(&up("", "7", "n")), error("type", "(cons ...) expects vec, got i64", &["up", "up", "up", "up", "up", "main"]));
        assert_eq!(same(&up("(:effects [])", "[]", "(do (print n) n)")), error("effect", "`print` performs effect io, but `up` declares (:effects [])", &["up", "main"]));
        for src in [
            "(defn up [n : i64] -> (Vec i64) (let [m (- n 1)] (do (+ n 1) (if (< m 0) [] (cons n (up m)))))) (defn main [] -> (Vec i64) (up 4))",
            "(defn zip [a : (Vec i64) b : (Vec i64)] -> (Vec i64) (if (empty? a) b (if (empty? b) a (if (< (get a 0) (get b 0)) (cons (get a 0) (zip (rest a) b)) (cons (get b 0) (zip a (rest b))))))) (defn main [] -> (Vec i64) (zip [1 4 6] [2 3 5 7]))",
            "(defn up [n : i64] -> (Vec i64) (if (= n 0) [] (cons (len (up (- n 1))) (up (- n 1))))) (defn main [] -> (Vec i64) (up 4))",
            "(defn up [n : i64] -> (Vec i64) (if (= n 0) [] (cons n (up)))) (defn main [] -> (Vec i64) (up 3))",
            "(defn up [n : i64] -> (Vec i64) (if (= n 0) [] (cons n (up (- n 1))))) (defn main [] -> i64 (len (map (fn [k] (len (up k))) (up 30))))",
        ] {
            let _ = same(src);
        }
    });
}

/// A cons-tail recursion deeper than the depth limit runs in constant depth
/// when no ensures is checked, and still stops at the limit when one is.
#[test]
fn cons_tail_recursion_needs_no_depth() {
    on_big_stack(|| {
        let src = "(defn up [n : i64] -> (Vec i64) (:ensures (= (len result) n)) (if (= n 0) [] (cons n (up (- n 1))))) (defn main [] -> i64 (len (up 300000)))";
        let m = module(src);
        let run = |mode| {
            let prog = warrant::ir::Program::new(&m, &Checks::new(&m, mode, None));
            let mut it = warrant::rt::Interp::new(&prog, false);
            let r = it.call_main().map(|v| prog.show(&v)).map_err(|e| e.kind.to_string());
            (r, it.prof.max_depth)
        };
        assert_eq!(run(Mode::Off), (Ok("300000".into()), 2));
        assert_eq!(run(Mode::Runtime).0, Err("stack".into()));
    });
}

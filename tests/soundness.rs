//! Differential soundness: when every obligation of a function is proved, no
//! input that meets its `requires` may make it fail at run time with all
//! contracts checked. Programs and inputs come from a fixed-seed generator.

use warrant::ast::lower;
use warrant::contracts::{Checks, Mode};
use warrant::eval::{Interp, Program};
use warrant::sexp::parse_all_spanned;
use warrant::solver::Z3;
use warrant::verify::{self, Status};

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
    /// Uniform in the open interval (-bound, bound).
    fn int(&mut self, bound: i64) -> i64 {
        self.within((1 - bound, bound - 1))
    }
    /// Uniform in the inclusive range, biased towards both ends.
    fn within(&mut self, (lo, hi): (i64, i64)) -> i64 {
        let span = hi as i128 - lo as i128 + 1;
        let off = match self.below(4) {
            0 => self.below(3) as i128,
            1 => span - 1 - self.below(3) as i128,
            _ => self.next() as i128 % span,
        };
        (lo as i128 + off.clamp(0, span - 1)) as i64
    }
}

const LITS: &[i64] = &[0, 1, -1, 2, -2, 3, 7, -7, 3037000500, i64::MAX, i64::MIN];

/// Mostly small literals: extremes make nearly every program overflow.
fn lit(r: &mut Rng) -> i64 {
    let n = if r.below(8) == 0 { LITS.len() } else { 8 };
    LITS[r.below(n as u64) as usize]
}

fn int_expr(r: &mut Rng, depth: u32) -> String {
    if depth == 0 || r.below(3) == 0 {
        return match r.below(3) {
            0 => "x".into(),
            1 => "y".into(),
            _ => lit(r).to_string(),
        };
    }
    let (a, b) = (int_expr(r, depth - 1), int_expr(r, depth - 1));
    match r.below(7) {
        0 => format!("(+ {} {})", a, b),
        1 => format!("(- {} {})", a, b),
        2 => format!("(* {} {})", a, b),
        3 => format!("(/ {} {})", a, b),
        4 => format!("(mod {} {})", a, b),
        5 => format!("(- {})", a),
        _ => format!("(if (< {} {}) {} {})", a, b, int_expr(r, depth - 1), int_expr(r, depth - 1)),
    }
}

fn ensures(r: &mut Rng) -> String {
    let rhs = if r.below(2) == 0 { (r.int(6)).to_string() } else { int_expr(r, 1) };
    let op = ["<", "<=", "=", ">=", ">"][r.below(5) as usize];
    format!("({} result {})", op, rhs)
}

/// Inclusive ranges the inputs are drawn from: signs, sizes and the i64 edges.
const RANGES: &[(i64, i64)] = &[
    (-3, 3),
    (-10, -1),
    (1, 10),
    (-100, 100),
    (0, 1000),
    (-3037000499, 3037000499),
    (i64::MIN, i64::MAX),
];

struct Case {
    src: String,
    x: (i64, i64),
    y: (i64, i64),
}

fn case(r: &mut Rng) -> Case {
    let x = RANGES[r.below(RANGES.len() as u64) as usize];
    let y = RANGES[r.below(RANGES.len() as u64) as usize];
    let src = format!(
        "(defn f [x : i64 y : i64] -> i64\n  (:requires (<= {} x) (<= x {}) (<= {} y) (<= y {}))\n  (:ensures {})\n  {})\n",
        x.0,
        x.1,
        y.0,
        y.1,
        ensures(r),
        int_expr(r, 2)
    );
    Case { src, x, y }
}

/// Runs `(f x y)` with every contract checked; `Err` is the error kind.
fn run(src: &str, x: i64, y: i64) -> Result<(), String> {
    let full = format!("{}(defn main [] -> i64 (f {} {}))\n", src, x, y);
    let (forms, spans) = parse_all_spanned(&full).unwrap();
    let m = lower(&forms, &spans).unwrap();
    let prog = Program::new(&m, &Checks::new(&m, Mode::Runtime, None));
    Interp::new(&prog, false).call_main().map(|_| ()).map_err(|e| e.kind.to_string())
}

#[test]
fn proved_functions_never_fail_at_run_time() {
    let Some(z3) = Z3::find(2000) else {
        eprintln!("z3 not found; skipping");
        return;
    };
    let mut r = Rng(0x005e_ed0f_5afe_c0de);
    let jobs = std::thread::available_parallelism().map_or(1, |n| n.get());
    let (mut proved, mut refuted) = (0, 0);
    for _ in 0..1500 {
        let c = case(&mut r);
        let (forms, spans) = parse_all_spanned(&c.src).unwrap();
        let m = lower(&forms, &spans).unwrap();
        let Ok(ty) = warrant::types::check(&m) else { panic!("generated an ill-typed program:\n{}", c.src) };
        let results = verify::discharge(warrant::vc::generate(&m, &ty), &z3, None, jobs);
        let all_proved = results.iter().all(|v| v.status == Status::Proved);
        if !all_proved {
            if results.iter().any(|v| matches!(v.status, Status::Failed { .. })) {
                refuted += 1;
            }
            continue;
        }
        proved += 1;
        let mut inputs: Vec<(i64, i64)> = [c.x.0, c.x.1].iter().flat_map(|&x| [(x, c.y.0), (x, c.y.1)]).collect();
        inputs.extend((0..40).map(|_| (r.within(c.x), r.within(c.y))));
        for (x, y) in inputs {
            if let Err(kind) = run(&c.src, x, y) {
                panic!("proved, yet (f {} {}) failed with {}:\n{}", x, y, kind, c.src);
            }
        }
    }
    eprintln!("proved {} refuted {}", proved, refuted);
    // The generator must exercise both sides, or the test proves nothing.
    assert!(proved >= 100 && refuted >= 100, "proved {} refuted {}", proved, refuted);
}

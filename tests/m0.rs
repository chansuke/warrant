use warrant::ast::lower;
use warrant::contracts::{Checks, Mode};
use warrant::eval::{show, Interp, Program};
use warrant::sexp::{parse_all, parse_all_spanned, pretty_all};
use warrant::wisp;

const EXAMPLES: &[(&str, &str)] = &[
    ("msort", include_str!("../examples/msort.wrt")),
    ("sum_sq", include_str!("../examples/sum_sq.wrt")),
    ("effect_leak", include_str!("../examples/effect_leak.wrt")),
    ("sum_sq_ok", include_str!("../examples/sum_sq_ok.wrt")),
];

#[test]
fn every_example_roundtrips_through_both_printers() {
    for (name, src) in EXAMPLES {
        let forms = parse_all(src).unwrap();
        let view = wisp::print_all(&forms);
        assert_eq!(wisp::parse(&view).unwrap(), forms, "{} wisp view:\n{}", name, view);
        let canon = pretty_all(&forms);
        assert_eq!(parse_all(&canon).unwrap(), forms, "{} pretty:\n{}", name, canon);
    }
}

fn run(src: &str) -> Result<String, (String, String)> {
    let src = src.to_string();
    // The tree-walker recurses deeply; mirror the CLI's large stack.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let (forms, spans) = parse_all_spanned(&src).unwrap();
            let m = lower(&forms, &spans).unwrap();
            let prog = Program::new(&m, &Checks::new(&m, Mode::Runtime, None));
            let mut it = Interp::new(&prog, true);
            it.call_main().map(|v| show(&v)).map_err(|e| (e.kind.to_string(), e.msg))
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn msort_sorts_and_satisfies_its_contracts() {
    let got = run(EXAMPLES[0].1).unwrap();
    let mut expect: Vec<i64> = (0..2000i64).map(|i| (i * 7919 + 42).rem_euclid(10007)).collect();
    expect.sort();
    let expect = format!("[{}]", expect[..10].iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "));
    assert_eq!(got, expect);
}

#[test]
fn overflow_is_an_error_not_a_wrap() {
    assert_eq!(run(EXAMPLES[1].1).unwrap_err().0, "overflow");
}

#[test]
fn bounded_sum_sq_runs_within_its_contract() {
    assert_eq!(run(EXAMPLES[3].1).unwrap(), "16000014");
}

#[test]
fn effect_leak_is_caught_transitively() {
    let (kind, msg) = run(EXAMPLES[2].1).unwrap_err();
    assert_eq!(kind, "effect");
    assert!(msg.contains("`add`"), "{}", msg);
}

#[test]
fn broken_implementation_violates_ensures() {
    let src = "(defn bad-sort [xs : (Vec i64)] -> (Vec i64)
                 (:ensures (sorted? result) (perm? result xs))
                 (cons 99 xs))
               (defn main [] -> (Vec i64) (bad-sort [3 1 2]))";
    let (kind, msg) = run(src).unwrap_err();
    assert_eq!(kind, "contract");
    assert!(msg.contains("ensures failed in bad-sort"), "{}", msg);
}

#[test]
fn requires_is_checked_before_the_body() {
    let src = "(defn head [xs : (Vec i64)] -> i64 (:requires (not (empty? xs))) (get xs 0))
               (defn main [] -> i64 (head []))";
    assert_eq!(run(src).unwrap_err().0, "contract");
}

#[test]
fn all_checks_every_element_and_stops_at_the_first_failure() {
    let src = "(defn small? [x : i64] -> Bool (< x 10))
               (defn main [] -> (Vec Bool)
                 (vec (all? small? [1 2 3]) (all? small? [1 20 3]) (all? small? [])))";
    assert_eq!(run(src).unwrap(), "[true false true]");
    let guarded = "(defn main [] -> Bool (all? (fn [x] (< (/ 10 x) 5)) [1 0]))";
    assert_eq!(run(guarded).unwrap(), "false");
}

#[test]
fn load_errors_point_at_the_source_in_both_views() {
    let wrt = "(defn f [x : i64] -> i64\n  (+ x y))";
    let (forms, spans) = parse_all_spanned(wrt).unwrap();
    let d = lower(&forms, &spans).unwrap_err();
    assert_eq!(d.to_sexp(), "(error :kind unbound :at (line 2 col 8) :msg \"unbound symbol `y`\")");
    let (forms, spans) = wisp::parse_spanned("defn f [x : i64] -> i64\n  + x y").unwrap();
    let d = lower(&forms, &spans).unwrap_err();
    assert_eq!(d.to_sexp(), "(error :kind unbound :at (line 2 col 7) :msg \"unbound symbol `y`\")");
}

#[test]
fn an_impossible_range_is_an_alloc_error_not_a_panic() {
    let (kind, _) = run("(defn main [] -> i64 (len (range 9223372036854775807)))").unwrap_err();
    assert_eq!(kind, "alloc");
}

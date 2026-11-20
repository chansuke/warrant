//! How many vector elements the IR runtime copies (`vec-elems` in
//! `run --report`). Building a vector one element at a time must copy O(n)
//! elements in total, whichever end it grows at, so doubling n at most
//! doubles the copies plus room for amortization.

use warrant::ast::lower;
use warrant::contracts::{Checks, Mode};
use warrant::ir::Program;
use warrant::rt::Interp;
use warrant::sexp::parse_all_spanned;

/// `(len result, vec-elems)` of `main`, with contracts off as in `bench`.
fn copies(src: &str) -> (String, u64) {
    let src = src.to_string();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let (forms, spans) = parse_all_spanned(&src).unwrap();
            let m = lower(&forms, &spans).unwrap();
            let prog = Program::new(&m, &Checks::new(&m, Mode::Off, None));
            let mut it = Interp::new(&prog, false);
            let v = it.call_main().unwrap_or_else(|e| panic!("{}\n{}", e.to_sexp(), src));
            (prog.show(&v), it.prof.vec_elems)
        })
        .unwrap()
        .join()
        .unwrap()
}

fn grows_linearly(name: &str, step: &str) {
    let src = |n: u64| {
        format!(
            "(defn grow [n : i64 acc : (Vec i64)] -> (Vec i64) (if (= n 0) acc (grow (- n 1) {})))
             (defn main [] -> i64 (len (grow {} [0])))",
            step, n
        )
    };
    let (len_a, a) = copies(&src(2000));
    let (len_b, b) = copies(&src(4000));
    assert_eq!((len_a.as_str(), len_b.as_str()), ("2001", "4001"), "{}", name);
    assert!(b as f64 <= 2.5 * a as f64 && b <= 10 * 4000, "{}: {} copies at n=2000, {} at n=4000", name, a, b);
}

#[test]
fn appending_to_an_argument_copies_linearly() {
    grows_linearly("append", "(concat acc [n])");
}

#[test]
fn prepending_to_an_argument_copies_linearly() {
    grows_linearly("prepend", "(concat [n] acc)");
    grows_linearly("cons", "(cons n acc)");
}

#[test]
fn a_fold_accumulator_is_not_shared_with_its_initial_value() {
    grows_linearly("fold", "(fold (fn [v x] (cons x v)) acc [n])");
}

#[test]
fn a_small_slice_does_not_keep_its_buffer() {
    // The 10 elements are copied out of the 1000-element buffer.
    assert_eq!(copies("(defn main [] -> (Vec i64) (slice (range 1000) 0 10))").1, 1000 + 10);
    // Half the buffer stays a view.
    assert_eq!(copies("(defn main [] -> i64 (len (slice (range 1000) 0 500)))").1, 1000);
}

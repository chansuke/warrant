//! The SMT-LIB vocabulary Warrant values are encoded in (D13). Integers are
//! mathematical `Int` with explicit range obligations. A vector is a datatype
//! of an array and a length, one per element sort.

use crate::types::Ty;

/// Datatype suffix for `(Vec elem)`: `VI` for i64, `VB` for Bool, `VS` for Str.
/// Nested vectors and vectors of functions are not encoded in M1.
pub fn vec_sort(elem: &Ty) -> Option<&'static str> {
    match elem {
        Ty::I64 => Some("VI"),
        Ty::Bool => Some("VB"),
        Ty::Str => Some("VS"),
        _ => None,
    }
}

/// The SMT sort of a Warrant type, when it has one.
pub fn sort(t: &Ty) -> Option<&'static str> {
    match t {
        Ty::I64 => Some("Int"),
        Ty::Bool => Some("Bool"),
        Ty::Str => Some("String"),
        Ty::Vec(e) => vec_sort(e),
        _ => None,
    }
}

pub const I64_MIN: &str = "(- 9223372036854775808)";

/// An upper bound on any vector's length: the interpreter cannot allocate
/// more than `isize::MAX` bytes of `Value`s (D21). Two lengths added together
/// still fit in i64.
pub const MAX_LEN: i64 = 1 << 59;

/// SMT-LIB has no negative literals: `-5` is `(- 5)`.
pub fn int_lit(n: i64) -> String {
    if n < 0 {
        format!("(- {})", n.unsigned_abs())
    } else {
        n.to_string()
    }
}

pub fn quote_sym(name: &str) -> String {
    format!("|{}|", name.replace('|', "_"))
}

pub fn str_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\"\""),
            ' '..='~' => out.push(c),
            c => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
        }
    }
    out.push('"');
    out
}

pub const PRELUDE: &str = r#"(declare-datatype VI ((mk-VI (arr-VI (Array Int Int)) (len-VI Int))))
(declare-datatype VB ((mk-VB (arr-VB (Array Int Bool)) (len-VB Int))))
(declare-datatype VS ((mk-VS (arr-VS (Array Int String)) (len-VS Int))))
(define-fun in64 ((x Int)) Bool (and (<= (- 9223372036854775808) x) (<= x 9223372036854775807)))
(define-fun tdiv ((a Int) (b Int)) Int
  (ite (>= a 0) (ite (> b 0) (div a b) (- (div a (- b))))
                (ite (> b 0) (- (div (- a) b)) (div (- a) (- b)))))
(define-fun sorted-VI ((v VI)) Bool
  (forall ((i Int) (j Int))
    (! (=> (and (<= 0 i) (<= i j) (< j (len-VI v))) (<= (select (arr-VI v) i) (select (arr-VI v) j)))
       :pattern ((select (arr-VI v) i) (select (arr-VI v) j)))))
(define-fun eq-VI ((a VI) (b VI)) Bool
  (and (= (len-VI a) (len-VI b))
       (forall ((i Int)) (=> (and (<= 0 i) (< i (len-VI a))) (= (select (arr-VI a) i) (select (arr-VI b) i))))))
(define-fun eq-VB ((a VB) (b VB)) Bool
  (and (= (len-VB a) (len-VB b))
       (forall ((i Int)) (=> (and (<= 0 i) (< i (len-VB a))) (= (select (arr-VB a) i) (select (arr-VB b) i))))))
(define-fun eq-VS ((a VS) (b VS)) Bool
  (and (= (len-VS a) (len-VS b))
       (forall ((i Int)) (=> (and (<= 0 i) (< i (len-VS a))) (= (select (arr-VS a) i) (select (arr-VS b) i))))))
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncating_division_matches_rust() {
        let Some(mut z) = crate::solver::Z3::find(2000) else { return };
        use crate::solver::{Outcome, Solver};
        for (a, b) in [(7i64, 2i64), (-7, 2), (7, -2), (-7, -2), (6, 3), (-1, 5)] {
            let script = format!("{}(assert (not (= (tdiv {} {}) {})))", PRELUDE, int_lit(a), int_lit(b), int_lit(a / b));
            assert_eq!(z.check(&script, &[]), Outcome::Proved, "{} / {}", a, b);
        }
    }
}

//! Randomized properties over generated programs. A fixed-seed xorshift keeps
//! every run reproducible; a failure prints the input that broke it.

use warrant::ast::lower;
use warrant::sexp::{flat, parse_all, parse_all_spanned, pretty_all, Sexp};
use warrant::wisp;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

const SYMS: &[&str] = &["f", "x", "+", "-", "->", ":", ".", "a|b", "a\\b", "empty?", "%r", "defn", "if", "let", "fn", "é"];
const KWS: &[&str] = &["requires", "ensures", "effects", "budget", "k"];
const STRS: &[&str] = &["", "a b", "q\"q", "back\\slash", "line\nbreak", "tab\t", "ü", "\\u{41}"];
const INTS: &[i64] = &[0, 1, -1, 42, i64::MIN, i64::MAX];

fn gen(r: &mut Rng, depth: usize) -> Sexp {
    match r.below(if depth == 0 { 5 } else { 8 }) {
        0 => Sexp::Int(*r.pick(INTS)),
        1 => Sexp::Bool(r.below(2) == 0),
        2 => Sexp::Str(r.pick(STRS).to_string()),
        3 => Sexp::Sym(r.pick(SYMS).to_string()),
        4 => Sexp::Kw(r.pick(KWS).to_string()),
        5 => Sexp::Vector((0..r.below(4)).map(|_| gen(r, depth - 1)).collect()),
        6 => {
            let mut v = vec![Sexp::Kw(r.pick(KWS).to_string())];
            v.extend((0..r.below(3)).map(|_| gen(r, depth - 1)));
            Sexp::List(v)
        }
        _ => Sexp::List((0..r.below(5)).map(|_| gen(r, depth - 1)).collect()),
    }
}

#[test]
fn any_canonical_form_roundtrips_through_wisp_and_pretty() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let mut checked = 0;
    for _ in 0..5000 {
        let n = 1 + r.below(3);
        // Canonical forms are what the parser produces, so go through text.
        let text: Vec<String> = (0..n).map(|_| flat(&gen(&mut r, 4))).collect();
        let Ok(forms) = parse_all(&text.join("\n")) else { continue };
        let view = wisp::print_all(&forms);
        assert_eq!(wisp::parse(&view).ok().as_ref(), Some(&forms), "wisp view:\n{}", view);
        let canon = pretty_all(&forms);
        assert_eq!(parse_all(&canon).ok().as_ref(), Some(&forms), "pretty:\n{}", canon);
        checked += 1;
    }
    assert!(checked > 4000, "only {} generated forms parsed", checked);
}

const SOUP: &[&str] = &[
    "(",
    ")",
    "[",
    "]",
    "\"",
    "\"s\"",
    " ",
    "\n",
    "  ",
    ";c\n",
    ":",
    ".",
    "0",
    "-9223372036854775808",
    "99999999999999999999",
    "defn",
    "f",
    "main",
    "x",
    ":",
    "i64",
    "Bool",
    "Str",
    "(Vec i64)",
    "(Fn [i64] i64)",
    "->",
    ":requires",
    ":ensures",
    ":effects",
    ":budget",
    "[io]",
    "(wall-ms 5)",
    "result",
    "if",
    "let",
    "fn",
    "do",
    "and",
    "or",
    "+",
    "/",
    "len",
    "get",
    "map",
    "fold",
    "all?",
    "perm?",
    "sorted?",
    "print",
    "true",
];

fn soup(r: &mut Rng) -> String {
    (0..r.below(60)).map(|_| *r.pick(SOUP)).collect::<Vec<_>>().join(" ")
}

/// Every front-end pass returns an error value on bad input; none may panic.
fn front_end(src: &str, as_wisp: bool) {
    let parsed = if as_wisp { wisp::parse_spanned(src) } else { parse_all_spanned(src) };
    let Ok((forms, spans)) = parsed else { return };
    let Ok(m) = lower(&forms, &spans) else { return };
    let _ = warrant::effects::check(&m);
    if let Ok(ty) = warrant::types::check(&m) {
        let _ = warrant::vc::generate(&m, &ty);
    }
}

#[test]
fn the_front_end_never_panics_on_token_soup() {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    for i in 0..20000 {
        let src = soup(&mut r);
        let as_wisp = i % 2 == 1;
        if std::panic::catch_unwind(|| front_end(&src, as_wisp)).is_err() {
            panic!("front end panicked (wisp: {}) on:\n{}", as_wisp, src);
        }
    }
}

#[test]
fn the_front_end_never_panics_on_well_formed_defns() {
    let mut r = Rng(0xdead_beef_cafe_f00d);
    for _ in 0..20000 {
        let src = format!("(defn {} [{}] -> {} {})", r.pick(&["f", "main"]), soup(&mut r), r.pick(SOUP), soup(&mut r));
        if std::panic::catch_unwind(|| front_end(&src, false)).is_err() {
            panic!("front end panicked on:\n{}", src);
        }
    }
}

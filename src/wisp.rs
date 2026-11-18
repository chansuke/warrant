//! Human view: an indentation-based rendering of the canonical S-expressions,
//! in the spirit of Wisp (SRFI-119). The mapping is lossless in both directions.
//!
//! Rules (one logical line = one list unless noted):
//! - `head a b` on a line, with indented child lines, is `(head a b child1 child2 ...)`.
//! - A line holding exactly one item and no children is that item itself
//!   (so `xs` is the symbol, `(f)` is the one-element list).
//! - A bare `:` opens a nested list running to the end of the line:
//!   `fold + 0 : map f xs` is `(fold + 0 (map f xs))`.
//! - A line starting with `. ` splices its items into the parent without wrapping.
//! - Inside brackets `( )` and `[ ]` the text is plain S-expression syntax.
//! - Brackets must close on the line they open. Indent with spaces only.

use crate::sexp::{flat, is_clause, ParseError, Parser, Sexp, SpanTree, WIDTH};

// ---------- printing ----------

pub fn print_all(forms: &[Sexp]) -> String {
    forms
        .iter()
        .map(|f| {
            let mut s = String::new();
            line(f, 0, &mut s);
            s
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn is_marker(x: &Sexp) -> bool {
    matches!(x, Sexp::Sym(s) if s == ":" || s == ".")
}

/// Lists that cannot be rendered as a Wisp line and must stay bracketed.
fn needs_brackets(v: &[Sexp]) -> bool {
    v.len() < 2 || v.iter().any(is_marker)
}

fn line(e: &Sexp, indent: usize, out: &mut String) {
    let pad = " ".repeat(indent);
    let items = match e {
        Sexp::List(v) if !needs_brackets(v) => v,
        _ => {
            out.push_str(&pad);
            out.push_str(&flat(e));
            out.push('\n');
            return;
        }
    };
    if !items.iter().any(is_clause) {
        let s = inline_line(items);
        if indent + s.len() <= WIDTH {
            out.push_str(&pad);
            out.push_str(&s);
            out.push('\n');
            return;
        }
    }
    let mut s = flat(&items[0]);
    let mut i = 1;
    while i < items.len() {
        let it = &items[i];
        let fi = flat(it);
        let small = match it {
            Sexp::List(_) => fi.len() <= 24 && i + 1 < items.len(),
            _ => true,
        };
        if is_clause(it) || !small || indent + s.len() + 1 + fi.len() > WIDTH {
            break;
        }
        s.push(' ');
        s.push_str(&fi);
        i += 1;
    }
    out.push_str(&pad);
    out.push_str(&s);
    out.push('\n');
    for it in &items[i..] {
        line(it, indent + 2, out);
    }
}

/// Render a list as the content of one line (without outer brackets).
/// Uses `:` for a trailing list argument when every earlier item is non-list.
fn inline_line(items: &[Sexp]) -> String {
    let (last, init) = items.split_last().expect("len >= 2");
    let mut parts: Vec<String> = init.iter().map(flat).collect();
    // Clause lines (`:budget (wall-ms 50)`) read better with brackets than with `:`.
    let init_simple = !matches!(init.first(), Some(Sexp::Kw(_)))
        && init.iter().all(|x| !matches!(x, Sexp::List(_)));
    match last {
        Sexp::List(v) if init_simple && !needs_brackets(v) && !is_clause(last) => {
            parts.push(":".into());
            parts.push(inline_line(v));
        }
        _ => parts.push(flat(last)),
    }
    parts.join(" ")
}

// ---------- parsing ----------

type Item = (Sexp, SpanTree);

struct Line {
    indent: usize,
    items: Vec<Item>,
    splice: bool,
    no: usize,
}

pub fn parse(src: &str) -> Result<Vec<Sexp>, ParseError> {
    parse_spanned(src).map(|(forms, _)| forms)
}

/// A list built from a Wisp line or a `:` starts where its first item starts.
fn list_of(items: Vec<Item>) -> Item {
    let at = items[0].1.at;
    let (v, kids) = items.into_iter().unzip();
    (Sexp::List(v), SpanTree { at, kids })
}

pub fn parse_spanned(src: &str) -> Result<(Vec<Sexp>, Vec<SpanTree>), ParseError> {
    let mut lines = Vec::new();
    for (i, raw) in src.lines().enumerate() {
        let no = i + 1;
        let indent = raw.chars().take_while(|c| *c == ' ').count();
        let rest = &raw[indent..];
        if rest.starts_with('\t') {
            return Err(ParseError::new(no, indent + 1, "indent with spaces, not tabs"));
        }
        let mut p = Parser::new_at(rest, no, indent + 1);
        let mut items = Vec::new();
        while let Some(e) = p.parse_expr()? {
            items.push(e);
        }
        if items.is_empty() {
            continue; // blank or comment-only line
        }
        let splice = items[0].0 == Sexp::Sym(".".into());
        if splice {
            items.remove(0);
            if items.is_empty() {
                return Err(ParseError::new(no, indent + 1, "`.` must be followed by items"));
            }
        }
        let items = fold_colon(items).map_err(|m| ParseError::new(no, indent + 1, m))?;
        lines.push(Line { indent, items, splice, no });
    }
    let mut out = Vec::new();
    if lines.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    if lines[0].indent != 0 {
        return Err(ParseError::new(lines[0].no, 1, "first form must not be indented"));
    }
    let mut i = 0;
    block(&lines, &mut i, &mut out)?;
    if i < lines.len() {
        return Err(ParseError::new(lines[i].no, 1, "inconsistent indentation"));
    }
    Ok(out.into_iter().unzip())
}

fn fold_colon(mut items: Vec<Item>) -> Result<Vec<Item>, String> {
    match items.iter().position(|x| x.0 == Sexp::Sym(":".into())) {
        None => Ok(items),
        Some(p) => {
            let tail = items.split_off(p + 1);
            items.pop();
            let tail = fold_colon(tail)?;
            if tail.is_empty() {
                return Err("`:` must be followed by an expression".into());
            }
            items.push(list_of(tail));
            Ok(items)
        }
    }
}

fn block(lines: &[Line], i: &mut usize, out: &mut Vec<Item>) -> Result<(), ParseError> {
    let base = lines[*i].indent;
    while *i < lines.len() {
        let ind = lines[*i].indent;
        if ind < base {
            return Ok(());
        }
        if ind > base {
            return Err(ParseError::new(lines[*i].no, 1, "inconsistent indentation (dedent to an unknown level)"));
        }
        let idx = *i;
        *i += 1;
        let mut children = Vec::new();
        if *i < lines.len() && lines[*i].indent > base {
            block(lines, i, &mut children)?;
        }
        let l = &lines[idx];
        if l.splice {
            if !children.is_empty() {
                return Err(ParseError::new(l.no, 1, "a `.` line cannot have children"));
            }
            out.extend(l.items.iter().cloned());
        } else if l.items.len() == 1 && children.is_empty() {
            out.push(l.items[0].clone());
        } else {
            let mut v = l.items.clone();
            v.extend(children);
            out.push(list_of(v));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_all;

    fn roundtrip(src: &str) {
        let forms = parse_all(src).unwrap();
        let w = print_all(&forms);
        let back = parse(&w).unwrap_or_else(|e| panic!("{}\n---\n{}", e.to_sexp(), w));
        assert_eq!(back, forms, "wisp view:\n{}", w);
    }

    #[test]
    fn colon_nesting() {
        let f = parse("fold + 0 : map f xs").unwrap();
        assert_eq!(flat(&f[0]), "(fold + 0 (map f xs))");
    }

    #[test]
    fn single_item_lines_and_splice() {
        let f = parse("f\n  x\n  (g)\n  . a b").unwrap();
        assert_eq!(flat(&f[0]), "(f x (g) a b)");
    }

    #[test]
    fn roundtrips_tricky_shapes() {
        roundtrip("(a) (b c) () [x : (T u)] (f (g) [] (h : i))");
        roundtrip("(defn f [x : i64] -> i64 (:effects []) (:ensures (>= result 0)) (if (< x 0) (- x) x))");
        roundtrip("(a b c d e f g h i j k l m n o p q r s t u v w x y z aa bb cc dd ee ff gg hh ii jj kk)");
    }

    #[test]
    fn spans_point_at_the_wisp_source() {
        let (f, s) = parse_spanned("defn f [x : i64] -> i64\n  :ensures (>= result 0)\n  fold + 0 : map g xs").unwrap();
        assert_eq!(flat(&f[0]), "(defn f [x : i64] -> i64 (:ensures (>= result 0)) (fold + 0 (map g xs)))");
        let at = |t: &SpanTree| (t.at.line, t.at.col);
        assert_eq!(at(&s[0]), (1, 1));
        assert_eq!(at(&s[0].kids[2].kids[2]), (1, 13));
        assert_eq!(at(&s[0].kids[5]), (2, 3));
        assert_eq!(at(&s[0].kids[5].kids[1].kids[1]), (2, 16));
        let fold = &s[0].kids[6];
        assert_eq!(at(fold), (3, 3));
        assert_eq!(at(&fold.kids[3]), (3, 14));
        assert_eq!(at(&fold.kids[3].kids[2]), (3, 20));
    }

    #[test]
    fn bad_dedent_is_an_error() {
        assert!(parse("a\n    b\n  c").is_err());
    }
}

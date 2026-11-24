//! Canonical form: S-expressions. This is what is stored on disk and what
//! agents read and write. Humans usually look at the Wisp view (see `wisp`).

use std::fmt;

/// Target line width for pretty printers.
pub const WIDTH: usize = 80;

/// Deepest bracket nesting a program may use. Every later pass recurses over
/// the tree, so deeper input would overflow the stack instead of failing.
pub const MAX_NESTING: usize = 1000;

#[derive(Clone, Debug, PartialEq)]
pub enum Sexp {
    Int(i64),
    Bool(bool),
    Str(String),
    Sym(String),
    /// `:name` — used as clause heads such as `(:ensures ...)`.
    Kw(String),
    List(Vec<Sexp>),
    Vector(Vec<Sexp>),
}

/// Where a form starts in the source (1-based).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

/// Positions for a parsed form, shaped exactly like the `Sexp` it belongs to.
/// Kept beside the tree rather than inside it so `Sexp` equality ignores layout.
#[derive(Clone, Debug, PartialEq)]
pub struct SpanTree {
    pub at: Pos,
    pub kids: Vec<SpanTree>,
}

impl SpanTree {
    pub fn leaf(line: usize, col: usize) -> Self {
        SpanTree { at: Pos { line, col }, kids: Vec::new() }
    }

    /// Spans for a form built in memory rather than parsed: every position
    /// is line 0, col 0.
    pub fn synthetic(e: &Sexp) -> Self {
        let kids = match e {
            Sexp::List(v) | Sexp::Vector(v) => v.iter().map(SpanTree::synthetic).collect(),
            _ => Vec::new(),
        };
        SpanTree { at: Pos { line: 0, col: 0 }, kids }
    }
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

impl ParseError {
    pub fn new(line: usize, col: usize, msg: impl Into<String>) -> Self {
        ParseError { line, col, msg: msg.into() }
    }
    /// Errors are S-expressions too, so agents can parse them.
    pub fn to_sexp(&self) -> String {
        format!("(error :kind parse :at (line {} col {}) :msg {})", self.line, self.col, quote_str(&self.msg))
    }
}

pub fn quote_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    LParen,
    RParen,
    LBrack,
    RBrack,
    Atom(String),
    Str(String),
}

pub struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    pub line: usize,
    pub col: usize,
}

impl<'a> Lexer<'a> {
    pub fn new_at(src: &'a str, line: usize, col: usize) -> Self {
        Lexer { chars: src.chars().peekable(), line, col }
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    /// Returns the next token with the line/col where it starts.
    pub fn next_tok(&mut self) -> Result<Option<(Tok, usize, usize)>, ParseError> {
        loop {
            match self.chars.peek() {
                None => return Ok(None),
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some(';') => {
                    while let Some(&c) = self.chars.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                _ => break,
            }
        }
        let (l, c) = (self.line, self.col);
        let ch = self.bump().expect("the loop above returns at the end of input");
        let tok = match ch {
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBrack,
            ']' => Tok::RBrack,
            '"' => {
                let mut s = String::new();
                loop {
                    match self.bump() {
                        None => return Err(ParseError::new(l, c, "unterminated string")),
                        Some('"') => break,
                        Some('\\') => match self.bump() {
                            Some('n') => s.push('\n'),
                            Some('t') => s.push('\t'),
                            Some('"') => s.push('"'),
                            Some('\\') => s.push('\\'),
                            _ => return Err(ParseError::new(self.line, self.col, "bad escape in string")),
                        },
                        Some(x) => s.push(x),
                    }
                }
                Tok::Str(s)
            }
            first => {
                let mut s = String::new();
                s.push(first);
                while let Some(&n) = self.chars.peek() {
                    if n.is_whitespace() || "()[]\";".contains(n) {
                        break;
                    }
                    s.push(n);
                    self.bump();
                }
                Tok::Atom(s)
            }
        };
        Ok(Some((tok, l, c)))
    }
}

pub fn atom(s: &str, line: usize, col: usize) -> Result<Sexp, ParseError> {
    match s {
        "true" => return Ok(Sexp::Bool(true)),
        "false" => return Ok(Sexp::Bool(false)),
        _ => {}
    }
    let digit_start = |t: &str| t.starts_with(|c: char| c.is_ascii_digit());
    let numeric = digit_start(s) || (s.len() > 1 && s.starts_with('-') && digit_start(&s[1..]));
    if numeric {
        return s
            .parse::<i64>()
            .map(Sexp::Int)
            .map_err(|_| ParseError::new(line, col, format!("invalid integer literal `{}` (must fit i64)", s)));
    }
    if s.len() > 1 && s.starts_with(':') {
        return Ok(Sexp::Kw(s[1..].to_string()));
    }
    Ok(Sexp::Sym(s.to_string()))
}

pub struct Parser<'a> {
    lex: Lexer<'a>,
    peeked: Option<(Tok, usize, usize)>,
    depth: usize,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Self {
        Self::new_at(src, 1, 1)
    }
    pub fn new_at(src: &'a str, line: usize, col: usize) -> Self {
        Parser { lex: Lexer::new_at(src, line, col), peeked: None, depth: 0 }
    }

    fn peek(&mut self) -> Result<Option<(Tok, usize, usize)>, ParseError> {
        if self.peeked.is_none() {
            self.peeked = self.lex.next_tok()?;
        }
        Ok(self.peeked.clone())
    }

    fn next(&mut self) -> Result<Option<(Tok, usize, usize)>, ParseError> {
        if let Some(t) = self.peeked.take() {
            return Ok(Some(t));
        }
        self.lex.next_tok()
    }

    pub fn parse_expr(&mut self) -> Result<Option<(Sexp, SpanTree)>, ParseError> {
        let Some((tok, l, c)) = self.next()? else { return Ok(None) };
        let mut span = SpanTree::leaf(l, c);
        if matches!(tok, Tok::LParen | Tok::LBrack) {
            if self.depth == MAX_NESTING {
                return Err(nesting_error(l, c));
            }
            self.depth += 1;
        }
        let e = match tok {
            Tok::LParen => Sexp::List(self.parse_seq(Tok::RParen, &mut span)?),
            Tok::LBrack => Sexp::Vector(self.parse_seq(Tok::RBrack, &mut span)?),
            Tok::RParen | Tok::RBrack => return Err(ParseError::new(l, c, "unexpected closing bracket")),
            Tok::Str(s) => Sexp::Str(s),
            Tok::Atom(a) => atom(&a, l, c)?,
        };
        if matches!(e, Sexp::List(_) | Sexp::Vector(_)) {
            self.depth -= 1;
        }
        Ok(Some((e, span)))
    }

    fn parse_seq(&mut self, close: Tok, span: &mut SpanTree) -> Result<Vec<Sexp>, ParseError> {
        let mut v = Vec::new();
        loop {
            match self.peek()? {
                None => return Err(ParseError::new(span.at.line, span.at.col, "bracket opened here is never closed")),
                Some((t, tl, tc)) if t == Tok::RParen || t == Tok::RBrack => {
                    self.next()?;
                    if t == close {
                        return Ok(v);
                    }
                    return Err(ParseError::new(tl, tc, "mismatched closing bracket"));
                }
                _ => {
                    let (e, s) = self.parse_expr()?.expect("peeked a token");
                    v.push(e);
                    span.kids.push(s);
                }
            }
        }
    }
}

pub fn nesting_error(line: usize, col: usize) -> ParseError {
    ParseError::new(line, col, format!("nesting deeper than {} levels", MAX_NESTING))
}

/// Bracket depth of `e`, without recursion.
pub fn nesting(e: &Sexp) -> usize {
    let mut deepest = 0;
    let mut stack = vec![(e, 0)];
    while let Some((e, d)) = stack.pop() {
        if let Sexp::List(v) | Sexp::Vector(v) = e {
            deepest = deepest.max(d + 1);
            stack.extend(v.iter().map(|x| (x, d + 1)));
        }
    }
    deepest
}

pub fn parse_all(src: &str) -> Result<Vec<Sexp>, ParseError> {
    parse_all_spanned(src).map(|(forms, _)| forms)
}

pub fn parse_all_spanned(src: &str) -> Result<(Vec<Sexp>, Vec<SpanTree>), ParseError> {
    let mut p = Parser::new(src);
    let (mut forms, mut spans) = (Vec::new(), Vec::new());
    while let Some((e, s)) = p.parse_expr()? {
        forms.push(e);
        spans.push(s);
    }
    Ok((forms, spans))
}

// ---------- printing ----------

pub fn flat(e: &Sexp) -> String {
    let mut s = String::new();
    write_flat(e, &mut s);
    s
}

fn write_flat(e: &Sexp, out: &mut String) {
    let seq = |open: char, close: char, v: &[Sexp], out: &mut String| {
        out.push(open);
        for (i, x) in v.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            write_flat(x, out);
        }
        out.push(close);
    };
    match e {
        Sexp::Int(n) => out.push_str(&n.to_string()),
        Sexp::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Sexp::Str(s) => out.push_str(&quote_str(s)),
        Sexp::Sym(s) => out.push_str(s),
        Sexp::Kw(k) => {
            out.push(':');
            out.push_str(k);
        }
        Sexp::List(v) => seq('(', ')', v, out),
        Sexp::Vector(v) => seq('[', ']', v, out),
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&flat(self))
    }
}

/// `(:effects ...)`, `(:ensures ...)` etc.
pub fn is_clause(e: &Sexp) -> bool {
    matches!(e, Sexp::List(v) if matches!(v.first(), Some(Sexp::Kw(_))))
}

pub fn pretty_all(forms: &[Sexp]) -> String {
    let mut s = forms.iter().map(pretty).collect::<Vec<_>>().join("\n\n");
    s.push('\n');
    s
}

pub fn pretty(e: &Sexp) -> String {
    let mut s = String::new();
    pp(e, 0, &mut s);
    s
}

fn pp(e: &Sexp, indent: usize, out: &mut String) {
    let f = flat(e);
    let (open, close, items) = match e {
        Sexp::List(v) => ('(', ')', v),
        Sexp::Vector(v) => ('[', ']', v),
        _ => {
            out.push_str(&f);
            return;
        }
    };
    let has_clause = items.iter().any(is_clause);
    if items.is_empty() || (indent + f.len() <= WIDTH && !has_clause) {
        out.push_str(&f);
        return;
    }
    out.push(open);
    let mut col = indent + 1;
    pp(&items[0], col, out);
    col += flat(&items[0]).len();
    let mut i = 1;
    while i < items.len() {
        let it = &items[i];
        let fi = flat(it);
        let small = match it {
            Sexp::List(_) => fi.len() <= 24 && i + 1 < items.len(),
            _ => true,
        };
        if is_clause(it) || !small || col + 1 + fi.len() > WIDTH {
            break;
        }
        out.push(' ');
        out.push_str(&fi);
        col += 1 + fi.len();
        i += 1;
    }
    let child = if open == '(' { indent + 2 } else { indent + 1 };
    for it in &items[i..] {
        out.push('\n');
        out.push_str(&" ".repeat(child));
        pp(it, child, out);
    }
    out.push(close);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nesting_past_the_limit_is_a_parse_error_at_the_bracket() {
        let deep = |n: usize| "(".repeat(n) + &")".repeat(n);
        assert_eq!(nesting(&parse_all(&deep(MAX_NESTING)).unwrap()[0]), MAX_NESTING);
        let e = parse_all(&deep(MAX_NESTING + 1)).unwrap_err();
        assert_eq!((e.line, e.col), (1, MAX_NESTING + 1));
        assert!(parse_all(&"[".repeat(MAX_NESTING + 1)).is_err());
    }

    #[test]
    fn parses_atoms_and_nesting() {
        let f = parse_all("(a 1 -2 :kw \"s\" [x y] true)").unwrap();
        assert_eq!(flat(&f[0]), "(a 1 -2 :kw \"s\" [x y] true)");
    }

    #[test]
    fn reports_position_of_unclosed_bracket() {
        let e = parse_all("(a\n  (b c)").unwrap_err();
        assert_eq!((e.line, e.col), (1, 1));
    }

    #[test]
    fn spans_mirror_the_tree_with_start_positions() {
        let (f, s) = parse_all_spanned("(a\n  (b c)\n  [d])").unwrap();
        assert_eq!(flat(&f[0]), "(a (b c) [d])");
        let at = |t: &SpanTree| (t.at.line, t.at.col);
        assert_eq!(at(&s[0]), (1, 1));
        assert_eq!(at(&s[0].kids[1]), (2, 3));
        assert_eq!(at(&s[0].kids[1].kids[1]), (2, 6));
        assert_eq!(at(&s[0].kids[2].kids[0]), (3, 4));
    }

    #[test]
    fn rejects_out_of_range_integer() {
        assert!(parse_all("99999999999999999999").is_err());
    }
}

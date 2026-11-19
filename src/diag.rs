//! Static diagnostics. Like every other output, they print as S-expressions.

use crate::sexp::{quote_str, Pos};

#[derive(Debug, Clone, PartialEq)]
pub struct Diag {
    pub kind: &'static str,
    pub at: Option<Pos>,
    pub msg: String,
}

impl Diag {
    pub fn new(kind: &'static str, at: Pos, msg: impl Into<String>) -> Self {
        Diag { kind, at: Some(at), msg: msg.into() }
    }

    pub fn to_sexp(&self) -> String {
        let at = match self.at {
            Some(p) => format!(" :at (line {} col {})", p.line, p.col),
            None => String::new(),
        };
        format!("(error :kind {}{} :msg {})", self.kind, at, quote_str(&self.msg))
    }
}

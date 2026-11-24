//! Static diagnostics and run-time errors. Like every other output, they
//! print as S-expressions.

use crate::sexp::{quote_str, Pos};

/// What went wrong, as `:kind` prints it. Each kind decides the exit code, so
/// a new failure picks its class here and `main` never chooses a number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    // The input could not be taken: exit 2.
    Parse,
    Syntax,
    Load,
    Io,
    Usage,
    // The program is wrong or failed while running: exit 1.
    Type,
    Effect,
    Contract,
    Overflow,
    DivZero,
    Bounds,
    Arity,
    Unbound,
    Stack,
    Alloc,
    // A bug in warrant itself (a panic): exit 101, as Rust's runtime does.
    Internal,
}

impl ErrorKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ErrorKind::Parse => "parse",
            ErrorKind::Syntax => "syntax",
            ErrorKind::Load => "load",
            ErrorKind::Io => "io",
            ErrorKind::Usage => "usage",
            ErrorKind::Type => "type",
            ErrorKind::Effect => "effect",
            ErrorKind::Contract => "contract",
            ErrorKind::Overflow => "overflow",
            ErrorKind::DivZero => "div-zero",
            ErrorKind::Bounds => "bounds",
            ErrorKind::Arity => "arity",
            ErrorKind::Unbound => "unbound",
            ErrorKind::Stack => "stack",
            ErrorKind::Alloc => "alloc",
            ErrorKind::Internal => "internal",
        }
    }

    /// 1 for a failure of the program, 2 for input the tool could not take,
    /// 101 for a bug in warrant.
    pub fn exit_code(self) -> i32 {
        match self {
            ErrorKind::Parse | ErrorKind::Syntax | ErrorKind::Load | ErrorKind::Io | ErrorKind::Usage => 2,
            ErrorKind::Type
            | ErrorKind::Effect
            | ErrorKind::Contract
            | ErrorKind::Overflow
            | ErrorKind::DivZero
            | ErrorKind::Bounds
            | ErrorKind::Arity
            | ErrorKind::Unbound
            | ErrorKind::Stack
            | ErrorKind::Alloc => 1,
            ErrorKind::Internal => 101,
        }
    }
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Diag {
    pub kind: ErrorKind,
    pub at: Option<Pos>,
    pub msg: String,
}

impl Diag {
    pub fn new(kind: ErrorKind, at: Pos, msg: impl Into<String>) -> Self {
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

/// A run-time failure, with the functions on the call stack innermost first.
#[derive(Debug)]
pub struct RtError {
    pub kind: ErrorKind,
    pub msg: String,
    pub trace: Vec<String>,
}

impl RtError {
    pub fn new(kind: ErrorKind, msg: impl Into<String>) -> Self {
        RtError { kind, msg: msg.into(), trace: Vec::new() }
    }
    pub fn to_sexp(&self) -> String {
        let tr = if self.trace.is_empty() {
            String::new()
        } else {
            format!(" :trace ({})", self.trace.join(" "))
        };
        format!("(error :kind {} :msg {}{})", self.kind, quote_str(&self.msg), tr)
    }
}

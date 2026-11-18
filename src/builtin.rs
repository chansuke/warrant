//! The builtin functions. Every pass (interpreter, type checker, effect
//! checker, VC generator) matches on this enum, so adding a builtin is a
//! compile error everywhere it still needs handling.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Not,
    Len,
    Get,
    Slice,
    Rest,
    Concat,
    Cons,
    IsEmpty,
    Range,
    Vec,
    Map,
    Fold,
    Filter,
    All,
    IsSorted,
    IsPerm,
    Print,
}

impl Builtin {
    pub const ALL: &'static [Builtin] = &[
        Builtin::Add,
        Builtin::Sub,
        Builtin::Mul,
        Builtin::Div,
        Builtin::Mod,
        Builtin::Eq,
        Builtin::Lt,
        Builtin::Le,
        Builtin::Gt,
        Builtin::Ge,
        Builtin::Not,
        Builtin::Len,
        Builtin::Get,
        Builtin::Slice,
        Builtin::Rest,
        Builtin::Concat,
        Builtin::Cons,
        Builtin::IsEmpty,
        Builtin::Range,
        Builtin::Vec,
        Builtin::Map,
        Builtin::Fold,
        Builtin::Filter,
        Builtin::All,
        Builtin::IsSorted,
        Builtin::IsPerm,
        Builtin::Print,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Builtin::Add => "+",
            Builtin::Sub => "-",
            Builtin::Mul => "*",
            Builtin::Div => "/",
            Builtin::Mod => "mod",
            Builtin::Eq => "=",
            Builtin::Lt => "<",
            Builtin::Le => "<=",
            Builtin::Gt => ">",
            Builtin::Ge => ">=",
            Builtin::Not => "not",
            Builtin::Len => "len",
            Builtin::Get => "get",
            Builtin::Slice => "slice",
            Builtin::Rest => "rest",
            Builtin::Concat => "concat",
            Builtin::Cons => "cons",
            Builtin::IsEmpty => "empty?",
            Builtin::Range => "range",
            Builtin::Vec => "vec",
            Builtin::Map => "map",
            Builtin::Fold => "fold",
            Builtin::Filter => "filter",
            Builtin::All => "all?",
            Builtin::IsSorted => "sorted?",
            Builtin::IsPerm => "perm?",
            Builtin::Print => "print",
        }
    }

    /// The interpreter resolves symbols through this on every lookup, so it is
    /// a `match` rather than a scan over `ALL`.
    pub fn from_name(s: &str) -> Option<Builtin> {
        Some(match s {
            "+" => Builtin::Add,
            "-" => Builtin::Sub,
            "*" => Builtin::Mul,
            "/" => Builtin::Div,
            "mod" => Builtin::Mod,
            "=" => Builtin::Eq,
            "<" => Builtin::Lt,
            "<=" => Builtin::Le,
            ">" => Builtin::Gt,
            ">=" => Builtin::Ge,
            "not" => Builtin::Not,
            "len" => Builtin::Len,
            "get" => Builtin::Get,
            "slice" => Builtin::Slice,
            "rest" => Builtin::Rest,
            "concat" => Builtin::Concat,
            "cons" => Builtin::Cons,
            "empty?" => Builtin::IsEmpty,
            "range" => Builtin::Range,
            "vec" => Builtin::Vec,
            "map" => Builtin::Map,
            "fold" => Builtin::Fold,
            "filter" => Builtin::Filter,
            "all?" => Builtin::All,
            "sorted?" => Builtin::IsSorted,
            "perm?" => Builtin::IsPerm,
            "print" => Builtin::Print,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique_and_resolve_back() {
        for b in Builtin::ALL {
            assert_eq!(Builtin::from_name(b.name()), Some(*b));
        }
    }
}

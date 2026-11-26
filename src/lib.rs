//! Warrant: canonical S-expression syntax, Wisp-style human view, static
//! types and effects, contracts proved with z3 or checked at run time, a
//! compiled runtime that runs pure calls in parallel, and a machine-readable
//! profiler.

// stdout belongs to the CLI in main.rs, whose every line is an S-expression,
// and a library error is a value, not a panic without a reason.
#![deny(clippy::print_stdout, clippy::print_stderr, clippy::unwrap_used)]

pub mod ast;
pub mod builtin;
pub mod cache;
pub mod contracts;
pub mod diag;
pub mod effects;
pub mod ir;
pub mod profile;
pub mod rt;
pub mod sexp;
pub mod smt;
pub mod solver;
pub mod specdiff;
pub mod types;
pub mod value;
pub mod vc;
pub mod verify;
pub mod wisp;

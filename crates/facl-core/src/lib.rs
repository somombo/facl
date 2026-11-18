//! The facl decision engine.
//!
//! This crate holds all of facl's security logic: it lowers a parsed policy to
//! an IR, canonicalizes and matches request paths, evaluates CEL conditions
//! and decides allow or deny. It is the proof target of the verification
//! pipeline, so it is written in the subset of Rust that Aeneas can extract:
//! `no_std`, no dependencies, UTF-8 text as `Vec<u8>`, `while` loops over
//! indices, and no code path that can panic.
#![no_std]
#![forbid(unsafe_code)]
#![deny(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
#![cfg_attr(
    test,
    allow(
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::panic,
        clippy::disallowed_types,
        clippy::disallowed_methods
    )
)]

extern crate alloc;
#[cfg(test)]
extern crate std;

pub mod ast;
pub mod decide;
pub mod eval;
pub mod footprint;
pub mod ir;
pub mod lower;
pub mod path;
pub mod value;

pub use ast::*;
pub use decide::{
    Conditions, Decision, DenyReason, HostConditions, Outcome, Request, Verdict, combine, decide,
    decide_with, method_bit,
};
pub use eval::{Env, Host, eval};
pub use footprint::{Footprint, footprint};
pub use ir::{CExpr, CompiledAllow, Pattern, Policy, Rule, Seg};
pub use lower::{LowerError, LowerErrorKind, MAX_DEPTH, lower};
pub use path::{Capture, PathError, canonicalize, match_pattern};
pub use value::{EvalError, Value, bytes_eq, map_get, value_eq};

#[cfg(test)]
mod tests;

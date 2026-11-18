//! The intermediate representation that policies are lowered to.
//!
//! A policy is plain data, so one interpreter evaluates it and it can be
//! serialized and passed around.

use crate::ast::CmpOp;
use crate::value::Value;
use alloc::boxed::Box;
use alloc::vec::Vec;

/// A compiled policy.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Policy {
    /// One rule per `match` that has allows, in source pre-order.
    pub rules: Vec<Rule>,
}

/// The allows that share one full path pattern.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rule {
    /// The full pattern: the parent's segments followed by the child's.
    pub pattern: Pattern,
    /// The allow statements of this match.
    pub allows: Vec<CompiledAllow>,
}

/// A path pattern.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Pattern {
    /// The leading segments.
    pub segs: Vec<Seg>,
    /// True when the pattern ends in `{name=**}`.
    pub rest: bool,
}

/// A segment of a compiled pattern. Captures are numbered in order: each
/// `Var`, then the rest capture.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Seg {
    /// A literal segment.
    Lit(Vec<u8>),
    /// A one-segment capture.
    Var,
}

/// An allow statement with its condition lowered.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CompiledAllow {
    /// The granted methods as a bit set.
    pub methods: u8,
    /// The condition; a missing condition lowers to `Lit(Bool(true))`.
    pub cond: CExpr,
}

/// A lowered expression. Names are resolved: captures are slots, and calls
/// are specific nodes.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CExpr {
    /// A literal value.
    Lit(Value),
    /// The capture with this number.
    Slot(u32),
    /// The `request` value.
    Request,
    /// The `context` value.
    Context,
    /// A list literal.
    List(Vec<CExpr>),
    /// `a.b`
    Select(Box<CExpr>, Vec<u8>),
    /// `a[k]`
    Index(Box<CExpr>, Box<CExpr>),
    /// `has(a.b)`
    Has(Box<CExpr>, Vec<u8>),
    /// `size(x)` or `x.size()`
    Size(Box<CExpr>),
    /// `x.startsWith(y)`
    StartsWith(Box<CExpr>, Box<CExpr>),
    /// `x.endsWith(y)`
    EndsWith(Box<CExpr>, Box<CExpr>),
    /// `request.is(t)`
    RequestIs(Box<CExpr>),
    /// `!a`
    Not(Box<CExpr>),
    /// `a && b`
    And(Box<CExpr>, Box<CExpr>),
    /// `a || b`
    Or(Box<CExpr>, Box<CExpr>),
    /// A comparison.
    Cmp(CmpOp, Box<CExpr>, Box<CExpr>),
    /// `a in b`
    In(Box<CExpr>, Box<CExpr>),
}

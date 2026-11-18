//! Lowering: from the syntax tree to the IR.
//!
//! `facl-check` reports every problem in a policy. Lowering repeats the
//! checks that the engine relies on, as defence in depth, and stops at the
//! first problem.

use crate::ast::{Allow, Expr, ExprKind, Item, Match, PatSeg, Service, Span};
use crate::ir::{CExpr, CompiledAllow, Pattern, Policy, Rule, Seg};
use crate::value::{Value, bytes_eq};
use alloc::boxed::Box;
use alloc::vec::Vec;

/// The deepest nesting of expressions, and of `match` blocks, that lowering
/// accepts. The engine's recursion is bounded by it.
pub const MAX_DEPTH: u32 = 64;

/// What is wrong with a policy.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LowerErrorKind {
    /// A name is not `request`, `context` or a capture in scope.
    UnknownIdentifier,
    /// A capture is named `request` or `context`.
    ReservedCaptureName,
    /// A capture name is already bound by this match or an enclosing one.
    DuplicateCapture,
    /// `{name=**}` is not the last segment of the pattern.
    RestNotLast,
    /// A match ending in `{name=**}` contains nested matches.
    RestWithChildren,
    /// A call to a function or method that does not exist.
    UnknownFunction,
    /// A call with the wrong number of arguments.
    BadArity,
    /// A call on the wrong kind of target, or `has` of a non-selection.
    BadTarget,
    /// Matches or expressions are nested deeper than [`MAX_DEPTH`].
    TooDeep,
}

/// A lowering failure and where it is.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LowerError {
    /// The problem.
    pub kind: LowerErrorKind,
    /// The source span it concerns.
    pub span: Span,
}

fn fail<T>(kind: LowerErrorKind, span: &Span) -> Result<T, LowerError> {
    Err(LowerError { kind, span: *span })
}

/// Lowers a service to a policy, returning the first error found.
pub fn lower(service: &Service) -> Result<Policy, LowerError> {
    let mut rules = Vec::new();
    let mut i = 0;
    while i < service.matches.len() {
        lower_match(&service.matches[i], &[], &[], 1, &mut rules)?;
        i += 1;
    }
    Ok(Policy { rules })
}

/// Lowers one match and, after it, its nested matches (source pre-order).
fn lower_match(
    m: &Match,
    parent_segs: &[Seg],
    parent_names: &[Vec<u8>],
    depth: u32,
    rules: &mut Vec<Rule>,
) -> Result<(), LowerError> {
    if depth > MAX_DEPTH {
        return fail(LowerErrorKind::TooDeep, &m.span);
    }
    let mut segs = parent_segs.to_vec();
    let mut names = parent_names.to_vec();
    let rest = lower_pattern(m, &mut segs, &mut names)?;
    let mut allows = Vec::new();
    let mut i = 0;
    while i < m.body.len() {
        match &m.body[i] {
            Item::Allow(a) => allows.push(lower_allow(a, &names)?),
            Item::Match(_) if rest => return fail(LowerErrorKind::RestWithChildren, &m.span),
            Item::Match(_) => {}
        }
        i += 1;
    }
    if !allows.is_empty() {
        let pattern = Pattern {
            segs: segs.clone(),
            rest,
        };
        rules.push(Rule { pattern, allows });
    }
    let mut k = 0;
    while k < m.body.len() {
        if let Item::Match(child) = &m.body[k] {
            lower_match(child, &segs, &names, depth + 1, rules)?;
        }
        k += 1;
    }
    Ok(())
}

/// Appends the match's segments and capture names; returns whether it ends in
/// a rest capture.
fn lower_pattern(
    m: &Match,
    segs: &mut Vec<Seg>,
    names: &mut Vec<Vec<u8>>,
) -> Result<bool, LowerError> {
    let mut rest = false;
    let mut i = 0;
    while i < m.pattern.len() {
        match &m.pattern[i] {
            PatSeg::Lit(s) => segs.push(Seg::Lit(s.clone())),
            PatSeg::Var(n) => {
                bind(names, n, &m.span)?;
                segs.push(Seg::Var);
            }
            PatSeg::Rest(n) => {
                if i + 1 != m.pattern.len() {
                    return fail(LowerErrorKind::RestNotLast, &m.span);
                }
                bind(names, n, &m.span)?;
                rest = true;
            }
        }
        i += 1;
    }
    Ok(rest)
}

/// Adds a capture name, rejecting reserved and repeated names.
fn bind(names: &mut Vec<Vec<u8>>, name: &[u8], span: &Span) -> Result<(), LowerError> {
    if bytes_eq(name, b"request") || bytes_eq(name, b"context") {
        return fail(LowerErrorKind::ReservedCaptureName, span);
    }
    if slot_of(names, name).is_some() {
        return fail(LowerErrorKind::DuplicateCapture, span);
    }
    names.push(name.to_vec());
    Ok(())
}

fn slot_of(names: &[Vec<u8>], name: &[u8]) -> Option<u32> {
    let mut i = 0;
    while i < names.len() {
        if bytes_eq(&names[i], name) {
            return Some(i as u32);
        }
        i += 1;
    }
    None
}

fn lower_allow(a: &Allow, names: &[Vec<u8>]) -> Result<CompiledAllow, LowerError> {
    let cond = match &a.cond {
        Some(e) => lower_expr(e, names, 1)?,
        None => CExpr::Lit(Value::Bool(true)),
    };
    Ok(CompiledAllow {
        methods: a.methods,
        cond,
    })
}

fn lower_expr(e: &Expr, names: &[Vec<u8>], depth: u32) -> Result<CExpr, LowerError> {
    if depth > MAX_DEPTH {
        return fail(LowerErrorKind::TooDeep, &e.span);
    }
    let d = depth + 1;
    match &e.kind {
        ExprKind::Null => Ok(CExpr::Lit(Value::Null)),
        ExprKind::Bool(b) => Ok(CExpr::Lit(Value::Bool(*b))),
        ExprKind::Int(n) => Ok(CExpr::Lit(Value::Int(*n))),
        ExprKind::Str(s) => Ok(CExpr::Lit(Value::Str(s.clone()))),
        ExprKind::List(items) => Ok(CExpr::List(lower_all(items, names, d)?)),
        ExprKind::Ident(n) => lower_ident(n, names, &e.span),
        ExprKind::Select(a, key) => Ok(CExpr::Select(lower_box(a, names, d)?, key.clone())),
        ExprKind::Index(a, k) => Ok(CExpr::Index(
            lower_box(a, names, d)?,
            lower_box(k, names, d)?,
        )),
        ExprKind::Call(name, args) => lower_call(name, args, names, d, &e.span),
        ExprKind::Method(target, name, args) => lower_method(target, name, args, names, d, &e.span),
        ExprKind::Not(a) => Ok(CExpr::Not(lower_box(a, names, d)?)),
        ExprKind::And(a, b) => Ok(CExpr::And(lower_box(a, names, d)?, lower_box(b, names, d)?)),
        ExprKind::Or(a, b) => Ok(CExpr::Or(lower_box(a, names, d)?, lower_box(b, names, d)?)),
        ExprKind::Cmp(op, a, b) => Ok(CExpr::Cmp(
            op.clone(),
            lower_box(a, names, d)?,
            lower_box(b, names, d)?,
        )),
        ExprKind::In(a, b) => Ok(CExpr::In(lower_box(a, names, d)?, lower_box(b, names, d)?)),
    }
}

fn lower_box(e: &Expr, names: &[Vec<u8>], depth: u32) -> Result<Box<CExpr>, LowerError> {
    Ok(Box::new(lower_expr(e, names, depth)?))
}

fn lower_all(items: &[Expr], names: &[Vec<u8>], depth: u32) -> Result<Vec<CExpr>, LowerError> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < items.len() {
        out.push(lower_expr(&items[i], names, depth)?);
        i += 1;
    }
    Ok(out)
}

fn lower_ident(name: &[u8], names: &[Vec<u8>], span: &Span) -> Result<CExpr, LowerError> {
    if bytes_eq(name, b"request") {
        return Ok(CExpr::Request);
    }
    if bytes_eq(name, b"context") {
        return Ok(CExpr::Context);
    }
    match slot_of(names, name) {
        Some(slot) => Ok(CExpr::Slot(slot)),
        None => fail(LowerErrorKind::UnknownIdentifier, span),
    }
}

/// Global calls: `size(x)` and `has(a.b)`.
fn lower_call(
    name: &[u8],
    args: &[Expr],
    names: &[Vec<u8>],
    depth: u32,
    span: &Span,
) -> Result<CExpr, LowerError> {
    let is_size = bytes_eq(name, b"size");
    let is_has = bytes_eq(name, b"has");
    if !is_size && !is_has {
        return fail(LowerErrorKind::UnknownFunction, span);
    }
    if args.len() != 1 {
        return fail(LowerErrorKind::BadArity, span);
    }
    if is_size {
        return Ok(CExpr::Size(lower_box(&args[0], names, depth)?));
    }
    match &args[0].kind {
        ExprKind::Select(target, key) => {
            Ok(CExpr::Has(lower_box(target, names, depth)?, key.clone()))
        }
        _ => fail(LowerErrorKind::BadTarget, span),
    }
}

/// Methods: `x.size()`, `x.startsWith(s)`, `x.endsWith(s)`, `request.is(s)`.
fn lower_method(
    target: &Expr,
    name: &[u8],
    args: &[Expr],
    names: &[Vec<u8>],
    depth: u32,
    span: &Span,
) -> Result<CExpr, LowerError> {
    if bytes_eq(name, b"size") {
        if !args.is_empty() {
            return fail(LowerErrorKind::BadArity, span);
        }
        return Ok(CExpr::Size(lower_box(target, names, depth)?));
    }
    let is_starts = bytes_eq(name, b"startsWith");
    let is_ends = bytes_eq(name, b"endsWith");
    let is_is = bytes_eq(name, b"is");
    if !is_starts && !is_ends && !is_is {
        return fail(LowerErrorKind::UnknownFunction, span);
    }
    if args.len() != 1 {
        return fail(LowerErrorKind::BadArity, span);
    }
    if is_is {
        return match &target.kind {
            ExprKind::Ident(n) if bytes_eq(n, b"request") => {
                Ok(CExpr::RequestIs(lower_box(&args[0], names, depth)?))
            }
            _ => fail(LowerErrorKind::BadTarget, span),
        };
    }
    let t = lower_box(target, names, depth)?;
    let a = lower_box(&args[0], names, depth)?;
    if is_starts {
        Ok(CExpr::StartsWith(t, a))
    } else {
        Ok(CExpr::EndsWith(t, a))
    }
}

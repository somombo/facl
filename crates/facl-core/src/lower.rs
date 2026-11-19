//! Lowering: from the syntax tree to the IR.
//!
//! `facl-check` reports every problem in a policy. Lowering repeats the
//! checks that the engine relies on, as defence in depth, and stops at the
//! first problem.

use crate::ast::{Expr, ExprKind, Item, Match, PatSeg, Service, Span};
use crate::ir::{CExpr, CompiledAllow, Pattern, Policy, Rule, Seg};
use crate::path::copy_bytes;
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

/// Compiles the condition of one allow. `lower_with` calls it for each allow
/// with the captures in scope.
pub trait CompileCond<E, C> {
    /// Compiles `cond`, where `names` are the capture names in scope.
    fn compile(&self, cond: &Option<E>, names: &[Vec<u8>]) -> Result<C, LowerError>;
}

struct ExprCompiler;

impl CompileCond<Expr, CExpr> for ExprCompiler {
    fn compile(&self, cond: &Option<Expr>, names: &[Vec<u8>]) -> Result<CExpr, LowerError> {
        match cond {
            Some(e) => lower_expr(e, names, 1),
            None => Ok(CExpr::Lit(Value::Bool(true))),
        }
    }
}

/// Lowers a service to a policy, returning the first error found.
pub fn lower(service: &Service) -> Result<Policy, LowerError> {
    lower_with(service, &ExprCompiler)
}

/// Lowers the structure of a service, compiling conditions with `k`.
pub fn lower_with<E, C, K: CompileCond<E, C>>(
    service: &Service<E>,
    k: &K,
) -> Result<Policy<C>, LowerError> {
    let mut rules = Vec::new();
    let mut i = 0;
    while i < service.matches.len() {
        rules = lower_match(&service.matches[i], &[], &[], 1, k, rules)?;
        i += 1;
    }
    Ok(Policy { rules })
}

fn copy_segs(segs: &[Seg]) -> Vec<Seg> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < segs.len() {
        match &segs[i] {
            Seg::Lit(s) => out.push(Seg::Lit(copy_bytes(s))),
            Seg::Var => out.push(Seg::Var),
        }
        i += 1;
    }
    out
}

fn copy_names(names: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < names.len() {
        out.push(copy_bytes(&names[i]));
        i += 1;
    }
    out
}

/// Lowers one match and, after it, its nested matches (source pre-order).
fn lower_match<E, C, K: CompileCond<E, C>>(
    m: &Match<E>,
    parent_segs: &[Seg],
    parent_names: &[Vec<u8>],
    depth: u32,
    k: &K,
    rules: Vec<Rule<C>>,
) -> Result<Vec<Rule<C>>, LowerError> {
    if depth > MAX_DEPTH {
        return fail(LowerErrorKind::TooDeep, &m.span);
    }
    let mut segs = copy_segs(parent_segs);
    let mut names = copy_names(parent_names);
    let rest = lower_pattern(&m.pattern, &m.span, &mut segs, &mut names)?;
    let allows = lower_allows(m, rest, &names, k)?;
    let mut rules = rules;
    if !allows.is_empty() {
        let pattern = Pattern {
            segs: copy_segs(&segs),
            rest,
        };
        rules.push(Rule { pattern, allows });
    }
    lower_children(m, &segs, &names, depth, k, rules)
}

/// Compiles the allows of a match in source order.
fn lower_allows<E, C, K: CompileCond<E, C>>(
    m: &Match<E>,
    rest: bool,
    names: &[Vec<u8>],
    k: &K,
) -> Result<Vec<CompiledAllow<C>>, LowerError> {
    let mut allows = Vec::new();
    let mut i = 0;
    while i < m.body.len() {
        allows = lower_allow_item(&m.body[i], &m.span, rest, names, k, allows)?;
        i += 1;
    }
    Ok(allows)
}

fn lower_allow_item<E, C, K: CompileCond<E, C>>(
    item: &Item<E>,
    span: &Span,
    rest: bool,
    names: &[Vec<u8>],
    k: &K,
    allows: Vec<CompiledAllow<C>>,
) -> Result<Vec<CompiledAllow<C>>, LowerError> {
    let mut allows = allows;
    match item {
        Item::Allow(a) => {
            let cond = k.compile(&a.cond, names)?;
            allows.push(CompiledAllow {
                methods: a.methods,
                cond,
            });
            Ok(allows)
        }
        Item::Match(_) if rest => fail(LowerErrorKind::RestWithChildren, span),
        Item::Match(_) => Ok(allows),
    }
}

/// Lowers the nested matches of a match in source order.
fn lower_children<E, C, K: CompileCond<E, C>>(
    m: &Match<E>,
    segs: &[Seg],
    names: &[Vec<u8>],
    depth: u32,
    k: &K,
    rules: Vec<Rule<C>>,
) -> Result<Vec<Rule<C>>, LowerError> {
    let mut rules = rules;
    let mut i = 0;
    while i < m.body.len() {
        rules = lower_child(&m.body[i], segs, names, depth, k, rules)?;
        i += 1;
    }
    Ok(rules)
}

fn lower_child<E, C, K: CompileCond<E, C>>(
    item: &Item<E>,
    segs: &[Seg],
    names: &[Vec<u8>],
    depth: u32,
    k: &K,
    rules: Vec<Rule<C>>,
) -> Result<Vec<Rule<C>>, LowerError> {
    match item {
        Item::Match(child) => lower_match(child, segs, names, depth + 1, k, rules),
        Item::Allow(_) => Ok(rules),
    }
}

/// Appends the pattern's segments and capture names; returns whether it ends
/// in a rest capture.
fn lower_pattern(
    pattern: &[PatSeg],
    span: &Span,
    segs: &mut Vec<Seg>,
    names: &mut Vec<Vec<u8>>,
) -> Result<bool, LowerError> {
    let mut rest = false;
    let mut i = 0;
    while i < pattern.len() {
        match &pattern[i] {
            PatSeg::Lit(s) => segs.push(Seg::Lit(copy_bytes(s))),
            PatSeg::Var(n) => {
                bind(names, n, span)?;
                segs.push(Seg::Var);
            }
            PatSeg::Rest(n) => {
                if i + 1 != pattern.len() {
                    return fail(LowerErrorKind::RestNotLast, span);
                }
                bind(names, n, span)?;
                rest = true;
            }
        }
        i += 1;
    }
    Ok(rest)
}

/// True for the names `request` and `context`.
fn is_reserved(name: &[u8]) -> bool {
    name.len() == 7
        && ((name[0] == b'r'
            && name[1] == b'e'
            && name[2] == b'q'
            && name[3] == b'u'
            && name[4] == b'e'
            && name[5] == b's'
            && name[6] == b't')
            || (name[0] == b'c'
                && name[1] == b'o'
                && name[2] == b'n'
                && name[3] == b't'
                && name[4] == b'e'
                && name[5] == b'x'
                && name[6] == b't'))
}

/// Adds a capture name, rejecting reserved and repeated names.
fn bind(names: &mut Vec<Vec<u8>>, name: &[u8], span: &Span) -> Result<(), LowerError> {
    if is_reserved(name) {
        return fail(LowerErrorKind::ReservedCaptureName, span);
    }
    if slot_of(names, name).is_some() {
        return fail(LowerErrorKind::DuplicateCapture, span);
    }
    names.push(copy_bytes(name));
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
        // The selection counts toward the depth, as in the checker.
        ExprKind::Select(target, key) => Ok(CExpr::Has(
            lower_box(target, names, depth + 1)?,
            key.clone(),
        )),
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

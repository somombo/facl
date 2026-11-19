//! The syntax tree that `facl-syntax` builds and `facl-check` and
//! [`crate::lower`] read.

use alloc::boxed::Box;
use alloc::vec::Vec;

/// A byte range in the source text.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    /// Offset of the first byte.
    pub start: u32,
    /// Offset one past the last byte.
    pub end: u32,
}

/// A whole rules file: `service NAME { ... }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Service<E = Expr> {
    /// The dotted service name, such as `http`.
    pub name: Vec<u8>,
    /// The top-level `match` blocks.
    pub matches: Vec<Match<E>>,
    /// The span of the whole service.
    pub span: Span,
}

/// A `match` block.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Match<E = Expr> {
    /// The path pattern relative to the parent match.
    pub pattern: Vec<PatSeg>,
    /// The nested matches and allow statements, in source order.
    pub body: Vec<Item<E>>,
    /// The span of the whole block.
    pub span: Span,
}

/// Something that can appear inside a `match` block.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Item<E = Expr> {
    /// A nested match.
    Match(Match<E>),
    /// An allow statement.
    Allow(Allow<E>),
}

/// One segment of a path pattern.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PatSeg {
    /// A literal segment.
    Lit(Vec<u8>),
    /// `{name}`: one segment, bound to `name`.
    Var(Vec<u8>),
    /// `{name=**}`: zero or more segments, bound to `name` as a list.
    Rest(Vec<u8>),
}

/// An `allow` statement.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Allow<E = Expr> {
    /// The granted methods as a bit set; see [`crate::method_bit`].
    pub methods: u8,
    /// The condition; `None` for `allow read;`, which always applies.
    pub cond: Option<E>,
    /// The span of the whole statement.
    pub span: Span,
}

/// An expression with its source span.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Expr {
    /// What kind of expression this is.
    pub kind: ExprKind,
    /// The source span.
    pub span: Span,
}

/// The shapes of expression in the CEL subset.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprKind {
    /// `null`
    Null,
    /// `true` or `false`
    Bool(bool),
    /// An integer literal.
    Int(i64),
    /// A string literal.
    Str(Vec<u8>),
    /// A list literal.
    List(Vec<Expr>),
    /// A bare name.
    Ident(Vec<u8>),
    /// `a.b`
    Select(Box<Expr>, Vec<u8>),
    /// `a[k]`
    Index(Box<Expr>, Box<Expr>),
    /// A global call such as `size(x)` or `has(a.b)`.
    Call(Vec<u8>, Vec<Expr>),
    /// A method call such as `x.startsWith(y)` or `request.is(t)`.
    Method(Box<Expr>, Vec<u8>, Vec<Expr>),
    /// `!a`
    Not(Box<Expr>),
    /// `a && b`
    And(Box<Expr>, Box<Expr>),
    /// `a || b`
    Or(Box<Expr>, Box<Expr>),
    /// A comparison.
    Cmp(CmpOp, Box<Expr>, Box<Expr>),
    /// `a in b`
    In(Box<Expr>, Box<Expr>),
}

/// A comparison operator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CmpOp {
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
}

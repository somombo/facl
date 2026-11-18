//! Name checks and lints for facl policies.
//!
//! The checker reads a parsed [`Service`] and reports every problem it finds.
//! It can only reject: it never rewrites the tree, so a bug here cannot widen
//! access. `facl_core::lower` repeats the checks the engine relies on.

use facl_core::{Allow, Expr, ExprKind, Item, Match, PatSeg, Service, Span};

/// The deepest nesting of expressions and matches the engine accepts.
pub const MAX_DEPTH: u32 = facl_core::MAX_DEPTH;

/// How serious a finding is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// The policy must not be used.
    Error,
    /// The policy is valid but probably not what was meant.
    Warning,
}

/// One finding, with the source span it concerns.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Issue {
    /// Whether this is an error or a warning.
    pub severity: Severity,
    /// A human-readable description.
    pub message: String,
    /// The source span.
    pub span: Span,
}

/// Checks a service and returns every issue, in source order. A policy is
/// acceptable when no issue has [`Severity::Error`].
pub fn check(service: &Service) -> Vec<Issue> {
    let mut c = Checker { issues: Vec::new() };
    for m in &service.matches {
        c.check_match(m, &[], 1);
    }
    c.issues
}

/// Returns true when any issue is an error.
pub fn has_errors(issues: &[Issue]) -> bool {
    issues.iter().any(|i| i.severity == Severity::Error)
}

struct Checker {
    issues: Vec<Issue>,
}

fn show(name: &[u8]) -> String {
    String::from_utf8_lossy(name).into_owned()
}

impl Checker {
    fn error(&mut self, span: Span, message: String) {
        self.issues.push(Issue {
            severity: Severity::Error,
            message,
            span,
        });
    }

    fn warn(&mut self, span: Span, message: String) {
        self.issues.push(Issue {
            severity: Severity::Warning,
            message,
            span,
        });
    }

    fn check_match(&mut self, m: &Match, parent: &[Vec<u8>], depth: u32) {
        if depth > MAX_DEPTH {
            self.error(
                m.span,
                format!("matches are nested more than {MAX_DEPTH} deep"),
            );
            return;
        }
        let mut names = parent.to_vec();
        let ends_in_rest = self.check_pattern(m, &mut names);
        let mut has_allow = false;
        let mut has_child = false;
        for item in &m.body {
            match item {
                Item::Allow(a) => {
                    has_allow = true;
                    self.check_allow(a, &names);
                }
                Item::Match(child) => {
                    has_child = true;
                    if ends_in_rest {
                        self.error(
                            child.span,
                            "a match ending in '{name=**}' cannot contain nested matches".into(),
                        );
                    } else {
                        self.check_match(child, &names, depth + 1);
                    }
                }
            }
        }
        if !has_allow && !has_child {
            self.warn(
                m.span,
                "match has no allow statements and grants nothing".into(),
            );
        }
    }

    /// Binds the pattern's captures; returns whether it ends in a rest capture.
    fn check_pattern(&mut self, m: &Match, names: &mut Vec<Vec<u8>>) -> bool {
        let mut rest = false;
        for (i, seg) in m.pattern.iter().enumerate() {
            let name = match seg {
                PatSeg::Lit(_) => continue,
                PatSeg::Var(n) => n,
                PatSeg::Rest(n) => {
                    if i + 1 == m.pattern.len() {
                        rest = true;
                    } else {
                        self.error(m.span, "'{name=**}' must be the last segment".into());
                    }
                    n
                }
            };
            if name == b"request" || name == b"context" {
                self.error(
                    m.span,
                    format!("'{}' is reserved and cannot be a capture", show(name)),
                );
            } else if names.contains(name) {
                self.error(m.span, format!("capture '{}' is already bound", show(name)));
            }
            names.push(name.clone());
        }
        rest
    }

    fn check_allow(&mut self, a: &Allow, names: &[Vec<u8>]) {
        if let Some(cond) = &a.cond {
            self.check_expr(cond, names, 1);
        }
    }

    fn check_expr(&mut self, e: &Expr, names: &[Vec<u8>], depth: u32) {
        if depth > MAX_DEPTH {
            self.error(
                e.span,
                format!("expression is nested more than {MAX_DEPTH} deep"),
            );
            return;
        }
        let d = depth + 1;
        match &e.kind {
            ExprKind::Null | ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) => {}
            ExprKind::List(items) => self.check_all(items, names, d),
            ExprKind::Ident(n) => {
                if n != b"request" && n != b"context" && !names.contains(n) {
                    self.error(e.span, format!("unknown name '{}'", show(n)));
                }
            }
            ExprKind::Select(a, _) | ExprKind::Not(a) => self.check_expr(a, names, d),
            ExprKind::Index(a, b)
            | ExprKind::And(a, b)
            | ExprKind::Or(a, b)
            | ExprKind::Cmp(_, a, b)
            | ExprKind::In(a, b) => {
                self.check_expr(a, names, d);
                self.check_expr(b, names, d);
            }
            ExprKind::Call(name, args) => self.check_call(e, name, args, names, d),
            ExprKind::Method(target, name, args) => {
                self.check_method(e, target, name, args, names, d);
            }
        }
    }

    fn check_all(&mut self, items: &[Expr], names: &[Vec<u8>], depth: u32) {
        for item in items {
            self.check_expr(item, names, depth);
        }
    }

    fn check_call(&mut self, e: &Expr, name: &[u8], args: &[Expr], names: &[Vec<u8>], d: u32) {
        self.check_all(args, names, d);
        if name != b"size" && name != b"has" {
            self.error(e.span, format!("unknown function '{}'", show(name)));
        } else if args.len() != 1 {
            self.error(
                e.span,
                format!("'{}' takes exactly one argument", show(name)),
            );
        } else if name == b"has" && !matches!(args[0].kind, ExprKind::Select(..)) {
            self.error(
                e.span,
                "'has' needs a field selection such as has(a.b)".into(),
            );
        }
    }

    fn check_method(
        &mut self,
        e: &Expr,
        target: &Expr,
        name: &[u8],
        args: &[Expr],
        names: &[Vec<u8>],
        d: u32,
    ) {
        self.check_expr(target, names, d);
        self.check_all(args, names, d);
        let expected = match name {
            b"size" => 0,
            b"startsWith" | b"endsWith" | b"is" => 1,
            _ => {
                self.error(e.span, format!("unknown method '{}'", show(name)));
                return;
            }
        };
        if args.len() != expected {
            self.error(
                e.span,
                format!("'{}' takes {expected} argument(s)", show(name)),
            );
        } else if name == b"is" && !matches!(&target.kind, ExprKind::Ident(n) if n == b"request") {
            self.error(e.span, "'is' can only be called on 'request'".into());
        }
    }
}

#[cfg(test)]
mod tests;

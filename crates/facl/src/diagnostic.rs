//! Diagnostics with 1-based line and column positions.

use facl_check::Issue;
use facl_core::{LowerError, LowerErrorKind, Span};
use facl_syntax::{ParseError, line_col};
use std::fmt;

pub use facl_check::Severity;

/// A problem found in a rules file.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Diagnostic {
    /// Whether this is an error or a warning.
    pub severity: Severity,
    /// A human-readable description.
    pub message: String,
    /// 1-based line.
    pub line: u32,
    /// 1-based column, counted in characters.
    pub col: u32,
}

impl Diagnostic {
    fn at(source: &str, severity: Severity, message: String, span: &Span) -> Diagnostic {
        let (line, col) = line_col(source, span.start);
        Diagnostic {
            severity,
            message,
            line,
            col,
        }
    }

    /// Returns true for an error, false for a warning.
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    pub(crate) fn from_parse_error(source: &str, e: &ParseError) -> Diagnostic {
        Diagnostic::at(source, Severity::Error, e.message.clone(), &e.span)
    }

    pub(crate) fn from_issue(source: &str, issue: &Issue) -> Diagnostic {
        Diagnostic::at(source, issue.severity, issue.message.clone(), &issue.span)
    }

    pub(crate) fn from_lower_error(source: &str, e: &LowerError) -> Diagnostic {
        let message = match e.kind {
            LowerErrorKind::UnknownIdentifier => "unknown name",
            LowerErrorKind::ReservedCaptureName => "reserved capture name",
            LowerErrorKind::DuplicateCapture => "duplicate capture name",
            LowerErrorKind::RestNotLast => "'{name=**}' must be the last segment",
            LowerErrorKind::RestWithChildren => "'{name=**}' match has nested matches",
            LowerErrorKind::UnknownFunction => "unknown function",
            LowerErrorKind::BadArity => "wrong number of arguments",
            LowerErrorKind::BadTarget => "invalid call target",
            LowerErrorKind::TooDeep => "nested too deeply",
        };
        Diagnostic::at(source, Severity::Error, message.to_string(), &e.span)
    }
}

impl fmt::Display for Diagnostic {
    /// Formats as `3:15: error: message`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        write!(f, "{}:{}: {kind}: {}", self.line, self.col, self.message)
    }
}

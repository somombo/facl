//! Rule combination and the allow or deny decision.

use crate::eval::{Env, Host, eval};
use crate::ir::Policy;
use crate::path::match_pattern;
use crate::value::{Value, bytes_eq};
use alloc::vec::Vec;

/// What one applicable condition contributed.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Outcome {
    /// The condition evaluated to exactly `true`.
    Granted,
    /// The condition was false, an error or not a boolean.
    NotGranted,
}

/// The combined verdict of all applicable conditions.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// At least one condition granted.
    Allow,
    /// None did.
    Deny,
}

/// Turns the outcomes of the applicable conditions into the verdict: allow
/// exactly when some condition was granted. Order does not matter, and an
/// extra outcome can never revoke a grant.
pub fn combine(outcomes: &[Outcome]) -> Verdict {
    let mut granted = false;
    let mut i = 0;
    while i < outcomes.len() {
        if let Outcome::Granted = outcomes[i] {
            granted = true;
        }
        i += 1;
    }
    if granted {
        Verdict::Allow
    } else {
        Verdict::Deny
    }
}

/// Why a request was denied.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DenyReason {
    /// No `match` pattern matched the path.
    NoMatchingRule,
    /// Some pattern matched, but no allow lists the method.
    NoAllowForMethod,
    /// Some allow lists the method, but no condition was true.
    ConditionsNotMet,
    /// The request path could not be canonicalized.
    BadRequestPath,
}

/// The engine's answer.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Decision {
    /// The request is allowed.
    Allow,
    /// The request is denied, with the reason.
    Deny(DenyReason),
}

/// A request as the engine sees it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Request {
    /// The method bit; see [`method_bit`]. 0 means an unknown method.
    pub method: u8,
    /// The canonical path segments.
    pub path: Vec<Vec<u8>>,
    /// The `request` value.
    pub request: Value,
    /// The `context` value.
    pub context: Value,
}

/// Maps an exact uppercase method name to its bit: GET=1, HEAD=2, OPTIONS=4,
/// POST=8, PUT=16, PATCH=32, DELETE=64. Anything else is 0, which no allow
/// grants.
pub fn method_bit(name: &[u8]) -> u8 {
    if bytes_eq(name, b"GET") {
        1
    } else if bytes_eq(name, b"HEAD") {
        2
    } else if bytes_eq(name, b"OPTIONS") {
        4
    } else if bytes_eq(name, b"POST") {
        8
    } else if bytes_eq(name, b"PUT") {
        16
    } else if bytes_eq(name, b"PATCH") {
        32
    } else if bytes_eq(name, b"DELETE") {
        64
    } else {
        0
    }
}

/// Decides a request.
///
/// A request is allowed only when a rule's pattern matches its whole path, an
/// allow of that rule lists the method, and the allow's condition evaluates
/// to exactly `true`. Every other request is denied.
pub fn decide<H: Host>(p: &Policy, r: &Request, host: &H) -> Decision {
    let mut outcomes = Vec::new();
    let mut matched = false;
    let mut applicable = false;
    let mut i = 0;
    while i < p.rules.len() {
        let rule = &p.rules[i];
        if let Some(slots) = match_pattern(&rule.pattern, &r.path) {
            matched = true;
            let env = Env {
                slots,
                request: r.request.clone(),
                context: r.context.clone(),
            };
            let mut j = 0;
            while j < rule.allows.len() {
                let allow = &rule.allows[j];
                if allow.methods & r.method != 0 {
                    applicable = true;
                    match eval(&allow.cond, &env, host) {
                        Ok(Value::Bool(true)) => outcomes.push(Outcome::Granted),
                        _ => outcomes.push(Outcome::NotGranted),
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }
    match combine(&outcomes) {
        Verdict::Allow => Decision::Allow,
        Verdict::Deny => {
            if !matched {
                Decision::Deny(DenyReason::NoMatchingRule)
            } else if !applicable {
                Decision::Deny(DenyReason::NoAllowForMethod)
            } else {
                Decision::Deny(DenyReason::ConditionsNotMet)
            }
        }
    }
}

//! Rule combination and the allow or deny decision.

use crate::eval::{Env, Host, eval};
use crate::ir::{CExpr, Policy, Rule};
use crate::path::{Capture, match_pattern};
use crate::value::Value;
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
    if name.len() == 3 {
        if name[0] == b'G' && name[1] == b'E' && name[2] == b'T' {
            return 1;
        }
        if name[0] == b'P' && name[1] == b'U' && name[2] == b'T' {
            return 16;
        }
    } else if name.len() == 4 {
        if name[0] == b'H' && name[1] == b'E' && name[2] == b'A' && name[3] == b'D' {
            return 2;
        }
        if name[0] == b'P' && name[1] == b'O' && name[2] == b'S' && name[3] == b'T' {
            return 8;
        }
    } else if name.len() == 5 {
        if name[0] == b'P'
            && name[1] == b'A'
            && name[2] == b'T'
            && name[3] == b'C'
            && name[4] == b'H'
        {
            return 32;
        }
    } else if name.len() == 6 {
        if name[0] == b'D'
            && name[1] == b'E'
            && name[2] == b'L'
            && name[3] == b'E'
            && name[4] == b'T'
            && name[5] == b'E'
        {
            return 64;
        }
    } else if name.len() == 7
        && name[0] == b'O'
        && name[1] == b'P'
        && name[2] == b'T'
        && name[3] == b'I'
        && name[4] == b'O'
        && name[5] == b'N'
        && name[6] == b'S'
    {
        return 4;
    }
    0
}

/// Evaluates the condition of one applicable allow.
pub trait Conditions<C> {
    /// What `cond` contributes, given the captures of the matched pattern.
    fn outcome(&self, cond: &C, captures: &[Capture]) -> Outcome;
}

/// Matches one rule. Returns the outcomes extended by each allow that lists
/// the method, whether the pattern matched, and whether an allow applied.
fn apply_rule<C, E: Conditions<C>>(
    rule: &Rule<C>,
    method: u8,
    segments: &[Vec<u8>],
    conds: &E,
    mut outcomes: Vec<Outcome>,
) -> (Vec<Outcome>, bool, bool) {
    let Some(captures) = match_pattern(&rule.pattern, segments) else {
        return (outcomes, false, false);
    };
    let mut applicable = false;
    let mut j = 0;
    while j < rule.allows.len() {
        let allow = &rule.allows[j];
        if allow.methods & method != 0 {
            applicable = true;
            outcomes.push(conds.outcome(&allow.cond, &captures));
        }
        j += 1;
    }
    (outcomes, true, applicable)
}

/// Decides a request, with the conditions evaluated by `conds`.
///
/// A request is allowed only when a rule's pattern matches its whole path, an
/// allow of that rule lists the method, and the allow's condition is granted.
/// Every other request is denied.
pub fn decide_with<C, E: Conditions<C>>(
    p: &Policy<C>,
    method: u8,
    segments: &[Vec<u8>],
    conds: &E,
) -> Decision {
    let mut outcomes = Vec::new();
    let mut matched = false;
    let mut applicable = false;
    let mut i = 0;
    while i < p.rules.len() {
        let rule = &p.rules[i];
        let (more, m, a) = apply_rule(rule, method, segments, conds, outcomes);
        outcomes = more;
        if m {
            matched = true;
        }
        if a {
            applicable = true;
        }
        i += 1;
    }
    match combine(&outcomes) {
        Verdict::Allow => Decision::Allow,
        Verdict::Deny => {
            if matched {
                if applicable {
                    Decision::Deny(DenyReason::ConditionsNotMet)
                } else {
                    Decision::Deny(DenyReason::NoAllowForMethod)
                }
            } else {
                Decision::Deny(DenyReason::NoMatchingRule)
            }
        }
    }
}

/// The CEL evaluator, bound to one request.
pub struct HostConditions<'a, H> {
    /// The host functions.
    pub host: &'a H,
    /// The `request` value.
    pub request: &'a Value,
    /// The `context` value.
    pub context: &'a Value,
}

impl<H: Host> Conditions<CExpr> for HostConditions<'_, H> {
    fn outcome(&self, cond: &CExpr, captures: &[Capture]) -> Outcome {
        let mut slots = Vec::new();
        let mut k = 0;
        while k < captures.len() {
            match &captures[k] {
                Capture::One(s) => slots.push(Value::Str(s.clone())),
                Capture::Rest(ss) => {
                    let mut items = Vec::new();
                    let mut m = 0;
                    while m < ss.len() {
                        items.push(Value::Str(ss[m].clone()));
                        m += 1;
                    }
                    slots.push(Value::List(items));
                }
            }
            k += 1;
        }
        let env = Env {
            slots,
            request: self.request,
            context: self.context,
        };
        match eval(cond, &env, self.host) {
            Ok(Value::Bool(true)) => Outcome::Granted,
            _ => Outcome::NotGranted,
        }
    }
}

/// Decides a request.
///
/// A request is allowed only when a rule's pattern matches its whole path, an
/// allow of that rule lists the method, and the allow's condition evaluates
/// to exactly `true`. Every other request is denied.
pub fn decide<H: Host>(p: &Policy, r: &Request, host: &H) -> Decision {
    let conds = HostConditions {
        host,
        request: &r.request,
        context: &r.context,
    };
    decide_with(p, r.method, &r.path, &conds)
}

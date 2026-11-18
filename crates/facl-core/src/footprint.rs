//! The footprint: which request facts a policy can read.
//!
//! The footprint is an optimization hint. An adapter may skip facts outside
//! it, such as token verification, and must still reach the same decision, so
//! it errs on the side of reading too much.

use crate::ir::{CExpr, Policy};
use crate::value::bytes_eq;

/// The top-level fields a policy can read. `request.method` and
/// `request.path` are always available and are not tracked.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Footprint {
    /// The policy may read `request.headers`.
    pub headers: bool,
    /// The policy may read `request.auth`.
    pub auth: bool,
    /// The policy may read `context`.
    pub context: bool,
}

/// Computes the footprint of a policy, conservatively.
///
/// - Any use of `request.headers`, or any `request.is()`, sets `headers`.
/// - Any use of `request.auth` sets `auth`.
/// - Using `request` other than as `.method`, `.path`, `.headers` or `.auth`
///   sets both `headers` and `auth`.
/// - Any use of `context` sets `context`.
pub fn footprint(p: &Policy) -> Footprint {
    let mut fp = Footprint {
        headers: false,
        auth: false,
        context: false,
    };
    let mut i = 0;
    while i < p.rules.len() {
        let rule = &p.rules[i];
        let mut j = 0;
        while j < rule.allows.len() {
            visit(&rule.allows[j].cond, &mut fp);
            j += 1;
        }
        i += 1;
    }
    fp
}

/// Records what a field read of `request` touches.
fn visit_field(target: &CExpr, key: &[u8], fp: &mut Footprint) {
    match target {
        CExpr::Request => {
            if bytes_eq(key, b"headers") {
                fp.headers = true;
            } else if bytes_eq(key, b"auth") {
                fp.auth = true;
            } else if !bytes_eq(key, b"method") && !bytes_eq(key, b"path") {
                fp.headers = true;
                fp.auth = true;
            }
        }
        other => visit(other, fp),
    }
}

fn visit(e: &CExpr, fp: &mut Footprint) {
    match e {
        CExpr::Lit(_) | CExpr::Slot(_) => {}
        CExpr::Request => {
            fp.headers = true;
            fp.auth = true;
        }
        CExpr::Context => fp.context = true,
        CExpr::List(items) => {
            let mut i = 0;
            while i < items.len() {
                visit(&items[i], fp);
                i += 1;
            }
        }
        CExpr::Select(a, key) | CExpr::Has(a, key) => visit_field(a, key, fp),
        CExpr::RequestIs(a) => {
            fp.headers = true;
            visit(a, fp);
        }
        CExpr::Size(a) | CExpr::Not(a) => visit(a, fp),
        CExpr::Index(a, b)
        | CExpr::StartsWith(a, b)
        | CExpr::EndsWith(a, b)
        | CExpr::And(a, b)
        | CExpr::Or(a, b)
        | CExpr::Cmp(_, a, b)
        | CExpr::In(a, b) => {
            visit(a, fp);
            visit(b, fp);
        }
    }
}

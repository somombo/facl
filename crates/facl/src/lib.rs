//! facl: compile and evaluate access-control policies.
//!
//! This is the public Rust API. [`Policy::compile`] parses, checks and lowers
//! a rules file; [`Policy::evaluate`] decides one request. All security logic
//! lives in `facl-core`; this crate is glue.

mod diagnostic;
mod facts;
mod host;
pub mod testcase;

pub use diagnostic::{Diagnostic, Severity};
pub use facl_core::{Decision, DenyReason, Footprint};
pub use facts::{FactsError, RequestFacts, decision_to_json, reason_name};

use facl_core::{Request, canonicalize, decide, footprint, lower, method_bit};

/// A compiled policy, ready to evaluate requests.
#[derive(Clone, Debug)]
pub struct Policy {
    ir: facl_core::Policy,
    footprint: Footprint,
}

/// Parses and checks a rules file and returns every diagnostic, warnings
/// included. The file is acceptable when none is an error.
pub fn check(source: &str) -> Vec<Diagnostic> {
    match facl_syntax::parse(source) {
        Err(e) => vec![Diagnostic::from_parse_error(source, &e)],
        Ok(service) => facl_check::check(&service)
            .iter()
            .map(|issue| Diagnostic::from_issue(source, issue))
            .collect(),
    }
}

impl Policy {
    /// Compiles a rules file. On failure returns the diagnostics, which
    /// include at least one error.
    pub fn compile(source: &str) -> Result<Policy, Vec<Diagnostic>> {
        let mut diagnostics = check(source);
        if diagnostics.iter().any(Diagnostic::is_error) {
            return Err(diagnostics);
        }
        let service = match facl_syntax::parse(source) {
            Ok(service) => service,
            Err(e) => return Err(vec![Diagnostic::from_parse_error(source, &e)]),
        };
        match lower(&service) {
            Ok(ir) => {
                let footprint = footprint(&ir);
                Ok(Policy { ir, footprint })
            }
            Err(e) => {
                diagnostics.push(Diagnostic::from_lower_error(source, &e));
                Err(diagnostics)
            }
        }
    }

    /// The request facts this policy can read.
    pub fn footprint(&self) -> Footprint {
        self.footprint.clone()
    }

    /// Decides a request. A path that cannot be canonicalized is denied with
    /// [`DenyReason::BadRequestPath`]. An error means the facts themselves
    /// are unusable; adapters must treat it as a denial.
    pub fn evaluate(&self, facts: &RequestFacts) -> Result<Decision, FactsError> {
        let path = match canonicalize(facts.path.as_bytes()) {
            Ok(path) => path,
            Err(_) => return Ok(Decision::Deny(DenyReason::BadRequestPath)),
        };
        let request = Request {
            method: method_bit(facts.method.as_bytes()),
            request: facts.request_value(&path)?,
            context: facts.context_value()?,
            path,
        };
        Ok(decide(&self.ir, &request, &host::FaclHost))
    }
}

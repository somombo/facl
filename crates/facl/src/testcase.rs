//! Test cases: the JSON format shared by `facl test` and the conformance
//! suite.

use crate::{Decision, FactsError, Policy, RequestFacts, reason_name};
use serde_json::Value as Json;

/// One test case: a request and the decision it should get.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Case {
    /// An optional label.
    pub name: Option<String>,
    /// The request, as written in the file: `METHOD PATH`.
    pub request: String,
    /// The facts the request is evaluated with.
    pub facts: RequestFacts,
    /// True for `"expect": "allow"`.
    pub expect_allow: bool,
    /// The expected denial reason, when the case states one.
    pub expect_reason: Option<String>,
}

/// What evaluating a case gave.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CaseResult {
    /// True when the decision and, if stated, the reason match.
    pub passed: bool,
    /// The actual decision.
    pub decision: Decision,
}

const KEYS: [&str; 7] = [
    "name", "request", "headers", "auth", "context", "expect", "reason",
];
const REASONS: [&str; 4] = [
    "no_matching_rule",
    "no_allow_for_method",
    "conditions_not_met",
    "bad_request_path",
];

fn bad<T>(message: String) -> Result<T, FactsError> {
    Err(FactsError(message))
}

impl Case {
    /// Reads one case. Unknown keys are rejected, so a typo cannot make a
    /// case pass silently.
    pub fn from_json(v: &Json) -> Result<Case, FactsError> {
        let Json::Object(obj) = v else {
            return bad("a case must be a JSON object".into());
        };
        if let Some(k) = obj.keys().find(|k| !KEYS.contains(&k.as_str())) {
            return bad(format!("unknown key '{k}' in case"));
        }
        let Some(Json::String(request)) = obj.get("request") else {
            return bad("case needs a string 'request' such as \"GET /path\"".into());
        };
        let Some((method, path)) = request.split_once(char::is_whitespace) else {
            return bad(format!("request '{request}' must be 'METHOD PATH'"));
        };
        let mut facts = serde_json::Map::new();
        facts.insert("method".into(), Json::String(method.to_string()));
        facts.insert("path".into(), Json::String(path.trim().to_string()));
        for key in ["headers", "auth", "context"] {
            if let Some(value) = obj.get(key) {
                facts.insert(key.into(), value.clone());
            }
        }
        let expect_allow = match obj.get("expect") {
            Some(Json::String(s)) if s == "allow" => true,
            Some(Json::String(s)) if s == "deny" => false,
            _ => return bad("'expect' must be \"allow\" or \"deny\"".into()),
        };
        let expect_reason = match obj.get("reason") {
            None | Some(Json::Null) => None,
            Some(Json::String(r)) if REASONS.contains(&r.as_str()) && !expect_allow => {
                Some(r.clone())
            }
            Some(_) => return bad("'reason' must be a denial reason, and only on deny".into()),
        };
        let name = match obj.get("name") {
            None => None,
            Some(Json::String(s)) => Some(s.clone()),
            Some(_) => return bad("'name' must be a string".into()),
        };
        Ok(Case {
            name,
            request: format!("{method} {}", path.trim()),
            facts: RequestFacts::from_json(&Json::Object(facts))?,
            expect_allow,
            expect_reason,
        })
    }

    /// Reads a cases file: a JSON array of cases.
    pub fn list_from_json(v: &Json) -> Result<Vec<Case>, FactsError> {
        let Json::Array(items) = v else {
            return bad("a cases file must be a JSON array".into());
        };
        let mut cases = Vec::new();
        for (i, item) in items.iter().enumerate() {
            match Case::from_json(item) {
                Ok(c) => cases.push(c),
                Err(FactsError(m)) => return bad(format!("case {}: {m}", i + 1)),
            }
        }
        Ok(cases)
    }

    /// Evaluates the case against a policy. Unusable facts count as a
    /// failure, never a pass.
    pub fn run(&self, policy: &Policy) -> Result<CaseResult, FactsError> {
        let decision = policy.evaluate(&self.facts)?;
        let passed = match &decision {
            Decision::Allow => self.expect_allow,
            Decision::Deny(r) => {
                !self.expect_allow
                    && self
                        .expect_reason
                        .as_deref()
                        .is_none_or(|want| want == reason_name(r))
            }
        };
        Ok(CaseResult { passed, decision })
    }
}

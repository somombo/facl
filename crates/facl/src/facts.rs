//! Request facts: the data an adapter passes in, and its conversion to the
//! engine's values.

use facl_core::{Decision, DenyReason, Value};
use serde_json::{Map, Value as Json};
use std::fmt;

/// The facts of one request, as an adapter supplies them.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RequestFacts {
    /// The HTTP method, such as `GET`.
    pub method: String,
    /// The percent-encoded path the router dispatches on, without a query.
    pub path: String,
    /// The request headers, in arrival order.
    pub headers: Vec<(String, String)>,
    /// `request.auth`; `None` means null.
    pub auth: Option<serde_json::Value>,
    /// The application's facts; `None` means an empty map.
    pub context: Option<serde_json::Value>,
}

/// The facts could not be used. Adapters must treat this as a denial.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FactsError(pub String);

impl fmt::Display for FactsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid request facts: {}", self.0)
    }
}

impl std::error::Error for FactsError {}

fn bad<T>(message: &str) -> Result<T, FactsError> {
    Err(FactsError(message.to_string()))
}

impl RequestFacts {
    /// Reads facts from a JSON object with the keys `method`, `path`,
    /// `headers` (an object of strings), `auth` and `context` (objects or
    /// null). Unknown keys are rejected.
    pub fn from_json(v: &Json) -> Result<Self, FactsError> {
        let Json::Object(obj) = v else {
            return bad("facts must be a JSON object");
        };
        for key in obj.keys() {
            if !["method", "path", "headers", "auth", "context"].contains(&key.as_str()) {
                return Err(FactsError(format!("unknown key '{key}'")));
            }
        }
        let text = |key: &str| match obj.get(key) {
            Some(Json::String(s)) => Ok(s.clone()),
            _ => Err(FactsError(format!("'{key}' must be a string"))),
        };
        Ok(RequestFacts {
            method: text("method")?,
            path: text("path")?,
            headers: headers_from_json(obj.get("headers"))?,
            auth: object_or_null(obj.get("auth"), "auth")?,
            context: object_or_null(obj.get("context"), "context")?,
        })
    }

    /// Builds the `request` value from the canonical path segments, or fails
    /// when `auth` is unusable.
    pub(crate) fn request_value(&self, segments: &[Vec<u8>]) -> Result<Value, FactsError> {
        let mut path = Vec::new();
        for seg in segments {
            path.push(b'/');
            path.extend_from_slice(seg);
        }
        if path.is_empty() {
            path.push(b'/');
        }
        let auth = match &self.auth {
            None | Some(Json::Null) => Value::Null,
            Some(a @ Json::Object(_)) => json_to_value(a)?,
            Some(_) => return bad("'auth' must be an object or null"),
        };
        Ok(Value::Map(vec![
            (
                b"method".to_vec(),
                Value::Str(self.method.clone().into_bytes()),
            ),
            (b"path".to_vec(), Value::Str(path)),
            (b"headers".to_vec(), self.headers_value()),
            (b"auth".to_vec(), auth),
        ]))
    }

    /// Lower-cases header names and joins duplicates with `", "`.
    fn headers_value(&self) -> Value {
        let mut merged: Vec<(String, String)> = Vec::new();
        for (name, value) in &self.headers {
            let name = name.to_ascii_lowercase();
            match merged.iter_mut().find(|(n, _)| *n == name) {
                Some((_, joined)) => {
                    joined.push_str(", ");
                    joined.push_str(value);
                }
                None => merged.push((name, value.clone())),
            }
        }
        Value::Map(
            merged
                .into_iter()
                .map(|(n, v)| (n.into_bytes(), Value::Str(v.into_bytes())))
                .collect(),
        )
    }

    /// The `context` value, or an error when it is not a map of usable values.
    pub(crate) fn context_value(&self) -> Result<Value, FactsError> {
        match &self.context {
            None | Some(Json::Null) => Ok(Value::Map(Vec::new())),
            Some(c @ Json::Object(_)) => json_to_value(c),
            Some(_) => bad("'context' must be an object or null"),
        }
    }
}

fn headers_from_json(v: Option<&Json>) -> Result<Vec<(String, String)>, FactsError> {
    let obj = match v {
        None | Some(Json::Null) => return Ok(Vec::new()),
        Some(Json::Object(obj)) => obj,
        Some(_) => return bad("'headers' must be an object"),
    };
    let mut out = Vec::new();
    for (name, value) in obj {
        match value {
            Json::String(s) => out.push((name.clone(), s.clone())),
            _ => return Err(FactsError(format!("header '{name}' must be a string"))),
        }
    }
    Ok(out)
}

/// `auth` and `context` are maps or null. Numbers are checked here too, so a
/// bad number fails when the facts are read, not when they are used.
fn object_or_null(v: Option<&Json>, key: &str) -> Result<Option<Json>, FactsError> {
    match v {
        None | Some(Json::Null) => Ok(None),
        Some(obj @ Json::Object(_)) => {
            json_to_value(obj)?;
            Ok(Some(obj.clone()))
        }
        Some(_) => Err(FactsError(format!("'{key}' must be an object or null"))),
    }
}

/// Converts JSON to a value. Numbers that are not `i64` are an error.
fn json_to_value(v: &Json) -> Result<Value, FactsError> {
    Ok(match v {
        Json::Null => Value::Null,
        Json::Bool(b) => Value::Bool(*b),
        Json::Number(n) => match n.as_i64() {
            Some(i) => Value::Int(i),
            None => return Err(FactsError(format!("number {n} is not a 64-bit integer"))),
        },
        Json::String(s) => Value::Str(s.clone().into_bytes()),
        Json::Array(items) => Value::List(
            items
                .iter()
                .map(json_to_value)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Json::Object(map) => Value::Map(
            map.iter()
                .map(|(k, v)| Ok((k.clone().into_bytes(), json_to_value(v)?)))
                .collect::<Result<Vec<_>, FactsError>>()?,
        ),
    })
}

/// The stable snake_case name of a denial reason.
pub fn reason_name(r: &DenyReason) -> &'static str {
    match r {
        DenyReason::NoMatchingRule => "no_matching_rule",
        DenyReason::NoAllowForMethod => "no_allow_for_method",
        DenyReason::ConditionsNotMet => "conditions_not_met",
        DenyReason::BadRequestPath => "bad_request_path",
    }
}

/// Renders a decision as `{"allowed": bool, "reason": null | "..."}`.
pub fn decision_to_json(d: &Decision) -> Json {
    let (allowed, reason) = match d {
        Decision::Allow => (true, Json::Null),
        Decision::Deny(r) => (false, Json::String(reason_name(r).to_string())),
    };
    let mut obj = Map::new();
    obj.insert("allowed".to_string(), Json::Bool(allowed));
    obj.insert("reason".to_string(), reason);
    Json::Object(obj)
}

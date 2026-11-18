//! WebAssembly bindings for facl.
//!
//! The boundary carries JSON strings only: facts go in as JSON and the
//! decision comes out as JSON. The JavaScript package wraps this class.

use facl::{Diagnostic, RequestFacts, decision_to_json};
use wasm_bindgen::prelude::*;

/// A compiled policy.
#[wasm_bindgen]
pub struct Policy {
    inner: facl::Policy,
}

/// Builds a JS `Error` whose `diagnostics` property lists the problems as
/// `[{severity, message, line, col}]`.
fn compile_error(diagnostics: &[Diagnostic]) -> JsValue {
    let list = js_sys::Array::new();
    for d in diagnostics {
        let item = js_sys::Object::new();
        let severity = if d.is_error() { "error" } else { "warning" };
        let fields: [(&str, JsValue); 4] = [
            ("severity", severity.into()),
            ("message", d.message.as_str().into()),
            ("line", d.line.into()),
            ("col", d.col.into()),
        ];
        for (key, value) in fields {
            // Setting a property on a fresh plain object cannot fail.
            let _ = js_sys::Reflect::set(&item, &key.into(), &value);
        }
        list.push(&item);
    }
    let message = diagnostics
        .iter()
        .find(|d| d.is_error())
        .map(|d| format!("{}:{}: {}", d.line, d.col, d.message))
        .unwrap_or_else(|| "policy failed to compile".to_string());
    let error = js_sys::Error::new(&message);
    let _ = js_sys::Reflect::set(&error, &"diagnostics".into(), &list);
    error.into()
}

#[wasm_bindgen]
impl Policy {
    /// Compiles a rules file. Throws an `Error` with a `diagnostics`
    /// property when the source is rejected.
    pub fn compile(source: &str) -> Result<Policy, JsValue> {
        facl::Policy::compile(source)
            .map(|inner| Policy { inner })
            .map_err(|diagnostics| compile_error(&diagnostics))
    }

    /// The request facts the policy can read: `{headers, auth, context}`.
    #[wasm_bindgen(getter)]
    pub fn footprint(&self) -> JsValue {
        let f = self.inner.footprint();
        let out = js_sys::Object::new();
        let fields = [
            ("headers", f.headers),
            ("auth", f.auth),
            ("context", f.context),
        ];
        for (key, value) in fields {
            let _ = js_sys::Reflect::set(&out, &key.into(), &value.into());
        }
        out.into()
    }

    /// Decides one request. `facts_json` has the shape read by
    /// `RequestFacts::from_json`; the result is the decision JSON. Throws an
    /// `Error` when the facts are unusable, which callers must treat as a
    /// denial.
    pub fn evaluate(&self, facts_json: &str) -> Result<String, JsError> {
        let value: serde_json::Value =
            serde_json::from_str(facts_json).map_err(|e| JsError::new(&e.to_string()))?;
        let facts = RequestFacts::from_json(&value).map_err(|e| JsError::new(&e.to_string()))?;
        let decision = self
            .inner
            .evaluate(&facts)
            .map_err(|e| JsError::new(&e.to_string()))?;
        Ok(decision_to_json(&decision).to_string())
    }
}

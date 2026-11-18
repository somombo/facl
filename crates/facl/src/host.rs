//! The host function `request.is()`, which runs outside the verified engine.

use facl_core::{EvalError, Host, Value, map_get};

/// The host that implements `request.is(type)` over the `content-type` header.
pub struct FaclHost;

impl Host for FaclHost {
    fn request_is(&self, request: &Value, media: &[u8]) -> Result<bool, EvalError> {
        let Ok(arg) = std::str::from_utf8(media) else {
            return Err(EvalError::BadArgument);
        };
        let arg = arg.to_ascii_lowercase();
        let Some(actual) = content_type(request) else {
            // No Content-Type: false, but still reject an unknown argument.
            return matches_media("", &arg).map(|_| false);
        };
        matches_media(&actual, &arg)
    }
}

/// The lower-cased media type of the request, without parameters.
fn content_type(request: &Value) -> Option<String> {
    let Value::Map(fields) = request else {
        return None;
    };
    let Some(Value::Map(headers)) = map_get(fields, b"headers") else {
        return None;
    };
    let Some(Value::Str(raw)) = map_get(headers, b"content-type") else {
        return None;
    };
    let text = String::from_utf8_lossy(raw);
    let media = text.split(';').next().unwrap_or("");
    Some(media.trim().to_ascii_lowercase())
}

/// Matches a media type against a `request.is` argument.
fn matches_media(actual: &str, arg: &str) -> Result<bool, EvalError> {
    let has_suffix = |suffix: &str| actual.ends_with(suffix);
    Ok(match arg {
        "json" => actual == "application/json" || has_suffix("+json"),
        "html" => actual == "text/html",
        "text" => actual.starts_with("text/"),
        "xml" => actual == "application/xml" || actual == "text/xml" || has_suffix("+xml"),
        "urlencoded" => actual == "application/x-www-form-urlencoded",
        "multipart" => actual.starts_with("multipart/"),
        _ => match arg.split_once('/') {
            Some((kind, "*")) if !kind.is_empty() => actual.starts_with(&format!("{kind}/")),
            Some((kind, sub)) if !kind.is_empty() && !sub.is_empty() => actual == arg,
            _ => return Err(EvalError::BadArgument),
        },
    })
}

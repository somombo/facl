//! Tests of the public facade: compile, evaluate, facts and diagnostics.

use facl::testcase::Case;
use facl::{Decision, DenyReason, FactsError, Policy, RequestFacts, Severity, decision_to_json};
use serde_json::json;

const RULES: &str = r#"
service http {
  match /users/{id} {
    allow read: if request.auth != null && request.auth.uid == id;
  }
  match /hook { allow post: if context.ok == true; }
  match /json { allow post: if request.is("json"); }
  match /h { allow get: if request.headers["x-a"] == "1, 2"; }
  match /p/{rest=**} { allow get: if request.path == "/p/a/b"; }
}
"#;

fn facts(method: &str, path: &str) -> RequestFacts {
    RequestFacts {
        method: method.into(),
        path: path.into(),
        headers: vec![],
        auth: None,
        context: None,
    }
}

fn policy() -> Policy {
    Policy::compile(RULES).expect("compiles")
}

#[test]
fn evaluates_requests() {
    let p = policy();
    let mut f = facts("GET", "/users/a");
    assert_eq!(
        p.evaluate(&f),
        Ok(Decision::Deny(DenyReason::ConditionsNotMet))
    );
    f.auth = Some(json!({"uid": "a"}));
    assert_eq!(p.evaluate(&f), Ok(Decision::Allow));
    assert_eq!(
        p.evaluate(&facts("GET", "/nope")),
        Ok(Decision::Deny(DenyReason::NoMatchingRule))
    );
    assert_eq!(
        p.evaluate(&facts("GET", "/users/%2e%2e")),
        Ok(Decision::Deny(DenyReason::BadRequestPath))
    );
}

#[test]
fn headers_are_lowercased_and_duplicates_joined() {
    let mut f = facts("GET", "/h");
    f.headers = vec![("X-A".into(), "1".into()), ("x-a".into(), "2".into())];
    assert_eq!(policy().evaluate(&f), Ok(Decision::Allow));
}

#[test]
fn request_path_is_canonical() {
    assert_eq!(
        policy().evaluate(&facts("GET", "/p/%61/b")),
        Ok(Decision::Allow)
    );
}

#[test]
fn empty_segments_are_a_bad_request_path() {
    for path in ["//p/a/b", "/p/a/b/", "/p//a/b"] {
        assert_eq!(
            policy().evaluate(&facts("GET", path)),
            Ok(Decision::Deny(DenyReason::BadRequestPath)),
            "{path}"
        );
    }
}

#[test]
fn request_is_uses_the_content_type() {
    let p = policy();
    let mut f = facts("POST", "/json");
    assert_eq!(
        p.evaluate(&f),
        Ok(Decision::Deny(DenyReason::ConditionsNotMet))
    );
    f.headers = vec![(
        "Content-Type".into(),
        " Application/JSON ; charset=utf-8".into(),
    )];
    assert_eq!(p.evaluate(&f), Ok(Decision::Allow));
    f.headers = vec![("Content-Type".into(), "application/ld+json".into())];
    assert_eq!(p.evaluate(&f), Ok(Decision::Allow));
    f.headers = vec![("Content-Type".into(), "text/html".into())];
    assert_eq!(
        p.evaluate(&f),
        Ok(Decision::Deny(DenyReason::ConditionsNotMet))
    );
}

#[test]
fn request_is_media_names() {
    let check = |arg: &str, content_type: &str| {
        let src =
            format!("service http {{ match /x {{ allow post: if request.is(\"{arg}\"); }} }}");
        let p = Policy::compile(&src).expect("compiles");
        let mut f = facts("POST", "/x");
        f.headers = vec![("content-type".into(), content_type.into())];
        p.evaluate(&f) == Ok(Decision::Allow)
    };
    assert!(check("html", "text/html; charset=x"));
    assert!(!check("html", "text/plain"));
    assert!(check("text", "text/plain"));
    assert!(!check("text", "application/json"));
    assert!(check("xml", "application/xml"));
    assert!(check("xml", "text/xml"));
    assert!(check("xml", "application/atom+xml"));
    assert!(check("urlencoded", "application/x-www-form-urlencoded"));
    assert!(check("multipart", "multipart/form-data; boundary=x"));
    assert!(check("image/png", "image/png"));
    assert!(!check("image/png", "image/jpeg"));
    assert!(check("image/*", "image/jpeg"));
    assert!(!check("image/*", "imagery/x"));
    assert!(!check("nonsense", "text/plain"));
}

#[test]
fn bad_facts_are_errors_not_decisions() {
    let p = policy();
    let mut f = facts("POST", "/hook");
    f.context = Some(json!({"ok": 1.5}));
    assert!(p.evaluate(&f).is_err());
    f.context = Some(json!([1]));
    assert!(p.evaluate(&f).is_err());
    f.context = None;
    f.auth = Some(json!("alice"));
    assert!(p.evaluate(&f).is_err());
    f.auth = Some(json!({"n": 18446744073709551615u64}));
    assert!(p.evaluate(&f).is_err());
}

#[test]
fn facts_from_json() {
    let v = json!({"method": "GET", "path": "/a", "headers": {"A": "b"}, "auth": null, "context": {"k": 1}});
    let f = RequestFacts::from_json(&v).expect("valid");
    assert_eq!(f.method, "GET");
    assert_eq!(f.headers, vec![("A".to_string(), "b".to_string())]);
    assert_eq!(f.auth, None);
    for bad in [
        json!([]),
        json!({"path": "/a"}),
        json!({"method": "GET"}),
        json!({"method": "GET", "path": "/a", "extra": 1}),
        json!({"method": "GET", "path": "/a", "headers": {"A": 1}}),
        json!({"method": "GET", "path": "/a", "auth": 3}),
        json!({"method": "GET", "path": "/a", "context": {"x": 1.5}}),
    ] {
        assert!(
            matches!(RequestFacts::from_json(&bad), Err(FactsError(_))),
            "{bad}"
        );
    }
}

#[test]
fn decisions_as_json() {
    assert_eq!(
        decision_to_json(&Decision::Allow),
        json!({"allowed": true, "reason": null})
    );
    assert_eq!(
        decision_to_json(&Decision::Deny(DenyReason::NoAllowForMethod)),
        json!({"allowed": false, "reason": "no_allow_for_method"})
    );
    assert_eq!(
        decision_to_json(&Decision::Deny(DenyReason::BadRequestPath))["reason"],
        "bad_request_path"
    );
}

#[test]
fn footprint_is_exposed() {
    let fp = policy().footprint();
    assert!(fp.auth && fp.context && fp.headers);
    let small =
        Policy::compile("service http { match /a { allow read: if request.method == 'GET'; } }")
            .expect("compiles");
    let fp = small.footprint();
    assert!(!fp.auth && !fp.context && !fp.headers);
}

#[test]
fn diagnostics_have_positions_and_display() {
    let src = "service http {\n  match /a {\n    allow read: if nope == 1;\n  }\n}\n";
    let d = Policy::compile(src).expect_err("fails");
    assert_eq!(d.len(), 1);
    assert_eq!((d[0].line, d[0].col), (3, 20));
    assert_eq!(d[0].to_string(), "3:20: error: unknown name 'nope'");
    let d =
        Policy::compile("service http {\n  match /a { allow read: if ; }\n}").expect_err("fails");
    assert_eq!(d[0].severity, Severity::Error);
    assert_eq!((d[0].line, d[0].col), (2, 29));
}

#[test]
fn warnings_do_not_block_compilation() {
    let src = "service http { match /a { } match /b { allow read; } }";
    assert!(Policy::compile(src).is_ok());
    let found = facl::check(src);
    assert_eq!(found.len(), 1);
    assert!(!found[0].is_error());
    assert_eq!(
        found[0].to_string(),
        "1:16: warning: match has no allow statements and grants nothing"
    );
}

#[test]
fn cases_reject_typos_and_bad_shapes() {
    for bad in [
        json!({"request": "GET /a", "expects": "allow"}),
        json!({"request": "GET /a"}),
        json!({"request": "GET", "expect": "allow"}),
        json!({"request": "GET /a", "expect": "maybe"}),
        json!({"request": "GET /a", "expect": "allow", "reason": "conditions_not_met"}),
        json!({"request": "GET /a", "expect": "deny", "reason": "because"}),
        json!("GET /a"),
    ] {
        assert!(Case::from_json(&bad).is_err(), "{bad}");
    }
    assert!(Case::list_from_json(&json!({})).is_err());
}

#[test]
fn cases_check_decision_and_reason() {
    let p = policy();
    let run = |v: serde_json::Value| {
        Case::from_json(&v)
            .expect("case")
            .run(&p)
            .expect("runs")
            .passed
    };
    assert!(run(json!({"request": "GET /nope", "expect": "deny"})));
    assert!(run(
        json!({"request": "GET /nope", "expect": "deny", "reason": "no_matching_rule"})
    ));
    assert!(!run(
        json!({"request": "GET /nope", "expect": "deny", "reason": "conditions_not_met"})
    ));
    assert!(!run(json!({"request": "GET /nope", "expect": "allow"})));
    assert!(!run(json!({"request": "GET /p/a/b", "expect": "deny"})));
}

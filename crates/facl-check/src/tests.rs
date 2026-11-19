use super::*;

fn issues(src: &str) -> Vec<Issue> {
    let service = facl_syntax::parse(src).unwrap_or_else(|e| panic!("parse failed: {e:?}"));
    check(&service)
}

fn errors(src: &str) -> Vec<String> {
    issues(src)
        .into_iter()
        .filter(|i| i.severity == Severity::Error)
        .map(|i| i.message)
        .collect()
}

fn with_cond(cond: &str) -> String {
    format!("service http {{ match /a/{{id}} {{ allow read: if {cond}; }} }}")
}

fn cond_errors(cond: &str) -> Vec<String> {
    errors(&with_cond(cond))
}

#[test]
fn a_good_policy_has_no_issues() {
    let src = "service http { match /users/{u} { allow read: if request.auth != null && request.auth.uid == u;
        match /files/{p=**} { allow write: if size(p) > 0 && context.ok == true; } } }";
    assert_eq!(issues(src), vec![]);
    assert!(!has_errors(&issues(src)));
}

#[test]
fn names_in_scope() {
    assert!(cond_errors("request.auth == null && context.x == id").is_empty());
    assert_eq!(cond_errors("nope == 1"), vec!["unknown name 'nope'"]);
    assert_eq!(cond_errors("id == other"), vec!["unknown name 'other'"]);
}

#[test]
fn captures_are_scoped_to_their_match_and_children() {
    let ok = "service http { match /a/{x} { allow read: if x == 'a'; match /b/{y} { allow read: if x == y; } } }";
    assert!(errors(ok).is_empty());
    // A sibling does not see the capture.
    let sibling =
        "service http { match /a/{x} { allow read; } match /b { allow read: if x == 'a'; } }";
    assert_eq!(errors(sibling), vec!["unknown name 'x'"]);
    // A parent does not see its child's capture.
    let parent = "service http { match /a { allow read: if y == 1; match /{y} { allow read; } } }";
    assert_eq!(errors(parent), vec!["unknown name 'y'"]);
}

#[test]
fn every_error_is_reported_with_a_span() {
    let src = "service http { match /a { allow read: if p == 1 || q == 2; } }";
    let found = issues(src);
    assert_eq!(found.len(), 2);
    let texts: Vec<&str> = found
        .iter()
        .map(|i| &src[i.span.start as usize..i.span.end as usize])
        .collect();
    assert_eq!(texts, vec!["p", "q"]);
}

#[test]
fn reserved_and_duplicate_capture_names() {
    let reserved = "service http { match /{request} { allow read; } }";
    assert_eq!(
        errors(reserved),
        vec!["'request' is reserved and cannot be a capture"]
    );
    let reserved = "service http { match /{context} { allow read; } }";
    assert_eq!(
        errors(reserved),
        vec!["'context' is reserved and cannot be a capture"]
    );
    let dup = "service http { match /{a}/{a} { allow read; } }";
    assert_eq!(errors(dup), vec!["capture 'a' is already bound"]);
    let nested = "service http { match /{a} { match /{a} { allow read; } } }";
    assert_eq!(errors(nested), vec!["capture 'a' is already bound"]);
    let dup_rest = "service http { match /{a}/{a=**} { allow read; } }";
    assert_eq!(errors(dup_rest), vec!["capture 'a' is already bound"]);
    // The same name in separate chains is fine.
    let siblings = "service http { match /{a} { allow read; } match /{a} { allow read; } }";
    assert!(errors(siblings).is_empty());
}

#[test]
fn rest_must_be_last_and_childless() {
    let not_last = "service http { match /{p=**}/x { allow read; } }";
    assert_eq!(
        errors(not_last),
        vec!["'{name=**}' must be the last segment"]
    );
    let children = "service http { match /{p=**} { allow read; match /x { allow read; } } }";
    assert_eq!(
        errors(children),
        vec!["a match ending in '{name=**}' cannot contain nested matches"]
    );
    assert!(errors("service http { match /a/{p=**} { allow read; } }").is_empty());
}

#[test]
fn function_names_and_arity() {
    assert_eq!(cond_errors("nope(1)"), vec!["unknown function 'nope'"]);
    assert_eq!(
        cond_errors("size() == 1"),
        vec!["'size' takes exactly one argument"]
    );
    assert_eq!(
        cond_errors("size(id, id) == 1"),
        vec!["'size' takes exactly one argument"]
    );
    assert_eq!(
        cond_errors("has(id, id)"),
        vec!["'has' takes exactly one argument"]
    );
    assert!(cond_errors("size(id) == 1 && has(request.auth)").is_empty());
}

#[test]
fn has_needs_a_selection() {
    let msg = "'has' needs a field selection such as has(a.b)";
    assert_eq!(cond_errors("has(id)"), vec![msg]);
    assert_eq!(cond_errors("has(id[0])"), vec![msg]);
    assert_eq!(cond_errors("has(1)"), vec![msg]);
    assert!(cond_errors("has(request.auth.uid)").is_empty());
}

#[test]
fn methods() {
    assert!(cond_errors("id.size() == 1 && id.startsWith('a') && id.endsWith('b')").is_empty());
    assert_eq!(cond_errors("id.nope()"), vec!["unknown method 'nope'"]);
    assert_eq!(
        cond_errors("id.size(1) == 1"),
        vec!["'size' takes 0 argument(s)"]
    );
    assert_eq!(
        cond_errors("id.startsWith()"),
        vec!["'startsWith' takes 1 argument(s)"]
    );
    assert_eq!(
        cond_errors("id.endsWith('a', 'b')"),
        vec!["'endsWith' takes 1 argument(s)"]
    );
}

#[test]
fn request_is_only_on_request() {
    assert!(cond_errors("request.is('json')").is_empty());
    let msg = "'is' can only be called on 'request'";
    assert_eq!(cond_errors("id.is('json')"), vec![msg]);
    assert_eq!(cond_errors("context.is('json')"), vec![msg]);
    assert_eq!(cond_errors("request.auth.is('json')"), vec![msg]);
    assert_eq!(
        cond_errors("request.is()"),
        vec!["'is' takes 1 argument(s)"]
    );
}

#[test]
fn errors_inside_arguments_are_found() {
    assert_eq!(cond_errors("size(nope) == 1"), vec!["unknown name 'nope'"]);
    assert_eq!(
        cond_errors("id.startsWith(nope)"),
        vec!["unknown name 'nope'"]
    );
    assert_eq!(cond_errors("[nope, nada] == id").len(), 2);
}

#[test]
fn depth_limit() {
    use facl_core::{Expr, ExprKind, Item, Span};
    let sp = Span { start: 0, end: 0 };
    let mut e = Expr {
        kind: ExprKind::Bool(true),
        span: sp,
    };
    for _ in 0..MAX_DEPTH {
        e = Expr {
            kind: ExprKind::Not(Box::new(e)),
            span: sp,
        };
    }
    let allow = facl_core::Allow {
        methods: 1,
        cond: Some(e),
        span: sp,
    };
    let m = facl_core::Match {
        pattern: vec![],
        body: vec![Item::Allow(allow)],
        span: sp,
    };
    let s = facl_core::Service {
        name: b"http".to_vec(),
        matches: vec![m],
        span: sp,
    };
    let found = check(&s);
    assert_eq!(found.len(), 1);
    assert!(found[0].message.contains("nested more than 64"));
}

#[test]
fn warns_about_matches_that_grant_nothing() {
    let found = issues("service http { match /a { } match /b { match /c { allow read; } } }");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].severity, Severity::Warning);
    assert!(found[0].message.contains("grants nothing"));
    assert!(!has_errors(&found));
}

#[test]
fn checker_and_lowering_agree_on_has_depth() {
    let src = |nots: usize| {
        format!(
            "service http {{ match /a {{ allow read: if {}has(context.x); }} }}",
            "!".repeat(nots)
        )
    };
    for (nots, ok) in [(61, true), (62, false)] {
        let service = facl_syntax::parse(&src(nots)).expect("parses");
        assert_eq!(errors(&src(nots)).is_empty(), ok, "checker, {nots}");
        assert_eq!(facl_core::lower(&service).is_ok(), ok, "lowering, {nots}");
    }
}

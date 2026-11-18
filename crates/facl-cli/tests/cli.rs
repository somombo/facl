//! Smoke tests that run the real `facl` binary.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn conformance(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../conformance")
        .join(name)
}

fn facl(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_facl"))
        .args(args)
        .output()
        .expect("runs facl")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn temp_file(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("facl-cli-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let path = dir.join(name);
    std::fs::write(&path, contents).expect("write");
    path
}

#[test]
fn check_accepts_a_good_file() {
    let rules = conformance("design-example.rules");
    let out = facl(&["check", rules.to_str().expect("utf8")]);
    assert_eq!(out.status.code(), Some(0));
    assert!(text(&out.stdout).contains(": ok"));
}

#[test]
fn check_reports_errors_with_positions() {
    let path = temp_file(
        "bad.rules",
        "service http {\n  match /a {\n    allow read: if nope;\n  }\n}\n",
    );
    let out = facl(&["check", path.to_str().expect("utf8")]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).contains("bad.rules:3:20: error: unknown name 'nope'"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn check_prints_warnings_but_succeeds() {
    let path = temp_file("warn.rules", "service http { match /a { } }");
    let out = facl(&["check", path.to_str().expect("utf8")]);
    assert_eq!(out.status.code(), Some(0));
    assert!(text(&out.stderr).contains("warning"));
}

#[test]
fn check_reports_syntax_errors() {
    let path = temp_file("syntax.rules", "service http {");
    let out = facl(&["check", path.to_str().expect("utf8")]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).contains("1:15: error: expected"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn missing_file_is_an_error() {
    let out = facl(&["check", "/no/such/file.rules"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stderr).contains("cannot read"));
}

#[test]
fn eval_prints_a_decision() {
    let rules = conformance("design-example.rules");
    let rules = rules.to_str().expect("utf8");
    let out = facl(&[
        "eval",
        rules,
        "GET",
        "/users/alice",
        "--auth",
        r#"{"uid":"bob"}"#,
    ]);
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(
        text(&out.stdout).trim(),
        r#"{"allowed":true,"reason":null}"#
    );
    let out = facl(&["eval", rules, "GET", "/users/alice"]);
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(
        text(&out.stdout).trim(),
        r#"{"allowed":false,"reason":"conditions_not_met"}"#
    );
    let out = facl(&[
        "eval",
        rules,
        "POST",
        "/webhooks/stripe",
        "--context",
        r#"{"stripeVerified":true}"#,
    ]);
    assert_eq!(
        text(&out.stdout).trim(),
        r#"{"allowed":true,"reason":null}"#
    );
}

#[test]
fn eval_takes_headers() {
    let path = temp_file(
        "hdr.rules",
        r#"service http { match /a { allow get: if request.headers["x-k"] == "v"; } }"#,
    );
    let rules = path.to_str().expect("utf8");
    let out = facl(&["eval", rules, "GET", "/a", "--header", "X-K=v"]);
    assert!(
        text(&out.stdout).contains(r#""allowed":true"#),
        "{}",
        text(&out.stdout)
    );
}

#[test]
fn eval_usage_errors() {
    let rules = conformance("design-example.rules");
    let rules = rules.to_str().expect("utf8");
    assert_eq!(facl(&["eval", rules, "GET"]).status.code(), Some(2));
    assert_eq!(
        facl(&["eval", rules, "GET", "/a", "--auth"]).status.code(),
        Some(2)
    );
    assert_eq!(
        facl(&["eval", rules, "GET", "/a", "--auth", "{nope"])
            .status
            .code(),
        Some(2)
    );
    assert_eq!(
        facl(&["eval", rules, "GET", "/a", "--bogus", "x"])
            .status
            .code(),
        Some(2)
    );
    assert_eq!(
        facl(&["eval", rules, "GET", "/a", "--header", "novalue"])
            .status
            .code(),
        Some(2)
    );
}

#[test]
fn eval_unusable_facts_fail() {
    let rules = conformance("design-example.rules");
    let out = facl(&[
        "eval",
        rules.to_str().expect("utf8"),
        "GET",
        "/a",
        "--auth",
        r#"{"n":1.5}"#,
    ]);
    assert_eq!(out.status.code(), Some(1));
}

#[test]
fn test_command_passes_on_the_design_example() {
    let rules = conformance("design-example.rules");
    let cases = conformance("design-example.cases.json");
    let out = facl(&[
        "test",
        rules.to_str().expect("utf8"),
        cases.to_str().expect("utf8"),
    ]);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("\u{2713} GET /users/alice"), "{stdout}");
    assert!(stdout.contains("uid=bob"));
    assert!(stdout.contains("conditions not met"));
    assert!(stdout.contains("no matching rule"));
    assert!(stdout.contains("14 passed, 0 failed"), "{stdout}");
}

#[test]
fn test_command_fails_on_a_wrong_expectation() {
    let rules = conformance("design-example.rules");
    let cases = temp_file(
        "wrong.cases.json",
        r#"[{"request": "GET /admin", "expect": "allow", "name": "oops"},
            {"request": "GET /admin", "expect": "deny", "reason": "no_matching_rule"}]"#,
    );
    let out = facl(&[
        "test",
        rules.to_str().expect("utf8"),
        cases.to_str().expect("utf8"),
    ]);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{stdout}");
    assert!(stdout.contains("\u{2717} GET /admin"), "{stdout}");
    assert!(stdout.contains("(expected allow) [oops]"), "{stdout}");
    assert!(stdout.contains("1 passed, 1 failed"), "{stdout}");
}

#[test]
fn test_command_rejects_malformed_cases() {
    let rules = conformance("design-example.rules");
    let cases = temp_file(
        "typo.cases.json",
        r#"[{"request": "GET /a", "expects": "deny"}]"#,
    );
    let out = facl(&[
        "test",
        rules.to_str().expect("utf8"),
        cases.to_str().expect("utf8"),
    ]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).contains("unknown key 'expects'"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn usage_and_version() {
    assert_eq!(facl(&[]).status.code(), Some(2));
    assert_eq!(facl(&["bogus"]).status.code(), Some(2));
    assert_eq!(facl(&["check"]).status.code(), Some(2));
    assert_eq!(facl(&["test", "a"]).status.code(), Some(2));
    let help = facl(&["--help"]);
    assert_eq!(help.status.code(), Some(0));
    assert!(text(&help.stdout).contains("facl check FILE"));
    let version = facl(&["--version"]);
    assert_eq!(text(&version.stdout).trim(), "facl 0.3.0");
}

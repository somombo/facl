//! Runs every `conformance/*.rules` and `*.cases.json` pair.

use facl::Policy;
use facl::testcase::Case;
use std::fs;
use std::path::{Path, PathBuf};

fn conformance_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../conformance")
}

/// The sorted base names of every `.rules` file in the corpus.
fn rule_names() -> Vec<String> {
    let mut names = Vec::new();
    for entry in fs::read_dir(conformance_dir()).expect("conformance dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "rules") {
            let stem = path.file_stem().expect("file stem").to_string_lossy();
            names.push(stem.into_owned());
        }
    }
    names.sort();
    names
}

fn run_pair(name: &str) -> (usize, Vec<String>) {
    let dir = conformance_dir();
    let source = fs::read_to_string(dir.join(format!("{name}.rules"))).expect("rules file");
    let cases_text = fs::read_to_string(dir.join(format!("{name}.cases.json")))
        .unwrap_or_else(|_| panic!("{name}.rules has no {name}.cases.json"));
    let policy = Policy::compile(&source).unwrap_or_else(|d| {
        let lines: Vec<String> = d.iter().map(ToString::to_string).collect();
        panic!("{name}.rules does not compile: {}", lines.join("; "))
    });
    let json = serde_json::from_str(&cases_text).expect("cases file is valid JSON");
    let cases = Case::list_from_json(&json)
        .unwrap_or_else(|e| panic!("{name}.cases.json is malformed: {e}"));
    let mut failures = Vec::new();
    for case in &cases {
        let label = case.name.as_deref().unwrap_or("");
        match case.run(&policy) {
            Ok(result) if result.passed => {}
            Ok(result) => failures.push(format!(
                "{name}: {} [{label}]: got {:?}, expected allow={} reason={:?}",
                case.request, result.decision, case.expect_allow, case.expect_reason
            )),
            Err(e) => failures.push(format!("{name}: {} [{label}]: {e}", case.request)),
        }
    }
    (cases.len(), failures)
}

#[test]
fn all_conformance_cases_pass() {
    let names = rule_names();
    for required in [
        "design-example",
        "errors",
        "paths",
        "methods",
        "functions",
        "context",
    ] {
        assert!(
            names.iter().any(|n| n == required),
            "missing group {required}"
        );
    }
    let mut total = 0;
    let mut failures = Vec::new();
    for name in &names {
        let (count, mut f) = run_pair(name);
        total += count;
        failures.append(&mut f);
    }
    assert!(total > 100, "suspiciously few cases: {total}");
    assert!(
        failures.is_empty(),
        "{} failing:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn every_cases_file_has_a_rules_file() {
    let names = rule_names();
    for entry in fs::read_dir(conformance_dir()).expect("conformance dir") {
        let file = entry
            .expect("dir entry")
            .file_name()
            .to_string_lossy()
            .into_owned();
        if let Some(stem) = file.strip_suffix(".cases.json") {
            assert!(names.iter().any(|n| n == stem), "{file} has no .rules file");
        }
    }
}

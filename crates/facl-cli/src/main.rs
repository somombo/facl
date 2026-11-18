//! The `facl` command-line tool: check, evaluate and test policies.
//!
//! Exit codes: 0 for success, 1 for errors or failing cases, 2 for usage
//! errors.

use facl::testcase::Case;
use facl::{Decision, Diagnostic, Policy, RequestFacts, decision_to_json, reason_name};
use serde_json::Value as Json;
use std::process::ExitCode;

const USAGE: &str = "\
facl: check and test access-control policies

USAGE:
    facl check FILE
    facl eval FILE METHOD PATH [--auth JSON] [--header NAME=VALUE]... [--context JSON]
    facl test FILE CASES.json
    facl --help | --version
";

const OK: u8 = 0;
const FAILURE: u8 = 1;
const USAGE_ERROR: u8 = 2;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    ExitCode::from(run(&args))
}

fn run(args: &[String]) -> u8 {
    let Some((command, rest)) = args.split_first() else {
        eprint!("{USAGE}");
        return USAGE_ERROR;
    };
    match command.as_str() {
        "-h" | "--help" | "help" => {
            print!("{USAGE}");
            OK
        }
        "-V" | "--version" => {
            println!("facl {}", env!("CARGO_PKG_VERSION"));
            OK
        }
        "check" => cmd_check(rest),
        "eval" => cmd_eval(rest),
        "test" => cmd_test(rest),
        other => usage_error(&format!("unknown command '{other}'")),
    }
}

fn usage_error(message: &str) -> u8 {
    eprintln!("facl: {message}");
    eprint!("{USAGE}");
    USAGE_ERROR
}

fn read_file(path: &str) -> Result<String, u8> {
    std::fs::read_to_string(path).map_err(|e| {
        eprintln!("facl: cannot read {path}: {e}");
        FAILURE
    })
}

fn print_diagnostics(file: &str, diagnostics: &[Diagnostic]) {
    for d in diagnostics {
        eprintln!("{file}:{d}");
    }
}

fn compile_file(file: &str) -> Result<Policy, u8> {
    let source = read_file(file)?;
    Policy::compile(&source).map_err(|diagnostics| {
        print_diagnostics(file, &diagnostics);
        FAILURE
    })
}

fn cmd_check(args: &[String]) -> u8 {
    let [file] = args else {
        return usage_error("check takes exactly one FILE");
    };
    let source = match read_file(file) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let diagnostics = facl::check(&source);
    print_diagnostics(file, &diagnostics);
    if diagnostics.iter().any(Diagnostic::is_error) {
        FAILURE
    } else {
        println!("{file}: ok");
        OK
    }
}

fn cmd_eval(args: &[String]) -> u8 {
    let [file, method, path, options @ ..] = args else {
        return usage_error("eval needs FILE METHOD PATH");
    };
    let facts = match parse_eval_options(method, path, options) {
        Ok(f) => f,
        Err(message) => return usage_error(&message),
    };
    let policy = match compile_file(file) {
        Ok(p) => p,
        Err(code) => return code,
    };
    match policy.evaluate(&facts) {
        Ok(decision) => {
            println!("{}", decision_to_json(&decision));
            OK
        }
        Err(e) => {
            eprintln!("facl: {e}");
            FAILURE
        }
    }
}

fn parse_eval_options(
    method: &str,
    path: &str,
    options: &[String],
) -> Result<RequestFacts, String> {
    let mut facts = RequestFacts {
        method: method.to_string(),
        path: path.to_string(),
        headers: Vec::new(),
        auth: None,
        context: None,
    };
    let mut i = 0;
    while i < options.len() {
        let flag = options[i].as_str();
        let Some(value) = options.get(i + 1) else {
            return Err(format!("{flag} needs a value"));
        };
        match flag {
            "--auth" => facts.auth = Some(parse_json(flag, value)?),
            "--context" => facts.context = Some(parse_json(flag, value)?),
            "--header" => match value.split_once('=') {
                Some((name, v)) if !name.is_empty() => {
                    facts.headers.push((name.to_string(), v.to_string()));
                }
                _ => return Err("--header needs NAME=VALUE".to_string()),
            },
            _ => return Err(format!("unknown option '{flag}'")),
        }
        i += 2;
    }
    Ok(facts)
}

fn parse_json(flag: &str, text: &str) -> Result<Json, String> {
    serde_json::from_str(text).map_err(|e| format!("{flag} is not valid JSON: {e}"))
}

fn cmd_test(args: &[String]) -> u8 {
    let [file, cases_file] = args else {
        return usage_error("test takes FILE CASES.json");
    };
    let policy = match compile_file(file) {
        Ok(p) => p,
        Err(code) => return code,
    };
    let cases = match load_cases(cases_file) {
        Ok(c) => c,
        Err(message) => {
            eprintln!("facl: {cases_file}: {message}");
            return FAILURE;
        }
    };
    let width = cases
        .iter()
        .map(|c| c.request.chars().count())
        .max()
        .unwrap_or(0);
    let caller_width = cases
        .iter()
        .map(|c| caller(c).chars().count())
        .max()
        .unwrap_or(0);
    let mut failed = 0;
    for case in &cases {
        let line = report_case(&policy, case, width, caller_width);
        if !line.0 {
            failed += 1;
        }
        println!("{}", line.1);
    }
    let passed = cases.len() - failed;
    println!("{passed} passed, {failed} failed");
    if failed == 0 { OK } else { FAILURE }
}

fn load_cases(path: &str) -> Result<Vec<Case>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let json: Json = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    Case::list_from_json(&json).map_err(|e| e.0)
}

/// Who the case's caller is, for display.
fn caller(case: &Case) -> String {
    match &case.facts.auth {
        None => "anonymous".to_string(),
        Some(auth) => match auth.get("uid").and_then(Json::as_str) {
            Some(uid) => format!("uid={uid}"),
            None => "authenticated".to_string(),
        },
    }
}

/// Runs a case and formats its line; the flag says whether it passed.
fn report_case(policy: &Policy, case: &Case, width: usize, caller_width: usize) -> (bool, String) {
    let (passed, decision, reason) = match case.run(policy) {
        Ok(result) => {
            let (word, reason) = match &result.decision {
                Decision::Allow => ("allow", String::new()),
                Decision::Deny(r) => ("deny", reason_name(r).replace('_', " ")),
            };
            (result.passed, word.to_string(), reason)
        }
        Err(e) => (false, "error".to_string(), e.to_string()),
    };
    let mark = if passed { "\u{2713}" } else { "\u{2717}" };
    let mut line = format!(
        "  {mark} {:<width$}   {:<caller_width$}   {decision:<5}   {reason}",
        case.request,
        caller(case),
    );
    if !passed {
        line.push_str(&format!("   (expected {})", expectation(case)));
        if let Some(name) = &case.name {
            line.push_str(&format!(" [{name}]"));
        }
    }
    (passed, line.trim_end().to_string())
}

fn expectation(case: &Case) -> String {
    match (&case.expect_allow, &case.expect_reason) {
        (true, _) => "allow".to_string(),
        (false, None) => "deny".to_string(),
        (false, Some(r)) => format!("deny, {}", r.replace('_', " ")),
    }
}

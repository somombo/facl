use crate::Result;
use crate::shrink::shrink;
use crate::syntax::Parsed;
use crate::wire::Case;
use facl::{Decision, DenyReason, Diagnostic, Policy, reason_name};
use facl_core::LowerErrorKind;
use serde_json::{Value as Json, json};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

#[derive(Debug)]
pub(crate) enum Reply {
    Verdicts(Vec<Decision>),
    Rejected { kind: String },
}

impl Reply {
    fn rejection(&self) -> Option<&str> {
        match self {
            Self::Verdicts(_) => None,
            Self::Rejected { kind } => Some(kind),
        }
    }

    fn json(&self) -> Json {
        match self {
            Self::Verdicts(verdicts) => {
                let verdicts: Vec<_> = verdicts
                    .iter()
                    .map(|d| match d {
                        Decision::Allow => json!("allow"),
                        Decision::Deny(reason) => json!({"deny": reason_name(reason)}),
                    })
                    .collect();
                json!({"compile": "ok", "verdicts": verdicts})
            }
            Self::Rejected { kind } => json!({"compile": {"error": kind}}),
        }
    }
}

pub(crate) struct Oracle {
    process: Child,
    input: Option<BufWriter<ChildStdin>>,
    output: BufReader<ChildStdout>,
    line: String,
}

impl Oracle {
    pub(crate) fn start(path: &Path) -> Result<Self> {
        let mut process = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|err| format!("could not start oracle {}: {err}", path.display()))?;
        let input = BufWriter::new(process.stdin.take().unwrap());
        let output = BufReader::new(process.stdout.take().unwrap());
        Ok(Self {
            process,
            input: Some(input),
            output,
            line: String::new(),
        })
    }

    pub(crate) fn evaluate(&mut self, case: &Case) -> Result<Reply> {
        let input = self.input.as_mut().unwrap();
        serde_json::to_writer(&mut *input, &case.json())?;
        input.write_all(b"\n")?;
        input.flush()?;
        self.line.clear();
        if self.output.read_line(&mut self.line)? == 0 {
            return Err(format!("oracle closed stdout while handling {}", case.id).into());
        }
        let response: Json = serde_json::from_str(&self.line)
            .map_err(|err| format!("unreadable oracle response for {}: {err}", case.id))?;
        if response["id"].as_str() != Some(case.id.as_str()) {
            return Err(format!(
                "oracle returned the wrong case id for {}: {response}",
                case.id
            )
            .into());
        }
        if let Some(err) = response.get("protocolError") {
            return Err(format!(
                "oracle protocol error for {}: {err}\n{}",
                case.id,
                case.json()
            )
            .into());
        }
        if let Some(kind) = response["compile"]["error"].as_str() {
            return Ok(Reply::Rejected {
                kind: kind.to_owned(),
            });
        }
        let verdicts = response["verdicts"].as_array();
        match verdicts {
            Some(v) if response["compile"] == "ok" && v.len() == case.requests.len() => Ok(
                Reply::Verdicts(v.iter().map(read_decision).collect::<Result<_>>()?),
            ),
            _ => Err(format!("bad oracle response for {}: {response}", case.id).into()),
        }
    }

    pub(crate) fn finish(mut self) -> Result<()> {
        drop(self.input.take());
        if !self.output.fill_buf()?.is_empty() {
            return Err("oracle produced extra output after the last case".into());
        }
        let status = self.process.wait()?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("oracle exited with {status}").into())
        }
    }
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.process.kill();
        let _ = self.process.wait();
    }
}

fn read_decision(j: &Json) -> Result<Decision> {
    if j == "allow" {
        return Ok(Decision::Allow);
    }
    let reason = match j["deny"].as_str() {
        Some("no_matching_rule") => DenyReason::NoMatchingRule,
        Some("no_allow_for_method") => DenyReason::NoAllowForMethod,
        Some("conditions_not_met") => DenyReason::ConditionsNotMet,
        Some("bad_request_path") => DenyReason::BadRequestPath,
        _ => return Err(format!("unrecognized oracle verdict {j}").into()),
    };
    Ok(Decision::Deny(reason))
}

pub(crate) struct Comparison {
    native: Reply,
    lean: Reply,
    diagnostics: Vec<Diagnostic>,
    parser_error: Option<String>,
    checker_stricter: bool,
    checker_missed: bool,
}

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum Difference {
    RoundTrip,
    Compile {
        rust: Option<String>,
        lean: Option<String>,
    },
    CheckerAccepted(String),
    CheckerStricter {
        lean: Option<String>,
    },
    Verdict {
        rust: Decision,
        lean: Decision,
    },
}

impl Comparison {
    pub(crate) fn difference(&self) -> Option<Difference> {
        if self.parser_error.is_some() {
            return Some(Difference::RoundTrip);
        }
        match (&self.native, &self.lean) {
            (Reply::Verdicts(native), Reply::Verdicts(lean)) => {
                native.iter().zip(lean).find_map(|(native, lean)| {
                    (native != lean).then(|| Difference::Verdict {
                        rust: native.clone(),
                        lean: lean.clone(),
                    })
                })
            }
            (native, lean) if native.rejection() != lean.rejection() => {
                let rust = native.rejection().map(str::to_owned);
                let lean = lean.rejection().map(str::to_owned);
                Some(if self.checker_stricter {
                    Difference::CheckerStricter { lean }
                } else {
                    Difference::Compile { rust, lean }
                })
            }
            (_, Reply::Rejected { kind, .. }) if self.checker_missed => {
                Some(Difference::CheckerAccepted(kind.clone()))
            }
            _ => None,
        }
    }

    fn report(&self, label: &str, case: &Case) {
        report_case(label, case);
        eprintln!("Rust {}\nLean {}", self.native.json(), self.lean.json());
        if let Some(parser_error) = &self.parser_error {
            eprintln!("{parser_error}");
        }
        for d in &self.diagnostics {
            eprintln!("{d}");
        }
    }
}

fn report_case(label: &str, case: &Case) {
    eprintln!(
        "{label} {}\n{}\n{}",
        case.id,
        case.json(),
        case.policy.print()
    );
}

pub(crate) fn compare(oracle: &mut Oracle, case: &Case) -> Result<Comparison> {
    let source = case.policy.print();
    let parsed = case.policy.check_round_trip(&source);
    let (native, diagnostics) = match Policy::compile(&source) {
        Ok(policy) => {
            let verdicts = case
                .requests
                .iter()
                .map(|facts| policy.evaluate(facts))
                .collect::<std::result::Result<_, _>>()?;
            (Reply::Verdicts(verdicts), Vec::new())
        }
        Err(diags) => {
            // The facade exposes diagnostic text; lower the parsed tree for its typed error.
            let kind = match &parsed {
                Ok(Parsed::Rejected(reason)) => reason.kind(),
                Ok(Parsed::Tree(tree)) => match facl_core::lower(tree) {
                    Ok(_) => "checkerStricter",
                    Err(err) => lower_error_name(&err.kind),
                },
                Err(_) => "printParse",
            };
            (
                Reply::Rejected {
                    kind: kind.to_owned(),
                },
                diags,
            )
        }
    };
    let checker_stricter = native.rejection() == Some("checkerStricter");
    // Policy::compile also rejects when the checker misses an error caught by lowering.
    let checker_missed = native.rejection().is_some()
        && !checker_stricter
        && matches!(&parsed, Ok(Parsed::Tree(_)))
        && !facl::check(&source).iter().any(Diagnostic::is_error);
    let lean = oracle.evaluate(case)?;
    Ok(Comparison {
        native,
        lean,
        diagnostics,
        parser_error: parsed.err(),
        checker_stricter,
        checker_missed,
    })
}

fn lower_error_name(kind: &LowerErrorKind) -> &'static str {
    match kind {
        LowerErrorKind::UnknownIdentifier => "unknownIdentifier",
        LowerErrorKind::ReservedCaptureName => "reservedCaptureName",
        LowerErrorKind::DuplicateCapture => "duplicateCapture",
        LowerErrorKind::RestNotLast => "restNotLast",
        LowerErrorKind::RestWithChildren => "restWithChildren",
        LowerErrorKind::UnknownFunction => "unknownFunction",
        LowerErrorKind::BadArity => "badArity",
        LowerErrorKind::BadTarget => "badTarget",
        LowerErrorKind::TooDeep => "tooDeep",
    }
}

pub(crate) struct Checked {
    pub requests: usize,
}

pub(crate) fn check_case(oracle: &mut Oracle, case: Case, seed: Option<u64>) -> Result<Checked> {
    let comparison = compare(oracle, &case).inspect_err(|_| report_case("Failed case", &case))?;
    let Some(difference) = comparison.difference() else {
        return Ok(Checked {
            requests: match &comparison.native {
                Reply::Verdicts(v) => v.len(),
                Reply::Rejected { .. } => 0,
            },
        });
    };
    if let Some(seed) = seed {
        eprintln!("Seed {seed}");
    }
    eprintln!("Disagreement {difference:?}");
    comparison.report("Original case", &case);
    let minimal = shrink(case, |candidate| -> Result<bool> {
        Ok(compare(oracle, candidate)?.difference().as_ref() == Some(&difference))
    })?;
    let comparison = compare(oracle, &minimal)?;
    if comparison.difference().as_ref() != Some(&difference) {
        return Err("the minimized disagreement did not reproduce".into());
    }
    comparison.report("Minimized case", &minimal);
    Err("Rust and Lean disagree".into())
}

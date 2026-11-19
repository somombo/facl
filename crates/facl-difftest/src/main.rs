mod generate;
mod runner;
mod shrink;
mod syntax;
mod wire;

use crate::generate::Generator;
use crate::runner::{Oracle, Reply, check_case};
use crate::syntax::{ParseRejection, Parsed, Rules};
use crate::wire::Case;
use facl::{Decision, reason_name, testcase};
use serde_json::Value as Json;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{self, BufReader};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

const USAGE: &str = "Usage:
  facl-difftest --oracle PATH --cases N --seed S
  facl-difftest --oracle PATH --conformance-only
  facl-difftest --cases N --seed S --round-trip-only
  facl-difftest --oracle PATH --replay CASE.json";

enum Mode {
    Diff,
    Conformance,
    RoundTrip,
    Replay(PathBuf),
}

struct Options {
    mode: Mode,
    oracle: Option<PathBuf>,
    cases: Option<usize>,
    seed: Option<u64>,
}

impl Options {
    fn parse() -> Result<Option<Self>> {
        let mut args = std::env::args_os().skip(1);
        let mut options = Self {
            mode: Mode::Diff,
            oracle: None,
            cases: None,
            seed: None,
        };
        while let Some(flag) = args.next() {
            let value = |next: Option<OsString>| {
                next.ok_or_else(|| format!("{} requires an argument", flag.to_string_lossy()))
            };
            match flag.to_str() {
                Some("--help" | "-h") => return Ok(None),
                Some("--oracle") => options.oracle = Some(value(args.next())?.into()),
                Some("--cases") => {
                    options.cases = Some(value(args.next())?.to_string_lossy().parse()?)
                }
                Some("--seed") => {
                    options.seed = Some(value(args.next())?.to_string_lossy().parse()?)
                }
                Some("--conformance-only" | "--round-trip-only" | "--replay")
                    if matches!(options.mode, Mode::Diff) =>
                {
                    options.mode = match flag.to_str() {
                        Some("--conformance-only") => Mode::Conformance,
                        Some("--round-trip-only") => Mode::RoundTrip,
                        _ => Mode::Replay(value(args.next())?.into()),
                    };
                }
                _ => return Err(format!("unexpected option {}", flag.to_string_lossy()).into()),
            }
        }
        Ok(Some(options))
    }

    fn oracle(&self) -> Result<Oracle> {
        Oracle::start(self.oracle.as_deref().ok_or("--oracle is required")?)
    }

    fn random_options(&self) -> Result<(usize, u64)> {
        let cases = self
            .cases
            .filter(|n| *n > 0)
            .ok_or("--cases must be positive")?;
        Ok((cases, self.seed.ok_or("--seed is required")?))
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("facl-difftest: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<()> {
    let options = match Options::parse() {
        Ok(Some(options)) => options,
        Ok(None) => {
            println!("{USAGE}");
            return Ok(());
        }
        Err(err) => return Err(format!("{err}\n{USAGE}").into()),
    };

    match &options.mode {
        Mode::RoundTrip => {
            let (cases, seed) = options.random_options()?;
            round_trips(cases, seed)
        }
        Mode::Conformance => {
            let mut oracle = options.oracle()?;
            conformance(&mut oracle)?;
            oracle.finish()
        }
        Mode::Replay(path) => {
            let input = if path == Path::new("-") {
                io::read_to_string(io::stdin().lock())?
            } else {
                fs::read_to_string(path)?
            };
            let case = Case::parse(&input)?;
            let id = case.id.clone();
            let mut oracle = options.oracle()?;
            check_case(&mut oracle, case, None)?;
            oracle.finish()?;
            println!("Rust and Lean agree for {id}");
            Ok(())
        }
        Mode::Diff => {
            let (cases, seed) = options.random_options()?;
            println!("Seed {seed}");
            let mut oracle = options.oracle()?;
            conformance(&mut oracle)?;
            let mut generator = Generator::new(seed);
            let mut requests = 0;
            for i in 0..cases {
                let checked = check_case(&mut oracle, generator.case(i), Some(seed))?;
                requests += checked.requests;
            }
            oracle.finish()?;
            println!("{cases} generated cases and {requests} request verdicts agreed");
            Ok(())
        }
    }
}

fn round_trips(cases: usize, seed: u64) -> Result<()> {
    println!("Seed {seed}");
    let mut generator = Generator::new(seed);
    let mut parsed = 0;
    let mut unknown_actions = 0;
    let mut too_deep = 0;
    for i in 0..cases {
        let case = generator.case(i);
        let source = case.policy.print();
        match case.policy.check_round_trip(&source) {
            Ok(Parsed::Tree(_)) => parsed += 1,
            Ok(Parsed::Rejected(ParseRejection::UnknownAction(_))) => unknown_actions += 1,
            Ok(Parsed::Rejected(ParseRejection::MatchDepth)) => too_deep += 1,
            Err(err) => return Err(format!("{}\n{}\n{source}\n{err}", case.id, case.json()).into()),
        }
    }
    println!(
        "{parsed} policy trees round-tripped. The parser rejected {unknown_actions} unknown actions and {too_deep} over-depth matches."
    );
    Ok(())
}

fn conformance(oracle: &mut Oracle) -> Result<()> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../conformance");
    let mut paths = fs::read_dir(dir)?
        .map(|entry| entry.map(|e| e.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    paths.sort();

    let mut count = 0;
    let mut suites = 0;
    for path in paths {
        let Some(name) = path
            .file_name()
            .and_then(|name| name.to_str())
            .and_then(|name| name.strip_suffix(".cases.json"))
        else {
            continue;
        };
        let source = fs::read_to_string(path.with_file_name(format!("{name}.rules")))?;
        let parsed = facl_syntax::parse(&source).map_err(|err| format!("{name}.rules: {err:?}"))?;
        let entries: Vec<Json> = serde_json::from_reader(BufReader::new(File::open(&path)?))?;
        let expected = entries
            .iter()
            .map(testcase::Case::from_json)
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let mut case = Case {
            id: format!("conformance-{name}"),
            policy: Rules::from_parsed(parsed),
            requests: expected.iter().map(|e| e.facts.clone()).collect(),
        };
        let verdicts = match oracle.evaluate(&case)? {
            Reply::Verdicts(verdicts) => verdicts,
            Reply::Rejected { kind: reason, .. } => {
                return Err(format!(
                    "{} rejected as {reason}\n{}\n{source}",
                    case.id,
                    case.json()
                )
                .into());
            }
        };
        for (expected, actual) in expected.iter().zip(verdicts) {
            let passed = match &actual {
                Decision::Allow => expected.expect_allow,
                Decision::Deny(reason) => {
                    !expected.expect_allow
                        && expected
                            .expect_reason
                            .as_ref()
                            .is_none_or(|want| want == reason_name(reason))
                }
            };
            if !passed {
                case.requests = vec![expected.facts.clone()];
                let label = expected.name.as_deref().unwrap_or(&expected.request);
                return Err(format!(
                    "{} ({label}) expected {} {:?}, got {actual:?}\n{}\n{source}",
                    case.id,
                    if expected.expect_allow {
                        "allow"
                    } else {
                        "deny"
                    },
                    expected.expect_reason,
                    case.json()
                )
                .into());
            }
        }
        count += expected.len();
        suites += 1;
    }
    if count == 0 {
        return Err("no conformance cases found".into());
    }
    println!("{count} conformance cases passed through Lean across {suites} fixtures");
    Ok(())
}

//! Micro-benchmarks: `cargo run --release -p facl --example bench`.

use facl::{Decision, Policy, RequestFacts};
use serde_json::json;
use std::hint::black_box;
use std::time::Instant;

const README: &str = r#"
service http {
  match /users/{userId} {
    allow read: if request.auth != null;
    allow write: if request.auth != null && request.auth.uid == userId;
    match /files/{path=**} {
      allow read, write: if request.auth != null && request.auth.uid == userId;
    }
  }
  match /public/{path=**} {
    allow get, head: if true;
  }
  match /webhooks/stripe {
    allow post: if context.stripeVerified == true;
  }
}
"#;
const PUBLIC_ONLY: &str = "service http { match /public/{path=**} { allow get: if true; } }";

/// Runs `f` for batches of about 20 ms and returns the median ns/op.
fn measure(mut f: impl FnMut()) -> f64 {
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed().as_millis() < 100 {
        f();
        n += 1;
    }
    let per_op = start.elapsed().as_nanos() as f64 / n as f64;
    let size = ((20e6 / per_op) as u64).max(1);
    let mut samples: Vec<f64> = (0..15)
        .map(|_| {
            let t = Instant::now();
            for _ in 0..size {
                f();
            }
            t.elapsed().as_nanos() as f64 / size as f64
        })
        .collect();
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn main() {
    println!(
        "rustc: {}",
        std::process::Command::new("rustc")
            .arg("--version")
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_default()
    );
    println!(
        "{:<24} {:<10} {:>12} {:>14}",
        "scenario", "layer", "ns/op", "ops/s"
    );
    let row = |name: &str, ns: f64| {
        println!(
            "{:<24} {:<10} {:>12.1} {:>14.0}",
            name,
            "native",
            ns,
            1e9 / ns
        );
    };

    let many: String = (0..100)
        .map(|i| format!("match /r{i}/{{id}} {{ allow read: if request.auth.uid == id; }}\n"))
        .collect();
    let many = format!("service http {{\n{many}}}");
    let alice = Some(json!({ "uid": "alice" }));
    let cases = [
        (
            "public read",
            README,
            "GET",
            "/public/docs/a.txt",
            None,
            true,
        ),
        (
            "owner write",
            README,
            "PUT",
            "/users/alice",
            alice.clone(),
            true,
        ),
        ("no rule", README, "DELETE", "/admin", None, false),
        ("bad path", README, "GET", "/a//b", None, false),
        (
            "100 rules, last matches",
            &many,
            "GET",
            "/r99/alice",
            alice,
            true,
        ),
        ("footprint", PUBLIC_ONLY, "GET", "/public/x", None, true),
    ];
    for (name, source, method, path, auth, allowed) in cases {
        let policy = Policy::compile(source).expect("policy compiles");
        let facts = RequestFacts {
            method: method.into(),
            path: path.into(),
            headers: Vec::new(),
            auth,
            context: None,
        };
        let decision = policy.evaluate(&facts).expect("facts are usable");
        assert_eq!(decision == Decision::Allow, allowed, "{name}: {decision:?}");
        row(
            name,
            measure(|| drop(black_box(policy.evaluate(black_box(&facts))))),
        );
    }
    let ns = measure(|| drop(black_box(Policy::compile(black_box(README)))));
    row("compile (README)", ns);
}

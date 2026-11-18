# facl verification

This Lean 4 project specifies how facl matches paths and combines rules. It also proves that three functions extracted from the Rust implement that spec:

- the grant combiner, `combine`
- path matching, `match_pattern`
- the decision procedure, `decide_with`

## What is specified

| Lean (`Facl/Spec.lean`) | Rust (`facl-core`) |
| --- | --- |
| `Seg`, `Pattern`, `matchPattern` | `Seg`, `Pattern`, `match_pattern` |
| `Outcome`, `Verdict`, `combine` | `Outcome`, `Verdict`, `combine` |
| `DenyReason`, `Decision`, `decide` | `DenyReason`, `Decision`, `decide_with` |

Conditions are abstract: `decide` takes `eval : Cond → List (Cap α) → Request α → Outcome`. The spec is generic in the path segment type `α`. The refinement proofs use bytes (`List U8`), as the Rust does, and the examples use `String`.

Differences from the Rust:

- Methods are a `Nat` bitmask.
- `combine` is the closed form of the Rust loop.
- `request` and `context` are folded into `eval`.

Theorems (`Facl/Theorems.lean`): `combine_eq_allow_iff`, `decide_eq_allow_iff`, `default_deny`, `decide_perm` (rule order is irrelevant), `decide_mono` (adding rules never revokes access), `match_length_of_not_rest`, `match_instantiate` (instantiating a pattern with its captures rebuilds the path). `Facl/Examples.lean` has `#guard` checks mirroring the conformance cases.

## Refinement proofs

Each theorem below is about the code Aeneas generated from the Rust. Each proves
that the function returns without failing, and that its result agrees with the
spec.

| Theorem | File | Shows |
| --- | --- | --- |
| `combine_spec` | [Facl/Refinement.lean](Facl/Refinement.lean) | `combine`'s verdict is `Facl.combine` of the outcomes |
| `combine_allow_iff` | [Facl/Refinement.lean](Facl/Refinement.lean) | `combine` allows exactly when some outcome is `Granted` |
| `match_pattern_spec` | [Facl/RefinementPath.lean](Facl/RefinementPath.lean) | `match_pattern`'s captures are `Facl.matchPattern`'s |
| `decide_with_spec` | [Facl/RefinementDecide.lean](Facl/RefinementDecide.lean) | `decide_with`'s decision is `Facl.decide`'s |

`decide_with_spec` covers matching, method filtering, combining and the deny
reasons. It holds for any condition evaluator that never fails and agrees with
the spec's `eval`. Its only other assumptions are size bounds that any real
policy meets:

- every pattern has fewer than `Usize.max` segments
- the policy has at most `Usize.max` allows in total

With it, the spec theorems carry over to the Rust: default deny, rule order not
mattering, and adding rules never revoking access. The Rust `decide` is
`decide_with` with the CEL evaluator plugged in, and that evaluator is not
proven yet.

The maps from the generated Rust types to the spec's types live in
[Facl/Lift.lean](Facl/Lift.lean), and `Challenge.lean` uses them too.

## Regenerate the Lean extraction

Regeneration uses rsync. With Nix flakes enabled, run this from the repository root.

```sh
verification/extract.sh
```

The script runs both tools from the pinned Aeneas flake. Aeneas is pinned at
`1dc8ad31b1b062a77c50e29144a6c7bba955fa09`, which pins Charon at
`454586e9b770231e66d2062993e632dfc06463e2`. The Lake dependency uses the same
Aeneas revision.

For a source build, check out that Aeneas revision and follow its build
instructions. Pass the absolute paths of the two built binaries to the same
script. [Aeneas installation instructions](https://github.com/AeneasVerif/aeneas/tree/1dc8ad31b1b062a77c50e29144a6c7bba955fa09#installation--build)

```sh
CHARON=/path/to/charon AENEAS=/path/to/aeneas verification/extract.sh
```

Charon starts at `crate::decide::combine`, `crate::path::match_pattern` and
`crate::decide::decide_with`, and follows their dependencies. The rest of
`facl-core` is outside this extraction. That includes the CEL evaluator, which
`decide_with` reaches only through its `Conditions` trait. Whole-crate
translation hits Aeneas's restriction on breaks to outer loops in `lower_match`.

At this Aeneas revision, writing extractable Rust has some pitfalls:

- **`!` on a `bool` used as a value.** Code such as `granted = !granted`
  extracts to Lean's `¬`, and the generated code does not typecheck. A mutation
  test found this. `!` in an `if` condition is fine.
- **No `Vec::clone` model.** `match_pattern` copies bytes with a loop instead.
- **A parameter named `path`.** It shadows the generated `path` namespace, so
  the Rust parameters are called `segments`.
- **An `if let` that drops an owned value inside a loop.** Aeneas fails with
  "Could not match the contexts". `decide_with` moves the per-rule work into
  `apply_rule`, which uses `let ... else`.

Charon treats the Rust standard library's slice `len` and `SliceIndex::index`
for `usize` as opaque. Aeneas supplies their Lean models. The extraction uses
no explicit `--opaque` or `--exclude` flags and needs no template files.

Commit the Lean output in `verification/FaclCore/`. After a successful
extraction the script mirrors the entire generated directory, removing stale
files and subdirectories. It keeps the intermediate LLBC in a temporary
directory and removes it when it exits.

## Check the proofs

Install Elan and run the following. Elan reads `lean-toolchain` and installs
Lean 4.36.0-rc2. Lake uses the committed dependency lockfile.

```sh
cd verification
lake exe cache get
lake build --wfail
```

The build requires all eleven theorems named in `comparator.json`, and checks that
their transitive axioms are drawn from `propext`, `Classical.choice` and
`Quot.sound`. The `aeneas` CI job runs `check.sh --paranoid`, described next.

## Check the proofs independently with comparator

`lake comparator` judges the proofs without trusting this project's build. In a
sandbox, it builds and exports two modules:

- the challenge, [Challenge.lean](Challenge.lean), which states the eleven theorems,
  each proved with `sorry`
- the solution, the `Facl` module, which proves them

It then checks that every theorem named in [comparator.json](comparator.json)
proves exactly the challenge's statement. It also checks that each uses no axiom
beyond `propext`, `Quot.sound` and `Classical.choice`, and that Lean's kernel
accepts it. With `--paranoid` it also replays the export through the other
checkers bundled with Lean: `leanchecker-paranoid`, `lean4lean`, `nanoda`,
`con-leche` and `con-ron`.

comparator takes the definitions the challenge imports as given. In particular,
it cannot tell whether the generated `FaclCore/` is what Aeneas produces from the
Rust. A hand-edited `Funs.lean` would pass comparator, because the challenge and
the solution would both see the same edit. The extraction drift check closes that
gap, so the two must run together. [check.sh](check.sh) runs them in order.

With both checks passing, a reviewer has to trust only these:

- `Challenge.lean`, `comparator.json`, [Facl/Spec.lean](Facl/Spec.lean) and
  [Facl/Lift.lean](Facl/Lift.lean)
- the pinned Charon and Aeneas, for translating the Rust faithfully
- the Aeneas Lean library's models of the Rust standard library
- the Lean kernels

The proofs themselves need no review.

### Prerequisites

- **Elan**, as above. `lake comparator` ships with the pinned Lean toolchain.
- **bubblewrap** (`bwrap`), which provides the sandbox. On Debian or Ubuntu, run
  `sudo apt install bubblewrap`.
  - `bwrap` needs unprivileged user namespaces, or must be installed setuid root.
  - To test it, run `bwrap --ro-bind / / --dev /dev --proc /proc true`.
  - If that fails with a permission error, your distribution restricts user
    namespaces. Ubuntu 23.10 and later do this through AppArmor. Allow them for
    `bwrap` before you continue.
- **A built project.** The build inside the sandbox has no network access, and
  the sandbox hides your home directory, so resolve and build the dependencies
  first. comparator reads the committed `lake-manifest.json`.

### Run it

From the repository root:

```sh
verification/check.sh               # drift check, strict build, then lake comparator
verification/check.sh --paranoid    # the same, plus every bundled kernel
```

The script stops at the first failure:

1. It regenerates `FaclCore/` with `extract.sh`, and fails if anything changed.
   This step needs the pinned Charon and Aeneas, either through Nix or through
   `CHARON` and `AENEAS`, as in "Regenerate the Lean extraction" above.
2. It runs `lake exe cache get` and `lake build --wfail`.
3. It runs `lake comparator`.

Without Charon and Aeneas, `verification/check.sh --no-extract` skips step 1.
`FaclCore/` is then trusted as committed. To run comparator by hand, first run
`lake exe cache get` and `lake build` from `verification/`, then
`lake comparator` with or without `--paranoid`.

Each run exports only the eleven theorems and what they depend on, about 5,100
declarations, not the whole Mathlib environment. With the build already done,
`verification/check.sh --paranoid` took about three minutes when measured on
2026-11-18.

`lake comparator` exits with one of three codes:

- **0:** accepted.
- **1:** rejected, because of a statement mismatch, a forbidden axiom, a kernel
  rejection or a failed build.
- **2:** it could not start, because `bwrap`, the manifest or the configuration
  is missing.

## Conventions

Where things go:

| File | Holds | Who writes it |
| --- | --- | --- |
| `Facl/Spec.lean` | The meaning: every definition a spec theorem's statement mentions | A person, reviewed |
| `Facl/Lift.lean` | Maps from the generated Rust types to the spec's types | A person, reviewed |
| `FaclCore/` | The Rust, as Aeneas generates it | `extract.sh` only, never by hand |
| `Challenge.lean` | The statements, each proved with `sorry` | A person, reviewed |
| `Facl/Theorems.lean`, `Facl/Refinement.lean` | The proofs, and private helper lemmas | Anyone, AI included |

A definition that any statement mentions never lives in a proof file. Challenge
and solution must share it, and the challenge cannot import proof files: they
declare theorems with the same names.

To add a proof, such as a refinement of `match_pattern` or `decide`:

1. Extend the extraction in `extract.sh` if the function is not extracted yet,
   and commit the regenerated `FaclCore/` with it.
2. Add any new definitions the statement needs to `Facl/Spec.lean` or
   `Facl/Lift.lean`.
3. Write the statement in `Challenge.lean`, add its name to `comparator.json`
   and to the axiom check in `Facl.lean`, and review the statement.
4. Prove it in a proof file. Give each extracted function its own `@[step]` spec
   lemma, as `combine_spec` has, so that proofs about callers can use it.
5. Run `verification/check.sh`. CI runs it too, with `--paranoid`.

When a statement changes, change `Challenge.lean` along with the solution, and
review that change. `Challenge` is a Lake library of its own and not a default
target, so `lake build` and CI never build its `sorry`s.

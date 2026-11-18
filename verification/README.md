# facl verification

This Lean 4 project specifies how facl matches paths and combines rules. It also proves that the grant combiner extracted from Rust implements the Lean spec.

## What is specified

| Lean (`Facl/Spec.lean`) | Rust (`facl-core`) |
| --- | --- |
| `Seg`, `Pattern`, `matchPattern` | `Seg`, `Pattern`, `match_pattern` |
| `Outcome`, `Verdict`, `combine` | `Outcome`, `Verdict`, `combine` |
| `DenyReason`, `Decision`, `decide` | `DenyReason`, `Decision`, `decide` |

Conditions are abstract: `decide` takes `eval : Cond → List Cap → Request → Outcome`. Differences from the Rust are noted in comments: literals are `String` not bytes, methods are a `Nat` bitmask, `combine` is the closed form of the Rust loop, and `request`/`context` are folded into `eval`.

Theorems (`Facl/Theorems.lean`): `combine_eq_allow_iff`, `decide_eq_allow_iff`, `default_deny`, `decide_perm` (rule order is irrelevant), `decide_mono` (adding rules never revokes access), `match_length_of_not_rest`, `match_instantiate` (instantiating a pattern with its captures rebuilds the path). `Facl/Examples.lean` has `#guard` checks mirroring the conformance cases.

## Combiner refinement

[Facl/Refinement.lean](Facl/Refinement.lean) proves two properties of the
generated `FaclCore.decide.combine` for every input slice.

- `combine_spec` proves the function returns successfully and its verdict agrees
  with `Facl.combine` on the corresponding list.
- `combine_allow_iff` proves the function returns successfully and its verdict is
  `Allow` exactly when the slice contains `Granted`.

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

Charon starts at `crate::decide::combine` and follows its dependencies. This
includes the Rust `combine` function and the `Outcome` and `Verdict` enums.
Whole-crate translation hits Aeneas's restriction on breaks to outer loops in
`lower_match`. The other `facl-core` declarations are outside this extraction.

At this Aeneas revision, Rust's `!` on a `bool` used as a value, such as
`granted = !granted`, extracts to Lean's `¬`, and the generated code does not
typecheck. A mutation test found this. Keep it in mind when extending the
extraction beyond `combine`.

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

The `aeneas` CI job checks the entire generated directory for drift and builds
the spec, examples and proofs with the Mathlib cache. The build requires both
combiner theorems and checks that their transitive axioms are drawn from
`propext`, `Classical.choice` and `Quot.sound`.

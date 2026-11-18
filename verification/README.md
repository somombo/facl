# facl verification

Standalone Lean 4 project (no Mathlib, no dependencies) specifying how facl matches paths and combines rules, with proofs of the key properties.

## What is specified

| Lean (`Facl/Spec.lean`) | Rust (`facl-core`) |
| --- | --- |
| `Seg`, `Pattern`, `matchPattern` | `Seg`, `Pattern`, `match_pattern` |
| `Outcome`, `Verdict`, `combine` | `Outcome`, `Verdict`, `combine` |
| `DenyReason`, `Decision`, `decide` | `DenyReason`, `Decision`, `decide` |

Conditions are abstract: `decide` takes `eval : Cond → List Cap → Request → Outcome`. Differences from the Rust are noted in comments: literals are `String` not bytes, methods are a `Nat` bitmask, `combine` is the closed form of the Rust loop, and `request`/`context` are folded into `eval`.

Theorems (`Facl/Theorems.lean`): `combine_eq_allow_iff`, `decide_eq_allow_iff`, `default_deny`, `decide_perm` (rule order is irrelevant), `decide_mono` (adding rules never revokes access), `match_length_of_not_rest`, `match_instantiate` (instantiating a pattern with its captures rebuilds the path). `Facl/Examples.lean` has `#guard` checks mirroring the conformance cases.

## Build

```sh
cd verification
lake build
```

Toolchain: `leanprover/lean4:v4.33.0`.

## Next step: Aeneas extraction of `facl-core`

```sh
cd crates/facl-core
charon cargo --preset=aeneas
aeneas -backend lean -loops-to-rec -split-files -namespace FaclCore <llbc>
```

## The v0.3 gate

The refinement theorem for the grant combiner, as in the design doc:

```lean
def Spec.combine (outs : List Outcome) : Verdict :=
  if outs.contains .granted then .allow else .deny

@[step] theorem combine.spec (outs : Slice Outcome) :
    combine outs ⦃ v => v = Spec.combine outs.val ⦄
```

## Toolchain change when wiring in extraction

Aeneas's generated Lean needs its pin, `leanprover/lean4:v4.36.0-rc2`, and pulls in Mathlib. Moving this project to that toolchain is part of wiring in extraction; until then it stays dependency-free on v4.33.0.

import Facl.Spec
import Facl.Lift
import FaclCore.Funs

/-! The statements `lake comparator` holds `Facl` to. The `sorry`s are deliberate:
see "Conventions" in README.md. -/

namespace Facl

theorem combine_eq_allow_iff (outs : List Outcome) :
    combine outs = .allow ↔ Outcome.granted ∈ outs := by
  sorry

theorem match_length_of_not_rest {α : Type} [DecidableEq α] (p : Pattern α) (path : List α) (caps : List (Cap α))
    (hr : p.rest = false) (h : matchPattern p path = some caps) :
    path.length = p.segs.length := by
  sorry

theorem match_instantiate {α : Type} [DecidableEq α] (p : Pattern α) (path : List α) (caps : List (Cap α))
    (h : matchPattern p path = some caps) : instantiate p caps = some path := by
  sorry

variable {α : Type} [DecidableEq α] {C : Type} (eval : C → List (Cap α) → Request α → Outcome)

theorem decide_eq_allow_iff (p : Policy α C) (req : Request α) :
    Facl.decide eval p req = .allow ↔
      ∃ r ∈ p.rules, ∃ caps, matchPattern r.pattern req.path = some caps ∧
        ∃ a ∈ r.allows, a.applies req.method = true ∧ eval a.cond caps req = .granted := by
  sorry

theorem default_deny (p : Policy α C) (req : Request α)
    (h : ∀ r ∈ p.rules, matchPattern r.pattern req.path = none) :
    Facl.decide eval p req = .deny .noMatchingRule := by
  sorry

theorem decide_perm (p q : Policy α C) (req : Request α) (h : p.rules.Perm q.rules) :
    Facl.decide eval p req = .allow ↔ Facl.decide eval q req = .allow := by
  sorry

theorem decide_mono (p q : Policy α C) (req : Request α)
    (h : ∀ r ∈ p.rules, r ∈ q.rules) (ha : Facl.decide eval p req = .allow) :
    Facl.decide eval q req = .allow := by
  sorry

theorem utf8Valid_iff (bytes : List UInt8) :
    utf8Valid bytes = true ↔ bytes.toByteArray.IsValidUTF8 := by
  sorry

theorem canonicalize_segment {raw : List UInt8} {segs : List (List UInt8)}
    (h : canonicalize raw = .ok segs) : ∀ s ∈ segs,
      s ≠ [] ∧ s ≠ utf8 "." ∧ s ≠ utf8 ".." ∧ '/'.toUInt8 ∉ s ∧ 0 ∉ s ∧
        s.toByteArray.IsValidUTF8 := by
  sorry

end Facl

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore.decide

theorem combine_spec (outs : Slice Outcome) :
    combine outs ⦃ verdict =>
      verdictToSpec verdict = Facl.combine (outs.val.map outcomeToSpec) ⦄ := by
  sorry

theorem combine_allow_iff (outs : Slice Outcome) :
    combine outs ⦃ verdict => (verdict = .Allow ↔ Outcome.Granted ∈ outs.val) ⦄ := by
  sorry

theorem decide_with_spec {C E : Type} (inst : Conditions E C) (p : ir.Policy C) (method : U8)
    (segments : Slice (alloc.vec.Vec U8)) (conds : E)
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (hsegs : ∀ r ∈ p.rules.val, r.pattern.segs.val.length < Usize.max)
    (hallows : (p.rules.val.map fun r => r.allows.val.length).sum ≤ Usize.max)
    (heval : ∀ cond captures, inst.outcome conds cond captures ⦃ o =>
      outcomeToSpec o = eval cond (captures.val.map path.captureToSpec)
        (requestToSpec method segments) ⦄) :
    decide_with inst p method segments conds ⦃ d =>
      decisionToSpec d = Facl.decide eval (ir.policyToSpec p) (requestToSpec method segments) ⦄ := by
  sorry

theorem method_bit_spec (bytes : Slice U8) :
    method_bit bytes ⦃ bit => bit.val = Facl.methodBit (bytesToSpec bytes) ⦄ := by
  sorry

end FaclCore.decide

namespace FaclCore.path

theorem match_pattern_spec (p : ir.Pattern) (segments : Slice (alloc.vec.Vec U8))
    (hsegs : p.segs.val.length < Usize.max) :
    match_pattern p segments ⦃ caps =>
      caps.map (fun v => v.val.map captureToSpec) =
        Facl.matchPattern (ir.patternToSpec p) (segmentsToSpec segments) ⦄ := by
  sorry

theorem canonicalize_spec (raw : Slice U8) :
    canonicalize raw ⦃ r => canonicalToSpec r = Facl.canonicalize (bytesToSpec raw) ⦄ := by
  sorry

end FaclCore.path

import Facl.RefinementRequest
import Facl.RefinementDecide
open Aeneas Aeneas.Std Aeneas.Std.Result
namespace FaclCore.decide

private theorem byteOfSpec_byteToSpec (b : U8) : byteOfSpec (byteToSpec b) = b := by
  apply UScalar.eq_of_val_eq
  show (BitVec.ofNat 8 b.val).toNat = b.val
  simp

theorem evaluate_with_spec {C E X P : Type} (condsInst : Conditions E C)
    (prepInst : PrepareConditions P C E X) (p : ir.Policy C) (method raw : Slice U8) (prep : P)
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (hsegs : ∀ r ∈ p.rules.val, r.pattern.segs.val.length < Usize.max)
    (hallows : (p.rules.val.map fun r => r.allows.val.length).sum ≤ Usize.max)
    (hprep : ∀ segments, prepInst.prepare prep segments ⦃ r => ∀ conds, r = .Ok conds →
      ∀ m cond captures, condsInst.outcome conds cond captures ⦃ o =>
        outcomeToSpec o = eval cond (captures.val.map path.captureToSpec)
          (requestToSpec m segments) ⦄ ⦄) :
    evaluate_with condsInst prepInst p method raw prep ⦃ r =>
      match Facl.canonicalize (bytesToSpec raw) with
      | .error _ => r = .Ok (.Deny .BadRequestPath)
      | .ok segs => ∀ d, r = .Ok d →
        decisionToSpec d = Facl.decide eval (ir.policyToSpec p)
          ⟨Facl.methodBit (bytesToSpec method), segs.map (·.map byteOfSpec)⟩ ⦄ := by
  unfold evaluate_with
  apply WP.spec_bind (path.canonicalize_spec raw)
  intro r hr
  cases r with
  | Err e =>
    rw [path.canonicalToSpec] at hr
    rw [← hr]
    simp
  | Ok segments =>
    rw [path.canonicalToSpec] at hr
    rw [← hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    apply WP.spec_bind (hprep (alloc.vec.Vec.deref segments))
    intro r1 hr1
    cases r1 with
    | Err x =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok conds =>
      simp only [Aeneas.Std.bind_ok]
      apply WP.spec_bind (method_bit_spec method)
      intro i hi
      refine WP.spec_bind (decide_with_spec condsInst p i (alloc.vec.Vec.deref segments) conds
        eval hsegs hallows fun cond captures => hr1 conds rfl i cond captures) ?_
      intro d hd
      simp only [WP.spec_ok]
      intro d' hd'
      cases hd'
      rw [hd]
      have : (segments.val.map (·.val.map byteToSpec)).map (·.map byteOfSpec) =
          segmentsToSpec (alloc.vec.Vec.deref segments) := by
        simp [segmentsToSpec, alloc.vec.Vec.deref, List.map_map, Function.comp_def,
          byteOfSpec_byteToSpec]
      simp only [requestToSpec, this, hi]

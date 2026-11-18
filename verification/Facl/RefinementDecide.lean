import Facl.Refinement
import Facl.RefinementPath

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore.decide

private theorem apply_rule_loop_spec {C E : Type} (inst : Conditions E C)
    (v : alloc.vec.Vec (ir.CompiledAllow C)) (method : U8) (conds : E)
    (outcomes : alloc.vec.Vec Outcome) (captures : alloc.vec.Vec path.Capture)
    (applicable : Bool) (j : Usize)
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (req : Facl.Request (List U8))
    (heval : ∀ cond captures, inst.outcome conds cond captures ⦃ o =>
      outcomeToSpec o = eval cond (captures.val.map path.captureToSpec) req ⦄)
    (hj : j.val ≤ v.length) (hb : outcomes.length + (v.length - j.val) ≤ Usize.max) :
    apply_rule_loop inst v method conds outcomes captures applicable j ⦃ res =>
      res.1.val.map outcomeToSpec = outcomes.val.map outcomeToSpec ++
        (((v.val.drop j.val).map ir.allowToSpec).filter (·.applies method.val)).map
          (fun a => eval a.cond (captures.val.map path.captureToSpec) req) ∧
      res.2 = (applicable || ((v.val.drop j.val).map ir.allowToSpec).any (·.applies method.val)) ⦄ := by
  have hj' : j.val ≤ v.val.length := hj
  have hb' : outcomes.val.length + (v.val.length - j.val) ≤ Usize.max := hb
  unfold apply_rule_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : j.val < v.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec v j hlt')
    intro allow hallow
    simp only [lift, Aeneas.Std.bind_ok]
    have hdrop : v.val.drop j.val = allow :: v.val.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hallow]
    have happ : (allow.methods &&& method != 0#u8) =
        (ir.allowToSpec allow).applies method.val := by
      simp only [Facl.Allow.applies, ir.allowToSpec]
      rw [Bool.eq_iff_iff]
      simp [UScalar.eq_equiv, UScalar.val_and]
    rw [hdrop, List.map_cons, List.filter_cons, List.any_cons, ← happ]
    split
    · rename_i hap
      simp only [Aeneas.Std.bind_assoc]
      apply WP.spec_bind (heval allow.cond captures.deref)
      intro o ho
      apply WP.spec_bind (alloc.vec.Vec.push_spec outcomes o (by omega))
      intro outcomes2 houts2
      simp only [Aeneas.Std.bind_ok]
      apply WP.spec_bind (Usize.add_spec (x := j) (y := 1#usize)
        (by simpa using (show j.val + 1 ≤ v.val.length by omega).trans (Slice.length_ineq v.slice)))
      intro next hnext
      have hval : next.val = j.val + 1 := by simpa using hnext
      refine WP.spec_mono (apply_rule_loop_spec inst v method conds outcomes2 captures true next
        eval req heval (by omega) (by simp only [alloc.vec.Vec.length, houts2, hval]; simp; omega)) ?_
      intro res hres
      rw [hval] at hres
      refine ⟨?_, ?_⟩
      · rw [hres.1, houts2]
        simp [ho, alloc.vec.Vec.deref, ir.allowToSpec]
      · rw [hres.2]
        simp [hap]
    · rename_i hap
      simp only [Aeneas.Std.bind_ok]
      apply WP.spec_bind (Usize.add_spec (x := j) (y := 1#usize)
        (by simpa using (show j.val + 1 ≤ v.val.length by omega).trans (Slice.length_ineq v.slice)))
      intro next hnext
      have hval : next.val = j.val + 1 := by simpa using hnext
      refine WP.spec_mono (apply_rule_loop_spec inst v method conds outcomes captures applicable next
        eval req heval (by omega) (by simp only [hval]; omega)) ?_
      intro res hres
      rw [hval] at hres
      refine ⟨?_, ?_⟩
      · rw [hres.1]
      · rw [hres.2]
        simp [hap]
  · rename_i hstop
    have hend : j.val = v.val.length := by
      have : ¬ j.val < v.val.length := hstop
      omega
    simp [hend]
termination_by v.length - j.val
decreasing_by all_goals omega


private theorem apply_rule_spec {C E : Type} (inst : Conditions E C) (rule : ir.Rule C)
    (method : U8) (segments : Slice (alloc.vec.Vec U8)) (conds : E)
    (outcomes : alloc.vec.Vec Outcome)
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (hsegs : rule.pattern.segs.val.length < Usize.max)
    (hb : outcomes.length + rule.allows.length ≤ Usize.max)
    (heval : ∀ cond captures, inst.outcome conds cond captures ⦃ o =>
      outcomeToSpec o = eval cond (captures.val.map path.captureToSpec)
        (requestToSpec method segments) ⦄) :
    apply_rule inst rule method segments conds outcomes ⦃ res =>
      res.1.val.map outcomeToSpec = outcomes.val.map outcomeToSpec ++
        Facl.ruleOutcomes eval (ir.ruleToSpec rule) (requestToSpec method segments) ∧
      res.2.1 = (Facl.matchPattern (ir.ruleToSpec rule).pattern
        (requestToSpec method segments).path).isSome ∧
      res.2.2 = !(Facl.ruleOutcomes eval (ir.ruleToSpec rule) (requestToSpec method segments)).isEmpty ⦄ := by
  unfold apply_rule
  apply WP.spec_bind (path.match_pattern_spec rule.pattern segments hsegs)
  intro o ho
  have hm : Facl.matchPattern (ir.ruleToSpec rule).pattern (requestToSpec method segments).path =
      o.map (fun v => v.val.map path.captureToSpec) := ho.symm
  cases o with
  | none =>
    simp only [Facl.ruleOutcomes, hm, WP.spec_ok]
    simp
  | some captures =>
    dsimp only
    refine WP.spec_bind (apply_rule_loop_spec inst rule.allows method conds outcomes captures false
      0#usize eval (requestToSpec method segments) heval (by simp) (by simpa using hb)) ?_
    intro res hres
    simp only [Facl.ruleOutcomes, hm, Option.map_some, Option.isSome_some]
    obtain ⟨outs, app⟩ := res
    refine (WP.spec_ok (outs, true, app)).mpr ?_
    refine ⟨?_, rfl, ?_⟩
    · rw [hres.1]
      simp [ir.ruleToSpec, requestToSpec]
    · rw [hres.2, Bool.eq_iff_iff]
      simp [ir.ruleToSpec, requestToSpec, List.any_eq_true, List.filter_eq_nil_iff]


private theorem ruleOutcomes_length_le {C : Type}
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (r : Facl.Rule (List U8) C) (req : Facl.Request (List U8)) :
    (Facl.ruleOutcomes eval r req).length ≤ r.allows.length := by
  unfold Facl.ruleOutcomes
  split
  · simp
  · simpa using List.length_filter_le _ _

private theorem decide_with_loop_spec {C E : Type} (inst : Conditions E C) (p : ir.Policy C)
    (method : U8) (segments : Slice (alloc.vec.Vec U8)) (conds : E)
    (outcomes : alloc.vec.Vec Outcome) (matched applicable : Bool) (i : Usize)
    (eval : C → List (Facl.Cap (List U8)) → Facl.Request (List U8) → Facl.Outcome)
    (hsegs : ∀ r ∈ p.rules.val, r.pattern.segs.val.length < Usize.max)
    (heval : ∀ cond captures, inst.outcome conds cond captures ⦃ o =>
      outcomeToSpec o = eval cond (captures.val.map path.captureToSpec)
        (requestToSpec method segments) ⦄)
    (hi : i.val ≤ p.rules.length)
    (hb : outcomes.length +
      ((p.rules.val.drop i.val).map fun r => r.allows.val.length).sum ≤ Usize.max) :
    decide_with_loop inst p method segments conds outcomes matched applicable i ⦃ res =>
      res.1.val.map outcomeToSpec = outcomes.val.map outcomeToSpec ++
        ((p.rules.val.drop i.val).map ir.ruleToSpec).flatMap
          (Facl.ruleOutcomes eval · (requestToSpec method segments)) ∧
      res.2.1 = (matched || ((p.rules.val.drop i.val).map ir.ruleToSpec).any
        (fun r => (Facl.matchPattern r.pattern (requestToSpec method segments).path).isSome)) ∧
      res.2.2 = (applicable || !(((p.rules.val.drop i.val).map ir.ruleToSpec).flatMap
        (Facl.ruleOutcomes eval · (requestToSpec method segments))).isEmpty) ⦄ := by
  have hi' : i.val ≤ p.rules.val.length := hi
  have hb' : outcomes.val.length +
      ((p.rules.val.drop i.val).map fun r => r.allows.val.length).sum ≤ Usize.max := hb
  unfold decide_with_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < p.rules.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec p.rules i hlt')
    intro rule hrule
    have hdrop : p.rules.val.drop i.val = rule :: p.rules.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hrule]
    have hrmem : rule ∈ p.rules.val := by rw [hrule]; exact List.getElem_mem _
    rw [hdrop] at hb' ⊢
    simp only [List.map_cons, List.sum_cons] at hb'
    apply WP.spec_bind (apply_rule_spec inst rule method segments conds outcomes eval
      (hsegs rule hrmem) (by simp only [alloc.vec.Vec.length]; omega) heval)
    intro res hres
    obtain ⟨more, m, a⟩ := res
    obtain ⟨h1, h2, h3⟩ := hres
    dsimp only at h1 h2 h3
    have e1 : (if m = true then ok true else ok matched : Result Bool) = ok (m || matched) := by
      cases m <;> simp
    have e2 : (if a = true then ok true else ok applicable : Result Bool) = ok (a || applicable) := by
      cases a <;> simp
    change (do
      let matched1 ← (if m = true then ok true else ok matched : Result Bool)
      let applicable1 ← (if a = true then ok true else ok applicable : Result Bool)
      let i2 ← i + 1#usize
      decide_with_loop inst p method segments conds more matched1 applicable1 i2) ⦃ _ ⦄
    simp only [e1, e2, Aeneas.Std.bind_ok]
    have hmax := alloc.vec.Vec.len_ineq p.rules
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
    intro next hnext
    have hval : next.val = i.val + 1 := by simpa using hnext
    have hlen := congrArg List.length h1
    have hle := ruleOutcomes_length_le eval (ir.ruleToSpec rule) (requestToSpec method segments)
    simp only [List.length_map, List.length_append, ir.ruleToSpec] at hlen hle
    refine WP.spec_mono (decide_with_loop_spec inst p method segments conds more (m || matched)
      (a || applicable) next eval hsegs heval (by omega) (by simp only [alloc.vec.Vec.length, hval]; omega)) ?_
    intro res hres
    rw [hval] at hres
    obtain ⟨r1, r2, r3⟩ := hres
    refine ⟨?_, ?_, ?_⟩
    · rw [r1, h1]
      simp [List.append_assoc]
    · rw [r2, h2]
      cases m <;> simp [Bool.or_assoc, Bool.or_comm]
    · rw [r3, h3]
      rw [Bool.eq_iff_iff]
      simp only [List.map_cons, List.flatMap_cons, Bool.or_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, ne_eq, List.append_eq_nil_iff]
      tauto
  · rename_i hstop
    have hend : i.val = p.rules.val.length := by
      have : ¬ i.val < p.rules.val.length := hstop
      omega
    simp [hend]
termination_by p.rules.length - i.val
decreasing_by all_goals omega


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
  unfold decide_with
  refine WP.spec_bind (decide_with_loop_spec inst p method segments conds
    (alloc.vec.Vec.new Outcome) false false 0#usize eval hsegs heval (by simp)
    (by simpa using hallows)) ?_
  intro res hres
  obtain ⟨outcomes, matched, applicable⟩ := res
  obtain ⟨h1, h2, h3⟩ := hres
  dsimp only at h1 h2 h3
  dsimp only
  refine WP.spec_bind (combine_spec (alloc.vec.Vec.deref outcomes)) ?_
  intro verdict hverdict
  have houts : (alloc.vec.Vec.deref outcomes).val.map outcomeToSpec =
      Facl.outcomes eval (ir.policyToSpec p) (requestToSpec method segments) := by
    simpa [alloc.vec.Vec.deref, Facl.outcomes, ir.policyToSpec] using h1
  rw [houts] at hverdict
  have hmatched : matched = (ir.policyToSpec p).rules.any
      (fun r => (Facl.matchPattern r.pattern (requestToSpec method segments).path).isSome) := by
    simpa [ir.policyToSpec] using h2
  have happ : applicable = !(Facl.outcomes eval (ir.policyToSpec p)
      (requestToSpec method segments)).isEmpty := by
    simpa [Facl.outcomes, ir.policyToSpec] using h3
  rw [Facl.decide]
  rw [← hmatched, ← happ, ← hverdict]
  cases verdict <;> cases matched <;> cases applicable <;>
    simp [verdictToSpec, decisionToSpec, denyReasonToSpec]

end FaclCore.decide

import Facl.Theorems
import FaclCore.Funs

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore.decide

def outcomeToSpec : Outcome → Facl.Outcome
  | .Granted => .granted
  | .NotGranted => .notGranted

def verdictToSpec : Verdict → Facl.Verdict
  | .Allow => .allow
  | .Deny => .deny

/-- The loop folds the remaining outcomes into the grant flag. -/
private theorem combine_loop_spec (outs : Slice Outcome) (granted : Bool) (i : Usize)
    (hbound : i.val ≤ outs.length) :
    combine_loop outs granted i ⦃ flag =>
      flag = (granted || ((outs.val.drop i.val).map outcomeToSpec).contains .granted) ⦄ := by
  unfold combine_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hindex
    have hinc : i.val + 1 ≤ outs.length := by omega
    apply WP.spec_bind (Slice.index_usize_spec outs i hindex)
    intro outcome houtcome
    have updateSpec :
        (match outcome with
         | .Granted => ok true
         | .NotGranted => ok granted) ⦃ flag =>
          flag = (granted || (Facl.Outcome.granted == outcomeToSpec outcome)) ⦄ := by
      cases outcome <;> simp [outcomeToSpec]
    apply WP.spec_bind updateSpec
    intro flag hflag
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
      (by simpa using hinc.trans (Slice.length_ineq outs)))
    intro next hnext
    have hval : next.val = i.val + 1 := by simpa using hnext
    rw [List.drop_eq_getElem_cons hindex, ← houtcome, List.map_cons, List.contains_cons,
      ← Bool.or_assoc, ← hflag, ← hval]
    exact combine_loop_spec outs flag next (by omega)
  · rename_i hstop
    have hend : i.val = outs.length := by omega
    simp [hend]
termination_by outs.length - i.val
decreasing_by omega

/-- The extracted Rust combiner succeeds and returns the verdict of the Lean spec. -/
@[step] theorem combine_spec (outs : Slice Outcome) :
    combine outs ⦃ verdict =>
      verdictToSpec verdict = Facl.combine (outs.val.map outcomeToSpec) ⦄ := by
  unfold combine
  apply WP.spec_bind (combine_loop_spec outs false 0#usize (by simp))
  intro granted hgranted
  have hcontains : granted = (outs.val.map outcomeToSpec).contains .granted := by
    simpa using hgranted
  rw [Facl.combine, ← hcontains]
  cases granted <;> simp [verdictToSpec]

/-- The extracted Rust combiner succeeds and allows exactly when a grant is present. -/
theorem combine_allow_iff (outs : Slice Outcome) :
    combine outs ⦃ verdict => (verdict = .Allow ↔ Outcome.Granted ∈ outs.val) ⦄ := by
  refine WP.spec_mono (combine_spec outs) ?_
  intro verdict hverdict
  have hallow : verdict = .Allow ↔ verdictToSpec verdict = .allow := by
    cases verdict <;> simp [verdictToSpec]
  rw [hallow, hverdict, Facl.combine_eq_allow_iff, List.mem_map]
  constructor
  · rintro ⟨outcome, hmem, heq⟩
    cases outcome with
    | Granted => exact hmem
    | NotGranted => simp [outcomeToSpec] at heq
  · intro hmem
    exact ⟨.Granted, hmem, rfl⟩

end FaclCore.decide

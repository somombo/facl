import Facl.Spec
import Facl.Lift
import FaclCore.Funs

/-! The statements `lake comparator` holds `Facl` to. The `sorry`s are deliberate:
see "Conventions" in README.md. -/

namespace Facl

theorem combine_eq_allow_iff (outs : List Outcome) :
    combine outs = .allow ↔ Outcome.granted ∈ outs := by
  sorry

theorem match_length_of_not_rest (p : Pattern) (path : List String) (caps : List Cap)
    (hr : p.rest = false) (h : matchPattern p path = some caps) :
    path.length = p.segs.length := by
  sorry

theorem match_instantiate (p : Pattern) (path : List String) (caps : List Cap)
    (h : matchPattern p path = some caps) : instantiate p caps = some path := by
  sorry

variable {C : Type} (eval : C → List Cap → Request → Outcome)

theorem decide_eq_allow_iff (p : Policy C) (req : Request) :
    Facl.decide eval p req = .allow ↔
      ∃ r ∈ p.rules, ∃ caps, matchPattern r.pattern req.path = some caps ∧
        ∃ a ∈ r.allows, a.applies req.method = true ∧ eval a.cond caps req = .granted := by
  sorry

theorem default_deny (p : Policy C) (req : Request)
    (h : ∀ r ∈ p.rules, matchPattern r.pattern req.path = none) :
    Facl.decide eval p req = .deny .noMatchingRule := by
  sorry

theorem decide_perm (p q : Policy C) (req : Request) (h : p.rules.Perm q.rules) :
    Facl.decide eval p req = .allow ↔ Facl.decide eval q req = .allow := by
  sorry

theorem decide_mono (p q : Policy C) (req : Request)
    (h : ∀ r ∈ p.rules, r ∈ q.rules) (ha : Facl.decide eval p req = .allow) :
    Facl.decide eval q req = .allow := by
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

end FaclCore.decide

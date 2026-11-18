import Facl.Spec
namespace Facl

/-! ## Combiner -/

theorem combine_eq_allow_iff (outs : List Outcome) :
    combine outs = .allow ↔ Outcome.granted ∈ outs := by
  unfold combine
  split <;> simp_all

/-! ## Path matching -/

theorem matchGo_length (segs : List Seg) (path : List String) (caps : List Cap)
    (h : matchGo false segs path = some caps) : path.length = segs.length := by
  induction segs generalizing path caps with
  | nil => cases path <;> simp_all [matchGo]
  | cons s ss ih =>
    cases path with
    | nil => cases s <;> simp [matchGo] at h
    | cons x xs =>
      cases s with
      | lit l =>
        simp only [matchGo] at h
        split at h
        · simpa using ih _ _ h
        · simp at h
      | var =>
        simp only [matchGo, Option.map_eq_some_iff] at h
        obtain ⟨c, hc, _⟩ := h
        simpa using ih _ _ hc

/-- Without `rest`, a successful match means equal length. -/
theorem match_length_of_not_rest (p : Pattern) (path : List String) (caps : List Cap)
    (hr : p.rest = false) (h : matchPattern p path = some caps) :
    path.length = p.segs.length := by
  unfold matchPattern at h; rw [hr] at h
  exact matchGo_length _ _ _ h

/-- Instantiating the pattern with its captures rebuilds the path. -/
theorem match_instantiate (p : Pattern) (path : List String) (caps : List Cap)
    (h : matchPattern p path = some caps) : instantiate p caps = some path := by
  unfold matchPattern at h; unfold instantiate
  generalize p.rest = r at *
  generalize p.segs = segs at *
  induction segs generalizing path caps with
  | nil =>
    cases r <;> cases path <;> simp_all [matchGo, instGo] <;> subst h <;> rfl
  | cons s ss ih =>
    cases path with
    | nil => cases s <;> simp [matchGo] at h
    | cons x xs =>
      cases s with
      | lit l =>
        simp only [matchGo] at h
        split at h
        · rename_i hl; subst hl; simp [instGo, ih _ _ h]
        · simp at h
      | var =>
        simp only [matchGo, Option.map_eq_some_iff] at h
        obtain ⟨c, hc, rfl⟩ := h
        simp [instGo, ih _ _ hc]

/-! ## Decision -/

variable {C : Type} (eval : C → List Cap → Request → Outcome)

theorem mem_ruleOutcomes (r : Rule C) (req : Request) (o : Outcome) :
    o ∈ ruleOutcomes eval r req ↔
      ∃ caps, matchPattern r.pattern req.path = some caps ∧
        ∃ a ∈ r.allows, a.applies req.method = true ∧ eval a.cond caps req = o := by
  unfold ruleOutcomes
  cases h : matchPattern r.pattern req.path with
  | none => simp
  | some caps => simp [and_assoc]

/-- `decide` allows exactly when some matching rule has an applicable allow
whose condition is granted. -/
theorem decide_eq_allow_iff (p : Policy C) (req : Request) :
    Facl.decide eval p req = .allow ↔
      ∃ r ∈ p.rules, ∃ caps, matchPattern r.pattern req.path = some caps ∧
        ∃ a ∈ r.allows, a.applies req.method = true ∧ eval a.cond caps req = .granted := by
  have key : Facl.decide eval p req = .allow ↔ combine (outcomes eval p req) = .allow := by
    unfold Facl.decide
    generalize outcomes eval p req = outs
    simp only []
    cases hc : combine outs <;> simp only [reduceCtorEq]
    split <;> (try split) <;> simp
  rw [key, combine_eq_allow_iff]
  unfold outcomes
  simp only [List.mem_flatMap, mem_ruleOutcomes]

/-- Default deny. -/
theorem default_deny (p : Policy C) (req : Request)
    (h : ∀ r ∈ p.rules, matchPattern r.pattern req.path = none) :
    Facl.decide eval p req = .deny .noMatchingRule := by
  have hn : outcomes eval p req = [] := by
    unfold outcomes
    simp only [List.flatMap_eq_nil_iff]
    intro r hr
    unfold ruleOutcomes; rw [h r hr]
  have hm : (p.rules.any fun r => (matchPattern r.pattern req.path).isSome) = false := by
    simp only [List.any_eq_false]
    intro r hr; rw [h r hr]; simp
  unfold Facl.decide
  simp [hn, hm, combine]

/-- Rule order is irrelevant. -/
theorem decide_perm (p q : Policy C) (req : Request) (h : p.rules.Perm q.rules) :
    Facl.decide eval p req = .allow ↔ Facl.decide eval q req = .allow := by
  rw [decide_eq_allow_iff, decide_eq_allow_iff]
  constructor <;> rintro ⟨r, hr, rest⟩
  · exact ⟨r, h.subset hr, rest⟩
  · exact ⟨r, h.symm.subset hr, rest⟩

/-- Adding rules never revokes access. -/
theorem decide_mono (p q : Policy C) (req : Request)
    (h : ∀ r ∈ p.rules, r ∈ q.rules) (ha : Facl.decide eval p req = .allow) :
    Facl.decide eval q req = .allow := by
  rw [decide_eq_allow_iff] at ha ⊢
  obtain ⟨r, hr, rest⟩ := ha
  exact ⟨r, h r hr, rest⟩

end Facl

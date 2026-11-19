import Facl.Spec
namespace Facl

/-! ## Combiner -/

theorem combine_eq_allow_iff (outs : List Outcome) :
    combine outs = .allow ↔ Outcome.granted ∈ outs := by
  unfold combine
  split <;> simp_all

/-! ## Path matching -/

theorem matchGo_length {α : Type} [DecidableEq α] (segs : List (Seg α)) (path : List α) (caps : List (Cap α))
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
theorem match_length_of_not_rest {α : Type} [DecidableEq α] (p : Pattern α) (path : List α) (caps : List (Cap α))
    (hr : p.rest = false) (h : matchPattern p path = some caps) :
    path.length = p.segs.length := by
  unfold matchPattern at h; rw [hr] at h
  exact matchGo_length _ _ _ h

/-- Instantiating the pattern with its captures rebuilds the path. -/
theorem match_instantiate {α : Type} [DecidableEq α] (p : Pattern α) (path : List α) (caps : List (Cap α))
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

variable {α : Type} [DecidableEq α] {C : Type} (eval : C → List (Cap α) → Request α → Outcome)

theorem mem_ruleOutcomes (r : Rule α C) (req : Request α) (o : Outcome) :
    o ∈ ruleOutcomes eval r req ↔
      ∃ caps, matchPattern r.pattern req.path = some caps ∧
        ∃ a ∈ r.allows, a.applies req.method = true ∧ eval a.cond caps req = o := by
  unfold ruleOutcomes
  cases h : matchPattern r.pattern req.path with
  | none => simp
  | some caps => simp [and_assoc]

/-- `decide` allows exactly when some matching rule has an applicable allow
whose condition is granted. -/
theorem decide_eq_allow_iff (p : Policy α C) (req : Request α) :
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
theorem default_deny (p : Policy α C) (req : Request α)
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
theorem decide_perm (p q : Policy α C) (req : Request α) (h : p.rules.Perm q.rules) :
    Facl.decide eval p req = .allow ↔ Facl.decide eval q req = .allow := by
  rw [decide_eq_allow_iff, decide_eq_allow_iff]
  constructor <;> rintro ⟨r, hr, rest⟩
  · exact ⟨r, h.subset hr, rest⟩
  · exact ⟨r, h.symm.subset hr, rest⟩

/-- Adding rules never revokes access. -/
theorem decide_mono (p q : Policy α C) (req : Request α)
    (h : ∀ r ∈ p.rules, r ∈ q.rules) (ha : Facl.decide eval p req = .allow) :
    Facl.decide eval q req = .allow := by
  rw [decide_eq_allow_iff] at ha ⊢
  obtain ⟨r, hr, rest⟩ := ha
  exact ⟨r, h r hr, rest⟩

end Facl

namespace Facl

mutual
private theorem lowerMatch_perm {α A C : Type} [DecidableEq α] (reserved : List α)
    (compile : Option A → List α → Except LowerError C) (depth : Nat) (segs : List (Seg α))
    (names : List α) (rules : List (Rule α C)) :
    (m : Match α A) → lowerMatch reserved compile depth segs names m = .ok rules →
    ((rules.flatMap (·.allows)).map (·.methods)).Perm m.allowMethods
  | .mk pattern body, h => by
    simp only [lowerMatch] at h
    split at h
    · cases h
    · cases hp : lowerPattern reserved pattern segs names with
      | error e => simp [hp, bind, Except.bind] at h
      | ok v =>
        obtain ⟨segs', names', rest⟩ := v
        cases ha : lowerAllows compile names' rest body with
        | error e => simp [hp, ha, bind, Except.bind] at h
        | ok allows =>
          cases hn : lowerNested reserved compile (depth + 1) segs' names' body with
          | error e => simp [hp, ha, hn, bind, Except.bind] at h
          | ok nested =>
            simp only [hp, ha, hn, bind, Except.bind] at h
            cases h
            have := lowerNested_perm reserved compile (depth + 1) segs' names' rest allows
              nested body ha hn
            by_cases he : allows.isEmpty
            · simp [List.isEmpty_iff.mp he, Match.allowMethods] at this ⊢
              exact this
            · simpa [he, Match.allowMethods] using this

private theorem lowerNested_perm {α A C : Type} [DecidableEq α] (reserved : List α)
    (compile : Option A → List α → Except LowerError C) (depth : Nat) (segs : List (Seg α))
    (names : List α) (rest : Bool) (allows : List (Allow C)) (rules : List (Rule α C)) :
    (items : List (Item α A)) → lowerAllows compile names rest items = .ok allows →
    lowerNested reserved compile depth segs names items = .ok rules →
    (allows.map (·.methods) ++ (rules.flatMap (·.allows)).map (·.methods)).Perm
      (Match.bodyAllowMethods items)
  | [], ha, hn => by
    simp only [lowerAllows, lowerNested] at ha hn
    cases ha; cases hn
    simp [Match.bodyAllowMethods]
  | .allow a :: items, ha, hn => by
    simp only [lowerAllows, lowerNested] at ha hn
    cases hc : compile a.cond names with
    | error e => simp [hc, bind, Except.bind] at ha
    | ok c =>
      cases hl : lowerAllows compile names rest items with
      | error e => simp [hc, hl, bind, Except.bind] at ha
      | ok as =>
        simp only [hc, hl, bind, Except.bind] at ha
        cases ha
        have := lowerNested_perm reserved compile depth segs names rest as rules items hl hn
        simpa [Match.bodyAllowMethods] using this
  | .nested m :: items, ha, hn => by
    simp only [lowerAllows, lowerNested] at ha hn
    split at ha
    · cases ha
    · cases hm : lowerMatch reserved compile depth segs names m with
      | error e => simp [hm, bind, Except.bind] at hn
      | ok rm =>
        cases hr : lowerNested reserved compile depth segs names items with
        | error e => simp [hm, hr, bind, Except.bind] at hn
        | ok more =>
          simp only [hm, hr, bind, Except.bind] at hn
          cases hn
          have h1 := lowerMatch_perm reserved compile depth segs names rm m hm
          have h2 := lowerNested_perm reserved compile depth segs names rest allows more items ha hr
          simp only [Match.bodyAllowMethods, List.flatMap_append, List.map_append]
          exact (List.perm_append_comm_assoc _ _ _).trans (h1.append h2)
end

private theorem lower_perm {α A C : Type} [DecidableEq α] (reserved : List α)
    (compile : Option A → List α → Except LowerError C) :
    (blocks : List (Match α A)) → (rs : List (List (Rule α C))) →
    blocks.mapM (lowerMatch reserved compile 1 [] []) = .ok rs →
    ((rs.flatten.flatMap (·.allows)).map (·.methods)).Perm (blocks.flatMap Match.allowMethods)
  | [], rs, h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | m :: ms, rs, h => by
    simp only [List.mapM_cons] at h
    cases hm : lowerMatch reserved compile 1 [] [] m with
    | error e => simp [hm, bind, Except.bind] at h
    | ok r =>
      cases hr : ms.mapM (lowerMatch reserved compile 1 [] []) with
      | error e => simp [hm, hr, bind, Except.bind] at h
      | ok rest =>
        simp only [hm, hr, bind, Except.bind] at h
        cases h
        simpa using (lowerMatch_perm reserved compile 1 [] [] r m hm).append
          (lower_perm reserved compile ms rest hr)

theorem lower_allow_methods {α A C : Type} [DecidableEq α] (reserved : List α)
    (compile : Option A → List α → Except LowerError C) (svc : Service α A) (p : Policy α C)
    (h : lower reserved compile svc = .ok p) :
    ((p.rules.flatMap (·.allows)).map (·.methods)).Perm (svc.blocks.flatMap Match.allowMethods) := by
  simp only [lower, bind, Except.bind] at h
  cases hm : svc.blocks.mapM (lowerMatch reserved compile 1 [] []) with
  | error e => simp [hm] at h
  | ok rs =>
    simp only [hm] at h
    cases h
    exact lower_perm reserved compile svc.blocks rs hm

end Facl

import Facl.Theorems
import Facl.Lift
import FaclCore.Funs

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore

private theorem bytes_eq_loop_spec (a b : Slice U8) (i : Usize) (hlen : a.length = b.length)
    (hi : i.val ≤ a.length) :
    value.bytes_eq_loop a b i ⦃ r => r = decide (a.val.drop i.val = b.val.drop i.val) ⦄ := by
  unfold value.bytes_eq_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    have hb : i.val < b.length := by omega
    apply WP.spec_bind (Slice.index_usize_spec a i hlt)
    intro x hx
    apply WP.spec_bind (Slice.index_usize_spec b i hb)
    intro y hy
    split
    · rename_i hne
      have : ¬ x = y := by simpa using hne
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hb, ← hx, ← hy]
      simp [this]
    · rename_i hne
      have hxy : x = y := UScalar.eq_of_val_eq (by simpa using hne)
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ a.length by omega).trans (Slice.length_ineq a)))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hb, ← hx, ← hy, ← hval]
      simp only [List.cons.injEq, hxy, true_and]
      exact WP.spec_mono (bytes_eq_loop_spec a b next hlen (by omega)) (fun r hr => by
        simpa [hval] using hr)
  · rename_i hstop
    have hend : i.val = a.length := by omega
    simp [hend, hlen]
termination_by a.length - i.val
decreasing_by omega

private theorem bytes_eq_spec (a b : Slice U8) :
    value.bytes_eq a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold value.bytes_eq
  dsimp only
  split
  · rename_i h
    have hl : a.length ≠ b.length := by simpa using h
    have : a.val ≠ b.val := fun e => hl (by simp [Slice.length, e])
    simp [this]
  · rename_i h
    have hl : a.length = b.length := by simpa using h
    exact WP.spec_mono (bytes_eq_loop_spec a b 0#usize hl (by simp)) (by simp)


private theorem copy_bytes_loop_spec (s : Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ s.length) (hb : out.length + (s.length - i.val) ≤ Usize.max) :
    path.copy_bytes_loop s out i ⦃ v => v.val = out.val ++ s.val.drop i.val ⦄ := by
  unfold path.copy_bytes_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  have hb' : out.val.length + (s.val.length - i.val) ≤ Usize.max := hb
  split
  · rename_i hlt
    have hlt' : i.val < s.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec s i hlt)
    intro x hx
    apply WP.spec_bind (alloc.vec.Vec.push_spec out x (by omega))
    intro out1 hout1
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
      (by simpa using (show i.val + 1 ≤ s.length by omega).trans (Slice.length_ineq s)))
    intro next hnext
    have hval : next.val = i.val + 1 := by simpa using hnext
    refine WP.spec_mono (copy_bytes_loop_spec s out1 next (by omega)
      (by simp only [alloc.vec.Vec.length, hout1, hval]; simp; omega)) ?_
    intro v hv
    rw [hv, hout1, hval, List.drop_eq_getElem_cons hlt, ← hx]
    simp
  · rename_i hstop
    have hend : i.val = s.length := by omega
    simp [hend]
termination_by s.length - i.val
decreasing_by omega

private theorem copy_bytes_spec (s : Slice U8) :
    path.copy_bytes s ⦃ v => v.val = s.val ⦄ := by
  unfold path.copy_bytes
  refine WP.spec_mono (copy_bytes_loop_spec s (alloc.vec.Vec.new U8) 0#usize (by simp)
    (by have := Slice.length_ineq s; simp)) ?_
  intro v hv
  simpa using hv

private theorem tail_loop_spec (segments : Slice (alloc.vec.Vec U8))
    (tail : alloc.vec.Vec (alloc.vec.Vec U8)) (j : Usize)
    (hj : j.val ≤ segments.length) (hb : tail.length + (segments.length - j.val) ≤ Usize.max) :
    path.match_pattern_loop0_loop0 segments tail j ⦃ t =>
      t.val = tail.val ++ segments.val.drop j.val ⦄ := by
  unfold path.match_pattern_loop0_loop0
  simp only [UScalar.lt_equiv, Slice.len_val]
  have hb' : tail.val.length + (segments.val.length - j.val) ≤ Usize.max := hb
  split
  · rename_i hlt
    have hlt' : j.val < segments.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec segments j hlt)
    intro seg hseg
    apply WP.spec_bind (copy_bytes_spec (alloc.vec.Vec.deref seg))
    intro copy hcopy
    have hcopy' : copy = seg := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hcopy)
    apply WP.spec_bind (alloc.vec.Vec.push_spec tail copy (by omega))
    intro tail1 htail1
    apply WP.spec_bind (Usize.add_spec (x := j) (y := 1#usize)
      (by simpa using (show j.val + 1 ≤ segments.length by omega).trans (Slice.length_ineq segments)))
    intro next hnext
    have hval : next.val = j.val + 1 := by simpa using hnext
    refine WP.spec_mono (tail_loop_spec segments tail1 next (by omega)
      (by simp only [alloc.vec.Vec.length, htail1, hval]; simp; omega)) ?_
    intro t ht
    rw [ht, htail1, hval, List.drop_eq_getElem_cons hlt, ← hseg, hcopy']
    simp
  · rename_i hstop
    have hend : j.val = segments.length := by omega
    simp [hend]
termination_by segments.length - j.val
decreasing_by omega


private theorem match_loop_spec (v : alloc.vec.Vec ir.Seg) (b : Bool)
    (segments : Slice (alloc.vec.Vec U8)) (captures : alloc.vec.Vec path.Capture) (i : Usize)
    (hi : i.val ≤ v.length) (hn : v.length < Usize.max)
    (hlen : if b then v.length ≤ segments.length else segments.length = v.length)
    (hcap : captures.length ≤ i.val) :
    path.match_pattern_loop0 v b segments captures i ⦃ r =>
      r.map (·.val.map path.captureToSpec) =
        (Facl.matchGo b ((v.val.drop i.val).map ir.segToSpec)
          ((segments.val.drop i.val).map (·.val))).map
          (captures.val.map path.captureToSpec ++ ·) ⦄ := by
  have hlen' : v.val.length ≤ segments.val.length ∧ (b = false → segments.val.length = v.val.length) := by
    cases b <;> simp at hlen <;> simp [hlen]
  have hcap' : captures.val.length ≤ i.val := hcap
  have hn' : v.val.length < Usize.max := hn
  have hi' : i.val ≤ v.val.length := hi
  unfold path.match_pattern_loop0
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < v.val.length := hlt
    have hseg : i.val < segments.val.length := by omega
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec v i hlt')
    intro s hs
    have hdv : v.val.drop i.val = s :: v.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hs]
    have hds : segments.val.drop i.val = segments.val[i.val] :: segments.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hseg
    have hmv : (v.val.drop i.val).map ir.segToSpec =
        ir.segToSpec s :: (v.val.drop (i.val + 1)).map ir.segToSpec := by rw [hdv, List.map_cons]
    have hmsegs : (segments.val.drop i.val).map (·.val) =
        segments.val[i.val].val :: (segments.val.drop (i.val + 1)).map (·.val) := by
      rw [hds, List.map_cons]
    cases s with
    | Lit lit =>
      dsimp only
      apply WP.spec_bind (Slice.index_usize_spec segments i hseg)
      intro x hx
      apply WP.spec_bind (bytes_eq_spec (alloc.vec.Vec.deref lit) (alloc.vec.Vec.deref x))
      intro eq heq
      split
      · rename_i hb
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
          (by simpa using (show i.val + 1 ≤ v.val.length by omega).trans (Slice.length_ineq v.slice)))
        intro next hnext
        have hval : next.val = i.val + 1 := by simpa using hnext
        have hlx : lit.val = x.val := by simpa [alloc.vec.Vec.deref, hb] using heq
        refine WP.spec_mono (match_loop_spec v b segments captures next (by omega) hn hlen
          (by omega)) ?_
        intro r hr
        rw [hr, hval, hmv, hmsegs, ← hx]
        simp only [Facl.matchGo, ir.segToSpec, hlx, ite_true]
      · rename_i hb
        have hlx : ¬ lit.val = x.val := by simpa [alloc.vec.Vec.deref, hb] using heq
        rw [hmv, hmsegs, ← hx]
        simp [Facl.matchGo, ir.segToSpec, hlx]
    | Var =>
      dsimp only
      apply WP.spec_bind (Slice.index_usize_spec segments i hseg)
      intro x hx
      apply WP.spec_bind (copy_bytes_spec (alloc.vec.Vec.deref x))
      intro copy hcopy
      apply WP.spec_bind (alloc.vec.Vec.push_spec captures (path.Capture.One copy) (by omega))
      intro caps1 hcaps1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ v.val.length by omega).trans (Slice.length_ineq v.slice)))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      refine WP.spec_mono (match_loop_spec v b segments caps1 next (by omega) hn hlen
        (by simp only [alloc.vec.Vec.length, hcaps1, hval]; simp; omega)) ?_
      intro r hr
      rw [hr, hval, hmv, hmsegs, ← hx, hcaps1]
      have hcx : copy.val = x.val := by simpa [alloc.vec.Vec.deref] using hcopy
      simp only [ir.segToSpec, Facl.matchGo]
      generalize Facl.matchGo b (List.map ir.segToSpec (List.drop (i.val + 1) v.val))
        (List.map (·.val) (List.drop (i.val + 1) segments.val)) = T
      cases T <;>
        simp [hcx, path.captureToSpec]
  · rename_i hstop
    have hstop' : ¬ i.val < v.val.length := hstop
    have hend : i.val = v.val.length := by omega
    have hdrop : v.val.drop i.val = [] := by simp [hend]
    cases b
    · have : segments.val.drop i.val = [] := by simp [hend, hlen'.2]
      simp [hdrop, this, Facl.matchGo]
    · apply WP.spec_bind (tail_loop_spec segments (alloc.vec.Vec.new (alloc.vec.Vec U8))
        (alloc.vec.Vec.len v) (by simp; omega) (by have := Slice.length_ineq segments; simp; omega))
      intro tail htail
      apply WP.spec_bind (alloc.vec.Vec.push_spec captures (path.Capture.Rest tail) (by omega))
      intro caps1 hcaps1
      simp [Facl.matchGo, hcaps1, htail, hend, path.captureToSpec]
termination_by v.length - i.val
decreasing_by all_goals omega


private theorem matchGo_none (b : Bool) (segs : List (Facl.Seg (List U8))) (path : List (List U8))
    (h : if b then path.length < segs.length else path.length ≠ segs.length) :
    Facl.matchGo b segs path = none := by
  induction segs generalizing path with
  | nil =>
    cases b <;> cases path <;> simp_all [Facl.matchGo]
  | cons sg ss ih =>
    cases path with
    | nil => cases sg <;> simp [Facl.matchGo]
    | cons x xs =>
      have h' : if b then xs.length < ss.length else xs.length ≠ ss.length := by
        cases b <;> simp at h ⊢ <;> omega
      cases sg <;> simp [Facl.matchGo, ih xs h']

namespace path

@[step] theorem match_pattern_spec (p : ir.Pattern) (segments : Slice (alloc.vec.Vec U8))
    (hsegs : p.segs.val.length < Usize.max) :
    match_pattern p segments ⦃ caps =>
      caps.map (fun v => v.val.map captureToSpec) =
        Facl.matchPattern (ir.patternToSpec p) (segmentsToSpec segments) ⦄ := by
  unfold match_pattern
  have hlen : (segmentsToSpec segments).length = segments.val.length := by simp [segmentsToSpec]
  have hpat : Facl.matchPattern (ir.patternToSpec p) (segmentsToSpec segments) =
      Facl.matchGo p.rest (p.segs.val.map ir.segToSpec) (segmentsToSpec segments) := rfl
  have hseg : p.segs.val.length < Usize.max := hsegs
  have hseg' := Slice.length_ineq segments
  rw [hpat]
  cases hr : p.rest
  · simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok]
    split
    · rename_i hw
      have hw' : segments.val.length ≠ p.segs.val.length := by simpa using hw
      simp only [WP.spec_ok]
      rw [matchGo_none false _ _ (by simpa [hlen] using hw')]
      rfl
    · rename_i hw
      have hw' : segments.val.length = p.segs.val.length := by simpa using hw
      refine WP.spec_mono (match_loop_spec p.segs false segments (alloc.vec.Vec.new Capture) 0#usize
        (by simp) hsegs (by simpa using hw') (by simp)) ?_
      intro r hr'
      simpa [segmentsToSpec] using hr'
  · simp only [↓reduceIte, Aeneas.Std.bind_ok]
    split
    · rename_i hw
      have hw' : segments.val.length < p.segs.val.length := by simpa using hw
      simp only [WP.spec_ok]
      rw [matchGo_none true _ _ (by simpa [hlen] using hw')]
      rfl
    · rename_i hw
      have hw' : ¬ segments.val.length < p.segs.val.length := by simpa using hw
      refine WP.spec_mono (match_loop_spec p.segs true segments (alloc.vec.Vec.new Capture) 0#usize
        (by simp) hsegs (by simp; omega) (by simp)) ?_
      intro r hr'
      simpa [segmentsToSpec] using hr'

end path

end FaclCore

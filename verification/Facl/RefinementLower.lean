import Facl.Spec
import Facl.Lift
import FaclCore.Funs

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore.lower

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

@[step] private theorem copy_bytes_spec (s : Slice U8) :
    path.copy_bytes s ⦃ v => v.val = s.val ⦄ := by
  unfold path.copy_bytes
  refine WP.spec_mono (copy_bytes_loop_spec s (alloc.vec.Vec.new U8) 0#usize (by simp)
    (by have := Slice.length_ineq s; simp)) ?_
  intro v hv
  simpa using hv

private theorem slot_of_loop_spec (names : Slice (alloc.vec.Vec U8)) (nm : Slice U8)
    (i : Usize) (hi : i.val ≤ names.length) :
    slot_of_loop names nm i ⦃ o =>
      o.isSome = decide (nm.val ∈ (names.val.drop i.val).map (·.val)) ⦄ := by
  unfold slot_of_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    apply WP.spec_bind (Slice.index_usize_spec names i hlt)
    intro v hv
    apply WP.spec_bind (bytes_eq_spec (alloc.vec.Vec.deref v) nm)
    intro b hb
    have hdrop : names.val.drop i.val = v :: names.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt, hv]
    have hb2 : b = decide (v.val = nm.val) := by simpa [alloc.vec.Vec.deref] using hb
    split
    · rename_i hbt
      simp [lift, hdrop, hb2] at hbt ⊢
      simp [hbt]
    · rename_i hbt
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ names.length by omega).trans (Slice.length_ineq names)))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      refine WP.spec_mono (slot_of_loop_spec names nm next (by omega)) ?_
      intro o ho
      have hne : ¬ v.val = nm.val := by simpa [hb2] using hbt
      rw [ho, hval, hdrop]
      simp [Ne.symm hne]
  · rename_i hstop
    have hend : i.val = names.length := by omega
    simp [hend]
termination_by names.length - i.val
decreasing_by omega

@[step] private theorem slot_of_spec (names : Slice (alloc.vec.Vec U8)) (nm : Slice U8) :
    slot_of names nm ⦃ o => o.isSome = decide (nm.val ∈ names.val.map (·.val)) ⦄ := by
  simpa using slot_of_loop_spec names nm 0#usize (by simp)

private theorem reservedNames_eq : reservedNames =
    [[114#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8],
     [99#u8, 111#u8, 110#u8, 116#u8, 101#u8, 120#u8, 116#u8]] := by
  rfl

@[step] private theorem is_reserved_spec (nm : Slice U8) :
    is_reserved nm ⦃ r => r = decide (nm.val ∈ reservedNames) ⦄ := by
  by_cases h : nm.val.length = 7
  · match hv : nm.val, h with
    | [a0, a1, a2, a3, a4, a5, a6], _ =>
      have hs : Slice.len nm = 7#usize := by
        apply UScalar.eq_of_val_eq; simp [hv]
      unfold is_reserved
      simp only [hs, ↓reduceIte]
      simp [Slice.index_usize, hv]
      rw [reservedNames_eq]
      clear hv h hs
      simp only [UScalar.eq_equiv, List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false]
      simp
      generalize a0.val = n0
      generalize a1.val = n1
      generalize a2.val = n2
      generalize a3.val = n3
      generalize a4.val = n4
      generalize a5.val = n5
      generalize a6.val = n6
      by_cases hP : n0 = 114 ∧ n1 = 101 ∧ n2 = 113 ∧ n3 = 117 ∧ n4 = 101 ∧ n5 = 115 ∧ n6 = 116
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hP
        simp
      by_cases hQ : n0 = 99 ∧ n1 = 111 ∧ n2 = 110 ∧ n3 = 116 ∧ n4 = 101 ∧ n5 = 120 ∧ n6 = 116
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hQ
        simp
      simp +contextual
      split_ifs <;> simp_all
  · have hs : ¬ Slice.len nm = 7#usize := fun e => h (by simpa [Slice.len_val, Slice.length] using congrArg UScalar.val e)
    unfold is_reserved
    simp only [hs, ↓reduceIte]
    simp only [WP.spec_ok]
    have : nm.val ∉ reservedNames := by
      rw [reservedNames_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      constructor <;> intro e <;> exact h (by rw [e]; rfl)
    simp [this]

@[step] private theorem bind_spec (names : alloc.vec.Vec (alloc.vec.Vec U8)) (nm : Slice U8)
    (span : ast.Span) (hn : names.length < Usize.max) :
    bind names nm span ⦃ res =>
      resultToSpec (fun _ => res.2.val.map (·.val)) res.1 =
        Facl.bindName reservedNames (names.val.map (·.val)) nm.val ⦄ := by
  unfold bind
  apply WP.spec_bind (is_reserved_spec nm)
  intro b hb
  split
  · rename_i h
    simp [hb] at h
    simp [fail, h, Facl.bindName, resultToSpec, kindToSpec]
  · rename_i h
    have h' : nm.val ∉ reservedNames := by simpa [hb] using h
    apply WP.spec_bind (slot_of_spec (alloc.vec.Vec.deref names) nm)
    intro o ho
    simp only [core.option.Option.is_some]
    have ho' : o.isSome = decide (nm.val ∈ names.val.map (·.val)) := by simpa [alloc.vec.Vec.deref] using ho
    by_cases hd : o.isSome = true
    · simp only [hd, ↓reduceIte]
      have hm : nm.val ∈ names.val.map (·.val) := by simpa [ho'] using hd
      simp [fail, hm, h', Facl.bindName, resultToSpec, kindToSpec]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hm : nm.val ∉ names.val.map (·.val) := by simpa [ho'] using hd
      apply WP.spec_bind (copy_bytes_spec nm)
      intro v hv
      apply WP.spec_bind (alloc.vec.Vec.push_spec names v hn)
      intro names1 hn1
      simp [h', hm, Facl.bindName, resultToSpec, hn1, hv]

private theorem copy_names_loop_spec (names : Slice (alloc.vec.Vec U8))
    (out : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hi : i.val ≤ names.length)
    (hb : out.length + (names.length - i.val) ≤ Usize.max) :
    copy_names_loop names out i ⦃ v => v.val = out.val ++ names.val.drop i.val ⦄ := by
  unfold copy_names_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  have hb' : out.val.length + (names.val.length - i.val) ≤ Usize.max := hb
  split
  · rename_i hlt
    have hlt' : i.val < names.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec names i hlt)
    intro x hx
    apply WP.spec_bind (copy_bytes_spec (alloc.vec.Vec.deref x))
    intro copy hcopy
    have hcopy' : copy = x := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hcopy)
    apply WP.spec_bind (alloc.vec.Vec.push_spec out copy (by omega))
    intro out1 hout1
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
      (by simpa using (show i.val + 1 ≤ names.length by omega).trans (Slice.length_ineq names)))
    intro next hnext
    have hval : next.val = i.val + 1 := by simpa using hnext
    refine WP.spec_mono (copy_names_loop_spec names out1 next (by omega)
      (by simp only [alloc.vec.Vec.length, hout1, hval]; simp; omega)) ?_
    intro v hv
    rw [hv, hout1, hval, List.drop_eq_getElem_cons hlt, ← hx, hcopy']
    simp
  · rename_i hstop
    have hend : i.val = names.length := by omega
    simp [hend]
termination_by names.length - i.val
decreasing_by omega

@[step] private theorem copy_names_spec (names : Slice (alloc.vec.Vec U8)) :
    copy_names names ⦃ v => v.val = names.val ⦄ := by
  unfold copy_names
  refine WP.spec_mono (copy_names_loop_spec names (alloc.vec.Vec.new _) 0#usize (by simp)
    (by have := Slice.length_ineq names; simp)) ?_
  intro v hv
  simpa using hv

private theorem copy_segs_loop_spec (segs : Slice ir.Seg) (out : alloc.vec.Vec ir.Seg)
    (i : Usize) (hi : i.val ≤ segs.length) (hb : out.length + (segs.length - i.val) ≤ Usize.max) :
    copy_segs_loop segs out i ⦃ v => v.val = out.val ++ segs.val.drop i.val ⦄ := by
  unfold copy_segs_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  have hb' : out.val.length + (segs.val.length - i.val) ≤ Usize.max := hb
  split
  · rename_i hlt
    have hlt' : i.val < segs.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec segs i hlt)
    intro x hx
    have hpush : ∀ y : ir.Seg, y = x → (do
        let out1 ← alloc.vec.Vec.push out y
        let i2 ← i + 1#usize
        copy_segs_loop segs out1 i2) ⦃ v => v.val = out.val ++ segs.val.drop i.val ⦄ := by
      intro y hy
      apply WP.spec_bind (alloc.vec.Vec.push_spec out y (by omega))
      intro out1 hout1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ segs.length by omega).trans (Slice.length_ineq segs)))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      refine WP.spec_mono (copy_segs_loop_spec segs out1 next (by omega)
        (by simp only [alloc.vec.Vec.length, hout1, hval]; simp; omega)) ?_
      intro v hv
      rw [hv, hout1, hval, List.drop_eq_getElem_cons hlt, ← hx, hy]
      simp
    cases x with
    | Lit s1 =>
      simp only [Aeneas.Std.bind_assoc]
      apply WP.spec_bind (copy_bytes_spec (alloc.vec.Vec.deref s1))
      intro copy hcopy
      have hcopy' : copy = s1 := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hcopy)
      exact hpush _ (by rw [hcopy'])
    | Var => exact hpush _ rfl
  · rename_i hstop
    have hend : i.val = segs.length := by omega
    simp [hend]
termination_by segs.length - i.val
decreasing_by omega

@[step] private theorem copy_segs_spec (segs : Slice ir.Seg) :
    copy_segs segs ⦃ v => v.val = segs.val ⦄ := by
  unfold copy_segs
  refine WP.spec_mono (copy_segs_loop_spec segs (alloc.vec.Vec.new _) 0#usize (by simp)
    (by have := Slice.length_ineq segs; simp)) ?_
  intro v hv
  simpa using hv

private theorem lower_pattern_loop_spec (pattern : Slice ast.PatSeg) (span : ast.Span)
    (segs : alloc.vec.Vec ir.Seg) (names : alloc.vec.Vec (alloc.vec.Vec U8)) (rest : Bool)
    (i : Usize) (hi : i.val ≤ pattern.length)
    (hs : segs.length + (pattern.length - i.val) ≤ Usize.max)
    (hn : names.length + (pattern.length - i.val) ≤ Usize.max) :
    lower_pattern_loop pattern span segs names rest i ⦃ res =>
      resultToSpec (fun b => (res.2.1.val.map ir.segToSpec, res.2.2.val.map (·.val), b)) res.1 =
        (Facl.lowerPattern reservedNames ((pattern.val.drop i.val).map ast.patSegToSpec)
          (segs.val.map ir.segToSpec) (names.val.map (·.val))).map
          (fun x => (x.1, x.2.1, x.2.2 || rest)) ⦄ := by
  have hs' : segs.val.length + (pattern.val.length - i.val) ≤ Usize.max := hs
  have hn' : names.val.length + (pattern.val.length - i.val) ≤ Usize.max := hn
  unfold lower_pattern_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    have hlt' : i.val < pattern.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec pattern i hlt)
    intro ps hps
    have hdrop : pattern.val.drop i.val = ps :: pattern.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hps]
    have hmax := Slice.length_ineq pattern
    have hlen : pattern.length = pattern.val.length := rfl
    rw [hdrop, List.map_cons]
    cases ps with
    | Lit s1 =>
      dsimp only
      apply WP.spec_bind (copy_bytes_spec (alloc.vec.Vec.deref s1))
      intro copy hcopy
      apply WP.spec_bind (alloc.vec.Vec.push_spec segs (ir.Seg.Lit copy) (by omega))
      intro segs1 hsegs1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ pattern.length by omega).trans hmax))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      have hseg : segs1.val.map ir.segToSpec =
          segs.val.map ir.segToSpec ++ [Facl.Seg.lit s1.val] := by
        simp [hsegs1, ir.segToSpec, hcopy, alloc.vec.Vec.deref]
      refine WP.spec_mono (lower_pattern_loop_spec pattern span segs1 names rest next (by omega)
        (by simp only [alloc.vec.Vec.length, hsegs1, hval]; simp; omega)
        (by omega)) ?_
      intro res hres
      rw [hres, hseg, hval]
      simp only [ast.patSegToSpec, Facl.lowerPattern]
    | Var n =>
      dsimp only
      apply WP.spec_bind (bind_spec names (alloc.vec.Vec.deref n) span (by omega))
      intro res hres
      obtain ⟨r, names1⟩ := res
      replace hres : resultToSpec (fun _ => names1.val.map (·.val)) r =
          Facl.bindName reservedNames (names.val.map (·.val)) n.val := by
        simpa [alloc.vec.Vec.deref] using hres
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [ast.patSegToSpec, Facl.lowerPattern]
        rw [← hres]
        rfl
      | Ok u =>
        have hl1 : names1.val.length = names.val.length + 1 := by
          unfold Facl.bindName at hres
          split_ifs at hres <;> simp [resultToSpec] at hres
          simpa using congrArg List.length hres
        apply WP.spec_bind (core.result.Result.Insts.CoreOpsTry.branch.step_spec
          (core.result.Result.Ok u : core.result.Result Unit LowerError))
        intro cf hcf
        obtain rfl : cf = .Continue u := hcf
        apply WP.spec_bind (alloc.vec.Vec.push_spec segs ir.Seg.Var (by omega))
        intro segs1 hsegs1
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
          (by simpa using (show i.val + 1 ≤ pattern.length by omega).trans hmax))
        intro next hnext
        have hval : next.val = i.val + 1 := by simpa using hnext
        have hseg : segs1.val.map ir.segToSpec = segs.val.map ir.segToSpec ++ [Facl.Seg.var] := by
          simp [hsegs1, ir.segToSpec]
        refine WP.spec_mono (lower_pattern_loop_spec pattern span segs1 names1 rest next (by omega)
          (by simp only [alloc.vec.Vec.length, hsegs1, hval]; simp; omega)
          (by simp only [alloc.vec.Vec.length, hl1, hval]; omega)) ?_
        intro res hres'
        rw [hres', hseg, hval]
        simp only [ast.patSegToSpec, Facl.lowerPattern]
        rw [← hres]
        rfl
    | Rest n =>
      dsimp only
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize)
        (by simpa using (show i.val + 1 ≤ pattern.length by omega).trans hmax))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      by_cases hlast : next.val = pattern.val.length
      · have hc : ¬ (next != Slice.len pattern) = true := by
          simp [UScalar.eq_equiv, hlast]
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        apply WP.spec_bind (bind_spec names (alloc.vec.Vec.deref n) span (by omega))
        intro res hres
        obtain ⟨r, names1⟩ := res
        replace hres : resultToSpec (fun _ => names1.val.map (·.val)) r =
            Facl.bindName reservedNames (names.val.map (·.val)) n.val := by
          simpa [alloc.vec.Vec.deref] using hres
        have hnil : (pattern.val.map ast.patSegToSpec).drop (i.val + 1) = [] := by
          rw [← List.map_drop, List.drop_eq_nil_of_le (by omega)]; rfl
        cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          simp only [ast.patSegToSpec, Facl.lowerPattern, hnil, ne_eq, not_true_eq_false,
            ↓reduceIte]
          rw [← hres]
          rfl
        | Ok u =>
          apply WP.spec_bind (core.result.Result.Insts.CoreOpsTry.branch.step_spec
            (core.result.Result.Ok u : core.result.Result Unit LowerError))
          intro cf hcf
          obtain rfl : cf = .Continue u := hcf
          have hl1 : names1.val.length = names.val.length + 1 := by
            unfold Facl.bindName at hres
            split_ifs at hres <;> simp [resultToSpec] at hres
            simpa using congrArg List.length hres
          have hend : next.val = pattern.val.length := hlast
          have hl2 := alloc.vec.Vec.len_ineq names1
          refine WP.spec_mono (lower_pattern_loop_spec pattern span segs names1 true next
            (by omega) (by omega) (by simp only [alloc.vec.Vec.length]; omega)) ?_
          intro res hres'
          rw [hres']
          simp only [ast.patSegToSpec, Facl.lowerPattern, ne_eq]
          rw [← hres]
          have hge : ¬ i.val + 1 < pattern.val.length := by omega
          simp [hend, hge, Facl.lowerPattern, resultToSpec]
          rfl
      · have hc : (next != Slice.len pattern) = true := by
          simp [hlast]
        simp only [hc, ↓reduceIte]
        have hne : (pattern.val.map ast.patSegToSpec).drop (i.val + 1) ≠ [] := by
          simp [List.drop_eq_nil_iff]; omega
        simp [fail, resultToSpec, kindToSpec]
        simp only [ast.patSegToSpec, Facl.lowerPattern, ne_eq, hne, not_false_eq_true, ↓reduceIte]
        rfl
  · rename_i hstop
    have hi' : i.val ≤ pattern.val.length := hi
    have hstop' : ¬ i.val < pattern.val.length := hstop
    have hend : i.val = pattern.val.length := by omega
    simp [hend, Facl.lowerPattern, resultToSpec]
    rfl

@[step] private theorem lower_pattern_spec (pattern : Slice ast.PatSeg) (span : ast.Span)
    (segs : alloc.vec.Vec ir.Seg) (names : alloc.vec.Vec (alloc.vec.Vec U8))
    (hs : segs.length + pattern.length ≤ Usize.max)
    (hn : names.length + pattern.length ≤ Usize.max) :
    lower_pattern pattern span segs names ⦃ res =>
      resultToSpec (fun b => (res.2.1.val.map ir.segToSpec, res.2.2.val.map (·.val), b)) res.1 =
        Facl.lowerPattern reservedNames (pattern.val.map ast.patSegToSpec)
          (segs.val.map ir.segToSpec) (names.val.map (·.val)) ⦄ := by
  unfold lower_pattern
  refine WP.spec_mono (lower_pattern_loop_spec pattern span segs names false 0#usize (by simp)
    (by simpa using hs) (by simpa using hn)) ?_
  intro res hres
  rw [hres]
  rcases h : Facl.lowerPattern reservedNames (pattern.val.map ast.patSegToSpec)
    (segs.val.map ir.segToSpec) (names.val.map (·.val)) with e | v <;> simp [h] <;> rfl

private def itemToSpec {E : Type} : ast.Item E → Facl.Item (List U8) E
  | .Match m => .nested (ast.matchToSpec m)
  | .Allow a => .allow ⟨a.methods.val, a.cond⟩

private theorem bodyToSpec_eq {E : Type} {n : Nat} (l : Aeneas.Data.ListN.ListN (ast.Item E) n) :
    ast.bodyToSpec l = l.toList.map itemToSpec := by
  induction l with
  | nil => simp [ast.bodyToSpec, Aeneas.Data.ListN.ListN.toList]
  | cons x l ih => cases x <;> simp [ast.bodyToSpec, Aeneas.Data.ListN.ListN.toList, ih, itemToSpec]

section
variable {E C K : Type} (inst : CompileCond K E C) (k : K)
  (compile : Option E → List (List U8) → Except Facl.LowerError C)
  (hcompile : ∀ cond names, inst.compile k cond names ⦃ r =>
    resultToSpec id r = compile cond (names.val.map (·.val)) ⦄)

include hcompile in
private theorem lower_allow_item_spec (item : ast.Item E) (span : ast.Span) (rest : Bool)
    (names : Slice (alloc.vec.Vec U8)) (allows : alloc.vec.Vec (ir.CompiledAllow C))
    (hb : allows.length < Usize.max) :
    lower_allow_item inst item span rest names k allows ⦃ r =>
      resultToSpec (fun v => v.val.map ir.allowToSpec) r =
        match item with
        | .Allow a => (compile a.cond (names.val.map (·.val))).map
            (fun c => allows.val.map ir.allowToSpec ++ [⟨a.methods.val, c⟩])
        | .Match _ => if rest then .error .restWithChildren
            else .ok (allows.val.map ir.allowToSpec) ⦄ := by
  unfold lower_allow_item
  cases item with
  | Match m =>
    dsimp only
    by_cases hr : rest = true
    · simp [hr, fail, resultToSpec, kindToSpec]
    · simp [hr, resultToSpec]
  | Allow a =>
    dsimp only
    apply WP.spec_bind (hcompile a.cond names)
    intro r hr
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      rw [← hr]
      rfl
    | Ok c =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      apply WP.spec_bind (alloc.vec.Vec.push_spec allows _ hb)
      intro allows1 h1
      rw [← hr]
      simp [resultToSpec, h1, ir.allowToSpec]
      rfl

include hcompile in
private theorem lower_allows_loop_spec (m : ast.Match E) (rest : Bool)
    (names : Slice (alloc.vec.Vec U8)) (allows : alloc.vec.Vec (ir.CompiledAllow C))
    (i : Usize) (hi : i.val ≤ m.body.length)
    (hb : allows.length + (m.body.length - i.val) ≤ Usize.max) :
    lower_allows_loop inst m rest names k allows i ⦃ r =>
      resultToSpec (fun v => v.val.map ir.allowToSpec) r =
        (Facl.lowerAllows compile (names.val.map (·.val)) rest
          ((m.body.val.map itemToSpec).drop i.val)).map (allows.val.map ir.allowToSpec ++ ·) ⦄ := by
  have hi' : i.val ≤ m.body.val.length := hi
  have hb' : allows.val.length + (m.body.val.length - i.val) ≤ Usize.max := hb
  unfold lower_allows_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < m.body.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec m.body i hlt')
    intro item hitem
    have hdrop : (m.body.val.map itemToSpec).drop i.val =
        itemToSpec item :: (m.body.val.map itemToSpec).drop (i.val + 1) := by
      rw [← List.map_drop, List.drop_eq_getElem_cons hlt', List.map_cons, ← hitem, List.map_drop]
    apply WP.spec_bind (lower_allow_item_spec inst k compile hcompile item m.span rest names
      allows (by show allows.val.length < _; omega))
    intro r hr
    rw [hdrop]
    have hmax := alloc.vec.Vec.len_ineq m.body
    have hnext : ∀ v : alloc.vec.Vec (ir.CompiledAllow C), v.val.length ≤ allows.val.length + 1 →
        (do let i3 ← i + 1#usize
            lower_allows_loop inst m rest names k v i3) ⦃ res =>
          resultToSpec (fun v => v.val.map ir.allowToSpec) res =
            (Facl.lowerAllows compile (names.val.map (·.val)) rest
              ((m.body.val.map itemToSpec).drop (i.val + 1))).map
              (v.val.map ir.allowToSpec ++ ·) ⦄ := by
      intro v hv
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      refine WP.spec_mono (lower_allows_loop_spec m rest names v next
        (by omega) (by simp only [alloc.vec.Vec.length, hval]; omega)) ?_
      intro res hres
      rw [hres, hval]
    cases item with
    | Match c =>
      cases r with
      | Err e =>
        by_cases hrest : rest = true
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          simp only [itemToSpec, Facl.lowerAllows, hrest, ↓reduceIte]
          rw [hr]
          simp [hrest]
          rfl
        · simp [hrest, resultToSpec] at hr
      | Ok v =>
        by_cases hrest : rest = true
        · simp [hrest, resultToSpec] at hr
        · simp only [hrest, Bool.false_eq_true, ↓reduceIte, resultToSpec,
            Except.ok.injEq] at hr
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          have hlv : v.val.length = allows.val.length := by simpa using congrArg List.length hr
          refine WP.spec_mono (hnext v (by omega)) ?_
          intro res hres
          rw [hres, hr]
          simp [itemToSpec, Facl.lowerAllows, hrest]
    | Allow a =>
      rcases hc : compile a.cond (names.val.map (·.val)) with e' | c
      · cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          simp [hc, resultToSpec, Except.map] at hr
          simp only [itemToSpec, Facl.lowerAllows, hc, resultToSpec, hr]
          rfl
        | Ok v => simp [hc, resultToSpec, Except.map] at hr
      · cases r with
        | Err e => simp [hc, resultToSpec, Except.map] at hr
        | Ok v =>
          simp [hc, resultToSpec, Except.map] at hr
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          have hlv : v.val.length = allows.val.length + 1 := by simpa using congrArg List.length hr
          refine WP.spec_mono (hnext v (by omega)) ?_
          intro res hres
          rw [hres, hr]
          rcases h : Facl.lowerAllows compile (names.val.map (·.val)) rest
            ((m.body.val.map itemToSpec).drop (i.val + 1)) with e'' | r' <;>
            simp [itemToSpec, Facl.lowerAllows, hc, h] <;> rfl
  · rename_i hstop
    have hstop' : ¬ i.val < m.body.val.length := hstop
    have hend : i.val = m.body.val.length := by omega
    simp [hend, Facl.lowerAllows, resultToSpec, Except.map]

include hcompile in
private theorem lower_allows_spec (m : ast.Match E) (rest : Bool)
    (names : Slice (alloc.vec.Vec U8)) :
    lower_allows inst m rest names k ⦃ r =>
      resultToSpec (fun v => v.val.map ir.allowToSpec) r =
        Facl.lowerAllows compile (names.val.map (·.val)) rest (m.body.val.map itemToSpec) ⦄ := by
  unfold lower_allows
  refine WP.spec_mono (lower_allows_loop_spec inst k compile hcompile m rest names
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)) ?_
  intro r hr
  rw [hr]
  rcases h : Facl.lowerAllows compile (names.val.map (·.val)) rest (m.body.val.map itemToSpec)
    with e | v <;> simp [h] <;> rfl

end

private theorem matchToSpec_eq {E : Type} (m : ast.Match E) :
    ast.matchToSpec m = .mk (m.pattern.val.map ast.patSegToSpec) (m.body.val.map itemToSpec) := by
  rcases m with ⟨p, ⟨⟨n, l, h⟩⟩, sp⟩
  simp [ast.matchToSpec, bodyToSpec_eq, ast.Match.pattern, ast.Match.body, alloc.vec.Vec.val,
    Slice.val]

private theorem lowerPattern_length (ps : List (Facl.PatSeg (List U8)))
    (segs : List (Facl.Seg (List U8))) (names : List (List U8)) (s n b)
    (h : Facl.lowerPattern reservedNames ps segs names = .ok (s, n, b)) :
    s.length ≤ segs.length + ps.length ∧ n.length ≤ names.length + ps.length := by
  induction ps generalizing segs names with
  | nil =>
    simp only [Facl.lowerPattern, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    simp
  | cons p ps ih =>
    cases p with
    | lit l =>
      have := ih _ _ h
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega
    | var v =>
      simp only [Facl.lowerPattern] at h
      rcases hb : Facl.bindName reservedNames names v with e | n1
      · simp [hb, Bind.bind, Except.bind] at h
      · have hn1 : n1.length = names.length + 1 := by
          unfold Facl.bindName at hb
          split_ifs at hb
          simp at hb
          simp [← hb]
        have := ih _ _ (by simpa [hb, Bind.bind, Except.bind] using h)
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    | rest r =>
      simp only [Facl.lowerPattern] at h
      by_cases hps : ps = []
      · subst hps
        rcases hb : Facl.bindName reservedNames names r with e | n1
        · simp [hb, Bind.bind, Except.bind] at h
        · have hn1 : n1.length = names.length + 1 := by
            unfold Facl.bindName at hb
            split_ifs at hb
            simp at hb
            simp [← hb]
          simp [hb, Bind.bind, Except.bind] at h
          obtain ⟨rfl, rfl, -⟩ := h
          simp [hn1]
      · simp [hps] at h

section
variable {E C K : Type} (inst : CompileCond K E C) (k : K)
  (compile : Option E → List (List U8) → Except Facl.LowerError C)
  (hcompile : ∀ cond names, inst.compile k cond names ⦃ r =>
    resultToSpec id r = compile cond (names.val.map (·.val)) ⦄)

private def MatchOK (s : Nat) : Prop :=
  ∀ (m : ast.Match E) (ps : Slice ir.Seg) (pn : Slice (alloc.vec.Vec U8)) (depth : U32)
    (rules : alloc.vec.Vec (ir.Rule C)),
    (ast.matchToSpec m).size = s → ps.length + s ≤ Usize.max → pn.length + s ≤ Usize.max →
    rules.length + s ≤ Usize.max →
    lower_match inst m ps pn depth k rules ⦃ r =>
      resultToSpec (fun v => v.val.map ir.ruleToSpec) r =
        (Facl.lowerMatch reservedNames compile depth.val (ps.val.map ir.segToSpec)
          (pn.val.map (·.val)) (ast.matchToSpec m)).map (rules.val.map ir.ruleToSpec ++ ·) ∧
      ∀ v, r = .Ok v → v.length ≤ rules.length + s ⦄

private theorem bodySize_le_cons {E : Type} (x : Facl.Item (List U8) E) (l : List (Facl.Item (List U8) E)) :
    Facl.Match.bodySize l ≤ Facl.Match.bodySize (x :: l) := by
  cases x <;> simp [Facl.Match.bodySize]

private theorem lower_child_match_spec (c : ast.Match E) (segs : Slice ir.Seg)
    (names : Slice (alloc.vec.Vec U8)) (depth : U32) (rules : alloc.vec.Vec (ir.Rule C))
    (hd : depth.val ≤ 64) (hok : MatchOK inst k compile (ast.matchToSpec c).size)
    (hs : segs.length + (ast.matchToSpec c).size ≤ Usize.max)
    (hn : names.length + (ast.matchToSpec c).size ≤ Usize.max)
    (hr : rules.length + (ast.matchToSpec c).size ≤ Usize.max) :
    lower_child inst (.Match c) segs names depth k rules ⦃ r =>
      resultToSpec (fun v => v.val.map ir.ruleToSpec) r =
        (Facl.lowerMatch reservedNames compile (depth.val + 1) (segs.val.map ir.segToSpec)
          (names.val.map (·.val)) (ast.matchToSpec c)).map (rules.val.map ir.ruleToSpec ++ ·) ∧
      ∀ v, r = .Ok v → v.length ≤ rules.length + (ast.matchToSpec c).size ⦄ := by
  unfold lower_child
  apply WP.spec_bind (U32.add_spec (x := depth) (y := 1#u32) (by scalar_tac))
  intro d1 hd1
  have hv : d1.val = depth.val + 1 := by simpa using hd1
  refine WP.spec_mono (hok c segs names d1 rules rfl hs hn hr) ?_
  intro r h
  rw [hv] at h
  exact h


private theorem lower_children_loop_spec (m : ast.Match E) (segs : Slice ir.Seg)
    (names : Slice (alloc.vec.Vec U8)) (depth : U32) (rules : alloc.vec.Vec (ir.Rule C))
    (i : Usize) (hd : depth.val ≤ 64) (hi : i.val ≤ m.body.length)
    (hbelow : ∀ s ≤ Facl.Match.bodySize ((m.body.val.map itemToSpec).drop i.val),
      MatchOK inst k compile s)
    (hs : segs.length + Facl.Match.bodySize ((m.body.val.map itemToSpec).drop i.val) ≤ Usize.max)
    (hn : names.length + Facl.Match.bodySize ((m.body.val.map itemToSpec).drop i.val) ≤ Usize.max)
    (hr : rules.length + Facl.Match.bodySize ((m.body.val.map itemToSpec).drop i.val) ≤ Usize.max) :
    lower_children_loop inst m segs names depth k rules i ⦃ r =>
      resultToSpec (fun v => v.val.map ir.ruleToSpec) r =
        (Facl.lowerNested reservedNames compile (depth.val + 1) (segs.val.map ir.segToSpec)
          (names.val.map (·.val)) ((m.body.val.map itemToSpec).drop i.val)).map
          (rules.val.map ir.ruleToSpec ++ ·) ∧
      ∀ v, r = .Ok v → v.length ≤ rules.length +
        Facl.Match.bodySize ((m.body.val.map itemToSpec).drop i.val) ⦄ := by
  have hi' : i.val ≤ m.body.val.length := hi
  unfold lower_children_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < m.body.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec m.body i hlt')
    intro item hitem
    have hdrop : (m.body.val.map itemToSpec).drop i.val =
        itemToSpec item :: (m.body.val.map itemToSpec).drop (i.val + 1) := by
      rw [← List.map_drop, List.drop_eq_getElem_cons hlt', List.map_cons, ← hitem, List.map_drop]
    rw [hdrop] at hbelow hs hn hr ⊢
    have hB := bodySize_le_cons (itemToSpec item) ((m.body.val.map itemToSpec).drop (i.val + 1))
    have hnext : ∀ v : alloc.vec.Vec (ir.Rule C), v.length +
        Facl.Match.bodySize ((m.body.val.map itemToSpec).drop (i.val + 1)) ≤ Usize.max →
        (do let i3 ← i + 1#usize
            lower_children_loop inst m segs names depth k v i3) ⦃ res =>
          resultToSpec (fun v => v.val.map ir.ruleToSpec) res =
            (Facl.lowerNested reservedNames compile (depth.val + 1) (segs.val.map ir.segToSpec)
              (names.val.map (·.val)) ((m.body.val.map itemToSpec).drop (i.val + 1))).map
              (v.val.map ir.ruleToSpec ++ ·) ∧
          ∀ w, res = .Ok w → w.length ≤ v.length +
            Facl.Match.bodySize ((m.body.val.map itemToSpec).drop (i.val + 1)) ⦄ := by
      intro v hv
      have hmax := alloc.vec.Vec.len_ineq m.body
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
      intro next hnext
      have hval : next.val = i.val + 1 := by simpa using hnext
      refine WP.spec_mono (lower_children_loop_spec m segs names depth v
        next hd (by omega) ?_ ?_ ?_ ?_) ?_
      · rw [hval]; intro s' hs'; exact hbelow s' (by omega)
      · rw [hval]; omega
      · rw [hval]; omega
      · rw [hval]; exact hv
      · intro res hres
        rw [hval] at hres
        exact hres
    cases item with
    | Match c =>
      simp only [itemToSpec, Facl.Match.bodySize] at hbelow hs hn hr ⊢
      apply WP.spec_bind (lower_child_match_spec inst k compile c segs names depth rules hd
        (hbelow _ (by omega)) (by omega) (by omega) (by omega))
      intro r hr1
      obtain ⟨hr1, hr2⟩ := hr1
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        rcases hm : Facl.lowerMatch reservedNames compile (depth.val + 1)
          (segs.val.map ir.segToSpec) (names.val.map (·.val)) (ast.matchToSpec c) with e' | rs
        · rw [hr1, hm]
          simp only [Facl.lowerNested, hm]
          rfl
        · simp [hm, resultToSpec, Except.map] at hr1
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        rcases hm : Facl.lowerMatch reservedNames compile (depth.val + 1)
          (segs.val.map ir.segToSpec) (names.val.map (·.val)) (ast.matchToSpec c) with e' | rs
        · simp [hm, resultToSpec, Except.map] at hr1
        · simp [hm, resultToSpec, Except.map] at hr1
          have hlv : v.length ≤ rules.length + (ast.matchToSpec c).size := hr2 v rfl
          refine WP.spec_mono (hnext v (by omega)) ?_
          intro res hres
          obtain ⟨h1, h2⟩ := hres
          refine ⟨?_, fun w hw => ?_⟩
          · rw [h1, hr1]
            rcases hn : Facl.lowerNested reservedNames compile (depth.val + 1)
              (segs.val.map ir.segToSpec) (names.val.map (·.val))
              ((m.body.val.map itemToSpec).drop (i.val + 1)) with e'' | more <;>
              simp [Facl.lowerNested, hm, hn, Bind.bind, Except.bind, Except.map]
          · have h3 := h2 w hw
            have h4 : w.length ≤ rules.length + ((ast.matchToSpec c).size +
                Facl.Match.bodySize ((m.body.val.map itemToSpec).drop (i.val + 1))) := by omega
            exact h4
    | Allow a =>
      simp only [itemToSpec, Facl.Match.bodySize] at hbelow hs hn hr ⊢
      unfold lower_child
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      refine WP.spec_mono (hnext rules (by omega)) ?_
      intro res hres
      obtain ⟨h1, h2⟩ := hres
      refine ⟨by rw [h1]; simp [Facl.lowerNested], fun w hw => ?_⟩
      have h3 := h2 w hw
      have h4 : w.length ≤ rules.length + (1 +
          Facl.Match.bodySize ((m.body.val.map itemToSpec).drop (i.val + 1))) := by omega
      exact h4
  · rename_i hstop
    have hstop' : ¬ i.val < m.body.val.length := hstop
    have hend : i.val = m.body.val.length := by omega
    simp [hend, Facl.lowerNested, Facl.Match.bodySize, resultToSpec, Except.map]

include hcompile in
private theorem matchOK_of_below (s : Nat) (hbelow : ∀ s' < s, MatchOK inst k compile s') :
    MatchOK inst k compile s := by
  intro m ps pn depth rules hsz hps hpn hrules
  have hmd : lower.MAX_DEPTH.val = 64 := by
    unfold lower.MAX_DEPTH; rfl
  rw [matchToSpec_eq] at hsz
  unfold lower_match
  rw [matchToSpec_eq]
  simp only [UScalar.lt_equiv, hmd]
  split
  · rename_i hdeep
    simp [fail, Facl.lowerMatch, Facl.maxDepth, hdeep, resultToSpec, kindToSpec]
    rfl
  · rename_i hok
    have hok' : depth.val ≤ 64 := by omega
    simp only [Facl.Match.size, List.length_map] at hsz
    have hmaxp := alloc.vec.Vec.len_ineq m.pattern
    apply WP.spec_bind (copy_segs_spec ps)
    intro segs hsegs
    apply WP.spec_bind (copy_names_spec pn)
    intro names hnames
    have hpl : (alloc.vec.Vec.deref m.pattern).length = m.pattern.val.length := by
      simp [alloc.vec.Vec.deref, Slice.length]
    have hps' : ps.val.length + s ≤ Usize.max := hps
    have hpn' : pn.val.length + s ≤ Usize.max := hpn
    have hrules' : rules.val.length + s ≤ Usize.max := hrules
    apply WP.spec_bind (lower_pattern_spec (alloc.vec.Vec.deref m.pattern) m.span segs names
      (by simp only [alloc.vec.Vec.length, hsegs, hpl]; omega)
      (by simp only [alloc.vec.Vec.length, hnames, hpl]; omega))
    intro res hres
    obtain ⟨r, segs1, names1⟩ := res
    have hres' : resultToSpec (fun b => (segs1.val.map ir.segToSpec, names1.val.map (·.val), b)) r =
        Facl.lowerPattern reservedNames (m.pattern.val.map ast.patSegToSpec)
          (ps.val.map ir.segToSpec) (pn.val.map (·.val)) := by
      simpa [alloc.vec.Vec.deref, hsegs, hnames] using hres
    have hdep : ¬ depth.val > Facl.maxDepth := by simp [Facl.maxDepth]; omega
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      simp only [Facl.lowerMatch, hdep, ↓reduceIte, ← hres']
      rfl
    | Ok rest =>
      have hp : Facl.lowerPattern reservedNames (m.pattern.val.map ast.patSegToSpec)
          (ps.val.map ir.segToSpec) (pn.val.map (·.val)) =
          .ok (segs1.val.map ir.segToSpec, names1.val.map (·.val), rest) := by
        rw [← hres']; rfl
      obtain ⟨hl1, hl2⟩ := lowerPattern_length _ _ _ _ _ _ hp
      simp only [List.length_map] at hl1 hl2
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_bind (lower_allows_spec inst k compile hcompile m rest
        (alloc.vec.Vec.deref names1))
      intro r1 hr1
      have hr1' : resultToSpec (fun v => v.val.map ir.allowToSpec) r1 =
          Facl.lowerAllows compile (names1.val.map (·.val)) rest (m.body.val.map itemToSpec) := by
        simpa [alloc.vec.Vec.deref] using hr1
      rcases hl : Facl.lowerAllows compile (names1.val.map (·.val)) rest
        (m.body.val.map itemToSpec) with e' | al
      · cases r1 with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          rw [hl] at hr1'
          simp [resultToSpec] at hr1'
          simp [Facl.lowerMatch, hdep, hp, hl, resultToSpec, ← hr1', Bind.bind, Except.bind,
            Except.map]
        | Ok v => rw [hl] at hr1'; simp [resultToSpec] at hr1'
      · cases r1 with
        | Err e => rw [hl] at hr1'; simp [resultToSpec] at hr1'
        | Ok val1 =>
          rw [hl] at hr1'
          simp [resultToSpec] at hr1'
          simp only [Aeneas.Std.bind_ok]
          have hpat := alloc.vec.Vec.len_ineq m.pattern
          have hmid : ∀ rules1 : alloc.vec.Vec (ir.Rule C),
              rules1.val.map ir.ruleToSpec = rules.val.map ir.ruleToSpec ++
                (if al.isEmpty then [] else [⟨⟨segs1.val.map ir.segToSpec, rest⟩, al⟩]) →
              rules1.length ≤ rules.length + 1 →
              lower_children inst m segs1.deref names1.deref depth k rules1 ⦃ r =>
                resultToSpec (fun v => v.val.map ir.ruleToSpec) r =
                  (Facl.lowerMatch reservedNames compile depth.val (ps.val.map ir.segToSpec)
                    (pn.val.map (·.val)) (Facl.Match.mk (m.pattern.val.map ast.patSegToSpec)
                      (m.body.val.map itemToSpec))).map (rules.val.map ir.ruleToSpec ++ ·) ∧
                ∀ (v : alloc.vec.Vec (ir.Rule C)), r = core.result.Result.Ok v →
                  v.length ≤ rules.length + s ⦄ := by
            intro rules1 hr1m hr1l
            unfold lower_children
            have hd0 : (0#usize).val = 0 := rfl
            have hdl : segs1.deref.length = segs1.val.length := by
              simp [alloc.vec.Vec.deref, Slice.length]
            have hdn : names1.deref.length = names1.val.length := by
              simp [alloc.vec.Vec.deref, Slice.length]
            refine WP.spec_mono (lower_children_loop_spec inst k compile m segs1.deref
              names1.deref depth rules1 0#usize hok' (by simp [hd0]) (fun s' hs' => hbelow s' (by simp [hd0] at hs'; omega))
              ?_ ?_ ?_) ?_
            · simp only [hd0, List.drop_zero, hdl]; omega
            · simp only [hd0, List.drop_zero, hdn]; omega
            · simp only [hd0, List.drop_zero]; omega
            · intro res hres
              obtain ⟨h1, h2⟩ := hres
              refine ⟨?_, fun w hw => ?_⟩
              · rw [h1]
                have e1 : segs1.deref.val = segs1.val := by simp [alloc.vec.Vec.deref]
                have e2 : names1.deref.val = names1.val := by simp [alloc.vec.Vec.deref]
                simp only [hd0, List.drop_zero, e1, e2]
                rcases hn : Facl.lowerNested reservedNames compile (depth.val + 1)
                  (segs1.val.map ir.segToSpec) (names1.val.map (·.val))
                  (m.body.val.map itemToSpec) with e'' | more <;>
                  simp [Facl.lowerMatch, hdep, hp, hl, hn, hr1m, Bind.bind, Except.bind,
                    Except.map]
              · have h3 := h2 w hw
                simp only [hd0, List.drop_zero] at h3
                have h4 : w.length ≤ rules.length + s := by omega
                exact h4
          apply WP.spec_bind (alloc.vec.Vec.is_empty.spec val1)
          intro b hb
          have hlen1 : val1.val.length = al.length := by rw [← hr1']; simp
          by_cases hbt : b = true
          · have hz : al = [] := by
              have h0 : val1.length = 0 := by simpa [hb] using hbt
              have : val1.val.length = 0 := h0
              rw [hlen1] at this
              exact List.length_eq_zero_iff.mp this
            simp only [hbt, ↓reduceIte, Aeneas.Std.bind_ok]
            exact hmid rules (by simp [hz]) (by omega)
          · have hnz : al ≠ [] := by
              intro hz
              apply hbt
              have : val1.length = 0 := by
                have : val1.val.length = 0 := by rw [hlen1, hz]; rfl
                exact this
              simpa [hb] using this
            simp only [hbt, Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_assoc]
            apply WP.spec_bind (copy_segs_spec (alloc.vec.Vec.deref segs1))
            intro v hv
            apply WP.spec_bind (alloc.vec.Vec.push_spec rules _ (by omega))
            intro rules1 hrules1
            refine hmid rules1 ?_ ?_
            · rw [hrules1]
              simp [hnz, ir.ruleToSpec, ir.patternToSpec, hr1', alloc.vec.Vec.deref] at hv ⊢
              rw [hv]
            · simp only [alloc.vec.Vec.length, hrules1]; simp

include hcompile in
private theorem matchOK_all (s : Nat) : MatchOK inst k compile s :=
  Nat.strong_induction_on s (fun s ih => matchOK_of_below inst k compile hcompile s ih)

include hcompile in
private theorem lower_with_loop_spec (service : ast.Service E) (rules : alloc.vec.Vec (ir.Rule C))
    (i : Usize) (hi : i.val ≤ service.matches.length)
    (hb : rules.length + ((service.matches.val.drop i.val).map
      fun m => (ast.matchToSpec m).size).sum ≤ Usize.max) :
    lower_with_loop inst service k rules i ⦃ r =>
      resultToSpec ir.policyToSpec r =
        (((service.matches.val.drop i.val).map ast.matchToSpec).mapM
          (Facl.lowerMatch reservedNames compile 1 [] [])).map
          (fun rs => ⟨rules.val.map ir.ruleToSpec ++ rs.flatten⟩) ⦄ := by
  have hi' : i.val ≤ service.matches.val.length := hi
  unfold lower_with_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < service.matches.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec service.matches i hlt')
    intro m hm
    have hdrop : service.matches.val.drop i.val =
        m :: service.matches.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hm]
    rw [hdrop] at hb ⊢
    simp only [List.map_cons, List.sum_cons] at hb ⊢
    simp only [lift, Aeneas.Std.bind_ok]
    have e1 : (Std.Array.empty ir.Seg).to_slice.val = [] := rfl
    have e2 : (Std.Array.empty (alloc.vec.Vec U8)).to_slice.val = [] := rfl
    have hmax := alloc.vec.Vec.len_ineq service.matches
    have hrl : rules.val.length = rules.length := rfl
    apply WP.spec_bind (matchOK_all inst k compile hcompile (ast.matchToSpec m).size m
      (Std.Array.empty ir.Seg).to_slice (Std.Array.empty (alloc.vec.Vec U8)).to_slice 1#u32 rules
      rfl (by simp [Slice.length, e1]; omega) (by simp [Slice.length, e2]; omega) (by omega))
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have h1 : (1#u32).val = 1 := rfl
    simp only [e1, e2, List.map_nil, List.mapM_cons, h1] at hr1 ⊢
    rcases hm : Facl.lowerMatch reservedNames compile 1 [] [] (ast.matchToSpec m) with e' | rs
    · cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp [hm, resultToSpec, Except.map] at hr1
        simp [resultToSpec, hr1, Bind.bind, Except.bind, Except.map]
      | Ok v => simp [hm, resultToSpec, Except.map] at hr1
    · cases r with
      | Err e => simp [hm, resultToSpec, Except.map] at hr1
      | Ok v =>
        simp [hm, resultToSpec, Except.map] at hr1
        have hlv : v.length ≤ rules.length + (ast.matchToSpec m).size := hr2 v rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
        intro next hnext
        have hval : next.val = i.val + 1 := by simpa using hnext
        refine WP.spec_mono (lower_with_loop_spec service v next (by omega)
          (by rw [hval]; omega)) ?_
        intro res hres
        rw [hres, hval, hr1]
        rcases hn : List.mapM (Facl.lowerMatch reservedNames compile 1 [] [])
          (List.map ast.matchToSpec (List.drop (i.val + 1) service.matches.val)) with e'' | bs <;>
          simp [Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
  · rename_i hstop
    have hstop' : ¬ i.val < service.matches.val.length := hstop
    have hend : i.val = service.matches.val.length := by omega
    simp [hend, resultToSpec, ir.policyToSpec, Except.map, Pure.pure, Except.pure]

end

theorem lower_with_spec {E C K : Type} (inst : CompileCond K E C) (service : ast.Service E)
    (k : K) (compile : Option E → List (List U8) → Except Facl.LowerError C)
    (hsize : (ast.serviceToSpec service).size ≤ Usize.max)
    (hcompile : ∀ cond names, inst.compile k cond names ⦃ r =>
      resultToSpec id r = compile cond (names.val.map (·.val)) ⦄) :
    lower_with inst service k ⦃ r =>
      resultToSpec ir.policyToSpec r =
        Facl.lower reservedNames compile (ast.serviceToSpec service) ⦄ := by
  unfold lower_with
  refine WP.spec_mono (lower_with_loop_spec inst k compile hcompile service
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simpa [Facl.Service.size, ast.serviceToSpec,
      Function.comp_def] using hsize)) ?_
  intro r hr
  rw [hr]
  simp [Facl.lower, ast.serviceToSpec, Bind.bind, Except.bind, Except.map]

end FaclCore.lower

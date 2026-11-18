import Facl.Spec
import Facl.Lift
import FaclCore.Funs

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace FaclCore

private theorem byteToSpec_eq_iff (a : U8) (n : Nat) (hn : n < 256) :
    byteToSpec a = UInt8.ofNat n ↔ a.val = n := by
  have := a.hBounds
  simp only [byteToSpec]
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show a.val < 256 by scalar_tac)] using this
  · intro h; rw [h]

private theorem methodBit_eq (l : List UInt8) :
    Facl.methodBit l =
      if [71, 69, 84] = l then 1 else if [72, 69, 65, 68] = l then 2
      else if [79, 80, 84, 73, 79, 78, 83] = l then 4 else if [80, 79, 83, 84] = l then 8
      else if [80, 85, 84] = l then 16 else if [80, 65, 84, 67, 72] = l then 32
      else if [68, 69, 76, 69, 84, 69] = l then 64 else 0 := by
  have h1 : Facl.utf8 "GET" = [71, 69, 84] := by decide
  have h2 : Facl.utf8 "HEAD" = [72, 69, 65, 68] := by decide
  have h3 : Facl.utf8 "OPTIONS" = [79, 80, 84, 73, 79, 78, 83] := by decide
  have h4 : Facl.utf8 "POST" = [80, 79, 83, 84] := by decide
  have h5 : Facl.utf8 "PUT" = [80, 85, 84] := by decide
  have h6 : Facl.utf8 "PATCH" = [80, 65, 84, 67, 72] := by decide
  have h7 : Facl.utf8 "DELETE" = [68, 69, 76, 69, 84, 69] := by decide
  simp only [Facl.methodBit, Facl.methodBits, List.find?_cons, h1, h2, h3, h4, h5, h6, h7]
  split_ifs <;> simp_all

private theorem byteToSpec_inj {a b : U8} (h : byteToSpec a = byteToSpec b) : a = b := by
  have h' := (byteToSpec_eq_iff a b.val (by scalar_tac)).mp h
  exact UScalar.eq_of_val_eq h'

private theorem map_byteToSpec_eq (l l' : List U8) :
    l'.map byteToSpec = l.map byteToSpec ↔ l' = l := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun a b h => byteToSpec_inj h) h
  · intro h; rw [h]

private theorem methodBit_eq' (l : List U8) :
    Facl.methodBit (l.map byteToSpec) =
      if [71#u8, 69#u8, 84#u8] = l then 1 else if [72#u8, 69#u8, 65#u8, 68#u8] = l then 2
      else if [79#u8, 80#u8, 84#u8, 73#u8, 79#u8, 78#u8, 83#u8] = l then 4
      else if [80#u8, 79#u8, 83#u8, 84#u8] = l then 8
      else if [80#u8, 85#u8, 84#u8] = l then 16
      else if [80#u8, 65#u8, 84#u8, 67#u8, 72#u8] = l then 32
      else if [68#u8, 69#u8, 76#u8, 69#u8, 84#u8, 69#u8] = l then 64 else 0 := by
  rw [methodBit_eq]
  have e : ∀ l' : List U8, ((l'.map byteToSpec = l.map byteToSpec) ↔ l' = l) :=
    fun l' => map_byteToSpec_eq l l'
  have k1 : ([71, 69, 84] : List UInt8) = [71#u8, 69#u8, 84#u8].map byteToSpec := by decide
  have k2 : ([72, 69, 65, 68] : List UInt8) = [72#u8, 69#u8, 65#u8, 68#u8].map byteToSpec := by decide
  have k3 : ([79, 80, 84, 73, 79, 78, 83] : List UInt8) =
      [79#u8, 80#u8, 84#u8, 73#u8, 79#u8, 78#u8, 83#u8].map byteToSpec := by decide
  have k4 : ([80, 79, 83, 84] : List UInt8) = [80#u8, 79#u8, 83#u8, 84#u8].map byteToSpec := by decide
  have k5 : ([80, 85, 84] : List UInt8) = [80#u8, 85#u8, 84#u8].map byteToSpec := by decide
  have k6 : ([80, 65, 84, 67, 72] : List UInt8) =
      [80#u8, 65#u8, 84#u8, 67#u8, 72#u8].map byteToSpec := by decide
  have k7 : ([68, 69, 76, 69, 84, 69] : List UInt8) =
      [68#u8, 69#u8, 76#u8, 69#u8, 84#u8, 69#u8].map byteToSpec := by decide
  rw [k1, k2, k3, k4, k5, k6, k7]
  simp only [e]

private theorem byteToSpec_toNat (b : U8) : (byteToSpec b).toNat = b.val := by
  have : b.val < 256 := by scalar_tac
  simp [byteToSpec]

private theorem utf8Go_pending (pending : List (UInt8 × UInt8)) (l : List UInt8) :
    Facl.utf8Go pending l = (decide (pending.length ≤ l.length) &&
      (List.zipWith Facl.inRange pending l).all id && Facl.utf8Go [] (l.drop pending.length)) := by
  induction pending generalizing l with
  | nil => simp
  | cons r p ih =>
    cases l with
    | nil => simp [Facl.utf8Go]
    | cons b l =>
      simp only [Facl.utf8Go, ih, List.length_cons, List.zipWith_cons_cons, List.all_cons,
        id, List.drop_succ_cons]
      cases Facl.inRange r b <;> simp

private theorem cont_iff (x : U8) : (x &&& 192#u8 = 128#u8) ↔ 128 ≤ x.val ∧ x.val ≤ 191 := by
  have h : ∀ n < 256, (n &&& 192 = 128 ↔ 128 ≤ n ∧ n ≤ 191) := by
    set_option maxRecDepth 100000 in decide
  have := h x.val (by scalar_tac)
  rw [UScalar.eq_equiv, UScalar.val_and]
  simpa using this

private theorem inRange_iff (lo hi : UInt8) (b : U8) :
    Facl.inRange (lo, hi) (byteToSpec b) = true ↔ lo.toNat ≤ b.val ∧ b.val ≤ hi.toNat := by
  simp [Facl.inRange, UInt8.le_iff_toNat_le, byteToSpec_toNat]

private theorem tail_ok_loop_spec (s : Slice U8) (i tail k : Usize)
    (hi : i.val + tail.val < s.length) (hk : 1 ≤ k.val) (hk2 : k.val ≤ tail.val + 1)
    (ht : tail.val < Usize.max) :
    path.tail_ok_loop s i tail k ⦃ n =>
      n.val = if (List.zipWith Facl.inRange (List.replicate (tail.val + 1 - k.val) (128, 191))
          ((s.val.drop (i.val + k.val)).map byteToSpec)).all id then tail.val + 1 else 0 ⦄ := by
  have hlen := Slice.length_ineq s
  have hi' : i.val + tail.val < s.val.length := hi
  unfold path.tail_ok_loop
  simp only [UScalar.le_equiv]
  split
  · rename_i hle
    have hlt : i.val + k.val < s.val.length := by omega
    apply WP.spec_bind (Usize.add_spec (x := i) (y := k) (by scalar_tac))
    intro i1 hi1
    apply WP.spec_bind (Slice.index_usize_spec s i1 (by scalar_tac))
    intro i2 hi2
    simp only [lift, Aeneas.Std.bind_ok]
    have hval : i1.val = i.val + k.val := by simpa using hi1
    have hdrop : s.val.drop (i.val + k.val) = i2 :: s.val.drop (i.val + k.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [hi2, hval]
    have hrep : tail.val + 1 - k.val = (tail.val - k.val) + 1 := by omega
    split
    · rename_i hne
      have hn : ¬ (i2 &&& 192#u8 = 128#u8) := bne_iff_ne.mp hne
      rw [cont_iff] at hn
      refine (WP.spec_ok _).mpr ?_
      rw [hdrop, hrep]
      have : Facl.inRange (128, 191) (byteToSpec i2) = false := by
        rw [Bool.eq_false_iff]
        intro h
        have := (inRange_iff 128 191 i2).mp h
        simp at this
        omega
      simp [this, List.replicate_succ]
    · rename_i hne
      have hn : i2 &&& 192#u8 = 128#u8 := Decidable.not_not.mp (fun hc => hne (bne_iff_ne.mpr hc))
      rw [cont_iff] at hn
      apply WP.spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      intro k1 hk1
      have hkv : k1.val = k.val + 1 := by simpa using hk1
      refine WP.spec_mono (tail_ok_loop_spec s i tail k1 hi (by omega) (by omega) ht) ?_
      intro n hn'
      rw [hn', hkv, hdrop, hrep]
      have : Facl.inRange (128, 191) (byteToSpec i2) = true := by
        rw [inRange_iff]
        simp
        omega
      have e : tail.val + 1 - (k.val + 1) = tail.val - k.val := by omega
      rw [e]
      simp [this, List.replicate_succ, show i.val + k.val + 1 = i.val + (k.val + 1) by omega]
  · rename_i hgt
    have : k.val = tail.val + 1 := by omega
    refine WP.spec_mono (Usize.add_spec (x := tail) (y := 1#usize) (by scalar_tac)) ?_
    intro n hn
    have : (tail.val + 1 - k.val) = 0 := by omega
    simp [this]
    simpa using hn
termination_by tail.val + 1 - k.val
decreasing_by all_goals scalar_tac

private theorem tail_ok_spec (s : Slice U8) (i tail : Usize) (lo hi : U8)
    (hi' : i.val < s.length) (ht1 : 1 ≤ tail.val) (ht : tail.val ≤ 3) :
    path.tail_ok s i tail lo hi ⦃ n =>
      let more := (s.val.drop (i.val + 1)).map byteToSpec
      let P := tail.val ≤ more.length ∧
        (List.zipWith Facl.inRange ((byteToSpec lo, byteToSpec hi) :: List.replicate (tail.val - 1) (128, 191))
          more).all id = true
      (n.val = 0 ∧ ¬ P) ∨ (n.val = tail.val + 1 ∧ P) ⦄ := by
  have hlen := Slice.length_ineq s
  unfold path.tail_ok
  apply WP.spec_bind (Usize.sub_spec (x := Slice.len s) (y := i) (by simp; scalar_tac))
  intro i2 hi2
  have hi2v : i2.val = s.length - i.val := by simp at hi2; exact hi2.1
  simp only [UScalar.le_equiv]
  split
  · rename_i hle
    refine (WP.spec_ok _).mpr (Or.inl ⟨rfl, ?_⟩)
    simp only [List.length_map, List.length_drop]
    have : s.val.length = s.length := rfl
    omega
  · rename_i hgt
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    intro i3 hi3
    have hi3v : i3.val = i.val + 1 := by simpa using hi3
    have hlt : i.val + 1 < s.val.length := by
      have : s.val.length = s.length := rfl
      omega
    apply WP.spec_bind (Slice.index_usize_spec s i3 (by scalar_tac))
    intro i4 hi4
    have hdrop : s.val.drop (i.val + 1) = i4 :: s.val.drop (i.val + 2) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [hi4, hi3v]
    simp only [UScalar.lt_equiv]
    split
    · rename_i hl
      refine (WP.spec_ok _).mpr (Or.inl ⟨rfl, ?_⟩)
      rintro ⟨-, h⟩
      rw [hdrop] at h
      obtain ⟨t, ht'⟩ : ∃ t, tail.val = t + 1 := ⟨tail.val - 1, by omega⟩
      rw [ht'] at h
      simp [inRange_iff, byteToSpec_toNat] at h
      omega
    · rename_i hl
      apply WP.spec_bind (Slice.index_usize_spec s i3 (by scalar_tac))
      intro i5 hi5
      have hi5' : i5 = i4 := by rw [hi5, hi4]
      subst hi5'
      split
      · rename_i hh
        refine (WP.spec_ok _).mpr (Or.inl ⟨rfl, ?_⟩)
        rintro ⟨-, h⟩
        rw [hdrop] at h
        obtain ⟨t, ht'⟩ : ∃ t, tail.val = t + 1 := ⟨tail.val - 1, by omega⟩
        rw [ht'] at h
        simp [inRange_iff, byteToSpec_toNat] at h
        omega
      · rename_i hh
        refine WP.spec_mono (tail_ok_loop_spec s i tail 2#usize (by omega) (by simp) (by simp; omega)
          (by scalar_tac)) ?_
        intro n hn
        have e2 : (2#usize : Usize).val = 2 := by simp
        rw [e2] at hn
        rw [hdrop]
        simp only [List.map_cons]
        obtain ⟨t, ht'⟩ : ∃ t, tail.val = t + 1 := ⟨tail.val - 1, by omega⟩
        rw [ht'] at hn ⊢
        have e : t + 1 + 1 - 2 = t := by omega
        have hin : Facl.inRange (byteToSpec lo, byteToSpec hi) (byteToSpec i5) = true := by
          rw [Facl.inRange]
          simp [UInt8.le_iff_toNat_le, byteToSpec_toNat]
          omega
        rw [e] at hn
        by_cases hc : (List.zipWith Facl.inRange (List.replicate t (128, 191))
            (List.map byteToSpec (List.drop (i.val + 2) s.val))).all id = true
        · simp only [hc, ite_true] at hn
          refine Or.inr ⟨hn, ?_, ?_⟩
          · have : s.val.length = s.length := rfl
            simp
            omega
          · simpa [List.replicate_succ, hin] using hc
        · simp only [hc] at hn
          refine Or.inl ⟨hn, ?_⟩
          rintro ⟨-, h⟩
          simp [hin] at h
          exact hc (by simpa using h)

private theorem inRange_eq (lo hi : UInt8) (b : U8) :
    Facl.inRange (lo, hi) (byteToSpec b) = decide (lo.toNat ≤ b.val ∧ b.val ≤ hi.toNat) := by
  rw [Bool.eq_iff_iff, inRange_iff]; simp

private theorem utf8Go_lead (b : U8) (more : List UInt8) :
    Facl.utf8Go [] (byteToSpec b :: more) =
      if b.val ≤ 127 then Facl.utf8Go [] more
      else if 194 ≤ b.val ∧ b.val ≤ 223 then Facl.utf8Go [(128, 191)] more
      else if b.val = 224 then Facl.utf8Go [(160, 191), (128, 191)] more
      else if b.val = 237 then Facl.utf8Go [(128, 159), (128, 191)] more
      else if (225 ≤ b.val ∧ b.val ≤ 236) ∨ (238 ≤ b.val ∧ b.val ≤ 239) then
        Facl.utf8Go [(128, 191), (128, 191)] more
      else if b.val = 240 then Facl.utf8Go [(144, 191), (128, 191), (128, 191)] more
      else if 241 ≤ b.val ∧ b.val ≤ 243 then Facl.utf8Go [(128, 191), (128, 191), (128, 191)] more
      else if b.val = 244 then Facl.utf8Go [(128, 143), (128, 191), (128, 191)] more
      else false := by
  have hb : b.val < 256 := by scalar_tac
  simp only [Facl.utf8Go, Facl.utf8Rows, List.find?_cons, inRange_eq, List.head?_cons,
    Option.any_some]
  simp
  rcases (by omega : b.val ≤ 127 ∨ (128 ≤ b.val ∧ b.val ≤ 193) ∨ (194 ≤ b.val ∧ b.val ≤ 223) ∨
      b.val = 224 ∨ (225 ≤ b.val ∧ b.val ≤ 236) ∨ b.val = 237 ∨ (238 ≤ b.val ∧ b.val ≤ 239) ∨
      b.val = 240 ∨ (241 ≤ b.val ∧ b.val ≤ 243) ∨ b.val = 244 ∨ 245 ≤ b.val) with
    h | h | h | h | h | h | h | h | h | h | h
  all_goals (simp (disch := omega) [decide_eq_false, decide_eq_true])
  all_goals (try split_ifs)
  all_goals (try intros)
  all_goals first | rfl | (exfalso; omega)

private theorem tail_case (s : Slice U8) (i tail : Usize) (lo hi : U8) (hi' : i.val < s.length)
    (ht1 : 1 ≤ tail.val) (ht3 : tail.val ≤ 3) (pend : List (UInt8 × UInt8))
    (hpend : pend = (byteToSpec lo, byteToSpec hi) :: List.replicate (tail.val - 1) (128, 191))
    (hgo : Facl.utf8Go [] ((s.val.drop i.val).map byteToSpec) =
      Facl.utf8Go pend ((s.val.drop (i.val + 1)).map byteToSpec)) :
    path.tail_ok s i tail lo hi ⦃ n =>
      let rest := (s.val.drop i.val).map byteToSpec
      (n.val = 0 ∧ Facl.utf8Go [] rest = false) ∨
      (0 < n.val ∧ n.val ≤ rest.length ∧ Facl.utf8Go [] rest = Facl.utf8Go [] (rest.drop n.val)) ⦄ := by
  subst hpend
  refine WP.spec_mono (tail_ok_spec s i tail lo hi hi' ht1 ht3) ?_
  intro n hn
  have hplen : ((byteToSpec lo, byteToSpec hi) :: List.replicate (tail.val - 1) (128, 191)).length =
      tail.val := by simp; omega
  have hmore : (List.map byteToSpec (s.val.drop (i.val + 1))).drop tail.val =
      ((s.val.drop i.val).map byteToSpec).drop (tail.val + 1) := by
    simp [List.drop_drop]; congr 1; omega
  rcases hn with ⟨h0, hP⟩ | ⟨h1, hP⟩
  · left
    refine ⟨h0, ?_⟩
    rw [hgo, utf8Go_pending, hplen]
    by_cases hc : tail.val ≤ (List.map byteToSpec (s.val.drop (i.val + 1))).length
    · have : ¬ (List.zipWith Facl.inRange
          ((byteToSpec lo, byteToSpec hi) :: List.replicate (tail.val - 1) (128, 191))
          (List.map byteToSpec (s.val.drop (i.val + 1)))).all id = true :=
        fun h => hP ⟨hc, h⟩
      simp only [Bool.not_eq_true] at this
      rw [this]; simp only [Bool.and_false, Bool.false_and]
    · rw [decide_eq_false hc]; simp only [Bool.false_and]
  · right
    obtain ⟨hl, hz⟩ := hP
    refine ⟨by omega, ?_, ?_⟩
    · simp at hl ⊢; omega
    · rw [hgo, utf8Go_pending, hplen, h1, ← hmore]
      rw [decide_eq_true hl, hz]; simp only [Bool.and_self, Bool.true_and]

private def charLen (s : Slice U8) (i : Usize) (b : U8) : Result Usize :=
  if b.val ≤ 127 then ok 1#usize
  else if 194 ≤ b.val ∧ b.val ≤ 223 then path.tail_ok s i 1#usize 128#u8 191#u8
  else if b.val = 224 then path.tail_ok s i 2#usize 160#u8 191#u8
  else if b.val = 237 then path.tail_ok s i 2#usize 128#u8 159#u8
  else if (225 ≤ b.val ∧ b.val ≤ 236) ∨ (238 ≤ b.val ∧ b.val ≤ 239) then
    path.tail_ok s i 2#usize 128#u8 191#u8
  else if b.val = 240 then path.tail_ok s i 3#usize 144#u8 191#u8
  else if 241 ≤ b.val ∧ b.val ≤ 243 then path.tail_ok s i 3#usize 128#u8 191#u8
  else if b.val = 244 then path.tail_ok s i 3#usize 128#u8 143#u8
  else ok 0#usize

private theorem utf8_char_len_eq (s : Slice U8) (i : Usize) :
    path.utf8_char_len s i = (Slice.index_usize s i >>= charLen s i) := by
  unfold path.utf8_char_len
  congr 1
  funext b
  have hb : b.val < 256 := by scalar_tac
  rcases (by omega : b.val ≤ 127 ∨ (128 ≤ b.val ∧ b.val ≤ 193) ∨ (194 ≤ b.val ∧ b.val ≤ 223) ∨
      b.val = 224 ∨ (225 ≤ b.val ∧ b.val ≤ 236) ∨ b.val = 237 ∨ (238 ≤ b.val ∧ b.val ≤ 239) ∨
      b.val = 240 ∨ (241 ≤ b.val ∧ b.val ≤ 243) ∨ b.val = 244 ∨ 245 ≤ b.val) with
    h | h | h | h | h | h | h | h | h | h | h
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left]
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_right]
    split <;> first | rfl | (exfalso; revert h; decide)
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left, ite_eq_right]
  · obtain rfl : b = 224#u8 := UScalar.eq_of_val_eq (by simp; omega)
    simp [charLen]
    split <;> first | rfl | (exfalso; simp_all +decide)
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left, ite_eq_right]
    split <;> first | rfl | (exfalso; revert h; decide)
  · obtain rfl : b = 237#u8 := UScalar.eq_of_val_eq (by simp; omega)
    simp [charLen]
    split <;> first | rfl | (exfalso; simp_all +decide)
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left, ite_eq_right]
    split <;> first | rfl | (exfalso; revert h; decide)
  · obtain rfl : b = 240#u8 := UScalar.eq_of_val_eq (by simp; omega)
    simp [charLen]
    split <;> first | rfl | (exfalso; simp_all +decide)
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left, ite_eq_right]
    split <;> first | rfl | (exfalso; revert h; decide)
  · obtain rfl : b = 244#u8 := UScalar.eq_of_val_eq (by simp; omega)
    simp [charLen]
    split <;> first | rfl | (exfalso; simp_all +decide)
  · simp (disch := scalar_tac) [UScalar.le_equiv, charLen, ite_eq_left, ite_eq_right]
    split <;> first | rfl | (exfalso; revert h; decide)


private theorem utf8_char_len_spec (s : Slice U8) (i : Usize) (hi : i.val < s.length) :
    path.utf8_char_len s i ⦃ n =>
      let rest := (s.val.drop i.val).map byteToSpec
      (n.val = 0 ∧ Facl.utf8Go [] rest = false) ∨
      (0 < n.val ∧ n.val ≤ rest.length ∧ Facl.utf8Go [] rest = Facl.utf8Go [] (rest.drop n.val)) ⦄ := by
  have hlen : s.val.length = s.length := rfl
  rw [utf8_char_len_eq]
  apply WP.spec_bind (Slice.index_usize_spec s i hi)
  intro b hb
  have hr : (s.val.drop i.val).map byteToSpec =
      byteToSpec b :: ((s.val.drop (i.val + 1)).map byteToSpec) := by
    rw [List.drop_eq_getElem_cons (by omega), List.map_cons, hb]
  have hlead := utf8Go_lead b ((s.val.drop (i.val + 1)).map byteToSpec)
  unfold charLen
  split_ifs
  · refine (WP.spec_ok _).mpr (Or.inr ⟨by simp, by simp [hr], ?_⟩)
    rw [hr, hlead]
    simp_all
  all_goals first
    | (refine tail_case s i _ _ _ hi (by simp) (by simp) _ rfl ?_
       rw [hr, hlead]
       split_ifs; rfl)
    | (refine (WP.spec_ok _).mpr (Or.inl ⟨by simp, ?_⟩)
       rw [hr, hlead]
       split_ifs; rfl)

private theorem utf8_valid_loop_spec (s : Slice U8) (i : Usize) (hi : i.val ≤ s.length) :
    path.utf8_valid_loop s i ⦃ r => r = Facl.utf8Go [] ((s.val.drop i.val).map byteToSpec) ⦄ := by
  have hlen : s.val.length = s.length := rfl
  have hmax := Slice.length_ineq s
  unfold path.utf8_valid_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    apply WP.spec_bind (utf8_char_len_spec s i (by simpa using hlt))
    intro n hn
    split
    · rename_i hz
      have hz' : n.val = 0 := by simp [hz]
      rcases hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact (WP.spec_ok _).mpr h.symm
      · omega
    · rename_i hnz
      have hnz' : n.val ≠ 0 := by simpa using hnz
      rcases hn with ⟨h, -⟩ | ⟨hpos, hle, heq⟩
      · omega
      · simp only [List.length_map, List.length_drop] at hle
        apply WP.spec_bind (Usize.add_spec (x := i) (y := n) (by scalar_tac))
        intro i2 hi2
        have hi2v : i2.val = i.val + n.val := by simpa using hi2
        refine WP.spec_mono (utf8_valid_loop_spec s i2 (by scalar_tac)) ?_
        intro r hr
        rw [hr, heq, hi2v]
        simp only [List.map_drop, List.drop_drop]
  · rename_i hge
    have : i.val = s.length := by scalar_tac
    refine (WP.spec_ok _).mpr ?_
    simp [Facl.utf8Go, this]
termination_by s.length - i.val
decreasing_by scalar_tac

private theorem byteToSpec_sub (b : U8) (k : Nat) (hk : k < 256) (h : k ≤ b.val) :
    byteToSpec b - UInt8.ofNat k = UInt8.ofNat (b.val - k) := by
  have hb : b.val < 256 := by scalar_tac
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_sub, byteToSpec_toNat, Nat.mod_eq_of_lt hk]
  omega

private theorem hexValue_eq (b : U8) :
    Facl.hexValue (byteToSpec b) =
      if 48 ≤ b.val ∧ b.val ≤ 57 then some (UInt8.ofNat (b.val - 48))
      else if 97 ≤ b.val ∧ b.val ≤ 102 then some (UInt8.ofNat (b.val - 97 + 10))
      else if 65 ≤ b.val ∧ b.val ≤ 70 then some (UInt8.ofNat (b.val - 65 + 10))
      else none := by
  have hb : b.val < 256 := by scalar_tac
  have n0 : '0'.toUInt8.toNat = 48 := by decide
  have n9 : '9'.toUInt8.toNat = 57 := by decide
  have na : 'a'.toUInt8.toNat = 97 := by decide
  have nf : 'f'.toUInt8.toNat = 102 := by decide
  have nA : 'A'.toUInt8.toNat = 65 := by decide
  have nF : 'F'.toUInt8.toNat = 70 := by decide
  have c0 : '0'.toUInt8 = UInt8.ofNat 48 := by decide
  have ca : 'a'.toUInt8 = UInt8.ofNat 97 := by decide
  have cA : 'A'.toUInt8 = UInt8.ofNat 65 := by decide
  unfold Facl.hexValue
  simp only [UInt8.le_iff_toNat_le, byteToSpec_toNat, n0, n9, na, nf, nA, nF]
  by_cases h1 : 48 ≤ b.val ∧ b.val ≤ 57
  · simp only [ite_eq_left h1, c0, byteToSpec_sub b 48 (by omega) h1.1]
  by_cases h2 : 97 ≤ b.val ∧ b.val ≤ 102
  · simp only [ite_eq_right h1, ite_eq_left h2, ca, byteToSpec_sub b 97 (by omega) h2.1]
    simp
  by_cases h3 : 65 ≤ b.val ∧ b.val ≤ 70
  · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, cA, byteToSpec_sub b 65 (by omega) h3.1]
    simp
  · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

private theorem hex_value_spec (b : U8) :
    path.hex_value b ⦃ o => o.map byteToSpec = Facl.hexValue (byteToSpec b) ∧
      ∀ v, o = some v → v.val < 16 ⦄ := by
  have hb : b.val < 256 := by scalar_tac
  rw [hexValue_eq]
  unfold path.hex_value
  rcases (by omega : b.val ≤ 47 ∨ (48 ≤ b.val ∧ b.val ≤ 57) ∨ (58 ≤ b.val ∧ b.val ≤ 64) ∨
      (65 ≤ b.val ∧ b.val ≤ 70) ∨ (71 ≤ b.val ∧ b.val ≤ 96) ∨ (97 ≤ b.val ∧ b.val ≤ 102) ∨
      103 ≤ b.val) with h | h | h | h | h | h | h <;>
  simp (disch := scalar_tac) [UScalar.le_equiv, ite_eq_left, ite_eq_right]
  · apply WP.spec_bind (U8.sub_spec (x := b) (y := 48#u8) (by scalar_tac))
    intro i hi
    refine (WP.spec_ok _).mpr ⟨⟨i, rfl, ?_⟩, ?_⟩
    · simp only [byteToSpec]; congr 1; scalar_tac
    · intro v hv; cases hv; scalar_tac
  · apply WP.spec_bind (U8.sub_spec (x := b) (y := 65#u8) (by scalar_tac))
    intro i hi
    apply WP.spec_bind (U8.add_spec (x := i) (y := 10#u8) (by scalar_tac))
    intro i1 hi1
    refine (WP.spec_ok _).mpr ⟨⟨i1, rfl, ?_⟩, ?_⟩
    · simp only [byteToSpec]
      have : i1.val = b.val - 65 + 10 := by scalar_tac
      rw [this, UInt8.ofNat_add]; rfl
    · intro v hv; cases hv; scalar_tac
  · apply WP.spec_bind (U8.sub_spec (x := b) (y := 97#u8) (by scalar_tac))
    intro i hi
    apply WP.spec_bind (U8.add_spec (x := i) (y := 10#u8) (by scalar_tac))
    intro i1 hi1
    refine (WP.spec_ok _).mpr ⟨⟨i1, rfl, ?_⟩, ?_⟩
    · simp only [byteToSpec]
      have : i1.val = b.val - 97 + 10 := by scalar_tac
      rw [this, UInt8.ofNat_add]; rfl
    · intro v hv; cases hv; scalar_tac

private def resToSpec {α β : Type} (f : α → β) :
    core.result.Result α path.PathError → Except Facl.PathError β
  | .Ok a => .ok (f a)
  | .Err e => .error (path.pathErrorToSpec e)

private theorem usize_lit1 (h) : Usize.ofNatCore 1 h = 1#usize := rfl
private theorem usize_lit2 (h) : Usize.ofNatCore 2 h = 2#usize := rfl

private theorem is_dot_segment_spec (seg : Slice U8) :
    path.is_dot_segment seg ⦃ r => r = decide (seg.val.map byteToSpec = Facl.utf8 "." ∨
      seg.val.map byteToSpec = Facl.utf8 "..") ⦄ := by
  have k1 : Facl.utf8 "." = [46#u8].map byteToSpec := by decide
  have k2 : Facl.utf8 ".." = [46#u8, 46#u8].map byteToSpec := by decide
  rw [k1, k2]
  simp only [map_byteToSpec_eq]
  unfold path.is_dot_segment
  obtain ⟨l, hl⟩ : ∃ l, seg.val = l := ⟨_, rfl⟩
  rw [hl]
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp [Slice.len, hl, Slice.index_usize, usize_lit1, usize_lit2]
  split <;> simp_all [WP.spec_ok]

private theorem validate_segment_loop_spec (seg : Slice U8) (i : Usize) (hi : i.val ≤ seg.length) :
    path.validate_segment_loop seg i ⦃ r => resToSpec id r =
      if 47#u8 ∈ seg.val.drop i.val ∨ 0#u8 ∈ seg.val.drop i.val then .error .forbiddenByte
      else if !Facl.utf8Valid (seg.val.map byteToSpec) then .error .invalidUtf8
      else .ok () ⦄ := by
  have hlen : seg.val.length = seg.length := rfl
  have hmax := Slice.length_ineq seg
  unfold path.validate_segment_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    have hlt' : i.val < seg.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec seg i hlt')
    intro i2 hi2
    have hdrop : seg.val.drop i.val = i2 :: seg.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hi2]
    split
    · rename_i h47
      refine (WP.spec_ok _).mpr ?_
      have : 47#u8 ∈ seg.val.drop i.val := by rw [hdrop, h47]; simp
      simp [resToSpec, this, path.pathErrorToSpec]
    · rename_i h47
      split
      · rename_i h0
        refine (WP.spec_ok _).mpr ?_
        have : 0#u8 ∈ seg.val.drop i.val := by rw [hdrop, h0]; simp
        simp [resToSpec, this, path.pathErrorToSpec]
      · rename_i h0
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i3 hi3
        have hi3v : i3.val = i.val + 1 := by simpa using hi3
        refine WP.spec_mono (validate_segment_loop_spec seg i3 (by scalar_tac)) ?_
        intro r hr
        rw [hr, hi3v, hdrop]
        have h47' : ¬ 47#u8 = i2 := fun h => h47 h.symm
        have h0' : ¬ 0#u8 = i2 := fun h => h0 h.symm
        simp [h47', h0']
  · rename_i hge
    have : i.val = seg.length := by scalar_tac
    have hd : seg.val.drop i.val = [] := by simp [List.drop_eq_nil_iff]; omega
    apply WP.spec_bind (utf8_valid_loop_spec seg 0#usize (by simp))
    intro b hb
    have hb2 : b = Facl.utf8Valid (seg.val.map byteToSpec) := by simpa [Facl.utf8Valid] using hb
    rw [hd]
    split
    · rename_i hb'
      refine (WP.spec_ok _).mpr ?_
      rw [hb'] at hb2
      simp [resToSpec, ← hb2]
    · rename_i hb'
      refine (WP.spec_ok _).mpr ?_
      have : b = false := by simpa using hb'
      rw [this] at hb2
      simp [resToSpec, ← hb2, path.pathErrorToSpec]
termination_by seg.length - i.val
decreasing_by scalar_tac

private theorem mem_map_byteToSpec (l : List U8) (x : U8) :
    byteToSpec x ∈ l.map byteToSpec ↔ x ∈ l :=
  List.mem_map_of_injective (fun _ _ h => byteToSpec_inj h)

private theorem validate_segment_spec (seg : Slice U8) :
    path.validate_segment seg ⦃ r => resToSpec id r = Facl.validateSegment (seg.val.map byteToSpec) ⦄ := by
  have h47 : '/'.toUInt8 = byteToSpec 47#u8 := by decide
  have h0 : (0 : UInt8) = byteToSpec 0#u8 := by decide
  unfold path.validate_segment
  apply WP.spec_bind (is_dot_segment_spec seg)
  intro b hb
  split
  · rename_i hd
    refine (WP.spec_ok _).mpr ?_
    rw [hd] at hb
    have := of_decide_eq_true hb.symm
    simp [resToSpec, Facl.validateSegment, this, path.pathErrorToSpec]
  · rename_i hd
    have hnd : ¬ (seg.val.map byteToSpec = Facl.utf8 "." ∨ seg.val.map byteToSpec = Facl.utf8 "..") := by
      have : b = false := by simpa using hd
      rw [this] at hb
      exact of_decide_eq_false hb.symm
    refine WP.spec_mono (validate_segment_loop_spec seg 0#usize (by simp)) ?_
    intro r hr
    rw [hr, Facl.validateSegment]
    simp only [hnd, ite_false, h47, h0, mem_map_byteToSpec]
    simp

private theorem percentDecode_plain (b : UInt8) (rest : List UInt8) (h : b ≠ '%'.toUInt8) :
    Facl.percentDecode (b :: rest) = (b :: ·) <$> Facl.percentDecode rest := by
  rcases rest with _ | ⟨h1, _ | ⟨l1, r⟩⟩
  · rw [Facl.percentDecode.eq_3 _ _ (by simp)]; exact ite_eq_left h
  · rw [Facl.percentDecode.eq_3 _ _ (by simp)]; exact ite_eq_left h
  · rw [Facl.percentDecode.eq_2]; exact ite_eq_left h

private theorem percentDecode_short (rest : List UInt8) (h : rest.length < 2) :
    Facl.percentDecode ('%'.toUInt8 :: rest) = .error .badPercentEncoding := by
  rw [Facl.percentDecode.eq_3 _ _ (by
    rintro a b r rfl
    simp at h)]
  exact ite_eq_right (by simp)

private theorem percentDecode_pct (a b : UInt8) (rest : List UInt8) :
    Facl.percentDecode ('%'.toUInt8 :: a :: b :: rest) =
      match Facl.hexValue a, Facl.hexValue b with
      | some h, some l => ((h * 16 + l) :: ·) <$> Facl.percentDecode rest
      | _, _ => .error .badPercentEncoding := by
  rw [Facl.percentDecode.eq_2]
  exact ite_eq_right (by simp)

private theorem decode_segment_loop_spec (seg : Slice U8) (out : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ seg.length) (hb : out.length + (seg.length - i.val) ≤ Usize.max) :
    path.decode_segment_loop seg out i ⦃ r =>
      resToSpec (fun v => v.val.map byteToSpec) r =
        (do let d ← Facl.percentDecode ((seg.val.drop i.val).map byteToSpec)
            let full := out.val.map byteToSpec ++ d
            Facl.validateSegment full
            return full) ⦄ := by
  have hlen : seg.val.length = seg.length := rfl
  have hmax := Slice.length_ineq seg
  have hb' : out.val.length + (seg.val.length - i.val) ≤ Usize.max := hb
  have h37 : '%'.toUInt8 = byteToSpec 37#u8 := by decide
  unfold path.decode_segment_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    have hlt' : i.val < seg.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec seg i hlt')
    intro i2 hi2
    have hdrop : seg.val.drop i.val = i2 :: seg.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hi2]
    rw [hdrop]
    split
    · rename_i h37'
      have hi2' : byteToSpec i2 = '%'.toUInt8 := by rw [h37, h37']
      apply WP.spec_bind (Usize.sub_spec (x := Slice.len seg) (y := i) (by simp; scalar_tac))
      intro i4 hi4
      have hi4v : i4.val = seg.length - i.val := by simp at hi4; exact hi4.1
      have hrest : (List.map byteToSpec (i2 :: List.drop (i.val + 1) seg.val)) =
          '%'.toUInt8 :: List.map byteToSpec (List.drop (i.val + 1) seg.val) := by
        rw [List.map_cons, hi2']
      split
      · rename_i hshort
        refine (WP.spec_ok _).mpr ?_
        rw [hrest, percentDecode_short _ (by simp; scalar_tac)]
        simp [resToSpec, path.pathErrorToSpec, Bind.bind, Except.bind]
      · rename_i hlong
        have h3 : 3 ≤ seg.length - i.val := by scalar_tac
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i5 hi5
        have hi5v : i5.val = i.val + 1 := by simpa using hi5
        apply WP.spec_bind (Slice.index_usize_spec seg i5 (by scalar_tac))
        intro i6 hi6
        apply WP.spec_bind (hex_value_spec i6)
        intro o ho
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 2#usize) (by scalar_tac))
        intro i7 hi7
        have hi7v : i7.val = i.val + 2 := by simpa using hi7
        apply WP.spec_bind (Slice.index_usize_spec seg i7 (by scalar_tac))
        intro i8 hi8
        apply WP.spec_bind (hex_value_spec i8)
        intro o1 ho1
        have hd1 : seg.val.drop (i.val + 1) = i6 :: i8 :: seg.val.drop (i.val + 3) := by
          rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
          simp [hi6, hi8, hi5v, hi7v]
        rw [hrest, hd1, List.map_cons, List.map_cons, percentDecode_pct, ← ho.1, ← ho1.1]
        cases o with
        | none =>
          refine (WP.spec_ok _).mpr ?_
          simp [resToSpec, path.pathErrorToSpec, Bind.bind, Except.bind]
        | some hh =>
          cases o1 with
          | none =>
            refine (WP.spec_ok _).mpr ?_
            simp [resToSpec, path.pathErrorToSpec, Bind.bind, Except.bind]
          | some ll =>
            have hh16 : hh.val < 16 := ho.2 hh rfl
            have ll16 : ll.val < 16 := ho1.2 ll rfl
            dsimp only
            apply WP.spec_bind (U8.mul_spec (x := hh) (y := 16#u8) (by scalar_tac))
            intro i9 hi9
            apply WP.spec_bind (U8.add_spec (x := i9) (y := ll) (by scalar_tac))
            intro i10 hi10
            apply WP.spec_bind (alloc.vec.Vec.push_spec out i10 (by scalar_tac))
            intro out1 hout1
            apply WP.spec_bind (Usize.add_spec (x := i) (y := 3#usize) (by scalar_tac))
            intro i11 hi11
            have hi11v : i11.val = i.val + 3 := by simpa using hi11
            refine WP.spec_mono (decode_segment_loop_spec seg out1 i11 (by scalar_tac)
              (by simp only [alloc.vec.Vec.length, hout1, hi11v]; simp; scalar_tac)) ?_
            intro r hr
            rw [hr, hi11v]
            have hb10 : byteToSpec i10 = byteToSpec hh * 16 + byteToSpec ll := by
              apply UInt8.toNat_inj.mp
              have e16 : (16 : UInt8).toNat = 16 := by decide
              have : i10.val = hh.val * 16 + ll.val := by scalar_tac
              simp only [UInt8.toNat_add, UInt8.toNat_mul, byteToSpec_toNat, e16, this]
              omega
            rcases Facl.percentDecode (List.map byteToSpec (List.drop (i.val + 3) seg.val)) with e | d
            · simp [Bind.bind, Except.bind]
            · simp [hout1, hb10, Bind.bind, Except.bind]
    · rename_i h37'
      apply WP.spec_bind (alloc.vec.Vec.push_spec out i2 (by scalar_tac))
      intro out1 hout1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i3 hi3
      have hi3v : i3.val = i.val + 1 := by simpa using hi3
      refine WP.spec_mono (decode_segment_loop_spec seg out1 i3 (by scalar_tac)
        (by simp only [alloc.vec.Vec.length, hout1, hi3v]; simp; scalar_tac)) ?_
      intro r hr
      rw [hr, hi3v]
      have hnp : byteToSpec i2 ≠ '%'.toUInt8 := by
        rw [h37]; intro h; exact h37' (byteToSpec_inj h)
      rcases hp : Facl.percentDecode (List.map byteToSpec (List.drop (i.val + 1) seg.val)) with e | d
      · have hp' := hp
        simp only [List.map_drop] at hp'
        simp [percentDecode_plain _ _ hnp, hp', Bind.bind, Except.bind]
      · have hp' := hp
        simp only [List.map_drop] at hp'
        simp [percentDecode_plain _ _ hnp, hp', hout1, Bind.bind, Except.bind]
  · rename_i hge
    have hi' : i.val = seg.length := by scalar_tac
    have hd : seg.val.drop i.val = [] := by simp [List.drop_eq_nil_iff]; omega
    apply WP.spec_bind (validate_segment_spec (alloc.vec.Vec.deref out))
    intro r hr
    rw [hd]
    cases r with
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      have hr' : Facl.validateSegment (List.map byteToSpec out.val) = .ok () := by
        simpa [resToSpec, alloc.vec.Vec.deref] using hr.symm
      refine (WP.spec_ok _).mpr ?_
      simp [resToSpec, Facl.percentDecode.eq_1, hr', Bind.bind, Except.bind]
      rfl
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      have hr' : Facl.validateSegment (List.map byteToSpec out.val) =
          .error (path.pathErrorToSpec e) := by
        simpa [resToSpec, alloc.vec.Vec.deref] using hr.symm
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, Aeneas.Std.bind_tc_ok]
      refine (WP.spec_ok _).mpr ?_
      simp [resToSpec, Facl.percentDecode.eq_1, hr', Bind.bind, Except.bind]
termination_by seg.length - i.val
decreasing_by all_goals scalar_tac

private theorem decode_segment_spec (seg : Slice U8) :
    path.decode_segment seg ⦃ r => resToSpec (fun v => v.val.map byteToSpec) r =
      Facl.decodeSegment (seg.val.map byteToSpec) ⦄ := by
  unfold path.decode_segment
  refine WP.spec_mono (decode_segment_loop_spec seg (alloc.vec.Vec.new U8) 0#usize (by simp)
    (by have := Slice.length_ineq seg; simp)) ?_
  intro r hr
  rw [hr]
  simp [Facl.decodeSegment]

private def segCheck (seg : List UInt8) : Except Facl.PathError (List UInt8) :=
  if '?'.toUInt8 ∈ seg ∨ '#'.toUInt8 ∈ seg then .error .queryOrFragment
  else if seg = [] then .error .emptySegment
  else .ok seg

private theorem splitOnPPrepend_head (p : UInt8 → Bool) (xs acc : List UInt8) :
    ∃ h t, List.splitOnPPrepend p xs acc = (acc.reverse ++ h) :: t := by
  rw [List.splitOnPPrepend_eq_modifyHead]
  cases hs : List.splitOnP p xs with
  | nil => exact absurd hs (List.splitOnP_ne_nil p xs)
  | cons h t => exact ⟨h, t, by simp⟩

private theorem mapM_bad_part (p : UInt8 → Bool) (xs acc : List UInt8)
    (h : '?'.toUInt8 ∈ acc ∨ '#'.toUInt8 ∈ acc) :
    List.mapM segCheck (List.splitOnPPrepend p xs acc) = .error .queryOrFragment := by
  obtain ⟨hd, t, e⟩ := splitOnPPrepend_head p xs acc
  have : '?'.toUInt8 ∈ acc.reverse ++ hd ∨ '#'.toUInt8 ∈ acc.reverse ++ hd := by
    simpa using Or.imp (fun h => Or.inl h) (fun h => Or.inl h) h
  have hc : segCheck (acc.reverse ++ hd) = .error .queryOrFragment := by
    unfold segCheck; exact ite_eq_left this
  rw [e, List.mapM_cons, hc]
  rfl

private theorem split_raw_loop_spec (raw : Slice U8)
    (segments : alloc.vec.Vec (alloc.vec.Vec U8)) (current : alloc.vec.Vec U8) (i : Usize)
    (hraw : 1 < raw.length) (hi : i.val ≤ raw.length)
    (hcur : ∀ b ∈ current.val, b ≠ 63#u8 ∧ b ≠ 35#u8)
    (hs : segments.length + (raw.length - i.val) < Usize.max)
    (hc : current.length + (raw.length - i.val) ≤ Usize.max) :
    path.split_raw_loop raw segments current i ⦃ r =>
      resToSpec (fun v => v.val.map (·.val.map byteToSpec)) r =
        (List.mapM segCheck (List.splitOnPPrepend (· == '/'.toUInt8)
          ((raw.val.drop i.val).map byteToSpec) (current.val.map byteToSpec).reverse)).map
          (fun ps => segments.val.map (·.val.map byteToSpec) ++ ps) ⦄ := by
  have hlen : raw.val.length = raw.length := rfl
  have hmax := Slice.length_ineq raw
  have hs' : segments.val.length + (raw.val.length - i.val) < Usize.max := hs
  have hc' : current.val.length + (raw.val.length - i.val) ≤ Usize.max := hc
  have h47 : '/'.toUInt8 = byteToSpec 47#u8 := by decide
  have h63 : '?'.toUInt8 = byteToSpec 63#u8 := by decide
  have h35 : '#'.toUInt8 = byteToSpec 35#u8 := by decide
  unfold path.split_raw_loop
  simp only [UScalar.lt_equiv, Slice.len_val]
  split
  · rename_i hlt
    have hlt' : i.val < raw.val.length := hlt
    apply WP.spec_bind (Slice.index_usize_spec raw i hlt')
    intro b hb
    have hdrop : raw.val.drop i.val = b :: raw.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hb]
    rw [hdrop, List.map_cons]
    split
    · rename_i h63'
      refine (WP.spec_ok _).mpr ?_
      have hb63 : byteToSpec b = '?'.toUInt8 := by rw [h63, h63']
      have hne : (byteToSpec b == '/'.toUInt8) = false := by rw [hb63]; decide
      rw [List.splitOnPPrepend_cons_neg (p := fun x => x == '/'.toUInt8) hne, mapM_bad_part _ _ _ (Or.inl (by simp [hb63]))]
      simp only [resToSpec, path.pathErrorToSpec]; rfl
    · rename_i h63'
      split
      · rename_i h35'
        refine (WP.spec_ok _).mpr ?_
        have hb35 : byteToSpec b = '#'.toUInt8 := by rw [h35, h35']
        have hne : (byteToSpec b == '/'.toUInt8) = false := by rw [hb35]; decide
        rw [List.splitOnPPrepend_cons_neg (p := fun x => x == '/'.toUInt8) hne, mapM_bad_part _ _ _ (Or.inr (by simp [hb35]))]
        simp only [resToSpec, path.pathErrorToSpec]; rfl
      · rename_i h35'
        split
        · rename_i h47'
          have hb47 : byteToSpec b = '/'.toUInt8 := by rw [h47, h47']
          have hpos : (byteToSpec b == '/'.toUInt8) = true := by rw [hb47]; simp
          rw [List.splitOnPPrepend_cons_pos (p := fun x => x == '/'.toUInt8) hpos, List.reverse_reverse]
          apply WP.spec_bind (alloc.vec.Vec.is_empty.spec current)
          intro b1 hb1
          split
          · rename_i he
            refine (WP.spec_ok _).mpr ?_
            have hnil : current.val = [] := by
              have : current.length = 0 := by simpa [he] using hb1
              exact List.length_eq_zero_iff.mp this
            simp [hnil, List.mapM_cons, segCheck, resToSpec, path.pathErrorToSpec, Bind.bind,
              Except.bind, Except.map]
          · rename_i hne
            have hne' : current.length ≠ 0 := by
              have : b1 = false := by simpa using hne
              simpa [this] using hb1
            have hcne : current.val ≠ [] := fun h => hne' (by simp [alloc.vec.Vec.length, h])
            apply WP.spec_bind (alloc.vec.Vec.push_spec segments current (by scalar_tac))
            intro segments1 hseg1
            apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
            intro i2 hi2
            have hi2v : i2.val = i.val + 1 := by simpa using hi2
            refine WP.spec_mono (split_raw_loop_spec raw segments1 (alloc.vec.Vec.new U8) i2 hraw
              (by scalar_tac) (by simp) (by simp only [alloc.vec.Vec.length, hseg1, hi2v]; simp; scalar_tac)
              (by simp; scalar_tac)) ?_
            intro r hr
            have hcs : segCheck (current.val.map byteToSpec) = .ok (current.val.map byteToSpec) := by
              unfold segCheck
              have h1 : ¬ ('?'.toUInt8 ∈ current.val.map byteToSpec ∨
                  '#'.toUInt8 ∈ current.val.map byteToSpec) := by
                rw [h63, h35, mem_map_byteToSpec, mem_map_byteToSpec]
                rintro (h | h)
                · exact (hcur _ h).1 rfl
                · exact (hcur _ h).2 rfl
              have h2 : ¬ (current.val.map byteToSpec = []) := by simpa using hcne
              rw [ite_eq_right h1, ite_eq_right h2]
            have hnew : (alloc.vec.Vec.new U8).val = [] := rfl
            rw [hr, hi2v, hnew, List.map_nil, List.reverse_nil, List.mapM_cons, hcs]
            simp only [List.splitOnPPrepend_nil_right]
            rcases List.mapM segCheck (List.splitOnP (fun x => x == '/'.toUInt8)
              (List.map byteToSpec (List.drop (i.val + 1) raw.val))) with e | d
            · simp [Bind.bind, Except.bind, Except.map]
            · simp [Bind.bind, Except.bind, Except.map, hseg1, Pure.pure, Except.pure]
        · rename_i h47'
          have hneq : (byteToSpec b == '/'.toUInt8) = false := by
            rw [h47]
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro h; exact h47' (byteToSpec_inj h)
          rw [List.splitOnPPrepend_cons_neg (p := fun x => x == '/'.toUInt8) hneq]
          apply WP.spec_bind (alloc.vec.Vec.push_spec current b (by scalar_tac))
          intro current1 hcur1
          apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          intro i2 hi2
          have hi2v : i2.val = i.val + 1 := by simpa using hi2
          refine WP.spec_mono (split_raw_loop_spec raw segments current1 i2 hraw (by scalar_tac)
            (by
              intro x hx
              rw [hcur1] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hcur x hx
              · simp at hx; subst hx; exact ⟨h63', h35'⟩)
            (by scalar_tac) (by simp only [alloc.vec.Vec.length, hcur1, hi2v]; simp; scalar_tac)) ?_
          intro r hr
          rw [hr, hi2v, hcur1]
          simp
  · rename_i hge
    have hd : raw.val.drop i.val = [] := by simp [List.drop_eq_nil_iff]; omega
    rw [hd]
    simp only [List.map_nil, List.splitOnPPrepend_nil, List.reverse_reverse]
    apply WP.spec_bind (alloc.vec.Vec.is_empty.spec current)
    intro b1 hb1
    split
    · rename_i he
      have hnil : current.val = [] := by
        have : current.length = 0 := by simpa [he] using hb1
        exact List.length_eq_zero_iff.mp this
      split
      · refine (WP.spec_ok _).mpr ?_
        simp [hnil, List.mapM_cons, segCheck, resToSpec, path.pathErrorToSpec, Bind.bind,
          Except.bind, Except.map]
      · scalar_tac
    · rename_i hne
      have hne' : current.length ≠ 0 := by
        have : b1 = false := by simpa using hne
        simpa [this] using hb1
      have hcne : current.val ≠ [] := fun h => hne' (by simp [alloc.vec.Vec.length, h])
      apply WP.spec_bind (alloc.vec.Vec.push_spec segments current (by scalar_tac))
      intro segments1 hseg1
      refine (WP.spec_ok _).mpr ?_
      have hcs : segCheck (current.val.map byteToSpec) = .ok (current.val.map byteToSpec) := by
        unfold segCheck
        have h1 : ¬ ('?'.toUInt8 ∈ current.val.map byteToSpec ∨
            '#'.toUInt8 ∈ current.val.map byteToSpec) := by
          rw [h63, h35, mem_map_byteToSpec, mem_map_byteToSpec]
          rintro (h | h)
          · exact (hcur _ h).1 rfl
          · exact (hcur _ h).2 rfl
        have h2 : ¬ (current.val.map byteToSpec = []) := by simpa using hcne
        rw [ite_eq_right h1, ite_eq_right h2]
      simp [List.mapM_cons, hcs, resToSpec, hseg1, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
termination_by raw.length - i.val
decreasing_by all_goals scalar_tac

private theorem split_raw_spec (raw : Slice U8) :
    path.split_raw raw ⦃ r =>
      resToSpec (fun v => v.val.map (·.val.map byteToSpec)) r =
        Facl.splitPath (raw.val.map byteToSpec) ⦄ := by
  have h47 : '/'.toUInt8 = byteToSpec 47#u8 := by decide
  have hmax := Slice.length_ineq raw
  unfold path.split_raw
  apply WP.spec_bind (core.slice.Slice.is_empty_spec raw)
  intro b hb
  split
  · rename_i hemp
    have hnil : raw.val = [] := by
      have : raw.length = 0 := by simpa [hemp] using hb
      exact List.length_eq_zero_iff.mp this
    refine (WP.spec_ok _).mpr ?_
    simp [hnil, Facl.splitPath, resToSpec, path.pathErrorToSpec]
  · rename_i hemp
    have hlen : 0 < raw.length := by
      have : ¬ (raw.length = 0) := fun h => hemp (by rw [hb]; exact h)
      omega
    apply WP.spec_bind (Slice.index_usize_spec raw 0#usize (by simpa using hlen))
    intro b0 hb0
    obtain ⟨l, hl⟩ : ∃ l, raw.val = b0 :: l := by
      have hne : raw.val ≠ [] := fun h => by simp [Slice.length, h] at hlen
      refine ⟨raw.val.tail, ?_⟩
      rcases hh : raw.val with _ | ⟨x, l⟩
      · exact absurd hh hne
      · simp [hh] at hb0 ⊢
        exact hb0.symm
    split
    · rename_i hne
      refine (WP.spec_ok _).mpr ?_
      have : ¬ b0 = 47#u8 := by simpa using hne
      have h' : byteToSpec b0 ≠ '/'.toUInt8 := by
        rw [h47]; intro h; exact this (byteToSpec_inj h)
      simp [hl, Facl.splitPath, h', resToSpec, path.pathErrorToSpec]
    · rename_i hne
      have h0 : b0 = 47#u8 := UScalar.eq_of_val_eq (by simpa using hne)
      subst h0
      have h47' : byteToSpec 47#u8 = '/'.toUInt8 := h47.symm
      rcases l with _ | ⟨x, l'⟩
      · have hlen1 : raw.length = 1 := by
          have : raw.val.length = raw.length := rfl
          rw [hl] at this
          simpa using this.symm
        unfold path.split_raw_loop
        have hnot : ¬ (1#usize : Usize).val < raw.length := by simp [hlen1]
        simp only [UScalar.lt_equiv, Slice.len_val, hnot, ite_false]
        apply WP.spec_bind (alloc.vec.Vec.is_empty.spec (alloc.vec.Vec.new U8))
        intro b1 hb1
        have hb1' : b1 = true := by simp at hb1; simpa using hb1
        subst hb1'
        refine (WP.spec_ok _).mpr ?_
        simp [hl, Facl.splitPath, h47', resToSpec]
      · have hraw : 1 < raw.length := by
          have : raw.val.length = raw.length := rfl
          rw [hl] at this
          simp only [List.length_cons] at this
          omega
        have hmax' : raw.length ≤ Usize.max := hmax
        refine WP.spec_mono (split_raw_loop_spec raw (alloc.vec.Vec.new _) (alloc.vec.Vec.new U8)
          1#usize hraw (by simpa using hraw.le) (by simp) (by simp; omega) (by simp; omega)) ?_
        intro r hr
        rw [hr]
        simp [hl, Facl.splitPath, h47', List.splitOn, List.splitOnPPrepend_nil_right]
        show Except.map (fun ps => ps) (List.mapM segCheck _) = List.mapM segCheck _
        generalize List.mapM segCheck _ = M
        cases M <;> rfl

private theorem canonicalize_loop_spec (encoded : alloc.vec.Vec (alloc.vec.Vec U8))
    (out : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize)
    (hi : i.val ≤ encoded.length) (hb : out.length + (encoded.length - i.val) ≤ Usize.max) :
    path.canonicalize_loop encoded out i ⦃ r =>
      resToSpec (fun v => v.val.map (·.val.map byteToSpec)) r =
        ((encoded.val.drop i.val).mapM
          (fun v => Facl.decodeSegment (v.val.map byteToSpec))).map
          (fun ds => out.val.map (·.val.map byteToSpec) ++ ds) ⦄ := by
  have hi' : i.val ≤ encoded.val.length := hi
  have hb' : out.val.length + (encoded.val.length - i.val) ≤ Usize.max := hb
  have hmax := alloc.vec.Vec.len_ineq encoded
  unfold path.canonicalize_loop
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, alloc.vec.Vec.index_slice_index]
  split
  · rename_i hlt
    have hlt' : i.val < encoded.val.length := hlt
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec encoded i hlt')
    intro v hv
    have hdrop : encoded.val.drop i.val = v :: encoded.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt', hv]
    apply WP.spec_bind (decode_segment_spec (alloc.vec.Vec.deref v))
    intro r hr
    rw [hdrop, List.mapM_cons]
    cases r with
    | Ok val =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      have hr' : Facl.decodeSegment (v.val.map byteToSpec) = .ok (val.val.map byteToSpec) := by
        simpa [resToSpec, alloc.vec.Vec.deref] using hr.symm
      apply WP.spec_bind (alloc.vec.Vec.push_spec out val (by simp only [alloc.vec.Vec.length] at hb ⊢; omega))
      intro out1 hout1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      have hi2v : i2.val = i.val + 1 := by simpa using hi2
      refine WP.spec_mono (canonicalize_loop_spec encoded out1 i2 (by scalar_tac)
        (by simp only [alloc.vec.Vec.length, hout1, hi2v]; simp; scalar_tac)) ?_
      intro r hr2
      rw [hr2, hi2v, hr']
      simp only [Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
      split <;> simp [hout1]
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      have hr' : Facl.decodeSegment (v.val.map byteToSpec) = .error (path.pathErrorToSpec e) := by
        simpa [resToSpec, alloc.vec.Vec.deref] using hr.symm
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, Aeneas.Std.bind_tc_ok]
      refine (WP.spec_ok _).mpr ?_
      rw [hr']
      simp [resToSpec, Bind.bind, Except.bind, Except.map]
  · rename_i hge
    have hel : encoded.length = encoded.val.length := rfl
    have : i.val = encoded.val.length := by omega
    simp [this, resToSpec, Except.map, Pure.pure, Except.pure]
termination_by encoded.length - i.val
decreasing_by all_goals scalar_tac

end FaclCore

namespace FaclCore.path

private theorem mapM_decode (l : List (alloc.vec.Vec U8)) :
    List.mapM Facl.decodeSegment (l.map (fun x => x.val.map byteToSpec)) =
      List.mapM (fun v => Facl.decodeSegment (v.val.map byteToSpec)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.mapM_cons, ih]

theorem canonicalize_spec (raw : Slice U8) :
    canonicalize raw ⦃ r => canonicalToSpec r = Facl.canonicalize (bytesToSpec raw) ⦄ := by
  have hc : ∀ r : core.result.Result (alloc.vec.Vec (alloc.vec.Vec U8)) PathError,
      canonicalToSpec r = resToSpec (fun v => v.val.map (·.val.map byteToSpec)) r := by
    intro r; cases r <;> rfl
  unfold canonicalize
  apply WP.spec_bind (split_raw_spec raw)
  intro r hr
  cases r with
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
    refine WP.spec_mono (canonicalize_loop_spec val (alloc.vec.Vec.new _) 0#usize (by simp)
      (by have := alloc.vec.Vec.len_ineq val; simp)) ?_
    intro r' hr'
    rw [hc, hr', Facl.canonicalize, bytesToSpec, ← hr]
    have h0 : (0#usize).val = 0 := rfl
    have hnew : (alloc.vec.Vec.new (alloc.vec.Vec U8)).val = [] := rfl
    simp only [resToSpec, Bind.bind, Except.bind, Except.map, h0, hnew, List.drop_zero, List.map_nil,
      List.nil_append]
    rw [mapM_decode]
    cases List.mapM (fun v => Facl.decodeSegment (List.map byteToSpec v.val)) val.val <;> rfl
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, Aeneas.Std.bind_tc_ok]
    refine (WP.spec_ok _).mpr ?_
    rw [Facl.canonicalize, bytesToSpec, ← hr]
    simp [canonicalToSpec, resToSpec, Bind.bind, Except.bind]

end FaclCore.path

namespace FaclCore.decide

private theorem usize_lit3 (h) : Usize.ofNatCore 3 h = 3#usize := rfl
private theorem usize_lit4 (h) : Usize.ofNatCore 4 h = 4#usize := rfl
private theorem usize_lit5 (h) : Usize.ofNatCore 5 h = 5#usize := rfl
private theorem usize_lit6 (h) : Usize.ofNatCore 6 h = 6#usize := rfl
private theorem usize_lit7 (h) : Usize.ofNatCore 7 h = 7#usize := rfl

theorem method_bit_spec (bytes : Slice U8) :
    method_bit bytes ⦃ bit => bit.val = Facl.methodBit (bytesToSpec bytes) ⦄ := by
  unfold method_bit
  have hs : bytesToSpec bytes = bytes.val.map byteToSpec := rfl
  rw [hs, methodBit_eq']
  obtain ⟨l, hl⟩ : ∃ l, bytes.val = l := ⟨_, rfl⟩
  rw [hl]
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, l⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Slice.len, hl, Slice.index_usize, usize_lit3, usize_lit4, usize_lit5, usize_lit6, usize_lit7]
  all_goals (clear hs hl; split_ifs <;> (simp only [WP.spec_ok]; scalar_tac))

end FaclCore.decide

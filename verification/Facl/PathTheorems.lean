import Facl.Spec

namespace Facl

private theorem inRange_iff (a b x : UInt8) :
    inRange (a, b) x = true ↔ a.toNat ≤ x.toNat ∧ x.toNat ≤ b.toNat := by
  simp [inRange, UInt8.le_iff_toNat_le]

private theorem find_row (b : UInt8) :
    utf8Rows.find? (·.head?.any (inRange · b)) =
      if b.toNat ≤ 0x7F then some [(0x00, 0x7F)]
      else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then some [(0xC2, 0xDF), (0x80, 0xBF)]
      else if b.toNat = 0xE0 then some [(0xE0, 0xE0), (0xA0, 0xBF), (0x80, 0xBF)]
      else if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then some [(0xE1, 0xEC), (0x80, 0xBF), (0x80, 0xBF)]
      else if b.toNat = 0xED then some [(0xED, 0xED), (0x80, 0x9F), (0x80, 0xBF)]
      else if 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF then some [(0xEE, 0xEF), (0x80, 0xBF), (0x80, 0xBF)]
      else if b.toNat = 0xF0 then some [(0xF0, 0xF0), (0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)]
      else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then some [(0xF1, 0xF3), (0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)]
      else if b.toNat = 0xF4 then some [(0xF4, 0xF4), (0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)]
      else none := by
  have h := b.toNat_lt
  simp only [utf8Rows, List.find?, List.head?, Option.any, inRange, UInt8.le_iff_toNat_le]
  by_cases h1 : b.toNat ≤ 0x7F
  · simp [h1]
  by_cases h2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h3 : b.toNat = 0xE0
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h4 : 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h5 : b.toNat = 0xED
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h6 : 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h7 : b.toNat = 0xF0
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h8 : 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  by_cases h9 : b.toNat = 0xF4
  · simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
  simp [*] <;> (repeat' split) <;> first | rfl | (exfalso; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)

private theorem go_nil_cons (b : UInt8) (t : List UInt8) :
    utf8Go [] (b :: t) =
      if b.toNat ≤ 0x7F then utf8Go [] t
      else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then utf8Go [(0x80, 0xBF)] t
      else if b.toNat = 0xE0 then utf8Go [(0xA0, 0xBF), (0x80, 0xBF)] t
      else if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then utf8Go [(0x80, 0xBF), (0x80, 0xBF)] t
      else if b.toNat = 0xED then utf8Go [(0x80, 0x9F), (0x80, 0xBF)] t
      else if 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF then utf8Go [(0x80, 0xBF), (0x80, 0xBF)] t
      else if b.toNat = 0xF0 then utf8Go [(0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)] t
      else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then utf8Go [(0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)] t
      else if b.toNat = 0xF4 then utf8Go [(0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)] t
      else false := by
  rw [utf8Go, find_row]
  by_cases h1 : b.toNat ≤ 0x7F
  · simp [h1]
  by_cases h2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
  · simp [*]
  by_cases h3 : b.toNat = 0xE0
  · simp [*]
  by_cases h4 : 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC
  · simp [*]
  by_cases h5 : b.toNat = 0xED
  · simp [*]
  by_cases h6 : 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF
  · simp [*]
  by_cases h7 : b.toNat = 0xF0
  · simp [*]
  by_cases h8 : 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3
  · simp [*]
  by_cases h9 : b.toNat = 0xF4
  · simp [*]
  simp [*]

private theorem go_cons (r : UInt8 × UInt8) (p : List (UInt8 × UInt8)) (b : UInt8) (t : List UInt8) :
    utf8Go (r :: p) (b :: t) = (inRange r b && utf8Go p t) := rfl

private theorem ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat_ofNat']

private theorem ofNat_eq {b : UInt8} {n : Nat} (h : b.toNat = n) (hn : n < 256) :
    UInt8.ofNat n = b := by
  apply UInt8.toNat_inj.1
  rw [ofNat_toNat]; omega

private theorem exists_char (n : Nat) (h : n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)) :
    ∃ c : Char, c.val.toNat = n :=
  ⟨Char.ofNatAux n h, by simp [Char.ofNatAux]⟩

private theorem enc_len2 (b0 b1 : UInt8) (n : Nat) (c : Char) (hc : c.val.toNat = n)
    (h0 : 0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (hn : n = (b0.toNat - 0xC0) * 64 + (b1.toNat - 0x80)) :
    String.utf8EncodeChar c = [b0, b1] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [hc]
  have a : ¬ n ≤ 0x7f := by omega
  have b : n ≤ 0x7ff := by omega
  simp only [a, b, ↓reduceIte, List.cons.injEq, and_true]
  exact ⟨ofNat_eq (by omega) (by omega), ofNat_eq (by omega) (by omega)⟩

private theorem enc_len3 (b0 b1 b2 : UInt8) (n : Nat) (c : Char) (hc : c.val.toNat = n)
    (h0 : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xEF) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (h2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)
    (hn : n = (b0.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80))
    (hE0 : b0.toNat = 0xE0 → 0xA0 ≤ b1.toNat) :
    String.utf8EncodeChar c = [b0, b1, b2] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [hc]
  have a : ¬ n ≤ 0x7f := by omega
  have b : ¬ n ≤ 0x7ff := by omega
  have d : n ≤ 0xffff := by omega
  simp only [a, b, d, ↓reduceIte, List.cons.injEq, and_true]
  exact ⟨ofNat_eq (by omega) (by omega), ofNat_eq (by omega) (by omega),
    ofNat_eq (by omega) (by omega)⟩

private theorem enc_len4 (b0 b1 b2 b3 : UInt8) (n : Nat) (c : Char) (hc : c.val.toNat = n)
    (h0 : 0xF0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (h2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF) (h3 : 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)
    (hn : n = (b0.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + (b2.toNat - 0x80) * 64 +
      (b3.toNat - 0x80))
    (hF0 : b0.toNat = 0xF0 → 0x90 ≤ b1.toNat) :
    String.utf8EncodeChar c = [b0, b1, b2, b3] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [hc]
  have a : ¬ n ≤ 0x7f := by omega
  have b : ¬ n ≤ 0x7ff := by omega
  have d : ¬ n ≤ 0xffff := by omega
  simp only [a, b, d, ↓reduceIte, List.cons.injEq, and_true]
  exact ⟨ofNat_eq (by omega) (by omega), ofNat_eq (by omega) (by omega),
    ofNat_eq (by omega) (by omega), ofNat_eq (by omega) (by omega)⟩

private theorem ir {a b x : UInt8} (h : a.toNat ≤ x.toNat ∧ x.toNat ≤ b.toNat) :
    inRange (a, b) x = true := (inRange_iff a b x).2 h

private theorem and1 {p c : Bool} (hp : p = true) : (p && c) = c := by simp [hp]

private theorem and2 {p q c : Bool} (hp : p = true) (hq : q = true) : (p && (q && c)) = c := by
  simp [hp, hq]

private theorem and3 {p q r c : Bool} (hp : p = true) (hq : q = true) (hr : r = true) :
    (p && (q && (r && c))) = c := by simp [hp, hq, hr]

private theorem L1 (b : UInt8) (t : List UInt8) (h : b.toNat ≤ 0x7F) :
    utf8Go [] (b :: t) = utf8Go [] t := by
  rw [go_nil_cons]; simp [h]

private theorem L2 (b0 b1 : UInt8) (t : List UInt8)
    (h0 : 0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF) :
    utf8Go [] (b0 :: b1 :: t) = utf8Go [] t := by
  have n1 : ¬ b0.toNat ≤ 0x7F := by omega
  rw [go_nil_cons]
  simp only [n1, h0, and_self, ↓reduceIte, go_cons]
  exact and1 (ir (by simp; omega))

private theorem L3 (b0 b1 b2 : UInt8) (t : List UInt8)
    (h0 : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xEF) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (h2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)
    (hE0 : b0.toNat = 0xE0 → 0xA0 ≤ b1.toNat) (hED : b0.toNat = 0xED → b1.toNat ≤ 0x9F) :
    utf8Go [] (b0 :: b1 :: b2 :: t) = utf8Go [] t := by
  have n1 : ¬ b0.toNat ≤ 0x7F := by omega
  have n2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF) := by omega
  rw [go_nil_cons]
  simp only [n1, n2, ↓reduceIte, go_cons]
  by_cases a : b0.toNat = 0xE0
  · simp only [a, ↓reduceIte]
    exact and2 (ir (by simp; omega)) (ir (by simp; omega))
  by_cases b : 0xE1 ≤ b0.toNat ∧ b0.toNat ≤ 0xEC
  · simp only [a, b, ↓reduceIte]
    exact and2 (ir (by simp; omega)) (ir (by simp; omega))
  by_cases c : b0.toNat = 0xED
  · simp only [c, ↓reduceIte]
    exact and2 (ir (by simp; omega)) (ir (by simp; omega))
  have d : 0xEE ≤ b0.toNat ∧ b0.toNat ≤ 0xEF := by omega
  simp only [a, b, c, d, ↓reduceIte]
  exact and2 (ir (by simp; omega)) (ir (by simp; omega))

private theorem L4 (b0 b1 b2 b3 : UInt8) (t : List UInt8)
    (h0 : 0xF0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4) (h1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (h2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF) (h3 : 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)
    (hF0 : b0.toNat = 0xF0 → 0x90 ≤ b1.toNat) (hF4 : b0.toNat = 0xF4 → b1.toNat ≤ 0x8F) :
    utf8Go [] (b0 :: b1 :: b2 :: b3 :: t) = utf8Go [] t := by
  have n1 : ¬ b0.toNat ≤ 0x7F := by omega
  have n2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF) := by omega
  have n3 : ¬ b0.toNat = 0xE0 := by omega
  have n4 : ¬ (0xE1 ≤ b0.toNat ∧ b0.toNat ≤ 0xEC) := by omega
  have n5 : ¬ b0.toNat = 0xED := by omega
  have n6 : ¬ (0xEE ≤ b0.toNat ∧ b0.toNat ≤ 0xEF) := by omega
  rw [go_nil_cons]
  simp only [n1, n2, n3, n4, n5, n6, ↓reduceIte, go_cons]
  by_cases a : b0.toNat = 0xF0
  · simp only [a, ↓reduceIte]
    exact and3 (ir (by simp; omega)) (ir (by simp; omega)) (ir (by simp; omega))
  by_cases b : 0xF1 ≤ b0.toNat ∧ b0.toNat ≤ 0xF3
  · simp only [a, b, ↓reduceIte]
    exact and3 (ir (by simp; omega)) (ir (by simp; omega)) (ir (by simp; omega))
  have c : b0.toNat = 0xF4 := by omega
  simp only [c, ↓reduceIte]
  exact and3 (ir (by simp; omega)) (ir (by simp; omega)) (ir (by simp; omega))

private theorem go_enc (c : Char) (rest : List UInt8) :
    utf8Go [] (String.utf8EncodeChar c ++ rest) = utf8Go [] rest := by
  have hc : c.val.toNat.isValidChar := c.valid
  unfold String.utf8EncodeChar
  dsimp only
  generalize c.val.toNat = v at hc ⊢
  have hc' : v < 0xd800 ∨ (0xdfff < v ∧ v < 0x110000) := hc
  by_cases h1 : v ≤ 0x7f
  · simp only [h1, ↓reduceIte, List.cons_append, List.nil_append]
    have e0 := ofNat_toNat v
    generalize UInt8.ofNat v = b0 at e0 ⊢
    exact L1 _ _ (by omega)
  by_cases h2 : v ≤ 0x7ff
  · simp only [h1, h2, ↓reduceIte, List.cons_append, List.nil_append]
    have e0 := ofNat_toNat (v / 64 % 0x20 + 0xc0)
    generalize UInt8.ofNat (v / 64 % 0x20 + 0xc0) = b0 at e0 ⊢
    have e1 := ofNat_toNat (v % 0x40 + 0x80)
    generalize UInt8.ofNat (v % 0x40 + 0x80) = b1 at e1 ⊢
    exact L2 _ _ _ (by omega) (by omega)
  by_cases h3 : v ≤ 0xffff
  · simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append]
    have e0 := ofNat_toNat (v / 4096 % 0x10 + 0xe0)
    generalize UInt8.ofNat (v / 4096 % 0x10 + 0xe0) = b0 at e0 ⊢
    have e1 := ofNat_toNat (v / 64 % 0x40 + 0x80)
    generalize UInt8.ofNat (v / 64 % 0x40 + 0x80) = b1 at e1 ⊢
    have e2 := ofNat_toNat (v % 0x40 + 0x80)
    generalize UInt8.ofNat (v % 0x40 + 0x80) = b2 at e2 ⊢
    exact L3 _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append]
  have e0 := ofNat_toNat (v / 262144 % 0x08 + 0xf0)
  generalize UInt8.ofNat (v / 262144 % 0x08 + 0xf0) = b0 at e0 ⊢
  have e1 := ofNat_toNat (v / 4096 % 0x40 + 0x80)
  generalize UInt8.ofNat (v / 4096 % 0x40 + 0x80) = b1 at e1 ⊢
  have e2 := ofNat_toNat (v / 64 % 0x40 + 0x80)
  generalize UInt8.ofNat (v / 64 % 0x40 + 0x80) = b2 at e2 ⊢
  have e3 := ofNat_toNat (v % 0x40 + 0x80)
  generalize UInt8.ofNat (v % 0x40 + 0x80) = b3 at e3 ⊢
  exact L4 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem enc_len1 (b0 : UInt8) (n : Nat) (c : Char) (hc : c.val.toNat = n)
    (h0 : b0.toNat ≤ 0x7F) (hn : n = b0.toNat) : String.utf8EncodeChar c = [b0] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [hc]
  have a : n ≤ 0x7f := by omega
  simp only [a, ↓reduceIte, List.cons.injEq, and_true]
  exact ofNat_eq (by omega) (by omega)

private theorem step (b : UInt8) (t : List UInt8) (h : utf8Go [] (b :: t) = true) :
    ∃ (c : Char) (rest : List UInt8), b :: t = String.utf8EncodeChar c ++ rest ∧
      utf8Go [] rest = true := by
  rw [go_nil_cons] at h
  by_cases a1 : b.toNat ≤ 0x7F
  · simp only [a1, ↓reduceIte] at h
    obtain ⟨c, hc⟩ := exists_char b.toNat (by omega)
    exact ⟨c, t, by rw [enc_len1 b _ c hc a1 rfl]; rfl, h⟩
  by_cases a2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
  · simp only [a1, a2, and_self, ↓reduceIte] at h
    rcases t with _ | ⟨b1, t'⟩
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char ((b.toNat - 0xC0) * 64 + (b1.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len2 b b1 _ c hc a2 (by omega) rfl]; rfl, h.2⟩
  have a2' : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := a2
  by_cases a3 : b.toNat = 0xE0
  · simp only [a3, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, t'⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len3 b b1 b2 _ c hc (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2⟩
  by_cases a4 : 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC
  · simp only [a1, a2', a3, a4, and_self, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, t'⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len3 b b1 b2 _ c hc (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2⟩
  have a4' : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := a4
  by_cases a5 : b.toNat = 0xED
  · simp only [a5, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, t'⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len3 b b1 b2 _ c hc (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2⟩
  have a5' : ¬ (b.toNat = 0xED) := a5
  by_cases a6 : 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF
  · simp only [a1, a2', a3, a4', a5', a6, and_self, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, t'⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + (b2.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len3 b b1 b2 _ c hc (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2⟩
  have a6' : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := a6
  by_cases a7 : b.toNat = 0xF0
  · simp only [a7, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, t'⟩⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + (b2.toNat - 0x80) * 64 +
          (b3.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len4 b b1 b2 b3 _ c hc (by omega) (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2.2⟩
  have a7' : ¬ (b.toNat = 0xF0) := a7
  by_cases a8 : 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3
  · simp only [a1, a2', a3, a4', a5', a6', a7', a8, and_self, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, t'⟩⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + (b2.toNat - 0x80) * 64 +
          (b3.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len4 b b1 b2 b3 _ c hc (by omega) (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2.2⟩
  have a8' : ¬ (0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3) := a8
  by_cases a9 : b.toNat = 0xF4
  · simp only [a9, ↓reduceIte] at h
    rcases t with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, t'⟩⟩⟩
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [utf8Go] at h
    · simp [go_cons, inRange_iff] at h
      obtain ⟨c, hc⟩ := exists_char
        ((b.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + (b2.toNat - 0x80) * 64 +
          (b3.toNat - 0x80)) (by omega)
      exact ⟨c, t', by rw [enc_len4 b b1 b2 b3 _ c hc (by omega) (by omega) (by omega) (by omega) rfl (by omega)]; rfl,
        h.2.2.2⟩
  have a9' : ¬ (b.toNat = 0xF4) := a9
  simp only [a1, a2', a3, a4', a5', a6', a7', a8', a9', ↓reduceIte] at h
  exact absurd h (by simp)

private theorem go_flatMap (cs : List Char) (rest : List UInt8) :
    utf8Go [] (cs.flatMap String.utf8EncodeChar ++ rest) = utf8Go [] rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons, List.append_assoc, go_enc, ih]

private theorem go_exists (n : Nat) : ∀ bytes : List UInt8, bytes.length ≤ n →
    utf8Go [] bytes = true → ∃ cs : List Char, bytes = cs.flatMap String.utf8EncodeChar := by
  induction n with
  | zero =>
    intro bytes hl _
    exact ⟨[], by simpa using hl⟩
  | succ n ih =>
    intro bytes hl h
    cases bytes with
    | nil => exact ⟨[], rfl⟩
    | cons b t =>
      obtain ⟨c, rest, hb, hr⟩ := step b t h
      have : rest.length ≤ n := by
        have := congrArg List.length hb
        have : (String.utf8EncodeChar c).length ≥ 1 := by
          unfold String.utf8EncodeChar; dsimp only; (repeat' split) <;> simp
        simp at *; omega
      obtain ⟨cs, hcs⟩ := ih rest this hr
      exact ⟨c :: cs, by simp [hb, hcs]⟩

theorem utf8Valid_iff (bytes : List UInt8) :
    utf8Valid bytes = true ↔ bytes.toByteArray.IsValidUTF8 := by
  constructor
  · intro h
    obtain ⟨cs, hcs⟩ := go_exists bytes.length bytes (Nat.le_refl _) h
    exact ⟨cs, by rw [hcs]; rfl⟩
  · rintro ⟨cs, hm⟩
    have : bytes = cs.flatMap String.utf8EncodeChar := List.toByteArray_inj.1 hm
    have := go_flatMap cs []
    simp_all [utf8Valid, utf8Go]

private theorem mapM_ok {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (out : List β), l.mapM f = .ok out → ∀ s ∈ out, ∃ a ∈ l, f a = .ok s := by
  intro l
  induction l with
  | nil => intro out h s hs; simp [pure, Except.pure] at h; subst h; simp at hs
  | cons a l ih =>
    intro out h s hs
    rw [List.mapM_cons] at h
    cases hf : f a with
    | error e => simp [hf, bind, Except.bind] at h
    | ok x =>
      cases hl : l.mapM f with
      | error e => simp [hf, hl, bind, Except.bind] at h
      | ok xs =>
        simp [hf, hl, bind, Except.bind, pure, Except.pure] at h
        subst h
        rcases List.mem_cons.1 hs with rfl | hs
        · exact ⟨a, by simp, hf⟩
        · obtain ⟨a', ha', hf'⟩ := ih xs hl s hs
          exact ⟨a', by simp [ha'], hf'⟩

private theorem map_ok {ε α β : Type} (f : α → β) (e : Except ε α) (o : β)
    (h : f <$> e = .ok o) : ∃ x, e = .ok x ∧ o = f x := by
  cases e <;> simp_all [Functor.map, Except.map]

private theorem percentDecode_ne_nil : ∀ (l o : List UInt8), percentDecode l = .ok o →
    l ≠ [] → o ≠ [] := by
  intro l o h hl
  cases l with
  | nil => exact absurd rfl hl
  | cons b rest =>
    unfold percentDecode at h
    split at h
    · obtain ⟨x, _, rfl⟩ := map_ok _ _ _ h
      simp
    · split at h
      · split at h
        · obtain ⟨x, _, rfl⟩ := map_ok _ _ _ h
          simp
        · simp at h
      · simp at h

private theorem splitPath_ne_nil {raw : List UInt8} {parts : List (List UInt8)}
    (h : splitPath raw = .ok parts) : ∀ a ∈ parts, a ≠ [] := by
  intro a ha
  unfold splitPath at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h; subst h; simp at ha
      · obtain ⟨seg, _, hf⟩ := mapM_ok _ _ _ h a ha
        split at hf
        · simp at hf
        · split at hf
          · simp at hf
          · simp at hf; subst hf; assumption

private theorem validate_facts {s : List UInt8} (h : validateSegment s = .ok ()) :
    s ≠ utf8 "." ∧ s ≠ utf8 ".." ∧ '/'.toUInt8 ∉ s ∧ 0 ∉ s ∧ s.toByteArray.IsValidUTF8 := by
  unfold validateSegment at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i h1 h2 h3
        simp only [not_or] at h1 h2
        simp only [Bool.not_eq_true] at h3
        exact ⟨h1.1, h1.2, h2.1, h2.2, (utf8Valid_iff s).1 (by simpa using h3)⟩

theorem canonicalize_segment {raw : List UInt8} {segs : List (List UInt8)}
    (h : canonicalize raw = .ok segs) : ∀ s ∈ segs,
      s ≠ [] ∧ s ≠ utf8 "." ∧ s ≠ utf8 ".." ∧ '/'.toUInt8 ∉ s ∧ 0 ∉ s ∧
        s.toByteArray.IsValidUTF8 := by
  intro s hs
  unfold canonicalize at h
  cases hsp : splitPath raw with
  | error e => simp [hsp, bind, Except.bind] at h
  | ok parts =>
    simp only [hsp, bind, Except.bind] at h
    obtain ⟨a, ha, hd⟩ := mapM_ok _ _ _ h s hs
    unfold decodeSegment at hd
    cases hp : percentDecode a with
    | error e => simp [hp, bind, Except.bind] at hd
    | ok out =>
      cases hv : validateSegment out with
      | error e => simp [hp, hv, bind, Except.bind] at hd
      | ok u =>
        simp [hp, hv, bind, Except.bind, pure, Except.pure] at hd
        subst hd
        cases u
        exact ⟨percentDecode_ne_nil a _ hp (splitPath_ne_nil hsp a ha), validate_facts hv⟩

end Facl

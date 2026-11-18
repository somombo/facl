/-! Hand-written spec of facl path matching, rule combination and `decide`.
Mirrors `facl-core` (see .ignore/plans/facl-v0.3-impl-notes.md).
Conditions are abstract: `decide` takes the evaluator as a parameter. -/
namespace Facl

/-- Rust `Seg { Lit(Vec<u8>), Var }`, generic over the segment type. -/
inductive Seg (α : Type) where
  | lit (s : α)
  | var
  deriving DecidableEq, Repr

/-- Rust `Pattern { segs, rest }`. -/
structure Pattern (α : Type) where
  segs : List (Seg α)
  rest : Bool
  deriving DecidableEq, Repr

/-- A captured value: Rust `Value::Str` (a `Var`) or `Value::List` of `Str` (the rest). -/
inductive Cap (α : Type) where
  | str (s : α)
  | path (segs : List α)
  deriving DecidableEq, Repr

/-- Segment-by-segment matching; captures come out in order. -/
def matchGo {α : Type} [DecidableEq α] (rest : Bool) : List (Seg α) → List α → Option (List (Cap α))
  | [], path =>
    if rest then some [.path path] else if path = [] then some [] else none
  | .lit s :: ss, x :: xs => if s = x then matchGo rest ss xs else none
  | .var :: ss, x :: xs => (matchGo rest ss xs).map (Cap.str x :: ·)
  | _ :: _, [] => none

/-- Rust `match_pattern`. Without `rest` the path length must equal the pattern's;
with `rest` the pattern matches a prefix and the remainder is the last capture. -/
def matchPattern {α : Type} [DecidableEq α] (p : Pattern α) (path : List α) :
    Option (List (Cap α)) :=
  matchGo p.rest p.segs path

/-- Rust `Outcome`. `notGranted` covers false, error and non-boolean. -/
inductive Outcome where
  | granted
  | notGranted
  deriving DecidableEq, Repr

inductive Verdict where
  | allow
  | deny
  deriving DecidableEq, Repr

/-- Rust `combine`: allow iff some outcome is `granted`
(the Rust is a `while` loop setting a flag; this is its closed form). -/
def combine (outs : List Outcome) : Verdict :=
  if outs.contains .granted then .allow else .deny

inductive DenyReason where
  | noMatchingRule
  | noAllowForMethod
  | conditionsNotMet
  | badRequestPath
  deriving DecidableEq, Repr

inductive Decision where
  | allow
  | deny (r : DenyReason)
  deriving DecidableEq, Repr

/-- Rust `CompiledAllow { methods: u8, cond }`. Methods are a bitmask, as in Rust,
but a `Nat` rather than a `u8` (no overflow modelling). -/
structure Allow (Cond : Type) where
  methods : Nat
  cond : Cond

structure Rule (α : Type) (Cond : Type) where
  pattern : Pattern α
  allows : List (Allow Cond)

structure Policy (α : Type) (Cond : Type) where
  rules : List (Rule α Cond)

/-- Rust `Request` restricted to what the spec needs: a method bit and canonical segments.
The `request` and `context` values are folded into the abstract evaluator. -/
structure Request (α : Type) where
  method : Nat
  path : List α

/-- An allow is applicable when its mask shares a bit with the request's method. -/
def Allow.applies {C : Type} (a : Allow C) (m : Nat) : Bool :=
  a.methods &&& m != 0

def utf8 (s : String) : List UInt8 := s.toList.flatMap String.utf8EncodeChar

/-- Rust `method_bit`: `read` is 7 and `write` is 120. Any other method gets 0, which no
allow grants. -/
def methodBits : List (String × Nat) :=
  [("GET", 1), ("HEAD", 2), ("OPTIONS", 4), ("POST", 8), ("PUT", 16), ("PATCH", 32), ("DELETE", 64)]

def methodBit (name : List UInt8) : Nat :=
  match methodBits.find? (utf8 ·.1 = name) with
  | some (_, bit) => bit
  | none => 0

/-- Outcomes of the applicable allows of one rule (empty if the rule does not match). -/
def ruleOutcomes {α C : Type} [DecidableEq α] (eval : C → List (Cap α) → Request α → Outcome)
    (r : Rule α C) (req : Request α) : List Outcome :=
  match matchPattern r.pattern req.path with
  | none => []
  | some caps => (r.allows.filter (·.applies req.method)).map (fun a => eval a.cond caps req)

def outcomes {α C : Type} [DecidableEq α] (eval : C → List (Cap α) → Request α → Outcome)
    (p : Policy α C) (req : Request α) : List Outcome :=
  p.rules.flatMap (ruleOutcomes eval · req)

/-- Rust `decide`: `matched`, `applicable`, then `combine`. -/
def decide {α C : Type} [DecidableEq α] (eval : C → List (Cap α) → Request α → Outcome)
    (p : Policy α C) (req : Request α) : Decision :=
  let matched := p.rules.any fun r => (matchPattern r.pattern req.path).isSome
  let outs := outcomes eval p req
  let applicable := !outs.isEmpty
  match combine outs with
  | .allow => .allow
  | .deny =>
    if !matched then .deny .noMatchingRule
    else if !applicable then .deny .noAllowForMethod
    else .deny .conditionsNotMet

/-- Rebuild a path from a pattern and captures (inverse of matching). -/
def instGo {α : Type} [DecidableEq α] (rest : Bool) : List (Seg α) → List (Cap α) → Option (List α)
  | [], caps =>
    if rest then (match caps with | [.path r] => some r | _ => none)
    else if caps = [] then some [] else none
  | .lit s :: ss, caps => (instGo rest ss caps).map (s :: ·)
  | .var :: ss, .str x :: cs => (instGo rest ss cs).map (x :: ·)
  | .var :: _, _ => none

def instantiate {α : Type} [DecidableEq α] (p : Pattern α) (caps : List (Cap α)) :
    Option (List α) :=
  instGo p.rest p.segs caps

/-! ## Request paths

Rust `canonicalize` and its helpers, from `path.rs`. -/

/-- Rust `PathError`. -/
inductive PathError where
  | noLeadingSlash
  | queryOrFragment
  | emptySegment
  | badPercentEncoding
  | dotSegment
  | forbiddenByte
  | invalidUtf8
  deriving DecidableEq, Repr

/-- Rust `split_raw`: after the leading `/`, the path is split at each `/`. Each part must
be non-empty and free of `?` and `#`, and the first part that is not decides the error.
The root `/` has no segments. -/
def splitPath (raw : List UInt8) : Except PathError (List (List UInt8)) :=
  match raw with
  | [] => .error .noLeadingSlash
  | b :: rest =>
    if b ≠ '/'.toUInt8 then .error .noLeadingSlash
    else if rest = [] then .ok []
    else (rest.splitOn '/'.toUInt8).mapM fun seg =>
      if '?'.toUInt8 ∈ seg ∨ '#'.toUInt8 ∈ seg then .error .queryOrFragment
      else if seg = [] then .error .emptySegment
      else .ok seg

/-- Rust `hex_value`. -/
def hexValue (b : UInt8) : Option UInt8 :=
  if '0'.toUInt8 ≤ b ∧ b ≤ '9'.toUInt8 then some (b - '0'.toUInt8)
  else if 'a'.toUInt8 ≤ b ∧ b ≤ 'f'.toUInt8 then some (b - 'a'.toUInt8 + 10)
  else if 'A'.toUInt8 ≤ b ∧ b ≤ 'F'.toUInt8 then some (b - 'A'.toUInt8 + 10)
  else none

/-- Each `%` and the two hex digits after it become one byte. -/
def percentDecode : List UInt8 → Except PathError (List UInt8)
  | [] => .ok []
  | b :: rest =>
    if b ≠ '%'.toUInt8 then (b :: ·) <$> percentDecode rest
    else match rest with
      | h :: l :: rest =>
        match hexValue h, hexValue l with
        | some h, some l => ((h * 16 + l) :: ·) <$> percentDecode rest
        | _, _ => .error .badPercentEncoding
      | _ => .error .badPercentEncoding

/-- Table 3-7 of the Unicode Standard, "Well-Formed UTF-8 Byte Sequences": for each range of
code points, the range of each byte of its encoding. -/
def utf8Rows : List (List (UInt8 × UInt8)) :=
  [[(0x00, 0x7F)],
   [(0xC2, 0xDF), (0x80, 0xBF)],
   [(0xE0, 0xE0), (0xA0, 0xBF), (0x80, 0xBF)],
   [(0xE1, 0xEC), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xED, 0xED), (0x80, 0x9F), (0x80, 0xBF)],
   [(0xEE, 0xEF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF0, 0xF0), (0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF1, 0xF3), (0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF4, 0xF4), (0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)]]

def inRange (r : UInt8 × UInt8) (b : UInt8) : Bool := r.1 ≤ b && b ≤ r.2

/-- `pending` holds the ranges for the rest of the current character. Between characters,
the next byte picks the row whose first range contains it. -/
def utf8Go : List (UInt8 × UInt8) → List UInt8 → Bool
  | [], [] => true
  | r :: pending, b :: bytes => inRange r b && utf8Go pending bytes
  | [], b :: bytes =>
    match utf8Rows.find? (·.head?.any (inRange · b)) with
    | some (_ :: pending) => utf8Go pending bytes
    | _ => false
  | _ :: _, [] => false

/-- Rust `utf8_valid`: the bytes split into characters that each fit a row of `utf8Rows`.
`utf8Valid_iff` in `Challenge.lean` states that this is Lean's `ByteArray.IsValidUTF8`. -/
def utf8Valid (bytes : List UInt8) : Bool := utf8Go [] bytes

/-- Rust `validate_segment`. -/
def validateSegment (seg : List UInt8) : Except PathError Unit :=
  if seg = utf8 "." ∨ seg = utf8 ".." then .error .dotSegment
  else if '/'.toUInt8 ∈ seg ∨ 0 ∈ seg then .error .forbiddenByte
  else if !utf8Valid seg then .error .invalidUtf8
  else .ok ()

/-- Rust `decode_segment`. -/
def decodeSegment (seg : List UInt8) : Except PathError (List UInt8) := do
  let out ← percentDecode seg
  validateSegment out
  return out

/-- Rust `canonicalize`. -/
def canonicalize (raw : List UInt8) : Except PathError (List (List UInt8)) := do
  let segs ← splitPath raw
  segs.mapM decodeSegment

end Facl

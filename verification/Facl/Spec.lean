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

/-- Method bits, identical to `facl_core::method_bit`: `read` is 7, `write` is 120. -/
def methodBit : String → Nat
  | "GET" => 1 | "HEAD" => 2 | "OPTIONS" => 4
  | "POST" => 8 | "PUT" => 16 | "PATCH" => 32 | "DELETE" => 64
  | _ => 0

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

end Facl

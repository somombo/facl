import Facl.Spec
import FaclCore.Types

open Aeneas Aeneas.Std

namespace FaclCore.decide

def outcomeToSpec : Outcome → Facl.Outcome
  | .Granted => .granted
  | .NotGranted => .notGranted

def verdictToSpec : Verdict → Facl.Verdict
  | .Allow => .allow
  | .Deny => .deny

def denyReasonToSpec : DenyReason → Facl.DenyReason
  | .NoMatchingRule => .noMatchingRule
  | .NoAllowForMethod => .noAllowForMethod
  | .ConditionsNotMet => .conditionsNotMet
  | .BadRequestPath => .badRequestPath

def decisionToSpec : Decision → Facl.Decision
  | .Allow => .allow
  | .Deny r => .deny (denyReasonToSpec r)

end FaclCore.decide

namespace FaclCore

def segmentsToSpec (segments : Slice (alloc.vec.Vec U8)) : List (List U8) :=
  segments.val.map (·.val)

def requestToSpec (method : U8) (segments : Slice (alloc.vec.Vec U8)) :
    Facl.Request (List U8) :=
  ⟨method.val, segmentsToSpec segments⟩

def path.captureToSpec : path.Capture → Facl.Cap (List U8)
  | .One s => .str s.val
  | .Rest ss => .path (ss.val.map (·.val))

def ir.segToSpec : ir.Seg → Facl.Seg (List U8)
  | .Lit l => .lit l.val
  | .Var => .var

def ir.patternToSpec (p : ir.Pattern) : Facl.Pattern (List U8) :=
  ⟨p.segs.val.map ir.segToSpec, p.rest⟩

def ir.allowToSpec {C : Type} (a : ir.CompiledAllow C) : Facl.Allow C :=
  ⟨a.methods.val, a.cond⟩

def ir.ruleToSpec {C : Type} (r : ir.Rule C) : Facl.Rule (List U8) C :=
  ⟨ir.patternToSpec r.pattern, r.allows.val.map ir.allowToSpec⟩

def ir.policyToSpec {C : Type} (p : ir.Policy C) : Facl.Policy (List U8) C :=
  ⟨p.rules.val.map ir.ruleToSpec⟩

def byteToSpec (b : U8) : UInt8 := UInt8.ofNat b.val

def bytesToSpec (s : Slice U8) : List UInt8 := s.val.map byteToSpec

def path.pathErrorToSpec : path.PathError → Facl.PathError
  | .NoLeadingSlash => .noLeadingSlash
  | .QueryOrFragment => .queryOrFragment
  | .EmptySegment => .emptySegment
  | .BadPercentEncoding => .badPercentEncoding
  | .DotSegment => .dotSegment
  | .ForbiddenByte => .forbiddenByte
  | .InvalidUtf8 => .invalidUtf8

def path.canonicalToSpec :
    core.result.Result (alloc.vec.Vec (alloc.vec.Vec U8)) path.PathError →
      Except Facl.PathError (List (List UInt8))
  | .Ok segs => .ok (segs.val.map (·.val.map byteToSpec))
  | .Err e => .error (pathErrorToSpec e)

def byteOfSpec (b : UInt8) : U8 := ⟨b.toBitVec⟩

def reservedNames : List (List U8) := ["request", "context"].map fun s => (Facl.utf8 s).map byteOfSpec

def ast.patSegToSpec : ast.PatSeg → Facl.PatSeg (List U8)
  | .Lit s => .lit s.val
  | .Var n => .var n.val
  | .Rest n => .rest n.val

mutual
def ast.matchToSpec {E : Type} : ast.Match E → Facl.Match (List U8) E
  | .mk pattern ⟨⟨_, body, _⟩⟩ _ => .mk (pattern.val.map ast.patSegToSpec) (ast.bodyToSpec body)

/-- The items of a body in order. It recurses on the `ListN` inside the body's `Vec`, so
that Lean sees the recursion is structural. -/
def ast.bodyToSpec {E : Type} {n : Nat} :
    Aeneas.Data.ListN.ListN (ast.Item E) n → List (Facl.Item (List U8) E)
  | .nil => []
  | .cons (.Match m) items => .nested (ast.matchToSpec m) :: ast.bodyToSpec items
  | .cons (.Allow a) items => .allow ⟨a.methods.val, a.cond⟩ :: ast.bodyToSpec items
end

def ast.serviceToSpec {E : Type} (s : ast.Service E) : Facl.Service (List U8) E :=
  ⟨s.«matches».val.map ast.matchToSpec⟩

def lower.kindToSpec : lower.LowerErrorKind → Facl.LowerError
  | .UnknownIdentifier => .unknownIdentifier
  | .ReservedCaptureName => .reservedCaptureName
  | .DuplicateCapture => .duplicateCapture
  | .RestNotLast => .restNotLast
  | .RestWithChildren => .restWithChildren
  | .UnknownFunction => .unknownFunction
  | .BadArity => .badArity
  | .BadTarget => .badTarget
  | .TooDeep => .tooDeep

def lower.resultToSpec {T T' : Type} (f : T → T') :
    core.result.Result T lower.LowerError → Except Facl.LowerError T'
  | .Ok x => .ok (f x)
  | .Err e => .error (kindToSpec e.kind)

end FaclCore

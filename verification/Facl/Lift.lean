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

end FaclCore

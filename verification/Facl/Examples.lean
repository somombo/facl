import Facl.Spec
namespace Facl

def usersId : Pattern := ⟨[.lit "users", .var], false⟩
def filesRest : Pattern := ⟨[.lit "files"], true⟩

#guard matchPattern usersId ["users", "alice"] == some [Cap.str "alice"]
#guard matchPattern usersId ["users"] == none
#guard matchPattern usersId ["users", "a", "b"] == none
#guard matchPattern usersId ["other", "a"] == none
#guard matchPattern filesRest ["files"] == some [Cap.path []]
#guard matchPattern filesRest ["files", "a", "b.txt"] == some [Cap.path ["a", "b.txt"]]
#guard matchPattern ⟨[], false⟩ [] == some []

example : combine [] = .deny := by decide
example : combine [.notGranted, .granted] = .allow := by decide

/-- Toy conditions: always true / always false. -/
def toyEval : Bool → List Cap → Request → Outcome
  | true, _, _ => .granted
  | false, _, _ => .notGranted

def toy : Policy Bool :=
  ⟨[⟨usersId, [⟨methodBit "GET", true⟩, ⟨methodBit "PUT", false⟩]⟩]⟩

#guard Facl.decide toyEval toy ⟨methodBit "GET", ["users", "alice"]⟩ == .allow
#guard Facl.decide toyEval toy ⟨methodBit "PUT", ["users", "alice"]⟩ == .deny .conditionsNotMet
#guard Facl.decide toyEval toy ⟨methodBit "DELETE", ["users", "alice"]⟩ == .deny .noAllowForMethod
#guard Facl.decide toyEval toy ⟨methodBit "GET", ["admin"]⟩ == .deny .noMatchingRule

end Facl

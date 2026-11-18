import Facl.Spec
namespace Facl

def usersId : Pattern String := ⟨[.lit "users", .var], false⟩
def filesRest : Pattern String := ⟨[.lit "files"], true⟩

#guard matchPattern usersId ["users", "alice"] == some [Cap.str "alice"]
#guard matchPattern usersId ["users"] == none
#guard matchPattern usersId ["users", "a", "b"] == none
#guard matchPattern usersId ["other", "a"] == none
#guard matchPattern filesRest ["files"] == some [Cap.path []]
#guard matchPattern filesRest ["files", "a", "b.txt"] == some [Cap.path ["a", "b.txt"]]
#guard matchPattern (⟨[], false⟩ : Pattern String) [] == some []

example : combine [] = .deny := by decide
example : combine [.notGranted, .granted] = .allow := by decide

/-- Toy conditions: always true / always false. -/
def toyEval : Bool → List (Cap String) → Request String → Outcome
  | true, _, _ => .granted
  | false, _, _ => .notGranted

def toy : Policy String Bool :=
  ⟨[⟨usersId, [⟨methodBit (utf8 "GET"), true⟩, ⟨methodBit (utf8 "PUT"), false⟩]⟩]⟩

#guard Facl.decide toyEval toy ⟨methodBit (utf8 "GET"), ["users", "alice"]⟩ == .allow
#guard Facl.decide toyEval toy ⟨methodBit (utf8 "PUT"), ["users", "alice"]⟩ == .deny .conditionsNotMet
#guard Facl.decide toyEval toy ⟨methodBit (utf8 "DELETE"), ["users", "alice"]⟩ == .deny .noAllowForMethod
#guard Facl.decide toyEval toy ⟨methodBit (utf8 "GET"), ["admin"]⟩ == .deny .noMatchingRule

#guard [("GET", 1), ("HEAD", 2), ("OPTIONS", 4), ("POST", 8), ("PUT", 16), ("PATCH", 32),
  ("DELETE", 64), ("get", 0), ("CONNECT", 0), ("", 0)].all fun (m, bit) => methodBit (utf8 m) == bit

def canon (raw : String) : Except PathError (List (List UInt8)) := canonicalize (utf8 raw)

#guard (canon "/").toOption == some []
#guard (canon "/users/alice").toOption == some [utf8 "users", utf8 "alice"]
#guard (canon "/a%20b/caf%C3%a9/%c3%A9").toOption == some [utf8 "a b", utf8 "café", utf8 "é"]
#guard (canon "/%61/%2561").toOption == some [utf8 "a", utf8 "%61"]
#guard (canon "/..a/a../.a/...").toOption == some [utf8 "..a", utf8 "a..", utf8 ".a", utf8 "..."]
#guard canon "" matches .error .noLeadingSlash
#guard canon "a/b" matches .error .noLeadingSlash
#guard canon "/a?x" matches .error .queryOrFragment
#guard canon "/a#x" matches .error .queryOrFragment
#guard canon "/%zz/a?x" matches .error .queryOrFragment
#guard ["//", "///", "//a", "/a//b", "/a/", "/a/b/", "/a///", "/a//?"].all
  (canon · matches .error .emptySegment)
#guard ["/%", "/%4", "/%zz", "/a%g0", "/%0"].all (canon · matches .error .badPercentEncoding)
#guard ["/.", "/..", "/a/../b", "/%2e", "/%2E%2e", "/.%2e", "/%2e/%C0"].all
  (canon · matches .error .dotSegment)
#guard ["/a%2Fb", "/a%2fb", "/a%00"].all (canon · matches .error .forbiddenByte)
#guard ["/%FF", "/%C3", "/%C0%AF", "/%ED%A0%80", "/%F4%90%80%80"].all
  (canon · matches .error .invalidUtf8)

/-! `utf8Valid` agrees with Lean's own validator on every one- and two-byte sequence, and on
three- and four-byte sequences around each row's boundaries. -/

def agrees (bytes : List UInt8) : Bool := utf8Valid bytes == bytes.toByteArray.validateUTF8
def bytesIn (lo hi : Nat) : List UInt8 := (List.range (hi + 1 - lo)).map (UInt8.ofNat <| · + lo)
def edges : List UInt8 := [0x7F, 0x80, 0xBF, 0xC0]

#guard utf8Valid (utf8 "héllo wörld €𝄞")
#guard (bytesIn 0 255).all fun a => agrees [a] && (bytesIn 0 255).all fun b => agrees [a, b]
#guard (bytesIn 0xE0 0xEF).all fun a => (bytesIn 0x7F 0xC0).all fun b =>
  edges.all fun c => agrees [a, b, c]
#guard (bytesIn 0xF0 0xF5).all fun a => (bytesIn 0x7F 0xC0).all fun b =>
  edges.all fun c => edges.all fun d => agrees [a, b, c, d]

end Facl

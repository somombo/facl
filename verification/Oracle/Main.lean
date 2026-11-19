import Facl.Cel
import Lean.Data.Json

open Lean Facl
open Facl.Cel (Bytes Expr Value Compiled Facts)

private def field (j : Json) (k : String) : Except String String :=
  j.getObjVal? k >>= Json.getStr?

private def array (j : Json) (k : String) : Except String (List Json) :=
  (j.getObjVal? k >>= Json.getArr?).map Array.toList

private def int64 (j : Json) : Except String Int64 := do
  let n ← j.getInt?
  if n < Int64.minValue.toInt || n > Int64.maxValue.toInt then
    throw "integer outside the signed 64-bit range"
  pure (Int64.ofInt n)

private def readOp : String → Except String Cel.CmpOp
  | "==" => .ok .eq
  | "!=" => .ok .ne
  | "<" => .ok .lt
  | "<=" => .ok .le
  | ">" => .ok .gt
  | ">=" => .ok .ge
  | s => .error s!"unknown comparison {s}"

private partial def readExpr (j : Json) : Except String Expr := do
  let child := fun k => j.getObjVal? k >>= readExpr
  let children := fun k => array j k >>= fun items => items.mapM readExpr
  match ← field j "k" with
  | "null" => pure .null
  | "bool" => .bool <$> (j.getObjVal? "v" >>= Json.getBool?)
  | "int" => .int <$> (j.getObjVal? "v" >>= int64)
  | "str" => pure (.str (utf8 (← field j "v")))
  | "list" => .list <$> children "items"
  | "ident" => pure (.ident (utf8 (← field j "name")))
  | "select" => pure (.select (← child "of") (utf8 (← field j "field")))
  | "index" => pure (.index (← child "of") (← child "key"))
  | "call" => pure (.call (← field j "fn") (← children "args"))
  | "method" => pure (.method (← child "of") (← field j "name") (← children "args"))
  | "not" => .not <$> child "e"
  | "and" => pure (.and (← child "l") (← child "r"))
  | "or" => pure (.or (← child "l") (← child "r"))
  | "cmp" => pure (.cmp (← readOp (← field j "op")) (← child "l") (← child "r"))
  | "in" => pure (.in_ (← child "l") (← child "r"))
  | k => throw s!"unknown expression form {k}"

private partial def readValue (j : Json) : Except String Value := do
  match j with
  | .null => pure .null
  | .bool b => pure (.bool b)
  | .num _ => .int <$> int64 j
  | .str s => pure (.str (utf8 s))
  | .arr a => .list <$> a.toList.mapM readValue
  | .obj o => .map <$> o.toList.mapM (fun (k, v) => do pure (utf8 k, ← readValue v))

private def readMap (j : Json) : Except String (Option (List (Bytes × Value))) := do
  match ← readValue j with
  | .null => pure none
  | .map entries => pure (some entries)
  | _ => throw "auth and context must be maps or null"

private def readHeader (j : Json) : Except String (String × String) := do
  match (← j.getArr?).toList with
  | [.str key, .str val] => pure (key, val)
  | _ => throw "a header must be a pair of strings"

private structure InputRequest extends Facts where
  path : Bytes

private def readRequest (j : Json) : Except String InputRequest := do
  pure {
    method := ← field j "method"
    path := utf8 (← field j "path")
    headers := ← (← array j "headers").mapM readHeader
    auth := ← readMap (j.getObjValD "auth")
    context := (← readMap (j.getObjValD "context")).getD []
  }

private def readSegment (j : Json) : Except String (PatSeg Bytes) := do
  match (← j.getObj?).toList with
  | [("lit", .str s)] => pure (.lit (utf8 s))
  | [("var", .str s)] => pure (.var (utf8 s))
  | [("rest", .str s)] => pure (.rest (utf8 s))
  | _ => throw "invalid pattern segment"

private structure OpenBlock where
  pattern : List (PatSeg Bytes)
  body : List (Item Bytes Expr) := []

-- The stream of match openings and endings keeps deep policies shallow in JSON.
-- An unknown action is a compile rejection; malformed JSON is a protocol error.
private def readPolicy (j : Json) : Except String (Option (Service Bytes Expr)) := do
  let _ ← field j "service"
  let mut stack : List OpenBlock := []
  let mut blocks := []
  let mut unknownAction := false
  for item in ← array j "items" do
    match item with
    | .str "end" =>
      let block :: parents := stack | throw "end without an open match"
      let closed := Match.mk block.pattern block.body.reverse
      match parents with
      | [] =>
        stack := []
        blocks := closed :: blocks
      | parent :: ancestors =>
        stack := { parent with body := .nested closed :: parent.body } :: ancestors
    | _ =>
      match item.getObjVal? "match" with
      | .ok pattern =>
        let segments ← (← pattern.getArr?).toList.mapM readSegment
        stack := { pattern := segments } :: stack
      | .error _ =>
        let allow ← item.getObjVal? "allow"
        let block :: parents := stack | throw "allow outside a match"
        let actions ← (← array allow "actions").mapM Json.getStr?
        if actions.isEmpty then throw "an allow requires at least one action"
        let mut bits := 0
        for action in actions do
          match actionBits (utf8 action) with
          | some mask => bits := bits ||| mask
          | none => unknownAction := true
        let cond ← (allow.getObjVal? "cond").toOption.mapM readExpr
        let stmt : AllowStmt Expr := ⟨bits, cond⟩
        stack := { block with body := .allow stmt :: block.body } :: parents
  unless stack.isEmpty do throw "unclosed match"
  pure (if unknownAction then none else some ⟨blocks.reverse⟩)

private def lowerErrorName : LowerError → String
  | .unknownIdentifier => "unknownIdentifier"
  | .reservedCaptureName => "reservedCaptureName"
  | .duplicateCapture => "duplicateCapture"
  | .restNotLast => "restNotLast"
  | .restWithChildren => "restWithChildren"
  | .unknownFunction => "unknownFunction"
  | .badArity => "badArity"
  | .badTarget => "badTarget"
  | .tooDeep => "tooDeep"

private def reasonName : DenyReason → String
  | .noMatchingRule => "no_matching_rule"
  | .noAllowForMethod => "no_allow_for_method"
  | .conditionsNotMet => "conditions_not_met"
  | .badRequestPath => "bad_request_path"

private def verdict (d : Decision) : Json :=
  match d with
  | .allow => toJson "allow"
  | .deny why => Json.mkObj [("deny", toJson (reasonName why))]

private def evaluate (policy : Policy Bytes Compiled) (req : InputRequest) : Json :=
  match canonicalize req.path with
  | .error _ => verdict (.deny .badRequestPath)
  | .ok path => verdict (decide (Cel.outcome req.toFacts) policy ⟨methodBit (utf8 req.method), path⟩)

private def result (j : Json) : Except String Json := do
  let id := toJson (← field j "id")
  let rejected := fun kind : String => Json.mkObj
    [("id", id), ("compile", Json.mkObj [("error", toJson kind)])]
  let requests ← (← array j "requests").mapM readRequest
  let some service ← readPolicy (← j.getObjVal? "policy") | pure (rejected "unknownAction")
  match lower Cel.reserved Cel.compile service with
  | .error err => pure (rejected (lowerErrorName err))
  | .ok policy =>
    let verdicts := requests.map (evaluate policy)
    pure (Json.mkObj [("id", id), ("compile", toJson "ok"), ("verdicts", toJson verdicts)])

#guard (readPolicy (json% {"service": "http", "items": [
  {"match": []}, {"allow": {"actions": ["unknown"]}}]})).isOk == false
#guard (result (json% {"id": "bad-facts", "policy": {"service": "http", "items": [
  {"match": []}, {"allow": {"actions": ["unknown"]}}, "end"]}, "requests": [null]})).isOk == false

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let parsed := Json.parse line
    let response := match parsed >>= result with
      | .ok r => r
      | .error msg => Json.mkObj [
          ("id", parsed.toOption.elim Json.null (·.getObjValD "id")),
          ("protocolError", toJson msg)]
    output.putStrLn response.compress
    output.flush

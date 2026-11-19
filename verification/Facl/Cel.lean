import Facl.Spec

/-! Conditions in facl's dynamic CEL subset. The CEL language definition supplies the
operators and field presence rules. Facl adds request facts and the Content-Type predicate. -/

namespace Facl.Cel

abbrev Bytes := List UInt8

inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int64)
  | str (s : Bytes)
  | list (items : List Value)
  /-- A map has one entry per key. -/
  | map (entries : List (Bytes × Value))
  deriving Repr

inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr

inductive Expr where
  | null
  | bool (b : Bool)
  | int (n : Int64)
  | str (s : Bytes)
  | list (items : List Expr)
  | ident (id : Bytes)
  | select (target : Expr) (key : Bytes)
  | index (target key : Expr)
  | call (fn : String) (args : List Expr)
  | method (target : Expr) (fn : String) (args : List Expr)
  | not (arg : Expr)
  | and (lhs rhs : Expr)
  | or (lhs rhs : Expr)
  | cmp (op : CmpOp) (lhs rhs : Expr)
  | in_ (item collection : Expr)
  deriving Repr

abbrev Compiled := Expr × List Bytes

def reserved : List Bytes := [utf8 "request", utf8 "context"]

private def arity (expected : Nat) (args : List Expr) : Except LowerError Unit :=
  if args.length == expected then .ok () else .error .badArity

/-- Each node of the condition counts toward the depth limit, including the selection in
`has(a.b)`. -/
private def check (scope : List Bytes) : Nat → Expr → Except LowerError Unit
  | 0, _ => .error .tooDeep
  | d + 1, e =>
    let child := check scope d
    match e with
    | .null | .bool _ | .int _ | .str _ => .ok ()
    | .list items => items.forM child
    | .ident id => if scope.contains id then .ok () else .error .unknownIdentifier
    | .select target _ | .not target => child target
    | .index a b | .and a b | .or a b | .cmp _ a b | .in_ a b => child a *> child b
    | .call fn args => do
      match fn with
      | "size" => arity 1 args *> args.forM child
      | "has" =>
        arity 1 args
        let [.select target key] := args | throw .badTarget
        child (.select target key)
      | _ => throw .unknownFunction
    | .method target fn args => do
      match fn with
      | "size" => arity 0 args
      | "startsWith" | "endsWith" => arity 1 args
      | "is" =>
        arity 1 args
        unless (match target with | .ident id => id == utf8 "request" | _ => false) do
          throw .badTarget
      | _ => throw .unknownFunction
      child target
      args.forM child

def compile (cond : Option Expr) (names : List Bytes) : Except LowerError Compiled := do
  let expr := cond.getD (.bool true)
  check (reserved ++ names) maxDepth expr
  pure (expr, names)

inductive EvalError where
  | typeMismatch
  | missingKey
  | badIndex
  | badArgument
  deriving DecidableEq, Repr

private abbrev Eval := Except EvalError
private abbrev Entries := List (Bytes × Value)

private def lookup {α : Type} (entries : List (Bytes × α)) (key : Bytes) : Option α :=
  (entries.find? (fun entry => entry.1 == key)).map Prod.snd

private def equal (a b : Value) : Bool :=
  match a, b with
  | .null, .null => true
  | .bool x, .bool y => x == y
  | .int x, .int y => x == y
  | .str x, .str y => x == y
  | .list xs, .list ys =>
    xs.length == ys.length && (xs.attach.zip ys).all fun (x, y) => equal x.val y
  | .map xs, .map ys =>
    xs.length == ys.length && xs.attach.all fun ⟨(key, x), _hx⟩ =>
      (lookup ys key).any (equal x)
  | _, _ => false
termination_by sizeOf a
decreasing_by
  · have h := List.sizeOf_lt_of_mem x.property
    simp_wf
    omega
  · have h := List.sizeOf_lt_of_mem _hx
    simp_all
    omega

private def ordering (a b : Value) : Eval Ordering :=
  match a, b with
  | .bool x, .bool y => .ok (compare x y)
  | .int x, .int y => .ok (compare x y)
  | .str x, .str y => .ok (compare x y)
  | _, _ => .error .typeMismatch

private def comparison (op : CmpOp) (a b : Value) : Eval Bool :=
  match op with
  | .eq => .ok (equal a b)
  | .ne => .ok (!equal a b)
  | .lt => (· == .lt) <$> ordering a b
  | .le => (· != .gt) <$> ordering a b
  | .gt => (· == .gt) <$> ordering a b
  | .ge => (· != .lt) <$> ordering a b

private def require (o : Option α) (err : EvalError) : Eval α :=
  o.elim (.error err) Except.ok

private def index (target key : Value) : Eval Value :=
  match target, key with
  | .list items, .int i =>
    if i < 0 then .error .badIndex
    else require items[i.toInt.toNat]? .badIndex
  | .map entries, .str k => require (lookup entries k) .missingKey
  | _, _ => .error .typeMismatch

private def has (target : Value) (key : Bytes) : Eval Bool :=
  match target with
  | .map entries => .ok (lookup entries key).isSome
  | _ => .error .typeMismatch

private def contains (collection item : Value) : Eval Bool :=
  match collection, item with
  | .list items, _ => .ok (items.any (equal item))
  | .map entries, .str key => .ok (lookup entries key).isSome
  | _, _ => .error .typeMismatch

private def text (s : Bytes) : Eval String :=
  require (String.fromUTF8? ⟨s.toArray⟩) .badArgument

private def size (value : Value) : Eval Int64 := do
  let n ← match value with
    | .str s => String.length <$> text s
    | .list items => pure items.length
    | .map entries => pure entries.length
    | _ => throw .typeMismatch
  pure (Int64.ofNat n)

private def asBool (value : Value) : Eval Bool :=
  match value with
  | .bool b => .ok b
  | _ => .error .typeMismatch

private def asString (value : Value) : Eval Bytes :=
  match value with
  | .str s => .ok s
  | _ => .error .typeMismatch

private def stringPredicate (test : Bytes → Bytes → Bool) (target arg : Value) : Eval Value := do
  let s ← asString target
  let pattern ← asString arg
  pure (.bool (test pattern s))

private def logical (decisive : Bool) (lhs rhs : Eval Value) : Eval Bool :=
  match lhs >>= asBool, rhs >>= asBool with
  | .ok a, .ok b => .ok (if decisive then a || b else a && b)
  | .ok b, .error e | .error e, .ok b =>
    if b == decisive then .ok b else .error e
  | .error e, .error _ => .error e

private def mediaMatches (arg : String) : Eval (String → Bool) :=
  match arg with
  | "json" => .ok fun s => s == "application/json" || s.endsWith "+json"
  | "html" => .ok (· == "text/html")
  | "text" => .ok (·.startsWith "text/")
  | "xml" => .ok fun s => s == "application/xml" || s == "text/xml" || s.endsWith "+xml"
  | "urlencoded" => .ok (· == "application/x-www-form-urlencoded")
  | "multipart" => .ok (·.startsWith "multipart/")
  | _ =>
    match arg.splitOn "/" with
    | kind :: first :: rest =>
      if kind.isEmpty || (first.isEmpty && rest.isEmpty) then .error .badArgument
      else if first == "*" && rest.isEmpty then .ok (·.startsWith (kind ++ "/"))
      else .ok (· == arg)
    | _ => .error .badArgument

private def whitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0d) || (0x2000 ≤ n && n ≤ 0x200a) ||
    [0x20, 0x85, 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000].contains n

private def contentType (s : String) : String :=
  let media := s.takeWhile (· != ';')
  ((media.dropWhile whitespace).dropEndWhile whitespace).copy.toLower

private def requestIs (header : Option String) (arg : Bytes) : Eval Bool := do
  let predicate ← mediaMatches (← text arg).toLower
  pure (header.any fun s => predicate (contentType s))

private structure Env where
  bindings : Entries
  media : Option String

private def eval (env : Env) (e : Expr) : Eval Value :=
  match e with
  | .null => .ok .null
  | .bool b => .ok (.bool b)
  | .int i => .ok (.int i)
  | .str s => .ok (.str s)
  | .list items => .list <$> (items.attach.mapM fun item => eval env item.val)
  | .ident id => require (lookup env.bindings id) .missingKey
  | .select a key => do index (← eval env a) (.str key)
  | .index a key => do index (← eval env a) (← eval env key)
  | .call "size" [arg] | .method arg "size" [] => do
    .int <$> (size (← eval env arg))
  | .call "has" [.select target key] => do
    .bool <$> (has (← eval env target) key)
  | .method target "startsWith" [arg] => do
    stringPredicate List.isPrefixOf (← eval env target) (← eval env arg)
  | .method target "endsWith" [arg] => do
    stringPredicate List.isSuffixOf (← eval env target) (← eval env arg)
  | .method _ "is" [arg] => do .bool <$> requestIs env.media (← asString (← eval env arg))
  | .call .. | .method .. => .error .badArgument
  | .not arg => do pure (.bool (!(← asBool (← eval env arg))))
  | .and a b => .bool <$> logical false (eval env a) (eval env b)
  | .or a b => .bool <$> logical true (eval env a) (eval env b)
  | .cmp op a b => do .bool <$> comparison op (← eval env a) (← eval env b)
  | .in_ item collection => do
    let key ← eval env item
    .bool <$> contains (← eval env collection) key
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem item.property
      omega

structure Facts where
  method : String
  headers : List (String × String) := []
  auth : Option (List (Bytes × Value)) := none
  context : List (Bytes × Value) := []

private def headers (raw : List (String × String)) : List (Bytes × String) :=
  let fields := raw.map fun (key, value) => (utf8 key.toLower, value)
  (fields.map Prod.fst).eraseDups.map fun key =>
    let values := fields.filterMap fun (k, v) => if k == key then some v else none
    (key, String.intercalate ", " values)

private def captureValue : Cap Bytes → Value
  | .str s => .str s
  | .path segments => .list (segments.map Value.str)

private def environment (facts : Facts) (path : List Bytes) (names : List Bytes)
    (caps : List (Cap Bytes)) : Env :=
  let normalizedHeaders := headers facts.headers
  let request := Value.map [
    (utf8 "method", .str (utf8 facts.method)),
    (utf8 "path", .str (utf8 "/" ++ (path.intersperse (utf8 "/")).flatten)),
    (utf8 "headers", .map (normalizedHeaders.map fun (k, v) => (k, .str (utf8 v)))),
    (utf8 "auth", facts.auth.elim .null Value.map)]
  ⟨[(utf8 "request", request), (utf8 "context", .map facts.context)] ++
    names.zip (caps.map captureValue), lookup normalizedHeaders (utf8 "content-type")⟩

def outcome (facts : Facts) (condition : Compiled) (caps : List (Cap Bytes))
    (req : Request Bytes) : Outcome :=
  match eval (environment facts req.path condition.2 caps) condition.1 with
  | .ok (.bool true) => .granted
  | _ => .notGranted

private def result (e : Expr) : Eval Value := eval ⟨[], none⟩ e
private def failure (e : Expr) (err : EvalError) : Bool :=
  match result e with
  | .error actual => actual == err
  | .ok _ => false

private def returns (e : Expr) (v : Value) : Bool := (result e).toOption.any (equal v)
private def str (s : String) : Expr := .str (utf8 s)
private def missing : Expr := .index (.list []) (.int 0)

#guard returns .null .null
#guard returns (.not (.bool true)) (.bool false)
#guard returns (.and (.bool false) missing) (.bool false)
#guard returns (.and missing (.bool false)) (.bool false)
#guard returns (.or (.bool true) missing) (.bool true)
#guard returns (.or missing (.bool true)) (.bool true)
#guard returns (.or (.int 1) (.bool true)) (.bool true)
#guard failure (.and missing (.bool true)) .badIndex
#guard failure (.or missing (.bool false)) .badIndex
#guard failure (.not (.int 1)) .typeMismatch

#guard returns (.cmp .eq (.list [.int 1, .null]) (.list [.int 1, .null])) (.bool true)
#guard returns (.cmp .ne (.int 1) (str "1")) (.bool true)
#guard returns (.cmp .lt (.int (-9223372036854775808)) (.int 0)) (.bool true)
#guard returns (.cmp .le (.int 3) (.int 3)) (.bool true)
#guard returns (.cmp .gt (str "β") (str "a")) (.bool true)
#guard returns (.cmp .ge (.bool true) (.bool false)) (.bool true)
#guard failure (.cmp .lt (.int 1) (str "1")) .typeMismatch
#guard equal (.map [(utf8 "a", .int 1), (utf8 "b", .list [.null])])
  (.map [(utf8 "b", .list [.null]), (utf8 "a", .int 1)])

#guard returns (.index (.list [.int 1]) (.int 0)) (.int 1)
#guard failure (.index (.list [.int 1]) (.int (-1))) .badIndex
#guard returns (.in_ (.int 1) (.list [.null, .int 1])) (.bool true)
#guard returns (.call "size" [str "é😀"]) (.int 2)
#guard returns (.method (.list [.null]) "size" []) (.int 1)
#guard returns (.method (str "αβ") "startsWith" [str "α"]) (.bool true)
#guard returns (.method (str "αβ") "endsWith" [str "β"]) (.bool true)
#guard failure (.method (.int 1) "startsWith" [missing]) .badIndex
#guard failure (.method .null "endsWith" [missing]) .badIndex

private def context : Expr := .ident (utf8 "context")
private def key := utf8 "flag"
private def checksContext (e : Expr) (ctx : Entries) (v : Value) : Bool :=
  (eval (environment { method := "GET", context := ctx } [] [] []) e).toOption.any (equal v)

#guard checksContext (.select context key) [(key, .bool true)] (.bool true)
#guard checksContext (.index context (str "flag")) [(key, .int 2)] (.int 2)
#guard checksContext (.in_ (str "flag") context) [(key, .null)] (.bool true)
#guard checksContext (.call "has" [.select context key]) [(key, .null)] (.bool true)
#guard checksContext (.call "has" [.select context key]) [] (.bool false)
#guard failure (.select .null key) .typeMismatch
#guard failure (.call "has" [.select .null key]) .typeMismatch
#guard (eval (environment { method := "GET" } [] [] []) (.select context key) |>.toOption).isNone

private def sampleFacts : Facts :=
  { method := "GET", headers := [("Content-Type", " Application/Problem+JSON ; charset=utf-8"),
      ("X-Token", "one"), ("x-TOKEN", "two")], auth := some [(utf8 "uid", .str (utf8 "alice"))] }

private def request := Expr.ident (utf8 "request")
private def factsReturn (e : Expr) (v : Value) : Bool :=
  (eval (environment sampleFacts [utf8 "users", utf8 "alice"]
      [utf8 "id", utf8 "tail"] [.str (utf8 "alice"), .path []]) e).toOption.any (equal v)

#guard factsReturn (.select request (utf8 "method")) (.str (utf8 "GET"))
#guard factsReturn (.select request (utf8 "path")) (.str (utf8 "/users/alice"))
#guard factsReturn (.select (.select request (utf8 "auth")) (utf8 "uid")) (.str (utf8 "alice"))
#guard factsReturn (.index (.select request (utf8 "headers")) (str "x-token"))
  (.str (utf8 "one, two"))
#guard factsReturn (.method request "is" [str "JSON"]) (.bool true)
#guard factsReturn (.method request "is" [str "application/*"]) (.bool true)
#guard factsReturn (.method request "is" [str "text/plain"]) (.bool false)
#guard (requestIs none (utf8 "json")).toOption == some false
#guard match requestIs none (utf8 "bogus") with | .error .badArgument => true | _ => false
#guard factsReturn (.ident (utf8 "id")) (.str (utf8 "alice"))
#guard factsReturn (.ident (utf8 "tail")) (.list [])
#guard (outcome sampleFacts (.bool true, []) [] ⟨1, []⟩) == .granted
#guard (outcome sampleFacts (.bool false, []) [] ⟨1, []⟩) == .notGranted
#guard (outcome sampleFacts (missing, []) [] ⟨1, []⟩) == .notGranted
#guard (outcome sampleFacts (str "true", []) [] ⟨1, []⟩) == .notGranted

private def rejected (e : Expr) (err : LowerError) : Bool :=
  match compile (some e) [] with
  | .error actual => actual == err
  | .ok _ => false

private def nestedNot : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .not (nestedNot n e)

#guard (compile none []).toOption.isSome
#guard (compile (some (.ident (utf8 "id"))) [utf8 "id"]).toOption.isSome
#guard rejected (.ident (utf8 "unknown")) .unknownIdentifier
#guard rejected (.call "unknown" []) .unknownFunction
#guard rejected (.call "size" []) .badArity
#guard rejected (.call "has" [.null]) .badTarget
#guard rejected (.method context "is" [str "json"]) .badTarget
#guard (compile (some (nestedNot 63 (.bool true))) []).toOption.isSome
#guard rejected (nestedNot 64 (.bool true)) .tooDeep
#guard (compile (some (nestedNot 61 (.call "has" [.select context key]))) []).toOption.isSome
#guard rejected (nestedNot 62 (.call "has" [.select context key])) .tooDeep

end Facl.Cel

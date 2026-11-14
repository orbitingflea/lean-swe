import LeanSwe.Json.Interface

namespace LeanSwe.Json.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except JsonError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertOkEq {α : Type} [BEq α] [ToString α]
    (actual : Except JsonError α) (expected : α) (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError s!"ASSERTION FAILED: {msg} (got {v}, expected {expected})")

private def assertErr {α : Type}
    (res : Except JsonError α) (expectedKind : JsonErrorKind) (expectedPath : Option String)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error, got ok)")
  | .error e =>
    if e.kind != expectedKind || e.path != expectedPath || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind={repr expectedKind} path={repr expectedPath})")

private def testRfc8259ParsingAndEscapes : IO Unit := do
  assertOkEq (parse "null") Lean.Json.null "null"
  assertOkEq (parse "true") (Lean.Json.bool true) "true"
  assertOkEq (parse "false") (Lean.Json.bool false) "false"
  assertOkEq (parse "  \t\n\r [ 1 , \"two\" , false , null ] \n ")
    (Lean.Json.arr #[Lean.Json.num 1, Lean.Json.str "two", Lean.Json.bool false, Lean.Json.null])
    "whitespace around array"

  assertOkEq (parse "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"")
    (Lean.Json.str "\"\\/\x08\x0c\n\r\t") "standard escapes"
  assertOkEq (parse "\"\\u0000\\u001f\\u03b1\\u03A9\"")
    (Lean.Json.str "\x00\x1fαΩ") "unicode hex escapes"
  assertOkEq (parse "\"\\ud83d\\ude80\"")
    (Lean.Json.str "🚀") "UTF-16 surrogate pair"
  assertOkEq (parse "\"\\ud800\"")
    (Lean.Json.str "\ufffd") "lone surrogate replacement"
  assertOkEq (parse "\"日本語 🚀 αβγ\"")
    (Lean.Json.str "日本語 🚀 αβγ") "raw UTF-8 multi-byte"

  assertOkEq (parse "0") (Lean.Json.num ⟨0, 0⟩) "zero"
  assertOkEq (parse "-0") (Lean.Json.num ⟨0, 0⟩) "negative zero"
  assertOkEq (parse "-42") (Lean.Json.num ⟨-42, 0⟩) "negative int"
  assertOkEq (parse "3.14159") (Lean.Json.num ⟨314159, 5⟩) "decimal"
  assertOkEq (parse "1.5e-3") (Lean.Json.num ⟨15, 4⟩) "negative exponent"
  assertOkEq (parse "2e+4") (Lean.Json.num ⟨20000, 0⟩) "positive exponent"
  assertOkEq (parse "1E2") (Lean.Json.num ⟨100, 0⟩) "uppercase exponent"

  let badInputs : Array String := #[
    "", "   ", "{", "}", "[", "]", "[1,]", "{\"a\":1,}", "{a:1}", "'single'",
    "01", "-01", ".5", "1.", "+1", "1e", "1e+", "\"unclosed", "\"\\x\"",
    "\"\\u123\"", "\"raw\nnewline\"", "\"raw\ttab\"", "true false", "NaN", "Infinity",
    "{\"a\":1}{\"b\":2}"
  ]
  for bad in badInputs do
    assertErr (parse bad) .parseError none s!"malformed input: {repr bad}"

private def testCompressPrettyAndRoundTrips : IO Unit := do
  let trickyStrings : Array String := #[
    "", "hello", "line1\nline2\r\nline3\tend", "\"quoted\" \\ slash /",
    "\x00\x01\x08\x0c\x1f", "αβγ 日本語 🚀"
  ]
  for s in trickyStrings do
    let j := encode s
    let c := compress j
    assertTrue (c != "" && !(c.contains '\n') && !(c.contains '\r'))
      s!"compress must be non-empty single-line for {repr s}: {repr c}"
    let parsed ← assertOk (parse c) s!"parse(compress) failed for {repr s}"
    assertOkEq (decode parsed) s s!"decode(parse(compress)) failed for {repr s}"

  let nums : Array Lean.JsonNumber := #[
    ⟨0, 0⟩, ⟨-42, 0⟩, ⟨314159, 5⟩, ⟨1, 100⟩, ⟨10, 1⟩, ⟨0, 3⟩
  ]
  for n in nums do
    let j := Lean.Json.num n
    let c := compress j
    let p := pretty j 20
    assertTrue (c != "" && !(c.contains '\n') && !(c.contains '\r')) "number compress non-empty single-line"
    assertTrue (p != "") "number pretty non-empty"
    let jc ← assertOk (parse c) s!"parse(compress) number {repr n}"
    let jp ← assertOk (parse p) s!"parse(pretty) number {repr n}"
    assertTrue (compress jc == c && compress jp == c)
      s!"round-trip compressed form mismatch for {repr n}"

  let mut deep := Lean.Json.mkObj [("leaf", Lean.Json.str "ok\nline")]
  for i in [:64] do
    deep := Lean.Json.mkObj [(s!"k{i}", Lean.Json.arr #[deep, Lean.Json.num i])]
  let cDeep := compress deep
  let pDeep := pretty deep 40
  assertTrue (!(cDeep.contains '\n') && !(cDeep.contains '\r')) "deep compress single-line"
  let deepC ← assertOk (parse cDeep) "parse deep compress"
  let deepP ← assertOk (parse pDeep) "parse deep pretty"
  assertTrue (deepC == deep && deepP == deep) "64-level deep round-trip"

  for b in #[true, false] do
    assertOkEq (parse (compress (encode b)) >>= decode) b "bool round-trip"
  for i in #[(0 : Int), -1, 1, 9876543210, -9876543210] do
    assertOkEq (parse (compress (encode i)) >>= decode) i "int round-trip"
  let arr : Array String := #["a\nb", "", "🚀"]
  assertOkEq (parse (compress (encode arr)) >>= decode) arr "array string round-trip"

private def testAccessorsAndDevtoolsPayloads : IO Unit := do
  let harnessRaw := "{\"claude\":{\"command\":\"claude\",\"timeout_sec\":120,\"enabled\":false,\"tags\":[\"fast\",\"cli\"],\"extra\":null,\"nested\":{\"model\":\"model-a\",\"retries\":3}}}"
  let root ← assertOk (parse harnessRaw) "parse harness payload"
  let objMap ← assertOk (getObject root) "getObject root"
  assertTrue (objMap.contains "claude") "object contains claude"
  assertErr (getObject (Lean.Json.arr #[])) .typeMismatch none "getObject on array"

  let tagsJson ← assertOk (getPath (α := Lean.Json) root ["claude", "tags"]) "getPath tags"
  let tagsArr ← assertOk (getArray tagsJson) "getArray tags"
  assertTrue (tagsArr.size == 2) "tags size"
  assertErr (getArray root) .typeMismatch none "getArray on object"

  let claudeObj ← assertOk (getField (α := Lean.Json) root "claude") "getField claude"
  assertOkEq (getField (α := Nat) claudeObj "timeout_sec") 120 "getField timeout_sec"
  assertOkEq (getField (α := Bool) claudeObj "enabled") false "getField enabled=false"
  assertOkEq (getOptField (α := Bool) claudeObj "enabled") (some false) "getOptField present false"
  assertOkEq (getOptField (α := String) claudeObj "extra") none "getOptField explicit null"
  assertOkEq (getOptField (α := String) claudeObj "missing") none "getOptField missing"
  assertErr (getOptField (α := Nat) claudeObj "command") .decodeError (some "command") "getOptField bad type"
  assertErr (getOptField (α := Nat) (Lean.Json.arr #[]) "timeout_sec") .typeMismatch none "getOptField non-object"
  assertErr (getOptField (α := Nat) Lean.Json.null "timeout_sec") .typeMismatch none "getOptField null root"

  assertErr (getField (α := Nat) claudeObj "missing") .missingField (some "missing") "getField missing"
  assertErr (getField (α := Nat) claudeObj "command") .decodeError (some "command") "getField bad type"
  assertErr (getField (α := Nat) Lean.Json.null "command") .typeMismatch none "getField non-object"

  assertOkEq (getPath (α := String) root ["claude", "nested", "model"]) "model-a" "getPath depth 3"
  assertOkEq (getPath (α := Nat) root ["claude", "nested", "retries"]) 3 "getPath depth 3 nat"
  assertErr (getPath (α := Nat) root ["claude", "nested", "missing"]) .missingField (some "claude.nested.missing") "getPath missing depth 3"
  assertErr (getPath (α := Nat) root ["claude", "nested", "model"]) .decodeError (some "claude.nested.model") "getPath decodeError depth 3"
  assertErr (getPath (α := Nat) root ["claude", "command", "sub"]) .typeMismatch (some "claude.command") "getPath non-object intermediate"
  assertErr (getPath (α := Nat) root ["absent", "sub"]) .missingField (some "absent") "getPath missing intermediate"
  assertErr (getPath (α := Nat) (Lean.Json.str "not-obj") ["a", "b"]) .typeMismatch none "getPath non-object root"
  assertOkEq (getPath (α := String) (Lean.Json.str "hello") []) "hello" "getPath empty path"

/-- Execute all runtime tests for `LeanSwe.Json`. -/
def runAll : IO Unit := do
  testRfc8259ParsingAndEscapes
  testCompressPrettyAndRoundTrips
  testAccessorsAndDevtoolsPayloads
  IO.println "PASS: LeanSwe.Json runtime tests"

end LeanSwe.Json.RuntimeTests

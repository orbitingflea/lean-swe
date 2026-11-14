import Packages.Regex.Impl

/-!
# Regex RuntimeTests

Concrete execution tests checking `Packages.Regex.liveApi` behavior across
patterns, replacements, splits, UTF-8 inputs, and syntax error reporting.
-/

namespace Packages.Regex.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except RegexError α) (expected : α) (msg : String) : IO Unit := do
  match actual with
  | .ok v =>
    if !(v == expected) then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {e.message})")

/-- Execute all runtime sanity checks for `Packages.Regex.liveApi`. -/
def runAll : IO Unit := do
  assertOkEq (liveApi.testPattern "[0-9]+" "id=42") true "digit match expected"
  assertOkEq (liveApi.testPattern "[0-9]+" "abc") false "non-match expected"
  match liveApi.findFirst "a+" "xaaay" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "aaa" && sp.startByte == 1 && sp.stopByte == 4)
      s!"unexpected findFirst span: {repr sp}"
  | other => throw (IO.userError s!"unexpected findFirst result: {repr other}")
  match liveApi.findAll "[0-9]+" "10,200,3" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["10", "200", "3"])
      s!"unexpected findAll: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected findAll error: {e.message}")
  assertOkEq (liveApi.countMatches "a+" "baaaaca") 2 "expected 2 matches"
  assertOkEq (liveApi.replaceAll "[0-9]+" "v1.2" "X") "vX.X" "expected replaceAll"
  assertOkEq (liveApi.splitBy "," "a,,b") #["a", "", "b"] "expected 3 split parts"
  -- UTF-8 multi-byte haystack byte bounds
  match liveApi.findFirst "b+" "αbbbβ" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "bbb" && sp.startByte == 2 && sp.stopByte == 5)
      s!"unexpected UTF-8 span: {repr sp}"
  | other => throw (IO.userError s!"unexpected UTF-8 findFirst: {repr other}")
  -- Syntax error checks
  for bad in ["[unclosed", "(abc", "*bad"] do
    match liveApi.testPattern bad "hello" with
    | .error e => assertTrue (e.message != "") s!"empty error message for {bad}"
    | .ok b => throw (IO.userError s!"expected parse error for {bad}, got {b}")
  IO.println "PASS: Packages.Regex runtime tests"

end Packages.Regex.RuntimeTests

import LeanSwe.RegExp.Interface

namespace LeanSwe.RegExp.RuntimeTests

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

/-- Execute all runtime sanity checks for `LeanSwe.RegExp`. -/
def runAll : IO Unit := do
  assertOkEq (testPattern "[0-9]+" "id=42") true "digit match expected"
  assertOkEq (testPattern "[0-9]+" "abc") false "non-match expected"
  match findFirst "a+" "xaaay" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "aaa" && sp.startByte == 1 && sp.stopByte == 4)
      s!"unexpected findFirst span: {repr sp}"
  | other => throw (IO.userError s!"unexpected findFirst result: {repr other}")
  match findAll "[0-9]+" "10,200,3" with
  | .ok xs =>
    assertTrue (xs.map (·.matched) == #["10", "200", "3"])
      s!"unexpected findAll: {repr xs}"
  | .error e => throw (IO.userError s!"unexpected findAll error: {e.message}")
  assertOkEq (countMatches "a+" "baaaaca") 2 "expected 2 matches"
  assertOkEq (replaceAll "[0-9]+" "v1.2" "X") "vX.X" "expected replaceAll"
  assertOkEq (splitBy "," "a,,b") #["a", "", "b"] "expected 3 split parts"
  match findFirst "b+" "αbbbβ" with
  | .ok (some sp) =>
    assertTrue (sp.matched == "bbb" && sp.startByte == 2 && sp.stopByte == 5)
      s!"unexpected UTF-8 span: {repr sp}"
  | other => throw (IO.userError s!"unexpected UTF-8 findFirst: {repr other}")
  for bad in ["[unclosed", "(abc", "*bad"] do
    match testPattern bad "hello" with
    | .error e => assertTrue (e.message != "") s!"empty error message for {bad}"
    | .ok b => throw (IO.userError s!"expected parse error for {bad}, got {b}")
  IO.println "PASS: LeanSwe.RegExp runtime tests"

end LeanSwe.RegExp.RuntimeTests

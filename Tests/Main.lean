import LeanSwe

open LeanSwe

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main : IO Unit := do
  RegExp.RuntimeTests.runAll
  Glob.RuntimeTests.runAll
  match RegExp.findAll "[0-9]+" "a1b22" with
  | .ok xs =>
    if xs.map (·.matched) != #["1", "22"] then
      throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
  | .error e =>
    throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")
  IO.println "ALL_LEAN_SWE_TESTS_PASSED"

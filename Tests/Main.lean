import LeanSwe

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main : IO Unit := do
  Packages.Regex.RuntimeTests.runAll
  IO.println "ALL_LEAN_SWE_TESTS_PASSED"

import LeanSwe.RegExp.Interface
import LeanSwe.EnvVars.Raw.RuntimeTests
import LeanSwe.EnvVars.RuntimeTests
import LeanSwe.CmdLine.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests
import LeanSwe.Compress.RuntimeTests
import LeanSwe.Process.RuntimeTests

namespace Tests.Common

/-- Scoped `BEq` instance comparing `Except` values structurally for test assertions. -/
scoped instance beqExcept {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

/-- Single mutation-test suite entry pairing `RuntimeTests` baseline checks with `--mode full` extras. -/
structure MutateSuite where
  /-- Canonical `--suite` CLI identifier matching `scripts/mutate_and_test.py`. -/
  name : String
  /-- Baseline runtime test action returning `none` on pass or `some reason` on environment skip. -/
  runBase : IO (Option String)
  /-- Extra unit, property, or fault-injection checks run when `--mode full` is selected. -/
  runExtra : IO Unit := pure ()

/-- Quick smoke check verifying `RegExp.findAll` extracts consecutive digit runs. -/
def smokeRegExp : IO Unit := do
  match LeanSwe.RegExp.findAll "[0-9]+" "a1b22" with
  | .ok xs =>
    if xs.map (·.matched) != #["1", "22"] then
      throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
  | .error e =>
    throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")

/-- Fail with `IO.userError` when `ok` is `false`. -/
def checkUnit (label : String) (ok : Bool) : IO Unit :=
  unless ok do
    throw (IO.userError s!"unit check failed: {label}")

/-- Split a comma-separated `--suite` CLI argument into trimmed non-empty suite names. -/
def parseSuiteCsv (raw : String) : Array String :=
  let parts := (raw.splitOn ",").filterMap fun item =>
    let t := item.trimAscii.toString
    if t.isEmpty then none else some t
  parts.toArray

/-- Validate requested `--suite` names (`all` or empty selects every suite) and filter in registry order. -/
def selectNamedSuites {α : Type} (all : Array α) (nameOf : α → String)
    (requested : Array String) : Except String (Array α) := do
  let filterAll := requested.isEmpty || requested.contains "all"
  if filterAll then
    return all
  let knownNames := all.map nameOf
  for s in requested do
    if !knownNames.contains s then
      throw s!"UNKNOWN_SUITE: {s}"
  return all.filter fun entry => requested.contains (nameOf entry)

/-- Match shared `--*-probe` subprocess worker flags used by both `lean-swe-test` and `lean-swe-mut-test`. -/
def findRuntimeProbe? : List String → Option (IO UInt32)
  | "--envvars-raw-probe" :: rest => some (LeanSwe.EnvVars.Raw.RuntimeTests.probeMain rest)
  | "--envvars-probe" :: rest => some (LeanSwe.EnvVars.RuntimeTests.probeMain rest)
  | "--cmdline-probe" :: rest => some (LeanSwe.CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest => some (LeanSwe.SlotPool.RuntimeTests.probeMain rest)
  | "--compress-probe" :: rest => some (LeanSwe.Compress.RuntimeTests.probeMain rest)
  | "--process-probe" :: rest => some (LeanSwe.Process.RuntimeTests.probeMain rest)
  | _ => none

end Tests.Common

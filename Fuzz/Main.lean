import Fuzz.Common.Suite
import Fuzz.Float.Suite
import Fuzz.SelfTest

namespace Fuzz.Main

open Fuzz.Common

/-- Parsed CLI options for `leanswe-fuzz`. -/
structure CliOptions where
  /-- Requested suite names (empty unless `--suite` was passed). -/
  suites : List String := []
  /-- Whether `--all` was explicitly passed. -/
  runAll : Bool := false
  /-- Whether `--list-suites` was requested. -/
  listSuites : Bool := false
  /-- Whether `--help` was requested. -/
  showHelp : Bool := false
  /-- Shared configuration passed to each selected `FuzzSuite`. -/
  config : FuzzConfig := {}
  deriving Repr

private def registeredSuites : List FuzzSuite := [
  Fuzz.SelfTest.suite,
  Fuzz.Float.suite
]

private def parsePositiveNat (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n =>
    if n > 0 then .ok n else .error s!"INVALID_{flag}: expected >= 1, got '{val}'"
  | none => .error s!"INVALID_{flag}: expected Nat, got '{val}'"

private def parseHexNat? (digits : List Char) : Option Nat :=
  if digits.isEmpty then
    none
  else
    digits.foldlM (init := 0) fun acc c =>
      let d? :=
        if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
        else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
        else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
        else none
      d?.map fun d => acc * 16 + d

private def parseUInt64 (flag val : String) : Except String UInt64 :=
  let parsed? :=
    if val.startsWith "0x" || val.startsWith "0X" then
      parseHexNat? (val.toList.drop 2)
    else
      val.toNat?
  match parsed? with
  | some n =>
    if n < UInt64.size then
      .ok (UInt64.ofNat n)
    else
      .error s!"INVALID_{flag}: out of UInt64 range, got '{val}'"
  | none => .error s!"INVALID_{flag}: expected UInt64, got '{val}'"

private def splitSuiteArg (raw : String) : List String :=
  (raw.splitOn ",").filter (!·.isEmpty)

private def parseArgs : List String → (opts : CliOptions := {}) → Except String CliOptions
  | [], opts => .ok opts
  | "--help" :: rest, opts => parseArgs rest { opts with showHelp := true }
  | "-h" :: rest, opts => parseArgs rest { opts with showHelp := true }
  | "--list-suites" :: rest, opts => parseArgs rest { opts with listSuites := true }
  | "--all" :: rest, opts => parseArgs rest { opts with runAll := true }
  | "--smoke" :: rest, opts =>
    parseArgs rest { opts with config := { opts.config with smoke := true } }
  | "--self-test-shrink" :: rest, opts =>
    parseArgs rest { opts with config := { opts.config with selfTestShrink := true } }
  | "--random-seed" :: rest, opts =>
    parseArgs rest { opts with config := { opts.config with randomSeed := true } }
  | ["--suite"], _ => .error "missing value for --suite"
  | "--suite" :: s :: rest, opts =>
    let names := splitSuiteArg s
    if names.isEmpty then
      .error "INVALID_SUITE: empty suite name"
    else
      parseArgs rest { opts with suites := opts.suites ++ names }
  | ["--steps"], _ => .error "missing value for --steps"
  | "--steps" :: s :: rest, opts => do
    let n ← parsePositiveNat "STEPS" s
    parseArgs rest { opts with config := { opts.config with steps := n } }
  | ["--seed"], _ => .error "missing value for --seed"
  | "--seed" :: s :: rest, opts => do
    let sd ← parseUInt64 "SEED" s
    parseArgs rest { opts with config := { opts.config with seed := sd, randomSeed := false } }
  | flag :: _, _ => .error s!"UNKNOWN_FLAG: {flag}"

private def drawOsEntropySeed : IO UInt64 := do
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let bytes ← handle.read 8
  if bytes.size < 8 then
    throw (IO.userError s!"drawOsEntropySeed short read from /dev/urandom: got {bytes.size} bytes")
  let mut v : UInt64 := 0
  for i in List.range 8 do
    v := v ||| (UInt64.ofNat bytes[i]!.toNat <<< UInt64.ofNat (8 * i))
  return v

private def findSuite? (name : String) : Option FuzzSuite :=
  registeredSuites.find? (·.name == name)

private def resolveSelectedSuites (opts : CliOptions) : Except String (List FuzzSuite) := do
  if opts.runAll || opts.suites.isEmpty then
    return registeredSuites
  let mut selected : List FuzzSuite := []
  let mut seen : List String := []
  for name in opts.suites do
    if seen.contains name then
      continue
    match findSuite? name with
    | some s =>
      selected := selected ++ [s]
      seen := seen ++ [name]
    | none =>
      let avail := ", ".intercalate (registeredSuites.map (·.name))
      throw s!"UNKNOWN_SUITE: '{name}' (available: {avail})"
  return selected

private def printUsage : IO Unit := do
  IO.println "Usage: leanswe-fuzz [OPTIONS]"
  IO.println "  --smoke              Run fast deterministic smoke corpus and shrinker self-test"
  IO.println "  --suite <name>       Run named fuzz suite (repeatable or comma-separated)"
  IO.println "  --all                Run all registered fuzz suites (default if --suite omitted)"
  IO.println "  --steps <N>          Number of fuzz steps per suite in full mode"
  IO.println "  --seed <u64>         Deterministic SplitMix64 seed (decimal or 0x hex)"
  IO.println "  --random-seed        Draw 64-bit seed from /dev/urandom and print SEED=<u64>"
  IO.println "  --self-test-shrink   Run shrinker self-test before fuzzing"
  IO.println "  --list-suites        List registered fuzz suites and exit"
  IO.println "  -h, --help           Show this help message"

/-- Unified CLI entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln msg
      return 2
  if opts.showHelp then
    printUsage
    return 0
  if opts.listSuites then
    for s in registeredSuites do
      IO.println s.name
    return 0
  if opts.runAll && !opts.suites.isEmpty then
    IO.eprintln "CONFLICTING_FLAGS: pass either --all or --suite, not both"
    return 2
  let selected ← match resolveSelectedSuites opts with
    | .ok ss => pure ss
    | .error msg =>
      IO.eprintln msg
      return 2
  let effectiveSeed ←
    if opts.config.randomSeed then drawOsEntropySeed else pure opts.config.seed
  let effectiveConfig : FuzzConfig := { opts.config with seed := effectiveSeed }
  IO.println s!"SEED={effectiveSeed}"
  for suite in selected do
    try
      if effectiveConfig.smoke || effectiveConfig.selfTestShrink then
        suite.selfTestShrink effectiveSeed
      if effectiveConfig.smoke then
        suite.runSmoke effectiveConfig
      else
        suite.runFuzz effectiveConfig
    catch e =>
      IO.eprintln s!"FUZZ_SUITE_FAILED suite={suite.name}: {e}"
      return 1
  return 0

end Fuzz.Main

/-- Top-level executable entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 :=
  Fuzz.Main.main args

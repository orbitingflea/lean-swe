import Fuzz.Common.Suite
import Fuzz.Compress.Suite
import Fuzz.Float.Suite
import Fuzz.CmdLine.Suite
import Fuzz.Passwd.Suite
import Fuzz.Dns.Suite
import Fuzz.SelfTest
import Fuzz.EnvVars.Suite
import Fuzz.CryptoHash.Suite
import LeanSwe.LinuxSyscall.Fuzz.Env

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
  /-- Whether `--seed` was explicitly passed. -/
  hasSeed : Bool := false
  /-- Whether `--random-seed` was explicitly passed. -/
  hasRandomSeed : Bool := false
  /-- Shared configuration passed to each selected `FuzzSuite`. -/
  config : FuzzConfig := {}
  deriving Repr

private def registeredSuites : List FuzzSuite := [
  Fuzz.SelfTest.suite,
  Fuzz.Float.suite,
  Fuzz.CmdLine.suite,
  Fuzz.EnvVars.suite,
  Fuzz.CryptoHash.suite,
  Fuzz.Passwd.suite,
  Fuzz.Dns.suite,
  Fuzz.Compress.suite
]

private def truncArg (s : String) (maxLen : Nat := 64) : String :=
  let chars := s.toList
  if chars.length <= maxLen then s
  else String.ofList (chars.take maxLen) ++ "..."

private def isSuiteNameChar (c : Char) : Bool :=
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
  ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '.'

private def isValidSuiteName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: rest =>
    (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')) &&
    rest.all isSuiteNameChar

private def validateRegisteredSuites : Except String Unit := do
  let mut seen : List String := []
  for s in registeredSuites do
    if !isValidSuiteName s.name then
      throw s!"INTERNAL_ERROR: invalid registered suite name '{truncArg s.name}'"
    if seen.contains s.name then
      throw s!"INTERNAL_ERROR: duplicate registered suite '{s.name}'"
    seen := seen ++ [s.name]

private def parseBoundedDec (chars : List Char) : Except String UInt64 := Id.run do
  if chars.isEmpty then
    return .error "nan"
  let mut acc : Nat := 0
  let mut overflow := false
  for c in chars do
    if '0' <= c && c <= '9' then
      if !overflow then
        acc := acc * 10 + (c.toNat - '0'.toNat)
        if acc >= UInt64.size then
          overflow := true
    else
      return .error "nan"
  if overflow then
    return .error "overflow"
  return .ok (UInt64.ofNat acc)

private def parseBoundedHex (chars : List Char) : Except String UInt64 := Id.run do
  if chars.isEmpty then
    return .error "nan"
  let mut acc : Nat := 0
  let mut overflow := false
  for c in chars do
    let d? :=
      if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
      else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
      else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
      else none
    match d? with
    | some d =>
      if !overflow then
        acc := acc * 16 + d
        if acc >= UInt64.size then
          overflow := true
    | none => return .error "nan"
  if overflow then
    return .error "overflow"
  return .ok (UInt64.ofNat acc)

private def parsePositiveNat (flag val : String) : Except String Nat :=
  match parseBoundedDec val.toList with
  | .ok u =>
    if u.toNat > 0 then .ok u.toNat
    else .error s!"INVALID_{flag}: expected >= 1, got '{truncArg val}'"
  | .error "overflow" =>
    .error s!"INVALID_{flag}: out of UInt64 range, got '{truncArg val}'"
  | .error _ =>
    .error s!"INVALID_{flag}: expected Nat, got '{truncArg val}'"

private def parseUInt64 (flag val : String) : Except String UInt64 :=
  let parsed :=
    if val.startsWith "0x" || val.startsWith "0X" then
      parseBoundedHex (val.toList.drop 2)
    else
      parseBoundedDec val.toList
  match parsed with
  | .ok u => .ok u
  | .error "overflow" => .error s!"INVALID_{flag}: out of UInt64 range, got '{truncArg val}'"
  | .error _ => .error s!"INVALID_{flag}: expected UInt64, got '{truncArg val}'"

private def splitSuiteArg (raw : String) : Except String (List String) := do
  if raw.isEmpty then
    throw "INVALID_SUITE: empty suite name"
  let parts := raw.splitOn ","
  for part in parts do
    if part.isEmpty then
      throw s!"INVALID_SUITE: empty suite segment in '{truncArg raw}'"
    if part.toList.any Char.isWhitespace then
      throw s!"INVALID_SUITE: whitespace in suite name '{truncArg part}'"
  return parts

private def stripEqFlag (arg pfx : String) : Option String :=
  if arg.startsWith pfx then
    some (String.ofList (arg.toList.drop pfx.length))
  else
    none

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
    parseArgs rest { opts with hasRandomSeed := true, config := { opts.config with randomSeed := true } }
  | ["--suite"], _ => .error "missing value for --suite"
  | "--suite" :: s :: rest, opts => do
    let names ← splitSuiteArg s
    parseArgs rest { opts with suites := opts.suites ++ names }
  | ["--steps"], _ => .error "missing value for --steps"
  | "--steps" :: s :: rest, opts => do
    let n ← parsePositiveNat "STEPS" s
    parseArgs rest { opts with config := { opts.config with steps := n } }
  | ["--seed"], _ => .error "missing value for --seed"
  | "--seed" :: s :: rest, opts => do
    let sd ← parseUInt64 "SEED" s
    parseArgs rest { opts with hasSeed := true, config := { opts.config with seed := sd } }
  | flag :: rest, opts =>
    if let some s := stripEqFlag flag "--suite=" then do
      let names ← splitSuiteArg s
      parseArgs rest { opts with suites := opts.suites ++ names }
    else if let some s := stripEqFlag flag "--steps=" then do
      let n ← parsePositiveNat "STEPS" s
      parseArgs rest { opts with config := { opts.config with steps := n } }
    else if let some s := stripEqFlag flag "--seed=" then do
      let sd ← parseUInt64 "SEED" s
      parseArgs rest { opts with hasSeed := true, config := { opts.config with seed := sd } }
    else
      .error s!"UNKNOWN_FLAG: {truncArg flag}"

private def drawOsEntropySeed : IO UInt64 := do
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let bytes ← handle.read 8
  if bytes.size < 8 then
    throw (IO.userError s!"drawOsEntropySeed short read from /dev/urandom: got {bytes.size} bytes")
  let mut v : UInt64 := 0
  for i in [:8] do
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
      throw s!"UNKNOWN_SUITE: '{truncArg name}' (available: {avail})"
  return selected

private def validateOptions (opts : CliOptions) : Except String (List FuzzSuite) := do
  if opts.runAll && !opts.suites.isEmpty then
    throw "CONFLICTING_FLAGS: pass either --all or --suite, not both"
  if opts.hasSeed && opts.hasRandomSeed then
    throw "CONFLICTING_FLAGS: pass either --seed or --random-seed, not both"
  resolveSelectedSuites opts

private def printUsage : IO Unit := do
  IO.println "Usage: leanswe-fuzz [OPTIONS]"
  IO.println "  --smoke              Run fast deterministic smoke corpus and shrinker self-test"
  IO.println "  --suite <name>       Run named fuzz suite (repeatable or comma-separated; supports --suite=<name>)"
  IO.println "  --all                Run all registered fuzz suites (default if --suite omitted)"
  IO.println "  --steps <N>          Number of fuzz steps per suite (supports --steps=<N>)"
  IO.println "  --seed <u64>         Deterministic SplitMix64 seed (decimal or 0x hex; supports --seed=<u64>)"
  IO.println "  --random-seed        Draw 64-bit seed from /dev/urandom and print SEED=<u64>"
  IO.println "  --self-test-shrink   Run shrinker self-test before fuzzing"
  IO.println "  --list-suites        List registered fuzz suites and exit"
  IO.println "  -h, --help           Show this help message"

private def safeStream (fd : UInt32) (orig : IO.FS.Stream) : IO.FS.Stream := {
  flush := do
    if (← LeanSwe.LinuxSyscall.Fuzz.Env.fdKind fd) != 6 then orig.flush
  read := orig.read
  write := fun bs => do
    if (← LeanSwe.LinuxSyscall.Fuzz.Env.fdKind fd) != 6 then orig.write bs
  getLine := orig.getLine
  putStr := fun s => do
    if (← LeanSwe.LinuxSyscall.Fuzz.Env.fdKind fd) != 6 then orig.putStr s
  isTty := orig.isTty
}

private def safeFlush (h : IO.FS.Stream) : IO Unit :=
  try h.flush catch _ => pure ()

private def safePrintln (s : String) : IO Unit := do
  try
    IO.println s
    safeFlush (← IO.getStdout)
  catch _ => pure ()

private def safeEprintln (s : String) : IO Unit := do
  try
    IO.eprintln s
    safeFlush (← IO.getStderr)
  catch _ => pure ()

/-- Unified CLI entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--cmdline-fuzz-worker" :: rest => return ← Fuzz.CmdLine.Subproc.workerMain rest
  | _ => pure ()
  let origOut ← IO.getStdout
  let origErr ← IO.getStderr
  if (← LeanSwe.LinuxSyscall.Fuzz.Env.fdKind 1) == 6 then
    let _ ← IO.setStdout (safeStream 1 origOut)
  if (← LeanSwe.LinuxSyscall.Fuzz.Env.fdKind 2) == 6 then
    let _ ← IO.setStderr (safeStream 2 origErr)
  let stdout ← IO.getStdout
  match validateRegisteredSuites with
  | .ok () => pure ()
  | .error msg =>
    safeEprintln msg
    return 2
  let opts ← match parseArgs args with
    | .ok o => pure o
    | .error msg =>
      safeEprintln msg
      return 2
  let selected ← match validateOptions opts with
    | .ok ss => pure ss
    | .error msg =>
      safeEprintln msg
      return 2
  if opts.showHelp then
    try printUsage catch _ => pure ()
    safeFlush stdout
    return 0
  if opts.listSuites then
    for s in registeredSuites do
      safePrintln s.name
    return 0
  let effectiveSeed ←
    if opts.hasRandomSeed then
      try
        drawOsEntropySeed
      catch e =>
        safeEprintln s!"ENTROPY_ERROR: {e}"
        return 2
    else
      pure opts.config.seed
  let effectiveConfig : FuzzConfig := { opts.config with seed := effectiveSeed }
  safePrintln s!"SEED={effectiveSeed}"
  let mut failedSuites : Array String := #[]
  for suite in selected do
    try
      if effectiveConfig.smoke || effectiveConfig.selfTestShrink then
        suite.selfTestShrink effectiveSeed
        safeFlush stdout
      if effectiveConfig.smoke then
        suite.runSmoke effectiveConfig
      else
        suite.runFuzz effectiveConfig
      safeFlush stdout
    catch e =>
      safeFlush stdout
      safeEprintln s!"FUZZ_SUITE_FAILED suite={suite.name}: {e}"
      failedSuites := failedSuites.push suite.name
  if !failedSuites.isEmpty then
    safeEprintln s!"FUZZ_RUN_FAILED failed={failedSuites.size}/{selected.length} suites={",".intercalate failedSuites.toList} seed={effectiveSeed}"
    return 1
  return 0

end Fuzz.Main

/-- Top-level executable entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 :=
  Fuzz.Main.main args

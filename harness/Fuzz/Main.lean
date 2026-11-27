import Fuzz.Common.Suite
import Fuzz.Compress.Suite
import Fuzz.Float.Suite
import Fuzz.CmdLine.Suite
import Fuzz.PostFork.Suite
import Fuzz.ProcessSandbox.Suite
import Fuzz.SelfTest
import Fuzz.EnvVars.Suite
import Fuzz.CryptoHash.Suite
import Fuzz.Sqlite.Suite
import Fuzz.Git.Suite
import Fuzz.Json.Suite
import Fuzz.Toml.Suite
import Fuzz.Uuid.Suite
import Fuzz.Time.Suite
import Fuzz.LinuxSyscall.Env
import Fuzz.LinuxSyscall.Main

namespace Fuzz.Main

open Fuzz.Common
open Fuzz.LinuxSyscall.Main

/-- Parsed CLI options for `leanswe-fuzz`. -/
structure CliOptions where
  /-- Requested suite names (empty unless `--suite` was passed). -/
  suites : List String := []
  /-- Suite names excluded via `--exclude` (repeatable or comma-separated). -/
  excludes : List String := []
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
  /-- Optional output path for nonce-authenticated `ERR_HIT` and `FUZZ_EQUIV` records. -/
  coverageLogPath? : Option String := none
  /-- Optional hex nonce paired with `--coverage-log`. -/
  nonce? : Option String := none
  /-- LinuxSyscall world-model suite and worker options. -/
  world : WorldOptions := {}
  deriving Repr

private def registeredSuites (world : WorldOptions) (outClosed : Bool) : List FuzzSuite :=
  [ Fuzz.SelfTest.suite
  , Fuzz.Float.suite
  , Fuzz.CmdLine.suite
  , Fuzz.EnvVars.suite
  , Fuzz.CryptoHash.suite
  , Fuzz.Compress.suite
  , Fuzz.PostFork.suite
  , Fuzz.ProcessSandbox.suite
  , Fuzz.Sqlite.suite
  , Fuzz.Git.suite
  , Fuzz.Json.suite
  , Fuzz.Toml.suite
  , Fuzz.Uuid.suite
  , Fuzz.Time.suite
  ] ++ Fuzz.LinuxSyscall.Main.suites world outClosed

private def truncArg (s : String) (maxLen : Nat := 64) : String :=
  let chars := s.toList
  if chars.length <= maxLen then s
  else String.ofList (chars.take maxLen) ++ "..."

private def isSuiteNameChar (c : Char) : Bool :=
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
  ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '.'

private def isValidSuiteName (suiteName : String) : Bool :=
  match suiteName.toList with
  | [] => false
  | c :: rest =>
    (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')) &&
    rest.all isSuiteNameChar

private def validateRegisteredSuites (allSuites : List FuzzSuite) : Except String Unit := do
  let mut seen : List String := []
  for s in allSuites do
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

private def parseNatArg (flag val : String) : Except String Nat :=
  match parseBoundedDec val.toList with
  | .ok u => .ok u.toNat
  | .error "overflow" =>
    .error s!"INVALID_{flag}: out of UInt64 range, got '{truncArg val}'"
  | .error _ =>
    .error s!"INVALID_{flag}: expected Nat, got '{truncArg val}'"

private def parsePositiveNat (flag val : String) : Except String Nat :=
  match parseBoundedDec val.toList with
  | .ok u =>
    if u.toNat > 0 then .ok u.toNat
    else .error s!"INVALID_{flag}: expected >= 1, got '{truncArg val}'"
  | .error "overflow" =>
    .error s!"INVALID_{flag}: out of UInt64 range, got '{truncArg val}'"
  | .error _ =>
    .error s!"INVALID_{flag}: expected Nat, got '{truncArg val}'"

private def parseBoundedRange (flag val : String) (lo hi : Nat) : Except String UInt32 := do
  let n ← parseNatArg flag val
  if n < lo || n > hi then
    throw s!"INVALID_{flag}: expected {lo}..{hi}, got '{truncArg val}'"
  return UInt32.ofNat n

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
  | "--require-ns" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with requireNs := true } }
  | "--allow-no-timens" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with allowNoTimens := true } }
  | "--poll-seccomp-worker" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with pollSeccompWorker := true } }
  | "--host-protected" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with hostProtected := true } }
  | "--preseeded-eps" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with preseededEps := true } }
  | "--assert-worker-hits" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with assertWorkerHits := true } }
  | "--close-fd0" :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with closeFd0 := true } }
  | ["--suite"], _ => .error "missing value for --suite"
  | "--suite" :: s :: rest, opts => do
    let names ← splitSuiteArg s
    parseArgs rest { opts with suites := opts.suites ++ names }
  | ["--exclude"], _ => .error "missing value for --exclude"
  | "--exclude" :: s :: rest, opts => do
    let names ← splitSuiteArg s
    parseArgs rest { opts with excludes := opts.excludes ++ names }
  | ["--steps"], _ => .error "missing value for --steps"
  | "--steps" :: s :: rest, opts => do
    let n ← parsePositiveNat "STEPS" s
    parseArgs rest { opts with config := { opts.config with steps := n } }
  | ["--seed"], _ => .error "missing value for --seed"
  | "--seed" :: s :: rest, opts => do
    let sd ← parseUInt64 "SEED" s
    parseArgs rest { opts with hasSeed := true, config := { opts.config with seed := sd } }
  | ["--env-child"], _ => .error "missing value for --env-child"
  | "--env-child" :: mode :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with envChild? := some mode } }
  | ["--seccomp-errno"], _ => .error "missing value for --seccomp-errno"
  | "--seccomp-errno" :: s :: rest, opts => do
    let v ← parseBoundedRange "SECCOMP_ERRNO" s 1 4095
    parseArgs rest { opts with world := { opts.world with seccompErrno := v } }
  | ["--seccomp-mask"], _ => .error "missing value for --seccomp-mask"
  | "--seccomp-mask" :: s :: rest, opts => do
    let v ← parseBoundedRange "SECCOMP_MASK" s 1 7
    parseArgs rest { opts with world := { opts.world with seccompMask := v } }
  | ["--seccomp-delay-steps"], _ => .error "missing value for --seccomp-delay-steps"
  | "--seccomp-delay-steps" :: s :: rest, opts => do
    let n ← parseNatArg "SECCOMP_DELAY_STEPS" s
    parseArgs rest { opts with world := { opts.world with seccompDelaySteps := n } }
  | ["--dir"], _ => .error "missing value for --dir"
  | "--dir" :: d :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with dir := d, explicitDir := true } }
  | ["--fs-root"], _ => .error "missing value for --fs-root"
  | "--fs-root" :: d :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with dir := d, explicitDir := true } }
  | ["--cross-dir"], _ => .error "missing value for --cross-dir"
  | "--cross-dir" :: d :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with crossDir? := some d } }
  | ["--chroot-dir"], _ => .error "missing value for --chroot-dir"
  | "--chroot-dir" :: d :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with chrootDir? := some d } }
  | ["--worker-mode"], _ => .error "missing value for --worker-mode"
  | "--worker-mode" :: m :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with workerMode? := some m } }
  | ["--seed-overlay-lower"], _ => .error "missing value for --seed-overlay-lower"
  | ["--seed-overlay-lower", _], _ => .error "missing count for --seed-overlay-lower"
  | "--seed-overlay-lower" :: d :: n :: rest, opts => do
    let k ← parseNatArg "SEED_OVERLAY_LOWER" n
    parseArgs rest { opts with world := { opts.world with seedOverlayLower? := some (d, k) } }
  | ["--seed-ro-tree"], _ => .error "missing value for --seed-ro-tree"
  | "--seed-ro-tree" :: d :: rest, opts =>
    parseArgs rest { opts with world := { opts.world with seedRoTree? := some d } }
  | ["--rlimit-nofile"], _ => .error "missing value for --rlimit-nofile"
  | "--rlimit-nofile" :: s :: rest, opts => do
    let n ← parsePositiveNat "RLIMIT_NOFILE" s
    parseArgs rest { opts with world := { opts.world with rlimitNofile? := some (UInt64.ofNat n) } }
  | ["--coverage-log"], _ => .error "missing value for --coverage-log"
  | "--coverage-log" :: p :: rest, opts =>
    parseArgs rest { opts with coverageLogPath? := some p }
  | ["--nonce"], _ => .error "missing value for --nonce"
  | "--nonce" :: nc :: rest, opts =>
    parseArgs rest { opts with nonce? := some nc }
  | flag :: rest, opts =>
    if let some s := stripEqFlag flag "--suite=" then do
      let names ← splitSuiteArg s
      parseArgs rest { opts with suites := opts.suites ++ names }
    else if let some s := stripEqFlag flag "--exclude=" then do
      let names ← splitSuiteArg s
      parseArgs rest { opts with excludes := opts.excludes ++ names }
    else if let some s := stripEqFlag flag "--steps=" then do
      let n ← parsePositiveNat "STEPS" s
      parseArgs rest { opts with config := { opts.config with steps := n } }
    else if let some s := stripEqFlag flag "--seed=" then do
      let sd ← parseUInt64 "SEED" s
      parseArgs rest { opts with hasSeed := true, config := { opts.config with seed := sd } }
    else if let some d := stripEqFlag flag "--dir=" then
      parseArgs rest { opts with world := { opts.world with dir := d, explicitDir := true } }
    else if let some d := stripEqFlag flag "--fs-root=" then
      parseArgs rest { opts with world := { opts.world with dir := d, explicitDir := true } }
    else if let some d := stripEqFlag flag "--cross-dir=" then
      parseArgs rest { opts with world := { opts.world with crossDir? := some d } }
    else if let some d := stripEqFlag flag "--chroot-dir=" then
      parseArgs rest { opts with world := { opts.world with chrootDir? := some d } }
    else if let some m := stripEqFlag flag "--worker-mode=" then
      parseArgs rest { opts with world := { opts.world with workerMode? := some m } }
    else if let some d := stripEqFlag flag "--seed-ro-tree=" then
      parseArgs rest { opts with world := { opts.world with seedRoTree? := some d } }
    else if let some m := stripEqFlag flag "--env-child=" then
      parseArgs rest { opts with world := { opts.world with envChild? := some m } }
    else if let some s := stripEqFlag flag "--seccomp-errno=" then do
      let v ← parseBoundedRange "SECCOMP_ERRNO" s 1 4095
      parseArgs rest { opts with world := { opts.world with seccompErrno := v } }
    else if let some s := stripEqFlag flag "--seccomp-mask=" then do
      let v ← parseBoundedRange "SECCOMP_MASK" s 1 7
      parseArgs rest { opts with world := { opts.world with seccompMask := v } }
    else if let some s := stripEqFlag flag "--seccomp-delay-steps=" then do
      let n ← parseNatArg "SECCOMP_DELAY_STEPS" s
      parseArgs rest { opts with world := { opts.world with seccompDelaySteps := n } }
    else if let some s := stripEqFlag flag "--rlimit-nofile=" then do
      let n ← parsePositiveNat "RLIMIT_NOFILE" s
      parseArgs rest { opts with world := { opts.world with rlimitNofile? := some (UInt64.ofNat n) } }
    else if let some p := stripEqFlag flag "--coverage-log=" then
      parseArgs rest { opts with coverageLogPath? := some p }
    else if let some nc := stripEqFlag flag "--nonce=" then
      parseArgs rest { opts with nonce? := some nc }
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

private def findSuite? (allSuites : List FuzzSuite) (suiteName : String) : Option FuzzSuite :=
  allSuites.find? (·.name == suiteName)

private def resolveSelectedSuites (allSuites : List FuzzSuite) (opts : CliOptions) : Except String (List FuzzSuite) := do
  let mut excluded : List String := []
  for exName in opts.excludes do
    match findSuite? allSuites exName with
    | some _ =>
      if !excluded.contains exName then
        excluded := excluded ++ [exName]
    | none =>
      let avail := ", ".intercalate (allSuites.map (·.name))
      throw s!"UNKNOWN_SUITE: '{truncArg exName}' in --exclude (available: {avail})"
  let base ←
    if opts.runAll || opts.suites.isEmpty then
      pure allSuites
    else do
      let mut selected : List FuzzSuite := []
      let mut seen : List String := []
      for suiteName in opts.suites do
        if seen.contains suiteName then
          continue
        match findSuite? allSuites suiteName with
        | some s =>
          selected := selected ++ [s]
          seen := seen ++ [suiteName]
        | none =>
          let avail := ", ".intercalate (allSuites.map (·.name))
          throw s!"UNKNOWN_SUITE: '{truncArg suiteName}' (available: {avail})"
      pure selected
  let filtered := base.filter fun s => !excluded.contains s.name
  if filtered.isEmpty then
    throw "NO_SUITES_SELECTED: all selected suites were excluded by --exclude"
  return filtered

private def suiteTargetPackages : String → Array String
  | "selftest" => #["Fuzz.SelfTest"]
  | "float" => #["LeanSwe.NumParse", "LeanSwe.Toml"]
  | "cmdline" => #["LeanSwe.CmdLine"]
  | "envvars" => #["LeanSwe.EnvVars"]
  | "cryptohash" => #["LeanSwe.CryptoHash.Raw", "LeanSwe.CryptoHash"]
  | "compress" => #["LeanSwe.Compress"]
  | "postfork" => #["LeanSwe.PostFork"]
  | "processsandbox" => #["LeanSwe.ProcessSandbox"]
  | "sqlite" => #["LeanSwe.Sqlite.Raw", "LeanSwe.Sqlite"]
  | "git" => #["LeanSwe.Git"]
  | "json" => #["LeanSwe.Json"]
  | "toml" => #["LeanSwe.Toml"]
  | "uuid" => #["LeanSwe.Uuid"]
  | "time" => #["LeanSwe.Time"]
  | "timerand" => #["LeanSwe.LinuxSyscall.TimeRand"]
  | "files" => #["LeanSwe.LinuxSyscall.Files"]
  | "process" => #["LeanSwe.LinuxSyscall.Process"]
  | "poll" => #["LeanSwe.LinuxSyscall.Poll"]
  | other => #[other]

private def validateOptions (allSuites : List FuzzSuite) (opts : CliOptions) : Except String (List FuzzSuite) := do
  if opts.runAll && !opts.suites.isEmpty then
    throw "CONFLICTING_FLAGS: pass either --all or --suite, not both"
  if opts.hasSeed && opts.hasRandomSeed then
    throw "CONFLICTING_FLAGS: pass either --seed or --random-seed, not both"
  match opts.coverageLogPath?, opts.nonce? with
  | some lp, some nc =>
    if lp.isEmpty || nc.isEmpty then
      throw "INVALID_ARGS: --coverage-log and --nonce must be non-empty"
  | some _, none | none, some _ =>
    throw "INVALID_ARGS: --coverage-log and --nonce must be provided together"
  | none, none => pure ()
  if opts.world.hasSpecialMode then
    return []
  resolveSelectedSuites allSuites opts

private def printUsage : IO Unit := do
  IO.println "Usage: leanswe-fuzz [OPTIONS]"
  IO.println "  --smoke                  Run fast deterministic smoke corpus and shrinker self-test"
  IO.println "  --suite <name>           Run named fuzz suite (repeatable or comma-separated; supports --suite=<name>)"
  IO.println "  --exclude <name>         Exclude named fuzz suite (repeatable or comma-separated; supports --exclude=<name>)"
  IO.println "  --all                    Run all registered fuzz suites (default if --suite omitted)"
  IO.println "  --steps <N>              Number of fuzz steps per suite (supports --steps=<N>)"
  IO.println "  --seed <u64>             Deterministic SplitMix64 seed (decimal or 0x hex; supports --seed=<u64>)"
  IO.println "  --random-seed            Draw 64-bit seed from /dev/urandom and print SEED=<u64>"
  IO.println "  --self-test-shrink       Run shrinker self-test before fuzzing"
  IO.println "  --require-ns             Require unprivileged namespaces for namespace-isolated suites"
  IO.println "  --allow-no-timens        Allow skipping CLONE_NEWTIME sub-episodes when unavailable"
  IO.println "  --dir, --fs-root <path>  Scratch directory root for files fuzzer episodes"
  IO.println "  --coverage-log <path>    Write nonce-authenticated ERR_HIT and FUZZ_EQUIV records"
  IO.println "  --nonce <hex>            Nonce token paired with --coverage-log"
  IO.println "  --list-suites            List registered fuzz suites and exit"
  IO.println "  -h, --help               Show this help message"

/-- Unified CLI entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--cmdline-fuzz-worker" :: rest => return ← Fuzz.CmdLine.Subproc.workerMain rest
  | _ => pure ()
  if let some rc ← Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker args then
    return rc
  let (outClosed, errClosed) ← Fuzz.LinuxSyscall.Env.sanitizeClosedStdio
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let opts ← match parseArgs args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln msg
      stderr.flush
      return 2
  let worldOpts : WorldOptions := {
    opts.world with
    coverageLogPath? := opts.coverageLogPath?
    coverageNonce? := opts.nonce?
  }
  let allSuites := registeredSuites worldOpts outClosed
  match validateRegisteredSuites allSuites with
  | .ok () => pure ()
  | .error msg =>
    IO.eprintln msg
    stderr.flush
    return 2
  let selected ← match validateOptions allSuites opts with
    | .ok ss => pure ss
    | .error msg =>
      IO.eprintln msg
      stderr.flush
      return 2
  if opts.showHelp then
    printUsage
    stdout.flush
    return 0
  if opts.listSuites then
    for s in allSuites do
      IO.println s.name
    stdout.flush
    return 0
  let effectiveSeed ←
    if opts.hasRandomSeed then
      try
        drawOsEntropySeed
      catch e =>
        IO.eprintln s!"ENTROPY_ERROR: {e}"
        stderr.flush
        return 2
    else
      pure opts.config.seed
  if worldOpts.hasSpecialMode then
    match opts.coverageLogPath?, opts.nonce? with
    | some lp, some nc => initCoverageLog lp nc
    | _, _ => pure ()
    let rc ← try
      Fuzz.LinuxSyscall.Main.runSpecialMode worldOpts opts.suites opts.config.steps
        effectiveSeed opts.hasRandomSeed outClosed errClosed
    finally
      closeCoverageLog
    stdout.flush
    stderr.flush
    return rc
  let effectiveConfig : FuzzConfig := { opts.config with seed := effectiveSeed }
  IO.println s!"SEED={effectiveSeed}"
  stdout.flush
  match opts.coverageLogPath?, opts.nonce? with
  | some lp, some nc => initCoverageLog lp nc
  | _, _ => pure ()
  let mut failedSuites : Array String := #[]
  try
    for suite in selected do
      resetSuiteBuckets
      let mut suiteOk := true
      try
        if effectiveConfig.smoke || effectiveConfig.selfTestShrink then
          suite.selfTestShrink effectiveSeed
          stdout.flush
        if effectiveConfig.smoke then
          suite.runSmoke effectiveConfig
        else
          suite.runFuzz effectiveConfig
        stdout.flush
      catch e =>
        suiteOk := false
        stdout.flush
        IO.eprintln s!"FUZZ_SUITE_FAILED suite={suite.name}: {e}"
        stderr.flush
        failedSuites := failedSuites.push suite.name
      let (bucketsHit, bucketsTotal) ← getSuiteBuckets
      let actualSteps ← getSuiteSteps effectiveConfig.steps
      if bucketsTotal > 0 || !suiteOk then
        for pkg in suiteTargetPackages suite.name do
          logFuzzEquiv pkg suite.name actualSteps bucketsHit bucketsTotal suiteOk
  finally
    closeCoverageLog
  if !failedSuites.isEmpty then
    IO.eprintln s!"FUZZ_RUN_FAILED failed={failedSuites.size}/{selected.length} suites={",".intercalate failedSuites.toList} seed={effectiveSeed}"
    stderr.flush
    return 1
  return 0

end Fuzz.Main

/-- Top-level executable entry point for `leanswe-fuzz`. -/
def main (args : List String) : IO UInt32 :=
  Fuzz.Main.main args

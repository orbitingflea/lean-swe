import Tests.Common
import Tests.Mutate.Codecs
import Tests.Mutate.Compress
import Tests.Mutate.ConnectProxy
import Tests.Mutate.CryptoHash
import Tests.Mutate.EnvVars
import Tests.Mutate.FsAndProcess
import Tests.Mutate.LinuxSyscall
import Tests.Mutate.NetRelay
import Tests.Mutate.PostFork
import Tests.Mutate.Sqlite

open Tests.Common
open Tests.Mutate

private def allSuites : Array MutateSuite := #[
  Codecs.regExpSuite,
  Codecs.globSuite,
  FsAndProcess.fsRawSuite,
  FsAndProcess.fsSuite,
  FsAndProcess.processSuite,
  Codecs.timeSuite,
  Codecs.jsonSuite,
  EnvVars.envVarsRawSuite,
  EnvVars.envVarsSuite,
  Codecs.uuidSuite,
  Sqlite.sqliteRawSuite,
  Sqlite.sqliteSuite,
  FsAndProcess.gitSuite,
  Codecs.cmdLineSuite,
  Codecs.numParseSuite,
  Codecs.tomlSuite,
  FsAndProcess.tempDirSuite,
  Compress.compressSuite,
  Codecs.base64Suite,
  CryptoHash.cryptoHashRawSuite,
  CryptoHash.cryptoHashSuite,
  Codecs.tarSuite,
  FsAndProcess.processSandboxSeccompSuite,
  FsAndProcess.processSandboxRawSuite,
  FsAndProcess.processSandboxSuite,
  ConnectProxy.connectProxySuite,
  NetRelay.netRelaySuite,
  FsAndProcess.slotPoolSuite
] ++ LinuxSyscall.suites ++ #[PostFork.postForkSuite]

private structure MutateFlags where
  mode : String := "full"
  suites : Array String := #[]

private def parseFlags : List String → Except String MutateFlags
  | [] => .ok {}
  | "--mode" :: m :: rest => do
    let f ← parseFlags rest
    return { f with mode := m }
  | "--suite" :: s :: rest => do
    let f ← parseFlags rest
    return { f with suites := parseSuiteCsv s ++ f.suites }
  | flag :: _ => .error s!"unknown flag {flag}"

/-- Mutation test driver supporting `--suite` filtering and omitting all `Proofs` imports. -/
def main (args : List String) : IO UInt32 := do
  if let some probe := findRuntimeProbe? args then
    return (← probe)
  if let some worker := LinuxSyscall.findEarlyWorker? args then
    return (← worker)
  if let "--postfork-probe" :: _ := args then
    return (← PostFork.runPostForkSubprocProbe)
  let flags ← match parseFlags args with
    | .ok f => pure f
    | .error msg =>
      IO.eprintln msg
      return 2
  if flags.mode != "baseline" && flags.mode != "full" then
    IO.eprintln s!"unknown --mode {flags.mode}"
    return 2
  let selected ← match selectNamedSuites allSuites (·.name) flags.suites with
    | .ok xs => pure xs
    | .error msg =>
      IO.eprintln msg
      return 2
  for suite in selected do
    try
      match ← suite.runBase with
      | none => pure ()
      | some reason => IO.println s!"SKIP: {suite.name} ({reason})"
      if flags.mode == "full" then
        suite.runExtra
    catch err =>
      IO.eprintln s!"FAIL: {suite.name} ({err.toString})"
      return 1
  return 0

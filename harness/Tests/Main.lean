import Core.Assumptions
import LeanSwe
import Tests.Common

open LeanSwe

private def escapeWorkflowCmd (s : String) : String :=
  ((s.replace "%" "%25").replace "\r" "%0D").replace "\n" "%0A"

private def singleLine (s : String) : String :=
  (s.replace "\r" " ").replace "\n" " "

private def allSuites : Array (String × String × IO (Option String)) := #[
  ("RegExp", "LeanSwe/RegExp/RuntimeTests.lean", do RegExp.RuntimeTests.runAll; Tests.Common.smokeRegExp; return none),
  ("Glob", "LeanSwe/Glob/RuntimeTests.lean", do Glob.RuntimeTests.runAll; return none),
  ("Fs", "LeanSwe/Fs/RuntimeTests.lean", do Fs.RuntimeTests.runAll; return none),
  ("Process", "LeanSwe/Process/RuntimeTests.lean", do Process.RuntimeTests.runAll; return none),
  ("Time", "LeanSwe/Time/RuntimeTests.lean", do Time.RuntimeTests.runAll; return none),
  ("Json", "LeanSwe/Json/RuntimeTests.lean", do Json.RuntimeTests.runAll; return none),
  ("EnvVars.Raw", "LeanSwe/EnvVars/Raw/RuntimeTests.lean", do EnvVars.Raw.RuntimeTests.runAll; return none),
  ("EnvVars", "LeanSwe/EnvVars/RuntimeTests.lean", do EnvVars.RuntimeTests.runAll; return none),
  ("Uuid", "LeanSwe/Uuid/RuntimeTests.lean", do Uuid.RuntimeTests.runAll; return none),
  ("Sqlite.Raw", "LeanSwe/Sqlite/Raw/RuntimeTests.lean", do Sqlite.Raw.RuntimeTests.runAll; return none),
  ("Sqlite", "LeanSwe/Sqlite/RuntimeTests.lean", do Sqlite.RuntimeTests.runAll; return none),
  ("Git", "LeanSwe/Git/RuntimeTests.lean", do Git.RuntimeTests.runAll; return none),
  ("CmdLine", "LeanSwe/CmdLine/RuntimeTests.lean", do CmdLine.RuntimeTests.runAll; return none),
  ("NumParse", "LeanSwe/NumParse/RuntimeTests.lean", do NumParse.RuntimeTests.runAll; return none),
  ("Toml", "LeanSwe/Toml/RuntimeTests.lean", do Toml.RuntimeTests.runAll; return none),
  ("TempDir", "LeanSwe/TempDir/RuntimeTests.lean", do TempDir.RuntimeTests.runAll; return none),
  ("Compress", "LeanSwe/Compress/RuntimeTests.lean", do Compress.RuntimeTests.runAll; return none),
  ("Base64", "LeanSwe/Base64/RuntimeTests.lean", do Base64.RuntimeTests.runAll; return none),
  ("CryptoHash.Raw", "LeanSwe/CryptoHash/Raw/RuntimeTests.lean", do CryptoHash.Raw.RuntimeTests.runAll; return none),
  ("CryptoHash", "LeanSwe/CryptoHash/RuntimeTests.lean", do CryptoHash.RuntimeTests.runAll; return none),
  ("Tar", "LeanSwe/Tar/RuntimeTests.lean", do Tar.RuntimeTests.runAll; return none),
  ("ConnectProxy", "LeanSwe/ConnectProxy/RuntimeTests.lean", do ConnectProxy.RuntimeTests.runAll; return none),
  ("SlotPool", "LeanSwe/SlotPool/RuntimeTests.lean", do SlotPool.RuntimeTests.runAll; return none),
  ("PostFork", "LeanSwe/PostFork/RuntimeTests.lean", do PostFork.RuntimeTests.runAll; return none)
]

private def findUnregisteredRuntimeTests : IO (Array String) := do
  let (leanSweDir, stripPfx) ← do
    if ← (System.FilePath.mk "LeanSwe").pathExists then
      pure (System.FilePath.mk "LeanSwe", "")
    else if ← (System.FilePath.mk "../LeanSwe").pathExists then
      pure (System.FilePath.mk "../LeanSwe", "../")
    else
      return #[]
  let registered := allSuites.map (fun (_, path, _) => path)
  let mut unregistered : Array String := #[]
  for entry in (← System.FilePath.walkDir leanSweDir) do
    if entry.fileName == some "RuntimeTests.lean" then
      let s := entry.toString
      let rel := if stripPfx.isEmpty then s else (s.drop stripPfx.length).toString
      if !registered.contains rel then
        unregistered := unregistered.push rel
  return unregistered.qsort (· < ·)

private def formatStepSummary (label : Option String) (passed : Nat)
    (skipped failed : Array (String × String)) : String :=
  let heading := match label with
    | some l => if l.isEmpty then "### Runtime tests" else s!"### {l}: Runtime tests"
    | none => "### Runtime tests"
  let base :=
    s!"{heading}\n\n| Passed | Skipped | Failed |\n| --- | --- | --- |\n| {passed} | {skipped.size} | {failed.size} |\n\n"
  let skipSec :=
    if skipped.isEmpty then ""
    else
      let items := skipped.foldl (fun acc (name, reason) => acc ++ s!"- `{name}`: {reason}\n") ""
      "**Skipped suites:**\n\n" ++ items ++ "\n"
  let failSec :=
    if failed.isEmpty then ""
    else
      let items := failed.foldl (fun acc (name, msg) => acc ++ s!"- `{name}`: {msg}\n") ""
      "**Failed suites:**\n\n" ++ items ++ "\n"
  base ++ skipSec ++ failSec

private structure MainOptions where
  logPath? : Option String := none
  nonce? : Option String := none
  coverageLogPath? : Option String := none
  coverageNonce? : Option String := none
  suites : Array String := #[]

private def parseMainOptions : List String → Except String MainOptions
  | [] => .ok {}
  | "--assump-log" :: lp :: rest => do
    let opts ← parseMainOptions rest
    return { opts with logPath? := some lp }
  | "--assump-nonce" :: nc :: rest => do
    let opts ← parseMainOptions rest
    return { opts with nonce? := some nc }
  | "--coverage-log" :: lp :: rest => do
    let opts ← parseMainOptions rest
    return { opts with coverageLogPath? := some lp }
  | "--coverage-nonce" :: nc :: rest => do
    let opts ← parseMainOptions rest
    return { opts with coverageNonce? := some nc }
  | "--suite" :: s :: rest => do
    let opts ← parseMainOptions rest
    return { opts with suites := Tests.Common.parseSuiteCsv s ++ opts.suites }
  | flag :: _ => .error s!"UNKNOWN_FLAG: {flag}"

private def nullOutStream : IO.FS.Stream where
  flush := pure ()
  read _ := pure ByteArray.empty
  write _ := pure ()
  getLine := pure ""
  putStr _ := pure ()
  isTty := pure false

private def isStdioFdClosedOrAnon (slot : LinuxSyscall.Files.StdioFd) : IO Bool := do
  match ← LinuxSyscall.Files.dupStdio slot with
  | .error e => return e == LinuxSyscall.Errno.EBADF
  | .ok dupFd =>
    try
      match ← LinuxSyscall.Files.fstat dupFd with
      | .ok st => return st.kind == .other
      | .error _ => return false
    finally
      let _ ← LinuxSyscall.Files.close dupFd

private def sanitizeClosedStdio : IO Unit := do
  if ← isStdioFdClosedOrAnon .stdout then
    let _ ← IO.setStdout nullOutStream
  if ← isStdioFdClosedOrAnon .stderr then
    let _ ← IO.setStderr nullOutStream

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main (args : List String) : IO UInt32 := do
  if let some probe := Tests.Common.findRuntimeProbe? args then
    return (← probe)
  sanitizeClosedStdio
  let opts ← match parseMainOptions args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln msg
      return 2
  match opts.logPath?, opts.nonce? with
  | some _, none | none, some _ =>
    IO.eprintln "INVALID_ARGS: --assump-log and --assump-nonce must be provided together"
    return 2
  | _, _ => pure ()
  let effectiveCovNonce? := opts.coverageNonce?.orElse (fun _ => opts.nonce?)
  match opts.coverageLogPath?, opts.coverageNonce?, effectiveCovNonce? with
  | none, some _, _ =>
    IO.eprintln "INVALID_ARGS: --coverage-nonce requires --coverage-log"
    return 2
  | some lp, _, some nc =>
    if lp.isEmpty || nc.isEmpty then
      IO.eprintln "INVALID_ARGS: --coverage-log and nonce must be non-empty"
      return 2
  | some _, _, none =>
    IO.eprintln "INVALID_ARGS: --coverage-log requires --coverage-nonce or --assump-nonce"
    return 2
  | none, none, _ => pure ()
  let selectedSuites ← match Tests.Common.selectNamedSuites allSuites (fun (name, _, _) => name) opts.suites with
    | .ok xs => pure xs
    | .error msg =>
      IO.eprintln msg
      return 2
  let unregistered ← findUnregisteredRuntimeTests
  if !unregistered.isEmpty then
    for path in unregistered do
      IO.eprintln s!"UNREGISTERED_RUNTIMETESTS: {path}"
    return 1
  let inGitHubActions := (← IO.getEnv "GITHUB_ACTIONS") == some "true"
  match opts.logPath?, opts.nonce? with
  | some lp, some nc => Core.initAssumpLog lp nc
  | _, _ => pure ()
  match opts.coverageLogPath?, effectiveCovNonce? with
  | some lp, some nc =>
    Core.initCoverageLog lp nc
    Core.setErrTestPassHook (some Tests.Common.onRegisteredErrorTestPass)
  | _, _ => pure ()
  let mut passed : Nat := 0
  let mut skipped : Array (String × String) := #[]
  let mut failed : Array (String × String) := #[]
  for (name, _, action) in selectedSuites do
    try
      match ← action with
      | none =>
        passed := passed + 1
      | some reason =>
        let cleanReason := singleLine reason
        IO.println s!"SKIP: {name} ({cleanReason})"
        if inGitHubActions then
          let msg := escapeWorkflowCmd s!"{name}: {cleanReason}"
          IO.println s!"::notice title=Skipped runtime test suite::{msg}"
        skipped := skipped.push (name, cleanReason)
    catch err =>
      let cleanErr := singleLine err.toString
      IO.eprintln s!"FAIL: {name} ({cleanErr})"
      failed := failed.push (name, cleanErr)
  Core.setErrTestPassHook none
  Core.closeAssumpLog
  Core.closeCoverageLog
  IO.println s!"TEST_SUMMARY: passed={passed} skipped={skipped.size} failed={failed.size}"
  for (name, reason) in skipped do
    IO.println s!"SKIPPED_SUITE: {name} | {reason}"
  for (name, msg) in failed do
    IO.eprintln s!"FAILED_SUITE: {name} | {msg}"
  let summaryLabel ← IO.getEnv "LEANSWE_SUMMARY_LABEL"
  Core.appendStepSummary (formatStepSummary summaryLabel passed skipped failed)
  if !failed.isEmpty then
    return 1
  if skipped.isEmpty then
    IO.println "ALL_LEAN_SWE_TESTS_PASSED"
  else
    IO.println "LEAN_SWE_TESTS_PASSED_WITH_SKIPS"
  return 0

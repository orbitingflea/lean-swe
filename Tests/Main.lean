import Core.Assumptions
import LeanSwe

open LeanSwe

private def smokeRegExp : IO Unit := do
  match RegExp.findAll "[0-9]+" "a1b22" with
  | .ok xs =>
    if xs.map (·.matched) != #["1", "22"] then
      throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
  | .error e =>
    throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")

private def escapeWorkflowCmd (s : String) : String :=
  ((s.replace "%" "%25").replace "\r" "%0D").replace "\n" "%0A"

private def singleLine (s : String) : String :=
  (s.replace "\r" " ").replace "\n" " "

private def allSuites : Array (String × String × IO (Option String)) := #[
  ("RegExp", "LeanSwe/RegExp/RuntimeTests.lean", do RegExp.RuntimeTests.runAll; smokeRegExp; return none),
  ("Glob", "LeanSwe/Glob/RuntimeTests.lean", do Glob.RuntimeTests.runAll; return none),
  ("Fs.Raw", "LeanSwe/Fs/Raw/RuntimeTests.lean", do Fs.Raw.RuntimeTests.runAll; return none),
  ("Fs", "LeanSwe/Fs/RuntimeTests.lean", do Fs.RuntimeTests.runAll; return none),
  ("Process.Raw", "LeanSwe/Process/Raw/RuntimeTests.lean", do Process.Raw.RuntimeTests.runAll; return none),
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
  ("ProcessSandbox.Seccomp", "LeanSwe/ProcessSandbox/Seccomp/RuntimeTests.lean", do ProcessSandbox.Seccomp.RuntimeTests.runAll; return none),
  ("ProcessSandbox.Raw", "LeanSwe/ProcessSandbox/Raw/RuntimeTests.lean", ProcessSandbox.Raw.RuntimeTests.runAllOutcome),
  ("ProcessSandbox", "LeanSwe/ProcessSandbox/RuntimeTests.lean", ProcessSandbox.RuntimeTests.runAllOutcome),
  ("ConnectProxy.Raw", "LeanSwe/ConnectProxy/Raw/RuntimeTests.lean", do ConnectProxy.Raw.RuntimeTests.runAll; return none),
  ("ConnectProxy", "LeanSwe/ConnectProxy/RuntimeTests.lean", do ConnectProxy.RuntimeTests.runAll; return none),
  ("SlotPool", "LeanSwe/SlotPool/RuntimeTests.lean", do SlotPool.RuntimeTests.runAll; return none),
  ("LinuxSyscall.Sandbox", "LeanSwe/LinuxSyscall/Sandbox/RuntimeTests.lean", do LinuxSyscall.Sandbox.RuntimeTests.runAll; return none),
  ("LinuxSyscall.TimeRand", "LeanSwe/LinuxSyscall/TimeRand/RuntimeTests.lean", do LinuxSyscall.TimeRand.RuntimeTests.runAll; return none)
]

private def findUnregisteredRuntimeTests : IO (Array String) := do
  let leanSweDir : System.FilePath := "LeanSwe"
  unless ← leanSweDir.pathExists do
    return #[]
  let registered := allSuites.map (fun (_, path, _) => path)
  let mut unregistered : Array String := #[]
  for entry in (← System.FilePath.walkDir leanSweDir) do
    if entry.fileName == some "RuntimeTests.lean" then
      if !registered.contains entry.toString then
        unregistered := unregistered.push entry.toString
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
  suites : Array String := #[]

private def parseMainOptions : List String → Except String MainOptions
  | [] => .ok {}
  | "--assump-log" :: lp :: rest => do
    let opts ← parseMainOptions rest
    return { opts with logPath? := some lp }
  | "--assump-nonce" :: nc :: rest => do
    let opts ← parseMainOptions rest
    return { opts with nonce? := some nc }
  | "--suite" :: s :: rest => do
    let opts ← parseMainOptions rest
    let parts := (s.splitOn ",").filterMap fun item =>
      let t := item.trimAscii.toString
      if t.isEmpty then none else some t
    return { opts with suites := parts.toArray ++ opts.suites }
  | flag :: _ => .error s!"UNKNOWN_FLAG: {flag}"

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--envvars-raw-probe" :: rest =>
    return (← EnvVars.Raw.RuntimeTests.probeMain rest)
  | "--envvars-probe" :: rest =>
    return (← EnvVars.RuntimeTests.probeMain rest)
  | "--cmdline-probe" :: rest =>
    return (← CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest =>
    return (← SlotPool.RuntimeTests.probeMain rest)
  | "--sandbox-strace-worker" :: mode :: [] =>
    LinuxSyscall.Sandbox.RuntimeTests.runStraceWorker mode
    return 0
  | "--sandbox-strace-fault-check" :: [] =>
    LinuxSyscall.Sandbox.RuntimeTests.runStraceFaultCheck
    IO.println "SANDBOX_STRACE_FAULT_CHECK_OK"
    return 0
  | "--timerand-strace-fault-check" :: rest =>
    return (← LinuxSyscall.TimeRand.RuntimeTests.probeMain rest)
  | "--uuid-probe" :: rest =>
    return (← Uuid.RuntimeTests.probeMain rest)
  | "--time-probe" :: rest =>
    return (← Time.RuntimeTests.probeMain rest)
  | _ =>
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
    let knownNames := allSuites.map (fun (name, _, _) => name)
    let filterAll := opts.suites.isEmpty || opts.suites.contains "all"
    if !filterAll then
      for s in opts.suites do
        if !knownNames.contains s then
          IO.eprintln s!"UNKNOWN_SUITE: {s}"
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
    let selectedSuites :=
      if filterAll then allSuites
      else allSuites.filter fun (name, _, _) => opts.suites.contains name
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
    Core.closeAssumpLog
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

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
  ("Uuid.Raw", "LeanSwe/Uuid/Raw/RuntimeTests.lean", do Uuid.Raw.RuntimeTests.runAll; return none),
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
  ("ProcessSandbox.Raw", "LeanSwe/ProcessSandbox/Raw/RuntimeTests.lean", ProcessSandbox.Raw.RuntimeTests.runAllOutcome),
  ("ProcessSandbox", "LeanSwe/ProcessSandbox/RuntimeTests.lean", ProcessSandbox.RuntimeTests.runAllOutcome),
  ("ConnectProxy.Raw", "LeanSwe/ConnectProxy/Raw/RuntimeTests.lean", do ConnectProxy.Raw.RuntimeTests.runAll; return none),
  ("ConnectProxy", "LeanSwe/ConnectProxy/RuntimeTests.lean", do ConnectProxy.RuntimeTests.runAll; return none),
  ("SlotPool", "LeanSwe/SlotPool/RuntimeTests.lean", do SlotPool.RuntimeTests.runAll; return none)
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

private def writeStepSummary (passed : Nat) (skipped failed : Array (String × String)) : IO Unit := do
  let some summaryPath ← IO.getEnv "GITHUB_STEP_SUMMARY" | return ()
  if summaryPath.isEmpty then
    return ()
  let heading := match ← IO.getEnv "LEANSWE_SUMMARY_LABEL" with
    | some label => if label.isEmpty then "### Runtime tests" else s!"### {label}: Runtime tests"
    | none => "### Runtime tests"
  let h ← IO.FS.Handle.mk summaryPath .append
  h.putStr s!"{heading}\n\n"
  h.putStr "| Passed | Skipped | Failed |\n"
  h.putStr "| --- | --- | --- |\n"
  h.putStr s!"| {passed} | {skipped.size} | {failed.size} |\n\n"
  if !skipped.isEmpty then
    h.putStr "**Skipped suites:**\n\n"
    for (name, reason) in skipped do
      h.putStr s!"- `{name}`: {reason}\n"
    h.putStr "\n"
  if !failed.isEmpty then
    h.putStr "**Failed suites:**\n\n"
    for (name, msg) in failed do
      h.putStr s!"- `{name}`: {msg}\n"
    h.putStr "\n"
  h.flush

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--cmdline-probe" :: rest =>
    return (← CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest =>
    return (← SlotPool.RuntimeTests.probeMain rest)
  | _ =>
    let unregistered ← findUnregisteredRuntimeTests
    if !unregistered.isEmpty then
      for path in unregistered do
        IO.eprintln s!"UNREGISTERED_RUNTIMETESTS: {path}"
      return 1
    let inGitHubActions := (← IO.getEnv "GITHUB_ACTIONS") == some "true"
    let mut passed : Nat := 0
    let mut skipped : Array (String × String) := #[]
    let mut failed : Array (String × String) := #[]
    for (name, _, action) in allSuites do
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
    IO.println s!"TEST_SUMMARY: passed={passed} skipped={skipped.size} failed={failed.size}"
    for (name, reason) in skipped do
      IO.println s!"SKIPPED_SUITE: {name} | {reason}"
    for (name, msg) in failed do
      IO.eprintln s!"FAILED_SUITE: {name} | {msg}"
    writeStepSummary passed skipped failed
    if !failed.isEmpty then
      return 1
    if skipped.isEmpty then
      IO.println "ALL_LEAN_SWE_TESTS_PASSED"
    else
      IO.println "LEAN_SWE_TESTS_PASSED_WITH_SKIPS"
    return 0

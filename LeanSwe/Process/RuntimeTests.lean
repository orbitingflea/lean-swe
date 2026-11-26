import Core.Assumptions
import Core.ConcOps
import LeanSwe.Process.Interface
import LeanSwe.Process.RuntimeTests.LiveProbes

namespace LeanSwe.Process.RuntimeTests

open LeanSwe.Process

private def withTempNonExecFile (k : System.FilePath → IO Unit) : IO Unit := do
  let tmpDir ← IO.FS.createTempDir
  try
    let noexec := tmpDir / "noexec_bin"
    IO.FS.writeFile noexec "#!/bin/sh\necho hi\n"
    let _ ← assertOk (← Process.runChecked { program := "/usr/bin/chmod", args := #["0644", noexec.toString] })
      "chmod 0644"
    k noexec
  finally
    IO.FS.removeDirAll tmpDir

private def withTempRegularFile (k : System.FilePath → IO Unit) : IO Unit := do
  let tmpDir ← IO.FS.createTempDir
  try
    let reg := tmpDir / "regular_file"
    IO.FS.writeFile reg "not a directory\n"
    k reg
  finally
    IO.FS.removeDirAll tmpDir

/-- Real error-forcing test: `validateRequest` rejects malformed requests with `.invalidInput`. -/
def err_process_validateRequest_invalidInput : IO Unit := do
  assertErrKind (Process.validateRequest { program := "" }) .invalidInput "validate empty program"
  assertErrKind (Process.validateRequest { program := "echo\x00x" }) .invalidInput "validate nul program"
  assertErrKind (Process.validateRequest { program := "echo", args := #["a\x00b"] }) .invalidInput "validate nul arg"
  assertErrKind (Process.validateRequest { program := "echo", cwd := some "a\x00b" }) .invalidInput "validate nul cwd"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("", some "1")] }) .invalidInput "validate empty env key"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("A=B", some "1")] }) .invalidInput "validate equals env key"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("A", some "x\x00y")] }) .invalidInput "validate nul env value"
  assertErrKind (Process.validateRequest { program := "echo", timeoutMs := some 0 }) .invalidInput "validate zero timeoutMs"

/-- Real error-forcing test: `run` returns `.notFound` on a missing executable. -/
def err_process_run_notFound : IO Unit := do
  assertErrKind (← Process.run { program := "leanswe_missing_binary_88888" }) .notFound "run notFound"

/-- Real error-forcing test: `run` returns `.permissionDenied` on a non-executable regular file. -/
def err_process_run_permissionDenied : IO Unit :=
  withTempNonExecFile fun p => do
    assertErrKind (← Process.run { program := p.toString }) .permissionDenied "run permissionDenied"

/-- Real error-forcing test: `run` returns `.invalidInput` on an empty program request. -/
def err_process_run_invalidInput : IO Unit := do
  assertErrKind (← Process.run { program := "" }) .invalidInput "run invalidInput empty"
  assertErrKind (← Process.run { program := "echo", timeoutMs := some 0 }) .invalidInput "run invalidInput zero timeout"

/-- Real error-forcing test: `run` returns `.timedOut` when a child outlives `timeoutMs`. -/
def err_process_run_timedOut : IO Unit := do
  assertErrKind (← Process.run { program := "sh", args := #["-c", "sleep 10"], timeoutMs := some 80 })
    .timedOut "run timedOut"

/-- Real error-forcing test: `run` returns `.outputLimitExceeded` when output exceeds `maxOutputBytes`. -/
def err_process_run_outputLimitExceeded : IO Unit := do
  assertErrKind (← Process.run { program := "printf", args := #["12345678901234567890"], maxOutputBytes := some 4 })
    .outputLimitExceeded "run outputLimitExceeded"

/-- Real error-forcing test: `run` returns `.terminatedBySignal` when a child dies from `SIGTERM`. -/
def err_process_run_terminatedBySignal : IO Unit := do
  assertErrKind (← Process.run { program := "sh", args := #["-c", "kill -TERM $$"] })
    .terminatedBySignal "run terminatedBySignal"

/-- Real error-forcing test: `run` returns `.ioError` (`ENOTDIR`) when `cwd` is a regular file. -/
def err_process_run_ioError : IO Unit :=
  withTempRegularFile fun reg => do
    assertErrKind (← Process.run { program := "true", cwd := some reg.toString }) .ioError "run ioError ENOTDIR"

/-- Real error-forcing test: `runChecked` returns `.notFound` on a missing executable. -/
def err_process_runChecked_notFound : IO Unit := do
  assertErrKind (← Process.runChecked { program := "leanswe_missing_binary_88888" }) .notFound "runChecked notFound"

/-- Real error-forcing test: `runChecked` returns `.permissionDenied` on a non-executable regular file. -/
def err_process_runChecked_permissionDenied : IO Unit :=
  withTempNonExecFile fun p => do
    assertErrKind (← Process.runChecked { program := p.toString }) .permissionDenied "runChecked permissionDenied"

/-- Real error-forcing test: `runChecked` returns `.invalidInput` on an empty program request. -/
def err_process_runChecked_invalidInput : IO Unit := do
  assertErrKind (← Process.runChecked { program := "" }) .invalidInput "runChecked invalidInput"

/-- Real error-forcing test: `runChecked` returns `.timedOut` when a child outlives `timeoutMs`. -/
def err_process_runChecked_timedOut : IO Unit := do
  assertErrKind (← Process.runChecked { program := "sh", args := #["-c", "sleep 10"], timeoutMs := some 80 })
    .timedOut "runChecked timedOut"

/-- Real error-forcing test: `runChecked` returns `.outputLimitExceeded` when output exceeds `maxOutputBytes`. -/
def err_process_runChecked_outputLimitExceeded : IO Unit := do
  assertErrKind (← Process.runChecked { program := "printf", args := #["12345678901234567890"], maxOutputBytes := some 4 })
    .outputLimitExceeded "runChecked outputLimitExceeded"

/-- Real error-forcing test: `runChecked` returns `.terminatedBySignal` when a child dies from `SIGTERM`. -/
def err_process_runChecked_terminatedBySignal : IO Unit := do
  assertErrKind (← Process.runChecked { program := "sh", args := #["-c", "kill -TERM $$"] })
    .terminatedBySignal "runChecked terminatedBySignal"

/-- Real error-forcing test: `runChecked` returns `.nonZeroExit` on a non-zero exit status. -/
def err_process_runChecked_nonZeroExit : IO Unit := do
  assertErrKind (← Process.runChecked { program := "sh", args := #["-c", "exit 7"] })
    .nonZeroExit "runChecked nonZeroExit"

/-- Real error-forcing test: `runChecked` returns `.ioError` (`ENOTDIR`) when `cwd` is a regular file. -/
def err_process_runChecked_ioError : IO Unit :=
  withTempRegularFile fun reg => do
    assertErrKind (← Process.runChecked { program := "true", cwd := some reg.toString }) .ioError "runChecked ioError ENOTDIR"

/-- Real error-forcing test: `runCommand` returns `.notFound` on a missing executable. -/
def err_process_runCommand_notFound : IO Unit := do
  assertErrKind (← Process.runCommand "leanswe_missing_binary_88888" #[]) .notFound "runCommand notFound"

/-- Real error-forcing test: `runCommand` returns `.permissionDenied` on a non-executable regular file. -/
def err_process_runCommand_permissionDenied : IO Unit :=
  withTempNonExecFile fun p => do
    assertErrKind (← Process.runCommand p.toString #[]) .permissionDenied "runCommand permissionDenied"

/-- Real error-forcing test: `runCommand` returns `.invalidInput` on an empty program name. -/
def err_process_runCommand_invalidInput : IO Unit := do
  assertErrKind (← Process.runCommand "" #[]) .invalidInput "runCommand invalidInput"

/-- Real error-forcing test: `runCommand` returns `.terminatedBySignal` when a child dies from `SIGTERM`. -/
def err_process_runCommand_terminatedBySignal : IO Unit := do
  assertErrKind (← Process.runCommand "sh" #["-c", "kill -TERM $$"])
    .terminatedBySignal "runCommand terminatedBySignal"

/-- Real error-forcing test: `runCommand` returns `.ioError` (`ENOTDIR`) when executing through a non-directory path component. -/
def err_process_runCommand_ioError : IO Unit :=
  withTempRegularFile fun reg => do
    assertErrKind (← Process.runCommand s!"{reg}/bin" #[]) .ioError "runCommand ioError ENOTDIR"

/-- Real error-forcing test: `runCommandChecked` returns `.notFound` on a missing executable. -/
def err_process_runCommandChecked_notFound : IO Unit := do
  assertErrKind (← Process.runCommandChecked "leanswe_missing_binary_88888" #[]) .notFound "runCommandChecked notFound"

/-- Real error-forcing test: `runCommandChecked` returns `.permissionDenied` on a non-executable regular file. -/
def err_process_runCommandChecked_permissionDenied : IO Unit :=
  withTempNonExecFile fun p => do
    assertErrKind (← Process.runCommandChecked p.toString #[]) .permissionDenied "runCommandChecked permissionDenied"

/-- Real error-forcing test: `runCommandChecked` returns `.invalidInput` on an empty program name. -/
def err_process_runCommandChecked_invalidInput : IO Unit := do
  assertErrKind (← Process.runCommandChecked "" #[]) .invalidInput "runCommandChecked invalidInput"

/-- Real error-forcing test: `runCommandChecked` returns `.terminatedBySignal` when a child dies from `SIGTERM`. -/
def err_process_runCommandChecked_terminatedBySignal : IO Unit := do
  assertErrKind (← Process.runCommandChecked "sh" #["-c", "kill -TERM $$"])
    .terminatedBySignal "runCommandChecked terminatedBySignal"

/-- Real error-forcing test: `runCommandChecked` returns `.nonZeroExit` on a non-zero exit status. -/
def err_process_runCommandChecked_nonZeroExit : IO Unit := do
  assertErrKind (← Process.runCommandChecked "sh" #["-c", "exit 7"])
    .nonZeroExit "runCommandChecked nonZeroExit"

/-- Real error-forcing test: `runCommandChecked` returns `.ioError` (`ENOTDIR`) when executing through a non-directory path component. -/
def err_process_runCommandChecked_ioError : IO Unit :=
  withTempRegularFile fun reg => do
    assertErrKind (← Process.runCommandChecked s!"{reg}/bin" #[]) .ioError "runCommandChecked ioError ENOTDIR"

private def mkMockLifecycleErrApi (eno : LinuxSyscall.Errno) : IO ProcessApi := do
  let slot : Internal.ProcSlotM LinuxSyscall.RawFd :=
    { pid := 42, pgid := 42, stdinFd? := none, stdoutFd? := none, stderrFd? := none, waited := false }
  let ref ← IO.mkRef ({ nextId := 2, slots := [(1, slot)] } : Internal.ProcTableState LinuxSyscall.RawFd)
  let sys : Internal.ProcessSysCapsM IO :=
    { proc :=
        { LinuxSyscall.Process.defaultOps with
          kill := fun _ _ => pure (.error eno)
          waitpid := fun _ _ => pure (.error eno) }
      files := LinuxSyscall.Files.defaultOps
      poll := LinuxSyscall.Poll.defaultOps
      timeRand := LinuxSyscall.TimeRand.defaultOps
      postFork := PostFork.defaultOps
      envRaw := LeanSwe.EnvVars.Raw.defaultOpsBase }
  return Internal.mkFullApiM sys Core.ioConcOps (Core.ioStateCell ref)

/-- Real error-forcing test: `spawn` returns `.notFound` on a missing executable. -/
def err_process_spawn_notFound : IO Unit := do
  assertErrKind (← Process.spawn { program := "leanswe_missing_binary_88888" }) .notFound "spawn notFound"

/-- Real error-forcing test: `spawn` returns `.permissionDenied` on a non-executable regular file. -/
def err_process_spawn_permissionDenied : IO Unit :=
  withTempNonExecFile fun p => do
    assertErrKind (← Process.spawn { program := p.toString }) .permissionDenied "spawn permissionDenied"

/-- Real error-forcing test: `spawn` validates requests and returns `.invalidInput` without spawning. -/
def err_process_spawn_invalidInput : IO Unit := do
  assertErrKind (← Process.spawn { program := "" }) .invalidInput "spawn invalidInput empty"
  assertErrKind (← Process.spawn { program := "echo", env := #[("BAD=KEY", some "1")] }) .invalidInput "spawn invalidInput bad env"

/-- Real error-forcing test: `spawn` returns `.ioError` (`ENOTDIR`) when `cwd` is a regular file. -/
def err_process_spawn_ioError : IO Unit :=
  withTempRegularFile fun reg => do
    assertErrKind (← Process.spawn { program := "true", cwd := some reg.toString }) .ioError "spawn ioError ENOTDIR"

/-- Mocked error-forcing test: `awaitOutput` maps underlying `ENOENT` to `.notFound`. -/
def err_process_awaitOutput_notFound : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.ENOENT
  assertErrKind (← api.awaitOutput { handleId := 1, pid := 42, pgid := 42 } ByteArray.empty none none) .notFound "awaitOutput notFound"

/-- Mocked error-forcing test: `awaitOutput` maps underlying `EPERM` to `.permissionDenied`. -/
def err_process_awaitOutput_permissionDenied : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EPERM
  assertErrKind (← api.awaitOutput { handleId := 1, pid := 42, pgid := 42 } ByteArray.empty none none) .permissionDenied "awaitOutput permissionDenied"

/-- Real error-forcing test: `awaitOutput` rejects `timeoutMs = some 0` with `.invalidInput`. -/
def err_process_awaitOutput_invalidInput : IO Unit := do
  assertErrKind (← Process.awaitOutput { handleId := 999999, pid := 1, pgid := 1 } ByteArray.empty (some 0) none)
    .invalidInput "awaitOutput invalidInput zero timeout"

/-- Real error-forcing test: `awaitOutput` rejects an unknown handle with `.ioError`. -/
def err_process_awaitOutput_ioError : IO Unit := do
  assertErrKind (← Process.awaitOutput { handleId := 999999, pid := 1, pgid := 1 }) .ioError "awaitOutput invalid handle"

/-- Mocked error-forcing test: `killProcessGroup` maps underlying `ENOENT` to `.notFound`. -/
def err_process_killProcessGroup_notFound : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.ENOENT
  assertErrKind (← api.killProcessGroup { handleId := 1, pid := 42, pgid := 42 }) .notFound "killProcessGroup notFound"

/-- Mocked error-forcing test: `killProcessGroup` maps underlying `EPERM` to `.permissionDenied`. -/
def err_process_killProcessGroup_permissionDenied : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EPERM
  assertErrKind (← api.killProcessGroup { handleId := 1, pid := 42, pgid := 42 }) .permissionDenied "killProcessGroup permissionDenied"

/-- Mocked error-forcing test: `killProcessGroup` maps underlying `EINVAL` to `.invalidInput`. -/
def err_process_killProcessGroup_invalidInput : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EINVAL
  assertErrKind (← api.killProcessGroup { handleId := 1, pid := 42, pgid := 42 }) .invalidInput "killProcessGroup invalidInput"

/-- Mocked error-forcing test: `killProcessGroup` maps underlying `EIO` to `.ioError`. -/
def err_process_killProcessGroup_ioError : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EIO
  assertErrKind (← api.killProcessGroup { handleId := 1, pid := 42, pgid := 42 }) .ioError "killProcessGroup ioError"

/-- Mocked error-forcing test: `reap` maps underlying `ENOENT` to `.notFound`. -/
def err_process_reap_notFound : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.ENOENT
  assertErrKind (← api.reap { handleId := 1, pid := 42, pgid := 42 }) .notFound "reap notFound"

/-- Mocked error-forcing test: `reap` maps underlying `EPERM` to `.permissionDenied`. -/
def err_process_reap_permissionDenied : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EPERM
  assertErrKind (← api.reap { handleId := 1, pid := 42, pgid := 42 }) .permissionDenied "reap permissionDenied"

/-- Mocked error-forcing test: `reap` maps underlying `EINVAL` to `.invalidInput`. -/
def err_process_reap_invalidInput : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EINVAL
  assertErrKind (← api.reap { handleId := 1, pid := 42, pgid := 42 }) .invalidInput "reap invalidInput"

/-- Mocked error-forcing test: `reap` maps underlying `EIO` to `.ioError`. -/
def err_process_reap_ioError : IO Unit := do
  let api ← mkMockLifecycleErrApi LinuxSyscall.Errno.EIO
  assertErrKind (← api.reap { handleId := 1, pid := 42, pgid := 42 }) .ioError "reap ioError"

/-- Registered runtime error-forcing tests paired 1-to-1 with `LeanSwe.Process.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Process.RuntimeTests.err_process_validateRequest_invalidInput"
       mode := .real
       run := err_process_validateRequest_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_notFound"
       mode := .real
       run := err_process_run_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_permissionDenied"
       mode := .real
       run := err_process_run_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_invalidInput"
       mode := .real
       run := err_process_run_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_timedOut"
       mode := .real
       run := err_process_run_timedOut }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_outputLimitExceeded"
       mode := .real
       run := err_process_run_outputLimitExceeded }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_terminatedBySignal"
       mode := .real
       run := err_process_run_terminatedBySignal }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_run_ioError"
       mode := .real
       run := err_process_run_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_notFound"
       mode := .real
       run := err_process_runChecked_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_permissionDenied"
       mode := .real
       run := err_process_runChecked_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_invalidInput"
       mode := .real
       run := err_process_runChecked_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_timedOut"
       mode := .real
       run := err_process_runChecked_timedOut }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_outputLimitExceeded"
       mode := .real
       run := err_process_runChecked_outputLimitExceeded }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_terminatedBySignal"
       mode := .real
       run := err_process_runChecked_terminatedBySignal }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_nonZeroExit"
       mode := .real
       run := err_process_runChecked_nonZeroExit }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runChecked_ioError"
       mode := .real
       run := err_process_runChecked_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommand_notFound"
       mode := .real
       run := err_process_runCommand_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommand_permissionDenied"
       mode := .real
       run := err_process_runCommand_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommand_invalidInput"
       mode := .real
       run := err_process_runCommand_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommand_terminatedBySignal"
       mode := .real
       run := err_process_runCommand_terminatedBySignal }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommand_ioError"
       mode := .real
       run := err_process_runCommand_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_notFound"
       mode := .real
       run := err_process_runCommandChecked_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_permissionDenied"
       mode := .real
       run := err_process_runCommandChecked_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_invalidInput"
       mode := .real
       run := err_process_runCommandChecked_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_terminatedBySignal"
       mode := .real
       run := err_process_runCommandChecked_terminatedBySignal }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_nonZeroExit"
       mode := .real
       run := err_process_runCommandChecked_nonZeroExit }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_ioError"
       mode := .real
       run := err_process_runCommandChecked_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_spawn_notFound"
       mode := .real
       run := err_process_spawn_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_spawn_permissionDenied"
       mode := .real
       run := err_process_spawn_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_spawn_invalidInput"
       mode := .real
       run := err_process_spawn_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_spawn_ioError"
       mode := .real
       run := err_process_spawn_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_notFound"
       mode := .mocked
       run := err_process_awaitOutput_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_permissionDenied"
       mode := .mocked
       run := err_process_awaitOutput_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_invalidInput"
       mode := .real
       run := err_process_awaitOutput_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_ioError"
       mode := .real
       run := err_process_awaitOutput_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_notFound"
       mode := .mocked
       run := err_process_killProcessGroup_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_permissionDenied"
       mode := .mocked
       run := err_process_killProcessGroup_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_invalidInput"
       mode := .mocked
       run := err_process_killProcessGroup_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_ioError"
       mode := .mocked
       run := err_process_killProcessGroup_ioError }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_reap_notFound"
       mode := .mocked
       run := err_process_reap_notFound }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_reap_permissionDenied"
       mode := .mocked
       run := err_process_reap_permissionDenied }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_reap_invalidInput"
       mode := .mocked
       run := err_process_reap_invalidInput }
   , { testName := "LeanSwe.Process.RuntimeTests.err_process_reap_ioError"
       mode := .mocked
       run := err_process_reap_ioError } ]

/-- Execute end-to-end OS runtime verification tests for `LeanSwe.Process`. -/
def runAll : IO Unit := do
  assertTrue ((← Process.activeProcessCount) == 0) "initial Process.activeProcessCount == 0"
  Core.runRegisteredErrorTests registeredErrorTests
  testPartialDrainTimeoutPreservesChunks
  testLiveTimeoutPreservesPriorOutput
  testIsPidDeadChecks
  testBackgroundChildLifecycle
  runLiveIntegrationSuite
  IO.println "PASS: LeanSwe.Process runtime tests"

/-- Auxiliary child-process entry point invoked via `--process-probe` inside runtime tests. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["nonutf8-env", errPath] => runNonUtf8ProbeChild errPath
  | _ => return 2

end LeanSwe.Process.RuntimeTests

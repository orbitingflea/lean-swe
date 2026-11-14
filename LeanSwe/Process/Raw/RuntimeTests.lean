import LeanSwe.Process.Raw.Interface

namespace LeanSwe.Process.Raw.RuntimeTests

open LeanSwe.Process.Raw

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except ProcessError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except ProcessError α) (expected : ProcessErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def runRawSimple (req : ExecRequest) : IO (Except ProcessError ExecOutcome) := do
  match ← Raw.spawn req with
  | .error e => return .error e
  | .ok h =>
    try
      let res ← Raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes
      match res with
      | .ok (.exited _) =>
        let _ ← Raw.reap h
        return res
      | .ok _ =>
        let _ ← Raw.killProcessGroup h
        let _ ← Raw.reap h
        return res
      | .error _ =>
        let _ ← Raw.killProcessGroup h
        let _ ← Raw.reap h
        return res
    catch err =>
      let _ ← Raw.killProcessGroup h
      let _ ← Raw.reap h
      throw err

private def isPidDead (pidStr : String) : IO Bool := do
  for _ in List.range 30 do
    let res ← runRawSimple { program := "/usr/bin/kill", args := #["-0", pidStr] }
    match res with
    | .ok (.exited out) =>
      if out.exitCode != 0 then
        return true
    | _ => return true
    IO.sleep 15
  return false

private def waitPidFileNonEmpty (pidFile : System.FilePath) : IO String := do
  for _ in List.range 50 do
    if ← pidFile.pathExists then
      let raw := (← IO.FS.readFile pidFile).trimAscii.toString
      if raw != "" then
        return raw
    IO.sleep 10
  return ""

/-- Execute OS-level runtime verification tests for `LeanSwe.Process.Raw`. -/
def runAll : IO Unit := do
  let baseCount ← Raw.activeProcessCount
  assertTrue (baseCount == 0) "initial raw activeProcessCount == 0"

  let tmpDir ← IO.FS.createTempDir
  try
    let direct ← assertOk (← runRawSimple {
      program := "printf"
      args := #["%s|%s", "a; echo pwn", "$(id) 'q' \"x\""]
    }) "raw execvp direct args"
    match direct with
    | .exited r =>
      assertTrue (r.exitCode == 0) "raw direct args exit 0"
      assertTrue (String.fromUTF8! r.stdout == "a; echo pwn|$(id) 'q' \"x\"")
        "raw direct args unexpanded"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")
    assertTrue ((← Raw.activeProcessCount) == 0) "active count after direct args"

    let realTmp ← IO.FS.realPath tmpDir
    let cwdOut ← assertOk (← runRawSimple {
      program := "pwd"
      cwd := some tmpDir.toString
    }) "raw cwd"
    match cwdOut with
    | .exited r =>
      assertTrue (r.exitCode == 0) "raw cwd exit 0"
      assertTrue ((String.fromUTF8! r.stdout).trimAscii.toString == realTmp.toString) "raw cwd matches"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")

    let envInherit ← assertOk (← runRawSimple {
      program := "sh"
      args := #["-c", "printf '%s|%s' \"${LEANSWE_RAW_SET:-missing}\" \"${PATH:+has_path}\""]
      env := #[("LEANSWE_RAW_SET", some "alpha")]
      inheritEnv := true
    }) "raw inheritEnv true"
    match envInherit with
    | .exited r =>
      assertTrue (r.exitCode == 0 && String.fromUTF8! r.stdout == "alpha|has_path")
        "raw inheritEnv true output"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")

    let envIsolated ← assertOk (← runRawSimple {
      program := "/usr/bin/env"
      env := #[("ONLY_KEY", some "only_val")]
      inheritEnv := false
    }) "raw inheritEnv false"
    match envIsolated with
    | .exited r =>
      assertTrue (r.exitCode == 0 && (String.fromUTF8! r.stdout).trimAscii.toString == "ONLY_KEY=only_val")
        "raw inheritEnv false output"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")

    let ioRes ← assertOk (← runRawSimple {
      program := "sh"
      args := #["-c", "cat; echo err_line >&2; exit 7"]
      stdin := "in_line\n".toUTF8
    }) "raw stdin/stdout/stderr/exit"
    match ioRes with
    | .exited r =>
      assertTrue (r.exitCode == 7) "raw non-zero exit code"
      assertTrue (String.fromUTF8! r.stdout == "in_line\n") "raw stdout stdin echo"
      assertTrue (String.fromUTF8! r.stderr == "err_line\n") "raw stderr capture"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")

    assertErrKind (← runRawSimple { program := "" }) .invalidInput "raw empty program"
    assertErrKind (← runRawSimple { program := "leanswe_missing_binary_99999" }) .notFound
      "raw missing binary"

    let noexec := tmpDir / "noexec_script"
    IO.FS.writeFile noexec "#!/bin/sh\necho hi\n"
    let _ ← runRawSimple { program := "/usr/bin/chmod", args := #["0644", noexec.toString] }
    assertErrKind (← runRawSimple { program := noexec.toString }) .permissionDenied
      "raw non-executable permissionDenied"

    let hActive ← assertOk (← Raw.spawn { program := "/usr/bin/sleep", args := #["60"] })
      "raw spawn active handle"
    assertTrue (hActive.pid > 0 && hActive.pgid > 0) "raw active handle positive pid/pgid"
    assertTrue ((← Raw.activeProcessCount) == 1) "raw activeProcessCount == 1 while running"
    assertOk (← Raw.killProcessGroup hActive) "raw killProcessGroup active handle"
    assertOk (← Raw.reap hActive) "raw reap after killProcessGroup"
    assertTrue ((← Raw.activeProcessCount) == 0) "raw activeProcessCount == 0 after kill+reap"
    assertTrue (← isPidDead (toString hActive.pid)) "raw killed process is dead"

    let pidFile := tmpDir / "grandchild.pid"
    let hTimeout ← assertOk (← Raw.spawn {
      program := "sh"
      args := #["-c", "sleep 60 & echo $! > \"$1\"; wait", "sh", pidFile.toString]
    }) "raw spawn timeout pg"
    let _ ← waitPidFileNonEmpty pidFile
    let tRes ← assertOk (← Raw.awaitOutput hTimeout ByteArray.empty (some 150) none)
      "raw await timeout"
    match tRes with
    | .timedOut _ _ => pure ()
    | other => throw (IO.userError s!"ASSERTION FAILED: expected timedOut, got {repr other}")
    assertOk (← Raw.killProcessGroup hTimeout) "raw kill timeout pg"
    assertOk (← Raw.reap hTimeout) "raw reap timeout pg"
    assertTrue ((← Raw.activeProcessCount) == 0) "raw active count after timeout"
    let gpPid := (← IO.FS.readFile pidFile).trimAscii.toString
    assertTrue (gpPid != "") "raw grandchild pid recorded"
    assertTrue (← isPidDead gpPid) "raw grandchild process dead after killProcessGroup"

    let okLimit ← assertOk (← runRawSimple {
      program := "printf"
      args := #["ok"]
      maxOutputBytes := some 64
    }) "raw maxOutputBytes within limit"
    match okLimit with
    | .exited r => assertTrue (r.exitCode == 0 && String.fromUTF8! r.stdout == "ok") "raw within limit"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected exited, got {repr other}")

    let overLimit ← assertOk (← runRawSimple {
      program := "printf"
      args := #["1234567890"]
      maxOutputBytes := some 4
    }) "raw maxOutputBytes exceeded"
    match overLimit with
    | .outputLimitExceeded _ _ => pure ()
    | other => throw (IO.userError s!"ASSERTION FAILED: expected outputLimitExceeded, got {repr other}")

    let sigRes ← assertOk (← runRawSimple {
      program := "sh"
      args := #["-c", "kill -TERM $$"]
    }) "raw terminatedBySignal"
    match sigRes with
    | .signaled sig _ _ => assertTrue (sig == 15) "raw signal is SIGTERM"
    | other => throw (IO.userError s!"ASSERTION FAILED: expected signaled, got {repr other}")

    assertTrue ((← Raw.activeProcessCount) == 0) "final raw activeProcessCount == 0"
  finally
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.Process.Raw runtime tests"

end LeanSwe.Process.Raw.RuntimeTests

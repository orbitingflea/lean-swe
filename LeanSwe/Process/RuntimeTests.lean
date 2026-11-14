import LeanSwe.Process.Interface

namespace LeanSwe.Process.RuntimeTests

open LeanSwe.Process

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

private def isPidDead (pidStr : String) : IO Bool := do
  for _ in List.range 30 do
    match ← Process.runCommand "/usr/bin/kill" #["-0", pidStr] with
    | .ok r =>
      if r.exitCode != 0 then
        return true
    | .error _ => return true
    IO.sleep 15
  return false

/-- Execute end-to-end OS runtime verification tests for `LeanSwe.Process`. -/
def runAll : IO Unit := do
  assertTrue ((← Process.activeProcessCount) == 0) "initial Process.activeProcessCount == 0"

  assertErrKind (Process.validateRequest { program := "" }) .invalidInput "validate empty program"
  assertErrKind (Process.validateRequest { program := "echo\x00x" }) .invalidInput "validate nul program"
  assertErrKind (Process.validateRequest { program := "echo", args := #["a\x00b"] }) .invalidInput
    "validate nul arg"
  assertErrKind (Process.validateRequest { program := "echo", cwd := some "a\x00b" }) .invalidInput
    "validate nul cwd"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("", some "1")] }) .invalidInput
    "validate empty env key"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("A=B", some "1")] }) .invalidInput
    "validate equals in env key"
  assertErrKind (Process.validateRequest { program := "echo", env := #[("A", some "x\x00y")] }) .invalidInput
    "validate nul env value"
  assertErrKind (Process.validateRequest { program := "echo", timeoutMs := some 0 }) .invalidInput
    "validate zero timeoutMs"

  let tmpDir ← IO.FS.createTempDir
  try
    let direct ← assertOk (← Process.runCommand "printf" #["%s|%s", "x; id", "$(uname) 'a' \"b\""])
      "runCommand execvp direct args"
    assertTrue (direct.exitCode == 0 && String.fromUTF8! direct.stdout == "x; id|$(uname) 'a' \"b\"")
      "runCommand metacharacters unexpanded"

    let checkedOk ← assertOk (← Process.runCommandChecked "printf" #["ok"]) "runCommandChecked zero"
    assertTrue (checkedOk.exitCode == 0 && String.fromUTF8! checkedOk.stdout == "ok")
      "runCommandChecked stdout"

    let reqText := Process.withTextInput (Process.mkCommandRequest "cat" #[]) "utf8-input-\nline2"
    let textRes ← assertOk (← Process.runChecked reqText) "withTextInput roundtrip"
    assertTrue (String.fromUTF8! textRes.stdout == "utf8-input-\nline2") "withTextInput stdout"

    let nzReq : ExecRequest := {
      program := "sh"
      args := #["-c", "echo out_msg; echo err_msg >&2; exit 9"]
    }
    let nzOut ← assertOk (← Process.run nzReq) "run allows non-zero exit"
    assertTrue (nzOut.exitCode == 9 &&
      String.fromUTF8! nzOut.stdout == "out_msg\n" &&
      String.fromUTF8! nzOut.stderr == "err_msg\n") "run non-zero preserves exitCode/stdout/stderr"

    match ← Process.runChecked nzReq with
    | .ok _ => throw (IO.userError "ASSERTION FAILED: runChecked should fail on non-zero exit")
    | .error err =>
      assertTrue (err.kind == .nonZeroExit &&
        err.exitCode == some 9 &&
        err.program == some "sh" &&
        err.stdout == some "out_msg\n".toUTF8 &&
        err.stderr == some "err_msg\n".toUTF8 &&
        err.message != "") "runChecked nonZeroExit fields"

    let realTmp ← IO.FS.realPath tmpDir
    let cwdRes ← assertOk (← Process.runChecked { program := "pwd", cwd := some tmpDir.toString }) "cwd"
    assertTrue ((String.fromUTF8! cwdRes.stdout).trimAscii.toString == realTmp.toString) "cwd realPath"

    let dupEnvRes ← assertOk (← Process.runChecked {
      program := "sh"
      args := #["-c", "printf '%s|%s' \"${LEANSWE_DUP:-missing}\" \"${LEANSWE_DROP:-unset}\""]
      env := #[
        ("LEANSWE_DUP", some "first"),
        ("LEANSWE_DUP", some "second"),
        ("LEANSWE_DROP", some "gone"),
        ("LEANSWE_DROP", none)
      ]
      inheritEnv := true
    }) "env dedup and unset"
    assertTrue (String.fromUTF8! dupEnvRes.stdout == "second|unset") "env last-wins and unset"

    let isoEnvRes ← assertOk (← Process.runChecked {
      program := "/usr/bin/env"
      env := #[("ISOLATED_VAR", some "123")]
      inheritEnv := false
    }) "inheritEnv false"
    assertTrue ((String.fromUTF8! isoEnvRes.stdout).trimAscii.toString == "ISOLATED_VAR=123")
      "inheritEnv false excludes parent env"

    assertErrKind (← Process.run { program := "leanswe_missing_binary_88888" }) .notFound
      "Process.run notFound"

    let noexec := tmpDir / "noexec_bin"
    IO.FS.writeFile noexec "#!/bin/sh\necho hi\n"
    let _ ← assertOk (← Process.runChecked { program := "/usr/bin/chmod", args := #["0644", noexec.toString] })
      "chmod 0644"
    assertErrKind (← Process.run { program := noexec.toString }) .permissionDenied
      "Process.run permissionDenied"

    let pidFile := tmpDir / "pg_grandchild.pid"
    let toRes ← Process.run {
      program := "sh"
      args := #["-c", "sleep 60 & echo $! > \"$1\"; wait", "sh", pidFile.toString]
      timeoutMs := some 350
    }
    assertErrKind toRes .timedOut "Process.run timedOut"
    assertTrue ((← Process.activeProcessCount) == 0) "activeProcessCount == 0 after timeout"
    let pidExists ← pidFile.pathExists
    let gpPid ← if pidExists then pure (← IO.FS.readFile pidFile).trimAscii.toString else pure ""
    assertTrue (gpPid != "") "Process.run timeout grandchild pid written"
    assertTrue (← isPidDead gpPid) "Process.run timeout killed grandchild in process group"

    let streamToRes ← Process.run {
      program := "sh"
      args := #["-c", "while :; do printf 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'; done"]
      timeoutMs := some 80
      maxOutputBytes := none
    }
    assertErrKind streamToRes .timedOut "Process.run continuous stdout respects timeoutMs"
    assertTrue ((← Process.activeProcessCount) == 0) "activeProcessCount == 0 after streaming timeout"

    let closedPipeToRes ← Process.run {
      program := "sh"
      args := #["-c", "exec 1>&- 2>&-; sleep 10"]
      timeoutMs := some 120
    }
    assertErrKind closedPipeToRes .timedOut "Process.run closed stdio respects timeoutMs"
    assertTrue ((← Process.activeProcessCount) == 0) "activeProcessCount == 0 after closed-pipe timeout"

    let olRes ← Process.run {
      program := "printf"
      args := #["12345678901234567890"]
      maxOutputBytes := some 4
    }
    assertErrKind olRes .outputLimitExceeded "Process.run outputLimitExceeded"

    match ← Process.run { program := "sh", args := #["-c", "kill -TERM $$"] } with
    | .ok _ => throw (IO.userError "ASSERTION FAILED: signaled process should error")
    | .error err =>
      assertTrue (err.kind == .terminatedBySignal && err.signal == some 15 && err.message != "")
        "Process.run terminatedBySignal SIGTERM"

    assertTrue ((← Process.activeProcessCount) == 0) "final Process.activeProcessCount == 0"
  finally
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.Process runtime tests"

end LeanSwe.Process.RuntimeTests

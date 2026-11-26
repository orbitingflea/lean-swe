import Core.Assumptions
import LeanSwe.Process.Interface

/-!
Live OS integration, timeout/streaming, PID-liveness, and raw non-UTF-8 `environ(7)`
runtime verification probes for `LeanSwe.Process.RuntimeTests`.
-/

namespace LeanSwe.Process.RuntimeTests

open LeanSwe.Process

/-- Assert that `cond` is `true`, throwing `IO.userError` with `msg` otherwise. -/
def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

/-- Unwrap `.ok v` or throw `IO.userError` with `msg`. -/
def assertOk {α : Type} (res : Except ProcessError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

/-- Assert that `res` is `.error e` with `e.kind == expected` and non-empty `e.message`. -/
def assertErrKind {α : Type} (res : Except ProcessError α) (expected : ProcessErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

/-- Assert that `action` throws an `IO.Error`. -/
def assertThrows {α : Type} (action : IO α) (msg : String) : IO Unit := do
  let threw ← try
    let _ ← action
    pure false
  catch _ =>
    pure true
  assertTrue threw msg

private def parsePositivePid (pidStr : String) : IO Int32 := do
  match pidStr.toNat? with
  | none =>
    throw (IO.userError s!"ASSERTION FAILED: invalid PID string '{pidStr}'")
  | some n =>
    if n == 0 || n > LinuxSyscall.Process.MAX_LINUX_PID.toNat then
      throw (IO.userError s!"ASSERTION FAILED: PID out of valid positive range: '{pidStr}'")
    return (UInt32.ofNat n).toInt32

private def isPidDeadWith
    (killFn : Int32 → LinuxSyscall.Process.Signal → IO (Except LinuxSyscall.Errno Unit))
    (attempts : Nat) (sleepMs : UInt32) (pidStr : String) : IO Bool := do
  let pid ← parsePositivePid pidStr
  for i in List.range attempts do
    match ← killFn pid .sigzero with
    | .ok () => pure ()
    | .error e =>
      if e == LinuxSyscall.Errno.ESRCH then
        return true
      else if e == LinuxSyscall.Errno.EPERM then
        pure ()
      else
        throw (IO.userError
          s!"ASSERTION FAILED: kill({pid}, 0) failed unexpectedly with {LinuxSyscall.Errno.name e} ({e})")
    if i + 1 < attempts && sleepMs > 0 then
      IO.sleep sleepMs
  return false

private def isPidDead (pidStr : String) : IO Bool :=
  isPidDeadWith LinuxSyscall.Process.kill 30 15 pidStr

/-- Deterministic tests verifying that `streamPipesLoop` preserves chunks already read earlier in a drain round when timeout fires mid-round. -/
def testPartialDrainTimeoutPreservesChunks : IO Unit := do
  let mkMockFiles (readFn : Nat → Nat → Except LinuxSyscall.Errno ByteArray) :
      LinuxSyscall.Files.FilesOpsM (StateM (Nat × Nat)) Nat :=
    { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      close := fun _ => pure (.ok ())
      read := fun fd _ => modifyGet fun (clk, rd) => (readFn fd rd, (clk, rd + 1))
      write := fun _ data => pure (.ok (UInt32.ofNat data.size))
      fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fcntl := fun _ _ => pure (.ok 0)
      fsync := fun _ => pure (.ok ())
      getcwd := fun _ => pure (.ok "/".toUTF8)
      lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
      reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF) }
  let mockPoll : LinuxSyscall.Poll.PollOpsM (StateM (Nat × Nat)) Nat :=
    { ppoll := fun entries _ => pure (.ok (entries.map Prod.snd))
      eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
  let mkMockTime (timeoutAtTick : Nat) : LinuxSyscall.TimeRand.TimeRandOpsM (StateM (Nat × Nat)) :=
    { clock_gettime := fun _ => modifyGet fun (clk, rd) =>
        let ts : LinuxSyscall.TimeRand.Timespec :=
          if clk ≥ timeoutAtTick then { sec := 1, nsec := 0 } else { sec := 0, nsec := 0 }
        (.ok ts, (clk + 1, rd))
      clock_nanosleep := fun _ _ _ => pure (.ok ())
      getrandom := fun _ _ => pure (.ok ByteArray.empty) }
  let outFiles := mkMockFiles fun fd rd =>
    if fd == 1 then
      if rd == 0 then .ok "OUT_CHUNK_1|".toUTF8
      else if rd == 1 then .ok "OUT_CHUNK_2".toUTF8
      else .error LinuxSyscall.Errno.EAGAIN
    else .error LinuxSyscall.Errno.EAGAIN
  let outRes := (SysBridge.streamPipesLoop outFiles mockPoll (mkMockTime 3)
    ByteArray.empty 0 (some 50) none 8
    { inFd? := none, outFd? := some 1, errFd? := some 2 } 4).run (0, 0)
  match outRes.1 with
  | .ok (.timedOut out err) =>
    assertTrue (out == "OUT_CHUNK_1|OUT_CHUNK_2".toUTF8 && err == ByteArray.empty)
      s!"mid-round stdout drain timeout dropped chunks: out={String.fromUTF8! out} err={String.fromUTF8! err}"
  | .ok (.eof _ _) =>
    throw (IO.userError "ASSERTION FAILED: mid-round stdout drain expected timedOut, got eof")
  | .ok (.limitExceeded _ _) =>
    throw (IO.userError "ASSERTION FAILED: mid-round stdout drain expected timedOut, got limitExceeded")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: mid-round stdout drain expected timedOut, got error {repr e}")
  let errFiles := mkMockFiles fun fd rd =>
    if fd == 1 then
      if rd == 0 then .ok "OUT_OK".toUTF8 else .error LinuxSyscall.Errno.EAGAIN
    else if fd == 2 then
      if rd == 2 then .ok "ERR_PARTIAL".toUTF8 else .error LinuxSyscall.Errno.EAGAIN
    else .error LinuxSyscall.Errno.EAGAIN
  let errRes := (SysBridge.streamPipesLoop errFiles mockPoll (mkMockTime 4)
    ByteArray.empty 0 (some 50) none 8
    { inFd? := none, outFd? := some 1, errFd? := some 2 } 4).run (0, 0)
  match errRes.1 with
  | .ok (.timedOut out err) =>
    assertTrue (out == "OUT_OK".toUTF8 && err == "ERR_PARTIAL".toUTF8)
      s!"mid-round stderr drain timeout dropped chunks: out={String.fromUTF8! out} err={String.fromUTF8! err}"
  | .ok (.eof _ _) =>
    throw (IO.userError "ASSERTION FAILED: mid-round stderr drain expected timedOut, got eof")
  | .ok (.limitExceeded _ _) =>
    throw (IO.userError "ASSERTION FAILED: mid-round stderr drain expected timedOut, got limitExceeded")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: mid-round stderr drain expected timedOut, got error {repr e}")

/-- End-to-end live OS check verifying that `Process.run` preserves stdout and stderr emitted before a timeout. -/
def testLiveTimeoutPreservesPriorOutput : IO Unit := do
  match ← Process.run {
    program := "sh"
    args := #["-c", "printf 'PARTIAL_BEFORE_TIMEOUT_OUT'; printf 'PARTIAL_BEFORE_TIMEOUT_ERR' >&2; sleep 10"]
    timeoutMs := some 200
  } with
  | .ok r =>
    throw (IO.userError s!"ASSERTION FAILED: live timeout unexpectedly exited {r.exitCode}")
  | .error err =>
    assertTrue (err.kind == .timedOut &&
      err.stdout == some "PARTIAL_BEFORE_TIMEOUT_OUT".toUTF8 &&
      err.stderr == some "PARTIAL_BEFORE_TIMEOUT_ERR".toUTF8)
      s!"live timeout did not preserve output written prior to timeout: {repr err}"
  assertTrue ((← Process.activeProcessCount) == 0) "activeProcessCount == 0 after live timeout"

/-- Unit and live OS checks verifying `isPidDead` / `isPidDeadWith`. -/
def testIsPidDeadChecks : IO Unit := do
  let invalidPids : List String := [
    "", "not_a_pid", "0", "-1", "-42", "123abc", " 1", "1 ",
    toString (LinuxSyscall.Process.MAX_LINUX_PID.toNat + 1)
  ]
  for bad in invalidPids do
    let called ← IO.mkRef false
    assertThrows (isPidDeadWith (fun _ _ => do called.set true; return .error LinuxSyscall.Errno.ESRCH) 1 0 bad)
      s!"isPidDeadWith should reject invalid PID '{bad}'"
    assertTrue (!(← called.get)) s!"isPidDeadWith should not invoke kill on invalid PID '{bad}'"
    assertThrows (isPidDead bad) s!"isPidDead should reject invalid PID '{bad}'"

  let okCalls ← IO.mkRef (0 : Nat)
  let okDead ← isPidDeadWith (fun pid sig => do
    assertTrue (pid == (42 : Int32) && sig == .sigzero) "isPidDeadWith passes parsed pid and sigzero (.ok)"
    okCalls.modify (· + 1)
    return .ok ()) 3 0 "42"
  assertTrue (!okDead && (← okCalls.get) == 3) "isPidDeadWith treats .ok () as alive across all attempts"

  let epermCalls ← IO.mkRef (0 : Nat)
  let epermDead ← isPidDeadWith (fun pid sig => do
    assertTrue (pid == (42 : Int32) && sig == .sigzero) "isPidDeadWith passes parsed pid and sigzero (EPERM)"
    epermCalls.modify (· + 1)
    return .error LinuxSyscall.Errno.EPERM) 3 0 "42"
  assertTrue (!epermDead && (← epermCalls.get) == 3) "isPidDeadWith treats EPERM as alive across all attempts"

  let transitionCalls ← IO.mkRef (0 : Nat)
  let transitionDead ← isPidDeadWith (fun pid sig => do
    assertTrue (pid == (42 : Int32) && sig == .sigzero) "isPidDeadWith passes parsed pid and sigzero (transition)"
    let n ← transitionCalls.modifyGet fun c => (c, c + 1)
    if n == 0 then return .ok ()
    else if n == 1 then return .error LinuxSyscall.Errno.EPERM
    else return .error LinuxSyscall.Errno.ESRCH) 5 0 "42"
  assertTrue (transitionDead && (← transitionCalls.get) == 3) "isPidDeadWith returns true immediately on ESRCH"

  for unexpected in [LinuxSyscall.Errno.EINVAL, LinuxSyscall.Errno.ENOSYS, LinuxSyscall.Errno.EACCES] do
    let errCalls ← IO.mkRef (0 : Nat)
    assertThrows (isPidDeadWith (fun _ _ => do errCalls.modify (· + 1); pure (.error unexpected)) 3 0 "42")
      s!"isPidDeadWith should throw on unexpected errno {LinuxSyscall.Errno.name unexpected}"
    assertTrue ((← errCalls.get) == 1)
      s!"isPidDeadWith should fail immediately on unexpected errno {LinuxSyscall.Errno.name unexpected}"

  let selfPid ← match ← LinuxSyscall.Process.getpid with
    | .ok p => pure p
    | .error e =>
      throw (IO.userError s!"ASSERTION FAILED: getpid failed with {LinuxSyscall.Errno.name e} ({e})")
  assertTrue (!(← isPidDeadWith LinuxSyscall.Process.kill 1 0 (toString selfPid)))
    s!"isPidDeadWith should report live self PID {selfPid} as not dead"

/-- Live OS end-to-end verification of `Process.{spawn,awaitOutput,killProcessGroup,reap}` lifecycle. -/
def testBackgroundChildLifecycle : IO Unit := do
  assertTrue ((← Process.activeProcessCount) == 0) "lifecycle initial activeProcessCount == 0"
  assertErrKind (← Process.spawn { program := "" }) .invalidInput "lifecycle spawn rejects empty program"
  assertTrue ((← Process.activeProcessCount) == 0) "lifecycle invalid spawn leaves activeProcessCount == 0"

  let h1 ← assertOk (← Process.spawn {
    program := "sh"
    args := #["-c", "cat; printf '|%s' \"$LEANSWE_BG\"; echo err_line >&2"]
    env := #[("LEANSWE_BG", some "first"), ("LEANSWE_BG", some "second")]
  }) "lifecycle spawn cat"
  try
    assertTrue ((← Process.activeProcessCount) == 1) "lifecycle activeProcessCount == 1 after spawn"
    assertErrKind (← Process.awaitOutput h1 ByteArray.empty (some 0) none)
      .invalidInput "lifecycle awaitOutput rejects zero timeout without consuming handle"
    match ← Process.awaitOutput h1 "bg-stdin".toUTF8 (some 5000) none with
    | .ok (.exited res) =>
      assertTrue (res.exitCode == 0 &&
        String.fromUTF8! res.stdout == "bg-stdin|second" &&
        String.fromUTF8! res.stderr == "err_line\n") "lifecycle awaitOutput exited result"
    | .ok other => throw (IO.userError s!"ASSERTION FAILED: lifecycle expected exited, got {repr other}")
    | .error e => throw (IO.userError s!"ASSERTION FAILED: lifecycle awaitOutput failed: {repr e}")
    assertOk (← Process.reap h1) "lifecycle reap h1"
  finally
    let _ ← Process.killProcessGroup h1
    let _ ← Process.reap h1
  assertTrue ((← Process.activeProcessCount) == 0) "lifecycle activeProcessCount == 0 after h1 reap"

  let h2 ← assertOk (← Process.spawn { program := "sleep", args := #["30"] }) "lifecycle spawn sleep"
  try
    assertTrue ((← Process.activeProcessCount) == 1) "lifecycle activeProcessCount == 1 for h2"
    assertOk (← Process.killProcessGroup h2) "lifecycle killProcessGroup h2"
    assertOk (← Process.reap h2) "lifecycle reap h2"
    assertTrue (← isPidDead (toString h2.pid)) "lifecycle h2 dead after killProcessGroup + reap"
  finally
    let _ ← Process.killProcessGroup h2
    let _ ← Process.reap h2
  assertTrue ((← Process.activeProcessCount) == 0) "lifecycle final activeProcessCount == 0"

/-- Live OS end-to-end command, environment, process-group kill, `PATH`, `ppoll`, and non-UTF-8 `environ(7)` checks. -/
def runLiveIntegrationSuite : IO Unit := do
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

    match ← Process.run { program := "sh", args := #["-c", "kill -TERM $$"] } with
    | .ok _ => throw (IO.userError "ASSERTION FAILED: signaled process should error")
    | .error err =>
      assertTrue (err.kind == .terminatedBySignal && err.signal == some 15 && err.message != "")
        "Process.run terminatedBySignal SIGTERM"

    let dotScript := tmpDir / "dot_tool"
    IO.FS.writeFile dotScript "#!/bin/sh\necho PATH_DOT_OK\n"
    IO.setAccessRights dotScript
      { user := { read := true, write := true, execution := true } }
    for (lbl, pVal) in [
        ("empty", ""),
        ("leading colon", ":/nonexistent_dir_leanswe_xyz"),
        ("trailing colon", "/nonexistent_dir_leanswe_xyz:"),
        ("adjacent colons", "/nonexistent_a::/nonexistent_b")] do
      let dr ← assertOk (← Process.runChecked {
        program := "dot_tool"
        cwd := some tmpDir.toString
        env := #[("PATH", some pVal)]
        inheritEnv := false
      }) s!"empty PATH segment ({lbl})"
      assertTrue (String.fromUTF8! dr.stdout == "PATH_DOT_OK\n") s!"empty PATH segment stdout ({lbl})"

    let noShebang := tmpDir / "noshebang_tool"
    IO.FS.writeFile noShebang "echo SHOULD_NOT_EXEC\n"
    IO.setAccessRights noShebang
      { user := { read := true, write := true, execution := true } }
    for (lbl, prog) in [("direct", noShebang.toString), ("path-search", "noshebang_tool")] do
      match ← Process.run {
        program := prog
        cwd := some tmpDir.toString
        env := #[("PATH", some tmpDir.toString)]
        inheritEnv := false
      } with
      | .ok r => throw (IO.userError s!"ASSERTION FAILED: ENOEXEC ({lbl}) unexpectedly succeeded: {r.exitCode}")
      | .error err =>
        assertTrue (err.kind == .invalidInput && err.errnoCode == some LinuxSyscall.Errno.ENOEXEC)
          s!"ENOEXEC refusal without /bin/sh ({lbl}): got {repr err}"

    let bigStdin := ByteArray.mk (Array.replicate 262144 (0x41 : UInt8))
    let bigOut ← assertOk (← Process.runChecked {
      program := "cat"
      stdin := bigStdin
      timeoutMs := some 5000
    }) "ppoll 256KiB stdin roundtrip"
    assertTrue (bigOut.stdout == bigStdin) "ppoll 256KiB stdin bytes preserved"

    let slowOut ← assertOk (← Process.runChecked {
      program := "sh"
      args := #["-c", "sleep 0.05; printf out_ok; printf err_ok >&2"]
      timeoutMs := some 5000
    }) "ppoll delayed stdout/stderr"
    assertTrue (String.fromUTF8! slowOut.stdout == "out_ok" &&
      String.fromUTF8! slowOut.stderr == "err_ok") "ppoll delayed stream bytes"

    let rawBase ← LeanSwe.EnvVars.Raw.listEnvironBytes
    let rawFoo := "FOO=".toUTF8 ++ ByteArray.mk #[0x80, 0xFF]
    let rawKeep := "FOO_SIB=".toUTF8 ++ ByteArray.mk #[0xFE, 0x81]
    let rawBadKey := ByteArray.mk #[0x80, 0xFF] ++ "=rawval".toUTF8
    let rawDrop := "DROP_RAW=".toUTF8 ++ ByteArray.mk #[0xC0, 0xAF]
    let rawRepl := "REPL_RAW=".toUTF8 ++ ByteArray.mk #[0xFF]
    let rawPath := "PATH=/nonutf8_".toUTF8 ++ ByteArray.mk #[0xFF] ++ ":/bin:/usr/bin".toUTF8
    let cleanBase := rawBase.filter fun e =>
      !SysBridge.bytesHasPrefixEq "FOO".toUTF8 e &&
      !SysBridge.bytesHasPrefixEq "FOO_SIB".toUTF8 e &&
      !SysBridge.bytesHasPrefixEq "DROP_RAW".toUTF8 e &&
      !SysBridge.bytesHasPrefixEq "REPL_RAW".toUTF8 e &&
      !SysBridge.bytesHasPrefixEq "PATH".toUTF8 e
    let probeErrFile := tmpDir / "nonutf8_probe.err"
    let exePath := (← IO.appPath).toString
    let childSpec : PostFork.ChildSpec :=
      { path := exePath
        argv := #[.lit exePath, .lit "--process-probe", .lit "nonutf8-env", .lit probeErrFile.toString]
        env := #[]
        rawEnv := cleanBase ++ #[rawFoo, rawKeep, rawBadKey, rawDrop, rawRepl, rawPath]
        stdio := .inherit
        processGroup := .inherit
        sigpipe := .resetDefault
        forkMode := .direct }
    match ← PostFork.spawn childSpec with
    | .error pe => throw (IO.userError s!"ASSERTION FAILED: non-UTF-8 env probe spawn failed: {pe.message}")
    | .ok spawned =>
      let waitLoop : IO LinuxSyscall.Process.WaitResult := do
        for _ in List.range 16 do
          match ← LinuxSyscall.Process.waitpid spawned.pid.toInt32 {} with
          | .ok wr => return wr
          | .error e =>
            if e == LinuxSyscall.Errno.EINTR then pure ()
            else throw (IO.userError s!"ASSERTION FAILED: waitpid non-UTF-8 probe failed: {e}")
        throw (IO.userError "ASSERTION FAILED: waitpid EINTR retry exhausted")
      let wr ← waitLoop
      let detail ← if ← probeErrFile.pathExists then IO.FS.readFile probeErrFile else pure ""
      assertTrue (match wr with | .exited _ code => code == 0 | _ => false)
        s!"non-UTF-8 inherited environ probe failed (wr={repr wr}, detail={detail})"

    assertTrue ((← Process.activeProcessCount) == 0) "final Process.activeProcessCount == 0"
  finally
    IO.FS.removeDirAll tmpDir

private def splitNulBytesAcc (curRev : List UInt8) (accRev : List ByteArray) : List UInt8 → List ByteArray
  | [] => if curRev.isEmpty then accRev.reverse else (ByteArray.mk curRev.reverse.toArray :: accRev).reverse
  | b :: bs =>
    if b == (0 : UInt8) then
      let acc' := if curRev.isEmpty then accRev else ByteArray.mk curRev.reverse.toArray :: accRev
      splitNulBytesAcc [] acc' bs
    else
      splitNulBytesAcc (b :: curRev) accRev bs

/-- Child-process helper verifying raw non-UTF-8 `environ(7)` inheritance and override filtering. -/
def runNonUtf8ProbeChild (errPath : String) : IO UInt32 := do
  let writeFail (msg : String) : IO UInt32 := do
    IO.FS.writeFile errPath msg
    return 1
  let res ← Process.run {
    program := "/bin/cat"
    args := #["/proc/self/environ"]
    inheritEnv := true
    env := #[("DROP_RAW", none), ("REPL_RAW", some "clean"), ("NEW_VAR", some "ok")]
    timeoutMs := some 5000
  }
  match res with
  | .error e => writeFail s!"grandchild spawn failed: {repr e}"
  | .ok out =>
    if out.exitCode != 0 then
      return ← writeFail s!"grandchild exitCode={out.exitCode}"
    let entries := splitNulBytesAcc [] [] out.stdout.toList
    let wantFoo := "FOO=".toUTF8 ++ ByteArray.mk #[0x80, 0xFF]
    let wantKeep := "FOO_SIB=".toUTF8 ++ ByteArray.mk #[0xFE, 0x81]
    let wantBadKey := ByteArray.mk #[0x80, 0xFF] ++ "=rawval".toUTF8
    let badDropPrefix := "DROP_RAW".toUTF8
    let wantRepl := "REPL_RAW=clean".toUTF8
    let badReplOld := "REPL_RAW=".toUTF8 ++ ByteArray.mk #[0xFF]
    let wantNew := "NEW_VAR=ok".toUTF8
    if !entries.contains wantFoo then
      return ← writeFail "missing raw FOO=\\x80\\xff in grandchild environ"
    if !entries.contains wantKeep then
      return ← writeFail "missing sibling FOO_SIB=\\xfe\\x81 in grandchild environ"
    if !entries.contains wantBadKey then
      return ← writeFail "missing raw non-UTF-8 key \\x80\\xff=rawval in grandchild environ"
    if entries.any (SysBridge.bytesHasPrefixEq badDropPrefix) then
      return ← writeFail "DROP_RAW was not removed from grandchild environ"
    if !entries.contains wantRepl || entries.contains badReplOld then
      return ← writeFail "REPL_RAW was not replaced cleanly with REPL_RAW=clean"
    if !entries.contains wantNew then
      return ← writeFail "missing NEW_VAR=ok in grandchild environ"
    let pathRes ← Process.run {
      program := "true"
      inheritEnv := true
      timeoutMs := some 5000
    }
    match pathRes with
    | .error pe => return ← writeFail s!"PATH search with non-UTF-8 segment failed: {repr pe}"
    | .ok pr =>
      if pr.exitCode != 0 then
        return ← writeFail s!"true via non-UTF-8 PATH exited {pr.exitCode}"
    return 0

end LeanSwe.Process.RuntimeTests

import Core.Assumptions
import LeanSwe.PostFork.Interface

/-!
Runtime verification of `LeanSwe.PostFork.externalAssumptions` (`5` checks) and
`LeanSwe.PostFork.errorCoverage` (`8` `.tested` `.real` checks) using live Linux
processes via `LeanSwe.PostFork.{spawn,spawnWithBarrier,releaseBarrier,abortBarrier}`.
-/

namespace LeanSwe.PostFork.RuntimeTests

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

@[extern "leanswe_postfork_host_pipe_cloexec"]
private opaque rawMkPipeCloexec : BaseIO (Except Errno (RawFd × RawFd))

@[extern "leanswe_postfork_host_close_fd"]
private opaque rawCloseFd : @& RawFd → BaseIO (Except Errno Unit)

@[extern "leanswe_postfork_host_write_once"]
private opaque rawWriteOnce : @& RawFd → @& ByteArray → UInt64 → UInt64 → BaseIO (Except Errno UInt64)

@[extern "leanswe_postfork_host_read_once"]
private opaque rawReadOnce : @& RawFd → UInt64 → BaseIO (Except Errno ByteArray)

@[extern "leanswe_postfork_host_wait_once"]
private opaque rawWaitOnce : Pid → BaseIO (Except Errno ChildWaitStatus)

private def assertTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"PostFork.RuntimeTests: assertion failed: {label}")

private def closeQuiet (fd : RawFd) : IO Unit := do
  let _ ← rawCloseFd fd

private def mkPipeOrThrow (label : String) : IO (RawFd × RawFd) := do
  match ← rawMkPipeCloexec with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"PostFork.RuntimeTests: {label} pipe2 failed errno={e}")

private def writeAllPipe (fd : RawFd) (data : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  for _ in List.range 64 do
    if off ≥ data.size then
      return
    match ← rawWriteOnce fd data off.toUInt64 (data.size - off).toUInt64 with
    | .ok n =>
      if n == 0 then
        throw (IO.userError "PostFork.RuntimeTests: zero-byte pipe write")
      off := off + n.toNat
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"PostFork.RuntimeTests: pipe write failed errno={e}")
  throw (IO.userError "PostFork.RuntimeTests: writeAllPipe exceeded loop budget")

private def readAllPipe (fd : RawFd) : IO ByteArray := do
  let mut chunks : Array ByteArray := #[]
  for _ in List.range 128 do
    match ← rawReadOnce fd 65536 with
    | .ok chunk =>
      if chunk.size == 0 then
        return LeanSwe.PostFork.Impl.Internal.concatByteChunks chunks
      chunks := chunks.push chunk
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"PostFork.RuntimeTests: pipe read failed errno={e}")
  throw (IO.userError "PostFork.RuntimeTests: readAllPipe exceeded loop budget")

private def waitReapOrThrow (label : String) (pid : Pid) : IO ChildWaitStatus := do
  for _ in List.range 64 do
    match ← rawWaitOnce pid with
    | .ok st => return st
    | .error e =>
      if e != Errno.EINTR then
        throw (IO.userError s!"PostFork.RuntimeTests: {label} waitpid({pid}) failed errno={e}")
  throw (IO.userError s!"PostFork.RuntimeTests: {label} waitpid exceeded EINTR budget")

private def expectInvalidInput {α : Type} (label : String) (res : Except PostForkError α) : IO Unit := do
  match res with
  | .error e =>
    assertTrue s!"{label}: expected invalidInput, got {repr e}" (e.kind == .invalidInput)
  | .ok _ =>
    throw (IO.userError s!"{label}: expected invalidInput error, got ok")

private def expectSysError {α : Type} (label : String) (res : Except PostForkError α) : IO Unit := do
  match res with
  | .error e =>
    assertTrue s!"{label}: expected sysError, got {repr e}" (e.kind == .sysError)
  | .ok _ =>
    throw (IO.userError s!"{label}: expected sysError error, got ok")

private def expectChildFailed {α : Type} (label : String) (stage : FailureStage)
    (res : Except PostForkError α) : IO Unit := do
  match res with
  | .error e =>
    assertTrue s!"{label}: expected childFailed, got {repr e}" (e.kind == .childFailed)
    match e.childFailure with
    | some cf =>
      assertTrue s!"{label}: expected stage={repr stage}, got {repr cf}" (cf.stage == stage)
      assertTrue s!"{label}: expected waitStatus exited 127, got {repr cf.waitStatus}"
        (cf.waitStatus == some (.exited 127))
    | none =>
      throw (IO.userError s!"{label}: missing childFailure payload")
  | .ok _ =>
    throw (IO.userError s!"{label}: expected childFailed error, got ok")

/-- Runtime verification for `LeanSwe.PostFork.assume_postfork_stdioCycleAndCloexec`. -/
def assume_postfork_stdioCycleAndCloexec : IO Unit := do
  let (inR, inW) ← mkPipeOrThrow "stdio in"
  let (outR, outW) ← mkPipeOrThrow "stdio out"
  let (errR, errW) ← mkPipeOrThrow "stdio err"
  let (cloR, cloW) ← mkPipeOrThrow "cloexec unkept"
  try
    writeAllPipe inW "hello-stdio".toUTF8
    closeQuiet inW
    closeQuiet cloW
    let script := "in_data=$(cat); clo_ok=no; [ ! -e \"$1\" ] && clo_ok=yes; printf 'IN=%s|CLO=%s|ENV=%s|CWD=%s' \"$in_data\" \"$clo_ok\" \"$PF_VAR\" \"$(pwd)\"; >&2 printf 'ERR:%s' \"$PF_VAR\""
    let child ← match ← spawn {
      path := "/bin/sh"
      argv := #[.lit "/bin/sh", .lit "-c", .lit script, .lit "sh", ArgToken.procSelfFd cloR]
      cwd := some "/tmp"
      env := #[("PF_VAR", "v42")]
      stdio := .redirect (.handle inR) (.handle outW) (.handle errW)
      fdPolicy := .closeAllAbove2Except #[]
      processGroup := .newGroup
    } with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"stdio spawn failed: {repr e}")
    closeQuiet inR
    closeQuiet outW
    closeQuiet errW
    closeQuiet cloR
    let stdoutBytes ← readAllPipe outR
    let stderrBytes ← readAllPipe errR
    let wst ← waitReapOrThrow "stdio sh" child.pid
    assertTrue s!"stdio child pgid={repr child.pgid}" (child.pgid == some child.pid)
    assertTrue s!"stdio exit=0 got {repr wst}" (wst == .exited 0)
    assertTrue s!"stdio stdout got {String.fromUTF8! stdoutBytes}"
      (stdoutBytes == "IN=hello-stdio|CLO=yes|ENV=v42|CWD=/tmp".toUTF8)
    assertTrue s!"stdio stderr got {String.fromUTF8! stderrBytes}"
      (stderrBytes == "ERR:v42".toUTF8)

    let (swapInR, swapInW) ← mkPipeOrThrow "swap in"
    let (swapOutR, swapOutW) ← mkPipeOrThrow "swap out"
    let (swapErrR, swapErrW) ← mkPipeOrThrow "swap err"
    try
      writeAllPipe swapInW "swap-ok".toUTF8
      closeQuiet swapInW
      let srcKeepOverlap ← spawn {
        path := "/bin/true"
        argv := #[.lit "/bin/true"]
        stdio := .redirect (.handle swapInR) (.handle swapOutW) (.handle swapErrW)
        fdPolicy := .inheritNonCloexec #[.handle swapErrW]
      }
      expectChildFailed "closeSrcs keepOverlap" .validate srcKeepOverlap
      let swapChild ← match ← spawn {
        path := "/bin/sh"
        argv := #[.lit "/bin/sh", .lit "-c", .lit "d=$(cat); printf 'O:%s' \"$d\"; >&2 printf 'E:%s' \"$d\""]
        stdio := .redirect (.handle swapInR) (.handle swapOutW) (.handle swapErrW)
        fdPolicy := .inheritNonCloexec #[]
      } with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"swap spawn failed: {repr e}")
      closeQuiet swapInR
      closeQuiet swapOutW
      closeQuiet swapErrW
      let sOut ← readAllPipe swapOutR
      let sErr ← readAllPipe swapErrR
      let sWst ← waitReapOrThrow "swap sh" swapChild.pid
      assertTrue s!"swap exit=0 got {repr sWst}" (sWst == .exited 0)
      assertTrue s!"swap stdout got {String.fromUTF8! sOut}" (sOut == "O:swap-ok".toUTF8)
      assertTrue s!"swap stderr got {String.fromUTF8! sErr}" (sErr == "E:swap-ok".toUTF8)
    finally
      closeQuiet swapInR
      closeQuiet swapInW
      closeQuiet swapOutR
      closeQuiet swapOutW
      closeQuiet swapErrR
      closeQuiet swapErrW

    let (nulInR, nulInW) ← mkPipeOrThrow "sigkill in"
    let (nulOutR, nulOutW) ← mkPipeOrThrow "sigkill out"
    try
      closeQuiet nulInW
      let sigChild ← match ← spawn {
        path := "/bin/sh"
        argv := #[.lit "/bin/sh", .lit "-c", .lit "kill -9 $$"]
        stdio := .redirect (.handle nulInR) (.handle nulOutW) (.handle nulOutW) true
      } with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"sigkill spawn failed: {repr e}")
      closeQuiet nulInR
      closeQuiet nulOutW
      let _ ← readAllPipe nulOutR
      let sigWst ← waitReapOrThrow "sigkill sh" sigChild.pid
      assertTrue s!"sigkill wait=.signaled 9 got {repr sigWst}" (sigWst == .signaled 9)
    finally
      closeQuiet nulInR
      closeQuiet nulInW
      closeQuiet nulOutR
      closeQuiet nulOutW
  finally
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW
    closeQuiet errR
    closeQuiet errW
    closeQuiet cloR
    closeQuiet cloW

/-- Runtime verification for `LeanSwe.PostFork.assume_postfork_errPipeWireAndBrokenPipe`. -/
def assume_postfork_errPipeWireAndBrokenPipe : IO Unit := do
  let badCwd ← spawn {
    path := "/bin/true"
    argv := #[.lit "/bin/true"]
    cwd := some "/nonexistent_postfork_rt_dir_01"
  }
  expectChildFailed "badCwd" .chdir badCwd
  match badCwd with
  | .error e => assertTrue s!"badCwd ENOENT got {repr e.errno}" (e.errno == some Errno.ENOENT)
  | .ok _ => pure ()

  let badBin ← spawn (ChildSpecM.ofCommand "/nonexistent_postfork_rt_bin_01")
  expectChildFailed "badBin" .execve badBin
  match badBin with
  | .error e => assertTrue s!"badBin ENOENT got {repr e.errno}" (e.errno == some Errno.ENOENT)
  | .ok _ => pure ()

  let notDir ← spawn (ChildSpecM.ofCommand "/bin/true/sub")
  expectChildFailed "notDir" .execve notDir
  match notDir with
  | .error e => assertTrue s!"notDir ENOTDIR got {repr e.errno}" (e.errno == some Errno.ENOTDIR)
  | .ok _ => pure ()

  let (epR, epW) ← mkPipeOrThrow "epipe"
  try
    closeQuiet epR
    match ← rawWriteOnce epW (ByteArray.mk #[1]) 0 1 with
    | .error e => assertTrue s!"writeOnce broken pipe EPIPE got {e}" (e == Errno.EPIPE)
    | .ok n => throw (IO.userError s!"expected EPIPE on broken pipe, got ok {n}")
  finally
    closeQuiet epR
    closeQuiet epW

/-- Runtime verification for `LeanSwe.PostFork.assume_postfork_syncBarrierReleaseAndAbort`. -/
def assume_postfork_syncBarrierReleaseAndAbort : IO Unit := do
  let (inR, inW) ← mkPipeOrThrow "barrier in"
  let (outR, outW) ← mkPipeOrThrow "barrier out"
  try
    closeQuiet inW
    let pend ← match ← spawnWithBarrier {
      path := "/bin/sh"
      argv := #[.lit "/bin/sh", .lit "-c", .lit "printf 'BAR_OK'"]
      stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
      processGroup := .newGroup
    } with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"spawnWithBarrier ok failed: {repr e}")
    closeQuiet inR
    closeQuiet outW
    assertTrue s!"pend pgid got {repr pend.pgid}" (pend.pgid == some pend.pid)
    let live ← match ← releaseBarrier pend with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"releaseBarrier ok failed: {repr e}")
    assertTrue s!"live pid match" (live.pid == pend.pid)
    let outBytes ← readAllPipe outR
    let wst ← waitReapOrThrow "barrier ok" live.pid
    assertTrue s!"barrier exit=0 got {repr wst}" (wst == .exited 0)
    assertTrue s!"barrier stdout got {String.fromUTF8! outBytes}" (outBytes == "BAR_OK".toUTF8)
  finally
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW

  let pendAbort ← match ← spawnWithBarrier (ChildSpecM.ofCommand "/bin/true") with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"spawnWithBarrier abort failed: {repr e}")
  match ← abortBarrier pendAbort with
  | .ok (.aborted wst) =>
    assertTrue s!"abortBarrier exit=125 got {repr wst}" (wst == .exited 125)
  | .ok other =>
    throw (IO.userError s!"abortBarrier expected aborted, got {repr other}")
  | .error e =>
    throw (IO.userError s!"abortBarrier failed: {repr e}")

/-- Runtime verification for `LeanSwe.PostFork.assume_postfork_argTokenAndImmortalThread`. -/
def assume_postfork_argTokenAndImmortalThread : IO Unit := do
  let (keepR, keepW) ← mkPipeOrThrow "argtoken keep"
  let (inR, inW) ← mkPipeOrThrow "argtoken in"
  let (outR, outW) ← mkPipeOrThrow "argtoken out"
  try
    writeAllPipe keepW "tok-data".toUTF8
    closeQuiet keepW
    closeQuiet inW
    let t ← IO.asTask (prio := .dedicated) do
      spawn {
        path := "/bin/sh"
        argv := #[
          .lit "/bin/sh",
          .lit "-c",
          .lit "d=$(cat \"/proc/self/fd/$1\"); printf '%s|%s|%s' \"$d\" \"$2\" \"$3\"",
          .lit "sh",
          ArgToken.ofHandle keepR,
          ArgToken.procSelfFd keepR,
          ArgToken.prefixedFd "--fd=" (.handle keepR) ":ok"
        ]
        stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
        fdPolicy := .closeAllAbove2Except #[.handle keepR]
        forkMode := .immortalThread
      }
    let spawnRes ← match t.get with
      | .ok r => pure r
      | .error e => throw e
    let child ← match spawnRes with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"immortalThread spawn failed: {repr e}")
    closeQuiet keepR
    closeQuiet inR
    closeQuiet outW
    let outBytes ← readAllPipe outR
    let wst ← waitReapOrThrow "immortalThread sh" child.pid
    assertTrue s!"immortalThread exit=0 got {repr wst}" (wst == .exited 0)
    let outStr := String.fromUTF8! outBytes
    let parts := outStr.splitOn "|"
    assertTrue s!"argToken parts={repr parts}" (parts.length == 3)
    assertTrue s!"argToken payload got {outStr}" (parts[0]! == "tok-data")
    assertTrue s!"argToken procSelfFd got {parts[1]!}" (parts[1]!.startsWith "/proc/self/fd/")
    assertTrue s!"argToken prefixedFd got {parts[2]!}"
      (parts[2]!.startsWith "--fd=" && parts[2]!.endsWith ":ok")
  finally
    closeQuiet keepR
    closeQuiet keepW
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW

  let closedRangeClose : Array (FdRef RawFd) :=
    (Array.range 64).map (fun i => FdRef.raw (Int32.ofNat i))
  let closedRawChild ← match ← spawn {
    path := "/bin/true"
    argv := #[.lit "/bin/true"]
    closeFds := closedRangeClose
  } with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"closed .raw closeFds spawn failed: {repr e}")
  let closedRawWst ← waitReapOrThrow "closed .raw closeFds" closedRawChild.pid
  assertTrue s!"closed .raw spawn exit=0 got {repr closedRawWst}" (closedRawWst == .exited 0)

  let closedRawPend ← match ← spawnWithBarrier {
    path := "/bin/true"
    argv := #[.lit "/bin/true"]
    closeFds := closedRangeClose
  } with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"closed .raw closeFds spawnWithBarrier failed: {repr e}")
  let closedRawLive ← match ← releaseBarrier closedRawPend with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"closed .raw closeFds releaseBarrier failed: {repr e}")
  let closedRawBarWst ← waitReapOrThrow "closed .raw barrier" closedRawLive.pid
  assertTrue s!"closed .raw barrier exit=0 got {repr closedRawBarWst}" (closedRawBarWst == .exited 0)

  let churnStop ← IO.mkRef false
  let churnTask ← IO.asTask (prio := .dedicated) do
    while !(← churnStop.get) do
      match ← rawMkPipeCloexec with
      | .ok (r, w) =>
        closeQuiet r
        closeQuiet w
      | .error _ => pure ()
  try
    for _ in List.range 16 do
      let concChild ← match ← spawn {
        path := "/bin/true"
        argv := #[.lit "/bin/true"]
        closeFds := closedRangeClose
      } with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"concurrent closed .raw spawn failed: {repr e}")
      let concWst ← waitReapOrThrow "concurrent closed .raw" concChild.pid
      assertTrue s!"concurrent closed .raw exit=0 got {repr concWst}" (concWst == .exited 0)
  finally
    churnStop.set true
    let _ ← IO.wait churnTask

  let (sigInR, sigInW) ← mkPipeOrThrow "sigpipe in"
  let (sigBrkR, sigBrkW) ← mkPipeOrThrow "sigpipe brk"
  let (sigErrR, sigErrW) ← mkPipeOrThrow "sigpipe err"
  try
    closeQuiet sigInW
    closeQuiet sigBrkR
    let defSigChild ← match ← spawn {
      path := "/bin/sh"
      argv := #[.lit "/bin/sh", .lit "-c", .lit "printf x"]
      stdio := .redirect (.handle sigInR) (.handle sigBrkW) (.handle sigErrW)
    } with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"default sigpipe spawn failed: {repr e}")
    let defSigWst ← waitReapOrThrow "default sigpipe sh" defSigChild.pid
    assertTrue s!"default ChildSpec.sigpipe resets SIGPIPE to SIG_DFL (got {repr defSigWst})"
      (defSigWst == .signaled 13)
  finally
    closeQuiet sigInR
    closeQuiet sigInW
    closeQuiet sigBrkR
    closeQuiet sigBrkW
    closeQuiet sigErrR
    closeQuiet sigErrW

  if ← System.FilePath.pathExists "/usr/bin/python3" then

    let (rdyR, rdyW) ← mkPipeOrThrow "pdeath rdy"
    let (hldR, hldW) ← mkPipeOrThrow "pdeath hld"
    let (finR, finW) ← mkPipeOrThrow "pdeath fin"
    try
      let pyCode := "import ctypes, os; ctypes.CDLL(None).prctl(1, 9, 0, 0, 0); os.write(1, b'R'); os.read(0, 1)"
      let dedTask ← IO.asTask (prio := .dedicated) do
        let r ← spawn {
          path := "/usr/bin/python3"
          argv := #[.lit "/usr/bin/python3", .lit "-c", .lit pyCode]
          stdio := .redirect (.handle hldR) (.handle rdyW) (.handle rdyW) true
          forkMode := .immortalThread
        }
        let _ ← readAllPipe finR
        pure r
      let mut gotReady := false
      for _ in List.range 64 do
        if !gotReady then
          match ← rawReadOnce rdyR 1 with
          | .ok bs =>
            if bs.size == 1 then
              gotReady := true
          | .error e =>
            if e != Errno.EINTR then
              throw (IO.userError s!"pdeath ready read failed errno={e}")
      assertTrue "pdeath child signalled ready" gotReady
      closeQuiet finW
      let dedRes ← match dedTask.get with
        | .ok r => pure r
        | .error e => throw e
      let pyChild ← match dedRes with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"pdeath immortalThread spawn failed: {repr e}")
      IO.sleep 30
      closeQuiet hldR
      closeQuiet hldW
      closeQuiet rdyW
      let pyWst ← waitReapOrThrow "pdeath python3" pyChild.pid
      assertTrue s!"pdeath immortalThread survived caller-thread exit (got {repr pyWst})"
        (pyWst == .exited 0)
    finally
      closeQuiet rdyR
      closeQuiet rdyW
      closeQuiet hldR
      closeQuiet hldW
      closeQuiet finR
      closeQuiet finW

/-- Runtime verification for `LeanSwe.PostFork.assume_postfork_closeUnkeptProcSelfFdFallback`. -/
def assume_postfork_closeUnkeptProcSelfFdFallback : IO Unit := do
  let (keepR, keepW) ← mkPipeOrThrow "unkept keep"
  let (dropR, dropW) ← mkPipeOrThrow "unkept drop"
  let (inR, inW) ← mkPipeOrThrow "unkept in"
  let (outR, outW) ← mkPipeOrThrow "unkept out"
  try
    writeAllPipe keepW "kept-payload".toUTF8
    closeQuiet keepW
    closeQuiet dropW
    closeQuiet inW
    let child ← match ← spawn {
      path := "/bin/sh"
      argv := #[
        .lit "/bin/sh",
        .lit "-c",
        .lit "d=$(cat \"/proc/self/fd/$1\"); if [ ! -e \"$2\" ]; then printf 'OK:%s' \"$d\"; fi",
        .lit "sh",
        ArgToken.ofHandle keepR,
        ArgToken.procSelfFd dropR
      ]
      stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
      fdPolicy := .closeAllAbove2Except #[.handle keepR]
    } with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"closeUnkept spawn failed: {repr e}")
    closeQuiet keepR
    closeQuiet dropR
    closeQuiet inR
    closeQuiet outW
    let outBytes ← readAllPipe outR
    let wst ← waitReapOrThrow "closeUnkept sh" child.pid
    assertTrue s!"closeUnkept exit=0 got {repr wst}" (wst == .exited 0)
    assertTrue s!"closeUnkept stdout got {String.fromUTF8! outBytes}"
      (outBytes == "OK:kept-payload".toUTF8)
  finally
    closeQuiet keepR
    closeQuiet keepW
    closeQuiet dropR
    closeQuiet dropW
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW

/-- Real error test for `LeanSwe.PostFork.spawn` (`invalidInput`). -/
def err_spawn_invalidInput : IO Unit := do
  expectInvalidInput "spawn empty path" (← spawn { path := "", argv := #[] })
  expectInvalidInput "spawn NUL path" (← spawn { path := "/bin/tr\x00ue", argv := #[] })
  expectInvalidInput "spawn NUL cwd" (← spawn { path := "/bin/true", argv := #[], cwd := some "/tmp/d\x00" })
  expectInvalidInput "spawn NUL argv" (← spawn { path := "/bin/true", argv := #[.lit "bad\x00arg"] })
  expectInvalidInput "spawn negative fdDecimal"
    (← spawn { path := "/bin/true", argv := #[.fdDecimal (.raw (-1))] })
  expectInvalidInput "spawn negative prefixedFd"
    (← spawn { path := "/bin/true", argv := #[.prefixedFd "p=" (.raw (-1)) ":s"] })
  expectInvalidInput "spawn NUL prefixedFd suffix"
    (← spawn { path := "/bin/true", argv := #[.prefixedFd "p=" (.raw 1) ":s\x00"] })
  expectInvalidInput "spawn NUL env value"
    (← spawn { path := "/bin/true", argv := #[], env := #[("K", "v\x00w")] })
  expectInvalidInput "spawn negative raw closeFd"
    (← spawn { path := "/bin/true", argv := #[], closeFds := #[.raw (-1)] })
  expectInvalidInput "spawn overlap close/keep"
    (← spawn { path := "/bin/true", argv := #[], closeFds := #[.raw 7], fdPolicy := .closeAllAbove2Except #[.raw 7] })

/-- Real error test for `LeanSwe.PostFork.spawn` (`sysError`). -/
def err_spawn_sysError : IO Unit := do
  expectSysError "spawn closed raw stdio"
    (← spawn { path := "/bin/true", argv := #[], stdio := .redirect (.raw 9999) (.raw 1) (.raw 2) true })

/-- Real error test for `LeanSwe.PostFork.spawn` (`childFailed`). -/
def err_spawn_childFailed : IO Unit := do
  expectChildFailed "spawn missing executable" .execve
    (← spawn (ChildSpecM.ofCommand "/nonexistent_postfork_rt_bin_02"))

/-- Real error test for `LeanSwe.PostFork.spawnWithBarrier` (`invalidInput`). -/
def err_spawnWithBarrier_invalidInput : IO Unit := do
  expectInvalidInput "spawnWithBarrier empty path" (← spawnWithBarrier { path := "", argv := #[] })
  expectInvalidInput "spawnWithBarrier negative keepFd"
    (← spawnWithBarrier { path := "/bin/true", argv := #[], fdPolicy := .closeAllAbove2Except #[.raw (-1)] })

/-- Real error test for `LeanSwe.PostFork.spawnWithBarrier` (`sysError`). -/
def err_spawnWithBarrier_sysError : IO Unit := do
  expectSysError "spawnWithBarrier closed raw keepFd"
    (← spawnWithBarrier { path := "/bin/true", argv := #[], fdPolicy := .closeAllAbove2Except #[.raw 9999] })

/-- Real error test for `LeanSwe.PostFork.releaseBarrier` (`sysError`). -/
def err_releaseBarrier_sysError : IO Unit := do
  let pend ← match ← spawnWithBarrier (ChildSpecM.ofCommand "/bin/true") with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"err_releaseBarrier_sysError spawn failed: {repr e}")
  try
    closeQuiet pend.syncWrite
    expectSysError "releaseBarrier closed syncWrite" (← releaseBarrier pend)
  finally
    closeQuiet pend.errRead
    let _ ← waitReapOrThrow "err_releaseBarrier_sysError cleanup" pend.pid
  let (inR, inW) ← mkPipeOrThrow "err_releaseBarrier_sysError cat stdin"
  let (outR, outW) ← mkPipeOrThrow "err_releaseBarrier_sysError cat out"
  let pendCat ← match ← spawnWithBarrier {
    path := "/bin/cat"
    argv := #[.lit "/bin/cat"]
    stdio := .redirect (.handle inR) (.handle outW) (.handle outW) true
  } with
  | .ok p => pure p
  | .error e =>
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW
    throw (IO.userError s!"err_releaseBarrier_sysError cat spawn failed: {repr e}")
  try
    closeQuiet inR
    closeQuiet outW
    closeQuiet pendCat.errRead
    expectSysError "releaseBarrier closed errRead fails fast before barrier write" (← releaseBarrier pendCat)
    closeQuiet pendCat.syncWrite
    let wst ← waitReapOrThrow "err_releaseBarrier_sysError cat abort reap" pendCat.pid
    assertTrue s!"closed errRead left child paused at barrier (exit 125, got {repr wst})"
      (wst == .exited 125)
  finally
    closeQuiet inR
    closeQuiet inW
    closeQuiet outR
    closeQuiet outW
    closeQuiet pendCat.syncWrite
    closeQuiet pendCat.errRead

/-- Real error test for `LeanSwe.PostFork.releaseBarrier` (`childFailed`). -/
def err_releaseBarrier_childFailed : IO Unit := do
  let pend ← match ← spawnWithBarrier (ChildSpecM.ofCommand "/nonexistent_postfork_rt_bin_03") with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"err_releaseBarrier_childFailed spawn failed: {repr e}")
  expectChildFailed "releaseBarrier missing executable" .execve (← releaseBarrier pend)
  let (kInR, kInW) ← mkPipeOrThrow "err_releaseBarrier_childFailed kill stdin"
  let (kOutR, kOutW) ← mkPipeOrThrow "err_releaseBarrier_childFailed kill out"
  let pendKilled ← match ← spawnWithBarrier {
    path := "/bin/cat"
    argv := #[.lit "/bin/cat"]
    stdio := .redirect (.handle kInR) (.handle kOutW) (.handle kOutW) true
  } with
  | .ok p => pure p
  | .error e =>
    closeQuiet kInR
    closeQuiet kInW
    closeQuiet kOutR
    closeQuiet kOutW
    throw (IO.userError s!"err_releaseBarrier_childFailed paused cat spawn failed: {repr e}")
  try
    closeQuiet kInR
    closeQuiet kOutW
    let killer ← match ← spawn {
      path := "/bin/kill"
      argv := #[.lit "/bin/kill", .lit "-9", .lit s!"{pendKilled.pid}"]
    } with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"err_releaseBarrier_childFailed kill -9 spawn failed: {repr e}")
    let kwst ← waitReapOrThrow "err_releaseBarrier_childFailed kill -9 reap" killer.pid
    assertTrue s!"kill -9 exit=0 got {repr kwst}" (kwst == .exited 0)
    let statPath : System.FilePath := ⟨s!"/proc/{pendKilled.pid}/stat"⟩
    for _ in List.range 500 do
      let stTxt ← try IO.FS.readFile statPath catch _ => pure ""
      if ((stTxt.splitOn ") ").getLastD "").startsWith "Z" then
        break
      IO.sleep 1
    match ← releaseBarrier pendKilled with
    | .ok c =>
      throw (IO.userError s!"releaseBarrier on SIGKILLed paused child falsely succeeded: {repr c}")
    | .error e =>
      assertTrue s!"SIGKILLed releaseBarrier kind=childFailed got {repr e}" (e.kind == .childFailed)
      assertTrue s!"SIGKILLed releaseBarrier errno=EIO got {repr e.errno}" (e.errno == some Errno.EIO)
      assertTrue s!"SIGKILLed releaseBarrier cf got {repr e.childFailure}"
        (e.childFailure == some { stage := .wireTruncated, errno := Errno.EIO, waitStatus := some (.signaled 9) })
      let postWait ← rawWaitOnce pendKilled.pid
      assertTrue s!"SIGKILLed releaseBarrier reaped child (expected ECHILD, got {repr postWait})"
        (match postWait with | .error err => err == Errno.ECHILD | .ok _ => false)
  finally
    closeQuiet kInR
    closeQuiet kInW
    closeQuiet kOutR
    closeQuiet kOutW
    closeQuiet pendKilled.syncWrite
    closeQuiet pendKilled.errRead

/-- Real error test for `LeanSwe.PostFork.abortBarrier` (`sysError`). -/
def err_abortBarrier_sysError : IO Unit := do
  let pend ← match ← spawnWithBarrier (ChildSpecM.ofCommand "/bin/true") with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"err_abortBarrier_sysError spawn failed: {repr e}")
  try
    closeQuiet pend.syncWrite
    expectSysError "abortBarrier closed syncWrite" (← abortBarrier pend)
  finally
    closeQuiet pend.errRead
    let _ ← waitReapOrThrow "err_abortBarrier_sysError cleanup" pend.pid

/-- Registry of all `5` runtime assumption checks matching `SpecTests.externalAssumptions`. -/
def registeredAssumptions : Array Core.RegisteredAssumption := #[
  ⟨"LeanSwe.PostFork.assume_postfork_stdioCycleAndCloexec", assume_postfork_stdioCycleAndCloexec⟩,
  ⟨"LeanSwe.PostFork.assume_postfork_errPipeWireAndBrokenPipe", assume_postfork_errPipeWireAndBrokenPipe⟩,
  ⟨"LeanSwe.PostFork.assume_postfork_syncBarrierReleaseAndAbort", assume_postfork_syncBarrierReleaseAndAbort⟩,
  ⟨"LeanSwe.PostFork.assume_postfork_argTokenAndImmortalThread", assume_postfork_argTokenAndImmortalThread⟩,
  ⟨"LeanSwe.PostFork.assume_postfork_closeUnkeptProcSelfFdFallback", assume_postfork_closeUnkeptProcSelfFdFallback⟩
]

/-- Registry of all `8` `.tested` real error-coverage tests matching `SpecTests.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.PostFork.RuntimeTests.err_spawn_invalidInput", .real, err_spawn_invalidInput⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_spawn_sysError", .real, err_spawn_sysError⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_spawn_childFailed", .real, err_spawn_childFailed⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_spawnWithBarrier_invalidInput", .real, err_spawnWithBarrier_invalidInput⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_spawnWithBarrier_sysError", .real, err_spawnWithBarrier_sysError⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_releaseBarrier_sysError", .real, err_releaseBarrier_sysError⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_releaseBarrier_childFailed", .real, err_releaseBarrier_childFailed⟩,
  ⟨"LeanSwe.PostFork.RuntimeTests.err_abortBarrier_sysError", .real, err_abortBarrier_sysError⟩
]

/-- Execute all runtime assumption tests and all error-coverage tests for `LeanSwe.PostFork`. -/
def runAll : IO Unit := do
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests

end LeanSwe.PostFork.RuntimeTests

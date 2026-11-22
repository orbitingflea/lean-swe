import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Poll.SpecTests
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.LinuxSyscall.Poll.Strace

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Poll
open Fuzz.LinuxSyscall

@[extern "leanswe_poll_close_fd"]
private opaque rawPollClose : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_poll_efd_write"]
private opaque rawEfdWrite : @& RawFd → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_poll_efd_read"]
private opaque rawEfdRead : @& RawFd → IO (Except Errno UInt64)

@[extern "leanswe_poll_open_pipe"]
private opaque rawOpenPipe : IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_poll_open_kind"]
private opaque rawOpenKind : UInt32 → IO (Except Errno RawFd)

@[extern "leanswe_poll_get_fd_flags"]
private opaque rawGetFdFlags : @& RawFd → IO (Except Errno UInt32)

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque rawRtArmSigalrm : UInt32 → UInt8 → BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque rawRtDisarmSigalrm : UInt32 → BaseIO Unit

private def assertTrue (msg : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"assertion failed: {msg}")

private def assertEqErrno (msg : String) (actual expected : Errno) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{msg}: expected errno {expected}, got {actual}")

private def assertErr {α : Type} (msg : String) (r : Except Errno α) (expected : Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error {expected}, got ok")
  | .error e => assertEqErrno msg e expected

private def assertOk {α : Type} (msg : String) (r : Except Errno α) : IO α := do
  match r with
  | .ok v => return v
  | .error e => throw (IO.userError s!"{msg}: unexpected error {e}")

private def safeClose (fd : RawFd) : IO Unit := do
  let _ ← rawPollClose fd

private def mkMockPollOps (err : Errno) : PollOps :=
  Internal.mkPollOps
    { ppoll := fun _ _ _ _ _ => pure (.error err)
      eventfd2 := fun _ _ => pure (.error err) }

private def closedEventFd : IO RawFd := do
  let fd ← assertOk "eventfd2 for close" (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
  assertOk "close eventfd" (← rawPollClose fd)
  return fd

private def runMockPollError (label : String) (forced : Errno) (expectedKind : PollErrorKind)
    (act : PollOps → IO (Except Errno Unit)) : IO Unit := do
  let res ← act (mkMockPollOps forced)
  match res with
  | .ok _ => throw (IO.userError s!"mock {label}: expected {forced}, got ok")
  | .error e =>
    assertEqErrno s!"mock {label}" e forced
    if PollErrorKind.ofErrno e != expectedKind then
      throw (IO.userError s!"mock {label}: wrong PollErrorKind classification")

private def straceInjectSpec (injectExpr workerFlag errName : String) : IO Unit := do
  let exe ← IO.appPath
  let out ← IO.Process.output {
    cmd := "strace"
    args := #["-f", "-qq", "-o", "/dev/null", "-e", s!"inject={injectExpr}",
      exe.toString, workerFlag, errName]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"strace {injectExpr} failed (exit={out.exitCode}): {out.stderr}")

/-- Verify `ppoll(2)` FD pinning, `Timespec` encoding, `PollEvents` roundtrip, `POLLERR`/`POLLHUP`, and duplicate FD handling. -/
private def assume_poll_ppoll_fdPinTimespecAndEventsAbi : IO Unit := do
  let ops := defaultOps
  let rEmpty ← ops.ppoll #[] (some { sec := 0, nsec := 0 })
  let emptyRev ← assertOk "ppoll empty" rEmpty
  assertTrue "ppoll empty len 0" (emptyRev.size == 0)

  let rBadNeg ← ops.ppoll #[] (some { sec := -1, nsec := 0 })
  assertErr "ppoll negative sec" rBadNeg Errno.EINVAL
  let rBadNs ← ops.ppoll #[] (some { sec := 0, nsec := NANOS_PER_SEC })
  assertErr "ppoll nsec >= 1e9" rBadNs Errno.EINVAL

  let e0 ← assertOk "eventfd2 0" (← ops.eventfd2 0 { nonblock := true, cloexec := true })
  let e5 ← assertOk "eventfd2 5" (← ops.eventfd2 5 { nonblock := true, cloexec := true })
  try
    let both : PollEvents := { pollin := true, pollout := true }
    let revBoth ← assertOk "ppoll both" (← ops.ppoll #[(e0, both), (e5, both)] (some { sec := 0, nsec := 0 }))
    assertTrue "e0 pollout only" (revBoth == #[{ pollout := true }, { pollin := true, pollout := true }])

    let revZero ← assertOk "ppoll unready zero" (← ops.ppoll #[(e0, { pollin := true })] (some { sec := 0, nsec := 0 }))
    assertTrue "unready zero -> empty" (revZero == #[{}])

    let revSmall ← assertOk "ppoll unready 5us" (← ops.ppoll #[(e0, { pollin := true })] (some { sec := 0, nsec := 5000 }))
    assertTrue "unready 5us -> empty" (revSmall == #[{}])

    let revInf ← assertOk "ppoll infinite ready" (← Poll.ppoll #[(e5, { pollin := true })])
    assertTrue "infinite ready -> pollin" (revInf == #[{ pollin := true }])

    let revDup ← assertOk "ppoll dup fds" (← ops.ppoll #[(e5, { pollin := true }), (e5, { pollout := true }), (e5, {})] (some { sec := 0, nsec := 0 }))
    assertTrue "dup fds revents" (revDup == #[{ pollin := true }, { pollout := true }, {}])

    let wakeTask ← IO.asTask (prio := .dedicated) do
      IO.sleep 10
      rawEfdWrite e0 1
    let rev64 ← assertOk "ppoll 64-bit tv_sec >= 2^32" (← ops.ppoll #[(e0, { pollin := true })] (some { sec := 0x100000000, nsec := 0 }))
    let _ ← IO.wait wakeTask
    assertTrue "ppoll 64-bit tv_sec blocked until wakeup" (rev64 == #[{ pollin := true }])
  finally
    safeClose e0
    safeClose e5

  let (pr, pw) ← assertOk "open pipe" (← rawOpenPipe)
  let _ ← safeClose pw
  let revHup ← assertOk "ppoll pipe read after writer close" (← ops.ppoll #[(pr, { pollin := true })] (some { sec := 0, nsec := 0 }))
  safeClose pr
  assertTrue "pipe POLLHUP" (revHup == #[{ pollhup := true }])

  let (pr2, pw2) ← assertOk "open pipe 2" (← rawOpenPipe)
  let _ ← safeClose pr2
  let revErr ← assertOk "ppoll pipe write after reader close" (← ops.ppoll #[(pw2, { pollout := true })] (some { sec := 0, nsec := 0 }))
  safeClose pw2
  assertTrue "pipe POLLERR" ((revErr.getD 0 {}).pollerr)

  let opath ← assertOk "open O_PATH" (← rawOpenKind 2)
  let revNval ← try
    assertOk "ppoll O_PATH" (← ops.ppoll #[(opath, { pollin := true, pollout := true })] (some { sec := 0, nsec := 0 }))
  finally
    safeClose opath
  assertTrue "O_PATH POLLNVAL" (revNval == #[{ pollnval := true }])

/-- Verify `eventfd2(2)` `initval` and `EFD_NONBLOCK`/`EFD_CLOEXEC`/`EFD_SEMAPHORE` ABI plus counter saturation. -/
private def assume_poll_eventfd2_flagsAndInitvalAbi : IO Unit := do
  let ops := defaultOps
  let eNorm ← assertOk "eventfd2 normal" (← ops.eventfd2 2 { nonblock := true, cloexec := true, semaphore := false })
  let eSem ← assertOk "eventfd2 sem" (← ops.eventfd2 2 { nonblock := true, cloexec := false, semaphore := true })
  let eBlock ← assertOk "eventfd2 blocking" (← Poll.eventfd2)
  try
    let fNorm ← assertOk "flags eNorm" (← rawGetFdFlags eNorm)
    assertTrue "eNorm CLOEXEC+NONBLOCK" (fNorm == 3)
    let fSem ← assertOk "flags eSem" (← rawGetFdFlags eSem)
    assertTrue "eSem NONBLOCK only" (fSem == 2)
    let fBlock ← assertOk "flags eBlock" (← rawGetFdFlags eBlock)
    assertTrue "eBlock CLOEXEC only" (fBlock == 1)
    assertErr "efd write maxval EINVAL" (← rawEfdWrite eNorm 0xffffffffffffffff) Errno.EINVAL
    assertOk "efd write saturate" (← rawEfdWrite eNorm (EFD_MAX_COUNT - 2))
    assertErr "efd write saturated EAGAIN" (← rawEfdWrite eNorm 1) Errno.EAGAIN
    let revSat ← assertOk "ppoll saturated" (← ops.ppoll #[(eNorm, { pollin := true, pollout := true })] (some {}))
    assertTrue "saturated pollin only" (revSat == #[{ pollin := true, pollout := false }])

    let vNorm ← assertOk "efd read normal" (← rawEfdRead eNorm)
    assertTrue "vNorm == EFD_MAX_COUNT" (vNorm == EFD_MAX_COUNT)
    assertErr "efd read drained EAGAIN" (← rawEfdRead eNorm) Errno.EAGAIN

    let vSem1 ← assertOk "efd read sem 1" (← rawEfdRead eSem)
    assertTrue "sem 1 == 1" (vSem1 == 1)
    let vSem2 ← assertOk "efd read sem 2" (← rawEfdRead eSem)
    assertTrue "sem 2 == 1" (vSem2 == 1)
    assertErr "efd read sem empty EAGAIN" (← rawEfdRead eSem) Errno.EAGAIN

    let eMax32 ← assertOk "eventfd2 0xffffffff" (← ops.eventfd2 0xffffffff { nonblock := true, cloexec := true, semaphore := false })
    try
      let vMax32 ← assertOk "efd read 0xffffffff" (← rawEfdRead eMax32)
      assertTrue "vMax32 == 0xffffffff" (vMax32 == 0xffffffff)
    finally
      safeClose eMax32
  finally
    safeClose eNorm
    safeClose eSem
    safeClose eBlock

  let cfd ← closedEventFd
  assertErr "closed efd read EBADF" (← rawEfdRead cfd) Errno.EBADF
  assertErr "closed efd write EBADF" (← rawEfdWrite cfd 1) Errno.EBADF
  assertErr "double close EBADF" (← rawPollClose cfd) Errno.EBADF

/-- Real `ppoll` `.badFd` test (`EBADF` on closed `LeanFdBox` at index 0 and index 1). -/
private def err_ppoll_badFd : IO Unit := do
  let live ← assertOk "eventfd2 live" (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
  let cfd ← closedEventFd
  try
    assertErr "ppoll closed at 0" (← defaultOps.ppoll #[(cfd, { pollin := true })] (some {})) Errno.EBADF
    assertErr "ppoll closed at 1" (← defaultOps.ppoll #[(live, { pollout := true }), (cfd, { pollin := true })] (some {})) Errno.EBADF
  finally
    safeClose live

/-- Real `ppoll` `.invalidArg` test (`EINVAL` on negative `tv_sec`, out-of-range `tv_nsec`, and `MAX_POLL_NFDS` plus wrapper `EIO` length guard). -/
private def err_ppoll_invalidArg : IO Unit := do
  let fd ← assertOk "eventfd2" (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
  try
    assertErr "ppoll sec=-1" (← defaultOps.ppoll #[(fd, { pollin := true })] (some { sec := -1, nsec := 0 })) Errno.EINVAL
    assertErr "ppoll nsec=1e9" (← defaultOps.ppoll #[(fd, { pollin := true })] (some { sec := 0, nsec := NANOS_PER_SEC })) Errno.EINVAL
    let okRawOps : PollOps :=
      Internal.mkPollOps
        { ppoll := fun _ _ _ _ _ => pure (.ok ByteArray.empty)
          eventfd2 := fun _ _ => pure (.error Errno.ENOSYS) }
    assertErr "ppoll bad ts wrapper guard" (← okRawOps.ppoll #[(fd, { pollin := true })] (some { sec := -1, nsec := 0 })) Errno.EINVAL
    let hugeEntries := Array.replicate (MAX_POLL_NFDS + 1) (fd, ({} : PollEvents))
    assertErr "ppoll max nfds wrapper guard" (← okRawOps.ppoll hugeEntries (some {})) Errno.EINVAL
    assertErr "ppoll max nfds none wrapper guard" (← okRawOps.ppoll hugeEntries none) Errno.EINVAL
    assertErr "ppoll max nfds none defaultOps" (← defaultOps.ppoll hugeEntries none) Errno.EINVAL
    assertErr "ppoll revents len mismatch" (← okRawOps.ppoll #[(fd, { pollin := true })] (some {})) Errno.EIO
  finally
    safeClose fd

/-- Real `ppoll` `.interrupted` test (`EINTR` via live `strace` fault injection). -/
private def err_ppoll_interrupted : IO Unit := do
  let _ ← assertOk "ppoll sanity" (← defaultOps.ppoll #[] (some {}))
  straceInjectSpec "ppoll:error=EINTR" "--poll-strace-worker" "EINTR"

/-- Mocked plus `strace` `ppoll` `.transientOrResource` test (`ENOMEM`). -/
private def err_ppoll_transient : IO Unit := do
  runMockPollError "ppoll transient" Errno.ENOMEM .transientOrResource fun ops =>
    ops.ppoll #[] (some {}) >>= fun r => pure (r.map fun _ => ())
  straceInjectSpec "ppoll:error=ENOMEM" "--poll-strace-worker" "ENOMEM"

/-- Mocked `eventfd2` non-transient error paths (`EBADF`, `EINVAL`, `EINTR`). -/
private def err_eventfd2_mocked : IO Unit := do
  runMockPollError "eventfd2 EBADF" Errno.EBADF .badFd fun ops =>
    ops.eventfd2 0 {} >>= fun r => pure (r.map fun _ => ())
  runMockPollError "eventfd2 EINVAL" Errno.EINVAL .invalidArg fun ops =>
    ops.eventfd2 0 {} >>= fun r => pure (r.map fun _ => ())
  runMockPollError "eventfd2 EINTR" Errno.EINTR .interrupted fun ops =>
    ops.eventfd2 0 {} >>= fun r => pure (r.map fun _ => ())

/-- Mocked plus `strace` `eventfd2` `.transientOrResource` test (`ENFILE`). -/
private def err_eventfd2_transient : IO Unit := do
  runMockPollError "eventfd2 transient" Errno.ENFILE .transientOrResource fun ops =>
    ops.eventfd2 0 {} >>= fun r => pure (r.map fun _ => ())
  straceInjectSpec "eventfd2:error=ENFILE:when=2+" "--poll-strace-efd-worker" "ENFILE"

@[noinline] private def allocPipeReadDroppingWrite : IO RawFd := do
  let (pr, _pw) ← assertOk "finalizer open pipe" (← rawOpenPipe)
  return pr

@[noinline] private def allocPipeWriteDroppingReadFd0 : IO RawFd := do
  let (pr, pw) ← assertOk "finalizer fd0 pipe" (← rawOpenPipe)
  let rawPr ← SandboxEnv.peekRawFd pr
  assertTrue "pipe read landed on raw fd 0" (rawPr == 0)
  return pw

private def runFdBoxAndErrorKindTests : IO Unit := do
  let prFin ← allocPipeReadDroppingWrite
  try
    let revFin ← assertOk "ppoll after writer finalizer"
      (← defaultOps.ppoll #[(prFin, { pollin := true })] (some { sec := 0, nsec := 0 }))
    assertTrue "writer finalizer closed pipe write end" (revFin == #[{ pollhup := true }])
  finally
    safeClose prFin

  let mut sawBusy := false
  for _ in [0 : 8] do
    if !sawBusy then
      let efdBusy ← assertOk "eventfd2 busy test" (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
      let entered ← IO.mkRef false
      let poller ← IO.asTask (prio := .dedicated) do
        entered.set true
        defaultOps.ppoll #[(efdBusy, { pollin := true })] (some { sec := 0, nsec := 500_000_000 })
      while !(← entered.get) do
        IO.sleep 1
      IO.sleep 5
      match ← rawPollClose efdBusy with
      | .error e =>
        if e == Errno.EBUSY then
          sawBusy := true
      | .ok () => pure ()
      let _ ← rawEfdWrite efdBusy 1
      let _ ← IO.wait poller
      safeClose efdBusy
  assertTrue "concurrent close observed EBUSY while pinned" sawBusy

  let abaOld ← assertOk "eventfd2 aba old" (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
  assertOk "close aba old" (← rawPollClose abaOld)
  assertErr "double close aba old EBADF" (← rawPollClose abaOld) Errno.EBADF
  let abaNew ← assertOk "eventfd2 aba new" (← defaultOps.eventfd2 3 { nonblock := true, cloexec := true })
  try
    assertErr "ppoll on closed abaOld after fd reuse EBADF"
      (← defaultOps.ppoll #[(abaOld, { pollin := true })] (some { sec := 0, nsec := 0 })) Errno.EBADF
    assertErr "ppoll partial pin with closed second entry EBADF"
      (← defaultOps.ppoll #[(abaNew, { pollout := true }), (abaOld, { pollin := true })]
        (some { sec := 0, nsec := 0 })) Errno.EBADF
  catch e =>
    safeClose abaNew
    throw e
  assertOk "close abaNew after partial pin EBADF" (← rawPollClose abaNew)

  let (stZero, _) ← SandboxEnv.runForked do
    SandboxEnv.closeRaw 0
    let zfd ← assertOk "eventfd2 raw fd 0" (← defaultOps.eventfd2 7 { nonblock := true, cloexec := true })
    let rawZ ← SandboxEnv.peekRawFd zfd
    assertTrue "eventfd2 landed on raw fd 0" (rawZ == 0)
    let revZ ← assertOk "ppoll raw fd 0"
      (← defaultOps.ppoll #[(zfd, { pollin := true, pollout := true })] (some { sec := 0, nsec := 0 }))
    assertTrue "ppoll raw fd 0 revents" (revZ == #[{ pollin := true, pollout := true }])
    assertOk "close raw fd 0" (← rawPollClose zfd)
    let pwFin0 ← allocPipeWriteDroppingReadFd0
    let revFin0 ← assertOk "ppoll after reader fd 0 finalizer"
      (← defaultOps.ppoll #[(pwFin0, { pollout := true })] (some { sec := 0, nsec := 0 }))
    assertTrue "reader fd 0 finalizer closed pipe read end"
      (revFin0 == #[{ pollout := true, pollerr := true }])
    assertOk "close pwFin0" (← rawPollClose pwFin0)
    let efdBlk ← assertOk "eventfd2 blocking none timeout"
      (← defaultOps.eventfd2 0 { nonblock := true, cloexec := true })
    rawRtArmSigalrm 5000 0
    let rNone ← defaultOps.ppoll #[(efdBlk, { pollin := true })] none
    rawRtDisarmSigalrm 0
    assertErr "ppoll timeout none interrupted EINTR" rNone Errno.EINTR
    assertOk "close efdBlk" (← rawPollClose efdBlk)
    return ByteArray.empty
  assertTrue "forked poll raw fd 0 child status" (stZero == 0)

  let errPairs : Array (Errno × PollErrorKind) :=
    #[ (Errno.EBADF, .badFd)
     , (Errno.EINVAL, .invalidArg)
     , (Errno.ENOSYS, .invalidArg)
     , (Errno.EINTR, .interrupted)
     , (Errno.ENOMEM, .transientOrResource)
     , (Errno.ENFILE, .transientOrResource)
     , (Errno.EMFILE, .transientOrResource)
     , (Errno.EIO, .transientOrResource)
     , (Errno.ENOSPC, .transientOrResource) ]
  for (code, wantKind) in errPairs do
    assertTrue s!"PollErrorKind.ofErrno {code}" (PollErrorKind.ofErrno code == wantKind)

/-- Run all `Poll` real and mocked regression and error-path checks (dispatched by `leanswe-fuzz --smoke` and `lean-swe-mut-test`). -/
def runChecks : IO Unit := do
  assume_poll_ppoll_fdPinTimespecAndEventsAbi
  assume_poll_eventfd2_flagsAndInitvalAbi
  err_ppoll_badFd
  err_ppoll_invalidArg
  err_ppoll_interrupted
  err_ppoll_transient
  err_eventfd2_mocked
  err_eventfd2_transient
  runFdBoxAndErrorKindTests

private def parseInjectedErrno (s : String) : Errno :=
  match s with
  | "EINTR" => Errno.EINTR
  | "ENOMEM" => Errno.ENOMEM
  | "EIO" => Errno.EIO
  | "ENFILE" => Errno.ENFILE
  | "EAGAIN" => Errno.EAGAIN
  | _ => 0

private def straceWorker (errName : String) : IO UInt32 := do
  let expected := parseInjectedErrno errName
  let e0 ← match ← defaultOps.eventfd2 0 { nonblock := true, cloexec := true } with
    | .ok fd => pure fd
    | .error e =>
      IO.eprintln s!"poll strace-worker: setup eventfd2 failed with {e}"
      return 4
  let e1 ← match ← defaultOps.eventfd2 1 { nonblock := true, cloexec := true } with
    | .ok fd => pure fd
    | .error e =>
      safeClose e0
      IO.eprintln s!"poll strace-worker: setup second eventfd2 failed with {e}"
      return 4
  let s0 := PollState.initial
  let some s1 := Poll.allowedStep s0 (.eventfd2 0 { nonblock := true, cloexec := true }) (.opened 0)
    | do safeClose e0; safeClose e1; IO.eprintln "poll strace-worker: model setup 0 failed"; return 5
  let some s2 := Poll.allowedStep s1 (.eventfd2 1 { nonblock := true, cloexec := true }) (.opened 1)
    | do safeClose e0; safeClose e1; IO.eprintln "poll strace-worker: model setup 1 failed"; return 5
  let reqEntries : Array (HandleId × PollEvents) := #[(0, { pollin := true, pollout := true }), (1, { pollout := true })]
  let res ← defaultOps.ppoll #[(e0, { pollin := true, pollout := true }), (e1, { pollout := true })] (some {})
  let c0 ← rawPollClose e0
  let c1 ← rawPollClose e1
  match c0, c1 with
  | .ok (), .ok () => pure ()
  | _, _ =>
    IO.eprintln s!"poll strace-worker: post-error close failed (unpin leak?): {repr c0}, {repr c1}"
    return 6
  match res with
  | .error e =>
    if e != expected then
      IO.eprintln s!"poll strace-worker: expected {expected} ({errName}), got {e}"
      return 2
    let stepOk := (Poll.allowedStep s2 (.ppoll reqEntries (some {})) (.err e)).isSome
    if errName == "EAGAIN" then
      if stepOk then
        IO.eprintln "poll strace-worker: model unexpectedly accepted EAGAIN"
        return 7
      return 0
    if !stepOk then
      IO.eprintln s!"poll strace-worker: allowedStep rejected {errName}"
      return 8
    return 0
  | .ok _ =>
    IO.eprintln s!"poll strace-worker: expected {errName}, got ok"
    return 3

private def straceEfdWorker (errName : String) : IO UInt32 := do
  let expected := parseInjectedErrno errName
  let s0 := PollState.initial
  let mut sawExpected := false
  for _ in [0 : 2] do
    match ← defaultOps.eventfd2 0 { nonblock := true, cloexec := true } with
    | .ok fd => safeClose fd
    | .error e =>
      if e == expected then
        let stepOk := (Poll.allowedStep s0 (.eventfd2 0 { nonblock := true, cloexec := true }) (.err e)).isSome
        if errName == "EAGAIN" then
          if stepOk then
            IO.eprintln "poll efd strace-worker: model unexpectedly accepted EAGAIN"
            return 7
          sawExpected := true
        else if !stepOk then
          IO.eprintln s!"poll efd strace-worker: allowedStep rejected {errName}"
          return 8
        else
          sawExpected := true
  if sawExpected then return 0
  IO.eprintln s!"poll efd strace-worker: did not observe {errName}"
  return 4

/-- Run live `strace -f` fault-injection checks (`EINTR`, `ENOMEM`, `EIO`, `ENFILE`, `EAGAIN`) against `ppoll` and `eventfd2`. -/
def runStraceFaultCheck : IO Unit := do
  for errName in ["EINTR", "ENOMEM", "EIO", "ENFILE", "EAGAIN"] do
    straceInjectSpec s!"ppoll:error={errName}" "--poll-strace-worker" errName
    straceInjectSpec s!"eventfd2:error={errName}:when=2+" "--poll-strace-efd-worker" errName

/-- Handle `--poll-strace-fault-check` and worker subcommands dispatched by `leanswe-fuzz` (`Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker`) and `lean-swe-mut-test`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    runStraceFaultCheck
    IO.println "POLL_STRACE_FAULT_CHECK: ok (EINTR, ENOMEM, EIO, ENFILE, EAGAIN)"
    return 0
  | ["--worker", errName] => straceWorker errName
  | ["--efd-worker", errName] => straceEfdWorker errName
  | _ =>
    IO.eprintln s!"unknown poll strace args: {args}"
    return 1

end Fuzz.LinuxSyscall.Poll.Strace

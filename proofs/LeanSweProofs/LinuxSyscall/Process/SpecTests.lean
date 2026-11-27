import Core.NondetTest
import LeanSwe.LinuxSyscall.Process.Types
import LeanSweProofs.LinuxSyscall.Process.Model

namespace LeanSwe.LinuxSyscall.Process

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Errno.isTransientOsErrno` matches `{EINTR, EIO, ENOMEM, ENFILE, EMFILE, ENOSPC}`, excludes `EFAULT`, and `ProcessErrorKind.ofErrno` universally maps every Linux `Errno` (including `EFAULT`, `EAGAIN`, and unenumerated codes) to its exact semantic category. -/
def test_process_errno_classificationAndTransient
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → ProcessErrorKind := ProcessErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  NondetTest.assert (classify e =
    (if e == Errno.ESRCH || e == Errno.ENOENT then .noSuchProcess
     else if e == Errno.ECHILD then .noChild
     else if e == Errno.EBADF then .badFd
     else if e == Errno.EINVAL || e == Errno.ENOSYS || e == Errno.EOPNOTSUPP then .invalidArg
     else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
     else .transientOrResource))
  NondetTest.assert (classify Errno.EFAULT = .transientOrResource ∧
    classify Errno.EAGAIN = .transientOrResource ∧
    classify (999 : Errno) = .transientOrResource)

/-- Portable wire encoders (`PipeFlags.toBits`, `WaitFlags.toBits`, `Signal.toRaw`, `PidfdOpenFlags.toBits`, `PidfdSignalFlags.toBits`) are injective with exact wire bit positions, and `PipeFlags.isValid`, `WaitFlags.isValid`, `PidfdOpenFlags.isValid`, `Signal.isValid`, and `PidfdSignalFlags.isValid` universally enforce exact Linux `7.1.6` `_NSIG` (`0..64`), `extraBits == 0`, and scope-exclusivity invariants. -/
def test_process_flagsAndSignals_encodersInjectiveAndValid
    {runner} [NondetTest runner]
    (encPipe : PipeFlags → UInt64 := PipeFlags.toBits)
    (pipeValid : PipeFlags → Bool := PipeFlags.isValid)
    (encWait : WaitFlags → UInt64 := WaitFlags.toBits)
    (waitValid : WaitFlags → Bool := WaitFlags.isValid)
    (encSig : Signal → UInt8 × Int32 := Signal.toRaw)
    (sigNum : Signal → Int := Signal.toLinuxNum)
    (sigValid : Signal → Bool := Signal.isValid)
    (encPidfdOpen : PidfdOpenFlags → UInt64 := PidfdOpenFlags.toBits)
    (pidfdOpenValid : PidfdOpenFlags → Bool := PidfdOpenFlags.isValid)
    (encPidfdSig : PidfdSignalFlags → UInt64 := PidfdSignalFlags.toBits)
    (pidfdSigValid : PidfdSignalFlags → Bool := PidfdSignalFlags.isValid) : runner Unit := do
  let pf1 ← nondet PipeFlags
  let pf2 ← nondet PipeFlags
  NondetTest.assert ((encPipe pf1 == encPipe pf2) = (pf1 == pf2))
  NondetTest.assert (encPipe pf1 =
    ((if pf1.cloexec then (1 : UInt64) else 0) |||
     (if pf1.nonblock then (2 : UInt64) else 0) |||
     (if pf1.direct then (4 : UInt64) else 0) |||
     (if pf1.notificationPipe then (8 : UInt64) else 0) |||
     (pf1.extraBits.toUInt64 <<< 4)))
  NondetTest.assert (pipeValid pf1 = (pf1.extraBits == 0))
  let wf1 ← nondet WaitFlags
  let wf2 ← nondet WaitFlags
  NondetTest.assert ((encWait wf1 == encWait wf2) = (wf1 == wf2))
  NondetTest.assert (encWait wf1 =
    ((if wf1.nohang then (1 : UInt64) else 0) |||
     (if wf1.untraced then (2 : UInt64) else 0) |||
     (if wf1.continued then (4 : UInt64) else 0) |||
     (if wf1.wall then (8 : UInt64) else 0) |||
     (if wf1.wclone then (16 : UInt64) else 0) |||
     (if wf1.wnothread then (32 : UInt64) else 0) |||
     (wf1.extraBits.toUInt64 <<< 6)))
  NondetTest.assert (waitValid wf1 = (wf1.extraBits == 0))
  let s1 ← nondet Signal
  let s2 ← nondet Signal
  NondetTest.assert ((encSig s1 == encSig s2) = (s1 == s2))
  NondetTest.assert (encSig s1 =
    (match s1 with
     | .sigzero => (0, 0)
     | .sighup => (1, 0)
     | .sigint => (2, 0)
     | .sigkill => (3, 0)
     | .sigusr1 => (4, 0)
     | .sigusr2 => (5, 0)
     | .sigterm => (6, 0)
     | .sigcont => (7, 0)
     | .sigstop => (8, 0)
     | .raw n => (9, n)))
  NondetTest.assert (sigNum s1 =
    (match s1 with
     | .sigzero => 0
     | .sighup => 1
     | .sigint => 2
     | .sigkill => 9
     | .sigusr1 => 10
     | .sigusr2 => 12
     | .sigterm => 15
     | .sigcont => 18
     | .sigstop => 19
     | .raw n => n.toInt))
  NondetTest.assert (sigValid s1 = decide (0 ≤ sigNum s1 ∧ sigNum s1 ≤ 64))
  let po1 ← nondet PidfdOpenFlags
  let po2 ← nondet PidfdOpenFlags
  NondetTest.assert ((encPidfdOpen po1 == encPidfdOpen po2) = (po1 == po2))
  NondetTest.assert (encPidfdOpen po1 =
    ((if po1.nonblock then (1 : UInt64) else 0) |||
     (if po1.thread then (2 : UInt64) else 0) |||
     (po1.extraBits.toUInt64 <<< 2)))
  NondetTest.assert (pidfdOpenValid po1 = (po1.extraBits == 0))
  let ps1 ← nondet PidfdSignalFlags
  let ps2 ← nondet PidfdSignalFlags
  NondetTest.assert ((encPidfdSig ps1 == encPidfdSig ps2) = (ps1 == ps2))
  NondetTest.assert (encPidfdSig ps1 =
    ((if ps1.thread then (1 : UInt64) else 0) |||
     (if ps1.threadGroup then (2 : UInt64) else 0) |||
     (if ps1.processGroup then (4 : UInt64) else 0) |||
     (ps1.extraBits.toUInt64 <<< 3)))
  NondetTest.assert (pidfdSigValid ps1 =
    (ps1.extraBits == 0 &&
     decide (((if ps1.thread then 1 else 0) +
              (if ps1.threadGroup then 1 else 0) +
              (if ps1.processGroup then 1 else 0)) ≤ 1)))

/-- `WaitResult.ofRawWait4` universally decodes `rcPid <= 0` (`WNOHANG`), `WIFEXITED`/`WEXITSTATUS`, `WIFSIGNALED`/`WTERMSIG`/`WCOREDUMP`, `WIFSTOPPED`/`WSTOPSIG`, and `WIFCONTINUED` (`0xffff`) across arbitrary `rcPid`, status payloads, and upper 16-bit status words. -/
def test_process_waitResult_ofRawWait4_decodesAllStatuses
    {runner} [NondetTest runner]
    (decode : RawWaitTuple → WaitResult := WaitResult.ofRawWait4) : runner Unit := do
  let nonPosPid ← nondet Int32
  assume (nonPosPid <= 0)
  let posPid ← nondet Int32
  assume (posPid > 0)
  let rawSt ← nondet UInt32
  let code ← nondet UInt8
  let termSig ← nondet UInt8
  assume (1 ≤ termSig ∧ termSig ≤ 126)
  let core ← nondet Bool
  let stopSig ← nondet UInt8
  let upper ← nondet UInt16
  let hi : UInt32 := upper.toUInt32 <<< 16
  NondetTest.assert (decode (nonPosPid, rawSt) = .stillRunning)
  NondetTest.assert (decode (posPid, hi ||| (code.toUInt32 <<< 8)) =
    .exited posPid.toUInt32 code)
  NondetTest.assert (decode (posPid,
      hi ||| (code.toUInt32 <<< 8) ||| (if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32) =
    .signaled posPid.toUInt32 termSig.toUInt32 core)
  NondetTest.assert (decode (posPid, hi ||| (stopSig.toUInt32 <<< 8) ||| 0x7f) =
    .stopped posPid.toUInt32 stopSig.toUInt32)
  NondetTest.assert (decode (posPid, hi ||| 0xffff) =
    .continued posPid.toUInt32)

/-- `Internal.mkProcessOps` rejects NPTL-reserved signals `32`/`33` (`Signal.isNptlReserved`) with `EINVAL` before calling C, forwards exact encoded flag masks and `(tag, arg)` signal pairs to all 7 `PosixProcessOpsM` hooks in `StateM Nat`, decodes `waitpid` tuples via `WaitResult.ofRawWait4`, and propagates `.error err` outcomes unchanged. -/
def test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4
    {runner} [NondetTest runner]
    (mkOps : PosixProcessOpsM (StateM Nat) Nat → ProcessOpsM (StateM Nat) Nat) : runner Unit := do
  let pf ← nondet PipeFlags
  let wpid ← nondet Int32
  let wf ← nondet WaitFlags
  let rawTuple ← nondet RawWaitTuple
  let kpid ← nondet Int32
  let sig ← nondet Signal
  let opid ← nondet UInt32
  let pof ← nondet PidfdOpenFlags
  let pfd ← nondet Nat
  let psig ← nondet Signal
  let psf ← nondet PidfdSignalFlags
  let myPid ← nondet UInt32
  let myUid ← nondet UInt32
  let err ← nondet Errno
  let n0 ← nondet Nat
  let rawOk : PosixProcessOpsM (StateM Nat) Nat :=
    { pipe2 := fun bits => do
        modify (· + 1)
        if bits == pf.toBits then return .ok (pfd + 1, pfd + 2)
        else return .error Errno.EINVAL
      waitpid := fun pid bits => do
        modify (· + 10)
        if pid == wpid && bits == wf.toBits then return .ok rawTuple
        else return .error Errno.EINVAL
      kill := fun pid tag arg => do
        modify (· + 100)
        if pid == kpid && (tag, arg) == sig.toRaw then return .ok ()
        else return .error Errno.EINVAL
      pidfd_open := fun pid bits => do
        modify (· + 1000)
        if pid == opid && bits == pof.toBits then return .ok (pfd + 3)
        else return .error Errno.EINVAL
      pidfd_send_signal := fun fd tag arg bits => do
        modify (· + 10000)
        if fd == pfd && (tag, arg) == psig.toRaw && bits == psf.toBits then return .ok ()
        else return .error Errno.EINVAL
      getpid := do
        modify (· + 100000)
        return .ok myPid
      getuid := do
        modify (· + 1000000)
        return .ok myUid }
  let opsOk := mkOps rawOk
  NondetTest.assert ((opsOk.pipe2 pf).run n0 = (.ok (pfd + 1, pfd + 2), n0 + 1))
  NondetTest.assert ((opsOk.waitpid wpid wf).run n0 = (.ok (WaitResult.ofRawWait4 rawTuple), n0 + 10))
  NondetTest.assert ((opsOk.kill kpid sig).run n0 =
    if sig.isNptlReserved then (.error Errno.EINVAL, n0) else (.ok (), n0 + 100))
  NondetTest.assert ((opsOk.pidfd_open opid pof).run n0 = (.ok (pfd + 3), n0 + 1000))
  NondetTest.assert ((opsOk.pidfd_send_signal pfd psig psf).run n0 =
    if psig.isNptlReserved then (.error Errno.EINVAL, n0) else (.ok (), n0 + 10000))
  NondetTest.assert (opsOk.getpid.run n0 = (.ok myPid, n0 + 100000))
  NondetTest.assert (opsOk.getuid.run n0 = (.ok myUid, n0 + 1000000))
  let rawErr : PosixProcessOpsM (StateM Nat) Nat :=
    { pipe2 := fun _ => do modify (· + 1); return .error err
      waitpid := fun _ _ => do modify (· + 10); return .error err
      kill := fun _ _ _ => do modify (· + 100); return .error err
      pidfd_open := fun _ _ => do modify (· + 1000); return .error err
      pidfd_send_signal := fun _ _ _ _ => do modify (· + 10000); return .error err
      getpid := pure (.error err)
      getuid := pure (.error err) }
  let opsErr := mkOps rawErr
  NondetTest.assert ((opsErr.pipe2 pf).run n0 = (.error err, n0 + 1))
  NondetTest.assert ((opsErr.waitpid wpid wf).run n0 = (.error err, n0 + 10))
  NondetTest.assert ((opsErr.kill kpid sig).run n0 =
    if sig.isNptlReserved then (.error Errno.EINVAL, n0) else (.error err, n0 + 100))
  NondetTest.assert ((opsErr.pidfd_open opid pof).run n0 = (.error err, n0 + 1000))
  NondetTest.assert ((opsErr.pidfd_send_signal pfd psig psf).run n0 =
    if psig.isNptlReserved then (.error Errno.EINVAL, n0) else (.error err, n0 + 10000))
  NondetTest.assert (opsErr.getpid.run n0 = (.error err, n0))
  NondetTest.assert (opsErr.getuid.run n0 = (.error err, n0))

/-- `pipe2` rejects unsupported flag bits (`extraBits != 0`) with `Errno.EINVAL` leaving state unchanged, and on valid `O_CLOEXEC`/`O_NONBLOCK` combinations allocates pairwise-distinct `(readFd, writeFd)` handles across repeated calls. -/
def test_process_ops_pipe2_flagsAndDistinctHandles
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ ← nondet ProcessSysState
  let badFlags ← nondet PipeFlags
  assume (badFlags.extraBits != 0)
  NondetTest.assert ((ops.pipe2 badFlags).run s₀ = (.error Errno.EINVAL, s₀))
  let (r1, s₁) := (ops.pipe2 { cloexec := true, nonblock := false }).run s₀
  match r1 with
  | .error _ => NondetTest.assert False
  | .ok (rd1, wr1) =>
    NondetTest.assert (rd1 ≠ wr1)
    NondetTest.assert (assocGet s₁.fds rd1 = some (.pipeRead true false))
    NondetTest.assert (assocGet s₁.fds wr1 = some (.pipeWrite true false))
    let (r2, s₂) := (ops.pipe2 { cloexec := false, nonblock := true }).run s₁
    match r2 with
    | .error _ => NondetTest.assert False
    | .ok (rd2, wr2) =>
      NondetTest.assert (rd2 ≠ wr2 ∧ rd1 ≠ rd2 ∧ rd1 ≠ wr2 ∧ wr1 ≠ rd2 ∧ wr1 ≠ wr2)
      NondetTest.assert (assocGet s₂.fds rd2 = some (.pipeRead false true))
      NondetTest.assert (assocGet s₂.fds wr2 = some (.pipeWrite false true))

/-- `getpid` and `getuid` return `.ok` with positive bounded `effectiveSelfPid s₀` (`1 <= pid <= 0x7fffffff`) and `s₀.selfUid` without mutating state, and remain constant across arbitrary intervening `pipe2`, `kill`, and `pidfd_open` calls. -/
def test_process_ops_getpidAndGetuid_consistentAndPositive
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ ← nondet ProcessSysState
  let (rPid₁, s₁) := ops.getpid.run s₀
  let (rUid₁, s₂) := ops.getuid.run s₁
  match rPid₁ with
  | .error _ => NondetTest.assert False
  | .ok pid₁ =>
    NondetTest.assert (1 ≤ pid₁ ∧ pid₁ ≤ maxLinuxPid ∧ pid₁ = effectiveSelfPid s₀ ∧ s₁ = s₀)
    match rUid₁ with
    | .error _ => NondetTest.assert False
    | .ok uid₁ =>
      NondetTest.assert (uid₁ = s₀.selfUid ∧ s₂ = s₀)
      let (_, s₃) := (ops.pipe2 {}).run s₂
      let (_, s₄) := (ops.kill pid₁.toInt32 .sigzero).run s₃
      let (_, s₅) := (ops.pidfd_open pid₁ { nonblock := true }).run s₄
      let (rPid₂, s₆) := ops.getpid.run s₅
      let (rUid₂, s₇) := ops.getuid.run s₆
      NondetTest.assert (rPid₂ = .ok pid₁ ∧ rUid₂ = .ok uid₁ ∧ s₆ = s₅ ∧ s₇ = s₅)

/-- `waitpid` validates option flags (`EINVAL`) before `INT32_MIN` (`ESRCH`) and child lookup (`ECHILD`), returns `.stillRunning` under `WNOHANG` and `EINTR` on blocking `waitpid` for controlled non-exiting children, and transitions exited zombies to `.reaped` so a second `waitpid` returns `ECHILD`. -/
def test_process_ops_waitpid_optionsWnohangAndExitedReap
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let sEmpty := ProcessSysState.initial 1000 1000 1000
  let (rBadOpt, sBadOpt) := (ops.waitpid Int32.minValue { extraBits := 1 }).run sEmpty
  NondetTest.assert (rBadOpt = .error Errno.EINVAL ∧ sBadOpt = sEmpty)
  let (rMin, sMin) := (ops.waitpid Int32.minValue {}).run sEmpty
  NondetTest.assert (rMin = .error Errno.ESRCH ∧ sMin = sEmpty)
  let (rNoChild, sNc) := (ops.waitpid (-1) {}).run sEmpty
  NondetTest.assert (rNoChild = .error Errno.ECHILD ∧ sNc = sEmpty)

  let sRun := sEmpty.spawnRunningChild 2001 2001
  let (rRunNh, sRunNh) := (ops.waitpid 2001 { nohang := true }).run sRun
  NondetTest.assert (rRunNh = .ok .stillRunning ∧ sRunNh = sRun)
  let (rRunBlk, sRunBlk) := (ops.waitpid 2001 { nohang := false }).run sRun
  NondetTest.assert (rRunBlk = .error Errno.EINTR ∧ sRunBlk = sRun)
  let (rWrongPgid, _) := (ops.waitpid (-3000) { nohang := true }).run sRun
  NondetTest.assert (rWrongPgid = .error Errno.ECHILD)

  let sEx := sEmpty.spawnZombieExited 2002 42 2002
  let (rReapEx, sReapedEx) := (ops.waitpid (-2002) { nohang := true }).run sEx
  NondetTest.assert (rReapEx = .ok (.exited 2002 42))
  let (rSecondEx, _) := (ops.waitpid 2002 { nohang := true }).run sReapedEx
  NondetTest.assert (rSecondEx = .error Errno.ECHILD)

/-- `waitpid` supports `WUNTRACED` (`.stopped` for `SIGSTOP` and `SIGTSTP = 20`) and `WCONTINUED` (`.continued`) without reaping the child, and transitions a `SIGKILL`-signaled child to `.reaped` so a subsequent `waitpid` returns `ECHILD`. -/
def test_process_ops_waitpid_stopContinueAndSignaledReap
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let sRun := ((ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2001 2001).spawnRunningChild 2003 2003
  let (rTstp, sTstp) := (ops.kill 2003 (.raw 20)).run sRun
  NondetTest.assert (rTstp = .ok ())
  let (rWaitTstp, _) := (ops.waitpid 2003 { nohang := true, untraced := true }).run sTstp
  NondetTest.assert (rWaitTstp = .ok (.stopped 2003 20))
  let (rStopKill, sStopped) := (ops.kill 2001 .sigstop).run sRun
  NondetTest.assert (rStopKill = .ok ())
  let (rStopNoFlag, _) := (ops.waitpid 2001 { nohang := true, untraced := false }).run sStopped
  NondetTest.assert (rStopNoFlag = .ok .stillRunning)
  let (rStopOk, sStopRep) := (ops.waitpid 2001 { nohang := true, untraced := true }).run sStopped
  NondetTest.assert (rStopOk = .ok (.stopped 2001 19))
  let (rStopAgain, _) := (ops.waitpid 2001 { nohang := true, untraced := true }).run sStopRep
  NondetTest.assert (rStopAgain = .ok .stillRunning)
  let (rContKill, sCont) := (ops.kill 2001 .sigcont).run sStopRep
  NondetTest.assert (rContKill = .ok ())
  let (rContOk, sAfterCont) := (ops.waitpid 2001 { nohang := true, continued := true }).run sCont
  NondetTest.assert (rContOk = .ok (.continued 2001))
  let (rKill9, sKilled) := (ops.kill 2001 .sigkill).run sAfterCont
  NondetTest.assert (rKill9 = .ok ())
  let (rReapSig, sReapedSig) := (ops.waitpid 2001 {}).run sKilled
  NondetTest.assert (rReapSig = .ok (.signaled 2001 9 false))
  let (rSecondSig, _) := (ops.waitpid 2001 {}).run sReapedSig
  NondetTest.assert (rSecondSig = .error Errno.ECHILD)

/-- Non-`SIGKILL` fatal signals sent to a `TASK_STOPPED` child remain queued (`waitpid` returns `.stillRunning`) until `SIGCONT` wakes the child to deliver the queued fatal signal under both `WNOHANG` and blocking `waitpid`. -/
def test_process_ops_waitpid_queuedFatalAcrossSigcont
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let sStopped := (ProcessSysState.initial 1000 1000 1000).spawnStoppedChild 2005 19 true 2005
  let (rQueueTerm, sQueued) := (ops.kill 2005 .sigterm).run sStopped
  NondetTest.assert (rQueueTerm = .ok ())
  let (rWhileStopped, _) :=
    (ops.waitpid 2005 { nohang := true, untraced := true, continued := true }).run sQueued
  NondetTest.assert (rWhileStopped = .ok .stillRunning)
  let (rWake, sWoken) := (ops.kill 2005 .sigcont).run sQueued
  NondetTest.assert (rWake = .ok ())
  let (rReapNh, _) := (ops.waitpid 2005 { nohang := true }).run sWoken
  NondetTest.assert (rReapNh = .ok (.signaled 2005 15 false))
  let (rReapBlk, sReaped) := (ops.waitpid 2005 { nohang := false }).run sWoken
  NondetTest.assert (rReapBlk = .ok (.signaled 2005 15 false))
  let (rAfterReap, _) := (ops.waitpid 2005 { nohang := true }).run sReaped
  NondetTest.assert (rAfterReap = .error Errno.ECHILD)

/-- `kill` enforces Linux `7.1.6` precedence (`ESRCH` on missing PID/PGID or `INT32_MIN` before `EINVAL`, `EINVAL` before `EPERM` on existing unowned targets, `EPERM` on unowned `-pgid`, `0` with no delivery when `kill(-1)` encounters only unowned `pid > 1` targets, `ESRCH` on `kill(-1)` when alone with self-threads), and treats default-ignored signals `{17, 23, 28}` (`SIGCHLD`, `SIGURG`, `SIGWINCH`) as no-ops. -/
def test_process_ops_kill_precedencePermissionsAndIgnoredSignals
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := ((ProcessSysState.initial 1000 1000 1000).registerForeignProc 1 1 false).spawnRunningChild 2010 5000
  let (rMinBad, _) := (ops.kill Int32.minValue (.raw 999)).run s₀
  NondetTest.assert (rMinBad = .error Errno.ESRCH)
  let (rMissBad, _) := (ops.kill 999999 (.raw 999)).run s₀
  NondetTest.assert (rMissBad = .error Errno.ESRCH)
  let (rMissPgidBad, _) := (ops.kill (-999999) (.raw 999)).run s₀
  NondetTest.assert (rMissPgidBad = .error Errno.ESRCH)
  let (rPid1BadSig, _) := (ops.kill 1 (.raw 999)).run s₀
  NondetTest.assert (rPid1BadSig = .error Errno.EINVAL)
  let (rNptl32, _) := (ops.kill 999999 (.raw 32)).run s₀
  NondetTest.assert (rNptl32 = .error Errno.EINVAL)
  let (rNptl33, _) := (ops.kill 2010 (.raw 33)).run s₀
  NondetTest.assert (rNptl33 = .error Errno.EINVAL)
  let (rPid1Zero, _) := (ops.kill 1 .sigzero).run s₀
  NondetTest.assert (rPid1Zero = .error Errno.EPERM)
  let (rPid1Term, _) := (ops.kill 1 .sigterm).run s₀
  NondetTest.assert (rPid1Term = .error Errno.EPERM)
  let sForeignOnly := (ProcessSysState.initial 1000 1000 1000).registerForeignProc 2 2 false
  let (rGrpZeroPerm, _) := (ops.kill (-2) .sigzero).run sForeignOnly
  let (rAllTermOk, sAfterAllTerm) := (ops.kill (-1) .sigterm).run sForeignOnly
  NondetTest.assert (rGrpZeroPerm = .error Errno.EPERM ∧ rAllTermOk = .ok () ∧ sAfterAllTerm = sForeignOnly)
  let sSelfThreadOnly := (ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 1001 1000
  let (rAllSelfOnly, _) := (ops.kill (-1) .sigzero).run sSelfThreadOnly
  NondetTest.assert (rAllSelfOnly = .error Errno.ESRCH)
  let (rIgn17, s₁) := (ops.kill 2010 (.raw 17)).run s₀
  let (rIgn23, s₂) := (ops.kill 2010 (.raw 23)).run s₁
  let (rIgn28, s₃) := (ops.kill 2010 (.raw 28)).run s₂
  NondetTest.assert (rIgn17 = .ok () ∧ rIgn23 = .ok () ∧ rIgn28 = .ok ())
  let (rStillAlive, _) := (ops.waitpid 2010 { nohang := true }).run s₃
  NondetTest.assert (rStillAlive = .ok .stillRunning)
  let (_, s₄) := (ops.kill 2010 .sigkill).run s₃
  let (rKilled9, _) := (ops.waitpid 2010 {}).run s₄
  NondetTest.assert (rKilled9 = .ok (.signaled 2010 9 false))

/-- `kill` treats `SIGZERO` as a side-effect-free existence/permission probe, preserves confirmed zombie status on fatal signals, rejects reaped PIDs with `ESRCH`, and delivers group signals via `-pgid`. -/
def test_process_ops_kill_sigzeroZombieAndProcessGroup
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := ((ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2010 5000).spawnZombieExited 2011 42 5000
  let (rZeroProbe, s₁) := (ops.kill 2010 .sigzero).run s₀
  NondetTest.assert (rZeroProbe = .ok () ∧ s₁ = s₀)
  let (rKillZombie, s₂) := (ops.kill 2011 .sigkill).run s₁
  NondetTest.assert (rKillZombie = .ok ())
  let (rReapZombie, s₃) := (ops.waitpid 2011 { nohang := true }).run s₂
  NondetTest.assert (rReapZombie = .ok (.exited 2011 42))
  let (rKillReaped, _) := (ops.kill 2011 .sigzero).run s₃
  NondetTest.assert (rKillReaped = .error Errno.ESRCH)
  let (rGroupTerm, s₄) := (ops.kill (-5000) .sigterm).run s₃
  NondetTest.assert (rGroupTerm = .ok ())
  let (rReap2010, _) := (ops.waitpid 2010 {}).run s₄
  NondetTest.assert (rReap2010 = .ok (.signaled 2010 15 false))

/-- `kill(child_non_leader_tid, sig)` routes signal delivery to the child's thread-group leader (`tgid`), and reaping `tgid` via `waitpid` also reaps its non-leader threads (`ESRCH` on subsequent `kill` and `pidfd_open`). -/
def test_process_ops_kill_nonLeaderThreadRoutesToTgidAndReaps
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := ((ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2020 6000)
    |>.registerNonLeaderThread 2021 2020 6000
  let (rKillChildTid, s₁) := (ops.kill 2021 .sigterm).run s₀
  NondetTest.assert (rKillChildTid = .ok ())
  let (rReapLeader, s₂) := (ops.waitpid 2020 {}).run s₁
  NondetTest.assert (rReapLeader = .ok (.signaled 2020 15 false))
  let (rTidAfterReap, _) := (ops.kill 2021 .sigzero).run s₂
  NondetTest.assert (rTidAfterReap = .error Errno.ESRCH)
  let (rPfdTidAfterReap, _) := (ops.pidfd_open 2021 {}).run s₂
  NondetTest.assert (rPfdTidAfterReap = .error Errno.ESRCH)

/-- `pidfd_open` validates flags (`EINVAL`) before `pid <= 0` (`0` and `0x80000000` -> `EINVAL`), returns `ESRCH` on missing PIDs and `ENOENT` on live non-leader threads, and succeeds on live, foreign (`PID 1`), and zombie thread-group leaders with distinct handles. -/
def test_process_ops_pidfdOpen_validationThreadAndZombie
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := ((((ProcessSysState.initial 1000 1000 1000).registerForeignProc 1 1 false).registerNonLeaderThread 1001 1000).spawnRunningChild 3001 6000).spawnZombieExited 3002 7 3002
  let (rBadFlags0, _) := (ops.pidfd_open 0 { extraBits := 1 }).run s₀
  NondetTest.assert (rBadFlags0 = .error Errno.EINVAL)
  let (rBadFlagsMiss, _) := (ops.pidfd_open 999999 { extraBits := 1 }).run s₀
  NondetTest.assert (rBadFlagsMiss = .error Errno.EINVAL)
  let (rPidZero, _) := (ops.pidfd_open 0 {}).run s₀
  NondetTest.assert (rPidZero = .error Errno.EINVAL)
  let (rPidNeg, _) := (ops.pidfd_open 0x80000000 {}).run s₀
  NondetTest.assert (rPidNeg = .error Errno.EINVAL)
  let (rPidMiss, _) := (ops.pidfd_open 0x7fffffff {}).run s₀
  NondetTest.assert (rPidMiss = .error Errno.ESRCH)
  let (rTid, _) := (ops.pidfd_open 1001 {}).run s₀
  NondetTest.assert (rTid = .error Errno.ENOENT)
  let (rOpen1, s₁) := (ops.pidfd_open 1 {}).run s₀
  let (rOpenZ, s₂) := (ops.pidfd_open 3002 { nonblock := true }).run s₁
  let (rOpenRun, _) := (ops.pidfd_open 3001 {}).run s₂
  match rOpen1, rOpenZ, rOpenRun with
  | .ok pfd1, .ok pfdZ, .ok pfdRun =>
    NondetTest.assert (pfdZ ≠ pfdRun ∧ pfdZ ≠ pfd1 ∧ pfdRun ≠ pfd1)
  | _, _, _ => NondetTest.assert False

/-- `pidfd_send_signal` enforces unallocated and closed-handle `EBADF` (even with invalid flags) and open non-pidfd `EINVAL`/`EBADF` precedence. -/
def test_process_ops_pidfdSendSignal_fdKindsAndFlags
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := ProcessSysState.initial 1000 1000 1000
  let (rUnallocFd, _) := (ops.pidfd_send_signal 99 .sigzero { extraBits := 1 }).run s₀
  NondetTest.assert (rUnallocFd = .error Errno.EBADF)
  let (rPipe, s₁) := (ops.pipe2 {}).run s₀
  match rPipe with
  | .error _ => NondetTest.assert False
  | .ok (pipeRd, _) =>
    let (rPipeBadFl, _) := (ops.pidfd_send_signal pipeRd .sigzero { thread := true, threadGroup := true }).run s₁
    NondetTest.assert (rPipeBadFl = .error Errno.EINVAL)
    let (rPipeValidFl, _) := (ops.pidfd_send_signal pipeRd .sigzero {}).run s₁
    NondetTest.assert (rPipeValidFl = .error Errno.EBADF)
    let s₁Closed := s₁.closeFd pipeRd
    let (rClosedBadFl, _) := (ops.pidfd_send_signal pipeRd .sigzero { extraBits := 1 }).run s₁Closed
    NondetTest.assert (rClosedBadFl = .error Errno.EBADF)

/-- `pidfd_send_signal` enforces `PID 1` `EINVAL`/`EPERM` precedence, empty-PGID `ESRCH`, and single-target post-reap `ESRCH` (`EINVAL` on invalid flags). -/
def test_process_ops_pidfdSendSignal_permissionsAndPostReap
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := (((ProcessSysState.initial 1000 1000 1000).registerForeignProc 1 1 false).spawnRunningChild 3001 6000).spawnZombieExited 3002 7 3002
  let (rOpen1, s₁) := (ops.pidfd_open 1 {}).run s₀
  let (rOpenZ, s₂) := (ops.pidfd_open 3002 { nonblock := true }).run s₁
  let (rOpenRun, s₃) := (ops.pidfd_open 3001 {}).run s₂
  match rOpen1, rOpenZ, rOpenRun with
  | .ok pfd1, .ok pfdZ, .ok pfdRun =>
    let (rPfd1BadSig, _) := (ops.pidfd_send_signal pfd1 (.raw 999) {}).run s₃
    NondetTest.assert (rPfd1BadSig = .error Errno.EINVAL)
    let (rPfd1Perm, _) := (ops.pidfd_send_signal pfd1 .sigzero {}).run s₃
    NondetTest.assert (rPfd1Perm = .error Errno.EPERM)
    let (rZZero, _) := (ops.pidfd_send_signal pfdZ .sigzero { processGroup := true }).run s₃
    NondetTest.assert (rZZero = .ok ())
    let (rEmptyPg, _) := (ops.pidfd_send_signal pfdRun .sigzero { processGroup := true }).run s₃
    NondetTest.assert (rEmptyPg = .error Errno.ESRCH)
    let (rSendHup, s₄) := (ops.pidfd_send_signal pfdRun .sighup {}).run s₃
    NondetTest.assert (rSendHup = .ok ())
    let (rReapRun, s₅) := (ops.waitpid 3001 {}).run s₄
    NondetTest.assert (rReapRun = .ok (.signaled 3001 1 false))
    let (rOpenReaped, _) := (ops.pidfd_open 3001 {}).run s₅
    NondetTest.assert (rOpenReaped = .error Errno.ESRCH)
    let (rSendReaped, _) := (ops.pidfd_send_signal pfdRun (.raw 999) {}).run s₅
    NondetTest.assert (rSendReaped = .error Errno.ESRCH)
    let (rSendReapedBadFl, _) := (ops.pidfd_send_signal pfdRun .sigzero { extraBits := 1 }).run s₅
    NondetTest.assert (rSendReapedBadFl = .error Errno.EINVAL)
  | _, _, _ => NondetTest.assert False

/-- `pidfd_send_signal` with `PIDFD_SIGNAL_PROCESS_GROUP` dispatches via `PIDTYPE_PGID` on the `pidfd`'s `PID`, succeeding when active members remain in `pgid == targetPid` even after the leader process itself was reaped or moved to another PGID, and returning `ESRCH` once the PGID becomes empty. -/
def test_process_ops_pidfdSendSignal_processGroupAfterLeaderReapOrMove
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let s₀ := (((ProcessSysState.initial 1000 1000 1000).spawnZombieExited 3010 0 3010).spawnRunningChild 3011 3010)
    |>.spawnRunningChild 3020 1000
    |>.spawnRunningChild 3021 3020
  let (rOpenLeader, s₁) := (ops.pidfd_open 3010 {}).run s₀
  let (rOpenMoved, s₂) := (ops.pidfd_open 3020 {}).run s₁
  match rOpenLeader, rOpenMoved with
  | .ok pfdLeader, .ok pfdMoved =>
    let (rReapLeader, s₃) := (ops.waitpid 3010 {}).run s₂
    NondetTest.assert (rReapLeader = .ok (.exited 3010 0))
    let (rBadSigPg, _) := (ops.pidfd_send_signal pfdLeader (.raw 999) { processGroup := true }).run s₃
    NondetTest.assert (rBadSigPg = .error Errno.EINVAL)
    let (rZeroPg, _) := (ops.pidfd_send_signal pfdLeader .sigzero { processGroup := true }).run s₃
    NondetTest.assert (rZeroPg = .ok ())
    let (rTermPg, s₄) := (ops.pidfd_send_signal pfdLeader .sigterm { processGroup := true }).run s₃
    NondetTest.assert (rTermPg = .ok ())
    let (rReapMember, s₅) := (ops.waitpid 3011 {}).run s₄
    NondetTest.assert (rReapMember = .ok (.signaled 3011 15 false))
    let (rEmptyAfterAllReaped, _) := (ops.pidfd_send_signal pfdLeader .sigzero { processGroup := true }).run s₅
    NondetTest.assert (rEmptyAfterAllReaped = .error Errno.ESRCH)

    let (rMovedPg, s₆) := (ops.pidfd_send_signal pfdMoved .sigterm { processGroup := true }).run s₅
    NondetTest.assert (rMovedPg = .ok ())
    let (rReap3021, s₇) := (ops.waitpid 3021 {}).run s₆
    NondetTest.assert (rReap3021 = .ok (.signaled 3021 15 false))
    let (rLeaderUntouched, _) := (ops.waitpid 3020 { nohang := true }).run s₇
    NondetTest.assert (rLeaderUntouched = .ok .stillRunning)
  | _, _ => NondetTest.assert False

/-- `Model.allowedStep` rejects aliased handles, enforces `selfPid` and `selfUid` from step 1 without mutating state, rejects `.stillRunning` without `WNOHANG`, rejects fabricated exits on controlled non-exiting children even when `!flags.nohang`, allows autonomous child exits under both `WNOHANG` and `!flags.nohang`, and rejects double-reaping. -/
def test_process_model_allowedStep_invariantsAndRejections
    {runner} [NondetTest runner]
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let s0 := (ProcessSysState.initial 1000 1000 500).registerNonLeaderThread 1001 1000
  NondetTest.assert ((step s0 (.pipe2 {}) (.piped 3 3)).isNone)
  NondetTest.assert ((step s0 (.pipe2 { extraBits := 1 }) (.piped 3 4)).isNone)
  NondetTest.assert ((step s0 (.pipe2 { extraBits := 1 }) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step s0 (.pipe2 {}) (.err Errno.EMFILE)).isSome)
  NondetTest.assert ((step s0 .getpid (.u32 0)).isNone)
  NondetTest.assert ((step s0 .getpid (.u32 0x80000000)).isNone)
  NondetTest.assert ((step s0 .getpid (.u32 4242)).isNone)
  NondetTest.assert (step s0 .getpid (.u32 1000) = some s0)
  NondetTest.assert ((step s0 .getpid (.err Errno.EACCES)).isNone)
  NondetTest.assert ((step s0 .getuid (.u32 777)).isNone)
  NondetTest.assert (step s0 .getuid (.u32 500) = some s0)
  NondetTest.assert ((step s0 .getuid (.err Errno.EACCES)).isNone)
  NondetTest.assert ((step s0 (.pidfd_open 1001 {}) (.opened 5)).isNone)
  NondetTest.assert ((step s0 (.pidfd_open 1001 {}) (.err Errno.ENOENT)).isSome)
  NondetTest.assert ((step { s0 with pidfdThreadSupported := false } (.pidfd_open 1001 {}) (.err Errno.EINVAL)).isSome)
  let sControlled := s0.spawnRunningChild 2050 2050
  NondetTest.assert ((step sControlled (.waitpid 2050 { nohang := false }) (.waited .stillRunning)).isNone)
  NondetTest.assert ((step sControlled (.waitpid 2050 { nohang := true }) (.waited .stillRunning)).isSome)
  NondetTest.assert ((step sControlled (.waitpid 2050 { nohang := false }) (.waited (.exited 2050 0))).isNone)
  NondetTest.assert ((step sControlled (.waitpid 2050 { nohang := false }) (.waited (.signaled 2050 9 false))).isNone)
  NondetTest.assert ((step sControlled (.waitpid 2050 { nohang := false, untraced := true }) (.waited (.stopped 2050 19))).isNone)
  let sAuto := s0.spawnAutonomousChild 2060 2060
  NondetTest.assert ((step sAuto (.waitpid 2060 { nohang := true }) (.waited (.exited 2060 7))).isSome)
  NondetTest.assert ((step sAuto (.waitpid 2060 { nohang := true }) (.waited (.signaled 2060 15 false))).isSome)
  match step sAuto (.waitpid 2060 { nohang := false }) (.waited (.exited 2060 0)) with
  | none => NondetTest.assert False
  | some sReaped =>
    NondetTest.assert ((step sReaped (.waitpid 2060 { nohang := false }) (.waited (.exited 2060 0))).isNone)
    NondetTest.assert ((step sReaped (.waitpid 2060 { nohang := false }) (.err Errno.ECHILD)).isSome)

/-- `Model.allowedStep` accurately captures Linux `7.1.6` SMP stop races (`SIGSTOP` + `WNOHANG | WUNTRACED`), seeded confirmed stops, and queued fatal signals across `SIGCONT` (including immediate `WCONTINUED` race before `do_exit`). -/
def test_process_model_allowedStep_stopRaceAndQueuedSigcont
    {runner} [NondetTest runner]
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let sBase := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2100 2100
  match step sBase (.kill 2100 .sigstop) .unit with
  | none => NondetTest.assert False
  | some sStopAsync =>
    NondetTest.assert ((step sStopAsync (.waitpid 2100 { nohang := true, untraced := true }) (.waited .stillRunning)).isSome)
    match step sStopAsync (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 19)) with
    | none => NondetTest.assert False
    | some sStopConfirmed =>
      match step sStopConfirmed (.kill 2100 .sigterm) .unit with
      | none => NondetTest.assert False
      | some sQueued =>
        NondetTest.assert ((step sQueued (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isNone)
        match step sQueued (.kill 2100 .sigcont) .unit with
        | none => NondetTest.assert False
        | some sWoken =>
          NondetTest.assert ((step sWoken (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isSome)
          NondetTest.assert ((step sWoken (.waitpid 2100 { nohang := false }) (.waited (.signaled 2100 15 false))).isSome)
          match step sWoken (.waitpid 2100 { nohang := true, continued := true }) (.waited (.continued 2100)) with
          | none => NondetTest.assert False
          | some sAfterContRace =>
            NondetTest.assert ((step sAfterContRace (.waitpid 2100 { nohang := false }) (.waited (.signaled 2100 15 false))).isSome)

  let sSeededStop := (ProcessSysState.initial 1000 1000 1000).spawnStoppedChild 2101 19 false 2101
  NondetTest.assert ((step sSeededStop (.waitpid 2101 { nohang := true, untraced := true }) (.waited .stillRunning)).isNone)

  match step sBase (.kill 2100 (.raw 20)) .unit with
  | none => NondetTest.assert False
  | some sTstp =>
    match step sTstp (.kill 2100 .sigstop) .unit with
    | none => NondetTest.assert False
    | some sTstpThenStop =>
      NondetTest.assert ((step sTstpThenStop (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 20))).isSome)
      NondetTest.assert ((step sTstpThenStop (.waitpid 2100 { nohang := true, untraced := true }) (.waited (.stopped 2100 19))).isSome)
    match step sTstp (.kill 2100 .sigterm) .unit with
    | none => NondetTest.assert False
    | some sTstpTerm =>
      NondetTest.assert ((step sTstpTerm (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isSome)
      NondetTest.assert ((step sTstpTerm (.waitpid 2100 { nohang := true }) (.waited .stillRunning)).isSome)

/-- `Model.allowedStep` accurately captures core-default `WCOREDUMP` outcomes (`SIGABRT = 6` vs `SIGKILL = 9` vs seeded `spawnZombieSignaled`), racing fatal signals while `asyncPending = true`, and preserved `autoExit?` race outcomes. -/
def test_process_model_allowedStep_coreDumpAndRacingSignals
    {runner} [NondetTest runner]
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let sBase := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2100 2100
  match step sBase (.kill 2100 (.raw 6)) .unit with
  | none => NondetTest.assert False
  | some sAbrt =>
    NondetTest.assert ((step sAbrt (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 6 false))).isSome)
    NondetTest.assert ((step sAbrt (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 6 true))).isSome)

  match step sBase (.kill 2100 .sigterm) .unit with
  | none => NondetTest.assert False
  | some sTerm1 =>
    match step sTerm1 (.kill 2100 .sigkill) .unit with
    | none => NondetTest.assert False
    | some sTermAndKill =>
      NondetTest.assert ((step sTermAndKill (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 15 false))).isSome)
      NondetTest.assert ((step sTermAndKill (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 9 false))).isSome)
      NondetTest.assert ((step sTermAndKill (.waitpid 2100 { nohang := true }) (.waited (.signaled 2100 9 true))).isNone)

  let sSeededZ := (ProcessSysState.initial 1000 1000 1000).spawnZombieSignaled 2102 6 false 2102
  NondetTest.assert ((step sSeededZ (.waitpid 2102 { nohang := true }) (.waited (.signaled 2102 6 false))).isSome)
  NondetTest.assert ((step sSeededZ (.waitpid 2102 { nohang := true }) (.waited (.signaled 2102 6 true))).isNone)

  let sPlanned := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2103 2103 (some (.exited 42))
  NondetTest.assert ((step sPlanned (.waitpid 2103 { nohang := true }) (.waited (.exited 2103 42))).isSome)
  NondetTest.assert ((step sPlanned (.waitpid 2103 { nohang := true }) (.waited (.exited 2103 99))).isNone)
  match step sPlanned (.kill 2103 .sigterm) .unit with
  | none => NondetTest.assert False
  | some sPlannedRaced =>
    NondetTest.assert ((step sPlannedRaced (.waitpid 2103 { nohang := true }) (.waited (.exited 2103 42))).isSome)
    NondetTest.assert ((step sPlannedRaced (.waitpid 2103 { nohang := true }) (.waited (.signaled 2103 15 false))).isSome)
    NondetTest.assert ((step sPlannedRaced (.waitpid 2103 { nohang := true }) (.waited (.exited 2103 99))).isNone)

/-- Ambient `sigchldAutoreap` (`SIGCHLD = SIG_IGN` / `SA_NOCLDWAIT`) still reports `WUNTRACED` stops while auto-reaping terminated children (`ECHILD` on `waitpid` and transitioning the child to `.reaped` so subsequent `kill`/`pidfd_open` return `ESRCH`), and `ambientIgnoredSigs` (such as `nohup` `SIGHUP = 1`) ignores listed signals while keeping `SIGKILL = 9` and `SIGSTOP = 19` unignorable. -/
def test_process_ops_ambientSigchldAutoreapAndIgnoredSigs
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let sAuto := ((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true).spawnRunningChild 2200 2200
  let (_, sStop) := (ops.kill 2200 .sigstop).run sAuto
  let (rWaitStop, sRep) := (ops.waitpid 2200 { nohang := true, untraced := true }).run sStop
  NondetTest.assert (rWaitStop = .ok (.stopped 2200 19))
  let (_, sKilled) := (ops.kill 2200 .sigkill).run sRep
  let (rWaitKilledNh, _) := (ops.waitpid 2200 { nohang := true }).run sKilled
  NondetTest.assert (rWaitKilledNh = .error Errno.ECHILD)
  let (rWaitKilledBlk, sAutoReaped) := (ops.waitpid 2200 { nohang := false }).run sKilled
  NondetTest.assert (rWaitKilledBlk = .error Errno.ECHILD)
  let (rKillAfterAutoreap, _) := (ops.kill 2200 .sigzero).run sAutoReaped
  NondetTest.assert (rKillAfterAutoreap = .error Errno.ESRCH)
  let (rPfdAfterAutoreap, _) := (ops.pidfd_open 2200 {}).run sAutoReaped
  NondetTest.assert (rPfdAfterAutoreap = .error Errno.ESRCH)

  let sNohup := ((ProcessSysState.initial 1000 1000 1000).withAmbientIgnoredSigs [1, 9, 19]).spawnRunningChild 2201 2201
  let (_, sAfterHup) := (ops.kill 2201 .sighup).run sNohup
  let (rAfterHup, _) := (ops.waitpid 2201 { nohang := true }).run sAfterHup
  NondetTest.assert (rAfterHup = .ok .stillRunning)
  let (_, sAfterStop) := (ops.kill 2201 .sigstop).run sAfterHup
  let (rAfterStop, sStopRep) := (ops.waitpid 2201 { nohang := true, untraced := true }).run sAfterStop
  NondetTest.assert (rAfterStop = .ok (.stopped 2201 19))
  let (_, sAfterKill) := (ops.kill 2201 .sigkill).run sStopRep
  let (rAfterKill, _) := (ops.waitpid 2201 {}).run sAfterKill
  NondetTest.assert (rAfterKill = .ok (.signaled 2201 9 false))

/-- Under `sigchldAutoreap = true`, `allowedStep` rejects `.exited`/`.signaled` on non-seeded children, reaps autoreapable children on `ECHILD` or observed `ESRCH` so they cannot resurrect, and rejects `ESRCH` on `selfPid`, `kill(0, ...)`, `selfPidfd`, and controlled live children. -/
def test_process_model_allowedStep_sigchldAutoreapPrecision
    {runner} [NondetTest runner]
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let s0 := (((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true)
    |>.spawnRunningChild 2210 2210)
    |>.spawnAutonomousChild 2211 2211
    |>.spawnZombieExited 2212 5 2212
  match step s0 (.pidfd_open 1000 {}) (.opened 0) with
  | none => NondetTest.assert False
  | some sWithSelfPfd =>
    NondetTest.assert ((step sWithSelfPfd (.pidfd_open 1000 {}) (.err Errno.ESRCH)).isNone)
    NondetTest.assert ((step sWithSelfPfd (.kill 1000 .sigzero) (.err Errno.ESRCH)).isNone)
    NondetTest.assert ((step sWithSelfPfd (.kill 0 .sigzero) (.err Errno.ESRCH)).isNone)
    NondetTest.assert ((step sWithSelfPfd (.pidfd_send_signal 0 .sigzero {}) (.err Errno.ESRCH)).isNone)
    NondetTest.assert ((step sWithSelfPfd (.kill 2210 .sigzero) (.err Errno.ESRCH)).isNone)
    NondetTest.assert ((step sWithSelfPfd (.waitpid 2211 { nohang := true }) (.waited (.exited 2211 0))).isNone)
    NondetTest.assert ((step sWithSelfPfd (.waitpid 2212 { nohang := true }) (.waited (.exited 2212 5))).isSome)
    match step sWithSelfPfd (.kill 2211 .sigzero) (.err Errno.ESRCH) with
    | none => NondetTest.assert False
    | some sAfterEsrch =>
      NondetTest.assert ((step sAfterEsrch (.kill 2211 .sigzero) .unit).isNone)
      NondetTest.assert ((step sAfterEsrch (.pidfd_open 2211 {}) (.opened 1)).isNone)
    let sDyingAuto := ((ProcessSysState.initial 1000 1000 1000).spawnAutonomousChild 2213 2213).withSigchldAutoreap true
    NondetTest.assert ((step sDyingAuto (.waitpid 2213 { nohang := true }) (.waited (.exited 2213 0))).isSome)
    NondetTest.assert ((step sDyingAuto (.waitpid 2213 { nohang := true }) (.err Errno.ECHILD)).isSome)
    let sToggleBack := (((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true).spawnRunningChild 2214 2214).withSigchldAutoreap false
    match step sToggleBack (.kill 2214 .sigkill) .unit with
    | none => NondetTest.assert False
    | some sToggleKilled =>
      NondetTest.assert ((step sToggleKilled (.waitpid 2214 { nohang := true }) (.err Errno.ECHILD)).isNone)
      NondetTest.assert ((step sToggleKilled (.waitpid 2214 { nohang := true }) (.waited (.signaled 2214 9 false))).isSome)
    let sSecAuto := s0.withAmbientSeccomp true
    NondetTest.assert (step sSecAuto (.waitpid (-1) {}) (.err Errno.EPERM) = some sSecAuto)

/-- Inside `CLONE_NEWPID`, `registerPid1Init` (`SIGNAL_UNKILLABLE`) ignores uncaught `SIGKILL` and `SIGSTOP` while returning `.ok ()`, and pre-`setsid()` outer-namespace `selfPgid = 0` succeeds on `kill(0, .sigzero)`, reaps `pgid = 0` children on `waitpid(0, ...)`, and returns `ESRCH` on `pidfd_send_signal(pfdSelf1, ..., { processGroup := true })`. -/
def test_process_ops_pidNamespaceUnkillableInitAndZeroPgid
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps) : runner Unit := do
  let sChild2 := (ProcessSysState.initial 2 1 1000).registerPid1Init 1 true
  let (rKill1_9, s1) := (ops.kill 1 .sigkill).run sChild2
  NondetTest.assert (rKill1_9 = .ok () ∧ s1 = sChild2)
  let (rKill1_19, s2) := (ops.kill 1 .sigstop).run s1
  NondetTest.assert (rKill1_19 = .ok () ∧ s2 = sChild2)
  let (rOpen1, s3) := (ops.pidfd_open 1 {}).run s2
  match rOpen1 with
  | .error _ => NondetTest.assert False
  | .ok pfd1 =>
    let (rPfd1_9, s4) := (ops.pidfd_send_signal pfd1 .sigkill {}).run s3
    NondetTest.assert (rPfd1_9 = .ok () ∧ s4 = s3)
    let (rProbe1, s5) := (ops.kill 1 .sigzero).run s4
    NondetTest.assert (rProbe1 = .ok () ∧ s5 = s3)

  let sPid1ZeroPgid := (ProcessSysState.initial 1 0 65534).spawnZombieExited 2 7 0
  let (rKillZero, sZ1) := (ops.kill 0 .sigzero).run sPid1ZeroPgid
  NondetTest.assert (rKillZero = .ok ())
  let (rOpenSelf1, sZ2) := (ops.pidfd_open 1 {}).run sZ1
  match rOpenSelf1 with
  | .error _ => NondetTest.assert False
  | .ok pfdSelf1 =>
    let (rPfdPg, sZ3) := (ops.pidfd_send_signal pfdSelf1 .sigzero { processGroup := true }).run sZ2
    NondetTest.assert (rPfdPg = .error Errno.ESRCH)
    let (rWaitZero, _) := (ops.waitpid 0 { nohang := true }).run sZ3
    NondetTest.assert (rWaitZero = .ok (.exited 2 7))

/-- On shared open hosts (`withOpenHostPids true`), `allowedStep` permits `pidfd_open`/`kill` outcomes on untracked host leaders (`kthreadd` `PID 2`), worker threads (`ENOENT`, or `EINVAL` when `!pidfdThreadSupported`), and LSM `EACCES`, and under `withAmbientSeccomp true` permits safe synthesized `Errno`s (`!= EFAULT`, `1..4095`) across all 7 fallible syscalls without mutating state. -/
def test_process_model_allowedStep_openHostPidsAndAmbientSeccomp
    {runner} [NondetTest runner]
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let sHost := (ProcessSysState.initial 1000 1000 1000).withOpenHostPids true
  NondetTest.assert ((step sHost (.pidfd_open 9999 {}) (.err Errno.ENOENT)).isSome)
  NondetTest.assert ((step { sHost with pidfdThreadSupported := false } (.pidfd_open 9999 {}) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step sHost (.kill 2 .sigzero) (.err Errno.EPERM)).isSome)
  NondetTest.assert ((step sHost (.kill 2 .sigzero) (.err Errno.EACCES)).isSome)
  NondetTest.assert ((step sHost (.kill (-1) .sigzero) .unit).isSome)
  NondetTest.assert ((step sHost (.kill 2 (.raw 999)) (.err Errno.EINVAL)).isSome)
  NondetTest.assert ((step sHost (.kill 2 (.raw 999)) .unit).isNone)
  match step sHost (.pidfd_open 2 {}) (.opened 0) with
  | none => NondetTest.assert False
  | some sHostWithPfd2 =>
    NondetTest.assert ((step sHostWithPfd2 (.pidfd_send_signal 0 .sigzero {}) (.err Errno.EPERM)).isSome)
    NondetTest.assert ((step sHostWithPfd2 (.pidfd_send_signal 0 .sigzero {}) (.err Errno.EACCES)).isSome)
    NondetTest.assert ((step sHostWithPfd2 (.pidfd_send_signal 0 (.raw 999) {}) (.err Errno.EINVAL)).isSome)

  let sSec := (ProcessSysState.initial 1000 1000 1000).withAmbientSeccomp true
  let sSecPfd := commitPidfd sSec 0 1000 false
  NondetTest.assert (step sSec (.pipe2 {}) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.waitpid (-1) {}) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.kill 1000 .sigzero) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.pidfd_open 1000 {}) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSecPfd (.pidfd_send_signal 0 .sigzero {}) (.err Errno.EPERM) = some sSecPfd)
  NondetTest.assert ((step sSec (.pipe2 {}) (.err Errno.EFAULT)).isNone)
  NondetTest.assert ((step sSec (.pipe2 {}) (.err 0)).isNone)
  NondetTest.assert (step sSec .getpid (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec .getuid (.err Errno.EPERM) = some sSec)
  NondetTest.assert ((step sSec .getpid (.err Errno.EFAULT)).isNone)
  NondetTest.assert ((step sHost (.pidfd_open 9999 {}) (.err Errno.EINVAL)).isNone)
  let sHostSelfPfd := commitPidfd sHost 0 1000 false
  NondetTest.assert ((step sHostSelfPfd (.pidfd_send_signal 0 .sigzero { processGroup := true }) (.err Errno.ESRCH)).isNone)
  NondetTest.assert ((step sHostSelfPfd (.pidfd_send_signal 0 .sigzero { processGroup := true }) .unit).isSome)
  NondetTest.assert ((step sSec (.kill 1000 (.raw 32)) (.err Errno.EPERM)).isNone)
  NondetTest.assert ((step sSec (.pidfd_send_signal 99 .sigzero {}) (.err Errno.EPERM)).isNone)
  let sKillStop := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2300 2300
  match step sKillStop (.kill 2300 .sigkill) .unit with
  | none => NondetTest.assert False
  | some sK9 =>
    match step sK9 (.kill 2300 .sigstop) .unit with
    | none => NondetTest.assert False
    | some sK9Stop =>
      NondetTest.assert ((step sK9Stop (.waitpid 2300 { nohang := true, untraced := true }) (.waited (.stopped 2300 19))).isNone)
  let sZCont := (ProcessSysState.initial 1000 1000 1000).spawnZombieSignaled 2301 6 false 2301
  match step sZCont (.kill 2301 .sigcont) .unit with
  | none => NondetTest.assert False
  | some sZAfterCont =>
    NondetTest.assert ((step sZAfterCont (.waitpid 2301 { nohang := true, continued := true }) (.waited (.continued 2301))).isNone)

/-- Universal soundness: for every `ProcessSysState` and every `ProcessReq`, `modelOps` produces an outcome and next state accepted identically by `allowedStep`. -/
def test_process_model_modelOpsSoundForAllowedStep
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps)
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let s ← nondet ProcessSysState
  let req ← nondet ProcessReq
  let (out, s') := (execProcessReq ops req).run s
  NondetTest.assert (step s req out = some s')

/-- Structural wiring promise: `Interface.defaultOps` is constructed via `Internal.mkProcessOps` and every top-level wrapper in `Interface` (both with explicit arguments and with default `optParam` flag values) delegates directly to `defaultOps`, so NPTL `32`/`33` guards, flag encoders, default `FD_CLOEXEC`, and `WaitResult.ofRawWait4` decoding cannot be bypassed. -/
def test_process_interface_defaultOpsWiring
    {runner} [NondetTest runner]
    (mkOps : PosixProcessOps → ProcessOps)
    (ops : ProcessOps)
    (wPipe2 : PipeFlags → IO (Except Errno (RawFd × RawFd)))
    (wPipe2Def : IO (Except Errno (RawFd × RawFd)))
    (wWaitpid : Int32 → WaitFlags → IO (Except Errno WaitResult))
    (wWaitpidDef : Int32 → IO (Except Errno WaitResult))
    (wKill : Int32 → Signal → IO (Except Errno Unit))
    (wPidfdOpen : UInt32 → PidfdOpenFlags → IO (Except Errno RawFd))
    (wPidfdOpenDef : UInt32 → IO (Except Errno RawFd))
    (wPidfdSend : RawFd → Signal → PidfdSignalFlags → IO (Except Errno Unit))
    (wPidfdSendDef : RawFd → Signal → IO (Except Errno Unit))
    (wGetpid : IO (Except Errno UInt32))
    (wGetuid : IO (Except Errno UInt32)) : runner Unit := do
  NondetTest.assert (∃ raw : PosixProcessOps, ops = mkOps raw)
  NondetTest.assert (∀ flags, wPipe2 flags = ops.pipe2 flags)
  NondetTest.assert (wPipe2Def = ops.pipe2 {})
  NondetTest.assert (∀ pid flags, wWaitpid pid flags = ops.waitpid pid flags)
  NondetTest.assert (∀ pid, wWaitpidDef pid = ops.waitpid pid {})
  NondetTest.assert (∀ pidOrNegPgid sig, wKill pidOrNegPgid sig = ops.kill pidOrNegPgid sig)
  NondetTest.assert (∀ pid flags, wPidfdOpen pid flags = ops.pidfd_open pid flags)
  NondetTest.assert (∀ pid, wPidfdOpenDef pid = ops.pidfd_open pid {})
  NondetTest.assert (∀ fd sig flags, wPidfdSend fd sig flags = ops.pidfd_send_signal fd sig flags)
  NondetTest.assert (∀ fd sig, wPidfdSendDef fd sig = ops.pidfd_send_signal fd sig {})
  NondetTest.assert (wGetpid = ops.getpid)
  NondetTest.assert (wGetuid = ops.getuid)

/-- Soundness and polymorphic `{m} [Monad m]` delegation promise for `Internal.mkProcessOps` covering both `IO` and `StateM`. -/
def test_process_impl_mkProcessOpsSound
    {runner} [NondetTest runner]
    (mkOps : {m : Type → Type} → [Monad m] → {fd : Type} → PosixProcessOpsM m fd → ProcessOpsM m fd) :
    runner Unit := do
  NondetTest.assert
    (∀ (raw : PosixProcessOpsM (StateM ProcessSysState) HandleId), RawPosixShimSound raw →
      ∀ (s : ProcessSysState) (req : ProcessReq),
        let r := (execProcessReq (mkOps raw) req).run s
        allowedStep s req r.1 = some r.2)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) (pf : PipeFlags),
      (mkOps raw).pipe2 pf = raw.pipe2 pf.toBits)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) (pid : Int32) (wf : WaitFlags),
      (mkOps raw).waitpid pid wf = do
        match ← raw.waitpid pid wf.toBits with
        | .ok t => return .ok (WaitResult.ofRawWait4 t)
        | .error e => return .error e)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) (pid : Int32) (sig : Signal),
      (mkOps raw).kill pid sig =
        if sig.isNptlReserved then pure (.error Errno.EINVAL) else raw.kill pid sig.toRaw.1 sig.toRaw.2)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) (pid : UInt32) (pof : PidfdOpenFlags),
      (mkOps raw).pidfd_open pid pof = raw.pidfd_open pid pof.toBits)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) (hid : fd) (sig : Signal) (psf : PidfdSignalFlags),
      (mkOps raw).pidfd_send_signal hid sig psf =
        if sig.isNptlReserved then pure (.error Errno.EINVAL) else raw.pidfd_send_signal hid sig.toRaw.1 sig.toRaw.2 psf.toBits)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd),
      (mkOps raw).getpid = raw.getpid)
  NondetTest.assert
    (∀ {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd),
      (mkOps raw).getuid = raw.getuid)

/-- Linux `7.1.6` `delay_group_leader` (`.delayedZombie`), thread-scoped vs group-scoped `pidfd_send_signal`, orphaned-PGID unblocked `SIGTSTP` drop, `PIDFD_THREAD`, and `esrch*Next` `.exitDead` pruning. -/
def test_process_model_delayedZombieThreadScopeOrphanAndExitDead
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps)
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let sDzBase : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 2001 2000 with
      procs := (2000, { pgid := 2000, role := .child .sigchld false, lifecycle := .delayedZombie (.exited 42) false [] }) ::
        ((ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 2001 2000).procs }
  let sDzFds := commitPidfd (commitPidfd sDzBase 0 2000 false false) 1 2000 false true
  let (wnh0, sDzAfterWnh) := (ops.waitpid 2000 { nohang := true }).run sDzFds
  NondetTest.assert (wnh0 = .ok .stillRunning)
  let (thrSigOut, sDzAfterThr) := (ops.pidfd_send_signal 0 .sigkill { thread := true }).run sDzAfterWnh
  NondetTest.assert (thrSigOut = .ok ())
  let (thrFdOut, sDzAfterThrFd) := (ops.pidfd_send_signal 1 .sigkill {}).run sDzAfterThr
  NondetTest.assert (thrFdOut = .ok ())
  NondetTest.assert ((step sDzAfterThrFd (.waitpid 2000 { nohang := false }) (.waited (.signaled 2000 9 false))).isNone)
  let (grpTermOut, sDzAfterTerm) := (ops.kill 2000 .sigterm).run sDzAfterThrFd
  NondetTest.assert (grpTermOut = .ok ())
  NondetTest.assert ((step sDzAfterTerm (.waitpid 2000 { nohang := false }) (.waited (.exited 2000 42))).isNone)
  let (blkAfterTerm, _) := (ops.waitpid 2000 { nohang := false }).run sDzAfterTerm
  NondetTest.assert (blkAfterTerm = .ok (.signaled 2000 15 false))
  let sDzStop0 := sDzFds
  let (dzStopOut, sDzStop1) := (ops.kill 2000 .sigstop).run sDzStop0
  NondetTest.assert (dzStopOut = .ok ())
  let (dzStopWait, sDzStop2) := (ops.waitpid 2000 { nohang := true, untraced := true }).run sDzStop1
  NondetTest.assert (dzStopWait = .ok (.stopped 2000 19))
  let (dzContOut, sDzStop3) := (ops.kill 2000 .sigcont).run sDzStop2
  NondetTest.assert (dzContOut = .ok ())
  let (dzContWait, sDzStop4) := (ops.waitpid 2000 { nohang := true, continued := true }).run sDzStop3
  NondetTest.assert (dzContWait = .ok (.continued 2000))
  let (dzTermOut, sDzStop5) := (ops.kill 2000 .sigterm).run sDzStop4
  NondetTest.assert (dzTermOut = .ok ())
  let (dzTermWait, _) := (ops.waitpid 2000 { nohang := false }).run sDzStop5
  NondetTest.assert (dzTermWait = .ok (.signaled 2000 15 false))
  let sDzIgn0 := sDzBase.withSigchldAutoreap true
  let (dzIgnKillOut, sDzIgn1) := (ops.kill 2000 .sigkill).run sDzIgn0
  NondetTest.assert (dzIgnKillOut = .ok ())
  let (dzIgnWait, _) := (ops.waitpid 2000 { nohang := false }).run sDzIgn1
  NondetTest.assert (dzIgnWait = .error Errno.ECHILD)
  let sDzDeadSub : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2000, { pgid := 2000, role := .child .sigchld false, lifecycle := .delayedZombie (.exited 42) false [] }),
                (2001, { pgid := 2000, role := .thread 2000, lifecycle := .exitDead })] }
  let (deadSubKill, sDzDeadSub1) := (ops.kill 2000 .sigkill).run sDzDeadSub
  NondetTest.assert (deadSubKill = .ok ())
  NondetTest.assert ((step sDzDeadSub1 (.waitpid 2000 { nohang := false }) (.waited (.exited 2000 42))).isSome)
  NondetTest.assert ((step sDzBase (.kill 2001 .sigzero) (.err Errno.ESRCH)).isNone)
  let sOrph0 := { ProcessSysState.initial 1000 1000 1000 with
    procs := [(2010, { pgid := 2010, orphanedPgid := true, role := .child .sigchld false, lifecycle := .alive ({ auto := .controlled } : AliveState) })] }
  let (stopOrphOut, sOrph1) := (ops.kill 2010 (.raw 20)).run sOrph0
  NondetTest.assert (stopOrphOut = .ok ())
  let eOrph1 := (assocGet sOrph1.procs 2010).getD { pgid := 2010, orphanedPgid := true, role := .child .sigchld false, lifecycle := .alive ({ auto := .controlled } : AliveState) }
  let sOrphMoved := { sOrph1 with procs := assocSet sOrph1.procs 2010 (eOrph1.setPgid 2011 false) }
  let (waitMovedOut, _) := (ops.waitpid 2010 { nohang := true, untraced := true }).run sOrphMoved
  NondetTest.assert (waitMovedOut = .ok .stillRunning)
  NondetTest.assert ((step sOrphMoved (.waitpid 2010 { nohang := true, untraced := true }) (.waited (.stopped 2010 20))).isSome)
  let sSelfThr := (ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 1001 1000
  NondetTest.assert ((step sSelfThr (.kill 1001 .sigzero) (.err Errno.ESRCH)).isNone)
  NondetTest.assert ((step sSelfThr (.pidfd_open 1001 { thread := true }) (.err Errno.ESRCH)).isNone)
  NondetTest.assert ((step sSelfThr (.pidfd_open 1001 { thread := false }) (.err Errno.ESRCH)).isNone)
  NondetTest.assert ((step sSelfThr (.pidfd_open 1001 { thread := false }) (.err Errno.ENOENT)).isSome)
  let sZDead : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).spawnZombieExited 2020 0 2020 with
      procs := (2021, { pgid := 2020, role := .thread 2020, lifecycle := .alive {} }) ::
        ((ProcessSysState.initial 1000 1000 1000).spawnZombieExited 2020 0 2020).procs }
  let (openDeadW, _) := (ops.pidfd_open 2021 { thread := true }).run sZDead
  let (killDeadW, _) := (ops.kill 2021 .sigzero).run sZDead
  NondetTest.assert (openDeadW = .error Errno.ESRCH ∧ killDeadW = .error Errno.ESRCH)
  let (zWnh, _) := (ops.waitpid 2020 { nohang := true }).run sZDead
  NondetTest.assert (zWnh = .ok (.exited 2020 0))
  let sEd : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2030, { pgid := 2030, role := .child .sigchld false, lifecycle := .exitDead })] }
  let sEdPfd := commitPidfd sEd 0 2030 false false
  NondetTest.assert (step sEd (.kill 2030 .sigzero) (.err Errno.ESRCH) = some (esrchKillNext sEd 2030))
  NondetTest.assert (step sEd (.pidfd_open 2030 {}) (.err Errno.ESRCH) = some (esrchPidfdOpenNext sEd 2030 {}))
  NondetTest.assert (step sEdPfd (.pidfd_send_signal 0 .sigzero {}) (.err Errno.ESRCH) = some (esrchPidfdSendNext sEdPfd 0 {}))
  let sNonLeadDead : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).spawnZombieExited 2040 0 2040 with
      procs := (2041, { pgid := 2040, role := .thread 2040, lifecycle := .alive {} }) ::
        ((ProcessSysState.initial 1000 1000 1000).spawnZombieExited 2040 0 2040).procs }
  NondetTest.assert (step sNonLeadDead (.kill 2041 .sigzero) (.err Errno.ESRCH) = some (esrchKillNext sNonLeadDead 2041))
  NondetTest.assert (step sNonLeadDead (.pidfd_open 2041 { thread := true }) (.err Errno.ESRCH) = some (esrchPidfdOpenNext sNonLeadDead 2041 { thread := true }))
  let (_, sDzStopKill) := (ops.kill 2000 .sigkill).run sDzStop2
  let (wDzStopKill, _) := (ops.waitpid 2000 { continued := true }).run sDzStopKill
  NondetTest.assert (wDzStopKill = .ok (.signaled 2000 9 false))
  NondetTest.assert ((step sDzStopKill (.waitpid 2000 { continued := true }) (.waited (.continued 2000))).isNone)
  let (_, sDzContKill) := (ops.kill 2000 .sigkill).run sDzStop3
  let (wDzContKill, _) := (ops.waitpid 2000 { continued := true }).run sDzContKill
  NondetTest.assert (wDzContKill = .ok (.signaled 2000 9 false))
  NondetTest.assert ((step sDzContKill (.waitpid 2000 { continued := true }) (.waited (.continued 2000))).isNone)
  let (_, sDzStoppedTerm) := (ops.kill 2000 .sigterm).run sDzStop2
  NondetTest.assert ((step sDzStoppedTerm (.kill 2001 .sigzero) (.err Errno.ESRCH)).isNone)
  let sDzSig6 : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 2001 2000 with
      procs := (2000, { pgid := 2000, role := .child .sigchld false, lifecycle := .delayedZombie (.signaled 6 false) false [] }) ::
        ((ProcessSysState.initial 1000 1000 1000).registerNonLeaderThread 2001 2000).procs }
  let (_, sDzSig6_1) := (ops.kill 2000 .sigterm).run sDzSig6
  let (_, sDzSig6_2) := (ops.kill 2000 .sigkill).run sDzSig6_1
  NondetTest.assert ((step sDzSig6_2 (.waitpid 2000 {}) (.waited (.signaled 2000 6 false))).isNone)
  let sPid1Dz : ProcessSysState :=
    { (ProcessSysState.initial 2 1 1000).registerNonLeaderThread 3 1 1 with
      procs := (1, { pgid := 1, role := .foreign true, lifecycle := .delayedZombie (.exited 0) false [] }) ::
        ((ProcessSysState.initial 2 1 1000).registerNonLeaderThread 3 1 1).procs }
  let (_, sPid1DzAfter) := (ops.kill 1 .sigkill).run sPid1Dz
  NondetTest.assert ((step sPid1DzAfter (.kill 3 .sigzero) (.err Errno.ESRCH)).isNone)
  let sOrphCont0 : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2050, { pgid := 1000, orphanedPgid := true, role := .child .sigchld false,
                         lifecycle := .alive { auto := .controlled, run := .stopped 19 true } })] }
  let (_, sOrphCont1) := (ops.kill 2050 .sigcont).run sOrphCont0
  let (_, sOrphCont2) := (ops.kill 2050 (.raw 20)).run sOrphCont1
  let eOrphCont2 := (assocGet sOrphCont2.procs 2050).getD { pgid := 1000, lifecycle := .reaped }
  let sOrphContMoved := { sOrphCont2 with procs := assocSet sOrphCont2.procs 2050 (eOrphCont2.setPgid 2050 false) }
  NondetTest.assert ((step sOrphContMoved (.waitpid 2050 { nohang := true, continued := true }) (.waited .stillRunning)).isSome)
  let (_, sOrphMovedCont) := (ops.kill 2010 .sigcont).run sOrphMoved
  NondetTest.assert ((step sOrphMovedCont (.waitpid 2010 { nohang := true, continued := true }) (.waited (.continued 2010))).isSome)
  let sEdMinPg : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2060, { pgid := 0x80000000, role := .child .sigchld false, lifecycle := .exitDead })] }
  let (edMinOut, sEdMinAfter) := (ops.kill Int32.minValue .sigzero).run sEdMinPg
  NondetTest.assert (edMinOut = .error Errno.ESRCH ∧ sEdMinAfter = sEdMinPg ∧
    step sEdMinPg (.kill Int32.minValue .sigzero) (.err Errno.ESRCH) = some sEdMinPg)
  let sAutoKill0 := (ProcessSysState.initial 1000 1000 1000).spawnAutonomousChild 2055 2055
  let (_, sAutoKill1) := (ops.kill 2055 .sigkill).run sAutoKill0
  let (_, sAutoKill2) := (ops.kill 2055 .sigcont).run sAutoKill1
  let (wAutoKillCont, _) := (ops.waitpid 2055 { continued := true }).run sAutoKill2
  NondetTest.assert (wAutoKillCont = .ok (.signaled 2055 9 false))
  NondetTest.assert ((step sAutoKill2 (.waitpid 2055 { continued := true }) (.waited (.continued 2055))).isNone)
  let sCtrlKill0 := (ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2056 2056
  let (_, sCtrlKill1) := (ops.kill 2056 .sigkill).run sCtrlKill0
  let (_, sCtrlKill2) := (ops.kill 2056 .sigterm).run sCtrlKill1
  NondetTest.assert ((step sCtrlKill2 (.waitpid 2056 {}) (.waited (.signaled 2056 15 false))).isNone)
  let (_, sDzKill1) := (ops.kill 2000 .sigkill).run sDzBase
  let (_, sDzKill2) := (ops.kill 2000 .sigterm).run sDzKill1
  NondetTest.assert ((step sDzKill2 (.waitpid 2000 {}) (.waited (.signaled 2000 15 false))).isNone)
  let sEdSub : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2030, { pgid := 2030, role := .child .sigchld false, lifecycle := .exitDead }),
                (2031, { pgid := 2030, role := .thread 2030, lifecycle := .exitDead })] }
  NondetTest.assert ((step sEdSub (.pidfd_open 2031 { thread := true }) (.err Errno.ENOENT)).isNone)
  NondetTest.assert ((step sEdSub (.pidfd_open 2031 { thread := true }) (.opened 0)).isSome)
  let sDzAuto : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true with
      procs := [(2070, { pgid := 2070, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) (exitReap := .autoreapOnly) }),
                (2071, { pgid := 2070, role := .thread 2070,
                         lifecycle := .alive { auto := .planned (.exited 0) } })] }
  let (wDzAutoOut, _) := (ops.waitpid 2070 {}).run sDzAuto
  NondetTest.assert (wDzAutoOut = .error Errno.ECHILD)
  NondetTest.assert ((step sDzAuto (.waitpid 2070 {}) (.err Errno.ECHILD)).isSome)
  NondetTest.assert ((step sDzAuto (.kill 2070 .sigzero) (.err Errno.ESRCH)).isSome)
  NondetTest.assert ((step sDzAuto (.pidfd_open 2070 {}) (.err Errno.ESRCH)).isSome)
  let sDzAutoCtrl : ProcessSysState :=
    { (ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true with
      procs := [(2072, { pgid := 2072, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) (exitReap := .autoreapOnly) }),
                (2079, { pgid := 2072, role := .thread 2072,
                         lifecycle := .alive { auto := .controlled } })] }
  NondetTest.assert ((step sDzAutoCtrl (.waitpid 2072 { nohang := true }) (.err Errno.ECHILD)).isNone)
  let sDzToggle0 : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2073, { pgid := 2073, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) (exitReap := .zombieOnly) }),
                (2078, { pgid := 2073, role := .thread 2073,
                         lifecycle := .alive { auto := .planned (.exited 7) } })] }
  let sDzToggle1 := sDzToggle0.withSigchldAutoreap true
  NondetTest.assert ((step sDzToggle1 (.waitpid 2073 { nohang := true }) (.waited (.exited 2073 7))).isSome)
  NondetTest.assert ((step sDzToggle1 (.waitpid 2073 { nohang := true }) (.err Errno.ECHILD)).isSome)
  let sDzSubEx : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2074, { pgid := 2074, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) }),
                (2084, { pgid := 2074, role := .thread 2074,
                         lifecycle := .alive { auto := .planned (.exited 99) } })] }
  NondetTest.assert ((step sDzSubEx (.waitpid 2074 {}) (.waited (.exited 2074 99))).isSome)
  NondetTest.assert ((step sDzSubEx (.waitpid 2074 {}) (.waited (.exited 2074 55))).isNone)
  let sDzSubSig : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2075, { pgid := 2075, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) }),
                (2085, { pgid := 2075, role := .thread 2075,
                         lifecycle := .alive { auto := .planned (.signaled 10 false) } })] }
  NondetTest.assert ((step sDzSubSig (.waitpid 2075 {}) (.waited (.signaled 2075 10 false))).isSome)
  NondetTest.assert ((step sDzSubSig (.waitpid 2075 {}) (.waited (.signaled 2075 12 false))).isNone)
  let (_, sDzSubExKilled) := (ops.kill 2074 .sigkill).run sDzSubEx
  NondetTest.assert ((step sDzSubExKilled (.waitpid 2074 { nohang := true }) (.waited (.exited 2074 99))).isSome)
  NondetTest.assert ((step sDzKill1 (.waitpid 2000 { nohang := true }) (.waited (.exited 2000 42))).isNone)
  let sDzOrph0 : ProcessSysState :=
    { ProcessSysState.initial 1000 1000 1000 with
      procs := [(2080, { pgid := 1000, orphanedPgid := true, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) }),
                (2081, { pgid := 1000, orphanedPgid := true, role := .thread 2080,
                         lifecycle := .alive { auto := .controlled } })] }
  let (_, sDzOrph1) := (ops.kill 2080 (.raw 20)).run sDzOrph0
  let sDzOrphMoved : ProcessSysState :=
    { sDzOrph1 with procs := sDzOrph1.procs.map fun (p, e) =>
        if p == 2080 || e.role == .thread 2080 then (p, e.setPgid 2080 false) else (p, e) }
  NondetTest.assert ((step sDzOrphMoved (.waitpid 2080 { nohang := true, untraced := true }) (.waited (.stopped 2080 20))).isSome)
  let sDzOrphStopped := (step sDzOrphMoved (.waitpid 2080 { nohang := true, untraced := true }) (.waited (.stopped 2080 20))).getD sDzOrphMoved
  let (_, sDzOrphCont) := (ops.kill 2080 .sigcont).run sDzOrphStopped
  NondetTest.assert ((step sDzOrphCont (.waitpid 2080 { nohang := true, continued := true }) (.waited (.continued 2080))).isSome)
  let (_, sDzOrphDirectCont) := (ops.kill 2080 .sigcont).run sDzOrphMoved
  NondetTest.assert ((step sDzOrphDirectCont (.waitpid 2080 { nohang := true, continued := true }) (.waited (.continued 2080))).isSome)
  let (_, sDzOrphWasStoppedCont) := (ops.kill 2080 .sigcont).run
    { sDzOrph0 with procs := [(2080, { pgid := 1000, orphanedPgid := true, role := .child .sigchld false,
                                       lifecycle := .delayedZombie (.exited 42) false [] (.stopped 19 true) }),
                              (2081, { pgid := 1000, orphanedPgid := true, role := .thread 2080,
                                       lifecycle := .alive { auto := .controlled } })] }
  let (_, sDzOrphWasStoppedTstp) := (ops.kill 2080 (.raw 20)).run sDzOrphWasStoppedCont
  let sDzOrphWasStoppedMoved : ProcessSysState :=
    { sDzOrphWasStoppedTstp with procs := sDzOrphWasStoppedTstp.procs.map fun (p, e) =>
        if p == 2080 || e.role == .thread 2080 then (p, e.setPgid 2080 false) else (p, e) }
  NondetTest.assert ((step sDzOrphWasStoppedMoved (.waitpid 2080 { nohang := true, continued := true }) (.waited .stillRunning)).isSome)
  let sDzIgnCont0 : ProcessSysState :=
    (((ProcessSysState.initial 1000 1000 1000).withSigchldAutoreap true).spawnRunningChild 2090 2090)
      |>.upsertProc 2091 { pgid := 2091, role := .child .sigchld false,
                           lifecycle := .delayedZombie (.exited 42) (exitReap := .autoreapOnly) }
      |>.upsertProc 2092 { pgid := 2091, role := .thread 2091,
                           lifecycle := .alive { auto := .planned (.exited 99) } }
  let (_, sDzIgnCont1) := (ops.kill 2091 .sigstop).run sDzIgnCont0
  let sDzIgnCont2 := (step sDzIgnCont1 (.waitpid 2091 { untraced := true }) (.waited (.stopped 2091 19))).getD sDzIgnCont1
  let (_, sDzIgnCont3) := (ops.kill 2091 .sigcont).run sDzIgnCont2
  NondetTest.assert ((step sDzIgnCont3 (.waitpid (-1) { nohang := true, continued := true }) (.waited .stillRunning)).isSome)
  let sDzIgnPruned0 : ProcessSysState :=
    (((ProcessSysState.initial 1000 1000 1000).spawnRunningChild 2090 2090)
      |>.upsertProc 2093 { pgid := 2093, role := .child .sigchld false,
                           lifecycle := .delayedZombie (.exited 42) (exitReap := .zombieOnly) }
      |>.upsertProc 2094 { pgid := 2093, role := .thread 2093,
                           lifecycle := .alive { auto := .planned (.exited 99) } }).withSigchldAutoreap true
  let sDzIgnPruned1 := (step sDzIgnPruned0 (.kill 2094 .sigzero) (.err Errno.ESRCH)).getD sDzIgnPruned0
  NondetTest.assert ((step sDzIgnPruned1 (.waitpid (-1) { nohang := true }) (.waited .stillRunning)).isSome)
  let sDzSubExPruned := (step sDzSubEx (.kill 2084 .sigzero) (.err Errno.ESRCH)).getD sDzSubEx
  NondetTest.assert ((step sDzSubExPruned (.waitpid 2074 {}) (.waited (.exited 2074 99))).isSome)
  let sDzSubSigPruned := (step sDzSubSig (.kill 2085 .sigzero) (.err Errno.ESRCH)).getD sDzSubSig
  NondetTest.assert ((step sDzSubSigPruned (.waitpid 2075 {}) (.waited (.signaled 2075 10 false))).isSome)
  let sDzArbSib0 : ProcessSysState :=
    (ProcessSysState.initial 1000 1000 1000)
      |>.upsertProc 2095 { pgid := 2095, role := .child .sigchld false,
                           lifecycle := .delayedZombie (.exited 42) }
      |>.upsertProc 2096 { pgid := 2095, role := .thread 2095,
                           lifecycle := .alive { auto := .controlled } }
      |>.upsertProc 2097 { pgid := 2095, role := .thread 2095,
                           lifecycle := .alive { auto := .arbitrary } }
  let sDzArbSib1 := (step sDzArbSib0 (.kill 2096 .sigzero) (.err Errno.ESRCH)).getD sDzArbSib0
  NondetTest.assert ((step sDzArbSib0 (.kill 2096 .sigzero) (.err Errno.ESRCH)).isSome)
  NondetTest.assert ((step sDzArbSib1 (.waitpid 2095 { nohang := true }) (.waited (.exited 2095 77))).isSome)
  let (_, sDzStopKill1) := (ops.kill 2074 .sigstop).run sDzSubEx
  let sDzStopKill2 := (step sDzStopKill1 (.waitpid 2074 { untraced := true }) (.waited (.stopped 2074 19))).getD sDzStopKill1
  let (_, sDzStopKill3) := (ops.kill 2074 .sigterm).run sDzStopKill2
  let (_, sDzStopKill4) := (ops.kill 2074 .sigkill).run sDzStopKill3
  NondetTest.assert ((step sDzStopKill4 (.waitpid 2074 {}) (.waited (.signaled 2074 9 false))).isSome)
  NondetTest.assert ((step sDzStopKill4 (.waitpid 2074 {}) (.waited (.signaled 2074 15 false))).isNone)
  NondetTest.assert ((step sDzStopKill4 (.waitpid 2074 {}) (.waited (.exited 2074 99))).isNone)

/-- Subthread `do_group_exit` parity on `.alive` and `.delayedZombie` leaders, confirmed-stop queued fatal wake semantics, shadowed-PID reap pruning, `wait4` clone/thread selector flags, `SIGCONT` same-session `EPERM` bypass, `O_NOTIFICATION_PIPE`, core-dump signal classification, and `SIGTTIN`/`SIGTTOU` job-control stops. -/
def test_process_model_subthreadGroupExitCloneFlagsSigcontAndWatchQueue
    {runner} [NondetTest runner]
    (ops : ProcessOpsM (StateM ProcessSysState) HandleId := modelOps)
    (step : ProcessSysState → ProcessReq → ProcessOutcome → Option ProcessSysState := allowedStep) : runner Unit := do
  let s0 := ProcessSysState.initial 1000 1000 1000
  let sDzCtrlPlan := s0
    |>.upsertProc 2050 { pgid := 2050, role := .child .sigchld false, lifecycle := .delayedZombie (.exited 42) }
    |>.upsertProc 2051 { pgid := 2050, role := .thread 2050, lifecycle := .alive { auto := .controlled } }
    |>.upsertProc 2052 { pgid := 2050, role := .thread 2050, lifecycle := .alive { auto := .planned (.exited 77) } }
  NondetTest.assert ((step sDzCtrlPlan (.kill 2051 .sigzero) (.err Errno.ESRCH)).isSome)
  NondetTest.assert ((step sDzCtrlPlan (.waitpid 2050 { nohang := true }) (.waited (.exited 2050 77))).isSome)
  let (_, sDzCtrlPlanKilled) := (ops.kill 2050 .sigkill).run sDzCtrlPlan
  NondetTest.assert ((step sDzCtrlPlanKilled (.waitpid 2050 { nohang := true }) (.waited (.exited 2050 77))).isSome)
  let sDzCtrlPlanIgn := ((s0.withSigchldAutoreap true).spawnRunningChild 2001 2001)
    |>.upsertProc 2050 { pgid := 2050, role := .child .sigchld false,
                         lifecycle := .delayedZombie (.exited 42) (exitReap := .autoreapOnly) }
    |>.upsertProc 2051 { pgid := 2050, role := .thread 2050, lifecycle := .alive { auto := .controlled } }
    |>.upsertProc 2052 { pgid := 2050, role := .thread 2050, lifecycle := .alive { auto := .planned (.exited 77) } }
  NondetTest.assert ((step sDzCtrlPlanIgn (.waitpid 2050 {}) (.err Errno.ECHILD)).isSome)
  let (_, sDzIgnStop1) := (ops.kill 2050 .sigstop).run sDzCtrlPlanIgn
  let sDzIgnStop2 := (step sDzIgnStop1 (.waitpid 2050 { untraced := true }) (.waited (.stopped 2050 19))).getD sDzIgnStop1
  let (_, sDzIgnStop3) := (ops.kill 2050 .sigcont).run sDzIgnStop2
  NondetTest.assert ((step sDzIgnStop3 (.waitpid (-1) { nohang := true, continued := true }) (.waited .stillRunning)).isSome)

  let sAliveSubEx := (s0.spawnRunningChild 2100 2100)
    |>.upsertProc 2101 { pgid := 2100, role := .thread 2100, lifecycle := .alive { auto := .controlled } }
    |>.upsertProc 2102 { pgid := 2100, role := .thread 2100, lifecycle := .alive { auto := .planned (.exited 77) } }
  let (wAliveBlk, _) := (ops.waitpid 2100 { nohang := false }).run sAliveSubEx
  NondetTest.assert (wAliveBlk = .ok (.exited 2100 77))
  let sAliveSubExPruned := (step sAliveSubEx (.kill 2102 .sigzero) (.err Errno.ESRCH)).getD sAliveSubEx
  NondetTest.assert ((step sAliveSubExPruned (.waitpid 2100 {}) (.waited (.exited 2100 77))).isSome)
  let (_, sAliveStop1) := (ops.kill 2100 .sigstop).run sAliveSubEx
  let sAliveStop2 := (step sAliveStop1 (.waitpid 2100 { untraced := true }) (.waited (.stopped 2100 19))).getD sAliveStop1
  let (_, sAliveStopKill) := (ops.kill 2100 .sigkill).run sAliveStop2
  NondetTest.assert ((step sAliveStopKill (.waitpid 2100 {}) (.waited (.exited 2100 77))).isNone)
  NondetTest.assert ((step sAliveStopKill (.waitpid 2100 {}) (.waited (.signaled 2100 9 false))).isSome)

  let sAliveSubSig := (s0.spawnRunningChild 2110 2110)
    |>.upsertProc 2111 { pgid := 2110, role := .thread 2110, lifecycle := .alive { auto := .planned (.signaled 10 false) } }
  let sAliveSubSigPruned := (step sAliveSubSig (.kill 2111 .sigzero) (.err Errno.ESRCH)).getD sAliveSubSig
  let (wAliveSigBlk, _) := (ops.waitpid 2110 { nohang := false }).run sAliveSubSigPruned
  NondetTest.assert (wAliveSigBlk = .ok (.signaled 2110 10 false))

  let sAliveSubArb := (s0.spawnRunningChild 2120 2120)
    |>.upsertProc 2121 { pgid := 2120, role := .thread 2120, lifecycle := .alive { auto := .arbitrary } }
  NondetTest.assert ((step sAliveSubArb (.waitpid 2120 { nohang := true, untraced := true }) (.waited (.stopped 2120 19))).isSome)
  let (_, sAliveSubArbCont) := (ops.kill 2120 .sigcont).run sAliveSubArb
  NondetTest.assert ((step sAliveSubArbCont (.waitpid 2120 { nohang := true, continued := true }) (.waited (.continued 2120))).isSome)

  let sAliveSubIgn := ((s0.withSigchldAutoreap true).spawnRunningChild 2001 2001)
    |>.spawnRunningChild 2130 2130
    |>.upsertProc 2131 { pgid := 2130, role := .thread 2130, lifecycle := .alive { auto := .planned (.exited 99) } }
  let (wAliveIgnOut, _) := (ops.waitpid 2130 {}).run sAliveSubIgn
  NondetTest.assert (wAliveIgnOut = .error Errno.ECHILD)
  NondetTest.assert ((step sAliveSubIgn (.kill 2130 .sigzero) (.err Errno.ESRCH)).isSome)
  let (_, sAliveIgnSt1) := (ops.kill 2130 .sigstop).run sAliveSubIgn
  let sAliveIgnSt2 := (step sAliveIgnSt1 (.waitpid 2130 { untraced := true }) (.waited (.stopped 2130 19))).getD sAliveIgnSt1
  let (_, sAliveIgnSt3) := (ops.kill 2130 .sigcont).run sAliveIgnSt2
  NondetTest.assert ((step sAliveIgnSt3 (.waitpid (-1) { nohang := true, continued := true }) (.waited .stillRunning)).isSome)

  let sDzStopTerm0 := s0
    |>.upsertProc 2200 { pgid := 2200, role := .child .sigchld false, lifecycle := .delayedZombie (.exited 42) }
    |>.upsertProc 2201 { pgid := 2200, role := .thread 2200, lifecycle := .alive { auto := .planned (.exited 99) } }
  let (_, sDzStopTerm1) := (ops.kill 2200 .sigstop).run sDzStopTerm0
  let (_, sDzStopTerm2) := (ops.kill 2200 .sigterm).run sDzStopTerm1
  let sDzStopTerm3 := (step sDzStopTerm2 (.waitpid 2200 { untraced := true }) (.waited (.stopped 2200 19))).getD sDzStopTerm2
  let (_, sDzStopTerm4) := (ops.kill 2200 .sigcont).run sDzStopTerm3
  NondetTest.assert ((step sDzStopTerm4 (.waitpid 2200 {}) (.waited (.signaled 2200 15 false))).isSome)
  NondetTest.assert ((step sDzStopTerm4 (.waitpid 2200 {}) (.waited (.exited 2200 42))).isNone)
  NondetTest.assert ((step sDzStopTerm4 (.waitpid 2200 {}) (.waited (.exited 2200 99))).isNone)
  let (_, sDzStopTermKill) := (ops.kill 2200 .sigkill).run sDzStopTerm4
  NondetTest.assert ((step sDzStopTermKill (.waitpid 2200 {}) (.waited (.exited 2200 99))).isNone)

  let sAlivePlan0 := s0.spawnRunningChild 2210 2210 (some (.exited 42))
  let (_, sAlivePlan1) := (ops.kill 2210 .sigstop).run sAlivePlan0
  let sAlivePlan2 := (step sAlivePlan1 (.waitpid 2210 { untraced := true }) (.waited (.stopped 2210 19))).getD sAlivePlan1
  let (_, sAlivePlan3) := (ops.kill 2210 .sigterm).run sAlivePlan2
  let (_, sAlivePlan4) := (ops.kill 2210 .sigcont).run sAlivePlan3
  NondetTest.assert ((step sAlivePlan4 (.waitpid 2210 {}) (.waited (.signaled 2210 15 false))).isSome)
  NondetTest.assert ((step sAlivePlan4 (.waitpid 2210 {}) (.waited (.exited 2210 42))).isNone)

  let sShadowBase := s0.spawnZombieExited 2300 99 2300
  let sShadow : ProcessSysState :=
    { sShadowBase with
      procs := (2300, { pgid := 2300, role := .child .sigchld false, lifecycle := .zombie (.exited 42) }) :: sShadowBase.procs }
  let (wShadow1, sShadowAfter) := (ops.waitpid 2300 { nohang := true }).run sShadow
  let (wShadow2, _) := (ops.waitpid 2300 { nohang := true }).run sShadowAfter
  NondetTest.assert (wShadow1 = .ok (.exited 2300 42) ∧ wShadow2 = .error Errno.ECHILD ∧ (assocGet sShadowAfter.procs 2300).isNone)
  let sShadowAutoBase := (s0.withSigchldAutoreap true).spawnRunningChild 2310 2310
  let sShadowAuto : ProcessSysState :=
    { sShadowAutoBase with
      procs := (2310, { pgid := 2310, role := .child .sigchld false,
                        lifecycle := .alive { auto := .arbitrary, exitReap := .autoreapOnly } }) :: sShadowAutoBase.procs }
  let sShadowGroupPruned := (step sShadowAuto (.kill (-2310) .sigzero) (.err Errno.ESRCH)).getD sShadowAuto
  NondetTest.assert ((assocGet sShadowGroupPruned.procs 2310).isNone)

  let sCloneThr := s0
    |>.spawnZombieExited 2400 10 2400 false false
    |>.spawnZombieExited 2401 20 2401 true false
    |>.spawnZombieExited 2402 30 2402 false true
  let (wDefOnClone, _) := (ops.waitpid 2401 { nohang := true }).run sCloneThr
  let (wCloneOnSigchld, _) := (ops.waitpid 2400 { nohang := true, wclone := true }).run sCloneThr
  let (wCloneOnClone, _) := (ops.waitpid 2401 { nohang := true, wclone := true }).run sCloneThr
  let (wWallOnClone, _) := (ops.waitpid 2401 { nohang := true, wall := true }).run sCloneThr
  let (wWallOnSigchld, _) := (ops.waitpid 2400 { nohang := true, wall := true }).run sCloneThr
  let (wNoThrOnSib, _) := (ops.waitpid 2402 { nohang := true, wnothread := true }).run sCloneThr
  let (wAllowThrOnSib, _) := (ops.waitpid 2402 { nohang := true, wnothread := false }).run sCloneThr
  NondetTest.assert (wDefOnClone = .error Errno.ECHILD ∧ wCloneOnSigchld = .error Errno.ECHILD)
  NondetTest.assert (wCloneOnClone = .ok (.exited 2401 20) ∧ wWallOnClone = .ok (.exited 2401 20) ∧ wWallOnSigchld = .ok (.exited 2400 10))
  NondetTest.assert (wNoThrOnSib = .error Errno.ECHILD ∧ wAllowThrOnSib = .ok (.exited 2402 30))
  let sCloneIgn := (s0.withSigchldAutoreap true).spawnAutonomousChild 2403 2403 true false
  NondetTest.assert ((step sCloneIgn (.waitpid 2403 { wclone := true }) (.err Errno.ECHILD)).isNone)
  NondetTest.assert ((step sCloneIgn (.waitpid 2403 { wclone := true }) (.waited (.exited 2403 0))).isSome)

  let sSessPerm := (s0.registerForeignProc 2500 2500 false true)
    |>.registerForeignProc 2501 2501 false false
    |>.upsertProc 2502 { pgid := 2502, canSignal := false, sameSession := true, role := .foreign false, lifecycle := .exitDead }
  let (kSameCont, _) := (ops.kill 2500 .sigcont).run sSessPerm
  let (kSameTerm, _) := (ops.kill 2500 .sigterm).run sSessPerm
  let (kSameZero, _) := (ops.kill 2500 .sigzero).run sSessPerm
  let (kDiffCont, _) := (ops.kill 2501 .sigcont).run sSessPerm
  let (kGrpSameCont, _) := (ops.kill (-2500) .sigcont).run sSessPerm
  let (kGrpDiffCont, _) := (ops.kill (-2501) .sigcont).run sSessPerm
  NondetTest.assert (kSameCont = .ok () ∧ kSameTerm = .error Errno.EPERM ∧ kSameZero = .error Errno.EPERM)
  NondetTest.assert (kDiffCont = .error Errno.EPERM ∧ kGrpSameCont = .ok () ∧ kGrpDiffCont = .error Errno.EPERM)
  NondetTest.assert ((step sSessPerm (.kill 2502 .sigcont) .unit).isSome)
  NondetTest.assert ((step sSessPerm (.kill 2502 .sigterm) .unit).isNone)

  let (pNotifOff, _) := (ops.pipe2 { notificationPipe := true }).run s0
  let (pNotifOn, _) := (ops.pipe2 { notificationPipe := true }).run (s0.withWatchQueueSupported true)
  NondetTest.assert (pNotifOff = .error Errno.ENOPKG ∧ pNotifOn = .ok (0, 1))
  NondetTest.assert ((step s0 (.pipe2 { notificationPipe := true }) (.err Errno.ENOPKG)).isSome)
  NondetTest.assert ((step s0 (.pipe2 { notificationPipe := true }) (.err Errno.EPERM)).isNone ∧
    (step s0 (.pipe2 { notificationPipe := true }) (.err Errno.EINVAL)).isNone ∧
    (step sSessPerm (.kill (-1) .sigterm) (.err Errno.EPERM)).isNone ∧
    (step sSessPerm (.kill (-1) .sigterm) .unit).isSome)
  NondetTest.assert ((step s0 (.pipe2 { notificationPipe := true }) (.piped 0 1)).isNone)
  NondetTest.assert ((step (s0.withWatchQueueSupported true) (.pipe2 { notificationPipe := true }) (.err Errno.ENOPKG)).isNone)

  let (_, sCoreTerm) := (ops.kill 2600 .sigterm).run (s0.spawnRunningChild 2600 2600)
  let (_, sCoreQuit) := (ops.kill 2600 (.raw 3)).run (s0.spawnRunningChild 2600 2600)
  NondetTest.assert ((step sCoreTerm (.waitpid 2600 {}) (.waited (.signaled 2600 15 true))).isNone)
  NondetTest.assert ((step sCoreTerm (.waitpid 2600 {}) (.waited (.signaled 2600 15 false))).isSome)
  NondetTest.assert ((step sCoreQuit (.waitpid 2600 {}) (.waited (.signaled 2600 3 true))).isSome)
  let (_, sTtin1) := (ops.kill 2601 (.raw 21)).run (s0.spawnRunningChild 2601 2601)
  let (wTtin, _) := (ops.waitpid 2601 { nohang := true, untraced := true }).run sTtin1
  let (_, sTtou1) := (ops.kill 2602 (.raw 22)).run (s0.spawnRunningChild 2602 2602)
  let (wTtou, _) := (ops.waitpid 2602 { nohang := true, untraced := true }).run sTtou1
  NondetTest.assert (wTtin = .ok (.stopped 2601 21) ∧ wTtou = .ok (.stopped 2602 22))
  let sOrphTtin0 := s0.spawnRunningChild 2603 2603 none false false true
  let (_, sOrphTtin1) := (ops.kill 2603 (.raw 21)).run sOrphTtin0
  let (_, sOrphTtin2) := (ops.kill 2603 (.raw 22)).run sOrphTtin1
  let (wOrphTty, _) := (ops.waitpid 2603 { nohang := true, untraced := true }).run sOrphTtin2
  NondetTest.assert (wOrphTty = .ok .stillRunning)
  NondetTest.assert ((step sOrphTtin2 (.waitpid 2603 { nohang := true, untraced := true }) (.waited (.stopped 2603 21))).isNone)
  NondetTest.assert ((step sOrphTtin2 (.waitpid 2603 { nohang := true, untraced := true }) (.waited (.stopped 2603 22))).isNone)

end LeanSwe.LinuxSyscall.Process

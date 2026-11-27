import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Process.Impl
import Fuzz.LinuxSyscall.ProcessEnv

namespace Fuzz.LinuxSyscall.Process.Strace

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process
open Fuzz.LinuxSyscall

private def logProcessErrHit (op : String) (e : Errno) (mode : String) : IO Unit :=
  Fuzz.Common.logErrHit s!"LeanSwe.LinuxSyscall.Process.{op}"
    (reprStr (ProcessErrorKind.ofErrno e)).trimAscii.toString mode

private def trackProcessErr {α : Type} (op : String) (mode : String) (r : Except Errno α) : IO (Except Errno α) := do
  if let .error e := r then
    logProcessErrHit op e mode
  return r

private def trackProcessOps (mode : String) (ops : ProcessOps) : ProcessOps :=
  { pipe2 := fun a => do trackProcessErr "pipe2" mode (← ops.pipe2 a)
    waitpid := fun a b => do trackProcessErr "waitpid" mode (← ops.waitpid a b)
    kill := fun a b => do trackProcessErr "kill" mode (← ops.kill a b)
    pidfd_open := fun a b => do trackProcessErr "pidfd_open" mode (← ops.pidfd_open a b)
    pidfd_send_signal := fun a b c => do trackProcessErr "pidfd_send_signal" mode (← ops.pidfd_send_signal a b c)
    getpid := do trackProcessErr "getpid" mode (← ops.getpid)
    getuid := do trackProcessErr "getuid" mode (← ops.getuid) }

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

private def assertErrOneOf {α : Type} (msg : String) (r : Except Errno α) (allowed : List Errno) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{msg}: expected error in {allowed}, got ok")
  | .error e =>
    if !allowed.contains e then
      throw (IO.userError s!"{msg}: expected error in {allowed}, got {e}")

private def assertOk {α : Type} (msg : String) (r : Except Errno α) : IO α := do
  match r with
  | .ok v => return v
  | .error e => throw (IO.userError s!"{msg}: unexpected error {e}")

private def closeQuiet (fd : RawFd) : IO Unit := do
  let _ ← ProcessEnv.closeFd fd

private def resolveSelfExe : IO String := do
  try
    return (← IO.FS.realPath "/proc/self/exe").toString
  catch _ =>
    try
      return (← IO.appPath).toString
    catch _ =>
      return "/proc/self/exe"

private def waitUntilReaped (pid : UInt32) : IO WaitResult := do
  for _ in [:200] do
    match ← waitpid pid.toInt32 { nohang := true } with
    | .ok .stillRunning => IO.sleep 5
    | .ok w => return w
    | .error e =>
      if e == Errno.EINTR then pure ()
      else throw (IO.userError s!"waitUntilReaped({pid}) unexpected error: {e}")
  throw (IO.userError s!"waitUntilReaped({pid}) timed out")

/-- Verify `pipe2` atomic flags, `EINVAL` on extraBits, and ABA-safe `LeanFdBox` close. -/
private def assume_process_pipe2_atomicFlagsAndFdPair : IO Unit := do
  assertErr "pipe2 extraBits=1" (← pipe2 { extraBits := 1 }) Errno.EINVAL
  assertErr "pipe2 extraBits=0x80000000" (← pipe2 { extraBits := 0x80000000 }) Errno.EINVAL
  for clo in [false, true] do
    for nb in [false, true] do
      let (rd, wr) ← assertOk s!"pipe2 clo={clo} nb={nb}" (← pipe2 { cloexec := clo, nonblock := nb })
      let (fdFlagsR, flFlagsR) ← assertOk s!"getFdFlags rd clo={clo} nb={nb}" (← ProcessEnv.getFdFlags rd)
      let (fdFlagsW, flFlagsW) ← assertOk s!"getFdFlags wr clo={clo} nb={nb}" (← ProcessEnv.getFdFlags wr)
      let expFd : UInt32 := if clo then 1 else 0
      let expNb : UInt32 := if nb then 0x800 else 0
      assertTrue s!"pipe2 rd FD_CLOEXEC clo={clo}" ((fdFlagsR &&& 1) == expFd)
      assertTrue s!"pipe2 wr FD_CLOEXEC clo={clo}" ((fdFlagsW &&& 1) == expFd)
      assertTrue s!"pipe2 rd O_NONBLOCK nb={nb}" ((flFlagsR &&& 0x800) == expNb)
      assertTrue s!"pipe2 wr O_NONBLOCK nb={nb}" ((flFlagsW &&& 0x800) == expNb)
      assertOk "close rd" (← ProcessEnv.closeFd rd)
      assertErr "double close rd" (← ProcessEnv.closeFd rd) Errno.EBADF
      assertOk "close wr" (← ProcessEnv.closeFd wr)
      assertErr "double close wr" (← ProcessEnv.closeFd wr) Errno.EBADF

/-- Verify `waitpid` `wait4` flag rejection, `INT32_MIN` `ESRCH`, exited/signaled/stopped/continued decoding, and reap. -/
private def assume_process_waitpid_wait4StatusAndReap : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  assertErr "waitpid invalid flag" (← waitpid (-1) { extraBits := 1 }) Errno.EINVAL
  assertErr "waitpid invalid high extraBits" (← waitpid (-1) { extraBits := 0x80000000 }) Errno.EINVAL
  assertErr "waitpid INT32_MIN" (← waitpid Int32.minValue {}) Errno.ESRCH

  let ((pidEx, _), _) ← assertOk "spawn zombie exit 42" (← ProcessEnv.spawnZombie (-1) false 42 false)
  try
    let w ← assertOk "waitpid exited" (← waitpid pidEx.toInt32 { nohang := true })
    assertTrue s!"expected exited({pidEx}, 42), got {repr w}" (w == .exited pidEx 42)
    assertErr "waitpid after reap ECHILD" (← waitpid pidEx.toInt32 {}) Errno.ECHILD
  finally
    ProcessEnv.cleanupChild pidEx

  let (pidRun, _) ← assertOk "spawn controlled" (← ProcessEnv.spawnControlled (-1) false)
  try
    let wNh ← assertOk "waitpid nohang live" (← waitpid pidRun.toInt32 { nohang := true })
    assertTrue "live child stillRunning" (wNh == .stillRunning)
    assertOk "kill SIGSTOP" (← kill pidRun.toInt32 .sigstop)
    let mut gotStop := false
    for _ in [:200] do
      let ws ← assertOk "waitpid WUNTRACED" (← waitpid pidRun.toInt32 { nohang := true, untraced := true })
      if ws == .stopped pidRun 19 then
        gotStop := true
        break
      IO.sleep 5
    assertTrue "observed WUNTRACED SIGSTOP" gotStop
    assertOk "kill SIGCONT" (← kill pidRun.toInt32 .sigcont)
    let mut gotCont := false
    for _ in [:200] do
      let wc ← assertOk "waitpid WCONTINUED" (← waitpid pidRun.toInt32 { nohang := true, continued := true })
      if wc == .continued pidRun then
        gotCont := true
        break
      IO.sleep 5
    assertTrue "observed WCONTINUED" gotCont
    assertOk "kill SIGKILL" (← kill pidRun.toInt32 .sigkill)
    let wk ← waitUntilReaped pidRun
    assertTrue s!"expected signaled({pidRun}, 9, false), got {repr wk}" (wk == .signaled pidRun 9 false)
  finally
    ProcessEnv.cleanupChild pidRun

/-- Verify `kill` signal encoding, invalid signal `EINVAL`, `SIGZERO` probes, ignored signals, and `-pgid` group routing. -/
private def assume_process_kill_signalAndGroupRouting : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let selfPid ← assertOk "getpid" (← getpid)
  assertErr "kill sig 65" (← kill selfPid.toInt32 (.raw 65)) Errno.EINVAL
  assertErr "kill sig -1" (← kill selfPid.toInt32 (.raw (-1))) Errno.EINVAL
  assertErr "kill INT32_MIN" (← kill Int32.minValue .sigzero) Errno.ESRCH

  let (cPid, cPgid) ← assertOk "spawn own-pgid child" (← ProcessEnv.spawnControlled 0 false)
  try
    assertOk "kill cPid SIGZERO" (← kill cPid.toInt32 .sigzero)
    assertOk "kill cPid SIGCHLD ignored" (← kill cPid.toInt32 (.raw 17))
    assertOk "kill cPid SIGURG ignored" (← kill cPid.toInt32 (.raw 23))
    assertOk "kill cPid SIGWINCH ignored" (← kill cPid.toInt32 (.raw 28))
    let w0 ← assertOk "still running after ignored" (← waitpid cPid.toInt32 { nohang := true })
    assertTrue "stillRunning after ignored signals" (w0 == .stillRunning)
    let negPgid : Int32 := Int32.ofInt (-(cPgid.toNat : Int))
    assertOk "kill -pgid SIGTERM" (← kill negPgid .sigterm)
    let wTerm ← waitUntilReaped cPid
    assertTrue s!"expected signaled({cPid}, 15, false), got {repr wTerm}" (wTerm == .signaled cPid 15 false)
    assertErr "kill reaped cPid ESRCH" (← kill cPid.toInt32 .sigzero) Errno.ESRCH
  finally
    ProcessEnv.cleanupChild cPid

/-- Verify `pidfd_open` (`__NR = 434`), `EINVAL` validation, non-leader thread `ENOENT`, and zombie/post-reap behavior. -/
private def assume_process_pidfdOpen_nr434AndCloexec : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let selfPid ← assertOk "getpid" (← getpid)
  assertErr "pidfd_open 0" (← pidfd_open 0 {}) Errno.EINVAL
  assertErr "pidfd_open 0x80000000" (← pidfd_open 0x80000000 {}) Errno.EINVAL
  assertErr "pidfd_open 0xffffffff" (← pidfd_open 0xffffffff {}) Errno.EINVAL
  assertErr "pidfd_open extraBits=1" (← pidfd_open selfPid { extraBits := 1 }) Errno.EINVAL
  assertErr "pidfd_open extraBits=0x80000000" (← pidfd_open selfPid { extraBits := 0x80000000 }) Errno.EINVAL
  let pfdSelf ← assertOk "pidfd_open self" (← pidfd_open selfPid { nonblock := true })
  try
    let (fdFlagsSelf, flFlagsSelf) ← assertOk "getFdFlags pfdSelf" (← ProcessEnv.getFdFlags pfdSelf)
    assertTrue "pidfd_open self FD_CLOEXEC" ((fdFlagsSelf &&& 1) == 1)
    assertTrue "pidfd_open self PIDFD_NONBLOCK" ((flFlagsSelf &&& 0x800) == 0x800)
  finally
    closeQuiet pfdSelf

  let (tid, th) ← assertOk "spawnThread" (← ProcessEnv.spawnThread)
  try
    let rThread ← pidfd_open tid {}
    assertErrOneOf "pidfd_open non-leader thread" rThread [Errno.ENOENT, Errno.EINVAL]
  finally
    ProcessEnv.joinThread th

  let ((zPid, _), _) ← assertOk "spawn zombie" (← ProcessEnv.spawnZombie (-1) false 7 false)
  try
    let pfdZ ← assertOk "pidfd_open zombie" (← pidfd_open zPid {})
    try
      let (fdFlagsZ, flFlagsZ) ← assertOk "getFdFlags pfdZ" (← ProcessEnv.getFdFlags pfdZ)
      assertTrue "pidfd_open zombie FD_CLOEXEC" ((fdFlagsZ &&& 1) == 1)
      assertTrue "pidfd_open zombie !PIDFD_NONBLOCK" ((flFlagsZ &&& 0x800) == 0)
      assertOk "pidfd_send_signal SIGZERO on zombie" (← pidfd_send_signal pfdZ .sigzero {})
      let w ← assertOk "reap zombie" (← waitpid zPid.toInt32 {})
      assertTrue "zombie exit 7" (w == WaitResult.exited zPid 7)
      assertErr "pidfd_send_signal after reap ESRCH" (← pidfd_send_signal pfdZ .sigzero {}) Errno.ESRCH
    finally
      closeQuiet pfdZ
  finally
    ProcessEnv.cleanupChild zPid

/-- Verify `pidfd_send_signal` (`__NR = 424`), flag validation, pipe `EBADF`, and `PIDTYPE_PGID` delivery after leader reap/move. -/
private def assume_process_pidfdSendSignal_nr424AndReapRaceGuard : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let (rd, wr) ← assertOk "pipe2 for badFd" (← pipe2 { cloexec := true })
  try
    assertErr "pidfd_send_signal bad flag on pipe"
      (← pidfd_send_signal rd .sigzero { extraBits := 1 }) Errno.EINVAL
    assertErr "pidfd_send_signal conflict scope"
      (← pidfd_send_signal rd .sigzero { thread := true, processGroup := true }) Errno.EINVAL
    assertErr "pidfd_send_signal on pipe fd EBADF"
      (← pidfd_send_signal rd .sigzero {}) Errno.EBADF
  finally
    closeQuiet rd
    closeQuiet wr

  let (leaderPid, pgid) ← assertOk "spawn group leader" (← ProcessEnv.spawnControlled 0 false)
  try
    let pfdLeader ← assertOk "pidfd_open leader" (← pidfd_open leaderPid {})
    try
      let (memberPid, _) ← assertOk "spawn group member"
        (← ProcessEnv.spawnControlled pgid.toInt32 false)
      try
        assertOk "kill leader" (← kill leaderPid.toInt32 .sigkill)
        let _ ← waitUntilReaped leaderPid
        assertOk "pidfd_send_signal PGID after leader reap"
          (← pidfd_send_signal pfdLeader .sigterm { processGroup := true })
        let wMember ← waitUntilReaped memberPid
        assertTrue s!"member killed by PIDTYPE_PGID, got {repr wMember}"
          (wMember == .signaled memberPid 15 false)
        assertErr "pidfd_send_signal PGID empty group ESRCH"
          (← pidfd_send_signal pfdLeader .sigzero { processGroup := true }) Errno.ESRCH
      finally
        ProcessEnv.cleanupChild memberPid
    finally
      closeQuiet pfdLeader
  finally
    ProcessEnv.cleanupChild leaderPid

/-- Verify `getpid` returns bounded positive `1 ≤ pid ≤ 0x7fffffff` and stays constant across intervening syscalls. -/
private def assume_process_getpid_positiveAndStable : IO Unit := do
  let p1 ← assertOk "getpid 1" (← getpid)
  assertTrue s!"getpid positive bounded ({p1})" (1 ≤ p1 && p1 ≤ maxLinuxPid)
  let (rd, wr) ← assertOk "pipe2" (← pipe2 { cloexec := true })
  closeQuiet rd
  closeQuiet wr
  assertOk "kill self SIGZERO" (← kill p1.toInt32 .sigzero)
  let pfd ← assertOk "pidfd_open self" (← pidfd_open p1 {})
  closeQuiet pfd
  let p2 ← assertOk "getpid 2" (← getpid)
  assertTrue s!"getpid stable ({p1} vs {p2})" (p1 == p2)

/-- Verify `getuid` returns stable real UID across intervening syscalls. -/
private def assume_process_getuid_stableRealUid : IO Unit := do
  let u1 ← assertOk "getuid 1" (← getuid)
  let p ← assertOk "getpid for getuid" (← getpid)
  assertOk "kill self SIGZERO" (← kill p.toInt32 .sigzero)
  let u2 ← assertOk "getuid 2" (← getuid)
  assertTrue s!"getuid stable ({u1} vs {u2})" (u1 == u2)

private def mkMockProcessOps (e : Errno) : ProcessOps :=
  trackProcessOps "mocked" <| Internal.mkProcessOps
    { pipe2 := fun _ => return .error e
      waitpid := fun _ _ => return .error e
      kill := fun _ _ _ => return .error e
      pidfd_open := fun _ _ => return .error e
      pidfd_send_signal := fun _ _ _ _ => return .error e
      getpid := return .error e
      getuid := return .error e }

/-- Mocked error-coverage test for `pipe2` (`ESRCH`, `ECHILD`, `EBADF`, `EPERM`, `ENFILE`, `EMFILE`, `ENOMEM`, `EINTR`). -/
private def err_pipe2_mocked : IO Unit := do
  for e in [Errno.ESRCH, Errno.ECHILD, Errno.EBADF, Errno.EPERM, Errno.ENFILE, Errno.EMFILE, Errno.ENOMEM, Errno.EINTR] do
    let r ← (mkMockProcessOps e).pipe2 {}
    assertErr s!"mocked pipe2 {e}" r e

/-- Real `pipe2` `invalidArg` error test (`EINVAL` on unsupported flag bits). -/
private def err_pipe2_invalidArg : IO Unit := do
  assertErr "real pipe2 extraBits=1" (← pipe2 { extraBits := 1 }) Errno.EINVAL
  logProcessErrHit "pipe2" Errno.EINVAL "real"
  assertErr "real pipe2 extraBits=0x80000000" (← pipe2 { extraBits := 0x80000000 }) Errno.EINVAL

/-- Real `waitpid` `noSuchProcess` error test (`INT32_MIN` returns `ESRCH`). -/
private def err_waitpid_noSuchProcess : IO Unit := do
  assertErr "real waitpid INT32_MIN" (← waitpid Int32.minValue {}) Errno.ESRCH
  logProcessErrHit "waitpid" Errno.ESRCH "real"

/-- Real `waitpid` `noChild` error test (`ECHILD` with no matching children). -/
private def err_waitpid_noChild : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  assertErr "real waitpid (-1) no children" (← waitpid (-1) {}) Errno.ECHILD
  logProcessErrHit "waitpid" Errno.ECHILD "real"
  assertErr "real waitpid nonexistent pid" (← waitpid 999999999 {}) Errno.ECHILD

/-- Mocked error-coverage test for `waitpid` (`EBADF`, `EPERM`, `EINTR`, `ENOMEM`). -/
private def err_waitpid_mocked : IO Unit := do
  for e in [Errno.EBADF, Errno.EPERM, Errno.EACCES, Errno.EINTR, Errno.ENOMEM] do
    let r ← (mkMockProcessOps e).waitpid (-1) {}
    assertErr s!"mocked waitpid {e}" r e

/-- Real `waitpid` `invalidArg` error test (`EINVAL` on unsupported option bits). -/
private def err_waitpid_invalidArg : IO Unit := do
  assertErr "real waitpid extraBits=1" (← waitpid (-1) { extraBits := 1 }) Errno.EINVAL
  logProcessErrHit "waitpid" Errno.EINVAL "real"

/-- Real `kill` `noSuchProcess` error test (`ESRCH` on `INT32_MIN` and reaped child). -/
private def err_kill_noSuchProcess : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  assertErr "real kill INT32_MIN" (← kill Int32.minValue .sigzero) Errno.ESRCH
  logProcessErrHit "kill" Errno.ESRCH "real"
  let ((pid, _), _) ← assertOk "spawn zombie" (← ProcessEnv.spawnZombie (-1) false 0 false)
  try
    let _ ← assertOk "reap zombie" (← waitpid pid.toInt32 {})
    assertErr "real kill reaped pid" (← kill pid.toInt32 .sigzero) Errno.ESRCH
  finally
    ProcessEnv.cleanupChild pid

/-- Mocked error-coverage test for `kill` (`ECHILD`, `EBADF`, `EINTR`, `ENOMEM`). -/
private def err_kill_mocked : IO Unit := do
  for e in [Errno.ECHILD, Errno.EBADF, Errno.EINTR, Errno.ENOMEM] do
    let r ← (mkMockProcessOps e).kill 1 .sigzero
    assertErr s!"mocked kill {e}" r e

/-- Real `kill` `invalidArg` error test (`EINVAL` on out-of-range and NPTL-reserved `32`/`33` signals). -/
private def err_kill_invalidArg : IO Unit := do
  let selfPid ← assertOk "getpid" (← getpid)
  assertErr "real kill sig -1" (← kill selfPid.toInt32 (.raw (-1))) Errno.EINVAL
  logProcessErrHit "kill" Errno.EINVAL "real"
  assertErr "real kill sig 65" (← kill selfPid.toInt32 (.raw 65)) Errno.EINVAL
  assertErr "real kill nptl 32" (← kill selfPid.toInt32 (.raw 32)) Errno.EINVAL
  assertErr "real kill nptl 33" (← kill selfPid.toInt32 (.raw 33)) Errno.EINVAL
  assertErr "real kill nptl 32 missing" (← kill 999999 (.raw 32)) Errno.EINVAL

private def isSingleUidUserns : IO Bool := do
  try
    let txt ← IO.FS.readFile "/proc/self/uid_map"
    let mut total : Nat := 0
    for line in txt.splitOn "\n" do
      let cols := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
      if let some cntStr := cols[2]? then
        total := total + cntStr.toNat?.getD 0
    return total == 1
  catch _ =>
    return false

/-- Real `kill` `permissionDenied` error test (`EPERM` on privileged init/kthreadd or userns `nobody`). -/
private def err_kill_permissionDenied : IO Unit := do
  let self ← assertOk "getpid" (← getpid)
  for target in [(1 : Int32), (2 : Int32)] do
    if target != self.toInt32 then
      let r ← kill target .sigzero
      if let .error e := r then
        if e == Errno.EPERM || e == Errno.EACCES then
          logProcessErrHit "kill" e "real"
          return ()
  let canNs ← ProcessEnv.probeUnshare
  if canNs then
    let rc ← assertOk "runNsWorker kill-eperm" (← ProcessEnv.runNsWorker true 6 "kill-eperm" "0")
    if rc == 0 then
      logProcessErrHit "kill" Errno.EPERM "real"
      return ()
  if ← isSingleUidUserns then
    let exe ← resolveSelfExe
    let out ← IO.Process.output {
      cmd := exe
      args := #["--process-strace-worker", "seccomp-kill", "EPERM"]
    }
    assertTrue s!"seccomp-kill EPERM worker failed (exit={out.exitCode}): {out.stderr}" (out.exitCode == 0)
    logProcessErrHit "kill" Errno.EPERM "fault_injected"
    return ()
  throw (IO.userError "err_kill_permissionDenied: could not observe EPERM/EACCES on host or userns")

/-- Real `pidfd_open` `noSuchProcess` error test (`ENOENT` on non-leader thread and `ESRCH` on reaped child). -/
private def err_pidfdOpen_noSuchProcess : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let (tid, th) ← assertOk "spawnThread" (← ProcessEnv.spawnThread)
  try
    assertErrOneOf "real pidfd_open thread ENOENT" (← pidfd_open tid {}) [Errno.ENOENT, Errno.EINVAL]
  finally
    ProcessEnv.joinThread th
  let ((pid, _), _) ← assertOk "spawn zombie" (← ProcessEnv.spawnZombie (-1) false 0 false)
  try
    let _ ← assertOk "reap zombie" (← waitpid pid.toInt32 {})
    assertErr "real pidfd_open reaped ESRCH" (← pidfd_open pid {}) Errno.ESRCH
    logProcessErrHit "pidfd_open" Errno.ESRCH "real"
  finally
    ProcessEnv.cleanupChild pid

/-- Mocked error-coverage test for `pidfd_open` (`ECHILD`, `EBADF`, `EPERM`, `EMFILE`, `ENFILE`, `ENOMEM`). -/
private def err_pidfdOpen_mocked : IO Unit := do
  for e in [Errno.ECHILD, Errno.EBADF, Errno.EPERM, Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM] do
    let r ← (mkMockProcessOps e).pidfd_open 1 {}
    assertErr s!"mocked pidfd_open {e}" r e

/-- Real `pidfd_open` `invalidArg` error test (`pid = 0` and unsupported flag bits). -/
private def err_pidfdOpen_invalidArg : IO Unit := do
  let selfPid ← assertOk "getpid" (← getpid)
  assertErr "real pidfd_open 0" (← pidfd_open 0 {}) Errno.EINVAL
  logProcessErrHit "pidfd_open" Errno.EINVAL "real"
  assertErr "real pidfd_open extraBits=1" (← pidfd_open selfPid { extraBits := 1 }) Errno.EINVAL

/-- Real `pidfd_send_signal` `noSuchProcess` error test (`ESRCH` after reap). -/
private def err_pidfdSendSignal_noSuchProcess : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let ((pid, _), _) ← assertOk "spawn zombie" (← ProcessEnv.spawnZombie (-1) false 1 false)
  try
    let pfd ← assertOk "pidfd_open zombie" (← pidfd_open pid {})
    try
      let _ ← assertOk "reap zombie" (← waitpid pid.toInt32 {})
      assertErr "real pidfd_send_signal reaped ESRCH" (← pidfd_send_signal pfd .sigzero {}) Errno.ESRCH
      logProcessErrHit "pidfd_send_signal" Errno.ESRCH "real"
    finally
      closeQuiet pfd
  finally
    ProcessEnv.cleanupChild pid

/-- Mocked error-coverage test for `pidfd_send_signal` (`ECHILD`, `EINTR`, `ENOMEM`). -/
private def err_pidfdSendSignal_mocked : IO Unit := do
  let (rd, wr) ← assertOk "pipe2 dummy fd" (← pipe2 { cloexec := true })
  try
    for e in [Errno.ECHILD, Errno.EINTR, Errno.ENOMEM] do
      let r ← (mkMockProcessOps e).pidfd_send_signal rd .sigzero {}
      assertErr s!"mocked pidfd_send_signal {e}" r e
  finally
    closeQuiet rd
    closeQuiet wr

/-- Real `pidfd_send_signal` `badFd` error test (closed descriptor and non-pidfd pipe). -/
private def err_pidfdSendSignal_badFd : IO Unit := do
  let selfPid ← assertOk "getpid" (← getpid)
  let pfd ← assertOk "pidfd_open self" (← pidfd_open selfPid {})
  closeQuiet pfd
  assertErr "closed pidfd EBADF" (← pidfd_send_signal pfd .sigzero {}) Errno.EBADF
  logProcessErrHit "pidfd_send_signal" Errno.EBADF "real"
  assertErr "closed pidfd extraBits EBADF" (← pidfd_send_signal pfd .sigzero { extraBits := 1 }) Errno.EBADF
  let (rd, wr) ← assertOk "pipe2" (← pipe2 { cloexec := true })
  try
    assertErr "non-pidfd EBADF" (← pidfd_send_signal rd .sigzero {}) Errno.EBADF
  finally
    closeQuiet rd
    closeQuiet wr

/-- Real `pidfd_send_signal` `invalidArg` error test (unsupported flag bits, conflicting scope bits, invalid and NPTL-reserved `32`/`33` signals). -/
private def err_pidfdSendSignal_invalidArg : IO Unit := do
  let selfPid ← assertOk "getpid" (← getpid)
  let pfd ← assertOk "pidfd_open self" (← pidfd_open selfPid {})
  try
    assertErr "extraBits=1" (← pidfd_send_signal pfd .sigzero { extraBits := 1 }) Errno.EINVAL
    logProcessErrHit "pidfd_send_signal" Errno.EINVAL "real"
    assertErr "extraBits=0x80000000" (← pidfd_send_signal pfd .sigzero { extraBits := 0x80000000 }) Errno.EINVAL
    assertErr "thread+process" (← pidfd_send_signal pfd .sigzero { thread := true, processGroup := true }) Errno.EINVAL
    assertErr "sig=999" (← pidfd_send_signal pfd (.raw 999) {}) Errno.EINVAL
    assertErr "nptl sig=32" (← pidfd_send_signal pfd (.raw 32) {}) Errno.EINVAL
    assertErr "nptl sig=33 thread" (← pidfd_send_signal pfd (.raw 33) { thread := true }) Errno.EINVAL
  finally
    closeQuiet pfd

/-- Real `pidfd_send_signal` `permissionDenied` error test (`EPERM` targeting PID 1/2). -/
private def err_pidfdSendSignal_permissionDenied : IO Unit := do
  let self ← assertOk "getpid" (← getpid)
  for target in [(1 : UInt32), (2 : UInt32)] do
    if target != self then
      if let .ok pfd := (← pidfd_open target {}) then
        let r ← pidfd_send_signal pfd .sigzero {}
        closeQuiet pfd
        if let .error e := r then
          if e == Errno.EPERM || e == Errno.EACCES then
            logProcessErrHit "pidfd_send_signal" e "real"
            return ()
  let canNs ← ProcessEnv.probeUnshare
  if canNs then
    let rc ← assertOk "runNsWorker pidfd-eperm" (← ProcessEnv.runNsWorker true 6 "pidfd-eperm" "0")
    if rc == 0 then
      logProcessErrHit "pidfd_send_signal" Errno.EPERM "real"
      return ()
  if ← isSingleUidUserns then
    let exe ← resolveSelfExe
    let out ← IO.Process.output {
      cmd := exe
      args := #["--process-strace-worker", "seccomp-pidfd-send", "EPERM"]
    }
    assertTrue s!"seccomp-pidfd-send EPERM worker failed (exit={out.exitCode}): {out.stderr}" (out.exitCode == 0)
    logProcessErrHit "pidfd_send_signal" Errno.EPERM "fault_injected"
    return ()
  throw (IO.userError "err_pidfdSendSignal_permissionDenied: could not observe EPERM/EACCES")

/-- Mocked error-coverage test for `getpid` (`ESRCH`, `ECHILD`, `EBADF`, `EINVAL`, `ENOMEM`, `EINTR`). -/
private def err_getpid_mocked : IO Unit := do
  for e in [Errno.ESRCH, Errno.ECHILD, Errno.EBADF, Errno.EINVAL, Errno.ENOMEM, Errno.EINTR] do
    let r ← (mkMockProcessOps e).getpid
    assertErr s!"mocked getpid {e}" r e

/-- Real `seccomp` `SECCOMP_RET_ERRNO | EPERM` error-coverage test for `getpid`. -/
private def err_getpid_seccomp : IO Unit := do
  let selfPid ← assertOk "getpid baseline" (← getpid)
  assertTrue "getpid positive" (selfPid > 0)
  let exe ← resolveSelfExe
  let out ← IO.Process.output {
    cmd := exe
    args := #["--process-strace-worker", "seccomp-getpid", "EPERM"]
  }
  assertTrue s!"seccomp getpid worker failed (exit={out.exitCode}): {out.stderr}" (out.exitCode == 0)
  logProcessErrHit "getpid" Errno.EPERM "fault_injected"

/-- Mocked error-coverage test for `getuid` (`ESRCH`, `ECHILD`, `EBADF`, `EINVAL`, `ENOMEM`, `EINTR`). -/
private def err_getuid_mocked : IO Unit := do
  for e in [Errno.ESRCH, Errno.ECHILD, Errno.EBADF, Errno.EINVAL, Errno.ENOMEM, Errno.EINTR] do
    let r ← (mkMockProcessOps e).getuid
    assertErr s!"mocked getuid {e}" r e

/-- Real `seccomp` `SECCOMP_RET_ERRNO | EPERM` error-coverage test for `getuid`. -/
private def err_getuid_seccomp : IO Unit := do
  let u1 ← assertOk "getuid baseline 1" (← getuid)
  let u2 ← assertOk "getuid baseline 2" (← getuid)
  assertTrue "getuid stable" (u1 == u2)
  let exe ← resolveSelfExe
  let out ← IO.Process.output {
    cmd := exe
    args := #["--process-strace-worker", "seccomp-getuid", "EPERM"]
  }
  assertTrue s!"seccomp getuid worker failed (exit={out.exitCode}): {out.stderr}" (out.exitCode == 0)
  logProcessErrHit "getuid" Errno.EPERM "fault_injected"

private def assertModelOk {α : Type} [BEq α] (label : String)
    (res : Except Errno α × ProcessSysState) (expected : α) : IO Unit :=
  match res.1 with
  | .ok actual => assertTrue label (actual == expected)
  | .error _ => assertTrue label false

private def assertModelErr {α : Type} (label : String)
    (res : Except Errno α × ProcessSysState) (expected : Errno) : IO Unit :=
  match res.1 with
  | .error err => assertTrue label (err == expected)
  | .ok _ => assertTrue label false

/-- Run physical Linux `7.1.6` edge-case reproducers (queued fatal signals, `SIGCHLD = SIG_IGN`, `SA_NOCLDWAIT`, `RLIMIT_CORE`, `CLONE_NEWPID` `PID 1`). -/
def runEdgeCaseReproducers : IO Unit := do
  let _ ← ProcessEnv.setSigchldAutoreap 0
  let (cStop, _) ← assertOk "spawn controlled for queued term" (← ProcessEnv.spawnControlled (-1) false)
  try
    assertOk "SIGSTOP child" (← kill cStop.toInt32 .sigstop)
    let mut stopped := false
    for _ in [:200] do
      let ws ← assertOk "waitpid WUNTRACED" (← waitpid cStop.toInt32 { nohang := true, untraced := true })
      if ws == .stopped cStop 19 then
        stopped := true
        break
      IO.sleep 5
    assertTrue "child stopped" stopped
    assertOk "queue SIGTERM on stopped" (← kill cStop.toInt32 .sigterm)
    let wsAfterTerm ← assertOk "waitpid while stopped" (← waitpid cStop.toInt32 { nohang := true })
    assertTrue "queued SIGTERM stillRunning while stopped" (wsAfterTerm == .stillRunning)
    assertOk "SIGCONT child" (← kill cStop.toInt32 .sigcont)
    let wTerm ← waitUntilReaped cStop
    assertTrue s!"queued SIGTERM fired on SIGCONT, got {repr wTerm}" (wTerm == .signaled cStop 15 false)
  finally
    ProcessEnv.cleanupChild cStop

  let ((zPre, _), _) ← assertOk "spawn pre-seeded zombie" (← ProcessEnv.spawnZombie (-1) false 11 false)
  try
    assertOk "enable SIGCHLD=SIG_IGN" (← ProcessEnv.setSigchldAutoreap 1)
    let (cAuto, _) ← assertOk "spawn autonomous under SIG_IGN" (← ProcessEnv.spawnAutonomous (-1) 0 3)
    IO.sleep 30
    let wPre ← assertOk "pre-seeded zombie waitable under SIG_IGN" (← waitpid zPre.toInt32 { nohang := true })
    assertTrue s!"pre-seeded zombie exited(11), got {repr wPre}" (wPre == .exited zPre 11)
    let mut gotEchild := false
    for _ in [:50] do
      match ← waitpid cAuto.toInt32 { nohang := true } with
      | .error e =>
        if e == Errno.ECHILD then
          gotEchild := true
          break
        else
          throw (IO.userError s!"unexpected autoreap waitpid error: {e}")
      | .ok .stillRunning => IO.sleep 10
      | other => throw (IO.userError s!"unexpected autoreap waitpid: {repr other}")
    assertTrue "autonomous child auto-reaped -> ECHILD" gotEchild
    assertErr "auto-reaped child ESRCH" (← kill cAuto.toInt32 .sigzero) Errno.ESRCH
  finally
    let _ ← ProcessEnv.setSigchldAutoreap 0
    ProcessEnv.cleanupChild zPre

  let ((zCore, _), dumped) ← assertOk "spawn SIGABRT zombie" (← ProcessEnv.spawnZombie (-1) true 6 true)
  try
    let wc ← assertOk "waitpid SIGABRT" (← waitpid zCore.toInt32 {})
    assertTrue s!"SIGABRT decoded core={dumped}, got {repr wc}" (wc == .signaled zCore 6 dumped)
  finally
    ProcessEnv.cleanupChild zCore

  let self ← assertOk "getpid" (← getpid)
  try
    assertOk "setSigIgn SIGCONT" (← ProcessEnv.setSigIgn 18 true)
    assertOk "kill self SIGCONT under SIG_IGN" (← kill self.toInt32 .sigcont)
    assertOk "reset SIGCONT SIG_DFL" (← ProcessEnv.setSigIgn 18 false)
    assertOk "setSigBlock SIGCONT" (← ProcessEnv.setSigBlock 18 true)
    assertOk "kill self SIGCONT under SIG_BLOCK" (← kill self.toInt32 .sigcont)
  finally
    let _ ← ProcessEnv.setSigIgn 18 false
    ProcessEnv.clearSigMask

  let (pdR, pdW) ← assertOk "pipe2 O_DIRECT" (← pipe2 { direct := true })
  try
    let (fdR, flR) ← assertOk "getFdFlags pdR" (← ProcessEnv.getFdFlags pdR)
    let (fdW, flW) ← assertOk "getFdFlags pdW" (← ProcessEnv.getFdFlags pdW)
    assertTrue "pipe2 O_DIRECT rd cloexec" ((fdR &&& 1) == 1)
    assertTrue "pipe2 O_DIRECT wr cloexec" ((fdW &&& 1) == 1)
    assertTrue "pipe2 O_DIRECT rd O_RDONLY" ((flR &&& 3) == 0)
    assertTrue "pipe2 O_DIRECT wr O_WRONLY" ((flW &&& 3) == 1)
    assertTrue "pipe2 O_DIRECT wr flag" ((flW &&& 0x4000) != 0 || (flW &&& 0x10000) != 0)
  finally
    closeQuiet pdR
    closeQuiet pdW
  assertTrue "PipeFlags.toBits notificationPipe"
    (PipeFlags.toBits { notificationPipe := true } == 9)
  let hasWatchQueue ← ProcessEnv.probeKernelWatchQueue
  match ← pipe2 { notificationPipe := true } with
  | .ok (nwR, nwW) =>
    closeQuiet nwR
    closeQuiet nwW
    assertTrue "O_NOTIFICATION_PIPE succeeded despite kernel lacking CONFIG_WATCH_QUEUE" hasWatchQueue
  | .error e =>
    assertTrue "O_NOTIFICATION_PIPE failed despite kernel supporting CONFIG_WATCH_QUEUE" (!hasWatchQueue)
    assertTrue s!"O_NOTIFICATION_PIPE expected ENOPKG, got {e}" (e == Errno.ENOPKG)

  let (cClone1, _) ← assertOk "spawn clone child 1" (← ProcessEnv.spawnCloneChild (-1) true 7)
  try
    let mut cloneZ1 := false
    for _ in [:200] do
      let (zst, _) ← ProcessEnv.probeZombie cClone1
      if zst != 0 then
        cloneZ1 := true
        break
      IO.sleep 5
    assertTrue "clone child 1 became zombie" cloneZ1
    assertErr "waitpid default ECHILD on clone child" (← waitpid cClone1.toInt32 { nohang := true }) Errno.ECHILD
    let wc1 ← assertOk "waitpid __WCLONE" (← waitpid cClone1.toInt32 { nohang := true, wclone := true })
    assertTrue s!"waitpid __WCLONE exited(7), got {repr wc1}" (wc1 == .exited cClone1 7)
  finally
    ProcessEnv.cleanupChild cClone1

  let (cClone2, _) ← assertOk "spawn clone child 2" (← ProcessEnv.spawnCloneChild (-1) true 8)
  try
    let mut cloneZ2 := false
    for _ in [:200] do
      let (zst, _) ← ProcessEnv.probeZombie cClone2
      if zst != 0 then
        cloneZ2 := true
        break
      IO.sleep 5
    assertTrue "clone child 2 became zombie" cloneZ2
    let wc2 ← assertOk "waitpid __WALL on clone child" (← waitpid cClone2.toInt32 { nohang := true, wall := true })
    assertTrue s!"waitpid __WALL exited(8), got {repr wc2}" (wc2 == .exited cClone2 8)
  finally
    ProcessEnv.cleanupChild cClone2

  let ((cSib, _), (_, sibTh)) ← assertOk "spawn sibling child" (← ProcessEnv.spawnSiblingChild (-1))
  try
    assertOk "kill sibling child" (← kill cSib.toInt32 .sigkill)
    let mut sibZ := false
    for _ in [:200] do
      let (zst, _) ← ProcessEnv.probeZombie cSib
      if zst != 0 then
        sibZ := true
        break
      IO.sleep 5
    assertTrue "sibling child became zombie" sibZ
    assertErr "waitpid __WNOTHREAD ECHILD on sibling child" (← waitpid cSib.toInt32 { nohang := true, wnothread := true }) Errno.ECHILD
    assertErr "waitpid __WALL|__WNOTHREAD ECHILD on sibling child" (← waitpid cSib.toInt32 { nohang := true, wall := true, wnothread := true }) Errno.ECHILD
    let wsib ← waitUntilReaped cSib
    assertTrue s!"sibling child reaped without __WNOTHREAD, got {repr wsib}" (wsib == .signaled cSib 9 false)
  finally
    ProcessEnv.cleanupChild cSib
    ProcessEnv.joinThread sibTh

  let hasPidfdThread ← ProcessEnv.probeKernelPidfdThread
  let (tid, th) ← assertOk "spawn thread for PIDFD_THREAD" (← ProcessEnv.spawnThread)
  try
    match ← pidfd_open tid { thread := true } with
    | .ok tpfd =>
      try
        assertOk "pidfd_send_signal on PIDFD_THREAD" (← pidfd_send_signal tpfd .sigzero {})
        assertErr "pidfd_send_signal PROCESS_GROUP on thread fd ESRCH" (← pidfd_send_signal tpfd .sigzero { processGroup := true }) Errno.ESRCH
      finally
        closeQuiet tpfd
    | .error e =>
      if hasPidfdThread then
        throw (IO.userError s!"PIDFD_THREAD supported by kernel but pidfd_open failed with {e}")
      assertTrue s!"PIDFD_THREAD expected EINVAL if unsupported, got {e}" (e == Errno.EINVAL)
  finally
    ProcessEnv.joinThread th

  let (cThr, (_, wTid)) ← assertOk "spawn threaded child" (← ProcessEnv.spawnThreadedChild (-1))
  try
    assertOk "kill threaded child" (← kill cThr.toInt32 .sigkill)
    let mut thrZ := false
    for _ in [:200] do
      let (zst, _) ← ProcessEnv.probeZombie cThr
      if zst != 0 then
        thrZ := true
        break
      IO.sleep 5
    assertTrue "threaded child leader became zombie" thrZ
    match ← pidfd_open wTid { thread := true } with
    | .ok tpfd =>
      closeQuiet tpfd
      throw (IO.userError "expected pidfd_open PIDFD_THREAD on worker of zombie leader to fail")
    | .error e =>
      assertTrue s!"pidfd_open on worker of zombie leader expected ESRCH/EINVAL, got {e}" (e == Errno.ESRCH || e == Errno.EINVAL)
    assertErr "kill worker tid of zombie leader ESRCH" (← kill wTid.toInt32 .sigzero) Errno.ESRCH
    let wthr ← waitUntilReaped cThr
    assertTrue s!"threaded child reaped SIGKILL, got {repr wthr}" (wthr == .signaled cThr 9 false)
  finally
    ProcessEnv.cleanupChild cThr

  let _ ← ProcessEnv.setSigIgn 15 false
  let (cDz, (_, _dzTid)) ← assertOk "spawn delayed-zombie child" (← ProcessEnv.spawnDelayedZombie (-1) 7)
  try
    let wDz0 ← assertOk "delayed-zombie initially stillRunning" (← waitpid cDz.toInt32 { nohang := true })
    assertTrue s!"delayed-zombie expected stillRunning before signal, got {repr wDz0}" (wDz0 == .stillRunning)
    let dzPfd ← assertOk "pidfd_open delayed-zombie leader" (← pidfd_open cDz {})
    try
      assertOk "pidfd_send_signal THREAD SIGTERM on delayed-zombie leader"
        (← pidfd_send_signal dzPfd .sigterm { thread := true })
      IO.sleep 10
      let wDz1 ← assertOk "delayed-zombie waitpid after THREAD SIGTERM" (← waitpid cDz.toInt32 { nohang := true })
      assertTrue s!"delayed-zombie expected stillRunning after PIDFD_SIGNAL_THREAD, got {repr wDz1}"
        (wDz1 == .stillRunning)
      assertOk "pidfd_send_signal THREAD_GROUP SIGTERM on delayed-zombie leader"
        (← pidfd_send_signal dzPfd .sigterm { threadGroup := true })
      let wDz2 ← assertOk "delayed-zombie blocking waitpid after THREAD_GROUP" (← waitpid cDz.toInt32 {})
      assertTrue s!"delayed-zombie expected signaled(15) after PIDFD_SIGNAL_THREAD_GROUP, got {repr wDz2}"
        (wDz2 == .signaled cDz 15 false)
    finally
      closeQuiet dzPfd
  finally
    ProcessEnv.cleanupChild cDz

  if hasPidfdThread then
    let (cDzThr, (_, _dzThrTid)) ← assertOk "spawn delayed-zombie for PIDFD_THREAD" (← ProcessEnv.spawnDelayedZombie (-1) 9)
    try
      let dzThrPfd ← assertOk "pidfd_open delayed-zombie PIDFD_THREAD" (← pidfd_open cDzThr { thread := true })
      try
        assertOk "pidfd_send_signal default scope on PIDFD_THREAD delayed-zombie leader"
          (← pidfd_send_signal dzThrPfd .sigterm {})
        IO.sleep 10
        let wDzThr1 ← assertOk "delayed-zombie waitpid after PIDFD_THREAD default" (← waitpid cDzThr.toInt32 { nohang := true })
        assertTrue s!"delayed-zombie expected stillRunning after PIDFD_THREAD default, got {repr wDzThr1}"
          (wDzThr1 == .stillRunning)
        assertOk "pidfd_send_signal THREAD_GROUP override on PIDFD_THREAD delayed-zombie leader"
          (← pidfd_send_signal dzThrPfd .sigterm { threadGroup := true })
        let wDzThr2 ← waitUntilReaped cDzThr
        assertTrue s!"delayed-zombie expected signaled(15) after PIDFD_THREAD+THREAD_GROUP, got {repr wDzThr2}"
          (wDzThr2 == .signaled cDzThr 15 false)
      finally
        closeQuiet dzThrPfd
    finally
      ProcessEnv.cleanupChild cDzThr

  try
    assertOk "setNofileMode 1 (0 free)" (← ProcessEnv.setNofileMode 1)
    assertErr "pipe2 EMFILE with 0 free FDs" (← pipe2 {}) Errno.EMFILE
    assertErr "pidfd_open EMFILE with 0 free FDs" (← pidfd_open self {}) Errno.EMFILE
    assertOk "setNofileMode 2 (1 free)" (← ProcessEnv.setNofileMode 2)
    assertErr "pipe2 EMFILE with 1 free FD" (← pipe2 {}) Errno.EMFILE
    let pfd1 ← assertOk "pidfd_open succeeds with 1 free FD" (← pidfd_open self {})
    closeQuiet pfd1
  finally
    let _ ← ProcessEnv.setNofileMode 0

  try
    assertOk "enable SA_NOCLDSTOP" (← ProcessEnv.setSigchldAutoreap 3)
    let (cNcs, _) ← assertOk "spawn stopped under SA_NOCLDSTOP" (← ProcessEnv.spawnStopped (-1) 19)
    try
      let wsNcs ← assertOk "waitpid WUNTRACED under SA_NOCLDSTOP" (← waitpid cNcs.toInt32 { nohang := true, untraced := true })
      assertTrue s!"SA_NOCLDSTOP still WUNTRACED visible, got {repr wsNcs}" (wsNcs == .stopped cNcs 19)
    finally
      ProcessEnv.cleanupChild cNcs
  finally
    let _ ← ProcessEnv.setSigchldAutoreap 0

  try
    assertOk "enable PR_SET_CHILD_SUBREAPER" (← ProcessEnv.setSubreaper true)
    let (gc, _) ← assertOk "spawn reparented grandchild" (← ProcessEnv.spawnReparentedGrandchild (-1))
    try
      assertOk "kill reparented grandchild" (← kill gc.toInt32 .sigkill)
      let wgc ← waitUntilReaped gc
      assertTrue s!"subreaper reaped grandchild SIGKILL, got {repr wgc}" (wgc == .signaled gc 9 false)
    finally
      ProcessEnv.cleanupChild gc
  finally
    let _ ← ProcessEnv.setSubreaper false

  if ← ProcessEnv.probeUnshare then
    let rc0 ← assertOk "ns zero-pgid check" (← ProcessEnv.runNsWorker false 0 "zero-pgid" "0")
    assertTrue s!"ns zero-pgid worker exited {rc0}" (rc0 == 0)
    let rc1 ← assertOk "ns pid1-unkillable asPid2=true check" (← ProcessEnv.runNsWorker true 6 "pid1-unkillable" "0")
    assertTrue s!"ns pid1-unkillable asPid2=true worker exited {rc1}" (rc1 == 0)
    let rc2 ← assertOk "ns pid1-unkillable asPid2=false check" (← ProcessEnv.runNsWorker true 0 "pid1-unkillable" "0")
    assertTrue s!"ns pid1-unkillable asPid2=false worker exited {rc2}" (rc2 == 0)
    let rcUid0 ← assertOk "ns mapUid0 check-uid0" (← ProcessEnv.runNsWorker true 4 "check-uid0" "0")
    assertTrue s!"ns mapUid0 check-uid0 worker exited {rcUid0}" (rcUid0 == 0)
    let rcOrph ← assertOk "ns orphan-tty-cont check" (← ProcessEnv.runNsWorker true 0 "orphan-tty-cont" "0")
    assertTrue s!"ns orphan-tty-cont worker exited {rcOrph}" (rcOrph == 0)
    let exeNs ← resolveSelfExe
    let outNeg1 ← IO.Process.output {
      cmd := exeNs
      args := #["--suite", "process", "--ns-worker", "kill-neg1-foreign-spawn", "0"]
    }
    assertTrue s!"ns kill-neg1-foreign-spawn failed (exit={outNeg1.exitCode}): {outNeg1.stderr}" (outNeg1.exitCode == 0)

  let fd0Ok ← assertOk "pidfd_open with fd 0 free" (← ProcessEnv.checkPidfdFd0)
  assertTrue "pidfd_open succeeds returning fd 0 when closed" fd0Ok
  let (cAuto1s, _) ← assertOk "spawnAutonomous >= 1s delay" (← ProcessEnv.spawnAutonomous (-1) 1000000 42)
  try
    IO.sleep 20
    let (zSt, _) ← ProcessEnv.probeZombie cAuto1s
    assertTrue "spawnAutonomous delay_us >= 1000000 sleeps instead of EINVAL exit" (zSt == 0)
  finally
    ProcessEnv.cleanupChild cAuto1s
  assertErr "setSigBlock invalid signal 0 EINVAL" (← ProcessEnv.setSigBlock 0 true) Errno.EINVAL
  assertErr "setSigBlock invalid signal 99 EINVAL" (← ProcessEnv.setSigBlock 99 true) Errno.EINVAL

  let efaultAborted ← assertOk "seccomp SECCOMP_RET_ERRNO | EFAULT probe" (← ProcessEnv.checkSeccompEfaultAbort)
  assertTrue "seccomp SECCOMP_RET_ERRNO | EFAULT triggers SIGABRT" efaultAborted

  for secErr in #[(1 : UInt32), 4, 5, 7, 9, 12, 28, 104, 116, 122, 4095] do
    let closeOk ← assertOk s!"seccomp SYS_close errno={secErr} probe" (← ProcessEnv.checkFdCloseSeccomp secErr)
    assertTrue s!"seccomp SYS_close errno={secErr} contract" closeOk

  assertErr "waitpid upper extraBits 0x80000000 EINVAL" (← waitpid (-1) { extraBits := 0x80000000 }) Errno.EINVAL
  assertErr "waitpid upper extraBits 0x04000000 EINVAL" (← waitpid (-1) { extraBits := 0x04000000 }) Errno.EINVAL
  assertErr "pidfd_open upper extraBits 0x80000000 EINVAL" (← pidfd_open self { extraBits := 0x80000000 }) Errno.EINVAL

  let (cDzEx, _) ← assertOk "spawn autonomous delayed-zombie" (← ProcessEnv.spawnDelayedZombie (-1) 23 8000 55)
  try
    let wDzEx ← assertOk "waitpid autonomous delayed-zombie exited" (← waitpid cDzEx.toInt32 {})
    assertTrue s!"autonomous delayed-zombie expected exited(55), got {repr wDzEx}" (wDzEx == .exited cDzEx 55)
  finally
    ProcessEnv.cleanupChild cDzEx

  let (defR, defW) ← assertOk "default pipe2" (← pipe2)
  try
    let (defFdR, _) ← assertOk "default pipe2 fd flags" (← ProcessEnv.getFdFlags defR)
    assertTrue "default pipe2 sets FD_CLOEXEC" ((defFdR &&& 1) == 1)
  finally
    closeQuiet defR
    closeQuiet defW
  assertErr "default waitpid -1 ECHILD" (← waitpid (-1)) Errno.ECHILD
  let defSelfPfd ← assertOk "default pidfd_open self" (← pidfd_open self)
  try
    let (cZero, probeSock) ← assertOk "spawn sigpending probe child" (← ProcessEnv.spawnSigPendingProbe)
    try
      assertErr "waitpid __WCLONE ECHILD on SIGCHLD fork child"
        (← waitpid cZero.toInt32 { nohang := true, wclone := true }) Errno.ECHILD
      let czPfd ← assertOk "pidfd_open cZero" (← pidfd_open cZero {})
      try
        assertOk "kill cZero sigzero no-queue" (← kill cZero.toInt32 .sigzero)
        assertOk "pidfd_send_signal cZero sigzero no-queue" (← pidfd_send_signal czPfd .sigzero)
        assertOk "default pidfd_send_signal" (← pidfd_send_signal defSelfPfd .sigzero)
        assertErr "pidfd_send_signal upper extraBits 0x80000000 EINVAL"
          (← pidfd_send_signal czPfd .sigzero { extraBits := 0x80000000 }) Errno.EINVAL
      catch e =>
        closeQuiet czPfd
        throw e
      assertOk "closeFd czPfd after pidfd_send_signal unpinned" (← ProcessEnv.closeFd czPfd)
      let pndMask ← ProcessEnv.finishSigPendingProbe cZero probeSock
      assertTrue s!"sigzero must not queue any signal (mask={pndMask})" (pndMask == 0)
    finally
      closeQuiet probeSock
      ProcessEnv.cleanupChild cZero
    assertTrue "threadGroup flag bit" (PidfdSignalFlags.toBits { threadGroup := true } == 2)
    assertOk "pidfd_send_signal threadGroup" (← pidfd_send_signal defSelfPfd .sigzero { threadGroup := true })
    assertErr "thread+threadGroup EINVAL"
      (← pidfd_send_signal defSelfPfd .sigzero { thread := true, threadGroup := true }) Errno.EINVAL
    assertErr "threadGroup+processGroup EINVAL"
      (← pidfd_send_signal defSelfPfd .sigzero { threadGroup := true, processGroup := true }) Errno.EINVAL
  finally
    closeQuiet defSelfPfd
  for (sig, tag, snum, sU32) in [
      (Signal.sighup, (1 : UInt8), (1 : Int), (1 : UInt32)),
      (.sigint, 2, 2, 2),
      (.sigusr1, 4, 10, 10),
      (.sigusr2, 5, 12, 12),
      (.raw 34, 9, 34, 34),
      (.raw 64, 9, 64, 64)] do
    assertTrue s!"signal {snum} toRaw" (sig.toRaw == (tag, if tag == 9 then Int32.ofInt snum else 0))
    assertTrue s!"signal {snum} toLinuxNum" (sig.toLinuxNum == snum)
    assertErr s!"kill ESRCH sig {snum}" (← kill Int32.minValue sig) Errno.ESRCH
    let _ ← ProcessEnv.setSigIgn sU32 false
    let (cSig, _) ← assertOk s!"spawn child sig {sU32}" (← ProcessEnv.spawnControlled (-1) false)
    try
      assertOk s!"deliver sig {sU32}" (← kill cSig.toInt32 sig)
      let wSig ← waitUntilReaped cSig
      assertTrue s!"expected signaled({cSig}, {sU32}, false), got {repr wSig}"
        (wSig == .signaled cSig sU32 false)
    finally
      ProcessEnv.cleanupChild cSig
  for (errVal, expKind) in [
      (Errno.ESRCH, ProcessErrorKind.noSuchProcess),
      (Errno.ENOENT, .noSuchProcess),
      (Errno.ECHILD, .noChild),
      (Errno.EBADF, .badFd),
      (Errno.EINVAL, .invalidArg),
      (Errno.ENOSYS, .invalidArg),
      (Errno.EOPNOTSUPP, .invalidArg),
      (Errno.EPERM, .permissionDenied),
      (Errno.EACCES, .permissionDenied),
      (Errno.ENOMEM, .transientOrResource)] do
    assertTrue s!"ProcessErrorKind.ofErrno {errVal}"
      (decide (ProcessErrorKind.ofErrno errVal = expKind))

  let s0 := ProcessSysState.initial 1000 1000 1000
  match ← pipe2 { notificationPipe := true } with
  | .ok (nr, nw) =>
    closeQuiet nr
    closeQuiet nw
    assertTrue "model watchQueueSupported=true accepts notificationPipe"
      (Process.allowedStep (s0.withWatchQueueSupported true) (.pipe2 { notificationPipe := true }) (.piped 0 1)).isSome
  | .error e =>
    assertTrue s!"notificationPipe expected ENOPKG, got {e}"
      (e == Errno.ENOPKG)
    assertTrue "model watchQueueSupported=false accepts live notificationPipe err"
      (Process.allowedStep s0 (.pipe2 { notificationPipe := true }) (.err e)).isSome
    assertTrue "model watchQueueSupported=false rejects EINVAL on valid notificationPipe"
      (Process.allowedStep s0 (.pipe2 { notificationPipe := true }) (.err Errno.EINVAL)).isNone
  assertTrue "model rejects EPERM on notificationPipe without seccomp"
    (Process.allowedStep s0 (.pipe2 { notificationPipe := true }) (.err Errno.EPERM)).isNone
  assertModelOk "modelOps watchQueueSupported=true opens notificationPipe"
    ((modelOps.pipe2 { notificationPipe := true }).run (s0.withWatchQueueSupported true)) (0, 1)

  for ttyStopSig in #[(21 : UInt32), 22] do
    let _ ← ProcessEnv.setSigIgn ttyStopSig false
    let (cTty, _) ← assertOk s!"spawn child for tty stop {ttyStopSig}" (← ProcessEnv.spawnControlled 0 false)
    try
      assertOk s!"deliver tty stop {ttyStopSig}" (← kill cTty.toInt32 (.raw ttyStopSig.toInt32))
      let mut sawStop := false
      for _ in [:200] do
        let w ← assertOk "waitpid tty stop" (← waitpid cTty.toInt32 { nohang := true, untraced := true })
        if w == .stopped cTty ttyStopSig then
          sawStop := true
          break
        IO.sleep 5
      assertTrue s!"expected stopped({cTty}, {ttyStopSig})" sawStop
    finally
      ProcessEnv.cleanupChild cTty

  let sClone := s0
    |>.spawnZombieExited 2400 10 2400 false false
    |>.spawnZombieExited 2401 20 2401 true false
    |>.spawnZombieExited 2402 30 2402 false true
  assertModelErr "model waitpid rejects __WCLONE child without wclone/wall"
    ((modelOps.waitpid 2401 { nohang := true }).run sClone) Errno.ECHILD
  assertModelOk "model waitpid reaps __WCLONE child with wclone=true"
    ((modelOps.waitpid 2401 { nohang := true, wclone := true }).run sClone) (.exited 2401 20)
  assertModelErr "model waitpid rejects sibling-thread child under wnothread=true"
    ((modelOps.waitpid 2402 { nohang := true, wnothread := true }).run sClone) Errno.ECHILD
  let sSess := (s0.registerForeignProc 2500 2500 false true).registerForeignProc 2501 2501 false false
  assertModelOk "model allows cross-UID SIGCONT in same session"
    ((modelOps.kill 2500 .sigcont).run sSess) ()
  assertModelErr "model rejects cross-UID SIGCONT across sessions with EPERM"
    ((modelOps.kill 2501 .sigcont).run sSess) Errno.EPERM
  assertModelErr "model rejects cross-UID SIGTERM in same session with EPERM"
    ((modelOps.kill 2500 .sigterm).run sSess) Errno.EPERM
  let (_, sTerm) := (modelOps.kill 2600 .sigterm).run (s0.spawnRunningChild 2600 2600)
  assertTrue "model rejects coreDumped=true on SIGTERM"
    (Process.allowedStep sTerm (.waitpid 2600 {}) (.waited (.signaled 2600 15 true))).isNone
  let (_, sOrphTtin) := (modelOps.kill 2603 (.raw 21)).run (s0.spawnRunningChild 2603 2603 none false false true)
  assertTrue "model drops SIGTTIN on orphaned PGID"
    (Process.allowedStep sOrphTtin (.waitpid 2603 { nohang := true, untraced := true }) (.waited (.stopped 2603 21))).isNone
  let sAliveSub := (s0.spawnRunningChild 2100 2100)
    |>.upsertProc 2101 { pgid := 2100, role := .thread 2100, lifecycle := .alive { auto := .controlled } }
    |>.upsertProc 2102 { pgid := 2100, role := .thread 2100, lifecycle := .alive { auto := .planned (.exited 77) } }
  assertModelOk "modelOps blocking waitpid reaps alive leader via planned subthread"
    ((modelOps.waitpid 2100 { nohang := false }).run sAliveSub) (.exited 2100 77)
  let sShadowBase := s0.spawnZombieExited 2300 99 2300
  let sShadow : ProcessSysState :=
    { sShadowBase with procs := (2300, { pgid := 2300, role := .child .sigchld false, lifecycle := .zombie (.exited 42) }) :: sShadowBase.procs }
  let (_, sShadowReaped) := (modelOps.waitpid 2300 { nohang := true }).run sShadow
  assertTrue "reapThreadGroup prunes shadowed duplicate PID entries"
    (assocGet sShadowReaped.procs 2300).isNone

/-- Run all `Process` real and mocked regression and error-path checks (dispatched by `leanswe-fuzz --smoke`). -/
def runChecks : IO Unit := do
  assume_process_pipe2_atomicFlagsAndFdPair
  assume_process_waitpid_wait4StatusAndReap
  assume_process_kill_signalAndGroupRouting
  assume_process_pidfdOpen_nr434AndCloexec
  assume_process_pidfdSendSignal_nr424AndReapRaceGuard
  assume_process_getpid_positiveAndStable
  assume_process_getuid_stableRealUid
  err_pipe2_mocked
  err_pipe2_invalidArg
  err_waitpid_noSuchProcess
  err_waitpid_noChild
  err_waitpid_mocked
  err_waitpid_invalidArg
  err_kill_noSuchProcess
  err_kill_mocked
  err_kill_invalidArg
  err_kill_permissionDenied
  err_pidfdOpen_noSuchProcess
  err_pidfdOpen_mocked
  err_pidfdOpen_invalidArg
  err_pidfdSendSignal_noSuchProcess
  err_pidfdSendSignal_mocked
  err_pidfdSendSignal_badFd
  err_pidfdSendSignal_invalidArg
  err_pidfdSendSignal_permissionDenied
  err_getpid_mocked
  err_getpid_seccomp
  err_getuid_mocked
  err_getuid_seccomp
  runEdgeCaseReproducers

private def checkWorkerErr (opName : String) (s0 : ProcessSysState) (req : ProcessReq) (expected : Errno)
    {α : Type} (res : Except Errno α) : IO UInt32 := do
  match res with
  | .error e =>
    if e != expected then
      IO.eprintln s!"process strace-worker ({opName}): expected {expected}, got {e}"
      return 2
    if (Process.allowedStep s0 req (.err e)).isNone then
      IO.eprintln s!"process strace-worker ({opName}): allowedStep rejected injected error {e}"
      return 5
    return 0
  | .ok _ =>
    IO.eprintln s!"process strace-worker ({opName}): expected error {expected}, got ok"
    return 3

private def straceWorker (opName errName : String) : IO UInt32 := do
  if opName == "noop" then
    return 0
  let expected : Errno := match errName with
    | "EINTR" => Errno.EINTR
    | "ENOMEM" => Errno.ENOMEM
    | "EMFILE" => Errno.EMFILE
    | "ENFILE" => Errno.ENFILE
    | "EIO" => Errno.EIO
    | "ENOSPC" => Errno.ENOSPC
    | "EPERM" => Errno.EPERM
    | _ => 0
  let maxAttempts : Nat := 8
  let sBase := ProcessSysState.initial 1000 1000 1000
  match opName with
  | "pipe2" =>
    let req : ProcessReq := .pipe2 { cloexec := true }
    for _ in [:maxAttempts] do
      let res ← pipe2 { cloexec := true }
      match res with
      | .ok (r, w) =>
        closeQuiet r
        closeQuiet w
      | .error _ =>
        return (← checkWorkerErr opName sBase req expected res)
    return (← checkWorkerErr opName sBase req expected (Except.ok () : Except Errno Unit))
  | "wait4" =>
    let req : ProcessReq := .waitpid Int32.minValue {}
    for _ in [:maxAttempts] do
      let res ← waitpid Int32.minValue {}
      if let .error e := res then
        if e == expected || e != Errno.ESRCH then
          return (← checkWorkerErr opName sBase req expected res)
    return (← checkWorkerErr opName sBase req expected (Except.error Errno.ESRCH : Except Errno Unit))
  | "kill" =>
    let req : ProcessReq := .kill Int32.minValue .sigzero
    for _ in [:maxAttempts] do
      let res ← kill Int32.minValue .sigzero
      if let .error e := res then
        if e == expected || e != Errno.ESRCH then
          return (← checkWorkerErr opName sBase req expected res)
    return (← checkWorkerErr opName sBase req expected (Except.error Errno.ESRCH : Except Errno Unit))
  | "pidfd_open" =>
    let selfPid ← assertOk "getpid" (← getpid)
    let sSelf := ProcessSysState.initial selfPid selfPid 1000
    let req : ProcessReq := .pidfd_open selfPid { nonblock := true }
    for _ in [:maxAttempts] do
      let res ← pidfd_open selfPid { nonblock := true }
      match res with
      | .ok fd => closeQuiet fd
      | .error _ =>
        return (← checkWorkerErr opName sSelf req expected res)
    return (← checkWorkerErr opName sSelf req expected (Except.ok () : Except Errno Unit))
  | "pidfd_send_signal" =>
    let selfPid ← assertOk "getpid" (← getpid)
    let pfd ← assertOk "pidfd_open self for strace" (← pidfd_open selfPid {})
    let sOpen := commitPidfd (ProcessSysState.initial selfPid selfPid 1000) 0 selfPid false false
    let req : ProcessReq := .pidfd_send_signal 0 .sigzero {}
    try
      for _ in [:maxAttempts] do
        let res ← pidfd_send_signal pfd .sigzero {}
        if let .error _ := res then
          return (← checkWorkerErr opName sOpen req expected res)
      return (← checkWorkerErr opName sOpen req expected (Except.ok () : Except Errno Unit))
    finally
      closeQuiet pfd
  | "getpid" =>
    let req : ProcessReq := .getpid
    for _ in [:maxAttempts] do
      let res ← getpid
      if let .error _ := res then
        return (← checkWorkerErr opName sBase req expected res)
    return (← checkWorkerErr opName sBase req expected (Except.ok () : Except Errno Unit))
  | "getuid" =>
    let req : ProcessReq := .getuid
    for _ in [:maxAttempts] do
      let res ← getuid
      if let .error _ := res then
        return (← checkWorkerErr opName sBase req expected res)
    return (← checkWorkerErr opName sBase req expected (Except.ok () : Except Errno Unit))
  | "seccomp-getpid" =>
    match ← ProcessEnv.installSeccompErrno 5 Errno.EPERM with
    | .error e =>
      IO.eprintln s!"process seccomp-getpid setup failed: {e}"
      return 1
    | .ok () =>
      return (← checkWorkerErr opName (sBase.withAmbientSeccomp true) .getpid expected (← getpid))
  | "seccomp-getuid" =>
    match ← ProcessEnv.installSeccompErrno 6 Errno.EPERM with
    | .error e =>
      IO.eprintln s!"process seccomp-getuid setup failed: {e}"
      return 1
    | .ok () =>
      return (← checkWorkerErr opName (sBase.withAmbientSeccomp true) .getuid expected (← getuid))
  | "seccomp-kill" =>
    let selfPid ← assertOk "getpid" (← getpid)
    match ← ProcessEnv.installSeccompErrno 2 expected with
    | .error e =>
      IO.eprintln s!"process seccomp-kill setup failed: {e}"
      return 1
    | .ok () =>
      let sSec := (ProcessSysState.initial selfPid selfPid 1000).withAmbientSeccomp true
      return (← checkWorkerErr opName sSec (.kill selfPid.toInt32 .sigzero) expected (← kill selfPid.toInt32 .sigzero))
  | "seccomp-pidfd-send" =>
    let selfPid ← assertOk "getpid" (← getpid)
    let pfd ← assertOk "pidfd_open self for seccomp-pidfd-send" (← pidfd_open selfPid {})
    let sOpen := (commitPidfd (ProcessSysState.initial selfPid selfPid 1000) 0 selfPid false false).withAmbientSeccomp true
    try
      match ← ProcessEnv.installSeccompErrno 4 expected with
      | .error e =>
        IO.eprintln s!"process seccomp-pidfd-send setup failed: {e}"
        return 1
      | .ok () =>
        return (← checkWorkerErr opName sOpen (.pidfd_send_signal 0 .sigzero {}) expected (← pidfd_send_signal pfd .sigzero {}))
    finally
      closeQuiet pfd
  | _ =>
    IO.eprintln s!"process strace-worker: unknown op {opName}"
    return 4

private def countBaselineSyscalls (exe : String) (sysName : String) : IO Nat := do
  let out ← IO.Process.output {
    cmd := "strace"
    args := #["-f", "-qq", "-e", s!"trace={sysName}", exe, "--process-strace-worker", "noop", "EINTR"]
  }
  let needle := sysName ++ "("
  let lines := out.stderr.splitOn "\n"
  return lines.foldl (fun acc line => if (line.splitOn needle).length > 1 then acc + 1 else acc) 0

/-- Run live `strace -f` fault-injection tests verifying transient errnos across all 7 syscalls and `allowedStep` rejection of `EMFILE`/`ENFILE` on non-FD operations. -/
def runStraceFaultCheck : IO Unit := do
  let sBase := ProcessSysState.initial 1000 1000 1000
  let sOpen := commitPidfd sBase 0 1000 false false
  for badErr in [Errno.EMFILE, Errno.ENFILE] do
    assertTrue s!"allowedStep rejects {badErr} on waitpid" (Process.allowedStep sBase (.waitpid Int32.minValue {}) (.err badErr)).isNone
    assertTrue s!"allowedStep rejects {badErr} on kill" (Process.allowedStep sBase (.kill Int32.minValue .sigzero) (.err badErr)).isNone
    assertTrue s!"allowedStep rejects {badErr} on pidfd_send_signal" (Process.allowedStep sOpen (.pidfd_send_signal 0 .sigzero {}) (.err badErr)).isNone
    assertTrue s!"allowedStep rejects {badErr} on getpid" (Process.allowedStep sBase .getpid (.err badErr)).isNone
    assertTrue s!"allowedStep rejects {badErr} on getuid" (Process.allowedStep sBase .getuid (.err badErr)).isNone
  let exe ← resolveSelfExe
  let cases : List (String × List String) :=
    [ ("pipe2", ["EINTR", "ENOMEM", "EMFILE", "ENFILE", "EIO", "ENOSPC"])
    , ("wait4", ["EINTR", "ENOMEM", "EIO", "ENOSPC"])
    , ("kill", ["EINTR", "ENOMEM", "EIO", "ENOSPC"])
    , ("pidfd_open", ["EINTR", "ENOMEM", "EMFILE", "ENFILE", "EIO", "ENOSPC"])
    , ("pidfd_send_signal", ["EINTR", "ENOMEM", "EIO", "ENOSPC"])
    , ("getpid", ["EINTR", "ENOMEM", "EIO", "ENOSPC"])
    , ("getuid", ["EINTR", "ENOMEM", "EIO", "ENOSPC"]) ]
  for (sysName, errs) in cases do
    let baseCount ← countBaselineSyscalls exe sysName
    let whenIdx := baseCount + 1
    for errName in errs do
      let out ← IO.Process.output {
        cmd := "strace"
        args := #["-f", "-qq", "-o", "/dev/null",
          "-e", s!"inject={sysName}:error={errName}:when={whenIdx}",
          exe, "--process-strace-worker", sysName, errName]
      }
      if out.exitCode != 0 then
        throw (IO.userError s!"strace fault-injection failed for {sysName}/{errName} (when={whenIdx}, exit={out.exitCode}): {out.stderr}")

/-- Handle `--process-strace-fault-check` and `--process-strace-worker` subcommands dispatched by `leanswe-fuzz` (`Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker`). -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    runStraceFaultCheck
    IO.println "PROCESS_STRACE_FAULT_CHECK: ok (all 7 syscalls x EINTR/ENOMEM/EIO/ENOSPC + pipe2/pidfd_open EMFILE/ENFILE + allowedStep)"
    return 0
  | ["--worker", opName, errName] =>
    straceWorker opName errName
  | _ =>
    IO.eprintln s!"unknown process strace args: {args}"
    return 1

end Fuzz.LinuxSyscall.Process.Strace

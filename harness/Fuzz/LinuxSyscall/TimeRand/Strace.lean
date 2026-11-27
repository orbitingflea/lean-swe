import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.TimeRand.Impl
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.LinuxSyscall.TimeRand.Strace

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

private def logTimeRandErrHit (op : String) (e : Errno) (mode : String) : IO Unit :=
  Fuzz.Common.logErrHit s!"LeanSwe.LinuxSyscall.TimeRand.{op}"
    (reprStr (TimeRandErrorKind.ofErrno e)).trimAscii.toString mode

private def failWith {α : Type} (msg : String) : IO α :=
  throw (IO.userError s!"TimeRand.Strace: {msg}")

@[extern "leanswe_sys_clock_gettime"]
private opaque rawClockGettimeForTest : UInt32 → BaseIO (Except Errno (Int64 × UInt32))

@[extern "leanswe_sys_clock_nanosleep"]
private opaque rawClockNanosleepForTest : UInt32 → UInt8 → Int64 → UInt32 → BaseIO (Except Errno Unit)

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    failWith s!"assertion failed: {label}"

private def expectOk {α : Type} (label : String) (res : Except Errno α) : IO α := do
  match res with
  | .ok v => return v
  | .error e => failWith s!"{label}: unexpected error {Errno.name e} ({e})"

private def expectErr {α : Type} (label : String) (expected : Errno) (res : Except Errno α) : IO Unit := do
  match res with
  | .ok _ => failWith s!"{label}: expected {Errno.name expected}, got ok"
  | .error e =>
    if e != expected then
      failWith s!"{label}: expected {Errno.name expected} ({expected}), got {Errno.name e} ({e})"

private def mkMockRawOps (getRes : Except Errno (Int64 × UInt32))
    (sleepRes : Except Errno Unit)
    (randRes : Except Errno ByteArray) : Internal.PosixTimeRandOps :=
  { clock_gettime := fun _ => return getRes
    clock_nanosleep := fun _ _ _ _ => return sleepRes
    getrandom := fun _ _ => return randRes }

/-- Runtime verification for `LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockGettime_realtimeAndMonotonic`. -/
private def assume_timerand_clockGettime_realtimeAndMonotonic : IO Unit := do
  let rt ← expectOk "clock_gettime realtime" (← clock_gettime .realtime)
  assertTrue "realtime valid nsec" rt.hasValidNsec
  let m0 ← expectOk "clock_gettime monotonic #0" (← clock_gettime .monotonic)
  assertTrue "monotonic #0 valid" m0.isValid
  let m1 ← expectOk "clock_gettime monotonic #1" (← clock_gettime .monotonic)
  assertTrue "monotonic #1 valid" m1.isValid
  assertTrue "monotonic non-decreasing" (m0.toNanosNat ≤ m1.toNanosNat)
  expectOk "clock_nanosleep 10us for monotonic check"
    (← clock_nanosleep .monotonic false { sec := 0, nsec := 10000 })
  let m2 ← expectOk "clock_gettime monotonic after 10us sleep" (← clock_gettime .monotonic)
  assertTrue "monotonic after sleep ≥ prior + 10000" (m1.toNanosNat + 10000 ≤ m2.toNanosNat)

/-- Runtime verification for `LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockNanosleep_relativeAndAbstime`. -/
private def assume_timerand_clockNanosleep_relativeAndAbstime : IO Unit := do
  let m0 ← expectOk "clock_gettime monotonic before rel sleep" (← clock_gettime .monotonic)
  expectOk "clock_nanosleep monotonic relative 5us"
    (← clock_nanosleep .monotonic false { sec := 0, nsec := 5000 })
  let m1 ← expectOk "clock_gettime monotonic after rel sleep" (← clock_gettime .monotonic)
  assertTrue "monotonic non-decreasing across rel sleep ≥ +5000" (m0.toNanosNat + 5000 ≤ m1.toNanosNat)
  let some monoDeadline := Timespec.ofNanosNat? (m1.toNanosNat + 5000)
    | failWith "Timespec.ofNanosNat? failed for monotonic deadline"
  expectOk "clock_nanosleep monotonic abstime"
    (← clock_nanosleep .monotonic true monoDeadline)
  let m2 ← expectOk "clock_gettime monotonic after abstime sleep" (← clock_gettime .monotonic)
  assertTrue "monotonic reached abstime deadline" (monoDeadline.toNanosNat ≤ m2.toNanosNat)
  let rt0 ← expectOk "clock_gettime realtime before rel/abstime sleep" (← clock_gettime .realtime)
  expectOk "clock_nanosleep realtime relative 1us"
    (← clock_nanosleep .realtime false { sec := 0, nsec := 1000 })
  let some rtDeadline := Timespec.ofEpochNanos? (rt0.toEpochNanos + 5000)
    | failWith "Timespec.ofEpochNanos? failed for realtime deadline"
  expectOk "clock_nanosleep realtime abstime"
    (← clock_nanosleep .realtime true rtDeadline)

/-- Runtime verification for `LeanSwe.LinuxSyscall.TimeRand.assume_timerand_getrandom_exactAndFlags`. -/
private def assume_timerand_getrandom_exactAndFlags : IO Unit := do
  let b0 ← expectOk "getrandom len=0" (← getrandom 0 {})
  assertTrue "getrandom len=0 empty" (b0.size == 0)
  let b16a ← expectOk "getrandom len=16 #1" (← getrandom 16 {})
  let b16b ← expectOk "getrandom len=16 #2" (← getrandom 16 {})
  assertTrue "getrandom len=16 #1 exact size" (b16a.size == 16)
  assertTrue "getrandom len=16 #2 exact size" (b16b.size == 16)
  assertTrue "getrandom draws distinct" (b16a != b16b)
  let bNb ← expectOk "getrandom nonblock" (← getrandom 16 { nonblock := true })
  assertTrue "getrandom nonblock size" (bNb.size == 16)
  let bRnd ← expectOk "getrandom random" (← getrandom 16 { random := true })
  assertTrue "getrandom random size" (bRnd.size == 16)
  let bIns ← expectOk "getrandom insecure" (← getrandom 16 { insecure := true })
  assertTrue "getrandom insecure size" (bIns.size == 16)
  let b300 ← expectOk "getrandom len=300" (← getrandom 300 {})
  assertTrue "getrandom len=300 bounds" (1 ≤ b300.size && b300.size ≤ 300)
  let bBig ← expectOk "getrandom > MAX_READ_BYTES" (← getrandom (MAX_READ_BYTES + 1024) {})
  assertTrue "getrandom clamped ≤ MAX_READ_BYTES"
    (1 ≤ bBig.size && bBig.size ≤ MAX_READ_BYTES.toNat)
  expectErr "getrandom random && insecure -> EINVAL"
    Errno.EINVAL (← getrandom 16 { random := true, insecure := true })

/-- Verify mocked `clock_gettime` error propagation across `invalidArg`, `wouldBlock`, `permissionDenied`, and `transientOrResource`. -/
private def err_clock_gettime_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EINVAL, TimeRandErrorKind.invalidArg)
                     , (Errno.EAGAIN, TimeRandErrorKind.wouldBlock)
                     , (Errno.EPERM, TimeRandErrorKind.permissionDenied)
                     , (Errno.EIO, TimeRandErrorKind.transientOrResource)
                     , (Errno.ENOMEM, TimeRandErrorKind.transientOrResource) ] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.error eno) (.ok ()) (.ok ByteArray.empty))
    expectErr s!"mock clock_gettime {Errno.name eno}" eno (← ops.clock_gettime .monotonic)
    logTimeRandErrHit "clock_gettime" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == kind)

/-- Verify real `clock_nanosleep` rejects invalid `Timespec`s (`sec < 0` and `nsec ≥ 10^9`) with `EINVAL`. -/
private def err_clock_nanosleep_invalidArg : IO Unit := do
  expectErr "clock_nanosleep negative sec -> EINVAL"
    Errno.EINVAL (← clock_nanosleep .monotonic false { sec := -1, nsec := 0 })
  logTimeRandErrHit "clock_nanosleep" Errno.EINVAL "real"
  expectErr "clock_nanosleep nsec >= 1e9 -> EINVAL"
    Errno.EINVAL (← clock_nanosleep .realtime true { sec := 0, nsec := 1000000000 })
  assertTrue "EINVAL is invalidArg" (TimeRandErrorKind.ofErrno Errno.EINVAL == .invalidArg)

/-- Verify mocked `clock_nanosleep` propagation for `wouldBlock` (`EAGAIN`) and `permissionDenied` (`EPERM`/`EACCES`). -/
private def err_clock_nanosleep_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EAGAIN, TimeRandErrorKind.wouldBlock)
                     , (Errno.EPERM, TimeRandErrorKind.permissionDenied)
                     , (Errno.EACCES, TimeRandErrorKind.permissionDenied) ] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.error eno) (.ok ByteArray.empty))
    expectErr s!"mock clock_nanosleep {Errno.name eno}" eno
      (← ops.clock_nanosleep .monotonic false { sec := 0, nsec := 1 })
    logTimeRandErrHit "clock_nanosleep" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == kind)

/-- Verify mocked `clock_nanosleep` propagation for `EINTR`, `EIO`, and `ENOMEM` (`transientOrResource`). -/
private def err_clock_nanosleep_transient : IO Unit := do
  for eno in [Errno.EINTR, Errno.EIO, Errno.ENOMEM] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.error eno) (.ok ByteArray.empty))
    expectErr s!"mock clock_nanosleep {Errno.name eno}" eno
      (← ops.clock_nanosleep .realtime false { sec := 0, nsec := 1 })
    logTimeRandErrHit "clock_nanosleep" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .transientOrResource)

/-- Verify real `getrandom` rejects `random && insecure` with `EINVAL` even when `len = 0`. -/
private def err_getrandom_invalidArg : IO Unit := do
  expectErr "getrandom random && insecure len=16 -> EINVAL"
    Errno.EINVAL (← getrandom 16 { random := true, insecure := true })
  logTimeRandErrHit "getrandom" Errno.EINVAL "real"
  expectErr "getrandom random && insecure len=0 -> EINVAL"
    Errno.EINVAL (← getrandom 0 { random := true, insecure := true })
  assertTrue "EINVAL is invalidArg" (TimeRandErrorKind.ofErrno Errno.EINVAL == .invalidArg)

/-- Verify mocked `getrandom` `EAGAIN` (`wouldBlock`) propagation when CRNG is unseeded. -/
private def err_getrandom_wouldBlock : IO Unit := do
  let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error Errno.EAGAIN))
  expectErr "mock getrandom EAGAIN" Errno.EAGAIN (← ops.getrandom 16 { nonblock := true })
  logTimeRandErrHit "getrandom" Errno.EAGAIN "mocked"
  assertTrue "EAGAIN is wouldBlock" (TimeRandErrorKind.ofErrno Errno.EAGAIN == .wouldBlock)

/-- Verify mocked `getrandom` `EPERM` / `EACCES` (`permissionDenied`) propagation. -/
private def err_getrandom_mocked : IO Unit := do
  for eno in [Errno.EPERM, Errno.EACCES] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error eno))
    expectErr s!"mock getrandom {Errno.name eno}" eno (← ops.getrandom 16 {})
    logTimeRandErrHit "getrandom" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .permissionDenied)

/-- Verify mocked `getrandom` `EINTR`, `EIO`, and `ENOMEM` (`transientOrResource`) propagation. -/
private def err_getrandom_transient : IO Unit := do
  for eno in [Errno.EINTR, Errno.EIO, Errno.ENOMEM] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error eno))
    expectErr s!"mock getrandom {Errno.name eno}" eno (← ops.getrandom 16 {})
    logTimeRandErrHit "getrandom" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .transientOrResource)

private def parseErrnoName? (s : String) : Option Errno :=
  match s with
  | "EPERM" => some Errno.EPERM
  | "EACCES" => some Errno.EACCES
  | "ENOSYS" => some Errno.ENOSYS
  | "EINVAL" => some Errno.EINVAL
  | "EINTR" => some Errno.EINTR
  | "ENOMEM" => some Errno.ENOMEM
  | "EIO" => some Errno.EIO
  | "EAGAIN" => some Errno.EAGAIN
  | _ => none

private def seccompWorker (errName : String) : IO UInt32 := do
  let some expected := parseErrnoName? errName
    | do
        IO.eprintln s!"seccomp-worker: unsupported errno {errName}"
        return 1
  let rc ← SandboxEnv.installTimeRandSeccompErrno expected
  if rc != 0 then
    IO.eprintln s!"seccomp-worker: installTimeRandSeccompErrno failed with errno {rc}"
    return 1
  let sSec := TimeRandState.initial.withOuterSeccomp
  let sPlain := TimeRandState.initial
  let reqs : List (TimeRandReq × IO (TimeRandOutcome) × Bool) :=
    [ (.clock_gettime .realtime, outcomeOfTimespec <$> clock_gettime .realtime, true)
    , (.clock_gettime .monotonic, outcomeOfTimespec <$> clock_gettime .monotonic, true)
    , (.clock_nanosleep .monotonic false { sec := 0, nsec := 1000 },
        outcomeOfUnit <$> clock_nanosleep .monotonic false { sec := 0, nsec := 1000 },
        expected != Errno.EINTR)
    , (.clock_nanosleep .monotonic false { sec := -1, nsec := 0 },
        outcomeOfUnit <$> clock_nanosleep .monotonic false { sec := -1, nsec := 0 }, false)
    , (.getrandom 16 {}, outcomeOfBytes <$> getrandom 16 {}, expected != Errno.EINTR)
    , (.getrandom 16 { random := true, insecure := true },
        outcomeOfBytes <$> getrandom 16 { random := true, insecure := true }, false) ]
  for (req, action, expectRejectedWithoutSeccomp) in reqs do
    let out ← action
    if out != .err expected then
      IO.eprintln s!"seccomp-worker: expected {Errno.name expected}, got {repr out} on {repr req}"
      return 2
    if allowedStep sSec req out != some sSec then
      IO.eprintln s!"seccomp-worker: allowedStep withOuterSeccomp rejected {repr out} on {repr req}"
      return 3
    if expectRejectedWithoutSeccomp && allowedStep sPlain req out != none then
      IO.eprintln s!"seccomp-worker: allowedStep without seccomp unexpectedly accepted {repr out} on {repr req}"
      return 4
  return 0

private def seccompEfaultWorker (opName : String) : IO UInt32 := do
  match ← SandboxEnv.setNoNewPrivs with
  | .error e =>
    IO.eprintln s!"seccomp-efault-worker: prctl(PR_SET_NO_NEW_PRIVS) failed with errno {e}"
    return 1
  | .ok () => pure ()
  let bpf := SandboxEnv.encodeTimeRandSeccompErrnoBpf Errno.EFAULT
  match ← SandboxEnv.installRawSeccomp bpf with
  | .error e =>
    IO.eprintln s!"seccomp-efault-worker: installRawSeccomp failed with errno {e}"
    return 1
  | .ok () => pure ()
  match opName with
  | "clock_gettime" =>
    let _ ← clock_gettime .monotonic
  | "clock_nanosleep" =>
    let _ ← clock_nanosleep .monotonic false { sec := 0, nsec := 1000 }
  | "getrandom" =>
    let _ ← getrandom 16 {}
  | _ =>
    IO.eprintln s!"seccomp-efault-worker: unknown op {opName}"
    return 1
  IO.eprintln s!"seccomp-efault-worker ({opName}): expected SIGABRT, syscall returned instead"
  return 99

private def seccompTsyncWorker : IO UInt32 := do
  let _tid ← match ← SandboxEnv.spawnSyncThread true with
    | .ok t => pure t
    | .error e =>
      IO.eprintln s!"seccomp-tsync-worker: spawnSyncThread failed with errno {e}"
      return 1
  try
    let rc ← SandboxEnv.installTimeRandSeccompErrno Errno.EPERM
    if rc != Errno.EAGAIN then
      IO.eprintln s!"seccomp-tsync-worker: expected EAGAIN ({Errno.EAGAIN}), got errno {rc}"
      return 2
    return 0
  finally
    let _ ← SandboxEnv.stopSyncThread

private def checkOuterSeccompRuntime : IO Unit := do
  let nnpBefore ← expectOk "PR_GET_NO_NEW_PRIVS before invalid calls" (← SandboxEnv.getNoNewPrivs)
  for (label, eno, mask) in
      [ ("eno=0", (0 : Errno), (7 : UInt32))
      , ("eno=4096", (4096 : Errno), (7 : UInt32))
      , ("eno=EFAULT", Errno.EFAULT, (7 : UInt32))
      , ("mask=0", Errno.EPERM, (0 : UInt32))
      , ("mask=8", Errno.EPERM, (8 : UInt32)) ] do
    let rc ← SandboxEnv.installTimeRandSeccompErrno eno mask
    assertTrue s!"installTimeRandSeccompErrno rejects {label} with EINVAL (got {rc})" (rc == Errno.EINVAL)
  let nnpAfter ← expectOk "PR_GET_NO_NEW_PRIVS after invalid calls" (← SandboxEnv.getNoNewPrivs)
  assertTrue "invalid installTimeRandSeccompErrno calls preserve PR_GET_NO_NEW_PRIVS" (nnpAfter == nnpBefore)
  let exe ← IO.appPath
  for errName in ["EPERM", "EINTR"] do
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #["--timerand-strace-fault-check", "--seccomp-worker", errName]
    }
    if out.exitCode != 0 then
      failWith s!"outer seccomp {errName} child check failed exit={out.exitCode}: {out.stderr}"
  let tsyncOut ← IO.Process.output {
    cmd := exe.toString
    args := #["--timerand-strace-fault-check", "--seccomp-tsync-worker"]
  }
  if tsyncOut.exitCode != 0 then
    failWith s!"outer seccomp TSYNC conflict check failed exit={tsyncOut.exitCode}: {tsyncOut.stderr}"
  for opName in ["clock_gettime", "clock_nanosleep", "getrandom"] do
    let abortOut ← IO.Process.output {
      cmd := exe.toString
      args := #["--timerand-strace-fault-check", "--seccomp-efault-worker", opName]
    }
    if abortOut.exitCode != 134 then
      failWith s!"outer seccomp EFAULT ({opName}) expected SIGABRT (134), got exit={abortOut.exitCode}: {abortOut.stderr}"

private def checkRawInvalidTags : IO Unit := do
  expectErr "raw clock_gettime clk=2 -> EINVAL"
    Errno.EINVAL (← rawClockGettimeForTest 2)
  expectErr "raw clock_nanosleep clk=2 -> EINVAL"
    Errno.EINVAL (← rawClockNanosleepForTest 2 0 0 1)
  expectErr "raw clock_nanosleep abstime=2 -> EINVAL"
    Errno.EINVAL (← rawClockNanosleepForTest 1 2 0 1)

/-- Run all `TimeRand` real and mocked regression and error-path checks (dispatched by `leanswe-fuzz --smoke`). -/
def runChecks : IO Unit := do
  assume_timerand_clockGettime_realtimeAndMonotonic
  assume_timerand_clockNanosleep_relativeAndAbstime
  assume_timerand_getrandom_exactAndFlags
  err_clock_gettime_mocked
  err_clock_nanosleep_invalidArg
  err_clock_nanosleep_mocked
  err_clock_nanosleep_transient
  err_getrandom_invalidArg
  err_getrandom_wouldBlock
  err_getrandom_mocked
  err_getrandom_transient
  checkRawInvalidTags
  checkOuterSeccompRuntime

private def straceWorker (opName errName : String) : IO UInt32 := do
  let some expected := parseErrnoName? errName
    | do
        IO.eprintln s!"strace-worker: unsupported errno {errName}"
        return 1
  let (req, res) : TimeRandReq × Except Errno Unit ←
    match opName with
    | "clock_gettime" =>
      let r ← clock_gettime .monotonic
      pure (.clock_gettime .monotonic, r.map (fun _ => ()))
    | "clock_gettime_realtime" =>
      let r ← clock_gettime .realtime
      pure (.clock_gettime .realtime, r.map (fun _ => ()))
    | "clock_nanosleep" =>
      let ts : Timespec := { sec := 0, nsec := 1000 }
      let r ← clock_nanosleep .monotonic false ts
      pure (.clock_nanosleep .monotonic false ts, r)
    | "clock_nanosleep_realtime" =>
      let ts : Timespec := { sec := 0, nsec := 1000 }
      let r ← clock_nanosleep .realtime false ts
      pure (.clock_nanosleep .realtime false ts, r)
    | "clock_nanosleep_abstime" =>
      let ts : Timespec := { sec := 0, nsec := 1000 }
      let r ← clock_nanosleep .monotonic true ts
      pure (.clock_nanosleep .monotonic true ts, r)
    | "getrandom" =>
      let r ← getrandom 16 {}
      pure (.getrandom 16 {}, r.map (fun _ => ()))
    | "getrandom_large" =>
      let r ← getrandom 8192 {}
      pure (.getrandom 8192 {}, r.map (fun _ => ()))
    | "getrandom_nonblock" =>
      let flags : GrndFlags := { nonblock := true }
      let r ← getrandom 16 flags
      pure (.getrandom 16 flags, r.map (fun _ => ()))
    | "getrandom_insecure" =>
      let flags : GrndFlags := { insecure := true }
      let r ← getrandom 16 flags
      pure (.getrandom 16 flags, r.map (fun _ => ()))
    | _ =>
      IO.eprintln s!"strace-worker: unknown op {opName}"
      return 1
  match res with
  | .error e =>
    if e != expected then
      IO.eprintln s!"strace-worker ({opName}): expected {Errno.name expected} ({expected}), got {Errno.name e} ({e})"
      return 2
    let sPlain := TimeRandState.initial
    let sReady : TimeRandState := { sPlain with crngReady := true }
    let sSec := sPlain.withOuterSeccomp
    let out : TimeRandOutcome := .err e
    if allowedStep sSec req out != some sSec then
      IO.eprintln s!"strace-worker ({opName}, {errName}): rejected by TimeRandState.withOuterSeccomp"
      return 4
    let isSleepOp := opName == "clock_nanosleep" || opName == "clock_nanosleep_realtime" || opName == "clock_nanosleep_abstime"
    let isRandOp := opName == "getrandom" || opName == "getrandom_large" || opName == "getrandom_nonblock" || opName == "getrandom_insecure"
    let expectPlainAllowed :=
      (isSleepOp && e == Errno.EINTR) ||
      ((opName == "getrandom" || opName == "getrandom_large") && e == Errno.EINTR) ||
      (opName == "getrandom_nonblock" && e == Errno.EAGAIN)
    let plainRes := allowedStep sPlain req out
    if expectPlainAllowed && plainRes != some sPlain then
      IO.eprintln s!"strace-worker ({opName}, {errName}): expected allowedStepCore to accept under initial state"
      return 5
    if !expectPlainAllowed && plainRes != none then
      IO.eprintln s!"strace-worker ({opName}, {errName}): expected allowedStepCore to reject without outer seccomp"
      return 6
    if isRandOp && allowedStep sReady req out != none then
      IO.eprintln s!"strace-worker ({opName}, {errName}): expected allowedStepCore to reject once crngReady = true"
      return 7
    let h1 := HealthyEnv.initial 1
    let h0 := HealthyEnv.initial 0
    let hReady1 := HealthyEnv.initial 1 0 true
    let hSec : HealthyEnv := { state := sSec, eintrBudget := 1 }
    if (healthyStep hSec req out).isSome then
      IO.eprintln s!"strace-worker ({opName}, {errName}): healthyStep accepted outer-seccomp state"
      return 8
    if isCriticalFault out then
      if (healthyStep h1 req out).isSome then
        IO.eprintln s!"strace-worker ({opName}, {errName}): healthyStep accepted critical fault"
        return 9
    else if expectPlainAllowed then
      if e == Errno.EINTR then
        if healthyStep h1 req out != some h0 || (healthyStep h0 req out).isSome then
          IO.eprintln s!"strace-worker ({opName}, {errName}): healthyStep EINTR budget check failed"
          return 10
      else
        if healthyStep h1 req out != some h1 || (healthyStep hReady1 req out).isSome then
          IO.eprintln s!"strace-worker ({opName}, {errName}): healthyStep EAGAIN check failed"
          return 11
    else
      if (healthyStep h1 req out).isSome then
        IO.eprintln s!"strace-worker ({opName}, {errName}): healthyStep accepted disallowed error"
        return 12
    return 0
  | .ok () =>
    IO.eprintln s!"strace-worker ({opName}): expected {Errno.name expected}, got ok"
    return 3

/-- Run live `strace -f` fault-injection checks verifying `EINTR`, `ENOMEM`, `EIO`, and `EAGAIN` across `clock_gettime`, `clock_nanosleep`, and `getrandom` variants. -/
def runStraceFaultCheck : IO Unit := do
  let exe ← IO.appPath
  let cases : List (String × String × List String) :=
    [ ("clock_gettime", "clock_gettime", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("clock_gettime_realtime", "clock_gettime", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("clock_nanosleep", "clock_nanosleep", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("clock_nanosleep_realtime", "clock_nanosleep", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("clock_nanosleep_abstime", "clock_nanosleep", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("getrandom", "getrandom", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("getrandom_large", "getrandom", ["EINTR", "ENOMEM", "EIO", "EAGAIN"])
    , ("getrandom_nonblock", "getrandom", ["EAGAIN", "EINTR", "ENOMEM", "EIO"])
    , ("getrandom_insecure", "getrandom", ["EAGAIN", "EINTR", "ENOMEM", "EIO"]) ]
  for (opName, syscallName, errNames) in cases do
    for errName in errNames do
      let out ← IO.Process.output {
        cmd := "strace"
        args := #["-f", "-qq", "-o", "/dev/null",
          "-e", s!"inject={syscallName}:error={errName}",
          exe.toString, "--timerand-strace-fault-check", "--worker", opName, errName]
      }
      if out.exitCode != 0 then
        throw (IO.userError s!"strace fault-injection failed for ({opName}, {errName}) exit={out.exitCode}: {out.stderr}")

/-- CLI entrypoint for `--timerand-strace-fault-check`, dispatched by `leanswe-fuzz` (`Fuzz.LinuxSyscall.Main.tryDispatchEarlyWorker`). -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    runStraceFaultCheck
    IO.println "TIMERAND_STRACE_FAULT_CHECK: ok (clock_gettime, clock_nanosleep, getrandom × EINTR, ENOMEM, EIO, EAGAIN)"
    return 0
  | ["--worker", opName, errName] =>
    straceWorker opName errName
  | ["--seccomp-worker", errName] =>
    seccompWorker errName
  | ["--seccomp-tsync-worker"] =>
    seccompTsyncWorker
  | ["--seccomp-efault-worker", opName] =>
    seccompEfaultWorker opName
  | _ =>
    IO.eprintln s!"unknown timerand strace args: {args}"
    return 1

end Fuzz.LinuxSyscall.TimeRand.Strace

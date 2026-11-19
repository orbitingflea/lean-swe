import Core.Assumptions
import LeanSwe.LinuxSyscall.TimeRand.Impl
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.TimeRand.Model

namespace LeanSwe.LinuxSyscall.TimeRand.RuntimeTests

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

private def failWith {α : Type} (msg : String) : IO α :=
  throw (IO.userError s!"TimeRand.RuntimeTests: {msg}")

@[extern "leanswe_fuzz_install_seccomp_errno"]
private opaque installSeccompErrnoRaw (eno : UInt32) (mask : UInt32) : BaseIO UInt32

@[extern "leanswe_sys_clock_gettime"]
private opaque rawClockGettimeForTest : UInt32 → BaseIO (Except Errno (Int64 × UInt32))

@[extern "leanswe_sys_clock_nanosleep"]
private opaque rawClockNanosleepForTest : UInt32 → UInt8 → Int64 → UInt32 → BaseIO (Except Errno Unit)

/-- Install a process-wide (`TSYNC`) `SECCOMP_RET_ERRNO` BPF filter in forked runtime-test children (`1 ≤ eno ≤ 4095`). -/
def installSeccompErrnoForTest (eno : Errno) (mask : UInt32 := 7) : BaseIO UInt32 :=
  installSeccompErrnoRaw eno mask

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
def assume_timerand_clockGettime_realtimeAndMonotonic : IO Unit := do
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
def assume_timerand_clockNanosleep_relativeAndAbstime : IO Unit := do
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
def assume_timerand_getrandom_exactAndFlags : IO Unit := do
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

/-- Registered assumption-obligation checks backed by real Linux syscalls. -/
def registeredAssumptions : Array RegisteredAssumption :=
  #[ { specName := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockGettime_realtimeAndMonotonic"
       run := assume_timerand_clockGettime_realtimeAndMonotonic }
   , { specName := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockNanosleep_relativeAndAbstime"
       run := assume_timerand_clockNanosleep_relativeAndAbstime }
   , { specName := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_getrandom_exactAndFlags"
       run := assume_timerand_getrandom_exactAndFlags } ]

/-- Verify mocked `clock_gettime` error propagation across `invalidArg`, `wouldBlock`, `permissionDenied`, and `transientOrResource`. -/
def err_clock_gettime_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EINVAL, TimeRandErrorKind.invalidArg)
                     , (Errno.EAGAIN, TimeRandErrorKind.wouldBlock)
                     , (Errno.EPERM, TimeRandErrorKind.permissionDenied)
                     , (Errno.EIO, TimeRandErrorKind.transientOrResource)
                     , (Errno.ENOMEM, TimeRandErrorKind.transientOrResource) ] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.error eno) (.ok ()) (.ok ByteArray.empty))
    expectErr s!"mock clock_gettime {Errno.name eno}" eno (← ops.clock_gettime .monotonic)
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == kind)

/-- Verify real `clock_nanosleep` rejects invalid `Timespec`s (`sec < 0` and `nsec ≥ 10^9`) with `EINVAL`. -/
def err_clock_nanosleep_invalidArg : IO Unit := do
  expectErr "clock_nanosleep negative sec -> EINVAL"
    Errno.EINVAL (← clock_nanosleep .monotonic false { sec := -1, nsec := 0 })
  expectErr "clock_nanosleep nsec >= 1e9 -> EINVAL"
    Errno.EINVAL (← clock_nanosleep .realtime true { sec := 0, nsec := 1000000000 })
  assertTrue "EINVAL is invalidArg" (TimeRandErrorKind.ofErrno Errno.EINVAL == .invalidArg)

/-- Verify mocked `clock_nanosleep` propagation for `wouldBlock` (`EAGAIN`) and `permissionDenied` (`EPERM`/`EACCES`). -/
def err_clock_nanosleep_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EAGAIN, TimeRandErrorKind.wouldBlock)
                     , (Errno.EPERM, TimeRandErrorKind.permissionDenied)
                     , (Errno.EACCES, TimeRandErrorKind.permissionDenied) ] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.error eno) (.ok ByteArray.empty))
    expectErr s!"mock clock_nanosleep {Errno.name eno}" eno
      (← ops.clock_nanosleep .monotonic false { sec := 0, nsec := 1 })
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == kind)

/-- Verify mocked `clock_nanosleep` propagation for `EINTR`, `EIO`, and `ENOMEM` (`transientOrResource`). -/
def err_clock_nanosleep_transient : IO Unit := do
  for eno in [Errno.EINTR, Errno.EIO, Errno.ENOMEM] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.error eno) (.ok ByteArray.empty))
    expectErr s!"mock clock_nanosleep {Errno.name eno}" eno
      (← ops.clock_nanosleep .realtime false { sec := 0, nsec := 1 })
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .transientOrResource)

/-- Verify real `getrandom` rejects `random && insecure` with `EINVAL` even when `len = 0`. -/
def err_getrandom_invalidArg : IO Unit := do
  expectErr "getrandom random && insecure len=16 -> EINVAL"
    Errno.EINVAL (← getrandom 16 { random := true, insecure := true })
  expectErr "getrandom random && insecure len=0 -> EINVAL"
    Errno.EINVAL (← getrandom 0 { random := true, insecure := true })
  assertTrue "EINVAL is invalidArg" (TimeRandErrorKind.ofErrno Errno.EINVAL == .invalidArg)

/-- Verify mocked `getrandom` `EAGAIN` (`wouldBlock`) propagation when CRNG is unseeded. -/
def err_getrandom_wouldBlock : IO Unit := do
  let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error Errno.EAGAIN))
  expectErr "mock getrandom EAGAIN" Errno.EAGAIN (← ops.getrandom 16 { nonblock := true })
  assertTrue "EAGAIN is wouldBlock" (TimeRandErrorKind.ofErrno Errno.EAGAIN == .wouldBlock)

/-- Verify mocked `getrandom` `EPERM` / `EACCES` (`permissionDenied`) propagation. -/
def err_getrandom_mocked : IO Unit := do
  for eno in [Errno.EPERM, Errno.EACCES] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error eno))
    expectErr s!"mock getrandom {Errno.name eno}" eno (← ops.getrandom 16 {})
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .permissionDenied)

/-- Verify mocked `getrandom` `EINTR`, `EIO`, and `ENOMEM` (`transientOrResource`) propagation. -/
def err_getrandom_transient : IO Unit := do
  for eno in [Errno.EINTR, Errno.EIO, Errno.ENOMEM] do
    let ops := Internal.mkTimeRandOps (mkMockRawOps (.ok (0, 0)) (.ok ()) (.error eno))
    expectErr s!"mock getrandom {Errno.name eno}" eno (← ops.getrandom 16 {})
    assertTrue s!"kind {Errno.name eno}" (TimeRandErrorKind.ofErrno eno == .transientOrResource)

/-- Registered `(request × TimeRandErrorKind)` error-coverage tests matching `TimeRand/SpecTests.lean`. -/
def registeredErrorTests : Array RegisteredErrorTest :=
  #[ { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_gettime_mocked"
       mode := .mocked
       run := err_clock_gettime_mocked }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_invalidArg"
       mode := .real
       run := err_clock_nanosleep_invalidArg }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_mocked"
       mode := .mocked
       run := err_clock_nanosleep_mocked }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_transient"
       mode := .mocked
       run := err_clock_nanosleep_transient }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_invalidArg"
       mode := .real
       run := err_getrandom_invalidArg }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_wouldBlock"
       mode := .mocked
       run := err_getrandom_wouldBlock }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_mocked"
       mode := .mocked
       run := err_getrandom_mocked }
   , { testName := "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_transient"
       mode := .mocked
       run := err_getrandom_transient } ]

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
  let rc ← installSeccompErrnoRaw expected 7
  if rc != 0 then
    IO.eprintln s!"seccomp-worker: installSeccompErrnoRaw failed with errno {rc}"
    return 1
  let sSec := TimeRandState.initial.withOuterSeccomp
  let sPlain := TimeRandState.initial
  let reqs : List (TimeRandReq × IO (TimeRandOutcome) × Bool) :=
    [ (.clock_gettime .realtime, outcomeOfTimespec <$> clock_gettime .realtime, true)
    , (.clock_gettime .monotonic, outcomeOfTimespec <$> clock_gettime .monotonic, true)
    , (.clock_nanosleep .monotonic false { sec := 0, nsec := 1000 },
        outcomeOfUnit <$> clock_nanosleep .monotonic false { sec := 0, nsec := 1000 }, true)
    , (.clock_nanosleep .monotonic false { sec := -1, nsec := 0 },
        outcomeOfUnit <$> clock_nanosleep .monotonic false { sec := -1, nsec := 0 }, false)
    , (.getrandom 16 {}, outcomeOfBytes <$> getrandom 16 {}, true)
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
  let rc ← installSeccompErrnoRaw Errno.EFAULT 7
  if rc != 0 then
    IO.eprintln s!"seccomp-efault-worker: installSeccompErrnoRaw failed with errno {rc}"
    return 1
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

private def checkOuterSeccompRuntime : IO Unit := do
  let exe ← IO.appPath
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["--timerand-strace-fault-check", "--seccomp-worker", "EPERM"]
  }
  if out.exitCode != 0 then
    failWith s!"outer seccomp child check failed exit={out.exitCode}: {out.stderr}"
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

/-- Run all `TimeRand` assumption checks and error-coverage tests. -/
def runAll : IO Unit := do
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  checkRawInvalidTags
  checkOuterSeccompRuntime
  IO.println "PASS: LeanSwe.LinuxSyscall.TimeRand runtime tests"

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

/-- CLI entrypoint for `--timerand-strace-fault-check`. -/
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
  | ["--seccomp-efault-worker", opName] =>
    seccompEfaultWorker opName
  | _ =>
    IO.eprintln s!"unknown timerand strace args: {args}"
    return 1

end LeanSwe.LinuxSyscall.TimeRand.RuntimeTests

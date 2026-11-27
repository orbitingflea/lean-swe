import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import LeanSwe.LinuxSyscall.TimeRand.Interface
import Fuzz.LinuxSyscall.Rng
import Fuzz.LinuxSyscall.SandboxEnv

namespace Fuzz.LinuxSyscall

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque armSigalrmRaw (usec : UInt32) (saRestart : UInt8) : BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque disarmSigalrmRaw (unused : UInt32) : BaseIO Unit

/-- Action executed by the `TimeRand` world-model fuzzer, optionally arming a short `SIGALRM` around `clock_nanosleep` or `getrandom`. -/
inductive TimeRandFuzzAction where
  /-- Execute `clock_gettime(clk)`. -/
  | clock_gettime (clk : ClockId)
  /-- Execute `clock_nanosleep(clk, abstime, req)` with optional `SIGALRM` in `armSigUs` microseconds (`0` disables signal). -/
  | clock_nanosleep (clk : ClockId) (abstime : Bool) (req : Timespec) (armSigUs : UInt32) (saRestart : Bool)
  /-- Execute `getrandom(len, flags)` with optional `SIGALRM` in `armSigUs` microseconds (`0` disables signal). -/
  | getrandom (len : UInt32) (flags : GrndFlags) (armSigUs : UInt32) (saRestart : Bool)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Convert a `TimeRandFuzzAction` to the model request `TimeRandReq`. -/
def TimeRandFuzzAction.toReq : TimeRandFuzzAction → TimeRandReq
  | .clock_gettime clk => .clock_gettime clk
  | .clock_nanosleep clk abstime req _ _ => .clock_nanosleep clk abstime req
  | .getrandom len flags _ _ => .getrandom len flags

/-- Tracked `(syscall × outcome)` counts emitted by `TimeRand` fuzzing runs. -/
structure TimeRandHitCounters where
  /-- Total `clock_gettime` calls. -/
  gettimeTotal : Nat := 0
  /-- Succeeding `clock_gettime .realtime` calls. -/
  gettimeRealtimeOk : Nat := 0
  /-- Succeeding `clock_gettime .monotonic` calls. -/
  gettimeMonotonicOk : Nat := 0
  /-- `clock_gettime` error count. -/
  gettimeErr : Nat := 0
  /-- Total `clock_nanosleep` calls. -/
  nanosleepTotal : Nat := 0
  /-- Succeeding `clock_nanosleep` calls. -/
  nanosleepOk : Nat := 0
  /-- Succeeding relative monotonic `clock_nanosleep` calls. -/
  nanosleepRelMonoOk : Nat := 0
  /-- Succeeding relative realtime `clock_nanosleep` calls. -/
  nanosleepRelRealOk : Nat := 0
  /-- Succeeding `TIMER_ABSTIME` monotonic `clock_nanosleep` calls. -/
  nanosleepAbsMonoOk : Nat := 0
  /-- Succeeding `TIMER_ABSTIME` realtime `clock_nanosleep` calls. -/
  nanosleepAbsRealOk : Nat := 0
  /-- `clock_nanosleep` `EINVAL` (`invalidArg`) hits. -/
  nanosleepInvalidArg : Nat := 0
  /-- `clock_nanosleep` `EINTR`/`EIO`/`ENOMEM` (`transientOrResource`) hits. -/
  nanosleepTransient : Nat := 0
  /-- `clock_nanosleep` `TIMER_ABSTIME` transient (`EINTR`) hits. -/
  nanosleepAbstimeTransient : Nat := 0
  /-- `clock_nanosleep` other non-`EINVAL`/non-transient error hits (e.g. `seccomp`). -/
  nanosleepOtherErr : Nat := 0
  /-- Total `getrandom` calls. -/
  getrandomTotal : Nat := 0
  /-- Succeeding `getrandom` calls with `len == 0`. -/
  getrandomOkZero : Nat := 0
  /-- Succeeding `getrandom` calls with `1 ≤ gotLen ≤ 256`. -/
  getrandomOkSmall : Nat := 0
  /-- Succeeding `getrandom` calls with `gotLen > 256`. -/
  getrandomOkLarge : Nat := 0
  /-- Partial `getrandom` calls with `0 < gotLen < min len MAX_READ_BYTES`. -/
  getrandomPartial : Nat := 0
  /-- Succeeding `getrandom` calls where requested `len > MAX_READ_BYTES` was clamped to `≤ MAX_READ_BYTES`. -/
  getrandomOverMaxReadBytes : Nat := 0
  /-- `getrandom` `EINVAL` (`invalidArg`) hits. -/
  getrandomInvalidArg : Nat := 0
  /-- `getrandom` `EAGAIN` (`wouldBlock`) hits. -/
  getrandomWouldBlock : Nat := 0
  /-- `getrandom` transient (`EINTR`/`ENOMEM`/`EIO`) hits. -/
  getrandomTransient : Nat := 0
  /-- `getrandom` other error hits. -/
  getrandomOtherErr : Nat := 0
  /-- Bitmask (`0..0x3F`) of observed valid `GrndFlags` flag combinations (`nonblock | random<<1 | insecure<<2`). -/
  getrandomValidFlagsMask : Nat := 0
  /-- Completed `seccomp` child sub-episodes (`blanket + selective`). -/
  envSeccompOk : Nat := 0
  /-- Completed `CLONE_NEWTIME` child sub-episodes. -/
  envTimensOk : Nat := 0
  /-- Expected `CLONE_NEWTIME` sub-episodes when unprivileged time namespaces are supported (`7` or `0`). -/
  envTimensExpected : Nat := 0
  deriving Repr, Inhabited

/-- Summary statistics returned by `fuzzTimeRand`. -/
structure TimeRandFuzzReport where
  /-- Executed syscall step count. -/
  steps : Nat
  /-- Executed episode count. -/
  episodes : Nat
  /-- Elapsed wall-clock milliseconds. -/
  elapsedMs : Nat
  /-- Observed `(syscall × outcome)` counts. -/
  hits : TimeRandHitCounters
  deriving Repr

private def genClockId (rng : Rng) : ClockId × Rng :=
  let (b, r1) := rng.chance 1 2
  (if b then .realtime else .monotonic, r1)

private def genGrndFlags (rng : Rng) : GrndFlags × Rng :=
  let (bits, r1) := rng.nextNat 8
  ({ nonblock := (bits &&& 1) != 0
     random := (bits &&& 2) != 0
     insecure := (bits &&& 4) != 0 }, r1)

private def validFlagsIndex (f : GrndFlags) : Nat :=
  (if f.nonblock then 1 else 0) +
  (if f.random then 2 else 0) +
  (if f.insecure then 4 else 0)

private def genFullNsec (rng : Rng) : UInt32 × Rng :=
  let (pick, r1) := rng.nextNat 10
  match pick with
  | 0 => (0, r1)
  | 1 => (999999999, r1)
  | _ =>
    let (ns, r2) := r1.nextRange 0 999999999
    (UInt32.ofNat ns, r2)

private def genFullNegInt64 (rng : Rng) : Int64 × Rng :=
  let (bPick, r1) := rng.nextNat 4
  match bPick with
  | 0 => (Int64.minValue, r1)
  | 1 => (-1, r1)
  | _ =>
    let (u, r2) := r1.nextU64
    (Int64.ofInt (-(Int.ofNat (u.toNat % 9223372036854775808 + 1))), r2)

private def genFullNonnegInt64 (rng : Rng) : Int64 × Rng :=
  let (bPick, r1) := rng.nextNat 4
  match bPick with
  | 0 => (0, r1)
  | 1 => (Int64.maxValue, r1)
  | _ =>
    let (u, r2) := r1.nextU64
    (Int64.ofInt (Int.ofNat (u.toNat % 9223372036854775808)), r2)

private def genInvalidNsec (rng : Rng) : UInt32 × Rng :=
  let (pick, r1) := rng.nextNat 8
  match pick with
  | 0 => (UInt32.ofNat NSEC_PER_SEC, r1)
  | 1 => (2000000000, r1)
  | 2 => (UInt32.ofNat (UInt32.size - 1), r1)
  | _ =>
    let (ns, r2) := r1.nextRange NSEC_PER_SEC (UInt32.size - 1)
    (UInt32.ofNat ns, r2)

private def genInvalidTimespec (rng : Rng) : Timespec × Rng :=
  let (kind, r1) := rng.nextNat 4
  match kind with
  | 0 =>
    let (secVal, r2) := genFullNegInt64 r1
    let (nsVal, r3) := genFullNsec r2
    ({ sec := secVal, nsec := nsVal }, r3)
  | 1 =>
    let (secVal, r2) := genFullNegInt64 r1
    let (nsVal, r3) := genInvalidNsec r2
    ({ sec := secVal, nsec := nsVal }, r3)
  | 2 =>
    let (secPick, r2) := r1.chance 1 2
    let (nsVal, r3) := genInvalidNsec r2
    ({ sec := if secPick then (0 : Int64) else (1 : Int64), nsec := nsVal }, r3)
  | _ =>
    let (secVal, r2) := genFullNonnegInt64 r1
    let (nsVal, r3) := genInvalidNsec r2
    ({ sec := secVal, nsec := nsVal }, r3)

private def timespecToEpochInt (ts : Timespec) : Int :=
  ts.sec.toInt * (NSEC_PER_SEC : Int) + Int.ofNat ts.nsec.toNat

private def ktimeMaxTs : Timespec :=
  { sec := 9223372036, nsec := 854775807 }

private def ktimeMaxPlusOneTs : Timespec :=
  { sec := 9223372036, nsec := 854775808 }

private structure ReplayFuzzAction where
  act : TimeRandFuzzAction
  abstimeOffsetNs? : Option Int := none
  deriving Repr, Inhabited

private def genInterruptedSleep (rng : Rng) (clk : ClockId)
    (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    ReplayFuzzAction × Rng :=
  let (abstime, r1) := rng.chance 1 2
  let (saRestart, r2) := r1.chance 1 2
  let (armUs, r3) := r2.nextRange 80 220
  let (shape, r4) := r3.nextNat 10
  if shape == 0 then
    let (kPick, r5) := r4.nextNat 3
    let (ts, r6) := match kPick with
      | 0 => (ktimeMaxTs, r5)
      | 1 => (ktimeMaxPlusOneTs, r5)
      | _ =>
        let (nsecVal, r5') := genFullNsec r5
        ({ sec := Int64.maxValue, nsec := nsecVal }, r5')
    ({ act := .clock_nanosleep clk abstime ts (UInt32.ofNat armUs) saRestart }, r6)
  else if shape == 1 then
    ({ act := .clock_nanosleep clk false { sec := 0, nsec := 0 } (UInt32.ofNat armUs) saRestart }, r4)
  else if shape == 2 then
    let (secPos, r5) := r4.nextRange 1 5
    let (nsecVal, r6) := genFullNsec r5
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      let futureNs := Int.ofNat secPos * (NSEC_PER_SEC : Int) + Int.ofNat nsecVal.toNat
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + futureNs)) with
      | some ts => ({ act := .clock_nanosleep clk true ts (UInt32.ofNat armUs) saRestart, abstimeOffsetNs? := some futureNs }, r6)
      | none => ({ act := .clock_nanosleep clk true ktimeMaxTs (UInt32.ofNat armUs) saRestart }, r6)
    else
      ({ act := .clock_nanosleep clk false { sec := Int64.ofInt (Int.ofNat secPos), nsec := nsecVal } (UInt32.ofNat armUs) saRestart }, r6)
  else
    let (nsDur, r5) := r4.nextRange 2000000 5000000
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + Int.ofNat nsDur)) with
      | some ts => ({ act := .clock_nanosleep clk true ts (UInt32.ofNat armUs) saRestart, abstimeOffsetNs? := some (Int.ofNat nsDur) }, r5)
      | none => ({ act := .clock_nanosleep clk true ktimeMaxTs (UInt32.ofNat armUs) saRestart }, r5)
    else
      ({ act := .clock_nanosleep clk false { sec := 0, nsec := UInt32.ofNat nsDur } (UInt32.ofNat armUs) saRestart }, r5)

private def genPastValidAbstime (rng : Rng) (clk : ClockId)
    (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    ReplayFuzzAction × Rng :=
  let (nsecVal, r1) := genFullNsec rng
  match clk with
  | .monotonic =>
    match lastMono? with
    | none => ({ act := .clock_nanosleep .monotonic true { sec := 0, nsec := 0 } 0 false }, r1)
    | some ts =>
      if ts.sec.toInt ≥ 2 then
        let maxPastSec := (ts.sec.toInt - 1).toNat
        let (secPick, r2) := r1.nextNat 3
        let (sec, r3) := match secPick with
          | 0 => (0, r2)
          | 1 => (1, r2)
          | _ => r2.nextRange 0 maxPastSec
        ({ act := .clock_nanosleep .monotonic true { sec := Int64.ofInt (Int.ofNat sec), nsec := nsecVal } 0 false }, r3)
      else if ts.sec.toInt == 1 then
        ({ act := .clock_nanosleep .monotonic true { sec := 0, nsec := nsecVal } 0 false }, r1)
      else
        ({ act := .clock_nanosleep .monotonic true { sec := 0, nsec := 0 } 0 false }, r1)
  | .realtime =>
    match lastReal? with
    | none => ({ act := .clock_nanosleep .realtime true { sec := 0, nsec := 0 } 0 false }, r1)
    | some ts =>
      if ts.sec.toInt ≤ 0 then
        ({ act := .clock_nanosleep .realtime false { sec := 0, nsec := 0 } 0 false }, r1)
      else if ts.sec.toInt == 1 then
        ({ act := .clock_nanosleep .realtime true { sec := 0, nsec := nsecVal } 0 false }, r1)
      else
        let maxPastSec := (ts.sec.toInt - 1).toNat
        let (secPick, r2) := r1.nextNat 3
        let (sec, r3) := match secPick with
          | 0 => (0, r2)
          | 1 => (1, r2)
          | _ => r2.nextRange 0 maxPastSec
        ({ act := .clock_nanosleep .realtime true { sec := Int64.ofInt (Int.ofNat sec), nsec := nsecVal } 0 false }, r3)

private def genNanosleepAction (rng : Rng) (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    ReplayFuzzAction × Rng :=
  let (clk, r1) := genClockId rng
  let (bucket, r2) := r1.nextNat 100
  if bucket < 30 then
    let (abstime, r3) := r2.chance 1 2
    let (ts, r4) := genInvalidTimespec r3
    let (doSig, r5) := r4.chance 1 8
    let (armUs, r6) := if doSig then r5.nextRange 60 160 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    ({ act := .clock_nanosleep clk abstime ts (UInt32.ofNat armUs) saRestart }, r7)
  else if bucket < 52 then
    genPastValidAbstime r2 clk lastMono? lastReal?
  else if bucket < 95 then
    let (abstime, r3) := r2.chance 1 2
    let (nsDelta, r4) := r3.nextRange 0 50000
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + Int.ofNat nsDelta)) with
      | some ts => ({ act := .clock_nanosleep clk true ts 0 false, abstimeOffsetNs? := some (Int.ofNat nsDelta) }, r4)
      | none => ({ act := .clock_nanosleep clk true { sec := 0, nsec := UInt32.ofNat nsDelta } 0 false }, r4)
    else
      ({ act := .clock_nanosleep clk false { sec := 0, nsec := UInt32.ofNat nsDelta } 0 false }, r4)
  else
    genInterruptedSleep r2 clk lastMono? lastReal?

private def genGetrandomAction (rng : Rng) : ReplayFuzzAction × Rng :=
  let (flags, r1) := genGrndFlags rng
  let (bucket, r2) := r1.nextNat 10000
  if bucket < 1000 then
    let (doSig, r3) := r2.chance 1 8
    let (armUs, r4) := if doSig then r3.nextRange 60 160 else (0, r3)
    let (saRestart, r5) := r4.chance 1 2
    ({ act := .getrandom 0 flags (UInt32.ofNat armUs) saRestart }, r5)
  else if bucket < 7100 then
    let (exact256, r3) := r2.chance 1 100
    let (len, r4) := if exact256 then (256, r3) else r3.nextRange 1 256
    let (doSig, r5) := if flags.isInvalid then r4.chance 1 8 else r4.chance 1 200
    let (armUs, r6) := if doSig then r5.nextRange 80 200 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    ({ act := .getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart }, r7)
  else if bucket < 9860 then
    let (bPick, r3) := r2.nextNat 100
    let (len, r4) :=
      if bPick == 0 then (257, r3)
      else if bPick == 1 then (4096, r3)
      else if bPick == 2 then (4097, r3)
      else r3.nextRange 257 65536
    let (doSig, r5) := if flags.isInvalid then r4.chance 1 8 else r4.chance 1 200
    let (armUs, r6) := if doSig then r5.nextRange 80 200 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    ({ act := .getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart }, r7)
  else if bucket < 9930 then
    let (useExactMax, r3) := r2.chance 1 4
    let (len, r4) :=
      if useExactMax then (MAX_READ_BYTES.toNat, r3)
      else r3.nextRange 65537 MAX_READ_BYTES.toNat
    let (doSig, r5) := r4.chance 1 4
    let (armUs, r6) := if doSig then r5.nextRange 80 240 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    ({ act := .getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart }, r7)
  else if bucket < 9970 then
    let (len, r3) := r2.nextRange 4194304 MAX_READ_BYTES.toNat
    let (armUs, r4) := r3.nextRange 80 280
    let (saRestart, r5) := r4.chance 1 2
    ({ act := .getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart }, r5)
  else
    let (sub, r3) := r2.nextNat 6
    let (lenU32, r4) := match sub with
      | 0 => (MAX_READ_BYTES + 1, r3)
      | 1 => ((0x02000000 : UInt32), r3)
      | 2 => ((0x7FFFFFFF : UInt32), r3)
      | 3 => ((0x80000000 : UInt32), r3)
      | 4 => ((0xFFFFFFFF : UInt32), r3)
      | _ =>
        let (extra, r4') := r3.nextRange 1 (UInt32.size - 1 - MAX_READ_BYTES.toNat)
        (MAX_READ_BYTES + UInt32.ofNat extra, r4')
    let (doSig, r5) := r4.chance 1 3
    let (armUs, r6) := if doSig then r5.nextRange 80 280 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    ({ act := .getrandom lenU32 flags (UInt32.ofNat armUs) saRestart }, r7)

private def genAction (rng : Rng) (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    ReplayFuzzAction × Rng :=
  let (kind, r1) := rng.nextNat 100
  if kind < 34 then
    let (clk, r2) := genClockId r1
    ({ act := .clock_gettime clk }, r2)
  else if kind < 67 then
    genNanosleepAction r1 lastMono? lastReal?
  else
    genGetrandomAction r1

private def recordHit (h : TimeRandHitCounters) (act : TimeRandFuzzAction)
    (out : TimeRandOutcome) : TimeRandHitCounters :=
  match act with
  | .clock_gettime clk =>
    let h' := { h with gettimeTotal := h.gettimeTotal + 1 }
    match out with
    | .timespec _ =>
      match clk with
      | .realtime => { h' with gettimeRealtimeOk := h'.gettimeRealtimeOk + 1 }
      | .monotonic => { h' with gettimeMonotonicOk := h'.gettimeMonotonicOk + 1 }
    | .err _ => { h' with gettimeErr := h'.gettimeErr + 1 }
    | _ => h'
  | .clock_nanosleep clk abstime _ _ _ =>
    let h' := { h with nanosleepTotal := h.nanosleepTotal + 1 }
    match out with
    | .unit =>
      match clk, abstime with
      | .monotonic, false => { h' with nanosleepOk := h'.nanosleepOk + 1, nanosleepRelMonoOk := h'.nanosleepRelMonoOk + 1 }
      | .realtime, false => { h' with nanosleepOk := h'.nanosleepOk + 1, nanosleepRelRealOk := h'.nanosleepRelRealOk + 1 }
      | .monotonic, true => { h' with nanosleepOk := h'.nanosleepOk + 1, nanosleepAbsMonoOk := h'.nanosleepAbsMonoOk + 1 }
      | .realtime, true => { h' with nanosleepOk := h'.nanosleepOk + 1, nanosleepAbsRealOk := h'.nanosleepAbsRealOk + 1 }
    | .err e =>
      if e == Errno.EINVAL || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS || e == Errno.ERANGE then
        { h' with nanosleepInvalidArg := h'.nanosleepInvalidArg + 1 }
      else if Errno.isTransientOsErrno e then
        { h' with
          nanosleepTransient := h'.nanosleepTransient + 1
          nanosleepAbstimeTransient := h'.nanosleepAbstimeTransient + (if abstime then 1 else 0) }
      else
        { h' with nanosleepOtherErr := h'.nanosleepOtherErr + 1 }
    | _ => h'
  | .getrandom len flags _ _ =>
    let maskBit := if !flags.isInvalid then (1 <<< validFlagsIndex flags) else 0
    let h' := { h with getrandomTotal := h.getrandomTotal + 1 }
    let cap := min len.toNat MAX_READ_BYTES.toNat
    match out with
    | .bytes bs =>
      let hOk := { h' with getrandomValidFlagsMask := h'.getrandomValidFlagsMask ||| maskBit }
      let partialHit := if 0 < bs.size && bs.size < cap then 1 else 0
      let overMaxHit := if len > MAX_READ_BYTES && bs.size ≤ MAX_READ_BYTES.toNat then 1 else 0
      if bs.size == 0 then
        { hOk with
          getrandomOkZero := hOk.getrandomOkZero + 1
          getrandomOverMaxReadBytes := hOk.getrandomOverMaxReadBytes + overMaxHit }
      else if bs.size ≤ GETRANDOM_EXACT_MAX then
        { hOk with
          getrandomOkSmall := hOk.getrandomOkSmall + 1
          getrandomPartial := hOk.getrandomPartial + partialHit
          getrandomOverMaxReadBytes := hOk.getrandomOverMaxReadBytes + overMaxHit }
      else
        { hOk with
          getrandomOkLarge := hOk.getrandomOkLarge + 1
          getrandomPartial := hOk.getrandomPartial + partialHit
          getrandomOverMaxReadBytes := hOk.getrandomOverMaxReadBytes + overMaxHit }
    | .err e =>
      if e == Errno.EINVAL || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS || e == Errno.ERANGE then
        { h' with getrandomInvalidArg := h'.getrandomInvalidArg + 1 }
      else if e == Errno.EAGAIN then
        { h' with getrandomWouldBlock := h'.getrandomWouldBlock + 1 }
      else if Errno.isTransientOsErrno e then
        { h' with getrandomTransient := h'.getrandomTransient + 1 }
      else
        { h' with getrandomOtherErr := h'.getrandomOtherErr + 1 }
    | _ => h'

private def withArmSigalrm {α : Type} (armSigUs : UInt32) (saRestart : Bool) (act : IO α) : IO α := do
  if armSigUs > 0 then
    try
      armSigalrmRaw armSigUs (if saRestart then 1 else 0)
      let r ← act
      disarmSigalrmRaw 0
      return r
    catch e =>
      disarmSigalrmRaw 0
      throw e
  else
    act

private def execAction (act : TimeRandFuzzAction) : IO TimeRandOutcome := do
  match act with
  | .clock_gettime clk =>
    return outcomeOfTimespec (← clock_gettime clk)
  | .clock_nanosleep clk abstime req armSigUs saRestart =>
    withArmSigalrm armSigUs saRestart do
      return outcomeOfUnit (← clock_nanosleep clk abstime req)
  | .getrandom len flags armSigUs saRestart =>
    withArmSigalrm armSigUs saRestart do
      return outcomeOfBytes (← getrandom len flags)

private def resolveReplayAction (entry : ReplayFuzzAction) : IO TimeRandFuzzAction := do
  match entry.act, entry.abstimeOffsetNs? with
  | .clock_nanosleep clk true _ armSigUs saRestart, some deltaNs =>
    match ← clock_gettime clk with
    | .ok nowTs =>
      let baseNs := match clk with
        | .monotonic => Int.ofNat nowTs.toNanosNat
        | .realtime => timespecToEpochInt nowTs
      match Timespec.ofEpochNanos? (baseNs + deltaNs) with
      | some freshTs => return .clock_nanosleep clk true freshTs armSigUs saRestart
      | none => return entry.act
    | .error _ => return entry.act
  | _, _ => return entry.act

private inductive SyscallKind where
  | gettime
  | nanosleep
  | getrandom
  deriving BEq, Repr

private inductive OutcomeClass where
  | ok
  | err (eno : Errno)
  deriving BEq, Repr

private abbrev MismatchClass := SyscallKind × OutcomeClass

private def reqSyscallKind : TimeRandReq → SyscallKind
  | .clock_gettime _ => .gettime
  | .clock_nanosleep _ _ _ => .nanosleep
  | .getrandom _ _ => .getrandom

private def outcomeClass : TimeRandOutcome → OutcomeClass
  | .err e => .err e
  | _ => .ok

private def checkTraceAgainstModel (initSt : TimeRandState) (trace : Array ReplayFuzzAction) :
    IO (Option MismatchClass) := do
  let mut st := initSt
  let mut hEnv : HealthyEnv := { state := initSt, eintrBudget := trace.size }
  for entry in trace do
    let act ← resolveReplayAction entry
    let out ← execAction act
    match allowedStep st act.toReq out with
    | some st' =>
      if hEnv.wf && !isCriticalFault out then
        match healthyStep hEnv act.toReq out with
        | some hEnv' =>
          if hEnv'.state != st' then
            return some (reqSyscallKind act.toReq, outcomeClass out)
          hEnv := hEnv'
        | none => return some (reqSyscallKind act.toReq, outcomeClass out)
      else
        if (healthyStep hEnv act.toReq out).isSome then
          return some (reqSyscallKind act.toReq, outcomeClass out)
        hEnv := { hEnv with state := st' }
      st := st'
    | none => return some (reqSyscallKind act.toReq, outcomeClass out)
  return none

private def evalModelOpsReq (st : TimeRandState) (req : TimeRandReq) :
    TimeRandReq × TimeRandOutcome × TimeRandState :=
  let boundedReq := match req with
    | .getrandom len flags => .getrandom (min len 65536) flags
    | other => other
  let (out, st') := match boundedReq with
    | .clock_gettime clk =>
      let (r, s') := (modelOps.clock_gettime clk).run st
      (outcomeOfTimespec r, s')
    | .clock_nanosleep clk abstime ts =>
      let (r, s') := (modelOps.clock_nanosleep clk abstime ts).run st
      (outcomeOfUnit r, s')
    | .getrandom len flags =>
      let (r, s') := (modelOps.getrandom len flags).run st
      (outcomeOfBytes r, s')
  (boundedReq, out, st')

private def checkModelOpsTrace (initSt : TimeRandState) (trace : Array ReplayFuzzAction) :
    Option MismatchClass := Id.run do
  let mut st := initSt
  for entry in trace do
    let (boundedReq, out, st') := evalModelOpsReq st entry.act.toReq
    if allowedStep st boundedReq out == some st' then
      st := st'
    else
      return some (reqSyscallKind boundedReq, outcomeClass out)
  return none

private def actionPayloadCandidates (entry : ReplayFuzzAction) : Array ReplayFuzzAction := Id.run do
  let mut cands : Array ReplayFuzzAction := #[]
  let pushAct (a : TimeRandFuzzAction) (off? : Option Int := entry.abstimeOffsetNs?)
      (arr : Array ReplayFuzzAction) : Array ReplayFuzzAction :=
    if a == entry.act && off? == entry.abstimeOffsetNs? then arr
    else arr.push { act := a, abstimeOffsetNs? := off? }
  match entry.act with
  | .clock_gettime _ => pure ()
  | .clock_nanosleep clk abstime req armUs saRestart =>
    if saRestart then
      cands := pushAct (.clock_nanosleep clk abstime req armUs false) entry.abstimeOffsetNs? cands
    if armUs > 0 then
      cands := pushAct (.clock_nanosleep clk abstime req 0 false) entry.abstimeOffsetNs? cands
      if armUs > 1 then
        cands := pushAct (.clock_nanosleep clk abstime req (armUs / 2) saRestart) entry.abstimeOffsetNs? cands
    for secCand in #[0, -1, 1, Int64.ofInt (req.sec.toInt / 2)] do
      if secCand != req.sec then
        cands := pushAct (.clock_nanosleep clk abstime { req with sec := secCand } armUs saRestart) entry.abstimeOffsetNs? cands
    for nsecCand in #[0, 1, UInt32.ofNat NSEC_PER_SEC, req.nsec / 2] do
      if nsecCand != req.nsec then
        cands := pushAct (.clock_nanosleep clk abstime { req with nsec := nsecCand } armUs saRestart) entry.abstimeOffsetNs? cands
    if let some delta := entry.abstimeOffsetNs? then
      if delta != 0 then
        cands := pushAct entry.act (some 0) cands
        if delta > 1 || delta < -1 then
          cands := pushAct entry.act (some (delta / 2)) cands
  | .getrandom len flags armUs saRestart =>
    if saRestart then
      cands := pushAct (.getrandom len flags armUs false) none cands
    if armUs > 0 then
      cands := pushAct (.getrandom len flags 0 false) none cands
      if armUs > 1 then
        cands := pushAct (.getrandom len flags (armUs / 2) saRestart) none cands
    for lenCand in #[0, 1, 16, 256, 4096, len / 2] do
      if lenCand < len then
        cands := pushAct (.getrandom lenCand flags armUs saRestart) none cands
    if flags.nonblock then
      cands := pushAct (.getrandom len { flags with nonblock := false } armUs saRestart) none cands
    if flags.random then
      cands := pushAct (.getrandom len { flags with random := false } armUs saRestart) none cands
    if flags.insecure then
      cands := pushAct (.getrandom len { flags with insecure := false } armUs saRestart) none cands
  return cands

private partial def shrinkActionPayloads {m : Type → Type} [Monad m]
    (fails : Array ReplayFuzzAction → m Bool) (trace : Array ReplayFuzzAction) :
    m (Array ReplayFuzzAction) := do
  let mut cur := trace
  for idx in [0 : cur.size] do
    let mut keepGoing := true
    while keepGoing do
      keepGoing := false
      let cands := actionPayloadCandidates cur[idx]!
      for cand in cands do
        let next := cur.set! idx cand
        if ← fails next then
          cur := next
          keepGoing := true
          break
  return cur

/-- Greedy delta-minimization shrinker reducing any failing trace toward a minimal reproducing subtrace. -/
partial def shrinkTrace {m : Type → Type} [Monad m] {α : Type}
    (fails : Array α → m Bool) (trace : Array α) : m (Array α) := do
  if trace.size ≤ 1 then
    return trace
  let mut cur := trace
  let mut chunk := max 1 (cur.size / 2)
  while chunk ≥ 1 && cur.size > 1 do
    let mut improved := false
    let mut start := 0
    while start < cur.size && cur.size > 1 do
      let stop := min cur.size (start + chunk)
      let cand := cur.extract 0 start ++ cur.extract stop cur.size
      if !cand.isEmpty && (← fails cand) then
        cur := cand
        chunk := min chunk (max 1 (cur.size / 2))
        improved := true
      else
        start := start + chunk
    if !improved then
      if chunk == 1 then
        break
      chunk := max 1 (chunk / 2)
  return cur

private def shrinkFailingReplayTrace {m : Type → Type} [Monad m]
    (fails : Array ReplayFuzzAction → m Bool) (trace : Array ReplayFuzzAction) :
    m (Array ReplayFuzzAction) := do
  let sub ← shrinkTrace fails trace
  shrinkActionPayloads fails sub

/-- Run `--self-test-shrink` verifying trace minimization, mismatch-class pinning, payload shrinking, and real replay execution. -/
def selfTestShrink (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x517cc1b727220a95)
  let mut trace : Array TimeRandFuzzAction := #[]
  for _ in List.range 12 do
    let (entry, r') := genAction rng none none
    rng := r'
    trace := trace.push entry.act
  let (targetIdx, rIdx) := rng.nextNat trace.size
  let (badTs, rBad) := genInvalidTimespec rIdx
  let trace1 := trace.set! targetIdx (.clock_nanosleep .monotonic true badTs 0 false)
  let isSingleFailure (xs : Array TimeRandFuzzAction) : IO Bool :=
    return xs.any fun
      | .clock_nanosleep _ true req _ _ => !req.isValid
      | _ => false
  let shrunk1 ← shrinkTrace isSingleFailure trace1
  unless shrunk1.size == 1 && (← isSingleFailure shrunk1) do
    throw (IO.userError s!"SELF_TEST_SHRINK failed 1-step: shrunk size={shrunk1.size}")
  let mut trace2 : Array TimeRandFuzzAction := #[]
  let mut rng2 := rBad
  for _ in List.range 12 do
    let (entry, r') := genAction rng2 none none
    rng2 := r'
    trace2 := trace2.push entry.act
  let markA : TimeRandFuzzAction := .getrandom 0 { nonblock := true, random := false, insecure := true } 0 false
  let markB : TimeRandFuzzAction := .getrandom 1 { nonblock := false, random := true, insecure := false } 0 false
  let trace2Clean := trace2.map fun a =>
    if a == markA || a == markB then .clock_gettime .monotonic else a
  let (idxA, rA) := rng2.nextNat 6
  let (idxBRel, _) := rA.nextNat 6
  let idxB := 6 + idxBRel
  let trace2Marked := (trace2Clean.set! idxA markA).set! idxB markB
  let isStatefulTwoStepFailure (xs : Array TimeRandFuzzAction) : IO Bool := do
    let mut sawA := false
    for x in xs do
      if x == markA then
        sawA := true
      else if x == markB && sawA then
        return true
    return false
  let shrunk2 ← shrinkTrace isStatefulTwoStepFailure trace2Marked
  unless shrunk2.size == 2 && (← isStatefulTwoStepFailure shrunk2) do
    throw (IO.userError s!"SELF_TEST_SHRINK failed 2-step stateful: shrunk size={shrunk2.size}")
  let realTrace : Array ReplayFuzzAction := #[
    { act := .clock_gettime .monotonic },
    { act := .clock_nanosleep .monotonic true { sec := 0, nsec := 1000 } 0 false, abstimeOffsetNs? := some 1000 },
    { act := .clock_gettime .realtime },
    { act := .clock_nanosleep .monotonic false { sec := -1, nsec := 0 } 0 false },
    { act := .getrandom 16 { nonblock := true } 0 false },
    { act := .getrandom 1024 { random := true } 100 true },
    { act := .clock_gettime .monotonic }
  ]
  if let some badCls ← checkTraceAgainstModel TimeRandState.initial realTrace then
    throw (IO.userError s!"SELF_TEST_SHRINK realTrace violated model: {repr badCls}")
  let targetCls : MismatchClass := (.getrandom, .ok)
  let evalWithInjectedBug (cand : Array ReplayFuzzAction) : IO (Option MismatchClass) := do
    if let some c ← checkTraceAgainstModel TimeRandState.initial cand then
      return some c
    for entry in cand do
      let act ← resolveReplayAction entry
      let out ← execAction act
      match act, out with
      | .getrandom len _ _ _, .bytes _ =>
        if len > 200 then
          return some (.getrandom, .ok)
      | _, _ => pure ()
    return none
  let shrunkReal ← shrinkFailingReplayTrace
    (fun cand => do return (← evalWithInjectedBug cand) == some targetCls) realTrace
  let payloadShrunkOk := match shrunkReal.toList with
    | [{ act := .getrandom len flags armUs saRestart, abstimeOffsetNs? := none }] =>
      len == 256 && !flags.random && armUs == 0 && !saRestart
    | _ => false
  unless payloadShrunkOk do
    throw (IO.userError s!"SELF_TEST_SHRINK failed real replay + slippage/payload pin: shrunkReal={repr shrunkReal}")
  IO.println s!"SELF_TEST_SHRINK: PASS original={trace1.size} shrunk1={shrunk1.size} shrunk2={shrunk2.size} real_payload={shrunkReal.size}"

private def assertCoverage (steps : Nat) (hits : TimeRandHitCounters)
    (requireEnvSubEpisodes : Bool) (allowNoTimens : Bool := false) : IO Unit := do
  if steps ≥ 1000 then
    if hits.gettimeRealtimeOk == 0 || hits.gettimeMonotonicOk == 0 then
      throw (IO.userError s!"fuzz coverage gap in clock_gettime: {repr hits}")
    if hits.nanosleepRelMonoOk == 0 || hits.nanosleepRelRealOk == 0 ||
        hits.nanosleepAbsMonoOk == 0 || hits.nanosleepAbsRealOk == 0 ||
        hits.nanosleepInvalidArg == 0 then
      throw (IO.userError s!"fuzz coverage gap in clock_nanosleep (clocks/abstime/invalidArg): {repr hits}")
    if hits.getrandomOkZero == 0 || hits.getrandomOkSmall == 0 ||
        hits.getrandomOkLarge == 0 || hits.getrandomInvalidArg == 0 ||
        (hits.getrandomValidFlagsMask &&& 0x3F) != 0x3F then
      throw (IO.userError s!"fuzz coverage gap in getrandom (sizes/flags): {repr hits}")
    if requireEnvSubEpisodes then
      if hits.envSeccompOk != 13 then
        throw (IO.userError s!"fuzz coverage gap in outer seccomp sub-episodes (expected 13): {repr hits}")
      if hits.gettimeErr == 0 || hits.getrandomWouldBlock == 0 || hits.getrandomTransient == 0 then
        throw (IO.userError s!"fuzz coverage gap in seccomp gettime/getrandom errors: {repr hits}")
      if !allowNoTimens && hits.envTimensExpected != 7 then
        throw (IO.userError s!"fuzz coverage gap in CLONE_NEWTIME sub-episodes (expected 7, got {hits.envTimensExpected}): {repr hits}")
      if hits.envTimensExpected > 0 && hits.envTimensOk != hits.envTimensExpected then
        throw (IO.userError s!"fuzz coverage gap in CLONE_NEWTIME sub-episodes (expected {hits.envTimensExpected}): {repr hits}")
  if steps ≥ 50000 then
    if hits.nanosleepTransient ≤ hits.nanosleepAbstimeTransient || hits.nanosleepAbstimeTransient == 0 then
      throw (IO.userError s!"fuzz coverage gap in clock_nanosleep EINTR (relative-only and abstime required): {repr hits}")
    if hits.getrandomPartial == 0 || hits.getrandomOverMaxReadBytes == 0 then
      throw (IO.userError s!"fuzz coverage gap in getrandom partial read / MAX_READ_BYTES clamp: {repr hits}")

private def checkSeccompTrace (initSt : TimeRandState) (eno mask : UInt32)
    (trace : Array ReplayFuzzAction) : IO (Option MismatchClass) := do
  let mut st := initSt
  for entry in trace do
    let act ← resolveReplayAction entry
    let out ← execAction act
    let cls := (reqSyscallKind act.toReq, outcomeClass out)
    let isBlocked := match act with
      | .clock_gettime _ => (mask &&& 1) != 0
      | .clock_nanosleep _ _ _ _ _ => (mask &&& 2) != 0
      | .getrandom _ _ _ _ => (mask &&& 4) != 0
    if isBlocked && out != .err eno then
      return some cls
    if !isBlocked then
      match allowedStep { st with ambientSeccomp := false } act.toReq out with
      | some _ => pure ()
      | none => return some cls
    match allowedStep st act.toReq out with
    | some st' =>
      if (healthyStep { state := st, eintrBudget := 2 } act.toReq out).isSome then
        return some cls
      st := st'
    | none => return some cls
  return none

/-- Run a child fuzz episode under an installed `SECCOMP_RET_ERRNO` filter matching `TimeRandState.withOuterSeccomp` (rejecting `eno = 0` or `> 4095`), optionally executing `delaySteps` un-filtered steps beforehand. -/
def fuzzTimeRandSeccompChild (steps : Nat) (seedVal : UInt64) (eno : UInt32)
    (mask : UInt32 := 7) (delaySteps : Nat := 0) :
    IO TimeRandFuzzReport := do
  if eno == 0 || eno > 4095 then
    throw (IO.userError s!"seccomp child rejects non-errno spoofing SECCOMP_RET_ERRNO | {eno} (valid kernel errnos are 1..4095)")
  if mask == 0 || mask > 7 then
    throw (IO.userError s!"seccomp child invalid syscall mask {mask} (expected 1..7)")
  let totalSteps := delaySteps + steps
  let mut rng := Rng.seed seedVal
  let mut hits : TimeRandHitCounters := {}
  let mut st := if delaySteps == 0 then TimeRandState.initial.withOuterSeccomp else TimeRandState.initial
  let mut seccompInstalled := false
  if delaySteps == 0 then
    let rc ← SandboxEnv.installTimeRandSeccompErrno eno mask
    if rc != 0 then
      throw (IO.userError s!"installTimeRandSeccompErrno({eno}, {mask}) failed with errno {rc}")
    seccompInstalled := true
  let mut lastMono? : Option Timespec := none
  let mut lastReal? : Option Timespec := none
  let mut trace : Array ReplayFuzzAction := Array.mkEmpty totalSteps
  let mut postInitSt : TimeRandState := st
  let mut postTrace : Array ReplayFuzzAction := Array.mkEmpty steps
  let mut gettimePostCount : Nat := 0
  let mut sleepValidCount : Nat := 0
  let mut sleepInvalidCount : Nat := 0
  let mut randValidCount : Nat := 0
  let mut randInvalidCount : Nat := 0
  for stepIdx in List.range totalSteps do
    if !seccompInstalled && stepIdx == delaySteps then
      if delaySteps ≥ 100 && (st.monoLowerBoundNs == 0 || !st.crngReady) then
        throw (IO.userError s!"mid-episode seccomp child warmup ({delaySteps} steps) did not advance state: mono={st.monoLowerBoundNs} crngReady={st.crngReady}")
      let rc ← SandboxEnv.installTimeRandSeccompErrno eno mask
      if rc != 0 then
        throw (IO.userError s!"mid-episode installTimeRandSeccompErrno({eno}, {mask}) failed with errno {rc}")
      st := st.withOuterSeccomp
      postInitSt := st
      seccompInstalled := true
    let (entry, r') := genAction rng lastMono? lastReal?
    let act := entry.act
    rng := r'
    trace := trace.push entry
    if seccompInstalled then
      postTrace := postTrace.push entry
    let out ← execAction act
    hits := recordHit hits act out
    let isBlocked := seccompInstalled && match act with
      | .clock_gettime _ => (mask &&& 1) != 0
      | .clock_nanosleep _ _ _ _ _ => (mask &&& 2) != 0
      | .getrandom _ _ _ _ => (mask &&& 4) != 0
    if seccompInstalled then
      match act with
      | .clock_gettime _ => gettimePostCount := gettimePostCount + 1
      | .clock_nanosleep _ _ req _ _ =>
        if req.isValid then sleepValidCount := sleepValidCount + 1 else sleepInvalidCount := sleepInvalidCount + 1
      | .getrandom _ flags _ _ =>
        if !flags.isInvalid then randValidCount := randValidCount + 1 else randInvalidCount := randInvalidCount + 1
    let stepOk :=
      (!isBlocked || out == .err eno) &&
      (isBlocked || (allowedStep { st with ambientSeccomp := false } act.toReq out).isSome)
    let nextSt? := if stepOk then allowedStep st act.toReq out else none
    match nextSt? with
    | some st' =>
      st := st'
      match act, out with
      | .clock_gettime .monotonic, .timespec ts => lastMono? := some ts
      | .clock_gettime .realtime, .timespec ts => lastReal? := some ts
      | _, _ => pure ()
    | none =>
      let origCls : MismatchClass := (reqSyscallKind act.toReq, outcomeClass out)
      if seccompInstalled then
        let shrunk ← shrinkFailingReplayTrace
          (fun cand => do return (← checkSeccompTrace postInitSt eno mask cand) == some origCls) postTrace
        throw (IO.userError s!"seccomp child model violation at step {stepIdx}: shrunk={repr shrunk}")
      else
        let shrunk ← shrinkFailingReplayTrace
          (fun cand => do return (← checkTraceAgainstModel TimeRandState.initial cand) == some origCls) trace
        throw (IO.userError s!"pre-seccomp child model violation at step {stepIdx}: shrunk={repr shrunk}")
  if gettimePostCount == 0 || sleepValidCount == 0 || sleepInvalidCount == 0 ||
      randValidCount == 0 || randInvalidCount == 0 then
    throw (IO.userError s!"seccomp child coverage gap (steps={steps}, mask={mask}): gettime={gettimePostCount} sleep=({sleepValidCount},{sleepInvalidCount}) rand=({randValidCount},{randInvalidCount})")
  IO.println s!"SECCOMP_HITS={hits.gettimeErr},{hits.getrandomWouldBlock},{hits.getrandomTransient}"
  return { steps := totalSteps, episodes := 1, elapsedMs := 1, hits := hits }

private def parseTaggedPrefix? (tag stdout : String) : Option String :=
  (stdout.splitOn "\n").findSome? fun line =>
    let t := line.trimAscii.toString
    if t.startsWith tag then some (t.drop tag.length).toString else none

private def parseSeccompHits (stdout : String) : Nat × Nat × Nat :=
  match parseTaggedPrefix? "SECCOMP_HITS=" stdout with
  | none => (0, 0, 0)
  | some rest =>
    match rest.splitOn "," with
    | [a, b, c] => (a.toNat?.getD 0, b.toNat?.getD 0, c.toNat?.getD 0)
    | _ => (0, 0, 0)

private def runEnvSubEpisodesFn (seedVal : UInt64) (allowNoTimens : Bool := false) :
    IO (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let exe ← IO.appPath
  let mut seccompOk : Nat := 0
  let mut aggGettimeErr : Nat := 0
  let mut aggRandWouldBlock : Nat := 0
  let mut aggRandTransient : Nat := 0
  let blanketErrnos : List Errno :=
    [Errno.EPERM, Errno.EACCES, Errno.ENOSYS, Errno.EAGAIN, Errno.EINVAL, (4095 : Errno)]
  let mut idx : Nat := 0
  for eno in blanketErrnos do
    let subSeed := seedVal ^^^ UInt64.ofNat (0x100 + idx)
    idx := idx + 1
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #[ "--suite", "timerand"
               , "--env-child", "seccomp"
               , "--seccomp-errno", toString eno.toNat
               , "--seccomp-mask", "7"
               , "--steps", "300"
               , "--seed", toString subSeed.toNat ]
    }
    if out.exitCode != 0 then
      throw (IO.userError s!"outer seccomp blanket sub-episode ({Errno.name eno}) failed exit={out.exitCode}: {out.stderr}")
    let (ge, rwb, rtr) := parseSeccompHits out.stdout
    aggGettimeErr := aggGettimeErr + ge
    aggRandWouldBlock := aggRandWouldBlock + rwb
    aggRandTransient := aggRandTransient + rtr
    seccompOk := seccompOk + 1
  let selectiveSpecs : List (Errno × UInt32) :=
    [ (Errno.EPERM, 1)
    , (Errno.EINVAL, 2)
    , (Errno.EAGAIN, 3)
    , (Errno.EINTR, 4)
    , (Errno.EACCES, 5)
    , (Errno.ENOSYS, 6) ]
  for (eno, mask) in selectiveSpecs do
    let subSeed := seedVal ^^^ UInt64.ofNat (0x180 + mask.toNat)
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #[ "--suite", "timerand"
               , "--env-child", "seccomp"
               , "--seccomp-errno", toString eno.toNat
               , "--seccomp-mask", toString mask.toNat
               , "--steps", "300"
               , "--seed", toString subSeed.toNat ]
    }
    if out.exitCode != 0 then
      throw (IO.userError s!"outer seccomp selective sub-episode ({Errno.name eno}, mask={mask}) failed exit={out.exitCode}: {out.stderr}")
    let (ge, rwb, rtr) := parseSeccompHits out.stdout
    aggGettimeErr := aggGettimeErr + ge
    aggRandWouldBlock := aggRandWouldBlock + rwb
    aggRandTransient := aggRandTransient + rtr
    seccompOk := seccompOk + 1
  let midSeed := seedVal ^^^ 0x1C0
  let midOut ← IO.Process.output {
    cmd := exe.toString
    args := #[ "--suite", "timerand"
             , "--env-child", "seccomp"
             , "--seccomp-errno", toString Errno.EPERM.toNat
             , "--seccomp-mask", "7"
             , "--seccomp-delay-steps", "500"
             , "--steps", "500"
             , "--seed", toString midSeed.toNat ]
  }
  if midOut.exitCode != 0 then
    throw (IO.userError s!"mid-episode outer seccomp sub-episode failed exit={midOut.exitCode}: {midOut.stderr}")
  let (mge, mrwb, mrtr) := parseSeccompHits midOut.stdout
  aggGettimeErr := aggGettimeErr + mge
  aggRandWouldBlock := aggRandWouldBlock + mrwb
  aggRandTransient := aggRandTransient + mrtr
  seccompOk := seccompOk + 1
  let mut timensOk : Nat := 0
  let mut timensExpected : Nat := 0
  let pyScript :=
    "import ctypes, os, sys\n" ++
    "ms, mns, bs, bns = sys.argv[1:5]\n" ++
    "exe = sys.argv[5]\n" ++
    "args = sys.argv[5:]\n" ++
    "libc = ctypes.CDLL(None, use_errno=True)\n" ++
    "libc.unshare.argtypes = [ctypes.c_int]\n" ++
    "libc.unshare.restype = ctypes.c_int\n" ++
    "uid, gid = os.getuid(), os.getgid()\n" ++
    "rc = libc.unshare(0x10000000 | 0x00000080)\n" ++
    "assert rc == 0, f'unshare errno={ctypes.get_errno()}'\n" ++
    "for p, data in [\n" ++
    "    ('/proc/self/setgroups', b'deny'),\n" ++
    "    ('/proc/self/uid_map', f'0 {uid} 1\\n'.encode()),\n" ++
    "    ('/proc/self/gid_map', f'0 {gid} 1\\n'.encode()),\n" ++
    "    ('/proc/self/timens_offsets', f'monotonic {ms} {mns}\\nboottime {bs} {bns}\\n'.encode()),\n" ++
    "]:\n" ++
    "    with open(p, 'wb', buffering=0) as f:\n" ++
    "        f.write(data)\n" ++
    "pid = os.fork()\n" ++
    "if pid == 0:\n" ++
    "    os.execv(exe, args)\n" ++
    "_, st = os.waitpid(pid, 0)\n" ++
    "sys.exit(os.waitstatus_to_exitcode(st))"
  let probe ← IO.Process.output {
    cmd := "python3"
    args := #["-c", pyScript, "3600", "0", "7200", "0", "/bin/true"]
  }
  if probe.exitCode != 0 then
    if !allowNoTimens then
      throw (IO.userError s!"CLONE_NEWTIME probe failed exit={probe.exitCode}: {probe.stderr} (pass --allow-no-timens only when unprivileged CLONE_NEWTIME is unavailable locally)")
  else
    timensExpected := 7
    let curMonoSec : Int ← match ← clock_gettime .monotonic with
      | .ok ts => pure ts.sec.toInt
      | .error _ => pure 0
    let bootOut ← IO.Process.output {
      cmd := "python3"
      args := #["-c", "import time; print(int(time.clock_gettime(time.CLOCK_BOOTTIME)))"]
    }
    let curBootSec : Int :=
      if bootOut.exitCode == 0 then
        bootOut.stdout.trimAscii.toString.toInt?.getD curMonoSec
      else
        curMonoSec
    let modNegMono := if curMonoSec ≥ 2 then toString (-(min 60 (curMonoSec / 2))) else "0"
    let modNegBoot := if curBootSec ≥ 2 then toString (-(min 30 (curBootSec / 2))) else "0"
    let nearZeroMono := if curMonoSec ≥ 2 then toString (-(curMonoSec - 1)) else "0"
    let nearZeroBoot := if curBootSec ≥ 2 then "-1" else "0"
    let fracNegMono := if curMonoSec ≥ 2 then toString (-(curMonoSec - 1)) else "0"
    let fracNegBoot := if curBootSec ≥ 2 then "-1" else "0"
    let highMono := if curMonoSec < 4611000000 then toString (4611000000 - curMonoSec) else "0"
    let cappedBoot := if curBootSec < 4611000000 then toString (min 4000000000 (4611000000 - curBootSec)) else "0"
    let offsets : List (String × String × String × String × Nat) :=
      [ ("3600", "0", "7200", "0", 1)
      , (modNegMono, "0", modNegBoot, "0", 2)
      , (cappedBoot, "0", cappedBoot, "0", 3)
      , (nearZeroMono, "0", nearZeroBoot, "0", 4)
      , (highMono, "0", cappedBoot, "0", 5)
      , (fracNegMono, "500000000", fracNegBoot, "500000000", 6)
      , (highMono, "999999999", cappedBoot, "999999999", 7) ]
    for (monoSec, monoNsec, bootSec, bootNsec, offId) in offsets do
      let subSeed := seedVal ^^^ UInt64.ofNat (0x200 + offId)
      let mBefore ← match ← clock_gettime .monotonic with
        | .ok ts => pure ts
        | .error e => throw (IO.userError s!"parent clock_gettime before timens failed: {Errno.name e}")
      let out ← IO.Process.output {
        cmd := "python3"
        args := #[ "-c", pyScript
                 , monoSec, monoNsec, bootSec, bootNsec
                 , exe.toString
                 , "--suite", "timerand"
                 , "--env-child", "timens"
                 , "--steps", "1000"
                 , "--seed", toString subSeed.toNat ]
      }
      let mAfter ← match ← clock_gettime .monotonic with
        | .ok ts => pure ts
        | .error e => throw (IO.userError s!"parent clock_gettime after timens failed: {Errno.name e}")
      if out.exitCode != 0 then
        throw (IO.userError s!"CLONE_NEWTIME sub-episode (mono={monoSec}s+{monoNsec}ns, boot={bootSec}s+{bootNsec}ns) failed exit={out.exitCode}: {out.stderr}")
      let some obsStr := parseTaggedPrefix? "FIRST_MONO_NS=" out.stdout
        | throw (IO.userError s!"CLONE_NEWTIME sub-episode missing FIRST_MONO_NS: {out.stdout}")
      let some obsNs := obsStr.toNat?
        | throw (IO.userError s!"CLONE_NEWTIME sub-episode invalid FIRST_MONO_NS={obsStr}")
      let offNs : Int := (monoSec.toInt?.getD 0) * (NSEC_PER_SEC : Int) + (monoNsec.toInt?.getD 0)
      let minExp : Int := max 0 (Int.ofNat mBefore.toNanosNat + offNs - 2000000000)
      let maxExp : Int := max 0 (Int.ofNat mAfter.toNanosNat + offNs + 30000000000)
      if Int.ofNat obsNs < minExp || Int.ofNat obsNs > maxExp then
        throw (IO.userError s!"CLONE_NEWTIME sub-episode #{offId} clock_gettime.monotonic unshifted or out of window: obs={obsNs}ns expected=[{minExp}, {maxExp}]ns (offset={monoSec}s+{monoNsec}ns)")
      timensOk := timensOk + 1
  return (seccompOk, timensOk, timensExpected, aggGettimeErr, aggRandWouldBlock, aggRandTransient)

private def runModelOpsSelfCheck : IO Unit := do
  let (rMax, stMax) := (modelOps.getrandom MAX_READ_BYTES {}).run TimeRandState.initial
  match rMax with
  | .ok bs =>
    unless bs.size == MAX_READ_BYTES.toNat && stMax.crngReady do
      throw (IO.userError s!"modelOps.getrandom MAX_READ_BYTES unexpected result: size={bs.size}")
  | .error e =>
    throw (IO.userError s!"modelOps.getrandom MAX_READ_BYTES failed: {e}")
  let sRealOob := TimeRandState.initial (realtimeNs := (Int.ofNat MAX_TIMESPEC_SEC + 1) * Int.ofNat NSEC_PER_SEC)
  let (rRt, sRt') := (modelOps.clock_gettime .realtime).run sRealOob
  unless (allowedStep sRealOob (.clock_gettime .realtime) (outcomeOfTimespec rRt) == some sRt') do
    throw (IO.userError "modelOps.clock_gettime .realtime out-of-range failed allowedStep")
  let (_, sOv1) := (modelOps.clock_nanosleep .monotonic false { sec := Int64.maxValue, nsec := 0 }).run TimeRandState.initial
  let (_, sOv2) := (modelOps.clock_nanosleep .monotonic false { sec := 1, nsec := 0 }).run sOv1
  let (rOvGet, sOv3) := (modelOps.clock_gettime .monotonic).run sOv2
  match rOvGet with
  | .ok _ =>
    unless allowedStep sOv2 (.clock_gettime .monotonic) (outcomeOfTimespec rOvGet) == some sOv3 do
      throw (IO.userError "modelOps.clock_gettime .monotonic post-overflow rejected by allowedStep")
  | .error e =>
    throw (IO.userError s!"modelOps.clock_gettime .monotonic post-overflow returned error {e}")

private def stepModelOpsDifferential (st : TimeRandState) (req : TimeRandReq) :
    Option (MismatchClass × TimeRandState) :=
  let (boundedReq, out, st') := evalModelOpsReq st req
  if allowedStep st boundedReq out != some st' then
    some ((reqSyscallKind boundedReq, outcomeClass out), st')
  else if !st.ambientSeccomp then
    let h0 : HealthyEnv := { state := st, eintrBudget := 2 }
    let (hOut, h1) := (execTimeRandReq healthyModelOps boundedReq).run h0
    if hOut == out && healthyStep h0 boundedReq hOut == some h1 &&
        h1.wf && h1.eintrBudget == 2 && h1.state == st' then
      none
    else
      some ((reqSyscallKind boundedReq, outcomeClass hOut), h1.state)
  else
    none

/-- Run the stateful `TimeRand` real-syscall fuzz loop for `steps` calls starting from `seedVal`. -/
def fuzzTimeRand (steps : Nat) (seedVal : UInt64)
    (runEnvSubEpisodes : Bool := false) (allowNoTimens : Bool := false) : IO TimeRandFuzzReport := do
  let t0 ← IO.monoMsNow
  if runEnvSubEpisodes then
    runModelOpsSelfCheck
  let mut rng := Rng.seed seedVal
  let mut done := 0
  let mut episodes := 0
  let mut hits : TimeRandHitCounters := {}
  let mut globalMonoNs : Nat := 0
  let mut globalCrngReady : Bool := false
  let mut firstMonoNs? : Option Nat := none
  let mut modelSt := TimeRandState.initial
  while done < steps do
    episodes := episodes + 1
    let (epTarget, rEp) := rng.nextRange 8 32
    rng := rEp
    let epLen := min epTarget (steps - done)
    let epInitSt : TimeRandState := { TimeRandState.initial with
      monoLowerBoundNs := globalMonoNs
      crngReady := globalCrngReady }
    let modelEpInitSt := modelSt
    let mut st := epInitSt
    let mut hEnv : HealthyEnv := { state := epInitSt, eintrBudget := epLen }
    let mut epTrace : Array ReplayFuzzAction := Array.mkEmpty epLen
    let mut lastMono? : Option Timespec := none
    let mut lastReal? : Option Timespec := none
    for _ in List.range epLen do
      let (entry, rAct) := genAction rng lastMono? lastReal?
      let act := entry.act
      rng := rAct
      epTrace := epTrace.push entry
      match stepModelOpsDifferential modelSt act.toReq with
      | none =>
        let (_, _, nextModelSt) := evalModelOpsReq modelSt act.toReq
        modelSt := nextModelSt
      | some (origCls, _) =>
        let shrunk ← shrinkFailingReplayTrace
          (fun cand => pure (checkModelOpsTrace modelEpInitSt cand == some origCls)) epTrace
        throw (IO.userError s!"modelOps differential violation at step {done} (seed={seedVal}, shrunk={repr shrunk}): req={repr act.toReq}")
      let out ← execAction act
      hits := recordHit hits act out
      match act, out with
      | .clock_gettime .monotonic, .timespec ts =>
        lastMono? := some ts
        if firstMonoNs?.isNone then
          firstMonoNs? := some ts.toNanosNat
      | .clock_gettime .realtime, .timespec ts => lastReal? := some ts
      | _, _ => pure ()
      match allowedStep st act.toReq out with
      | some st' =>
        if !isCriticalFault out then
          match healthyStep hEnv act.toReq out with
          | some hEnv' =>
            if hEnv'.state != st' || !hEnv'.wf then
              throw (IO.userError s!"TimeRand healthyStep state divergence at step {done}: req={repr act.toReq} out={repr out}")
            if isEintrOutcome out then
              if hEnv'.eintrBudget + 1 != hEnv.eintrBudget ||
                  (healthyStep { hEnv with eintrBudget := 0 } act.toReq out).isSome then
                throw (IO.userError s!"TimeRand healthyStep EINTR budget violation at step {done}: req={repr act.toReq}")
            hEnv := hEnv'
          | none =>
            let origCls : MismatchClass := (reqSyscallKind act.toReq, outcomeClass out)
            let shrunk ← shrinkFailingReplayTrace
              (fun cand => do return (← checkTraceAgainstModel epInitSt cand) == some origCls) epTrace
            throw (IO.userError
              s!"TimeRand healthyStep violation at step {done} (seed={seedVal}, shrunk={repr shrunk}): req={repr act.toReq} out={repr out} env={repr hEnv}")
        else
          if (healthyStep hEnv act.toReq out).isSome then
            throw (IO.userError
              s!"TimeRand healthyStep accepted critical/unhealthy outcome at step {done}: req={repr act.toReq} out={repr out}")
          hEnv := { hEnv with state := st' }
        st := st'
        globalMonoNs := max globalMonoNs st'.monoLowerBoundNs
        globalCrngReady := globalCrngReady || st'.crngReady
      | none =>
        let origCls : MismatchClass := (reqSyscallKind act.toReq, outcomeClass out)
        let shrunk ← shrinkFailingReplayTrace
          (fun cand => do return (← checkTraceAgainstModel epInitSt cand) == some origCls) epTrace
        throw (IO.userError
          s!"TimeRand fuzz model violation at step {done} (seed={seedVal}, shrunk={repr shrunk}): req={repr act.toReq} out={repr out} state={repr st}")
      done := done + 1
  if steps ≥ 1000 && runEnvSubEpisodes then
    let (secOk, timOk, timExp, secGe, secRwb, secRtr) ← runEnvSubEpisodesFn seedVal allowNoTimens
    hits := { hits with
      gettimeErr := hits.gettimeErr + secGe
      getrandomWouldBlock := hits.getrandomWouldBlock + secRwb
      getrandomTransient := hits.getrandomTransient + secRtr
      envSeccompOk := secOk
      envTimensOk := timOk
      envTimensExpected := timExp }
  assertCoverage steps hits (steps ≥ 1000 && runEnvSubEpisodes) allowNoTimens
  let t1 ← IO.monoMsNow
  let elapsedMs := max 1 (t1 - t0)
  if !runEnvSubEpisodes then
    let obsMono ← match firstMonoNs? with
      | some ns => pure ns
      | none =>
        match ← clock_gettime .monotonic with
        | .ok ts => pure ts.toNanosNat
        | .error _ => pure 0
    IO.println s!"FIRST_MONO_NS={obsMono}"
  IO.println "SYSCALL_OUTCOME_HITS:"
  IO.println s!"  clock_gettime: total={hits.gettimeTotal} realtime_ok={hits.gettimeRealtimeOk} monotonic_ok={hits.gettimeMonotonicOk} err={hits.gettimeErr}"
  IO.println s!"  clock_nanosleep: total={hits.nanosleepTotal} ok={hits.nanosleepOk} relMonoOk={hits.nanosleepRelMonoOk} relRealOk={hits.nanosleepRelRealOk} absMonoOk={hits.nanosleepAbsMonoOk} absRealOk={hits.nanosleepAbsRealOk} invalidArg={hits.nanosleepInvalidArg} transientOrResource={hits.nanosleepTransient} abstimeTransient={hits.nanosleepAbstimeTransient} other_err={hits.nanosleepOtherErr}"
  IO.println s!"  getrandom: total={hits.getrandomTotal} ok_zero={hits.getrandomOkZero} ok_small={hits.getrandomOkSmall} ok_large={hits.getrandomOkLarge} partial={hits.getrandomPartial} overMax={hits.getrandomOverMaxReadBytes} invalidArg={hits.getrandomInvalidArg} wouldBlock={hits.getrandomWouldBlock} transient={hits.getrandomTransient} other_err={hits.getrandomOtherErr} validFlagsMask={hits.getrandomValidFlagsMask}"
  IO.println s!"  env_subepisodes: seccomp_ok={hits.envSeccompOk} timens_ok={hits.envTimensOk}/{hits.envTimensExpected}"
  let rate := (steps * 1000) / elapsedMs
  IO.println s!"FUZZ_SUMMARY suite=timerand steps={steps} episodes={episodes} elapsed_ms={elapsedMs} syscalls_per_sec={rate}"
  return { steps := steps, episodes := episodes, elapsedMs := elapsedMs, hits := hits }

end Fuzz.LinuxSyscall

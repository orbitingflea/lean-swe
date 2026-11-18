import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.Fuzz.Rng

namespace LeanSwe.LinuxSyscall.Fuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

@[extern "leanswe_fuzz_arm_sigalrm"]
private opaque armSigalrmRaw (usec : UInt32) (saRestart : UInt8) : BaseIO Unit

@[extern "leanswe_fuzz_disarm_sigalrm"]
private opaque disarmSigalrmRaw (unused : UInt32) : BaseIO Unit

@[extern "leanswe_fuzz_install_seccomp_errno"]
private opaque installSeccompErrnoRaw (eno : UInt32) (mask : UInt32) : BaseIO UInt32

/-- Action executed by the `TimeRand` world-model fuzzer, optionally arming a short `SIGALRM` around `clock_nanosleep` or `getrandom`. -/
inductive TimeRandFuzzAction where
  /-- Execute `clock_gettime(clk)`. -/
  | clock_gettime (clk : ClockId)
  /-- Execute `clock_nanosleep(clk, abstime, req)` with optional `SIGALRM` in `armSigUs` microseconds (`0` disables signal). -/
  | clock_nanosleep (clk : ClockId) (abstime : Bool) (req : Timespec) (armSigUs : UInt32) (saRestart : Bool)
  /-- Execute `getrandom(len, flags)` with optional `SIGALRM` in `armSigUs` microseconds (`0` disables signal). -/
  | getrandom (len : UInt32) (flags : GrndFlags) (armSigUs : UInt32) (saRestart : Bool)
  deriving Repr, DecidableEq, BEq

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

private def genInterruptedSleep (rng : Rng) (clk : ClockId)
    (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    TimeRandFuzzAction × Rng :=
  let (abstime, r1) := rng.chance 1 2
  let (saRestart, r2) := r1.chance 1 2
  let (armUs, r3) := r2.nextRange 80 220
  let (shape, r4) := r3.nextNat 10
  if shape == 0 then
    let (kPick, r5) := r4.nextNat 3
    let ts := match kPick with
      | 0 => ktimeMaxTs
      | 1 => ktimeMaxPlusOneTs
      | _ =>
        let (nsecVal, _) := genFullNsec r5
        { sec := Int64.maxValue, nsec := nsecVal }
    (.clock_nanosleep clk abstime ts (UInt32.ofNat armUs) saRestart, r5)
  else if shape == 1 then
    let (secPos, r5) := r4.nextRange 1 5
    let (nsecVal, r6) := genFullNsec r5
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      let futureNs := Int.ofNat secPos * (NSEC_PER_SEC : Int) + Int.ofNat nsecVal.toNat
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + futureNs)) with
      | some ts => (.clock_nanosleep clk true ts (UInt32.ofNat armUs) saRestart, r6)
      | none => (.clock_nanosleep clk true ktimeMaxTs (UInt32.ofNat armUs) saRestart, r6)
    else
      (.clock_nanosleep clk false { sec := Int64.ofInt (Int.ofNat secPos), nsec := nsecVal } (UInt32.ofNat armUs) saRestart, r6)
  else
    let (nsDur, r5) := r4.nextRange 2000000 5000000
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + Int.ofNat nsDur)) with
      | some ts => (.clock_nanosleep clk true ts (UInt32.ofNat armUs) saRestart, r5)
      | none => (.clock_nanosleep clk true ktimeMaxTs (UInt32.ofNat armUs) saRestart, r5)
    else
      (.clock_nanosleep clk false { sec := 0, nsec := UInt32.ofNat nsDur } (UInt32.ofNat armUs) saRestart, r5)

private def genNanosleepAction (rng : Rng) (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    TimeRandFuzzAction × Rng :=
  let (clk, r1) := genClockId rng
  let (bucket, r2) := r1.nextNat 100
  if bucket < 30 then
    let (abstime, r3) := r2.chance 1 2
    let (ts, r4) := genInvalidTimespec r3
    let (doSig, r5) := r4.chance 1 8
    let (armUs, r6) := if doSig then r5.nextRange 60 160 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    (.clock_nanosleep clk abstime ts (UInt32.ofNat armUs) saRestart, r7)
  else if bucket < 52 then
    let curSecNat : Nat := match clk with
      | .monotonic => match lastMono? with
        | some ts => if ts.sec.toInt > 0 then (ts.sec.toInt - 1).toNat else 0
        | none => 0
      | .realtime => match lastReal? with
        | some ts => if ts.sec.toInt > 0 then (ts.sec.toInt - 1).toNat else 0
        | none => 0
    let (secPick, r3) := r2.nextNat 3
    let (sec, r4) := match secPick with
      | 0 => (0, r3)
      | 1 => (1, r3)
      | _ => r3.nextRange 0 curSecNat
    let (nsecVal, r5) := genFullNsec r4
    (.clock_nanosleep clk true { sec := Int64.ofInt (Int.ofNat sec), nsec := nsecVal } 0 false, r5)
  else if bucket < 95 then
    let (abstime, r3) := r2.chance 1 2
    let (nsDelta, r4) := r3.nextRange 0 50000
    if abstime then
      let baseInt? := match clk with
        | .monotonic => lastMono?.map (fun ts : Timespec => Int.ofNat ts.toNanosNat)
        | .realtime => lastReal?.map timespecToEpochInt
      match baseInt?.bind (fun b => Timespec.ofEpochNanos? (b + Int.ofNat nsDelta)) with
      | some ts => (.clock_nanosleep clk true ts 0 false, r4)
      | none => (.clock_nanosleep clk true { sec := 0, nsec := UInt32.ofNat nsDelta } 0 false, r4)
    else
      (.clock_nanosleep clk false { sec := 0, nsec := UInt32.ofNat nsDelta } 0 false, r4)
  else
    genInterruptedSleep r2 clk lastMono? lastReal?

private def genGetrandomAction (rng : Rng) : TimeRandFuzzAction × Rng :=
  let (flags, r1) := genGrndFlags rng
  let (bucket, r2) := r1.nextNat 10000
  if bucket < 1000 then
    let (doSig, r3) := r2.chance 1 8
    let (armUs, r4) := if doSig then r3.nextRange 60 160 else (0, r3)
    let (saRestart, r5) := r4.chance 1 2
    (.getrandom 0 flags (UInt32.ofNat armUs) saRestart, r5)
  else if bucket < 7200 then
    let (exact256, r3) := r2.chance 1 100
    let (len, r4) := if exact256 then (256, r3) else r3.nextRange 1 256
    let (doSig, r5) := if flags.isInvalid then r4.chance 1 8 else r4.chance 1 200
    let (armUs, r6) := if doSig then r5.nextRange 80 200 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    (.getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart, r7)
  else if bucket < 9910 then
    let (exact257, r3) := r2.chance 1 100
    let (len, r4) := if exact257 then (257, r3) else r3.nextRange 257 65536
    let (doSig, r5) := if flags.isInvalid then r4.chance 1 8 else r4.chance 1 200
    let (armUs, r6) := if doSig then r5.nextRange 80 200 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    (.getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart, r7)
  else if bucket < 9950 then
    let (useExactMax, r3) := r2.chance 1 4
    let (len, r4) :=
      if useExactMax then (MAX_READ_BYTES.toNat, r3)
      else r3.nextRange 65537 MAX_READ_BYTES.toNat
    let (doSig, r5) := r4.chance 1 4
    let (armUs, r6) := if doSig then r5.nextRange 80 240 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    (.getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart, r7)
  else if bucket < 9980 then
    let (len, r3) := r2.nextRange 4194304 MAX_READ_BYTES.toNat
    let (armUs, r4) := r3.nextRange 80 280
    let (saRestart, r5) := r4.chance 1 2
    (.getrandom (UInt32.ofNat len) flags (UInt32.ofNat armUs) saRestart, r5)
  else
    let (sub, r3) := r2.nextNat 4
    let (lenU32, r4) := match sub with
      | 0 => ((0x02000000 : UInt32), r3)
      | 1 => ((0xFFFFFFFF : UInt32), r3)
      | _ =>
        let (extra, r4') := r3.nextRange 1 (UInt32.size - 1 - MAX_READ_BYTES.toNat)
        (MAX_READ_BYTES + UInt32.ofNat extra, r4')
    let (doSig, r5) := r4.chance 1 3
    let (armUs, r6) := if doSig then r5.nextRange 80 280 else (0, r5)
    let (saRestart, r7) := r6.chance 1 2
    (.getrandom lenU32 flags (UInt32.ofNat armUs) saRestart, r7)

private def genAction (rng : Rng) (lastMono? : Option Timespec) (lastReal? : Option Timespec) :
    TimeRandFuzzAction × Rng :=
  let (kind, r1) := rng.nextNat 100
  if kind < 34 then
    let (clk, r2) := genClockId r1
    (.clock_gettime clk, r2)
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
      match TimeRandErrorKind.ofErrno e with
      | .invalidArg => { h' with nanosleepInvalidArg := h'.nanosleepInvalidArg + 1 }
      | .transientOrResource =>
        { h' with
          nanosleepTransient := h'.nanosleepTransient + 1
          nanosleepAbstimeTransient := h'.nanosleepAbstimeTransient + (if abstime then 1 else 0) }
      | _ => { h' with nanosleepOtherErr := h'.nanosleepOtherErr + 1 }
    | _ => h'
  | .getrandom len flags _ _ =>
    let maskBit := if !flags.isInvalid then (1 <<< validFlagsIndex flags) else 0
    let h' := { h with
      getrandomTotal := h.getrandomTotal + 1
      getrandomValidFlagsMask := h.getrandomValidFlagsMask ||| maskBit }
    let cap := min len.toNat MAX_READ_BYTES.toNat
    match out with
    | .bytes bs =>
      let partialHit := if 0 < bs.size && bs.size < cap then 1 else 0
      let overMaxHit := if len > MAX_READ_BYTES && bs.size ≤ MAX_READ_BYTES.toNat then 1 else 0
      if bs.size == 0 then
        { h' with
          getrandomOkZero := h'.getrandomOkZero + 1
          getrandomOverMaxReadBytes := h'.getrandomOverMaxReadBytes + overMaxHit }
      else if bs.size ≤ GETRANDOM_EXACT_MAX then
        { h' with
          getrandomOkSmall := h'.getrandomOkSmall + 1
          getrandomPartial := h'.getrandomPartial + partialHit
          getrandomOverMaxReadBytes := h'.getrandomOverMaxReadBytes + overMaxHit }
      else
        { h' with
          getrandomOkLarge := h'.getrandomOkLarge + 1
          getrandomPartial := h'.getrandomPartial + partialHit
          getrandomOverMaxReadBytes := h'.getrandomOverMaxReadBytes + overMaxHit }
    | .err e =>
      match TimeRandErrorKind.ofErrno e with
      | .invalidArg => { h' with getrandomInvalidArg := h'.getrandomInvalidArg + 1 }
      | .wouldBlock => { h' with getrandomWouldBlock := h'.getrandomWouldBlock + 1 }
      | .transientOrResource => { h' with getrandomTransient := h'.getrandomTransient + 1 }
      | _ => { h' with getrandomOtherErr := h'.getrandomOtherErr + 1 }
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

private def checkTraceAgainstModel (initSt : TimeRandState) (trace : Array TimeRandFuzzAction) : IO Bool := do
  let mut st := initSt
  for act in trace do
    let out ← execAction act
    match allowedStep st act.toReq out with
    | some st' => st := st'
    | none => return false
  return true

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
        improved := true
      else
        start := start + chunk
    if !improved then
      if chunk == 1 then
        break
      chunk := max 1 (chunk / 2)
  return cur

/-- Run `--self-test-shrink` verifying that `shrinkTrace` reduces a randomly sampled multi-step failing trace to size 1. -/
def selfTestShrink (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x517cc1b727220a95)
  let mut trace : Array TimeRandFuzzAction := #[]
  for _ in List.range 12 do
    let (act, r') := genAction rng none none
    rng := r'
    trace := trace.push act
  let targetIdx := (rng.nextNat trace.size).1
  let (badTs, _) := genInvalidTimespec rng
  trace := trace.set! targetIdx (.clock_nanosleep .monotonic true badTs 0 false)
  let isSyntheticFailure (xs : Array TimeRandFuzzAction) : IO Bool :=
    return xs.any fun
      | .clock_nanosleep _ true req _ _ => !req.isValid
      | _ => false
  let shrunk ← shrinkTrace isSyntheticFailure trace
  unless shrunk.size == 1 && (← isSyntheticFailure shrunk) do
    throw (IO.userError s!"SELF_TEST_SHRINK failed: shrunk size={shrunk.size}")
  IO.println s!"SELF_TEST_SHRINK: PASS original={trace.size} shrunk={shrunk.size}"

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
      if !allowNoTimens && hits.envTimensExpected != 7 then
        throw (IO.userError s!"fuzz coverage gap in CLONE_NEWTIME sub-episodes (expected 7, got {hits.envTimensExpected}): {repr hits}")
      if hits.envTimensExpected > 0 && hits.envTimensOk != hits.envTimensExpected then
        throw (IO.userError s!"fuzz coverage gap in CLONE_NEWTIME sub-episodes (expected {hits.envTimensExpected}): {repr hits}")
  if steps ≥ 100000 then
    if hits.nanosleepTransient ≤ hits.nanosleepAbstimeTransient || hits.nanosleepAbstimeTransient == 0 then
      throw (IO.userError s!"fuzz coverage gap in clock_nanosleep EINTR (relative-only and abstime required): {repr hits}")
    if hits.getrandomPartial == 0 || hits.getrandomOverMaxReadBytes == 0 then
      throw (IO.userError s!"fuzz coverage gap in getrandom partial read / MAX_READ_BYTES clamp: {repr hits}")

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
    let rc ← installSeccompErrnoRaw eno mask
    if rc != 0 then
      throw (IO.userError s!"installSeccompErrnoRaw({eno}, {mask}) failed with errno {rc}")
    seccompInstalled := true
  let mut lastMono? : Option Timespec := none
  let mut lastReal? : Option Timespec := none
  let mut trace : Array TimeRandFuzzAction := Array.mkEmpty totalSteps
  let mut sleepValidCount : Nat := 0
  let mut sleepInvalidCount : Nat := 0
  let mut randValidCount : Nat := 0
  let mut randInvalidCount : Nat := 0
  for stepIdx in List.range totalSteps do
    if !seccompInstalled && stepIdx == delaySteps then
      if delaySteps ≥ 100 && (st.monoLowerBoundNs == 0 || !st.crngReady) then
        throw (IO.userError s!"mid-episode seccomp child warmup ({delaySteps} steps) did not advance state: mono={st.monoLowerBoundNs} crngReady={st.crngReady}")
      let rc ← installSeccompErrnoRaw eno mask
      if rc != 0 then
        throw (IO.userError s!"mid-episode installSeccompErrnoRaw({eno}, {mask}) failed with errno {rc}")
      st := st.withOuterSeccomp
      seccompInstalled := true
    let (act, r') := genAction rng lastMono? lastReal?
    rng := r'
    trace := trace.push act
    let out ← execAction act
    hits := recordHit hits act out
    let isBlocked := seccompInstalled && match act with
      | .clock_gettime _ => (mask &&& 1) != 0
      | .clock_nanosleep _ _ _ _ _ => (mask &&& 2) != 0
      | .getrandom _ _ _ _ => (mask &&& 4) != 0
    if seccompInstalled then
      match act with
      | .clock_gettime _ => pure ()
      | .clock_nanosleep _ _ req _ _ =>
        if req.isValid then sleepValidCount := sleepValidCount + 1 else sleepInvalidCount := sleepInvalidCount + 1
      | .getrandom _ flags _ _ =>
        if !flags.isInvalid then randValidCount := randValidCount + 1 else randInvalidCount := randInvalidCount + 1
    if isBlocked && out != .err eno then
      throw (IO.userError s!"seccomp child step {stepIdx}: expected errno {eno}, got {repr out} for {repr act.toReq}")
    if !isBlocked then
      match allowedStep { st with ambientSeccomp := false } act.toReq out with
      | some _ => pure ()
      | none =>
        throw (IO.userError s!"seccomp child step {stepIdx}: unblocked syscall rejected by allowedStepCore: req={repr act.toReq} out={repr out}")
    match act, out with
    | .clock_gettime .monotonic, .timespec ts => lastMono? := some ts
    | .clock_gettime .realtime, .timespec ts => lastReal? := some ts
    | _, _ => pure ()
    match allowedStep st act.toReq out with
    | some st' => st := st'
    | none =>
      if delaySteps == 0 then
        let shrunk ← shrinkTrace (fun cand => do return !(← checkTraceAgainstModel TimeRandState.initial.withOuterSeccomp cand)) trace
        throw (IO.userError s!"seccomp child model violation: shrunk={repr shrunk}")
      else
        throw (IO.userError s!"mid-episode seccomp child model violation at step {stepIdx}: req={repr act.toReq} out={repr out} st={repr st}")
  if hits.gettimeTotal == 0 || sleepValidCount == 0 || sleepInvalidCount == 0 ||
      randValidCount == 0 || randInvalidCount == 0 then
    throw (IO.userError s!"seccomp child coverage gap (steps={steps}, mask={mask}): gettime={hits.gettimeTotal} sleep=({sleepValidCount},{sleepInvalidCount}) rand=({randValidCount},{randInvalidCount})")
  return { steps := totalSteps, episodes := 1, elapsedMs := 1, hits := hits }

private def runEnvSubEpisodesFn (seedVal : UInt64) (allowNoTimens : Bool := false) : IO (Nat × Nat × Nat) := do
  let exe ← IO.appPath
  let mut seccompOk : Nat := 0
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
  seccompOk := seccompOk + 1
  let mut timensOk : Nat := 0
  let mut timensExpected : Nat := 0
  let pyScript :=
    "import ctypes, os, sys; " ++
    "ms, mns, bs, bns = sys.argv[1:5]; exe = sys.argv[5]; args = sys.argv[5:]; " ++
    "libc = ctypes.CDLL(None, use_errno=True); " ++
    "libc.unshare.argtypes = [ctypes.c_int]; " ++
    "libc.unshare.restype = ctypes.c_int; " ++
    "uid, gid = os.getuid(), os.getgid(); " ++
    "rc = libc.unshare(0x10000000 | 0x00000080); " ++
    "assert rc == 0, f'unshare errno={ctypes.get_errno()}'; " ++
    "open('/proc/self/setgroups', 'wb').write(b'deny'); " ++
    "open('/proc/self/uid_map', 'wb').write(f'0 {uid} 1\\n'.encode()); " ++
    "open('/proc/self/gid_map', 'wb').write(f'0 {gid} 1\\n'.encode()); " ++
    "open('/proc/self/timens_offsets', 'wb').write(f'monotonic {ms} {mns}\\nboottime {bs} {bns}\\n'.encode()); " ++
    "pid = os.fork(); " ++
    "os.execv(exe, args) if pid == 0 else None; " ++
    "_, st = os.waitpid(pid, 0); " ++
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
    let modNegMono := if curMonoSec > 2 then toString (-(min 60 (curMonoSec / 2))) else "0"
    let modNegBoot := if curMonoSec > 2 then toString (-(min 30 (curMonoSec / 2))) else "0"
    let nearZeroMono := if curMonoSec ≥ 2 then toString (-(curMonoSec - 1)) else "0"
    let nearZeroBoot := if curMonoSec ≥ 2 then "-1" else "0"
    let fracNegMono := if curMonoSec ≥ 3 then toString (-(curMonoSec - 1)) else "0"
    let fracNegBoot := if curMonoSec ≥ 3 then "-1" else "0"
    let highMono := if curMonoSec < 4611000000 then toString (4611000000 - curMonoSec) else "0"
    let cappedBoot := if curMonoSec < 4611000000 then toString (min 4000000000 (4611000000 - curMonoSec)) else "0"
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
      if out.exitCode != 0 then
        throw (IO.userError s!"CLONE_NEWTIME sub-episode (mono={monoSec}s+{monoNsec}ns, boot={bootSec}s+{bootNsec}ns) failed exit={out.exitCode}: {out.stderr}")
      timensOk := timensOk + 1
  return (seccompOk, timensOk, timensExpected)

/-- Run the stateful `TimeRand` real-syscall fuzz loop for `steps` calls starting from `seedVal`. -/
def fuzzTimeRand (steps : Nat) (seedVal : UInt64)
    (runEnvSubEpisodes : Bool := false) (allowNoTimens : Bool := false) : IO TimeRandFuzzReport := do
  let t0 ← IO.monoMsNow
  let mut rng := Rng.seed seedVal
  let mut done := 0
  let mut episodes := 0
  let mut hits : TimeRandHitCounters := {}
  while done < steps do
    episodes := episodes + 1
    let (epTarget, rEp) := rng.nextRange 8 32
    rng := rEp
    let epLen := min epTarget (steps - done)
    let mut st := TimeRandState.initial
    let mut epTrace : Array TimeRandFuzzAction := Array.mkEmpty epLen
    let mut lastMono? : Option Timespec := none
    let mut lastReal? : Option Timespec := none
    for _ in List.range epLen do
      let (act, rAct) := genAction rng lastMono? lastReal?
      rng := rAct
      epTrace := epTrace.push act
      let out ← execAction act
      hits := recordHit hits act out
      match act, out with
      | .clock_gettime .monotonic, .timespec ts => lastMono? := some ts
      | .clock_gettime .realtime, .timespec ts => lastReal? := some ts
      | _, _ => pure ()
      match allowedStep st act.toReq out with
      | some st' => st := st'
      | none =>
        let shrunk ← shrinkTrace (fun cand => do return !(← checkTraceAgainstModel TimeRandState.initial cand)) epTrace
        throw (IO.userError
          s!"TimeRand fuzz model violation at step {done} (seed={seedVal}, shrunk={repr shrunk}): req={repr act.toReq} out={repr out} state={repr st}")
      done := done + 1
  if steps ≥ 1000 && runEnvSubEpisodes then
    let (secOk, timOk, timExp) ← runEnvSubEpisodesFn seedVal allowNoTimens
    hits := { hits with envSeccompOk := secOk, envTimensOk := timOk, envTimensExpected := timExp }
  assertCoverage steps hits (steps ≥ 1000 && runEnvSubEpisodes) allowNoTimens
  let t1 ← IO.monoMsNow
  let elapsedMs := max 1 (t1 - t0)
  IO.println "SYSCALL_OUTCOME_HITS:"
  IO.println s!"  clock_gettime: total={hits.gettimeTotal} realtime_ok={hits.gettimeRealtimeOk} monotonic_ok={hits.gettimeMonotonicOk} err={hits.gettimeErr}"
  IO.println s!"  clock_nanosleep: total={hits.nanosleepTotal} ok={hits.nanosleepOk} relMonoOk={hits.nanosleepRelMonoOk} relRealOk={hits.nanosleepRelRealOk} absMonoOk={hits.nanosleepAbsMonoOk} absRealOk={hits.nanosleepAbsRealOk} invalidArg={hits.nanosleepInvalidArg} transientOrResource={hits.nanosleepTransient} abstimeTransient={hits.nanosleepAbstimeTransient} other_err={hits.nanosleepOtherErr}"
  IO.println s!"  getrandom: total={hits.getrandomTotal} ok_zero={hits.getrandomOkZero} ok_small={hits.getrandomOkSmall} ok_large={hits.getrandomOkLarge} partial={hits.getrandomPartial} overMax={hits.getrandomOverMaxReadBytes} invalidArg={hits.getrandomInvalidArg} wouldBlock={hits.getrandomWouldBlock} transient={hits.getrandomTransient} other_err={hits.getrandomOtherErr} validFlagsMask={hits.getrandomValidFlagsMask}"
  IO.println s!"  env_subepisodes: seccomp_ok={hits.envSeccompOk} timens_ok={hits.envTimensOk}/{hits.envTimensExpected}"
  let rate := (steps * 1000) / elapsedMs
  IO.println s!"FUZZ_SUMMARY suite=timerand steps={steps} episodes={episodes} elapsed_ms={elapsedMs} syscalls_per_sec={rate}"
  return { steps := steps, episodes := episodes, elapsedMs := elapsedMs, hits := hits }

end LeanSwe.LinuxSyscall.Fuzz

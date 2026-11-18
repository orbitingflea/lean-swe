import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model

namespace LeanSwe.LinuxSyscall.TimeRand

open Core (NondetTest ErrorObligation ErrorJustification ErrorTestMode AssumptionObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Errno.isTransientOsErrno` excludes `EFAULT` and matches `{EINTR, EIO, ENOMEM, ENFILE, EMFILE, ENOSPC}`, and `TimeRandErrorKind.ofErrno` classifies all core `TimeRand` errnos into their exact semantic buckets. -/
def test_timerand_errno_classificationAndTransient
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → TimeRandErrorKind := TimeRandErrorKind.ofErrno) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  NondetTest.assert (classify Errno.EINVAL = .invalidArg)
  NondetTest.assert (classify Errno.EOPNOTSUPP = .invalidArg)
  NondetTest.assert (classify Errno.ENOSYS = .invalidArg)
  NondetTest.assert (classify Errno.ERANGE = .invalidArg)
  NondetTest.assert (classify Errno.EAGAIN = .wouldBlock)
  NondetTest.assert (classify Errno.EPERM = .permissionDenied)
  NondetTest.assert (classify Errno.EACCES = .permissionDenied)
  NondetTest.assert (classify Errno.EINTR = .transientOrResource)
  NondetTest.assert (classify Errno.EIO = .transientOrResource)
  NondetTest.assert (classify Errno.ENOMEM = .transientOrResource)

/-- `ClockId.toRaw` and `GrndFlags.toBits` are injective, and `GrndFlags.isInvalid` rejects iff `random && insecure` (allowing `nonblock && insecure` and `nonblock && random` per Linux `7.1+`). -/
def test_timerand_encoders_injectiveAndGrndInvalid
    {runner} [NondetTest runner]
    (encClock : ClockId → UInt32 := ClockId.toRaw)
    (encGrnd : GrndFlags → UInt32 := GrndFlags.toBits)
    (isBadGrnd : GrndFlags → Bool := GrndFlags.isInvalid) : runner Unit := do
  let c1 ← nondet ClockId
  let c2 ← nondet ClockId
  let g1 ← nondet GrndFlags
  let g2 ← nondet GrndFlags
  NondetTest.assert ((encClock c1 == encClock c2) = (c1 == c2))
  NondetTest.assert (encClock .realtime = 0 ∧ encClock .monotonic = 1)
  NondetTest.assert ((encGrnd g1 == encGrnd g2) = (g1 == g2))
  NondetTest.assert (isBadGrnd g1 = (g1.random && g1.insecure))
  NondetTest.assert (isBadGrnd { nonblock := true, insecure := true } = false)
  NondetTest.assert (isBadGrnd { nonblock := true, random := true } = false)
  NondetTest.assert (isBadGrnd { random := true, insecure := true } = true)

/-- `Timespec.isValid` enforces `0 ≤ sec` and `nsec < 10^9`, and `Timespec.ofNanosNat?` / `Timespec.ofEpochNanos?` round-trip all representable positive and pre-1970 nanosecond timestamps while returning `none` on `Int64` overflow. -/
def test_timerand_timespec_validAndNanosRoundTrip
    {runner} [NondetTest runner]
    (isValidFn : Timespec → Bool := Timespec.isValid)
    (ofNatFn : Nat → Option Timespec := Timespec.ofNanosNat?)
    (ofEpochFn : Int → Option Timespec := Timespec.ofEpochNanos?) : runner Unit := do
  let ts ← nondet Timespec
  let ns ← nondet Nat
  let epochNs ← nondet Int
  NondetTest.assert (isValidFn ts = (decide (0 ≤ ts.sec.toInt) && decide (ts.nsec.toNat < NSEC_PER_SEC)))
  NondetTest.assert (if ns ≤ MAX_TIMESPEC_NANOS then
    ∃ out, ofNatFn ns = some out ∧ isValidFn out = true ∧ out.toNanosNat = ns
  else
    ofNatFn ns = none)
  let secInt := epochNs.ediv (Int.ofNat NSEC_PER_SEC)
  NondetTest.assert (if MIN_TIMESPEC_SEC_INT ≤ secInt ∧ secInt ≤ Int.ofNat MAX_TIMESPEC_SEC then
    ∃ out, ofEpochFn epochNs = some out ∧ out.hasValidNsec = true ∧ out.toEpochNanos = epochNs
  else
    ofEpochFn epochNs = none)

/-- `mkOps` (`Internal.mkTimeRandOpsM`) faithfully encodes `ClockId.toRaw`, `abstime` (`0` vs `1`), `Timespec` fields, and `GrndFlags.toBits`, reconstructing `Timespec` on `clock_gettime` `.ok` and propagating every `Errno` unchanged. -/
def test_timerand_mkTimeRandOps_encodesAndDelegates
    {runner} [NondetTest runner]
    (mkOps : PosixTimeRandOpsM Id → TimeRandOpsM Id) :
    runner Unit := do
  let rawGet ← nondet (UInt32 → Except Errno (Int64 × UInt32))
  let rawSleep ← nondet (UInt32 → UInt8 → Int64 → UInt32 → Except Errno Unit)
  let rawRand ← nondet (UInt32 → UInt32 → Except Errno ByteArray)
  let clk ← nondet ClockId
  let abstime ← nondet Bool
  let req ← nondet Timespec
  let len ← nondet UInt32
  let flags ← nondet GrndFlags
  let raw : PosixTimeRandOpsM Id :=
    { clock_gettime := rawGet
      clock_nanosleep := rawSleep
      getrandom := rawRand }
  let ops := mkOps raw
  let expectedGet : Except Errno Timespec :=
    match rawGet clk.toRaw with
    | .ok (sec, nsec) => .ok { sec, nsec }
    | .error e => .error e
  NondetTest.assert (ops.clock_gettime clk = expectedGet)
  NondetTest.assert (ops.clock_nanosleep clk abstime req =
    rawSleep clk.toRaw (if abstime then 1 else 0) req.sec req.nsec)
  NondetTest.assert (ops.getrandom len flags = rawRand len flags.toBits)

/-- `clock_nanosleep` rejects every invalid `Timespec` (`sec < 0` or `nsec ≥ 1_000_000_000`) with `Errno.EINVAL` without mutating state across both `ClockId`s and both `abstime` modes (including `TIMER_ABSTIME` on `CLOCK_REALTIME`). -/
def test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes
    {S : Type} {runner} [NondetTest runner] (ops : TimeRandOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let clk ← nondet ClockId
  let abstime ← nondet Bool
  let badReq ← nondet Timespec
  assume (badReq.isValid = false)
  NondetTest.assert ((ops.clock_nanosleep clk abstime badReq).run s₀ = (.error Errno.EINVAL, s₀))

/-- Multi-call `CLOCK_MONOTONIC` sequences over `TimeRandOpsM (StateM TimeRandState)` preserve non-decreasing readings across back-to-back `clock_gettime`, relative `clock_nanosleep`, `TIMER_ABSTIME` `clock_nanosleep`, and `CLOCK_REALTIME` sleeps. -/
def test_timerand_ops_monotonicMultiCallAndNanosleepBounds
    {runner} [NondetTest runner]
    (ops : TimeRandOpsM (StateM TimeRandState)) : runner Unit := do
  let s₀ ← nondet TimeRandState
  let relTs ← nondet Timespec
  let absTs ← nondet Timespec
  assume (relTs.isValid = true)
  assume (absTs.isValid = true)
  assume (s₀.monoLowerBoundNs + relTs.toNanosNat + absTs.toNanosNat ≤ MAX_TIMESPEC_NANOS)
  let (r0, s₁) := (ops.clock_gettime .monotonic).run s₀
  let (r1, s₂) := (ops.clock_gettime .monotonic).run s₁
  match r0, r1 with
  | .ok t0, .ok t1 =>
    NondetTest.assert (t0.isValid = true ∧ t1.isValid = true)
    NondetTest.assert (s₀.monoLowerBoundNs ≤ t0.toNanosNat ∧ t0.toNanosNat ≤ t1.toNanosNat)
    let (rsRel, s₃) := (ops.clock_nanosleep .monotonic false relTs).run s₂
    NondetTest.assert (rsRel = .ok ())
    let (r2, s₄) := (ops.clock_gettime .monotonic).run s₃
    match r2 with
    | .error _ => NondetTest.assert False
    | .ok t2 =>
      NondetTest.assert (t2.isValid = true ∧ t1.toNanosNat + relTs.toNanosNat ≤ t2.toNanosNat)
      let (rsAbs, s₅) := (ops.clock_nanosleep .monotonic true absTs).run s₄
      NondetTest.assert (rsAbs = .ok ())
      let (r3, s₆) := (ops.clock_gettime .monotonic).run s₅
      match r3 with
      | .error _ => NondetTest.assert False
      | .ok t3 =>
        NondetTest.assert (t3.isValid = true ∧ max t2.toNanosNat absTs.toNanosNat ≤ t3.toNanosNat)
        let (rsReal, s₇) := (ops.clock_nanosleep .realtime false relTs).run s₆
        NondetTest.assert (rsReal = .ok ())
        let (r4, _) := (ops.clock_gettime .monotonic).run s₇
        NondetTest.assert (∃ t4, r4 = .ok t4 ∧ t3.toNanosNat ≤ t4.toNanosNat)
  | _, _ => NondetTest.assert False

/-- `getrandom` over `TimeRandOpsM (StateM TimeRandState)` rejects `random && insecure` with `EINVAL` (even when `len = 0`), enforces CRNG readiness (`EAGAIN` on `nonblock && !insecure` before seeding, immediate success on `insecure`), transitions `crngReady` permanently on non-`insecure` success, returns exact byte counts, and produces distinct 16-byte draws. -/
def test_timerand_ops_getrandom_flagsLengthsAndCrngState
    {runner} [NondetTest runner]
    (ops : TimeRandOpsM (StateM TimeRandState)) : runner Unit := do
  let s₀ ← nondet TimeRandState
  let len ← nondet UInt32
  let nb ← nondet Bool
  NondetTest.assert ((ops.getrandom len { nonblock := nb, random := true, insecure := true }).run s₀ =
    (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.getrandom 0 { nonblock := nb, random := true, insecure := true }).run s₀ =
    (.error Errno.EINVAL, s₀))
  let sUnseeded : TimeRandState := { s₀ with crngReady := false }
  NondetTest.assert ((ops.getrandom 16 { nonblock := true, insecure := false }).run sUnseeded =
    (.error Errno.EAGAIN, sUnseeded))
  let (rInsec, sAfterInsec) := (ops.getrandom 16 { nonblock := true, insecure := true }).run sUnseeded
  NondetTest.assert ((∃ bs, rInsec = .ok bs ∧ bs.size = 16) ∧ sAfterInsec.crngReady = false)
  let (rZero, sSeeded) := (ops.getrandom 0 {}).run sUnseeded
  NondetTest.assert (rZero = .ok ByteArray.empty ∧ sSeeded.crngReady = true)
  let (rNb1, sDraw1) := (ops.getrandom 16 { nonblock := true }).run sSeeded
  let (rNb2, sDraw2) := (ops.getrandom 16 { nonblock := true }).run sDraw1
  match rNb1, rNb2 with
  | .ok b1, .ok b2 =>
    NondetTest.assert (b1.size = 16 ∧ b2.size = 16 ∧ b1 ≠ b2 ∧ sDraw2.crngReady = true)
  | _, _ => NondetTest.assert False
  let (rArb, _) := (ops.getrandom len { insecure := true }).run s₀
  NondetTest.assert (∃ bs, rArb = .ok bs ∧ bs.size = min len.toNat MAX_READ_BYTES.toNat ∧
    validGetrandomResultLen len bs.size = true)

/-- `allowedStep` enforces all Linux `7.1+` `TimeRand` acceptance and rejection invariants across `clock_gettime`, `clock_nanosleep`, and `getrandom` (`len = 0`, `len ≤ 256` exact read, `len > 256` partial read clamped to `MAX_READ_BYTES`, `EINTR`, `EAGAIN`, and `EINVAL`). -/
def test_timerand_allowedStep_exactKernelSemantics
    {runner} [NondetTest runner]
    (step : TimeRandState → TimeRandReq → TimeRandOutcome → Option TimeRandState := allowedStep) :
    runner Unit := do
  let sRaw ← nondet TimeRandState
  let s : TimeRandState := { sRaw with ambientSeccomp := false }
  let negReal : Timespec := { sec := -1, nsec := 999999999 }
  let badNsec : Timespec := { sec := 0, nsec := 1000000000 }
  NondetTest.assert (step s (.clock_gettime .realtime) (.timespec negReal) = some s)
  NondetTest.assert (step s (.clock_gettime .realtime) (.timespec badNsec) = none)
  NondetTest.assert (step s (.clock_gettime .monotonic) (.timespec negReal) = none)
  NondetTest.assert (step s (.clock_gettime .monotonic) (.timespec badNsec) = none)
  let sPos : TimeRandState := { s with monoLowerBoundNs := 5000 }
  NondetTest.assert (step sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 4999 }) = none)
  NondetTest.assert (step sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 5000 }) =
    some { sPos with monoLowerBoundNs := 5000 })
  NondetTest.assert (step s (.clock_nanosleep .realtime true negReal) .unit = none)
  NondetTest.assert (step s (.clock_nanosleep .realtime true negReal) (.err Errno.EINVAL) = some s)
  NondetTest.assert (step s (.clock_nanosleep .monotonic false badNsec) .unit = none)
  NondetTest.assert (step s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINTR) = none)
  NondetTest.assert (step s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINVAL) = some s)
  let reqValid : Timespec := { sec := 0, nsec := 2000 }
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic false reqValid) .unit =
    some { sPos with monoLowerBoundNs := 7000 })
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic true reqValid) .unit =
    some { sPos with monoLowerBoundNs := 5000 })
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic true { sec := 0, nsec := 9000 }) .unit =
    some { sPos with monoLowerBoundNs := 9000 })
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINTR) = some sPos)
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINVAL) = none)
  NondetTest.assert (step s (.getrandom 0 { random := true, insecure := true }) (.bytes ByteArray.empty) = none)
  NondetTest.assert (step s (.getrandom 0 { random := true, insecure := true }) (.err Errno.EINVAL) = some s)
  NondetTest.assert ((step s (.getrandom 0 {}) (.bytes ByteArray.empty)).isSome = true)
  NondetTest.assert (step s (.getrandom 0 {}) (.bytes (ByteArray.mk #[1])) = none)
  NondetTest.assert (step s (.getrandom 16 {}) (.bytes (ByteArray.mk #[1, 2, 3])) = none)
  NondetTest.assert ((step s (.getrandom 300 {}) (.bytes (ByteArray.mk #[1, 2, 3]))).isSome = true)
  NondetTest.assert (step s (.getrandom 300 {}) (.bytes ByteArray.empty) = none)
  let sUnready : TimeRandState := { s with crngReady := false }
  let sReady : TimeRandState := { s with crngReady := true }
  NondetTest.assert (step sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = some sUnready)
  NondetTest.assert (step sUnready (.getrandom 16 { nonblock := true, insecure := true }) (.err Errno.EAGAIN) = none)
  NondetTest.assert (step sUnready (.getrandom 16 { nonblock := false }) (.err Errno.EAGAIN) = none)
  NondetTest.assert (step sReady (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = none)
  NondetTest.assert (step s (.getrandom 16 {}) (.err Errno.EMFILE) = none)
  NondetTest.assert (step s (.getrandom 16 {}) (.err Errno.ENFILE) = none)
  NondetTest.assert (step s (.clock_gettime .monotonic) (.err Errno.EMFILE) = none)
  NondetTest.assert (step s (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOSPC) = none)
  let sZero : TimeRandState := { s with monoLowerBoundNs := 0, realtimeNs := 0 }
  NondetTest.assert (step sZero (.clock_gettime .realtime) (.err Errno.EINTR) = none)
  NondetTest.assert (step sZero (.clock_gettime .realtime) (.err Errno.ENOMEM) = none)
  NondetTest.assert (step sZero (.clock_gettime .realtime) (.err Errno.EIO) = none)
  NondetTest.assert (step sZero (.clock_gettime .monotonic) (.err Errno.EINTR) = none)
  NondetTest.assert (step sZero (.clock_gettime .monotonic) (.err Errno.ENOMEM) = none)
  NondetTest.assert (step sZero (.clock_gettime .monotonic) (.err Errno.EIO) = none)
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOMEM) = none)
  NondetTest.assert (step sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EIO) = none)
  NondetTest.assert (step sUnready (.getrandom 16 {}) (.err Errno.EINTR) = some sUnready)
  NondetTest.assert (step sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EINTR) = none)
  NondetTest.assert (step sUnready (.getrandom 16 { insecure := true }) (.err Errno.EINTR) = none)
  NondetTest.assert (step sReady (.getrandom 16 {}) (.err Errno.EINTR) = none)
  NondetTest.assert (step sUnready (.getrandom 16 {}) (.err Errno.ENOMEM) = none)
  NondetTest.assert (step sUnready (.getrandom 16 {}) (.err Errno.EIO) = none)

/-- Under `TimeRandState.withOuterSeccomp`, `allowedStep` permits `SECCOMP_RET_ERRNO` codes `1..4095` (excluding `EFAULT`) across all 3 syscalls while keeping `EFAULT`, out-of-range codes, non-error invariants, and non-seccomp strictness intact. -/
def test_timerand_allowedStep_withOuterSeccomp
    {runner} [NondetTest runner]
    (step : TimeRandState → TimeRandReq → TimeRandOutcome → Option TimeRandState := allowedStep) :
    runner Unit := do
  let sBase ← nondet TimeRandState
  let sNoSec : TimeRandState := { sBase with ambientSeccomp := false }
  let sSec := sNoSec.withOuterSeccomp
  let reqBadTs : Timespec := { sec := -1, nsec := 0 }
  let reqValidTs : Timespec := { sec := 0, nsec := 1000 }
  let sPosSec : TimeRandState := { sSec with monoLowerBoundNs := 5000 }
  NondetTest.assert (TimeRandState.initial.ambientSeccomp = false)
  NondetTest.assert (sSec.ambientSeccomp = true)
  NondetTest.assert (step sNoSec (.clock_gettime .monotonic) (.err Errno.EPERM) = none)
  NondetTest.assert (step sSec (.clock_gettime .monotonic) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.clock_gettime .realtime) (.err Errno.EACCES) = some sSec)
  NondetTest.assert (step sSec (.clock_nanosleep .monotonic false reqBadTs) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.clock_nanosleep .monotonic false reqValidTs) (.err Errno.ENOSYS) = some sSec)
  NondetTest.assert (step sSec (.getrandom 16 { random := true, insecure := true }) (.err Errno.EAGAIN) = some sSec)
  NondetTest.assert (step sSec (.getrandom 16 {}) (.err Errno.EINVAL) = some sSec)
  NondetTest.assert (step sSec (.clock_gettime .monotonic) (.err Errno.EFAULT) = none)
  NondetTest.assert (step sSec (.clock_nanosleep .monotonic false reqValidTs) (.err Errno.EFAULT) = none)
  NondetTest.assert (step sSec (.getrandom 16 {}) (.err Errno.EFAULT) = none)
  NondetTest.assert (step sSec (.getrandom 16 {}) (.err 0) = none)
  NondetTest.assert (step sSec (.getrandom 16 {}) (.err 4096) = none)
  NondetTest.assert (step sPosSec (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 4999 }) = none)

/-- Every step executed by `modelOps` from any `TimeRandState` and any `TimeRand` request produces an outcome and next state accepted by `allowedStep`. -/
def test_timerand_modelOps_soundAgainstAllowedStep
    {runner} [NondetTest runner]
    (ops : TimeRandOpsM (StateM TimeRandState))
    (step : TimeRandState → TimeRandReq → TimeRandOutcome → Option TimeRandState := allowedStep) :
    runner Unit := do
  let s ← nondet TimeRandState
  let clk ← nondet ClockId
  let abstime ← nondet Bool
  let req ← nondet Timespec
  let len ← nondet UInt32
  let flags ← nondet GrndFlags
  let (rGet, sGet) := (ops.clock_gettime clk).run s
  NondetTest.assert (step s (.clock_gettime clk) (outcomeOfTimespec rGet) = some sGet)
  let (rSleep, sSleep) := (ops.clock_nanosleep clk abstime req).run s
  NondetTest.assert (step s (.clock_nanosleep clk abstime req) (outcomeOfUnit rSleep) = some sSleep)
  let (rRand, sRand) := (ops.getrandom len flags).run s
  NondetTest.assert (step s (.getrandom len flags) (outcomeOfBytes rRand) = some sRand)

/-- Thin C-wrapper boundary assumptions for `LeanSwe.LinuxSyscall.TimeRand` (`c/timerand_shim.c`), verified at runtime against the host Linux kernel with nonce logging. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockGettime_realtimeAndMonotonic"
      subject := "LeanSwe.LinuxSyscall.TimeRand.clock_gettime"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_clockNanosleep_relativeAndAbstime"
      subject := "LeanSwe.LinuxSyscall.TimeRand.clock_nanosleep"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.TimeRand.assume_timerand_getrandom_exactAndFlags"
      subject := "LeanSwe.LinuxSyscall.TimeRand.getrandom"
      formalPred? := none } ]

/-- Complete `(request × TimeRandErrorKind)` error-coverage matrix for all 3 curated `TimeRand` syscalls (`12` obligations), linked to real Linux kernel tests and mocked/`strace` fault-injection tests in `RuntimeTests.lean`. -/
def errorCoverage : List (ErrorObligation TimeRandErrorKind) :=
  [ { request := "LeanSwe.LinuxSyscall.TimeRand.clock_gettime", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_gettime_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_gettime", errorKind := .wouldBlock, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_gettime_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_gettime", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_gettime_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_gettime", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_gettime_mocked" .mocked }

  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_nanosleep", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_nanosleep", errorKind := .wouldBlock, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_nanosleep", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.clock_nanosleep", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_clock_nanosleep_transient" .mocked }

  , { request := "LeanSwe.LinuxSyscall.TimeRand.getrandom", errorKind := .invalidArg, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_invalidArg" .real }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.getrandom", errorKind := .wouldBlock, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_wouldBlock" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.getrandom", errorKind := .permissionDenied, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.TimeRand.getrandom", errorKind := .transientOrResource, justification := .tested "LeanSwe.LinuxSyscall.TimeRand.RuntimeTests.err_getrandom_transient" .mocked } ]

end LeanSwe.LinuxSyscall.TimeRand

import LeanSwe.LinuxSyscall.TimeRand.Proofs.OpsProofs

namespace LeanSwe.LinuxSyscall.TimeRand.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

private theorem allowedStep_clock_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let negReal : Timespec := { sec := -1, nsec := 999999999 }
    let badNsec : Timespec := { sec := 0, nsec := 1000000000 }
    let sPos : TimeRandState := { s with monoLowerBoundNs := 5000 }
    let sZero : TimeRandState := { s with monoLowerBoundNs := 0, realtimeNs := 0 }
    allowedStep s (.clock_gettime .realtime) (.timespec negReal) = some s ∧
    allowedStep s (.clock_gettime .realtime) (.timespec badNsec) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.timespec negReal) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.timespec badNsec) = none ∧
    allowedStep sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 4999 }) = none ∧
    allowedStep sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 5000 }) =
      some { sPos with monoLowerBoundNs := 5000 } ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.EINTR) = none ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.ENOMEM) = none ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.EIO) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.EINTR) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.ENOMEM) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.EIO) = none := by
  have hzero : decide (-9223372036854775808 ≤ Int.ediv 0 1000000000 ∧ Int.ediv 0 1000000000 ≤ 9223372036854775807) = true := by decide
  simp [allowedStep, allowedStepCore, hs, Timespec.hasValidNsec, Timespec.isValid,
    Timespec.toNanosNat, MAX_TIMESPEC_SEC, MAX_TIMESPEC_NANOS,
    NSEC_PER_SEC] <;>
  exact hzero

private theorem allowedStep_sleep_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let negReal : Timespec := { sec := -1, nsec := 999999999 }
    let badNsec : Timespec := { sec := 0, nsec := 1000000000 }
    let sPos : TimeRandState := { s with monoLowerBoundNs := 5000 }
    let reqValid : Timespec := { sec := 0, nsec := 2000 }
    allowedStep s (.clock_nanosleep .realtime true negReal) .unit = none ∧
    allowedStep s (.clock_nanosleep .realtime true negReal) (.err Errno.EINVAL) = some s ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) .unit = none ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINTR) = none ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINVAL) = some s ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) .unit =
      some { sPos with monoLowerBoundNs := 7000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic true reqValid) .unit =
      some { sPos with monoLowerBoundNs := 5000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic true { sec := 0, nsec := 9000 }) .unit =
      some { sPos with monoLowerBoundNs := 9000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINTR) = some sPos ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINVAL) = none ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOMEM) = none ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EIO) = none := by
  simp [allowedStep, allowedStepCore, hs, Timespec.isValid, Timespec.toNanosNat,
    MAX_TIMESPEC_NANOS, MAX_TIMESPEC_SEC, NSEC_PER_SEC,
    Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO]

private theorem allowedStep_rand_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let sUnready : TimeRandState := { s with crngReady := false }
    let sReady : TimeRandState := { s with crngReady := true }
    let reqValid : Timespec := { sec := 0, nsec := 2000 }
    allowedStep s (.getrandom 0 { random := true, insecure := true }) (.bytes ByteArray.empty) = none ∧
    allowedStep s (.getrandom 0 { random := true, insecure := true }) (.err Errno.EINVAL) = some s ∧
    (allowedStep s (.getrandom 0 {}) (.bytes ByteArray.empty)).isSome = true ∧
    allowedStep s (.getrandom 0 {}) (.bytes (ByteArray.mk #[1])) = none ∧
    allowedStep s (.getrandom 16 {}) (.bytes (ByteArray.mk #[1, 2, 3])) = none ∧
    (allowedStep s (.getrandom 300 {}) (.bytes (ByteArray.mk #[1, 2, 3]))).isSome = true ∧
    allowedStep s (.getrandom 300 {}) (.bytes ByteArray.empty) = none ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = some sUnready ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true, insecure := true }) (.err Errno.EAGAIN) = none ∧
    allowedStep sUnready (.getrandom 16 { nonblock := false }) (.err Errno.EAGAIN) = none ∧
    allowedStep sReady (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = none ∧
    allowedStep s (.getrandom 16 {}) (.err Errno.EMFILE) = none ∧
    allowedStep s (.getrandom 16 {}) (.err Errno.ENFILE) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.err Errno.EMFILE) = none ∧
    allowedStep s (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOSPC) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.EINTR) = some sUnready ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EINTR) = none ∧
    allowedStep sUnready (.getrandom 16 { insecure := true }) (.err Errno.EINTR) = none ∧
    allowedStep sReady (.getrandom 16 {}) (.err Errno.EINTR) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.ENOMEM) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.EIO) = none := by
  cases hc : s.crngReady <;>
    simp [allowedStep, allowedStepCore, hs, Timespec.isValid, GrndFlags.isInvalid,
      validGetrandomResultLen, NSEC_PER_SEC, GETRANDOM_EXACT_MAX,
      MAX_READ_BYTES, Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.EAGAIN,
      Errno.EMFILE, Errno.ENFILE, Errno.ENOSPC, hc]

/-- Proof of `test_timerand_allowedStep_exactKernelSemantics` for `allowedStep`. -/
theorem proof_timerand_allowedStep_exactKernelSemantics :
    AllPass (test_timerand_allowedStep_exactKernelSemantics) := by
  intro sRaw
  let s : TimeRandState := { sRaw with ambientSeccomp := false }
  have hs : s.ambientSeccomp = false := rfl
  have hc := allowedStep_clock_cases s hs
  have hs' := allowedStep_sleep_cases s hs
  have hr := allowedStep_rand_cases s hs
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
    hs'.1, hs'.2.1, hs'.2.2.1, hs'.2.2.2.1, hs'.2.2.2.2.1, hs'.2.2.2.2.2.1,
    hs'.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.2.1,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2,
    hs'.2.2.2.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.2.2.2,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    trivial⟩

/-- Proof of `test_timerand_allowedStep_withOuterSeccomp` for `allowedStep`. -/
theorem proof_timerand_allowedStep_withOuterSeccomp :
    AllPass (test_timerand_allowedStep_withOuterSeccomp) := by
  intro sBase
  dsimp only [test_timerand_allowedStep_withOuterSeccomp, Core.NondetTest.assert, Bind.bind]
  simp [TimeRandState.initial, TimeRandState.withOuterSeccomp, allowedStep, allowedStepCore,
    Timespec.isValid, Timespec.toNanosNat, GrndFlags.isInvalid,
    MAX_TIMESPEC_NANOS, MAX_TIMESPEC_SEC,
    NSEC_PER_SEC, Errno.EPERM, Errno.EACCES, Errno.ENOSYS, Errno.EAGAIN, Errno.EINVAL,
    Errno.EFAULT, Errno.EINTR]

/-- Proof of `test_timerand_modelOps_soundAgainstAllowedStep` for `modelOps` and `allowedStep`. -/
theorem proof_timerand_modelOps_soundAgainstAllowedStep :
    AllPass (test_timerand_modelOps_soundAgainstAllowedStep modelOps) := by
  intro s clk abstime req len flags
  dsimp (config := { zeta := false }) only [NondetTest.assert, Bind.bind, StateT.run]
  change (allowedStep s (.clock_gettime clk) (outcomeOfTimespec (modelOps.clock_gettime clk s).1) =
      some (modelOps.clock_gettime clk s).2) ∧
    (allowedStep s (.clock_nanosleep clk abstime req) (outcomeOfUnit (modelOps.clock_nanosleep clk abstime req s).1) =
      some (modelOps.clock_nanosleep clk abstime req s).2) ∧
    (allowedStep s (.getrandom len flags) (outcomeOfBytes (modelOps.getrandom len flags s).1) =
      some (modelOps.getrandom len flags s).2) ∧ True
  refine ⟨?_, ?_, ?_, trivial⟩
  · cases clk
    · have hspec := ofEpochNanos?_spec s.realtimeNs
      dsimp only at hspec
      rw [modelOps_clock_gettime_realtime]
      split at hspec
      · rcases hspec with ⟨ts, htsEq, htsValid, _⟩
        rw [htsEq]
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, htsValid]
      · rw [hspec]
        let clampedSec : Int64 :=
          if s.realtimeNs < 0 then Int64.minValue else Int64.maxValue
        let clampedNsec : UInt32 :=
          if s.realtimeNs < 0 then 0 else UInt32.ofNat (NSEC_PER_SEC - 1)
        let clampedTs : Timespec := { sec := clampedSec, nsec := clampedNsec }
        have hval : clampedTs.hasValidNsec = true := by
          dsimp only [clampedTs, clampedNsec, Timespec.hasValidNsec, NSEC_PER_SEC]
          by_cases hneg : s.realtimeNs < 0 <;> simp [hneg] <;> decide
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hval, clampedTs, clampedSec, clampedNsec]
    · rw [modelOps_clock_gettime_monotonic]
      by_cases hm : s.monoLowerBoundNs ≤ MAX_TIMESPEC_NANOS
      · obtain ⟨ts, htsEq, htsValid, htsNs⟩ := ofNanosNat?_some hm
        rw [htsEq]
        have hmin : min s.monoLowerBoundNs MAX_TIMESPEC_NANOS = s.monoLowerBoundNs := Nat.min_eq_left hm
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, htsValid, htsNs, hmin]
      · have hgt : MAX_TIMESPEC_NANOS < s.monoLowerBoundNs := Nat.lt_of_not_le hm
        have hnone := ofNanosNat?_none hgt
        rw [hnone]
        have hmin : min s.monoLowerBoundNs MAX_TIMESPEC_NANOS = MAX_TIMESPEC_NANOS :=
          Nat.min_eq_right (Nat.le_of_lt hgt)
        have hmax : max s.monoLowerBoundNs MAX_TIMESPEC_NANOS = s.monoLowerBoundNs :=
          Nat.max_eq_left (Nat.le_of_lt hgt)
        have hval : Timespec.isValid { sec := Int64.ofInt (MAX_TIMESPEC_SEC : Int), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) } = true := by decide
        have hns : Timespec.toNanosNat { sec := Int64.ofInt (MAX_TIMESPEC_SEC : Int), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) } = MAX_TIMESPEC_NANOS := by decide
        cases hsec : s.ambientSeccomp
        · simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hmin]
          rw [hval, hns]
          cases s; simp_all
        · simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hmin]
          rw [hval, hns]
          cases s; simp_all
  · rw [modelOps_clock_nanosleep]
    by_cases hv : req.isValid = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hsec : s.ambientSeccomp <;> cases clk <;>
        simp [outcomeOfUnit, allowedStep, allowedStepCore, hsec, hv]
    · have hfalse : req.isValid = false := by
        cases hb : req.isValid <;> simp_all
      cases hsec : s.ambientSeccomp <;>
        simp [hfalse, outcomeOfUnit, allowedStep, allowedStepCore, hsec, Errno.EINVAL, Errno.EFAULT]
  · rw [modelOps_getrandom]
    by_cases hinv : flags.isInvalid = true
    · cases hsec : s.ambientSeccomp <;>
        simp [hinv, outcomeOfBytes, allowedStep, allowedStepCore, hsec, Errno.EINVAL, Errno.EFAULT]
    · have hinvFalse : flags.isInvalid = false := by
        cases hb : flags.isInvalid <;> simp_all
      simp only [hinvFalse, Bool.false_eq_true, ↓reduceIte]
      by_cases hea : (!s.crngReady && flags.nonblock && !flags.insecure) = true
      · simp only [hea, ↓reduceIte, outcomeOfBytes]
        cases hsec : s.ambientSeccomp
        · simp only [allowedStep, allowedStepCore, hsec, Bool.false_eq_true, ↓reduceIte, hinvFalse, hea]
          rfl
        · simp [allowedStep, hsec, Errno.EAGAIN, Errno.EFAULT]
      · have heaFalse : (!s.crngReady && flags.nonblock && !flags.insecure) = false := by
          cases hb : (!s.crngReady && flags.nonblock && !flags.insecure) <;> simp_all
        simp only [heaFalse, Bool.false_eq_true, ↓reduceIte, outcomeOfBytes]
        have hlen : validGetrandomResultLen len
            (deterministicEntropyBytes s.entropyDraws (min len.toNat MAX_READ_BYTES.toNat)).size = true := by
          rw [deterministicEntropyBytes_size]
          exact validGetrandomResultLen_eq len
        cases hsec : s.ambientSeccomp <;>
          simp [allowedStep, allowedStepCore, hsec, hinvFalse, hlen]

/-- Exact disjoint partition of `Errno.isTransientOsErrno` into `EINTR`, `Errno.isCriticalOsErrno`, and `Errno.isResourceLimitErrno`. -/
theorem errno_transient_partition (e : Errno) :
    Errno.isTransientOsErrno e =
      (e == Errno.EINTR || Errno.isCriticalOsErrno e || Errno.isResourceLimitErrno e) ∧
    (Errno.isCriticalOsErrno e && Errno.isResourceLimitErrno e) = false := by
  refine ⟨?_, ?_⟩
  · unfold Errno.isTransientOsErrno Errno.isCriticalOsErrno Errno.isResourceLimitErrno
    cases e == Errno.EINTR <;> cases e == Errno.EIO <;> cases e == Errno.ENOMEM <;>
      cases e == Errno.ENFILE <;> cases e == Errno.EMFILE <;> cases e == Errno.ENOSPC <;> rfl
  · by_cases h1 : e == Errno.ENOMEM
    · have : e = Errno.ENOMEM := eq_of_beq h1
      subst this; decide
    · by_cases h2 : e == Errno.EIO
      · have : e = Errno.EIO := eq_of_beq h2
        subst this; decide
      · by_cases h3 : e == Errno.ENFILE
        · have : e = Errno.ENFILE := eq_of_beq h3
          subst this; decide
        · simp [Errno.isCriticalOsErrno, h1, h2, h3]

/-- `allowedStepCore` preserves `ambientSeccomp`. -/
theorem allowedStepCore_preserves_ambientSeccomp
    (s s' : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : allowedStepCore s req out = some s') :
    s'.ambientSeccomp = s.ambientSeccomp := by
  cases req with
  | clock_gettime clk =>
    cases out with
    | timespec ts =>
      cases clk <;> simp only [allowedStepCore] at h <;> split at h <;>
        first | contradiction | (injection h with hEq; rw [← hEq])
    | _ => simp [allowedStepCore] at h
  | clock_nanosleep clk abstime reqTs =>
    simp only [allowedStepCore] at h
    split at h
    · cases out with
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
    · cases out with
      | unit =>
        cases clk <;> simp only at h <;> injection h with hEq <;> rw [← hEq]
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
  | getrandom len flags =>
    simp only [allowedStepCore] at h
    split at h
    · cases out with
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
    · cases out with
      | bytes got =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h

/-- `allowedStepCore` never permits curated critical OS faults. -/
theorem allowedStepCore_not_critical
    (s s' : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : allowedStepCore s req out = some s') :
    isCriticalFault out = false := by
  cases out with
  | unit | timespec _ | bytes _ => rfl
  | err e =>
    cases req with
    | clock_gettime clk => simp [allowedStepCore] at h
    | clock_nanosleep clk abstime reqTs =>
      simp only [allowedStepCore] at h
      split at h
      · split at h
        · rename_i heq
          have : e = Errno.EINVAL := eq_of_beq heq
          subst this; decide
        · contradiction
      · split at h
        · rename_i heq
          have : e = Errno.EINTR := eq_of_beq heq
          subst this; decide
        · contradiction
    | getrandom len flags =>
      simp only [allowedStepCore] at h
      split at h
      · split at h
        · rename_i heq
          have : e = Errno.EINVAL := eq_of_beq heq
          subst this; decide
        · contradiction
      · split at h
        · rename_i hcond
          rcases Bool.or_eq_true_iff.mp hcond with h1 | h2
          · simp only [Bool.and_eq_true] at h1
            have : e = Errno.EAGAIN := eq_of_beq h1.2
            subst this; decide
          · simp only [Bool.and_eq_true] at h2
            have : e = Errno.EINTR := eq_of_beq h2.2
            subst this; decide
        · contradiction

end LeanSwe.LinuxSyscall.TimeRand.Proofs

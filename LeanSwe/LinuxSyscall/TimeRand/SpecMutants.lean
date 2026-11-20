import LeanSwe.LinuxSyscall.TimeRand.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.LinuxSyscall.TimeRand`. -/

namespace LeanSwe.LinuxSyscall.TimeRand

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def stubModelOps : TimeRandOpsM (StateM TimeRandState) :=
  { clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
    clock_nanosleep := fun _ _ _ => pure (.ok ())
    getrandom := fun _ _ => pure (.ok ByteArray.empty) }

example : ¬ Core.AllPass (test_timerand_errno_classificationAndTransient
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    TimeRandErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_timerand_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EAGAIN then .invalidArg else TimeRandErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.EAGAIN
  exact absurd h0.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_timerand_encoders_injectiveAndGrndInvalid
    (encClock := fun _ => 0)) := by
  intro h
  have h0 := h .realtime .monotonic {} {}
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_timerand_encoders_injectiveAndGrndInvalid
    (encGrnd := fun f => { f with insecure := false }.toBits)) := by
  intro h
  have h0 := h .realtime .realtime { insecure := false } { insecure := true }
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_timerand_encoders_injectiveAndGrndInvalid
    (isBadGrnd := fun f => (f.random && f.insecure) || (f.nonblock && f.insecure))) := by
  intro h
  have h0 := h .realtime .realtime {} {}
  exact absurd h0.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_timerand_timespec_validAndNanosRoundTrip
    (isValidFn := fun ts => decide (ts.nsec.toNat < NSEC_PER_SEC))) := by
  intro h
  have h0 := h { sec := -1, nsec := 0 } 0 0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_timerand_timespec_validAndNanosRoundTrip
    (ofEpochFn := fun _ => some { sec := 0, nsec := 0 })) := by
  intro h
  have h0 := h {} 0 (-1)
  have h1 := h0.2.2.1
  simp [Timespec.hasValidNsec, Timespec.toEpochNanos, MIN_TIMESPEC_SEC_INT,
    MAX_TIMESPEC_SEC, NSEC_PER_SEC] at h1

example : ¬ Core.AllPass (test_timerand_mkTimeRandOps_encodesAndDelegates
    (fun raw =>
      { clock_gettime := fun clk =>
          match raw.clock_gettime clk.toRaw with
          | .ok (sec, nsec) => .ok { sec, nsec }
          | .error e => .error e
        clock_nanosleep := fun clk _ req => raw.clock_nanosleep clk.toRaw 0 req.sec req.nsec
        getrandom := fun len flags => raw.getrandom len flags.toBits })) := by
  intro h
  have h0 := h (fun _ => .ok (0, 0))
    (fun _ abs _ _ => if abs == 1 then .ok () else .error Errno.EINVAL)
    (fun _ _ => .ok ByteArray.empty)
    .monotonic true { sec := 0, nsec := 1 } 0 {}
  dsimp [Core.NondetTest.assert, Bind.bind] at h0
  cases h0.2.1

example : ¬ Core.AllPass (test_timerand_mkTimeRandOps_encodesAndDelegates
    (fun raw =>
      { clock_gettime := fun clk =>
          match raw.clock_gettime clk.toRaw with
          | .ok (sec, nsec) => .ok { sec, nsec }
          | .error e => .error e
        clock_nanosleep := fun clk abstime req =>
          raw.clock_nanosleep clk.toRaw (if abstime then 1 else 0) req.sec req.nsec
        getrandom := fun len _ => raw.getrandom len 0 })) := by
  intro h
  have h0 := h (fun _ => .ok (0, 0))
    (fun _ _ _ _ => .ok ())
    (fun _ fb => if fb == 0 then .error Errno.EINVAL else .ok ByteArray.empty)
    .monotonic false {} 16 { nonblock := true }
  dsimp [GrndFlags.toBits, Core.NondetTest.assert, Bind.bind] at h0
  cases h0.2.2.1

example : ¬ Core.AllPass (test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes
    { modelOps with
      clock_nanosleep := fun clk abstime req =>
        if clk == .realtime && abstime && req.nsec.toNat < NSEC_PER_SEC then pure (.ok ())
        else modelOps.clock_nanosleep clk abstime req }) := by
  intro h
  have h0 := h {} .realtime true { sec := -1, nsec := 0 } (by decide)
  dsimp [Core.NondetTest.assert, StateT.run, pure, StateT.pure, NSEC_PER_SEC] at h0
  cases h0.1

example : ¬ Core.AllPass (test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes
    { modelOps with
      clock_nanosleep := fun clk abstime req =>
        if req.nsec.toNat == NSEC_PER_SEC then pure (.ok ())
        else modelOps.clock_nanosleep clk abstime req }) := by
  intro h
  have h0 := h {} .monotonic false { sec := 0, nsec := 1000000000 } (by decide)
  dsimp [Core.NondetTest.assert, StateT.run, pure, StateT.pure, NSEC_PER_SEC] at h0
  cases h0.1

example : ¬ Core.AllPass (test_timerand_ops_monotonicMultiCallAndNanosleepBounds stubModelOps) := by
  intro h
  have h0 := h { monoLowerBoundNs := 100 } { sec := 0, nsec := 50 } { sec := 0, nsec := 200 }
    (by decide) (by decide) (by decide)
  dsimp [test_timerand_ops_monotonicMultiCallAndNanosleepBounds, stubModelOps,
    Timespec.toNanosNat, NSEC_PER_SEC, Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.2.1.1 (by decide)

example : ¬ Core.AllPass (test_timerand_ops_monotonicMultiCallAndNanosleepBounds
    { modelOps with
      clock_nanosleep := fun _ _ req =>
        if !req.isValid then pure (.error Errno.EINVAL) else pure (.ok ()) }) := by
  intro h
  have h0 := h { monoLowerBoundNs := 0 } { sec := 0, nsec := 50 } { sec := 0, nsec := 0 }
    (by decide) (by decide) (by decide)
  dsimp [test_timerand_ops_monotonicMultiCallAndNanosleepBounds, modelOps,
    Timespec.ofNanosNat?, Timespec.isValid, Timespec.toNanosNat, MAX_TIMESPEC_SEC, NSEC_PER_SEC,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, StateT.set, pure, StateT.pure] at h0
  exact absurd h0.2.2.2.1.2 (by decide)

example : ¬ Core.AllPass (test_timerand_ops_getrandom_flagsLengthsAndCrngState stubModelOps) := by
  intro h
  have h0 := h {} 16 false
  dsimp [test_timerand_ops_getrandom_flagsLengthsAndCrngState, stubModelOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_timerand_ops_getrandom_flagsLengthsAndCrngState
    { modelOps with
      getrandom := fun len flags =>
        if flags.isInvalid then pure (.error Errno.EINVAL)
        else do
          let s ← get
          if !s.crngReady && flags.nonblock && !flags.insecure then pure (.error Errno.EAGAIN)
          else do
            set { s with crngReady := s.crngReady || !flags.insecure }
            pure (.ok (ByteArray.mk (List.replicate (min len.toNat MAX_READ_BYTES.toNat) (0 : UInt8)).toArray)) }) := by
  intro h
  have h0 := h {} 16 false
  dsimp [test_timerand_ops_getrandom_flagsLengthsAndCrngState, modelOps, GrndFlags.isInvalid,
    MAX_READ_BYTES, Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure] at h0
  exact h0.2.2.2.2.2.1.2.2.1 rfl

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .getrandom 16 _, .bytes _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics,
    Core.NondetTest.assert, Bind.bind] at h0
  have hShort := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hShort

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .getrandom _ _, .err e => if e == Errno.EAGAIN then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics,
    Core.NondetTest.assert, Bind.bind] at h0
  have hReadyEagain := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hReadyEagain

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .getrandom _ _, .err e => if Errno.isTransientOsErrno e then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics, Errno.isTransientOsErrno,
    Core.NondetTest.assert, Bind.bind] at h0
  have hEmfile := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hEmfile

example : ¬ Core.AllPass (test_timerand_modelOps_soundAgainstAllowedStep stubModelOps) := by
  intro h
  have h0 := h { monoLowerBoundNs := 10 } .monotonic false {} 0 {}
  dsimp [test_timerand_modelOps_soundAgainstAllowedStep, stubModelOps, allowedStep,
    outcomeOfTimespec, Timespec.isValid, Timespec.toNanosNat, NSEC_PER_SEC,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_timerand_allowedStep_withOuterSeccomp
    (fun s req out => allowedStep { s with ambientSeccomp := false } req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_withOuterSeccomp, TimeRandState.withOuterSeccomp,
    allowedStep, allowedStepCore,
    Core.NondetTest.assert, Bind.bind] at h0
  cases h0.2.2.2.1

example : ¬ Core.AllPass (test_timerand_allowedStep_withOuterSeccomp
    (fun s req out =>
      if s.ambientSeccomp then
        match out with
        | .err _ => some s
        | _ => allowedStep s req out
      else allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_withOuterSeccomp, TimeRandState.withOuterSeccomp,
    allowedStep, allowedStepCore,
    Core.NondetTest.assert, Bind.bind] at h0
  cases h0.2.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .clock_gettime _, .err e => if e == Errno.ENOMEM then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics,
    Timespec.ofEpochNanos?, MIN_TIMESPEC_SEC_INT, MAX_TIMESPEC_SEC, NSEC_PER_SEC,
    Core.NondetTest.assert, Bind.bind] at h0
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hBad

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .clock_nanosleep _ _ _, .err e => if e == Errno.EIO then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics,
    Core.NondetTest.assert, Bind.bind] at h0
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hBad

example : ¬ Core.AllPass (test_timerand_allowedStep_exactKernelSemantics
    (fun s req out =>
      match req, out with
      | .getrandom _ _, .err e => if e == Errno.EINTR then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  have h0 := h {}
  dsimp [test_timerand_allowedStep_exactKernelSemantics,
    Core.NondetTest.assert, Bind.bind] at h0
  have hBad := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hBad

example : ¬ Core.AllPass (test_timerand_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if !env.wf || isCriticalFault out then none
      else (allowedStep env.state req out).map (fun s' => { state := s', eintrBudget := env.eintrBudget }))) := by
  intro h
  exact absurd h.2.2.1.2 (by decide)

example : ¬ Core.AllPass (test_timerand_healthyStep_and_healthyModelOps
    (ops := { healthyModelOps with clock_gettime := fun _ => pure (.error Errno.EINTR) })) := by
  intro h
  have h0 := h.2.2.2.2.2 (HealthyEnv.initial 1 0 false) rfl .monotonic false { sec := 0, nsec := 0 } 0 {}
  rcases h0.1.2.1 with ⟨_, hEq⟩
  cases hEq

example : ¬ Core.AllPass (test_timerand_healthyStep_and_healthyModelOps
    (ops := { healthyModelOps with
      getrandom := fun len flags env =>
        if flags.isInvalid then (.error Errno.EINVAL, env)
        else
          let cap := min len.toNat MAX_READ_BYTES.toNat
          (.ok (ByteArray.mk (Array.replicate cap 0)),
           { env with state := { env.state with
               crngReady := env.state.crngReady || !flags.insecure
               entropyDraws := env.state.entropyDraws + 1 } }) })) := by
  intro h
  have h0 := h.2.2.2.2.2 (HealthyEnv.initial 1 0 false) rfl .monotonic false { sec := 0, nsec := 0 }
    16 { nonblock := true }
  have hEq := congrArg Prod.fst h0.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_timerand_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if decide (env.eintrBudget ≥ 2) && isEintrOutcome out then
        (healthyStep env req out).map (fun env' => { env' with eintrBudget := env.eintrBudget })
      else
        healthyStep env req out)) := by
  intro h
  have hRest := h.2.2.2.2.2 (HealthyEnv.initial 1 0 false) rfl .monotonic false { sec := 0, nsec := 0 } 0 {}
  have hStep := (hRest.2.2.2 (HealthyEnv.initial 2 0 false)
    (.clock_nanosleep .monotonic false { sec := 0, nsec := 1000 }) (.err Errno.EINTR)).1
  exact absurd (congrArg (Option.map HealthyEnv.eintrBudget) hStep) (by decide)

end LeanSwe.LinuxSyscall.TimeRand

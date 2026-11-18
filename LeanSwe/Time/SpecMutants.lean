import Core.NondetTest
import LeanSwe.Time.Types
import LeanSwe.Time.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Time`. -/

namespace LeanSwe.Time

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM TimeRandState Timespec)

private def stubTimeApiAt {m : Type → Type} [Monad m] : TimeApiM m :=
  { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
    monoNanosNow := pure 0
    sleepMs := fun _ => pure ()
    sleepDuration := fun _ => pure ()
    measure := fun act => do
      let a ← act
      pure (a, 0)
    elapsedDuration := fun _ _ => 0
    deadlineNanos := fun start _ => start
    isMonoExpired := fun _ _ => false
    formatUtcIso8601 := fun _ => ""
    parseUtcIso8601 := fun _ => .error { kind := .invalidFormat, message := "stub" }
    formatUtcCompact := fun _ => ""
    formatUtcDate := fun _ => ""
    parseUtcDate := fun _ => .error { kind := .invalidFormat, message := "stub" }
    utcDateOfTimestamp := fun _ => Std.Time.PlainDate.ofEpochDay 0
    timestampOfUtcDate := fun _ => Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0 }

example : ¬ Core.AllPass (test_time_mono_deadlineAndElapsed stubTimeApiAt) := by
  intro h
  have h0 := h 10 (Std.Time.Duration.ofSeconds 5) 20 20
  dsimp [test_time_mono_deadlineAndElapsed, Core.NondetTest.assert, Bind.bind, stubTimeApiAt] at h0
  exact absurd h0.1 (by decide)

private def buggyExpiredEqOnlyApi : TimeApi :=
  { stubTimeApiAt with
    deadlineNanos := fun start limit =>
      if limit.toNanoseconds.val ≥ 0 then start + limit.toNanoseconds.val.toNat else start
    isMonoExpired := fun nowMono dl => nowMono == dl }

example : ¬ Core.AllPass (test_time_mono_deadlineAndElapsed buggyExpiredEqOnlyApi) := by
  intro h
  have h0 := h 10 (Std.Time.Duration.ofSeconds 5) 5000000020 20
  dsimp [test_time_mono_deadlineAndElapsed, Core.NondetTest.assert, Bind.bind, buggyExpiredEqOnlyApi] at h0
  exact absurd h0.2.1 (by decide)

private def buggySleepTruncatesUInt32Api : TimeApiM (StateM FakeClock) :=
  { (stubTimeApiAt (m := StateM FakeClock)) with
    nowTimestamp := do
      let s ← get
      pure s.wall
    monoNanosNow := do
      let s ← get
      pure s.monoNanos
    sleepMs := fun ms => do
      let c := UInt32.ofNat ms
      modify fun s =>
        { wall := s.wall + Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat c.toNat)
          monoNanos := s.monoNanos + c.toNat * 1000000
          sleepLog := s.sleepLog.push c } }

example : ¬ Core.AllPass (test_time_fakeClock_sleepMs_advancesAndChunks buggySleepTruncatesUInt32Api) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ 4294967296
  dsimp [test_time_fakeClock_sleepMs_advancesAndChunks, buggySleepTruncatesUInt32Api,
    Core.NondetTest.assert, Bind.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, StateT.pure] at h0
  exact absurd h0.1 (by decide)

private def buggySleepDurationNegApi : TimeApiM (StateM FakeClock) :=
  { (stubTimeApiAt (m := StateM FakeClock)) with
    sleepDuration := fun _ =>
      modify fun s => { s with monoNanos := s.monoNanos + 1000000 } }

example : ¬ Core.AllPass (test_time_fakeClock_sleepDuration_clampsAndRoundsUp buggySleepDurationNegApi) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ (Std.Time.Duration.ofSeconds (-1))
  dsimp [test_time_fakeClock_sleepDuration_clampsAndRoundsUp, buggySleepDurationNegApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_time_fakeClock_measure_returnsValueAndElapsed stubTimeApiAt) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ 5
  simp [stubTimeApiAt, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_time_fakeClock_nowTimestamp_readsWithoutMutating stubTimeApiAt) := by
  intro h
  have h0 := h ⟨Std.Time.Timestamp.ofSecondsSinceUnixEpoch 42, 0, #[]⟩
  simp [stubTimeApiAt, StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_time_fakeClock_monoNanosNow_readsWithoutMutating stubTimeApiAt) := by
  intro h
  have h0 := h ⟨0, 77, #[]⟩
  simp [stubTimeApiAt, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_time_utcIso8601_roundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) (by decide)
  simp [stubTimeApiAt, bind, assert] at h0

example : ¬ Core.AllPass (test_time_utcIso8601_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcIso8601 := fun _ => .error { kind := .invalidFormat, message := "" } }) := by
  intro h
  have h0 := h "bad"
  simp [bind, assert] at h0

example : ¬ Core.AllPass (test_time_utcIso8601_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcIso8601 := fun _ => .ok (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) }) := by
  intro h
  have h0 := h "bad"
  simp [bind, assert, Except.isOk, Except.toBool] at h0

example : ¬ Core.AllPass (test_time_utcDate_roundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.PlainDate.ofEpochDay 0) (by decide)
  simp [stubTimeApiAt, bind, assert] at h0

example : ¬ Core.AllPass (test_time_utcDate_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcDate := fun _ => .error { kind := .invalidFormat, message := "" } }) := by
  intro h
  have h0 := h "bad"
  simp [bind, assert] at h0

example : ¬ Core.AllPass (test_time_utcDate_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcDate := fun _ => .ok (Std.Time.PlainDate.ofEpochDay 0) }) := by
  intro h
  have h0 := h "bad"
  simp [bind, assert, Except.isOk, Except.toBool] at h0

example : ¬ Core.AllPass (test_time_utcDate_timestampRoundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.PlainDate.ofEpochDay 1)
  simp [stubTimeApiAt, bind, assert] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_time_utcCompact_formatShape stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) (by decide)
  simp [stubTimeApiAt, bind, assert] at h0

example : ¬ Core.AllPass (test_time_utcCompact_formatShape
    { stubTimeApiAt with
      formatUtcIso8601 := fun _ => "1970-01-01T00:00:00.000000000Z"
      formatUtcCompact := fun _ => "00000000T000000Z" }) := by
  intro h
  have h0 := h (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) (by decide)
  dsimp [test_time_utcCompact_formatShape, stubTimeApiAt, Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass (test_time_mkTimeOps_readsRealtimeAndMonotonic
    (fun _ => { nowTimestamp := Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0
                monoNanosNow := 0
                sleep := fun _ => () })) := by
  intro h
  have h0 := h { sec := -1, nsec := 999999999 } { sec := 0, nsec := 42 } Errno.EIO (by decide)
  have h1 := h0.2.1
  simp [Timespec.toNanosNat, LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC] at h1

example : ¬ Core.AllPass (test_time_mkTimeOps_sleepZeroAndModelSleepMs
    (fun _ =>
      { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
        monoNanosNow := pure 0
        sleep := fun _ => pure () })
    (fun _ =>
      { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
        monoNanosNow := do return (← get).monoLowerBoundNs
        sleep := fun _ => pure () })
    (fun _ => stubTimeApiAt)) := by
  intro h
  have h0 := h {} {} 5 (by decide)
  have h1 := h0.2.2.1
  dsimp only [stubTimeApiAt, StateT.run, Bind.bind, StateT.bind, pure, StateT.pure] at h1
  omega

example : ¬ Core.AllPass (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift
    (fun sys =>
      { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
        monoNanosNow := pure 0
        sleep := fun ms =>
          if ms == 0 then pure ()
          else do
            let _ ← sys.clock_nanosleep .monotonic false
              { sec := Int64.ofInt (Int.ofNat (ms.toNat / 1000))
                nsec := UInt32.ofNat ((ms.toNat % 1000) * 1000000) }
            pure () })) := by
  intro h
  have h0 := h { sec := 1, nsec := 0 } 10 1 Errno.EIO (by decide) (by decide) (by decide) (by decide) (by decide)
  dsimp [test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift, scriptedSleepSysOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure] at h0
  exact absurd h0.1 (by decide)

private def retryBugNoFallbackLoop {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (target : Timespec) : Nat → m Unit
  | 0 => do
    let _ ← sys.clock_nanosleep .monotonic true target
    pure ()
  | fuel + 1 => do
    match ← sys.clock_nanosleep .monotonic true target with
    | .ok () => pure ()
    | .error e =>
      if e == Errno.EINTR then retryBugNoFallbackLoop sys target fuel
      else pure ()

example : ¬ Core.AllPass (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift
    (fun sys =>
      { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
        monoNanosNow := pure 0
        sleep := fun ms =>
          if ms == 0 then pure ()
          else do
            match ← sys.clock_gettime .monotonic with
            | .ok nowTs =>
              if decide (0 ≤ nowTs.sec.toInt) then
                match Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) with
                | some targetTs => retryBugNoFallbackLoop sys targetTs MAX_EINTR_RETRIES
                | none => pure ()
              else pure ()
            | .error _ => pure () })) := by
  intro h
  have h0 := h { sec := 1, nsec := 0 } 10 1 Errno.EIO (by decide) (by decide) (by decide) (by decide) (by decide)
  have hGetErr := h0.2.2.2.2.2.1
  dsimp [scriptedSleepSysOps, Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure] at hGetErr
  exact absurd hGetErr.2.1 (by decide)

example : ¬ Core.AllPass (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift
    (fun sys =>
      { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
        monoNanosNow := pure 0
        sleep := fun ms =>
          if ms == 0 then pure ()
          else do
            match ← sys.clock_gettime .monotonic with
            | .ok nowTs =>
              if decide (0 ≤ nowTs.sec.toInt) then
                match Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) with
                | some targetTs => retryBugNoFallbackLoop sys targetTs MAX_EINTR_RETRIES
                | none =>
                  let _ ← sys.clock_nanosleep .monotonic false { sec := 0, nsec := 0 }
                  pure ()
              else
                let _ ← sys.clock_nanosleep .monotonic false { sec := 0, nsec := 0 }
                pure ()
            | .error _ =>
              let _ ← sys.clock_nanosleep .monotonic false { sec := 0, nsec := 0 }
              pure () })) := by
  intro h
  have h0 := h { sec := 1, nsec := 0 } 10 1 Errno.EIO (by decide) (by decide) (by decide) (by decide) (by decide)
  have hGetErr := h0.2.2.2.2.2.1
  dsimp [scriptedSleepSysOps, Timespec.isValid, Timespec.toNanosNat,
    LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC, Core.NondetTest.assert, Bind.bind,
    StateT.run, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, StateT.pure] at hGetErr
  exact absurd hGetErr.2.2 (by decide)

end LeanSwe.Time

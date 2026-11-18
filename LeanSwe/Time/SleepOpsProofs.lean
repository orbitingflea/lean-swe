import LeanSwe.Time.SleepModelProofs

namespace LeanSwe.Time.SleepOpsProofs

open Core
open Core.NondetTest
open Std.Time
open LeanSwe.Time.SleepModelProofs

theorem sleepZeroAndModelSleepMs_impl :
    AllPass (test_time_mkTimeOps_sleepZeroAndModelSleepMs Internal.mkTimeOps Internal.mkTimeOps Internal.mkApiM) :=
  SleepModelProofs.sleepZeroAndModelSleepMs_impl

private theorem scriptedSleep_clock_gettime_ok (fb : Except LeanSwe.LinuxSyscall.Errno Unit)
    (s : SleepTraceState) (h : s.gettimeErr? = none) :
    ((scriptedSleepSysOps fb).clock_gettime .monotonic).run s =
      (.ok s.monoNow, { s with gettimeCalls := s.gettimeCalls + 1 }) := by
  simp [scriptedSleepSysOps, h, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set, pure, StateT.pure, Bind.bind, StateT.bind]

private theorem scriptedSleep_clock_gettime_err (fb : Except LeanSwe.LinuxSyscall.Errno Unit)
    (s : SleepTraceState) (e : LeanSwe.LinuxSyscall.Errno) (h : s.gettimeErr? = some e) :
    ((scriptedSleepSysOps fb).clock_gettime .monotonic).run s =
      (.error e, { s with gettimeCalls := s.gettimeCalls + 1 }) := by
  simp [scriptedSleepSysOps, h, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set, pure, StateT.pure, Bind.bind, StateT.bind]

private theorem scriptedSleep_clock_nanosleep_step (fb : Except LeanSwe.LinuxSyscall.Errno Unit)
    (clk : LeanSwe.LinuxSyscall.TimeRand.ClockId) (abstime : Bool)
    (req : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (r : Except LeanSwe.LinuxSyscall.Errno Unit) (s : SleepTraceState)
    (hr : r = match s.sleepResponses with | [] => fb | x :: _ => x) :
    ((scriptedSleepSysOps fb).clock_nanosleep clk abstime req).run s =
      (r, { s with sleepResponses := s.sleepResponses.tail,
                   nanosleepLog := (clk, abstime, req) :: s.nanosleepLog }) := by
  subst hr
  cases hsr : s.sleepResponses <;>
    simp [scriptedSleepSysOps, hsr, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, pure, StateT.pure, Bind.bind, StateT.bind]

private theorem sleepAbstimeRetry_zero {σ : Type}
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (target : LeanSwe.LinuxSyscall.TimeRand.Timespec) (s : σ) :
    ((Internal.sleepAbstimeRetry sys target 0).run s).2 =
      ((sys.clock_nanosleep .monotonic true target).run s).2 := rfl

private theorem sleepAbstimeRetry_succ_ok {σ : Type}
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (target : LeanSwe.LinuxSyscall.TimeRand.Timespec) (fuel : Nat) (s s1 : σ)
    (h : (sys.clock_nanosleep .monotonic true target).run s = (.ok (), s1)) :
    (Internal.sleepAbstimeRetry sys target (fuel + 1)).run s = ((), s1) := by
  have hbind : (Internal.sleepAbstimeRetry sys target (fuel + 1)).run s =
      (let p := (sys.clock_nanosleep .monotonic true target).run s
       StateT.run (match p.1 with
        | .ok () => pure ()
        | .error e => if e == .EINTR then Internal.sleepAbstimeRetry sys target fuel else pure () : StateM σ Unit) p.2) := rfl
  rw [hbind, h]
  rfl

private theorem sleepAbstimeRetry_succ_err {σ : Type}
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (target : LeanSwe.LinuxSyscall.TimeRand.Timespec) (fuel : Nat) (e : LeanSwe.LinuxSyscall.Errno)
    (s s1 : σ) (h : (sys.clock_nanosleep .monotonic true target).run s = (.error e, s1)) :
    (Internal.sleepAbstimeRetry sys target (fuel + 1)).run s =
      (if e == .EINTR then (Internal.sleepAbstimeRetry sys target fuel).run s1 else ((), s1)) := by
  have hbind : (Internal.sleepAbstimeRetry sys target (fuel + 1)).run s =
      (let p := (sys.clock_nanosleep .monotonic true target).run s
       StateT.run (match p.1 with
        | .ok () => pure ()
        | .error e => if e == .EINTR then Internal.sleepAbstimeRetry sys target fuel else pure () : StateM σ Unit) p.2) := rfl
  rw [hbind, h]
  dsimp only
  split <;> rfl

private theorem sleepAbstimeRetry_eintr_ok (target : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (n fuel : Nat) (hn : n ≤ fuel) (s : SleepTraceState)
    (hresp : s.sleepResponses = List.replicate n (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok ()]) :
    let s' := ((Internal.sleepAbstimeRetry scriptedSleepSysOps target fuel).run s).2
    s'.gettimeCalls = s.gettimeCalls ∧
    s'.nanosleepLog = List.replicate (n + 1) (.monotonic, true, target) ++ s.nanosleepLog := by
  induction n generalizing fuel s with
  | zero =>
    have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic true target (.ok ()) s
      (by rw [hresp]; rfl)
    cases fuel with
    | zero =>
      dsimp only
      rw [sleepAbstimeRetry_zero, hc]
      exact ⟨rfl, rfl⟩
    | succ fuel' =>
      dsimp only
      rw [sleepAbstimeRetry_succ_ok scriptedSleepSysOps target fuel' s _ hc]
      exact ⟨rfl, rfl⟩
  | succ n ih =>
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic true target
        (.error LeanSwe.LinuxSyscall.Errno.EINTR) s (by rw [hresp]; rfl)
      have hstep := sleepAbstimeRetry_succ_err scriptedSleepSysOps target fuel'
        LeanSwe.LinuxSyscall.Errno.EINTR s _ hc
      rw [beq_self_eq_true] at hstep
      simp only [↓reduceIte] at hstep
      have hresp' : ({ s with sleepResponses := s.sleepResponses.tail, nanosleepLog := (.monotonic, true, target) :: s.nanosleepLog } : SleepTraceState).sleepResponses =
          List.replicate n (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok ()] := by
        dsimp; rw [hresp]; rfl
      have hih := ih fuel' (by omega)
        { s with sleepResponses := s.sleepResponses.tail,
                 nanosleepLog := (.monotonic, true, target) :: s.nanosleepLog } hresp'
      dsimp only
      rw [hstep]
      refine ⟨hih.1, ?_⟩
      rw [hih.2]
      have hrep : ∀ (k : Nat) (x : LeanSwe.LinuxSyscall.TimeRand.ClockId × Bool × LeanSwe.LinuxSyscall.TimeRand.Timespec) l,
          x :: (List.replicate k x ++ x :: l) = List.replicate (k + 1 + 1) x ++ l := by
        intro k x l
        induction k with
        | zero => rfl
        | succ k ihk => simp [List.replicate_succ] at ihk ⊢; exact ihk
      exact hrep n (.monotonic, true, target) s.nanosleepLog

private theorem sleepAbstimeRetry_storm (target : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (fuel : Nat) (s : SleepTraceState) (hresp : s.sleepResponses = []) :
    let s' := ((Internal.sleepAbstimeRetry (scriptedSleepSysOps (.error LeanSwe.LinuxSyscall.Errno.EINTR)) target fuel).run s).2
    s'.gettimeCalls = s.gettimeCalls ∧
    s'.nanosleepLog.length = s.nanosleepLog.length + fuel + 1 := by
  induction fuel generalizing s with
  | zero =>
    have hc := scriptedSleep_clock_nanosleep_step (.error LeanSwe.LinuxSyscall.Errno.EINTR)
      .monotonic true target (.error LeanSwe.LinuxSyscall.Errno.EINTR) s (by rw [hresp])
    dsimp only
    rw [sleepAbstimeRetry_zero, hc]
    exact ⟨rfl, by simp⟩
  | succ fuel' ih =>
    have hc := scriptedSleep_clock_nanosleep_step (.error LeanSwe.LinuxSyscall.Errno.EINTR)
      .monotonic true target (.error LeanSwe.LinuxSyscall.Errno.EINTR) s (by rw [hresp])
    have hstep := sleepAbstimeRetry_succ_err (scriptedSleepSysOps (.error LeanSwe.LinuxSyscall.Errno.EINTR))
      target fuel' LeanSwe.LinuxSyscall.Errno.EINTR s _ hc
    rw [beq_self_eq_true] at hstep
    simp only [↓reduceIte] at hstep
    have hih := ih
      { s with sleepResponses := s.sleepResponses.tail,
               nanosleepLog := (.monotonic, true, target) :: s.nanosleepLog }
      (by dsimp; rw [hresp]; rfl)
    dsimp only
    rw [hstep]
    refine ⟨hih.1, ?_⟩
    rw [hih.2]
    simp; omega

private theorem sleepAbstimeRetry_fatal (target : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (fuel : Nat) (e : LeanSwe.LinuxSyscall.Errno) (hne : e ≠ LeanSwe.LinuxSyscall.Errno.EINTR)
    (s : SleepTraceState) (rest : List (Except LeanSwe.LinuxSyscall.Errno Unit))
    (hresp : s.sleepResponses = .error e :: rest) :
    let s' := ((Internal.sleepAbstimeRetry scriptedSleepSysOps target (fuel + 1)).run s).2
    s'.gettimeCalls = s.gettimeCalls ∧ s'.nanosleepLog.length = s.nanosleepLog.length + 1 := by
  have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic true target (.error e) s
    (by rw [hresp])
  have hstep := sleepAbstimeRetry_succ_err scriptedSleepSysOps target fuel e s _ hc
  rw [beq_false_of_ne hne] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  dsimp only
  rw [hstep]
  exact ⟨rfl, by simp⟩

private theorem relativeTimespecOfMs_valid (ms : UInt32) :
    (Internal.relativeTimespecOfMs ms).isValid = true ∧
      (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000 := by
  have hms_lt : ms.toNat < 2 ^ 32 := ms.toBitVec.isLt
  have hsec0 : (Int64.ofInt (Int.ofNat (ms.toNat / 1000))).toInt = ((ms.toNat / 1000 : Nat) : Int) :=
    int64_toInt_ofNat _ (by omega)
  have hnsec0 : (UInt32.ofNat (ms.toNat % 1000 * 1000000)).toNat = ms.toNat % 1000 * 1000000 := by
    rw [UInt32.toNat_ofNat']; omega
  simp only [LeanSwe.LinuxSyscall.TimeRand.Timespec.isValid,
    LeanSwe.LinuxSyscall.TimeRand.Timespec.toNanosNat,
    LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC,
    LeanSwe.Time.Internal.relativeTimespecOfMs, hsec0, hnsec0]
  constructor
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, by omega⟩
  · rw [Int.toNat_natCast]
    omega

private theorem mkTimeOps_sleep_rel_err {σ : Type} (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (ms : UInt32) (hms : ms ≠ 0) (s0 s1 : σ) (e : LeanSwe.LinuxSyscall.Errno)
    (hget : (sys.clock_gettime .monotonic).run s0 = (.error e, s1)) :
    (((Internal.mkTimeOps sys).sleep ms).run s0).2 =
      ((sys.clock_nanosleep .monotonic false (Internal.relativeTimespecOfMs ms)).run s1).2 := by
  dsimp [Internal.mkTimeOps]
  rw [beq_false_of_ne hms]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_run_bind, hget]
  rfl

private theorem mkTimeOps_sleep_rel_neg {σ : Type} (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (ms : UInt32) (hms : ms ≠ 0) (s0 s1 : σ) (nowTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (hget : (sys.clock_gettime .monotonic).run s0 = (.ok nowTs, s1))
    (hneg : decide (0 ≤ nowTs.sec.toInt) = false) :
    (((Internal.mkTimeOps sys).sleep ms).run s0).2 =
      ((sys.clock_nanosleep .monotonic false (Internal.relativeTimespecOfMs ms)).run s1).2 := by
  dsimp [Internal.mkTimeOps]
  rw [beq_false_of_ne hms]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_run_bind, hget]
  dsimp only
  rw [hneg]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem mkTimeOps_sleep_rel_none {σ : Type} (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (ms : UInt32) (hms : ms ≠ 0) (s0 s1 : σ) (nowTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (hget : (sys.clock_gettime .monotonic).run s0 = (.ok nowTs, s1))
    (hpos : 0 ≤ nowTs.sec.toInt)
    (hnone : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) = none) :
    (((Internal.mkTimeOps sys).sleep ms).run s0).2 =
      ((sys.clock_nanosleep .monotonic false (Internal.relativeTimespecOfMs ms)).run s1).2 := by
  dsimp [Internal.mkTimeOps]
  rw [beq_false_of_ne hms]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_run_bind, hget]
  dsimp only
  rw [decide_eq_true hpos]
  simp only [↓reduceIte, hnone]
  rfl

private theorem sleep_eintr_cases (startMono targetTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (ms : UInt32) (hms0 : ms ≠ 0) (hsec : 0 ≤ startMono.sec.toInt)
    (htarget : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? (startMono.toNanosNat + ms.toNat * 1000000) = some targetTs)
    (htarget_valid : targetTs.isValid = true)
    (htarget_ns : targetTs.toNanosNat = startMono.toNanosNat + ms.toNat * 1000000)
    (eintrCount : Nat) (heintr_le : eintrCount ≤ Internal.MAX_EINTR_RETRIES) :
    let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.ok ()))).sleep ms).run
      { monoNow := startMono, sleepResponses := List.replicate eintrCount (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok ()] }).2
    st.gettimeCalls = 1 ∧
      st.nanosleepLog.length = eintrCount + 1 ∧
      (st.nanosleepLog.all fun x =>
        x.1 == .monotonic && x.2.1 == true && x.2.2.isValid && x.2.2.toNanosNat == startMono.toNanosNat + ms.toNat * 1000000) = true := by
  have hget := scriptedSleep_clock_gettime_ok (.ok ())
    { monoNow := startMono, sleepResponses := List.replicate eintrCount (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok ()] } rfl
  have hs := congrArg Prod.snd (mkTimeOps_sleep_abstime (scriptedSleepSysOps (.ok ())) ms hms0 _ startMono targetTs _ hget hsec htarget)
  have he := sleepAbstimeRetry_eintr_ok targetTs eintrCount Internal.MAX_EINTR_RETRIES heintr_le
    { monoNow := startMono,
      sleepResponses := List.replicate eintrCount (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok ()],
      gettimeCalls := 1 } rfl
  have hclk : (LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic == LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic) = true := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; exact he.1
  · rw [hs, he.2]; simp
  · rw [hs, he.2]; simp [htarget_valid, htarget_ns, hclk]

private theorem sleep_fatal_storm_cases (startMono targetTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (ms : UInt32) (hms0 : ms ≠ 0) (hsec : 0 ≤ startMono.sec.toInt)
    (htarget : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? (startMono.toNanosNat + ms.toNat * 1000000) = some targetTs)
    (fatalErr : LeanSwe.LinuxSyscall.Errno) (hfatal : fatalErr ≠ LeanSwe.LinuxSyscall.Errno.EINTR) :
    (let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.ok ()))).sleep ms).run
      { monoNow := startMono, sleepResponses := [.error fatalErr, .ok ()] }).2
     st.gettimeCalls = 1 ∧ st.nanosleepLog.length = 1) ∧
    (let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.error LeanSwe.LinuxSyscall.Errno.EINTR))).sleep ms).run
      { monoNow := startMono, sleepResponses := [] }).2
     st.gettimeCalls = 1 ∧ st.nanosleepLog.length = Internal.MAX_EINTR_RETRIES + 1) := by
  refine ⟨?_, ?_⟩
  · have hget := scriptedSleep_clock_gettime_ok (.ok ())
      { monoNow := startMono, sleepResponses := [.error fatalErr, .ok ()] } rfl
    have hs := congrArg Prod.snd (mkTimeOps_sleep_abstime (scriptedSleepSysOps (.ok ())) ms hms0 _ startMono targetTs _ hget hsec htarget)
    have hfuel : (Internal.MAX_EINTR_RETRIES - 1) + 1 = Internal.MAX_EINTR_RETRIES := by decide
    dsimp only; rw [hs, ← hfuel]
    exact sleepAbstimeRetry_fatal targetTs (Internal.MAX_EINTR_RETRIES - 1) fatalErr hfatal
      { monoNow := startMono, sleepResponses := [.error fatalErr, .ok ()], gettimeCalls := 1 }
      [.ok ()] rfl
  · have hget := scriptedSleep_clock_gettime_ok (.error LeanSwe.LinuxSyscall.Errno.EINTR)
      { monoNow := startMono, sleepResponses := [] } rfl
    have hs := congrArg Prod.snd (mkTimeOps_sleep_abstime (scriptedSleepSysOps (.error LeanSwe.LinuxSyscall.Errno.EINTR)) ms hms0 _ startMono targetTs _ hget hsec htarget)
    have hl := sleepAbstimeRetry_storm targetTs Internal.MAX_EINTR_RETRIES
      { monoNow := startMono, sleepResponses := [], gettimeCalls := 1 } rfl
    dsimp only; rw [hs]; simp [hl.1, hl.2, Nat.add_comm]

private theorem sleep_rel_err_case (ms : UInt32) (hms0 : ms ≠ 0) (fatalErr : LeanSwe.LinuxSyscall.Errno)
    (hrel : (Internal.relativeTimespecOfMs ms).isValid = true ∧ (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000) :
    let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.ok ()))).sleep ms).run
      { gettimeErr? := some fatalErr, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] }).2
    st.gettimeCalls = 1 ∧ st.nanosleepLog.length = 1 ∧
      (st.nanosleepLog.all fun x => x.1 == .monotonic && x.2.1 == false && x.2.2.isValid && x.2.2.toNanosNat == ms.toNat * 1000000) = true := by
  have hclk : (LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic == LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic) = true := rfl
  have hget := scriptedSleep_clock_gettime_err (.ok ())
    { gettimeErr? := some fatalErr, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] } fatalErr rfl
  have hrel_call := mkTimeOps_sleep_rel_err scriptedSleepSysOps ms hms0 _ _ fatalErr hget
  have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic false (Internal.relativeTimespecOfMs ms)
    (.error LeanSwe.LinuxSyscall.Errno.EINTR)
    { gettimeErr? := some fatalErr, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()], gettimeCalls := 1 } rfl
  dsimp only
  rw [hrel_call, congrArg Prod.snd hc]
  simp [hrel.1, hrel.2, hclk]

private theorem sleep_rel_overflow_case (ms : UInt32) (hms : ms > 0) (hms0 : ms ≠ 0)
    (hrel : (Internal.relativeTimespecOfMs ms).isValid = true ∧ (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000) :
    let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.ok ()))).sleep ms).run
      { monoNow := { sec := 9223372036854775807, nsec := 999999999 },
        sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] }).2
    st.gettimeCalls = 1 ∧ st.nanosleepLog.length = 1 ∧
      (st.nanosleepLog.all fun x => x.1 == .monotonic && x.2.1 == false && x.2.2.isValid && x.2.2.toNanosNat == ms.toNat * 1000000) = true := by
  have hclk : (LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic == LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic) = true := rfl
  let tsMax : LeanSwe.LinuxSyscall.TimeRand.Timespec := { sec := 9223372036854775807, nsec := 999999999 }
  have hs0 : tsMax.sec.toInt = 9223372036854775807 := by decide
  have hsec_max : 0 ≤ tsMax.sec.toInt := by omega
  have hns_max : tsMax.toNanosNat = 9223372036854775807 * 1000000000 + 999999999 := by decide
  have hms_pos : 0 < ms.toNat := hms
  have hgt : LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS < tsMax.toNanosNat + ms.toNat * 1000000 := by
    dsimp [LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS,
      LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_SEC,
      LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC]
    rw [hns_max]; omega
  have hnone : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? (tsMax.toNanosNat + ms.toNat * 1000000) = none := by
    simp [LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat?, hgt]
  have hget := scriptedSleep_clock_gettime_ok (.ok ())
    { monoNow := tsMax, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] } rfl
  have hrel_call := mkTimeOps_sleep_rel_none scriptedSleepSysOps ms hms0 _ _ tsMax hget hsec_max hnone
  have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic false (Internal.relativeTimespecOfMs ms)
    (.error LeanSwe.LinuxSyscall.Errno.EINTR)
    { monoNow := tsMax, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()], gettimeCalls := 1 } rfl
  dsimp only
  rw [hrel_call, congrArg Prod.snd hc]
  simp [hrel.1, hrel.2, hclk]

private theorem sleep_rel_neg_case (ms : UInt32) (hms0 : ms ≠ 0)
    (hrel : (Internal.relativeTimespecOfMs ms).isValid = true ∧ (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000) :
    let st := (((Internal.mkTimeOps (scriptedSleepSysOps (.ok ()))).sleep ms).run
      { monoNow := { sec := -1, nsec := 0 },
        sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] }).2
    st.gettimeCalls = 1 ∧ st.nanosleepLog.length = 1 ∧
      (st.nanosleepLog.all fun x => x.1 == .monotonic && x.2.1 == false && x.2.2.isValid && x.2.2.toNanosNat == ms.toNat * 1000000) = true := by
  have hclk : (LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic == LeanSwe.LinuxSyscall.TimeRand.ClockId.monotonic) = true := rfl
  let tsNeg : LeanSwe.LinuxSyscall.TimeRand.Timespec := { sec := -1, nsec := 0 }
  have hneg : decide (0 ≤ tsNeg.sec.toInt) = false := by decide
  have hget := scriptedSleep_clock_gettime_ok (.ok ())
    { monoNow := tsNeg, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()] } rfl
  have hrel_call := mkTimeOps_sleep_rel_neg scriptedSleepSysOps ms hms0 _ _ tsNeg hget hneg
  have hc := scriptedSleep_clock_nanosleep_step (.ok ()) .monotonic false (Internal.relativeTimespecOfMs ms)
    (.error LeanSwe.LinuxSyscall.Errno.EINTR)
    { monoNow := tsNeg, sleepResponses := [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok ()], gettimeCalls := 1 } rfl
  dsimp only
  rw [hrel_call, congrArg Prod.snd hc]
  simp [hrel.1, hrel.2, hclk]

theorem sleepAbstimeRetriesEintrWithoutDrift_impl :
    AllPass (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift Internal.mkTimeOps) := by
  intro startMono ms eintrCount fatalErr hvalid hms hbound heintr hfatal
  dsimp [test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift, Core.NondetTest.assert, Bind.bind]
  have hms0 : ms ≠ 0 := by intro h; subst h; exact Nat.lt_irrefl 0 hms
  have hsec : 0 ≤ startMono.sec.toInt := by
    dsimp [LeanSwe.LinuxSyscall.TimeRand.Timespec.isValid] at hvalid
    simp at hvalid; exact hvalid.1
  rcases toNanosNat_ofNanosNat_some hbound with ⟨targetTs, htarget, htarget_sec, htarget_nsec, htarget_ns⟩
  have htarget_valid : targetTs.isValid = true := by
    simp [LeanSwe.LinuxSyscall.TimeRand.Timespec.isValid, LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC,
      htarget_sec, htarget_nsec]
  have heintr_le : eintrCount ≤ Internal.MAX_EINTR_RETRIES := by
    dsimp [Internal.MAX_EINTR_RETRIES, LeanSwe.Time.MAX_EINTR_RETRIES]
    omega
  have hrel := relativeTimespecOfMs_valid ms
  have h1 := sleep_eintr_cases startMono targetTs ms hms0 hsec htarget htarget_valid htarget_ns eintrCount heintr_le
  have h2 := sleep_fatal_storm_cases startMono targetTs ms hms0 hsec htarget fatalErr hfatal
  have h3 := sleep_rel_err_case ms hms0 fatalErr hrel
  have h4 := sleep_rel_overflow_case ms hms hms0 hrel
  have h5 := sleep_rel_neg_case ms hms0 hrel
  exact ⟨h1.1, h1.2.1, h1.2.2, h2.1, h2.2, h3, h4, h5, trivial⟩

end LeanSwe.Time.SleepOpsProofs

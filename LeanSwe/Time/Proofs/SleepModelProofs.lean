import LeanSwe.Time.Interface
import LeanSwe.Time.SpecTests

namespace LeanSwe.Time.SleepModelProofs

open Core
open Core.NondetTest
open Std.Time

theorem toNanoseconds_ofNanoseconds (n : Nanosecond.Offset) :
    (Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

theorem toNanoseconds_inj {a b : Duration}
    (h : a.toNanoseconds = b.toNanoseconds) : a = b := by
  have heq : a.toNanoseconds.val = b.toNanoseconds.val := congrArg Internal.UnitVal.val h
  rcases a with ⟨⟨sa⟩, ⟨na, hna⟩, hpa⟩
  rcases b with ⟨⟨sb⟩, ⟨nb, hnb⟩, hpb⟩
  change sa * 1000000000 + na = sb * 1000000000 + nb at heq
  have hna' : -999999999 ≤ na ∧ na ≤ 999999999 := hna
  have hnb' : -999999999 ≤ nb ∧ nb ≤ 999999999 := hnb
  have hpa' : (sa ≥ 0 ∧ na ≥ 0) ∨ (sa ≤ 0 ∧ na ≤ 0) := hpa
  have hpb' : (sb ≥ 0 ∧ nb ≥ 0) ∨ (sb ≤ 0 ∧ nb ≤ 0) := hpb
  have hs : sa = sb := by omega
  subst hs
  have hn : na = nb := by omega
  subst hn
  rfl

theorem int64_toInt_ofNat (n : Nat) (hn : n < 2 ^ 63) :
    (Int64.ofInt (n : Int)).toInt = (n : Int) := by
  rw [Int64.toInt_ofInt, Int.bmod_def]
  have hsz : (Int64.size : Int) = 18446744073709551616 := by decide
  have h1 : (n : Int) % (Int64.size : Int) = (n : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg n) (by rw [hsz]; omega)
  rw [h1]
  have hlt : (n : Int) < ((Int64.size : Int) + 1) / 2 := by rw [hsz]; omega
  simp only [hlt, ↓reduceIte]

theorem toNanosNat_ofNanosNat_some {ns : Nat}
    (hle : ns ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS) :
    ∃ ts, LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? ns = some ts ∧
      0 ≤ ts.sec.toInt ∧ ts.nsec.toNat < 1000000000 ∧ ts.toNanosNat = ns := by
  have hle' : ns ≤ 9223372036854775807 * 1000000000 + 999999999 := by
    dsimp [LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS,
      LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_SEC,
      LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC] at hle
    exact hle
  have hs : ns / 1000000000 ≤ Int64.maxValue.toInt.toNat := by
    have hm : Int64.maxValue.toInt.toNat = 9223372036854775807 := by decide
    rw [hm]; omega
  have hns_sec_lt : ns / 1000000000 < 2 ^ 63 := by
    have : ns ≤ 9223372036854775807 * 1000000000 + 999999999 := hle'
    omega
  refine ⟨{ sec := Int64.ofInt ((ns / 1000000000 : Nat) : Int),
            nsec := UInt32.ofNat (ns % 1000000000) }, ?_, ?_, ?_, ?_⟩
  · dsimp [LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat?, LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC]
    have hgt : ¬ (ns > LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS) := Nat.not_lt.mpr hle
    simp [hgt]
  · change 0 ≤ (Int64.ofInt ((ns / 1000000000 : Nat) : Int)).toInt
    rw [int64_toInt_ofNat _ hns_sec_lt]; omega
  · rw [UInt32.toNat_ofNat']; omega
  · dsimp [LeanSwe.LinuxSyscall.TimeRand.Timespec.toNanosNat, LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC]
    have hcast : ((ns / 1000000000 : Nat) : Int) = (ns : Int) / 1000000000 :=
      Int.natCast_ediv ns 1000000000
    have hmod : (UInt32.ofNat (ns % 1000000000)).toNat = ns % 1000000000 := by
      rw [UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
    rw [← hcast, int64_toInt_ofNat _ hns_sec_lt, Int.toNat_natCast, hmod]
    omega

private theorem modelOps_clock_gettime_monotonic (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState)
    (nowTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (hnow : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? s0.monoLowerBoundNs = some nowTs)
    (hns : nowTs.toNanosNat = s0.monoLowerBoundNs) :
    ((LeanSwe.LinuxSyscall.TimeRand.modelOps.clock_gettime .monotonic).run s0) =
      (.ok nowTs, s0) := by
  simp [LeanSwe.LinuxSyscall.TimeRand.modelOps, hnow, hns, StateT.run,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
    pure, StateT.pure, Bind.bind, StateT.bind]

private theorem modelOps_clock_nanosleep_monotonic_abs
    (targetTs : LeanSwe.LinuxSyscall.TimeRand.Timespec) (hvalid : targetTs.isValid = true)
    (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState) :
    ((LeanSwe.LinuxSyscall.TimeRand.modelOps.clock_nanosleep .monotonic true targetTs).run s0) =
      (.ok (), { s0 with monoLowerBoundNs := max s0.monoLowerBoundNs targetTs.toNanosNat }) := by
  simp [LeanSwe.LinuxSyscall.TimeRand.modelOps, hvalid, StateT.run,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
    pure, StateT.pure, Bind.bind, StateT.bind]

private theorem modelOps_sleepAbstimeRetry_valid (targetTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (hvalid : targetTs.isValid = true) (fuel : Nat) (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState) :
    ((Internal.sleepAbstimeRetry LeanSwe.LinuxSyscall.TimeRand.modelOps targetTs (fuel + 1)).run s0).2 =
      { s0 with monoLowerBoundNs := max s0.monoLowerBoundNs targetTs.toNanosNat } := by
  dsimp [Internal.sleepAbstimeRetry]
  simp only [StateT.run, Bind.bind]
  have hcall := modelOps_clock_nanosleep_monotonic_abs targetTs hvalid s0
  simp only [StateT.run] at hcall
  rw [hcall]
  rfl

theorem mkTimeOps_sleep_zero {σ : Type} (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (s0 : σ) :
    ((Internal.mkTimeOps sys).sleep 0).run s0 = ((), s0) := by
  dsimp [Internal.mkTimeOps, StateT.run, pure, StateT.pure]

theorem stateM_run_bind {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

theorem stateM_run_seq {σ α β : Type} (a : StateM σ α) (b : StateM σ β) (s : σ) :
    (a >>= fun _ => b).run s = b.run (a.run s).2 := rfl

theorem mkTimeOps_sleep_abstime {σ : Type} (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (ms : UInt32) (hms : ms ≠ 0) (s0 : σ) (nowTs targetTs : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (s1 : σ) (hget : (sys.clock_gettime .monotonic).run s0 = (.ok nowTs, s1))
    (hsec : 0 ≤ nowTs.sec.toInt)
    (htarget : LeanSwe.LinuxSyscall.TimeRand.Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) = some targetTs) :
    ((Internal.mkTimeOps sys).sleep ms).run s0 =
      (Internal.sleepAbstimeRetry sys targetTs Internal.MAX_EINTR_RETRIES).run s1 := by
  dsimp [Internal.mkTimeOps]
  rw [beq_false_of_ne hms]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_run_bind, hget]
  dsimp only
  rw [decide_eq_true hsec]
  simp only [↓reduceIte, htarget]

private theorem modelOps_sleep_spec (ms : UInt32) (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState)
    (hbound : s0.monoLowerBoundNs + ms.toNat * 1000000 ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS) :
    (((Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps).sleep ms).run s0).2 =
      { s0 with monoLowerBoundNs := s0.monoLowerBoundNs + ms.toNat * 1000000 } := by
  by_cases h0 : ms = 0
  · subst h0
    exact congrArg Prod.snd (mkTimeOps_sleep_zero LeanSwe.LinuxSyscall.TimeRand.modelOps s0)
  · have hm0 : s0.monoLowerBoundNs ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS := by omega
    rcases toNanosNat_ofNanosNat_some hm0 with ⟨nowTs, hnow, hnow_sec, _, hnow_ns⟩
    rcases toNanosNat_ofNanosNat_some hbound with ⟨targetTs, htarget, htarget_sec, htarget_nsec, htarget_ns⟩
    have hvalid_target : targetTs.isValid = true := by
      simp [LeanSwe.LinuxSyscall.TimeRand.Timespec.isValid, LeanSwe.LinuxSyscall.TimeRand.NSEC_PER_SEC,
        htarget_sec, htarget_nsec]
    have hget := modelOps_clock_gettime_monotonic s0 nowTs hnow hnow_ns
    have hsleep := mkTimeOps_sleep_abstime LeanSwe.LinuxSyscall.TimeRand.modelOps ms h0 s0 nowTs targetTs s0
      hget hnow_sec (by rw [hnow_ns]; exact htarget)
    have hretry := modelOps_sleepAbstimeRetry_valid targetTs hvalid_target
      (Internal.MAX_EINTR_RETRIES - 1) s0
    have hfuel : (Internal.MAX_EINTR_RETRIES - 1) + 1 = Internal.MAX_EINTR_RETRIES := by decide
    rw [hfuel] at hretry
    rw [congrArg Prod.snd hsleep, hretry, htarget_ns]
    have hmax : max s0.monoLowerBoundNs (s0.monoLowerBoundNs + ms.toNat * 1000000) =
        s0.monoLowerBoundNs + ms.toNat * 1000000 :=
      Nat.max_eq_right (Nat.le_add_right _ _)
    rw [hmax]

private theorem sleepMs_succ_eq {σ : Type} (ops : TimeOpsM (StateM σ)) (ms : Nat) (hms : ms ≠ 0) (s0 : σ) :
    (Internal.sleepMs ops ms).run s0 =
      (Internal.sleepMs ops (ms - min ms (UInt32.size - 1))).run
        ((ops.sleep (UInt32.ofNat (min ms (UInt32.size - 1)))).run s0).2 := by
  rw [Internal.sleepMs]
  simp only [hms, ↓reduceIte]
  rfl

private theorem modelSleepMs_spec (ms : Nat) (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState)
    (hbound : s0.monoLowerBoundNs + ms * 1000000 ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS) :
    ((Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms).run s0).2 =
      { s0 with monoLowerBoundNs := s0.monoLowerBoundNs + ms * 1000000 } := by
  induction ms using Nat.strongRecOn generalizing s0 with
  | _ ms ih =>
    by_cases h0 : ms = 0
    · subst h0
      rw [Internal.sleepMs]
      simp [StateT.run, pure, StateT.pure]
    · have hpos : 0 < ms := Nat.pos_of_ne_zero h0
      have hmax : min ms (UInt32.size - 1) ≤ UInt32.size - 1 := Nat.min_le_right _ _
      have hcpos : 0 < min ms (UInt32.size - 1) := Nat.lt_min.mpr ⟨hpos, by decide⟩
      have hc_le : min ms (UInt32.size - 1) ≤ ms := Nat.min_le_left _ _
      have hchunk_lt : min ms (UInt32.size - 1) < UInt32.size :=
        Nat.lt_of_le_of_lt hmax (Nat.sub_lt (by decide) (by decide))
      have hchunk_toNat : (UInt32.ofNat (min ms (UInt32.size - 1))).toNat = min ms (UInt32.size - 1) := by
        rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hchunk_lt
      have hbound_c : s0.monoLowerBoundNs + (UInt32.ofNat (min ms (UInt32.size - 1))).toNat * 1000000 ≤
          LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS := by
        rw [hchunk_toNat]
        exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc_le) _) hbound
      have hst1 := modelOps_sleep_spec (UInt32.ofNat (min ms (UInt32.size - 1))) s0 hbound_c
      have hrem_lt : ms - min ms (UInt32.size - 1) < ms := Nat.sub_lt hpos hcpos
      have hmul : min ms (UInt32.size - 1) * 1000000 + (ms - min ms (UInt32.size - 1)) * 1000000 = ms * 1000000 := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hc_le]
      have hbound_rem : ({ s0 with monoLowerBoundNs := s0.monoLowerBoundNs + min ms (UInt32.size - 1) * 1000000 } :
          LeanSwe.LinuxSyscall.TimeRand.TimeRandState).monoLowerBoundNs +
          (ms - min ms (UInt32.size - 1)) * 1000000 ≤
          LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS := by
        dsimp only; rw [Nat.add_assoc, hmul]; exact hbound
      have hih := ih (ms - min ms (UInt32.size - 1)) hrem_lt
        { s0 with monoLowerBoundNs := s0.monoLowerBoundNs + min ms (UInt32.size - 1) * 1000000 } hbound_rem
      rw [congrArg Prod.snd (sleepMs_succ_eq _ ms h0 s0), hst1, hchunk_toNat, hih]
      dsimp only
      rw [Nat.add_assoc, hmul]

private theorem mkTimeOps_monoNanosNow {σ : Type}
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM (StateM σ))
    (s0 s1 : σ) (ts : LeanSwe.LinuxSyscall.TimeRand.Timespec)
    (hget : (sys.clock_gettime .monotonic).run s0 = (.ok ts, s1))
    (hsec : 0 ≤ ts.sec.toInt) :
    ((Internal.mkTimeOps sys).monoNanosNow.run s0) = (ts.toNanosNat, s1) := by
  have hbind : ((Internal.mkTimeOps sys).monoNanosNow.run s0) =
      (let p := (sys.clock_gettime .monotonic).run s0
       StateT.run (match p.1 with
        | .ok ts => pure (if decide (0 ≤ ts.sec.toInt) = true then ts.toNanosNat else 0)
        | .error _ => pure 0 : StateM σ Nat) p.2) := rfl
  rw [hbind, hget]
  dsimp only
  rw [decide_eq_true hsec]
  simp only [↓reduceIte]
  rfl

private theorem modelOps_monoNanosNow (s0 : LeanSwe.LinuxSyscall.TimeRand.TimeRandState)
    (hle : s0.monoLowerBoundNs ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS) :
    ((Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps).monoNanosNow.run s0) =
      (s0.monoLowerBoundNs, s0) := by
  rcases toNanosNat_ofNanosNat_some hle with ⟨ts, hts, hsec, _, hns⟩
  have hget := modelOps_clock_gettime_monotonic s0 ts hts hns
  rw [mkTimeOps_monoNanosNow LeanSwe.LinuxSyscall.TimeRand.modelOps s0 s0 ts hget hsec, hns]

theorem sleepZeroAndModelSleepMs_impl :
    AllPass (test_time_mkTimeOps_sleepZeroAndModelSleepMs Internal.mkTimeOps Internal.mkTimeOps Internal.mkApiM) := by
  intro traceInit s0 ms hbound
  dsimp [test_time_mkTimeOps_sleepZeroAndModelSleepMs, Internal.mkApiM, Internal.measure,
    Core.NondetTest.assert, Bind.bind]
  have hz := congrArg Prod.snd (mkTimeOps_sleep_zero scriptedSleepSysOps traceInit)
  refine ⟨?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · have h1 := modelSleepMs_spec ms s0 hbound
    have h2 := modelOps_monoNanosNow s0 (by omega)
    let s1 := ((Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms).run s0).2
    have hs1_b : s1.monoLowerBoundNs ≤ LeanSwe.LinuxSyscall.TimeRand.MAX_TIMESPEC_NANOS := by
      change (((Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms).run s0).2).monoLowerBoundNs ≤ _
      rw [h1]
      exact hbound
    have h3 := modelOps_monoNanosNow s1 hs1_b
    change let res := (((Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps).monoNanosNow >>= fun startMono =>
        Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms >>= fun () =>
        (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps).monoNanosNow >>= fun stopMono =>
        pure (ms, Internal.elapsedDuration startMono stopMono)).run s0)
      res.1.1 = ms ∧ res.2.monoLowerBoundNs = s0.monoLowerBoundNs + ms * 1000000 ∧
        res.1.2 = Duration.ofMillisecond (Millisecond.Offset.ofNat ms) ∧ True
    dsimp only
    rw [stateM_run_bind, h2]
    dsimp only
    rw [stateM_run_bind]
    have hs1_def : ((Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms).run s0).2 = s1 := rfl
    rw [hs1_def, stateM_run_bind, h3]
    dsimp only [Internal.elapsedDuration]
    change (ms, Internal.elapsedDuration s0.monoLowerBoundNs s1.monoLowerBoundNs, s1).1 = ms ∧
      s1.monoLowerBoundNs = s0.monoLowerBoundNs + ms * 1000000 ∧
      Internal.elapsedDuration s0.monoLowerBoundNs s1.monoLowerBoundNs =
        Duration.ofMillisecond (Millisecond.Offset.ofNat ms) ∧ True
    have hs1_eq : s1.monoLowerBoundNs = s0.monoLowerBoundNs + ms * 1000000 := by
      change (((Internal.sleepMs (Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.modelOps) ms).run s0).2).monoLowerBoundNs = _
      rw [h1]
    rw [hs1_eq]
    refine ⟨rfl, rfl, ?_, trivial⟩
    dsimp only [Internal.elapsedDuration]
    simp only [show s0.monoLowerBoundNs ≤ s0.monoLowerBoundNs + ms * 1000000 by omega, ↓reduceIte,
      show s0.monoLowerBoundNs + ms * 1000000 - s0.monoLowerBoundNs = ms * 1000000 by omega]
    apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    rw [toNanoseconds_ofNanoseconds]
    change ((Nanosecond.Offset.ofNat (ms * 1000000)).val) =
      (Duration.ofNanoseconds (Millisecond.Offset.ofNat ms).toNanoseconds).toNanoseconds.val
    rw [toNanoseconds_ofNanoseconds]
    change ((ms * 1000000 : Nat) : Int) = (ms : Int) * 1000000
    omega

end LeanSwe.Time.SleepModelProofs

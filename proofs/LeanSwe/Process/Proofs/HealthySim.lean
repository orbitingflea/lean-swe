import LeanSwe.Process.Proofs.HealthySimBase
import LeanSwe.Process.Proofs.HealthySimFiles

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

@[simp] private theorem stateM_modifyGet_run {S α : Type} (f : S → α × S) (s : S) :
    (modifyGet f : StateM S α).run s = f s := rfl

private theorem int64_toInt_ofInt' {x : Int}
    (hlo : TimeRand.MIN_TIMESPEC_SEC_INT ≤ x) (hhi : x ≤ Int.ofNat TimeRand.MAX_TIMESPEC_SEC) :
    (Int64.ofInt x).toInt = x := by
  rw [Int64.toInt_ofInt]
  change -9223372036854775808 ≤ x at hlo
  change x ≤ 9223372036854775807 at hhi
  change (if x % (18446744073709551616 : Int) < (9223372036854775808 : Int) then
      x % (18446744073709551616 : Int)
    else x % (18446744073709551616 : Int) - (18446744073709551616 : Int)) = x
  by_cases hx : 0 ≤ x
  · rw [Int.emod_eq_of_lt hx (by omega)]
    have hlt : x < (9223372036854775808 : Int) := by omega
    simp [hlt]
  · have hm : x % (18446744073709551616 : Int) = x + (18446744073709551616 : Int) := by omega
    rw [hm]
    have hge : ¬ x + (18446744073709551616 : Int) < (9223372036854775808 : Int) := by omega
    simp [hge]

private theorem u32_toNat_ofNat_lt' {n : Nat} (h : n < 4294967296) :
    (UInt32.ofNat n).toNat = n := by
  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

private theorem tr_ofNanosNat?_none {ns : Nat} (h : TimeRand.MAX_TIMESPEC_NANOS < ns) :
    TimeRand.Timespec.ofNanosNat? ns = none := by
  unfold TimeRand.Timespec.ofNanosNat?
  have hble : ns.ble TimeRand.MAX_TIMESPEC_NANOS = false := by
    cases hb : ns.ble TimeRand.MAX_TIMESPEC_NANOS
    · rfl
    · have := Nat.ble_eq.mp hb; omega
  simp [hble]

private theorem tr_ofNanosNat?_some {ns : Nat} (h : ns ≤ TimeRand.MAX_TIMESPEC_NANOS) :
    ∃ out, TimeRand.Timespec.ofNanosNat? ns = some out ∧
      TimeRand.Timespec.isValid out = true ∧ out.toNanosNat = ns := by
  unfold TimeRand.Timespec.ofNanosNat?
  rw [Nat.ble_eq.mpr h]; simp only [↓reduceIte]
  have hbound : ns ≤ 9223372036854775807999999999 := h
  have hrem : ns % 1000000000 < 1000000000 := Nat.mod_lt ns (by decide)
  have hsec : (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt = Int.ofNat (ns / 1000000000) :=
    int64_toInt_ofInt' (Int.le_trans (by decide) (Int.natCast_nonneg _))
      (by change ((ns / 1000000000 : Nat) : Int) ≤ 9223372036854775807; omega)
  have hnsec : (UInt32.ofNat (ns % 1000000000)).toNat = ns % 1000000000 :=
    u32_toNat_ofNat_lt' (by omega)
  refine ⟨_, rfl, ?_, ?_⟩
  · unfold TimeRand.Timespec.isValid TimeRand.NSEC_PER_SEC
    change (decide (0 ≤ (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt) &&
        decide ((UInt32.ofNat (ns % 1000000000)).toNat < 1000000000)) = true
    rw [hsec, hnsec]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, hrem⟩
  · unfold TimeRand.Timespec.toNanosNat TimeRand.NSEC_PER_SEC
    change (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt.toNat * 1000000000 +
        (UInt32.ofNat (ns % 1000000000)).toNat = ns
    rw [hsec, hnsec]; exact Nat.div_add_mod' ns 1000000000

private theorem tr_ofEpochNanos?_spec (ns : Int) :
    let secInt := ns.ediv (Int.ofNat TimeRand.NSEC_PER_SEC)
    if TimeRand.MIN_TIMESPEC_SEC_INT ≤ secInt ∧ secInt ≤ Int.ofNat TimeRand.MAX_TIMESPEC_SEC then
      ∃ out, TimeRand.Timespec.ofEpochNanos? ns = some out ∧ out.hasValidNsec = true
    else TimeRand.Timespec.ofEpochNanos? ns = none := by
  by_cases h : TimeRand.MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat TimeRand.NSEC_PER_SEC) ∧
      ns.ediv (Int.ofNat TimeRand.NSEC_PER_SEC) ≤ Int.ofNat TimeRand.MAX_TIMESPEC_SEC
  · simp only [h]; unfold TimeRand.Timespec.ofEpochNanos? TimeRand.NSEC_PER_SEC; dsimp only
    have h' : TimeRand.MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat 1000000000) ∧
        ns.ediv (Int.ofNat 1000000000) ≤ Int.ofNat TimeRand.MAX_TIMESPEC_SEC := h
    rw [decide_eq_true h']; simp only [↓reduceIte]
    have hmod0 : 0 ≤ ns.emod (1000000000 : Int) := Int.emod_nonneg ns (by decide)
    have hmod1 : ns.emod (1000000000 : Int) < (1000000000 : Int) := Int.emod_lt_of_pos ns (by decide)
    have hnsec : (UInt32.ofNat (ns.emod (1000000000 : Int)).toNat).toNat =
        (ns.emod (1000000000 : Int)).toNat := u32_toNat_ofNat_lt' (by omega)
    refine ⟨_, rfl, ?_⟩
    unfold TimeRand.Timespec.hasValidNsec TimeRand.NSEC_PER_SEC
    change decide ((UInt32.ofNat (ns.emod (1000000000 : Int)).toNat).toNat < 1000000000) = true
    rw [hnsec]; exact decide_eq_true (by omega)
  · simp only [h]; unfold TimeRand.Timespec.ofEpochNanos? TimeRand.NSEC_PER_SEC; dsimp only
    have h' : ¬(TimeRand.MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat 1000000000) ∧
        ns.ediv (Int.ofNat 1000000000) ≤ Int.ofNat TimeRand.MAX_TIMESPEC_SEC) := h
    rw [decide_eq_false h']; rfl

private theorem tr_entListAux_len (drawIdx rem pos : Nat) (acc : List UInt8) :
    (TimeRand.deterministicEntropyListAux drawIdx rem pos acc).length = acc.length + rem := by
  induction rem generalizing pos acc with
  | zero => simp [TimeRand.deterministicEntropyListAux]
  | succ rem ih => simp only [TimeRand.deterministicEntropyListAux, ih, List.length_cons]; omega

private theorem tr_entBytesAux_sz (drawIdx rem pos : Nat) (acc : ByteArray) :
    (TimeRand.deterministicEntropyBytesAux drawIdx rem pos acc).size = acc.size + rem := by
  induction rem generalizing pos acc with
  | zero => simp [TimeRand.deterministicEntropyBytesAux]
  | succ rem ih => simp only [TimeRand.deterministicEntropyBytesAux, ih, ByteArray.size_push]; omega

private theorem tr_entBytes_sz (drawIdx len : Nat) :
    (TimeRand.deterministicEntropyBytes drawIdx len).size = len := by
  unfold TimeRand.deterministicEntropyBytes
  by_cases h : len ≤ 256
  · simp [h, ByteArray.size, TimeRand.deterministicEntropyList, tr_entListAux_len]
  · simp only [h, ↓reduceIte, tr_entBytesAux_sz]
    have h0 : (ByteArray.emptyWithCapacity len).size = 0 := rfl
    omega

private theorem tr_validGrndLen (len : UInt32) :
    TimeRand.validGetrandomResultLen len (min len.toNat MAX_READ_BYTES.toNat) = true := by
  unfold TimeRand.validGetrandomResultLen
  by_cases h0 : min len.toNat MAX_READ_BYTES.toNat = 0
  · simp [h0]
  · have hgt : 1 ≤ min len.toNat MAX_READ_BYTES.toNat := by omega
    by_cases hle : min len.toNat MAX_READ_BYTES.toNat ≤ TimeRand.GETRANDOM_EXACT_MAX <;> simp [h0, hle, hgt]

private theorem tr_healthyStep_of_core {env : TimeRand.HealthyEnv} {req : TimeRand.TimeRandReq}
    {out : TimeRand.TimeRandOutcome} {s' : TimeRand.TimeRandState}
    (hWf : env.wf = true) (hCore : TimeRand.allowedStepCore env.state req out = some s')
    (hNoCrit : TimeRand.isCriticalFault out = false) (hNoEi : TimeRand.isEintrOutcome out = false) :
    TimeRand.healthyStep env req out = some { env with state := s' } := by
  have hSec : env.state.ambientSeccomp = false := by
    unfold TimeRand.HealthyEnv.wf at hWf
    cases h : env.state.ambientSeccomp <;> simp_all
  unfold TimeRand.healthyStep TimeRand.allowedStep
  simp [hWf, hSec, hCore, hNoCrit, hNoEi]

/-- `healthySimDeps.timeRand` refines canonical `TimeRand.healthyStep` via `projSimTime` and `TimeRand.modelOps`. -/
theorem healthySimDeps_timeRand_refinesHealthy :
    TimeRand.RefinesHealthyTimeRandAt projSimTime healthySimDeps.timeRand := by
  intro s req hWf
  cases req with
  | clock_gettime clk =>
    dsimp only [TimeRand.execTimeRandReq, healthySimDeps, Functor.map, StateT.map, StateT.run,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    cases clk with
    | realtime =>
      let clampTs : TimeRand.Timespec :=
        { sec := if (toSimTimeState s).realtimeNs < 0 then Int64.minValue else Int64.maxValue,
          nsec := if (toSimTimeState s).realtimeNs < 0 then 0 else UInt32.ofNat (TimeRand.NSEC_PER_SEC - 1) }
      have hRun : TimeRand.modelOps.clock_gettime .realtime (toSimTimeState s) =
          match TimeRand.Timespec.ofEpochNanos? (toSimTimeState s).realtimeNs with
          | some ts => (.ok ts, toSimTimeState s)
          | none => (.ok clampTs, toSimTimeState s) := by
        dsimp only [TimeRand.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
          get, MonadState.get, getThe, MonadStateOf.get, StateT.get, clampTs]
        cases TimeRand.Timespec.ofEpochNanos? (toSimTimeState s).realtimeNs <;> rfl
      rw [hRun]
      have hSpec := tr_ofEpochNanos?_spec (toSimTimeState s).realtimeNs; dsimp only at hSpec
      have hId : projSimTime { s with timeState := toSimTimeState s } = projSimTime s := rfl
      split at hSpec
      · obtain ⟨ts, hEq, hVal⟩ := hSpec
        rw [hEq]; dsimp only; rw [hId]; apply tr_healthyStep_of_core hWf _ rfl rfl
        simp [projSimTime, TimeRand.outcomeOfTimespec, TimeRand.allowedStepCore, hVal]
      · rw [hSpec]; dsimp only; rw [hId]; apply tr_healthyStep_of_core hWf _ rfl rfl
        have hVal : clampTs.hasValidNsec = true := by
          unfold TimeRand.Timespec.hasValidNsec TimeRand.NSEC_PER_SEC
          dsimp only [clampTs]
          by_cases hn : (toSimTimeState s).realtimeNs < 0 <;> simp [hn] <;> decide
        simp [projSimTime, TimeRand.outcomeOfTimespec, TimeRand.allowedStepCore, hVal]
    | monotonic =>
      let maxTs : TimeRand.Timespec :=
        { sec := Int64.ofInt (Int.ofNat TimeRand.MAX_TIMESPEC_SEC),
          nsec := UInt32.ofNat (TimeRand.NSEC_PER_SEC - 1) }
      have hRun : TimeRand.modelOps.clock_gettime .monotonic (toSimTimeState s) =
          match TimeRand.Timespec.ofNanosNat? (toSimTimeState s).monoLowerBoundNs with
          | some ts => (.ok ts, { toSimTimeState s with monoLowerBoundNs := ts.toNanosNat })
          | none => (.ok maxTs, toSimTimeState s) := by
        dsimp only [TimeRand.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
          get, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, maxTs]
        cases TimeRand.Timespec.ofNanosNat? (toSimTimeState s).monoLowerBoundNs <;> rfl
      rw [hRun]
      by_cases hm : (toSimTimeState s).monoLowerBoundNs ≤ TimeRand.MAX_TIMESPEC_NANOS
      · obtain ⟨ts, hEq, hVal, hNs⟩ := tr_ofNanosNat?_some hm
        rw [hEq]; dsimp only
        have hProj : projSimTime { s with timeState := { toSimTimeState s with monoLowerBoundNs := ts.toNanosNat } } =
            { projSimTime s with state := { toSimTimeState s with monoLowerBoundNs := ts.toNanosNat } } := rfl
        rw [hProj]; apply tr_healthyStep_of_core hWf _ rfl rfl
        simp [projSimTime, TimeRand.outcomeOfTimespec, TimeRand.allowedStepCore, hVal, hNs, Nat.min_eq_left hm]
      · have hgt := Nat.lt_of_not_le hm
        rw [tr_ofNanosNat?_none hgt]; dsimp only
        have hId : projSimTime { s with timeState := toSimTimeState s } = projSimTime s := rfl
        rw [hId]; apply tr_healthyStep_of_core hWf _ rfl rfl
        have hVal : maxTs.isValid = true := by decide
        have hNs : maxTs.toNanosNat = TimeRand.MAX_TIMESPEC_NANOS := by decide
        dsimp only [projSimTime, TimeRand.outcomeOfTimespec, TimeRand.allowedStepCore]
        rw [hVal, hNs, Nat.min_eq_right (Nat.le_of_lt hgt), Nat.max_eq_left (Nat.le_of_lt hgt)]
        simp only [Bool.true_and]
        cases toSimTimeState s; rfl
  | clock_nanosleep clk abs reqTs =>
    dsimp only [TimeRand.execTimeRandReq, healthySimDeps, Functor.map, StateT.map, StateT.run,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    let nextMono : Nat :=
      if abs then max (toSimTimeState s).monoLowerBoundNs reqTs.toNanosNat
      else max (toSimTimeState s).monoLowerBoundNs
        (min TimeRand.MAX_TIMESPEC_NANOS ((toSimTimeState s).monoLowerBoundNs + reqTs.toNanosNat))
    have hRun : TimeRand.modelOps.clock_nanosleep clk abs reqTs (toSimTimeState s) =
        if !reqTs.isValid then (.error Errno.EINVAL, toSimTimeState s)
        else match clk with
          | .realtime => (.ok (), toSimTimeState s)
          | .monotonic => (.ok (), { toSimTimeState s with monoLowerBoundNs := nextMono }) := by
      dsimp only [TimeRand.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, nextMono]
      cases reqTs.isValid <;> cases clk <;> rfl
    rw [hRun]
    have hId : projSimTime { s with timeState := toSimTimeState s } = projSimTime s := rfl
    cases hv : reqTs.isValid
    · simp only [Bool.not_false, ↓reduceIte, hId]
      apply tr_healthyStep_of_core hWf _ (by decide) (by decide)
      simp [projSimTime, TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases clk with
      | realtime =>
        dsimp only; rw [hId]; apply tr_healthyStep_of_core hWf _ rfl rfl
        simp [projSimTime, TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]
      | monotonic =>
        dsimp only [nextMono]
        have hProj : ∀ m, projSimTime { s with timeState := { toSimTimeState s with monoLowerBoundNs := m } } =
            { projSimTime s with state := { toSimTimeState s with monoLowerBoundNs := m } } := fun _ => rfl
        rw [hProj]; apply tr_healthyStep_of_core hWf _ rfl rfl
        simp [projSimTime, TimeRand.outcomeOfUnit, TimeRand.allowedStepCore, hv]
  | getrandom len flags =>
    dsimp only [TimeRand.execTimeRandReq, healthySimDeps, Functor.map, StateT.map, StateT.run,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    let nextTr : TimeRand.TimeRandState :=
      { toSimTimeState s with
        crngReady := (toSimTimeState s).crngReady || !flags.insecure,
        entropyDraws := (toSimTimeState s).entropyDraws + 1 }
    have hRun : TimeRand.modelOps.getrandom len flags (toSimTimeState s) =
        if flags.isInvalid then (.error Errno.EINVAL, toSimTimeState s)
        else if !(toSimTimeState s).crngReady && flags.nonblock && !flags.insecure then
          (.error Errno.EAGAIN, toSimTimeState s)
        else
          (.ok (TimeRand.deterministicEntropyBytes (toSimTimeState s).entropyDraws (min len.toNat MAX_READ_BYTES.toNat)),
           nextTr) := by
      dsimp only [TimeRand.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, nextTr]
      cases flags.isInvalid <;> cases (toSimTimeState s).crngReady <;>
        cases flags.nonblock <;> cases flags.insecure <;> rfl
    rw [hRun]
    have hId : projSimTime { s with timeState := toSimTimeState s } = projSimTime s := rfl
    by_cases h1 : flags.isInvalid = true
    · simp only [h1, ↓reduceIte, hId]
      apply tr_healthyStep_of_core hWf _ (by decide) (by decide)
      simp [projSimTime, TimeRand.outcomeOfBytes, TimeRand.allowedStepCore, h1]
    · have h1F : flags.isInvalid = false := Bool.eq_false_iff.mpr h1
      simp only [h1F, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (!(toSimTimeState s).crngReady && flags.nonblock && !flags.insecure) = true
      · simp only [h2, ↓reduceIte, hId]
        apply tr_healthyStep_of_core hWf _ (by decide) (by decide)
        simp [projSimTime, TimeRand.outcomeOfBytes, TimeRand.allowedStepCore, h1F, h2]
      · have h2F : (!(toSimTimeState s).crngReady && flags.nonblock && !flags.insecure) = false :=
          Bool.eq_false_iff.mpr h2
        simp only [h2F, Bool.false_eq_true, ↓reduceIte]
        have hProj : projSimTime { s with timeState := nextTr } =
            { projSimTime s with state := nextTr } := rfl
        rw [hProj]; apply tr_healthyStep_of_core hWf _ rfl rfl
        have hLen : TimeRand.validGetrandomResultLen len
            (TimeRand.deterministicEntropyBytes (toSimTimeState s).entropyDraws (min len.toNat MAX_READ_BYTES.toNat)).size = true := by
          rw [tr_entBytes_sz]; exact tr_validGrndLen len
        simp [projSimTime, TimeRand.outcomeOfBytes, TimeRand.allowedStepCore, h1F, hLen, nextTr]

/-- `healthySimDeps.postFork` satisfies `RefinesHealthyPostFork`. -/
theorem healthySimDeps_postFork_refinesHealthy :
    RefinesHealthyPostFork healthySimDeps.postFork where
  spawn_healthy s spec := by
    dsimp only [healthySimDeps, stateM_modifyGet_run]
    refine ⟨?_, (by intro _ h; cases h)⟩
    intro child hEq
    injection hEq with hC
    rw [← hC]
    exact ⟨by decide, by decide, fun _ => rfl⟩

/-- `healthySimDeps` satisfies `RefinesHealthySysDeps` via `refinesHealthySysDeps_of_components` (deriving `close` FD erasure directly from canonical `Files.healthyStep`). -/
theorem healthySimDeps_refinesHealthy :
    RefinesHealthySysDeps
      (fun s : HealthySimState => s.tbl)
      (fun s t => { s with tbl := t })
      (fun s => (projSimFiles s).state.fds.map Prod.fst)
      healthySimDeps := by
  apply refinesHealthySysDeps_of_components
    (fun s : HealthySimState => s.tbl)
    (fun s t => { s with tbl := t })
    projSimProc
    projSimFiles
    projSimTime
    healthySimDeps
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · exact healthySimDeps_proc_refinesHealthy
  · exact healthySimDeps_files_refinesHealthy
  · exact healthySimDeps_timeRand_refinesHealthy
  · exact healthySimDeps_postFork_refinesHealthy
  · intro _ _; rfl
  · intro _ _; rfl
  · intro s flags
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, toSimFilesState]
    by_cases hVal : flags.isValid = true
    · by_cases hNotif : flags.notificationPipe = true
      · refine ⟨?_, ?_, ?_⟩
        · simp [hVal, hNotif]
        · intro _ _; simp [hVal, hNotif]
        · intro _ _ h; simp [hVal, hNotif] at h
      · have hNotifF : flags.notificationPipe = false := Bool.eq_false_iff.mpr hNotif
        refine ⟨?_, ?_, ?_⟩
        · simp [hVal, hNotifF]
        · intro _ h; simp [hVal, hNotifF] at h
        · intro rf wf hEq
          simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotifF] at hEq ⊢
          injection hEq with hSub
          injection hSub with hR hW
          subst hR hW
          have hSimLe : maxKey s.simFds 10 ≤ Nat.max (maxKey s.procFds s.procNextHid) (maxKey s.simFds 10) :=
            Nat.le_max_right _ _
          have hMapFst : ∀ ys : List (Files.HandleId × HealthySimFd),
              (ys.map (fun (k, d) => (k, toSimOpenDesc d))).map Prod.fst = ys.map Prod.fst := by
            intro ys; induction ys with
            | nil => rfl
            | cons hd tl ih => rcases hd with ⟨k, d⟩; simp [ih]
          rw [hMapFst]
          refine ⟨?_, ?_, ?_, by simp [hMapFst]⟩
          · intro hEqRW
            exact Nat.succ_ne_self _ hEqRW.symm
          · intro hMem
            have hLe := mem_fst_le_maxKey s.simFds 10 _ hMem
            exact Nat.not_le_of_gt (Nat.lt_succ_of_le hSimLe) hLe
          · intro hMem
            have hLe := mem_fst_le_maxKey s.simFds 10 _ hMem
            exact Nat.not_le_of_gt (Nat.lt_succ_of_le (Nat.le_succ_of_le hSimLe)) hLe
    · have hValF : flags.isValid = false := Bool.eq_false_iff.mpr hVal
      refine ⟨?_, ?_, ?_⟩
      · simp [hValF]
      · intro _ _; simp [hValF]
      · intro _ _ h; simp [hValF] at h
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · intro s hid
    dsimp only [healthySimDeps, stateM_modifyGet_run]
    cases Files.assocGet s.simFds hid <;> rfl
  · intro s hid cap
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, toSimFilesState]
    cases hGet : Files.assocGet s.simFds hid with
    | none => exact ⟨rfl, rfl⟩
    | some d =>
      dsimp only
      split
      · exact ⟨rfl, rfl⟩
      · split
        · split <;> exact ⟨rfl, rfl⟩
        · split
          · exact ⟨rfl, rfl⟩
          · refine ⟨rfl, ?_⟩
            have hMapFst : ∀ ys : List (Files.HandleId × HealthySimFd),
                (ys.map (fun (k, v) => (k, toSimOpenDesc v))).map Prod.fst = ys.map Prod.fst := by
              intro ys; induction ys with
              | nil => rfl
              | cons hd tl ih => rcases hd with ⟨k, v⟩; simp [ih]
            rw [hMapFst, hMapFst]
            have hMem : hid ∈ s.simFds.map Prod.fst := by
              apply Classical.byContradiction
              intro hNotMem
              have hNone := (assocGet_none_iff_not_mem_fst s.simFds hid).mpr hNotMem
              rw [hGet] at hNone
              cases hNone
            exact map_fst_assocSet_of_mem s.simFds hid _ hMem
  · intro s hid data
    dsimp only [healthySimDeps, stateM_modifyGet_run]
    cases Files.assocGet s.simFds hid with
    | none => exact ⟨rfl, rfl⟩
    | some d =>
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
  · intro _ _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _ _ _ _; exact ⟨rfl, rfl⟩
  · intro s hid cmd
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, toSimFilesState]
    have hMapFst : ∀ ys : List (Files.HandleId × HealthySimFd),
        (ys.map (fun (k, v) => (k, toSimOpenDesc v))).map Prod.fst = ys.map Prod.fst := by
      intro ys; induction ys with
      | nil => rfl
      | cons hd tl ih => rcases hd with ⟨k, v⟩; simp [ih]
    cases hGet : Files.assocGet s.simFds hid with
    | none => exact ⟨rfl, rfl⟩
    | some d =>
      have hMem : hid ∈ s.simFds.map Prod.fst := by
        apply Classical.byContradiction
        intro hNotMem
        have hNone := (assocGet_none_iff_not_mem_fst s.simFds hid).mpr hNotMem
        rw [hGet] at hNone
        cases hNone
      cases cmd with
      | getFl | getFd => exact ⟨rfl, rfl⟩
      | setFl _ _ | setFd _ =>
        refine ⟨rfl, ?_⟩
        rw [hMapFst, hMapFst]
        exact map_fst_assocSet_of_mem s.simFds hid _ hMem
      | addSeals _ =>
        dsimp only
        repeat (first | exact ⟨rfl, rfl⟩ | split)
      | getSeals =>
        dsimp only
        split <;> exact ⟨rfl, rfl⟩
  · intro s entries to
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, toSimFilesState]
    split
    · exact ⟨rfl, rfl, by intro _ h; cases h⟩
    · cases to <;> exact ⟨rfl, rfl, by intro _ h; cases h⟩
  · intro _ _; exact ⟨rfl, rfl⟩
  · intro _ _ _ _; exact ⟨rfl, rfl⟩
  · intro s spec
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimFiles, toSimFilesState]
    refine ⟨rfl, ?_⟩
    suffices ∀ (ys : List (Files.HandleId × HealthySimFd)) (f : Files.HandleId × HealthySimFd → HealthySimFd),
        ((ys.map (fun x => (x.1, f x))).map (fun (k, d) => (k, toSimOpenDesc d))).map Prod.fst =
          (ys.map (fun (k, d) => (k, toSimOpenDesc d))).map Prod.fst from
      this s.simFds _
    intro ys f
    induction ys with
    | nil => rfl
    | cons hd tl ih => rcases hd with ⟨k, d⟩; simp only [List.map_cons]; exact congrArg (k :: ·) ih
  · intro _; exact ⟨rfl, rfl, (by intro _ h; cases h)⟩

end LeanSwe.Process.Proofs

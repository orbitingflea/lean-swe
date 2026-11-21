import LeanSwe.Process.Proofs.HealthySimBase
import LeanSwe.Process.Proofs.HealthySimFiles

/-!
# Assembled `healthyStep` Simulation Witness for `LeanSwe.Process.SysBridge`

Combines `Process`, `Files`, `TimeRand`, and `PostFork` healthy-step refinements via
`refinesHealthySysDeps_of_components` to witness `RefinesHealthySysDeps`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

@[simp] private theorem stateM_modifyGet_run {S α : Type} (f : S → α × S) (s : S) :
    (modifyGet f : StateM S α).run s = f s := rfl

/-- `healthySimDeps.timeRand` refines `healthyTimeRandStep` via `projSimTime` and `TimeRand.modelOps`. -/
theorem healthySimDeps_timeRand_refinesHealthy :
    RefinesHealthyTimeRandAt projSimTime healthySimDeps.timeRand where
  clock_gettime_healthy s clk _ := by
    have hSound : TimeRand.allowedStep (toSimTimeState s) (.clock_gettime clk)
        (TimeRand.outcomeOfTimespec ((TimeRand.modelOps.clock_gettime clk).run (toSimTimeState s)).1) =
        some ((TimeRand.modelOps.clock_gettime clk).run (toSimTimeState s)).2 :=
      (TimeRand.Proofs.proof_timerand_modelOps_soundAgainstAllowedStep
        (toSimTimeState s) clk false {} 0 {}).1
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimTime]
    cases hRun : (TimeRand.modelOps.clock_gettime clk).run (toSimTimeState s) with
    | mk res ts' =>
      rw [hRun] at hSound
      dsimp only at hSound ⊢
      have hRunUnf := hRun
      unfold TimeRand.modelOps StateT.run at hRunUnf
      dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set] at hRunUnf
      have hProps : ts'.ambientSeccomp = false ∧ (∀ code, TimeRand.outcomeOfTimespec res = .err code → False) := by
        cases clk with
        | realtime =>
          dsimp only at hRunUnf
          cases hEp : TimeRand.Timespec.ofEpochNanos? (toSimTimeState s).realtimeNs <;>
            (rw [hEp] at hRunUnf; dsimp only [StateT.pure, Pure.pure] at hRunUnf;
             injection hRunUnf with hR hS; rw [← hR, ← hS]; exact ⟨rfl, fun _ hc => by cases hc⟩)
        | monotonic =>
          dsimp only at hRunUnf
          cases hMn : TimeRand.Timespec.ofNanosNat? (toSimTimeState s).monoLowerBoundNs with
          | none =>
            rw [hMn] at hRunUnf; dsimp only [StateT.pure, Pure.pure] at hRunUnf
            injection hRunUnf with hR hS; rw [← hR, ← hS]; exact ⟨rfl, fun _ hc => by cases hc⟩
          | some ts =>
            rw [hMn] at hRunUnf; dsimp only [StateT.bind, StateT.pure, StateT.set, Bind.bind, Pure.pure] at hRunUnf
            injection hRunUnf with hR hS; rw [← hR, ← hS]; exact ⟨rfl, fun _ hc => by cases hc⟩
      obtain ⟨hSec', hNoErr⟩ := hProps
      have hToEq : toSimTimeState { s with timeState := ts' } = ts' := by
        cases ts'; simp [toSimTimeState] at hSec' ⊢; exact hSec'
      refine ⟨?_, rfl⟩
      unfold healthyTimeRandStep
      have hSec0 : (toSimTimeState s).ambientSeccomp = false := rfl
      rw [hSec0, hSound, hToEq]
      cases hOut : TimeRand.outcomeOfTimespec res with
      | timespec _ | unit | bytes _ => rfl
      | err code => exact False.elim (hNoErr code hOut)
  clock_nanosleep_healthy s clk abs req _ := by
    have hSound : TimeRand.allowedStep (toSimTimeState s) (.clock_nanosleep clk abs req)
        (TimeRand.outcomeOfUnit ((TimeRand.modelOps.clock_nanosleep clk abs req).run (toSimTimeState s)).1) =
        some ((TimeRand.modelOps.clock_nanosleep clk abs req).run (toSimTimeState s)).2 :=
      (TimeRand.Proofs.proof_timerand_modelOps_soundAgainstAllowedStep
        (toSimTimeState s) clk abs req 0 {}).2.1
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimTime]
    cases hRun : (TimeRand.modelOps.clock_nanosleep clk abs req).run (toSimTimeState s) with
    | mk res ts' =>
      rw [hRun] at hSound
      dsimp only at hSound ⊢
      have hRunUnf := hRun
      unfold TimeRand.modelOps StateT.run at hRunUnf
      dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set] at hRunUnf
      by_cases hVal : req.isValid = true
      · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRunUnf
        have hSec' : ts'.ambientSeccomp = false := by
          cases clk <;>
            (dsimp only [StateT.bind, StateT.pure, StateT.set, Bind.bind, Pure.pure] at hRunUnf;
             injection hRunUnf with _ hS; rw [← hS]; rfl)
        have hOk : res = .ok () := by
          cases clk <;>
            (dsimp only [StateT.bind, StateT.pure, StateT.set, Bind.bind, Pure.pure] at hRunUnf;
             injection hRunUnf with hR _; exact hR.symm)
        subst hOk
        have hToEq : toSimTimeState { s with timeState := ts' } = ts' := by
          cases ts'; simp [toSimTimeState] at hSec' ⊢; exact hSec'
        refine ⟨?_, rfl⟩
        unfold healthyTimeRandStep
        have hSec0 : (toSimTimeState s).ambientSeccomp = false := rfl
        rw [hSec0]
        dsimp only [Bool.false_eq_true, ↓reduceIte, TimeRand.outcomeOfUnit] at hSound ⊢
        rw [hSound, hToEq]
        rfl
      · have hValF : req.isValid = false := Bool.eq_false_iff.mpr hVal
        simp only [hValF, Bool.not_false, ↓reduceIte] at hRunUnf
        dsimp only [StateT.pure, Pure.pure] at hRunUnf
        injection hRunUnf with hR hS
        subst hR hS
        refine ⟨?_, rfl⟩
        unfold healthyTimeRandStep
        have hSec0 : (toSimTimeState s).ambientSeccomp = false := rfl
        rw [hSec0]
        dsimp only [TimeRand.outcomeOfUnit] at hSound ⊢
        rw [hSound]
        simp [toSimTimeState, isCriticalOsErrno, Errno.EINVAL, Errno.EINTR,
          Errno.ENOMEM, Errno.EIO, Errno.ENFILE]

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

/-- `healthySimDeps` satisfies `RefinesHealthySysDeps` via `refinesHealthySysDeps_of_components` (deriving `close` FD erasure directly from canonical `healthyFilesStep`). -/
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

/-- `RawProcessOpsM (StateM HealthySimState)` constructed through `SysBridge.mkRawOpsM` over genuine `healthySimDeps`. -/
def healthySimRawOps : RawProcessOpsM (StateM HealthySimState) :=
  SysBridge.mkRawOpsM healthySimDeps
    (SysBridge.stateProcTableOps (fun s => s.tbl) (fun s t => { s with tbl := t }))
    4 8

end LeanSwe.Process.Proofs

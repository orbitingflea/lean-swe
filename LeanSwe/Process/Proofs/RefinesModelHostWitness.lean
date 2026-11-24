import Core.Refines
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.Model.HealthySim
import LeanSwe.Process.Proofs.HealthySim

/-!
# Concrete Healthy-OS Capability Witness for `LeanSwe.Process.Model.HealthyHost`

Provides `healthySimHostCaps` over `HealthySimState` and proves
`healthySimHostCaps_refines_allowedHostCapStep`, witnessing non-vacuity of the
end-to-end `Impl + SysBridge` capability contract `Model.allowedHostCapStep`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

/-- Project `HealthySimState` into public `Model.ProcessHostWorld`. -/
def projSimToHostWorld (s : Model.Internal.HealthySimState) : Model.ProcessHostWorld :=
  { proc := projSimProc s
    files := projSimFiles s
    time := projSimTime s
    ambientEnv := #["PATH=/bin:/usr/bin".toUTF8]
    tbl := s.tbl }

/-- Concrete `Model.HealthyHostCapsM` witness backed by `healthySimDeps` over `HealthySimState`. -/
def healthySimHostCaps : Model.HealthyHostCapsM (StateM Model.Internal.HealthySimState) where
  proc := healthySimDeps.proc
  files := healthySimDeps.files
  poll := healthySimDeps.poll
  timeRand := healthySimDeps.timeRand
  postFork := healthySimDeps.postFork
  listEnvironBytes := pure #["PATH=/bin:/usr/bin".toUTF8]
  table := Model.stateHostTableOps Model.Internal.HealthySimState.tbl (fun s t => { s with tbl := t })

private theorem except_map_id_pair {ε α β : Type} (x : Except ε (α × β)) :
    x.map (fun p => (id p.1, id p.2)) = x := by
  cases x <;> rfl

private theorem map_fst_pres {α β : Type} (xs : List (α × β)) (g : α × β → α × β)
    (hg : ∀ x, (g x).1 = x.1) :
    (xs.map g).map Prod.fst = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, hg, ih]

private theorem map_hostSlotToEntry_fst (xs : List (Nat × Model.ProcSlotM Files.HandleId)) :
    (xs.map Model.hostSlotToEntry).map (·.handleId) = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨k, v⟩; simp [Model.hostSlotToEntry, ih]

private theorem removeHostSlotList_mem {fd : Type} (hid : Nat) (xs : List (Nat × Model.ProcSlotM fd))
    (p : Nat × Model.ProcSlotM fd) (hp : p ∈ (Model.removeHostSlotList hid xs).2) :
    p ∈ xs := by
  induction xs with
  | nil => simp [Model.removeHostSlotList] at hp
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold Model.removeHostSlotList at hp
    by_cases hEq : (k == hid) = true
    · rw [ite_eq_left hEq] at hp
      exact List.mem_cons_of_mem _ hp
    · rw [ite_eq_right hEq] at hp
      dsimp only at hp
      simp only [List.mem_cons] at hp ⊢
      rcases hp with rfl | hTl
      · exact Or.inl rfl
      · exact Or.inr (ih hTl)

private theorem hasNoDupHandleIds_remove {fd : Type} (hid : Nat)
    (xs : List (Nat × Model.ProcSlotM fd))
    (hNoDup : Model.hasNoDupHandleIds (xs.map Prod.fst) = true) :
    Model.hasNoDupHandleIds ((Model.removeHostSlotList hid xs).2.map Prod.fst) = true := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true'] at hNoDup
    unfold Model.removeHostSlotList
    by_cases hEq : (k == hid) = true
    · rw [ite_eq_left hEq]
      exact hNoDup.2
    · rw [ite_eq_right hEq]
      dsimp only
      simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, ih hNoDup.2⟩
      rw [Bool.eq_false_iff]
      intro hCont
      have hMemFst : k ∈ (Model.removeHostSlotList hid tl).2.map Prod.fst := List.contains_iff_mem.mp hCont
      rcases List.mem_map.mp hMemFst with ⟨⟨k', v'⟩, hp, hk⟩
      dsimp only at hk
      subst hk
      have hpTl := removeHostSlotList_mem hid tl (k', v') hp
      have hMemTl : k' ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k', v'), hpTl, rfl⟩
      have hContTl : (tl.map Prod.fst).contains k' = true := List.contains_iff_mem.mpr hMemTl
      rw [hContTl] at hNoDup
      cases hNoDup.1

private theorem hostWorldWf_of_tbl {w : Model.ProcessHostWorld}
    (hProc : w.proc.wf = true) (hFiles : w.files.wf = true) (hTime : w.time.wf = true)
    (hSlots : w.tbl.slots.all (fun p => Model.hostSlotWf p.2) = true)
    (hNext : w.tbl.nextId ≥ 1)
    (hNoDup : Model.hasNoDupHandleIds (w.tbl.slots.map Prod.fst) = true)
    (hLt : ∀ p ∈ w.tbl.slots, p.1 < w.tbl.nextId) :
    Model.hostWorldWf w = true := by
  unfold Model.hostWorldWf Model.processStateWf Model.hostWorldToProcessState
  simp only [hProc, hFiles, hTime, hSlots, Bool.and_true, Bool.true_and,
    map_hostSlotToEntry_fst, hNoDup]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map]
  refine ⟨hNext, ?_⟩
  intro e ⟨p, hp, he⟩
  subst he
  have hpWf : Model.hostSlotWf p.2 = true := (List.all_eq_true.mp hSlots) p hp
  unfold Model.hostSlotWf at hpWf
  simp only [decide_eq_true_eq] at hpWf
  have hPidPos : (1 : Nat) ≤ p.2.pid.toNat := hpWf.1
  have hPgidPos : (1 : Nat) ≤ p.2.pgid.toNat := hpWf.2.2.1
  exact ⟨⟨hLt p hp, by simpa [Model.hostSlotToEntry] using Int.ofNat_lt.mpr hPidPos⟩,
    by simpa [Model.hostSlotToEntry] using Int.ofNat_lt.mpr hPgidPos⟩

private theorem hostWorldWf_elim_tbl {w : Model.ProcessHostWorld}
    (hWf : Model.hostWorldWf w = true) :
    w.proc.wf = true ∧
    w.files.wf = true ∧
    w.time.wf = true ∧
    w.tbl.slots.all (fun p => Model.hostSlotWf p.2) = true ∧
    w.tbl.nextId ≥ 1 ∧
    Model.hasNoDupHandleIds (w.tbl.slots.map Prod.fst) = true ∧
    ∀ p ∈ w.tbl.slots, p.1 < w.tbl.nextId := by
  unfold Model.hostWorldWf Model.processStateWf Model.hostWorldToProcessState at hWf
  simp only [Bool.and_eq_true, map_hostSlotToEntry_fst, decide_eq_true_eq] at hWf
  obtain ⟨⟨⟨⟨hProc, hFiles⟩, hTime⟩, hSlots⟩, ⟨hNext, hNoDup⟩, hAll⟩ := hWf
  refine ⟨hProc, hFiles, hTime, hSlots, hNext, hNoDup, ?_⟩
  intro p hp
  have hE := (List.all_eq_true.mp hAll) (Model.hostSlotToEntry p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  simp only [decide_eq_true_eq] at hE
  exact hE.1.1

private theorem simWorlds_wf (s : Model.Internal.HealthySimState) :
    (projSimProc s).wf = true ∧ (projSimFiles s).wf = true ∧ (projSimTime s).wf = true :=
  ⟨rfl, rfl, rfl⟩

private theorem hostWorldWf_simTbl_eq (s s' : Model.Internal.HealthySimState)
    (hTbl : s'.tbl = s.tbl) (hWf : Model.hostWorldWf (projSimToHostWorld s) = true) :
    Model.hostWorldWf (projSimToHostWorld s') = true := by
  obtain ⟨_, _, _, hSlots, hNext, hNoDup, hLt⟩ := hostWorldWf_elim_tbl hWf
  obtain ⟨hP, hF, hT⟩ := simWorlds_wf s'
  apply hostWorldWf_of_tbl hP hF hT
  · simpa [projSimToHostWorld, hTbl] using hSlots
  · simpa [projSimToHostWorld, hTbl] using hNext
  · simpa [projSimToHostWorld, hTbl] using hNoDup
  · intro p hp
    simp only [projSimToHostWorld, hTbl] at hp ⊢
    exact hLt p hp

/-- Genuine witness proving `healthySimHostCaps` refines `Model.allowedHostCapStep` under `Model.hostWorldWf`. -/
theorem healthySimHostCaps_refines_allowedHostCapStep :
    Core.RefinesStep projSimToHostWorld Model.hostWorldWf
      (Model.execHostCapStep healthySimHostCaps) Model.allowedHostCapStep := by
  intro s req hWf
  cases req with
  | proc pr =>
    dsimp only [Model.execHostCapStep, Model.allowedHostCapStep, Function.comp]
    cases pr with
    | pipe2 flags =>
      have hP := healthySimDeps_proc_refinesHealthy.pipe2_healthy s flags rfl
      dsimp only [healthySimHostCaps, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hP ⊢
      cases hRun : healthySimDeps.proc.pipe2 flags s with
      | mk res s' =>
        dsimp only
        rw [hRun, except_map_id_pair] at hP
        have hTblEq : s'.tbl = s.tbl := by
          dsimp only [healthySimDeps] at hRun
          split at hRun
          · injection hRun with _ hS'; rw [← hS']
          · split at hRun
            · injection hRun with _ hS'; rw [← hS']
            · injection hRun with _ hS'; rw [← hS']
        have hTimeEq : projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps] at hRun
          split at hRun
          · injection hRun with _ hS'; rw [← hS']
          · split at hRun
            · injection hRun with _ hS'; rw [← hS']
            · injection hRun with _ hS'; rw [← hS']; rfl
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hTblEq hWf, hP, hTimeEq, rfl, by simp [projSimToHostWorld, hTblEq]⟩
    | waitpid pid flags =>
      have hP := healthySimDeps_proc_refinesHealthy.waitpid_healthy s pid flags rfl
      dsimp only [healthySimHostCaps, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hP ⊢
      cases hRun : healthySimDeps.proc.waitpid pid flags s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hP
        have hTblEq : s'.tbl = s.tbl := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']
        have hTimeEq : projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']; rfl
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hTblEq hWf, hP, hTimeEq, rfl, by simp [projSimToHostWorld, hTblEq]⟩
    | kill target sig =>
      have hP := healthySimDeps_proc_refinesHealthy.kill_healthy s target sig rfl
      dsimp only [healthySimHostCaps, Model.HostProcReq.toProcessReq, LinuxSyscall.Process.execProcessReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hP ⊢
      cases hRun : healthySimDeps.proc.kill target sig s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hP
        have hTblEq : s'.tbl = s.tbl := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']
        have hTimeEq : projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hTblEq hWf, hP, hTimeEq, rfl, by simp [projSimToHostWorld, hTblEq]⟩
  | files fr =>
    dsimp only [Model.execHostCapStep, Model.allowedHostCapStep, Function.comp]
    cases fr with
    | close hid =>
      have hF := healthySimDeps_files_refinesHealthy.close_healthy s hid rfl
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.close hid s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          cases hGet : Files.assocGet s.simFds hid <;>
            (rw [hGet] at hRun; dsimp only at hRun; injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩)
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hF, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1], (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | read hid cap =>
      have hF := healthySimDeps_files_refinesHealthy.read_healthy s hid cap rfl
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.read hid cap s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          cases hGet : Files.assocGet s.simFds hid with
          | none => rw [hGet] at hRun; dsimp only at hRun; injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
          | some d =>
            rw [hGet] at hRun; dsimp only at hRun
            repeat (first | (injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩) | split at hRun)
        refine ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hF.1, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1], ?_, (fun _ _ _ h => by cases h)⟩
        intro hid' cap' bs hReq hOut
        injection hReq with hHid hCap
        subst hHid hCap
        cases res with
        | error e => cases hOut
        | ok bs' =>
          injection hOut with hBs
          subst hBs
          exact hF.2 bs' rfl
    | write hid data =>
      have hF := healthySimDeps_files_refinesHealthy.write_healthy s hid data rfl
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.write hid data s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          cases hGet : Files.assocGet s.simFds hid with
          | none => rw [hGet] at hRun; dsimp only at hRun; injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
          | some d => rw [hGet] at hRun; dsimp only at hRun; split at hRun <;> (injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩)
        refine ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hF.1, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1], (fun _ _ _ h => by cases h), ?_⟩
        intro hid' data' n hReq hOut
        injection hReq with hHid hData
        subst hHid hData
        cases res with
        | error e => cases hOut
        | ok n' =>
          injection hOut with hN
          subst hN
          exact hF.2 n' rfl
    | fstatat dir path flags =>
      have hF := healthySimDeps_files_refinesHealthy.fstatat_healthy s dir path flags rfl
      have hMap : Option.map id dir = dir := by cases dir <;> rfl
      rw [hMap] at hF
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.fstatat dir path flags s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hEq : s' = s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; exact hS'.symm
        subst hEq
        exact ⟨hWf, fun _ => hWf, hF, rfl, rfl, rfl, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | faccessat dir path mask flags =>
      have hF := healthySimDeps_files_refinesHealthy.faccessat_healthy s dir path mask flags rfl
      have hMap : Option.map id dir = dir := by cases dir <;> rfl
      rw [hMap] at hF
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.faccessat dir path mask flags s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hEq : s' = s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; exact hS'.symm
        subst hEq
        exact ⟨hWf, fun _ => hWf, hF, rfl, rfl, rfl, rfl, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    | fcntl hid cmd =>
      have hF := healthySimDeps_files_refinesHealthy.fcntl_healthy s hid cmd rfl
      dsimp only [healthySimHostCaps, Model.HostFilesReq.toFilesReq, LinuxSyscall.Files.execFilesReq,
        Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run] at hF ⊢
      cases hRun : healthySimDeps.files.fcntl hid cmd s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hF
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimTime s' = projSimTime s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          cases hGet : Files.assocGet s.simFds hid with
          | none => rw [hGet] at hRun; dsimp only at hRun; injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
          | some d => rw [hGet] at hRun; dsimp only at hRun; cases cmd <;> repeat (first | (injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩) | split at hRun)
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hF, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1], (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
  | poll entries timeout? =>
    dsimp only [Model.execHostCapStep, healthySimHostCaps, healthySimDeps,
      Model.allowedHostCapStep, Functor.map, StateT.map, Pure.pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
    split
    · exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, by simp only [Array.size_map]⟩
    · cases timeout? with
      | none => exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, by simp only [Array.size_map]⟩
      | some ts =>
        cases hNs : TimeRand.modelOps.clock_nanosleep TimeRand.ClockId.monotonic false
          { sec := ts.sec, nsec := ts.nsec } (toSimTimeState s) with
        | mk _ ts' =>
          dsimp only
          rw [hNs]
          exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s _ rfl hWf, rfl, rfl, rfl, rfl, by simp only [Array.size_map]⟩
  | timeRand tr =>
    have hT := healthySimDeps_timeRand_refinesHealthy s tr rfl
    dsimp only [Model.execHostCapStep, healthySimHostCaps, Model.allowedHostCapStep]
    cases tr with
    | clock_gettime clk =>
      dsimp only [LinuxSyscall.TimeRand.execTimeRandReq, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at hT ⊢
      cases hRun : healthySimDeps.timeRand.clock_gettime clk s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hT
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimFiles s' = projSimFiles s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hT, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1]⟩
    | clock_nanosleep clk abs reqTs =>
      dsimp only [LinuxSyscall.TimeRand.execTimeRandReq, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at hT ⊢
      cases hRun : healthySimDeps.timeRand.clock_nanosleep clk abs reqTs s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hT
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimFiles s' = projSimFiles s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hT, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1]⟩
    | getrandom len flags =>
      dsimp only [LinuxSyscall.TimeRand.execTimeRandReq, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at hT ⊢
      cases hRun : healthySimDeps.timeRand.getrandom len flags s with
      | mk res s' =>
        dsimp only
        rw [hRun] at hT
        have hSEq : s'.tbl = s.tbl ∧ projSimProc s' = projSimProc s ∧ projSimFiles s' = projSimFiles s := by
          dsimp only [healthySimDeps, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            Pure.pure, StateT.pure] at hRun
          injection hRun with _ hS'; rw [← hS']; exact ⟨rfl, rfl, rfl⟩
        exact ⟨hWf, fun _ => hostWorldWf_simTbl_eq s s' hSEq.1 hWf, hT, hSEq.2.1, hSEq.2.2, rfl,
          by simp [projSimToHostWorld, hSEq.1]⟩
  | postFork spec =>
    dsimp only [Model.execHostCapStep, healthySimHostCaps, healthySimDeps,
      Model.allowedHostCapStep, Functor.map, StateT.map, Pure.pure, StateT.pure,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
    refine ⟨hWf, fun _ => hostWorldWf_simTbl_eq s _ rfl hWf, rfl, rfl, rfl, ?_⟩
    exact ⟨by decide, by decide, fun _ => rfl⟩
  | listAmbientEnv =>
    dsimp only [Model.execHostCapStep, healthySimHostCaps, Model.allowedHostCapStep,
      Functor.map, StateT.map, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, fun _ => hWf, rfl, rfl⟩
  | table tr =>
    obtain ⟨_, _, _, hSlots, hNext, hNoDup, hLt⟩ := hostWorldWf_elim_tbl hWf
    dsimp only [Model.execHostCapStep, healthySimHostCaps, Model.execHostTableReq,
      Model.stateHostTableOps, Model.allowedHostCapStep, Model.allowedHostTableStep,
      Functor.map, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
      modifyGet, MonadStateOf.modifyGet, StateT.run]
    cases tr with
    | insertSlot slot =>
      dsimp only [Model.insertHostSlotPure]
      try unfold StateT.map
      try unfold StateT.modifyGet
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure]
      refine ⟨hWf, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      intro hReqWf
      have hSlot : Model.hostSlotWf slot = true := hReqWf
      obtain ⟨hP, hF, hT⟩ := simWorlds_wf s
      apply hostWorldWf_of_tbl hP hF hT
      · simp only [projSimToHostWorld, List.all_cons, Bool.and_eq_true]
        exact ⟨hSlot, by simpa [projSimToHostWorld] using hSlots⟩
      · simp only [projSimToHostWorld]
        omega
      · simp only [projSimToHostWorld, List.map_cons, Model.hasNoDupHandleIds,
          Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨?_, by simpa [projSimToHostWorld] using hNoDup⟩
        rw [Bool.eq_false_iff]
        intro hCont
        have hMem : s.tbl.nextId ∈ s.tbl.slots.map Prod.fst :=
          List.contains_iff_mem.mp hCont
        rcases List.mem_map.mp hMem with ⟨p, hp, hEq⟩
        have hP := hLt p hp
        dsimp only [projSimToHostWorld] at hP
        omega
      · intro p hp
        simp only [projSimToHostWorld, List.mem_cons] at hp ⊢
        rcases hp with rfl | hpRest
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hLt p (by simpa [projSimToHostWorld] using hpRest))
    | takeSlotIo hid =>
      dsimp only [Model.takeHostSlotIoPure]
      try unfold StateT.map
      try unfold StateT.modifyGet
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure, projSimToHostWorld]
      cases hFind : Model.findHostSlotPure hid s.tbl.slots with
      | none =>
        dsimp only
        exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some slot =>
        dsimp only
        refine ⟨hWf, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        intro _
        obtain ⟨hP, hF, hT⟩ := simWorlds_wf s
        apply hostWorldWf_of_tbl hP hF hT
        · simp only [List.all_eq_true]
          intro p hp
          rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
          have hvWf : Model.hostSlotWf v = true :=
            (List.all_eq_true.mp hSlots) (k, v) (by simpa [projSimToHostWorld] using hkv)
          by_cases hEq : (k == hid) = true
          · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; simpa [Model.hostSlotWf] using hvWf
          · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hvWf
        · exact hNext
        · rw [map_fst_pres _ _ (fun x => by by_cases h : (x.1 == hid) = true <;> simp [h])]
          exact hNoDup
        · intro p hp
          rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, rfl⟩
          have hkLt : k < s.tbl.nextId := hLt (k, v) (by simpa [projSimToHostWorld] using hkv)
          by_cases hEq : (k == hid) = true
          · simp only [hEq, ↓reduceIte]; exact hkLt
          · simp only [hEq, Bool.false_eq_true, ↓reduceIte]; exact hkLt
    | markWaited hid waited =>
      dsimp only [Model.markHostWaitedPure]
      try unfold StateT.map
      try unfold StateT.modifyGet
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure, projSimToHostWorld]
      cases hFind : Model.findHostSlotPure hid s.tbl.slots with
      | none =>
        dsimp only
        exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some slot =>
        dsimp only
        refine ⟨hWf, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        intro _
        obtain ⟨hP, hF, hT⟩ := simWorlds_wf s
        apply hostWorldWf_of_tbl hP hF hT
        · simp only [List.all_eq_true]
          intro p hp
          rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, hpEq⟩
          have hvWf : Model.hostSlotWf v = true :=
            (List.all_eq_true.mp hSlots) (k, v) (by simpa [projSimToHostWorld] using hkv)
          by_cases hEq : (k == hid) = true
          · rw [ite_eq_left hEq] at hpEq; rw [← hpEq]; simpa [Model.hostSlotWf] using hvWf
          · rw [ite_eq_right hEq] at hpEq; rw [← hpEq]; exact hvWf
        · exact hNext
        · rw [map_fst_pres _ _ (fun x => by by_cases h : (x.1 == hid) = true <;> simp [h])]
          exact hNoDup
        · intro p hp
          rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, rfl⟩
          have hkLt : k < s.tbl.nextId := hLt (k, v) (by simpa [projSimToHostWorld] using hkv)
          by_cases hEq : (k == hid) = true
          · simp only [hEq, ↓reduceIte]; exact hkLt
          · simp only [hEq, Bool.false_eq_true, ↓reduceIte]; exact hkLt
    | lookupPgid hid =>
      try unfold StateT.map
      try unfold StateT.bind
      try unfold StateT.get
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure]
      exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | detachSlot hid =>
      dsimp only [Model.detachHostSlotPure]
      try unfold StateT.map
      try unfold StateT.modifyGet
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure]
      refine ⟨hWf, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      intro _
      obtain ⟨hP, hF, hT⟩ := simWorlds_wf s
      apply hostWorldWf_of_tbl hP hF hT
      · simp only [projSimToHostWorld, List.all_eq_true]
        intro p hp
        exact (List.all_eq_true.mp hSlots) p (removeHostSlotList_mem hid _ p hp)
      · simpa [projSimToHostWorld] using hNext
      · simp only [projSimToHostWorld]
        exact hasNoDupHandleIds_remove hid _ hNoDup
      · intro p hp
        simp only [projSimToHostWorld] at hp ⊢
        exact hLt p (removeHostSlotList_mem hid _ p hp)
    | activeCount =>
      try unfold StateT.map
      try unfold StateT.bind
      try unfold StateT.get
      try unfold StateT.pure
      dsimp only [Pure.pure, Bind.bind, StateT.bind, StateT.pure]
      exact ⟨hWf, fun _ => hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanSwe.Process.Proofs

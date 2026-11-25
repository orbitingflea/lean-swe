import LeanSwe.Process.Proofs.RefinesModelApi
import LeanSwe.Process.Proofs.RefinesModelHostFrames

/-!
Host-world handle-table step lemmas and `SysBridge.spawnPure` refinement over
`Model.HealthyHostCapsM`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Project `SysBridge.SysDepsM` out of `Model.HealthyHostCapsM`. -/
def hostDepsOf {W : Type} (cap : Model.HealthyHostCapsM (StateM W)) :
    SysBridge.SysDepsM (StateM W) Files.HandleId where
  proc := cap.proc
  files := cap.files
  poll := cap.poll
  timeRand := cap.timeRand
  postFork := cap.postFork
  listAmbientEnv := Except.ok <$> cap.listEnvironBytes

theorem hostWorldWf_implies_processStateWf {w : Model.ProcessHostWorld}
    (hWf : Model.hostWorldWf w = true) :
    Model.processStateWf (Model.hostWorldToProcessState w) = true := by
  unfold Model.hostWorldWf at hWf
  simp only [Bool.and_eq_true] at hWf
  exact hWf.2

private theorem findHostSlotPure_some_mem {fd : Type} (hid : Nat)
    (xs : List (Nat × Model.ProcSlotM fd)) (slot : Model.ProcSlotM fd)
    (h : Model.findHostSlotPure hid xs = some slot) :
    hid ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [Model.findHostSlotPure] at h
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    unfold Model.findHostSlotPure at h
    by_cases hEq : (k == hid) = true
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inl (beq_iff_eq.mp hEq).symm
    · rw [ite_eq_right hEq] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem map_hostSlotToEntry_fst' (xs : List (Nat × Model.ProcSlotM Files.HandleId)) :
    (xs.map Model.hostSlotToEntry).map (·.handleId) = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨k, v⟩; simp [Model.hostSlotToEntry, ih]

private theorem map_fst_update_hostSlot (xs : List (Nat × Model.ProcSlotM Files.HandleId))
    (hid : Nat) (f : Model.ProcSlotM Files.HandleId → Model.ProcSlotM Files.HandleId) :
    (xs.map fun x => if x.1 == hid then (x.1, f x.2) else (x.1, x.2)).map Prod.fst =
      xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hEq : (k == hid) = true
    · simp only [List.map_cons, hEq, ↓reduceIte, ih]
    · simp only [List.map_cons, hEq, Bool.false_eq_true, ↓reduceIte, ih]

private theorem filter_update_hostSlot (xs : List (Nat × Model.ProcSlotM Files.HandleId))
    (hid : Nat) (f : Model.ProcSlotM Files.HandleId → Model.ProcSlotM Files.HandleId) :
    ((xs.map fun x => if x.1 == hid then (x.1, f x.2) else (x.1, x.2)).map
        Model.hostSlotToEntry).filter (·.handleId != hid) =
      (xs.map Model.hostSlotToEntry).filter (·.handleId != hid) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hEq : (k == hid) = true
    · have hNeF : (k != hid) = false := by simp [beq_iff_eq.mp hEq]
      simp only [List.map_cons, hEq, ↓reduceIte, List.filter_cons, Model.hostSlotToEntry, hNeF,
        Bool.false_eq_true, ih]
    · have hNe : k ≠ hid := fun h => hEq (beq_iff_eq.mpr h)
      have hNeT : (k != hid) = true := bne_iff_ne.mpr hNe
      simp only [List.map_cons, hEq, Bool.false_eq_true, ↓reduceIte, List.filter_cons,
        Model.hostSlotToEntry, hNeT, ih]

private theorem map_removeHostSlotList_eq_filter (xs : List (Nat × Model.ProcSlotM Files.HandleId))
    (hid : Nat) (hNoDup : Model.hasNoDupHandleIds (xs.map Prod.fst) = true) :
    (Model.removeHostSlotList hid xs).2.map Model.hostSlotToEntry =
      (xs.map Model.hostSlotToEntry).filter (·.handleId != hid) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, Model.hasNoDupHandleIds, Bool.and_eq_true, Bool.not_eq_true'] at hNoDup
    unfold Model.removeHostSlotList
    by_cases hEq : (k == hid) = true
    · have hkHid : k = hid := beq_iff_eq.mp hEq
      subst hkHid
      have hNeF : (k != k) = false := by simp
      simp only [hEq, ↓reduceIte, List.map_cons, List.filter_cons, Model.hostSlotToEntry, hNeF,
        Bool.false_eq_true]
      rw [List.filter_eq_self.mpr]
      intro e he
      rcases List.mem_map.mp he with ⟨⟨k', v'⟩, hkv, rfl⟩
      dsimp only [Model.hostSlotToEntry]
      rw [bne_iff_ne]
      intro hKe
      subst hKe
      have hMem : k' ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k', v'), hkv, rfl⟩
      have hCont : (tl.map Prod.fst).contains k' = true := List.contains_iff_mem.mpr hMem
      rw [hCont] at hNoDup
      cases hNoDup.1
    · have hNe : k ≠ hid := fun h => hEq (beq_iff_eq.mpr h)
      have hNeT : (k != hid) = true := bne_iff_ne.mpr hNe
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.filter_cons,
        Model.hostSlotToEntry, hNeT, ih hNoDup.2]

private theorem hostWorldWf_noDup {w : Model.ProcessHostWorld} (hWf : Model.hostWorldWf w = true) :
    Model.hasNoDupHandleIds (w.tbl.slots.map Prod.fst) = true := by
  have hPw := hostWorldWf_implies_processStateWf hWf
  unfold Model.processStateWf Model.hostWorldToProcessState at hPw
  simp only [Bool.and_eq_true] at hPw
  rw [← map_hostSlotToEntry_fst']
  exact hPw.1.2

theorem capTbl_insertSlot_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (slot : SysBridge.ProcSlotM Files.HandleId)
    (hPid1 : 1 ≤ slot.pid) (hPidMax : slot.pid ≤ Model.maxLinuxPidModel)
    (hPgid1 : 1 ≤ slot.pgid) (hPgidMax : slot.pgid ≤ Model.maxLinuxPidModel)
    (hInSome : slot.stdinFd?.isNone = false) (hWaitF : slot.waited = false) :
    let r := (cap.table.insertSlot slot).run w
    Model.hostWorldWf (proj r.2) = true ∧
    r.1 = (Model.hostWorldToProcessState (proj w)).nextHandleId ∧
    Int.ofNat slot.pid.toNat > 0 ∧
    Int.ofNat slot.pgid.toNat > 0 ∧
    Model.hostWorldToProcessState (proj r.2) =
      { nextHandleId := (Model.hostWorldToProcessState (proj w)).nextHandleId + 1
        activeHandles :=
          { handleId := r.1
            pid := Int.ofNat slot.pid.toNat
            pgid := Int.ofNat slot.pgid.toNat
            ioConsumed := false
            waited := false } :: (Model.hostWorldToProcessState (proj w)).activeHandles } := by
  have hReqWf : Model.hostCapReqWf (.table (.insertSlot slot)) = true := by
    unfold Model.hostCapReqWf Model.hostSlotWf
    exact decide_eq_true ⟨hPid1, hPidMax, hPgid1, hPgidMax⟩
  have hStep := hCap w (.table (.insertSlot slot)) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  dsimp only [Model.insertHostSlotPure] at hStep
  obtain ⟨_, hWf', _, _, _, _, hIdEq, hTblEq⟩ := hStep
  have hWf2 := hWf' hReqWf
  have hPidNat : (1 : Nat) ≤ slot.pid.toNat := hPid1
  have hPgidNat : (1 : Nat) ≤ slot.pgid.toNat := hPgid1
  dsimp only [Model.hostWorldToProcessState]
  refine ⟨hWf2, hIdEq, Int.ofNat_lt.mpr hPidNat, Int.ofNat_lt.mpr hPgidNat, ?_⟩
  rw [hTblEq, ← hIdEq]
  simp only [List.map_cons, Model.hostSlotToEntry, hInSome, Bool.false_and, hWaitF]

theorem capTbl_takeSlotIo_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Nat) :
    let r := (cap.table.takeSlotIo hid).run w
    Model.hostWorldWf (proj r.2) = true ∧
    (Model.hostWorldToProcessState (proj r.2)).nextHandleId =
      (Model.hostWorldToProcessState (proj w)).nextHandleId ∧
    (Model.hostWorldToProcessState (proj r.2)).activeHandles.map (·.handleId) =
      (Model.hostWorldToProcessState (proj w)).activeHandles.map (·.handleId) ∧
    (Model.hostWorldToProcessState (proj r.2)).activeHandles.filter (·.handleId != hid) =
      (Model.hostWorldToProcessState (proj w)).activeHandles.filter (·.handleId != hid) ∧
    (∀ t, r.1 = some t → hid ∈ (Model.hostWorldToProcessState (proj w)).activeHandles.map (·.handleId)) := by
  have hStep := hCap w (.table (.takeSlotIo hid)) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  dsimp only [Model.takeHostSlotIoPure] at hStep
  obtain ⟨_, hWf', _, _, _, _, hResEq, hTblEq⟩ := hStep
  refine ⟨hWf' rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots <;> rfl
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rfl
    | some _ =>
      dsimp only
      rw [map_hostSlotToEntry_fst', map_hostSlotToEntry_fst']
      exact map_fst_update_hostSlot (proj w).tbl.slots hid
        (fun s => { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rfl
    | some _ =>
      dsimp only
      exact filter_update_hostSlot (proj w).tbl.slots hid
        (fun s => { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
  · intro t ht
    rw [ht] at hResEq
    cases hF : Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rw [hF] at hResEq; cases hResEq
    | some slot =>
      unfold Model.hostWorldToProcessState
      rw [map_hostSlotToEntry_fst']
      exact findHostSlotPure_some_mem hid (proj w).tbl.slots slot hF

theorem capTbl_markWaited_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Nat) (waited : Bool) :
    let r := (cap.table.markWaited hid waited).run w
    Model.hostWorldWf (proj r.2) = true ∧
    (Model.hostWorldToProcessState (proj r.2)).nextHandleId =
      (Model.hostWorldToProcessState (proj w)).nextHandleId ∧
    (Model.hostWorldToProcessState (proj r.2)).activeHandles.map (·.handleId) =
      (Model.hostWorldToProcessState (proj w)).activeHandles.map (·.handleId) ∧
    (Model.hostWorldToProcessState (proj r.2)).activeHandles.filter (·.handleId != hid) =
      (Model.hostWorldToProcessState (proj w)).activeHandles.filter (·.handleId != hid) ∧
    (r.1 = true → hid ∈ (Model.hostWorldToProcessState (proj w)).activeHandles.map (·.handleId)) := by
  have hStep := hCap w (.table (.markWaited hid waited)) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  dsimp only [Model.markHostWaitedPure] at hStep
  obtain ⟨_, hWf', _, _, _, _, hResEq, hTblEq⟩ := hStep
  refine ⟨hWf' rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots <;> rfl
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rfl
    | some _ =>
      dsimp only
      rw [map_hostSlotToEntry_fst', map_hostSlotToEntry_fst']
      exact map_fst_update_hostSlot (proj w).tbl.slots hid
        (fun s => { s with waited := s.waited || waited })
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
    cases Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rfl
    | some _ =>
      dsimp only
      exact filter_update_hostSlot (proj w).tbl.slots hid
        (fun s => { s with waited := s.waited || waited })
  · intro ht
    rw [ht] at hResEq
    cases hF : Model.findHostSlotPure hid (proj w).tbl.slots with
    | none => rw [hF] at hResEq; cases hResEq
    | some slot =>
      unfold Model.hostWorldToProcessState
      rw [map_hostSlotToEntry_fst']
      exact findHostSlotPure_some_mem hid (proj w).tbl.slots slot hF

theorem capTbl_lookupPgid_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Nat) :
    let r := (cap.table.lookupPgid hid).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w (.table (.lookupPgid hid)) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  exact ⟨hStep.2.1 rfl, hStep.2.2.2.2.2.2.2⟩

theorem capTbl_detachSlot_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Nat) :
    let r := (cap.table.detachSlot hid).run w
    Model.hostWorldWf (proj r.2) = true ∧
    (Model.hostWorldToProcessState (proj r.2)).nextHandleId =
      (Model.hostWorldToProcessState (proj w)).nextHandleId ∧
    (Model.hostWorldToProcessState (proj r.2)).activeHandles =
      (Model.hostWorldToProcessState (proj w)).activeHandles.filter (·.handleId != hid) := by
  have hStep := hCap w (.table (.detachSlot hid)) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  dsimp only [Model.detachHostSlotPure] at hStep
  obtain ⟨_, hWf', _, _, _, _, _, hTblEq⟩ := hStep
  refine ⟨hWf' rfl, ?_, ?_⟩
  · unfold Model.hostWorldToProcessState; rw [hTblEq]
  · unfold Model.hostWorldToProcessState; rw [hTblEq]
    exact map_removeHostSlotList_eq_filter (proj w).tbl.slots hid (hostWorldWf_noDup hWf)

theorem capTbl_activeCount_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := cap.table.activeCount.run w
    Model.hostWorldWf (proj r.2) = true ∧
    Model.hostWorldToProcessState (proj r.2) = Model.hostWorldToProcessState (proj w) ∧
    r.1 = (Model.hostWorldToProcessState (proj w)).activeHandles.length := by
  have hStep := hCap w (.table .activeCount) hWf
  unfold Model.execHostCapStep Model.execHostTableReq Model.allowedHostCapStep Model.allowedHostTableStep at hStep
  rw [hostStateT_map_run, hostStateT_map_run] at hStep
  obtain ⟨_, hWf', _, _, _, _, hCntEq, hTblEq⟩ := hStep
  refine ⟨hWf' rfl, ?_, ?_⟩
  · dsimp only [Model.hostWorldToProcessState]; rw [hTblEq]
  · dsimp only [Model.hostWorldToProcessState]; rw [hCntEq, List.length_map]

theorem tblEq_to_stateEq {w1 w2 : Model.ProcessHostWorld} (h : w1.tbl = w2.tbl) :
    Model.hostWorldToProcessState w1 = Model.hostWorldToProcessState w2 := by
  unfold Model.hostWorldToProcessState
  rw [h]

theorem spawnPure_refines_host {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (req : ExecRequest) :
    let r := (SysBridge.spawnPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL req).run w
    Model.hostWorldWf (proj r.2) = true ∧
    Model.allowedRawSpawn (Model.hostWorldToProcessState (proj w)) r.1 (Model.hostWorldToProcessState (proj r.2)) := by
  unfold SysBridge.spawnPure
  dsimp only [hostDepsOf]
  split
  · rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, mapRawError_invalidArg_isNonOutcome _ _ _⟩
  · rw [hostStateT_bind_run]
    have hWd := hostValidateWorkingDir_spec proj cap hCap req.cwd DEFAULT_EINTR_FUEL w hWf
    cases hWdRun : (SysBridge.validateWorkingDir cap.files req.cwd DEFAULT_EINTR_FUEL).run w with
    | mk wdRes w1 =>
      rw [hWdRun] at hWd
      cases wdRes with
      | error wdErr =>
        rw [hostStateT_pure_run]
        exact ⟨hWd.1, tblEq_to_stateEq hWd.2.1, hWd.2.2 _ rfl⟩
      | ok _ =>
        dsimp only
        rw [hostStateT_bind_run]
        have hEnv : let r := (SysBridge.readBaseEnv
            { proc := cap.proc, files := cap.files, poll := cap.poll, timeRand := cap.timeRand,
              postFork := cap.postFork, listAmbientEnv := Except.ok <$> cap.listEnvironBytes } req.inheritEnv).run w1
            Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w1).tbl ∧
            (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
          unfold SysBridge.readBaseEnv
          cases req.inheritEnv with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hostStateT_pure_run]
            exact ⟨hWd.1, rfl, fun _ h => by cases h⟩
          | true =>
            simp only [↓reduceIte]
            rw [hostStateT_map_run]
            have hA := cap_listAmbientEnv_frame proj cap hCap w1 hWd.1
            exact ⟨hA.1, hA.2, fun _ h => by cases h⟩
        cases hEnvRun : (SysBridge.readBaseEnv
            { proc := cap.proc, files := cap.files, poll := cap.poll, timeRand := cap.timeRand,
              postFork := cap.postFork, listAmbientEnv := Except.ok <$> cap.listEnvironBytes } req.inheritEnv).run w1 with
        | mk envRes w2 =>
          rw [hEnvRun] at hEnv
          cases envRes with
          | error envErr =>
            rw [hostStateT_pure_run]
            exact ⟨hEnv.1, tblEq_to_stateEq (hEnv.2.1.trans hWd.2.1),
              ensureNonEmpty_host_isNonOutcome _ _ (by decide) (hEnv.2.2 _ rfl)⟩
          | ok baseEnv =>
            dsimp only
            rw [hostStateT_bind_run]
            let envBytes := SysBridge.mergeRawEnvOverrides baseEnv req.env
            have hRes := hostResolveExecutablePath_spec proj cap hCap req.program req.cwd envBytes
              DEFAULT_EINTR_FUEL w2 hEnv.1
            cases hResRun : (SysBridge.resolveExecutablePath cap.files req.program req.cwd envBytes
                DEFAULT_EINTR_FUEL).run w2 with
            | mk pathRes w3 =>
              rw [hResRun] at hRes
              cases pathRes with
              | error resErr =>
                rw [hostStateT_pure_run]
                exact ⟨hRes.1, tblEq_to_stateEq (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1)), hRes.2.2 _ rfl⟩
              | ok resolvedPath =>
                dsimp only
                split
                · rw [hostStateT_pure_run]
                  exact ⟨hRes.1, tblEq_to_stateEq (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1)),
                    mapRawError_invalidArg_isNonOutcome _ _ _⟩
                · rw [hostStateT_bind_run]
                  have hP1 := hostRetryEintr_frame proj (cap.proc.pipe2 { cloexec := true })
                    (fun x hx => execProc_pipe2_frame proj cap hCap x hx { cloexec := true })
                    DEFAULT_EINTR_FUEL w3 hRes.1
                  cases hP1Run : (LinuxSyscall.retryEintr (cap.proc.pipe2 { cloexec := true })
                      DEFAULT_EINTR_FUEL).run w3 with
                  | mk p1Res w4 =>
                    rw [hP1Run] at hP1
                    cases p1Res with
                    | error e1 =>
                      rw [hostStateT_pure_run]
                      exact ⟨hP1.1, tblEq_to_stateEq (hP1.2.trans (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1))),
                        mapErrno_isNonOutcome _ _ _⟩
                    | ok p1 =>
                      rcases p1 with ⟨inR, inW⟩
                      dsimp only
                      rw [hostStateT_bind_run]
                      have hP2 := hostRetryEintr_frame proj (cap.proc.pipe2 { cloexec := true })
                        (fun x hx => execProc_pipe2_frame proj cap hCap x hx { cloexec := true })
                        DEFAULT_EINTR_FUEL w4 hP1.1
                      cases hP2Run : (LinuxSyscall.retryEintr (cap.proc.pipe2 { cloexec := true })
                          DEFAULT_EINTR_FUEL).run w4 with
                      | mk p2Res w5 =>
                        rw [hP2Run] at hP2
                        cases p2Res with
                        | error e2 =>
                          dsimp only
                          rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                          have hc1 := hostCloseOpt_frame proj cap hCap (some inR) w5 hP2.1
                          have hc2 := hostCloseOpt_frame proj cap hCap (some inW)
                            (Files.closeOpt cap.files (some inR) |>.run w5).2 hc1.1
                          exact ⟨hc2.1, tblEq_to_stateEq (hc2.2.trans (hc1.2.trans (hP2.2.trans
                            (hP1.2.trans (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1)))))),
                            mapErrno_isNonOutcome _ _ _⟩
                        | ok p2 =>
                          rcases p2 with ⟨outR, outW⟩
                          dsimp only
                          rw [hostStateT_bind_run]
                          have hP3 := hostRetryEintr_frame proj (cap.proc.pipe2 { cloexec := true })
                            (fun x hx => execProc_pipe2_frame proj cap hCap x hx { cloexec := true })
                            DEFAULT_EINTR_FUEL w5 hP2.1
                          cases hP3Run : (LinuxSyscall.retryEintr (cap.proc.pipe2 { cloexec := true })
                              DEFAULT_EINTR_FUEL).run w5 with
                          | mk p3Res w6 =>
                            rw [hP3Run] at hP3
                            cases p3Res with
                            | error e3 =>
                              dsimp only
                              rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run,
                                hostStateT_pure_run]
                              have hc1 := hostCloseOpt_frame proj cap hCap (some inR) w6 hP3.1
                              have hc2 := hostCloseOpt_frame proj cap hCap (some inW)
                                (Files.closeOpt cap.files (some inR) |>.run w6).2 hc1.1
                              have hc3 := hostCloseOpt_frame proj cap hCap (some outR)
                                (Files.closeOpt cap.files (some inW) |>.run
                                  (Files.closeOpt cap.files (some inR) |>.run w6).2).2 hc2.1
                              have hc4 := hostCloseOpt_frame proj cap hCap (some outW)
                                (Files.closeOpt cap.files (some outR) |>.run
                                  (Files.closeOpt cap.files (some inW) |>.run
                                    (Files.closeOpt cap.files (some inR) |>.run w6).2).2).2 hc3.1
                              exact ⟨hc4.1, tblEq_to_stateEq (hc4.2.trans (hc3.2.trans (hc2.2.trans (hc1.2.trans
                                (hP3.2.trans (hP2.2.trans (hP1.2.trans (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1))))))))),
                                mapErrno_isNonOutcome _ _ _⟩
                            | ok p3 =>
                              rcases p3 with ⟨errR, errW⟩
                              dsimp only
                              rw [hostStateT_bind_run]
                              let spec : PostFork.ChildSpecM Files.HandleId :=
                                { path := resolvedPath
                                  argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                                  cwd := req.cwd, env := #[], rawEnv := envBytes
                                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                                  fdPolicy := .inheritNonCloexec #[]
                                  closeFds := #[.handle inW, .handle outR, .handle errR]
                                  processGroup := .newGroup, sigpipe := .resetDefault, forkMode := .direct }
                              have hPf := cap_postFork_step proj cap hCap w6 hP3.1 spec
                              cases hPfRun : (cap.postFork.spawn spec).run w6 with
                              | mk pfRes w7 =>
                                rw [hPfRun] at hPf
                                dsimp only
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
                                have hc1 := hostCloseOpt_frame proj cap hCap (some inR) w7 hPf.1
                                have hc2 := hostCloseOpt_frame proj cap hCap (some outW)
                                  (Files.closeOpt cap.files (some inR) |>.run w7).2 hc1.1
                                have hc3 := hostCloseOpt_frame proj cap hCap (some errW)
                                  (Files.closeOpt cap.files (some outW) |>.run
                                    (Files.closeOpt cap.files (some inR) |>.run w7).2).2 hc2.1
                                let w8 := (Files.closeOpt cap.files (some errW) |>.run
                                  (Files.closeOpt cap.files (some outW) |>.run
                                    (Files.closeOpt cap.files (some inR) |>.run w7).2).2).2
                                have hTbl8 : (proj w8).tbl = (proj w).tbl :=
                                  hc3.2.trans (hc2.2.trans (hc1.2.trans (hPf.2.1.trans
                                    (hP3.2.trans (hP2.2.trans (hP1.2.trans (hRes.2.1.trans (hEnv.2.1.trans hWd.2.1))))))))
                                cases pfRes with
                                | error pfErr =>
                                  dsimp only
                                  rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                  have hc4 := hostCloseOpt_frame proj cap hCap (some inW) w8 hc3.1
                                  have hc5 := hostCloseOpt_frame proj cap hCap (some outR)
                                    (Files.closeOpt cap.files (some inW) |>.run w8).2 hc4.1
                                  have hc6 := hostCloseOpt_frame proj cap hCap (some errR)
                                    (Files.closeOpt cap.files (some outR) |>.run
                                      (Files.closeOpt cap.files (some inW) |>.run w8).2).2 hc5.1
                                  exact ⟨hc6.1, tblEq_to_stateEq (hc6.2.trans (hc5.2.trans (hc4.2.trans hTbl8))),
                                    mapPostForkError_isNonOutcome _ _⟩
                                | ok child =>
                                  dsimp only
                                  let rawPgid := child.pgid.getD child.pid
                                  by_cases hBadPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID ||
                                      rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = true
                                  · rw [ite_eq_left hBadPid, hostStateT_bind_run, hostStateT_bind_run,
                                      hostStateT_bind_run, hostStateT_pure_run]
                                    have hc4 := hostCloseOpt_frame proj cap hCap (some inW) w8 hc3.1
                                    have hc5 := hostCloseOpt_frame proj cap hCap (some outR)
                                      (Files.closeOpt cap.files (some inW) |>.run w8).2 hc4.1
                                    have hc6 := hostCloseOpt_frame proj cap hCap (some errR)
                                      (Files.closeOpt cap.files (some outR) |>.run
                                        (Files.closeOpt cap.files (some inW) |>.run w8).2).2 hc5.1
                                    exact ⟨hc6.1, tblEq_to_stateEq (hc6.2.trans (hc5.2.trans (hc4.2.trans hTbl8))),
                                      mapRawError_userError_isNonOutcome _⟩
                                  · rw [ite_eq_right hBadPid, hostStateT_bind_run]
                                    have hOkPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID ||
                                        rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = false :=
                                      Bool.eq_false_iff.mpr hBadPid
                                    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not,
                                      UInt32.lt_iff_toNat_lt] at hOkPid
                                    have hPidNe : child.pid.toNat ≠ 0 := fun hz =>
                                      hOkPid.1.1.1 (UInt32.toNat_inj.mp hz)
                                    have hPgidNe : rawPgid.toNat ≠ 0 := fun hz =>
                                      hOkPid.1.2 (UInt32.toNat_inj.mp hz)
                                    have hMaxNat : LinuxSyscall.Process.MAX_LINUX_PID.toNat ≤ Model.maxLinuxPidModel.toNat := by decide
                                    have hP1Ge : (1 : UInt32) ≤ child.pid := by rw [UInt32.le_iff_toNat_le]; change 1 ≤ child.pid.toNat; omega
                                    have hPMax : child.pid ≤ Model.maxLinuxPidModel := by rw [UInt32.le_iff_toNat_le]; omega
                                    have hPg1Ge : (1 : UInt32) ≤ rawPgid := by rw [UInt32.le_iff_toNat_le]; change 1 ≤ rawPgid.toNat; omega
                                    have hPgMax : rawPgid ≤ Model.maxLinuxPidModel := by rw [UInt32.le_iff_toNat_le]; omega
                                    have hIns := capTbl_insertSlot_step proj cap hCap w8 hc3.1
                                      { pid := child.pid, pgid := rawPgid, stdinFd? := some inW,
                                        stdoutFd? := some outR, stderrFd? := some errR, waited := false }
                                      hP1Ge hPMax hPg1Ge hPgMax rfl rfl
                                    cases hInsRun : (cap.table.insertSlot
                                        { pid := child.pid, pgid := rawPgid, stdinFd? := some inW,
                                          stdoutFd? := some outR, stderrFd? := some errR, waited := false }).run w8 with
                                    | mk hid w9 =>
                                      rw [hInsRun] at hIns
                                      rw [hostStateT_pure_run]
                                      obtain ⟨hWf9, hHidEq, hPidPos, hPgidPos, hSt9⟩ := hIns
                                      have hSt8 := tblEq_to_stateEq hTbl8
                                      rw [hSt8] at hHidEq hSt9
                                      exact ⟨hWf9, hHidEq, hPidPos, hPgidPos, hSt9⟩

end LeanSwe.Process.Proofs

import Core.Obeys
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesPreflightSealModel
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesSpawnModel
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStreamLoop

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

private theorem preserves_bind_eq {W α β : Type} {proj : W → RawHostWorld} {Q : β → W → Prop}
    {target : RawHostWorld} {ma : StateM W α} {k : α → StateM W β} {w : W}
    (hEq : proj w = target) (hWf : rawHostWorldWf target = true) (hMa : PreservesProj proj ma)
    (hK : ∀ a s, proj s = target → Q ((k a).run s).1 ((k a).run s).2) :
    Q ((ma >>= k).run w).1 ((ma >>= k).run w).2 := by
  simp only [stateM_bind_run]
  have hp := hMa w (by rw [hEq]; exact hWf)
  exact hK _ _ (hp.trans hEq)

private theorem preserves_err_eq {W α β : Type} {proj : W → RawHostWorld} {Q : β → W → Prop}
    {target : RawHostWorld} {ma : StateM W α} {res : β} {w : W}
    (hEq : proj w = target) (hWf : rawHostWorldWf target = true) (hMa : PreservesProj proj ma)
    (hQ : ∀ s, proj s = target → Q res s) :
    Q ((ma >>= fun _ => pure res).run w).1 ((ma >>= fun _ => pure res).run w).2 := by
  simp only [stateM_bind_run, stateM_pure_run]
  exact hQ _ ((hMa w (by rw [hEq]; exact hWf)).trans hEq)

/-- Main single-step behavioral refinement theorem for `Internal.mkOpsFromHostCapM` across all 13 effectful `RawProcessSandboxOpsM` operations. -/
theorem refinesStepFrom_mkOpsFromHostCapM :
    Core.ObeysStepFrom id Model.rawHostWorldWf Model.execRawCapStep Model.allowedRawCapStep
      Model.rawHostWorldWf Internal.mkOpsFromHostCapM Model.execRawOpsStep Model.allowedRawOpsStep := by
  intro W proj cap hCap w req hWf
  dsimp only [Function.comp, id] at hCap hWf ⊢
  cases req with
  | hostSeccompArch =>
    have ⟨hLin, hTgt⟩ := cap_metaInfo_eq hCap hWf
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, hostSeccompArchPure, toHostSysDeps, stateM_map_run, stateM_pure_run]
    dsimp only [allowedRawOpsStep]
    refine ⟨hWf, rfl, rfl, ?_, rfl⟩
    rw [hLin, hTgt]
    rfl
  | preflight preq =>
    dsimp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM, mkRawOpsM]
    rw [stateM_map_run]
    exact preflightPure_refines hCap DEFAULT_EINTR_FUEL preq w hWf
  | discoverHostPreset =>
    have ⟨hLin, _⟩ := cap_metaInfo_eq hCap hWf
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, discoverHostPresetPure, stateM_map_run]
    rcases Bool.eq_false_or_eq_true (toHostSysDeps cap).isLinux with hCapLin | hCapLin
    · have hProjT : (proj w).isLinux = true := by rw [← hLin]; exact hCapLin
      simp only [hCapLin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
      dsimp only [toHostSysDeps, allowedRawOpsStep]
      have ⟨hP, hInv⟩ := discoverHostPresetM_spec hCap DEFAULT_EINTR_FUEL
      have hEq := hP w hWf
      have ⟨hSys, hEtc, hHome⟩ := hInv w hWf
      exact ⟨by rw [hEq]; exact hWf, by rw [hEq], by rw [hEq], hEq, hProjT, hSys, hEtc, hHome⟩
    · have hProjF : (proj w).isLinux = false := by rw [← hLin]; exact hCapLin
      simp only [hCapLin, Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      exact ⟨hWf, rfl, rfl, rfl, hProjF, rfl, mapRawError_unavail_ne_empty _ _⟩
  | sealPlan plan sec =>
    dsimp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM, mkRawOpsM]
    rw [stateM_map_run]
    exact sealPlanPure_refines hCap DEFAULT_EINTR_FUEL plan sec w hWf
  | closePlan ph =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, closePlanPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId ph.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, Or.inl hVal, rfl⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]
      dsimp only [toHostSysDeps]
      have hDet := tbl_detachPlan_spec hCap hWf ph.handleId
      rcases hDet with ⟨hWf1, hL1, hT1, hBx1, hFw1, hBody⟩
      let w1 := ((toHostTableOps cap).detachPlan ph.handleId).run w |>.2
      cases hR : (((toHostTableOps cap).detachPlan ph.handleId).run w).1 with
      | none =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyF, hEq⟩
        simp only [stateM_pure_run]
        dsimp only [allowedRawOpsStep]
        exact ⟨hWf1, hL1, hT1, hBx1, hFw1, rfl, (mapRawError_invalidArg_spec _ _ _).2, Or.inr hKeyF, hEq⟩
      | some slot =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyT, hLen⟩
        let Q : Except SandboxError Unit → W → Prop :=
          fun out u => allowedRawOpsStep (proj w) (.closePlan ph) (.exceptUnit out) (proj u)
        change Q _ _
        refine preserves_bind_eq (w := w1) rfl hWf1 (preservesProj_closeOpt hCap (some slot.planMemfd)) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap (some slot.initMemfd)) fun _ s hEq => ?_
        exact preserves_err_eq hEq hWf1 (preservesProj_closeOpt hCap (some slot.hostsMemfd)) fun s' hEq' =>
          ⟨by rw [hEq']; exact hWf1, by rw [hEq']; exact hL1, by rw [hEq']; exact hT1,
            by rw [hEq']; exact hBx1, by rw [hEq']; exact hFw1, hVal, hKeyT, by rw [hEq']; exact hLen⟩
  | spawnBox ph =>
    dsimp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM, mkRawOpsM]
    rw [stateM_map_run]
    exact spawnBoxPure_refines hCap DEFAULT_EINTR_FUEL ph w hWf
  | startPortForwarders bh fwds =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, startPortForwardersPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId bh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      exact ⟨hWf, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, rfl, fun _ => ⟨rfl, rfl⟩⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run]
      dsimp only [toHostSysDeps]
      have hTk := tbl_takeBoxListeners_spec hCap hWf bh.handleId fwds.size
      rcases hTk with ⟨hWf1, hL1, hT1, hPl1, hFw1, hBxLen1, hBody⟩
      let w1 := ((toHostTableOps cap).takeBoxListeners bh.handleId fwds.size).run w |>.2
      cases hR : (((toHostTableOps cap).takeBoxListeners bh.handleId fwds.size).run w).1 with
      | none =>
        rw [hR] at hBody
        simp only [stateM_pure_run]
        dsimp only [allowedRawOpsStep]
        exact ⟨hWf1, hL1, hT1, hPl1, hBxLen1, (mapRawError_invalidArg_spec _ _ _).2, hFw1, fun _ => ⟨rfl, hBody⟩⟩
      | some listenerFds =>
        rw [hR] at hBody
        dsimp only
        have hKeyT : tableHasKey bh.handleId (proj w).table.boxes = true := hBody
        let Q : Except SandboxError PortForwarderHandle → W → Prop :=
          fun out s => allowedRawOpsStep (proj w) (.startPortForwarders bh fwds) (.exceptFwd out) (proj s)
        change Q _ _
        refine preserves_bind_eq (w := w1) rfl hWf1
          (preservesProj_of_seqUnit _ fun u hu => (hCap u (.startFwdTask listenerFds (fwds.map PortForward.hostPort)) hu).2)
          fun rStart s hEq => ?_
        cases rStart with
        | error e =>
          dsimp only
          exact preserves_err_eq hEq hWf1 (preservesProj_closeFdArray hCap listenerFds) fun s' hEq' => by
            refine ⟨by rw [hEq']; exact hWf1, by rw [hEq']; exact hL1, by rw [hEq']; exact hT1,
              by rw [hEq']; exact hPl1, by rw [hEq']; exact hBxLen1, mapRawError_ioError_ne_empty e _,
              by rw [hEq']; exact hFw1, fun hOr => ?_⟩
            rcases hOr with hF | hF <;> simp [hVal, hKeyT] at hF
        | ok taskHandle =>
          dsimp only
          rw [stateM_bind_run]
          let fslot : ForwarderSlotM Nat := { boxHandleId := bh.handleId, taskHandle := taskHandle }
          have hIns := tbl_insertFwd_spec hCap (by rw [hEq]; exact hWf1) fslot
          rcases hIns with ⟨hWf3, hL3, hT3, hPl3, hBx3, hIBody⟩
          cases hI : (((toHostTableOps cap).insertFwd fslot).run s).1 with
          | none =>
            rw [hI] at hIBody
            exact preserves_err_eq (hIBody.trans hEq) hWf1
              (preservesProj_of_seqUnit _ fun u hu => (hCap u (.stopFwdTask taskHandle) hu).2) fun s' hEq' => by
                refine ⟨by rw [hEq']; exact hWf1, by rw [hEq']; exact hL1, by rw [hEq']; exact hT1,
                  by rw [hEq']; exact hPl1, by rw [hEq']; exact hBxLen1,
                  mapRawError_ioError_ne_empty Errno.ENOMEM _, by rw [hEq']; exact hFw1, fun hOr => ?_⟩
                rcases hOr with hF | hF <;> simp [hVal, hKeyT] at hF
          | some fhid =>
            rw [hI] at hIBody
            rcases hIBody with ⟨hFhidV, hFwLen⟩
            simp only [stateM_pure_run]
            dsimp only [Q, allowedRawOpsStep]
            exact ⟨hWf3, by rw [hL3, hEq]; exact hL1, by rw [hT3, hEq]; exact hT1,
              by rw [hPl3, hEq]; exact hPl1, by rw [hBx3, hEq]; exact hBxLen1,
              hVal, hKeyT, hFhidV, rfl, by rw [hFwLen, hEq, hFw1]⟩
  | stopPortForwarders fh =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, stopPortForwardersPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId fh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, Or.inl hVal, rfl⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]
      dsimp only [toHostSysDeps]
      have hDet := tbl_detachFwd_spec hCap hWf fh.handleId
      rcases hDet with ⟨hWf1, hL1, hT1, hPl1, hBx1, hBody⟩
      let w1 := ((toHostTableOps cap).detachFwd fh.handleId).run w |>.2
      cases hR : (((toHostTableOps cap).detachFwd fh.handleId).run w).1 with
      | none =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyF, hEq⟩
        simp only [stateM_pure_run]
        dsimp only [allowedRawOpsStep]
        exact ⟨hWf1, hL1, hT1, hPl1, hBx1, rfl, (mapRawError_invalidArg_spec _ _ _).2, Or.inr hKeyF, hEq⟩
      | some fslot =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyT, hLen⟩
        let Q : Except SandboxError Unit → W → Prop :=
          fun out u => allowedRawOpsStep (proj w) (.stopPortForwarders fh) (.exceptUnit out) (proj u)
        change Q _ _
        exact preserves_err_eq (w := w1) rfl hWf1
          (preservesProj_of_seqUnit _ fun u hu => (hCap u (.stopFwdTask fslot.taskHandle) hu).2) fun s' hEq' =>
          ⟨by rw [hEq']; exact hWf1, by rw [hEq']; exact hL1, by rw [hEq']; exact hT1,
            by rw [hEq']; exact hPl1, by rw [hEq']; exact hBx1, hVal, hKeyT, by rw [hEq']; exact hLen⟩
  | readBoxOutput bh stdin toMs maxOut? =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, readBoxOutputPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId bh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, fun _ => ⟨rfl, rfl⟩⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]
      dsimp only [toHostSysDeps]
      have hTk := tbl_takeBoxIo_spec hCap hWf bh.handleId
      rcases hTk with ⟨hWf1, hL1, hT1, hPl1, hFw1, hBxLen1, hBody⟩
      let w1 := ((toHostTableOps cap).takeBoxIo bh.handleId).run w |>.2
      cases hR : (((toHostTableOps cap).takeBoxIo bh.handleId).run w).1 with
      | none =>
        rw [hR] at hBody
        simp only [stateM_pure_run]
        dsimp only [allowedRawOpsStep]
        exact ⟨hWf1, hL1, hT1, hPl1, hBxLen1, hFw1, (mapRawError_invalidArg_spec _ _ _).2, fun _ => ⟨rfl, hBody⟩⟩
      | some ioInfo =>
        rw [hR] at hBody
        have hKeyT : tableHasKey bh.handleId (proj w).table.boxes = true := hBody
        rcases ioInfo with ⟨inFd?, outFd?, errFd?, statusFd?, goFd?, prog, cwd⟩
        dsimp only
        have ⟨hCoreP, hCoreI⟩ := readBoxOutputCore_spec hCap prog cwd inFd? outFd? errFd? statusFd? goFd? stdin toMs maxOut? DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
        have hP2 := hCoreP w1 hWf1
        have hI2 := hCoreI w1 hWf1
        change allowedRawOpsStep (proj w) (.readBoxOutput bh stdin toMs maxOut?)
          (.exceptResult ((readBoxOutputCore cap.files cap.poll cap.timeRand prog cwd inFd? outFd? errFd? statusFd? goFd? stdin toMs maxOut? DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL).run w1).1)
          (proj ((readBoxOutputCore cap.files cap.poll cap.timeRand prog cwd inFd? outFd? errFd? statusFd? goFd? stdin toMs maxOut? DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL).run w1).2)
        cases hC : ((readBoxOutputCore cap.files cap.poll cap.timeRand prog cwd inFd? outFd? errFd? statusFd? goFd? stdin toMs maxOut? DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL).run w1).1 with
        | ok res =>
          rw [hC] at hI2
          dsimp only [allowedRawOpsStep]
          exact ⟨by rw [hP2]; exact hWf1, by rw [hP2]; exact hL1, by rw [hP2]; exact hT1,
            by rw [hP2]; exact hPl1, by rw [hP2]; exact hBxLen1, by rw [hP2]; exact hFw1,
            hVal, hKeyT, hI2.1, hI2.2⟩
        | error err =>
          rw [hC] at hI2
          dsimp only [allowedRawOpsStep]
          refine ⟨by rw [hP2]; exact hWf1, by rw [hP2]; exact hL1, by rw [hP2]; exact hT1,
            by rw [hP2]; exact hPl1, by rw [hP2]; exact hBxLen1, by rw [hP2]; exact hFw1, hI2, fun hOr => ?_⟩
          rcases hOr with hF | hF <;> simp [hVal, hKeyT] at hF
  | killProcessGroup bh =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, killProcessGroupPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId bh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      simp only [hVal, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hWf, trivial, trivial, trivial, (mapRawError_invalidArg_spec _ _ _).2, rfl⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]
      dsimp only [toHostSysDeps]
      have ⟨hSome, hProj⟩ := tbl_findBoxKillInfo_spec hCap hWf bh.handleId
      let w1 := ((toHostTableOps cap).findBoxKillInfo bh.handleId).run w |>.2
      have hWf1 : rawHostWorldWf (proj w1) = true := by rw [hProj]; exact hWf
      cases hF : (((toHostTableOps cap).findBoxKillInfo bh.handleId).run w).1 with
      | none =>
        rw [hF] at hSome
        have hKeyF : tableHasKey bh.handleId (proj w).table.boxes = false := hSome.symm
        simp only [stateM_pure_run]
        change allowedRawOpsStep (proj w) (.killProcessGroup bh) (.exceptUnit (.error _)) (proj w1)
        dsimp only [allowedRawOpsStep]
        rw [hProj]
        simp only [hVal, hKeyF, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hWf, trivial, trivial, trivial, (mapRawError_invalidArg_spec _ _ _).2, rfl⟩
      | some info =>
        rw [hF] at hSome
        have hKeyT : tableHasKey bh.handleId (proj w).table.boxes = true := hSome.symm
        rcases info with ⟨pgid, _⟩
        dsimp only
        have ⟨hKP, hKE⟩ := killBoxPg_spec hCap pgid DEFAULT_EINTR_FUEL
        have hEnd : proj ((killBoxPg cap.proc pgid DEFAULT_EINTR_FUEL).run w1).2 = proj w := (hKP w1 hWf1).trans hProj
        change allowedRawOpsStep (proj w) (.killProcessGroup bh)
          (.exceptUnit ((killBoxPg cap.proc pgid DEFAULT_EINTR_FUEL).run w1).1)
          (proj ((killBoxPg cap.proc pgid DEFAULT_EINTR_FUEL).run w1).2)
        cases hK : ((killBoxPg cap.proc pgid DEFAULT_EINTR_FUEL).run w1).1 with
        | ok u =>
          cases u
          dsimp only [allowedRawOpsStep]
          rw [hEnd]
          exact ⟨hWf, rfl, rfl, rfl, hVal, hKeyT⟩
        | error e =>
          have ⟨hKind, hMsg⟩ := hKE w1 hWf1 e hK
          dsimp only [allowedRawOpsStep]
          rw [hEnd]
          simp only [hVal, hKeyT, Bool.and_self, ↓reduceIte]
          exact ⟨hWf, trivial, trivial, trivial, hMsg, hKind⟩
  | pidfdKill bh =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, pidfdKillPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId bh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      simp only [hVal, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hWf, trivial, trivial, trivial, (mapRawError_invalidArg_spec _ _ _).2, rfl⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]
      dsimp only [toHostSysDeps]
      have ⟨hSome, hProj⟩ := tbl_findBoxKillInfo_spec hCap hWf bh.handleId
      let w1 := ((toHostTableOps cap).findBoxKillInfo bh.handleId).run w |>.2
      have hWf1 : rawHostWorldWf (proj w1) = true := by rw [hProj]; exact hWf
      cases hF : (((toHostTableOps cap).findBoxKillInfo bh.handleId).run w).1 with
      | none =>
        rw [hF] at hSome
        have hKeyF : tableHasKey bh.handleId (proj w).table.boxes = false := hSome.symm
        simp only [stateM_pure_run]
        change allowedRawOpsStep (proj w) (.pidfdKill bh) (.exceptUnit (.error _)) (proj w1)
        dsimp only [allowedRawOpsStep]
        rw [hProj]
        simp only [hVal, hKeyF, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hWf, trivial, trivial, trivial, (mapRawError_invalidArg_spec _ _ _).2, rfl⟩
      | some info =>
        rw [hF] at hSome
        have hKeyT : tableHasKey bh.handleId (proj w).table.boxes = true := hSome.symm
        rcases info with ⟨_, pidfd⟩
        dsimp only
        have ⟨hKP, hKE⟩ := killBoxPidfd_spec hCap pidfd DEFAULT_EINTR_FUEL
        have hEnd : proj ((killBoxPidfd cap.proc pidfd DEFAULT_EINTR_FUEL).run w1).2 = proj w := (hKP w1 hWf1).trans hProj
        change allowedRawOpsStep (proj w) (.pidfdKill bh)
          (.exceptUnit ((killBoxPidfd cap.proc pidfd DEFAULT_EINTR_FUEL).run w1).1)
          (proj ((killBoxPidfd cap.proc pidfd DEFAULT_EINTR_FUEL).run w1).2)
        cases hK : ((killBoxPidfd cap.proc pidfd DEFAULT_EINTR_FUEL).run w1).1 with
        | ok u =>
          cases u
          dsimp only [allowedRawOpsStep]
          rw [hEnd]
          exact ⟨hWf, rfl, rfl, rfl, hVal, hKeyT⟩
        | error e =>
          have ⟨hKind, hMsg⟩ := hKE w1 hWf1 e hK
          dsimp only [allowedRawOpsStep]
          rw [hEnd]
          simp only [hVal, hKeyT, Bool.and_self, ↓reduceIte]
          exact ⟨hWf, trivial, trivial, trivial, hMsg, hKind⟩
  | reapBox bh =>
    simp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM,
      mkRawOpsM, reapBoxPure, stateM_map_run]
    cases hVal : isValidSandboxHandleId bh.handleId with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      dsimp only [allowedRawOpsStep]
      simp only [hVal, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hWf, trivial, trivial, trivial, trivial, (mapRawError_invalidArg_spec _ _ _).2, rfl, trivial⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run]
      dsimp only [toHostSysDeps]
      have hDet := tbl_detachBox_spec hCap hWf bh.handleId
      rcases hDet with ⟨hWf1, hL1, hT1, hPl1, hFw1, hBody⟩
      let w1 := ((toHostTableOps cap).detachBox bh.handleId).run w |>.2
      cases hR : (((toHostTableOps cap).detachBox bh.handleId).run w).1 with
      | none =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyF, hEq⟩
        simp only [stateM_pure_run]
        dsimp only [allowedRawOpsStep]
        simp only [hVal, hKeyF, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hWf1, hL1, hT1, hPl1, hFw1, (mapRawError_invalidArg_spec _ _ _).2, rfl, hEq⟩
      | some bslot =>
        rw [hR] at hBody
        rcases hBody with ⟨hKeyT, hLen⟩
        let Q : Except SandboxError Unit → W → Prop :=
          fun out u => allowedRawOpsStep (proj w) (.reapBox bh) (.exceptUnit out) (proj u)
        have hPostCg : ∀ s, proj s = proj w1 →
            let tail : StateM W (Except SandboxError Unit) := do
              Files.closeOpt cap.files (some bslot.pidfd)
              match ← cleanupCgroupDir cap.files cap.timeRand bslot.cgroupDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL with
              | .ok () => pure (.ok ())
              | .error e => pure (.error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory")))
            Q (tail.run s).1 (tail.run s).2 := by
          intro s hEq
          dsimp only
          refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap (some bslot.pidfd)) fun _ s hEq => ?_
          refine preserves_bind_eq hEq hWf1 (preservesProj_cleanupCgroupDir hCap bslot.cgroupDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL) fun rCl s hEq => ?_
          cases rCl with
          | ok _ =>
            simp only [stateM_pure_run]
            dsimp only [Q, allowedRawOpsStep]
            exact ⟨by rw [hEq]; exact hWf1, by rw [hEq]; exact hL1, by rw [hEq]; exact hT1,
              by rw [hEq]; exact hPl1, by rw [hEq]; exact hFw1, hVal, hKeyT, by rw [hEq]; exact hLen⟩
          | error e =>
            simp only [stateM_pure_run]
            dsimp only [Q, allowedRawOpsStep]
            simp only [hVal, hKeyT, Bool.and_self, ↓reduceIte]
            exact ⟨by rw [hEq]; exact hWf1, by rw [hEq]; exact hL1, by rw [hEq]; exact hT1,
              by rw [hEq]; exact hPl1, by rw [hEq]; exact hFw1, mapRawError_ioError_ne_empty e _, rfl,
              by rw [hEq]; exact hLen⟩
        have hPostWait : ∀ s, proj s = proj w1 →
            let act : StateM W (Except SandboxError Unit) := do
              if bslot.pid > 0 && bslot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
                let _ ← LinuxSyscall.Process.waitpidReapLoop cap.proc bslot.pid.toInt32 DEFAULT_EINTR_FUEL
                pure ()
              Files.closeOpt cap.files (some bslot.pidfd)
              match ← cleanupCgroupDir cap.files cap.timeRand bslot.cgroupDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL with
              | .ok () => pure (.ok ())
              | .error e => pure (.error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory")))
            Q (act.run s).1 (act.run s).2 := by
          intro s hEq
          dsimp only
          cases hPid : (bslot.pid > 0 && bslot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID) with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hPostCg s hEq
          | true =>
            simp only [↓reduceIte]
            refine preserves_bind_eq hEq hWf1 (preservesProj_waitpidReapLoop hCap bslot.pid.toInt32 DEFAULT_EINTR_FUEL) fun _ s hEq => ?_
            exact hPostCg s hEq
        change Q _ _
        refine preserves_bind_eq (w := w1) rfl hWf1 (preservesProj_closeOpt hCap bslot.stdinFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap bslot.stdoutFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap bslot.stderrFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap bslot.statusFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeOpt hCap bslot.goFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf1 (preservesProj_closeFdArray hCap bslot.listenerFds) fun _ s hEq => ?_
        cases hCg : (!bslot.cgroupDir.isEmpty) with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hPostWait s hEq
        | true =>
          simp only [↓reduceIte]
          refine preserves_bind_eq hEq hWf1 (preservesProj_writeTextFile hCap (cgroupSubfile bslot.cgroupDir "cgroup.kill") "1" DEFAULT_EINTR_FUEL) fun _ s hEq => ?_
          exact hPostWait s hEq
  | activeResourceCounts =>
    have ⟨hCnt, hProj⟩ := tbl_counts_spec hCap hWf
    dsimp only [execRawOpsStep, Internal.mkOpsFromHostCapM, SysBridge.mkOpsFromHostCapM, mkRawOpsM]
    rw [stateM_map_run]
    dsimp only [allowedRawOpsStep]
    exact ⟨by rw [hProj]; exact hWf, by rw [hProj], by rw [hProj], hCnt, hProj⟩

/-- Concrete non-vacuity capability model over `StateM RawTableState` for any `(isLinux, target)` platform identity. -/
def modelRawHostCap (isLinux : Bool) (target : String) : RawHostCapM (StateM RawTableState) where
  files := {
    openat := fun _ _ _ _ => pure (.error Errno.ENOSYS)
    openat2 := fun _ _ _ => pure (.error Errno.ENOSYS)
    close := fun _ => pure (.ok ())
    read := fun _ _ => pure (.ok ByteArray.empty)
    write := fun _ bs => pure (.ok (UInt32.ofNat bs.size))
    fstat := fun _ => pure (.error Errno.ENOSYS)
    fstatat := fun _ _ _ => pure (.error Errno.ENOENT)
    faccessat := fun _ _ _ _ => pure (.error Errno.ENOENT)
    mkdirat := fun _ _ _ => pure (.error Errno.ENOSYS)
    unlinkat := fun _ _ _ => pure (.ok ())
    renameat2 := fun _ _ _ _ _ => pure (.error Errno.ENOSYS)
    symlinkat := fun _ _ _ => pure (.error Errno.ENOSYS)
    readlinkat := fun _ _ _ => pure (.error Errno.ENOSYS)
    getdents64 := fun _ _ => pure (.error Errno.ENOSYS)
    fchmodat := fun _ _ _ => pure (.error Errno.ENOSYS)
    fchmod := fun _ _ => pure (.error Errno.ENOSYS)
    flock := fun _ _ => pure (.error Errno.ENOSYS)
    fcntl := fun _ _ => pure (.ok 0)
    fsync := fun _ => pure (.ok ())
    getcwd := fun _ => pure (.error Errno.ENOSYS)
    lseek := fun _ _ _ => pure (.error Errno.ENOSYS)
    reopenReadOnly := fun fd => pure (.ok fd)
    dupStdio := fun _ => pure (.error Errno.ENOSYS)
  }
  net := {
    socket := fun _ _ _ _ => pure (.error Errno.ENOSYS)
    socketpair := fun _ _ _ => pure (.error Errno.ENOSYS)
    bind := fun _ _ => pure (.error Errno.ENOSYS)
    listen := fun _ _ => pure (.error Errno.ENOSYS)
    accept4 := fun _ _ => pure (.error Errno.ENOSYS)
    connect := fun _ _ => pure (.error Errno.ENOSYS)
    getsockopt := fun _ _ => pure (.error Errno.ENOSYS)
    setsockopt := fun _ _ _ => pure (.error Errno.ENOSYS)
    getsockname := fun _ => pure (.error Errno.ENOSYS)
    recvfrom := fun _ _ _ => pure (.error Errno.ENOSYS)
    sendto := fun _ _ _ => pure (.error Errno.ENOSYS)
    shutdown := fun _ _ => pure (.error Errno.ENOSYS)
    sendmsg := fun _ _ => pure (.error Errno.ENOSYS)
    recvmsg := fun _ _ => pure (.error Errno.ENOSYS)
    ioctl := fun _ _ _ => pure (.error Errno.ENOSYS)
  }
  poll := {
    ppoll := fun entries _ => pure (.ok (entries.map fun _ => ({} : Poll.PollEvents)))
    eventfd2 := fun _ _ => pure (.error Errno.ENOSYS)
  }
  proc := {
    pipe2 := fun _ => pure (.error Errno.EMFILE)
    waitpid := fun _ _ => pure (.error Errno.ECHILD)
    kill := fun _ _ => pure (.ok ())
    pidfd_open := fun _ _ => pure (.error Errno.ENOSYS)
    pidfd_send_signal := fun _ _ _ => pure (.ok ())
    getpid := pure (.ok 1)
    getuid := pure (.ok 1000)
  }
  sandbox := {
    landlockCreateRuleset := fun _ _ => pure (.error Errno.ENOSYS)
    landlockAddRule := fun _ _ => pure (.error Errno.ENOSYS)
    landlockRestrictSelf := fun _ => pure (.error Errno.ENOSYS)
    seccomp := fun _ _ _ => pure (.error Errno.ENOSYS)
    prctl := fun _ => pure (.error Errno.ENOSYS)
    setrlimit := fun _ _ _ => pure (.error Errno.ENOSYS)
    memfdCreate := fun _ _ => pure (.error Errno.ENOMEM)
  }
  timeRand := {
    clock_gettime := fun _ => pure (.ok { sec := 1, nsec := 0 })
    clock_nanosleep := fun _ _ _ => pure (.ok ())
    getrandom := fun _ _ => pure (.error Errno.ENOSYS)
  }
  passwd := {
    getpwuid := fun _ => pure (.ok none)
    getpwnam := fun _ => pure (.ok none)
  }
  postFork := {
    spawn := fun _ => pure (.error { kind := .sysError, message := "model" })
    spawnWithBarrier := fun _ => pure (.error { kind := .sysError, message := "model" })
    releaseBarrier := fun _ => pure (.error { kind := .sysError, message := "model" })
    abortBarrier := fun _ => pure (.error { kind := .sysError, message := "model" })
  }
  isLinux := isLinux
  target := target
  getEnvPath := pure none
  getEnvHome := pure none
  startFwdTask := fun _ _ => pure (.error Errno.EMFILE)
  stopFwdTask := fun _ => pure ()
  getTable := fun t => (t, t)
  modifyTable := fun f t => (t, f t)

/-- Non-vacuity witness: `modelRawHostCap` satisfies `allowedRawCapStep` for every platform `(isLinux, target)`. -/
theorem modelRawHostCap_refines_allowedRawCapStep (isLinux : Bool) (target : String) :
    Core.ObeysStep (fun t : RawTableState => ({ isLinux := isLinux, target := target, table := t } : RawHostWorld))
      rawHostWorldWf (execRawCapStep (modelRawHostCap isLinux target)) allowedRawCapStep := by
  intro t req _
  cases req <;> exact ⟨rfl, rfl⟩

end LeanSwe.ProcessSandbox.Raw.Proofs

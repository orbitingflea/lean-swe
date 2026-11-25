import Core.ConcOps
import LeanSwe.ProcessSandbox.Raw.Model.FullStep
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Proofs.FullObeysHelpers
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesModel

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge

private theorem cell_get_spec {W : Type} {Ref TaskH : Type → Type}
    {projRaw : W → HealthyRawSysWorld}
    {projCell : W → HostCellState Ref TaskH}
    {cell : Core.StateCellM (StateM W) (HostCellState Ref TaskH)}
    (hCell : Core.ObeysStateCell projRaw projCell cell)
    {w : W} (_hWf : rawHostWorldWf (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))) = true) :
    (cell.get.run w).1 = projCell w ∧
    mapFullToRawWorld (projRaw (cell.get.run w).2) (cellToRawTable (projCell (cell.get.run w).2)) =
      mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
  have ⟨hVal, hC, hR⟩ := hCell.1 w
  change (cell.get w).1 = projCell w ∧
    mapFullToRawWorld (projRaw (cell.get w).2) (cellToRawTable (projCell (cell.get w).2)) =
      mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))
  exact ⟨hVal, by rw [hR, hC]⟩

private theorem cell_modifyGet_spec {W α : Type} {Ref TaskH : Type → Type}
    {projRaw : W → HealthyRawSysWorld}
    {projCell : W → HostCellState Ref TaskH}
    {cell : Core.StateCellM (StateM W) (HostCellState Ref TaskH)}
    (hCell : Core.ObeysStateCell projRaw projCell cell)
    {w : W} (hWf : rawHostWorldWf (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))) = true)
    (step : HostCellState Ref TaskH → α × HostCellState Ref TaskH) :
    let r := (cell.modifyGet step).run w
    r.1 = (step (projCell w)).1 ∧
    (projRaw w).wf = true ∧
    mapFullToRawWorld (projRaw r.2) (cellToRawTable (projCell r.2)) =
      { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
        table := cellTableToModel (step (projCell w)).2 } := by
  have hSys : (projRaw w).wf = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
  have ⟨hVal, hC, hR⟩ := hCell.2 step w
  change (cell.modifyGet step w).1 = (step (projCell w)).1 ∧
    (projRaw w).wf = true ∧
    mapFullToRawWorld (projRaw (cell.modifyGet step w).2) (cellToRawTable (projCell (cell.modifyGet step w).2)) =
      { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
        table := cellTableToModel (step (projCell w)).2 }
  refine ⟨hVal, hSys, ?_⟩
  rw [hR, hC]
  simp only [mapFullToRawWorld, cellToRawTable, hSys, ↓reduceIte]

/-- `mkCellTableOps cell` satisfies `TblObeysRawWorld` under `ObeysStateCell projRaw projCell cell`. -/
theorem tblObeysRawWorld_mkCellTableOps {W : Type} {Ref TaskH : Type → Type}
    {projRaw : W → HealthyRawSysWorld}
    {projCell : W → HostCellState Ref TaskH}
    {cell : Core.StateCellM (StateM W) (HostCellState Ref TaskH)}
    (hCell : Core.ObeysStateCell projRaw projCell cell) :
    TblObeysRawWorld
      (fun w => mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)))
      (mkCellTableOps cell) where
  counts {w} hWf := by
    have hSys : (projRaw w).wf = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
    have ⟨hVal, hEq⟩ := cell_get_spec hCell hWf
    dsimp only [mkCellTableOps]
    rw [stateM_bind_run, stateM_pure_run]
    refine ⟨?_, hEq⟩
    rw [hVal]
    simp [countsPure, mapFullToRawWorld, cellToRawTable, cellTableToModel, tableCounts, hSys]
  nextCgSeq {w} hWf := by
    have ⟨_, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf nextCgSeqPure
    have hEqTbl : cellTableToModel (nextCgSeqPure (projCell w)).2 =
        { (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table with
          cgSeq := (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.cgSeq + 1 } := by
      simp [nextCgSeqPure, mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]
    have hP : mapFullToRawWorld (projRaw ((mkCellTableOps cell).nextCgSeq.run w).2)
        (cellToRawTable (projCell ((mkCellTableOps cell).nextCgSeq.run w).2)) =
        { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := { (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table with
            cgSeq := (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.cgSeq + 1 } } := by
      dsimp only [mkCellTableOps]; rw [hProj, hEqTbl]
    refine ⟨hP, ?_⟩
    rw [hP, rawHostWorldWf_iff]
    exact (rawHostWorldWf_iff _).mp hWf
  findPlan {w} hWf hid := by
    have hSys : (projRaw w).wf = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
    have ⟨hVal, hEq⟩ := cell_get_spec hCell hWf
    dsimp only [mkCellTableOps]
    rw [stateM_bind_run, stateM_pure_run]
    refine ⟨?_, hEq⟩
    rw [hVal, assocFind_isSome_eq_tableHasKey]
    simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys]
  findBoxKillInfo {w} hWf hid := by
    have hSys : (projRaw w).wf = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
    have ⟨hVal, hEq⟩ := cell_get_spec hCell hWf
    dsimp only [mkCellTableOps]
    rw [stateM_bind_run, stateM_pure_run]
    refine ⟨?_, hEq⟩
    rw [hVal, Option.isSome_map, assocFind_isSome_eq_tableHasKey]
    simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys]
  insertPlan {w} hWf slot := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (insertPlanPure · slot)
    dsimp only [mkCellTableOps]
    rw [hProj, hVal]
    have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    have hNid : (projCell w).nextId = (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.nextId := by
      simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]
    unfold insertPlanPure allocHandleIdPure
    dsimp only
    cases hId : isValidSandboxHandleId (projCell w).nextId with
    | true =>
      simp only [↓reduceIte]
      have hIdM : isValidSandboxHandleId (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.nextId = true := by
        rw [← hNid]; exact hId
      refine ⟨?_, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        hId, hNid,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by dsimp only [cellTableToModel]; omega, ?_,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hBx,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
      simp only [cellTableToModel, List.map_cons, List.all_cons, Bool.and_eq_true, hId, true_and]
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel (projCell w) } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      exact ⟨hWf, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, hSys], rfl⟩
  detachPlan {w} hWf hid := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (detachPlanPure · hid)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold detachPlanPure
    cases hRem : (assocRemove hid (projCell w).plans).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (projCell w).plans hRem
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel { projCell w with plans := (assocRemove hid (projCell w).plans).2 } } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        rw [hEq]; simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      refine ⟨hWf, rfl, rfl, rfl, rfl, ?_, rfl⟩
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (projCell w).plans slot hRem
      refine ⟨?_, rfl, rfl,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hLen⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hN,
        ?_,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hBx,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
      dsimp only [cellTableToModel]
      rw [list_all_keys_map_snd]
      exact hAll _ (by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, list_all_keys_map_snd, hSys] using hPl)
  insertBox {w} hWf slot := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (insertBoxPure · slot)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    have hNid : (projCell w).nextId = (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.nextId := by
      simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]
    unfold insertBoxPure allocHandleIdPure
    dsimp only
    cases hId : isValidSandboxHandleId (projCell w).nextId with
    | true =>
      simp only [↓reduceIte]
      refine ⟨?_, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        hId, hNid,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by dsimp only [cellTableToModel]; omega,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
        ?_,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
      simp only [cellTableToModel, List.map_cons, List.all_cons, Bool.and_eq_true, hId, true_and]
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hBx
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel (projCell w) } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      exact ⟨hWf, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, hSys], rfl⟩
  detachBox {w} hWf hid := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (detachBoxPure · hid)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold detachBoxPure
    cases hRem : (assocRemove hid (projCell w).boxes).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (projCell w).boxes hRem
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel { projCell w with boxes := (assocRemove hid (projCell w).boxes).2 } } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        rw [hEq]; simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      refine ⟨hWf, rfl, rfl, rfl, rfl, ?_, rfl⟩
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (projCell w).boxes slot hRem
      refine ⟨?_, rfl, rfl,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hLen⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hN,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
        ?_,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
      dsimp only [cellTableToModel]
      rw [list_all_keys_map_snd]
      exact hAll _ (by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, list_all_keys_map_snd, hSys] using hBx)
  takeBoxListeners {w} hWf hid expected := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (takeBoxListenersPure · hid expected)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold takeBoxListenersPure
    cases hF : assocFind hid (projCell w).boxes with
    | none =>
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel (projCell w) } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]; exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some slot =>
      cases hBad : (slot.fwdsTaken || slot.listenerFds.size != expected) with
      | true =>
        simp only [hBad, ↓reduceIte]
        have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
            table := cellTableToModel (projCell w) } =
            mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
          simp [mapFullToRawWorld, cellToRawTable, hSys]
        rw [hSame]
        exact ⟨hWf, trivial, trivial,
          by simp [mapFullToRawWorld, cellToRawTable, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, hSys], rfl⟩
      | false =>
        simp only [hBad, Bool.false_eq_true, ↓reduceIte]
        have hKey : tableHasKey hid (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.boxes = true := by
          have h1 := assocFind_isSome_eq_tableHasKey hid (projCell w).boxes
          rw [hF] at h1
          simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using h1.symm
        have hPres := list_map_key_cond_preserves hid
          (fun b : BoxSlotM RawFd => { b with fwdsTaken := true, listenerFds := #[] })
          (projCell w).boxes
        refine ⟨?_, trivial, trivial,
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          hKey⟩
        rw [rawHostWorldWf_iff]
        refine ⟨by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hN,
          by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
          ?_,
          by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
        dsimp only [cellTableToModel]
        rw [list_all_keys_map_snd, hPres.2 isValidSandboxHandleId]
        simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, list_all_keys_map_snd, hSys] using hBx
  takeBoxIo {w} hWf hid := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (takeBoxIoPure · hid)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold takeBoxIoPure
    cases hF : assocFind hid (projCell w).boxes with
    | none =>
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel (projCell w) } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]; exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some slot =>
      cases hRs : slot.readStarted with
      | true =>
        simp only [hRs, ↓reduceIte]
        have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
            table := cellTableToModel (projCell w) } =
            mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
          simp [mapFullToRawWorld, cellToRawTable, hSys]
        rw [hSame]
        exact ⟨hWf, trivial, trivial,
          by simp [mapFullToRawWorld, cellToRawTable, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, hSys], rfl⟩
      | false =>
        simp only [hRs, Bool.false_eq_true, ↓reduceIte]
        have hKey : tableHasKey hid (mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))).table.boxes = true := by
          have h1 := assocFind_isSome_eq_tableHasKey hid (projCell w).boxes
          rw [hF] at h1
          simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using h1.symm
        have hPres := list_map_key_cond_preserves hid
          (fun b : BoxSlotM RawFd => { b with readStarted := true, stdinFd? := none, stdoutFd? := none, stderrFd? := none, statusFd? := none, goFd? := none })
          (projCell w).boxes
        refine ⟨?_, trivial, trivial,
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
          hKey⟩
        rw [rawHostWorldWf_iff]
        refine ⟨by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hN,
          by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
          ?_,
          by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw⟩
        dsimp only [cellTableToModel]
        rw [list_all_keys_map_snd, hPres.2 isValidSandboxHandleId]
        simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, list_all_keys_map_snd, hSys] using hBx
  insertFwd {w} hWf slot := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (insertFwdPure · slot)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold insertFwdPure allocHandleIdPure
    dsimp only
    cases hId : isValidSandboxHandleId (projCell w).nextId with
    | true =>
      simp only [↓reduceIte]
      refine ⟨?_, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        hId,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys]⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by dsimp only [cellTableToModel]; omega,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hBx,
        ?_⟩
      simp only [cellTableToModel, List.map_cons, List.all_cons, Bool.and_eq_true, hId, true_and]
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hFw
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel (projCell w) } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      exact ⟨hWf, trivial, trivial,
        by simp [mapFullToRawWorld, cellToRawTable, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, hSys], rfl⟩
  detachFwd {w} hWf hid := by
    have ⟨hVal, hSys, hProj⟩ := cell_modifyGet_spec hCell hWf (detachFwdPure · hid)
    dsimp only [mkCellTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff _).mp hWf
    unfold detachFwdPure
    cases hRem : (assocRemove hid (projCell w).forwarders).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (projCell w).forwarders hRem
      have hSame : { mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) with
          table := cellTableToModel { projCell w with forwarders := (assocRemove hid (projCell w).forwarders).2 } } =
          mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)) := by
        rw [hEq]; simp [mapFullToRawWorld, cellToRawTable, hSys]
      rw [hSame]
      refine ⟨hWf, rfl, rfl, rfl, rfl, ?_, rfl⟩
      simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (projCell w).forwarders slot hRem
      refine ⟨?_, rfl, rfl,
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simp [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys],
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, tableHasKey_map_snd, hSys] using hKey,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hLen⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hN,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hPl,
        by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, hSys] using hBx,
        ?_⟩
      dsimp only [cellTableToModel]
      rw [list_all_keys_map_snd]
      exact hAll _ (by simpa [mapFullToRawWorld, cellToRawTable, cellTableToModel, list_all_keys_map_snd, hSys] using hFw)

/-- End-to-end `Core.ObeysStepFromConcCell` theorem for `Internal.mkFullOpsM` over `FullSysOpsM`,
    `Core.ConcOpsM`, and `Core.StateCellM`. -/
theorem obeysStepFromConcCell_mkFullOpsM :
    Core.ObeysStepFromConcCell (CellS := HostCellState)
      Model.mapFullToRawWorld Model.cellToRawTable
      Model.fullWorldWf Model.execFullRawStep Model.allowedFullRawStep
      Model.rawHostWorldWf Internal.mkFullOpsM
      Model.execPkgStep Model.allowedPkgStep := by
  intro W projRaw raw conc projCell cell hRaw hRawFrame hConc hCell
  exact mkRawOpsM_refines_allowedRawOpsStep
    (depsPreservesProj_mkSafeSysDepsM hRaw hRawFrame hConc)
    (tblObeysRawWorld_mkCellTableOps hCell)

end LeanSwe.ProcessSandbox.Raw.Proofs

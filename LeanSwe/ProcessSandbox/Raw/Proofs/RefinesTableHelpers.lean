import LeanSwe.ProcessSandbox.Raw.SysBridge.HostCap
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge

/-- Abstract behavioral specification of `HostTableOpsM (StateM W) fd fwdTask` relative to `proj : W → RawHostWorld`. -/
structure TblObeysRawWorld {W fd fwdTask : Type} (proj : W → RawHostWorld)
    (tbl : HostTableOpsM (StateM W) fd fwdTask) : Prop where
  /-- `counts` returns `tableCounts (proj w).table` and preserves `proj w`. -/
  counts : ∀ {w : W}, rawHostWorldWf (proj w) = true →
    (tbl.counts.run w).1 = tableCounts (proj w).table ∧ proj (tbl.counts.run w).2 = proj w
  /-- `nextCgSeq` increments `cgSeq` and preserves `rawHostWorldWf` and all handle tables. -/
  nextCgSeq : ∀ {w : W}, rawHostWorldWf (proj w) = true →
    let w' := (tbl.nextCgSeq.run w).2
    proj w' = { proj w with table := { (proj w).table with cgSeq := (proj w).table.cgSeq + 1 } } ∧
    rawHostWorldWf (proj w') = true
  /-- `findPlan` preserves `proj w` and returns `some` iff `tableHasKey hid (proj w).table.plans`. -/
  findPlan : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    ((tbl.findPlan hid).run w).1.isSome = tableHasKey hid (proj w).table.plans ∧
    proj ((tbl.findPlan hid).run w).2 = proj w
  /-- `findBoxKillInfo` preserves `proj w` and returns `some` iff `tableHasKey hid (proj w).table.boxes`. -/
  findBoxKillInfo : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    ((tbl.findBoxKillInfo hid).run w).1.isSome = tableHasKey hid (proj w).table.boxes ∧
    proj ((tbl.findBoxKillInfo hid).run w).2 = proj w
  /-- `insertPlan` allocates `nextId` and adds 1 plan on `some`, or preserves `proj w` on `none`. -/
  insertPlan : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ slot : PlanSlotM fd,
    let r := (tbl.insertPlan slot).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.boxes = (proj w).table.boxes ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    match r.1 with
    | none => proj r.2 = proj w
    | some hid =>
      isValidSandboxHandleId hid = true ∧ hid = (proj w).table.nextId ∧
      (proj r.2).table.plans.length = (proj w).table.plans.length + 1
  /-- `detachPlan` removes `hid` on `some` or preserves `proj w` with `tableHasKey = false` on `none`. -/
  detachPlan : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    let r := (tbl.detachPlan hid).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.boxes = (proj w).table.boxes ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    match r.1 with
    | none => tableHasKey hid (proj w).table.plans = false ∧ proj r.2 = proj w
    | some _ => tableHasKey hid (proj w).table.plans = true ∧ (proj r.2).table.plans.length + 1 = (proj w).table.plans.length
  /-- `insertBox` allocates `nextId` and adds 1 box on `some`, or preserves `proj w` on `none`. -/
  insertBox : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ slot : BoxSlotM fd,
    let r := (tbl.insertBox slot).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    match r.1 with
    | none => proj r.2 = proj w
    | some hid =>
      isValidSandboxHandleId hid = true ∧ hid = (proj w).table.nextId ∧
      (proj r.2).table.boxes.length = (proj w).table.boxes.length + 1
  /-- `detachBox` removes `hid` on `some` or preserves `proj w` with `tableHasKey = false` on `none`. -/
  detachBox : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    let r := (tbl.detachBox hid).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    match r.1 with
    | none => tableHasKey hid (proj w).table.boxes = false ∧ proj r.2 = proj w
    | some _ => tableHasKey hid (proj w).table.boxes = true ∧ (proj r.2).table.boxes.length + 1 = (proj w).table.boxes.length
  /-- `takeBoxListeners` claims listeners preserving `boxes.length`, or preserves `proj w` on `none`. -/
  takeBoxListeners : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid expected : Nat,
    let r := (tbl.takeBoxListeners hid expected).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    (proj r.2).table.boxes.length = (proj w).table.boxes.length ∧
    match r.1 with
    | none => proj r.2 = proj w
    | some _ => tableHasKey hid (proj w).table.boxes = true
  /-- `takeBoxIo` claims box I/O pipes preserving `boxes.length`, or preserves `proj w` on `none`. -/
  takeBoxIo : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    let r := (tbl.takeBoxIo hid).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.fwds = (proj w).table.fwds ∧
    (proj r.2).table.boxes.length = (proj w).table.boxes.length ∧
    match r.1 with
    | none => proj r.2 = proj w
    | some _ => tableHasKey hid (proj w).table.boxes = true
  /-- `insertFwd` allocates a valid handle ID and adds 1 forwarder on `some`, or preserves `proj w` on `none`. -/
  insertFwd : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ slot : ForwarderSlotM fwdTask,
    let r := (tbl.insertFwd slot).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.boxes = (proj w).table.boxes ∧
    match r.1 with
    | none => proj r.2 = proj w
    | some hid =>
      isValidSandboxHandleId hid = true ∧
      (proj r.2).table.fwds.length = (proj w).table.fwds.length + 1
  /-- `detachFwd` removes `hid` on `some` or preserves `proj w` with `tableHasKey = false` on `none`. -/
  detachFwd : ∀ {w : W}, rawHostWorldWf (proj w) = true → ∀ hid : Nat,
    let r := (tbl.detachFwd hid).run w
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = (proj w).isLinux ∧ (proj r.2).target = (proj w).target ∧
    (proj r.2).table.plans = (proj w).table.plans ∧ (proj r.2).table.boxes = (proj w).table.boxes ∧
    match r.1 with
    | none => tableHasKey hid (proj w).table.fwds = false ∧ proj r.2 = proj w
    | some _ => tableHasKey hid (proj w).table.fwds = true ∧ (proj r.2).table.fwds.length + 1 = (proj w).table.fwds.length

/-- `fromSysPlanSlot ∘ toSysPlanSlot` is the identity. -/
theorem fromSysPlanSlot_toSysPlanSlot (r : RawPlanRecord) : fromSysPlanSlot (toSysPlanSlot r) = r := by
  cases r; rfl

/-- `fromSysBoxSlot ∘ toSysBoxSlot` is the identity. -/
theorem fromSysBoxSlot_toSysBoxSlot (r : RawBoxRecord) : fromSysBoxSlot (toSysBoxSlot r) = r := by
  cases r; rfl

/-- `fromSysFwdSlot ∘ toSysFwdSlot` is the identity. -/
theorem fromSysFwdSlot_toSysFwdSlot (r : RawFwdRecord) : fromSysFwdSlot (toSysFwdSlot r) = r := by
  cases r; rfl

/-- Mapping a pair-value function over an association list and its inverse is the identity. -/
theorem list_map_snd_comp {α β : Type} (f : α → β) (g : β → α) (hfg : ∀ x, g (f x) = x)
    (xs : List (Nat × α)) :
    (xs.map fun (k, v) => (k, f v)).map (fun (k, v) => (k, g v)) = xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨k, v⟩; simp [hfg, ih]

/-- `fromSysTable (toSysTable t) = t`. -/
theorem fromSysTable_toSysTable (t : RawTableState) : fromSysTable (toSysTable t) = t := by
  cases t
  simp only [fromSysTable, toSysTable,
    list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
    list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot,
    list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]

/-- Mapping values in an association list preserves `tableHasKey`. -/
theorem tableHasKey_map_snd {α β : Type} (hid : Nat) (f : α → β) (xs : List (Nat × α)) :
    tableHasKey hid (xs.map fun (k, v) => (k, f v)) = tableHasKey hid xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, tableHasKey, List.any_cons]
    exact congrArg (fun b => (k == hid) || b) ih

/-- Mapping values in an association list preserves key predicates under `List.all`. -/
theorem list_all_keys_map_snd {α β : Type} (P : Nat → Bool) (f : α → β) (xs : List (Nat × α)) :
    (xs.map fun (k, v) => (k, f v)).all (fun p => P p.1) = xs.all (fun p => P p.1) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.all_cons]
    exact congrArg (fun b => P k && b) ih

/-- `(assocFind hid xs).isSome` equals `tableHasKey hid xs`. -/
theorem assocFind_isSome_eq_tableHasKey {α : Type} (hid : Nat) (xs : List (Nat × α)) :
    (assocFind hid xs).isSome = tableHasKey hid xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [assocFind, tableHasKey, List.any_cons]
    cases (k == hid)
    · simpa [tableHasKey] using ih
    · rfl

/-- `assocRemove` returning `none` leaves the list unchanged and implies `tableHasKey = false`. -/
theorem assocRemove_none {α : Type} (hid : Nat) :
    ∀ (xs : List (Nat × α)), (assocRemove hid xs).1 = none →
      (assocRemove hid xs).2 = xs ∧ tableHasKey hid xs = false
  | [], _ => ⟨rfl, rfl⟩
  | (k, v) :: rest, h => by
    unfold assocRemove at h ⊢
    cases hk : (k == hid)
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have ⟨hEq, hKey⟩ := assocRemove_none hid rest h
      exact ⟨by simp [hEq], by simp only [tableHasKey, List.any_cons, hk, Bool.false_or]; exact hKey⟩
    · simp [hk] at h

/-- `assocRemove` returning `some v` implies `tableHasKey = true`, decrements length by 1, and preserves key predicates. -/
theorem assocRemove_some {α : Type} (hid : Nat) :
    ∀ (xs : List (Nat × α)) (v : α), (assocRemove hid xs).1 = some v →
      tableHasKey hid xs = true ∧
      (assocRemove hid xs).2.length + 1 = xs.length ∧
      (∀ P : Nat → Bool, xs.all (fun p => P p.1) = true →
        (assocRemove hid xs).2.all (fun p => P p.1) = true)
  | [], _, h => by cases h
  | (k, v0) :: rest, v, h => by
    unfold assocRemove at h ⊢
    cases hk : (k == hid)
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid rest v h
      refine ⟨by simp only [tableHasKey, List.any_cons, hk, Bool.false_or]; exact hKey,
        by simp [hLen], fun P hP => ?_⟩
      simp only [List.all_cons, Bool.and_eq_true] at hP ⊢
      exact ⟨hP.1, hAll P hP.2⟩
    · simp only [hk, ↓reduceIte] at h ⊢
      refine ⟨by simp only [tableHasKey, List.any_cons, hk, Bool.true_or], by simp, fun P hP => ?_⟩
      simp only [List.all_cons, Bool.and_eq_true] at hP
      exact hP.2

/-- Updating entries matching `hid` preserves list length and key predicates. -/
theorem list_map_key_cond_preserves {α : Type} (hid : Nat) (f : α → α) (xs : List (Nat × α)) :
    (xs.map fun (k, v) => if k == hid then (k, f v) else (k, v)).length = xs.length ∧
    ∀ P : Nat → Bool,
      (xs.map fun (k, v) => if k == hid then (k, f v) else (k, v)).all (fun p => P p.1) =
        xs.all (fun p => P p.1) := by
  constructor
  · simp
  · intro P
    induction xs with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨k, v⟩
      simp only [List.map_cons, List.all_cons]
      cases (k == hid) <;> exact congrArg (fun b => P k && b) ih

/-- Well-formedness characterization for `RawHostWorld`. -/
theorem rawHostWorldWf_iff (w : RawHostWorld) :
    rawHostWorldWf w = true ↔
      0 < w.table.nextId ∧
      w.table.plans.all (fun p => isValidSandboxHandleId p.1) = true ∧
      w.table.boxes.all (fun b => isValidSandboxHandleId b.1) = true ∧
      w.table.fwds.all (fun f => isValidSandboxHandleId f.1) = true := by
  simp [rawHostWorldWf, Bool.and_eq_true, and_assoc]

private theorem cap_getTable_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    {w : W} (hWf : rawHostWorldWf (proj w) = true) :
    (cap.getTable.run w).1 = (proj w).table ∧ proj (cap.getTable.run w).2 = proj w := by
  have h := hCap w .getTable hWf
  simpa only [execRawCapStep, stateM_map_run, allowedRawCapStep, RawCapStepOut.table.injEq] using h

private theorem tbl_modify_run {W α : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    {w : W} (hWf : rawHostWorldWf (proj w) = true)
    (step : HostTableState Nat Nat → α × HostTableState Nat Nat) :
    let act : StateM W α := do
      let st ← cap.modifyTable fun s => fromSysTable (step (toSysTable s)).2
      return (step (toSysTable st)).1
    (act.run w).1 = (step (toSysTable (proj w).table)).1 ∧
    proj (act.run w).2 = { proj w with table := fromSysTable (step (toSysTable (proj w).table)).2 } := by
  have h := hCap w (.modifyTable fun s => fromSysTable (step (toSysTable s)).2) hWf
  simp only [execRawCapStep, stateM_map_run, allowedRawCapStep, RawCapStepOut.table.injEq] at h
  exact ⟨by simp only [stateM_bind_run, stateM_pure_run, h.1],
    by simpa only [stateM_bind_run, stateM_pure_run] using h.2⟩

/-- Bridge `ObeysStep` on `RawHostCapM` to `TblObeysRawWorld` on `toHostTableOps cap`. -/
theorem tblObeysRawWorld_toHostTableOps {W : Type} {proj : W → RawHostWorld}
    {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) :
    TblObeysRawWorld proj (toHostTableOps cap) where
  counts {w} hWf := by
    have ⟨hT, hP⟩ := cap_getTable_spec hCap hWf
    dsimp only [toHostTableOps]; rw [stateM_bind_run, stateM_pure_run, hT]
    exact ⟨by simp [countsPure, toSysTable, tableCounts], hP⟩
  nextCgSeq {w} hWf := by
    have hM := (tbl_modify_run hCap hWf nextCgSeqPure).2
    have hEq : fromSysTable (nextCgSeqPure (toSysTable (proj w).table)).2 =
        { (proj w).table with cgSeq := (proj w).table.cgSeq + 1 } := by
      cases (proj w).table
      simp [nextCgSeqPure, fromSysTable, toSysTable,
        list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
        list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot,
        list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
    have hProj : proj ((toHostTableOps cap).nextCgSeq.run w).2 =
        { proj w with table := { (proj w).table with cgSeq := (proj w).table.cgSeq + 1 } } := by
      rw [← hEq]; exact hM
    exact ⟨hProj, by rw [hProj, rawHostWorldWf_iff]; exact (rawHostWorldWf_iff (proj w)).mp hWf⟩
  findPlan {w} hWf hid := by
    have ⟨hT, hP⟩ := cap_getTable_spec hCap hWf
    dsimp only [toHostTableOps]; rw [stateM_bind_run, stateM_pure_run, hT]
    exact ⟨by simp [toSysTable, assocFind_isSome_eq_tableHasKey, tableHasKey_map_snd], hP⟩
  findBoxKillInfo {w} hWf hid := by
    have ⟨hT, hP⟩ := cap_getTable_spec hCap hWf
    dsimp only [toHostTableOps]; rw [stateM_bind_run, stateM_pure_run, hT]
    exact ⟨by simp [toSysTable, Option.isSome_map, assocFind_isSome_eq_tableHasKey, tableHasKey_map_snd], hP⟩
  insertPlan {w} hWf slot := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => insertPlanPure s slot)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    unfold insertPlanPure allocHandleIdPure; dsimp only [toSysTable]
    cases hId : isValidSandboxHandleId (proj w).table.nextId with
    | true =>
      have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
      simp only [↓reduceIte, fromSysTable, List.map_cons, List.length_cons, List.length_map,
        list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot,
        list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
      refine ⟨?_, trivial, trivial, trivial, trivial, hId, trivial, trivial⟩
      rw [rawHostWorldWf_iff]
      refine ⟨by dsimp only; omega, ?_, hBx, hFw⟩
      simp only [List.all_cons, Bool.and_eq_true, hId, true_and]
      rw [list_all_keys_map_snd, list_all_keys_map_snd]; exact hPl
    | false =>
      have hRt : fromSysTable (toSysTable (proj w).table) = (proj w).table := fromSysTable_toSysTable _
      dsimp only [toSysTable] at hRt; simp only [Bool.false_eq_true, ↓reduceIte, hRt]
      exact ⟨hWf, trivial, trivial, trivial, trivial, trivial⟩
  detachPlan {w} hWf hid := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => detachPlanPure s hid)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
    unfold detachPlanPure
    cases hRem : (assocRemove hid (toSysTable (proj w).table).plans).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (toSysTable (proj w).table).plans hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      have hEq' : fromSysTable { toSysTable (proj w).table with plans := (assocRemove hid (toSysTable (proj w).table).plans).2 } = (proj w).table := by
        rw [hEq]; exact fromSysTable_toSysTable _
      rw [hEq']; exact ⟨hWf, rfl, rfl, rfl, rfl, hKey, rfl⟩
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (toSysTable (proj w).table).plans slot hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      dsimp only [fromSysTable, toSysTable]
      rw [list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot,
        list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
      refine ⟨?_, rfl, rfl, rfl, rfl, hKey, by simpa [toSysTable] using hLen⟩
      rw [rawHostWorldWf_iff]; refine ⟨hN, ?_, hBx, hFw⟩
      rw [list_all_keys_map_snd]; exact hAll _ (by rw [toSysTable, list_all_keys_map_snd]; exact hPl)
  insertBox {w} hWf slot := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => insertBoxPure s slot)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    unfold insertBoxPure allocHandleIdPure; dsimp only [toSysTable]
    cases hId : isValidSandboxHandleId (proj w).table.nextId with
    | true =>
      have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
      simp only [↓reduceIte, fromSysTable, List.map_cons, List.length_cons, List.length_map,
        list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
        list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
      refine ⟨?_, trivial, trivial, trivial, trivial, hId, trivial, trivial⟩
      rw [rawHostWorldWf_iff]; refine ⟨by dsimp only; omega, hPl, ?_, hFw⟩
      simp only [List.all_cons, Bool.and_eq_true, hId, true_and]
      rw [list_all_keys_map_snd, list_all_keys_map_snd]; exact hBx
    | false =>
      have hRt : fromSysTable (toSysTable (proj w).table) = (proj w).table := fromSysTable_toSysTable _
      dsimp only [toSysTable] at hRt; simp only [Bool.false_eq_true, ↓reduceIte, hRt]
      exact ⟨hWf, trivial, trivial, trivial, trivial, trivial⟩
  detachBox {w} hWf hid := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => detachBoxPure s hid)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
    unfold detachBoxPure
    cases hRem : (assocRemove hid (toSysTable (proj w).table).boxes).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (toSysTable (proj w).table).boxes hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      have hEq' : fromSysTable { toSysTable (proj w).table with boxes := (assocRemove hid (toSysTable (proj w).table).boxes).2 } = (proj w).table := by
        rw [hEq]; exact fromSysTable_toSysTable _
      rw [hEq']; exact ⟨hWf, rfl, rfl, rfl, rfl, hKey, rfl⟩
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (toSysTable (proj w).table).boxes slot hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      dsimp only [fromSysTable, toSysTable]
      rw [list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
        list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
      refine ⟨?_, rfl, rfl, rfl, rfl, hKey, by simpa [toSysTable] using hLen⟩
      rw [rawHostWorldWf_iff]; refine ⟨hN, hPl, ?_, hFw⟩
      rw [list_all_keys_map_snd]; exact hAll _ (by rw [toSysTable, list_all_keys_map_snd]; exact hBx)
  takeBoxListeners {w} hWf hid expected := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => takeBoxListenersPure s hid expected)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
    unfold takeBoxListenersPure
    cases hF : assocFind hid (toSysTable (proj w).table).boxes with
    | none => rw [fromSysTable_toSysTable]; exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some slot =>
      cases hBad : (slot.fwdsTaken || slot.listenerFds.size != expected) with
      | true => simp only [hBad, ↓reduceIte, fromSysTable_toSysTable]; exact ⟨hWf, trivial, trivial, trivial, trivial, trivial, trivial⟩
      | false =>
        have hKey : tableHasKey hid (proj w).table.boxes = true := by
          have h1 := assocFind_isSome_eq_tableHasKey hid (toSysTable (proj w).table).boxes
          rw [hF, toSysTable, tableHasKey_map_snd] at h1; exact h1.symm
        have hPres := list_map_key_cond_preserves hid (fun b : BoxSlotM Nat => { b with fwdsTaken := true, listenerFds := #[] }) (toSysTable (proj w).table).boxes
        simp only [hBad, Bool.false_eq_true, ↓reduceIte, fromSysTable, toSysTable, List.length_map,
          list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
          list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
        refine ⟨?_, trivial, trivial, trivial, trivial, trivial, hKey⟩
        rw [rawHostWorldWf_iff]; refine ⟨hN, hPl, ?_, hFw⟩
        dsimp only [toSysTable] at hPres
        rw [list_all_keys_map_snd, hPres.2 isValidSandboxHandleId, list_all_keys_map_snd]; exact hBx
  takeBoxIo {w} hWf hid := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => takeBoxIoPure s hid)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
    unfold takeBoxIoPure
    cases hF : assocFind hid (toSysTable (proj w).table).boxes with
    | none => rw [fromSysTable_toSysTable]; exact ⟨hWf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some slot =>
      cases hRs : slot.readStarted with
      | true => simp only [hRs, ↓reduceIte, fromSysTable_toSysTable]; exact ⟨hWf, trivial, trivial, trivial, trivial, trivial, trivial⟩
      | false =>
        have hKey : tableHasKey hid (proj w).table.boxes = true := by
          have h1 := assocFind_isSome_eq_tableHasKey hid (toSysTable (proj w).table).boxes
          rw [hF, toSysTable, tableHasKey_map_snd] at h1; exact h1.symm
        have hPres := list_map_key_cond_preserves hid
          (fun b : BoxSlotM Nat => { b with readStarted := true, stdinFd? := none, stdoutFd? := none, stderrFd? := none, statusFd? := none, goFd? := none })
          (toSysTable (proj w).table).boxes
        simp only [hRs, Bool.false_eq_true, ↓reduceIte, fromSysTable, toSysTable, List.length_map,
          list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
          list_map_snd_comp toSysFwdSlot fromSysFwdSlot fromSysFwdSlot_toSysFwdSlot]
        refine ⟨?_, trivial, trivial, trivial, trivial, trivial, hKey⟩
        rw [rawHostWorldWf_iff]; refine ⟨hN, hPl, ?_, hFw⟩
        dsimp only [toSysTable] at hPres
        rw [list_all_keys_map_snd, hPres.2 isValidSandboxHandleId, list_all_keys_map_snd]; exact hBx
  insertFwd {w} hWf slot := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => insertFwdPure s slot)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    unfold insertFwdPure allocHandleIdPure; dsimp only [toSysTable]
    cases hId : isValidSandboxHandleId (proj w).table.nextId with
    | true =>
      have ⟨_, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
      simp only [↓reduceIte, fromSysTable, List.map_cons, List.length_cons, List.length_map,
        list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
        list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot]
      refine ⟨?_, trivial, trivial, trivial, trivial, hId, trivial⟩
      rw [rawHostWorldWf_iff]; refine ⟨by dsimp only; omega, hPl, hBx, ?_⟩
      simp only [List.all_cons, Bool.and_eq_true, hId, true_and]
      rw [list_all_keys_map_snd, list_all_keys_map_snd]; exact hFw
    | false =>
      have hRt : fromSysTable (toSysTable (proj w).table) = (proj w).table := fromSysTable_toSysTable _
      dsimp only [toSysTable] at hRt; simp only [Bool.false_eq_true, ↓reduceIte, hRt]
      exact ⟨hWf, trivial, trivial, trivial, trivial, trivial⟩
  detachFwd {w} hWf hid := by
    have ⟨hVal, hProj⟩ := tbl_modify_run hCap hWf (fun s => detachFwdPure s hid)
    dsimp only [toHostTableOps]; rw [hProj, hVal]
    have ⟨hN, hPl, hBx, hFw⟩ := (rawHostWorldWf_iff (proj w)).mp hWf
    unfold detachFwdPure
    cases hRem : (assocRemove hid (toSysTable (proj w).table).forwarders).1 with
    | none =>
      have ⟨hEq, hKey⟩ := assocRemove_none hid (toSysTable (proj w).table).forwarders hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      have hEq' : fromSysTable { toSysTable (proj w).table with forwarders := (assocRemove hid (toSysTable (proj w).table).forwarders).2 } = (proj w).table := by
        rw [hEq]; exact fromSysTable_toSysTable _
      rw [hEq']; exact ⟨hWf, rfl, rfl, rfl, rfl, hKey, rfl⟩
    | some slot =>
      have ⟨hKey, hLen, hAll⟩ := assocRemove_some hid (toSysTable (proj w).table).forwarders slot hRem
      rw [toSysTable, tableHasKey_map_snd] at hKey
      dsimp only [fromSysTable, toSysTable]
      rw [list_map_snd_comp toSysPlanSlot fromSysPlanSlot fromSysPlanSlot_toSysPlanSlot,
        list_map_snd_comp toSysBoxSlot fromSysBoxSlot fromSysBoxSlot_toSysBoxSlot]
      refine ⟨?_, rfl, rfl, rfl, rfl, hKey, by simpa [toSysTable] using hLen⟩
      rw [rawHostWorldWf_iff]; refine ⟨hN, hPl, hBx, ?_⟩
      rw [list_all_keys_map_snd]; exact hAll _ (by rw [toSysTable, list_all_keys_map_snd]; exact hFw)

/-- `Internal.mapRawError (.invalidArgument p e msg)` always produces `.invalidInput` with non-empty message. -/
theorem mapRawError_invalidArg_spec (p : Option String) (e : Option Errno) (msg : String) :
    (Internal.mapRawError (.invalidArgument p e msg)).kind = .invalidInput ∧
    (Internal.mapRawError (.invalidArgument p e msg)).message ≠ "" := by
  refine ⟨rfl, ?_⟩
  simp only [Internal.mapRawError, Model.Internal.mapRawError]
  cases h : msg.isEmpty with
  | true => simp only [↓reduceIte]; decide
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact String.isEmpty_eq_false_iff.mp h

end LeanSwe.ProcessSandbox.Raw.Proofs

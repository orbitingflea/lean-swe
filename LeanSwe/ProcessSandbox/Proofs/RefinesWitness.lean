import Core.Obeys
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Model.Refines
import LeanSwe.ProcessSandbox.Proofs.RefinesHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Raw.Model

private def eraseFirstByKey {α : Type} (hid : Nat) : List (Nat × α) → List (Nat × α)
  | [] => []
  | p :: rest => if p.1 == hid then rest else p :: eraseFirstByKey hid rest

private theorem eraseFirstByKey_length {α : Type} (hid : Nat) (xs : List (Nat × α))
    (h : tableHasKey hid xs = true) : (eraseFirstByKey hid xs).length + 1 = xs.length := by
  induction xs with
  | nil => simp [tableHasKey] at h
  | cons p rest ih =>
    unfold eraseFirstByKey
    cases hp : (p.1 == hid)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hRest : tableHasKey hid rest = true := by
        simpa [tableHasKey, List.any_cons, hp] using h
      have := ih hRest
      omega
    · simp

private theorem eraseFirstByKey_all {α : Type} (hid : Nat) (P : Nat × α → Bool)
    (xs : List (Nat × α)) (h : xs.all P = true) : (eraseFirstByKey hid xs).all P = true := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    unfold eraseFirstByKey
    cases hp : (p.1 == hid)
    · simp [h.1, ih h.2]
    · simp [h.2]

private def witnessRawOps : RawProcessSandboxOpsM (StateM RawHostWorld) where
  mapRawError := Raw.Model.Internal.mapRawError
  decodeHostAuditArch := decodeHostAuditArch
  encodePlan _ _ := .error { kind := .invalidInput, message := "mock encodePlan" }
  hostSeccompArch := fun s => (decodeHostAuditArch (detectHostAuditArch s.isLinux s.target), s)
  preflight _ := fun s =>
    if s.isLinux then (.ok (), s)
    else (.error { kind := .unavailable, message := "non-linux" }, s)
  discoverHostPreset := fun s =>
    if s.isLinux then (.ok {}, s)
    else (.error { kind := .unavailable, message := "non-linux" }, s)
  sealPlan _ _ := fun s => (.error { kind := .ioError, message := "mock sealPlan" }, s)
  closePlan ph := fun s =>
    if isValidSandboxHandleId ph.handleId && tableHasKey ph.handleId s.table.plans then
      (.ok (), { s with table := { s.table with plans := eraseFirstByKey ph.handleId s.table.plans } })
    else
      (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
  spawnBox ph := fun s =>
    if isValidSandboxHandleId ph.handleId && tableHasKey ph.handleId s.table.plans then
      (.error { kind := .unavailable, message := "mock spawnBox" }, s)
    else
      (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
  startPortForwarders bh _ := fun s =>
    if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
      (.error { kind := .ioError, message := "mock startPortForwarders" }, s)
    else
      (.error { kind := .invalidInput, message := "invalid box handle" }, s)
  stopPortForwarders fh := fun s =>
    if isValidSandboxHandleId fh.handleId && tableHasKey fh.handleId s.table.fwds then
      (.ok (), { s with table := { s.table with fwds := eraseFirstByKey fh.handleId s.table.fwds } })
    else
      (.error { kind := .invalidInput, message := "invalid forwarder handle" }, s)
  readBoxOutput bh _ _ _ := fun s =>
    if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
      (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)
    else
      (.error { kind := .invalidInput, message := "invalid box handle" }, s)
  killProcessGroup bh := fun s =>
    if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
      (.ok (), s)
    else
      (.error { kind := .invalidInput, message := "invalid box handle" }, s)
  pidfdKill bh := fun s =>
    if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
      (.ok (), s)
    else
      (.error { kind := .invalidInput, message := "invalid box handle" }, s)
  reapBox bh := fun s =>
    if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
      (.ok (), { s with table := { s.table with boxes := eraseFirstByKey bh.handleId s.table.boxes } })
    else
      (.error { kind := .invalidInput, message := "invalid box handle" }, s)
  activeResourceCounts := fun s => (tableCounts s.table, s)

/-- Non-vacuity proof that `witnessRawOps` satisfies `Model.allowedRawStep`. -/
theorem witnessRawOps_obeys_allowedRawStep :
    Core.ObeysStep id Model.rawStepWf (Model.execRawStep witnessRawOps) Model.allowedRawStep := by
  intro s req hw
  have hw0 : rawHostWorldWf s = true := hw
  have hwParts :
      decide (0 < s.table.nextId) = true ∧
      s.table.plans.all (fun p => isValidSandboxHandleId p.1) = true ∧
      s.table.boxes.all (fun b => isValidSandboxHandleId b.1) = true ∧
      s.table.fwds.all (fun f => isValidSandboxHandleId f.1) = true := by
    simp only [rawHostWorldWf, Bool.and_eq_true, and_assoc] at hw0
    exact hw0
  cases req with
  | hostSeccompArch =>
    exact ⟨hw0, rfl, rfl, rfl, rfl⟩
  | preflight _ =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hL : s.isLinux <;> simp [hw0, hL]
  | discoverHostPreset =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hL : s.isLinux <;> simp [hw0, hL]
  | sealPlan _ _ =>
    exact ⟨hw0, rfl, rfl, rfl, rfl, by decide, rfl⟩
  | closePlan ph =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId ph.handleId
    · simp [hw0]
    · cases hK : tableHasKey ph.handleId s.table.plans
      · simp [hw0]
      · simp [rawHostWorldWf, hwParts.1, hwParts.2.2.1, hwParts.2.2.2,
          eraseFirstByKey_all ph.handleId _ s.table.plans hwParts.2.1,
          eraseFirstByKey_length ph.handleId s.table.plans hK]
  | spawnBox ph =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId ph.handleId
    · simp [hw0]
    · cases hK : tableHasKey ph.handleId s.table.plans <;> simp [hw0]
  | startPortForwarders bh _ =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId bh.handleId
    · simp [hw0]
    · cases hK : tableHasKey bh.handleId s.table.boxes <;> simp [hw0]
  | stopPortForwarders fh =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId fh.handleId
    · simp [hw0]
    · cases hK : tableHasKey fh.handleId s.table.fwds
      · simp [hw0]
      · simp [rawHostWorldWf, hwParts.1, hwParts.2.1, hwParts.2.2.1,
          eraseFirstByKey_all fh.handleId _ s.table.fwds hwParts.2.2.2,
          eraseFirstByKey_length fh.handleId s.table.fwds hK]
  | readBoxOutput bh _ _ _ =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId bh.handleId
    · simp [hw0]
    · cases hK : tableHasKey bh.handleId s.table.boxes
      · simp [hw0]
      · simp [hw0, outcomeNonNeg]
  | killProcessGroup bh =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId bh.handleId
    · simp [hw0]
    · cases hK : tableHasKey bh.handleId s.table.boxes <;> simp [hw0]
  | pidfdKill bh =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId bh.handleId
    · simp [hw0]
    · cases hK : tableHasKey bh.handleId s.table.boxes <;> simp [hw0]
  | reapBox bh =>
    dsimp only [Model.execRawStep, execRawOpsStep, witnessRawOps, Model.allowedRawStep,
      allowedRawOpsStep, stateM_map_run, StateT.run, id]
    cases hV : isValidSandboxHandleId bh.handleId
    · simp [hw0]
    · cases hK : tableHasKey bh.handleId s.table.boxes
      · simp [hw0]
      · simp [rawHostWorldWf, hwParts.1, hwParts.2.1, hwParts.2.2.2,
          eraseFirstByKey_all bh.handleId _ s.table.boxes hwParts.2.2.1,
          eraseFirstByKey_length bh.handleId s.table.boxes hK]
  | activeResourceCounts =>
    exact ⟨hw0, rfl, rfl, rfl, rfl⟩

end LeanSwe.ProcessSandbox.Proofs

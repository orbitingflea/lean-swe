import LeanSwe.Process.Raw.Types
import LeanSwe.Process.Raw.Interface
import LeanSwe.Process.Raw.Impl
import LeanSwe.Process.Raw.SpecTests

namespace LeanSwe.Process.Raw.Proofs

open Core
open Core.NondetTest

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- Proof of `test_processRaw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_processRaw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_processRaw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | executableNotFound prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "executable not found: " prog (by decide))
  | permissionDenied _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | timedOut prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | outputLimitExceeded prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | signaled prog _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_processRaw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_processRaw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_processRaw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_processRaw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_processRaw_mapRawError_preservesKindAndFields` for `defaultOps`. -/
theorem proof_processRaw_mapRawError_preservesKindAndFields :
    AllPass (test_processRaw_mapRawError_preservesKindAndFields defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_processRaw_mapRawError_preservesKindAndFields`. -/
theorem reach_processRaw_mapRawError_preservesKindAndFields :
    CanReach (test_processRaw_mapRawError_preservesKindAndFields defaultOps) :=
  ⟨.userError "err", by simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]⟩

/-- Pure state model for verifying `RawProcessOpsM` process-group lifecycle contracts. -/
structure RawProcState where
  /-- Active handle entries `(handleId, groupStillAlive)`. -/
  active : List (Nat × Bool) := []
  deriving DecidableEq, Repr

private def freshHandleId (active : List (Nat × Bool)) : Nat :=
  (active.foldl (fun m p => max m p.1) 0) + 1

private theorem freshHandleId_pos (active : List (Nat × Bool)) : 0 < freshHandleId active := by
  unfold freshHandleId
  omega

private theorem freshHandleId_gt_all (active : List (Nat × Bool)) :
    ∀ p ∈ active, p.1 < freshHandleId active := by
  have hle : ∀ (xs : List (Nat × Bool)) (init : Nat),
      init ≤ xs.foldl (fun m p => max m p.1) init ∧
      ∀ p ∈ xs, p.1 ≤ xs.foldl (fun m p => max m p.1) init := by
    intro xs
    induction xs with
    | nil =>
      intro init
      exact ⟨Nat.le_refl _, fun _ h => by contradiction⟩
    | cons x rest ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init x.1)
      constructor
      · exact Nat.le_trans (Nat.le_max_left _ _) h1
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Nat.le_trans (Nat.le_max_right _ _) h1
        · exact h2 p hp'
  intro p hp
  have := (hle active 0).2 p hp
  unfold freshHandleId
  omega

private theorem freshHandleId_not_mem (active : List (Nat × Bool)) :
    ∀ b, (freshHandleId active, b) ∉ active := by
  intro b hmem
  have hlt := freshHandleId_gt_all active (freshHandleId active, b) hmem
  omega

private theorem find?_fresh_cons (k : Nat) (b : Bool) (xs : List (Nat × Bool)) :
    ((k, b) :: xs).find? (fun p => p.1 == k) = some (k, b) := by
  simp [List.find?]

private theorem map_kill_fresh (k : Nat) (xs : List (Nat × Bool))
    (hfresh : ∀ p ∈ xs, p.1 < k) :
    ((k, true) :: xs).map (fun p => if p.1 == k then (p.1, false) else p) =
      (k, false) :: xs := by
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte]
  congr 1
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons]
    have hlt : x.1 < k := hfresh x (by simp)
    have hne : (x.1 == k) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact ih (fun p hp => hfresh p (by simp [hp]))

private theorem filter_ne_fresh (k : Nat) (xs : List (Nat × Bool))
    (hfresh : ∀ p ∈ xs, p.1 < k) :
    ((k, false) :: xs).filter (fun p => p.1 != k) = xs := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hlt : x.1 < k := hfresh x (by simp)
    have hbne : (x.1 != k) = true := bne_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp only [List.filter_cons, hbne, ↓reduceIte]
    congr 1
    exact ih (fun p hp => hfresh p (by simp [hp]))

/-- Pure `StateM RawProcState` implementation of `RawProcessOpsM` used in `Raw.Proofs`. -/
def mockRawOps : RawProcessOpsM (StateM RawProcState) :=
  { mapRawError := Internal.mapRawError
    spawn := fun req => fun s =>
      if req.program.isEmpty then
        (.error (Internal.mapRawError (.invalidArgument (some req.program) 22 "empty program")), s)
      else
        let hid := freshHandleId s.active
        (.ok { handleId := hid, pid := Int.ofNat hid, pgid := Int.ofNat hid },
         { active := (hid, true) :: s.active })
    awaitOutput := fun _ _ _ _ =>
      pure (.ok (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }))
    killProcessGroup := fun h => fun s =>
      (.ok (), { active := s.active.map (fun p => if p.1 == h.handleId then (p.1, false) else p) })
    reap := fun h => fun s =>
      match s.active.find? (fun p => p.1 == h.handleId) with
      | none => (.ok (), s)
      | some (_, true) =>
        (.error (Internal.mapRawError (.userError "cannot reap active process group")), s)
      | some (_, false) =>
        (.ok (), { active := s.active.filter (fun p => p.1 != h.handleId) })
    activeProcessCount := fun s => (s.active.length, s) }

/-- Proof of `test_processRaw_spawn_emptyProgram_failsInvalidInput` for `mockRawOps`. -/
theorem proof_processRaw_spawn_emptyProgram_failsInvalidInput :
    AllPass (test_processRaw_spawn_emptyProgram_failsInvalidInput mockRawOps) := by
  intro s₀ req hEmpty
  have hisEmpty : req.program.isEmpty = true := by rw [hEmpty]; rfl
  simp only [mockRawOps, hisEmpty, ↓reduceIte, Internal.mapRawError, StateT.run, assert]
  refine ⟨⟨⟨_, rfl, rfl, ?_⟩, trivial⟩, trivial⟩
  dsimp
  exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_processRaw_spawn_emptyProgram_failsInvalidInput`. -/
theorem reach_processRaw_spawn_emptyProgram_failsInvalidInput :
    CanReach (test_processRaw_spawn_emptyProgram_failsInvalidInput mockRawOps) := by
  refine ⟨{}, { program := "" }, rfl, ?_⟩
  have h := proof_processRaw_spawn_emptyProgram_failsInvalidInput {} { program := "" } rfl
  simpa [test_processRaw_spawn_emptyProgram_failsInvalidInput, mockRawOps, StateT.run,
    assume, assert, Bind.bind] using h

/-- Proof of `test_processRaw_killAndReap_restoresActiveCount` for `mockRawOps`. -/
theorem proof_processRaw_killAndReap_restoresActiveCount :
    AllPass (test_processRaw_killAndReap_restoresActiveCount mockRawOps) := by
  intro s₀ req
  dsimp only [mockRawOps, StateT.run]
  by_cases hEmpty : req.program.isEmpty = true
  · simp [hEmpty, assume]
  · simp only [hEmpty, Bool.false_eq_true, ↓reduceIte]
    have hpos : 0 < freshHandleId s₀.active := freshHandleId_pos s₀.active
    have hgt : ∀ p ∈ s₀.active, p.1 < freshHandleId s₀.active := freshHandleId_gt_all s₀.active
    have hmap := map_kill_fresh (freshHandleId s₀.active) s₀.active hgt
    have hflt := filter_ne_fresh (freshHandleId s₀.active) s₀.active hgt
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact Int.natCast_pos.mpr hpos
    · exact Int.natCast_pos.mpr hpos
    · simp
    · simp only [hmap, List.find?_cons_of_pos, beq_self_eq_true, hflt, assert]
      trivial

/-- Non-vacuity `CanReach` witness for `test_processRaw_killAndReap_restoresActiveCount`. -/
theorem reach_processRaw_killAndReap_restoresActiveCount :
    CanReach (test_processRaw_killAndReap_restoresActiveCount mockRawOps) := by
  refine ⟨{}, { program := "echo" }, ?_⟩
  have h := proof_processRaw_killAndReap_restoresActiveCount {} { program := "echo" }
  simpa [test_processRaw_killAndReap_restoresActiveCount, mockRawOps, StateT.run,
    assume, assert, Bind.bind] using h

end LeanSwe.Process.Raw.Proofs

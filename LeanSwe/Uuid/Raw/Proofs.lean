import LeanSwe.Uuid.Raw.Interface
import LeanSwe.Uuid.Raw.SpecTests

namespace LeanSwe.Uuid.Raw.Proofs

open Core
open Core.NondetTest

private theorem nonEmptyMsg_ne_empty {fallback msg : String} (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  by_cases h : msg.isEmpty
  · simp [h, hf]
  · simp [h]
    intro heq
    subst heq
    exact h rfl

/-- Proof of `test_uuidraw_mapRawError_normalizesError` for `defaultOps`. -/
theorem proof_uuidraw_mapRawError_normalizesError :
    AllPass (test_uuidraw_mapRawError_normalizesError defaultOps) := by
  intro raw
  cases raw with
  | osError code detail =>
    dsimp [test_uuidraw_mapRawError_normalizesError, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty ?_⟩, rfl, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp at hlen
    exact absurd hlen.1 (by decide)
  | shortRead gotBytes detail =>
    dsimp [test_uuidraw_mapRawError_normalizesError, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty ?_⟩, trivial, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp at hlen
  | userError detail =>
    dsimp [test_uuidraw_mapRawError_normalizesError, defaultOps, Internal.mkRawOps,
      Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty (by decide)⟩, trivial, trivial⟩

private def mockRawOps : RawUuidOpsM (StateM Nat) :=
  { mapRawError := Internal.mapRawError
    randomBytes16 := do
      let n ← get
      set (n + 1)
      return .ok (ByteArray.mk (Array.replicate 16 (UInt8.ofNat (n % 256)))) }

private theorem mockRawOps_run_eq (n : Nat) :
    (mockRawOps.randomBytes16.run n).1 =
      .ok (ByteArray.mk (Array.replicate 16 (UInt8.ofNat (n % 256)))) :=
  rfl

/-- Proof of `test_uuidraw_randomBytes16_returns16BytesOrError` on a mock `StateM Nat` entropy source. -/
theorem proof_uuidraw_randomBytes16_returns16BytesOrError :
    AllPass (test_uuidraw_randomBytes16_returns16BytesOrError mockRawOps) := by
  intro n
  dsimp [test_uuidraw_randomBytes16_returns16BytesOrError]
  rw [mockRawOps_run_eq]
  simp [Core.NondetTest.assert, ByteArray.size]

/-- Non-vacuity witness for `test_uuidraw_randomBytes16_returns16BytesOrError`. -/
theorem reach_uuidraw_randomBytes16_returns16BytesOrError :
    CanReach (test_uuidraw_randomBytes16_returns16BytesOrError mockRawOps) := by
  refine ⟨0, ?_⟩
  dsimp [test_uuidraw_randomBytes16_returns16BytesOrError]
  rw [mockRawOps_run_eq]
  simp [Core.NondetTest.assert, ByteArray.size]

end LeanSwe.Uuid.Raw.Proofs

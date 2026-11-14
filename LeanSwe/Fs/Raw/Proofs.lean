import LeanSwe.Fs.Raw.Types
import LeanSwe.Fs.Raw.Interface
import LeanSwe.Fs.Raw.Impl
import LeanSwe.Fs.Raw.SpecTests

namespace LeanSwe.Fs.Raw.Proofs

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

/-- Proof of `test_fsraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_fsraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_fsraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | noFileOrDirectory p _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "no such file or directory: " p (by decide))
  | alreadyExists _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | permissionDenied _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | inappropriateType _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | unsupportedOperation _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | wouldBlock _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_fsraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_fsraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_fsraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_fsraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_fsraw_mapRawError_wouldBlock` for `defaultOps`. -/
theorem proof_fsraw_mapRawError_wouldBlock :
    AllPass (test_fsraw_mapRawError_wouldBlock defaultOps) := by
  intro path? errno detail
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨⟨trivial, trivial, trivial, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_mapRawError_wouldBlock`. -/
theorem reach_fsraw_mapRawError_wouldBlock :
    CanReach (test_fsraw_mapRawError_wouldBlock defaultOps) :=
  ⟨some "/tmp/a.lock", 11, "", proof_fsraw_mapRawError_wouldBlock (some "/tmp/a.lock") 11 ""⟩

end LeanSwe.Fs.Raw.Proofs

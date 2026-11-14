import LeanSwe.Env.Raw.Types
import LeanSwe.Env.Raw.Interface
import LeanSwe.Env.Raw.Impl
import LeanSwe.Env.Raw.SpecTests

namespace LeanSwe.Env.Raw.Proofs

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

/-- Proof of `test_envraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_envraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_envraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | invalidEncoding _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_envraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_envraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_envraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_envraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_envraw_mapRawError_preservesKindAndMetadata` for `defaultOps`. -/
theorem proof_envraw_mapRawError_preservesKindAndMetadata :
    AllPass (test_envraw_mapRawError_preservesKindAndMetadata defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_envraw_mapRawError_preservesKindAndMetadata`. -/
theorem reach_envraw_mapRawError_preservesKindAndMetadata :
    CanReach (test_envraw_mapRawError_preservesKindAndMetadata defaultOps) :=
  ⟨.invalidEncoding (some "PATH") "bad",
    proof_envraw_mapRawError_preservesKindAndMetadata (.invalidEncoding (some "PATH") "bad")⟩

end LeanSwe.Env.Raw.Proofs

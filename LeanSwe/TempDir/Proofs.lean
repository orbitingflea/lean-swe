import Core.Refines
import LeanSwe.TempDir.Proofs.Shared
import LeanSwe.TempDir.Proofs.WithTempDirProofs
import LeanSwe.TempDir.Proofs.LockedProofs
import LeanSwe.TempDir.Proofs.CleanupBase
import LeanSwe.TempDir.Proofs.CleanupProofs
import LeanSwe.TempDir.Proofs.RefinesModel

/-!
Top-level umbrella verification module for `LeanSwe.TempDir`. Re-exports all specification
proofs (Specs 1–15) and exposes the compositional `refines_model` theorem tying
`Internal.mkApiFromCapsM` to the pure domain transitions in `LeanSwe.TempDir.Model`.
-/

namespace LeanSwe.TempDir.Proofs

open LeanSwe.TempDir.Model

/-- Full public `Interface` refinement of `LeanSwe.TempDir` (`mkApiM` and `defaultApi` both
delegate directly to `Internal.mkApiFromCapsM`) against `LeanSwe.TempDir.Model`. -/
theorem refines_model :
    Core.RefinesStepFromFinally id tempDirStepWf
      execRawStep allowedRawStep
      tempDirStepWf Internal.mkApiFromCapsM
      execPkgStep allowedPkgStep :=
  refinesStepFromFinally_mkApiFromCapsM

end LeanSwe.TempDir.Proofs

import Core.Obeys
import LeanSweProofs.TempDir.Proofs.Shared
import LeanSweProofs.TempDir.Proofs.WithTempDirProofs
import LeanSweProofs.TempDir.Proofs.LockedProofs
import LeanSweProofs.TempDir.Proofs.CleanupBase
import LeanSweProofs.TempDir.Proofs.CleanupProofs
import LeanSweProofs.TempDir.Proofs.RefinesModel

/-!
Top-level umbrella verification module for `LeanSwe.TempDir`. Re-exports all specification
proofs (Specs 1–15) and exposes the compositional `obeys_model` theorem tying
`Internal.mkApiFromCapsM` to the pure domain transitions in `LeanSwe.TempDir.Model`.
-/

namespace LeanSwe.TempDir.Proofs

open LeanSwe.TempDir.Model

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.TempDir` (`mkApiM` and `defaultApi`
both delegate directly to `Internal.mkApiFromCapsM`) against `LeanSwe.TempDir.Model`. -/
theorem obeys_model :
    Core.ObeysStepFromFinally id tempDirStepWf
      execRawStep allowedRawStep
      tempDirStepWf Internal.mkApiFromCapsM
      execPkgStep allowedPkgStep :=
  refinesStepFromFinally_mkApiFromCapsM

end LeanSwe.TempDir.Proofs

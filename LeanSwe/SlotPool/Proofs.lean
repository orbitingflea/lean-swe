import Core.Obeys
import LeanSwe.SlotPool.Proofs.SimLemmas
import LeanSwe.SlotPool.Proofs.CoreProofs
import LeanSwe.SlotPool.Proofs.LeaseAndPollProofs
import LeanSwe.SlotPool.Proofs.RefinesModel

/-!
Top-level umbrella verification module for `LeanSwe.SlotPool`. Re-exports all specification
proofs (Specs 1–11) and exposes the compositional `obeys_model` theorem tying
`LeanSwe.SlotPool.mkApiM` (`defaultApi` and `withSlot` delegate directly to `mkApiM`) to the
pure domain transitions in `LeanSwe.SlotPool.Model.Refines`.
-/

namespace LeanSwe.SlotPool.Proofs

open LeanSwe.SlotPool.Model

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.SlotPool` (`mkApiM`, `defaultApi`,
and `withSlot`) against `LeanSwe.SlotPool.Model`. -/
theorem obeys_model :
    Core.ObeysStepFrom2 id slotPoolStepWf
      execFsStep allowedFsStep
      execTimeStep allowedTimeStep
      slotPoolStepWf LeanSwe.SlotPool.mkApiM
      execPkgStep allowedPkgStep :=
  refinesStepFrom2_mkApiM

end LeanSwe.SlotPool.Proofs

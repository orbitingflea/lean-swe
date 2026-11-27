import Core.Obeys
import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSweProofs.Compress.Model.Refines
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers
import LeanSweProofs.Compress.Proofs.RequestProofs
import LeanSweProofs.Compress.Proofs.ImpossibleProofs
import LeanSweProofs.Compress.Proofs.StoredBoundsProofs
import LeanSweProofs.Compress.Proofs.ModelSoundnessProofs
import LeanSweProofs.Compress.Proofs.BridgeProofs
import LeanSweProofs.Compress.Proofs.ObeysProcess
import LeanSweProofs.Compress.Proofs.ObeysWorld
import LeanSweProofs.Compress.Proofs.ObeysWorldWitness

/-!
Top-level umbrella verification module for `LeanSwe.Compress`. Re-exports all specification
proofs (`AllPass`, `CanReach`, and `.provedImpossible`) and exposes the canonical composite
`obeys_model` theorem over `LeanSwe.Process.Model` and `LeanSwe.Compress.Model` alongside
`obeys_model_nonvacuous`.
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

/-- Full public `Interface` composite refinement (`Core.ObeysStepFrom`) of `LeanSwe.Compress`
(`Internal.mkApiM` and all 5 public operations `compress`, `decompress`, `compressWith`,
`decompressWith`, and `isToolAvailable`) over `LeanSwe.Process.Model` (`ProcessModelState`)
and `LeanSwe.Compress.Model` (`CompressWorld`). -/
theorem obeys_model :
    Core.ObeysStepFrom id Model.processStepWf Model.execProcessStep Model.allowedProcessStep
      Model.processStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgProcessStep ∧
    Core.ObeysStepFrom id Model.worldStepWf Model.execProcessStep Model.allowedWorldProcessStep
      Model.worldStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgWorldStep :=
  ⟨obeysStepFrom_process, obeysStepFrom_world⟩

/-- Non-vacuity witness showing both `ProcessApiM` step contracts in `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ proc : ProcessApiM (StateM LeanSwe.Process.Model.ProcessModelState),
      Core.ObeysStep id Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep) ∧
    (∃ proc : ProcessApiM (StateM Model.CompressWorld),
      Core.ObeysStep id Model.worldStepWf (Model.execProcessStep proc) Model.allowedWorldProcessStep) :=
  ⟨⟨modelProcessApi, modelProcessApi_obeys_allowedProcessStep⟩,
   ⟨worldProcessApi, worldProcessApi_obeys_allowedWorldProcessStep⟩⟩

end LeanSwe.Compress.Proofs

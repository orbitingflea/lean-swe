import Core.Obeys
import LeanSwe.Compress.Types
import LeanSwe.Compress.Model
import LeanSwe.Compress.Model.Refines
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSwe.Compress.SpecTests
import LeanSwe.Compress.Proofs.SharedHelpers
import LeanSwe.Compress.Proofs.RequestProofs
import LeanSwe.Compress.Proofs.ImpossibleProofs
import LeanSwe.Compress.Proofs.StoredBoundsProofs
import LeanSwe.Compress.Proofs.ModelSoundnessProofs
import LeanSwe.Compress.Proofs.BridgeProofs
import LeanSwe.Compress.Proofs.ObeysProcess
import LeanSwe.Compress.Proofs.ObeysWorld
import LeanSwe.Compress.Proofs.ObeysWorldWitness

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

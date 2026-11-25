import Core.Obeys
import LeanSwe.ProcessSandbox.Proofs.ModelProofs
import LeanSwe.ProcessSandbox.Proofs.ValidateProofs
import LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers
import LeanSwe.ProcessSandbox.Proofs.ApiBracketHelpers
import LeanSwe.ProcessSandbox.Proofs.ApiProofs
import LeanSwe.ProcessSandbox.Proofs.ApiSpawnOkProofs
import LeanSwe.ProcessSandbox.Proofs.ApiSealProofs
import LeanSwe.ProcessSandbox.Proofs.ApiOutcomeProofs
import LeanSwe.ProcessSandbox.Proofs.ApiCancelProofs
import LeanSwe.ProcessSandbox.Proofs.SeccompApiProofs
import LeanSwe.ProcessSandbox.Proofs.ErrorImpossibility
import LeanSwe.ProcessSandbox.Proofs.RefinesHelpers
import LeanSwe.ProcessSandbox.Proofs.RefinesWitness
import LeanSwe.ProcessSandbox.Proofs.RefinesModel

namespace LeanSwe.ProcessSandbox.Proofs

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.ProcessSandbox` covering `validateSpec`, `run`, and `isAvailable` over `Raw.Model.RawHostWorld`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.ProcessSandbox.validateSpec Model.validateSpecModel ∧
    Core.ObeysStepFromFinally id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨refinesPure_validateSpec, refinesStepFromFinally_mkApiM⟩

/-- Non-vacuity witness showing the `Model.allowedRawStep` premise of `obeys_model` is inhabited. -/
theorem obeys_model_nonvacuous :
    ∃ raw : RawProcessSandboxOpsM (StateM Raw.Model.RawHostWorld),
      Core.ObeysStep id Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep :=
  ⟨_, witnessRawOps_obeys_allowedRawStep⟩

end LeanSwe.ProcessSandbox.Proofs

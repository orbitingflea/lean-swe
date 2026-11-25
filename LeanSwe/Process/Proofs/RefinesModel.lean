import Core.Obeys
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.Interface
import LeanSwe.Process.Proofs.RefinesModelApi
import LeanSwe.Process.Proofs.RefinesModelWitness
import LeanSwe.Process.Proofs.RefinesModelHostWitness
import LeanSwe.Process.Proofs.RefinesModelHost
import LeanSwe.Process.Proofs.RefinesModelHostDefault

/-!
Top-level `Core.Obeys` assembly for `LeanSwe.Process`, pairing the pure
`Core.ObeysPureEq*` refinements, `Core.ObeysStepFrom` over `Internal.mkApiM`,
end-to-end `Core.ObeysStepFrom` over `Internal.mkApiFromHostCapsM` (`Impl + SysBridge`),
and non-vacuity capability witnesses (`process_refines_model`, `refines_model_nonvacuous`).
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

/-- Combined `Core.Obeys` theorem for `LeanSwe.Process` over `Model` and `Model.HealthyHost`. -/
theorem process_refines_model :
    Core.ObeysPureEq LeanSwe.Process.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.Process.validateRequest Model.validateRequestModel ∧
    @Core.ObeysPureEq2 String (Array String) ExecRequest
      (@LeanSwe.Process.mkCommandRequest) Model.mkCommandRequestModel ∧
    Core.ObeysPureEq2 LeanSwe.Process.withTextInput Model.withTextInputModel ∧
    Core.ObeysStepFrom id Model.processStateWf
      Model.execRawStep Model.allowedRawStep
      Model.processStateWf Internal.mkApiM
      Model.execPkgStep Model.allowedPkgStep ∧
    Core.ObeysStepFrom id Model.hostWorldWf
      Model.execHostCapStep Model.allowedHostCapStep
      Model.hostWorldWf Internal.mkApiFromHostCapsM
      Model.execPkgStep Model.allowedPkgHostStep :=
  ⟨refinesPure_mapRawError,
   refinesPure_validateRequest,
   refinesPure_mkCommandRequest,
   refinesPure_withTextInput,
   refinesStepFrom_mkApiM,
   refinesStepFrom_mkApiFromHostCapsM⟩

/-- Non-vacuity witness showing both raw process-model ops and simulated host capabilities inhabit `process_refines_model`. -/
theorem refines_model_nonvacuous :
    (∃ (ops : RawProcessOpsM (StateM Model.ProcessModelState)),
      Core.ObeysStep id Model.processStateWf (Model.execRawStep ops) Model.allowedRawStep) ∧
    (∃ (W : Type) (proj : W → Model.ProcessHostWorld) (cap : Model.HealthyHostCapsM (StateM W)),
      Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep) :=
  ⟨⟨_, modelRawOps_refines_allowedRawStep⟩, ⟨_, _, _, healthySimHostCaps_refines_allowedHostCapStep⟩⟩

end LeanSwe.Process.Proofs

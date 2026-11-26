import Core.Obeys
import Core.ConcOps
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.Model.FullStep
import LeanSwe.Process.Interface
import LeanSwe.Process.Proofs.RefinesModelApi
import LeanSwe.Process.Proofs.RefinesModelWitness
import LeanSwe.Process.Proofs.RefinesModelHostWitness
import LeanSwe.Process.Proofs.RefinesModelHost
import LeanSwe.Process.Proofs.FullObeys
import LeanSwe.Process.Proofs.FullObeysWitness

/-!
Top-level `Core.Obeys` assembly for `LeanSwe.Process`, pairing pure `Core.ObeysPureEq*`
refinements with `Core.ObeysStepFromConcCell` over `Internal.mkFullApiM` and the
schedule-parameterized non-vacuity witness (`process_obeys_model`, `process_obeys_model_nonvacuous`).
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

/-- Combined `Core.Obeys` theorem for `LeanSwe.Process` over `Internal.mkFullApiM`, `Model`, and `Model.FullStep`. -/
theorem process_obeys_model :
    Core.ObeysPureEq LeanSwe.Process.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.Process.validateRequest Model.validateRequestModel ∧
    @Core.ObeysPureEq2 String (Array String) ExecRequest
      (@LeanSwe.Process.mkCommandRequest) Model.mkCommandRequestModel ∧
    Core.ObeysPureEq2 LeanSwe.Process.withTextInput Model.withTextInputModel ∧
    Core.ObeysStepFromConcCell (CellS := Internal.ProcCellS)
      Model.mapFullWorldToState Model.procCellToState
      Model.fullRawWf Model.execFullRawStep Model.allowedFullRawStep
      Model.processStateWf Internal.mkFullApiM
      Model.execPkgStep Model.allowedPkgStep :=
  ⟨refinesPure_mapRawError,
   refinesPure_validateRequest,
   refinesPure_mkCommandRequest,
   refinesPure_withTextInput,
   obeysStepFromConcCell_mkFullApiM⟩

/-- Non-vacuity witness showing both raw process-model ops and simulated host capabilities inhabit legacy helper specs. -/
theorem refines_model_nonvacuous :
    (∃ (ops : RawProcessOpsM (StateM Model.ProcessModelState)),
      Core.ObeysStep id Model.processStateWf (Model.execRawStep ops) Model.allowedRawStep) ∧
    (∃ (W : Type) (proj : W → Model.ProcessHostWorld) (cap : Model.HealthyHostCapsM (StateM W)),
      Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep) :=
  ⟨⟨_, modelRawOps_refines_allowedRawStep⟩, ⟨_, _, _, healthySimHostCaps_refines_allowedHostCapStep⟩⟩

end LeanSwe.Process.Proofs

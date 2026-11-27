import Core.Obeys
import LeanSweProofs.Sqlite.Raw.Proofs.Helpers
import LeanSweProofs.Sqlite.Raw.Proofs.ErrorAndFlagsProofs
import LeanSweProofs.Sqlite.Raw.Proofs.WalProofs
import LeanSweProofs.Sqlite.Raw.Proofs.UriProofs
import LeanSweProofs.Sqlite.Raw.Proofs.StmtProofs
import LeanSweProofs.Sqlite.Raw.Proofs.ObeysPureEquiv
import LeanSweProofs.Sqlite.Raw.Proofs.ObeysModel

namespace LeanSwe.Sqlite.Raw.Proofs

open LeanSwe.Sqlite.Raw

/-- Canonical `Core.Obeys*` specification theorem for `LeanSwe.Sqlite.Raw`. -/
theorem obeys_model :
    Core.ObeysPureEq mapRawError Model.mapRawErrorModel ∧
    Core.ObeysStepFromFinally id Model.cStepWf
      Model.execCStep Model.allowedCStep Model.rawStepWf
      Internal.mkRawOps Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_obeys, mkRawOps_obeys⟩

/-- Concrete non-vacuity witness instantiating `obeys_model` over `Model.modelCSqliteOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPkgStep (Internal.mkRawOps Model.modelCSqliteOps)) Model.allowedPkgStep :=
  obeys_model.2 id Model.modelCSqliteOps modelCSqliteOps_obeys

end LeanSwe.Sqlite.Raw.Proofs

import Core.Obeys
import LeanSwe.Base64.Interface
import LeanSweProofs.Base64.Model
import LeanSweProofs.Base64.Model.Obeys
import LeanSweProofs.Base64.Proofs.CodecEquiv

namespace LeanSwe.Base64.Proofs

open LeanSwe.Base64
open LeanSwe.Base64.Model

/-- Full public `Interface` obedience of `LeanSwe.Base64` against `LeanSwe.Base64.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Base64.encode Model.encode ∧
    Core.ObeysPureEq LeanSwe.Base64.encodeUrl Model.encodeUrlModel ∧
    Core.ObeysPureEq2 LeanSwe.Base64.encodeWith Model.encodeWithModel ∧
    Core.ObeysPure LeanSwe.Base64.decode Model.allowedDecode ∧
    Core.ObeysPure LeanSwe.Base64.decodeUrl Model.allowedDecodeUrl ∧
    Core.ObeysPure2 LeanSwe.Base64.decodeWith Model.allowedDecodeWith :=
  ⟨fun bs => encodeWith_eq_encodeModel Model.defaultEncodeOptions bs,
   fun bs => encodeWith_eq_encodeModel Model.urlEncodeOptions bs,
   encodeWith_eq_encodeModel,
   fun s => decodeWith_matchesModel_aux Model.defaultDecodeOptions s,
   fun s => decodeWith_matchesModel_aux Model.urlDecodeOptions s,
   decodeWith_matchesModel_aux⟩

end LeanSwe.Base64.Proofs

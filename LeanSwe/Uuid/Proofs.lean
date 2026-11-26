import Core.Assumptions
import Core.Obeys
import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.Model
import LeanSwe.Uuid.Model.Refines
import LeanSwe.Uuid.Proofs.Codec
import LeanSwe.Uuid.Proofs.Entropy
import LeanSwe.Uuid.Proofs.RefinesModel

/-!
# Verified RFC 4122 UUIDv4 Specification Proofs

Top-level verification entry point exporting `obeys_model`, its non-vacuity
witness `obeys_model_nonvacuous`, and the exhaustive error-kind impossibility
theorems (`uuid_*_never_*`). Pure codec theory lives in `Proofs/Codec.lean`.
-/

namespace LeanSwe.Uuid.Proofs

open Core LeanSwe.Uuid LeanSwe.Uuid.Proofs.Codec LeanSwe.Uuid.Proofs.Entropy

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.entropyFailed`. -/
theorem uuid_fromRandomBytes_never_entropyFailed (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.fromRandomBytes bs) :=
  fromRandomBytes_never .entropyFailed (by decide) bs

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidFormat`. -/
theorem uuid_fromRandomBytes_never_invalidFormat (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidFormat (LeanSwe.Uuid.fromRandomBytes bs) :=
  fromRandomBytes_never .invalidFormat (by decide) bs

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidVersion`. -/
theorem uuid_fromRandomBytes_never_invalidVersion (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidVersion (LeanSwe.Uuid.fromRandomBytes bs) :=
  fromRandomBytes_never .invalidVersion (by decide) bs

/-- Proof that `LeanSwe.Uuid.parse` never returns `.entropyFailed`. -/
theorem uuid_parse_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parse s) :=
  parse_never .entropyFailed (by decide) (by decide) s

/-- Proof that `LeanSwe.Uuid.parse` never returns `.invalidLength`. -/
theorem uuid_parse_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parse s) :=
  parse_never .invalidLength (by decide) (by decide) s

/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.entropyFailed`. -/
theorem uuid_parseHex_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parseHex s) :=
  parseHexChars_never .entropyFailed (by decide) (by decide) s.toList

/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.invalidLength`. -/
theorem uuid_parseHex_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parseHex s) :=
  parseHexChars_never .invalidLength (by decide) (by decide) s.toList

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidLength`. -/
theorem uuid_getUuid_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.getUuid w :=
  getUuid_never .invalidLength (by decide) w

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidFormat`. -/
theorem uuid_getUuid_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.getUuid w :=
  getUuid_never .invalidFormat (by decide) w

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidVersion`. -/
theorem uuid_getUuid_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.getUuid w :=
  getUuid_never .invalidVersion (by decide) w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidLength`. -/
theorem uuid_v4_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidLength w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidFormat`. -/
theorem uuid_v4_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidFormat w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidVersion`. -/
theorem uuid_v4_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidVersion w

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.Uuid` against `LeanSwe.Uuid.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Uuid.mapRawError Model.mapRawError ∧
    Core.ObeysPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes ∧
    Core.ObeysPureEq LeanSwe.Uuid.toString Model.toString ∧
    Core.ObeysPureEq LeanSwe.Uuid.toHex Model.toHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.parse Model.parse ∧
    Core.ObeysPureEq LeanSwe.Uuid.parseHex Model.parseHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.isValid Model.isValid ∧
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep :=
  LeanSwe.Uuid.Proofs.RefinesModel.refines_model_impl

/-- Concrete non-vacuity witness instantiating `obeys_model` over `RefinesModel.refRawOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStep Model.toModelState Model.pkgWf
      (Model.execPkgStep (Internal.mkApi RefinesModel.refRawOps)) Model.allowedPkgStep :=
  obeys_model.2.2.2.2.2.2.2 id RefinesModel.refRawOps RefinesModel.refRawOps_obeys_model

end LeanSwe.Uuid.Proofs

import Core.Assumptions
import Core.Obeys
import LeanSwe.Tar.Interface
import LeanSweProofs.Tar.Model.WireSpec
import LeanSweProofs.Tar.Proofs.PackValid
import LeanSweProofs.Tar.Proofs.RefinesPack
import LeanSweProofs.Tar.Proofs.RefinesUnpack

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem packWith_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.packWith opts entries) := by
  unfold Core.NeverErrorKindPure LeanSwe.Tar.packWith
  cases h : Impl.packWith opts entries with
  | ok _ => trivial
  | error _ => exact fun hek => hk (hek ▸ packWith_err_kind opts entries h)

private theorem pack_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (entries : List TarEntry) : Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.pack entries) :=
  packWith_never_of_not_packKind k hk {} entries

/-- `Tar.pack` never returns `.checksumMismatch`. -/
theorem tar_pack_never_checksumMismatch (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .checksumMismatch (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .checksumMismatch (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.truncatedArchive`. -/
theorem tar_pack_never_truncatedArchive (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .truncatedArchive (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .truncatedArchive (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.unsupportedEntry`. -/
theorem tar_pack_never_unsupportedEntry (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .unsupportedEntry (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .unsupportedEntry (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.invalidEncoding`. -/
theorem tar_pack_never_invalidEncoding (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .invalidEncoding (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .invalidEncoding (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.resourceLimitExceeded`. -/
theorem tar_pack_never_resourceLimitExceeded (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .resourceLimitExceeded (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .resourceLimitExceeded (by unfold IsPackErrorKind; decide) entries

/-- `Tar.packWith` never returns `.checksumMismatch`. -/
theorem tar_packWith_never_checksumMismatch (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .checksumMismatch (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .checksumMismatch (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.truncatedArchive`. -/
theorem tar_packWith_never_truncatedArchive (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .truncatedArchive (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .truncatedArchive (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.unsupportedEntry`. -/
theorem tar_packWith_never_unsupportedEntry (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .unsupportedEntry (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .unsupportedEntry (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.invalidEncoding`. -/
theorem tar_packWith_never_invalidEncoding (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .invalidEncoding (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .invalidEncoding (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.resourceLimitExceeded`. -/
theorem tar_packWith_never_resourceLimitExceeded (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .resourceLimitExceeded (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .resourceLimitExceeded (by unfold IsPackErrorKind; decide) opts entries

/-- Full public `Interface` obedience of `LeanSwe.Tar` against `LeanSwe.Tar.Model`. -/
theorem obeys_model :
    Core.ObeysPure LeanSwe.Tar.pack Model.allowedPack ∧
    Core.ObeysPure2 LeanSwe.Tar.packWith Model.allowedPackWith ∧
    Core.ObeysPure LeanSwe.Tar.unpack Model.allowedUnpack ∧
    Core.ObeysPure2 LeanSwe.Tar.unpackWith Model.allowedUnpackWith :=
  ⟨pack_refines_model, packWith_refines_model, unpack_refines_model, unpackWith_refines_model⟩

end LeanSwe.Tar.Proofs

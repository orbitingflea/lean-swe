import Core.NondetTest
import LeanSwe.Tar.Types
import LeanSwe.Tar.Model
import LeanSwe.Tar.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Tar`. -/

namespace LeanSwe.Tar

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Tar.Model

private def stubTarApi : TarApi :=
  { pack := fun _ => .error { kind := .invalidHeader, message := "" }
  , packWith := fun _ _ => .error { kind := .invalidHeader, message := "" }
  , unpack := fun _ => .error { kind := .invalidHeader, message := "" }
  , unpackWith := fun _ _ => .error { kind := .invalidHeader, message := "" }
  }

example : ¬ Core.AllPass (test_tar_onError_returnsNonEmptyMessage stubTarApi) := by
  intro h
  have h0 := h [] {} ByteArray.empty {}
  simp [stubTarApi, bind, assert] at h0

private def mismatchedDefaultApi : TarApi :=
  { stubTarApi with
    pack := fun _ => .ok ByteArray.empty
    packWith := fun _ _ => .error { kind := .invalidHeader, message := "err" } }

example : ¬ Core.AllPass (test_tar_defaultWrappers_matchOptionsDefaults mismatchedDefaultApi) := by
  intro h
  have h0 := h [] ByteArray.empty
  simp [mismatchedDefaultApi, bind, assert] at h0

example : ¬ Core.AllPass (test_tar_packWith_iffValidArchive stubTarApi) := by
  intro h
  have h0 := h {} []
  simp [stubTarApi, ValidArchive, validArchiveBool, noDupNormalizedPathsBool, noDupNormalizedPathsBool.go, assert] at h0

private def permissiveUnpackApi : TarApi :=
  { stubTarApi with
    unpackWith := fun _ _ => .ok [{ path := "/bad", kind := .regular }] }

example : ¬ Core.AllPass (test_tar_unpackWith_returnsValidArchiveWithinLimits permissiveUnpackApi) := by
  intro h
  have h0 := h {} ByteArray.empty
  simp [permissiveUnpackApi, ValidArchive, validArchiveBool, validEntryBool,
    validateEntryPath, hasNulChars, bind, assert] at h0

example : ¬ Core.AllPass (test_tar_packUnpack_roundTrip stubTarApi) := by
  intro h
  have h0 := h [] {} {}
  have hv : ValidArchive false false [] := by
    simp [ValidArchive, validArchiveBool, noDupNormalizedPathsBool, noDupNormalizedPathsBool.go]
  have h1 := h0 hv rfl rfl (Nat.zero_le _) (Nat.zero_le _) rfl
  simp [stubTarApi, assert] at h1

example : ¬ Core.AllPass (test_tar_packWith_concreteUstarAndPaxCases_roundTrip stubTarApi) := by
  intro h
  simp only [Core.AllPass, test_tar_packWith_concreteUstarAndPaxCases_roundTrip, stubTarApi, bind, assert] at h
  exact h.1

private def permissivePathApi : TarApi :=
  { stubTarApi with
    packWith := fun _ _ => .ok ByteArray.empty }

example : ¬ Core.AllPass (test_tar_packWith_invalidAndUnsafePaths_rejected permissivePathApi) := by
  intro h
  simp only [Core.AllPass, test_tar_packWith_invalidAndUnsafePaths_rejected, checkPackError, permissivePathApi, bind, assert] at h
  exact h.1

example : ¬ Core.AllPass (test_tar_packWith_symlinkAndEntryInvariants_rejected permissivePathApi) := by
  intro h
  simp only [Core.AllPass, test_tar_packWith_symlinkAndEntryInvariants_rejected, checkPackError, permissivePathApi, bind, assert] at h
  exact h.1

private def emptyOkUnpackApi : TarApi :=
  { stubTarApi with
    unpackWith := fun _ _ => .ok [] }

example : ¬ Core.AllPass (test_tar_unpackWith_framingAndTrailer_validated emptyOkUnpackApi) := by
  intro h
  simp only [Core.AllPass, test_tar_unpackWith_framingAndTrailer_validated, checkUnpackError, emptyOkUnpackApi, bind, assert] at h
  exact h.1

example : ¬ Core.AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated emptyOkUnpackApi) := by
  intro h
  simp only [Core.AllPass, test_tar_unpackWith_checksumNumericAndUnsupported_validated, checkUnpackError, emptyOkUnpackApi, bind, assert] at h
  exact h.1

example : ¬ Core.AllPass (test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced emptyOkUnpackApi) := by
  intro h
  simp only [Core.AllPass, test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced, checkUnpackError, emptyOkUnpackApi, bind, assert] at h
  exact h.1

example : ¬ Core.AllPass (test_tar_unpackWith_securityOnWire_enforced emptyOkUnpackApi) := by
  intro h
  simp only [Core.AllPass, test_tar_unpackWith_securityOnWire_enforced, checkUnpackError, emptyOkUnpackApi, bind, assert] at h
  exact h.1

end LeanSwe.Tar

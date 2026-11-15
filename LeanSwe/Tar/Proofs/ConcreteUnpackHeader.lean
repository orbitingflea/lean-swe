import LeanSwe.Tar.Proofs.ConcreteUnpackHeaderPax

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem allPass_test5_match_iff
    (hdr : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith {} (hdr ++ twoZeroBlocks) = .ok res)
    (p : List TarEntry → Prop) (k : Unit → Core.AllPassRun Unit) :
    AllPass (have x := hdr; have jp := k;
      match defaultApi.unpack (x ++ twoZeroBlocks) with
      | .error _ => Bind.bind (assert False) (fun __r => jp __r)
      | .ok r => Bind.bind (assert (p r)) (fun __r => jp __r)) ↔
    p res ∧ AllPass (k ()) := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  exact allPass_assert_bind (p res) (fun __r => k __r)

private theorem allPass_test5_match_pax_iff
    (pax : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith {}
      (pax ++ mkUstarHeader "a.txt" 420 0 0 0 0 48 "" "" "" "" ++ twoZeroBlocks) = .ok res)
    (p : List TarEntry → Prop) (k : Unit → Core.AllPassRun Unit) :
    AllPass (have x := pax; have jp := k;
      match defaultApi.unpack
        (x ++ mkUstarHeader "a.txt" 420 0 0 0 0 48 "" "" "" "" ++ twoZeroBlocks) with
      | .error _ => Bind.bind (assert False) (fun __r => jp __r)
      | .ok r => Bind.bind (assert (p r)) (fun __r => jp __r)) ↔
    p res ∧ AllPass (k ()) := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  exact allPass_assert_bind (p res) (fun __r => k __r)

private theorem allPass_test5_match_tail_iff
    (hdr : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith {} (hdr ++ twoZeroBlocks) = .ok res)
    (p : List TarEntry → Prop) :
    AllPass (have x := hdr;
      match defaultApi.unpack (x ++ twoZeroBlocks) with
      | .error _ => assert False
      | .ok r => assert (p r)) ↔
    p res := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  simp only [AllPass, assert, and_true]

/-- Prove `test_tar_unpackWith_checksumNumericAndUnsupported_validated` for `defaultApi`. -/
theorem allPass_unpackWith_checksumNumericAndUnsupported_validated :
    AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated defaultApi) := by
  have ⟨resPosUid, hposUid_ok, hposUid_teq⟩ := test5_posBase256Uid_ok
  have ⟨resNulUid, hnulUid_ok, hnulUid_teq⟩ := test5_nulUid_ok
  have ⟨resValidPax, hvalidPax_ok, hvalidPax_teq⟩ := test5_validPax_ok
  have ⟨resGarbage, hgarbage_ok, hgarbage_teq⟩ := test5_garbageLink_ok
  dsimp only [baseHdr5] at hposUid_ok hnulUid_ok hvalidPax_ok hgarbage_ok
  unfold test_tar_unpackWith_checksumNumericAndUnsupported_validated
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badChkVal_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badChkSyntax_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_allNulChk_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badMagic_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_negBase256_err ?_
  refine (allPass_test5_match_iff _ resPosUid hposUid_ok _ _).mpr ⟨hposUid_teq, ?_⟩
  refine allPass_checkUnpackError_bind {} _ _ _ test5_nulSize_err ?_
  refine (allPass_test5_match_iff _ resNulUid hnulUid_ok _ _).mpr ⟨hnulUid_teq, ?_⟩
  refine allPass_checkUnpackError_bind {} _ _ _ test5_hardlink_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_globalPax_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badDir_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_sparsePax_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_nulUnamePax_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_dupPathPax_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badLenPax_err ?_
  refine (allPass_test5_match_pax_iff _ resValidPax hvalidPax_ok _ _).mpr ⟨hvalidPax_teq, ?_⟩
  refine allPass_checkUnpackError_bind {} _ _ _ test5_badUtf8Name_err ?_
  exact (allPass_test5_match_tail_iff _ resGarbage hgarbage_ok _).mpr hgarbage_teq

end LeanSwe.Tar.Proofs

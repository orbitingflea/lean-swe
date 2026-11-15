import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.Universal

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem defaultApi_packWith_eq (opts : PackOptions) (entries : List TarEntry) :
    defaultApi.packWith opts entries = Impl.packWith opts entries := rfl

private theorem allPass_checkPackError_iff (api : TarApi) (opts : PackOptions)
    (es : List TarEntry) (expectedKind : TarErrorKind) :
    AllPass (checkPackError api opts es expectedKind) ↔
    (match api.packWith opts es with
      | .ok _ => False
      | .error err => err.kind = expectedKind ∧ (!err.message.isEmpty) = true) := by
  unfold checkPackError
  cases api.packWith opts es with
  | ok _ => simp [AllPass, NondetTest.assert]
  | error err => simp [AllPass, NondetTest.assert]

private theorem tarErrorKind_eq_of_beq {a b : TarErrorKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem checkPackError_of_eval {opts : PackOptions} {es : List TarEntry}
    {expectedKind : TarErrorKind}
    (h : (match Impl.packWith opts es with
      | .error err => err.kind == expectedKind && !err.message.isEmpty
      | .ok _ => false) = true) :
    AllPass (checkPackError defaultApi opts es expectedKind) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  cases hp : Impl.packWith opts es with
  | ok _ => simp [hp] at h
  | error err =>
    simp only [hp, Bool.and_eq_true] at h
    exact ⟨tarErrorKind_eq_of_beq h.1, h.2⟩

private theorem checkPackError_of_pack_err {opts : PackOptions} {es : List TarEntry}
    {expectedKind : TarErrorKind} {err : TarError}
    (hp : Impl.packWith opts es = .error err)
    (hk : err.kind = expectedKind)
    (hm : (!err.message.isEmpty) = true) :
    AllPass (checkPackError defaultApi opts es expectedKind) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq, hp]
  exact ⟨hk, hm⟩

private theorem allPass_seq_checkPackError (opts : PackOptions) (es : List TarEntry)
    (expectedKind : TarErrorKind) (next : AllPassRun Unit)
    (ha : AllPass (checkPackError defaultApi opts es expectedKind))
    (hb : AllPass next) :
    AllPass (Bind.bind (checkPackError defaultApi opts es expectedKind) (fun _ => next)) := by
  have hiff : ∀ api opts es ek next,
      AllPass (Bind.bind (checkPackError api opts es ek) (fun _ => next)) ↔
      AllPass (checkPackError api opts es ek) ∧ AllPass next := by
    intro api opts es ek next
    unfold checkPackError
    generalize api.packWith opts es = p
    cases p with
    | ok _ => simp [AllPass, Bind.bind, NondetTest.assert]
    | error err => simp [AllPass, Bind.bind, NondetTest.assert, and_assoc]
  exact (hiff _ _ _ _ _).mpr ⟨ha, hb⟩

private theorem allPass_seq_checkRoundTripCase (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (entries : List TarEntry) (next : AllPassRun Unit)
    (ha : AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries))
    (hb : AllPass next) :
    AllPass (Bind.bind (checkRoundTripCase defaultApi packOpts unpackOpts entries) (fun _ => next)) := by
  have hiff : ∀ api po uo es next,
      AllPass (Bind.bind (checkRoundTripCase api po uo es) (fun _ => next)) ↔
      AllPass (checkRoundTripCase api po uo es) ∧ AllPass next := by
    intro api po uo es next
    unfold checkRoundTripCase
    cases api.packWith po es with
    | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
    | ok bytes =>
      dsimp only
      cases api.unpackWith uo bytes with
      | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
      | ok decoded => simp [AllPass, Bind.bind, NondetTest.assert]
  exact (hiff _ _ _ _ _).mpr ⟨ha, hb⟩

private theorem checkPackError_test2_dup :
    AllPass (checkPackError defaultApi {}
      [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }]
      .duplicatePath) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  have hp : Impl.packWith {}
      [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }] =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub", entryPath := some "sub" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv1 : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
    have hm1 : (({ path := "sub/", kind := .directory } : TarEntry).kind != .regular &&
        ({ path := "sub/", kind := .directory } : TarEntry).data.size != 0) = false := rfl
    have hl1 : (({ path := "sub/", kind := .directory } : TarEntry).kind != .symlink &&
        ({ path := "sub/", kind := .directory } : TarEntry).linkTarget != "") = false := rfl
    have hn1 : (hasNulString "" || hasNulString "") = false := by decide
    have hu1 : ((0 : Nat) ≥ u64Limit || (0 : Nat) ≥ u64Limit || (0 : Nat) ≥ u64Limit ||
        (ByteArray.empty).size ≥ u64Limit) = false := by decide
    have hs1 : ([].contains "sub") = false := rfl
    simp only [hv1, hm1, hl1, hn1, hu1, hs1, Bool.false_eq_true, ↓reduceIte]
    rw [Impl.packWith.go.eq_2]
    have hv2 : validateEntryPath false false .regular "sub" = .ok "sub" := rfl
    have hm2 : (({ path := "sub", kind := .regular } : TarEntry).kind != .regular &&
        ({ path := "sub", kind := .regular } : TarEntry).data.size != 0) = false := rfl
    have hl2 : (({ path := "sub", kind := .regular } : TarEntry).kind != .symlink &&
        ({ path := "sub", kind := .regular } : TarEntry).linkTarget != "") = false := rfl
    have hs2 : (["sub"].contains "sub") = true := rfl
    simp only [hv2, hm2, hl2, hn1, hu1, hs2, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hp]
  exact ⟨rfl, rfl⟩

private theorem checkPackError_test3_dir_data :
    AllPass (checkPackError defaultApi {} [{ path := "d", kind := .directory, data := "x".toUTF8 }]
      .invalidHeader) := by
  have hx : ("x".toUTF8).size = 1 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hp : Impl.packWith {} [{ path := "d", kind := .directory, data := "x".toUTF8 }] =
      .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "d" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv : validateEntryPath false false .directory "d" = .ok "d" := rfl
    have hc : (EntryKind.directory != EntryKind.regular && 1 != 0) = true := rfl
    simp only [hv, hx, hc, ↓reduceIte]
  exact checkPackError_of_pack_err hp rfl rfl

private theorem checkPackError_test3_sym_data :
    AllPass (checkPackError defaultApi {}
      [{ path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" }]
      .invalidHeader) := by
  have hx : ("x".toUTF8).size = 1 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hp : Impl.packWith {}
      [{ path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" }] =
      .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "s" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv : validateEntryPath false false .symlink "s" = .ok "s" := rfl
    have hs : validateSymlinkTarget false false "s" "t" = .ok () := rfl
    have hc : (EntryKind.symlink != EntryKind.regular && 1 != 0) = true := rfl
    simp only [hv, hs, hx, hc, ↓reduceIte]
  exact checkPackError_of_pack_err hp rfl rfl

/-- Prove `test_tar_packWith_invalidAndUnsafePaths_rejected` for `defaultApi`. -/
theorem allPass_packWith_invalidAndUnsafePaths_rejected :
    AllPass (test_tar_packWith_invalidAndUnsafePaths_rejected defaultApi) := by
  have hv_rt : ValidArchive true true
      [{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }] := by
    unfold ValidArchive; decide
  have hfit_rt : ([{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }].all
      fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
    decide
  have hrt := checkRoundTripCase_of_valid
    (packOpts := { allowAbsolute := true, allowParentTraversal := true })
    (unpackOpts := { allowAbsolute := true, allowParentTraversal := true })
    hv_rt rfl rfl (by decide) (by decide) hfit_rt
  unfold test_tar_packWith_invalidAndUnsafePaths_rejected
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test2_dup ?_
  exact checkPackError_of_eval (by decide)

/-- Prove `test_tar_packWith_symlinkAndEntryInvariants_rejected` for `defaultApi`. -/
theorem allPass_packWith_symlinkAndEntryInvariants_rejected :
    AllPass (test_tar_packWith_symlinkAndEntryInvariants_rejected defaultApi) := by
  have hv_rt : ValidArchive false false
      [{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
       { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }] := by
    unfold ValidArchive; decide
  have hfit_rt : ([{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
      { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }].all fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
    decide
  have hrt := checkRoundTripCase_of_valid (packOpts := {}) (unpackOpts := {})
    hv_rt rfl rfl (by decide) (by decide) hfit_rt
  unfold test_tar_packWith_symlinkAndEntryInvariants_rejected
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test3_dir_data ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test3_sym_data ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  exact checkPackError_of_eval (by decide)

end LeanSwe.Tar.Proofs

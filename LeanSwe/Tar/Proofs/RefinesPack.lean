import LeanSwe.Tar.Model.WireSpec
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem encodeEntryBlocks_eq_model (e : TarEntry) (normPath : String) :
    encodeEntryBlocks e normPath = encodeEntryModel e normPath := by
  unfold encodeEntryBlocks encodeEntryModel
  dsimp only
  simp only [wirePathOfImpl_eq, needsPaxImpl_eq, findUstarSplitImpl_eq, padBlock512Impl_eq,
    buildPaxPayloadImpl_eq, pathFitsUstarImpl_eq, ustarOctal7LimitImpl_eq, ustarOctal11LimitImpl_eq,
    asciiFallback, asciiFallbackModel]
  by_cases hp : (!needsPax e (wirePathOf e.kind normPath)) = true
  · simp only [hp, ↓reduceIte, ← mkUstarHeader_eq_buildUstarHeader]
    cases hk : e.kind <;> rfl
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, ← mkUstarHeader_eq_buildUstarHeader]
    cases hk : e.kind <;> rfl

private def packResRel (a : Except TarError String) (b : Except TarErrKey String) : Prop :=
  match a, b with
  | .ok x, .ok y => x = y
  | .error err, .error key => tarErrKeyOf err = key ∧ !err.message.isEmpty = true
  | _, _ => False

private theorem validatePackEntryTail_refines (e : TarEntry) (normPath : String) :
    packResRel
      (if e.kind != .regular && e.data.size != 0 then
        Except.error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some e.path }
      else if e.kind != .symlink && e.linkTarget != "" then
        .error { kind := .invalidHeader, message := "non-symlink tar entry cannot have linkTarget", entryPath := some e.path }
      else if hasNulStringImpl e.uname || hasNulStringImpl e.gname then
        .error { kind := .invalidHeader, message := "uname/gname cannot contain NUL byte", entryPath := some e.path }
      else if e.uid ≥ u64LimitImpl || e.gid ≥ u64LimitImpl || e.mtime ≥ u64LimitImpl || e.data.size ≥ u64LimitImpl then
        .error { kind := .sizeOverflow, message := "tar entry numeric field exceeds 2^64 - 1", entryPath := some e.path }
      else
        .ok normPath)
      (if e.kind != .regular && e.data.size != 0 then
        Except.error (.invalidHeader, some e.path, none)
      else if e.kind != .symlink && e.linkTarget != "" then
        .error (.invalidHeader, some e.path, none)
      else if hasNulString e.uname || hasNulString e.gname then
        .error (.invalidHeader, some e.path, none)
      else if e.uid ≥ u64Limit || e.gid ≥ u64Limit || e.mtime ≥ u64Limit || e.data.size ≥ u64Limit then
        .error (.sizeOverflow, some e.path, none)
      else
        .ok normPath) := by
  by_cases c1 : (e.kind != .regular && e.data.size != 0) = true
  · simp only [c1, ↓reduceIte, packResRel]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte]
  by_cases c2 : (e.kind != .symlink && e.linkTarget != "") = true
  · simp only [c2, ↓reduceIte, packResRel]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte]
  rw [hasNulStringImpl_eq, hasNulStringImpl_eq]
  by_cases c3 : (hasNulString e.uname || hasNulString e.gname) = true
  · simp only [c3, ↓reduceIte, packResRel]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte]
  rw [u64LimitImpl_eq]
  by_cases c4 : (decide (e.uid ≥ u64Limit) || decide (e.gid ≥ u64Limit) ||
      decide (e.mtime ≥ u64Limit) || decide (e.data.size ≥ u64Limit)) = true
  · simp only [c4, ↓reduceIte, packResRel]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr c4, Bool.false_eq_true, ↓reduceIte, packResRel]

private theorem validatePackEntry_refines (opts : PackOptions) (e : TarEntry) :
    packResRel (validatePackEntry opts e) (validatePackEntryModel opts e) := by
  unfold validatePackEntry validatePackEntryModel
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [validateEntryPathImpl_eq]
  cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | error err =>
    exact ⟨rfl, (validateEntryPath_err_props _ _ _ _ hv).1⟩
  | ok normPath =>
    dsimp only
    cases hk : e.kind with
    | regular | directory =>
      simpa only [hk] using validatePackEntryTail_refines e normPath
    | symlink =>
      dsimp only
      rw [validateSymlinkTargetImpl_eq]
      cases hs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath e.linkTarget with
      | error err =>
        exact ⟨rfl, (validateSymlinkTarget_err_props _ _ _ _ hs).1⟩
      | ok u =>
        cases u
        simpa only [hk] using validatePackEntryTail_refines e normPath

private theorem packWith_go_refines (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) :
    match packWith.go opts rest seen acc, packWithModelAux opts seen rest with
    | .ok bs, .ok mbs => bs = acc ++ mbs
    | .error err, .error key => tarErrKeyOf err = key ∧ !err.message.isEmpty = true
    | _, _ => False := by
  induction rest generalizing seen acc with
  | nil =>
    unfold packWith.go packWithModelAux
    rw [zeroBlockImpl_eq, ByteArray.append_assoc]
  | cons e tail ih =>
    unfold packWith.go packWithModelAux
    simp only [zeroDeterministicMetaImpl_eq]
    have hv := validatePackEntry_refines opts e
    cases hi : validatePackEntry opts e <;> cases hm : validatePackEntryModel opts e
    · simp only [hi, hm, packResRel] at hv
      exact hv
    · simp only [hi, hm, packResRel] at hv
    · simp only [hi, hm, packResRel] at hv
    · simp only [hi, hm, packResRel] at hv
      subst hv
      rename_i normPath
      by_cases hdup : seen.contains normPath = true
      · simp only [hdup, ↓reduceIte]
        refine ⟨rfl, ?_⟩
        dsimp only [ToString.toString]
        exact nonEmpty_append_left (by decide)
      · have hdupF : seen.contains normPath = false := Bool.eq_false_iff.mpr hdup
        simp only [hdupF, Bool.false_eq_true, ↓reduceIte]
        let eff := if opts.deterministic = true then zeroDeterministicMeta e else e
        have hstep := ih (normPath :: seen) (acc ++ encodeEntryBlocks eff normPath)
        cases hgt : packWith.go opts tail (normPath :: seen) (acc ++ encodeEntryBlocks eff normPath) <;>
          cases hmt : packWithModelAux opts (normPath :: seen) tail
        · simp only [hgt, hmt] at hstep
          exact hstep
        · simp only [hgt, hmt] at hstep
        · simp only [hgt, hmt] at hstep
        · simp only [hgt, hmt] at hstep
          simp only [Except.map]
          rw [hstep, encodeEntryBlocks_eq_model, ByteArray.append_assoc]

/-- `LeanSwe.Tar.packWith` refines `Model.allowedPackWith` on all options and entry lists. -/
theorem packWith_refines_model (opts : PackOptions) (entries : List TarEntry) :
    allowedPackWith opts entries (LeanSwe.Tar.packWith opts entries) := by
  unfold allowedPackWith packWithModel LeanSwe.Tar.packWith Impl.packWith
  have h := packWith_go_refines opts entries [] ByteArray.empty
  cases hi : packWith.go opts entries [] ByteArray.empty <;>
    cases hm : packWithModelAux opts [] entries <;>
    simp only [hi, hm] at h ⊢
  · exact h
  · simpa [ByteArray.empty_append] using h

/-- `LeanSwe.Tar.pack` refines `Model.allowedPack` on all entry lists. -/
theorem pack_refines_model (entries : List TarEntry) :
    allowedPack entries (LeanSwe.Tar.pack entries) :=
  packWith_refines_model {} entries

end LeanSwe.Tar.Proofs

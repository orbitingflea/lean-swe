import Core.Obeys
import Core.Assumptions
import LeanSwe.Fs.Interface
import LeanSwe.Fs.Model

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs

private theorem splitCharList_eq (sep : Char) (cs : List Char) :
    Internal.splitCharList sep cs = Model.splitCharList sep cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : (c == sep) = true <;> (simp [Internal.splitCharList, Model.splitCharList, h, ih]; try rfl)

private theorem joinSlashChars_eq (segs : List (List Char)) :
    Internal.joinSlashChars segs = Model.joinSlashChars segs := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons _ _ => simp only [Internal.joinSlashChars, Model.joinSlashChars, ih]

private theorem collapseChars_eq (abs : Bool) (segs acc : List (List Char)) :
    Internal.collapseChars abs segs acc = Model.collapseChars abs segs acc := by
  induction segs generalizing acc with
  | nil => rfl
  | cons seg rest ih =>
    unfold Internal.collapseChars Model.collapseChars
    split
    · exact ih acc
    · split
      · cases acc with
        | nil => exact ih _
        | cons top tail =>
          dsimp only
          split
          · exact ih tail
          · exact ih _
      · exact ih (seg :: acc)

private theorem cleanCharSegments_eq (path : String) :
    Internal.cleanCharSegments path = Model.cleanCharSegments path := by
  unfold Internal.cleanCharSegments Model.cleanCharSegments
  dsimp only
  rw [splitCharList_eq]
  rfl

private theorem splitLastAux_eq {α : Type} (xs acc : List α) :
    Internal.splitLastAux xs acc = Model.splitLastAux xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons _ _ => exact ih (x :: acc)

private theorem splitParentName_eq (path : String) :
    Internal.splitParentName path = Model.splitParentName path := by
  unfold Internal.splitParentName Model.splitParentName
  simp only [cleanCharSegments_eq, splitLastAux_eq, joinSlashChars_eq]
  rfl

private theorem splitRevAtDot_eq (cs : List Char) :
    Internal.splitRevAtDot cs = Model.splitRevAtDot cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : c = '.'
    · subst h; rfl
    · have h1 : Internal.splitRevAtDot (c :: rest) =
          match Internal.splitRevAtDot rest with
          | none => none
          | some (pref, suf) => some (pref, c :: suf) := by
        conv => lhs; rw [Internal.splitRevAtDot.eq_def]
        split
        · contradiction
        · rename_i heq; cases heq; contradiction
        · rename_i heq; cases heq; rfl
      have h2 : Model.splitRevAtDot (c :: rest) =
          match Model.splitRevAtDot rest with
          | none => none
          | some (pref, suf) => some (pref, c :: suf) := by
        conv => lhs; rw [Model.splitRevAtDot.eq_def]
        split
        · contradiction
        · rename_i heq; cases heq; contradiction
        · rename_i heq; cases heq; rfl
      rw [h1, h2, ih]

private theorem splitNameSuffix_eq (fileName : String) :
    Internal.splitNameSuffix fileName = Model.splitNameSuffix fileName := by
  unfold Internal.splitNameSuffix Model.splitNameSuffix
  rw [splitRevAtDot_eq]
  rfl

private theorem stripPrefixParts_eq (bs ps : List (List Char)) :
    Internal.stripPrefixParts bs ps = Model.stripPrefixParts bs ps := by
  induction bs generalizing ps with
  | nil => rfl
  | cons b brest ih =>
    cases ps with
    | nil => rfl
    | cons p prest =>
      unfold Internal.stripPrefixParts Model.stripPrefixParts
      split
      · exact ih prest
      · rfl

/-- Pure refinement for `Fs.join`. -/
theorem refinesPure_join : Core.ObeysPureEq2 LeanSwe.Fs.join LeanSwe.Fs.Model.join :=
  fun _ _ => rfl

/-- Pure refinement for `Fs.joinMany`. -/
theorem refinesPure_joinMany : Core.ObeysPureEq LeanSwe.Fs.joinMany LeanSwe.Fs.Model.joinMany :=
  fun _ => rfl

/-- Pure refinement for `Fs.normPath`. -/
theorem refinesPure_normPath : Core.ObeysPureEq LeanSwe.Fs.normPath LeanSwe.Fs.Model.normPath := fun p => by
  change Internal.normPath p = Model.normPath p
  unfold Internal.normPath Model.normPath
  simp only [splitCharList_eq, collapseChars_eq, joinSlashChars_eq]
  rfl

/-- Pure refinement for `Fs.parent`. -/
theorem refinesPure_parent : Core.ObeysPureEq LeanSwe.Fs.parent LeanSwe.Fs.Model.parent := fun p => by
  change Internal.parent p = Model.parent p
  unfold Internal.parent Model.parent
  rw [splitParentName_eq]
  rfl

/-- Pure refinement for `Fs.name`. -/
theorem refinesPure_name : Core.ObeysPureEq LeanSwe.Fs.name LeanSwe.Fs.Model.name := fun p => by
  change Internal.name p = Model.name p
  unfold Internal.name Model.name
  rw [splitParentName_eq]
  rfl

/-- Pure refinement for `Fs.stem`. -/
theorem refinesPure_stem : Core.ObeysPureEq LeanSwe.Fs.stem LeanSwe.Fs.Model.stem := fun p => by
  change Internal.stem p = Model.stem p
  unfold Internal.stem Model.stem
  have hn : Internal.name p = Model.name p := refinesPure_name p
  simp only [hn, splitNameSuffix_eq]

/-- Pure refinement for `Fs.suffix`. -/
theorem refinesPure_suffix : Core.ObeysPureEq LeanSwe.Fs.suffix LeanSwe.Fs.Model.suffix := fun p => by
  change Internal.suffix p = Model.suffix p
  unfold Internal.suffix Model.suffix
  have hn : Internal.name p = Model.name p := refinesPure_name p
  simp only [hn, splitNameSuffix_eq]
  rfl

/-- Pure refinement for `Fs.suffixes`. -/
theorem refinesPure_suffixes : Core.ObeysPureEq LeanSwe.Fs.suffixes LeanSwe.Fs.Model.suffixes := fun p => by
  change Internal.suffixes p = Model.suffixes p
  unfold Internal.suffixes Model.suffixes
  have hn : Internal.name p = Model.name p := refinesPure_name p
  simp only [hn, splitCharList_eq]
  rfl

/-- Pure refinement for `Fs.withName`. -/
theorem refinesPure_withName : Core.ObeysPureEq2 LeanSwe.Fs.withName LeanSwe.Fs.Model.withName := fun p n => by
  change Internal.withName p n = Model.withName p n
  unfold Internal.withName Model.withName
  simp only [splitParentName_eq]
  rfl

/-- Pure refinement for `Fs.withSuffix`. -/
theorem refinesPure_withSuffix : Core.ObeysPureEq2 LeanSwe.Fs.withSuffix LeanSwe.Fs.Model.withSuffix := fun p s => by
  change Internal.withSuffix p s = Model.withSuffix p s
  unfold Internal.withSuffix Model.withSuffix
  have hwn : ∀ n, Internal.withName p n = Model.withName p n := refinesPure_withName p
  simp only [splitParentName_eq, splitNameSuffix_eq, hwn]
  rfl

/-- Pure refinement for `Fs.isAbsolute`. -/
theorem refinesPure_isAbsolute : Core.ObeysPureEq LeanSwe.Fs.isAbsolute LeanSwe.Fs.Model.isAbsolute :=
  fun _ => rfl

/-- Pure refinement for `Fs.relativeTo`. -/
theorem refinesPure_relativeTo : Core.ObeysPureEq2 LeanSwe.Fs.relativeTo LeanSwe.Fs.Model.relativeTo := fun p b => by
  change Internal.relativeTo p b = Model.relativeTo p b
  unfold Internal.relativeTo Model.relativeTo
  have hnp : Internal.normPath p = Model.normPath p := refinesPure_normPath p
  have hnb : Internal.normPath b = Model.normPath b := refinesPure_normPath b
  simp only [hnp, hnb, cleanCharSegments_eq, stripPrefixParts_eq, joinSlashChars_eq]
  rfl

/-- Pure refinement for `Fs.mapRawError`. -/
theorem refinesPure_mapRawError : Core.ObeysPureEq LeanSwe.Fs.mapRawError LeanSwe.Fs.Model.mapRawError :=
  fun _ => rfl

private theorem withName_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path newName : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.withName path newName) := by
  rw [refinesPure_withName]
  unfold LeanSwe.Fs.Model.withName
  split
  · exact fun h => hk h.symm
  · split
    · exact fun h => hk h.symm
    · trivial

private theorem withSuffix_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path newSuffix : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.withSuffix path newSuffix) := by
  rw [refinesPure_withSuffix]
  unfold LeanSwe.Fs.Model.withSuffix
  split
  · exact fun h => hk h.symm
  · split
    · exact fun h => hk h.symm
    · dsimp only
      split
      · exact fun h => hk h.symm
      · rw [← refinesPure_withName]; exact withName_never_of k hk path _

private theorem relativeTo_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path base : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.relativeTo path base) := by
  rw [refinesPure_relativeTo]
  unfold LeanSwe.Fs.Model.relativeTo
  dsimp only
  split
  · exact fun h => hk h.symm
  · split
    · exact fun h => hk h.symm
    · trivial
    · trivial

/-- `Fs.withName` never returns `.notFound`. -/
theorem fs_withName_never_notFound (path newName : String) : Core.NeverErrorKindPure FsError.kind .notFound (LeanSwe.Fs.withName path newName) := withName_never_of .notFound (by decide) path newName
/-- `Fs.withName` never returns `.alreadyExists`. -/
theorem fs_withName_never_alreadyExists (path newName : String) : Core.NeverErrorKindPure FsError.kind .alreadyExists (LeanSwe.Fs.withName path newName) := withName_never_of .alreadyExists (by decide) path newName
/-- `Fs.withName` never returns `.permissionDenied`. -/
theorem fs_withName_never_permissionDenied (path newName : String) : Core.NeverErrorKindPure FsError.kind .permissionDenied (LeanSwe.Fs.withName path newName) := withName_never_of .permissionDenied (by decide) path newName
/-- `Fs.withName` never returns `.isADirectory`. -/
theorem fs_withName_never_isADirectory (path newName : String) : Core.NeverErrorKindPure FsError.kind .isADirectory (LeanSwe.Fs.withName path newName) := withName_never_of .isADirectory (by decide) path newName
/-- `Fs.withName` never returns `.notADirectory`. -/
theorem fs_withName_never_notADirectory (path newName : String) : Core.NeverErrorKindPure FsError.kind .notADirectory (LeanSwe.Fs.withName path newName) := withName_never_of .notADirectory (by decide) path newName
/-- `Fs.withName` never returns `.notEmpty`. -/
theorem fs_withName_never_notEmpty (path newName : String) : Core.NeverErrorKindPure FsError.kind .notEmpty (LeanSwe.Fs.withName path newName) := withName_never_of .notEmpty (by decide) path newName
/-- `Fs.withName` never returns `.unsupported`. -/
theorem fs_withName_never_unsupported (path newName : String) : Core.NeverErrorKindPure FsError.kind .unsupported (LeanSwe.Fs.withName path newName) := withName_never_of .unsupported (by decide) path newName
/-- `Fs.withName` never returns `.wouldBlock`. -/
theorem fs_withName_never_wouldBlock (path newName : String) : Core.NeverErrorKindPure FsError.kind .wouldBlock (LeanSwe.Fs.withName path newName) := withName_never_of .wouldBlock (by decide) path newName
/-- `Fs.withName` never returns `.ioError`. -/
theorem fs_withName_never_ioError (path newName : String) : Core.NeverErrorKindPure FsError.kind .ioError (LeanSwe.Fs.withName path newName) := withName_never_of .ioError (by decide) path newName

/-- `Fs.withSuffix` never returns `.notFound`. -/
theorem fs_withSuffix_never_notFound (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .notFound (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .notFound (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.alreadyExists`. -/
theorem fs_withSuffix_never_alreadyExists (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .alreadyExists (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .alreadyExists (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.permissionDenied`. -/
theorem fs_withSuffix_never_permissionDenied (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .permissionDenied (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .permissionDenied (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.isADirectory`. -/
theorem fs_withSuffix_never_isADirectory (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .isADirectory (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .isADirectory (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.notADirectory`. -/
theorem fs_withSuffix_never_notADirectory (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .notADirectory (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .notADirectory (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.notEmpty`. -/
theorem fs_withSuffix_never_notEmpty (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .notEmpty (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .notEmpty (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.unsupported`. -/
theorem fs_withSuffix_never_unsupported (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .unsupported (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .unsupported (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.wouldBlock`. -/
theorem fs_withSuffix_never_wouldBlock (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .wouldBlock (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .wouldBlock (by decide) path newSuffix
/-- `Fs.withSuffix` never returns `.ioError`. -/
theorem fs_withSuffix_never_ioError (path newSuffix : String) : Core.NeverErrorKindPure FsError.kind .ioError (LeanSwe.Fs.withSuffix path newSuffix) := withSuffix_never_of .ioError (by decide) path newSuffix

/-- `Fs.relativeTo` never returns `.notFound`. -/
theorem fs_relativeTo_never_notFound (path base : String) : Core.NeverErrorKindPure FsError.kind .notFound (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .notFound (by decide) path base
/-- `Fs.relativeTo` never returns `.alreadyExists`. -/
theorem fs_relativeTo_never_alreadyExists (path base : String) : Core.NeverErrorKindPure FsError.kind .alreadyExists (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .alreadyExists (by decide) path base
/-- `Fs.relativeTo` never returns `.permissionDenied`. -/
theorem fs_relativeTo_never_permissionDenied (path base : String) : Core.NeverErrorKindPure FsError.kind .permissionDenied (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .permissionDenied (by decide) path base
/-- `Fs.relativeTo` never returns `.isADirectory`. -/
theorem fs_relativeTo_never_isADirectory (path base : String) : Core.NeverErrorKindPure FsError.kind .isADirectory (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .isADirectory (by decide) path base
/-- `Fs.relativeTo` never returns `.notADirectory`. -/
theorem fs_relativeTo_never_notADirectory (path base : String) : Core.NeverErrorKindPure FsError.kind .notADirectory (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .notADirectory (by decide) path base
/-- `Fs.relativeTo` never returns `.notEmpty`. -/
theorem fs_relativeTo_never_notEmpty (path base : String) : Core.NeverErrorKindPure FsError.kind .notEmpty (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .notEmpty (by decide) path base
/-- `Fs.relativeTo` never returns `.unsupported`. -/
theorem fs_relativeTo_never_unsupported (path base : String) : Core.NeverErrorKindPure FsError.kind .unsupported (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .unsupported (by decide) path base
/-- `Fs.relativeTo` never returns `.wouldBlock`. -/
theorem fs_relativeTo_never_wouldBlock (path base : String) : Core.NeverErrorKindPure FsError.kind .wouldBlock (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .wouldBlock (by decide) path base
/-- `Fs.relativeTo` never returns `.ioError`. -/
theorem fs_relativeTo_never_ioError (path base : String) : Core.NeverErrorKindPure FsError.kind .ioError (LeanSwe.Fs.relativeTo path base) := relativeTo_never_of .ioError (by decide) path base

end LeanSwe.Fs.Proofs

import Core.Refines
import Core.Assumptions
import LeanSwe.Fs.Interface
import LeanSwe.Fs.Model

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs

/-- Pure refinement for `Fs.join`. -/
theorem refinesPure_join : Core.RefinesPureEq2 LeanSwe.Fs.join LeanSwe.Fs.Model.join :=
  fun _ _ => rfl

/-- Pure refinement for `Fs.joinMany`. -/
theorem refinesPure_joinMany : Core.RefinesPureEq LeanSwe.Fs.joinMany LeanSwe.Fs.Model.joinMany :=
  fun _ => rfl

/-- Pure refinement for `Fs.normPath`. -/
theorem refinesPure_normPath : Core.RefinesPureEq LeanSwe.Fs.normPath LeanSwe.Fs.Model.normPath :=
  fun _ => rfl

/-- Pure refinement for `Fs.parent`. -/
theorem refinesPure_parent : Core.RefinesPureEq LeanSwe.Fs.parent LeanSwe.Fs.Model.parent :=
  fun _ => rfl

/-- Pure refinement for `Fs.name`. -/
theorem refinesPure_name : Core.RefinesPureEq LeanSwe.Fs.name LeanSwe.Fs.Model.name :=
  fun _ => rfl

/-- Pure refinement for `Fs.stem`. -/
theorem refinesPure_stem : Core.RefinesPureEq LeanSwe.Fs.stem LeanSwe.Fs.Model.stem :=
  fun _ => rfl

/-- Pure refinement for `Fs.suffix`. -/
theorem refinesPure_suffix : Core.RefinesPureEq LeanSwe.Fs.suffix LeanSwe.Fs.Model.suffix :=
  fun _ => rfl

/-- Pure refinement for `Fs.suffixes`. -/
theorem refinesPure_suffixes : Core.RefinesPureEq LeanSwe.Fs.suffixes LeanSwe.Fs.Model.suffixes :=
  fun _ => rfl

/-- Pure refinement for `Fs.withName`. -/
theorem refinesPure_withName : Core.RefinesPureEq2 LeanSwe.Fs.withName LeanSwe.Fs.Model.withName :=
  fun _ _ => rfl

/-- Pure refinement for `Fs.withSuffix`. -/
theorem refinesPure_withSuffix : Core.RefinesPureEq2 LeanSwe.Fs.withSuffix LeanSwe.Fs.Model.withSuffix :=
  fun _ _ => rfl

/-- Pure refinement for `Fs.isAbsolute`. -/
theorem refinesPure_isAbsolute : Core.RefinesPureEq LeanSwe.Fs.isAbsolute LeanSwe.Fs.Model.isAbsolute :=
  fun _ => rfl

/-- Pure refinement for `Fs.relativeTo`. -/
theorem refinesPure_relativeTo : Core.RefinesPureEq2 LeanSwe.Fs.relativeTo LeanSwe.Fs.Model.relativeTo :=
  fun _ _ => rfl

/-- Pure refinement for `Fs.mapRawError`. -/
theorem refinesPure_mapRawError : Core.RefinesPureEq LeanSwe.Fs.mapRawError LeanSwe.Fs.Model.mapRawError :=
  fun _ => rfl

private theorem withName_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path newName : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.withName path newName) := by
  change Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.Model.withName path newName)
  unfold LeanSwe.Fs.Model.withName
  split
  · exact fun h => hk h.symm
  · split
    · exact fun h => hk h.symm
    · trivial

private theorem withSuffix_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path newSuffix : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.withSuffix path newSuffix) := by
  change Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.Model.withSuffix path newSuffix)
  unfold LeanSwe.Fs.Model.withSuffix
  split
  · exact fun h => hk h.symm
  · split
    · exact fun h => hk h.symm
    · dsimp only
      split
      · exact fun h => hk h.symm
      · exact withName_never_of k hk path _

private theorem relativeTo_never_of (k : FsErrorKind) (hk : k ≠ .invalidInput) (path base : String) :
    Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.relativeTo path base) := by
  change Core.NeverErrorKindPure FsError.kind k (LeanSwe.Fs.Model.relativeTo path base)
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

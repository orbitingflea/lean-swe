import Core.Refines
import LeanSwe.Fs.Interface
import LeanSwe.Fs.Model.HealthyStep
import LeanSwe.Fs.SpecTests
import LeanSwe.Fs.Proofs.RawDirOps
import LeanSwe.Fs.Proofs.SubtreeIsolation
import LeanSwe.Fs.Proofs.SubtreeModelSpecs
import LeanSwe.Fs.Proofs.SubtreeTests
import LeanSwe.Fs.Proofs.PurePathProofs
import LeanSwe.Fs.Proofs.VfsShared
import LeanSwe.Fs.Proofs.CopyTreeProofs
import LeanSwe.Fs.Proofs.LockProofs
import LeanSwe.Fs.Proofs.AtomicWriteProofs
import LeanSwe.Fs.Proofs.FsRefines

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Full public `Interface` refinement of `LeanSwe.Fs` against `LeanSwe.Fs.Model` and `LeanSwe.LinuxSyscall.Files.healthyStep`. -/
theorem refines_model :
    Core.RefinesPureEq2 LeanSwe.Fs.join Model.join ∧
    Core.RefinesPureEq LeanSwe.Fs.joinMany Model.joinMany ∧
    Core.RefinesPureEq LeanSwe.Fs.normPath Model.normPath ∧
    Core.RefinesPureEq LeanSwe.Fs.parent Model.parent ∧
    Core.RefinesPureEq LeanSwe.Fs.name Model.name ∧
    Core.RefinesPureEq LeanSwe.Fs.stem Model.stem ∧
    Core.RefinesPureEq LeanSwe.Fs.suffix Model.suffix ∧
    Core.RefinesPureEq LeanSwe.Fs.suffixes Model.suffixes ∧
    Core.RefinesPureEq2 LeanSwe.Fs.withName Model.withName ∧
    Core.RefinesPureEq2 LeanSwe.Fs.withSuffix Model.withSuffix ∧
    Core.RefinesPureEq LeanSwe.Fs.isAbsolute Model.isAbsolute ∧
    Core.RefinesPureEq2 LeanSwe.Fs.relativeTo Model.relativeTo ∧
    Core.RefinesPureEq LeanSwe.Fs.mapRawError Model.mapRawError ∧
    Core.RefinesStepFromFinally id fsWorldWf
      execScopedRawFsStep allowedScopedRawFsStep
      fsWorldWf Internal.mkApiFromScopedRawM
      execFsStep allowedFsStep ∧
    Core.RefinesStepFromFinally id fsWorldWf
      execFilesCapStep allowedFilesCapStep
      fsWorldWf Internal.mkApiFromHealthyFilesM
      execFsStep allowedFsStep ∧
    Core.RefinesStepFromFinally id fsWorldWf
      execFilesCapStep allowedFilesCapStep
      fsWorldWf Internal.mkSubtreeOpenerFromHealthyFilesM
      execSubtreeStep allowedSubtreeStep :=
  ⟨refinesPure_join,
   refinesPure_joinMany,
   refinesPure_normPath,
   refinesPure_parent,
   refinesPure_name,
   refinesPure_stem,
   refinesPure_suffix,
   refinesPure_suffixes,
   refinesPure_withName,
   refinesPure_withSuffix,
   refinesPure_isAbsolute,
   refinesPure_relativeTo,
   refinesPure_mapRawError,
   refinesStepFromFinally_mkApiFromScopedRawM,
   refinesStepFromFinally_mkApiFromHealthyFilesM,
   refinesStepFromFinally_mkSubtreeOpenerFromHealthyFilesM⟩

end LeanSwe.Fs.Proofs

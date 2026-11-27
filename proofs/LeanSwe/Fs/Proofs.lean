import Core.Obeys
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

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.Fs` against `LeanSwe.Fs.Model`, `LeanSwe.LinuxSyscall.Files.healthyStep`, and `LeanSwe.LinuxSyscall.TimeRand.healthyStep`. -/
theorem obeys_model :
    Core.ObeysPureEq2 LeanSwe.Fs.join Model.join ∧
    Core.ObeysPureEq LeanSwe.Fs.joinMany Model.joinMany ∧
    Core.ObeysPureEq LeanSwe.Fs.normPath Model.normPath ∧
    Core.ObeysPureEq LeanSwe.Fs.parent Model.parent ∧
    Core.ObeysPureEq LeanSwe.Fs.name Model.name ∧
    Core.ObeysPureEq LeanSwe.Fs.stem Model.stem ∧
    Core.ObeysPureEq LeanSwe.Fs.suffix Model.suffix ∧
    Core.ObeysPureEq LeanSwe.Fs.suffixes Model.suffixes ∧
    Core.ObeysPureEq2 LeanSwe.Fs.withName Model.withName ∧
    Core.ObeysPureEq2 LeanSwe.Fs.withSuffix Model.withSuffix ∧
    Core.ObeysPureEq LeanSwe.Fs.isAbsolute Model.isAbsolute ∧
    Core.ObeysPureEq2 LeanSwe.Fs.relativeTo Model.relativeTo ∧
    Core.ObeysPureEq LeanSwe.Fs.mapRawError Model.mapRawError ∧
    Core.ObeysStepFromFinally fsDepsWorldToFsWorld fsDepsWorldWf
      execFsSysCapStep allowedFsSysCapStep
      fsWorldWf Internal.mkSubtreeOpenerFromCapsM
      execSubtreeStep allowedSubtreeStep ∧
    Core.ObeysStepFromFinally fsDepsWorldToFsWorld fsDepsWorldWf
      execFsSysCapStep allowedFsSysCapStep
      fsWorldWf Internal.mkApiFromCapsM
      execFsStep allowedFsStep :=
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
   refinesStepFromFinally_mkSubtreeOpenerFromCapsM,
   refinesStepFromFinally_mkApiFromCapsM⟩

end LeanSwe.Fs.Proofs

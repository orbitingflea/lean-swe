import Core.Obeys
import LeanSwe.Fs.Interface
import LeanSweProofs.Fs.Model.HealthyStep
import LeanSweProofs.Fs.SpecTests
import LeanSweProofs.Fs.Proofs.RawDirOps
import LeanSweProofs.Fs.Proofs.SubtreeIsolation
import LeanSweProofs.Fs.Proofs.SubtreeModelSpecs
import LeanSweProofs.Fs.Proofs.SubtreeTests
import LeanSweProofs.Fs.Proofs.PurePathProofs
import LeanSweProofs.Fs.Proofs.VfsShared
import LeanSweProofs.Fs.Proofs.CopyTreeProofs
import LeanSweProofs.Fs.Proofs.LockProofs
import LeanSweProofs.Fs.Proofs.AtomicWriteProofs
import LeanSweProofs.Fs.Proofs.FsRefines

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

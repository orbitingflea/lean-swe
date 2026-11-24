import LeanSwe.Process.Interface
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.SysBridge

/-!
Exact bridging theorems connecting `LeanSwe.Process.defaultApi` (`SysBridge.defaultOps`)
to `Internal.mkApiFromCapsM` over `ioHostCaps`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.Process

/-- Host capability bundle over `IO` wrapping `LinuxSyscall.*.defaultOps`, `PostFork.defaultOps`, `EnvVars.Raw.listEnvironBytes`, and `SysBridge.ioProcTableOps`. -/
def ioHostCaps : Model.ProcessHostCapsM LinuxSyscall.RawFd IO where
  proc := LinuxSyscall.Process.defaultOps
  files := LinuxSyscall.Files.defaultOps
  poll := LinuxSyscall.Poll.defaultOps
  timeRand := LinuxSyscall.TimeRand.defaultOps
  postFork := PostFork.defaultOps
  listEnvironBytes := EnvVars.Raw.listEnvironBytes
  table := SysBridge.ioProcTableOps

/-- `LeanSwe.Process.defaultApi` pure operations and `activeProcessCount` match `Internal.mkApiFromCapsM ioHostCaps` definitionally. -/
theorem defaultApi_pure_and_activeCount_eq_mkApiFromCapsM :
    LeanSwe.Process.defaultApi.mapRawError = (Internal.mkApiFromCapsM ioHostCaps).mapRawError ∧
    LeanSwe.Process.defaultApi.validateRequest = (Internal.mkApiFromCapsM ioHostCaps).validateRequest ∧
    LeanSwe.Process.defaultApi.mkCommandRequest = (Internal.mkApiFromCapsM ioHostCaps).mkCommandRequest ∧
    LeanSwe.Process.defaultApi.withTextInput = (Internal.mkApiFromCapsM ioHostCaps).withTextInput ∧
    LeanSwe.Process.defaultApi.activeProcessCount = (Internal.mkApiFromCapsM ioHostCaps).activeProcessCount :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `SysBridge.ioSysDeps` and `SysBridge.ioProcTableOps` match the capability projections of `Internal.mkApiFromCapsM ioHostCaps`. -/
theorem defaultOps_core_eq_mkApiFromCapsM :
    SysBridge.mkRawOpsM SysBridge.ioSysDeps SysBridge.ioProcTableOps =
      SysBridge.mkRawOpsM
        { proc := ioHostCaps.proc
          files := ioHostCaps.files
          poll := ioHostCaps.poll
          timeRand := ioHostCaps.timeRand
          postFork := ioHostCaps.postFork
          listAmbientEnv := Except.ok <$> ioHostCaps.listEnvironBytes }
        ioHostCaps.table := by
  have hDeps : SysBridge.ioSysDeps =
      { proc := ioHostCaps.proc, files := ioHostCaps.files, poll := ioHostCaps.poll,
        timeRand := ioHostCaps.timeRand, postFork := ioHostCaps.postFork,
        listAmbientEnv := Except.ok <$> ioHostCaps.listEnvironBytes } := by
    have hEnv : SysBridge.ioSysDeps.listAmbientEnv = (Except.ok <$> ioHostCaps.listEnvironBytes) := by
      funext s
      dsimp only [SysBridge.ioSysDeps, ioHostCaps, Bind.bind, Pure.pure, Functor.map,
        EStateM.bind, EStateM.pure, EStateM.map]
      cases EnvVars.Raw.listEnvironBytes s <;> rfl
    dsimp only [SysBridge.ioSysDeps, ioHostCaps]
    congr 1
  rw [hDeps]
  rfl

end LeanSwe.Process.Proofs

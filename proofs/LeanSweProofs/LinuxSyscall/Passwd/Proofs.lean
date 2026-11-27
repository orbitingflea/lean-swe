import Core.Obeys
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSweProofs.LinuxSyscall.Passwd.Model
import LeanSweProofs.LinuxSyscall.Passwd.Model.Refines
import LeanSwe.LinuxSyscall.Passwd.Impl
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSweProofs.LinuxSyscall.Passwd.SpecTests
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.ModelCore
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.ModelSoundness
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.OpsContracts
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.HealthyStep
import LeanSweProofs.LinuxSyscall.Passwd.Proofs.IoAndObeys

/-!
Top-level umbrella verification module for `LeanSwe.LinuxSyscall.Passwd`. Re-exports all
specification proofs (`AllPass` and `CanReach`) and exposes the canonical `obeys_model`
capability-refinement theorem alongside `obeys_model_nonvacuous`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open LeanSwe.LinuxSyscall.Passwd

/-- Canonical `Core.ObeysStepFrom` capability refinement for `LeanSwe.LinuxSyscall.Passwd`,
covering `Internal.mkPasswdOpsM` and both public `Interface` operations (`getpwuid`, `getpwnam`)
over `HealthyEnv`. -/
theorem obeys_model :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkPasswdOpsM Model.execPkgStep Model.allowedPkgStep :=
  obeysStepFrom_passwd

/-- Non-vacuity witness showing both `Model.rawStepWf` and the raw `Internal.PosixPasswdOpsM`
contract in `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ env : HealthyEnv, Model.rawStepWf env = true) ∧
    (∃ raw : Internal.PosixPasswdOpsM (StateM HealthyEnv),
      Core.ObeysStep id Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep) :=
  ⟨⟨HealthyEnv.initial 1, healthyEnv_initial_wf 1 true⟩,
   ⟨Model.modelRawOps, modelRawOps_obeys_allowedRawStep⟩⟩

end LeanSwe.LinuxSyscall.Passwd.Proofs

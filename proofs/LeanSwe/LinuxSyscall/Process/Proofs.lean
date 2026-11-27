import Core.Obeys
import LeanSwe.LinuxSyscall.Process.Proofs.BitAndWiring
import LeanSwe.LinuxSyscall.Process.Proofs.ConcreteSpec
import LeanSwe.LinuxSyscall.Process.Proofs.ModelSoundness
import LeanSwe.LinuxSyscall.Process.Proofs.HealthyStep
import LeanSwe.LinuxSyscall.Process.Proofs.ObeysRaw
import LeanSwe.LinuxSyscall.Process.Proofs.ObeysHealthy

namespace LeanSwe.LinuxSyscall.Process.Proofs

open LeanSwe.LinuxSyscall.Process

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.LinuxSyscall.Process` against `Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.LinuxSyscall.Process.killTargetOfPgid Model.killTargetOfPgid ∧
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkProcessOps Model.execPkgStep Model.allowedPkgStep :=
  ⟨fun _ => rfl, mkProcessOps_obeysStepFrom⟩

/-- Non-vacuity witness for `LeanSwe.LinuxSyscall.Process` `obeys_model` (`HealthyEnv.wf`, `allowedRawStep`, `allowedPkgStep`, and `allowedWaitpidReapLoop` are simultaneously inhabited). -/
theorem obeys_model_nonvacuous :
    (∃ env₀ : HealthyEnv, HealthyEnv.wf env₀ = true) ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execWaitpidReapLoop
        (LeanSwe.LinuxSyscall.Process.waitpidReapLoop Model.healthyModelOps))
      Model.allowedWaitpidReapLoop :=
  ⟨⟨HealthyEnv.initial, rfl⟩,
   rawHealthyModelOps_obeysStep,
   healthyModelOps_obeysStep,
   waitpidReapLoop_obeysStepFrom id Model.healthyModelOps healthyModelOps_obeysSingleStep⟩

end LeanSwe.LinuxSyscall.Process.Proofs

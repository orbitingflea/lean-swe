import Core.Obeys
import LeanSwe.LinuxSyscall.Net.Proofs.CodecsAndBounds
import LeanSwe.LinuxSyscall.Net.Proofs.OpsLifecycle
import LeanSwe.LinuxSyscall.Net.Proofs.StateTransitions
import LeanSwe.LinuxSyscall.Net.Proofs.ModelSoundness
import LeanSwe.LinuxSyscall.Net.Proofs.HealthyStep
import LeanSwe.LinuxSyscall.Net.Proofs.ObeysRaw
import LeanSwe.LinuxSyscall.Net.Proofs.ObeysHealthyBase
import LeanSwe.LinuxSyscall.Net.Proofs.ObeysHealthyConn
import LeanSwe.LinuxSyscall.Net.Proofs.ObeysHealthyIo
import LeanSwe.LinuxSyscall.Net.Proofs.ObeysHealthyTop

namespace LeanSwe.LinuxSyscall.Net.Proofs

open LeanSwe.LinuxSyscall.Net

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.LinuxSyscall.Net` against `Model`. -/
theorem obeys_model :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkNetOpsM Model.execPkgStep Model.allowedPkgStep :=
  mkNetOpsM_obeysStepFrom

/-- Non-vacuity witness for `LeanSwe.LinuxSyscall.Net` `obeys_model` (`HealthyEnv.wf`, `allowedRawStep`, and `allowedPkgStep` are simultaneously inhabited). -/
theorem obeys_model_nonvacuous :
    (∃ env₀ : HealthyEnv, HealthyEnv.wf env₀ = true) ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep :=
  ⟨⟨HealthyEnv.initial, rfl⟩, rawHealthyModelOps_obeysStep, healthyModelOps_obeysStep⟩

end LeanSwe.LinuxSyscall.Net.Proofs

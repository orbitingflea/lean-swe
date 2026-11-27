import Core.Obeys
import LeanSweProofs.LinuxSyscall.Net.Proofs.CodecsAndBounds
import LeanSweProofs.LinuxSyscall.Net.Proofs.OpsLifecycle
import LeanSweProofs.LinuxSyscall.Net.Proofs.StateTransitions
import LeanSweProofs.LinuxSyscall.Net.Proofs.ModelSoundness
import LeanSweProofs.LinuxSyscall.Net.Proofs.HealthyStep
import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysRaw
import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysHealthyBase
import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysHealthyConn
import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysHealthyIo
import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysHealthyTop

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

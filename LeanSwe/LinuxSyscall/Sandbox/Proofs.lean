import Core.Obeys
import LeanSwe.LinuxSyscall.Sandbox.Model.Refines
import LeanSwe.LinuxSyscall.Sandbox.Proofs.Basic
import LeanSwe.LinuxSyscall.Sandbox.Proofs.Ops
import LeanSwe.LinuxSyscall.Sandbox.Proofs.ModelRel
import LeanSwe.LinuxSyscall.Sandbox.Proofs.ModelEnv
import LeanSwe.LinuxSyscall.Sandbox.Proofs.Model
import LeanSwe.LinuxSyscall.Sandbox.Proofs.HealthyStep
import LeanSwe.LinuxSyscall.Sandbox.Proofs.ObeysModel

/-!
Top-level umbrella verification module for `LeanSwe.LinuxSyscall.Sandbox`. Re-exports all
specification proofs and exposes the canonical `obeys_model` capability-refinement theorem
alongside `obeys_model_nonvacuous`.
-/

namespace LeanSwe.LinuxSyscall.Sandbox.Proofs

open LeanSwe.LinuxSyscall.Sandbox

/-- Canonical `Core.ObeysStepFrom` capability refinement for `LeanSwe.LinuxSyscall.Sandbox`,
covering `Internal.mkSandboxOpsM` and all 7 public `Interface` operations (`landlockCreateRuleset`,
`landlockAddRule`, `landlockRestrictSelf`, `seccomp`, `prctl`, `setrlimit`, `memfdCreate`)
over `HealthyEnv`. -/
theorem obeys_model :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkSandboxOpsM Model.execPkgStep Model.allowedPkgStep :=
  obeysStepFrom_sandbox

/-- Non-vacuity witness showing both `Model.rawStepWf` and the raw `PosixSandboxOpsM`
contract in `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ env : HealthyEnv, Model.rawStepWf env = true) ∧
    (∃ raw : Model.RawSandboxOpsM (StateM HealthyEnv),
      Core.ObeysStep id Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep) :=
  ⟨⟨HealthyEnv.initial 1, healthyEnv_initial_wf 1⟩,
   ⟨Model.modelRawOps, modelRawOps_obeys_allowedRawStep⟩⟩

end LeanSwe.LinuxSyscall.Sandbox.Proofs

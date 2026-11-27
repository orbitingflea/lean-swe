import LeanSweProofs.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `allowedStep` and `allowedStepCore` enforce the relational invariants tested in `test_sandbox_model_allowedStep_relationalInvariants`. -/
theorem sandbox_model_allowedStep_relationalInvariants_allPass :
    AllPass (test_sandbox_model_allowedStep_relationalInvariants allowedStep) := by
  dsimp only [AllPass, test_sandbox_model_allowedStep_relationalInvariants, NondetTest.assert,
    Bind.bind, Pure.pure]
  repeat first | exact trivial | refine ⟨?_, ?_⟩ | decide +kernel

end LeanSwe.LinuxSyscall.Sandbox

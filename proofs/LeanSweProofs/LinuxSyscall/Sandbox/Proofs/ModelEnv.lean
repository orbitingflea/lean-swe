import LeanSweProofs.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `allowedStep` satisfies environment-freedom, `CLONE_NEWUSER`, stacked Landlock cap, and `O_PATH`/`pseudoFs` checks. -/
theorem sandbox_model_allowedStep_environmentFreeAndOPath_allPass :
    AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath allowedStep) := by
  dsimp only [AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath, NondetTest.assert,
    Bind.bind, Pure.pure]
  repeat first | exact trivial | refine ⟨?_, ?_⟩ | decide +kernel

end LeanSwe.LinuxSyscall.Sandbox

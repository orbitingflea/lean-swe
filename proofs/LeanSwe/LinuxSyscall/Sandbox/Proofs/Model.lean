import LeanSwe.LinuxSyscall.Sandbox.Proofs.ModelMisc

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- Every well-formed `s : SandboxSysState` and `req : SandboxReq` executed on `modelOps` refines `allowedStep` and preserves `wf`. -/
theorem sandbox_model_modelOpsRefinesAllowedStep_allPass :
    AllPass (test_sandbox_model_modelOpsRefinesAllowedStep modelOps allowedStep) := by
  dsimp only [AllPass, test_sandbox_model_modelOpsRefinesAllowedStep, NondetTest.assert,
    Bind.bind, Pure.pure]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro s hwf req
  cases req with
  | landlockCreateRuleset attr? flags =>
    have h := refine_landlockCreateRuleset s hwf attr? flags
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | landlockAddRule ruleset rule =>
    have h := refine_landlockAddRule s hwf ruleset rule
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | landlockRestrictSelf ruleset =>
    have h := refine_landlockRestrictSelf s hwf ruleset
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | seccomp op flags filterBytes =>
    have h := refine_seccomp s hwf op flags filterBytes
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | prctl op =>
    have h := refine_prctl s hwf op
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | setrlimit res cur max =>
    have h := refine_setrlimit s hwf res cur max
    exact ⟨⟨h.1, h.2⟩, trivial⟩
  | memfdCreate name flags =>
    have h := refine_memfdCreate s hwf name flags
    exact ⟨⟨h.1, h.2⟩, trivial⟩

/-- Reachability witness for `test_sandbox_model_modelOpsRefinesAllowedStep`. -/
theorem sandbox_model_modelOpsRefinesAllowedStep_canReach :
    CanReach (test_sandbox_model_modelOpsRefinesAllowedStep modelOps allowedStep) := by
  dsimp only [CanReach, CanReachRun, test_sandbox_model_modelOpsRefinesAllowedStep, NondetTest.assert,
    Bind.bind, Pure.pure]
  have h := refine_prctl SandboxSysState.initial rfl .getNoNewPrivs
  exact ⟨⟨rfl, rfl⟩, SandboxSysState.initial, rfl, .prctl .getNoNewPrivs, ⟨⟨h.1, h.2⟩, trivial⟩⟩

end LeanSwe.LinuxSyscall.Sandbox

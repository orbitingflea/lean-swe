import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Seccomp.Proofs
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.ApiProofs
import LeanSwe.ProcessSandbox.Proofs.ApiSpawnOkProofs

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Seccomp.Proofs

/-- Proof of `test_seccomp_run_queriesHostArchAndSealsEncodedFilter` for `Internal.mkApiM`. -/
theorem proof_seccomp_run_queriesHostArchAndSealsEncodedFilter :
    AllPass (test_seccomp_run_queriesHostArchAndSealsEncodedFilter Internal.mkApiM) := by
  intro arch s₀ ⟨hB, hM, hP⟩ ⟨hSpFail, _⟩ hScriptOk
  let sArch : MockSandboxState := { s₀ with hostSeccompArch? := some arch }
  let spec : BoxSpec := { program := "/bin/true" }
  let valid : ValidBoxSpec :=
    { program := "/bin/true"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hVal : validateSpecPure spec = .ok valid :=
    validateSpecPure_simple "/bin/true" ByteArray.empty 60_000 (some (16 * 1024 * 1024))
      (by decide) (by decide) (by decide)
  have hRun := runGeneric_mock_spawn_ok (s₀ := sArch) hVal hB (fun _ => hM) (fun _ => hP) rfl hSpFail
  have hEmpty : (compilePlan valid sArch.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpty, ↓reduceIte] at hRun
  dsimp only [Internal.mkApiM]
  dsimp only [spec] at hRun
  rw [hRun]
  cases hScr : sArch.scriptedOutput with
  | error _ =>
    have hScr' : s₀.scriptedOutput.isOk = false := by
      rw [show s₀.scriptedOutput = sArch.scriptedOutput from rfl, hScr]; rfl
    simp [hScr'] at hScriptOk
  | ok res =>
    have hResOk :
        (match mockReadResult (.ok res) valid.limits.maxOutputBytes with
         | Except.error e => Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | Except.ok out => Except.ok out).isOk = true := rfl
    dsimp only [assert]
    refine ⟨⟨hResOk, compileSeccompBpf_valid arch, encodeSeccompBpf_eq_model_pub _,
      eval_compiled_nr0_allow arch, eval_compiled_bad_arch_eperm arch,
      by unfold Internal.encodedSeccompFilter; rfl, rfl, rfl, rfl⟩, ?_⟩
    intro sNoArch specFail hSpecOk ⟨hB', hM', hP', hNoArch⟩
    cases hV : validateSpecPure specFail with
    | error _ => simp [Internal.validateSpec, hV, Except.isOk, Except.toBool] at hSpecOk
    | ok validF =>
      have hRunFail := runGeneric_mock_host_arch_none (s₀ := sNoArch) hV hB' (fun _ => hM') (fun _ => hP') hNoArch
      rw [hRunFail]
      dsimp only [assert]
      exact ⟨⟨⟨_, rfl, rfl, by decide⟩, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem reach_seccomp_run_helper (arch : SeccompArch) (s₀ : MockSandboxState)
    (hPre : s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧ s₀.pidsCgroupAvailable = true)
    (hFail : s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none)
    (hScr : s₀.scriptedOutput.isOk = true) :
    CanReach (test_seccomp_run_queriesHostArchAndSealsEncodedFilter Internal.mkApiM) := by
  let sNoArch : MockSandboxState := { hostSeccompArch? := none }
  have hAll := proof_seccomp_run_queriesHostArchAndSealsEncodedFilter arch s₀ hPre hFail hScr
  dsimp only [assert] at hAll
  refine ⟨arch, s₀, hPre, hFail, hScr, hAll.1, sNoArch, { program := "/bin/true" },
    rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  exact hAll.2 sNoArch { program := "/bin/true" } rfl ⟨rfl, rfl, rfl, rfl⟩

/-- Non-vacuity `CanReach` witness for `test_seccomp_run_queriesHostArchAndSealsEncodedFilter`. -/
theorem reach_seccomp_run_queriesHostArchAndSealsEncodedFilter :
    CanReach (test_seccomp_run_queriesHostArchAndSealsEncodedFilter Internal.mkApiM) :=
  reach_seccomp_run_helper .x86_64 {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl

end LeanSwe.ProcessSandbox.Proofs

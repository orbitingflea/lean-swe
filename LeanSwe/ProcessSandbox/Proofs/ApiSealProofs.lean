import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.ApiProofs
import LeanSwe.ProcessSandbox.Proofs.ApiSpawnOkProofs

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

/-- Proof of `test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan :
    AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP, hArch⟩ ⟨hSpFail, _⟩
  rcases Option.isSome_iff_exists.mp hArch with ⟨arch, hArchEq⟩
  let preset0 : HostRuntimePreset :=
    { systemEntries :=
        #[ .readOnlyDir "/usr"
         , .topSymlink "/bin" "usr/bin"
         , .topSymlink "/lib" "usr/lib"
         , .readOnlyDir "/home" ]
      etcPaths := #["/etc/passwd", "/etc/localtime", "/etc/shadow"]
      excludedHomePaths :=
        #[ "/usr/local/homes/user"
         , "/lib/custom_home/bob"
         , "/home/" ++ "user" ] }
  let sWithPreset : MockSandboxState := { s₀ with preset := preset0 }
  let spec : BoxSpec :=
    { program := "env"
      mounts := #[.readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"] }
  let valid : ValidBoxSpec :=
    { program := "env"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp", .readOnly "/data/sub" "/work/sub", .readOnly "/data" "/work"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hVal : validateSpecPure spec = .ok valid := by
    dsimp only [spec, valid, validateSpecPure, hasNulChar, normalizeCleanAbsPath, parseCleanAbsSegs,
      splitSlashChars, splitSlashAux, validateMountsList, validateAndNormalizeMount,
      isReservedBoxSegs, reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair,
      dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
    rfl
  have hArchPreset : sWithPreset.hostSeccompArch? = some arch := hArchEq
  have hRun := runGeneric_mock_spawn_ok (s₀ := sWithPreset) hVal hB (fun _ => hM) (fun _ => hP) hArchPreset hSpFail
  have hEmpty : (compilePlan valid sWithPreset.preset).portForwards.isEmpty = true := rfl
  simp only [hEmpty, ↓reduceIte] at hRun
  have hPresetEq : sWithPreset.preset = preset0 := rfl
  rw [hPresetEq] at hRun
  dsimp only [Internal.mkApiM]
  erw [hRun]
  dsimp only
  simp only [assert]
  exact ⟨by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, trivial⟩

private theorem reach_seal_helper (s₀ : MockSandboxState)
    (hPre : s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
      s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
    (hFail : s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none) :
    CanReach (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan Internal.mkApiM) :=
  ⟨s₀, hPre, hFail, proof_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan s₀ hPre hFail⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan`. -/
theorem reach_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan :
    CanReach (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan Internal.mkApiM) :=
  reach_seal_helper {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩

end LeanSwe.ProcessSandbox.Proofs

import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

/-- When `s₀.hostSeccompArch? = none`, `Internal.runGeneric mockRawOps` fails closed with `.unavailable` after `preflight`. -/
theorem runGeneric_mock_host_arch_none {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec}
    (hVal : validateSpecPure spec = .ok valid)
    (hHost : s₀.hostBaseAvailable = true)
    (hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true)
    (hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true)
    (hNoArch : s₀.hostSeccompArch? = none) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    let err := Internal.ensureNonEmptyMsg "unsupported host architecture for seccomp"
      { kind := .unavailable, message := "unsupported host architecture for seccomp" }
    StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
      (.error { err with kind := .unavailable }, { s₀ with lastPreflightReq := some req }) := by
  intro req err
  have hPre : (mockRawOps.preflight req) s₀ =
      (.ok (), { s₀ with lastPreflightReq := some req }) := by
    dsimp only [mockRawOps]
    have hb : (!s₀.hostBaseAvailable) = false := by simp [hHost]
    have hm : (req.needMemoryCgroup && !s₀.memoryCgroupAvailable) = false := by
      cases hc : valid.limits.memoryMaxBytes.isSome
      · simp [req, hc]
      · simp [req, hc, hMem hc]
    have hp : (req.needPidsCgroup && !s₀.pidsCgroupAvailable) = false := by
      cases hc : valid.limits.pidsMax.isSome
      · simp [req, hc]
      · simp [req, hc, hPids hc]
    simp [hb, hm, hp]
  let sPref := { s₀ with lastPreflightReq := some req }
  have hArchOp : (mockRawOps.hostSeccompArch) sPref =
      (.error { kind := .unavailable, message := "unsupported host architecture for seccomp" }, sPref) := by
    dsimp only [mockRawOps, sPref]
    rw [hNoArch]
  dsimp only [StateT.run, Internal.runGeneric]
  rw [hVal]
  dsimp only
  rw [stateM_bind_apply, hPre]
  dsimp only
  rw [stateM_bind_apply, hArchOp]
  rfl

/-- Symbolic result of `Internal.runGeneric mockRawOps` when `spawnBox` fails and closes the sealed plan. -/
theorem runGeneric_mock_spawn_fail {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec} {arch : SeccompArch} {err : SandboxError}
    (hVal : validateSpecPure spec = .ok valid)
    (hHost : s₀.hostBaseAvailable = true)
    (hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true)
    (hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true)
    (hArch : s₀.hostSeccompArch? = some arch)
    (hFail : s₀.failSpawnWith = some err) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    let plan := compilePlan valid s₀.preset
    let seccompBytes := Internal.encodedSeccompFilter arch
    let idPlan := allocMockHandleId s₀
    let err' := Internal.ensureNonEmptyMsg "failed to spawn sandbox"
      { err with message := if err.message.isEmpty then "spawnBox failed" else err.message }
    StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
      (.error err',
       { s₀ with
         nextHandleId := idPlan + 1
         lastPreflightReq := some req
         lastSealedPlan := some plan
         lastSealedSeccompBytes := some seccompBytes
         spawnCalls := s₀.spawnCalls + 1 }) := by
  intro req plan seccompBytes idPlan err'
  have hPre : (mockRawOps.preflight req) s₀ =
      (.ok (), { s₀ with lastPreflightReq := some req }) := by
    dsimp only [mockRawOps]
    have hb : (!s₀.hostBaseAvailable) = false := by simp [hHost]
    have hm : (req.needMemoryCgroup && !s₀.memoryCgroupAvailable) = false := by
      cases hc : valid.limits.memoryMaxBytes.isSome
      · simp [req, hc]
      · simp [req, hc, hMem hc]
    have hp : (req.needPidsCgroup && !s₀.pidsCgroupAvailable) = false := by
      cases hc : valid.limits.pidsMax.isSome
      · simp [req, hc]
      · simp [req, hc, hPids hc]
    simp [hb, hm, hp]
  let sPref := { s₀ with lastPreflightReq := some req }
  have hArchOp : (mockRawOps.hostSeccompArch) sPref = (.ok arch, sPref) := by
    dsimp only [mockRawOps, sPref]
    rw [hArch]
  let sSeal :=
    { sPref with
      nextHandleId := idPlan + 1
      openPlans := idPlan :: s₀.openPlans
      lastSealedPlan := some plan
      lastSealedSeccompBytes := some seccompBytes }
  have hSecValid : isValidMockSeccompBytes seccompBytes = true :=
    isValidMockSeccompBytes_compiled arch
  have hSeal : (mockRawOps.sealPlan plan seccompBytes) sPref = (.ok { handleId := idPlan }, sSeal) := by
    dsimp only [mockRawOps]
    simp only [hSecValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hPhValid : isValidSandboxHandleId idPlan = true := isValidSandboxHandleId_alloc s₀
  have hPhMem : sSeal.openPlans.contains idPlan = true := by simp [sSeal]
  have hBadPlan : (!isValidSandboxHandleId idPlan || !sSeal.openPlans.contains idPlan) = false := by
    rw [hPhValid, hPhMem]; rfl
  have hSp : (mockRawOps.spawnBox { handleId := idPlan }) sSeal =
      (.error { err with message := if err.message.isEmpty then "spawnBox failed" else err.message },
       { sSeal with spawnCalls := s₀.spawnCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    simp [sSeal, sPref, hFail]
  have hClose : (mockRawOps.closePlan { handleId := idPlan }) { sSeal with spawnCalls := s₀.spawnCalls + 1 } =
      (.ok (), { s₀ with nextHandleId := idPlan + 1, lastPreflightReq := some req, lastSealedPlan := some plan, lastSealedSeccompBytes := some seccompBytes, spawnCalls := s₀.spawnCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    have hEr : sSeal.openPlans.erase idPlan = s₀.openPlans := by simp [sSeal, List.erase]
    simp only [sSeal, sPref, hEr]
  dsimp only [StateT.run, Internal.runGeneric]
  rw [hVal]
  dsimp only
  rw [stateM_bind_apply, hPre]
  dsimp only
  rw [stateM_bind_apply, hArchOp]
  dsimp only
  rw [stateM_bind_apply]
  change (match (mockRawOps.discoverHostPreset) sPref with | _ => _) = _
  have hDisc : (mockRawOps.discoverHostPreset) sPref = (.ok s₀.preset, sPref) := rfl
  rw [hDisc]
  dsimp only
  rw [stateM_bind_apply, hSeal]
  dsimp only
  rw [stateM_bind_apply, stateM_tryFinally'_apply, stateM_bind_apply, hSp]
  dsimp only [Pure.pure, StateT.pure]
  rw [stateM_bind_apply, hClose]
  rfl

/-- Proof of `test_psandbox_run_invalidSpec_hasZeroSideEffects` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_invalidSpec_hasZeroSideEffects :
    AllPass (test_psandbox_run_invalidSpec_hasZeroSideEffects Internal.mkApiM) := by
  intro s₀ spec
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  rcases except_cases (validateSpecPure spec) with ⟨e0, hVal⟩ | ⟨valid, hVal⟩
  · rw [hVal]
    dsimp only
    rw [runGeneric_mock_invalid hVal]
    dsimp only [assert]
    exact ⟨⟨⟨Internal.ensureNonEmptyMsg "invalid sandbox specification" e0, rfl,
      by rw [ensureNonEmptyMsg_kind]; exact validateSpecPure_error_kind hVal,
      ensureNonEmptyMsg_ne_empty "invalid sandbox specification" e0 (by decide)⟩, rfl⟩, trivial⟩
  · rw [hVal]
    simp [assume]

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_invalidSpec_hasZeroSideEffects`. -/
theorem reach_psandbox_run_invalidSpec_hasZeroSideEffects :
    CanReach (test_psandbox_run_invalidSpec_hasZeroSideEffects Internal.mkApiM) := by
  let spec : BoxSpec := { program := "" }
  have hVal : validateSpecPure spec =
      .error { kind := .invalidInput, message := "program must not be empty" } := rfl
  refine ⟨{}, spec, ?_⟩
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  rw [hVal]
  dsimp only
  rw [runGeneric_mock_invalid hVal]
  dsimp only [assert]
  exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl⟩, trivial⟩

/-- Proof of `test_psandbox_isAvailable_and_failClosedUnavailable` for `Internal.mkApiM`. -/
theorem proof_psandbox_isAvailable_and_failClosedUnavailable :
    AllPass (test_psandbox_isAvailable_and_failClosedUnavailable Internal.mkApiM) := by
  intro s₀
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  have hAvail :
      StateT.run (Internal.isAvailableGeneric mockRawOps) s₀ =
        (s₀.hostBaseAvailable && s₀.memoryCgroupAvailable && s₀.pidsCgroupAvailable,
         { s₀ with lastPreflightReq := some { needMemoryCgroup := true, needPidsCgroup := true } }) := by
    dsimp only [StateT.run, Internal.isAvailableGeneric]
    rw [stateM_bind_apply]
    dsimp only [mockRawOps]
    cases s₀.hostBaseAvailable <;> cases s₀.memoryCgroupAvailable <;> cases s₀.pidsCgroupAvailable <;>
      rfl
  rw [hAvail]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro sUnavail spec hSpecOk hCondUnavail
  rcases except_cases (validateSpecPure spec) with ⟨_, hVal⟩ | ⟨valid, hVal⟩
  · simp [hVal, Except.isOk, Except.toBool] at hSpecOk
  · have hLim := validateSpecPure_limits hVal
    have hFail : !sUnavail.hostBaseAvailable ∨
        (valid.limits.memoryMaxBytes.isSome && !sUnavail.memoryCgroupAvailable) ∨
        (valid.limits.pidsMax.isSome && !sUnavail.pidsCgroupAvailable) := by
      rw [hLim]
      exact hCondUnavail
    obtain ⟨e, hRunEq, hMsg⟩ := runGeneric_mock_preflight_err hVal hFail
    rw [hRunEq]
    dsimp only [assert]
    refine ⟨⟨⟨{ e with kind := .unavailable }, rfl, rfl, hMsg⟩, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro sSpawnUnavail specSpawn hSpawnOk ⟨hB, hM, hP⟩
    rcases except_cases (validateSpecPure specSpawn) with ⟨_, hValSp⟩ | ⟨validSp, hValSp⟩
    · simp [hValSp, Except.isOk, Except.toBool] at hSpawnOk
    · let sPreExecFail : MockSandboxState :=
        { sSpawnUnavail with
          failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
      by_cases hNone : sSpawnUnavail.hostSeccompArch? = none
      · have hArch : sPreExecFail.hostSeccompArch? = none := hNone
        have hNoArch := runGeneric_mock_host_arch_none (s₀ := sPreExecFail) hValSp hB (fun _ => hM) (fun _ => hP) hArch
        dsimp only [sPreExecFail] at hNoArch
        rw [hNoArch]
        dsimp only [assert]
        exact ⟨⟨⟨_, rfl, rfl, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩
      · rcases Option.ne_none_iff_exists'.mp hNone with ⟨arch, hArch0⟩
        have hArch : sPreExecFail.hostSeccompArch? = some arch := hArch0
        have hSp := runGeneric_mock_spawn_fail (s₀ := sPreExecFail) hValSp hB (fun _ => hM) (fun _ => hP) hArch rfl
        dsimp only [sPreExecFail] at hSp
        rw [hSp]
        dsimp only [assert]
        exact ⟨⟨⟨_, rfl, by decide, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_isAvailable_and_failClosedUnavailable`. -/
theorem reach_psandbox_isAvailable_and_failClosedUnavailable :
    CanReach (test_psandbox_isAvailable_and_failClosedUnavailable Internal.mkApiM) := by
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
  let sUnavail : MockSandboxState := { hostBaseAvailable := false }
  have hVal : validateSpecPure spec = .ok valid :=
    validateSpecPure_simple "/bin/true" ByteArray.empty 60_000 (some (16 * 1024 * 1024))
      (by decide) (by decide) (by decide)
  refine ⟨{}, ?_⟩
  dsimp only [Internal.mkApiM, Internal.validateSpec]
  have hAvail :
      StateT.run (Internal.isAvailableGeneric mockRawOps) ({} : MockSandboxState) =
        (true, { ({} : MockSandboxState) with lastPreflightReq := some { needMemoryCgroup := true, needPidsCgroup := true } }) :=
    rfl
  rw [hAvail]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, sUnavail, spec, ?_⟩
  refine ⟨by rw [hVal]; rfl, Or.inl rfl, ?_⟩
  obtain ⟨e, hRunEq, hMsg⟩ := runGeneric_mock_preflight_err (s₀ := sUnavail) hVal (Or.inl rfl)
  rw [hRunEq]
  dsimp only [assert]
  let sSpawnUnavail : MockSandboxState := { hostSeccompArch? := none }
  refine ⟨⟨⟨{ e with kind := .unavailable }, rfl, rfl, hMsg⟩, rfl, rfl, rfl, rfl, rfl⟩, sSpawnUnavail, spec, ?_⟩
  refine ⟨by rw [hVal]; rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
  let sPreExecFail : MockSandboxState :=
    { sSpawnUnavail with failSpawnWith := some { kind := .unavailable, message := "pre-execvp setup failed" } }
  have hNoArch := runGeneric_mock_host_arch_none (s₀ := sPreExecFail) hVal rfl (fun _ => rfl) (fun _ => rfl) rfl
  dsimp only [sPreExecFail, sSpawnUnavail] at hNoArch
  rw [hNoArch]
  dsimp only [assert]
  exact ⟨⟨⟨_, rfl, rfl, by decide⟩, rfl, rfl, rfl, rfl⟩, trivial⟩


end LeanSwe.ProcessSandbox.Proofs

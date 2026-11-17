import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers
import LeanSwe.ProcessSandbox.Proofs.ApiBracketHelpers
import LeanSwe.ProcessSandbox.Proofs.ApiProofs

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

/-- Full symbolic characterization of `Internal.runGeneric mockRawOps` when preflight, host arch query, and `spawnBox` succeed. -/
theorem runGeneric_mock_spawn_ok {s₀ : MockSandboxState} {spec : BoxSpec}
    {valid : ValidBoxSpec} {arch : SeccompArch}
    (hVal : validateSpecPure spec = .ok valid)
    (hHost : s₀.hostBaseAvailable = true)
    (hMem : valid.limits.memoryMaxBytes.isSome = true → s₀.memoryCgroupAvailable = true)
    (hPids : valid.limits.pidsMax.isSome = true → s₀.pidsCgroupAvailable = true)
    (hArch : s₀.hostSeccompArch? = some arch)
    (hNoFailSpawn : s₀.failSpawnWith = none) :
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    let plan := compilePlan valid s₀.preset
    let seccompBytes := Internal.encodedSeccompFilter arch
    let idPlan := allocMockHandleId s₀
    let sPref := { s₀ with lastPreflightReq := some req }
    let sSeal :=
      { sPref with
        nextHandleId := idPlan + 1
        openPlans := idPlan :: s₀.openPlans
        lastSealedPlan := some plan
        lastSealedSeccompBytes := some seccompBytes }
    let sSpawnPre := { sSeal with spawnCalls := s₀.spawnCalls + 1 }
    let idBox := allocMockHandleId sSpawnPre
    let sSpawn := { sSpawnPre with nextHandleId := idBox + 1, activeBoxes := idBox :: s₀.activeBoxes }
    if plan.portForwards.isEmpty then
      StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
        (match mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out,
         { s₀ with
           nextHandleId := idBox + 1
           lastPreflightReq := some req
           lastSealedPlan := some plan
           lastSealedSeccompBytes := some seccompBytes
           lastReadStdin := some valid.stdin
           lastReadTimeoutMs := some valid.limits.timeoutMs
           spawnCalls := s₀.spawnCalls + 1
           guestExecCalls := s₀.guestExecCalls + 1
           killPgCalls := s₀.killPgCalls + 1
           pidfdKillCalls := s₀.pidfdKillCalls + 1
           reapCalls := s₀.reapCalls + 1 })
    else
      match s₀.failForwarderStartWith with
      | some ferr =>
        let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
          { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
        StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
          (.error err',
           { s₀ with
             nextHandleId := idBox + 1
             lastPreflightReq := some req
             lastSealedPlan := some plan
             lastSealedSeccompBytes := some seccompBytes
             lastStartedForwards := some plan.portForwards
             spawnCalls := s₀.spawnCalls + 1
             killPgCalls := s₀.killPgCalls + 1
             pidfdKillCalls := s₀.pidfdKillCalls + 1
             reapCalls := s₀.reapCalls + 1 })
      | none =>
        let sStart := { sSpawn with lastStartedForwards := some plan.portForwards }
        let idFwd := allocMockHandleId sStart
        StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
          (match mockReadResult s₀.scriptedOutput valid.limits.maxOutputBytes with
           | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
           | .ok out => .ok out,
           { s₀ with
             nextHandleId := idFwd + 1
             lastPreflightReq := some req
             lastSealedPlan := some plan
             lastSealedSeccompBytes := some seccompBytes
             lastStartedForwards := some plan.portForwards
             lastReadStdin := some valid.stdin
             lastReadTimeoutMs := some valid.limits.timeoutMs
             spawnCalls := s₀.spawnCalls + 1
             guestExecCalls := s₀.guestExecCalls + 1
             killPgCalls := s₀.killPgCalls + 1
             pidfdKillCalls := s₀.pidfdKillCalls + 1
             reapCalls := s₀.reapCalls + 1 }) := by
  intro req plan seccompBytes idPlan sPref sSeal sSpawnPre idBox sSpawn
  have hPre : (mockRawOps.preflight req) s₀ = (.ok (), sPref) := by
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
    simp [hb, hm, hp, sPref]
  have hArchOp : (mockRawOps.hostSeccompArch) sPref = (.ok arch, sPref) := by
    dsimp only [mockRawOps, sPref]
    rw [hArch]
  have hDisc : (mockRawOps.discoverHostPreset) sPref = (.ok s₀.preset, sPref) := rfl
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
  have hBhValid : isValidSandboxHandleId idBox = true := isValidSandboxHandleId_alloc sSpawnPre
  let bh : BoxHandle := { handleId := idBox, pid := 200, pgid := 200, pidfd := 5 }
  have hSp : (mockRawOps.spawnBox { handleId := idPlan }) sSeal = (.ok bh, sSpawn) := by
    dsimp only [mockRawOps]
    simp only [hBadPlan, Bool.false_eq_true, ↓reduceIte]
    simp [sSeal, sPref, hNoFailSpawn, sSpawnPre, sSpawn, idBox, bh]
  have hPlanFwds : plan.portForwards = valid.portForwards := rfl
  have hSetup :
      StateT.run (Internal.runGeneric mockRawOps spec) s₀ =
        let (res, sOuter) :=
          let (boxRes, sBox) := mockBoxBracket bh valid sSpawn
          let (_, sClosed) := (mockRawOps.closePlan { handleId := idPlan }) sBox
          (boxRes, sClosed)
        (res, sOuter) := by
    dsimp only [StateT.run, Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [stateM_bind_apply, hPre]
    dsimp only
    rw [stateM_bind_apply, hArchOp]
    dsimp only
    rw [stateM_bind_apply, hDisc]
    dsimp only
    rw [stateM_bind_apply, hSeal]
    dsimp only
    rw [stateM_bind_apply, stateM_tryFinally'_apply, stateM_bind_apply, hSp]
    dsimp only [Pure.pure, StateT.pure]
    rw [stateM_bind_apply]
    rfl
  by_cases hEmpty : plan.portForwards.isEmpty = true
  · simp only [hEmpty, ↓reduceIte]
    have hEmptyV : valid.portForwards.isEmpty = true := hEmpty
    have hBox := mock_boxBracket_none bh valid s₀.activeBoxes sSpawn hBhValid rfl hEmptyV
    rw [hSetup, hBox]
    dsimp only
    have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
    have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
    have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
      rw [hPhValid, hOpenMem]; rfl
    dsimp only [mockRawOps]
    simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
    have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
    rw [hEr]
    rfl
  · have hEmptyF : plan.portForwards.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
    simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
    have hEmptyVF : valid.portForwards.isEmpty = false := hEmptyF
    have hBox := mock_boxBracket_fwd bh valid s₀.activeBoxes sSpawn hBhValid rfl hEmptyVF
    have hFailEq : sSpawn.failForwarderStartWith = s₀.failForwarderStartWith := rfl
    rw [hFailEq] at hBox
    cases hFwdFail : s₀.failForwarderStartWith with
    | some ferr =>
      simp only [hFwdFail] at hBox ⊢
      rw [hSetup, hBox]
      dsimp only
      have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
      have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
      have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
        rw [hPhValid, hOpenMem]; rfl
      dsimp only [mockRawOps]
      simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
      rw [hEr]
      rfl
    | none =>
      simp only [hFwdFail] at hBox ⊢
      rw [hSetup, hBox]
      dsimp only
      have hOpen : sSpawn.openPlans = idPlan :: s₀.openPlans := rfl
      have hOpenMem : sSpawn.openPlans.contains idPlan = true := by rw [hOpen]; simp
      have hBadC : (!isValidSandboxHandleId idPlan || !sSpawn.openPlans.contains idPlan) = false := by
        rw [hPhValid, hOpenMem]; rfl
      dsimp only [mockRawOps]
      simp only [hBadC, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn.openPlans.erase idPlan = s₀.openPlans := by rw [hOpen]; simp [List.erase]
      rw [hEr]
      rfl

end LeanSwe.ProcessSandbox.Proofs

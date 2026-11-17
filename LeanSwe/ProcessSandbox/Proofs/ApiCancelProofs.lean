import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.ApiProofs

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

private theorem exceptT_stateM_bind_ok {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β) (s : σ)
    {a : α} {s₁ : σ} (hx : x.run s = (.ok a, s₁)) :
    (x >>= f).run s = (f a).run s₁ := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, StateT.bind] at hx ⊢
  rw [hx]

private theorem exceptT_stateM_bind_err {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β) (s : σ)
    {e : ε} {s₁ : σ} (hx : x.run s = (.error e, s₁)) :
    (x >>= f).run s = (.error e, s₁) := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, StateT.bind] at hx ⊢
  rw [hx]
  dsimp only
  rfl

private theorem exceptT_stateM_tryFinally'_err {ε σ α β : Type}
    (x : ExceptT ε (StateM σ) α) (f : Option α → ExceptT ε (StateM σ) β) (s : σ)
    {e : ε} {b : β} {s₁ s₂ : σ}
    (hx : x.run s = (.error e, s₁))
    (hf : (f none).run s₁ = (.ok b, s₂)) :
    (tryFinally' x f).run s = (.error e, s₂) := by
  dsimp only [tryFinally', MonadFinally.tryFinally', ExceptT.mk, ExceptT.run,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure] at hx hf ⊢
  rw [hx]
  dsimp only
  rw [hf]
  rfl

private theorem runGeneric_mockEx_cancel_setup (sRun0 : MockSandboxState)
    {arch : SeccompArch}
    (hB : sRun0.hostBaseAvailable = true)
    (hM : sRun0.memoryCgroupAvailable = true)
    (hP : sRun0.pidsCgroupAvailable = true)
    (hArch : sRun0.hostSeccompArch? = some arch)
    (hSpFail : sRun0.failSpawnWith = none) :
    let valid : ValidBoxSpec :=
      { program := "/bin/sleep"
        args := #["60"]
        cwd := "/tmp"
        stdin := ByteArray.empty
        mounts := #[.scratch "/tmp"]
        allowBoxLocalhost := false
        portForwards := #[{ boxPort := 3000, hostPort := 13000 }]
        env := #[("PATH", "/usr/bin:/bin")]
        limits := {} }
    let req : PreflightReq := { needMemoryCgroup := true, needPidsCgroup := true }
    let plan := compilePlan valid sRun0.preset
    let seccompBytes := Internal.encodedSeccompFilter arch
    let idPlan := allocMockHandleId sRun0
    let sPref := { sRun0 with lastPreflightReq := some req }
    let sSeal :=
      { sPref with
        nextHandleId := idPlan + 1
        openPlans := idPlan :: sRun0.openPlans
        lastSealedPlan := some plan
        lastSealedSeccompBytes := some seccompBytes }
    let sSpawnPre := { sSeal with spawnCalls := sRun0.spawnCalls + 1 }
    let idBox := allocMockHandleId sSpawnPre
    let bh : BoxHandle := { handleId := idBox, pid := 200, pgid := 200, pidfd := 5 }
    let sSpawn := { sSpawnPre with nextHandleId := idBox + 1, activeBoxes := idBox :: sRun0.activeBoxes }
    (mockRawOpsEx.preflight req).run sRun0 = (.ok (.ok ()), sPref) ∧
    (mockRawOpsEx.hostSeccompArch).run sPref = (.ok (.ok arch), sPref) ∧
    (mockRawOpsEx.discoverHostPreset).run sPref = (.ok (.ok sRun0.preset), sPref) ∧
    (mockRawOpsEx.sealPlan plan seccompBytes).run sPref = (.ok (.ok { handleId := idPlan }), sSeal) ∧
    (mockRawOpsEx.spawnBox { handleId := idPlan }).run sSeal = (.ok (.ok bh), sSpawn) := by
  intro valid req plan seccompBytes idPlan sPref sSeal sSpawnPre idBox bh sSpawn
  have hPre : (mockRawOpsEx.preflight req).run sRun0 = (.ok (.ok ()), sPref) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
    simp [hB, hM, hP, sPref, req]
  have hArchOp : (mockRawOpsEx.hostSeccompArch).run sPref = (.ok (.ok arch), sPref) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run, sPref]
    rw [hArch]
  have hPres : (mockRawOpsEx.discoverHostPreset).run sPref = (.ok (.ok sRun0.preset), sPref) := rfl
  have hSecValid : isValidMockSeccompBytes seccompBytes = true :=
    isValidMockSeccompBytes_compiled arch
  have hSeal : (mockRawOpsEx.sealPlan plan seccompBytes).run sPref = (.ok (.ok { handleId := idPlan }), sSeal) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
    simp only [hSecValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hPhValid : isValidSandboxHandleId idPlan = true := isValidSandboxHandleId_alloc sRun0
  have hPhMem : sSeal.openPlans.contains idPlan = true := by simp [sSeal]
  have hBad : (!isValidSandboxHandleId idPlan || !sSeal.openPlans.contains idPlan) = false := by
    rw [hPhValid, hPhMem]; rfl
  have hSp : (mockRawOpsEx.spawnBox { handleId := idPlan }).run sSeal = (.ok (.ok bh), sSpawn) := by
    dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    dsimp only [sSeal, sPref, sSpawnPre, sSpawn, idBox, bh]
    rw [hSpFail]
  exact ⟨hPre, hArchOp, hPres, hSeal, hSp⟩

/-- Proof of `test_psandbox_run_monadFinallyCleansUpOnCancellation` for `Internal.mkApiM`. -/
theorem proof_psandbox_run_monadFinallyCleansUpOnCancellation :
    AllPass (test_psandbox_run_monadFinallyCleansUpOnCancellation Internal.mkApiM) := by
  intro s₀ ⟨hB, hM, hP, hArch⟩ ⟨hSpFail, hFwdFail⟩
  rcases Option.isSome_iff_exists.mp hArch with ⟨arch, hArchEq⟩
  let spec : BoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }] }
  let valid : ValidBoxSpec :=
    { program := "/bin/sleep"
      args := #["60"]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[{ boxPort := 3000, hostPort := 13000 }]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }
  have hVal : validateSpecPure spec = .ok valid := by
    dsimp only [spec, valid, validateSpecPure, hasNulChar, validateMountsList,
      allDistinct, isValidEnvPair, dedupEnvPairs, defaultSandboxPath, defaultSandboxCwd,
      mountBoxPath, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  let sRead0 : MockSandboxState := { s₀ with throwOnReadOutput := true, throwOnStartForwarders := false }
  have hArchRead0 : sRead0.hostSeccompArch? = some arch := hArchEq
  obtain ⟨hPre1, hArch1, hPres1, hSeal1, hSp1⟩ :=
    runGeneric_mockEx_cancel_setup sRead0 hB hM hP hArchRead0 hSpFail
  let req : PreflightReq := { needMemoryCgroup := true, needPidsCgroup := true }
  let plan := compilePlan valid s₀.preset
  let seccompBytes := Internal.encodedSeccompFilter arch
  let idPlan1 := allocMockHandleId sRead0
  let sPref1 := { sRead0 with lastPreflightReq := some req }
  let sSeal1 :=
    { sPref1 with
      nextHandleId := idPlan1 + 1
      openPlans := idPlan1 :: s₀.openPlans
      lastSealedPlan := some plan
      lastSealedSeccompBytes := some seccompBytes }
  let sSpawnPre1 := { sSeal1 with spawnCalls := s₀.spawnCalls + 1 }
  let idBox1 := allocMockHandleId sSpawnPre1
  let bh1 : BoxHandle := { handleId := idBox1, pid := 200, pgid := 200, pidfd := 5 }
  let sSpawn1 := { sSpawnPre1 with nextHandleId := idBox1 + 1, activeBoxes := idBox1 :: s₀.activeBoxes }
  have hPhValid1 : isValidSandboxHandleId idPlan1 = true := isValidSandboxHandleId_alloc sRead0
  have hBhValid1 : isValidSandboxHandleId idBox1 = true := isValidSandboxHandleId_alloc sSpawnPre1
  have hBhActive1 : sSpawn1.activeBoxes.contains idBox1 = true := by simp [sSpawn1]
  let sStart1 := { sSpawn1 with lastStartedForwards := some plan.portForwards }
  let idFwd1 := allocMockHandleId sStart1
  let fh1 : PortForwarderHandle := { handleId := idFwd1, boxHandleId := idBox1 }
  let sFwd1 := { sStart1 with nextHandleId := idFwd1 + 1, activeForwarders := (idFwd1, idBox1) :: s₀.activeForwarders }
  have hFhValid1 : isValidSandboxHandleId idFwd1 = true := isValidSandboxHandleId_alloc sStart1
  have hStart1 : (mockRawOpsEx.startPortForwarders bh1 plan.portForwards).run sSpawn1 = (.ok (.ok fh1), sFwd1) := by
    dsimp only [mockRawOpsEx, mockRawOps, ExceptT.mk, ExceptT.run]
    have hThrow : sSpawn1.throwOnStartForwarders = false := rfl
    simp only [hThrow, Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.run]
    have hBhId : bh1.handleId = idBox1 := rfl
    have hBad : (!isValidSandboxHandleId bh1.handleId || !sSpawn1.activeBoxes.contains bh1.handleId) = false := by
      rw [hBhId, hBhValid1, hBhActive1]; rfl
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hFailNone : sSpawn1.failForwarderStartWith = none := hFwdFail
    dsimp only [sStart1, idFwd1, fh1, sFwd1]
    rw [hFailNone]
  let sReadErr1 :=
    { sFwd1 with
      guestExecCalls := s₀.guestExecCalls + 1
      lastReadStdin := some valid.stdin
      lastReadTimeoutMs := some valid.limits.timeoutMs }
  have hRead1 : (mockRawOpsEx.readBoxOutput bh1 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes).run sFwd1 =
      (.error "cancelled-during-read", sReadErr1) := rfl
  let sStop1 := { sReadErr1 with activeForwarders := s₀.activeForwarders }
  let ioFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ =>
      match some fh1 with
      | some fh => do
        let _ ← mockRawOpsEx.stopPortForwarders fh
        pure ()
      | none => pure ()
  have hStop1 : (ioFin1 none).run sReadErr1 = (.ok (), sStop1) := by
    have hS : (mockRawOpsEx.stopPortForwarders fh1).run sReadErr1 = (.ok (.ok ()), sStop1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hAny : sReadErr1.activeForwarders.any (fun p => p.1 == fh1.handleId) = true := by
        simp [sReadErr1, sFwd1, fh1]
      have hFhId : fh1.handleId = idFwd1 := rfl
      have hBad : (!isValidSandboxHandleId fh1.handleId ||
          !sReadErr1.activeForwarders.any (fun p => p.1 == fh1.handleId)) = false := by
        rw [hAny, hFhId, hFhValid1]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : eraseFirstForwarder fh1.handleId sReadErr1.activeForwarders = s₀.activeForwarders := by
        simp [sReadErr1, sFwd1, fh1, eraseFirstForwarder]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hS
  have hIoTry1 := exceptT_stateM_tryFinally'_err _ ioFin1 _ hRead1 hStop1
  let sKillReap1 :=
    { sStop1 with
      activeBoxes := s₀.activeBoxes
      killPgCalls := s₀.killPgCalls + 1
      pidfdKillCalls := s₀.pidfdKillCalls + 1
      reapCalls := s₀.reapCalls + 1 }
  let boxFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.killProcessGroup bh1
      let _ ← mockRawOpsEx.pidfdKill bh1
      let _ ← mockRawOpsEx.reapBox bh1
      pure ()
  have hBoxFin1 : (boxFin1 none).run sStop1 = (.ok (), sKillReap1) := by
    have hMem : sStop1.activeBoxes.contains bh1.handleId = true := by
      simp [sStop1, sReadErr1, sFwd1, sStart1, sSpawn1, bh1]
    have hBhId : bh1.handleId = idBox1 := rfl
    have hBad : (!isValidSandboxHandleId bh1.handleId || !sStop1.activeBoxes.contains bh1.handleId) = false := by
      rw [hMem, hBhId, hBhValid1]; rfl
    have hK : (mockRawOpsEx.killProcessGroup bh1).run sStop1 =
        (.ok (.ok ()), { sStop1 with killPgCalls := s₀.killPgCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hP : (mockRawOpsEx.pidfdKill bh1).run { sStop1 with killPgCalls := s₀.killPgCalls + 1 } =
        (.ok (.ok ()), { sStop1 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hR : (mockRawOpsEx.reapBox bh1).run
        { sStop1 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 } =
        (.ok (.ok ()), sKillReap1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sStop1.activeBoxes.erase bh1.handleId = s₀.activeBoxes := by
        simp [sStop1, sReadErr1, sFwd1, sStart1, sSpawn1, bh1, List.erase]
      rw [hEr]
    dsimp only [boxFin1]
    rw [exceptT_stateM_bind_ok _ _ _ hK, exceptT_stateM_bind_ok _ _ _ hP,
      exceptT_stateM_bind_ok _ _ _ hR]
    rfl
  let sClose1 := { sKillReap1 with openPlans := s₀.openPlans }
  let planFin1 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.closePlan { handleId := idPlan1 }
      pure ()
  have hPlanFin1 : (planFin1 none).run sKillReap1 = (.ok (), sClose1) := by
    have hC : (mockRawOpsEx.closePlan { handleId := idPlan1 }).run sKillReap1 = (.ok (.ok ()), sClose1) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hOpen : sKillReap1.openPlans = idPlan1 :: s₀.openPlans := rfl
      have hMem : sKillReap1.openPlans.contains idPlan1 = true := by rw [hOpen]; simp
      have hBad : (!isValidSandboxHandleId idPlan1 || !sKillReap1.openPlans.contains idPlan1) = false := by
        rw [hPhValid1, hMem]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sKillReap1.openPlans.erase idPlan1 = s₀.openPlans := by
        rw [hOpen]; simp [List.erase]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hC
  have hPre1' : (mockRawOpsEx.preflight
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }).run sRead0 =
      (.ok (.ok ()), sPref1) := hPre1
  have hArch1' : (mockRawOpsEx.hostSeccompArch).run sPref1 = (.ok (.ok arch), sPref1) := hArch1
  have hPres1' : (mockRawOpsEx.discoverHostPreset).run sPref1 =
      (.ok (.ok s₀.preset), sPref1) := hPres1
  have hSeal1' : (mockRawOpsEx.sealPlan (compilePlan valid s₀.preset) seccompBytes).run sPref1 =
      (.ok (.ok { handleId := idPlan1 }), sSeal1) := hSeal1
  have hSp1' : (mockRawOpsEx.spawnBox { handleId := idPlan1 }).run sSeal1 =
      (.ok (.ok bh1), sSpawn1) := hSp1
  have hRunReadCancel :
      (Internal.runGeneric mockRawOpsEx spec).run sRead0 = (.error "cancelled-during-read", sClose1) := by
    dsimp only [Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPre1']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hArch1']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPres1']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hSeal1']
    dsimp only
    have hOuterErr :
        ((do
          match ← mockRawOpsEx.spawnBox { handleId := idPlan1 } with
          | .error e => return Except.error (Internal.ensureNonEmptyMsg "failed to spawn sandbox" e)
          | .ok bh =>
            let (boxRes, _) ← tryFinally' (do
              let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                if plan.portForwards.isEmpty then
                  pure (.ok none)
                else do
                  match ← mockRawOpsEx.startPortForwarders bh plan.portForwards with
                  | .error e =>
                    pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                  | .ok fh =>
                    pure (.ok (some fh))
              match fwdRes with
              | .error e => return Except.error e
              | .ok fwdOpt =>
                let (ioRes, _) ← tryFinally'
                  (mockRawOpsEx.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                  (fun _ =>
                    match fwdOpt with
                    | some fh => do
                      let _ ← mockRawOpsEx.stopPortForwarders fh
                      pure ()
                    | none => pure ())
                match ioRes with
                | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
                | .ok out => return Except.ok out
            ) (fun _ => do
              let _ ← mockRawOpsEx.killProcessGroup bh
              let _ ← mockRawOpsEx.pidfdKill bh
              let _ ← mockRawOpsEx.reapBox bh
              pure ())
            return boxRes) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSeal1 =
          (.error "cancelled-during-read", sKillReap1) := by
      rw [exceptT_stateM_bind_ok _ _ _ hSp1']
      dsimp only
      have hMidErr :
          ((do
            let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
              if plan.portForwards.isEmpty then
                pure (.ok none)
              else do
                match ← mockRawOpsEx.startPortForwarders bh1 plan.portForwards with
                | .error e =>
                  pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                | .ok fh =>
                  pure (.ok (some fh))
            match fwdRes with
            | .error e => return Except.error e
            | .ok fwdOpt =>
              let (ioRes, _) ← tryFinally'
                (mockRawOpsEx.readBoxOutput bh1 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                (fun _ =>
                  match fwdOpt with
                  | some fh => do
                    let _ ← mockRawOpsEx.stopPortForwarders fh
                    pure ()
                  | none => pure ())
              match ioRes with
              | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
              | .ok out => return Except.ok out) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSpawn1 =
            (.error "cancelled-during-read", sStop1) := by
        have hNotEmp : plan.portForwards.isEmpty = false := rfl
        simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte]
        rw [exceptT_stateM_bind_ok _ _ _ hStart1]
        dsimp only
        rw [exceptT_stateM_bind_ok (x := pure (Except.ok (some fh1))) _ _ rfl]
        dsimp only
        exact exceptT_stateM_bind_err _ _ _ hIoTry1
      have hMidTry := exceptT_stateM_tryFinally'_err _ boxFin1 _ hMidErr hBoxFin1
      exact exceptT_stateM_bind_err _ _ _ hMidTry
    dsimp only [plan] at hOuterErr
    have hOuterTry := exceptT_stateM_tryFinally'_err _ planFin1 _ hOuterErr hPlanFin1
    exact exceptT_stateM_bind_err _ _ _ hOuterTry
  let sFwd0 : MockSandboxState := { s₀ with throwOnReadOutput := false, throwOnStartForwarders := true }
  have hArchFwd0 : sFwd0.hostSeccompArch? = some arch := hArchEq
  obtain ⟨hPre2, hArch2, hPres2, hSeal2, hSp2⟩ :=
    runGeneric_mockEx_cancel_setup sFwd0 hB hM hP hArchFwd0 hSpFail
  let idPlan2 := allocMockHandleId sFwd0
  let sPref2 := { sFwd0 with lastPreflightReq := some req }
  let sSeal2 :=
    { sPref2 with
      nextHandleId := idPlan2 + 1
      openPlans := idPlan2 :: s₀.openPlans
      lastSealedPlan := some plan
      lastSealedSeccompBytes := some seccompBytes }
  let sSpawnPre2 := { sSeal2 with spawnCalls := s₀.spawnCalls + 1 }
  let idBox2 := allocMockHandleId sSpawnPre2
  let bh2 : BoxHandle := { handleId := idBox2, pid := 200, pgid := 200, pidfd := 5 }
  let sSpawn2 := { sSpawnPre2 with nextHandleId := idBox2 + 1, activeBoxes := idBox2 :: s₀.activeBoxes }
  have hPhValid2 : isValidSandboxHandleId idPlan2 = true := isValidSandboxHandleId_alloc sFwd0
  have hBhValid2 : isValidSandboxHandleId idBox2 = true := isValidSandboxHandleId_alloc sSpawnPre2
  have hStartErr2 : (mockRawOpsEx.startPortForwarders bh2 plan.portForwards).run sSpawn2 =
      (.error "cancelled-during-forwarder-start", sSpawn2) := rfl
  let sKillReap2 :=
    { sSpawn2 with
      activeBoxes := s₀.activeBoxes
      killPgCalls := s₀.killPgCalls + 1
      pidfdKillCalls := s₀.pidfdKillCalls + 1
      reapCalls := s₀.reapCalls + 1 }
  let boxFin2 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.killProcessGroup bh2
      let _ ← mockRawOpsEx.pidfdKill bh2
      let _ ← mockRawOpsEx.reapBox bh2
      pure ()
  have hBoxFin2 : (boxFin2 none).run sSpawn2 = (.ok (), sKillReap2) := by
    have hMem : sSpawn2.activeBoxes.contains bh2.handleId = true := by simp [sSpawn2, bh2]
    have hBhId : bh2.handleId = idBox2 := rfl
    have hBad : (!isValidSandboxHandleId bh2.handleId || !sSpawn2.activeBoxes.contains bh2.handleId) = false := by
      rw [hMem, hBhId, hBhValid2]; rfl
    have hK : (mockRawOpsEx.killProcessGroup bh2).run sSpawn2 =
        (.ok (.ok ()), { sSpawn2 with killPgCalls := s₀.killPgCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hP : (mockRawOpsEx.pidfdKill bh2).run { sSpawn2 with killPgCalls := s₀.killPgCalls + 1 } =
        (.ok (.ok ()), { sSpawn2 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 }) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]; rfl
    have hR : (mockRawOpsEx.reapBox bh2).run
        { sSpawn2 with killPgCalls := s₀.killPgCalls + 1, pidfdKillCalls := s₀.pidfdKillCalls + 1 } =
        (.ok (.ok ()), sKillReap2) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sSpawn2.activeBoxes.erase bh2.handleId = s₀.activeBoxes := by
        simp [sSpawn2, bh2, List.erase]
      rw [hEr]
    dsimp only [boxFin2]
    rw [exceptT_stateM_bind_ok _ _ _ hK, exceptT_stateM_bind_ok _ _ _ hP,
      exceptT_stateM_bind_ok _ _ _ hR]
    rfl
  let sClose2 := { sKillReap2 with openPlans := s₀.openPlans }
  let planFin2 : Option (Except SandboxError SandboxResult) → ExceptT String (StateM MockSandboxState) Unit :=
    fun _ => do
      let _ ← mockRawOpsEx.closePlan { handleId := idPlan2 }
      pure ()
  have hPlanFin2 : (planFin2 none).run sKillReap2 = (.ok (), sClose2) := by
    have hC : (mockRawOpsEx.closePlan { handleId := idPlan2 }).run sKillReap2 = (.ok (.ok ()), sClose2) := by
      dsimp only [mockRawOpsEx, liftMockState, mockRawOps, ExceptT.mk, ExceptT.run]
      have hOpen : sKillReap2.openPlans = idPlan2 :: s₀.openPlans := rfl
      have hMem : sKillReap2.openPlans.contains idPlan2 = true := by rw [hOpen]; simp
      have hBad : (!isValidSandboxHandleId idPlan2 || !sKillReap2.openPlans.contains idPlan2) = false := by
        rw [hPhValid2, hMem]; rfl
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      have hEr : sKillReap2.openPlans.erase idPlan2 = s₀.openPlans := by
        rw [hOpen]; simp [List.erase]
      rw [hEr]
    exact exceptT_stateM_bind_ok _ _ _ hC
  have hPre2' : (mockRawOpsEx.preflight
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }).run sFwd0 =
      (.ok (.ok ()), sPref2) := hPre2
  have hArch2' : (mockRawOpsEx.hostSeccompArch).run sPref2 = (.ok (.ok arch), sPref2) := hArch2
  have hPres2' : (mockRawOpsEx.discoverHostPreset).run sPref2 =
      (.ok (.ok s₀.preset), sPref2) := hPres2
  have hSeal2' : (mockRawOpsEx.sealPlan (compilePlan valid s₀.preset) seccompBytes).run sPref2 =
      (.ok (.ok { handleId := idPlan2 }), sSeal2) := hSeal2
  have hSp2' : (mockRawOpsEx.spawnBox { handleId := idPlan2 }).run sSeal2 =
      (.ok (.ok bh2), sSpawn2) := hSp2
  have hRunFwdCancel :
      (Internal.runGeneric mockRawOpsEx spec).run sFwd0 = (.error "cancelled-during-forwarder-start", sClose2) := by
    dsimp only [Internal.runGeneric]
    rw [hVal]
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPre2']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hArch2']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hPres2']
    dsimp only
    rw [exceptT_stateM_bind_ok _ _ _ hSeal2']
    dsimp only
    have hOuterErr :
        ((do
          match ← mockRawOpsEx.spawnBox { handleId := idPlan2 } with
          | .error e => return Except.error (Internal.ensureNonEmptyMsg "failed to spawn sandbox" e)
          | .ok bh =>
            let (boxRes, _) ← tryFinally' (do
              let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                if plan.portForwards.isEmpty then
                  pure (.ok none)
                else do
                  match ← mockRawOpsEx.startPortForwarders bh plan.portForwards with
                  | .error e =>
                    pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                  | .ok fh =>
                    pure (.ok (some fh))
              match fwdRes with
              | .error e => return Except.error e
              | .ok fwdOpt =>
                let (ioRes, _) ← tryFinally'
                  (mockRawOpsEx.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                  (fun _ =>
                    match fwdOpt with
                    | some fh => do
                      let _ ← mockRawOpsEx.stopPortForwarders fh
                      pure ()
                    | none => pure ())
                match ioRes with
                | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
                | .ok out => return Except.ok out
            ) (fun _ => do
              let _ ← mockRawOpsEx.killProcessGroup bh
              let _ ← mockRawOpsEx.pidfdKill bh
              let _ ← mockRawOpsEx.reapBox bh
              pure ())
            return boxRes) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSeal2 =
          (.error "cancelled-during-forwarder-start", sKillReap2) := by
      rw [exceptT_stateM_bind_ok _ _ _ hSp2']
      dsimp only
      have hMidErr :
          ((do
            let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
              if plan.portForwards.isEmpty then
                pure (.ok none)
              else do
                match ← mockRawOpsEx.startPortForwarders bh2 plan.portForwards with
                | .error e =>
                  pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
                | .ok fh =>
                  pure (.ok (some fh))
            match fwdRes with
            | .error e => return Except.error e
            | .ok fwdOpt =>
              let (ioRes, _) ← tryFinally'
                (mockRawOpsEx.readBoxOutput bh2 valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                (fun _ =>
                  match fwdOpt with
                  | some fh => do
                    let _ ← mockRawOpsEx.stopPortForwarders fh
                    pure ()
                  | none => pure ())
              match ioRes with
              | .error e => return Except.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
              | .ok out => return Except.ok out) : ExceptT String (StateM MockSandboxState) (Except SandboxError SandboxResult)).run sSpawn2 =
            (.error "cancelled-during-forwarder-start", sSpawn2) := by
        have hNotEmp : plan.portForwards.isEmpty = false := rfl
        simp only [hNotEmp, Bool.false_eq_true, ↓reduceIte]
        exact exceptT_stateM_bind_err _ _ _ hStartErr2
      have hMidTry := exceptT_stateM_tryFinally'_err _ boxFin2 _ hMidErr hBoxFin2
      exact exceptT_stateM_bind_err _ _ _ hMidTry
    dsimp only [plan] at hOuterErr
    have hOuterTry := exceptT_stateM_tryFinally'_err _ planFin2 _ hOuterErr hPlanFin2
    exact exceptT_stateM_bind_err _ _ _ hOuterTry
  dsimp only [Internal.mkApiM]
  dsimp only [spec, sRead0] at hRunReadCancel
  dsimp only [spec, sFwd0] at hRunFwdCancel
  rw [hRunReadCancel]
  dsimp only [assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [hRunFwdCancel]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private theorem reach_cancel_helper (s₀ : MockSandboxState)
    (hPre : s₀.hostBaseAvailable = true ∧ s₀.memoryCgroupAvailable = true ∧
      s₀.pidsCgroupAvailable = true ∧ s₀.hostSeccompArch?.isSome = true)
    (hFail : s₀.failSpawnWith = none ∧ s₀.failForwarderStartWith = none) :
    CanReach (test_psandbox_run_monadFinallyCleansUpOnCancellation Internal.mkApiM) :=
  ⟨s₀, hPre, hFail, proof_psandbox_run_monadFinallyCleansUpOnCancellation s₀ hPre hFail⟩

/-- Non-vacuity `CanReach` witness for `test_psandbox_run_monadFinallyCleansUpOnCancellation`. -/
theorem reach_psandbox_run_monadFinallyCleansUpOnCancellation :
    CanReach (test_psandbox_run_monadFinallyCleansUpOnCancellation Internal.mkApiM) :=
  reach_cancel_helper {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩

end LeanSwe.ProcessSandbox.Proofs

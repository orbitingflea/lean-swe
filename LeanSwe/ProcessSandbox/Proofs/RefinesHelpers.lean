import Core.Obeys
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Model.Refines
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Raw.Model

/-- Definitional unfolding of `StateM` bind. -/
theorem stateM_bind_run {W α β : Type} (m : StateM W α) (f : α → StateM W β) (w : W) :
    (m >>= f).run w = (f (m.run w).1).run (m.run w).2 := rfl

/-- Definitional unfolding of `StateM` pure. -/
theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

/-- Definitional unfolding of `StateM` map. -/
theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

/-- Definitional unfolding of `StateM` `tryFinally'`. -/
theorem stateM_tryFinally'_run {W α β : Type} (m : StateM W α)
    (f : Option α → StateM W β) (w : W) :
    (tryFinally' m f).run w =
      let r1 := m.run w
      let r2 := (f (some r1.1)).run r1.2
      ((r1.1, r2.1), r2.2) := rfl

/-- `raw.closePlan` preserves world well-formedness, `boxes`, `fwds`, and does not grow `plans`. -/
theorem step_closePlan {W : Type} (proj : W → RawHostWorld)
    (raw : RawProcessSandboxOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (ph : PlanHandle) (w : W) (hw : rawHostWorldWf (proj w) = true) :
    let w' := (raw.closePlan ph).run w |>.2
    rawHostWorldWf (proj w') = true ∧
    (proj w').isLinux = (proj w).isLinux ∧
    (proj w').target = (proj w).target ∧
    (proj w').table.boxes = (proj w).table.boxes ∧
    (proj w').table.fwds = (proj w).table.fwds ∧
    (proj w').table.plans.length ≤ (proj w).table.plans.length := by
  have h := hRaw w (.closePlan ph) hw
  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
    stateM_map_run] at h
  rcases h with ⟨hw', hLin, hTgt, hBox, hFwd, hRes⟩
  refine ⟨hw', hLin, hTgt, hBox, hFwd, ?_⟩
  cases hC : ((raw.closePlan ph).run w).1 with
  | ok _ =>
    rw [hC] at hRes
    omega
  | error _ =>
    rw [hC] at hRes
    rw [hRes.2.2.2]
    exact Nat.le_refl _

/-- `raw.stopPortForwarders` preserves world well-formedness, `plans`, `boxes`, and does not grow `fwds`. -/
theorem step_stopPortForwarders {W : Type} (proj : W → RawHostWorld)
    (raw : RawProcessSandboxOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (fh : PortForwarderHandle) (w : W) (hw : rawHostWorldWf (proj w) = true) :
    let w' := (raw.stopPortForwarders fh).run w |>.2
    rawHostWorldWf (proj w') = true ∧
    (proj w').isLinux = (proj w).isLinux ∧
    (proj w').target = (proj w).target ∧
    (proj w').table.plans = (proj w).table.plans ∧
    (proj w').table.boxes = (proj w).table.boxes ∧
    (proj w').table.fwds.length ≤ (proj w).table.fwds.length := by
  have h := hRaw w (.stopPortForwarders fh) hw
  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
    stateM_map_run] at h
  rcases h with ⟨hw', hLin, hTgt, hPl, hBox, hRes⟩
  refine ⟨hw', hLin, hTgt, hPl, hBox, ?_⟩
  cases hS : ((raw.stopPortForwarders fh).run w).1 with
  | ok _ =>
    rw [hS] at hRes
    omega
  | error _ =>
    rw [hS] at hRes
    rw [hRes.2.2.2]
    exact Nat.le_refl _

/-- Box teardown (`killProcessGroup`; `pidfdKill`; `reapBox`) preserves `plans`, `fwds`, and does not grow `boxes`. -/
theorem step_boxCleanup {W : Type} (proj : W → RawHostWorld)
    (raw : RawProcessSandboxOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (bh : BoxHandle) (w : W) (hw : rawHostWorldWf (proj w) = true) :
    let w' := (do
      let _ ← raw.killProcessGroup bh
      let _ ← raw.pidfdKill bh
      let _ ← raw.reapBox bh
      pure ()).run w |>.2
    rawHostWorldWf (proj w') = true ∧
    (proj w').isLinux = (proj w).isLinux ∧
    (proj w').target = (proj w).target ∧
    (proj w').table.plans = (proj w).table.plans ∧
    (proj w').table.fwds = (proj w).table.fwds ∧
    (proj w').table.boxes.length ≤ (proj w).table.boxes.length := by
  have hK := hRaw w (.killProcessGroup bh) hw
  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
    stateM_map_run] at hK
  rcases hK with ⟨hw1, _, _, hEq1, _⟩
  let w1 := ((raw.killProcessGroup bh).run w).2
  have hP := hRaw w1 (.pidfdKill bh) hw1
  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
    stateM_map_run] at hP
  rcases hP with ⟨hw2, _, _, hEq2, _⟩
  let w2 := ((raw.pidfdKill bh).run w1).2
  have hR := hRaw w2 (.reapBox bh) hw2
  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
    stateM_map_run] at hR
  rcases hR with ⟨hw3, hLin3, hTgt3, hPl3, hFwd3, hRes3⟩
  have hEq20 : proj w2 = proj w := hEq2.trans hEq1
  have hW' :
      ((do
        let _ ← raw.killProcessGroup bh
        let _ ← raw.pidfdKill bh
        let _ ← raw.reapBox bh
        pure ()).run w).2 = ((raw.reapBox bh).run w2).2 := rfl
  dsimp only
  rw [hW']
  refine ⟨hw3, (by rw [hLin3, hEq20]), (by rw [hTgt3, hEq20]),
    (by rw [hPl3, hEq20]), (by rw [hFwd3, hEq20]), ?_⟩
  cases hRR : ((raw.reapBox bh).run w2).1 with
  | ok _ =>
    rw [hRR] at hRes3
    rw [← hEq20]
    omega
  | error _ =>
    rw [hRR] at hRes3
    rw [← hEq20]
    cases hCond : (isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId (proj w2).table.boxes)
    · rw [hCond] at hRes3
      simp only [Bool.false_eq_true, ↓reduceIte] at hRes3
      rw [hRes3.2.2]
      exact Nat.le_refl _
    · rw [hCond] at hRes3
      simp only [↓reduceIte] at hRes3
      omega

/-- Post-`spawnBox` bracket step lemma for `Internal.runGeneric` over any `allowedRawStep`-obeying `raw`. -/
theorem runGeneric_after_spawn_ok {W : Type} (proj : W → RawHostWorld)
    (raw : RawProcessSandboxOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep)
    (valid : ValidBoxSpec) (preset : HostRuntimePreset)
    (s0 : RawHostWorld) (bh : BoxHandle) (w5 : W)
    (hw5 : rawHostWorldWf (proj w5) = true)
    (hLin0 : s0.isLinux = true)
    (hArch0 : (decodeHostAuditArch (detectHostAuditArch s0.isLinux s0.target)).isOk = true)
    (hLin5 : (proj w5).isLinux = s0.isLinux)
    (hTgt5 : (proj w5).target = s0.target)
    (hPl5 : (proj w5).table.plans.length = s0.table.plans.length + 1)
    (hBox5 : (proj w5).table.boxes.length = s0.table.boxes.length + 1)
    (hFwd5 : (proj w5).table.fwds = s0.table.fwds) :
    let plan := compilePlan valid preset
    let act : StateM W (Except SandboxError SandboxResult) := do
      let (boxRes, _) ← tryFinally' (do
        let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
          if plan.portForwards.isEmpty then
            pure (.ok none)
          else do
            match ← raw.startPortForwarders bh plan.portForwards with
            | .error e =>
              pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
            | .ok fh =>
              pure (.ok (some fh))
        match fwdRes with
        | .error e => return .error e
        | .ok fwdOpt =>
          let (ioRes, _) ← tryFinally'
            (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
            (fun _ =>
              match fwdOpt with
              | some fh => do
                let _ ← raw.stopPortForwarders fh
                pure ()
              | none => pure ())
          match ioRes with
          | .error e =>
            return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
          | .ok out =>
            return .ok out
      ) (fun _ => do
        let _ ← raw.killProcessGroup bh
        let _ ← raw.pidfdKill bh
        let _ ← raw.reapBox bh
        pure ())
      return boxRes
    let r := act.run w5
    rawHostWorldWf (proj r.2) = true ∧
    (proj r.2).isLinux = s0.isLinux ∧
    (proj r.2).target = s0.target ∧
    (proj r.2).table.plans.length = s0.table.plans.length + 1 ∧
    (proj r.2).table.boxes.length ≤ s0.table.boxes.length + 1 ∧
    (proj r.2).table.fwds.length ≤ s0.table.fwds.length + 1 ∧
    (valid.portForwards.isEmpty = true → (proj r.2).table.fwds = s0.table.fwds) ∧
    match r.1 with
    | .ok boxRes =>
      s0.isLinux = true ∧
      (decodeHostAuditArch (detectHostAuditArch s0.isLinux s0.target)).isOk = true ∧
      outcomeNonNeg boxRes.outcome ∧
      (∀ m, valid.limits.maxOutputBytes = some m → boxRes.stdout.size + boxRes.stderr.size ≤ m)
    | .error err =>
      err.message ≠ "" ∧
      (s0.isLinux = false → err.kind = .unavailable ∧ tableCounts (proj r.2).table = tableCounts s0.table) ∧
      ((decodeHostAuditArch (detectHostAuditArch s0.isLinux s0.target)).isOk = false →
        err.kind = .unavailable ∧ tableCounts (proj r.2).table = tableCounts s0.table) := by
  intro plan act
  have hPlanFwds : plan.portForwards = valid.portForwards := rfl
  cases hEmp : valid.portForwards.isEmpty
  · have hEmpP : plan.portForwards.isEmpty = false := by rw [hPlanFwds, hEmp]
    have hSf := hRaw w5 (.startPortForwarders bh plan.portForwards) hw5
    dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
      stateM_map_run] at hSf
    rcases hSf with ⟨hw6, hLin6, hTgt6, hPl6, hBox6, hSfRes⟩
    cases hSfPair : (raw.startPortForwarders bh plan.portForwards).run w5 with
    | mk sfRes w6 =>
      rw [hSfPair] at hw6 hLin6 hTgt6 hPl6 hBox6 hSfRes
      dsimp only at hw6 hLin6 hTgt6 hPl6 hBox6 hSfRes
      cases sfRes with
      | error e =>
        rcases hSfRes with ⟨_, hFwd6, _⟩
        have hClean := step_boxCleanup proj raw hRaw bh w6 hw6
        rcases hClean with ⟨hwC, hLinC, hTgtC, hPlC, hFwdC, hBoxC⟩
        have hActEq :
            act.run w5 =
              (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e),
               ((do
                 let _ ← raw.killProcessGroup bh
                 let _ ← raw.pidfdKill bh
                 let _ ← raw.reapBox bh
                 pure ()).run w6).2) := by
          dsimp only [act]
          rw [stateM_bind_run, stateM_tryFinally'_run]
          simp only [hEmpP, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run, hSfPair]
        rw [hActEq]
        dsimp only
        refine ⟨hwC, hLinC.trans (hLin6.trans hLin5), hTgtC.trans (hTgt6.trans hTgt5),
          (by rw [hPlC, hPl6, hPl5]),
          (by omega),
          (by rw [hFwdC, hFwd6, hFwd5]; exact Nat.le_succ _),
          (fun h => by cases h),
          ensureNonEmptyMsg_ne_empty "failed to start port forwarders" e (by decide),
          (fun h => by rw [hLin0] at h; cases h),
          (fun h => by rw [hArch0] at h; cases h)⟩
      | ok fh =>
        rcases hSfRes with ⟨_, _, _, _, hFwd6⟩
        have hRd := hRaw w6 (.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes) hw6
        dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
          stateM_map_run] at hRd
        rcases hRd with ⟨hw7, hLin7, hTgt7, hPl7, hBox7, hFwd7, hRdRes⟩
        cases hRdPair : (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes).run w6 with
        | mk rdRes w7 =>
          rw [hRdPair] at hw7 hLin7 hTgt7 hPl7 hBox7 hFwd7 hRdRes
          dsimp only at hw7 hLin7 hTgt7 hPl7 hBox7 hFwd7 hRdRes
          have hStop := step_stopPortForwarders proj raw hRaw fh w7 hw7
          rcases hStop with ⟨hw8, hLin8, hTgt8, hPl8, hBox8, hFwd8⟩
          let w8 := ((raw.stopPortForwarders fh).run w7).2
          have hClean := step_boxCleanup proj raw hRaw bh w8 hw8
          rcases hClean with ⟨hwC, hLinC, hTgtC, hPlC, hFwdC, hBoxC⟩
          cases rdRes with
          | error e =>
            have hActEq :
                act.run w5 =
                  (.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e),
                   ((do
                     let _ ← raw.killProcessGroup bh
                     let _ ← raw.pidfdKill bh
                     let _ ← raw.reapBox bh
                     pure ()).run w8).2) := by
              dsimp only [act]
              rw [stateM_bind_run, stateM_tryFinally'_run]
              simp only [hEmpP, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run,
                hSfPair, stateM_tryFinally'_run, hRdPair, w8]
            rw [hActEq]
            dsimp only
            refine ⟨hwC, hLinC.trans (hLin8.trans (hLin7.trans (hLin6.trans hLin5))),
              hTgtC.trans (hTgt8.trans (hTgt7.trans (hTgt6.trans hTgt5))),
              (by rw [hPlC, hPl8, hPl7, hPl6, hPl5]),
              (by rw [hBox8] at hBoxC; omega),
              (by rw [hFwdC]; exact Nat.le_trans hFwd8 (by rw [hFwd7, hFwd6, hFwd5]; exact Nat.le_refl _)),
              (fun h => by cases h),
              ensureNonEmptyMsg_ne_empty "sandbox I/O failed" e (by decide),
              (fun h => by rw [hLin0] at h; cases h),
              (fun h => by rw [hArch0] at h; cases h)⟩
          | ok boxRes =>
            have hActEq :
                act.run w5 =
                  (.ok boxRes,
                   ((do
                     let _ ← raw.killProcessGroup bh
                     let _ ← raw.pidfdKill bh
                     let _ ← raw.reapBox bh
                     pure ()).run w8).2) := by
              dsimp only [act]
              rw [stateM_bind_run, stateM_tryFinally'_run]
              simp only [hEmpP, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run,
                hSfPair, stateM_tryFinally'_run, hRdPair, w8]
            rw [hActEq]
            dsimp only
            refine ⟨hwC, hLinC.trans (hLin8.trans (hLin7.trans (hLin6.trans hLin5))),
              hTgtC.trans (hTgt8.trans (hTgt7.trans (hTgt6.trans hTgt5))),
              (by rw [hPlC, hPl8, hPl7, hPl6, hPl5]),
              (by rw [hBox8] at hBoxC; omega),
              (by rw [hFwdC]; exact Nat.le_trans hFwd8 (by rw [hFwd7, hFwd6, hFwd5]; exact Nat.le_refl _)),
              (fun h => by cases h),
              hLin0, hArch0, hRdRes.2.2.1, hRdRes.2.2.2⟩
  · have hEmpP : plan.portForwards.isEmpty = true := by rw [hPlanFwds, hEmp]
    have hRd := hRaw w5 (.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes) hw5
    dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
      stateM_map_run] at hRd
    rcases hRd with ⟨hw7, hLin7, hTgt7, hPl7, hBox7, hFwd7, hRdRes⟩
    cases hRdPair : (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes).run w5 with
    | mk rdRes w7 =>
      rw [hRdPair] at hw7 hLin7 hTgt7 hPl7 hBox7 hFwd7 hRdRes
      dsimp only at hw7 hLin7 hTgt7 hPl7 hBox7 hFwd7 hRdRes
      have hClean := step_boxCleanup proj raw hRaw bh w7 hw7
      rcases hClean with ⟨hwC, hLinC, hTgtC, hPlC, hFwdC, hBoxC⟩
      cases rdRes with
      | error e =>
        have hActEq :
            act.run w5 =
              (.error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e),
               ((do
                 let _ ← raw.killProcessGroup bh
                 let _ ← raw.pidfdKill bh
                 let _ ← raw.reapBox bh
                 pure ()).run w7).2) := by
          dsimp only [act]
          rw [stateM_bind_run, stateM_tryFinally'_run]
          simp only [hEmpP, ↓reduceIte, stateM_bind_run, stateM_pure_run,
            stateM_tryFinally'_run, hRdPair]
        rw [hActEq]
        dsimp only
        refine ⟨hwC, hLinC.trans (hLin7.trans hLin5), hTgtC.trans (hTgt7.trans hTgt5),
          (by rw [hPlC, hPl7, hPl5]), (by omega),
          (by rw [hFwdC, hFwd7, hFwd5]; exact Nat.le_succ _),
          (fun _ => by rw [hFwdC, hFwd7, hFwd5]),
          ensureNonEmptyMsg_ne_empty "sandbox I/O failed" e (by decide),
          (fun h => by rw [hLin0] at h; cases h),
          (fun h => by rw [hArch0] at h; cases h)⟩
      | ok boxRes =>
        have hActEq :
            act.run w5 =
              (.ok boxRes,
               ((do
                 let _ ← raw.killProcessGroup bh
                 let _ ← raw.pidfdKill bh
                 let _ ← raw.reapBox bh
                 pure ()).run w7).2) := by
          dsimp only [act]
          rw [stateM_bind_run, stateM_tryFinally'_run]
          simp only [hEmpP, ↓reduceIte, stateM_bind_run, stateM_pure_run,
            stateM_tryFinally'_run, hRdPair]
        rw [hActEq]
        dsimp only
        refine ⟨hwC, hLinC.trans (hLin7.trans hLin5), hTgtC.trans (hTgt7.trans hTgt5),
          (by rw [hPlC, hPl7, hPl5]), (by omega),
          (by rw [hFwdC, hFwd7, hFwd5]; exact Nat.le_succ _),
          (fun _ => by rw [hFwdC, hFwd7, hFwd5]),
          hLin0, hArch0, hRdRes.2.2.1, hRdRes.2.2.2⟩

end LeanSwe.ProcessSandbox.Proofs

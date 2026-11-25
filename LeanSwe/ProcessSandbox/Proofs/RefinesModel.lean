import Core.Obeys
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Model.Refines
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers
import LeanSwe.ProcessSandbox.Proofs.RefinesHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model
open LeanSwe.ProcessSandbox.Raw.Model

/-- `ProcessSandbox.validateSpec` refines `Model.validateSpecModel` definitionally. -/
theorem refinesPure_validateSpec :
    Core.ObeysPureEq LeanSwe.ProcessSandbox.validateSpec Model.validateSpecModel :=
  fun _ => rfl

/-- `Internal.mkApiM` satisfies `Core.ObeysStepFromFinally` lifting `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem refinesStepFromFinally_mkApiM :
    Core.ObeysStepFromFinally id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hw
  cases req with
  | validateSpec spec =>
    exact ⟨hw, rfl, rfl, rfl, rfl⟩
  | isAvailable =>
    have hPre := hRaw w (.preflight { needMemoryCgroup := true, needPidsCgroup := true }) hw
    dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
      stateM_map_run] at hPre
    rcases hPre with ⟨hw1, hLin1, hTgt1, hCnt1, hPl1, hBox1, hFwd1, hPreRes⟩
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.isAvailableGeneric,
      Model.allowedPkgStep, stateM_map_run, stateM_bind_run, Function.comp, id]
    cases hP : ((raw.preflight { needMemoryCgroup := true, needPidsCgroup := true }).run w).1 with
    | ok _ =>
      rw [hP] at hPreRes
      exact ⟨hw1, hLin1, hTgt1, hCnt1, hPl1, hBox1, hFwd1, fun _ => hPreRes⟩
    | error _ =>
      exact ⟨hw1, hLin1, hTgt1, hCnt1, hPl1, hBox1, hFwd1, fun h => by cases h⟩
  | run spec =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.runGeneric,
      Model.allowedPkgStep, stateM_map_run, Function.comp, id]
    cases hVal : validateSpecPure spec with
    | error e =>
      refine ⟨hw, rfl, rfl, rfl, ?_, ?_⟩
      · rw [ensureNonEmptyMsg_kind]
        exact validateSpecPure_error_kind hVal
      · exact ensureNonEmptyMsg_ne_empty "invalid sandbox specification" e (by decide)
    | ok valid =>
      let pfReq : PreflightReq :=
        { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
          needPidsCgroup := valid.limits.pidsMax.isSome }
      have hPre := hRaw w (.preflight pfReq) hw
      dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
        stateM_map_run] at hPre
      rcases hPre with ⟨hw1, hLin1, hTgt1, hCnt1, hPl1, hBox1, hFwd1, hPreRes⟩
      rw [stateM_bind_run]
      cases hPrePair : (raw.preflight pfReq).run w with
      | mk preRes w1 =>
        rw [hPrePair] at hw1 hLin1 hTgt1 hCnt1 hPl1 hBox1 hFwd1 hPreRes
        dsimp only at hw1 hLin1 hTgt1 hCnt1 hPl1 hBox1 hFwd1 hPreRes
        cases preRes with
        | error e =>
          dsimp only
          rw [stateM_pure_run]
          dsimp only
          refine ⟨hw1, hLin1, hTgt1,
            (by rw [hPl1]; exact Nat.le_succ _),
            (by rw [hBox1]; exact Nat.le_succ _),
            (by rw [hFwd1]; exact Nat.le_succ _),
            (fun _ => hFwd1),
            ensureNonEmptyMsg_ne_empty "sandbox unavailable" e (by decide),
            (fun _ => ⟨rfl, hCnt1⟩),
            (fun _ => ⟨rfl, hCnt1⟩)⟩
        | ok u =>
          cases u
          dsimp only
          have hArch := hRaw w1 .hostSeccompArch hw1
          dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
            stateM_map_run] at hArch
          rcases hArch with ⟨hw2, hLin2, hTgt2, hArchEq, hEq21⟩
          rw [stateM_bind_run]
          cases hArchPair : raw.hostSeccompArch.run w1 with
          | mk archRes w2 =>
            rw [hArchPair] at hw2 hLin2 hTgt2 hArchEq hEq21
            dsimp only at hw2 hLin2 hTgt2 hArchEq hEq21
            cases archRes with
            | error e =>
              dsimp only
              rw [stateM_pure_run]
              dsimp only
              refine ⟨hw2, hLin2.trans hLin1, hTgt2.trans hTgt1,
                (by rw [hEq21, hPl1]; exact Nat.le_succ _),
                (by rw [hEq21, hBox1]; exact Nat.le_succ _),
                (by rw [hEq21, hFwd1]; exact Nat.le_succ _),
                (fun _ => by rw [hEq21, hFwd1]),
                ensureNonEmptyMsg_ne_empty "unsupported host architecture for seccomp" e (by decide),
                (fun h => by rw [hPreRes] at h; cases h),
                (fun _ => ⟨rfl, by rw [hEq21, hCnt1]⟩)⟩
            | ok arch =>
              dsimp only
              have hArchOk : (decodeHostAuditArch (detectHostAuditArch (proj w).isLinux (proj w).target)).isOk = true := by
                rw [← hLin1, ← hTgt1, ← hArchEq]
                rfl
              have hDisc := hRaw w2 .discoverHostPreset hw2
              dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
                stateM_map_run] at hDisc
              rcases hDisc with ⟨hw3, hLin3, hTgt3, hEq32, _⟩
              rw [stateM_bind_run]
              cases hDiscPair : raw.discoverHostPreset.run w2 with
              | mk discRes w3 =>
                rw [hDiscPair] at hw3 hLin3 hTgt3 hEq32
                dsimp only at hw3 hLin3 hTgt3 hEq32
                cases discRes with
                | error e =>
                  dsimp only
                  rw [stateM_pure_run]
                  dsimp only
                  refine ⟨hw3, hLin3.trans (hLin2.trans hLin1), hTgt3.trans (hTgt2.trans hTgt1),
                    (by rw [hEq32, hEq21, hPl1]; exact Nat.le_succ _),
                    (by rw [hEq32, hEq21, hBox1]; exact Nat.le_succ _),
                    (by rw [hEq32, hEq21, hFwd1]; exact Nat.le_succ _),
                    (fun _ => by rw [hEq32, hEq21, hFwd1]),
                    ensureNonEmptyMsg_ne_empty "host runtime preset discovery failed" e (by decide),
                    (fun h => by rw [hPreRes] at h; cases h),
                    (fun h => by rw [hArchOk] at h; cases h)⟩
                | ok preset =>
                  dsimp only
                  let plan := compilePlan valid preset
                  let secBytes := Internal.encodedSeccompFilter arch
                  have hSeal := hRaw w3 (.sealPlan plan secBytes) hw3
                  dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
                    stateM_map_run] at hSeal
                  rcases hSeal with ⟨hw4, hLin4, hTgt4, hBox4, hFwd4, hSealRes⟩
                  rw [stateM_bind_run]
                  cases hSealPair : (raw.sealPlan plan secBytes).run w3 with
                  | mk sealRes w4 =>
                    rw [hSealPair] at hw4 hLin4 hTgt4 hBox4 hFwd4 hSealRes
                    dsimp only at hw4 hLin4 hTgt4 hBox4 hFwd4 hSealRes
                    cases sealRes with
                    | error e =>
                      dsimp only
                      rw [stateM_pure_run]
                      dsimp only
                      refine ⟨hw4, hLin4.trans (hLin3.trans (hLin2.trans hLin1)),
                        hTgt4.trans (hTgt3.trans (hTgt2.trans hTgt1)),
                        (by rw [hSealRes.2, hEq32, hEq21, hPl1]; exact Nat.le_succ _),
                        (by rw [hBox4, hEq32, hEq21, hBox1]; exact Nat.le_succ _),
                        (by rw [hFwd4, hEq32, hEq21, hFwd1]; exact Nat.le_succ _),
                        (fun _ => by rw [hFwd4, hEq32, hEq21, hFwd1]),
                        ensureNonEmptyMsg_ne_empty "failed to seal sandbox plan" e (by decide),
                        (fun h => by rw [hPreRes] at h; cases h),
                        (fun h => by rw [hArchOk] at h; cases h)⟩
                    | ok ph =>
                      dsimp only
                      rcases hSealRes with ⟨_, _, _, _, _, hPl4⟩
                      rw [stateM_bind_run, stateM_tryFinally'_run, stateM_bind_run]
                      have hSp := hRaw w4 (.spawnBox ph) hw4
                      dsimp only [Model.execRawStep, execRawOpsStep, Model.allowedRawStep, allowedRawOpsStep,
                        stateM_map_run] at hSp
                      rcases hSp with ⟨hw5, hLin5, hTgt5, hPl5, hFwd5, hSpRes⟩
                      cases hSpPair : (raw.spawnBox ph).run w4 with
                      | mk spRes w5 =>
                        rw [hSpPair] at hw5 hLin5 hTgt5 hPl5 hFwd5 hSpRes
                        dsimp only at hw5 hLin5 hTgt5 hPl5 hFwd5 hSpRes
                        cases spRes with
                        | error e =>
                          dsimp only
                          simp only [stateM_bind_run, stateM_pure_run]
                          have hCl := step_closePlan proj raw hRaw ph w5 hw5
                          rcases hCl with ⟨hwC, hLinC, hTgtC, hBoxC, hFwdC, hPlC⟩
                          refine ⟨hwC, hLinC.trans (hLin5.trans (hLin4.trans (hLin3.trans (hLin2.trans hLin1)))),
                            hTgtC.trans (hTgt5.trans (hTgt4.trans (hTgt3.trans (hTgt2.trans hTgt1)))),
                            (by rw [hPl5, hPl4, hEq32, hEq21, hPl1] at hPlC; exact hPlC),
                            (by rw [hBoxC, hSpRes.2.1, hBox4, hEq32, hEq21, hBox1]; exact Nat.le_succ _),
                            (by rw [hFwdC, hFwd5, hFwd4, hEq32, hEq21, hFwd1]; exact Nat.le_succ _),
                            (fun _ => by rw [hFwdC, hFwd5, hFwd4, hEq32, hEq21, hFwd1]),
                            ensureNonEmptyMsg_ne_empty "failed to spawn sandbox" e (by decide),
                            (fun h => by rw [hPreRes] at h; cases h),
                            (fun h => by rw [hArchOk] at h; cases h)⟩
                        | ok bh =>
                          dsimp only
                          rcases hSpRes with ⟨_, _, _, _, _, _, _, hBox5⟩
                          let boxAct : StateM W (Except SandboxError SandboxResult) := do
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
                          have hInner := runGeneric_after_spawn_ok proj raw hRaw valid preset (proj w) bh w5
                            hw5 hPreRes hArchOk
                            (hLin5.trans (hLin4.trans (hLin3.trans (hLin2.trans hLin1))))
                            (hTgt5.trans (hTgt4.trans (hTgt3.trans (hTgt2.trans hTgt1))))
                            (by rw [hPl5, hPl4, hEq32, hEq21, hPl1])
                            (by rw [hBox5, hBox4, hEq32, hEq21, hBox1])
                            (by rw [hFwd5, hFwd4, hEq32, hEq21, hFwd1])
                          dsimp only at hInner
                          rcases hInner with ⟨hwB, hLinB, hTgtB, hPlB, hBoxB, hFwdB, hFwdEmpB, hResB⟩
                          have hCl := step_closePlan proj raw hRaw ph (boxAct.run w5).2 hwB
                          rcases hCl with ⟨hwC, hLinC, hTgtC, hBoxC, hFwdC, hPlC⟩
                          change
                            rawHostWorldWf (proj ((raw.closePlan ph).run (boxAct.run w5).2).2) = true ∧
                            (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).isLinux = (proj w).isLinux ∧
                            (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).target = (proj w).target ∧
                            (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table.plans.length ≤ (proj w).table.plans.length + 1 ∧
                            (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table.boxes.length ≤ (proj w).table.boxes.length + 1 ∧
                            (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table.fwds.length ≤ (proj w).table.fwds.length + 1 ∧
                            (valid.portForwards.isEmpty = true → (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table.fwds = (proj w).table.fwds) ∧
                            match (boxAct.run w5).1 with
                            | .ok boxRes =>
                              (proj w).isLinux = true ∧
                              (decodeHostAuditArch (detectHostAuditArch (proj w).isLinux (proj w).target)).isOk = true ∧
                              outcomeNonNeg boxRes.outcome ∧
                              (∀ m, valid.limits.maxOutputBytes = some m → boxRes.stdout.size + boxRes.stderr.size ≤ m)
                            | .error err =>
                              err.message ≠ "" ∧
                              ((proj w).isLinux = false → err.kind = .unavailable ∧ tableCounts (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table = tableCounts (proj w).table) ∧
                              ((decodeHostAuditArch (detectHostAuditArch (proj w).isLinux (proj w).target)).isOk = false →
                                err.kind = .unavailable ∧ tableCounts (proj ((raw.closePlan ph).run (boxAct.run w5).2).2).table = tableCounts (proj w).table)
                          refine ⟨hwC, hLinC.trans hLinB, hTgtC.trans hTgtB,
                            (Nat.le_trans hPlC (Nat.le_of_eq hPlB)),
                            (by rw [hBoxC]; exact hBoxB), (by rw [hFwdC]; exact hFwdB),
                            (fun h => by rw [hFwdC]; exact hFwdEmpB h), ?_⟩
                          have hResB' :
                              match (boxAct.run w5).1 with
                              | .ok boxRes =>
                                (proj w).isLinux = true ∧
                                (decodeHostAuditArch (detectHostAuditArch (proj w).isLinux (proj w).target)).isOk = true ∧
                                outcomeNonNeg boxRes.outcome ∧
                                (∀ m, valid.limits.maxOutputBytes = some m → boxRes.stdout.size + boxRes.stderr.size ≤ m)
                              | .error err =>
                                err.message ≠ "" ∧
                                ((proj w).isLinux = false → err.kind = .unavailable ∧ tableCounts (proj (boxAct.run w5).2).table = tableCounts (proj w).table) ∧
                                ((decodeHostAuditArch (detectHostAuditArch (proj w).isLinux (proj w).target)).isOk = false →
                                  err.kind = .unavailable ∧ tableCounts (proj (boxAct.run w5).2).table = tableCounts (proj w).table) := hResB
                          cases hOut : (boxAct.run w5).1 with
                          | ok boxRes =>
                            rw [hOut] at hResB'
                            exact hResB'
                          | error err =>
                            rw [hOut] at hResB'
                            exact ⟨hResB'.1, (fun h => by rw [hPreRes] at h; cases h),
                              (fun h => by rw [hArchOk] at h; cases h)⟩

end LeanSwe.ProcessSandbox.Proofs

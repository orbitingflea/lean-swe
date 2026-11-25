import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesTableHelpers
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepPresetBwrap
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesPipeHelpers
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesPure

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

private theorem preserves_bind_eq {W α β : Type} {proj : W → RawHostWorld} {Q : β → W → Prop}
    {target : RawHostWorld} {ma : StateM W α} {k : α → StateM W β} {w : W}
    (hEq : proj w = target) (hWf : rawHostWorldWf target = true) (hMa : PreservesProj proj ma)
    (hK : ∀ a s, proj s = target → Q ((k a).run s).1 ((k a).run s).2) :
    Q ((ma >>= k).run w).1 ((ma >>= k).run w).2 := by
  simp only [stateM_bind_run]
  have hp := hMa w (by rw [hEq]; exact hWf)
  exact hK _ _ (hp.trans hEq)

private theorem preserves_err_eq {W α β : Type} {proj : W → RawHostWorld} {Q : β → W → Prop}
    {target : RawHostWorld} {ma : StateM W α} {res : β} {w : W}
    (hEq : proj w = target) (hWf : rawHostWorldWf target = true) (hMa : PreservesProj proj ma)
    (hQ : ∀ s, proj s = target → Q res s) :
    Q ((ma >>= fun _ => pure res).run w).1 ((ma >>= fun _ => pure res).run w).2 := by
  simp only [stateM_bind_run, stateM_pure_run]
  exact hQ _ ((hMa w (by rw [hEq]; exact hWf)).trans hEq)

/-- `preflightPure` satisfies `allowedRawOpsStep` for `.preflight req`. -/
theorem preflightPure_refines {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (eintrFuel : Nat) (req : PreflightReq) (w : W) (hWf : rawHostWorldWf (proj w) = true)
    (emb : Except String ByteArray := embeddedInitBytes) :
    let r := (preflightPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel req emb).run w
    allowedRawOpsStep (proj w) (.preflight req) (.exceptUnit r.1) (proj r.2) := by
  have ⟨hLin, _⟩ := cap_metaInfo_eq hCap hWf
  let Q : Except SandboxError Unit → W → Prop :=
    fun out s => allowedRawOpsStep (proj w) (.preflight req) (.exceptUnit out) (proj s)
  have hUnavail : ∀ (w' : W) (e? : Option Errno) (msg : String),
      rawHostWorldWf (proj w') = true →
      (proj w').isLinux = (proj w).isLinux →
      (proj w').target = (proj w).target →
      (proj w').table.plans = (proj w).table.plans →
      (proj w').table.boxes = (proj w).table.boxes →
      (proj w').table.fwds = (proj w).table.fwds →
      Q (.error (Internal.mapRawError (.unavailable e? msg))) w' := by
    intro w' e? msg hWf' hL' hT' hPl hBx hFw
    refine ⟨hWf', hL', hT', ?_, hPl, hBx, hFw, rfl, mapRawError_unavail_ne_empty e? msg⟩
    simp [tableCounts, hPl, hBx, hFw]
  have hUnavailSame : ∀ (s : W) (e? : Option Errno) (msg : String),
      proj s = proj w →
      Q (.error (Internal.mapRawError (.unavailable e? msg))) s := fun s e? msg hp =>
    hUnavail s e? msg (by rw [hp]; exact hWf) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp])
  change Q ((preflightPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel req emb).run w).1
    ((preflightPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel req emb).run w).2
  unfold preflightPure
  rcases Bool.eq_false_or_eq_true (toHostSysDeps cap).isLinux with hCapLin | hCapLin
  · have hProjLin : (proj w).isLinux = true := by rw [← hLin]; exact hCapLin
    simp only [hCapLin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases Bool.eq_false_or_eq_true (Bwrap.detectHostAuditArch true (toHostSysDeps cap).target == 0) with hArch | hArch
    · simp only [hArch, ↓reduceIte, stateM_pure_run]
      exact hUnavailSame w (some Errno.ENOSYS) _ rfl
    · simp only [hArch, Bool.false_eq_true, ↓reduceIte]
      dsimp only [toHostSysDeps]
      refine preserves_bind_eq rfl hWf (preservesProj_resolveBwrapPath hCap eintrFuel) fun bw? s hEq => ?_
      cases bw? with
      | none => simp only [stateM_pure_run]; exact hUnavailSame s (some Errno.ENOENT) _ hEq
      | some bwrapPath =>
        dsimp only
        refine preserves_bind_eq hEq hWf
          (preservesProj_of_seqUnit _ fun u hu => (hCap u (.sandboxLandlockCreateRuleset none Sandbox.LANDLOCK_CREATE_RULESET_VERSION) hu).2)
          fun rLl s hEq => ?_
        cases rLl with
        | error e => simp only [stateM_pure_run]; exact hUnavailSame s (some e) _ hEq
        | ok lr =>
          cases lr with
          | ruleset h =>
            dsimp only
            exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some h)) (fun s' hEq' => hUnavailSame s' (some Errno.ENOSYS) _ hEq')
          | version abi =>
            dsimp only
            by_cases hAbi : abi.toNat < 4
            · simp only [hAbi, ↓reduceIte, stateM_pure_run]
              exact hUnavailSame s (some Errno.ENOSYS) _ hEq
            · simp only [hAbi, ↓reduceIte]
              refine preserves_bind_eq hEq hWf
                (preservesProj_of_seqUnit _ fun u hu => (hCap u (.sandboxSeccomp (.getActionAvail Sandbox.SECCOMP_RET_ERRNO) {} ByteArray.empty) hu).2)
                fun rSc s hEq => ?_
              cases rSc with
              | error e => simp only [stateM_pure_run]; exact hUnavailSame s (some e) _ hEq
              | ok _ =>
                dsimp only
                cases emb with
                | error msg => simp only [stateM_pure_run]; exact hUnavailSame s (some Errno.ENOEXEC) msg hEq
                | ok initBytes =>
                  dsimp only
                  refine preserves_bind_eq hEq hWf (preservesProj_probeBwrapNamespaces hCap bwrapPath initBytes eintrFuel) fun rPr s hEq => ?_
                  cases rPr with
                  | error e => simp only [stateM_pure_run]; exact hUnavailSame s (some e) _ hEq
                  | ok _ =>
                    dsimp only
                    refine preserves_bind_eq hEq hWf (preservesProj_of_seqUnit _ fun u hu => (hCap u .procGetpid hu).2) fun rPid s hEq => ?_
                    cases rPid with
                    | error e => simp only [stateM_pure_run]; exact hUnavailSame s (some e) _ hEq
                    | ok pid =>
                      dsimp only
                      rw [stateM_bind_run]
                      have hWfS : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                      have ⟨hSeqProj, hWfSeq⟩ := tbl_nextCgSeq_spec hCap hWfS
                      let seq := ((toHostTableOps cap).nextCgSeq.run s).1
                      let sSeq := ((toHostTableOps cap).nextCgSeq.run s).2
                      let targetSeq : RawHostWorld := { proj w with table := { (proj w).table with cgSeq := (proj w).table.cgSeq + 1 } }
                      have hEqSeq : proj sSeq = targetSeq := by simpa [sSeq, targetSeq, hEq] using hSeqProj
                      have hWfT : rawHostWorldWf targetSeq = true := by rw [← hEqSeq]; exact hWfSeq
                      refine preserves_bind_eq (w := sSeq) hEqSeq hWfT (preservesProj_createSiblingCgroup hCap pid seq eintrFuel) fun rCg s hEq => ?_
                      cases rCg with
                      | error e =>
                        simp only [stateM_pure_run]
                        refine hUnavail s (some e) _ (by rw [hEq]; exact hWfT) ?_ ?_ ?_ ?_ ?_ <;> simp [hEq, targetSeq]
                      | ok cgDir =>
                        dsimp only
                        have hFinish : ∀ (fail? : Option (Errno × String)) (u : W), proj u = targetSeq →
                            let fin : StateM W (Except SandboxError Unit) := do
                              let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                              match fail? with
                              | some (e, msg) => return .error (Internal.mapRawError (.unavailable (some e) msg))
                              | none => return .ok ()
                            Q (fin.run u).1 (fin.run u).2 := by
                          intro fail? u hu
                          dsimp only
                          refine preserves_bind_eq hu hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel) fun _ u hu => ?_
                          cases fail? with
                          | some em =>
                            rcases em with ⟨e, msg⟩
                            simp only [stateM_pure_run]
                            refine hUnavail u (some e) msg (by rw [hu]; exact hWfT) ?_ ?_ ?_ ?_ ?_ <;> simp [hu, targetSeq]
                          | none =>
                            simp only [stateM_pure_run]
                            refine ⟨by rw [hu]; exact hWfT, by simp [hu, targetSeq], by simp [hu, targetSeq],
                              by simp [tableCounts, hu, targetSeq], by simp [hu, targetSeq],
                              by simp [hu, targetSeq], by simp [hu, targetSeq], hProjLin⟩
                        have hAfterMem : ∀ (mf : Option (Errno × String)) (u : W), proj u = targetSeq →
                            let rest : StateM W (Except SandboxError Unit) := do
                              let fail? ← match mf with
                                | some f => pure (some f)
                                | none =>
                                  if req.needPidsCgroup then
                                    match ← configureCgroupPids cap.files cgDir "max" eintrFuel with
                                    | .ok () => pure none
                                    | .error e => pure (some (e, "direct cgroup v2 pids controller unavailable"))
                                  else pure none
                              let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                              match fail? with
                              | some (e, msg) => return .error (Internal.mapRawError (.unavailable (some e) msg))
                              | none => return .ok ()
                            Q (rest.run u).1 (rest.run u).2 := by
                          intro mf u hu
                          dsimp only
                          cases mf with
                          | some f =>
                            rw [stateM_bind_run]
                            exact hFinish (some f) u hu
                          | none =>
                            cases req.needPidsCgroup with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              rw [stateM_bind_run]
                              exact hFinish none u hu
                            | true =>
                              simp only [↓reduceIte]
                              refine preserves_bind_eq hu hWfT (preservesProj_writeTextFile hCap _ "max" eintrFuel) fun rP u hu => ?_
                              cases rP with
                              | ok _ => rw [stateM_bind_run]; exact hFinish none u hu
                              | error e => rw [stateM_bind_run]; exact hFinish (some (e, "direct cgroup v2 pids controller unavailable")) u hu
                        refine preserves_bind_eq hEq hWfT
                          (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.filesFaccessat none _ _ {}) hu).2) eintrFuel)
                          fun r1 s hEq => ?_
                        cases r1 with
                        | error e => rw [stateM_bind_run]; exact hFinish (some (e, "cgroup v2 cgroup.kill is unavailable")) s hEq
                        | ok _ =>
                          dsimp only
                          refine preserves_bind_eq hEq hWfT
                            (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.filesFaccessat none _ _ {}) hu).2) eintrFuel)
                            fun r2 s hEq => ?_
                          cases r2 with
                          | error e => rw [stateM_bind_run]; exact hFinish (some (e, "cgroup v2 cgroup.events is unavailable")) s hEq
                          | ok _ =>
                            dsimp only
                            cases req.needMemoryCgroup with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              rw [stateM_bind_run]
                              exact hAfterMem none s hEq
                            | true =>
                              simp only [↓reduceIte]
                              refine preserves_bind_eq hEq hWfT (preservesProj_configureCgroupMemory hCap cgDir "max" eintrFuel) fun rM s hEq => ?_
                              cases rM with
                              | ok _ => rw [stateM_bind_run]; exact hAfterMem none s hEq
                              | error fe =>
                                rcases fe with ⟨fname, e⟩
                                rw [stateM_bind_run]
                                exact hAfterMem (some (e, if fname == "memory.max" then "direct cgroup v2 memory controller unavailable" else s!"direct cgroup v2 {fname} unavailable")) s hEq
  · simp only [hCapLin, Bool.not_false, ↓reduceIte, stateM_pure_run]
    exact hUnavailSame w none _ rfl

/-- `sealPlanPure` satisfies `allowedRawOpsStep` for `.sealPlan plan sec`. -/
theorem sealPlanPure_refines {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (eintrFuel : Nat) (plan : CompiledSandboxPlan) (sec : ByteArray)
    (w : W) (hWf : rawHostWorldWf (proj w) = true)
    (emb : Except String ByteArray := embeddedInitBytes) :
    let r := (sealPlanPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel plan sec emb).run w
    allowedRawOpsStep (proj w) (.sealPlan plan sec) (.exceptPlan r.1) (proj r.2) := by
  have ⟨hLin, _⟩ := cap_metaInfo_eq hCap hWf
  have hEnc := refinesPure_encodePlan plan sec
  let Q : Except SandboxError PlanHandle → W → Prop :=
    fun out s => allowedRawOpsStep (proj w) (.sealPlan plan sec) (.exceptPlan out) (proj s)
  have hErrSame : ∀ (s : W) (e : SandboxError), proj s = proj w → e.message ≠ "" →
      Q (.error e) s := fun s e hp hne => by
    change allowedRawOpsStep (proj w) (.sealPlan plan sec) (.exceptPlan (.error e)) (proj s)
    rw [hp]; exact ⟨hWf, rfl, rfl, rfl, rfl, hne, rfl⟩
  change Q ((sealPlanPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel plan sec emb).run w).1
    ((sealPlanPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel plan sec emb).run w).2
  unfold sealPlanPure
  cases hE : Internal.encodePlan plan sec with
  | error e =>
    change allowedEncodePlan plan sec (Internal.encodePlan plan sec) at hEnc
    rw [hE] at hEnc
    simp only [stateM_pure_run]
    exact hErrSame w e rfl hEnc.2.1
  | ok wire =>
    change allowedEncodePlan plan sec (Internal.encodePlan plan sec) at hEnc
    rw [hE] at hEnc
    rcases hEnc with ⟨hMand, hSec, _, _⟩
    dsimp only
    cases hLim : isPlanWithinInitLimits plan with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
      exact hErrSame w _ rfl (mapRawError_invalidArg_spec _ _ _).2
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases Bool.eq_false_or_eq_true (toHostSysDeps cap).isLinux with hCapLin | hCapLin
      · have hProjLin : (proj w).isLinux = true := by rw [← hLin]; exact hCapLin
        simp only [hCapLin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        dsimp only [toHostSysDeps]
        cases emb with
        | error msg =>
          simp only [stateM_pure_run]
          exact hErrSame w _ rfl (mapRawError_unavail_ne_empty _ msg)
        | ok initBytes =>
          dsimp only
          refine preserves_bind_eq rfl hWf (preservesProj_createSealedMemfd hCap "leanswe-psandbox-plan" wire eintrFuel) fun r1 s hEq => ?_
          cases r1 with
          | error e => simp only [stateM_pure_run]; exact hErrSame s _ hEq (mapRawError_ioError_ne_empty e _)
          | ok planMemfd =>
            dsimp only
            refine preserves_bind_eq hEq hWf (preservesProj_createSealedMemfd hCap "leanswe-psandbox-init" initBytes eintrFuel) fun r2 s hEq => ?_
            cases r2 with
            | error e =>
              dsimp only
              exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some planMemfd))
                (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
            | ok initMemfd =>
              dsimp only
              refine preserves_bind_eq hEq hWf (preservesProj_createSealedMemfd hCap "leanswe-psandbox-hosts" SYNTHETIC_HOSTS_BYTES eintrFuel) fun r3 s hEq => ?_
              cases r3 with
              | error e =>
                dsimp only
                refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some planMemfd)) fun _ s hEq => ?_
                exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some initMemfd))
                  (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
              | ok hostsMemfd =>
                dsimp only
                let slot : PlanSlotM Nat := { plan := plan, planMemfd := planMemfd, initMemfd := initMemfd, hostsMemfd := hostsMemfd }
                rw [stateM_bind_run]
                have hIns := tbl_insertPlan_spec hCap (by rw [hEq]; exact hWf) slot
                rcases hIns with ⟨hWf4, hL4, hT4, hBx4, hFw4, hBody⟩
                cases hR : (((toHostTableOps cap).insertPlan slot).run s).1 with
                | none =>
                  rw [hR] at hBody
                  refine preserves_bind_eq (hBody.trans hEq) hWf (preservesProj_closeOpt hCap (some planMemfd)) fun _ s hEq => ?_
                  refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some initMemfd)) fun _ s hEq => ?_
                  exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some hostsMemfd))
                    (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty Errno.ENOMEM _))
                | some hid =>
                  rw [hR] at hBody
                  rcases hBody with ⟨hHidV, hHidEq, hLen⟩
                  simp only [stateM_pure_run]
                  refine ⟨hWf4, hL4.trans (congrArg RawHostWorld.isLinux hEq),
                    hT4.trans (congrArg RawHostWorld.target hEq),
                    hBx4.trans (congrArg (fun x => x.table.boxes) hEq),
                    hFw4.trans (congrArg (fun x => x.table.fwds) hEq),
                    hProjLin, hMand, hSec, hHidV,
                    hHidEq.trans (congrArg (fun x => x.table.nextId) hEq),
                    hLen.trans (congrArg (fun x => x.table.plans.length + 1) hEq)⟩
      · simp only [hCapLin, Bool.not_false, ↓reduceIte, stateM_pure_run]
        exact hErrSame w _ rfl (mapRawError_unavail_ne_empty _ _)

end LeanSwe.ProcessSandbox.Raw.Proofs

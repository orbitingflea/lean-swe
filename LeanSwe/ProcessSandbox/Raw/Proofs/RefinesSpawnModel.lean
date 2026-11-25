import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesTableHelpers
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepPresetBwrap
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepSpawnKill
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesPipeHelpers

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

private theorem preservesProj_allocCtrlSocketpair {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (nFwds eintrFuel : Nat) :
    PreservesProj proj (allocCtrlSocketpair cap.net nFwds eintrFuel) := by
  unfold allocCtrlSocketpair
  refine preservesProj_ite ?_ (preservesProj_pure _)
  refine preservesProj_bind
    (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.netSocketpair .unix .seqpacket { cloexec := true }) hu).2) eintrFuel)
    fun r => ?_
  cases r <;> exact preservesProj_pure _

private theorem preservesProj_setupSpawnCgroupLimits {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (cgDir : String) (limits : SandboxLimits) (eintrFuel : Nat) :
    PreservesProj proj (setupSpawnCgroupLimits cap.files cgDir limits eintrFuel) := by
  have hPids : PreservesProj proj
      (match limits.pidsMax with
       | none => pure none
       | some pMax => do
         match ← configureCgroupPids cap.files cgDir (toString (cappedPidsMax pMax)) eintrFuel with
         | .ok () => pure none
         | .error e => pure (some (e, s!"failed to set direct cgroup v2 pids.max: {Errno.name e}"))) := by
    cases limits.pidsMax with
    | none => exact preservesProj_pure _
    | some pMax =>
      unfold configureCgroupPids
      refine preservesProj_bind (preservesProj_writeTextFile hCap _ (toString (cappedPidsMax pMax)) eintrFuel) fun r => ?_
      cases r <;> exact preservesProj_pure _
  unfold setupSpawnCgroupLimits
  refine preservesProj_bind
    (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.filesFaccessat none _ _ {}) hu).2) eintrFuel)
    fun r1 => ?_
  cases r1 with
  | error _ => exact preservesProj_pure _
  | ok _ =>
    dsimp only
    cases limits.memoryMaxBytes with
    | none => exact hPids
    | some memMax =>
      refine preservesProj_bind (preservesProj_configureCgroupMemory hCap cgDir (toString memMax) eintrFuel) fun rM => ?_
      cases rM with
      | ok _ => exact hPids
      | error fe => rcases fe with ⟨_, _⟩; exact preservesProj_pure _

private theorem preservesProj_recvPortListenerFds {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (ctrlR? : Option Nat) (statusR nFwds : Nat) :
    PreservesProj proj (recvPortListenerFds cap.files cap.net cap.poll ctrlR? statusR nFwds) := by
  unfold recvPortListenerFds
  cases ctrlR? with
  | none => exact preservesProj_pure _
  | some cr =>
    unfold recvFdsScm
    exact preservesProj_bind (preservesProj_recvFdsScm hCap cr statusR nFwds #[] 2048) fun r =>
      preservesProj_bind (preservesProj_closeOpt hCap (some cr)) fun _ => preservesProj_pure r

/-- `spawnBoxPure` satisfies `allowedRawOpsStep` for `.spawnBox ph`. -/
theorem spawnBoxPure_refines {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (eintrFuel : Nat) (ph : PlanHandle) (w : W) (hWf : rawHostWorldWf (proj w) = true) :
    let r := (spawnBoxPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel ph).run w
    allowedRawOpsStep (proj w) (.spawnBox ph) (.exceptBox r.1) (proj r.2) := by
  let Q : Except SandboxError BoxHandle → W → Prop :=
    fun out s => allowedRawOpsStep (proj w) (.spawnBox ph) (.exceptBox out) (proj s)
  have hErrValid : ∀ (w' : W) (e : SandboxError),
      isValidSandboxHandleId ph.handleId = true →
      tableHasKey ph.handleId (proj w).table.plans = true →
      rawHostWorldWf (proj w') = true →
      (proj w').isLinux = (proj w).isLinux →
      (proj w').target = (proj w).target →
      (proj w').table.plans = (proj w).table.plans →
      (proj w').table.boxes = (proj w).table.boxes →
      (proj w').table.fwds = (proj w).table.fwds →
      e.message ≠ "" → Q (.error e) w' := by
    intro w' e hVal hKey hWf' hL' hT' hPl hBx hFw hMsg
    refine ⟨hWf', hL', hT', hPl, hFw, hMsg, hBx, fun hOr => ?_⟩
    rcases hOr with hF | hF <;> simp [hVal, hKey] at hF
  change Q ((spawnBoxPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel ph).run w).1
    ((spawnBoxPure (toHostSysDeps cap) (toHostTableOps cap) eintrFuel ph).run w).2
  unfold spawnBoxPure
  cases hVal : isValidSandboxHandleId ph.handleId with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, stateM_pure_run]
    exact ⟨hWf, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run]
    dsimp only [toHostSysDeps]
    have ⟨hFindSome, hFindProj⟩ := tbl_findPlan_spec hCap hWf ph.handleId
    cases hFp : (((toHostTableOps cap).findPlan ph.handleId).run w).1 with
    | none =>
      rw [hFp] at hFindSome
      simp only [stateM_pure_run]
      change allowedRawOpsStep (proj w) (.spawnBox ph) (.exceptBox (.error _)) (proj (((toHostTableOps cap).findPlan ph.handleId).run w).2)
      rw [hFindProj]
      exact ⟨hWf, rfl, rfl, rfl, rfl, (mapRawError_invalidArg_spec _ _ _).2, rfl, fun _ => ⟨rfl, rfl⟩⟩
    | some pslot =>
      rw [hFp] at hFindSome
      have hKey : tableHasKey ph.handleId (proj w).table.plans = true := hFindSome.symm
      let w0 := ((toHostTableOps cap).findPlan ph.handleId).run w |>.2
      have hEq0 : proj w0 = proj w := hFindProj
      have hErrSame : ∀ (s : W) (e : SandboxError), proj s = proj w → e.message ≠ "" → Q (.error e) s := fun s e hp hm =>
        hErrValid s e hVal hKey (by rw [hp]; exact hWf) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) hm
      have hPipe : PreservesProj proj (retryEintr (cap.proc.pipe2 { cloexec := true }) eintrFuel) :=
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.procPipe2 { cloexec := true }) hu).2) eintrFuel
      have hReopen : ∀ fd, PreservesProj proj (retryEintr (cap.files.reopenReadOnly fd) eintrFuel) := fun fd =>
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.filesReopenReadOnly fd) hu).2) eintrFuel
      dsimp only
      have ⟨hPreP, hPreE⟩ := precheckHostMounts_spec hCap eintrFuel pslot.plan.userMounts.toList
      have hPreRun : proj ((precheckHostMounts cap.files eintrFuel pslot.plan.userMounts.toList).run w0).2 = proj w :=
        (hPreP w0 (by rw [hEq0]; exact hWf)).trans hEq0
      rw [stateM_bind_run]
      cases hPre : ((precheckHostMounts cap.files eintrFuel pslot.plan.userMounts.toList).run w0).1 with
      | error e =>
        simp only [stateM_pure_run]
        exact hErrSame _ e hPreRun (hPreE w0 (by rw [hEq0]; exact hWf) e hPre)
      | ok _ =>
        dsimp only
        refine preserves_bind_eq hPreRun hWf (preservesProj_resolveBwrapPath hCap eintrFuel) fun bw? s hEq => ?_
        cases bw? with
        | none => simp only [stateM_pure_run]; exact hErrSame s _ hEq (mapRawError_unavail_ne_empty _ _)
        | some bwrapPath =>
          dsimp only
          refine preserves_bind_eq hEq hWf hPipe fun rIn s hEq => ?_
          cases rIn with
          | error e => simp only [stateM_pure_run]; exact hErrSame s _ hEq (mapRawError_ioError_ne_empty e _)
          | ok pIn =>
            rcases pIn with ⟨inR, inW⟩
            dsimp only
            refine preserves_bind_eq hEq hWf hPipe fun rOut s hEq => ?_
            cases rOut with
            | error e =>
              dsimp only
              refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some inR)) fun _ s hEq => ?_
              exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some inW))
                (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
            | ok pOut =>
              rcases pOut with ⟨outR, outW⟩
              dsimp only
              refine preserves_bind_eq hEq hWf hPipe fun rErr s hEq => ?_
              cases rErr with
              | error e =>
                dsimp only
                refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some inR)) fun _ s hEq => ?_
                refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some inW)) fun _ s hEq => ?_
                refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some outR)) fun _ s hEq => ?_
                exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap (some outW))
                  (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
              | ok pErr =>
                rcases pErr with ⟨errR, errW⟩
                dsimp only
                have hClStd : PreservesProj proj (do
                    Files.closeOpt cap.files (some inR); Files.closeOpt cap.files (some inW)
                    Files.closeOpt cap.files (some outR); Files.closeOpt cap.files (some outW)
                    Files.closeOpt cap.files (some errR); Files.closeOpt cap.files (some errW)) :=
                  preservesProj_bind (preservesProj_closeOpt hCap (some inR)) fun _ =>
                    preservesProj_bind (preservesProj_closeOpt hCap (some inW)) fun _ =>
                      preservesProj_bind (preservesProj_closeOpt hCap (some outR)) fun _ =>
                        preservesProj_bind (preservesProj_closeOpt hCap (some outW)) fun _ =>
                          preservesProj_bind (preservesProj_closeOpt hCap (some errR)) fun _ => preservesProj_closeOpt hCap (some errW)
                refine preserves_bind_eq hEq hWf (hReopen pslot.initMemfd) fun rI s hEq => ?_
                cases rI with
                | error e => dsimp only; exact preserves_err_eq hEq hWf hClStd (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                | ok initFd =>
                  dsimp only
                  refine preserves_bind_eq hEq hWf (hReopen pslot.hostsMemfd) fun rH s hEq => ?_
                  cases rH with
                  | error e =>
                    dsimp only
                    refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some initFd)) fun _ s hEq => ?_
                    exact preserves_err_eq hEq hWf hClStd (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                  | ok hostsFd =>
                    dsimp only
                    refine preserves_bind_eq hEq hWf (hReopen pslot.planMemfd) fun rP s hEq => ?_
                    cases rP with
                    | error e =>
                      dsimp only
                      refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some hostsFd)) fun _ s hEq => ?_
                      refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some initFd)) fun _ s hEq => ?_
                      exact preserves_err_eq hEq hWf hClStd (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                    | ok planFd =>
                      dsimp only
                      have hClBase : PreservesProj proj (do
                          Files.closeOpt cap.files (some planFd); Files.closeOpt cap.files (some hostsFd); Files.closeOpt cap.files (some initFd)
                          do
                            Files.closeOpt cap.files (some inR); Files.closeOpt cap.files (some inW)
                            Files.closeOpt cap.files (some outR); Files.closeOpt cap.files (some outW)
                            Files.closeOpt cap.files (some errR); Files.closeOpt cap.files (some errW)) :=
                        preservesProj_bind (preservesProj_closeOpt hCap (some planFd)) fun _ =>
                          preservesProj_bind (preservesProj_closeOpt hCap (some hostsFd)) fun _ =>
                            preservesProj_bind (preservesProj_closeOpt hCap (some initFd)) fun _ => hClStd
                      refine preserves_bind_eq hEq hWf hPipe fun rSt s hEq => ?_
                      cases rSt with
                      | error e => dsimp only; exact preserves_err_eq hEq hWf hClBase (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                      | ok pSt =>
                        rcases pSt with ⟨statusR, statusW⟩
                        dsimp only
                        refine preserves_bind_eq hEq hWf hPipe fun rGo s hEq => ?_
                        cases rGo with
                        | error e =>
                          dsimp only
                          refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some statusR)) fun _ s hEq => ?_
                          refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some statusW)) fun _ s hEq => ?_
                          exact preserves_err_eq hEq hWf hClBase (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                        | ok pGo =>
                          rcases pGo with ⟨goR, goW⟩
                          dsimp only
                          refine preserves_bind_eq hEq hWf (preservesProj_allocCtrlSocketpair hCap pslot.plan.portForwards.size eintrFuel) fun rCtrl s hEq => ?_
                          cases rCtrl with
                          | error e =>
                            dsimp only
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some goR)) fun _ s hEq => ?_
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some goW)) fun _ s hEq => ?_
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some statusR)) fun _ s hEq => ?_
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some statusW)) fun _ s hEq => ?_
                            exact preserves_err_eq hEq hWf hClBase (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_ioError_ne_empty e _))
                          | ok ctrlPair? =>
                            dsimp only
                            have hClPre : PreservesProj proj (do
                                Files.closeOpt cap.files (ctrlPair?.map Prod.fst); Files.closeOpt cap.files (ctrlPair?.map Prod.snd)
                                Files.closeOpt cap.files (some goR); Files.closeOpt cap.files (some goW)
                                Files.closeOpt cap.files (some statusR); Files.closeOpt cap.files (some statusW)
                                do
                                  Files.closeOpt cap.files (some planFd); Files.closeOpt cap.files (some hostsFd); Files.closeOpt cap.files (some initFd)
                                  do
                                    Files.closeOpt cap.files (some inR); Files.closeOpt cap.files (some inW)
                                    Files.closeOpt cap.files (some outR); Files.closeOpt cap.files (some outW)
                                    Files.closeOpt cap.files (some errR); Files.closeOpt cap.files (some errW)) :=
                              preservesProj_bind (preservesProj_closeOpt hCap (ctrlPair?.map Prod.fst)) fun _ =>
                                preservesProj_bind (preservesProj_closeOpt hCap (ctrlPair?.map Prod.snd)) fun _ =>
                                  preservesProj_bind (preservesProj_closeOpt hCap (some goR)) fun _ =>
                                    preservesProj_bind (preservesProj_closeOpt hCap (some goW)) fun _ =>
                                      preservesProj_bind (preservesProj_closeOpt hCap (some statusR)) fun _ =>
                                        preservesProj_bind (preservesProj_closeOpt hCap (some statusW)) fun _ => hClBase
                            refine preserves_bind_eq hEq hWf (preservesProj_of_seqUnit _ fun u hu => (hCap u .procGetpid hu).2) fun rPid s hEq => ?_
                            cases rPid with
                            | error e => dsimp only; exact preserves_err_eq hEq hWf hClPre (fun s' hEq' => hErrSame s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                            | ok hostPid =>
                              dsimp only
                              rw [stateM_bind_run]
                              have hWfS : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                              have ⟨hSeqProj, hWfSeq⟩ := tbl_nextCgSeq_spec hCap hWfS
                              let seq := ((toHostTableOps cap).nextCgSeq.run s).1
                              let sSeq := ((toHostTableOps cap).nextCgSeq.run s).2
                              let targetSeq : RawHostWorld := { proj w with table := { (proj w).table with cgSeq := (proj w).table.cgSeq + 1 } }
                              have hEqSeq : proj sSeq = targetSeq := by simpa [sSeq, targetSeq, hEq] using hSeqProj
                              have hWfT : rawHostWorldWf targetSeq = true := by rw [← hEqSeq]; exact hWfSeq
                              have hErrSeq : ∀ (u : W) (e : SandboxError), proj u = targetSeq → e.message ≠ "" → Q (.error e) u := fun u e hu hm =>
                                hErrValid u e hVal hKey (by rw [hu]; exact hWfT) (by rw [hu]) (by rw [hu]) (by rw [hu]) (by rw [hu]) (by rw [hu]) hm
                              refine preserves_bind_eq (w := sSeq) hEqSeq hWfT (preservesProj_createSiblingCgroup hCap hostPid seq eintrFuel) fun rCg s hEq => ?_
                              cases rCg with
                              | error e => dsimp only; exact preserves_err_eq hEq hWfT hClPre (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                              | ok cgDir =>
                                dsimp only
                                refine preserves_bind_eq hEq hWfT (preservesProj_setupSpawnCgroupLimits hCap cgDir pslot.plan.limits eintrFuel) fun rCfg s hEq => ?_
                                cases rCfg with
                                | some em =>
                                  rcases em with ⟨e, msg⟩
                                  dsimp only
                                  refine preserves_bind_eq hEq hWfT hClPre fun _ s hEq => ?_
                                  exact preserves_err_eq hEq hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel)
                                    (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ msg))
                                | none =>
                                  dsimp only
                                  refine preserves_bind_eq hEq hWfT (preservesProj_of_seqUnit _ fun u hu => (hCap u (.postForkSpawnWithBarrier _) hu).2) fun rSp s hEq => ?_
                                  cases rSp with
                                  | error pfErr =>
                                    dsimp only
                                    refine preserves_bind_eq hEq hWfT hClPre fun _ s hEq => ?_
                                    exact preserves_err_eq hEq hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel)
                                      (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                                  | ok pending =>
                                    dsimp only
                                    have hClChild : PreservesProj proj (do
                                        Files.closeOpt cap.files (some initFd); Files.closeOpt cap.files (some hostsFd); Files.closeOpt cap.files (some planFd)
                                        Files.closeOpt cap.files (some inR); Files.closeOpt cap.files (some outW); Files.closeOpt cap.files (some errW)
                                        Files.closeOpt cap.files (some statusW); Files.closeOpt cap.files (some goR); Files.closeOpt cap.files (ctrlPair?.map Prod.snd)) :=
                                      preservesProj_bind (preservesProj_closeOpt hCap (some initFd)) fun _ =>
                                        preservesProj_bind (preservesProj_closeOpt hCap (some hostsFd)) fun _ =>
                                          preservesProj_bind (preservesProj_closeOpt hCap (some planFd)) fun _ =>
                                            preservesProj_bind (preservesProj_closeOpt hCap (some inR)) fun _ =>
                                              preservesProj_bind (preservesProj_closeOpt hCap (some outW)) fun _ =>
                                                preservesProj_bind (preservesProj_closeOpt hCap (some errW)) fun _ =>
                                                  preservesProj_bind (preservesProj_closeOpt hCap (some statusW)) fun _ =>
                                                    preservesProj_bind (preservesProj_closeOpt hCap (some goR)) fun _ =>
                                                      preservesProj_closeOpt hCap (ctrlPair?.map Prod.snd)
                                    have hClPar : PreservesProj proj (do
                                        Files.closeOpt cap.files (some inW); Files.closeOpt cap.files (some outR); Files.closeOpt cap.files (some errR)
                                        Files.closeOpt cap.files (some statusR); Files.closeOpt cap.files (some goW); Files.closeOpt cap.files (ctrlPair?.map Prod.fst)) :=
                                      preservesProj_bind (preservesProj_closeOpt hCap (some inW)) fun _ =>
                                        preservesProj_bind (preservesProj_closeOpt hCap (some outR)) fun _ =>
                                          preservesProj_bind (preservesProj_closeOpt hCap (some errR)) fun _ =>
                                            preservesProj_bind (preservesProj_closeOpt hCap (some statusR)) fun _ =>
                                              preservesProj_bind (preservesProj_closeOpt hCap (some goW)) fun _ =>
                                                preservesProj_closeOpt hCap (ctrlPair?.map Prod.fst)
                                    refine preserves_bind_eq hEq hWfT (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun u hu => (hCap u (.procPidfdOpen pending.pid {}) hu).2) eintrFuel) fun rPfd s hEq => ?_
                                    cases rPfd with
                                    | error e =>
                                      dsimp only
                                      refine preserves_bind_eq hEq hWfT (preservesProj_of_seqUnit _ fun u hu => (hCap u (.postForkAbortBarrier pending) hu).2) fun _ s hEq => ?_
                                      refine preserves_bind_eq hEq hWfT hClChild fun _ s hEq => ?_
                                      refine preserves_bind_eq hEq hWfT hClPar fun _ s hEq => ?_
                                      exact preserves_err_eq hEq hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel)
                                        (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                                    | ok pidfd =>
                                      dsimp only
                                      refine preserves_bind_eq hEq hWfT (preservesProj_writeTextFile hCap _ (toString pending.pid) eintrFuel) fun rWcg s hEq => ?_
                                      cases rWcg with
                                      | error e =>
                                        dsimp only
                                        refine preserves_bind_eq hEq hWfT (preservesProj_of_seqUnit _ fun u hu => (hCap u (.postForkAbortBarrier pending) hu).2) fun _ s hEq => ?_
                                        refine preserves_bind_eq hEq hWfT (preservesProj_closeOpt hCap (some pidfd)) fun _ s hEq => ?_
                                        refine preserves_bind_eq hEq hWfT hClChild fun _ s hEq => ?_
                                        refine preserves_bind_eq hEq hWfT hClPar fun _ s hEq => ?_
                                        exact preserves_err_eq hEq hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel)
                                          (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                                      | ok _ =>
                                        dsimp only
                                        refine preserves_bind_eq hEq hWfT (preservesProj_of_seqUnit _ fun u hu => (hCap u (.postForkReleaseBarrier pending) hu).2) fun rRel s hEq => ?_
                                        refine preserves_bind_eq hEq hWfT hClChild fun _ s hEq => ?_
                                        cases rRel with
                                        | error pfErr =>
                                          dsimp only
                                          refine preserves_bind_eq hEq hWfT (preservesProj_closeOpt hCap (some pidfd)) fun _ s hEq => ?_
                                          refine preserves_bind_eq hEq hWfT hClPar fun _ s hEq => ?_
                                          exact preserves_err_eq hEq hWfT (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel)
                                            (fun s' hEq' => hErrSeq s' _ hEq' (mapRawError_unavail_ne_empty _ _))
                                        | ok child =>
                                          dsimp only
                                          have hRoll : ∀ (s : W) (e : SandboxError), proj s = targetSeq → e.message ≠ "" →
                                              let tail : StateM W (Except SandboxError BoxHandle) := do
                                                Files.closeOpt cap.files (some inW); Files.closeOpt cap.files (some outR)
                                                Files.closeOpt cap.files (some errR); Files.closeOpt cap.files (some statusR)
                                                Files.closeOpt cap.files (some goW)
                                                rollbackRunningChild cap.files cap.proc cap.timeRand child.pid (some pidfd) cgDir eintrFuel
                                                pure (.error e)
                                              Q (tail.run s).1 (tail.run s).2 := by
                                            intro s e hs hm
                                            dsimp only
                                            refine preserves_bind_eq hs hWfT (preservesProj_closeOpt hCap (some inW)) fun _ s hs => ?_
                                            refine preserves_bind_eq hs hWfT (preservesProj_closeOpt hCap (some outR)) fun _ s hs => ?_
                                            refine preserves_bind_eq hs hWfT (preservesProj_closeOpt hCap (some errR)) fun _ s hs => ?_
                                            refine preserves_bind_eq hs hWfT (preservesProj_closeOpt hCap (some statusR)) fun _ s hs => ?_
                                            refine preserves_bind_eq hs hWfT (preservesProj_closeOpt hCap (some goW)) fun _ s hs => ?_
                                            exact preserves_err_eq hs hWfT (preservesProj_rollbackRunningChild hCap child.pid (some pidfd) cgDir eintrFuel)
                                              (fun s' hs' => hErrSeq s' e hs' hm)
                                          refine preserves_bind_eq hEq hWfT (preservesProj_recvPortListenerFds hCap (ctrlPair?.map Prod.fst) statusR pslot.plan.portForwards.size) fun rLst s hEq => ?_
                                          cases rLst with
                                          | error e =>
                                            dsimp only
                                            refine preserves_bind_eq hEq hWfT (preservesProj_drainStderrSnippet hCap errR 255 16) fun snip s hEq => ?_
                                            exact hRoll s _ hEq (mapRawError_unavail_ne_empty _ _)
                                          | ok listenerFds =>
                                            dsimp only
                                            refine preserves_bind_eq hEq hWfT (preservesProj_readInitStatusBlocking hCap statusR ByteArray.empty 64) fun rMsg s hEq => ?_
                                            rcases rMsg with ⟨msg?, readErr?⟩
                                            cases msg? with
                                            | none =>
                                              dsimp only
                                              refine preserves_bind_eq hEq hWfT (preservesProj_drainStderrSnippet hCap errR 255 16) fun snip s hEq => ?_
                                              refine preserves_bind_eq hEq hWfT (preservesProj_closeFdArray hCap listenerFds) fun _ s hEq => ?_
                                              exact hRoll s _ hEq (mapRawError_unavail_ne_empty _ _)
                                            | some msg =>
                                              dsimp only
                                              cases hReady : (msg.kind == PS_STATUS_READY) with
                                              | true =>
                                                simp only [↓reduceIte]
                                                cases hBadPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || child.pgid.getD child.pid == 0 || child.pgid.getD child.pid > LinuxSyscall.Process.MAX_LINUX_PID) with
                                                | true =>
                                                  simp only [↓reduceIte]
                                                  refine preserves_bind_eq hEq hWfT (preservesProj_closeFdArray hCap listenerFds) fun _ s hEq => ?_
                                                  exact hRoll s _ hEq (mapRawError_unavail_ne_empty _ _)
                                                | false =>
                                                  simp only [Bool.false_eq_true, ↓reduceIte]
                                                  let pgid := child.pgid.getD child.pid
                                                  have hPidPos : 0 < Int.ofNat child.pid.toNat := by
                                                    have hNe0 : child.pid ≠ 0 := by intro hz; simp [hz] at hBadPid
                                                    have hNatPos : 0 < child.pid.toNat :=
                                                      Nat.pos_of_ne_zero fun hz => by
                                                        have hEqU := @UInt32.ofNat_toNat child.pid
                                                        rw [hz] at hEqU
                                                        exact hNe0 hEqU.symm
                                                    simp only [Int.ofNat_eq_natCast]; omega
                                                  have hPgidPos : 0 < Int.ofNat pgid.toNat := by
                                                    have hNe0 : pgid ≠ 0 := by intro hz; simp [pgid, hz] at hBadPid
                                                    have hNatPos : 0 < pgid.toNat :=
                                                      Nat.pos_of_ne_zero fun hz => by
                                                        have hEqU := @UInt32.ofNat_toNat pgid
                                                        rw [hz] at hEqU
                                                        exact hNe0 hEqU.symm
                                                    simp only [Int.ofNat_eq_natCast]; omega
                                                  let bslot : BoxSlotM Nat :=
                                                    { pid := child.pid, pgid := pgid, pidfd := pidfd,
                                                      stdinFd? := some inW, stdoutFd? := some outR, stderrFd? := some errR,
                                                      statusFd? := some statusR, goFd? := some goW,
                                                      listenerFds := listenerFds, cgroupDir := cgDir,
                                                      program := pslot.plan.program, cwd := pslot.plan.cwd }
                                                  rw [stateM_bind_run]
                                                  have hIns := tbl_insertBox_spec hCap (by rw [hEq]; exact hWfT) bslot
                                                  rcases hIns with ⟨hWfB, hLB, hTB, hPlB, hFwB, hBody⟩
                                                  cases hR : (((toHostTableOps cap).insertBox bslot).run s).1 with
                                                  | none =>
                                                    rw [hR] at hBody
                                                    refine preserves_bind_eq (hBody.trans hEq) hWfT (preservesProj_closeFdArray hCap listenerFds) fun _ s hEq => ?_
                                                    exact hRoll s _ hEq (mapRawError_ioError_ne_empty Errno.ENOMEM _)
                                                  | some bhid =>
                                                    rw [hR] at hBody
                                                    rcases hBody with ⟨hHidV, hHidEq, hLen⟩
                                                    simp only [stateM_pure_run]
                                                    refine ⟨hWfB, by simpa [hEq, targetSeq] using hLB, by simpa [hEq, targetSeq] using hTB,
                                                      by simpa [hEq, targetSeq] using hPlB, by simpa [hEq, targetSeq] using hFwB,
                                                      hVal, hKey, hHidV, by simpa [hEq, targetSeq] using hHidEq,
                                                      hPidPos, hPgidPos, rfl, by simpa [hEq, targetSeq] using hLen⟩
                                              | false =>
                                                simp only [Bool.false_eq_true, ↓reduceIte]
                                                refine preserves_bind_eq hEq hWfT (preservesProj_drainStderrSnippet hCap errR 255 16) fun snip s hEq => ?_
                                                refine preserves_bind_eq hEq hWfT (preservesProj_closeFdArray hCap listenerFds) fun _ s hEq => ?_
                                                exact hRoll s _ hEq (mapRawError_unavail_ne_empty _ _)

end LeanSwe.ProcessSandbox.Raw.Proofs

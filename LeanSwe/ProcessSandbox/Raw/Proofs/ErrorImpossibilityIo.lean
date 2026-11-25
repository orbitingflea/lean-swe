import Core.Assumptions
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Proofs.EncodePlan
import LeanSwe.ProcessSandbox.Raw.Proofs.IoTotalHelpers

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

private theorem ioTotal_waitProbeExitZero {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (pid : Int32) : ∀ fuel, IoTotal (waitProbeExitZero deps.proc pid fuel)
  | 0 => ioTotal_pure _
  | fuel + 1 => by
    unfold waitProbeExitZero
    refine ioTotal_bind (hc.waitpid pid {}) fun r => ?_
    cases r with
    | ok wr =>
      cases wr with
      | exited _ c => exact if h : c = 0 then by simp [h]; exact ioTotal_pure _ else by simp [h]; exact ioTotal_pure _
      | _ => exact ioTotal_pure _
    | error _ => exact ioTotal_ite (ioTotal_waitProbeExitZero hc pid fuel) (ioTotal_pure _)

/-- `probeBwrapNamespaces` is total under `SysDepsTotal`. -/
theorem ioTotal_probeBwrapNamespaces {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (bw : String) (ib : ByteArray) (fuel : Nat) :
    IoTotal (probeBwrapNamespaces deps.files deps.sandbox deps.proc deps.postFork bw ib fuel) := by
  have hOpen3 : IoTotal (openThreeDevNull deps.files fuel) := by
    unfold openThreeDevNull
    have h1 := ioTotal_retryEintr (hc.openat none "/dev/null".toUTF8 { access := .rdwr, cloexec := true } 0) fuel
    refine ioTotal_bind h1 fun r0 => ?_
    cases r0 with
    | error _ => exact ioTotal_pure _
    | ok d0 =>
      refine ioTotal_bind h1 fun r1 => ?_
      cases r1 with
      | error _ => exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) (fun _ => ioTotal_pure _)
      | ok d1 =>
        refine ioTotal_bind h1 fun r2 => ?_
        cases r2 with
        | error _ =>
          exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
            ioTotal_bind (ioTotal_closeOpt hc (some d1)) (fun _ => ioTotal_pure _)
        | ok _ => exact ioTotal_pure _
  unfold probeBwrapNamespaces
  refine ioTotal_bind hOpen3 fun r3 => ?_
  cases r3 with
  | error _ => exact ioTotal_pure _
  | ok ds =>
    rcases ds with ⟨d0, d1, d2⟩
    refine ioTotal_bind (ioTotal_createSealedMemfd hc _ ib fuel) fun rM => ?_
    cases rM with
    | error _ =>
      exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
        ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ =>
          ioTotal_bind (ioTotal_closeOpt hc (some d2)) (fun _ => ioTotal_pure _)
    | ok mfd =>
      refine ioTotal_bind (ioTotal_retryEintr (hc.reopenReadOnly mfd) fuel) fun rRo => ?_
      refine ioTotal_bind (ioTotal_closeOpt hc (some mfd)) fun _ => ?_
      cases rRo with
      | error _ =>
        exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
          ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ =>
            ioTotal_bind (ioTotal_closeOpt hc (some d2)) (fun _ => ioTotal_pure _)
      | ok ifd =>
        refine ioTotal_bind (ioTotal_discoverSystemEntries hc fuel) fun sysEs => ?_
        have hAfterLd (hasLd : Bool) : IoTotal (do
            let childSpec : PostFork.ChildSpecM fd := {
              path := bw
              argv := buildProbeBwrapArgv bw sysEs hasLd ifd
              stdio := .redirect (.handle d0) (.handle d1) (.handle d2) false
              fdPolicy := .closeAllAbove2Except #[.handle ifd]
              processGroup := .newGroup
              sigpipe := .resetDefault
              forkMode := .immortalThread
            }
            let spawnRes ← deps.postFork.spawn childSpec
            Files.closeOpt deps.files (some d0)
            Files.closeOpt deps.files (some d1)
            Files.closeOpt deps.files (some d2)
            Files.closeOpt deps.files (some ifd)
            match spawnRes with
            | .error pfErr => return .error (pfErr.errno.getD Errno.EPERM)
            | .ok child => waitProbeExitZero deps.proc child.pid.toInt32 fuel) := by
          refine ioTotal_bind (hc.pfSpawn _) fun rSp => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d2)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some ifd)) fun _ => ?_
          cases rSp with
          | error _ => exact ioTotal_pure _
          | ok child => exact ioTotal_waitProbeExitZero hc child.pid.toInt32 fuel
        refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none "/etc/ld.so.cache".toUTF8 {}) fuel) fun rLd => ?_
        cases rLd with
        | ok _ => exact ioTotal_bind (ioTotal_pure true) hAfterLd
        | error _ => exact ioTotal_bind (ioTotal_pure false) hAfterLd

private theorem ioTotal_waitpidReapLoop {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (pid : Int32) :
    ∀ fuel, IoTotal (LinuxSyscall.Process.waitpidReapLoop deps.proc pid fuel)
  | 0 => ioTotal_pure _
  | fuel + 1 => by
    unfold LinuxSyscall.Process.waitpidReapLoop
    refine ioTotal_bind (hc.waitpid pid {}) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_pure _
    | error _ =>
      exact ioTotal_ite (ioTotal_waitpidReapLoop hc pid fuel) (ioTotal_ite (ioTotal_pure _) (ioTotal_pure _))

private theorem preflightPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl)
    (fuel : Nat) (req : PreflightReq) (emb : Except String ByteArray) :
    IoSafeErr (· = .unavailable) (preflightPure deps tbl fuel req emb) := by
  unfold preflightPure
  refine ioSafeErr_ite (ioSafeErr_err rfl) (ioSafeErr_ite (ioSafeErr_err rfl) ?_)
  refine ioSafeErr_bind (ioTotal_resolveBwrapPath hc fuel) fun bw? => ?_
  cases bw? with
  | none => exact ioSafeErr_err rfl
  | some bw =>
    refine ioSafeErr_bind (hc.landlockCreateRuleset _ _) fun rLl => ?_
    cases rLl with
    | error _ => exact ioSafeErr_err rfl
    | ok cr =>
      cases cr with
      | ruleset h => exact ioSafeErr_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioSafeErr_err rfl)
      | version _ =>
        refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
        refine ioSafeErr_bind (hc.seccomp _ {} ByteArray.empty) fun rSc => ?_
        cases rSc with
        | error _ => exact ioSafeErr_err rfl
        | ok _ =>
          cases emb with
          | error _ => exact ioSafeErr_err rfl
          | ok ib =>
            refine ioSafeErr_bind (ioTotal_probeBwrapNamespaces hc bw ib fuel) fun rPb => ?_
            cases rPb with
            | error _ => exact ioSafeErr_err rfl
            | ok _ =>
              refine ioSafeErr_bind hc.getpid fun rPid => ?_
              cases rPid with
              | error _ => exact ioSafeErr_err rfl
              | ok pid =>
                refine ioSafeErr_bind ht.nextCgSeq fun seq => ?_
                refine ioSafeErr_bind (ioTotal_createSiblingCgroup hc pid seq fuel) fun rCg => ?_
                cases rCg with
                | error _ => exact ioSafeErr_err rfl
                | ok cgDir =>
                  have hFinish (fail? : Option (Errno × String)) :
                      IoSafeErr (· = .unavailable) (do
                        let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
                        match fail? with
                        | some (e, msg) => return .error (Internal.mapRawError (.unavailable (some e) msg))
                        | none => return .ok ()) := by
                    refine ioSafeErr_bind (ioTotal_cleanupCgroupDir hc cgDir _ _ fuel) fun _ => ?_
                    cases fail? with
                    | none => exact ioSafeErr_ok ()
                    | some em => rcases em with ⟨_, _⟩; exact ioSafeErr_err rfl
                  have hAfterMem (mf : Option (Errno × String)) :
                      IoSafeErr (· = .unavailable) (do
                        let fail? ← match mf with
                          | some f => pure (some f)
                          | none =>
                            if req.needPidsCgroup then
                              match ← configureCgroupPids deps.files cgDir "max" fuel with
                              | .ok () => pure none
                              | .error e => pure (some (e, "direct cgroup v2 pids controller unavailable"))
                            else pure none
                        let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
                        match fail? with
                        | some (e, msg) => return .error (Internal.mapRawError (.unavailable (some e) msg))
                        | none => return .ok ()) := by
                    cases mf with
                    | some f => exact ioSafeErr_bind (ioTotal_pure (some f)) hFinish
                    | none =>
                      cases req.needPidsCgroup with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact ioSafeErr_bind (ioTotal_pure none) hFinish
                      | true =>
                        simp only [↓reduceIte]
                        refine ioSafeErr_bind (ioTotal_writeTextFile hc _ "max" fuel) fun rP => ?_
                        cases rP with
                        | ok _ => exact ioSafeErr_bind (ioTotal_pure none) hFinish
                        | error e => exact ioSafeErr_bind (ioTotal_pure (some (e, _))) hFinish
                  refine ioSafeErr_bind (ioTotal_retryEintr (hc.faccessat none _ _ {}) fuel) fun rK => ?_
                  cases rK with
                  | error e => exact ioSafeErr_bind (ioTotal_pure (some (e, _))) hFinish
                  | ok _ =>
                    refine ioSafeErr_bind (ioTotal_retryEintr (hc.faccessat none _ _ {}) fuel) fun rE => ?_
                    cases rE with
                    | error e => exact ioSafeErr_bind (ioTotal_pure (some (e, _))) hFinish
                    | ok _ =>
                      cases req.needMemoryCgroup with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact ioSafeErr_bind (ioTotal_pure none) hAfterMem
                      | true =>
                        simp only [↓reduceIte]
                        refine ioSafeErr_bind (ioTotal_configureCgroupMemory hc cgDir "max" fuel) fun rM => ?_
                        cases rM with
                        | ok _ => exact ioSafeErr_bind (ioTotal_pure none) hAfterMem
                        | error fe =>
                          rcases fe with ⟨_, _⟩
                          exact ioSafeErr_bind (ioTotal_pure (some _)) hAfterMem

private theorem preflight_safe (req : PreflightReq) :
    IoSafeErr (· = .unavailable) (LeanSwe.ProcessSandbox.Raw.preflight req) := by
  dsimp only [LeanSwe.ProcessSandbox.Raw.preflight, LeanSwe.ProcessSandbox.Raw.defaultOps,
    Internal.mkFullOpsM, Driver.mkFullOpsM, Driver.mkFullOpsWithPlatformM, mkRawOpsM]
  exact preflightPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _)
    DEFAULT_EINTR_FUEL req embeddedInitBytes

private theorem discoverHostPresetPure_safe {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fuel : Nat) :
    IoSafeErr (· = .unavailable) (discoverHostPresetPure deps fuel) := by
  unfold discoverHostPresetPure
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  exact ioSafeErr_bind (ioTotal_discoverHostPresetM hc _) (fun p => ioSafeErr_ok p)

private theorem discoverHostPreset_safe :
    IoSafeErr (· = .unavailable) LeanSwe.ProcessSandbox.Raw.discoverHostPreset :=
  discoverHostPresetPure_safe (mkSafeSysDepsM_total _ _ _) DEFAULT_EINTR_FUEL

private theorem sealPlanPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl)
    (fuel : Nat) (plan : CompiledSandboxPlan) (seccompBytes : ByteArray)
    (emb : Except String ByteArray) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .unavailable ∨ k = .ioError)
      (sealPlanPure deps tbl fuel plan seccompBytes emb) := by
  unfold sealPlanPure
  have hInv := encodePlan_inv plan seccompBytes
  cases hEnc : Internal.encodePlan plan seccompBytes with
  | error e =>
    rw [hEnc] at hInv
    exact ioSafeErr_err (Or.inl hInv.1)
  | ok wire =>
    dsimp only
    refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
    refine ioSafeErr_ite (ioSafeErr_err (Or.inr (Or.inl rfl))) ?_
    cases emb with
    | error _ => exact ioSafeErr_err (Or.inr (Or.inl rfl))
    | ok ib =>
      refine ioSafeErr_bind (ioTotal_createSealedMemfd hc _ wire fuel) fun r1 => ?_
      cases r1 with
      | error _ => exact ioSafeErr_err (Or.inr (Or.inr rfl))
      | ok m1 =>
        refine ioSafeErr_bind (ioTotal_createSealedMemfd hc _ ib fuel) fun r2 => ?_
        cases r2 with
        | error _ => exact ioSafeErr_bind (ioTotal_closeOpt hc (some m1)) (fun _ => ioSafeErr_err (Or.inr (Or.inr rfl)))
        | ok m2 =>
          refine ioSafeErr_bind (ioTotal_createSealedMemfd hc _ SYNTHETIC_HOSTS_BYTES fuel) fun r3 => ?_
          cases r3 with
          | error _ =>
            exact ioSafeErr_bind (ioTotal_closeOpt hc (some m1)) fun _ =>
              ioSafeErr_bind (ioTotal_closeOpt hc (some m2)) (fun _ => ioSafeErr_err (Or.inr (Or.inr rfl)))
          | ok m3 =>
            refine ioSafeErr_bind (ht.insertPlan _) fun hid? => ?_
            cases hid? with
            | some hid => exact ioSafeErr_ok ({ handleId := hid } : PlanHandle)
            | none =>
              exact ioSafeErr_bind (ioTotal_closeOpt hc (some m1)) fun _ =>
                ioSafeErr_bind (ioTotal_closeOpt hc (some m2)) fun _ =>
                  ioSafeErr_bind (ioTotal_closeOpt hc (some m3)) (fun _ => ioSafeErr_err (Or.inr (Or.inr rfl)))

private theorem sealPlan_safe (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .unavailable ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.sealPlan plan seccompBytes) := by
  dsimp only [LeanSwe.ProcessSandbox.Raw.sealPlan, LeanSwe.ProcessSandbox.Raw.defaultOps,
    Internal.mkFullOpsM, Driver.mkFullOpsM, Driver.mkFullOpsWithPlatformM, mkRawOpsM]
  exact sealPlanPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _)
    DEFAULT_EINTR_FUEL plan seccompBytes embeddedInitBytes

private theorem closePlanPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (ph : PlanHandle) :
    IoSafeErr (· = .invalidInput) (closePlanPure deps tbl ph) := by
  unfold closePlanPure
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  refine ioSafeErr_bind (ht.detachPlan _) fun slot? => ?_
  cases slot? with
  | none => exact ioSafeErr_err rfl
  | some slot =>
    exact ioSafeErr_bind (ioTotal_closeOpt hc (some slot.planMemfd)) fun _ =>
      ioSafeErr_bind (ioTotal_closeOpt hc (some slot.initMemfd)) fun _ =>
        ioSafeErr_bind (ioTotal_closeOpt hc (some slot.hostsMemfd)) (fun _ => ioSafeErr_ok ())

private theorem closePlan_safe (ph : PlanHandle) :
    IoSafeErr (· = .invalidInput) (LeanSwe.ProcessSandbox.Raw.closePlan ph) :=
  closePlanPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _) ph

private theorem startPortForwardersPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (bh : BoxHandle) (fwds : Array PortForward) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (startPortForwardersPure deps tbl bh fwds) := by
  unfold startPortForwardersPure
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ht.takeBoxListeners _ _) fun lfds? => ?_
  cases lfds? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some lfds =>
    refine ioSafeErr_bind (hc.startFwdTask lfds _) fun rStart => ?_
    cases rStart with
    | error _ => exact ioSafeErr_bind (ioTotal_closeFdArray hc lfds) (fun _ => ioSafeErr_err (Or.inr rfl))
    | ok th =>
      refine ioSafeErr_bind (ht.insertFwd _) fun fhid? => ?_
      cases fhid? with
      | none => exact ioSafeErr_bind (hc.stopFwdTask th) (fun _ => ioSafeErr_err (Or.inr rfl))
      | some fhid => exact ioSafeErr_ok ({ handleId := fhid, boxHandleId := bh.handleId } : PortForwarderHandle)

private theorem startPortForwarders_safe (bh : BoxHandle) (fwds : Array PortForward) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.startPortForwarders bh fwds) :=
  startPortForwardersPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _) bh fwds

private theorem stopPortForwardersPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (fh : PortForwarderHandle) :
    IoSafeErr (· = .invalidInput) (stopPortForwardersPure deps tbl fh) := by
  unfold stopPortForwardersPure
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  refine ioSafeErr_bind (ht.detachFwd _) fun slot? => ?_
  cases slot? with
  | none => exact ioSafeErr_err rfl
  | some slot => exact ioSafeErr_bind (hc.stopFwdTask slot.taskHandle) (fun _ => ioSafeErr_ok ())

private theorem stopPortForwarders_safe (fh : PortForwarderHandle) :
    IoSafeErr (· = .invalidInput) (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) :=
  stopPortForwardersPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _) fh

private theorem killProcessGroupPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (fuel : Nat) (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (killProcessGroupPure deps tbl fuel bh) := by
  unfold killProcessGroupPure
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ht.findBoxKillInfo _) fun info? => ?_
  cases info? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some p =>
    rcases p with ⟨pgid, _⟩
    unfold killBoxPg
    refine ioSafeErr_ite (ioSafeErr_ok ()) ?_
    refine ioSafeErr_bind (ioTotal_retryEintr (hc.kill _ .sigkill) _) fun r => ?_
    cases r with
    | ok _ => exact ioSafeErr_ok ()
    | error _ => exact ioSafeErr_ite (ioSafeErr_ok ()) (ioSafeErr_err (Or.inr rfl))

private theorem killProcessGroup_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.killProcessGroup bh) :=
  killProcessGroupPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _)
    DEFAULT_EINTR_FUEL bh

private theorem pidfdKillPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (fuel : Nat) (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (pidfdKillPure deps tbl fuel bh) := by
  unfold pidfdKillPure
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ht.findBoxKillInfo _) fun info? => ?_
  cases info? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some p =>
    rcases p with ⟨_, pidfd⟩
    unfold killBoxPidfd
    refine ioSafeErr_bind (ioTotal_retryEintr (hc.pidfdSendSignal pidfd .sigkill {}) _) fun r => ?_
    cases r with
    | ok _ => exact ioSafeErr_ok ()
    | error _ => exact ioSafeErr_ite (ioSafeErr_ok ()) (ioSafeErr_err (Or.inr rfl))

private theorem pidfdKill_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.pidfdKill bh) :=
  pidfdKillPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _)
    DEFAULT_EINTR_FUEL bh

private theorem reapBoxPure_safe {fd fwdTask : Type}
    {deps : HostSysDepsM IO fd fwdTask} {tbl : HostTableOpsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ht : TableOpsTotal tbl) (fuel : Nat) (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (reapBoxPure deps tbl fuel bh) := by
  unfold reapBoxPure
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ht.detachBox _) fun slot? => ?_
  cases slot? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some bslot =>
    refine ioSafeErr_bind (ioTotal_closeOpt hc bslot.stdinFd?) fun _ => ?_
    refine ioSafeErr_bind (ioTotal_closeOpt hc bslot.stdoutFd?) fun _ => ?_
    refine ioSafeErr_bind (ioTotal_closeOpt hc bslot.stderrFd?) fun _ => ?_
    refine ioSafeErr_bind (ioTotal_closeOpt hc bslot.statusFd?) fun _ => ?_
    refine ioSafeErr_bind (ioTotal_closeOpt hc bslot.goFd?) fun _ => ?_
    refine ioSafeErr_bind (ioTotal_closeFdArray hc bslot.listenerFds) fun _ => ?_
    have hRest1 : IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError) (do
        Files.closeOpt deps.files (some bslot.pidfd)
        match ← cleanupCgroupDir deps.files deps.timeRand bslot.cgroupDir
            CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel with
        | .ok () => return .ok ()
        | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))) := by
      refine ioSafeErr_bind (ioTotal_closeOpt hc (some bslot.pidfd)) fun _ => ?_
      refine ioSafeErr_bind (ioTotal_cleanupCgroupDir hc bslot.cgroupDir _ _ _) fun rCl => ?_
      cases rCl with
      | ok _ => exact ioSafeErr_ok ()
      | error _ => exact ioSafeErr_err (Or.inr rfl)
    have hRest2 : IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
        (if bslot.pid > 0 && bslot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then do
          let _ ← LinuxSyscall.Process.waitpidReapLoop deps.proc bslot.pid.toInt32 fuel
          Files.closeOpt deps.files (some bslot.pidfd)
          match ← cleanupCgroupDir deps.files deps.timeRand bslot.cgroupDir
              CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel with
          | .ok () => return .ok ()
          | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))
        else do
          Files.closeOpt deps.files (some bslot.pidfd)
          match ← cleanupCgroupDir deps.files deps.timeRand bslot.cgroupDir
              CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel with
          | .ok () => return .ok ()
          | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))) :=
      ioSafeErr_ite (ioSafeErr_bind (ioTotal_waitpidReapLoop hc bslot.pid.toInt32 _) (fun _ => hRest1)) hRest1
    exact ioSafeErr_ite (ioSafeErr_bind (ioTotal_writeTextFile hc _ "1" _) (fun _ => hRest2)) hRest2

private theorem reapBox_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.reapBox bh) :=
  reapBoxPure_safe (mkSafeSysDepsM_total _ _ _) (mkCellTableOps_ioStateCell_total _)
    DEFAULT_EINTR_FUEL bh

/-- `preflight` never fails with `.invalidInput`. -/
theorem raw_preflight_never_invalidInput (req : PreflightReq) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .invalidInput (LeanSwe.ProcessSandbox.Raw.preflight req) w :=
  ioSafeErr_never (preflight_safe req) (by rintro _ rfl; decide) w

/-- `preflight` never fails with `.notFound`. -/
theorem raw_preflight_never_notFound (req : PreflightReq) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.preflight req) w :=
  ioSafeErr_never (preflight_safe req) (by rintro _ rfl; decide) w

/-- `preflight` never fails with `.permissionDenied`. -/
theorem raw_preflight_never_permissionDenied (req : PreflightReq) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.preflight req) w :=
  ioSafeErr_never (preflight_safe req) (by rintro _ rfl; decide) w

/-- `preflight` never fails with `.ioError`. -/
theorem raw_preflight_never_ioError (req : PreflightReq) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .ioError (LeanSwe.ProcessSandbox.Raw.preflight req) w :=
  ioSafeErr_never (preflight_safe req) (by rintro _ rfl; decide) w

/-- `discoverHostPreset` never fails with `.invalidInput`. -/
theorem raw_discoverHostPreset_never_invalidInput (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .invalidInput LeanSwe.ProcessSandbox.Raw.discoverHostPreset w :=
  ioSafeErr_never discoverHostPreset_safe (by rintro _ rfl; decide) w

/-- `discoverHostPreset` never fails with `.notFound`. -/
theorem raw_discoverHostPreset_never_notFound (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound LeanSwe.ProcessSandbox.Raw.discoverHostPreset w :=
  ioSafeErr_never discoverHostPreset_safe (by rintro _ rfl; decide) w

/-- `discoverHostPreset` never fails with `.permissionDenied`. -/
theorem raw_discoverHostPreset_never_permissionDenied (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied LeanSwe.ProcessSandbox.Raw.discoverHostPreset w :=
  ioSafeErr_never discoverHostPreset_safe (by rintro _ rfl; decide) w

/-- `discoverHostPreset` never fails with `.ioError`. -/
theorem raw_discoverHostPreset_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .ioError LeanSwe.ProcessSandbox.Raw.discoverHostPreset w :=
  ioSafeErr_never discoverHostPreset_safe (by rintro _ rfl; decide) w

/-- `sealPlan` never fails with `.notFound`. -/
theorem raw_sealPlan_never_notFound (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.sealPlan plan seccompBytes) w :=
  ioSafeErr_never (sealPlan_safe plan seccompBytes) (by rintro _ (rfl | rfl | rfl) <;> decide) w

/-- `sealPlan` never fails with `.permissionDenied`. -/
theorem raw_sealPlan_never_permissionDenied (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.sealPlan plan seccompBytes) w :=
  ioSafeErr_never (sealPlan_safe plan seccompBytes) (by rintro _ (rfl | rfl | rfl) <;> decide) w

/-- `closePlan` never fails with `.unavailable`. -/
theorem raw_closePlan_never_unavailable (ph : PlanHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.closePlan ph) w :=
  ioSafeErr_never (closePlan_safe ph) (by rintro _ rfl; decide) w

/-- `closePlan` never fails with `.notFound`. -/
theorem raw_closePlan_never_notFound (ph : PlanHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.closePlan ph) w :=
  ioSafeErr_never (closePlan_safe ph) (by rintro _ rfl; decide) w

/-- `closePlan` never fails with `.permissionDenied`. -/
theorem raw_closePlan_never_permissionDenied (ph : PlanHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.closePlan ph) w :=
  ioSafeErr_never (closePlan_safe ph) (by rintro _ rfl; decide) w

/-- `closePlan` never fails with `.ioError`. -/
theorem raw_closePlan_never_ioError (ph : PlanHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .ioError (LeanSwe.ProcessSandbox.Raw.closePlan ph) w :=
  ioSafeErr_never (closePlan_safe ph) (by rintro _ rfl; decide) w

/-- `startPortForwarders` never fails with `.unavailable`. -/
theorem raw_startPortForwarders_never_unavailable (bh : BoxHandle) (fwds : Array PortForward) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.startPortForwarders bh fwds) w :=
  ioSafeErr_never (startPortForwarders_safe bh fwds) (by rintro _ (rfl | rfl) <;> decide) w

/-- `startPortForwarders` never fails with `.notFound`. -/
theorem raw_startPortForwarders_never_notFound (bh : BoxHandle) (fwds : Array PortForward) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.startPortForwarders bh fwds) w :=
  ioSafeErr_never (startPortForwarders_safe bh fwds) (by rintro _ (rfl | rfl) <;> decide) w

/-- `startPortForwarders` never fails with `.permissionDenied`. -/
theorem raw_startPortForwarders_never_permissionDenied (bh : BoxHandle) (fwds : Array PortForward) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.startPortForwarders bh fwds) w :=
  ioSafeErr_never (startPortForwarders_safe bh fwds) (by rintro _ (rfl | rfl) <;> decide) w

/-- `stopPortForwarders` never fails with `.unavailable`. -/
theorem raw_stopPortForwarders_never_unavailable (fh : PortForwarderHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) w :=
  ioSafeErr_never (stopPortForwarders_safe fh) (by rintro _ rfl; decide) w

/-- `stopPortForwarders` never fails with `.notFound`. -/
theorem raw_stopPortForwarders_never_notFound (fh : PortForwarderHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) w :=
  ioSafeErr_never (stopPortForwarders_safe fh) (by rintro _ rfl; decide) w

/-- `stopPortForwarders` never fails with `.permissionDenied`. -/
theorem raw_stopPortForwarders_never_permissionDenied (fh : PortForwarderHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) w :=
  ioSafeErr_never (stopPortForwarders_safe fh) (by rintro _ rfl; decide) w

/-- `stopPortForwarders` never fails with `.ioError`. -/
theorem raw_stopPortForwarders_never_ioError (fh : PortForwarderHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .ioError (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) w :=
  ioSafeErr_never (stopPortForwarders_safe fh) (by rintro _ rfl; decide) w

/-- `killProcessGroup` never fails with `.unavailable`. -/
theorem raw_killProcessGroup_never_unavailable (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.killProcessGroup bh) w :=
  ioSafeErr_never (killProcessGroup_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `killProcessGroup` never fails with `.notFound`. -/
theorem raw_killProcessGroup_never_notFound (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.killProcessGroup bh) w :=
  ioSafeErr_never (killProcessGroup_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `killProcessGroup` never fails with `.permissionDenied`. -/
theorem raw_killProcessGroup_never_permissionDenied (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.killProcessGroup bh) w :=
  ioSafeErr_never (killProcessGroup_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `pidfdKill` never fails with `.unavailable`. -/
theorem raw_pidfdKill_never_unavailable (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.pidfdKill bh) w :=
  ioSafeErr_never (pidfdKill_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `pidfdKill` never fails with `.notFound`. -/
theorem raw_pidfdKill_never_notFound (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.pidfdKill bh) w :=
  ioSafeErr_never (pidfdKill_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `pidfdKill` never fails with `.permissionDenied`. -/
theorem raw_pidfdKill_never_permissionDenied (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.pidfdKill bh) w :=
  ioSafeErr_never (pidfdKill_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `reapBox` never fails with `.unavailable`. -/
theorem raw_reapBox_never_unavailable (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.reapBox bh) w :=
  ioSafeErr_never (reapBox_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `reapBox` never fails with `.notFound`. -/
theorem raw_reapBox_never_notFound (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.reapBox bh) w :=
  ioSafeErr_never (reapBox_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

/-- `reapBox` never fails with `.permissionDenied`. -/
theorem raw_reapBox_never_permissionDenied (bh : BoxHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.reapBox bh) w :=
  ioSafeErr_never (reapBox_safe bh) (by rintro _ (rfl | rfl) <;> decide) w

end LeanSwe.ProcessSandbox.Raw.Proofs

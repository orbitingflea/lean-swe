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

private theorem ioTotal_waitpidReapLoop {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (pid : Int32) : ∀ fuel, IoTotal (LinuxSyscall.Process.waitpidReapLoop cap.proc pid fuel)
  | 0 => ioTotal_pure _
  | fuel + 1 => by
    unfold LinuxSyscall.Process.waitpidReapLoop
    refine ioTotal_bind (hc.waitpid pid {}) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_pure _
    | error _ =>
      exact ioTotal_ite (ioTotal_waitpidReapLoop hc pid fuel) (ioTotal_ite (ioTotal_pure _) (ioTotal_pure _))

private theorem ioTotal_tblModify {α : Type} {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (f : Model.RawTableState → Model.RawTableState) (g : Model.RawTableState → α) :
    IoTotal (do let st ← cap.modifyTable f; return g st) :=
  ioTotal_bind (hc.modifyTable f) (fun st => ioTotal_pure (g st))

private theorem ioTotal_tblGet {α : Type} {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (g : Model.RawTableState → α) :
    IoTotal (do let st ← cap.getTable; return g st) :=
  ioTotal_bind hc.getTable (fun st => ioTotal_pure (g st))

private theorem preflightPure_safe {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) (req : PreflightReq) (emb : Except String ByteArray) :
    IoSafeErr (· = .unavailable) (preflightPure (toHostSysDeps cap) (toHostTableOps cap) fuel req emb) := by
  unfold preflightPure
  dsimp only [toHostSysDeps, toHostTableOps]
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
                refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun seq => ?_
                refine ioSafeErr_bind (ioTotal_createSiblingCgroup hc pid seq fuel) fun rCg => ?_
                cases rCg with
                | error _ => exact ioSafeErr_err rfl
                | ok cgDir =>
                  have hFinish (fail? : Option (Errno × String)) :
                      IoSafeErr (· = .unavailable) (do
                        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
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
                              match ← configureCgroupPids cap.files cgDir "max" fuel with
                              | .ok () => pure none
                              | .error e => pure (some (e, "direct cgroup v2 pids controller unavailable"))
                            else pure none
                        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
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
    IoSafeErr (· = .unavailable) (LeanSwe.ProcessSandbox.Raw.preflight req) :=
  preflightPure_safe sysBridge_defaultOps_total DEFAULT_EINTR_FUEL req embeddedInitBytes

private theorem discoverHostPreset_safe :
    IoSafeErr (· = .unavailable) LeanSwe.ProcessSandbox.Raw.discoverHostPreset := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (discoverHostPresetPure (toHostSysDeps SysBridge.defaultOps) DEFAULT_EINTR_FUEL)
  unfold discoverHostPresetPure
  dsimp only [toHostSysDeps]
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  exact ioSafeErr_bind (ioTotal_discoverHostPresetM hc _) (fun p => ioSafeErr_ok p)

private theorem sealPlanPure_safe {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) (plan : CompiledSandboxPlan) (seccompBytes : ByteArray)
    (emb : Except String ByteArray) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .unavailable ∨ k = .ioError)
      (sealPlanPure (toHostSysDeps cap) (toHostTableOps cap) fuel plan seccompBytes emb) := by
  unfold sealPlanPure
  dsimp only [toHostSysDeps, toHostTableOps]
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
            refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun hid? => ?_
            cases hid? with
            | some hid => exact ioSafeErr_ok ({ handleId := hid } : PlanHandle)
            | none =>
              exact ioSafeErr_bind (ioTotal_closeOpt hc (some m1)) fun _ =>
                ioSafeErr_bind (ioTotal_closeOpt hc (some m2)) fun _ =>
                  ioSafeErr_bind (ioTotal_closeOpt hc (some m3)) (fun _ => ioSafeErr_err (Or.inr (Or.inr rfl)))

private theorem sealPlan_safe (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .unavailable ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.sealPlan plan seccompBytes) :=
  sealPlanPure_safe sysBridge_defaultOps_total DEFAULT_EINTR_FUEL plan seccompBytes embeddedInitBytes

private theorem closePlan_safe (ph : PlanHandle) :
    IoSafeErr (· = .invalidInput) (LeanSwe.ProcessSandbox.Raw.closePlan ph) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (closePlanPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) ph)
  unfold closePlanPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun slot? => ?_
  cases slot? with
  | none => exact ioSafeErr_err rfl
  | some slot =>
    exact ioSafeErr_bind (ioTotal_closeOpt hc (some slot.planMemfd)) fun _ =>
      ioSafeErr_bind (ioTotal_closeOpt hc (some slot.initMemfd)) fun _ =>
        ioSafeErr_bind (ioTotal_closeOpt hc (some slot.hostsMemfd)) (fun _ => ioSafeErr_ok ())

private theorem startPortForwarders_safe (bh : BoxHandle) (fwds : Array PortForward) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.startPortForwarders bh fwds) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (startPortForwardersPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) bh fwds)
  unfold startPortForwardersPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun lfds? => ?_
  cases lfds? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some lfds =>
    refine ioSafeErr_bind (hc.startFwdTask lfds _) fun rStart => ?_
    cases rStart with
    | error _ => exact ioSafeErr_bind (ioTotal_closeFdArray hc lfds) (fun _ => ioSafeErr_err (Or.inr rfl))
    | ok th =>
      refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun fhid? => ?_
      cases fhid? with
      | none => exact ioSafeErr_bind (hc.stopFwdTask th) (fun _ => ioSafeErr_err (Or.inr rfl))
      | some fhid => exact ioSafeErr_ok ({ handleId := fhid, boxHandleId := bh.handleId } : PortForwarderHandle)

private theorem stopPortForwarders_safe (fh : PortForwarderHandle) :
    IoSafeErr (· = .invalidInput) (LeanSwe.ProcessSandbox.Raw.stopPortForwarders fh) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (stopPortForwardersPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) fh)
  unfold stopPortForwardersPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err rfl) ?_
  refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun slot? => ?_
  cases slot? with
  | none => exact ioSafeErr_err rfl
  | some slot => exact ioSafeErr_bind (hc.stopFwdTask slot.taskHandle) (fun _ => ioSafeErr_ok ())

private theorem killProcessGroup_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.killProcessGroup bh) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (killProcessGroupPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) DEFAULT_EINTR_FUEL bh)
  unfold killProcessGroupPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ioTotal_tblGet hc _) fun info? => ?_
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

private theorem pidfdKill_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.pidfdKill bh) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (pidfdKillPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) DEFAULT_EINTR_FUEL bh)
  unfold pidfdKillPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ioTotal_tblGet hc _) fun info? => ?_
  cases info? with
  | none => exact ioSafeErr_err (Or.inl rfl)
  | some p =>
    rcases p with ⟨_, pidfd⟩
    unfold killBoxPidfd
    refine ioSafeErr_bind (ioTotal_retryEintr (hc.pidfdSendSignal pidfd .sigkill {}) _) fun r => ?_
    cases r with
    | ok _ => exact ioSafeErr_ok ()
    | error _ => exact ioSafeErr_ite (ioSafeErr_ok ()) (ioSafeErr_err (Or.inr rfl))

private theorem reapBox_safe (bh : BoxHandle) :
    IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
      (LeanSwe.ProcessSandbox.Raw.reapBox bh) := by
  have hc := sysBridge_defaultOps_total
  show IoSafeErr _ (reapBoxPure (toHostSysDeps SysBridge.defaultOps) (toHostTableOps SysBridge.defaultOps) DEFAULT_EINTR_FUEL bh)
  unfold reapBoxPure
  dsimp only [toHostSysDeps, toHostTableOps]
  refine ioSafeErr_ite (ioSafeErr_err (Or.inl rfl)) ?_
  refine ioSafeErr_bind (ioTotal_tblModify hc _ _) fun slot? => ?_
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
        Files.closeOpt SysBridge.defaultOps.files (some bslot.pidfd)
        match ← cleanupCgroupDir SysBridge.defaultOps.files SysBridge.defaultOps.timeRand bslot.cgroupDir
            CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL with
        | .ok () => return .ok ()
        | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))) := by
      refine ioSafeErr_bind (ioTotal_closeOpt hc (some bslot.pidfd)) fun _ => ?_
      refine ioSafeErr_bind (ioTotal_cleanupCgroupDir hc bslot.cgroupDir _ _ _) fun rCl => ?_
      cases rCl with
      | ok _ => exact ioSafeErr_ok ()
      | error _ => exact ioSafeErr_err (Or.inr rfl)
    have hRest2 : IoSafeErr (fun k => k = .invalidInput ∨ k = .ioError)
        (if bslot.pid > 0 && bslot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then do
          let _ ← LinuxSyscall.Process.waitpidReapLoop SysBridge.defaultOps.proc bslot.pid.toInt32 DEFAULT_EINTR_FUEL
          Files.closeOpt SysBridge.defaultOps.files (some bslot.pidfd)
          match ← cleanupCgroupDir SysBridge.defaultOps.files SysBridge.defaultOps.timeRand bslot.cgroupDir
              CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL with
          | .ok () => return .ok ()
          | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))
        else do
          Files.closeOpt SysBridge.defaultOps.files (some bslot.pidfd)
          match ← cleanupCgroupDir SysBridge.defaultOps.files SysBridge.defaultOps.timeRand bslot.cgroupDir
              CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS DEFAULT_EINTR_FUEL with
          | .ok () => return .ok ()
          | .error e => return .error (Internal.mapRawError (.ioError none e "failed to remove box cgroup directory"))) :=
      ioSafeErr_ite (ioSafeErr_bind (ioTotal_waitpidReapLoop hc bslot.pid.toInt32 _) (fun _ => hRest1)) hRest1
    exact ioSafeErr_ite (ioSafeErr_bind (ioTotal_writeTextFile hc _ "1" _) (fun _ => hRest2)) hRest2

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

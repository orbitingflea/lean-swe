import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

/-- `recvFdsScm` preserves `proj`. -/
theorem preservesProj_recvFdsScm {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (ctrlFd statusFd : Nat) (expected : Nat) :
    ∀ got fuel, PreservesProj proj (recvFdsScmLoop cap.files cap.net cap.poll ctrlFd statusFd expected got fuel)
  | got, 0 => by
    unfold recvFdsScmLoop
    exact preservesProj_ite (preservesProj_pure _)
      (preservesProj_bind (preservesProj_closeFdArray hCap got) (fun _ => preservesProj_pure _))
  | got, fuel + 1 => by
    unfold recvFdsScmLoop
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.pollPpoll _ none) hWf).2) fun r => ?_
    cases r with
    | error _ =>
      exact preservesProj_ite (preservesProj_recvFdsScm hCap ctrlFd statusFd expected got fuel)
        (preservesProj_bind (preservesProj_closeFdArray hCap got) (fun _ => preservesProj_pure _))
    | ok _ =>
      refine preservesProj_ite ?_ ?_
      · refine preservesProj_bind
          (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.netRecvmsg ctrlFd _) hWf).2) fun rm => ?_
        cases rm with
        | error _ =>
          exact preservesProj_ite (preservesProj_recvFdsScm hCap ctrlFd statusFd expected got fuel)
            (preservesProj_bind (preservesProj_closeFdArray hCap got) (fun _ => preservesProj_pure _))
        | ok batch =>
          exact preservesProj_ite
            (preservesProj_bind (preservesProj_closeFdArray hCap batch) fun _ =>
              preservesProj_bind (preservesProj_closeFdArray hCap got) (fun _ => preservesProj_pure _))
            (preservesProj_recvFdsScm hCap ctrlFd statusFd expected (got ++ batch) fuel)
      · exact preservesProj_ite
          (preservesProj_bind (preservesProj_closeFdArray hCap got) (fun _ => preservesProj_pure _))
          (preservesProj_recvFdsScm hCap ctrlFd statusFd expected got fuel)

/-- `drainStderrSnippet` preserves `proj`. -/
theorem preservesProj_drainStderrSnippet {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (stderrFd : Nat) (maxBytes fuel : Nat) :
    PreservesProj proj (drainStderrSnippet cap.files stderrFd maxBytes fuel) := by
  have hLoop : ∀ chunks total f,
      PreservesProj proj (drainStderrSnippetLoop cap.files stderrFd maxBytes chunks total f) := by
    intro chunks total f
    induction f generalizing chunks total with
    | zero => exact preservesProj_pure _
    | succ f ih =>
      unfold drainStderrSnippetLoop
      refine preservesProj_ite (preservesProj_pure _) ?_
      refine preservesProj_bind
        (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesRead stderrFd _) hWf).2) fun r => ?_
      cases r with
      | error _ => exact preservesProj_pure _
      | ok _ => exact preservesProj_ite (preservesProj_pure _) (ih _ _)
  unfold drainStderrSnippet
  exact preservesProj_bind (preservesProj_setNonblockingOpt hCap (some stderrFd)) fun _ =>
    preservesProj_bind (hLoop #[] 0 fuel) (fun _ => preservesProj_pure _)

/-- `precheckHostMounts` preserves `proj` and returns non-empty error messages on failure. -/
theorem precheckHostMounts_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (fuel : Nat) :
    ∀ mounts,
      PreservesProj proj (precheckHostMounts cap.files fuel mounts) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        ∀ e, ((precheckHostMounts cap.files fuel mounts).run w).1 = .error e → e.message ≠ ""
  | [] => ⟨preservesProj_pure _, fun _ _ _ h => by cases h⟩
  | mnt :: rest => by
    have ⟨hPR, hER⟩ := precheckHostMounts_spec hCap fuel rest
    unfold precheckHostMounts
    cases hm : mountHostPath? mnt with
    | none => exact ⟨hPR, hER⟩
    | some hp =>
      have hSt : PreservesProj proj (retryEintr (cap.files.fstatat none hp.toUTF8 {}) fuel) :=
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none hp.toUTF8 {}) hWf).2) fuel
      constructor
      · refine preservesProj_bind hSt fun r => ?_
        cases r with
        | error _ => exact preservesProj_pure _
        | ok _ => exact hPR
      · intro w hWf e he
        simp only [stateM_bind_run] at he
        have h1 := hSt w hWf
        have hWf1 : rawHostWorldWf (proj ((retryEintr (cap.files.fstatat none hp.toUTF8 {}) fuel).run w).2) = true := by
          rw [h1]; exact hWf
        cases hR : ((retryEintr (cap.files.fstatat none hp.toUTF8 {}) fuel).run w).1 with
        | error err =>
          rw [hR] at he
          simp only [stateM_pure_run] at he
          cases he
          exact (HostBwrap.mapPathErrnoToSandboxError_classification hp "host mount path error" err).2.2.1
        | ok _ =>
          rw [hR] at he
          exact hER _ hWf1 e he

private theorem mapRawError_io_ne_empty (e : Errno) (msg : String) :
    (Internal.mapRawError (.ioError none e msg)).message ≠ "" := by
  simp only [Internal.mapRawError, Model.Internal.mapRawError]
  cases h : msg.isEmpty with
  | true =>
    simp only [↓reduceIte]
    intro heq
    rw [String.append_eq_empty_iff] at heq
    exact absurd heq.1 (by decide)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact String.isEmpty_eq_false_iff.mp h

/-- `killBoxPg` preserves `proj` and only returns `.ioError` with non-empty message on failure. -/
theorem killBoxPg_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (pgid : UInt32) (fuel : Nat) :
    PreservesProj proj (killBoxPg cap.proc pgid fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      ∀ e, ((killBoxPg cap.proc pgid fuel).run w).1 = .error e → e.kind = .ioError ∧ e.message ≠ "" := by
  unfold killBoxPg
  have hK : PreservesProj proj (retryEintr (cap.proc.kill (LinuxSyscall.Process.killTargetOfPgid pgid) .sigkill) fuel) :=
    preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procKill _ .sigkill) hWf).2) fuel
  constructor
  · refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind hK fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  · intro w _ e he
    cases hBad : (pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID) with
    | true => simp only [hBad, ↓reduceIte, stateM_pure_run] at he; cases he
    | false =>
      simp only [hBad, Bool.false_eq_true, ↓reduceIte, stateM_bind_run] at he
      cases hR : ((retryEintr (cap.proc.kill (LinuxSyscall.Process.killTargetOfPgid pgid) .sigkill) fuel).run w).1 with
      | ok _ => rw [hR] at he; simp only [stateM_pure_run] at he; cases he
      | error err =>
        rw [hR] at he
        dsimp only at he
        cases hSrch : (err == Errno.ESRCH) with
        | true => simp only [hSrch, ↓reduceIte, stateM_pure_run] at he; cases he
        | false =>
          simp only [hSrch, Bool.false_eq_true, ↓reduceIte, stateM_pure_run] at he
          cases he
          exact ⟨rfl, mapRawError_io_ne_empty err _⟩

/-- `killBoxPidfd` preserves `proj` and only returns `.ioError` with non-empty message on failure. -/
theorem killBoxPidfd_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (pidfd : Nat) (fuel : Nat) :
    PreservesProj proj (killBoxPidfd cap.proc pidfd fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      ∀ e, ((killBoxPidfd cap.proc pidfd fuel).run w).1 = .error e → e.kind = .ioError ∧ e.message ≠ "" := by
  unfold killBoxPidfd
  have hK : PreservesProj proj (retryEintr (cap.proc.pidfd_send_signal pidfd .sigkill {}) fuel) :=
    preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procPidfdSendSignal pidfd .sigkill {}) hWf).2) fuel
  constructor
  · refine preservesProj_bind hK fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  · intro w _ e he
    simp only [stateM_bind_run] at he
    cases hR : ((retryEintr (cap.proc.pidfd_send_signal pidfd .sigkill {}) fuel).run w).1 with
    | ok _ => rw [hR] at he; simp only [stateM_pure_run] at he; cases he
    | error err =>
      rw [hR] at he
      dsimp only at he
      cases hSrch : (err == Errno.ESRCH) with
      | true => simp only [hSrch, ↓reduceIte, stateM_pure_run] at he; cases he
      | false =>
        simp only [hSrch, Bool.false_eq_true, ↓reduceIte, stateM_pure_run] at he
        cases he
        exact ⟨rfl, mapRawError_io_ne_empty err _⟩

/-- `LinuxSyscall.Process.waitpidReapLoop` preserves `proj`. -/
theorem preservesProj_waitpidReapLoop {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (pid : Int32) :
    ∀ fuel, PreservesProj proj (LinuxSyscall.Process.waitpidReapLoop cap.proc pid fuel)
  | 0 => preservesProj_pure _
  | fuel + 1 => by
    unfold LinuxSyscall.Process.waitpidReapLoop
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procWaitpid pid {}) hWf).2) fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ =>
      exact preservesProj_ite (preservesProj_waitpidReapLoop hCap pid fuel)
        (preservesProj_ite (preservesProj_pure _) (preservesProj_pure _))

/-- `rollbackRunningChild` preserves `proj`. -/
theorem preservesProj_rollbackRunningChild {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (childPid : UInt32) (pidfd? : Option Nat) (cgDir : String) (fuel : Nat) :
    PreservesProj proj (rollbackRunningChild cap.files cap.proc cap.timeRand childPid pidfd? cgDir fuel) := by
  have hTail3 : PreservesProj proj (do
      Files.closeOpt cap.files pidfd?
      let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
      pure ()) :=
    preservesProj_bind (preservesProj_closeOpt hCap pidfd?) fun _ =>
      preservesProj_bind (preservesProj_cleanupCgroupDir hCap cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel)
        (fun _ => preservesProj_pure ())
  have hTail2 : PreservesProj proj (if childPid > 0 && childPid ≤ LinuxSyscall.Process.MAX_LINUX_PID then do
      let _ ← LinuxSyscall.Process.waitpidReapLoop cap.proc childPid.toInt32 fuel
      Files.closeOpt cap.files pidfd?
      let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
      pure ()
    else do
      Files.closeOpt cap.files pidfd?
      let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
      pure ()) :=
    preservesProj_ite
      (preservesProj_bind (preservesProj_waitpidReapLoop hCap childPid.toInt32 fuel) (fun _ => hTail3))
      hTail3
  have hTail1 : PreservesProj proj (if !cgDir.isEmpty then do
      let _ ← writeTextFile cap.files (cgroupSubfile cgDir "cgroup.kill") "1" fuel
      if childPid > 0 && childPid ≤ LinuxSyscall.Process.MAX_LINUX_PID then do
        let _ ← LinuxSyscall.Process.waitpidReapLoop cap.proc childPid.toInt32 fuel
        Files.closeOpt cap.files pidfd?
        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
        pure ()
      else do
        Files.closeOpt cap.files pidfd?
        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
        pure ()
    else
      if childPid > 0 && childPid ≤ LinuxSyscall.Process.MAX_LINUX_PID then do
        let _ ← LinuxSyscall.Process.waitpidReapLoop cap.proc childPid.toInt32 fuel
        Files.closeOpt cap.files pidfd?
        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
        pure ()
      else do
        Files.closeOpt cap.files pidfd?
        let _ ← cleanupCgroupDir cap.files cap.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS fuel
        pure ()) :=
    preservesProj_ite
      (preservesProj_bind (preservesProj_writeTextFile hCap _ "1" fuel) (fun _ => hTail2))
      hTail2
  unfold rollbackRunningChild
  refine preservesProj_bind (killBoxPg_spec hCap childPid fuel).1 fun _ => ?_
  cases pidfd? with
  | none => exact hTail1
  | some pfd => exact preservesProj_bind (killBoxPidfd_spec hCap pfd fuel).1 (fun _ => hTail1)

/-- `readInitStatusBlocking` preserves `proj`. -/
theorem preservesProj_readInitStatusBlocking {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (statusFd : Nat) :
    ∀ buf fuel, PreservesProj proj (readInitStatusBlocking cap.files statusFd buf fuel)
  | _, 0 => preservesProj_pure _
  | buf, fuel + 1 => by
    unfold readInitStatusBlocking
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesRead statusFd _) hWf).2) fun r => ?_
    cases r with
    | ok bs =>
      exact preservesProj_ite (preservesProj_pure _)
        (preservesProj_ite (preservesProj_pure _)
          (preservesProj_readInitStatusBlocking hCap statusFd (buf ++ bs) fuel))
    | error _ =>
      exact preservesProj_ite (preservesProj_readInitStatusBlocking hCap statusFd buf fuel)
        (preservesProj_pure _)

/-- `readInitStatusStep` preserves `proj`. -/
theorem preservesProj_readInitStatusStep {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (statusFd : Nat) :
    ∀ buf fuel, PreservesProj proj (readInitStatusStep cap.files statusFd buf fuel)
  | _, 0 => preservesProj_pure _
  | buf, fuel + 1 => by
    unfold readInitStatusStep
    refine preservesProj_ite
      (preservesProj_bind (preservesProj_closeOpt hCap (some statusFd)) (fun _ => preservesProj_pure _)) ?_
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesRead statusFd _) hWf).2) fun r => ?_
    cases r with
    | ok bs =>
      exact preservesProj_ite
        (preservesProj_bind (preservesProj_closeOpt hCap (some statusFd)) (fun _ => preservesProj_pure _))
        (preservesProj_ite
          (preservesProj_bind (preservesProj_closeOpt hCap (some statusFd)) (fun _ => preservesProj_pure _))
          (preservesProj_readInitStatusStep hCap statusFd (buf ++ bs) fuel))
    | error _ =>
      exact preservesProj_ite (preservesProj_readInitStatusStep hCap statusFd buf fuel)
        (preservesProj_ite (preservesProj_pure _)
          (preservesProj_bind (preservesProj_closeOpt hCap (some statusFd)) (fun _ => preservesProj_pure _)))

end LeanSwe.ProcessSandbox.Raw.Proofs

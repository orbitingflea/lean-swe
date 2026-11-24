import Core.Refines
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Interface
import LeanSwe.Process.Proofs.SysBridge

/-!
Helper frame and error-classification lemmas lifting `Model.HealthyHostCapsM`
refinement (`Model.allowedHostCapStep`) through individual OS capabilities and
non-loop `LeanSwe.Process.SysBridge` primitives.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Run law for `StateM` bind. -/
theorem hostStateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

/-- Run law for `StateM` map. -/
theorem hostStateT_map_run {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := by
  dsimp only [Functor.map, StateT.map, StateT.run]
  cases x s
  rfl

/-- Run law for `StateM` pure. -/
theorem hostStateT_pure_run {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

private theorem mapRawError_nonOutcome_other (raw : ProcessRawError)
    (h1 : ∀ p t d, raw ≠ .timedOut p t d)
    (h2 : ∀ p m d, raw ≠ .outputLimitExceeded p m d)
    (h3 : ∀ p s d, raw ≠ .signaled p s d) :
    Model.isNonOutcomeError (SysBridge.mapRawError raw) := by
  refine ⟨mapRawError_message_ne_empty raw, ?_, ?_, ?_, ?_⟩ <;>
    cases raw with
    | executableNotFound _ _ _ | permissionDenied _ _ _ | invalidArgument _ _ _
    | otherError _ _ | userError _ => simp [SysBridge.mapRawError]
    | timedOut p t d => exact absurd rfl (h1 p t d)
    | outputLimitExceeded p m d => exact absurd rfl (h2 p m d)
    | signaled p s d => exact absurd rfl (h3 p s d)

/-- `SysBridge.mapRawError` on `.userError` satisfies `Model.isNonOutcomeError`. -/
theorem mapRawError_userError_isNonOutcome (msg : String) :
    Model.isNonOutcomeError (SysBridge.mapRawError (.userError msg)) :=
  mapRawError_nonOutcome_other (.userError msg)
    (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

/-- `SysBridge.mapRawError` on `.invalidArgument` satisfies `Model.isNonOutcomeError`. -/
theorem mapRawError_invalidArg_isNonOutcome (p? : Option String) (c : Errno) (msg : String) :
    Model.isNonOutcomeError (SysBridge.mapRawError (.invalidArgument p? c msg)) :=
  mapRawError_nonOutcome_other (.invalidArgument p? c msg)
    (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

/-- `SysBridge.mapRawError` on `.permissionDenied` satisfies `Model.isNonOutcomeError`. -/
theorem mapRawError_permDenied_isNonOutcome (p? : Option String) (c : Errno) (msg : String) :
    Model.isNonOutcomeError (SysBridge.mapRawError (.permissionDenied p? c msg)) :=
  mapRawError_nonOutcome_other (.permissionDenied p? c msg)
    (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

/-- `SysBridge.mapRawError` on `.executableNotFound` satisfies `Model.isNonOutcomeError`. -/
theorem mapRawError_notFound_isNonOutcome (p : String) (c : Errno) (msg : String) :
    Model.isNonOutcomeError (SysBridge.mapRawError (.executableNotFound p c msg)) :=
  mapRawError_nonOutcome_other (.executableNotFound p c msg)
    (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

/-- `SysBridge.mapErrno` always satisfies `Model.isNonOutcomeError`. -/
theorem mapErrno_isNonOutcome (prog? : Option String) (ctx : String) (e : Errno) :
    Model.isNonOutcomeError (SysBridge.mapErrno prog? ctx e) := by
  have h := mapErrno_kind_and_msg prog? ctx e
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  unfold SysBridge.mapErrno
  dsimp only
  split
  · simp [SysBridge.mapRawError]
  · split
    · simp [SysBridge.mapRawError]
    · split <;> simp [SysBridge.mapRawError]

/-- `SysBridge.mapPostForkError` always satisfies `Model.isNonOutcomeError`. -/
theorem mapPostForkError_isNonOutcome (req : ExecRequest) (pfErr : PostFork.PostForkError) :
    Model.isNonOutcomeError (SysBridge.mapPostForkError req pfErr) := by
  have h := mapPostForkError_kind_and_msg req pfErr
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  unfold SysBridge.mapPostForkError
  cases pfErr.childFailure with
  | some _ => exact (mapErrno_isNonOutcome _ _ _).2.2.2.2
  | none =>
    cases pfErr.kind <;> dsimp only
    · simp [SysBridge.mapRawError]
    all_goals
      cases pfErr.errno with
      | some _ => exact (mapErrno_isNonOutcome _ _ _).2.2.2.2
      | none => simp [SysBridge.mapRawError]

/-- `SysBridge.ensureNonEmptyMsg` preserves `Model.isNonOutcomeError`. -/
theorem ensureNonEmpty_host_isNonOutcome (fb : String) (err : ProcessError)
    (hfb : fb ≠ "") (herr : Model.isNonOutcomeError err) :
    Model.isNonOutcomeError (SysBridge.ensureNonEmptyMsg fb err) := by
  obtain ⟨_, h1, h2, h3, h4⟩ := herr
  unfold SysBridge.ensureNonEmptyMsg
  split
  · exact ⟨hfb, h1, h2, h3, h4⟩
  · next h =>
    refine ⟨?_, h1, h2, h3, h4⟩
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- Frame preservation for `cap.proc` (`pipe2`, `waitpid`, `kill`). -/
theorem cap_proc_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (req : Model.HostProcReq) :
    let r := (LinuxSyscall.Process.execProcessReq cap.proc req.toProcessReq).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w (.proc req) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  exact ⟨hStep.2.1 rfl, hStep.2.2.2.2.2⟩

/-- Frame preservation for `cap.files` (`close`, `read`, `write`, `fstatat`, `faccessat`, `fcntl`). -/
theorem cap_files_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (req : Model.HostFilesReq) :
    let r := (LinuxSyscall.Files.execFilesReq cap.files req.toFilesReq).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w (.files req) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  exact ⟨hStep.2.1 rfl, hStep.2.2.2.2.2.2.1⟩

/-- Frame + size-bound preservation for `cap.files.read`. -/
theorem cap_read_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Files.HandleId) (capBytes : UInt32) :
    let r := (cap.files.read hid capBytes).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ bs, r.1 = .ok bs → bs.size ≤ capBytes.toNat) := by
  have hStep := hCap w (.files (.read hid capBytes)) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  refine ⟨hStep.2.1 rfl, hStep.2.2.2.2.2.2.1, ?_⟩
  intro bs hOk
  exact hStep.2.2.2.2.2.2.2.1 hid capBytes bs rfl (by simp [hOk, Files.outcomeOfBytes])

/-- Frame preservation for `cap.poll.ppoll`. -/
theorem cap_ppoll_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (entries : Array (Files.HandleId × Poll.PollEvents)) (timeout? : Option Poll.Timespec) :
    let r := (cap.poll.ppoll entries timeout?).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w (.poll entries timeout?) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  exact ⟨hStep.2.1 rfl, hStep.2.2.2.2.2.1⟩

/-- Frame preservation for `cap.timeRand`. -/
theorem cap_timeRand_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (req : TimeRand.TimeRandReq) :
    let r := (TimeRand.execTimeRandReq cap.timeRand req).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w (.timeRand req) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  exact ⟨hStep.2.1 rfl, hStep.2.2.2.2.2.2⟩

/-- Frame + PID/PGID invariant for `cap.postFork.spawn`. -/
theorem cap_postFork_step {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (spec : PostFork.ChildSpecM Files.HandleId) :
    let r := (cap.postFork.spawn spec).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ child, r.1 = .ok child →
      1 ≤ child.pid ∧ child.pid ≤ Model.maxLinuxPidModel ∧
      (spec.processGroup = .newGroup → child.pgid = some child.pid)) := by
  have hStep := hCap w (.postFork spec) hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  refine ⟨hStep.2.1 rfl, hStep.2.2.2.2.1, ?_⟩
  intro child hOk
  rw [hOk] at hStep
  exact hStep.2.2.2.2.2

/-- Frame preservation for `cap.listEnvironBytes`. -/
theorem cap_listAmbientEnv_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := cap.listEnvironBytes.run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have hStep := hCap w .listAmbientEnv hWf
  unfold Model.execHostCapStep Model.allowedHostCapStep at hStep
  rw [hostStateT_map_run] at hStep
  dsimp only at hStep ⊢
  refine ⟨hStep.2.1 rfl, ?_⟩
  rw [hStep.2.2.1]

/-- Frame preservation for `cap.proc.pipe2`. -/
theorem execProc_pipe2_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (flags : LinuxSyscall.Process.PipeFlags) :
    let r := (cap.proc.pipe2 flags).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_proc_frame proj cap hCap w hWf (.pipe2 flags)
  dsimp only [Model.HostProcReq.toProcessReq] at h
  unfold LinuxSyscall.Process.execProcessReq at h
  rw [hostStateT_bind_run, hostStateT_pure_run] at h
  cases hR : (cap.proc.pipe2 flags).run w with
  | mk _ _ => rw [hR] at h; exact h

/-- Frame preservation for `cap.proc.waitpid`. -/
theorem execProc_waitpid_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags) :
    let r := (cap.proc.waitpid pid flags).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_proc_frame proj cap hCap w hWf (.waitpid pid flags)
  dsimp only [Model.HostProcReq.toProcessReq] at h
  unfold LinuxSyscall.Process.execProcessReq at h
  rw [hostStateT_bind_run, hostStateT_pure_run] at h
  cases hR : (cap.proc.waitpid pid flags).run w with
  | mk _ _ => rw [hR] at h; exact h

/-- Frame preservation for `cap.proc.kill`. -/
theorem execProc_kill_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (target : Int32) (sig : LinuxSyscall.Process.Signal) :
    let r := (cap.proc.kill target sig).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_proc_frame proj cap hCap w hWf (.kill target sig)
  dsimp only [Model.HostProcReq.toProcessReq] at h
  unfold LinuxSyscall.Process.execProcessReq at h
  rw [hostStateT_bind_run, hostStateT_pure_run] at h
  cases hR : (cap.proc.kill target sig).run w with
  | mk _ _ => rw [hR] at h; exact h

/-- Frame preservation for `cap.files.close`. -/
theorem execFiles_close_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Files.HandleId) :
    let r := (cap.files.close hid).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_files_frame proj cap hCap w hWf (.close hid)
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at h
  rw [hostStateT_map_run] at h
  exact h

/-- Frame preservation for `cap.files.write`. -/
theorem execFiles_write_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Files.HandleId) (data : ByteArray) :
    let r := (cap.files.write hid data).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_files_frame proj cap hCap w hWf (.write hid data)
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at h
  rw [hostStateT_map_run] at h
  exact h

/-- Frame preservation for `cap.files.fstatat`. -/
theorem execFiles_fstatat_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (dir : Option Files.HandleId) (path : ByteArray) (flags : Files.AtFlags) :
    let r := (cap.files.fstatat dir path flags).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_files_frame proj cap hCap w hWf (.fstatat dir path flags)
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at h
  rw [hostStateT_map_run] at h
  exact h

/-- Frame preservation for `cap.files.faccessat`. -/
theorem execFiles_faccessat_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (dir : Option Files.HandleId) (path : ByteArray) (mask : Files.AccessModeMask) (flags : Files.AtFlags) :
    let r := (cap.files.faccessat dir path mask flags).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_files_frame proj cap hCap w hWf (.faccessat dir path mask flags)
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at h
  rw [hostStateT_map_run] at h
  exact h

/-- Frame preservation for `cap.files.fcntl`. -/
theorem execFiles_fcntl_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (hid : Files.HandleId) (cmd : Files.FcntlCmd) :
    let r := (cap.files.fcntl hid cmd).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_files_frame proj cap hCap w hWf (.fcntl hid cmd)
  dsimp only [Model.HostFilesReq.toFilesReq, Files.execFilesReq] at h
  rw [hostStateT_map_run] at h
  exact h

/-- Frame preservation for `cap.timeRand.clock_gettime`. -/
theorem execTime_clockGettime_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (clk : TimeRand.ClockId) :
    let r := (cap.timeRand.clock_gettime clk).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_timeRand_frame proj cap hCap w hWf (.clock_gettime clk)
  dsimp only [TimeRand.execTimeRandReq] at h
  rw [hostStateT_bind_run, hostStateT_pure_run] at h
  cases hRun : (cap.timeRand.clock_gettime clk).run w with
  | mk _ _ => rw [hRun] at h; exact h

/-- Frame preservation for `cap.timeRand.clock_nanosleep`. -/
theorem execTime_clockNanosleep_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (clk : TimeRand.ClockId) (abs : Bool) (reqTs : TimeRand.Timespec) :
    let r := (cap.timeRand.clock_nanosleep clk abs reqTs).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  have h := cap_timeRand_frame proj cap hCap w hWf (.clock_nanosleep clk abs reqTs)
  dsimp only [TimeRand.execTimeRandReq] at h
  rw [hostStateT_bind_run, hostStateT_pure_run] at h
  cases hRun : (cap.timeRand.clock_nanosleep clk abs reqTs).run w with
  | mk _ _ => rw [hRun] at h; exact h

/-- Frame preservation for `retryEintr`. -/
theorem hostRetryEintr_frame {W α : Type} (proj : W → Model.ProcessHostWorld)
    (act : StateM W (Except Errno α))
    (hAct : ∀ w, Model.hostWorldWf (proj w) = true →
      let r := act.run w
      Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl)
    (fuel : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (LinuxSyscall.retryEintr act fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  induction fuel generalizing w with
  | zero => exact hAct w hWf
  | succ f ih =>
    unfold LinuxSyscall.retryEintr
    rw [hostStateT_bind_run]
    have h1 := hAct w hWf
    cases hR : act.run w with
    | mk res w1 =>
      rw [hR] at h1
      cases res with
      | ok _ => rw [hostStateT_pure_run]; exact h1
      | error e =>
        dsimp only
        split
        · have h2 := ih w1 h1.1
          exact ⟨h2.1, h2.2.trans h1.2⟩
        · rw [hostStateT_pure_run]; exact h1

/-- Frame preservation for `Files.closeOpt`. -/
theorem hostCloseOpt_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (fd? : Option Files.HandleId) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (Files.closeOpt cap.files fd?).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  cases fd? with
  | none => exact ⟨hWf, rfl⟩
  | some hid =>
    unfold Files.closeOpt
    rw [hostStateT_bind_run, hostStateT_pure_run]
    exact execFiles_close_frame proj cap hCap w hWf hid

/-- Frame preservation for `Files.setNonblockingOpt`. -/
theorem hostSetNonblockingOpt_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (fd? : Option Files.HandleId) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (Files.setNonblockingOpt cap.files fd?).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  cases fd? with
  | none => exact ⟨hWf, rfl⟩
  | some hid =>
    unfold Files.setNonblockingOpt
    rw [hostStateT_bind_run, hostStateT_pure_run]
    exact execFiles_fcntl_frame proj cap hCap w hWf hid (.setFl true false)

/-- Frame + non-outcome-error invariant for `SysBridge.validateWorkingDir`. -/
theorem hostValidateWorkingDir_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (cwd? : Option String) (eintrFuel : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.validateWorkingDir cap.files cwd? eintrFuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
  unfold SysBridge.validateWorkingDir
  cases cwd? with
  | none => exact ⟨hWf, rfl, fun _ h => by cases h⟩
  | some cwdDir =>
    dsimp only
    split
    · rw [hostStateT_pure_run]
      exact ⟨hWf, rfl, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
    · rw [hostStateT_bind_run]
      have h1 := hostRetryEintr_frame proj (cap.files.fstatat none cwdDir.toUTF8 {})
        (fun x hx => execFiles_fstatat_frame proj cap hCap x hx none cwdDir.toUTF8 {}) eintrFuel w hWf
      cases hR1 : (LinuxSyscall.retryEintr (cap.files.fstatat none cwdDir.toUTF8 {}) eintrFuel).run w with
      | mk r1 w1 =>
        rw [hR1] at h1
        dsimp only
        cases r1 with
        | error e =>
          rw [hostStateT_pure_run]
          exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok st =>
          dsimp only
          split
          · rw [hostStateT_pure_run]
            exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
          · rw [hostStateT_bind_run]
            have h2 := hostRetryEintr_frame proj
              (cap.files.faccessat none cwdDir.toUTF8 { exec := true } { eaccess := true })
              (fun x hx => execFiles_faccessat_frame proj cap hCap x hx none cwdDir.toUTF8 _ _)
              eintrFuel w1 h1.1
            cases hR2 : (LinuxSyscall.retryEintr
                (cap.files.faccessat none cwdDir.toUTF8 { exec := true } { eaccess := true }) eintrFuel).run w1 with
            | mk r2 w2 =>
              rw [hR2] at h2
              dsimp only
              cases r2 with
              | error e =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, h2.2.trans h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
              | ok _ =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, h2.2.trans h1.2, fun _ h => by cases h⟩

/-- Frame + non-outcome-error invariant for `SysBridge.resolveExecutablePath`. -/
theorem hostResolveExecutablePath_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (program : String) (cwd? : Option String) (envBytes : Array ByteArray) (eintrFuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.resolveExecutablePath cap.files program cwd? envBytes eintrFuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
  unfold SysBridge.resolveExecutablePath
  split
  · rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, fun _ h => by cases h⟩
  · suffices ∀ (dirs : List String) (sawPerm : Bool) (st : W),
        Model.hostWorldWf (proj st) = true →
        let r := (SysBridge.searchPathDirs cap.files program cwd? eintrFuel sawPerm dirs).run st
        Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj st).tbl ∧
        (∀ err, r.1 = .error err → Model.isNonOutcomeError err) from
      this _ false w hWf
    intro dirs
    induction dirs with
    | nil =>
      intro sawPerm st hSt
      unfold SysBridge.searchPathDirs
      split <;> rw [hostStateT_pure_run]
      · exact ⟨hSt, rfl, fun _ h => by injection h with he; subst he; exact mapRawError_permDenied_isNonOutcome _ _ _⟩
      · exact ⟨hSt, rfl, fun _ h => by injection h with he; subst he; exact mapRawError_notFound_isNonOutcome _ _ _⟩
    | cons d rest ih =>
      intro sawPerm st hSt
      unfold SysBridge.searchPathDirs
      dsimp only
      rw [hostStateT_bind_run]
      let pb := SysBridge.probePathBytes cwd? d program
      have h1 := hostRetryEintr_frame proj (cap.files.fstatat none pb {})
        (fun x hx => execFiles_fstatat_frame proj cap hCap x hx none pb {}) eintrFuel st hSt
      cases hR1 : (LinuxSyscall.retryEintr (cap.files.fstatat none pb {}) eintrFuel).run st with
      | mk r1 w1 =>
        rw [hR1] at h1
        dsimp only
        cases r1 with
        | error e =>
          dsimp only
          split
          · have h2 := ih true w1 h1.1; exact ⟨h2.1, h2.2.1.trans h1.2, h2.2.2⟩
          · split
            · have h2 := ih sawPerm w1 h1.1; exact ⟨h2.1, h2.2.1.trans h1.2, h2.2.2⟩
            · rw [hostStateT_pure_run]
              exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok statRes =>
          dsimp only
          split
          · have h2 := ih true w1 h1.1; exact ⟨h2.1, h2.2.1.trans h1.2, h2.2.2⟩
          · rw [hostStateT_bind_run]
            have h2 := hostRetryEintr_frame proj
              (cap.files.faccessat none pb { exec := true } { eaccess := true })
              (fun x hx => execFiles_faccessat_frame proj cap hCap x hx none pb _ _)
              eintrFuel w1 h1.1
            cases hR2 : (LinuxSyscall.retryEintr
                (cap.files.faccessat none pb { exec := true } { eaccess := true }) eintrFuel).run w1 with
            | mk r2 w2 =>
              rw [hR2] at h2
              dsimp only
              cases r2 with
              | ok _ =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, h2.2.trans h1.2, fun _ h => by cases h⟩
              | error e =>
                dsimp only
                split
                · have h3 := ih true w2 h2.1; exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2), h3.2.2⟩
                · split
                  · have h3 := ih sawPerm w2 h2.1; exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2), h3.2.2⟩
                  · rw [hostStateT_pure_run]
                    exact ⟨h2.1, h2.2.trans h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩

/-- Frame preservation for `TimeRand.monoNowMs`. -/
theorem hostMonoNowMs_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (TimeRand.monoNowMs cap.timeRand).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  unfold TimeRand.monoNowMs
  rw [hostStateT_bind_run]
  have h1 := execTime_clockGettime_frame proj cap hCap w hWf .monotonic
  cases hR : (cap.timeRand.clock_gettime .monotonic).run w with
  | mk res w1 =>
    rw [hR] at h1
    dsimp only
    cases res <;> (rw [hostStateT_pure_run]; exact h1)

/-- Frame + `timeoutMs?.isSome` invariant for `TimeRand.checkTimedOut`. -/
theorem hostCheckTimedOut_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (startMs : Nat) (timeoutMs? : Option Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (TimeRand.checkTimedOut cap.timeRand startMs timeoutMs?).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ rem, r.1 = .ok (true, rem) → timeoutMs?.isSome = true) := by
  unfold TimeRand.checkTimedOut
  cases timeoutMs? with
  | none =>
    rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, fun _ h => by cases h⟩
  | some timeoutMs =>
    dsimp only
    rw [hostStateT_bind_run]
    have h1 := hostMonoNowMs_frame proj cap hCap w hWf
    cases hR : (TimeRand.monoNowMs cap.timeRand).run w with
    | mk res w1 =>
      rw [hR] at h1
      dsimp only
      cases res with
      | error e =>
        rw [hostStateT_pure_run]
        exact ⟨h1.1, h1.2, fun _ h => by cases h⟩
      | ok nowMs =>
        dsimp only
        split <;> rw [hostStateT_pure_run] <;> exact ⟨h1.1, h1.2, fun _ _ => rfl⟩

/-- Frame preservation for `TimeRand.sleepMonoMs`. -/
theorem hostSleepMonoMs_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.RefinesStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (ms : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (TimeRand.sleepMonoMs cap.timeRand ms).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  unfold TimeRand.sleepMonoMs
  rw [hostStateT_bind_run, hostStateT_pure_run]
  exact execTime_clockNanosleep_frame proj cap hCap w hWf .monotonic false _

end LeanSwe.Process.Proofs

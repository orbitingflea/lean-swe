import Core.Obeys
import Core.ConcOps
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.Model
import LeanSwe.Process.Model.HealthyHost
import LeanSwe.Process.Model.FullStep
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Proofs.SysBridge
import LeanSwe.Process.Proofs.RefinesModelHostFrames

/-!
Frame-preservation and non-outcome-error invariants lifting `Model.allowedFullRawStep`
(`Internal.ProcessSysCapsM` over `RawFd`) through individual OS capabilities, path search,
and wait/reap loops for `Core.ObeysStepFromConcCell`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Abstract invariant and binary frame-preservation bundle for `Internal.ProcessSysCapsM (StateM W)`. -/
structure SysPreservesFrame {W : Type} (inv : W → Prop) (frame : W → W → Prop)
    (sys : Internal.ProcessSysCapsM (StateM W)) : Prop where
  /-- `pipe2` preserves `inv` and `frame`. -/
  pipe2 : ∀ flags w, inv w → let r := (sys.proc.pipe2 flags).run w; inv r.2 ∧ frame w r.2
  /-- `waitpid` preserves `inv` and `frame`. -/
  waitpid : ∀ pid flags w, inv w → let r := (sys.proc.waitpid pid flags).run w; inv r.2 ∧ frame w r.2
  /-- `kill` preserves `inv` and `frame`. -/
  kill : ∀ target sig w, inv w → let r := (sys.proc.kill target sig).run w; inv r.2 ∧ frame w r.2
  /-- `close` preserves `inv` and `frame`. -/
  close : ∀ fd w, inv w → let r := (sys.files.close fd).run w; inv r.2 ∧ frame w r.2
  /-- `read` preserves `inv` and `frame`. -/
  read : ∀ fd cap w, inv w → let r := (sys.files.read fd cap).run w; inv r.2 ∧ frame w r.2
  /-- `write` preserves `inv` and `frame`. -/
  write : ∀ fd bs w, inv w → let r := (sys.files.write fd bs).run w; inv r.2 ∧ frame w r.2
  /-- `fstatat` preserves `inv` and `frame`. -/
  fstatat : ∀ d p fl w, inv w → let r := (sys.files.fstatat d p fl).run w; inv r.2 ∧ frame w r.2
  /-- `faccessat` preserves `inv` and `frame`. -/
  faccessat : ∀ d p m fl w, inv w → let r := (sys.files.faccessat d p m fl).run w; inv r.2 ∧ frame w r.2
  /-- `fcntl` preserves `inv` and `frame`. -/
  fcntl : ∀ fd cmd w, inv w → let r := (sys.files.fcntl fd cmd).run w; inv r.2 ∧ frame w r.2
  /-- `ppoll` preserves `inv` and `frame`. -/
  ppoll : ∀ fds to? w, inv w → let r := (sys.poll.ppoll fds to?).run w; inv r.2 ∧ frame w r.2
  /-- `clock_gettime` preserves `inv` and `frame`. -/
  clockGettime : ∀ clk w, inv w → let r := (sys.timeRand.clock_gettime clk).run w; inv r.2 ∧ frame w r.2
  /-- `clock_nanosleep` preserves `inv` and `frame`. -/
  clockNanosleep : ∀ clk abs ts w, inv w → let r := (sys.timeRand.clock_nanosleep clk abs ts).run w; inv r.2 ∧ frame w r.2
  /-- `postFork.spawn` preserves `inv` and `frame`. -/
  postFork : ∀ spec w, inv w → let r := (sys.postFork.spawn spec).run w; inv r.2 ∧ frame w r.2
  /-- `envRaw.listEnvironBytes` preserves `inv` and `frame`. -/
  listEnvironBytes : ∀ w, inv w → let r := sys.envRaw.listEnvironBytes.run w; inv r.2 ∧ frame w r.2

/-- Derive `SysPreservesFrame` from `Core.ObeysStep` and `projCell` frame invariance on `execFullRawStep`. -/
theorem sysPreservesFrame_of_obeysStep {W CellT : Type}
    (projRaw : W → Model.FullHostWorld) (projCell : W → CellT)
    (sys : Internal.ProcessSysCapsM (StateM W))
    (hStep : Core.ObeysStep projRaw Model.fullRawWf (Model.execFullRawStep sys) Model.allowedFullRawStep)
    (hFrame : ∀ w req, Model.fullRawWf (projRaw w) = true →
      projCell ((Model.execFullRawStep sys req).run w).2 = projCell w) :
    SysPreservesFrame (fun w => Model.fullRawWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) sys := by
  have stepInv : ∀ req w, Model.fullRawWf (projRaw w) = true →
      let w' := ((Model.execFullRawStep sys req).run w).2
      Model.fullRawWf (projRaw w') = true ∧ projCell w' = projCell w := by
    intro req w hw
    have hs := hStep w req hw
    have hf := hFrame w req hw
    cases hR : (Model.execFullRawStep sys req).run w with
    | mk out w' =>
      rw [hR] at hs hf
      exact ⟨hs.2.1, hf⟩
  refine
    { pipe2 := fun flags w hw => by
        have h := stepInv (.proc (.pipe2 flags)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdProcReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      waitpid := fun pid flags w hw => by
        have h := stepInv (.proc (.waitpid pid flags)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdProcReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      kill := fun target sig w hw => by
        have h := stepInv (.proc (.kill target sig)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdProcReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      close := fun fd w hw => by
        have h := stepInv (.files (.close fd)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      read := fun fd cap w hw => by
        have h := stepInv (.files (.read fd cap)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      write := fun fd bs w hw => by
        have h := stepInv (.files (.write fd bs)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      fstatat := fun d p fl w hw => by
        have h := stepInv (.files (.fstatat d p fl)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      faccessat := fun d p m fl w hw => by
        have h := stepInv (.files (.faccessat d p m fl)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      fcntl := fun fd cmd w hw => by
        have h := stepInv (.files (.fcntl fd cmd)) w hw
        dsimp only [Model.execFullRawStep, Model.execRawFdFilesReq] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h
      ppoll := fun fds to? w hw => by
        have h := stepInv (.poll fds to?) w hw
        dsimp only [Model.execFullRawStep] at h
        rw [hostStateT_map_run] at h; exact h
      clockGettime := fun clk w hw => by
        have h := stepInv (.timeRand (.clock_gettime clk)) w hw
        dsimp only [Model.execFullRawStep, TimeRand.execTimeRandReq] at h
        rw [hostStateT_map_run, hostStateT_bind_run, hostStateT_pure_run] at h
        cases hR : (sys.timeRand.clock_gettime clk).run w with
        | mk _ _ => rw [hR] at h; exact h
      clockNanosleep := fun clk abs ts w hw => by
        have h := stepInv (.timeRand (.clock_nanosleep clk abs ts)) w hw
        dsimp only [Model.execFullRawStep, TimeRand.execTimeRandReq] at h
        rw [hostStateT_map_run, hostStateT_bind_run, hostStateT_pure_run] at h
        cases hR : (sys.timeRand.clock_nanosleep clk abs ts).run w with
        | mk _ _ => rw [hR] at h; exact h
      postFork := fun spec w hw => by
        have h := stepInv (.postFork spec) w hw
        dsimp only [Model.execFullRawStep] at h
        rw [hostStateT_map_run] at h; exact h
      listEnvironBytes := fun w hw => by
        have h := stepInv (.envRaw .listEnvironBytes) w hw
        dsimp only [Model.execFullRawStep, EnvVars.Raw.Model.execPkgStep] at h
        rw [hostStateT_map_run, hostStateT_map_run] at h; exact h }

theorem fullRetryEintr_frame {W α : Type} {inv : W → Prop} {frame : W → W → Prop}
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    (act : StateM W (Except Errno α))
    (hAct : ∀ w, inv w → let r := act.run w; inv r.2 ∧ frame w r.2)
    (fuel : Nat) (w : W) (hWf : inv w) :
    let r := (LinuxSyscall.retryEintr act fuel).run w
    inv r.2 ∧ frame w r.2 := by
  induction fuel generalizing w with
  | zero => exact hAct w hWf
  | succ _ ih =>
    unfold LinuxSyscall.retryEintr
    rw [hostStateT_bind_run]
    have h1 := hAct w hWf
    cases hR : act.run w with
    | mk res w1 =>
      rw [hR] at h1
      cases res with
      | ok _ => rw [hostStateT_pure_run]; exact h1
      | error _ =>
        dsimp only; split
        · have h2 := ih w1 h1.1
          exact ⟨h2.1, htrans _ _ _ h1.2 h2.2⟩
        · rw [hostStateT_pure_run]; exact h1

theorem fullCloseOpt_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w) {sys : Internal.ProcessSysCapsM (StateM W)}
    (hSys : SysPreservesFrame inv frame sys)
    (fd? : Option RawFd) (w : W) (hWf : inv w) :
    let r := (Files.closeOpt sys.files fd?).run w
    inv r.2 ∧ frame w r.2 := by
  cases fd? with
  | none => exact ⟨hWf, hrefl w⟩
  | some fd =>
    unfold Files.closeOpt
    rw [hostStateT_bind_run, hostStateT_pure_run]
    exact hSys.close fd w hWf

theorem fullSetNonblockingOpt_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w) {sys : Internal.ProcessSysCapsM (StateM W)}
    (hSys : SysPreservesFrame inv frame sys)
    (fd? : Option RawFd) (w : W) (hWf : inv w) :
    let r := (Files.setNonblockingOpt sys.files fd?).run w
    inv r.2 ∧ frame w r.2 := by
  cases fd? with
  | none => exact ⟨hWf, hrefl w⟩
  | some fd =>
    unfold Files.setNonblockingOpt
    rw [hostStateT_bind_run, hostStateT_pure_run]
    exact hSys.fcntl fd (.setFl true false) w hWf

theorem fullValidateWorkingDir_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (cwd? : Option String) (eintrFuel : Nat) (w : W) (hWf : inv w) :
    let r := (SysBridge.validateWorkingDir sys.files cwd? eintrFuel).run w
    inv r.2 ∧ frame w r.2 ∧ (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
  unfold SysBridge.validateWorkingDir
  cases cwd? with
  | none => exact ⟨hWf, hrefl w, fun _ h => by cases h⟩
  | some cwdDir =>
    dsimp only; split
    · rw [hostStateT_pure_run]
      exact ⟨hWf, hrefl w, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
    · rw [hostStateT_bind_run]
      have h1 := fullRetryEintr_frame htrans (sys.files.fstatat none cwdDir.toUTF8 {})
        (hSys.fstatat none cwdDir.toUTF8 {}) eintrFuel w hWf
      cases hR1 : (LinuxSyscall.retryEintr (sys.files.fstatat none cwdDir.toUTF8 {}) eintrFuel).run w with
      | mk r1 w1 =>
        rw [hR1] at h1; dsimp only
        cases r1 with
        | error _ =>
          rw [hostStateT_pure_run]
          exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok _ =>
          dsimp only; split
          · rw [hostStateT_pure_run]
            exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
          · rw [hostStateT_bind_run]
            have h2 := fullRetryEintr_frame htrans
              (sys.files.faccessat none cwdDir.toUTF8 { exec := true } { eaccess := true })
              (hSys.faccessat none cwdDir.toUTF8 _ _) eintrFuel w1 h1.1
            cases hR2 : (LinuxSyscall.retryEintr
                (sys.files.faccessat none cwdDir.toUTF8 { exec := true } { eaccess := true }) eintrFuel).run w1 with
            | mk r2 w2 =>
              rw [hR2] at h2; dsimp only
              cases r2 with
              | error _ =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, htrans _ _ _ h1.2 h2.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
              | ok _ =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, htrans _ _ _ h1.2 h2.2, fun _ h => by cases h⟩

theorem fullResolveExecutablePath_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (program : String) (cwd? : Option String) (envBytes : Array ByteArray) (eintrFuel : Nat)
    (w : W) (hWf : inv w) :
    let r := (SysBridge.resolveExecutablePath sys.files program cwd? envBytes eintrFuel).run w
    inv r.2 ∧ frame w r.2 ∧ (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
  unfold SysBridge.resolveExecutablePath
  split
  · rw [hostStateT_pure_run]; exact ⟨hWf, hrefl w, fun _ h => by cases h⟩
  · suffices ∀ (dirs : List String) (sawPerm : Bool) (st : W), inv st →
        let r := (SysBridge.searchPathDirs sys.files program cwd? eintrFuel sawPerm dirs).run st
        inv r.2 ∧ frame st r.2 ∧ (∀ err, r.1 = .error err → Model.isNonOutcomeError err) from
      this _ false w hWf
    intro dirs
    induction dirs with
    | nil =>
      intro sawPerm st hSt; unfold SysBridge.searchPathDirs
      split <;> rw [hostStateT_pure_run]
      · exact ⟨hSt, hrefl st, fun _ h => by injection h with he; subst he; exact mapRawError_permDenied_isNonOutcome _ _ _⟩
      · exact ⟨hSt, hrefl st, fun _ h => by injection h with he; subst he; exact mapRawError_notFound_isNonOutcome _ _ _⟩
    | cons d rest ih =>
      intro sawPerm st hSt; unfold SysBridge.searchPathDirs; dsimp only; rw [hostStateT_bind_run]
      let pb := SysBridge.probePathBytes cwd? d program
      have h1 := fullRetryEintr_frame htrans (sys.files.fstatat none pb {})
        (hSys.fstatat none pb {}) eintrFuel st hSt
      cases hR1 : (LinuxSyscall.retryEintr (sys.files.fstatat none pb {}) eintrFuel).run st with
      | mk r1 w1 =>
        rw [hR1] at h1; dsimp only
        cases r1 with
        | error _ =>
          dsimp only; split
          · have h2 := ih true w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, h2.2.2⟩
          · split
            · have h2 := ih sawPerm w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, h2.2.2⟩
            · rw [hostStateT_pure_run]
              exact ⟨h1.1, h1.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok _ =>
          dsimp only; split
          · have h2 := ih true w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, h2.2.2⟩
          · rw [hostStateT_bind_run]
            have h2 := fullRetryEintr_frame htrans
              (sys.files.faccessat none pb { exec := true } { eaccess := true })
              (hSys.faccessat none pb _ _) eintrFuel w1 h1.1
            cases hR2 : (LinuxSyscall.retryEintr
                (sys.files.faccessat none pb { exec := true } { eaccess := true }) eintrFuel).run w1 with
            | mk r2 w2 =>
              rw [hR2] at h2; dsimp only
              cases r2 with
              | ok _ => rw [hostStateT_pure_run]; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2, fun _ h => by cases h⟩
              | error _ =>
                dsimp only; split
                · have h3 := ih true w2 h2.1
                  exact ⟨h3.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                · split
                  · have h3 := ih sawPerm w2 h2.1
                    exact ⟨h3.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                  · rw [hostStateT_pure_run]
                    exact ⟨h2.1, htrans _ _ _ h1.2 h2.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩

theorem fullMonoNowMs_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (w : W) (hWf : inv w) :
    let r := (TimeRand.monoNowMs sys.timeRand).run w
    inv r.2 ∧ frame w r.2 := by
  unfold TimeRand.monoNowMs; rw [hostStateT_bind_run]
  have h1 := hSys.clockGettime .monotonic w hWf
  cases hR : (sys.timeRand.clock_gettime .monotonic).run w with
  | mk res _ => rw [hR] at h1; dsimp only; cases res <;> (rw [hostStateT_pure_run]; exact h1)

theorem fullCheckTimedOut_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w) {sys : Internal.ProcessSysCapsM (StateM W)}
    (hSys : SysPreservesFrame inv frame sys)
    (startMs : Nat) (timeoutMs? : Option Nat) (w : W) (hWf : inv w) :
    let r := (TimeRand.checkTimedOut sys.timeRand startMs timeoutMs?).run w
    inv r.2 ∧ frame w r.2 ∧ (∀ rem, r.1 = .ok (true, rem) → timeoutMs?.isSome = true) := by
  unfold TimeRand.checkTimedOut
  cases timeoutMs? with
  | none => rw [hostStateT_pure_run]; exact ⟨hWf, hrefl w, fun _ h => by cases h⟩
  | some _ =>
    dsimp only; rw [hostStateT_bind_run]
    have h1 := fullMonoNowMs_frame hSys w hWf
    cases hR : (TimeRand.monoNowMs sys.timeRand).run w with
    | mk res _ =>
      rw [hR] at h1; dsimp only
      cases res with
      | error _ => rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, fun _ h => by cases h⟩
      | ok _ => dsimp only; split <;> rw [hostStateT_pure_run] <;> exact ⟨h1.1, h1.2, fun _ _ => rfl⟩

theorem fullSleepMonoMs_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (ms : Nat) (w : W) (hWf : inv w) :
    let r := (TimeRand.sleepMonoMs sys.timeRand ms).run w
    inv r.2 ∧ frame w r.2 := by
  unfold TimeRand.sleepMonoMs; rw [hostStateT_bind_run, hostStateT_pure_run]
  exact hSys.clockNanosleep .monotonic false _ w hWf

theorem fullWaitBlockingLoop_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pid : Int32) (stdout stderr : ByteArray) (fuel : Nat) (w : W) (hWf : inv w) :
    let r := (SysBridge.waitBlockingLoop sys.proc pid stdout stderr fuel).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (.exited res) => res.stdout = stdout ∧ res.stderr = stderr
    | .ok (.signaled _ out err) => out = stdout ∧ err = stderr
    | .ok (.timedOut _ _) | .ok (.outputLimitExceeded _ _) => False := by
  induction fuel generalizing w with
  | zero =>
    unfold SysBridge.waitBlockingLoop; rw [hostStateT_pure_run]
    exact ⟨hWf, hrefl w, mapRawError_userError_isNonOutcome _⟩
  | succ _ ih =>
    unfold SysBridge.waitBlockingLoop; rw [hostStateT_bind_run]
    have h1 := hSys.waitpid pid {} w hWf
    cases hW : (sys.proc.waitpid pid {}).run w with
    | mk wr w1 =>
      rw [hW] at h1; dsimp only
      cases wr with
      | ok res => rw [hostStateT_pure_run]; cases res <;> exact ⟨h1.1, h1.2, rfl, rfl⟩
      | error _ =>
        dsimp only; split
        · have h2 := ih w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, h2.2.2⟩
        · split
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, mapErrno_isNonOutcome _ _ _⟩

theorem fullWaitTimedLoop_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) (fuel : Nat)
    (w : W) (hWf : inv w) :
    let r := (SysBridge.waitTimedLoop sys.proc sys.timeRand pid startMs timeoutMs stdout stderr fuel).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (_, .exited res) => res.stdout = stdout ∧ res.stderr = stderr
    | .ok (_, .signaled _ out err) => out = stdout ∧ err = stderr
    | .ok (_, .timedOut out err) => out = stdout ∧ err = stderr
    | .ok (_, .outputLimitExceeded _ _) => False := by
  induction fuel generalizing w with
  | zero =>
    unfold SysBridge.waitTimedLoop; rw [hostStateT_pure_run]
    exact ⟨hWf, hrefl w, mapRawError_userError_isNonOutcome _⟩
  | succ _ ih =>
    unfold SysBridge.waitTimedLoop; rw [hostStateT_bind_run]
    have h1 := hSys.waitpid pid { nohang := true } w hWf
    cases hW : (sys.proc.waitpid pid { nohang := true }).run w with
    | mk wr w1 =>
      rw [hW] at h1; dsimp only
      cases wr with
      | ok res =>
        cases res with
        | stillRunning =>
          dsimp only; rw [hostStateT_bind_run]
          have h2 := fullCheckTimedOut_spec hrefl hSys startMs (some timeoutMs) w1 h1.1
          cases hCt : (TimeRand.checkTimedOut sys.timeRand startMs (some timeoutMs)).run w1 with
          | mk ct w2 =>
            rw [hCt] at h2; dsimp only
            cases ct with
            | error _ =>
              rw [hostStateT_pure_run]
              exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, mapErrno_isNonOutcome _ _ _⟩
            | ok pair =>
              rcases pair with ⟨expired, remMs⟩
              cases expired with
              | true =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, rfl, rfl⟩
              | false =>
                dsimp only; rw [hostStateT_bind_run]
                have h3 := fullSleepMonoMs_frame hSys (Nat.min remMs 5) w2 h2.1
                cases hSl : (TimeRand.sleepMonoMs sys.timeRand (Nat.min remMs 5)).run w2 with
                | mk _ w3 =>
                  rw [hSl] at h3
                  have h4 := ih w3 h3.1
                  exact ⟨h4.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2.1 (htrans _ _ _ h3.2 h4.2.1)), h4.2.2⟩
        | exited _ _ | signaled _ _ _ | stopped _ _ | continued _ =>
          rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
      | error _ =>
        dsimp only; split
        · have h2 := ih w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2.1, h2.2.2⟩
        · split
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, mapErrno_isNonOutcome _ _ _⟩

theorem fullKillGraceProbeLoop_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (target : Int32) (steps : Nat) (w : W) (hWf : inv w) :
    let r := (SysBridge.killGraceProbeLoop sys.proc sys.timeRand target steps).run w
    inv r.2 ∧ frame w r.2 := by
  induction steps generalizing w with
  | zero => exact ⟨hWf, hrefl w⟩
  | succ _ ih =>
    unfold SysBridge.killGraceProbeLoop; rw [hostStateT_bind_run]
    have h1 := fullSleepMonoMs_frame hSys 5 w hWf
    cases hSl : (TimeRand.sleepMonoMs sys.timeRand 5).run w with
    | mk _ w1 =>
      rw [hSl] at h1; dsimp only; rw [hostStateT_bind_run]
      have h2 := hSys.kill target .sigzero w1 h1.1
      cases hKl : (sys.proc.kill target .sigzero).run w1 with
      | mk kr w2 =>
        rw [hKl] at h2; dsimp only
        cases kr with
        | ok _ =>
          have h3 := ih w2 h2.1
          exact ⟨h3.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2 h3.2)⟩
        | error _ =>
          dsimp only; split
          · rw [hostStateT_pure_run]; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2⟩
          · have h3 := ih w2 h2.1
            exact ⟨h3.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2 h3.2)⟩

theorem fullWaitpidReapLoop_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pid : Int32) (fuel : Nat) (w : W) (hWf : inv w) :
    let r := (LinuxSyscall.Process.waitpidReapLoop sys.proc pid fuel).run w
    inv r.2 ∧ frame w r.2 := by
  induction fuel generalizing w with
  | zero => exact ⟨hWf, hrefl w⟩
  | succ _ ih =>
    unfold LinuxSyscall.Process.waitpidReapLoop; rw [hostStateT_bind_run]
    have h1 := hSys.waitpid pid {} w hWf
    cases hW : (sys.proc.waitpid pid {}).run w with
    | mk wr w1 =>
      rw [hW] at h1; dsimp only
      cases wr with
      | ok _ => rw [hostStateT_pure_run]; exact h1
      | error _ =>
        dsimp only; split
        · have h2 := ih w1 h1.1; exact ⟨h2.1, htrans _ _ _ h1.2 h2.2⟩
        · split <;> rw [hostStateT_pure_run] <;> exact h1

end LeanSwe.Process.Proofs

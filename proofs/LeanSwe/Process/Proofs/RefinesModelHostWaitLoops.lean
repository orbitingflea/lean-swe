import LeanSwe.Process.Proofs.RefinesModelHostFrames

/-!
Wait, grace-probe, and reap loop invariants lifted from `Model.HealthyHostCapsM`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Frame + outcome invariant for `SysBridge.waitBlockingLoop`. -/
theorem hostWaitBlockingLoop_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (pid : Int32) (stdout stderr : ByteArray) (fuel : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.waitBlockingLoop cap.proc pid stdout stderr fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (.exited res) => res.stdout = stdout ∧ res.stderr = stderr
    | .ok (.signaled _ out err) => out = stdout ∧ err = stderr
    | .ok (.timedOut _ _) | .ok (.outputLimitExceeded _ _) => False := by
  induction fuel generalizing w with
  | zero =>
    unfold SysBridge.waitBlockingLoop
    rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, mapRawError_userError_isNonOutcome _⟩
  | succ f ih =>
    unfold SysBridge.waitBlockingLoop
    rw [hostStateT_bind_run]
    have h1 := execProc_waitpid_frame proj cap hCap w hWf pid {}
    cases hW : (cap.proc.waitpid pid {}).run w with
    | mk wr w1 =>
      rw [hW] at h1
      dsimp only
      cases wr with
      | ok res =>
        rw [hostStateT_pure_run]
        cases res <;> exact ⟨h1.1, h1.2, rfl, rfl⟩
      | error e =>
        dsimp only
        split
        · have h2 := ih w1 h1.1
          exact ⟨h2.1, h2.2.1.trans h1.2, h2.2.2⟩
        · split
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, mapErrno_isNonOutcome _ _ _⟩

/-- Frame + outcome invariant for `SysBridge.waitTimedLoop`. -/
theorem hostWaitTimedLoop_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) (fuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.waitTimedLoop cap.proc cap.timeRand pid startMs timeoutMs stdout stderr fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (_, .exited res) => res.stdout = stdout ∧ res.stderr = stderr
    | .ok (_, .signaled _ out err) => out = stdout ∧ err = stderr
    | .ok (_, .timedOut out err) => out = stdout ∧ err = stderr
    | .ok (_, .outputLimitExceeded _ _) => False := by
  induction fuel generalizing w with
  | zero =>
    unfold SysBridge.waitTimedLoop
    rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, mapRawError_userError_isNonOutcome _⟩
  | succ f ih =>
    unfold SysBridge.waitTimedLoop
    rw [hostStateT_bind_run]
    have h1 := execProc_waitpid_frame proj cap hCap w hWf pid { nohang := true }
    cases hW : (cap.proc.waitpid pid { nohang := true }).run w with
    | mk wr w1 =>
      rw [hW] at h1
      dsimp only
      cases wr with
      | ok res =>
        cases res with
        | stillRunning =>
          dsimp only
          rw [hostStateT_bind_run]
          have h2 := hostCheckTimedOut_spec proj cap hCap startMs (some timeoutMs) w1 h1.1
          cases hCt : (TimeRand.checkTimedOut cap.timeRand startMs (some timeoutMs)).run w1 with
          | mk ct w2 =>
            rw [hCt] at h2
            dsimp only
            cases ct with
            | error e =>
              rw [hostStateT_pure_run]
              exact ⟨h2.1, h2.2.1.trans h1.2, mapErrno_isNonOutcome _ _ _⟩
            | ok pair =>
              rcases pair with ⟨expired, remMs⟩
              cases expired with
              | true =>
                rw [hostStateT_pure_run]
                exact ⟨h2.1, h2.2.1.trans h1.2, rfl, rfl⟩
              | false =>
                dsimp only
                rw [hostStateT_bind_run]
                have h3 := hostSleepMonoMs_frame proj cap hCap (Nat.min remMs 5) w2 h2.1
                cases hSl : (TimeRand.sleepMonoMs cap.timeRand (Nat.min remMs 5)).run w2 with
                | mk _ w3 =>
                  rw [hSl] at h3
                  have h4 := ih w3 h3.1
                  exact ⟨h4.1, h4.2.1.trans (h3.2.trans (h2.2.1.trans h1.2)), h4.2.2⟩
        | exited _ _ => rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
        | signaled _ _ _ => rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
        | stopped _ _ => rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
        | continued _ => rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
      | error e =>
        dsimp only
        split
        · have h2 := ih w1 h1.1
          exact ⟨h2.1, h2.2.1.trans h1.2, h2.2.2⟩
        · split
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, rfl, rfl⟩
          · rw [hostStateT_pure_run]; exact ⟨h1.1, h1.2, mapErrno_isNonOutcome _ _ _⟩

/-- Frame preservation for `SysBridge.killGraceProbeLoop`. -/
theorem hostKillGraceProbeLoop_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (target : Int32) (steps : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.killGraceProbeLoop cap.proc cap.timeRand target steps).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  induction steps generalizing w with
  | zero => exact ⟨hWf, rfl⟩
  | succ s ih =>
    unfold SysBridge.killGraceProbeLoop
    rw [hostStateT_bind_run]
    have h1 := hostSleepMonoMs_frame proj cap hCap 5 w hWf
    cases hSl : (TimeRand.sleepMonoMs cap.timeRand 5).run w with
    | mk _ w1 =>
      rw [hSl] at h1
      dsimp only
      rw [hostStateT_bind_run]
      have h2 := execProc_kill_frame proj cap hCap w1 h1.1 target .sigzero
      cases hKl : (cap.proc.kill target .sigzero).run w1 with
      | mk kr w2 =>
        rw [hKl] at h2
        dsimp only
        cases kr with
        | ok _ =>
          have h3 := ih w2 h2.1
          exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2)⟩
        | error e =>
          dsimp only
          split
          · rw [hostStateT_pure_run]; exact ⟨h2.1, h2.2.trans h1.2⟩
          · have h3 := ih w2 h2.1
            exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2)⟩

/-- Frame preservation for `LinuxSyscall.Process.waitpidReapLoop`. -/
theorem hostWaitpidReapLoop_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (pid : Int32) (fuel : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (LinuxSyscall.Process.waitpidReapLoop cap.proc pid fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  induction fuel generalizing w with
  | zero => exact ⟨hWf, rfl⟩
  | succ f ih =>
    unfold LinuxSyscall.Process.waitpidReapLoop
    rw [hostStateT_bind_run]
    have h1 := execProc_waitpid_frame proj cap hCap w hWf pid {}
    cases hW : (cap.proc.waitpid pid {}).run w with
    | mk wr w1 =>
      rw [hW] at h1
      dsimp only
      cases wr with
      | ok _ => rw [hostStateT_pure_run]; exact h1
      | error e =>
        dsimp only
        split
        · have h2 := ih w1 h1.1
          exact ⟨h2.1, h2.2.trans h1.2⟩
        · split <;> rw [hostStateT_pure_run] <;> exact h1

end LeanSwe.Process.Proofs

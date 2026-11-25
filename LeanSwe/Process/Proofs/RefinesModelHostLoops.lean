import LeanSwe.Process.Proofs.RefinesModelHostFrames

/-!
Fuel-loop invariants for `SysBridge` pipe streaming, blocking/timed `waitpid`,
and `killGraceProbeLoop` / `waitpidReapLoop` lifted from `Model.HealthyHostCapsM`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Frame + non-outcome-error invariant for `SysBridge.writeStdinStep`. -/
theorem hostWriteStdinStep_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (inFd : Files.HandleId) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (pos : Nat) (prog : Bool) (fuel : Nat) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.writeStdinStep cap.files cap.timeRand inFd stdin startMs timeoutMs? pos prog fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ err, r.1 = .error err → Model.isNonOutcomeError err) ∧
    (∀ fd' p' pr', r.1 = .ok (fd', p', pr', true) → timeoutMs?.isSome = true) := by
  induction fuel generalizing pos prog w with
  | zero =>
    unfold SysBridge.writeStdinStep
    split
    · rw [hostStateT_bind_run, hostStateT_pure_run]
      have h1 := hostCloseOpt_frame proj cap hCap (some inFd) w hWf
      exact ⟨h1.1, h1.2, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
    · rw [hostStateT_pure_run]
      exact ⟨hWf, rfl, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
  | succ f ih =>
    unfold SysBridge.writeStdinStep
    split
    · rw [hostStateT_bind_run, hostStateT_pure_run]
      have h1 := hostCloseOpt_frame proj cap hCap (some inFd) w hWf
      exact ⟨h1.1, h1.2, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
    · rw [hostStateT_bind_run]
      have h1 := hostCheckTimedOut_spec proj cap hCap startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut cap.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1
        dsimp only
        cases ct with
        | error e =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := hostCloseOpt_frame proj cap hCap (some inFd) w1 h1.1
          exact ⟨h2.1, h2.2.trans h1.2.1,
            (fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _),
            fun _ _ _ h => by cases h⟩
        | ok pair =>
          rcases pair with ⟨expired, rem⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := hostCloseOpt_frame proj cap hCap (some inFd) w1 h1.1
            exact ⟨h2.1, h2.2.trans h1.2.1, (fun _ h => by cases h),
              fun _ _ _ _ => h1.2.2 rem rfl⟩
          | false =>
            dsimp only
            rw [hostStateT_bind_run]
            let slice := stdin.extract pos (Nat.min stdin.size (pos + SysBridge.STDIN_WRITE_CHUNK))
            have h2 := execFiles_write_frame proj cap hCap w1 h1.1 inFd slice
            cases hWr : (cap.files.write inFd slice).run w1 with
            | mk wr w2 =>
              rw [hWr] at h2
              dsimp only
              cases wr with
              | ok n =>
                dsimp only
                split
                · rw [hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := hostCloseOpt_frame proj cap hCap (some inFd) w2 h2.1
                  exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2.1),
                    (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                · split
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := hostCloseOpt_frame proj cap hCap (some inFd) w2 h2.1
                    exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2.1),
                      (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                  · have h3 := ih (pos + n.toNat) true w2 h2.1
                    exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2.1), h3.2.2.1, h3.2.2.2⟩
              | error e =>
                dsimp only
                split
                · have h3 := ih pos prog w2 h2.1
                  exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2.1), h3.2.2.1, h3.2.2.2⟩
                · split
                  · rw [hostStateT_pure_run]
                    exact ⟨h2.1, h2.2.trans h1.2.1, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := hostCloseOpt_frame proj cap hCap (some inFd) w2 h2.1
                    exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2.1),
                      (fun _ h => by cases h), fun _ _ _ h => by cases h⟩

/-- Frame + output-bound invariant for `SysBridge.drainPipeStep`. -/
theorem hostDrainPipeStep_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (pipeFd : Files.HandleId) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen iterBytes : Nat) (prog : Bool) (fuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (hSum : (chunks.toList.map ByteArray.size).sum = curLen)
    (hBound : ∀ lim, maxOutputBytes? = some lim → curLen + otherLen ≤ lim) :
    let r := (SysBridge.drainPipeStep cap.files cap.timeRand pipeFd otherLen startMs
      timeoutMs? maxOutputBytes? chunks curLen iterBytes prog fuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ ch' len', r.1 = .timedOut ch' len' →
      timeoutMs?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ ch' len', r.1 = .limitExceeded ch' len' →
      maxOutputBytes?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ fd? ch' len' pr, r.1 = .cont fd? ch' len' pr →
      (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ err, r.1 = .ioErr err → Model.isNonOutcomeError err) := by
  induction fuel generalizing chunks curLen iterBytes prog w with
  | zero =>
    unfold SysBridge.drainPipeStep
    rw [hostStateT_pure_run]
    refine ⟨hWf, rfl, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
    intro _ ch' len' _ hEq
    injection hEq with _ hCh hLen _
    subst hCh hLen
    exact ⟨hSum, hBound⟩
  | succ f ih =>
    unfold SysBridge.drainPipeStep
    split
    · rw [hostStateT_pure_run]
      refine ⟨hWf, rfl, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
      intro _ ch' len' _ hEq
      injection hEq with _ hCh hLen _
      subst hCh hLen
      exact ⟨hSum, hBound⟩
    · rw [hostStateT_bind_run]
      have h1 := hostCheckTimedOut_spec proj cap hCap startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut cap.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1
        dsimp only
        cases ct with
        | error e =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := hostCloseOpt_frame proj cap hCap (some pipeFd) w1 h1.1
          exact ⟨h2.1, h2.2.trans h1.2.1,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok pair =>
          rcases pair with ⟨expired, rem⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := hostCloseOpt_frame proj cap hCap (some pipeFd) w1 h1.1
            refine ⟨h2.1, h2.2.trans h1.2.1, ?_, (fun _ _ h => by cases h),
              (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
            intro ch' len' hEq
            injection hEq with hCh hLen
            subst hCh hLen
            exact ⟨h1.2.2 rem rfl, hSum, hBound⟩
          | false =>
            dsimp only
            rw [hostStateT_bind_run]
            have h2 := cap_read_frame proj cap hCap w1 h1.1 pipeFd SysBridge.PIPE_READ_CHUNK
            cases hRd : (cap.files.read pipeFd SysBridge.PIPE_READ_CHUNK).run w1 with
            | mk rd w2 =>
              rw [hRd] at h2
              dsimp only
              cases rd with
              | error e =>
                dsimp only
                split
                · have h3 := ih chunks curLen iterBytes prog w2 h2.1 hSum hBound
                  exact ⟨h3.1, h3.2.1.trans (h2.2.1.trans h1.2.1), h3.2.2⟩
                · split
                  · rw [hostStateT_pure_run]
                    refine ⟨h2.1, h2.2.1.trans h1.2.1, (fun _ _ h => by cases h),
                      (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                    intro _ ch' len' _ hEq
                    injection hEq with _ hCh hLen _
                    subst hCh hLen
                    exact ⟨hSum, hBound⟩
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := hostCloseOpt_frame proj cap hCap (some pipeFd) w2 h2.1
                    exact ⟨h3.1, h3.2.trans (h2.2.1.trans h1.2.1),
                      (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
                      fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
              | ok chunk =>
                dsimp only
                by_cases hEmp : (chunk.size == 0) = true
                · rw [ite_eq_left hEmp, hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := hostCloseOpt_frame proj cap hCap (some pipeFd) w2 h2.1
                  refine ⟨h3.1, h3.2.trans (h2.2.1.trans h1.2.1), (fun _ _ h => by cases h),
                    (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                  intro _ ch' len' _ hEq
                  injection hEq with _ hCh hLen _
                  subst hCh hLen
                  exact ⟨hSum, hBound⟩
                · rw [ite_eq_right hEmp]
                  have hPushSum : ((chunks.push chunk).toList.map ByteArray.size).sum = curLen + chunk.size := by
                    simp [Array.toList_push, hSum]
                  cases maxOutputBytes? with
                  | none =>
                    have h3 := ih (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size)
                      true w2 h2.1 hPushSum (fun _ hm => by cases hm)
                    exact ⟨h3.1, h3.2.1.trans (h2.2.1.trans h1.2.1), h3.2.2⟩
                  | some maxOut =>
                    dsimp only
                    have hCurLe := hBound maxOut rfl
                    by_cases hGt : curLen + otherLen + chunk.size > maxOut
                    · rw [ite_eq_left hGt]
                      by_cases hKeep : maxOut - (curLen + otherLen) > 0
                      · rw [ite_eq_left hKeep]
                        dsimp only
                        rw [hostStateT_bind_run, hostStateT_pure_run]
                        have h3 := hostCloseOpt_frame proj cap hCap (some pipeFd) w2 h2.1
                        have hPreSz : (chunk.extract 0 (maxOut - (curLen + otherLen))).size =
                            maxOut - (curLen + otherLen) := by
                          rw [ByteArray.size_extract]; omega
                        have hPreSum :
                            ((chunks.push (chunk.extract 0 (maxOut - (curLen + otherLen)))).toList.map ByteArray.size).sum =
                              curLen + (chunk.extract 0 (maxOut - (curLen + otherLen))).size := by
                          simp [Array.toList_push, hSum]
                        refine ⟨h3.1, h3.2.trans (h2.2.1.trans h1.2.1),
                          (fun _ _ h => by cases h), ?_, (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
                        intro ch' len' hEq
                        injection hEq with hCh hLen
                        subst hCh hLen
                        refine ⟨rfl, hPreSum, ?_⟩
                        intro lim hLim
                        injection hLim with hLimEq
                        subst hLimEq
                        rw [hPreSz]
                        omega
                      · rw [ite_eq_right hKeep]
                        dsimp only
                        rw [hostStateT_bind_run, hostStateT_pure_run]
                        have h3 := hostCloseOpt_frame proj cap hCap (some pipeFd) w2 h2.1
                        refine ⟨h3.1, h3.2.trans (h2.2.1.trans h1.2.1),
                          (fun _ _ h => by cases h), ?_, (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
                        intro ch' len' hEq
                        injection hEq with hCh hLen
                        subst hCh hLen
                        exact ⟨rfl, hSum, hBound⟩
                    · rw [ite_eq_right hGt]
                      have hNextB : ∀ lim, some maxOut = some lim → (curLen + chunk.size) + otherLen ≤ lim := by
                        intro lim hLim
                        injection hLim with hLimEq
                        subst hLimEq
                        omega
                      have h3 := ih (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size)
                        true w2 h2.1 hPushSum hNextB
                      exact ⟨h3.1, h3.2.1.trans (h2.2.1.trans h1.2.1), h3.2.2⟩

private theorem hostCloseStreamState_frame {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (st : SysBridge.StreamLoopState Files.HandleId) (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.closeStreamState cap.files st).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl := by
  unfold SysBridge.closeStreamState
  rw [hostStateT_bind_run, hostStateT_bind_run]
  have h1 := hostCloseOpt_frame proj cap hCap st.inFd? w hWf
  have h2 := hostCloseOpt_frame proj cap hCap st.outFd? (Files.closeOpt cap.files st.inFd? |>.run w).2 h1.1
  have h3 := hostCloseOpt_frame proj cap hCap st.errFd?
    (Files.closeOpt cap.files st.outFd? |>.run (Files.closeOpt cap.files st.inFd? |>.run w).2).2 h2.1
  exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2)⟩

private theorem hostStepStdinIfReady_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (ready : Bool) (inFd? : Option Files.HandleId) (stdin : ByteArray)
    (startMs : Nat) (timeoutMs? : Option Nat) (stdinPos stepFuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) :
    let r := (SysBridge.stepStdinIfReady ready cap.files cap.timeRand inFd? stdin startMs timeoutMs? stdinPos stepFuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ a b c d err, r.1 = (a, b, c, d, some err) → Model.isNonOutcomeError err) ∧
    (∀ a b c e, r.1 = (a, b, c, true, e) → timeoutMs?.isSome = true) := by
  unfold SysBridge.stepStdinIfReady
  cases ready with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hostStateT_pure_run]
    exact ⟨hWf, rfl, (fun _ _ _ _ _ h => by cases h), fun _ _ _ _ h => by cases h⟩
  | true =>
    simp only [↓reduceIte]
    dsimp only [SysBridge.stepStdinOpt]
    cases inFd? with
    | none =>
      dsimp only
      rw [hostStateT_pure_run]
      exact ⟨hWf, rfl, (fun _ _ _ _ _ h => by cases h), fun _ _ _ _ h => by cases h⟩
    | some inFd =>
      dsimp only
      rw [hostStateT_bind_run]
      have h1 := hostWriteStdinStep_spec proj cap hCap inFd stdin startMs timeoutMs? stdinPos false stepFuel w hWf
      cases hWr : (SysBridge.writeStdinStep cap.files cap.timeRand inFd stdin startMs timeoutMs? stdinPos false stepFuel).run w with
      | mk wr w1 =>
        rw [hWr] at h1
        cases wr with
        | error e =>
          rw [hostStateT_pure_run]
          exact ⟨h1.1, h1.2.1,
            (fun _ _ _ _ _ h => by
              simp only [Prod.mk.injEq, Option.some.injEq] at h
              rcases h with ⟨-, -, -, -, rfl⟩
              exact h1.2.2.1 e rfl),
            fun _ _ _ _ h => by simp only [Prod.mk.injEq] at h; cases h.2.2.2.1⟩
        | ok tup =>
          rcases tup with ⟨fd', p', pr', toFlag⟩
          rw [hostStateT_pure_run]
          refine ⟨h1.1, h1.2.1, (fun _ _ _ _ _ h => by simp only [Prod.mk.injEq] at h; cases h.2.2.2.2), ?_⟩
          intro _ _ _ _ hEq
          simp only [Prod.mk.injEq] at hEq
          rcases hEq with ⟨-, -, -, hT, -⟩
          subst hT
          exact h1.2.2.2 fd' p' pr' rfl

private theorem hostStepDrainIfReady_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (ready : Bool) (pipeFd? : Option Files.HandleId) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat) (chunks : Array ByteArray) (curLen stepFuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (hSum : (chunks.toList.map ByteArray.size).sum = curLen)
    (hBound : ∀ lim, maxOutputBytes? = some lim → curLen + otherLen ≤ lim) :
    let r := (SysBridge.stepDrainIfReady ready cap.files cap.timeRand pipeFd? otherLen startMs
      timeoutMs? maxOutputBytes? chunks curLen stepFuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    (∀ ch' len', r.1 = .timedOut ch' len' →
      timeoutMs?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ ch' len', r.1 = .limitExceeded ch' len' →
      maxOutputBytes?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ fd? ch' len' pr, r.1 = .cont fd? ch' len' pr →
      (ch'.toList.map ByteArray.size).sum = len' ∧
      ∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim) ∧
    (∀ err, r.1 = .ioErr err → Model.isNonOutcomeError err) := by
  unfold SysBridge.stepDrainIfReady
  cases ready with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hostStateT_pure_run]
    refine ⟨hWf, rfl, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
    intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
  | true =>
    simp only [↓reduceIte]
    dsimp only [SysBridge.stepDrainOpt]
    cases pipeFd? with
    | none =>
      dsimp only
      rw [hostStateT_pure_run]
      refine ⟨hWf, rfl, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
      intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
    | some pipeFd =>
      dsimp only
      exact hostDrainPipeStep_spec proj cap hCap pipeFd otherLen startMs timeoutMs? maxOutputBytes?
        chunks curLen 0 false stepFuel w hWf hSum hBound

/-- Frame + outcome invariant for `SysBridge.streamPipesLoop`. -/
theorem hostStreamPipesLoop_spec {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (stdin : ByteArray) (startMs : Nat) (timeoutMs? maxOutputBytes? : Option Nat) (stepFuel : Nat)
    (st : SysBridge.StreamLoopState Files.HandleId) (ioFuel : Nat)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true)
    (hOutSum : (st.outChunks.toList.map ByteArray.size).sum = st.outLen)
    (hErrSum : (st.errChunks.toList.map ByteArray.size).sum = st.errLen)
    (hBound : ∀ lim, maxOutputBytes? = some lim → st.outLen + st.errLen ≤ lim) :
    let r := (SysBridge.streamPipesLoop cap.files cap.poll cap.timeRand stdin startMs
      timeoutMs? maxOutputBytes? stepFuel st ioFuel).run w
    Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w).tbl ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (.eof out err) => ∀ lim, maxOutputBytes? = some lim → out.size + err.size ≤ lim
    | .ok (.timedOut _ _) => timeoutMs?.isSome = true
    | .ok (.limitExceeded out err) =>
      maxOutputBytes?.isSome = true ∧
      ∀ lim, maxOutputBytes? = some lim → out.size + err.size ≤ lim := by
  induction ioFuel generalizing st w with
  | zero =>
    unfold SysBridge.streamPipesLoop
    rw [hostStateT_bind_run, hostStateT_pure_run]
    have h1 := hostCloseStreamState_frame proj cap hCap st w hWf
    exact ⟨h1.1, h1.2, mapRawError_userError_isNonOutcome _⟩
  | succ f ih =>
    unfold SysBridge.streamPipesLoop
    split
    · rw [hostStateT_pure_run]
      refine ⟨hWf, rfl, ?_⟩
      intro lim hLim
      have h1 := concatChunks_size st.outChunks st.outLen
      have h2 := concatChunks_size st.errChunks st.errLen
      have hB := hBound lim hLim
      rw [h1, h2, hOutSum, hErrSum]
      exact hB
    · rw [hostStateT_bind_run]
      have h1 := hostCheckTimedOut_spec proj cap hCap startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut cap.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1
        dsimp only
        cases ct with
        | error e =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := hostCloseStreamState_frame proj cap hCap st w1 h1.1
          exact ⟨h2.1, h2.2.trans h1.2.1, mapErrno_isNonOutcome _ _ _⟩
        | ok pair =>
          rcases pair with ⟨expired, remMs⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := hostCloseStreamState_frame proj cap hCap st w1 h1.1
            exact ⟨h2.1, h2.2.trans h1.2.1, h1.2.2 remMs rfl⟩
          | false =>
            dsimp only
            rw [hostStateT_bind_run]
            let pollTimeout? : Option Poll.Timespec := timeoutMs?.map fun _ => Poll.msToPollTimespec remMs
            have h2 := cap_ppoll_frame proj cap hCap w1 h1.1 (SysBridge.buildPollEntries st) pollTimeout?
            cases hP : (cap.poll.ppoll (SysBridge.buildPollEntries st) pollTimeout?).run w1 with
            | mk pRes w2 =>
              rw [hP] at h2
              dsimp only
              cases pRes with
              | error e =>
                dsimp only
                split
                · have h3 := ih st w2 h2.1 hOutSum hErrSum hBound
                  exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2.1), h3.2.2⟩
                · rw [hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := hostCloseStreamState_frame proj cap hCap st w2 h2.1
                  exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2.1), mapErrno_isNonOutcome _ _ _⟩
              | ok revents =>
                dsimp only
                split
                · have h3 := ih st w2 h2.1 hOutSum hErrSum hBound
                  exact ⟨h3.1, h3.2.1.trans (h2.2.trans h1.2.1), h3.2.2⟩
                · rw [hostStateT_bind_run]
                  have hIn := hostStepStdinIfReady_spec proj cap hCap
                    (SysBridge.decodeReadyFlags st revents).1 st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel w2 h2.1
                  cases hInRun : (SysBridge.stepStdinIfReady (SysBridge.decodeReadyFlags st revents).1
                      cap.files cap.timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel).run w2 with
                  | mk inRes w3 =>
                    rw [hInRun] at hIn
                    rcases inRes with ⟨inFdNext?, stdinPos', _, inTimedOut, inErr?⟩
                    dsimp only
                    cases inErr? with
                    | some err =>
                      rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                      have hc1 := hostCloseOpt_frame proj cap hCap st.outFd? w3 hIn.1
                      have hc2 := hostCloseOpt_frame proj cap hCap st.errFd? (Files.closeOpt cap.files st.outFd? |>.run w3).2 hc1.1
                      exact ⟨hc2.1, hc2.2.trans (hc1.2.trans (hIn.2.1.trans (h2.2.trans h1.2.1))),
                        hIn.2.2.1 _ _ _ _ _ rfl⟩
                    | none =>
                      dsimp only
                      by_cases hToIn : inTimedOut = true
                      · rw [ite_eq_left hToIn, hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                        have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w3 hIn.1
                        have hc2 := hostCloseOpt_frame proj cap hCap st.outFd? (Files.closeOpt cap.files inFdNext? |>.run w3).2 hc1.1
                        have hc3 := hostCloseOpt_frame proj cap hCap st.errFd?
                          (Files.closeOpt cap.files st.outFd? |>.run (Files.closeOpt cap.files inFdNext? |>.run w3).2).2 hc2.1
                        subst hToIn
                        exact ⟨hc3.1, hc3.2.trans (hc2.2.trans (hc1.2.trans (hIn.2.1.trans (h2.2.trans h1.2.1)))),
                          hIn.2.2.2 _ _ _ _ rfl⟩
                      · rw [ite_eq_right hToIn, hostStateT_bind_run]
                        have hOut := hostStepDrainIfReady_spec proj cap hCap
                          (SysBridge.decodeReadyFlags st revents).2.1 st.outFd? st.errLen startMs
                          timeoutMs? maxOutputBytes? st.outChunks st.outLen stepFuel w3 hIn.1 hOutSum hBound
                        cases hOutRun : (SysBridge.stepDrainIfReady (SysBridge.decodeReadyFlags st revents).2.1
                            cap.files cap.timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                            st.outChunks st.outLen stepFuel).run w3 with
                        | mk outStep w4 =>
                          rw [hOutRun] at hOut
                          dsimp only
                          cases outStep with
                          | ioErr err =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w4 hOut.1
                            have hc2 := hostCloseOpt_frame proj cap hCap st.errFd? (Files.closeOpt cap.files inFdNext? |>.run w4).2 hc1.1
                            exact ⟨hc2.1, hc2.2.trans (hc1.2.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1)))),
                              hOut.2.2.2.2.2 _ rfl⟩
                          | timedOut outC' outL' =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w4 hOut.1
                            have hc2 := hostCloseOpt_frame proj cap hCap st.errFd? (Files.closeOpt cap.files inFdNext? |>.run w4).2 hc1.1
                            exact ⟨hc2.1, hc2.2.trans (hc1.2.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1)))),
                              (hOut.2.2.1 _ _ rfl).1⟩
                          | limitExceeded outC' outL' =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w4 hOut.1
                            have hc2 := hostCloseOpt_frame proj cap hCap st.errFd? (Files.closeOpt cap.files inFdNext? |>.run w4).2 hc1.1
                            obtain ⟨hMaxS, hOutSum', hBOut⟩ := hOut.2.2.2.1 _ _ rfl
                            refine ⟨hc2.1, hc2.2.trans (hc1.2.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1)))),
                              hMaxS, fun lim hLim => ?_⟩
                            have hs1 := concatChunks_size outC' outL'
                            have hs2 := concatChunks_size st.errChunks st.errLen
                            have hb := hBOut lim hLim
                            rw [hs1, hs2, hOutSum', hErrSum]
                            exact hb
                          | cont outFdNext? outC' outL' _ =>
                            dsimp only
                            rw [hostStateT_bind_run]
                            obtain ⟨hOutSum', hOutB0⟩ := hOut.2.2.2.2.1 _ _ _ _ rfl
                            have hOutB : ∀ lim, maxOutputBytes? = some lim → st.errLen + outL' ≤ lim := by
                              intro lim hLim; have hb := hOutB0 lim hLim; omega
                            have hErr := hostStepDrainIfReady_spec proj cap hCap
                              (SysBridge.decodeReadyFlags st revents).2.2 st.errFd? outL' startMs
                              timeoutMs? maxOutputBytes? st.errChunks st.errLen stepFuel w4 hOut.1 hErrSum hOutB
                            cases hErrRun : (SysBridge.stepDrainIfReady (SysBridge.decodeReadyFlags st revents).2.2
                                cap.files cap.timeRand st.errFd? outL' startMs timeoutMs? maxOutputBytes?
                                st.errChunks st.errLen stepFuel).run w4 with
                            | mk errStep w5 =>
                              rw [hErrRun] at hErr
                              dsimp only
                              cases errStep with
                              | ioErr err =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w5 hErr.1
                                have hc2 := hostCloseOpt_frame proj cap hCap outFdNext? (Files.closeOpt cap.files inFdNext? |>.run w5).2 hc1.1
                                exact ⟨hc2.1, hc2.2.trans (hc1.2.trans (hErr.2.1.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1))))),
                                  hErr.2.2.2.2.2 _ rfl⟩
                              | timedOut errC' errL' =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w5 hErr.1
                                have hc2 := hostCloseOpt_frame proj cap hCap outFdNext? (Files.closeOpt cap.files inFdNext? |>.run w5).2 hc1.1
                                exact ⟨hc2.1, hc2.2.trans (hc1.2.trans (hErr.2.1.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1))))),
                                  (hErr.2.2.1 _ _ rfl).1⟩
                              | limitExceeded errC' errL' =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := hostCloseOpt_frame proj cap hCap inFdNext? w5 hErr.1
                                have hc2 := hostCloseOpt_frame proj cap hCap outFdNext? (Files.closeOpt cap.files inFdNext? |>.run w5).2 hc1.1
                                obtain ⟨hMaxS, hErrSum', hBErr⟩ := hErr.2.2.2.1 _ _ rfl
                                refine ⟨hc2.1, hc2.2.trans (hc1.2.trans (hErr.2.1.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1))))),
                                  hMaxS, fun lim hLim => ?_⟩
                                have hs1 := concatChunks_size outC' outL'
                                have hs2 := concatChunks_size errC' errL'
                                have hb := hBErr lim hLim
                                rw [hs1, hs2, hOutSum', hErrSum']
                                omega
                              | cont errFdNext? errC' errL' _ =>
                                dsimp only
                                obtain ⟨hErrSum', hErrB0⟩ := hErr.2.2.2.2.1 _ _ _ _ rfl
                                have hNextB : ∀ lim, maxOutputBytes? = some lim → outL' + errL' ≤ lim := by
                                  intro lim hLim; have hb := hErrB0 lim hLim; omega
                                split
                                · rw [hostStateT_pure_run]
                                  refine ⟨hErr.1, hErr.2.1.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1))), ?_⟩
                                  intro lim hLim
                                  have hs1 := concatChunks_size outC' outL'
                                  have hs2 := concatChunks_size errC' errL'
                                  have hb := hNextB lim hLim
                                  rw [hs1, hs2, hOutSum', hErrSum']
                                  exact hb
                                · have hRec := ih
                                    { inFd? := inFdNext?, outFd? := outFdNext?, errFd? := errFdNext?
                                      stdinPos := stdinPos', outChunks := outC', outLen := outL'
                                      errChunks := errC', errLen := errL' } w5 hErr.1 hOutSum' hErrSum' hNextB
                                  exact ⟨hRec.1, hRec.2.1.trans (hErr.2.1.trans (hOut.2.1.trans (hIn.2.1.trans (h2.2.trans h1.2.1)))),
                                    hRec.2.2⟩

end LeanSwe.Process.Proofs

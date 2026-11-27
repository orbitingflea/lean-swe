import LeanSweProofs.Process.Proofs.FullObeysFrames

/-!
Streaming fuel-loop invariants and OS-phase specifications (`spawnOsPhase`, `awaitOsPhase`,
`killGroupOsPhase`, `reapOsPhase`) over `SysPreservesFrame` for `Core.ObeysStepFromConcCell`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

private theorem fullWriteStdinStep_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (inFd : RawFd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (pos : Nat) (prog : Bool) (fuel : Nat) (w : W) (hWf : inv w) :
    let r := (SysBridge.writeStdinStep sys.files sys.timeRand inFd stdin startMs timeoutMs? pos prog fuel).run w
    inv r.2 ∧ frame w r.2 ∧
    (∀ err, r.1 = .error err → Model.isNonOutcomeError err) ∧
    (∀ fd' p' pr', r.1 = .ok (fd', p', pr', true) → timeoutMs?.isSome = true) := by
  induction fuel generalizing pos prog w with
  | zero =>
    unfold SysBridge.writeStdinStep; split
    · rw [hostStateT_bind_run, hostStateT_pure_run]
      have h1 := fullCloseOpt_frame hrefl hSys (some inFd) w hWf
      exact ⟨h1.1, h1.2, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
    · rw [hostStateT_pure_run]
      exact ⟨hWf, hrefl w, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
  | succ _ ih =>
    unfold SysBridge.writeStdinStep; split
    · rw [hostStateT_bind_run, hostStateT_pure_run]
      have h1 := fullCloseOpt_frame hrefl hSys (some inFd) w hWf
      exact ⟨h1.1, h1.2, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
    · rw [hostStateT_bind_run]
      have h1 := fullCheckTimedOut_spec hrefl hSys startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut sys.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1; dsimp only
        cases ct with
        | error _ =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := fullCloseOpt_frame hrefl hSys (some inFd) w1 h1.1
          exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2,
            (fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _),
            fun _ _ _ h => by cases h⟩
        | ok pair =>
          rcases pair with ⟨expired, rem⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := fullCloseOpt_frame hrefl hSys (some inFd) w1 h1.1
            exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, (fun _ h => by cases h), fun _ _ _ _ => h1.2.2 rem rfl⟩
          | false =>
            dsimp only; rw [hostStateT_bind_run]
            let slice := stdin.extract pos (Nat.min stdin.size (pos + SysBridge.STDIN_WRITE_CHUNK))
            have h2 := hSys.write inFd slice w1 h1.1
            cases hWr : (sys.files.write inFd slice).run w1 with
            | mk wr w2 =>
              rw [hWr] at h2; dsimp only
              cases wr with
              | ok n =>
                dsimp only; split
                · rw [hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := fullCloseOpt_frame hrefl hSys (some inFd) w2 h2.1
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                    (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                · split
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := fullCloseOpt_frame hrefl hSys (some inFd) w2 h2.1
                    exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                      (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                  · have h3 := ih (pos + n.toNat) true w2 h2.1
                    exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2.1, h3.2.2.2⟩
              | error _ =>
                dsimp only; split
                · have h3 := ih pos prog w2 h2.1
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2.1, h3.2.2.2⟩
                · split
                  · rw [hostStateT_pure_run]
                    exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, (fun _ h => by cases h), fun _ _ _ h => by cases h⟩
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := fullCloseOpt_frame hrefl hSys (some inFd) w2 h2.1
                    exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                      (fun _ h => by cases h), fun _ _ _ h => by cases h⟩

private theorem fullDrainPipeStep_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pipeFd : RawFd) (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen iterBytes : Nat) (prog : Bool) (fuel : Nat)
    (w : W) (hWf : inv w)
    (hSum : (chunks.toList.map ByteArray.size).sum = curLen)
    (hBound : ∀ lim, maxOutputBytes? = some lim → curLen + otherLen ≤ lim) :
    let r := (SysBridge.drainPipeStep sys.files sys.timeRand pipeFd otherLen startMs
      timeoutMs? maxOutputBytes? chunks curLen iterBytes prog fuel).run w
    inv r.2 ∧ frame w r.2 ∧
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
    unfold SysBridge.drainPipeStep; rw [hostStateT_pure_run]
    refine ⟨hWf, hrefl w, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
    intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
  | succ _ ih =>
    unfold SysBridge.drainPipeStep; split
    · rw [hostStateT_pure_run]
      refine ⟨hWf, hrefl w, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
      intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
    · rw [hostStateT_bind_run]
      have h1 := fullCheckTimedOut_spec hrefl hSys startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut sys.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1; dsimp only
        cases ct with
        | error _ =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := fullCloseOpt_frame hrefl hSys (some pipeFd) w1 h1.1
          exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        | ok pair =>
          rcases pair with ⟨expired, rem⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := fullCloseOpt_frame hrefl hSys (some pipeFd) w1 h1.1
            refine ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, ?_, (fun _ _ h => by cases h),
              (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
            intro ch' len' hEq; injection hEq with hCh hLen; subst hCh hLen
            exact ⟨h1.2.2 rem rfl, hSum, hBound⟩
          | false =>
            dsimp only; rw [hostStateT_bind_run]
            have h2 := hSys.read pipeFd SysBridge.PIPE_READ_CHUNK w1 h1.1
            cases hRd : (sys.files.read pipeFd SysBridge.PIPE_READ_CHUNK).run w1 with
            | mk rd w2 =>
              rw [hRd] at h2; dsimp only
              cases rd with
              | error _ =>
                dsimp only; split
                · have h3 := ih chunks curLen iterBytes prog w2 h2.1 hSum hBound
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                · split
                  · rw [hostStateT_pure_run]
                    refine ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, (fun _ _ h => by cases h),
                      (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                    intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
                  · rw [hostStateT_bind_run, hostStateT_pure_run]
                    have h3 := fullCloseOpt_frame hrefl hSys (some pipeFd) w2 h2.1
                    exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                      (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
                      fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
              | ok chunk =>
                dsimp only
                by_cases hEmp : (chunk.size == 0) = true
                · rw [ite_eq_left hEmp, hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := fullCloseOpt_frame hrefl hSys (some pipeFd) w2 h2.1
                  refine ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2), (fun _ _ h => by cases h),
                    (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                  intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hSum, hBound⟩
                · rw [ite_eq_right hEmp]
                  have hPushSum : ((chunks.push chunk).toList.map ByteArray.size).sum = curLen + chunk.size := by
                    simp [Array.toList_push, hSum]
                  cases maxOutputBytes? with
                  | none =>
                    have h3 := ih (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size)
                      true w2 h2.1 hPushSum (fun _ hm => by cases hm)
                    exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                  | some maxOut =>
                    dsimp only
                    have _ := hBound maxOut rfl
                    by_cases hGt : curLen + otherLen + chunk.size > maxOut
                    · rw [ite_eq_left hGt]
                      by_cases hKeep : maxOut - (curLen + otherLen) > 0
                      · rw [ite_eq_left hKeep]; dsimp only; rw [hostStateT_bind_run, hostStateT_pure_run]
                        have h3 := fullCloseOpt_frame hrefl hSys (some pipeFd) w2 h2.1
                        have hPreSz : (chunk.extract 0 (maxOut - (curLen + otherLen))).size =
                            maxOut - (curLen + otherLen) := by rw [ByteArray.size_extract]; omega
                        have hPreSum :
                            ((chunks.push (chunk.extract 0 (maxOut - (curLen + otherLen)))).toList.map ByteArray.size).sum =
                              curLen + (chunk.extract 0 (maxOut - (curLen + otherLen))).size := by
                          simp [Array.toList_push, hSum]
                        refine ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                          (fun _ _ h => by cases h), ?_, (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
                        intro ch' len' hEq; injection hEq with hCh hLen; subst hCh hLen
                        refine ⟨rfl, hPreSum, fun lim hLim => ?_⟩
                        injection hLim with hLimEq; subst hLimEq; rw [hPreSz]; omega
                      · rw [ite_eq_right hKeep]; dsimp only; rw [hostStateT_bind_run, hostStateT_pure_run]
                        have h3 := fullCloseOpt_frame hrefl hSys (some pipeFd) w2 h2.1
                        refine ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2),
                          (fun _ _ h => by cases h), ?_, (fun _ _ _ _ h => by cases h), fun _ h => by cases h⟩
                        intro ch' len' hEq; injection hEq with hCh hLen; subst hCh hLen
                        exact ⟨rfl, hSum, hBound⟩
                    · rw [ite_eq_right hGt]
                      have hNextB : ∀ lim, some maxOut = some lim → (curLen + chunk.size) + otherLen ≤ lim := by
                        intro lim hLim; injection hLim with hLimEq; subst hLimEq; omega
                      have h3 := ih (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size)
                        true w2 h2.1 hPushSum hNextB
                      exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩

theorem fullCloseStreamState_frame {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (st : SysBridge.StreamLoopState RawFd) (w : W) (hWf : inv w) :
    let r := (SysBridge.closeStreamState sys.files st).run w
    inv r.2 ∧ frame w r.2 := by
  unfold SysBridge.closeStreamState; rw [hostStateT_bind_run, hostStateT_bind_run]
  have h1 := fullCloseOpt_frame hrefl hSys st.inFd? w hWf
  have h2 := fullCloseOpt_frame hrefl hSys st.outFd? (Files.closeOpt sys.files st.inFd? |>.run w).2 h1.1
  have h3 := fullCloseOpt_frame hrefl hSys st.errFd?
    (Files.closeOpt sys.files st.outFd? |>.run (Files.closeOpt sys.files st.inFd? |>.run w).2).2 h2.1
  exact ⟨h3.1, htrans _ _ _ h1.2 (htrans _ _ _ h2.2 h3.2)⟩

theorem fullStreamPipesLoop_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (stdin : ByteArray) (startMs : Nat) (timeoutMs? maxOutputBytes? : Option Nat) (stepFuel : Nat)
    (st : SysBridge.StreamLoopState RawFd) (ioFuel : Nat)
    (w : W) (hWf : inv w)
    (hOutSum : (st.outChunks.toList.map ByteArray.size).sum = st.outLen)
    (hErrSum : (st.errChunks.toList.map ByteArray.size).sum = st.errLen)
    (hBound : ∀ lim, maxOutputBytes? = some lim → st.outLen + st.errLen ≤ lim) :
    let r := (SysBridge.streamPipesLoop sys.files sys.poll sys.timeRand stdin startMs
      timeoutMs? maxOutputBytes? stepFuel st ioFuel).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (.eof out err) => ∀ lim, maxOutputBytes? = some lim → out.size + err.size ≤ lim
    | .ok (.timedOut _ _) => timeoutMs?.isSome = true
    | .ok (.limitExceeded out err) =>
      maxOutputBytes?.isSome = true ∧
      ∀ lim, maxOutputBytes? = some lim → out.size + err.size ≤ lim := by
  induction ioFuel generalizing st w with
  | zero =>
    unfold SysBridge.streamPipesLoop; rw [hostStateT_bind_run, hostStateT_pure_run]
    have h1 := fullCloseStreamState_frame hrefl htrans hSys st w hWf
    exact ⟨h1.1, h1.2, mapRawError_userError_isNonOutcome _⟩
  | succ _ ih =>
    unfold SysBridge.streamPipesLoop; split
    · rw [hostStateT_pure_run]
      refine ⟨hWf, hrefl w, fun lim hLim => ?_⟩
      have h1 := concatChunks_size st.outChunks st.outLen
      have h2 := concatChunks_size st.errChunks st.errLen
      rw [h1, h2, hOutSum, hErrSum]; exact hBound lim hLim
    · rw [hostStateT_bind_run]
      have h1 := fullCheckTimedOut_spec hrefl hSys startMs timeoutMs? w hWf
      cases hCt : (TimeRand.checkTimedOut sys.timeRand startMs timeoutMs?).run w with
      | mk ct w1 =>
        rw [hCt] at h1; dsimp only
        cases ct with
        | error _ =>
          rw [hostStateT_bind_run, hostStateT_pure_run]
          have h2 := fullCloseStreamState_frame hrefl htrans hSys st w1 h1.1
          exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, mapErrno_isNonOutcome _ _ _⟩
        | ok pair =>
          rcases pair with ⟨expired, remMs⟩
          cases expired with
          | true =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            have h2 := fullCloseStreamState_frame hrefl htrans hSys st w1 h1.1
            exact ⟨h2.1, htrans _ _ _ h1.2.1 h2.2, h1.2.2 remMs rfl⟩
          | false =>
            dsimp only; rw [hostStateT_bind_run]
            let pollTimeout? : Option Poll.Timespec := timeoutMs?.map fun _ => Poll.msToPollTimespec remMs
            have h2 := hSys.ppoll (SysBridge.buildPollEntries st) pollTimeout? w1 h1.1
            cases hP : (sys.poll.ppoll (SysBridge.buildPollEntries st) pollTimeout?).run w1 with
            | mk pRes w2 =>
              rw [hP] at h2; dsimp only
              cases pRes with
              | error _ =>
                dsimp only; split
                · have h3 := ih st w2 h2.1 hOutSum hErrSum hBound
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                · rw [hostStateT_bind_run, hostStateT_pure_run]
                  have h3 := fullCloseStreamState_frame hrefl htrans hSys st w2 h2.1
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2), mapErrno_isNonOutcome _ _ _⟩
              | ok revents =>
                dsimp only; split
                · have h3 := ih st w2 h2.1 hOutSum hErrSum hBound
                  exact ⟨h3.1, htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 h3.2.1), h3.2.2⟩
                · rw [hostStateT_bind_run]
                  have hIn : let r := (SysBridge.stepStdinIfReady (SysBridge.decodeReadyFlags st revents).1
                      sys.files sys.timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel).run w2
                      inv r.2 ∧ frame w2 r.2 ∧
                      (∀ a b c d err, r.1 = (a, b, c, d, some err) → Model.isNonOutcomeError err) ∧
                      (∀ a b c e, r.1 = (a, b, c, true, e) → timeoutMs?.isSome = true) := by
                    unfold SysBridge.stepStdinIfReady
                    cases (SysBridge.decodeReadyFlags st revents).1 with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]; rw [hostStateT_pure_run]
                      exact ⟨h2.1, hrefl w2, (fun _ _ _ _ _ h => by cases h), fun _ _ _ _ h => by cases h⟩
                    | true =>
                      simp only [↓reduceIte]; dsimp only [SysBridge.stepStdinOpt]
                      cases st.inFd? with
                      | none =>
                        dsimp only; rw [hostStateT_pure_run]
                        exact ⟨h2.1, hrefl w2, (fun _ _ _ _ _ h => by cases h), fun _ _ _ _ h => by cases h⟩
                      | some inFd =>
                        dsimp only; rw [hostStateT_bind_run]
                        have hw := fullWriteStdinStep_spec hrefl htrans hSys inFd stdin startMs timeoutMs? st.stdinPos false stepFuel w2 h2.1
                        cases hWr : (SysBridge.writeStdinStep sys.files sys.timeRand inFd stdin startMs timeoutMs? st.stdinPos false stepFuel).run w2 with
                        | mk wr _ =>
                          rw [hWr] at hw
                          cases wr with
                          | error e =>
                            rw [hostStateT_pure_run]
                            exact ⟨hw.1, hw.2.1,
                              (fun _ _ _ _ _ h => by simp only [Prod.mk.injEq, Option.some.injEq] at h; rcases h with ⟨-, -, -, -, rfl⟩; exact hw.2.2.1 e rfl),
                              fun _ _ _ _ h => by simp only [Prod.mk.injEq] at h; cases h.2.2.2.1⟩
                          | ok tup =>
                            rcases tup with ⟨fd', p', pr', toFlag⟩; rw [hostStateT_pure_run]
                            refine ⟨hw.1, hw.2.1, (fun _ _ _ _ _ h => by simp only [Prod.mk.injEq] at h; cases h.2.2.2.2), ?_⟩
                            intro _ _ _ _ hEq; simp only [Prod.mk.injEq] at hEq; rcases hEq with ⟨-, -, -, hT, -⟩; subst hT
                            exact hw.2.2.2 fd' p' pr' rfl
                  cases hInRun : (SysBridge.stepStdinIfReady (SysBridge.decodeReadyFlags st revents).1
                      sys.files sys.timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel).run w2 with
                  | mk inRes w3 =>
                    rw [hInRun] at hIn
                    rcases inRes with ⟨inFdNext?, stdinPos', _, inTimedOut, inErr?⟩
                    have hf3 : frame w w3 := htrans _ _ _ h1.2.1 (htrans _ _ _ h2.2 hIn.2.1)
                    dsimp only
                    cases inErr? with
                    | some err =>
                      rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                      have hc1 := fullCloseOpt_frame hrefl hSys st.outFd? w3 hIn.1
                      have hc2 := fullCloseOpt_frame hrefl hSys st.errFd? (Files.closeOpt sys.files st.outFd? |>.run w3).2 hc1.1
                      exact ⟨hc2.1, htrans _ _ _ hf3 (htrans _ _ _ hc1.2 hc2.2), hIn.2.2.1 _ _ _ _ _ rfl⟩
                    | none =>
                      dsimp only
                      by_cases hToIn : inTimedOut = true
                      · rw [ite_eq_left hToIn, hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                        have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w3 hIn.1
                        have hc2 := fullCloseOpt_frame hrefl hSys st.outFd? (Files.closeOpt sys.files inFdNext? |>.run w3).2 hc1.1
                        have hc3 := fullCloseOpt_frame hrefl hSys st.errFd?
                          (Files.closeOpt sys.files st.outFd? |>.run (Files.closeOpt sys.files inFdNext? |>.run w3).2).2 hc2.1
                        subst hToIn
                        exact ⟨hc3.1, htrans _ _ _ hf3 (htrans _ _ _ hc1.2 (htrans _ _ _ hc2.2 hc3.2)), hIn.2.2.2 _ _ _ _ rfl⟩
                      · rw [ite_eq_right hToIn, hostStateT_bind_run]
                        have stepDr : ∀ (rdy : Bool) (pfd? : Option RawFd) (oLen : Nat) (chs : Array ByteArray) (cLen : Nat) (wx : W),
                            inv wx → (chs.toList.map ByteArray.size).sum = cLen →
                            (∀ lim, maxOutputBytes? = some lim → cLen + oLen ≤ lim) →
                            let r := (SysBridge.stepDrainIfReady rdy sys.files sys.timeRand pfd? oLen startMs timeoutMs? maxOutputBytes? chs cLen stepFuel).run wx
                            inv r.2 ∧ frame wx r.2 ∧
                            (∀ ch' len', r.1 = .timedOut ch' len' → timeoutMs?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧ ∀ lim, maxOutputBytes? = some lim → len' + oLen ≤ lim) ∧
                            (∀ ch' len', r.1 = .limitExceeded ch' len' → maxOutputBytes?.isSome = true ∧ (ch'.toList.map ByteArray.size).sum = len' ∧ ∀ lim, maxOutputBytes? = some lim → len' + oLen ≤ lim) ∧
                            (∀ fd? ch' len' pr, r.1 = .cont fd? ch' len' pr → (ch'.toList.map ByteArray.size).sum = len' ∧ ∀ lim, maxOutputBytes? = some lim → len' + oLen ≤ lim) ∧
                            (∀ err, r.1 = .ioErr err → Model.isNonOutcomeError err) := by
                          intro rdy pfd? oLen chs cLen wx hwx hS hB
                          unfold SysBridge.stepDrainIfReady
                          cases rdy with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]; rw [hostStateT_pure_run]
                            refine ⟨hwx, hrefl wx, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                            intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hS, hB⟩
                          | true =>
                            simp only [↓reduceIte]; dsimp only [SysBridge.stepDrainOpt]
                            cases pfd? with
                            | none =>
                              dsimp only; rw [hostStateT_pure_run]
                              refine ⟨hwx, hrefl wx, (fun _ _ h => by cases h), (fun _ _ h => by cases h), ?_, fun _ h => by cases h⟩
                              intro _ ch' len' _ hEq; injection hEq with _ hCh hLen _; subst hCh hLen; exact ⟨hS, hB⟩
                            | some pfd =>
                              exact fullDrainPipeStep_spec hrefl htrans hSys pfd oLen startMs timeoutMs? maxOutputBytes? chs cLen 0 false stepFuel wx hwx hS hB
                        have hOut := stepDr (SysBridge.decodeReadyFlags st revents).2.1 st.outFd? st.errLen st.outChunks st.outLen w3 hIn.1 hOutSum hBound
                        cases hOutRun : (SysBridge.stepDrainIfReady (SysBridge.decodeReadyFlags st revents).2.1
                            sys.files sys.timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                            st.outChunks st.outLen stepFuel).run w3 with
                        | mk outStep w4 =>
                          rw [hOutRun] at hOut
                          have hf4 : frame w w4 := htrans _ _ _ hf3 hOut.2.1
                          dsimp only
                          cases outStep with
                          | ioErr _ =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w4 hOut.1
                            have hc2 := fullCloseOpt_frame hrefl hSys st.errFd? (Files.closeOpt sys.files inFdNext? |>.run w4).2 hc1.1
                            exact ⟨hc2.1, htrans _ _ _ hf4 (htrans _ _ _ hc1.2 hc2.2), hOut.2.2.2.2.2 _ rfl⟩
                          | timedOut _ _ =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w4 hOut.1
                            have hc2 := fullCloseOpt_frame hrefl hSys st.errFd? (Files.closeOpt sys.files inFdNext? |>.run w4).2 hc1.1
                            exact ⟨hc2.1, htrans _ _ _ hf4 (htrans _ _ _ hc1.2 hc2.2), (hOut.2.2.1 _ _ rfl).1⟩
                          | limitExceeded outC' outL' =>
                            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                            have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w4 hOut.1
                            have hc2 := fullCloseOpt_frame hrefl hSys st.errFd? (Files.closeOpt sys.files inFdNext? |>.run w4).2 hc1.1
                            obtain ⟨hMaxS, hOutSum', hBOut⟩ := hOut.2.2.2.1 _ _ rfl
                            refine ⟨hc2.1, htrans _ _ _ hf4 (htrans _ _ _ hc1.2 hc2.2), hMaxS, fun lim hLim => ?_⟩
                            rw [concatChunks_size outC' outL', concatChunks_size st.errChunks st.errLen, hOutSum', hErrSum]
                            exact hBOut lim hLim
                          | cont outFdNext? outC' outL' _ =>
                            dsimp only; rw [hostStateT_bind_run]
                            obtain ⟨hOutSum', hOutB0⟩ := hOut.2.2.2.2.1 _ _ _ _ rfl
                            have hOutB : ∀ lim, maxOutputBytes? = some lim → st.errLen + outL' ≤ lim := by
                              intro lim hLim; have hb := hOutB0 lim hLim; omega
                            have hErr := stepDr (SysBridge.decodeReadyFlags st revents).2.2 st.errFd? outL' st.errChunks st.errLen w4 hOut.1 hErrSum hOutB
                            cases hErrRun : (SysBridge.stepDrainIfReady (SysBridge.decodeReadyFlags st revents).2.2
                                sys.files sys.timeRand st.errFd? outL' startMs timeoutMs? maxOutputBytes?
                                st.errChunks st.errLen stepFuel).run w4 with
                            | mk errStep w5 =>
                              rw [hErrRun] at hErr
                              have hf5 : frame w w5 := htrans _ _ _ hf4 hErr.2.1
                              dsimp only
                              cases errStep with
                              | ioErr _ =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w5 hErr.1
                                have hc2 := fullCloseOpt_frame hrefl hSys outFdNext? (Files.closeOpt sys.files inFdNext? |>.run w5).2 hc1.1
                                exact ⟨hc2.1, htrans _ _ _ hf5 (htrans _ _ _ hc1.2 hc2.2), hErr.2.2.2.2.2 _ rfl⟩
                              | timedOut _ _ =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w5 hErr.1
                                have hc2 := fullCloseOpt_frame hrefl hSys outFdNext? (Files.closeOpt sys.files inFdNext? |>.run w5).2 hc1.1
                                exact ⟨hc2.1, htrans _ _ _ hf5 (htrans _ _ _ hc1.2 hc2.2), (hErr.2.2.1 _ _ rfl).1⟩
                              | limitExceeded errC' errL' =>
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                have hc1 := fullCloseOpt_frame hrefl hSys inFdNext? w5 hErr.1
                                have hc2 := fullCloseOpt_frame hrefl hSys outFdNext? (Files.closeOpt sys.files inFdNext? |>.run w5).2 hc1.1
                                obtain ⟨hMaxS, hErrSum', hBErr⟩ := hErr.2.2.2.1 _ _ rfl
                                refine ⟨hc2.1, htrans _ _ _ hf5 (htrans _ _ _ hc1.2 hc2.2), hMaxS, fun lim hLim => ?_⟩
                                have hb := hBErr lim hLim
                                rw [concatChunks_size outC' outL', concatChunks_size errC' errL', hOutSum', hErrSum']; omega
                              | cont errFdNext? errC' errL' _ =>
                                dsimp only
                                obtain ⟨hErrSum', hErrB0⟩ := hErr.2.2.2.2.1 _ _ _ _ rfl
                                have hNextB : ∀ lim, maxOutputBytes? = some lim → outL' + errL' ≤ lim := by
                                  intro lim hLim; have hb := hErrB0 lim hLim; omega
                                split
                                · rw [hostStateT_pure_run]
                                  refine ⟨hErr.1, hf5, fun lim hLim => ?_⟩
                                  rw [concatChunks_size outC' outL', concatChunks_size errC' errL', hOutSum', hErrSum']
                                  exact hNextB lim hLim
                                · have hRec := ih
                                    { inFd? := inFdNext?, outFd? := outFdNext?, errFd? := errFdNext?
                                      stdinPos := stdinPos', outChunks := outC', outLen := outL'
                                      errChunks := errC', errLen := errL' } w5 hErr.1 hOutSum' hErrSum' hNextB
                                  exact ⟨hRec.1, htrans _ _ _ hf5 hRec.2.1, hRec.2.2⟩

end LeanSwe.Process.Proofs

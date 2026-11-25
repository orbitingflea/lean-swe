import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepSpawnKill
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesPipeHelpers

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

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

private theorem stepBoxStdin_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (st : BoxStreamState Nat) (inRev? : Option Poll.PollEvents)
    (stdin : ByteArray) (startMs toMs stepFuel : Nat) :
    PreservesProj proj (stepBoxStdin cap.files cap.timeRand st inRev? stdin startMs toMs stepFuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true → ∀ e,
      ((stepBoxStdin cap.files cap.timeRand st inRev? stdin startMs toMs stepFuel).run w).1.2.2.2 = some e →
      e.message ≠ "" := by
  unfold stepBoxStdin
  cases st.inFd? with
  | none => exact ⟨preservesProj_pure _, fun _ _ _ h => by cases h⟩
  | some inFd =>
    cases inRev? with
    | none => exact ⟨preservesProj_pure _, fun _ _ _ h => by cases h⟩
    | some ev =>
      dsimp only
      cases (ev.pollerr || ev.pollhup || ev.pollnval) with
      | true =>
        simp only [↓reduceIte]
        refine ⟨preservesProj_bind (preservesProj_closeOpt hCap (some inFd)) fun _ => preservesProj_pure _, ?_⟩
        intro w _ e h
        simp only [stateM_bind_run, stateM_pure_run] at h
        cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ev.pollout with
        | true =>
          simp only [↓reduceIte]
          have ⟨hPw, hEw⟩ := writeStdinStep_spec hCap inFd stdin startMs (some toMs) st.stdinPos false stepFuel
          refine ⟨preservesProj_bind hPw fun r => ?_, fun w hWf e h => ?_⟩
          · cases r with
            | error _ => exact preservesProj_pure _
            | ok res => rcases res with ⟨_, _, _, _⟩; exact preservesProj_pure _
          · rw [stateM_bind_run] at h
            cases hW : ((writeStdinStep cap.files cap.timeRand inFd stdin startMs (some toMs) st.stdinPos false stepFuel).run w).1 with
            | error e' =>
              rw [hW] at h
              simp only [stateM_pure_run] at h
              injection h with hEqE
              subst hEqE
              exact hEw w hWf e' hW
            | ok res =>
              rcases res with ⟨_, _, _, _⟩
              rw [hW] at h
              simp only [stateM_pure_run] at h
              cases h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨preservesProj_pure _, fun _ _ _ h => by cases h⟩

private theorem stepBoxPipe_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (ready : Bool) (fd? : Option Nat) (chunks : Array ByteArray) (curLen otherLen startMs toMs : Nat)
    (maxOut? : Option Nat) (stepFuel : Nat)
    (hSum : curLen = (chunks.toList.map ByteArray.size).sum)
    (hBnd : ∀ m, maxOut? = some m → curLen + otherLen ≤ m) :
    PreservesProj proj (stepBoxPipe cap.files cap.timeRand ready fd? chunks curLen otherLen startMs toMs maxOut? stepFuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      PipeStepInv otherLen maxOut?
        ((stepBoxPipe cap.files cap.timeRand ready fd? chunks curLen otherLen startMs toMs maxOut? stepFuel).run w).1 := by
  unfold stepBoxPipe
  cases ready with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨preservesProj_pure _, fun _ _ => ⟨hSum, hBnd⟩⟩
  | true =>
    simp only [↓reduceIte]
    cases fd? with
    | none => exact ⟨preservesProj_pure _, fun _ _ => ⟨hSum, hBnd⟩⟩
    | some pfd => exact drainPipeStep_spec hCap pfd otherLen startMs (some toMs) maxOut? chunks curLen 0 false stepFuel hSum hBnd

private theorem preservesProj_stepBoxStatus {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (stReady : Bool) (st : BoxStreamState Nat) :
    PreservesProj proj (stepBoxStatus cap.files stReady st) := by
  unfold stepBoxStatus
  cases stReady with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact preservesProj_pure _
  | true =>
    simp only [↓reduceIte]
    cases st.statusFd? with
    | none => exact preservesProj_pure _
    | some sfd =>
      refine preservesProj_bind (preservesProj_readInitStatusStep hCap sfd st.statusBuf 16) fun r => ?_
      rcases r with ⟨_, _, _⟩
      exact preservesProj_pure _

/-- `readBoxStreamLoop` preserves `proj`, bounds `stdout.size + stderr.size` by `maxOut?`, and ensures non-negative outcome and non-empty error messages. -/
theorem readBoxStreamLoop_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (program cwd : String) (stdin : ByteArray) (startMs toMs : Nat) (maxOut? : Option Nat) (stepFuel : Nat) :
    ∀ (st : BoxStreamState Nat) (fuel : Nat),
      st.outLen = (st.outChunks.toList.map ByteArray.size).sum →
      st.errLen = (st.errChunks.toList.map ByteArray.size).sum →
      (∀ m, maxOut? = some m → st.outLen + st.errLen ≤ m) →
      PreservesProj proj (readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs toMs maxOut? stepFuel st fuel) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        StreamResInv maxOut? ((readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs toMs maxOut? stepFuel st fuel).run w).1
  | st, 0, _, _, _ =>
    ⟨preservesProj_bind (preservesProj_closeBoxStreamState hCap st) (fun _ => preservesProj_pure _),
     fun _ _ => mapRawError_ioError_ne_empty _ _⟩
  | st, fuel + 1, hOut, hErr, hBnd => by
    cases hDone : (st.outFd?.isNone && st.errFd?.isNone && st.statusFd?.isNone) with
    | true =>
      rw [readBoxStreamLoop]
      simp only [hDone, ↓reduceIte]
      exact ⟨preservesProj_bind (preservesProj_closeOpt hCap st.inFd?) (fun _ => preservesProj_pure _),
        fun _ _ => classify_streamResInv program cwd false false st.statusMsg? st.outChunks st.errChunks st.outLen st.errLen maxOut? hOut hErr hBnd⟩
    | false =>
      have hTo := preservesProj_checkTimedOut hCap startMs (some toMs)
      have hPoll : ∀ ts, PreservesProj proj (cap.poll.ppoll (buildBoxPollEntries st) ts) := fun ts =>
        preservesProj_of_seqUnit _ fun u hu => (hCap u (.pollPpoll (buildBoxPollEntries st) ts) hu).2
      have hCombined : ∀ w, rawHostWorldWf (proj w) = true →
          let r := (readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs toMs maxOut? stepFuel st (fuel + 1)).run w
          proj r.2 = proj w ∧ StreamResInv maxOut? r.1 := by
        intro w hWf
        let Q : Except SandboxError SandboxResult → W → Prop := fun res s => proj s = proj w ∧ StreamResInv maxOut? res
        change Q ((readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs toMs maxOut? stepFuel st (fuel + 1)).run w).1
          ((readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs toMs maxOut? stepFuel st (fuel + 1)).run w).2
        rw [readBoxStreamLoop]
        simp only [hDone, Bool.false_eq_true, ↓reduceIte]
        refine preserves_bind_eq rfl hWf hTo fun rTo1 s hEq => ?_
        cases rTo1 with
        | error err =>
          dsimp only
          exact preserves_err_eq hEq hWf (preservesProj_closeBoxStreamState hCap st) fun s' hEq' =>
            ⟨hEq', mapRawError_ioError_ne_empty _ _⟩
        | ok pair1 =>
          rcases pair1 with ⟨b1, rem1⟩
          cases b1 with
          | true =>
            dsimp only
            exact preserves_err_eq hEq hWf (preservesProj_closeBoxStreamState hCap st) fun s' hEq' =>
              ⟨hEq', classify_streamResInv program cwd true false st.statusMsg? st.outChunks st.errChunks st.outLen st.errLen maxOut? hOut hErr hBnd⟩
          | false =>
            dsimp only
            refine preserves_bind_eq hEq hWf (hPoll (some (Poll.msToPollTimespec rem1))) fun rP s hEq => ?_
            cases rP with
            | error err =>
              dsimp only
              cases hEi : (err == Errno.EINTR) with
              | true =>
                simp only [↓reduceIte]
                have ⟨hPr, hIr⟩ := readBoxStreamLoop_spec hCap program cwd stdin startMs toMs maxOut? stepFuel st fuel hOut hErr hBnd
                have hWfs : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                exact ⟨(hPr s hWfs).trans hEq, hIr s hWfs⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact preserves_err_eq hEq hWf (preservesProj_closeBoxStreamState hCap st) fun s' hEq' =>
                  ⟨hEq', mapRawError_ioError_ne_empty _ _⟩
            | ok revents =>
              dsimp only
              rcases hDec : decodeBoxReadyFlags st revents with ⟨inRev?, outReady, errReady, stReady⟩
              dsimp only
              cases hIdle : isBoxPollIdle inRev? outReady errReady stReady with
              | true =>
                simp only [↓reduceIte]
                refine preserves_bind_eq hEq hWf hTo fun rTo2 s hEq => ?_
                cases rTo2 with
                | error err =>
                  dsimp only
                  exact preserves_err_eq hEq hWf (preservesProj_closeBoxStreamState hCap st) fun s' hEq' =>
                    ⟨hEq', mapRawError_ioError_ne_empty _ _⟩
                | ok pair2 =>
                  rcases pair2 with ⟨b2, _⟩
                  cases b2 with
                  | true =>
                    dsimp only
                    exact preserves_err_eq hEq hWf (preservesProj_closeBoxStreamState hCap st) fun s' hEq' =>
                      ⟨hEq', classify_streamResInv program cwd true false st.statusMsg? st.outChunks st.errChunks st.outLen st.errLen maxOut? hOut hErr hBnd⟩
                  | false =>
                    dsimp only
                    have ⟨hPr, hIr⟩ := readBoxStreamLoop_spec hCap program cwd stdin startMs toMs maxOut? stepFuel st fuel hOut hErr hBnd
                    have hWfs : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                    exact ⟨(hPr s hWfs).trans hEq, hIr s hWfs⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                have ⟨hPin, hEin⟩ := stepBoxStdin_spec hCap st inRev? stdin startMs toMs stepFuel
                have hWfs : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                rw [stateM_bind_run]
                let s1 := ((stepBoxStdin cap.files cap.timeRand st inRev? stdin startMs toMs stepFuel).run s).2
                have hEq1 : proj s1 = proj w := (hPin s hWfs).trans hEq
                cases hIn : ((stepBoxStdin cap.files cap.timeRand st inRev? stdin startMs toMs stepFuel).run s).1 with
                | mk inFdNext? rest1 =>
                  rcases rest1 with ⟨stdinPos', inTimedOut, inErr?⟩
                  dsimp only
                  cases hIE : inErr? with
                  | some e =>
                    dsimp only
                    have hMsgE : e.message ≠ "" := hEin s hWfs e (by rw [hIn, hIE])
                    refine preserves_bind_eq (w := s1) hEq1 hWf (preservesProj_closeOpt hCap st.outFd?) fun _ s hEq => ?_
                    refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.errFd?) fun _ s hEq => ?_
                    exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                      ⟨hEq', hMsgE⟩
                  | none =>
                    dsimp only
                    cases inTimedOut with
                    | true =>
                      simp only [↓reduceIte]
                      refine preserves_bind_eq (w := s1) hEq1 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                      refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.outFd?) fun _ s hEq => ?_
                      refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.errFd?) fun _ s hEq => ?_
                      exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                        ⟨hEq', classify_streamResInv program cwd true false st.statusMsg? st.outChunks st.errChunks st.outLen st.errLen maxOut? hOut hErr hBnd⟩
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      have ⟨hPout, hIout⟩ := stepBoxPipe_spec hCap outReady st.outFd? st.outChunks st.outLen st.errLen startMs toMs maxOut? stepFuel hOut hBnd
                      have hWfs1 : rawHostWorldWf (proj s1) = true := by rw [hEq1]; exact hWf
                      rw [stateM_bind_run]
                      let s2 := ((stepBoxPipe cap.files cap.timeRand outReady st.outFd? st.outChunks st.outLen st.errLen startMs toMs maxOut? stepFuel).run s1).2
                      have hEq2 : proj s2 = proj w := (hPout s1 hWfs1).trans hEq1
                      have hOutInv := hIout s1 hWfs1
                      cases hRo : ((stepBoxPipe cap.files cap.timeRand outReady st.outFd? st.outChunks st.outLen st.errLen startMs toMs maxOut? stepFuel).run s1).1 with
                      | ioErr e =>
                        rw [hRo] at hOutInv
                        dsimp only
                        refine preserves_bind_eq (w := s2) hEq2 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.errFd?) fun _ s hEq => ?_
                        exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                          ⟨hEq', hOutInv⟩
                      | timedOut outChunks' outLen' =>
                        rw [hRo] at hOutInv
                        dsimp only
                        refine preserves_bind_eq (w := s2) hEq2 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.errFd?) fun _ s hEq => ?_
                        exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                          ⟨hEq', classify_streamResInv program cwd true false st.statusMsg? outChunks' st.errChunks outLen' st.errLen maxOut? hOutInv.1 hErr hOutInv.2⟩
                      | limitExceeded outChunks' outLen' =>
                        rw [hRo] at hOutInv
                        dsimp only
                        refine preserves_bind_eq (w := s2) hEq2 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap st.errFd?) fun _ s hEq => ?_
                        exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                          ⟨hEq', classify_streamResInv program cwd false true st.statusMsg? outChunks' st.errChunks outLen' st.errLen maxOut? hOutInv.1 hErr hOutInv.2⟩
                      | cont outFdNext? outChunks' outLen' _ =>
                        rw [hRo] at hOutInv
                        dsimp only
                        have hBndE : ∀ m, maxOut? = some m → st.errLen + outLen' ≤ m := fun m hm => by
                          have := hOutInv.2 m hm; omega
                        have ⟨hPerr, hIerr⟩ := stepBoxPipe_spec hCap errReady st.errFd? st.errChunks st.errLen outLen' startMs toMs maxOut? stepFuel hErr hBndE
                        have hWfs2 : rawHostWorldWf (proj s2) = true := by rw [hEq2]; exact hWf
                        rw [stateM_bind_run]
                        let s3 := ((stepBoxPipe cap.files cap.timeRand errReady st.errFd? st.errChunks st.errLen outLen' startMs toMs maxOut? stepFuel).run s2).2
                        have hEq3 : proj s3 = proj w := (hPerr s2 hWfs2).trans hEq2
                        have hErrInv := hIerr s2 hWfs2
                        cases hRe : ((stepBoxPipe cap.files cap.timeRand errReady st.errFd? st.errChunks st.errLen outLen' startMs toMs maxOut? stepFuel).run s2).1 with
                        | ioErr e =>
                          rw [hRe] at hErrInv
                          dsimp only
                          refine preserves_bind_eq (w := s3) hEq3 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                          refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap outFdNext?) fun _ s hEq => ?_
                          exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                            ⟨hEq', hErrInv⟩
                        | timedOut errChunks' errLen' =>
                          rw [hRe] at hErrInv
                          dsimp only
                          have hBnd' : ∀ m, maxOut? = some m → outLen' + errLen' ≤ m := fun m hm => by
                            have := hErrInv.2 m hm; omega
                          refine preserves_bind_eq (w := s3) hEq3 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                          refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap outFdNext?) fun _ s hEq => ?_
                          exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                            ⟨hEq', classify_streamResInv program cwd true false st.statusMsg? outChunks' errChunks' outLen' errLen' maxOut? hOutInv.1 hErrInv.1 hBnd'⟩
                        | limitExceeded errChunks' errLen' =>
                          rw [hRe] at hErrInv
                          dsimp only
                          have hBnd' : ∀ m, maxOut? = some m → outLen' + errLen' ≤ m := fun m hm => by
                            have := hErrInv.2 m hm; omega
                          refine preserves_bind_eq (w := s3) hEq3 hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                          refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap outFdNext?) fun _ s hEq => ?_
                          exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap st.statusFd?) fun s' hEq' =>
                            ⟨hEq', classify_streamResInv program cwd false true st.statusMsg? outChunks' errChunks' outLen' errLen' maxOut? hOutInv.1 hErrInv.1 hBnd'⟩
                        | cont errFdNext? errChunks' errLen' _ =>
                          rw [hRe] at hErrInv
                          dsimp only
                          have hBnd' : ∀ m, maxOut? = some m → outLen' + errLen' ≤ m := fun m hm => by
                            have := hErrInv.2 m hm; omega
                          refine preserves_bind_eq (w := s3) hEq3 hWf (preservesProj_stepBoxStatus hCap stReady st) fun rSt s hEq => ?_
                          rcases rSt with ⟨stFdNext?, stBuf', stMsgNext?⟩
                          dsimp only
                          cases hEarly : isEarlyAbortStatus stMsgNext? with
                          | true =>
                            simp only [↓reduceIte]
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap inFdNext?) fun _ s hEq => ?_
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap outFdNext?) fun _ s hEq => ?_
                            refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap errFdNext?) fun _ s hEq => ?_
                            exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap stFdNext?) fun s' hEq' =>
                              ⟨hEq', classify_streamResInv program cwd false false stMsgNext? outChunks' errChunks' outLen' errLen' maxOut? hOutInv.1 hErrInv.1 hBnd'⟩
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            have ⟨hPr, hIr⟩ := readBoxStreamLoop_spec hCap program cwd stdin startMs toMs maxOut? stepFuel
                              { inFd? := inFdNext?, outFd? := outFdNext?, errFd? := errFdNext?, statusFd? := stFdNext?,
                                stdinPos := stdinPos', outChunks := outChunks', outLen := outLen',
                                errChunks := errChunks', errLen := errLen', statusBuf := stBuf', statusMsg? := stMsgNext? }
                              fuel hOutInv.1 hErrInv.1 hBnd'
                            have hWfs : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
                            exact ⟨(hPr s hWfs).trans hEq, hIr s hWfs⟩
      exact ⟨fun w hWf => (hCombined w hWf).1, fun w hWf => (hCombined w hWf).2⟩

/-- `readBoxOutputCore` preserves `proj`, bounds `stdout.size + stderr.size` by `maxOut?`, and ensures non-negative outcome and non-empty error messages. -/
theorem readBoxOutputCore_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (program cwd : String) (inFd0? outFd0? errFd0? statusFd0? goFd0? : Option Nat)
    (stdin : ByteArray) (timeoutMs : Nat) (maxOut? : Option Nat) (eintrFuel ioFuel : Nat) :
    PreservesProj proj (readBoxOutputCore cap.files cap.poll cap.timeRand program cwd inFd0? outFd0? errFd0? statusFd0? goFd0? stdin timeoutMs maxOut? eintrFuel ioFuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      match ((readBoxOutputCore cap.files cap.poll cap.timeRand program cwd inFd0? outFd0? errFd0? statusFd0? goFd0? stdin timeoutMs maxOut? eintrFuel ioFuel).run w).1 with
      | .ok res => outcomeNonNeg res.outcome ∧ (∀ m, maxOut? = some m → res.stdout.size + res.stderr.size ≤ m)
      | .error err => err.message ≠ "" := by
  have hSetup : PreservesProj proj (setupStdinPipe cap.files stdin inFd0?) := by
    unfold setupStdinPipe
    refine preservesProj_ite (preservesProj_bind (preservesProj_closeOpt hCap inFd0?) (fun _ => preservesProj_pure none)) ?_
    cases inFd0? with
    | none => exact preservesProj_pure none
    | some inFd =>
      exact preservesProj_bind
        (preservesProj_of_seqUnit _ fun u hu => (hCap u (.filesFcntl inFd (.setFl true false)) hu).2)
        (fun _ => preservesProj_pure (some inFd))
  have hBoth : ∀ w, rawHostWorldWf (proj w) = true →
      let r := (readBoxOutputCore cap.files cap.poll cap.timeRand program cwd inFd0? outFd0? errFd0? statusFd0? goFd0? stdin timeoutMs maxOut? eintrFuel ioFuel).run w
      proj r.2 = proj w ∧ StreamResInv maxOut? r.1 := by
    intro w hWf
    let Q : Except SandboxError SandboxResult → W → Prop := fun res s => proj s = proj w ∧ StreamResInv maxOut? res
    have hAfterGo : ∀ s, proj s = proj w →
        let rest : StateM W (Except SandboxError SandboxResult) := do
          let inFd? ← setupStdinPipe cap.files stdin inFd0?
          Files.setNonblockingOpt cap.files outFd0?
          Files.setNonblockingOpt cap.files errFd0?
          Files.setNonblockingOpt cap.files statusFd0?
          match ← TimeRand.monoNowMs cap.timeRand with
          | .error e =>
            Files.closeOpt cap.files inFd?
            Files.closeOpt cap.files outFd0?
            Files.closeOpt cap.files errFd0?
            Files.closeOpt cap.files statusFd0?
            return .error (Internal.mapRawError (.ioError none e s!"clock_gettime: {Errno.name e}"))
          | .ok startMs =>
            readBoxStreamLoop cap.files cap.poll cap.timeRand program cwd stdin startMs (Nat.max 1 timeoutMs) maxOut? eintrFuel
              { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0?, statusFd? := statusFd0? } ioFuel
        Q (rest.run s).1 (rest.run s).2 := by
      intro s hEq
      dsimp only
      refine preserves_bind_eq hEq hWf hSetup fun inFd? s hEq => ?_
      refine preserves_bind_eq hEq hWf (preservesProj_setNonblockingOpt hCap outFd0?) fun _ s hEq => ?_
      refine preserves_bind_eq hEq hWf (preservesProj_setNonblockingOpt hCap errFd0?) fun _ s hEq => ?_
      refine preserves_bind_eq hEq hWf (preservesProj_setNonblockingOpt hCap statusFd0?) fun _ s hEq => ?_
      refine preserves_bind_eq hEq hWf (preservesProj_monoNowMs hCap) fun rNow s hEq => ?_
      cases rNow with
      | error err =>
        dsimp only
        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap inFd?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap outFd0?) fun _ s hEq => ?_
        refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap errFd0?) fun _ s hEq => ?_
        exact preserves_err_eq hEq hWf (preservesProj_closeOpt hCap statusFd0?) fun s' hEq' =>
          ⟨hEq', mapRawError_ioError_ne_empty _ _⟩
      | ok startMs =>
        dsimp only
        have ⟨hPl, hIl⟩ := readBoxStreamLoop_spec hCap program cwd stdin startMs (Nat.max 1 timeoutMs) maxOut? eintrFuel
          { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0?, statusFd? := statusFd0? } ioFuel rfl rfl (fun m _ => Nat.zero_le m)
        have hWfs : rawHostWorldWf (proj s) = true := by rw [hEq]; exact hWf
        exact ⟨(hPl s hWfs).trans hEq, hIl s hWfs⟩
    change Q ((readBoxOutputCore cap.files cap.poll cap.timeRand program cwd inFd0? outFd0? errFd0? statusFd0? goFd0? stdin timeoutMs maxOut? eintrFuel ioFuel).run w).1
      ((readBoxOutputCore cap.files cap.poll cap.timeRand program cwd inFd0? outFd0? errFd0? statusFd0? goFd0? stdin timeoutMs maxOut? eintrFuel ioFuel).run w).2
    unfold readBoxOutputCore
    cases goFd0? with
    | none =>
      dsimp only
      exact hAfterGo w rfl
    | some goFd =>
      dsimp only
      refine preserves_bind_eq rfl hWf (preservesProj_writeAllFd hCap goFd _ 0 eintrFuel) fun _ s hEq => ?_
      refine preserves_bind_eq hEq hWf (preservesProj_closeOpt hCap (some goFd)) fun _ s hEq => ?_
      exact hAfterGo s hEq
  exact ⟨fun w hWf => (hBoth w hWf).1, fun w hWf => (hBoth w hWf).2⟩

end LeanSwe.ProcessSandbox.Raw.Proofs

import LeanSwe.Process.Proofs.SysBridge.StreamSteps

/-!
Multiplexed `ppoll` streaming loop (`streamPipesLoop`) descriptor-conservation and
output-cap specification for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

theorem streamPipesLoop_spec {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (poll : Poll.PollOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hCloseO : ∀ s h, openFds ((files.close h).run s).2 = (openFds s).erase h)
    (hRead : ∀ s h c, getTbl ((files.read h c).run s).2 = getTbl s ∧
      openFds ((files.read h c).run s).2 = openFds s)
    (hWrite : ∀ s h d, getTbl ((files.write h d).run s).2 = getTbl s ∧
      openFds ((files.write h d).run s).2 = openFds s)
    (hPoll : ∀ s entries to, getTbl ((poll.ppoll entries to).run s).2 = getTbl s ∧
      openFds ((poll.ppoll entries to).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    {errR outR inW : fd} (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW)
    (base : List fd)
    (stdin : ByteArray) (startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat) (stepFuel : Nat)
    (bErr bOut bIn : Bool)
    (st : StreamLoopState fd) (ioFuel : Nat) (s : S)
    (hIn : st.inFd? = optFdOf inW bIn)
    (hOut : st.outFd? = optFdOf outR bOut)
    (hErr : st.errFd? = optFdOf errR bErr)
    (hOpen : openFds s = pipePrefix errR outR inW bErr bOut bIn base)
    (hOutSum : (st.outChunks.toList.map ByteArray.size).sum = st.outLen)
    (hErrSum : (st.errChunks.toList.map ByteArray.size).sum = st.errLen)
    (hCap : ∀ lim, maxOutputBytes? = some lim → st.outLen + st.errLen ≤ lim) :
    let r := (SysBridge.streamPipesLoop files poll timeRand stdin startMs timeoutMs? maxOutputBytes? stepFuel st ioFuel).run s
    getTbl r.2 = getTbl s ∧
    openFds r.2 = base ∧
    (∀ out errB, r.1 = .ok (.eof out errB) →
      ∀ lim, maxOutputBytes? = some lim → out.size + errB.size ≤ lim) ∧
    (∀ out errB, r.1 = .ok (.timedOut out errB) → timeoutMs?.isSome = true) ∧
    (∀ out errB, r.1 = .ok (.limitExceeded out errB) →
      maxOutputBytes?.isSome = true ∧
      (∀ lim, maxOutputBytes? = some lim → out.size + errB.size ≤ lim)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun s0 : S => (getTbl s0, openFds s0)
  have hCgP : ∀ s0 clk, proj ((timeRand.clock_gettime clk).run s0).2 = proj s0 :=
    fun s0 clk => Prod.ext (hCg s0 clk).1 (hCg s0 clk).2
  induction ioFuel generalizing bErr bOut bIn st s with
  | zero =>
    unfold SysBridge.streamPipesLoop
    rw [stateT_bind_eq]
    dsimp only [pure, StateT.pure, StateT.run]
    obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
      hEO hEI hOI st s hIn hOut hErr hOpen
    refine ⟨hT, hO, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
    intro err hEq
    injection hEq with hE
    rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ fuel ih =>
    unfold SysBridge.streamPipesLoop
    split
    · next hAllNone =>
      rw [Bool.and_eq_true, Bool.and_eq_true] at hAllNone
      have hbIn : bIn = false := optFdOf_isNone inW bIn (hIn ▸ hAllNone.1.1)
      have hbOut : bOut = false := optFdOf_isNone outR bOut (hOut ▸ hAllNone.1.2)
      have hbErr : bErr = false := optFdOf_isNone errR bErr (hErr ▸ hAllNone.2)
      subst hbIn hbOut hbErr
      dsimp only [pure, StateT.pure, StateT.run]
      have hO : openFds s = base := by simpa [pipePrefix] using hOpen
      refine ⟨rfl, hO, ?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
      intro out errB hEq lim hLim
      injection hEq with hSub
      injection hSub with hO1 hE1
      rw [← hO1, ← hE1, concatChunks_size, concatChunks_size, hOutSum, hErrSum]
      exact hCap lim hLim
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 =
          pipePrefix errR outR inW bErr bOut bIn base :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
          hEO hEI hOI st s1 hIn hOut hErr hFcO
        refine ⟨hT.trans hFcT, hO,
          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact mapErrno_kind_and_msg none "clock_gettime" e
      | ok pair =>
        rcases pair with ⟨isTo, remMs⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          let pollTimeout? : Option Poll.Timespec :=
            timeoutMs?.map fun _ => Poll.msToPollTimespec remMs
          let pollRun := (poll.ppoll (SysBridge.buildPollEntries st) pollTimeout?).run s1
          have hPollFrame := hPoll s1 (SysBridge.buildPollEntries st) pollTimeout?
          have hFpT : getTbl pollRun.2 = getTbl s := hPollFrame.1.trans hFcT
          have hFpO : openFds pollRun.2 = pipePrefix errR outR inW bErr bOut bIn base :=
            hPollFrame.2.trans hFcO
          cases hPr : pollRun.1 with
          | error pe =>
            dsimp only
            by_cases hEintr : pe == Errno.EINTR
            · simp only [hEintr, ↓reduceIte]
              obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr bOut bIn st pollRun.2
                hIn hOut hErr hFpO hOutSum hErrSum hCap
              exact ⟨hFi.trans hFpT, hOi, hEofI, hToI, hLiI, hErrI⟩
            · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
              rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
                hEO hEI hOI st pollRun.2 hIn hOut hErr hFpO
              refine ⟨hT.trans hFpT, hO,
                (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
              intro err hEq
              injection hEq with hE
              rw [← hE]
              exact mapErrno_kind_and_msg none "ppoll" pe
          | ok revents =>
            dsimp only
            generalize SysBridge.decodeReadyFlags st revents = rFlags
            rcases rFlags with ⟨inReady, outReady, errReady⟩
            dsimp only
            by_cases hIdle : (!inReady && !outReady && !errReady) = true
            · simp only [hIdle, ↓reduceIte]
              obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr bOut bIn st pollRun.2
                hIn hOut hErr hFpO hOutSum hErrSum hCap
              exact ⟨hFi.trans hFpT, hOi, hEofI, hToI, hLiI, hErrI⟩
            · simp only [hIdle, Bool.false_eq_true, ↓reduceIte]
              have hStdinStep :
                  ∃ bIn' inFdNext? stdinPos' inProg inTimedOut inErr? s2,
                    (SysBridge.stepStdinIfReady inReady files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel).run pollRun.2 =
                      ((inFdNext?, stdinPos', inProg, inTimedOut, inErr?), s2) ∧
                    getTbl s2 = getTbl s ∧
                    inFdNext? = optFdOf inW bIn' ∧
                    openFds s2 = pipePrefix errR outR inW bErr bOut bIn' base ∧
                    (inTimedOut = true → timeoutMs?.isSome = true) ∧
                    (∀ e, inErr? = some e →
                      bIn' = false ∧
                      e.message ≠ "" ∧ e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal) := by
                unfold SysBridge.stepStdinIfReady
                cases inReady
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact ⟨bIn, st.inFd?, st.stdinPos, false, false, none, pollRun.2, rfl,
                    hFpT, hIn, hFpO, (by intro h; cases h), (by intro _ h; cases h)⟩
                · simp only [↓reduceIte]
                  unfold SysBridge.stepStdinOpt
                  rw [hIn]
                  cases bIn with
                  | false =>
                    exact ⟨false, none, st.stdinPos, false, false, none, pollRun.2, rfl, hFpT, rfl, hFpO,
                      (by intro h; cases h), (by intro _ h; cases h)⟩
                  | true =>
                    dsimp only [optFdOf]
                    obtain ⟨hFw, hTw, hOw, hEw⟩ := writeStdinStep_spec getTbl openFds files timeRand
                      hCloseT hWrite hCg inW (fun b => pipePrefix errR outR inW bErr bOut b base)
                      (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_in hEI hOI])
                      stdin startMs timeoutMs? st.stdinPos false stepFuel pollRun.2 hFpO
                    let rwS := (SysBridge.writeStdinStep files timeRand inW stdin startMs timeoutMs? st.stdinPos false stepFuel).run pollRun.2
                    cases hRw : rwS.1 with
                    | error e =>
                      obtain ⟨hOErr, hMsgErr⟩ := hEw e hRw
                      refine ⟨false, none, st.stdinPos, false, false, some e, rwS.2, ?_, hFw.trans hFpT,
                        rfl, hOErr, (by intro h; cases h), ?_⟩
                      · rw [stateT_bind_eq]; dsimp only [rwS] at hRw; rw [hRw]; rfl
                      · intro err he; injection he with hEq; rw [← hEq]; exact ⟨rfl, hMsgErr⟩
                    | ok tup =>
                      rcases tup with ⟨nFd, p', pr, to⟩
                      obtain ⟨bIn', hnFd, hOOk⟩ := hOw nFd p' pr to hRw
                      refine ⟨bIn', nFd, p', pr, to, none, rwS.2, ?_, hFw.trans hFpT,
                        hnFd, hOOk,
                        fun hToTrue => hTw nFd p' pr (by rw [hToTrue] at hRw; exact hRw),
                        (by intro _ h; cases h)⟩
                      rw [stateT_bind_eq]; dsimp only [rwS] at hRw; rw [hRw]; rfl
              rcases hStdinStep with ⟨bIn', inFdNext?, stdinPos', inProg, inTimedOut, inErr?, s2,
                hRunIn, hFs2, hInNext, hOs2, hInTo, hInErr⟩
              rw [stateT_bind_eq, hRunIn]
              dsimp only
              cases inErr? with
              | some e =>
                dsimp only
                obtain ⟨hbInF, hMsgIn⟩ := hInErr e rfl
                subst hbInF
                rw [hOut, hErr, stateT_bind_eq, stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hTOut, hOOut⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                  (fun b => pipePrefix errR outR inW bErr b false base)
                  (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_out hEO]) bOut s2 hOs2
                let s2a := ((Files.closeOpt files (optFdOf outR bOut)).run s2).2
                obtain ⟨hTErr, hOErr⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                  (fun b => pipePrefix errR outR inW b false false base)
                  (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_err]) bErr s2a hOOut
                refine ⟨hTErr.trans (hTOut.trans hFs2), hOErr,
                  (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgIn
              | none =>
                dsimp only
                cases hInToB : inTimedOut
                · rw [ite_eq_right (by decide)]
                  have hOutStep :
                      ∃ outRes s3,
                        (SysBridge.stepDrainIfReady outReady files timeRand st.outFd? st.errLen startMs timeoutMs? maxOutputBytes?
                          st.outChunks st.outLen stepFuel).run s2 = (outRes, s3) ∧
                        getTbl s3 = getTbl s ∧
                        (∀ ch' len', outRes = .timedOut ch' len' →
                          timeoutMs?.isSome = true ∧
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ ch' len', outRes = .limitExceeded ch' len' →
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          maxOutputBytes?.isSome = true ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ fd? ch' len' pr, outRes = .cont fd? ch' len' pr →
                          (∃ bOut', fd? = optFdOf outR bOut' ∧
                            openFds s3 = pipePrefix errR outR inW bErr bOut' bIn' base) ∧
                          (ch'.toList.map ByteArray.size).sum = len' ∧
                          (∀ lim, maxOutputBytes? = some lim → len' + st.errLen ≤ lim)) ∧
                        (∀ err, outRes = .ioErr err →
                          openFds s3 = pipePrefix errR outR inW bErr false bIn' base ∧
                          err.message ≠ "" ∧ err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
                    unfold SysBridge.stepDrainIfReady
                    cases outReady
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      refine ⟨.cont st.outFd? st.outChunks st.outLen false, s2, rfl, hFs2,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                      intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst hFd h1 h2
                      exact ⟨⟨bOut, hOut, hOs2⟩, hOutSum, hCap⟩
                    · simp only [↓reduceIte]
                      unfold SysBridge.stepDrainOpt
                      rw [hOut]
                      cases bOut with
                      | false =>
                        refine ⟨.cont none st.outChunks st.outLen false, s2, rfl, hFs2,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                        intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst h1 h2
                        exact ⟨⟨false, hFd.symm, hOs2⟩, hOutSum, hCap⟩
                      | true =>
                        dsimp only [optFdOf]
                        obtain ⟨hFo, hToO, hLiO, hCoO, hEoO⟩ := drainPipeStep_spec getTbl openFds files timeRand
                          hCloseT hRead hCg outR (fun b => pipePrefix errR outR inW bErr b bIn' base)
                          (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_out hEO])
                          st.errLen startMs timeoutMs? maxOutputBytes?
                          st.outChunks st.outLen 0 false stepFuel s2 hOs2 hOutSum hCap
                        exact ⟨_, _, rfl, hFo.trans hFs2, hToO, hLiO, hCoO, hEoO⟩
                  rcases hOutStep with ⟨outRes, s3, hRunOut, hFs3, hToO, hLiO, hCoO, hEoO⟩
                  rw [stateT_bind_eq, hRunOut]
                  dsimp only
                  have hCloseInAndErr : ∀ st0,
                      openFds st0 = pipePrefix errR outR inW bErr false bIn' base →
                      getTbl st0 = getTbl s →
                      let rEnd := ((Files.closeOpt files st.errFd?).run
                        ((Files.closeOpt files inFdNext?).run st0).2)
                      getTbl rEnd.2 = getTbl s ∧ openFds rEnd.2 = base := by
                    intro st0 hO0 hT0
                    rw [hInNext, hErr]
                    obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                      (fun b => pipePrefix errR outR inW bErr false b base)
                      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' st0 hO0
                    obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                      (fun b => pipePrefix errR outR inW b false false base)
                      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) bErr _ hO1
                    exact ⟨hT2.trans (hT1.trans hT0), hO2⟩
                  cases outRes with
                  | ioErr e =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hO3, hMsgO⟩ := hEoO e rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    refine ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                    intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgO
                  | timedOut outChunks' outLen' =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hSomeTo, hO3, _, _⟩ := hToO outChunks' outLen' rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    exact ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), fun _ _ _ => hSomeTo,
                      (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                  | limitExceeded outChunks' outLen' =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hO3, hSome, hOSum', hOCap'⟩ := hLiO outChunks' outLen' rfl
                    obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndErr s3 hO3 hFs3
                    refine ⟨hTEnd, hOEnd,
                      (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                    intro out errB hEq
                    injection hEq with hSub
                    injection hSub with hO1 hE1
                    rw [← hO1, ← hE1]
                    refine ⟨hSome, ?_⟩
                    intro lim hLim
                    rw [concatChunks_size, concatChunks_size, hOSum', hErrSum]
                    exact hOCap' lim hLim
                  | cont outFdNext? outChunks' outLen' outProg =>
                    dsimp only
                    obtain ⟨⟨bOut', hOutNext, hOs3⟩, hOSum', hOCap'⟩ := hCoO outFdNext? outChunks' outLen' outProg rfl
                    have hErrCapIn : ∀ lim, maxOutputBytes? = some lim → st.errLen + outLen' ≤ lim := by
                      intro lim hLim; have := hOCap' lim hLim; omega
                    have hErrStep :
                        ∃ errRes s4,
                          (SysBridge.stepDrainIfReady errReady files timeRand st.errFd? outLen' startMs timeoutMs? maxOutputBytes?
                            st.errChunks st.errLen stepFuel).run s3 = (errRes, s4) ∧
                          getTbl s4 = getTbl s ∧
                          (∀ ch' len', errRes = .timedOut ch' len' →
                            timeoutMs?.isSome = true ∧
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ ch' len', errRes = .limitExceeded ch' len' →
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            maxOutputBytes?.isSome = true ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ fd? ch' len' pr, errRes = .cont fd? ch' len' pr →
                            (∃ bErr', fd? = optFdOf errR bErr' ∧
                              openFds s4 = pipePrefix errR outR inW bErr' bOut' bIn' base) ∧
                            (ch'.toList.map ByteArray.size).sum = len' ∧
                            (∀ lim, maxOutputBytes? = some lim → len' + outLen' ≤ lim)) ∧
                          (∀ err, errRes = .ioErr err →
                            openFds s4 = pipePrefix errR outR inW false bOut' bIn' base ∧
                            err.message ≠ "" ∧ err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
                      unfold SysBridge.stepDrainIfReady
                      cases errReady
                      · simp only [Bool.false_eq_true, ↓reduceIte]
                        refine ⟨.cont st.errFd? st.errChunks st.errLen false, s3, rfl, hFs3,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                        intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst hFd h1 h2
                        exact ⟨⟨bErr, hErr, hOs3⟩, hErrSum, hErrCapIn⟩
                      · simp only [↓reduceIte]
                        unfold SysBridge.stepDrainOpt
                        rw [hErr]
                        cases bErr with
                        | false =>
                          refine ⟨.cont none st.errChunks st.errLen false, s3, rfl, hFs3,
                            (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                          intro fd? ch' len' _ hEq; injection hEq with hFd h1 h2 _; subst h1 h2
                          exact ⟨⟨false, hFd.symm, hOs3⟩, hErrSum, hErrCapIn⟩
                        | true =>
                          dsimp only [optFdOf]
                          obtain ⟨hFe, hToE, hLiE, hCoE, hEoE⟩ := drainPipeStep_spec getTbl openFds files timeRand
                            hCloseT hRead hCg errR (fun b => pipePrefix errR outR inW b bOut' bIn' base)
                            (fun s0 hs0 => by rw [hCloseO, hs0, pipePrefix_erase_err])
                            outLen' startMs timeoutMs? maxOutputBytes?
                            st.errChunks st.errLen 0 false stepFuel s3 hOs3 hErrSum hErrCapIn
                          exact ⟨_, _, rfl, hFe.trans hFs3, hToE, hLiE, hCoE, hEoE⟩
                    rcases hErrStep with ⟨errRes, s4, hRunErr, hFs4, hToE, hLiE, hCoE, hEoE⟩
                    rw [stateT_bind_eq, hRunErr]
                    dsimp only
                    have hCloseInAndOut : ∀ st0,
                        openFds st0 = pipePrefix errR outR inW false bOut' bIn' base →
                        getTbl st0 = getTbl s →
                        let rEnd := ((Files.closeOpt files outFdNext?).run
                          ((Files.closeOpt files inFdNext?).run st0).2)
                        getTbl rEnd.2 = getTbl s ∧ openFds rEnd.2 = base := by
                      intro st0 hO0 hT0
                      rw [hInNext, hOutNext]
                      obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                        (fun b => pipePrefix errR outR inW false bOut' b base)
                        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' st0 hO0
                      obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                        (fun b => pipePrefix errR outR inW false b false base)
                        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) bOut' _ hO1
                      exact ⟨hT2.trans (hT1.trans hT0), hO2⟩
                    cases errRes with
                    | ioErr e =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hO4, hMsgE⟩ := hEoE e rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      refine ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
                      intro err hEq; injection hEq with hE; rw [← hE]; exact hMsgE
                    | timedOut errChunks' errLen' =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hSomeTo, hO4, _, _⟩ := hToE errChunks' errLen' rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      exact ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), fun _ _ _ => hSomeTo,
                        (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                    | limitExceeded errChunks' errLen' =>
                      dsimp only
                      rw [stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hO4, hSome, hESum', hECap'⟩ := hLiE errChunks' errLen' rfl
                      obtain ⟨hTEnd, hOEnd⟩ := hCloseInAndOut s4 hO4 hFs4
                      refine ⟨hTEnd, hOEnd,
                        (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                      intro out errB hEq
                      injection hEq with hSub
                      injection hSub with hO1 hE1
                      rw [← hO1, ← hE1]
                      refine ⟨hSome, ?_⟩
                      intro lim hLim
                      rw [concatChunks_size, concatChunks_size, hOSum', hESum']
                      have := hECap' lim hLim
                      omega
                    | cont errFdNext? errChunks' errLen' errProg =>
                      dsimp only
                      obtain ⟨⟨bErr', hErrNext, hOs4⟩, hESum', hECap'⟩ := hCoE errFdNext? errChunks' errLen' errProg rfl
                      have hNextCap : ∀ lim, maxOutputBytes? = some lim → outLen' + errLen' ≤ lim := by
                        intro lim hLim; have := hECap' lim hLim; omega
                      split
                      · next hNextAllNone =>
                        rw [Bool.and_eq_true, Bool.and_eq_true] at hNextAllNone
                        have hbIn' : bIn' = false := optFdOf_isNone inW bIn' (hInNext ▸ hNextAllNone.1.1)
                        have hbOut' : bOut' = false := optFdOf_isNone outR bOut' (hOutNext ▸ hNextAllNone.1.2)
                        have hbErr' : bErr' = false := optFdOf_isNone errR bErr' (hErrNext ▸ hNextAllNone.2)
                        subst hbIn' hbOut' hbErr'
                        dsimp only [pure, StateT.pure, StateT.run]
                        have hOEnd : openFds s4 = base := by simpa [pipePrefix] using hOs4
                        refine ⟨hFs4, hOEnd, ?_,
                          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
                        intro out errB hEq lim hLim
                        injection hEq with hSub
                        injection hSub with hO1 hE1
                        rw [← hO1, ← hE1, concatChunks_size, concatChunks_size, hOSum', hESum']
                        exact hNextCap lim hLim
                      · obtain ⟨hFi, hOi, hEofI, hToI, hLiI, hErrI⟩ := ih bErr' bOut' bIn'
                          { inFd? := inFdNext?
                            outFd? := outFdNext?
                            errFd? := errFdNext?
                            stdinPos := stdinPos'
                            outChunks := outChunks'
                            outLen := outLen'
                            errChunks := errChunks'
                            errLen := errLen' }
                          s4 hInNext hOutNext hErrNext hOs4 hOSum' hESum' hNextCap
                        exact ⟨hFi.trans hFs4, hOi, hEofI, hToI, hLiI, hErrI⟩
                · rw [ite_eq_left rfl]
                  rw [hInNext, hOut, hErr, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                  dsimp only [pure, StateT.pure, StateT.run]
                  obtain ⟨hT1, hO1⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inW
                    (fun b => pipePrefix errR outR inW bErr bOut b base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn' s2 hOs2
                  obtain ⟨hT2, hO2⟩ := closeOpt_optFdOf getTbl openFds files hCloseT outR
                    (fun b => pipePrefix errR outR inW bErr b false base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) bOut _ hO1
                  obtain ⟨hT3, hO3⟩ := closeOpt_optFdOf getTbl openFds files hCloseT errR
                    (fun b => pipePrefix errR outR inW b false false base)
                    (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) bErr _ hO2
                  exact ⟨hT3.trans (hT2.trans (hT1.trans hFs2)), hO3,
                    (by intro _ _ h; cases h), fun _ _ _ => hInTo hInToB,
                    (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeStreamState_pipePrefix getTbl openFds files hCloseT hCloseO
            hEO hEI hOI st s1 hIn hOut hErr hFcO
          exact ⟨hT.trans hFcT, hO,
            (by intro _ _ h; cases h), fun _ _ _ => hTo remMs hCt,
            (by intro _ _ h; cases h), (by intro _ h; cases h)⟩

end LeanSwe.Process.Proofs

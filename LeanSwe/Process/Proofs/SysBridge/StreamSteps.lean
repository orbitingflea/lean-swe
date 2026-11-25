import LeanSwe.Process.Proofs.SysBridge.EnvAndPath

/-!
Monotonic clock helper frames and per-iteration `writeStdinStep` / `drainPipeStep`
conservation lemmas for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

theorem monoNowMs_spec {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (s : S) :
    proj ((TimeRand.monoNowMs timeRand).run s).2 = proj s := by
  unfold TimeRand.monoNowMs
  rw [stateT_bind_eq]
  cases ((timeRand.clock_gettime .monotonic).run s).1 with
  | ok _ => exact hCg s .monotonic
  | error _ => exact hCg s .monotonic

theorem checkTimedOut_spec {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (startMs : Nat) (timeoutMs? : Option Nat) (s : S) :
    let r := (TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s
    proj r.2 = proj s ∧
    (timeoutMs? = none → r.1 = .ok (false, 0)) ∧
    (∀ rem, r.1 = .ok (true, rem) → timeoutMs?.isSome = true) := by
  dsimp only
  cases timeoutMs? with
  | none =>
    dsimp only [TimeRand.checkTimedOut, pure, StateT.pure, StateT.run]
    exact ⟨rfl, fun _ => rfl, (by intro _ h; cases h)⟩
  | some timeoutMs =>
    unfold TimeRand.checkTimedOut
    rw [stateT_bind_eq]
    have hF := monoNowMs_spec proj timeRand hCg s
    cases ((TimeRand.monoNowMs timeRand).run s).1 with
    | error _ =>
      dsimp only [pure, StateT.pure, StateT.run]
      exact ⟨hF, (by intro h; cases h), (by intro _ h; cases h)⟩
    | ok _ =>
      dsimp only
      split <;>
        (dsimp only [pure, StateT.pure, StateT.run]
         exact ⟨hF, (by intro h; cases h), fun _ _ => rfl⟩)

theorem sleepMonoMs_frame {S α : Type}
    (proj : S → α)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (ms : Nat) (s : S) :
    proj ((TimeRand.sleepMonoMs timeRand ms).run s).2 = proj s := by
  unfold TimeRand.sleepMonoMs
  rw [stateT_bind_eq]
  exact hNs s _ _ _

theorem writeStdinStep_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hWrite : ∀ s h d, getTbl ((files.write h d).run s).2 = getTbl s ∧
      openFds ((files.write h d).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    (inFd : fd) (fdAt : Bool → List fd)
    (hErase : ∀ st, openFds st = fdAt true → openFds ((files.close inFd).run st).2 = fdAt false)
    (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (pos : Nat) (prog : Bool) (fuel : Nat) (s : S)
    (hOpen : openFds s = fdAt true) :
    let r := (SysBridge.writeStdinStep files timeRand inFd stdin startMs timeoutMs? pos prog fuel).run s
    getTbl r.2 = getTbl s ∧
    (∀ nextFd? p' pr, r.1 = .ok (nextFd?, p', pr, true) → timeoutMs?.isSome = true) ∧
    (∀ nextFd? p' pr to, r.1 = .ok (nextFd?, p', pr, to) →
      ∃ b', nextFd? = optFdOf inFd b' ∧ openFds r.2 = fdAt b') ∧
    (∀ err, r.1 = .error err →
      openFds r.2 = fdAt false ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hCgP : ∀ st clk, proj ((timeRand.clock_gettime clk).run st).2 = proj st :=
    fun st clk => Prod.ext (hCg st clk).1 (hCg st clk).2
  induction fuel generalizing pos prog s with
  | zero =>
    unfold SysBridge.writeStdinStep
    split
    · rw [stateT_bind_eq]
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s hOpen
      refine ⟨hT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨false, hN.symm, hO⟩
    · dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨rfl, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨true, hN.symm, hOpen⟩
  | succ f ih =>
    unfold SysBridge.writeStdinStep
    split
    · rw [stateT_bind_eq]
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s hOpen
      refine ⟨hT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro nextFd? _ _ _ hEq
      injection hEq with hSub; injection hSub with hN _
      exact ⟨false, hN.symm, hO⟩
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = fdAt true :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s1 hFcO
        refine ⟨hT.trans hFcT, (by intro _ _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact ⟨hO, mapErrno_kind_and_msg none "clock_gettime" e⟩
      | ok pair =>
        rcases pair with ⟨isTo, rem⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          let slice := stdin.extract pos (Nat.min stdin.size (pos + STDIN_WRITE_CHUNK))
          have hFwT : getTbl ((files.write inFd slice).run s1).2 = getTbl s :=
            (hWrite s1 inFd slice).1.trans hFcT
          have hFwO : openFds ((files.write inFd slice).run s1).2 = fdAt true :=
            (hWrite s1 inFd slice).2.trans hFcO
          let s2 := ((files.write inFd slice).run s1).2
          cases hW : ((files.write inFd slice).run s1).1 with
          | ok n =>
            dsimp only
            split
            · rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
              refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
              intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
              exact ⟨false, hN.symm, hO⟩
            · split
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
                refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨false, hN.symm, hO⟩
              · obtain ⟨hFi, hTi, hOi, hEi⟩ := ih (pos + n.toNat) true s2 hFwO
                exact ⟨hFi.trans hFwT, hTi, hOi, hEi⟩
          | error e =>
            dsimp only
            split
            · obtain ⟨hFi, hTi, hOi, hEi⟩ := ih pos prog s2 hFwO
              exact ⟨hFi.trans hFwT, hTi, hOi, hEi⟩
            · split
              · dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨true, hN.symm, hFwO⟩
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s2 hFwO
                refine ⟨hT.trans hFwT, (by intro _ _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
                exact ⟨false, hN.symm, hO⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT inFd fdAt hErase true s1 hFcO
          refine ⟨hT.trans hFcT, fun _ _ _ _ => hTo rem hCt, ?_, (by intro _ h; cases h)⟩
          intro nextFd? _ _ _ hEq; injection hEq with hSub; injection hSub with hN _
          exact ⟨false, hN.symm, hO⟩

theorem drainPipeStep_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (openFds : S → List fd)
    (files : Files.FilesOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hCloseT : ∀ s h, getTbl ((files.close h).run s).2 = getTbl s)
    (hRead : ∀ s h c, getTbl ((files.read h c).run s).2 = getTbl s ∧
      openFds ((files.read h c).run s).2 = openFds s)
    (hCg : ∀ s clk, getTbl ((timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((timeRand.clock_gettime clk).run s).2 = openFds s)
    (pipeFd : fd) (fdAt : Bool → List fd)
    (hErase : ∀ st, openFds st = fdAt true → openFds ((files.close pipeFd).run st).2 = fdAt false)
    (otherLen startMs : Nat)
    (timeoutMs? maxOutputBytes? : Option Nat)
    (chunks : Array ByteArray) (curLen iterBytes : Nat) (prog : Bool) (fuel : Nat) (s : S)
    (hOpen : openFds s = fdAt true)
    (hSum : (chunks.toList.map ByteArray.size).sum = curLen)
    (hCap : ∀ lim, maxOutputBytes? = some lim → curLen + otherLen ≤ lim) :
    let r := (SysBridge.drainPipeStep files timeRand pipeFd otherLen startMs timeoutMs? maxOutputBytes?
      chunks curLen iterBytes prog fuel).run s
    getTbl r.2 = getTbl s ∧
    (∀ ch' len', r.1 = .timedOut ch' len' →
      timeoutMs?.isSome = true ∧
      openFds r.2 = fdAt false ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ ch' len', r.1 = .limitExceeded ch' len' →
      openFds r.2 = fdAt false ∧
      maxOutputBytes?.isSome = true ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ fd? ch' len' pr, r.1 = .cont fd? ch' len' pr →
      (∃ b', fd? = optFdOf pipeFd b' ∧ openFds r.2 = fdAt b') ∧
      (ch'.toList.map ByteArray.size).sum = len' ∧
      (∀ lim, maxOutputBytes? = some lim → len' + otherLen ≤ lim)) ∧
    (∀ err, r.1 = .ioErr err →
      openFds r.2 = fdAt false ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hCgP : ∀ st clk, proj ((timeRand.clock_gettime clk).run st).2 = proj st :=
    fun st clk => Prod.ext (hCg st clk).1 (hCg st clk).2
  induction fuel generalizing chunks curLen iterBytes prog s with
  | zero =>
    unfold SysBridge.drainPipeStep
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
    intro fd? ch' len' _ hEq
    injection hEq with hFd hCh hLen _
    subst hCh hLen
    exact ⟨⟨true, hFd.symm, hOpen⟩, hSum, hCap⟩
  | succ f ih =>
    unfold SysBridge.drainPipeStep
    split
    · dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro fd? ch' len' _ hEq
      injection hEq with hFd hCh hLen _
      subst hCh hLen
      exact ⟨⟨true, hFd.symm, hOpen⟩, hSum, hCap⟩
    · rw [stateT_bind_eq]
      obtain ⟨hFcP, _, hTo⟩ := checkTimedOut_spec proj timeRand hCgP startMs timeoutMs? s
      have hFcT : getTbl ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = getTbl s :=
        congrArg Prod.fst hFcP
      have hFcO : openFds ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2 = fdAt true :=
        (congrArg Prod.snd hFcP).trans hOpen
      let s1 := ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).2
      cases hCt : ((TimeRand.checkTimedOut timeRand startMs timeoutMs?).run s).1 with
      | error e =>
        dsimp only
        rw [stateT_bind_eq]
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s1 hFcO
        refine ⟨hT.trans hFcT,
          (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
        intro err hEq
        injection hEq with hE
        rw [← hE]
        exact ⟨hO, mapErrno_kind_and_msg none "clock_gettime" e⟩
      | ok pair =>
        rcases pair with ⟨isTo, rem⟩
        cases isTo
        · dsimp only
          rw [stateT_bind_eq]
          have hFrT : getTbl ((files.read pipeFd PIPE_READ_CHUNK).run s1).2 = getTbl s :=
            (hRead s1 pipeFd PIPE_READ_CHUNK).1.trans hFcT
          have hFrO : openFds ((files.read pipeFd PIPE_READ_CHUNK).run s1).2 = fdAt true :=
            (hRead s1 pipeFd PIPE_READ_CHUNK).2.trans hFcO
          let s2 := ((files.read pipeFd PIPE_READ_CHUNK).run s1).2
          cases hR : ((files.read pipeFd PIPE_READ_CHUNK).run s1).1 with
          | ok chunk =>
            dsimp only
            split
            · rw [stateT_bind_eq]
              dsimp only [pure, StateT.pure, StateT.run]
              obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
              refine ⟨hT.trans hFrT,
                (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
              intro fd? ch' len' _ hEq
              injection hEq with hFd hCh hLen _
              subst hCh hLen
              exact ⟨⟨false, hFd.symm, hO⟩, hSum, hCap⟩
            · have hPushSum : ((chunks.push chunk).toList.map ByteArray.size).sum = curLen + chunk.size := by
                simp [Array.toList_push, hSum]
              cases maxOutputBytes? with
              | none =>
                dsimp only
                obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih (chunks.push chunk) (curLen + chunk.size)
                  (iterBytes + chunk.size) true s2 hFrO hPushSum (fun _ hm => by cases hm)
                exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
              | some maxOut =>
                dsimp only
                have hCurLe : curLen + otherLen ≤ maxOut := hCap maxOut rfl
                by_cases hGt : curLen + otherLen + chunk.size > maxOut
                · rw [ite_eq_left hGt]
                  by_cases hKeep : maxOut - (curLen + otherLen) > 0
                  · rw [ite_eq_left hKeep]
                    dsimp only
                    rw [stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                    have hPreSz : (chunk.extract 0 (maxOut - (curLen + otherLen))).size = maxOut - (curLen + otherLen) := by
                      rw [ByteArray.size_extract]
                      omega
                    have hPreSum :
                        ((chunks.push (chunk.extract 0 (maxOut - (curLen + otherLen)))).toList.map ByteArray.size).sum =
                          curLen + (chunk.extract 0 (maxOut - (curLen + otherLen))).size := by
                      simp [Array.toList_push, hSum]
                    refine ⟨hT.trans hFrT,
                      (by intro _ _ h; cases h), ?_, (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
                    intro ch' len' hEq
                    injection hEq with hCh hLen
                    subst hCh hLen
                    refine ⟨hO, rfl, hPreSum, ?_⟩
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    rw [hPreSz]
                    omega
                  · rw [ite_eq_right hKeep]
                    dsimp only
                    rw [stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                    refine ⟨hT.trans hFrT,
                      (by intro _ _ h; cases h), ?_, (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
                    intro ch' len' hEq
                    injection hEq with hCh hLen
                    subst hCh hLen
                    refine ⟨hO, rfl, hSum, ?_⟩
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    exact hCurLe
                · rw [ite_eq_right hGt]
                  have hNextCap : ∀ lim, some maxOut = some lim → (curLen + chunk.size) + otherLen ≤ lim := by
                    intro lim hLim
                    injection hLim with hLimEq
                    subst hLimEq
                    omega
                  obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih (chunks.push chunk) (curLen + chunk.size)
                    (iterBytes + chunk.size) true s2 hFrO hPushSum hNextCap
                  exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
          | error e =>
            dsimp only
            split
            · obtain ⟨hFi, hTi, hLi, hCi, hEi⟩ := ih chunks curLen iterBytes prog s2 hFrO hSum hCap
              exact ⟨hFi.trans hFrT, hTi, hLi, hCi, hEi⟩
            · split
              · dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hFrT, (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_, (by intro _ h; cases h)⟩
                intro fd? ch' len' _ hEq
                injection hEq with hFd hCh hLen _
                subst hCh hLen
                exact ⟨⟨true, hFd.symm, hFrO⟩, hSum, hCap⟩
              · rw [stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s2 hFrO
                refine ⟨hT.trans hFrT,
                  (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ _ _ h; cases h), ?_⟩
                intro err hEq
                injection hEq with hE
                subst hE
                exact ⟨hO, mapErrno_kind_and_msg none "read" e⟩
        · dsimp only
          rw [stateT_bind_eq]
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hT, hO⟩ := closeOpt_optFdOf getTbl openFds files hCloseT pipeFd fdAt hErase true s1 hFcO
          refine ⟨hT.trans hFcT, ?_, (by intro _ _ h; cases h),
            (by intro _ _ _ _ h; cases h), (by intro _ h; cases h)⟩
          intro ch' len' hEq
          injection hEq with hCh hLen
          subst hCh hLen
          exact ⟨hTo rem hCt, hO, hSum, hCap⟩

end LeanSwe.Process.Proofs

import LeanSweProofs.Process.Proofs.SysBridge.StreamLoop
import LeanSweProofs.Process.Proofs.SysBridge.SpawnLaws

/-!
`awaitOsPhase` laws and the universal `mkRawOpsM_satisfies_RawProcessLaws` theorem
for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

theorem awaitOsPhase_laws {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel ioFuel : Nat)
    (pid : UInt32) (inFd0? outFd0? errFd0? : Option fd)
    {errR outR inW : fd} (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW)
    (hSlotIn : inFd0? = optFdOf inW true)
    (hSlotOut : outFd0? = optFdOf outR true)
    (hSlotErr : errFd0? = optFdOf errR true)
    (base : List fd)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat)
    (s₂ : S)
    (hOpen₂ : openFds s₂ = pipePrefix errR outR inW true true true base) :
    let aw := (SysBridge.awaitOsPhase deps eintrFuel ioFuel pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOutputBytes?).run s₂
    getTbl aw.2 = getTbl s₂ ∧
    openFds aw.2 = base ∧
    (∀ err, aw.1 = .error err →
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) ∧
    (∀ wf res, aw.1 = .ok (wf, .exited res) →
      ∀ lim, maxOutputBytes? = some lim → res.stdout.size + res.stderr.size ≤ lim) ∧
    (∀ wf o e, aw.1 = .ok (wf, .timedOut o e) → timeoutMs?.isSome = true) ∧
    (∀ wf o e, aw.1 = .ok (wf, .outputLimitExceeded o e) →
      maxOutputBytes?.isSome = true ∧
      (∀ lim, maxOutputBytes? = some lim → o.size + e.size ≤ lim)) := by
  dsimp only
  let proj := fun s : S => (getTbl s, openFds s)
  have hCloseT : ∀ s h, getTbl ((deps.files.close h).run s).2 = getTbl s :=
    fun s h => (hDeps.close_frame s h).1
  have hCloseO : ∀ s h, openFds ((deps.files.close h).run s).2 = (openFds s).erase h :=
    fun s h => (hDeps.close_frame s h).2.1
  have hReadTO : ∀ s h c, getTbl ((deps.files.read h c).run s).2 = getTbl s ∧
      openFds ((deps.files.read h c).run s).2 = openFds s :=
    fun s h c => ⟨(hDeps.read_frame s h c).1, (hDeps.read_frame s h c).2.1⟩
  have hWriteTO : ∀ s h d, getTbl ((deps.files.write h d).run s).2 = getTbl s ∧
      openFds ((deps.files.write h d).run s).2 = openFds s :=
    fun s h d => ⟨(hDeps.write_frame s h d).1, (hDeps.write_frame s h d).2.1⟩
  have hFcntlTO : ∀ s h cmd, getTbl ((deps.files.fcntl h cmd).run s).2 = getTbl s ∧
      openFds ((deps.files.fcntl h cmd).run s).2 = openFds s :=
    fun s h cmd => ⟨(hDeps.fcntl_frame s h cmd).1, (hDeps.fcntl_frame s h cmd).2.1⟩
  have hWaitP : ∀ s p fl, proj ((deps.proc.waitpid p fl).run s).2 = proj s :=
    fun s p fl => Prod.ext (hDeps.waitpid_frame s p fl).1 (hDeps.waitpid_frame s p fl).2.1
  have hCgTO : ∀ s clk, getTbl ((deps.timeRand.clock_gettime clk).run s).2 = getTbl s ∧
      openFds ((deps.timeRand.clock_gettime clk).run s).2 = openFds s :=
    fun s clk => ⟨(hDeps.clock_gettime_frame s clk).1, (hDeps.clock_gettime_frame s clk).2.1⟩
  have hCgP : ∀ s clk, proj ((deps.timeRand.clock_gettime clk).run s).2 = proj s :=
    fun s clk => Prod.ext (hCgTO s clk).1 (hCgTO s clk).2
  have hNsP : ∀ s clk abs r, proj ((deps.timeRand.clock_nanosleep clk abs r).run s).2 = proj s :=
    fun s clk abs r =>
      Prod.ext (hDeps.clock_nanosleep_frame s clk abs r).1 (hDeps.clock_nanosleep_frame s clk abs r).2
  unfold SysBridge.awaitOsPhase
  have hSetupIn :
      ∃ bIn₀ inFd? s₃,
        (SysBridge.setupStdinPipe deps.files stdin inFd0?).run s₂ = (inFd?, s₃) ∧
        getTbl s₃ = getTbl s₂ ∧
        inFd? = optFdOf inW bIn₀ ∧
        openFds s₃ = pipePrefix errR outR inW true true bIn₀ base := by
    unfold SysBridge.setupStdinPipe
    rw [hSlotIn]
    split
    · obtain ⟨hTi, hOi⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT inW
        (fun b => pipePrefix errR outR inW true true b base)
        (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) true s₂ hOpen₂
      refine ⟨false, none, ((Files.closeOpt deps.files (optFdOf inW true)).run s₂).2,
        ?_, hTi, rfl, hOi⟩
      rw [stateT_bind_eq]; rfl
    · dsimp only [optFdOf]
      refine ⟨true, some inW, ((deps.files.fcntl inW (.setFl true false)).run s₂).2,
        ?_, (hFcntlTO s₂ inW _).1, rfl, (hFcntlTO s₂ inW _).2.trans hOpen₂⟩
      rw [stateT_bind_eq]; rfl
  rcases hSetupIn with ⟨bIn₀, inFd?, s₃, hRunInSet, hFs₃, hInOpt, hOpen₃⟩
  rw [stateT_bind_eq, hRunInSet]
  dsimp only
  have hSetupOut :
      ∃ s₄,
        (Files.setNonblockingOpt deps.files outFd0?).run s₃ = ((), s₄) ∧
        getTbl s₄ = getTbl s₂ ∧
        openFds s₄ = pipePrefix errR outR inW true true bIn₀ base := by
    unfold Files.setNonblockingOpt
    rw [hSlotOut]
    dsimp only [optFdOf]
    refine ⟨((deps.files.fcntl outR (.setFl true false)).run s₃).2,
      ?_, (hFcntlTO s₃ outR _).1.trans hFs₃, (hFcntlTO s₃ outR _).2.trans hOpen₃⟩
    rw [stateT_bind_eq]; rfl
  rcases hSetupOut with ⟨s₄, hRunOutSet, hFs₄, hOpen₄⟩
  rw [stateT_bind_eq, hRunOutSet]
  dsimp only
  have hSetupErr :
      ∃ s₅,
        (Files.setNonblockingOpt deps.files errFd0?).run s₄ = ((), s₅) ∧
        getTbl s₅ = getTbl s₂ ∧
        openFds s₅ = pipePrefix errR outR inW true true bIn₀ base := by
    unfold Files.setNonblockingOpt
    rw [hSlotErr]
    dsimp only [optFdOf]
    refine ⟨((deps.files.fcntl errR (.setFl true false)).run s₄).2,
      ?_, (hFcntlTO s₄ errR _).1.trans hFs₄, (hFcntlTO s₄ errR _).2.trans hOpen₄⟩
    rw [stateT_bind_eq]; rfl
  rcases hSetupErr with ⟨s₅, hRunErrSet, hFs₅, hOpen₅⟩
  rw [stateT_bind_eq, hRunErrSet]
  dsimp only
  have hStartStep :
      ∃ startRes s₆,
        (SysBridge.readStartMsOpt deps.timeRand timeoutMs?).run s₅ = (startRes, s₆) ∧
        getTbl s₆ = getTbl s₂ ∧
        openFds s₆ = pipePrefix errR outR inW true true bIn₀ base ∧
        (∀ err, startRes = .error err →
          err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
    unfold SysBridge.readStartMsOpt
    cases timeoutMs? with
    | none => exact ⟨.ok 0, s₅, rfl, hFs₅, hOpen₅, (by intro _ h; cases h)⟩
    | some _ =>
      have hFmP := monoNowMs_spec proj deps.timeRand hCgP s₅
      rcases hM : (TimeRand.monoNowMs deps.timeRand).run s₅ with ⟨mRes, sM⟩
      rw [hM] at hFmP
      cases mRes with
      | ok ms =>
        exact ⟨.ok ms, sM, by rw [stateT_bind_eq, hM]; rfl,
          (congrArg Prod.fst hFmP).trans hFs₅,
          (congrArg Prod.snd hFmP).trans hOpen₅, (by intro _ h; cases h)⟩
      | error e =>
        exact ⟨.error (SysBridge.mapErrno none "clock_gettime" e), sM,
          by rw [stateT_bind_eq, hM]; rfl,
          (congrArg Prod.fst hFmP).trans hFs₅,
          (congrArg Prod.snd hFmP).trans hOpen₅,
          fun err he => by
            injection he with hE; rw [← hE]
            exact (mapErrno_kind_and_msg none "clock_gettime" e).2⟩
  rcases hStartStep with ⟨startRes, s₆, hRunStart, hFs₆, hOpen₆, hErrStart⟩
  rw [stateT_bind_eq, hRunStart]
  dsimp only
  cases startRes with
  | error e =>
    dsimp only
    rw [hInOpt, hSlotOut, hSlotErr, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
    dsimp only [pure, StateT.pure, StateT.run]
    obtain ⟨hTc1, hOc1⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT inW
      (fun b => pipePrefix errR outR inW true true b base)
      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_in hEI hOI]) bIn₀ s₆ hOpen₆
    obtain ⟨hTc2, hOc2⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT outR
      (fun b => pipePrefix errR outR inW true b false base)
      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_out hEO]) true _ hOc1
    obtain ⟨hTc3, hOc3⟩ := closeOpt_optFdOf getTbl openFds deps.files hCloseT errR
      (fun b => pipePrefix errR outR inW b false false base)
      (fun sx hsx => by rw [hCloseO, hsx, pipePrefix_erase_err]) true _ hOc2
    refine ⟨hTc3.trans (hTc2.trans (hTc1.trans hFs₆)), hOc3, ?_,
      (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    exact hErrStart e rfl
  | ok startMs =>
    dsimp only
    rw [stateT_bind_eq]
    let initSt : StreamLoopState fd :=
      { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
    have hPollTO : ∀ s entries to, getTbl ((deps.poll.ppoll entries to).run s).2 = getTbl s ∧
        openFds ((deps.poll.ppoll entries to).run s).2 = openFds s :=
      fun s entries to => ⟨(hDeps.ppoll_frame s entries to).1, (hDeps.ppoll_frame s entries to).2.1⟩
    obtain ⟨hFst, hOst, hEofSt, hToSt, hLimSt, hErrSt⟩ := streamPipesLoop_spec getTbl openFds
      deps.files deps.poll deps.timeRand hCloseT hCloseO hReadTO hWriteTO hPollTO hCgTO
      hEO hEI hOI base stdin startMs timeoutMs? maxOutputBytes? eintrFuel
      true true bIn₀ initSt ioFuel s₆ hInOpt hSlotOut hSlotErr hOpen₆ rfl rfl (fun _ _ => Nat.zero_le _)
    cases hLoop : (SysBridge.streamPipesLoop deps.files deps.poll deps.timeRand stdin startMs
        timeoutMs? maxOutputBytes? eintrFuel initSt ioFuel).run s₆ with
    | mk loopRes s₇ =>
      rw [hLoop] at hFst hOst hEofSt hToSt hLimSt hErrSt
      have hTbl₇ : getTbl s₇ = getTbl s₂ := hFst.trans hFs₆
      cases loopRes with
      | error e =>
        dsimp only [pure, StateT.pure, StateT.run]
        refine ⟨hTbl₇, hOst, ?_,
          (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        exact (hErrSt e rfl).2
      | ok phase =>
        cases phase with
        | timedOut out errB =>
          dsimp only [pure, StateT.pure, StateT.run]
          exact ⟨hTbl₇, hOst, (by intro _ h; cases h), (by intro _ _ h; cases h),
            fun _ _ _ _ => hToSt out errB rfl, (by intro _ _ _ h; cases h)⟩
        | limitExceeded out errB =>
          dsimp only [pure, StateT.pure, StateT.run]
          obtain ⟨hMaxSome, hMaxLe⟩ := hLimSt out errB rfl
          refine ⟨hTbl₇, hOst, (by intro _ h; cases h), (by intro _ _ h; cases h),
            (by intro _ _ _ h; cases h), ?_⟩
          intro _ o e hEq
          injection hEq with hP
          injection hP with _ hSub
          injection hSub with hO hE
          rw [← hO, ← hE]
          exact ⟨hMaxSome, hMaxLe⟩
        | eof out errB =>
          dsimp only
          have hCapEof := hEofSt out errB rfl
          cases timeoutMs? with
          | none =>
            dsimp only
            rw [stateT_bind_eq]
            obtain ⟨hFwP, hExW, hNoToW, hNoLimW, hErrW⟩ := waitBlockingLoop_spec proj deps.proc
              hWaitP pid.toInt32 out errB eintrFuel s₇
            cases hWRes : (SysBridge.waitBlockingLoop deps.proc pid.toInt32 out errB eintrFuel).run s₇ with
            | mk wRes s₈ =>
              rw [hWRes] at hFwP hExW hNoToW hNoLimW hErrW
              have hTbl₈ : getTbl s₈ = getTbl s₂ := (congrArg Prod.fst hFwP).trans hTbl₇
              have hOpen₈ : openFds s₈ = base := (congrArg Prod.snd hFwP).trans hOst
              cases wRes with
              | error e =>
                dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hTbl₈, hOpen₈, ?_,
                  (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
                intro err hEq; injection hEq with hE; rw [← hE]
                exact (hErrW e rfl).2
              | ok outcome =>
                dsimp only [pure, StateT.pure, StateT.run]
                refine ⟨hTbl₈, hOpen₈, (by intro _ h; cases h), ?_, ?_, ?_⟩
                · intro _ res hEq
                  injection hEq with hP
                  injection hP with _ hOutEq
                  obtain ⟨hOutB, hErrB⟩ := hExW res (congrArg Except.ok hOutEq)
                  rw [hOutB, hErrB]
                  exact hCapEof
                · intro _ o e hEq
                  injection hEq with hP
                  injection hP with _ hOutEq
                  exact absurd (congrArg Except.ok hOutEq) (hNoToW o e)
                · intro _ o e hEq
                  injection hEq with hP
                  injection hP with _ hOutEq
                  exact absurd (congrArg Except.ok hOutEq) (hNoLimW o e)
          | some timeoutMs =>
            dsimp only
            obtain ⟨hFwP, hExW, hNoLimW, hErrW⟩ := waitTimedLoop_spec proj deps.proc deps.timeRand
              hWaitP hCgP hNsP pid.toInt32 startMs timeoutMs out errB ioFuel s₇
            cases hWRes : (SysBridge.waitTimedLoop deps.proc deps.timeRand pid.toInt32
                startMs timeoutMs out errB ioFuel).run s₇ with
            | mk wRes s₈ =>
              rw [hWRes] at hFwP hExW hNoLimW hErrW
              have hTbl₈ : getTbl s₈ = getTbl s₂ := (congrArg Prod.fst hFwP).trans hTbl₇
              have hOpen₈ : openFds s₈ = base := (congrArg Prod.snd hFwP).trans hOst
              cases wRes with
              | error e =>
                refine ⟨hTbl₈, hOpen₈, ?_,
                  (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
                intro err hEq; injection hEq with hE; rw [← hE]
                exact (hErrW e rfl).2
              | ok wpair =>
                rcases wpair with ⟨waitedFlag, outcome⟩
                refine ⟨hTbl₈, hOpen₈, (by intro _ h; cases h), ?_, (by intro _ _ _ _; rfl), ?_⟩
                · intro wf res hEq
                  injection hEq with hP
                  injection hP with hWfEq hOutEq
                  subst hWfEq
                  obtain ⟨hOutB, hErrB⟩ := hExW waitedFlag res
                    (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq)
                  rw [hOutB, hErrB]
                  exact hCapEof
                · intro wf o e hEq
                  injection hEq with hP
                  injection hP with hWfEq hOutEq
                  subst hWfEq
                  exact absurd (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq)
                    (hNoLimW waitedFlag o e)

/-- Core bridge theorem: for **every** `deps` satisfying `RefinesHealthySysDeps`, `SysBridge.mkRawOpsM deps (stateProcTableOps getTbl setTbl) eintrFuel ioFuel` satisfies `RawProcessLaws openFds` (including full OS descriptor conservation and process-slot conservation) across arbitrary short pipe `read`/`write`, `EAGAIN`, `EPIPE`, bounded `EINTR`, and everyday OS errors (`EMFILE`, `ENOENT`, `EACCES`). -/
theorem mkRawOpsM_satisfies_RawProcessLaws {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel ioFuel : Nat) :
    RawProcessLaws openFds
      (SysBridge.mkRawOpsM deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel ioFuel) := by
  let proj := fun s : S => (getTbl s, openFds s)
  have hWaitTO : ∀ s pid fl, getTbl ((deps.proc.waitpid pid fl).run s).2 = getTbl s ∧
      openFds ((deps.proc.waitpid pid fl).run s).2 = openFds s :=
    fun s pid fl => ⟨(hDeps.waitpid_frame s pid fl).1, (hDeps.waitpid_frame s pid fl).2.1⟩
  have hKillP : ∀ s t sg, proj ((deps.proc.kill t sg).run s).2 = proj s :=
    fun s t sg => Prod.ext (hDeps.kill_frame s t sg).1 (hDeps.kill_frame s t sg).2.1
  have hNsP : ∀ s clk abs r, proj ((deps.timeRand.clock_nanosleep clk abs r).run s).2 = proj s :=
    fun s clk abs r =>
      Prod.ext (hDeps.clock_nanosleep_frame s clk abs r).1 (hDeps.clock_nanosleep_frame s clk abs r).2
  have hSpawnSpec := spawnPure_laws getTbl setTbl openFds deps hDeps eintrFuel
  refine
    { mapRawError_eq := rfl
      activeCount_pure := fun _ => rfl
      spawn_err := ?_
      spawn_lifecycle := ?_ }
  · intro s req err hEq
    have hSp := (hSpawnSpec s req).1 err (congrArg Prod.fst hEq)
    exact ⟨congrArg (fun t => t.slots.length) hSp.1, hSp.2.1, hSp.2.2⟩
  · intro s₀ req h s₁ hSpawnOk
    have hSpOk := (hSpawnSpec s₀ req).2 h (congrArg Prod.fst hSpawnOk)
    have hs₁Eq :
        ((SysBridge.spawnPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel req).run s₀).2 = s₁ :=
      congrArg Prod.snd hSpawnOk
    rw [hs₁Eq] at hSpOk
    obtain ⟨hPidPos, hPgidPos, errR, outR, inW, slot, hEO, hEI, hOI,
      hSlotIn, hSlotOut, hSlotErr, hOpen₁, hTbl₁⟩ := hSpOk
    refine ⟨hPidPos, hPgidPos, ?_⟩
    have hKillAndReapNone : ∀ (stAw : S) (sl : ProcSlotM fd) (rest : List (Nat × ProcSlotM fd)) (nid : Nat),
        getTbl stAw = { nextId := nid, slots := (h.handleId, sl) :: rest } →
        openFds stAw = openFds s₀ →
        (sl.stdinFd? = none ∧ sl.stdoutFd? = none ∧ sl.stderrFd? = none) →
        rest.length = (getTbl s₀).slots.length →
        let kl := (SysBridge.killProcessGroupPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run stAw
        let rp := (SysBridge.reapPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run kl.2
        (getTbl rp.2).slots.length = (getTbl s₀).slots.length ∧
        openFds rp.2 = openFds s₀ ∧
        (∀ rerr, rp.1 = .error rerr →
          rerr.kind ≠ .timedOut ∧ rerr.kind ≠ .outputLimitExceeded ∧ rerr.kind ≠ .terminatedBySignal) := by
      intro stAw sl rest nid hTblAw hOpenAw hFdsNone hRestLen
      have hFkP := killProcessGroupPure_frame proj getTbl setTbl deps hKillP hNsP eintrFuel h stAw
      let kl := (SysBridge.killProcessGroupPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run stAw
      have hTblKl : getTbl kl.2 = { nextId := nid, slots := (h.handleId, sl) :: rest } :=
        (congrArg Prod.fst hFkP).trans hTblAw
      have hOpenKl : openFds kl.2 = openFds s₀ :=
        (congrArg Prod.snd hFkP).trans hOpenAw
      obtain ⟨hLenRp, hOpenRp, hErrRp⟩ := reapPure_head_slot_none_spec getTbl setTbl openFds
        hDeps.get_set hDeps.openFds_set deps hWaitTO eintrFuel h sl rest nid kl.2 hTblKl hFdsNone
      exact ⟨hLenRp.trans hRestLen, hOpenRp.trans hOpenKl, hErrRp⟩
    let restTaken := (getTbl s₀).slots.map fun (k, s) =>
      if k == h.handleId then (k, { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none }) else (k, s)
    have hRestTakenLen : restTaken.length = (getTbl s₀).slots.length := List.length_map _
    let slotTaken : ProcSlotM fd := { slot with stdinFd? := none, stdoutFd? := none, stderrFd? := none }
    have hSlotTakenNone : slotTaken.stdinFd? = none ∧ slotTaken.stdoutFd? = none ∧ slotTaken.stderrFd? = none :=
      ⟨rfl, rfl, rfl⟩
    have hTake : ((SysBridge.stateProcTableOps getTbl setTbl).takeSlotIo h.handleId).run s₁ =
        (some (slot.pid, slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?),
         setTbl s₁ { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken }) := by
      dsimp only [SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
      rw [hTbl₁]
      simp only [SysBridge.takeSlotIoPure, SysBridge.findSlotPure, beq_self_eq_true, ↓reduceIte,
        List.map_cons, slotTaken, restTaken]
      rfl
    have hMarkHelper : ∀ (stM : S) (waitedFlag : Bool),
        getTbl stM = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } →
        ∃ slM restM,
          ((SysBridge.stateProcTableOps getTbl setTbl).markWaited h.handleId waitedFlag).run stM =
            (true, setTbl stM { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }) ∧
          (slM.stdinFd? = none ∧ slM.stdoutFd? = none ∧ slM.stderrFd? = none) ∧
          restM.length = (getTbl s₀).slots.length := by
      intro stM waitedFlag hTblM
      refine ⟨{ slotTaken with waited := slotTaken.waited || waitedFlag },
        restTaken.map (fun (k, s) => if k == h.handleId then (k, { s with waited := s.waited || waitedFlag }) else (k, s)),
        ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
      · dsimp only [SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run]
        rw [hTblM]
        simp only [SysBridge.markWaitedPure, SysBridge.findSlotPure, beq_self_eq_true,
          ↓reduceIte, List.map_cons]
        rfl
      · rw [List.length_map, hRestTakenLen]
    dsimp only [SysBridge.mkRawOpsM]
    unfold SysBridge.awaitOutputPure
    rw [stateT_bind_eq, hTake]
    dsimp only
    rw [stateT_bind_eq]
    let s₂ := setTbl s₁ { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken }
    have hTbl₂ : getTbl s₂ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
      hDeps.get_set s₁ _
    have hOpen₂ : openFds s₂ = pipePrefix errR outR inW true true true (openFds s₀) :=
      (hDeps.openFds_set s₁ _).trans hOpen₁
    have hAwOs := awaitOsPhase_laws getTbl setTbl openFds deps hDeps eintrFuel ioFuel
      slot.pid slot.stdinFd? slot.stdoutFd? slot.stderrFd?
      hEO hEI hOI hSlotIn hSlotOut hSlotErr (openFds s₀)
      req.stdin req.timeoutMs req.maxOutputBytes s₂ hOpen₂
    cases hAwRun : (SysBridge.awaitOsPhase deps eintrFuel ioFuel slot.pid slot.stdinFd? slot.stdoutFd?
        slot.stderrFd? req.stdin req.timeoutMs req.maxOutputBytes).run s₂ with
    | mk awRes s₇ =>
      rw [hAwRun] at hAwOs
      obtain ⟨hFs₇, hOs₇, hAwErr, hAwEx, hAwTo, hAwLim⟩ := hAwOs
      have hTbl₇ : getTbl s₇ = { nextId := h.handleId + 1, slots := (h.handleId, slotTaken) :: restTaken } :=
        hFs₇.trans hTbl₂
      cases awRes with
      | error e =>
        dsimp only [pure, StateT.pure, StateT.run]
        obtain ⟨hLenEnd, hOpenEnd, _⟩ := hKillAndReapNone s₇ slotTaken restTaken (h.handleId + 1)
          hTbl₇ hOs₇ hSlotTakenNone hRestTakenLen
        refine ⟨?_, (by intro _ h; cases h), (by intro _ _ _ h; cases h),
          (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        obtain ⟨hk1, hk2, hk3⟩ := hAwErr e rfl
        exact ⟨hk1, hk2, hk3, hLenEnd, hOpenEnd⟩
      | ok pair =>
        rcases pair with ⟨waitedFlag, outcome⟩
        dsimp only
        obtain ⟨slM, restM, hMkRun, hSlMNone, hRestMLen⟩ := hMarkHelper s₇ waitedFlag hTbl₇
        rw [stateT_bind_eq, hMkRun]
        dsimp only
        rw [ite_eq_right (by decide)]
        dsimp only [pure, StateT.pure, StateT.run]
        let s₉ := setTbl s₇ { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM }
        have hTbl₉ : getTbl s₉ = { nextId := h.handleId + 1, slots := (h.handleId, slM) :: restM } :=
          hDeps.get_set s₇ _
        have hOpen₉ : openFds s₉ = openFds s₀ :=
          (hDeps.openFds_set s₇ _).trans hOs₇
        obtain ⟨hLenKillReap, hOpenKillReap, _⟩ := hKillAndReapNone s₉ slM restM (h.handleId + 1)
          hTbl₉ hOpen₉ hSlMNone hRestMLen
        obtain ⟨hLenDirectReap, hOpenDirectReap, hErrDirectReap⟩ := reapPure_head_slot_none_spec
          getTbl setTbl openFds hDeps.get_set hDeps.openFds_set deps hWaitTO
          eintrFuel h slM restM (h.handleId + 1) s₉ hTbl₉ hSlMNone
        refine ⟨(by intro _ h; cases h), ?_, ?_, ?_, ?_⟩
        · intro res hEq
          injection hEq with hOutEq
          exact ⟨hAwEx waitedFlag res (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq),
            hLenDirectReap.trans hRestMLen, hOpenDirectReap.trans hOpen₉, hErrDirectReap⟩
        · intro _ _ _ _
          exact ⟨hLenKillReap, hOpenKillReap⟩
        · intro o e hEq
          injection hEq with hOutEq
          exact ⟨hAwTo waitedFlag o e (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq),
            hLenKillReap, hOpenKillReap⟩
        · intro o e hEq
          injection hEq with hOutEq
          obtain ⟨hMaxSome, hMaxLe⟩ := hAwLim waitedFlag o e
            (congrArg (fun x => Except.ok (waitedFlag, x)) hOutEq)
          exact ⟨hMaxSome, hMaxLe, hLenKillReap, hOpenKillReap⟩

end LeanSwe.Process.Proofs

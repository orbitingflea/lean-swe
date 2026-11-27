import LeanSweProofs.Process.Proofs.SysBridge.StreamSteps

/-!
Blocking/timed `waitpid`, `killProcessGroupPure`, `reapPure`, and fresh-pipe erasure
lemmas for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

private theorem decodeWaitOutcome_spec (wr : LinuxSyscall.Process.WaitResult) (out errB : ByteArray) :
    (∀ res, SysBridge.decodeWaitOutcome wr out errB = .exited res → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ o e, SysBridge.decodeWaitOutcome wr out errB ≠ .timedOut o e) ∧
    (∀ o e, SysBridge.decodeWaitOutcome wr out errB ≠ .outputLimitExceeded o e) := by
  cases wr with
  | signaled _ _ _ =>
    dsimp only [SysBridge.decodeWaitOutcome]
    exact ⟨(by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
  | exited _ _ | stopped _ _ | continued _ | stillRunning =>
    dsimp only [SysBridge.decodeWaitOutcome]
    refine ⟨?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h)⟩
    intro res hEq
    injection hEq with hR
    rw [← hR]
    exact ⟨rfl, rfl⟩

theorem waitBlockingLoop_spec {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (pid : Int32) (out errB : ByteArray) (fuel : Nat) (s : S) :
    let r := (SysBridge.waitBlockingLoop proc pid out errB fuel).run s
    proj r.2 = proj s ∧
    (∀ res, r.1 = .ok (.exited res) → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ o e, r.1 ≠ .ok (.timedOut o e)) ∧
    (∀ o e, r.1 ≠ .ok (.outputLimitExceeded o e)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  induction fuel generalizing s with
  | zero =>
    unfold SysBridge.waitBlockingLoop
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ f ih =>
    unfold SysBridge.waitBlockingLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid {}
    let s1 := ((proc.waitpid pid {}).run s).2
    cases hW : ((proc.waitpid pid {}).run s).1 with
    | ok wr =>
      dsimp only [pure, StateT.pure, StateT.run]
      obtain ⟨hEx, hNoTo, hNoLim⟩ := decodeWaitOutcome_spec wr out errB
      refine ⟨hFw, ?_, ?_, ?_, (by intro _ h; cases h)⟩
      · intro res hEq; injection hEq with hSub; exact hEx res hSub
      · intro o e hEq; injection hEq with hSub; exact hNoTo o e hSub
      · intro o e hEq; injection hEq with hSub; exact hNoLim o e hSub
    | error e =>
      dsimp only
      split
      · obtain ⟨hFi, hEx, hNoTo, hNoLim, hEi⟩ := ih s1
        exact ⟨hFi.trans hFw, hEx, hNoTo, hNoLim, hEi⟩
      · split
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, ?_, (by intro _ _ h; cases h), (by intro _ _ h; cases h), (by intro _ h; cases h)⟩
          intro res hEq; injection hEq with hSub; injection hSub with hR; rw [← hR]; exact ⟨rfl, rfl⟩
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, (by intro _ h; cases h), (by intro _ _ h; cases h), (by intro _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "waitpid" e

theorem waitTimedLoop_spec {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (hCg : ∀ s clk, proj ((timeRand.clock_gettime clk).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (pid : Int32) (startMs timeoutMs : Nat) (out errB : ByteArray) (fuel : Nat) (s : S) :
    let r := (SysBridge.waitTimedLoop proc timeRand pid startMs timeoutMs out errB fuel).run s
    proj r.2 = proj s ∧
    (∀ w res, r.1 = .ok (w, .exited res) → res.stdout = out ∧ res.stderr = errB) ∧
    (∀ w o e, r.1 ≠ .ok (w, .outputLimitExceeded o e)) ∧
    (∀ err, r.1 = .error err →
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  induction fuel generalizing s with
  | zero =>
    unfold SysBridge.waitTimedLoop
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨rfl, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  | succ f ih =>
    unfold SysBridge.waitTimedLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid { nohang := true }
    let s1 := ((proc.waitpid pid { nohang := true }).run s).2
    cases hW : ((proc.waitpid pid { nohang := true }).run s).1 with
    | ok wr =>
      cases wr with
      | stillRunning =>
        dsimp only
        rw [stateT_bind_eq]
        obtain ⟨hFc, _, _⟩ := checkTimedOut_spec proj timeRand hCg startMs (some timeoutMs) s1
        let s2 := ((TimeRand.checkTimedOut timeRand startMs (some timeoutMs)).run s1).2
        cases hCt : ((TimeRand.checkTimedOut timeRand startMs (some timeoutMs)).run s1).1 with
        | error e =>
          dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFc.trans hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "clock_gettime" e
        | ok pair =>
          rcases pair with ⟨isTo, remMs⟩
          cases isTo
          · dsimp only
            rw [stateT_bind_eq]
            have hFs := sleepMonoMs_frame proj timeRand hNs (Nat.min remMs 5) s2
            obtain ⟨hFi, hEx, hNoLim, hEi⟩ := ih ((TimeRand.sleepMonoMs timeRand (Nat.min remMs 5)).run s2).2
            exact ⟨hFi.trans (hFs.trans (hFc.trans hFw)), hEx, hNoLim, hEi⟩
          · dsimp only [pure, StateT.pure, StateT.run]
            exact ⟨hFc.trans hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
      | exited rPid code =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
      | signaled rPid sig core =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        exact ⟨hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
      | stopped rPid sig =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
      | continued rPid =>
        dsimp only [pure, StateT.pure, StateT.run, SysBridge.decodeWaitOutcome]
        refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
        intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
        exact ⟨rfl, rfl⟩
    | error e =>
      dsimp only
      split
      · obtain ⟨hFi, hEx, hNoLim, hEi⟩ := ih s1
        exact ⟨hFi.trans hFw, hEx, hNoLim, hEi⟩
      · split
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, ?_, (by intro _ _ _ h; cases h), (by intro _ h; cases h)⟩
          intro _ res hEq; injection hEq with hP; injection hP with _ hSub; injection hSub with hR; rw [← hR]
          exact ⟨rfl, rfl⟩
        · dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨hFw, (by intro _ _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact mapErrno_kind_and_msg none "waitpid" e

private theorem killGraceProbeLoop_frame {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (timeRand : TimeRand.TimeRandOpsM (StateM S))
    (hKill : ∀ s t sg, proj ((proc.kill t sg).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (target : Int32) (steps : Nat) (s : S) :
    proj ((SysBridge.killGraceProbeLoop proc timeRand target steps).run s).2 = proj s := by
  induction steps generalizing s with
  | zero => rfl
  | succ st ih =>
    unfold SysBridge.killGraceProbeLoop
    rw [stateT_bind_eq, stateT_bind_eq]
    have hFs := sleepMonoMs_frame proj timeRand hNs 5 s
    let s1 := ((TimeRand.sleepMonoMs timeRand 5).run s).2
    have hFk := hKill s1 target .sigzero
    let s2 := ((proc.kill target .sigzero).run s1).2
    cases ((proc.kill target .sigzero).run s1).1 with
    | error e =>
      dsimp only
      split
      · exact hFk.trans hFs
      · exact (ih s2).trans (hFk.trans hFs)
    | ok _ =>
      dsimp only
      exact (ih s2).trans (hFk.trans hFs)

theorem killProcessGroupPure_frame {S β fd : Type}
    (proj : S → β)
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (deps : SysDepsM (StateM S) fd)
    (hKill : ∀ s t sg, proj ((deps.proc.kill t sg).run s).2 = proj s)
    (hNs : ∀ s clk abs req, proj ((deps.timeRand.clock_nanosleep clk abs req).run s).2 = proj s)
    (eintrFuel : Nat) (h : ProcessHandle) (s : S) :
    proj ((SysBridge.killProcessGroupPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run s).2 =
      proj s := by
  unfold SysBridge.killProcessGroupPure SysBridge.killGroupOsPhase
  rw [stateT_bind_eq]
  have hLk : ((SysBridge.stateProcTableOps getTbl setTbl).lookupPgid h.handleId).run s =
      ((SysBridge.findSlotPure h.handleId (getTbl s).slots).map (·.pgid), s) := rfl
  rw [hLk]
  dsimp only
  cases (SysBridge.findSlotPure h.handleId (getTbl s).slots).map (·.pgid) with
  | none => rfl
  | some pgid =>
    dsimp only
    split
    · rfl
    · rw [stateT_bind_eq]
      let target := LinuxSyscall.Process.killTargetOfPgid pgid
      have hF1 := retryEintr_frame proj (deps.proc.kill target .sigterm)
        (fun st => hKill st target .sigterm) eintrFuel s
      let s1 := ((LinuxSyscall.retryEintr (deps.proc.kill target .sigterm) eintrFuel).run s).2
      cases ((LinuxSyscall.retryEintr (deps.proc.kill target .sigterm) eintrFuel).run s).1 with
      | error e =>
        dsimp only
        split <;> exact hF1
      | ok _ =>
        dsimp only
        rw [stateT_bind_eq]
        have hFg := killGraceProbeLoop_frame proj deps.proc deps.timeRand hKill hNs target 5 s1
        let s2 := ((SysBridge.killGraceProbeLoop deps.proc deps.timeRand target 5).run s1).2
        cases ((SysBridge.killGraceProbeLoop deps.proc deps.timeRand target 5).run s1).1 with
        | true => exact hFg.trans hF1
        | false =>
          rw [ite_eq_right (by decide)]
          rw [stateT_bind_eq]
          have hF2 := retryEintr_frame proj (deps.proc.kill target .sigkill)
            (fun st => hKill st target .sigkill) eintrFuel s2
          cases ((LinuxSyscall.retryEintr (deps.proc.kill target .sigkill) eintrFuel).run s2).1 with
          | error e =>
            dsimp only
            split <;> exact hF2.trans (hFg.trans hF1)
          | ok _ =>
            exact hF2.trans (hFg.trans hF1)

private theorem reapWaitLoop_frame {S β fd : Type}
    (proj : S → β)
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM S) fd)
    (hWait : ∀ s pid fl, proj ((proc.waitpid pid fl).run s).2 = proj s)
    (pid : Int32) (fuel : Nat) (s : S) :
    proj ((LinuxSyscall.Process.waitpidReapLoop proc pid fuel).run s).2 = proj s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih =>
    unfold LinuxSyscall.Process.waitpidReapLoop
    rw [stateT_bind_eq]
    have hFw := hWait s pid {}
    cases ((proc.waitpid pid {}).run s).1 with
    | ok _ => exact hFw
    | error _ =>
      dsimp only
      split
      · exact (ih _).trans hFw
      · split <;> exact hFw

theorem reapPure_head_slot_none_spec {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (hGetSet : ∀ s t, getTbl (setTbl s t) = t)
    (hOpenSet : ∀ s t, openFds (setTbl s t) = openFds s)
    (deps : SysDepsM (StateM S) fd)
    (hWait : ∀ s pid fl,
      getTbl ((deps.proc.waitpid pid fl).run s).2 = getTbl s ∧
      openFds ((deps.proc.waitpid pid fl).run s).2 = openFds s)
    (eintrFuel : Nat) (h : ProcessHandle) (slot : ProcSlotM fd)
    (rest : List (Nat × ProcSlotM fd)) (nextId : Nat) (s : S)
    (hTbl : getTbl s = { nextId := nextId, slots := (h.handleId, slot) :: rest })
    (hFdsNone : slot.stdinFd? = none ∧ slot.stdoutFd? = none ∧ slot.stderrFd? = none) :
    let r := (SysBridge.reapPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel h).run s
    (getTbl r.2).slots.length = rest.length ∧
    openFds r.2 = openFds s ∧
    (∀ err, r.1 = .error err →
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) := by
  dsimp only
  let proj := fun st : S => (getTbl st, openFds st)
  have hWaitP : ∀ st pid fl, proj ((deps.proc.waitpid pid fl).run st).2 = proj st :=
    fun st pid fl => Prod.ext (hWait st pid fl).1 (hWait st pid fl).2
  unfold SysBridge.reapPure SysBridge.reapOsPhase
  rw [stateT_bind_eq]
  have hDet : ((SysBridge.stateProcTableOps getTbl setTbl).detachSlot h.handleId).run s =
      (some slot, setTbl s { nextId := nextId, slots := rest }) := by
    dsimp only [SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    rw [hTbl]
    simp only [SysBridge.detachSlotPure, SysBridge.removeSlotList, beq_self_eq_true, ↓reduceIte]
    rfl
  rw [hDet]
  dsimp only
  let s1 := setTbl s { nextId := nextId, slots := rest }
  have hGs1 : getTbl s1 = { nextId := nextId, slots := rest } := hGetSet s _
  have hOs1 : openFds s1 = openFds s := hOpenSet s _
  rw [hFdsNone.1, hFdsNone.2.1, hFdsNone.2.2]
  dsimp only [Files.closeOpt]
  rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
  dsimp only [pure, StateT.pure, StateT.run]
  split
  · have hFrP := reapWaitLoop_frame proj deps.proc hWaitP slot.pid.toInt32 eintrFuel s1
    dsimp only [StateT.run] at hFrP
    rcases hW : LinuxSyscall.Process.waitpidReapLoop deps.proc slot.pid.toInt32 eintrFuel s1 with ⟨wRes, sW⟩
    rw [hW] at hFrP
    have hFrT : getTbl sW = { nextId := nextId, slots := rest } := (congrArg Prod.fst hFrP).trans hGs1
    have hFrO : openFds sW = openFds s := (congrArg Prod.snd hFrP).trans hOs1
    dsimp only [bind, StateT.bind, StateT.run]
    change _ ∧ _ ∧ _
    have hW' : LinuxSyscall.Process.waitpidReapLoop deps.proc slot.pid.toInt32 eintrFuel
        (setTbl s { nextId := nextId, slots := rest }) = (wRes, sW) := hW
    rw [hW']
    cases wRes with
    | ok _ =>
      exact ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, (by intro _ h; cases h)⟩
    | error oe =>
      cases oe with
      | none =>
        refine ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, ?_⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        refine ⟨?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
      | some e =>
        refine ⟨congrArg (fun t => t.slots.length) hFrT, hFrO, ?_⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        have hM := mapErrno_kind_and_msg none "waitpid" e
        exact ⟨hM.2.1, hM.2.2.1, hM.2.2.2⟩
  · dsimp only [pure, StateT.pure, StateT.run]
    exact ⟨congrArg (fun t => t.slots.length) hGs1, hOs1, (by intro _ h; cases h)⟩

theorem erase_two_fresh {fd : Type} [DecidableEq fd]
    {r w : fd} {base : List fd} (hNe : r ≠ w) :
    ((w :: r :: base).erase r).erase w = base := by
  simp [beq_false_of_ne (Ne.symm hNe)]

theorem erase_four_fresh {fd : Type} [DecidableEq fd]
    {r1 w1 r2 w2 : fd} {base : List fd}
    (h1 : r1 ≠ w1) (h2 : r2 ≠ w2)
    (hr2 : r2 ∉ w1 :: r1 :: base) (hw2 : w2 ∉ w1 :: r1 :: base) :
    ((((w2 :: r2 :: w1 :: r1 :: base).erase r1).erase w1).erase r2).erase w2 = base := by
  simp only [List.mem_cons, not_or] at hr2 hw2
  simp [beq_false_of_ne (Ne.symm h1),
    beq_false_of_ne (Ne.symm h2),
    beq_false_of_ne hr2.1,
    beq_false_of_ne hr2.2.1,
    beq_false_of_ne hw2.1,
    beq_false_of_ne hw2.2.1]

theorem erase_child_ends_six {fd : Type} [DecidableEq fd]
    {inR inW outR outW errR errW : fd} {base : List fd}
    (h1 : inR ≠ inW) (_h2 : outR ≠ outW) (_h3 : errR ≠ errW)
    (hr2 : outR ∉ inW :: inR :: base) (hw2 : outW ∉ inW :: inR :: base)
    (hr3 : errR ∉ outW :: outR :: inW :: inR :: base)
    (hw3 : errW ∉ outW :: outR :: inW :: inR :: base) :
    (((errW :: errR :: outW :: outR :: inW :: inR :: base).erase inR).erase outW).erase errW =
      errR :: outR :: inW :: base ∧
    errR ≠ outR ∧ errR ≠ inW ∧ outR ≠ inW := by
  simp only [List.mem_cons, not_or] at hr2 hw2 hr3 hw3
  refine ⟨?_, hr3.2.1, hr3.2.2.1, hr2.1⟩
  simp [beq_false_of_ne (Ne.symm h1),
    beq_false_of_ne hr2.2.1,
    beq_false_of_ne hw2.2.1,
    beq_false_of_ne hr3.1,
    beq_false_of_ne hr3.2.2.2.1,
    beq_false_of_ne hw3.1,
    beq_false_of_ne hw3.2.2.2.1]

theorem erase_parent_ends_three {fd : Type} [DecidableEq fd]
    {errR outR inW : fd} {base : List fd}
    (hEO : errR ≠ outR) (hEI : errR ≠ inW) (hOI : outR ≠ inW) :
    (((errR :: outR :: inW :: base).erase inW).erase outR).erase errR = base := by
  simp [beq_false_of_ne hEO, beq_false_of_ne hEI, beq_false_of_ne hOI]

end LeanSwe.Process.Proofs

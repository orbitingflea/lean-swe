import LeanSwe.PostFork.Proofs.PureAndWire

/-!
Kernel proofs for child I/O and error-reporting functions:
- `postfork.child.read_sync_byte` (`SyncBytePost`, `read_sync_byte_spec`),
- `postfork.child.write_all` (`WriteAllPost`, `write_all_spec`),
- `postfork.child.report_bytes_and_exit` (`ReportBytesPost`, `report_bytes_and_exit_spec`),
- `postfork.child.report_and_exit` (`report_and_exit_spec`),
- `test_postfork_readSyncByte_eintrRetryAndClose_allPass`,
- `test_postfork_writeAll_eintrPartialWriteAndReassembly_canReach`.
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section SyncByte

private theorem fd_ops_eintr_eq : postfork.fd_ops.EINTR = EINTR := by
  unfold postfork.fd_ops.EINTR EINTR
  rfl

private theorem ebadf_ne_eintr : EBADF ≠ EINTR := by
  unfold EBADF EINTR
  decide

private theorem eisdir_ne_eintr : EISDIR ≠ EINTR := by
  unfold EISDIR EINTR
  decide

private theorem epipe_ne_eintr : EPIPE ≠ EINTR := by
  unfold EPIPE EINTR
  decide

private theorem match_usize_zero {α : Type} (a b : α) :
    (match (0#usize : Usize).val with | 1 => a | _ => b) = b := by
  have h : (0#usize : Usize).val = 0 := by decide
  rw [h]
  rfl

private theorem match_usize_one {α : Type} (a b : α) :
    (match (1#usize : Usize).val with | 1 => a | _ => b) = a := by
  have h : (1#usize : Usize).val = 1 := by decide
  rw [h]
  rfl

/-- First fault in `oracle` after skipping leading `EINTR` failures. -/
def firstNonEintrFault : List StepFault → Option StepFault
  | [] => none
  | .fail e :: rest =>
    if sanitizeErrno e == EINTR then firstNonEintrFault rest else some (.fail e)
  | .seccomp e :: rest =>
    if sanitizeErrno e == EINTR then firstNonEintrFault rest else some (.seccomp e)
  | f :: _ => some f

private theorem lt_oracle_of_currentFault_seccomp {s : ChildState} {rawE : I32}
    (hcf : currentFault s = StepFault.seccomp rawE) :
    s.trace.length < s.oracle.length := by
  by_cases hlt : s.trace.length < s.oracle.length
  · exact hlt
  · have hge : s.oracle.length ≤ s.trace.length := Nat.le_of_not_lt hlt
    rw [currentFault, List.getElem?_eq_none hge] at hcf
    cases hcf

private theorem match_stepFault_nonSec {α : Type} (f : StepFault) (h : ∀ e, f ≠ .seccomp e)
    (onSec : I32 → α) (onOther : StepFault → α) :
    (match f with | .seccomp rawE => onSec rawE | other => onOther other) = onOther f := by
  cases f with
  | seccomp rawE => exact absurd rfl (h rawE)
  | normal | fail _ | partialWrite _ | dentsBatch _ => rfl

private theorem firstNonEintrFault_step_eintr (s : ChildState) (rawE : I32)
    (hcf : currentFault s = StepFault.fail rawE) (he : sanitizeErrno rawE = EINTR) :
    firstNonEintrFault (s.oracle.drop s.trace.length) =
      firstNonEintrFault (s.oracle.drop (s.trace.length + 1)) := by
  have hlt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_fail hcf
  have hdrop : s.oracle.drop s.trace.length =
      s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
    List.drop_eq_getElem_cons hlt
  have hget : currentFault s = s.oracle[s.trace.length] := by
    simp [currentFault, List.getElem?_eq_getElem hlt]
  have helem : s.oracle[s.trace.length] = StepFault.fail rawE := by
    rw [← hget, hcf]
  rw [hdrop, helem]
  simp [firstNonEintrFault, he]

private theorem firstNonEintrFault_step_seccomp_eintr (s : ChildState) (rawE : I32)
    (hcf : currentFault s = StepFault.seccomp rawE) (he : sanitizeErrno rawE = EINTR) :
    firstNonEintrFault (s.oracle.drop s.trace.length) =
      firstNonEintrFault (s.oracle.drop (s.trace.length + 1)) := by
  have hlt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_seccomp hcf
  have hdrop : s.oracle.drop s.trace.length =
      s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
    List.drop_eq_getElem_cons hlt
  have hget : currentFault s = s.oracle[s.trace.length] := by
    simp [currentFault, List.getElem?_eq_getElem hlt]
  have helem : s.oracle[s.trace.length] = StepFault.seccomp rawE := by
    rw [← hget, hcf]
  rw [hdrop, helem]
  simp [firstNonEintrFault, he]

private theorem firstNonEintrFault_fail_ne (s : ChildState) (rawE : I32)
    (hcf : currentFault s = StepFault.fail rawE) (hne : sanitizeErrno rawE ≠ EINTR) :
    firstNonEintrFault (s.oracle.drop s.trace.length) = some (StepFault.fail rawE) := by
  have hlt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_fail hcf
  have hdrop : s.oracle.drop s.trace.length =
      s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
    List.drop_eq_getElem_cons hlt
  have hget : currentFault s = s.oracle[s.trace.length] := by
    simp [currentFault, List.getElem?_eq_getElem hlt]
  have helem : s.oracle[s.trace.length] = StepFault.fail rawE := by
    rw [← hget, hcf]
  rw [hdrop, helem]
  have hbeq : (sanitizeErrno rawE == EINTR) = false := beq_false_of_ne hne
  simp [firstNonEintrFault, hbeq]

private theorem firstNonEintrFault_seccomp_ne (s : ChildState) (rawE : I32)
    (hcf : currentFault s = StepFault.seccomp rawE) (hne : sanitizeErrno rawE ≠ EINTR) :
    firstNonEintrFault (s.oracle.drop s.trace.length) = some (StepFault.seccomp rawE) := by
  have hlt : s.trace.length < s.oracle.length := lt_oracle_of_currentFault_seccomp hcf
  have hdrop : s.oracle.drop s.trace.length =
      s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
    List.drop_eq_getElem_cons hlt
  have hget : currentFault s = s.oracle[s.trace.length] := by
    simp [currentFault, List.getElem?_eq_getElem hlt]
  have helem : s.oracle[s.trace.length] = StepFault.seccomp rawE := by
    rw [← hget, hcf]
  rw [hdrop, helem]
  have hbeq : (sanitizeErrno rawE == EINTR) = false := beq_false_of_ne hne
  simp [firstNonEintrFault, hbeq]

private theorem firstNonEintrFault_nonfail (s : ChildState)
    (hcf : ∀ rawE, currentFault s ≠ StepFault.fail rawE ∧ currentFault s ≠ StepFault.seccomp rawE) :
    match firstNonEintrFault (s.oracle.drop s.trace.length) with
    | some (.fail _) | some (.seccomp _) => False
    | _ => True := by
  by_cases hlt : s.trace.length < s.oracle.length
  · have hdrop : s.oracle.drop s.trace.length =
        s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
      List.drop_eq_getElem_cons hlt
    have hget : currentFault s = s.oracle[s.trace.length] := by
      simp [currentFault, List.getElem?_eq_getElem hlt]
    rw [hdrop]
    cases hf : s.oracle[s.trace.length] with
    | normal => simp [firstNonEintrFault]
    | partialWrite _ => simp [firstNonEintrFault]
    | dentsBatch _ => simp [firstNonEintrFault]
    | fail rawE =>
      exfalso
      exact (hcf rawE).1 (hget.trans hf)
    | seccomp rawE =>
      exfalso
      exact (hcf rawE).2 (hget.trans hf)
  · have hge : s.oracle.length ≤ s.trace.length := Nat.le_of_not_lt hlt
    rw [List.drop_of_length_le hge]
    trivial

/-- Postcondition for `postfork.child.read_sync_byte`. -/
def SyncBytePost (s : ChildState) (syncR : I32) (gotOne : Bool) (s' : ChildState) : Prop :=
  if syncR < 0#i32 then
    gotOne = false ∧ s' = s
  else if s.status = Status.running then
    SameChildConfig s' s ∧
    s'.pgid = s.pgid ∧
    s'.cwd = s.cwd ∧
    s'.sig = s.sig ∧
    s'.writeLog = s.writeLog ∧
    (oracleHasSeccomp s.oracle = false → s'.fds = (s.closeSlot syncR.val).fds) ∧
    (oracleHasSeccomp s.oracle = false → s'.isOpen syncR.val = false) ∧
    (∀ k : Int, k ≠ syncR.val → s'.getFd k = s.getFd k) ∧
    (∃ suf, s'.trace = s.trace ++ suf) ∧
    (gotOne = true ↔
      ∃ e writable broken b rest,
        s.getFd syncR.val = some e ∧
        s.getDesc e.desc = .stream true writable broken (b :: rest) ∧
        match firstNonEintrFault (s.oracle.drop s.trace.length) with
        | some (.fail _) | some (.seccomp _) => False
        | _ => True)
  else
    gotOne = false ∧ s' = s

private theorem read_sync_byte_loop_spec (s : ChildState) (syncR : I32) :
    OkPost (postfork.child.read_sync_byte_loop s syncR) fun res =>
      if s.status = Status.running then
        SameChildConfig res.1 s ∧
        res.1.pgid = s.pgid ∧
        res.1.cwd = s.cwd ∧
        res.1.sig = s.sig ∧
        res.1.writeLog = s.writeLog ∧
        res.1.fds = s.fds ∧
        (∃ suf, res.1.trace = s.trace ++ suf) ∧
        (res.2 = true ↔
          ∃ e writable broken b rest,
            s.getFd syncR.val = some e ∧
            s.getDesc e.desc = .stream true writable broken (b :: rest) ∧
            match firstNonEintrFault (s.oracle.drop s.trace.length) with
            | some (.fail _) | some (.seccomp _) => False
            | _ => True)
      else
        res = (s, false) := by
  by_cases hRun : s.status = Status.running
  · simp only [hRun, ↓reduceIte]
    let inv : ChildState → Prop := fun cur =>
      SameChildConfig cur s ∧
      cur.pgid = s.pgid ∧
      cur.cwd = s.cwd ∧
      cur.sig = s.sig ∧
      cur.writeLog = s.writeLog ∧
      cur.fds = s.fds ∧
      cur.descs = s.descs ∧
      (∃ suf, cur.trace = s.trace ++ suf) ∧
      firstNonEintrFault (cur.oracle.drop cur.trace.length) =
        firstNonEintrFault (s.oracle.drop s.trace.length)
    rw [postfork.child.read_sync_byte_loop]
    refine okPost_loop_decr_nat
      (fun cur => cur.oracle.length - cur.trace.length) inv _
      (postfork.child.read_sync_byte_loop.body syncR) s ?_
      ⟨SameChildConfig.refl s, rfl, rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, rfl⟩
    intro cur hInv
    rcases hInv with ⟨hCfg, hPgid, hCwd, hSig, hWlog, hFds, hDescs, ⟨suf, hTrace⟩, hFirst⟩
    have hCurRun : cur.status = Status.running := hCfg.status.trans hRun
    have hGetFdEq : cur.getFd syncR.val = s.getFd syncR.val := by
      simp [ChildState.getFd, hFds]
    have hGetDescEq : ∀ d, cur.getDesc d = s.getDesc d := by
      intro d
      simp [ChildState.getDesc, hDescs]
    unfold postfork.child.read_sync_byte_loop.body
    dsimp only
    by_cases hSec : ∃ rawE, currentFault cur = StepFault.seccomp rawE
    · rcases hSec with ⟨rawE, hcf⟩
      unfold sys.read1
      simp only [hCurRun, hcf, bind_ok, Aeneas.Std.uncurry]
      by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
      · simp only [hEintr, ↓reduceIte]
        have hNe : sanitizeErrno rawE ≠ EINTR := by
          intro heq
          rw [fd_ops_eintr_eq, heq] at hEintr
          simp at hEintr
        have hFail := firstNonEintrFault_seccomp_ne cur rawE hcf hNe
        rw [hFirst] at hFail
        refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
        dsimp only
        refine ⟨⟨hCfg.oracle, hCurRun.symm.trans hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
            hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
            hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
          hPgid, hCwd, hSig, hWlog, hFds,
          ⟨suf ++ [⟨.read1 syncR, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
        constructor
        · intro hF; cases hF
        · intro ⟨_, _, _, _, _, _, _, hNoFail⟩
          rw [hFail] at hNoFail
          simp at hNoFail
      · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
        have hEqEintr : sanitizeErrno rawE = EINTR := by
          rw [fd_ops_eintr_eq] at hEintr
          exact Classical.not_not.mp (fun hne => hEintr (bne_iff_ne.mpr hne))
        have hlt : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_seccomp hcf
        have hStepFirst := firstNonEintrFault_step_seccomp_eintr cur rawE hcf hEqEintr
        refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
        · refine ⟨⟨hCfg.oracle, hCurRun.symm.trans hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
              hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
              hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
            hPgid, hCwd, hSig, hWlog, hFds, hDescs,
            ⟨suf ++ [⟨.read1 syncR, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
            ?_⟩
          simpa [List.length_append] using hStepFirst.symm.trans hFirst
        · simp only [List.length_append, List.length_singleton]
          omega
    · have hNonSec : ∀ rawE, currentFault cur ≠ StepFault.seccomp rawE := fun rawE h => hSec ⟨rawE, h⟩
      have hReadEq : ∀ (buf1 : Aeneas.Std.Array U8 1#usize), sys.read1 cur syncR buf1 =
          match cur.getFd syncR.val with
          | none =>
            Result.ok ((core.result.Result.Err EBADF : core.result.Result Usize I32),
              { cur with trace := cur.trace ++ [⟨.read1 syncR, .err EBADF⟩] }, buf1)
          | some e =>
            match cur.getDesc e.desc with
            | .directory _ | .procSelfFd _ =>
              Result.ok ((core.result.Result.Err EISDIR : core.result.Result Usize I32),
                { cur with trace := cur.trace ++ [⟨.read1 syncR, .err EISDIR⟩] }, buf1)
            | .stream false _ _ _ =>
              Result.ok ((core.result.Result.Err EBADF : core.result.Result Usize I32),
                { cur with trace := cur.trace ++ [⟨.read1 syncR, .err EBADF⟩] }, buf1)
            | .stream true wr brk bs =>
              match currentFault cur with
              | .fail rawE =>
                let err := sanitizeErrno rawE
                Result.ok ((core.result.Result.Err err : core.result.Result Usize I32),
                  { cur with trace := cur.trace ++ [⟨.read1 syncR, .err err⟩] }, buf1)
              | _ =>
                match bs with
                | [] =>
                  Result.ok ((core.result.Result.Ok 0#usize : core.result.Result Usize I32),
                    { cur with trace := cur.trace ++ [⟨.read1 syncR, .okVal 0⟩] }, buf1)
                | b :: rest =>
                  let s' := cur.putDesc e.desc (.stream true wr brk rest)
                  Result.ok ((core.result.Result.Ok 1#usize : core.result.Result Usize I32),
                    { s' with trace := s'.trace ++ [⟨.read1 syncR, .okVal 1⟩] },
                    Aeneas.Std.Array.make 1#usize [b]) := by
        intro buf1
        unfold sys.read1
        cases hcf : currentFault cur with
        | seccomp rawE => exact absurd hcf (hNonSec rawE)
        | fail _ | normal | partialWrite _ | dentsBatch _ => simp only [hCurRun]; rfl
      rw [hReadEq]
      cases hFd : cur.getFd syncR.val with
    | none =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      have hNe : (EBADF != postfork.fd_ops.EINTR) = true := by
        rw [fd_ops_eintr_eq]
        exact bne_iff_ne.mpr ebadf_ne_eintr
      rw [hNe]
      simp only [↓reduceIte]
      refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
      dsimp only
      refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
          hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
          hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
        hPgid, hCwd, hSig, hWlog, hFds,
        ⟨suf ++ [⟨.read1 syncR, .err EBADF⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
      constructor
      · intro hF; cases hF
      · intro ⟨e, _, _, _, _, he, _⟩
        rw [← hGetFdEq, hFd] at he
        cases he
    | some e =>
      dsimp only
      simp only [hGetFdEq] at hFd
      cases hDesc : cur.getDesc e.desc with
      | directory _ =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        have hNe : (EISDIR != postfork.fd_ops.EINTR) = true := by
          rw [fd_ops_eintr_eq]
          exact bne_iff_ne.mpr eisdir_ne_eintr
        rw [hNe]
        simp only [↓reduceIte]
        refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
        dsimp only
        refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
            hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
            hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
          hPgid, hCwd, hSig, hWlog, hFds,
          ⟨suf ++ [⟨.read1 syncR, .err EISDIR⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
        constructor
        · intro hF; cases hF
        · intro ⟨e', _, _, _, _, he', hd', _⟩
          rw [hFd] at he'
          injection he' with heq
          subst heq
          rw [← hGetDescEq e.desc, hDesc] at hd'
          cases hd'
      | procSelfFd cursor =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        have hNe : (EISDIR != postfork.fd_ops.EINTR) = true := by
          rw [fd_ops_eintr_eq]
          exact bne_iff_ne.mpr eisdir_ne_eintr
        rw [hNe]
        simp only [↓reduceIte]
        refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
        dsimp only
        refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
            hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
            hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
          hPgid, hCwd, hSig, hWlog, hFds,
          ⟨suf ++ [⟨.read1 syncR, .err EISDIR⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
        constructor
        · intro hF; cases hF
        · intro ⟨e', _, _, _, _, he', hd', _⟩
          rw [hFd] at he'
          injection he' with heq
          subst heq
          rw [← hGetDescEq e.desc, hDesc] at hd'
          cases hd'
      | stream readable writable broken stream =>
        cases readable
        · simp only [bind_ok, Aeneas.Std.uncurry]
          have hNe : (EBADF != postfork.fd_ops.EINTR) = true := by
            rw [fd_ops_eintr_eq]
            exact bne_iff_ne.mpr ebadf_ne_eintr
          rw [hNe]
          simp only [↓reduceIte]
          refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
          dsimp only
          refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
              hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
              hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
            hPgid, hCwd, hSig, hWlog, hFds,
            ⟨suf ++ [⟨.read1 syncR, .err EBADF⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
          constructor
          · intro hF; cases hF
          · intro ⟨e', _, _, _, _, he', hd', _⟩
            rw [hFd] at he'
            injection he' with heq
            subst heq
            rw [← hGetDescEq e.desc, hDesc] at hd'
            cases hd'
        · cases hcf : currentFault cur with
          | seccomp rawE => exact absurd hcf (hNonSec rawE)
          | fail rawE =>
            simp only [bind_ok, Aeneas.Std.uncurry]
            by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
            · simp only [hEintr, ↓reduceIte]
              have hNe : sanitizeErrno rawE ≠ EINTR := by
                intro heq
                rw [fd_ops_eintr_eq, heq] at hEintr
                simp at hEintr
              have hFail := firstNonEintrFault_fail_ne cur rawE hcf hNe
              rw [hFirst] at hFail
              refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro hF; cases hF
              · intro ⟨_, _, _, _, _, _, _, hNoFail⟩
                rw [hFail] at hNoFail
                simp at hNoFail
            · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
              have hEqEintr : sanitizeErrno rawE = EINTR := by
                rw [fd_ops_eintr_eq] at hEintr
                exact Classical.not_not.mp (fun hne => hEintr (bne_iff_ne.mpr hne))
              have hlt : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_fail hcf
              have hStepFirst := firstNonEintrFault_step_eintr cur rawE hcf hEqEintr
              refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
              · refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                    hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                    hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                  hPgid, hCwd, hSig, hWlog, hFds, hDescs,
                  ⟨suf ++ [⟨.read1 syncR, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
                  ?_⟩
                simpa [List.length_append] using hStepFirst.symm.trans hFirst
              · simp only [List.length_append, List.length_singleton]
                omega
          | normal =>
            cases stream with
            | nil =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 0⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro hF; cases hF
              · intro ⟨e', _, _, _, _, he', hd', _⟩
                rw [hFd] at he'
                injection he' with heq
                subst heq
                rw [← hGetDescEq e.desc, hDesc] at hd'
                cases hd'
            | cons b rest =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              let s1 := cur.putDesc e.desc (DescState.stream true writable broken rest)
              let s2 : ChildState := { s1 with trace := s1.trace ++ [⟨.read1 syncR, .okVal 1⟩] }
              have hNonFail := firstNonEintrFault_nonfail cur (fun _ => ⟨(by rw [hcf]; intro h; cases h), (by rw [hcf]; intro h; cases h)⟩)
              rw [hFirst] at hNonFail
              refine ⟨ControlFlow.done (s2, true), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 1⟩], by simp [s2, s1, ChildState.putDesc, hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro _
                exact ⟨e, writable, broken, b, rest, hFd, hGetDescEq e.desc ▸ hDesc, hNonFail⟩
              · intro _; rfl
          | partialWrite _ =>
            cases stream with
            | nil =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 0⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro hF; cases hF
              · intro ⟨e', _, _, _, _, he', hd', _⟩
                rw [hFd] at he'
                injection he' with heq
                subst heq
                rw [← hGetDescEq e.desc, hDesc] at hd'
                cases hd'
            | cons b rest =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              let s1 := cur.putDesc e.desc (DescState.stream true writable broken rest)
              let s2 : ChildState := { s1 with trace := s1.trace ++ [⟨.read1 syncR, .okVal 1⟩] }
              have hNonFail := firstNonEintrFault_nonfail cur (fun _ => ⟨(by rw [hcf]; intro h; cases h), (by rw [hcf]; intro h; cases h)⟩)
              rw [hFirst] at hNonFail
              refine ⟨ControlFlow.done (s2, true), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 1⟩], by simp [s2, s1, ChildState.putDesc, hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro _
                exact ⟨e, writable, broken, b, rest, hFd, hGetDescEq e.desc ▸ hDesc, hNonFail⟩
              · intro _; rfl
          | dentsBatch _ =>
            cases stream with
            | nil =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              refine ⟨ControlFlow.done (_, false), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 0⟩], by simp [hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro hF; cases hF
              · intro ⟨e', _, _, _, _, he', hd', _⟩
                rw [hFd] at he'
                injection he' with heq
                subst heq
                rw [← hGetDescEq e.desc, hDesc] at hd'
                cases hd'
            | cons b rest =>
              simp only [bind_ok, Aeneas.Std.uncurry]
              let s1 := cur.putDesc e.desc (DescState.stream true writable broken rest)
              let s2 : ChildState := { s1 with trace := s1.trace ++ [⟨.read1 syncR, .okVal 1⟩] }
              have hNonFail := firstNonEintrFault_nonfail cur (fun _ => ⟨(by rw [hcf]; intro h; cases h), (by rw [hcf]; intro h; cases h)⟩)
              rw [hFirst] at hNonFail
              refine ⟨ControlFlow.done (s2, true), rfl, ?_⟩
              dsimp only
              refine ⟨⟨hCfg.oracle, hCfg.status, hCfg.fdLimit, hCfg.kernelMasksSetfd,
                  hCfg.closeRangeSupported, hCfg.closeRangeErrno, hCfg.procSelfFdAvailable,
                  hCfg.procOpenErrno, hCfg.pid, hCfg.sid, hCfg.chdirResolved⟩,
                hPgid, hCwd, hSig, hWlog, hFds,
                ⟨suf ++ [⟨.read1 syncR, .okVal 1⟩], by simp [s2, s1, ChildState.putDesc, hTrace, List.append_assoc]⟩, ?_⟩
              constructor
              · intro _
                exact ⟨e, writable, broken, b, rest, hFd, hGetDescEq e.desc ▸ hDesc, hNonFail⟩
              · intro _; rfl
  · simp only [hRun, ↓reduceIte]
    rw [postfork.child.read_sync_byte_loop]
    refine okPost_loop_decr_nat (fun _ => 0) (fun cur => cur = s) _
      (postfork.child.read_sync_byte_loop.body syncR) s ?_ rfl
    intro cur hEq
    subst hEq
    unfold postfork.child.read_sync_byte_loop.body
    unfold sys.read1
    cases hSt : cur.status with
    | running => exact absurd hSt hRun
    | exited _ =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      exact ⟨ControlFlow.done (cur, false), rfl, rfl⟩
    | signaled _ =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      exact ⟨ControlFlow.done (cur, false), rfl, rfl⟩
    | execd _ =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      exact ⟨ControlFlow.done (cur, false), rfl, rfl⟩

/-- Reusable `OkPost` specification for `postfork.child.read_sync_byte`. -/
theorem read_sync_byte_spec (s : ChildState) (syncR : I32) :
    OkPost (postfork.child.read_sync_byte s syncR) fun p => SyncBytePost s syncR p.1 p.2 := by
  unfold postfork.child.read_sync_byte
  by_cases hNeg : syncR < 0#i32
  · simp only [hNeg, ↓reduceIte]
    refine ⟨(false, s), rfl, ?_⟩
    simp [SyncBytePost, hNeg]
  · simp only [hNeg, ↓reduceIte]
    refine okPost_bind (read_sync_byte_loop_spec s syncR) ?_
    intro ⟨s1, gotOne⟩ hLoop
    by_cases hRun : s.status = Status.running
    · simp only [hRun, ↓reduceIte] at hLoop
      rcases hLoop with ⟨hCfg1, hPgid1, hCwd1, hSig1, hWlog1, hFds1, ⟨suf1, hTrace1⟩, hGot⟩
      have hRun1 : s1.status = Status.running := hCfg1.status.trans hRun
      obtain ⟨r, s2, hCloseEq, hCfg2, hPgid2, hCwd2, hSig2, _, hWlog2, hTraceLen2, hFds2, _⟩ :=
        sys_close_running s1 hRun1 syncR
      have hTrace2 : ∃ suf2, s2.trace = s.trace ++ suf2 := by
        unfold sys.close runUnitSyscall at hCloseEq
        simp only [hRun1] at hCloseEq
        by_cases hOpen : s1.isOpen syncR.val = true
        · simp only [hOpen, ↓reduceIte] at hCloseEq
          cases hcf : currentFault s1 with
          | seccomp _ | fail _ | normal | partialWrite _ | dentsBatch _ =>
            simp only [hcf, Aeneas.Std.Result.ok.injEq] at hCloseEq
            have hS2 := (congrArg Prod.snd hCloseEq).symm
            dsimp only at hS2
            rw [hS2]
            dsimp only [ChildState.closeSlot]
            rw [hTrace1, List.append_assoc]
            exact ⟨_, rfl⟩
        · simp only [hOpen, Bool.false_eq_true, ↓reduceIte] at hCloseEq
          cases hcf : currentFault s1 with
          | seccomp _ | fail _ | normal | partialWrite _ | dentsBatch _ =>
            simp only [hcf, Aeneas.Std.Result.ok.injEq] at hCloseEq
            have hS2 := (congrArg Prod.snd hCloseEq).symm
            dsimp only at hS2
            rw [hS2]
            dsimp only [ChildState.closeSlot]
            rw [hTrace1, List.append_assoc]
            exact ⟨_, rfl⟩
      dsimp only [Aeneas.Std.uncurry]
      rw [hCloseEq, bind_ok]
      refine ⟨(gotOne, s2), rfl, ?_⟩
      simp only [SyncBytePost, hNeg, ↓reduceIte, hRun]
      have hFdsEq : oracleHasSeccomp s.oracle = false → s2.fds = (s.closeSlot syncR.val).fds := by
        intro hNoSec
        have hNoSec1 : oracleHasSeccomp s1.oracle = false := hCfg1.oracle.symm ▸ hNoSec
        have hNonSec1 : ∀ rawE, currentFault s1 ≠ StepFault.seccomp rawE :=
          fun rawE hcf => not_seccomp_of_oracleHasSeccomp_false hNoSec1 hcf
        rw [hFds2]
        cases hcf : currentFault s1 with
        | seccomp rawE => exact absurd hcf (hNonSec1 rawE)
        | fail _ | normal | partialWrite _ | dentsBatch _ => simp [ChildState.closeSlot, hFds1]
      have hClosedSelf : oracleHasSeccomp s.oracle = false → s2.isOpen syncR.val = false := by
        intro hNoSec
        simp only [ChildState.isOpen, ChildState.getFd, hFdsEq hNoSec]
        rw [ChildState.closeSlot, find?_eraseFdEntries_self]
        rfl
      have hOther : ∀ k : Int, k ≠ syncR.val → s2.getFd k = s.getFd k := by
        intro k hne
        simp only [ChildState.getFd]
        rw [hFds2]
        cases hcf : currentFault s1 with
        | seccomp _ => dsimp only; rw [hFds1]
        | fail _ | normal | partialWrite _ | dentsBatch _ =>
          have hFind := find?_eraseFdEntries_ne s.fds hne
          simp only [ChildState.closeSlot, hFds1, hFind]
      exact ⟨hCfg2.trans hCfg1, hPgid2.trans hPgid1, hCwd2.trans hCwd1, hSig2.trans hSig1,
        hWlog2.trans hWlog1, hFdsEq, hClosedSelf, hOther, hTrace2, hGot⟩
    · simp only [hRun, ↓reduceIte] at hLoop
      have hs1 : s1 = s := congrArg Prod.fst hLoop
      have hGot : gotOne = false := congrArg Prod.snd hLoop
      rw [hs1, hGot]
      dsimp only [Aeneas.Std.uncurry]
      rw [sys_close_not_running s hRun syncR, bind_ok]
      refine ⟨(false, s), rfl, ?_⟩
      simp [SyncBytePost, hNeg, hRun]

end SyncByte

section WriteAll

private theorem slice_index_from_ok (buf : Slice U8) (off : Usize) (hle : off.val ≤ buf.length) :
    ∃ s1 : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) buf
        { start := off, «end» := buf.len } = Result.ok s1 ∧
      s1.val = buf.val.drop off.val := by
  change ∃ s1 : Slice U8,
    core.slice.index.SliceIndexRangeUsizeSlice.index { start := off, «end» := buf.len } buf =
      Result.ok s1 ∧ s1.val = buf.val.drop off.val
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  have hCond : off ≤ buf.len ∧ buf.len.val ≤ buf.length := by
    exact ⟨hle, Nat.le_refl _⟩
  simp only [hCond, and_self, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  rw [Slice.from_val]
  simp only [List.slice]
  have hTake : (buf.val.drop off.val).take (buf.len.val - off.val) = buf.val.drop off.val := by
    apply List.take_of_length_le
    rw [List.length_drop]
    change buf.val.length - off.val ≤ buf.length - off.val
    exact Nat.le_refl _
  exact hTake

private theorem usize_sub_ok (len off : Usize) (hle : off.val ≤ len.val) :
    ∃ d : Usize, len - off = Result.ok d ∧ d.val = len.val - off.val := by
  have hCond : off.val ≤ len.val := hle
  obtain ⟨d, hd, hdVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.sub_spec hCond)
  exact ⟨d, hd, by simpa using hdVal.1⟩

private theorem usize_add_ok (off n : Usize) (hle : off.val + n.val ≤ Usize.max) :
    ∃ off1 : Usize, off + n = Result.ok off1 ∧ off1.val = off.val + n.val := by
  obtain ⟨off1, ho, hoVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.add_spec hle)
  exact ⟨off1, ho, by simpa using hoVal⟩

private theorem mkUsize_val_le_slice (n : Nat) (buf : Slice U8) (hle : n ≤ buf.length) :
    (mkUsize n : Nat) = n :=
  mkUsize_val_le_scalar buf.len hle

private theorem writtenBytesForDesc_append_one (xs : List (Desc × Bytes)) (d0 d : Desc) (bs : Bytes) :
    writtenBytesForDesc (xs ++ [(d0, bs)]) d =
      if d0 == d then writtenBytesForDesc xs d ++ bs else writtenBytesForDesc xs d := by
  unfold writtenBytesForDesc
  rw [List.filterMap_append, List.flatten_append]
  by_cases hEq : d0 = d
  · simp [hEq]
  · simp [hEq, beq_false_of_ne hEq]

private theorem appendedBytesForDesc_append_one (base extra : List (Desc × Bytes))
    (d0 d : Desc) (bs : Bytes) :
    appendedBytesForDesc base (base ++ extra ++ [(d0, bs)]) d =
      if d0 == d then appendedBytesForDesc base (base ++ extra) d ++ bs
      else appendedBytesForDesc base (base ++ extra) d := by
  unfold appendedBytesForDesc
  rw [List.append_assoc, List.drop_left, List.drop_left]
  exact writtenBytesForDesc_append_one extra d0 d bs

private theorem list_take_add_drop {α : Type} (a b : Nat) (xs : List α) :
    xs.take a ++ (xs.drop a).take b = xs.take (a + b) := by
  induction xs generalizing a with
  | nil => simp
  | cons x rest ih =>
    cases a with
    | zero => simp
    | succ a' =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, Nat.succ_add]
      congr 1
      exact ih a'

private def noNonEintrFail (oracle : List StepFault) : Prop :=
  ∀ f ∈ oracle, match f with
    | .fail rawE | .seccomp rawE => sanitizeErrno rawE = EINTR
    | _ => True

private theorem noNonEintrFail_drop_step (s : ChildState) (hNo : noNonEintrFail (s.oracle.drop s.trace.length)) :
    noNonEintrFail (s.oracle.drop (s.trace.length + 1)) ∧
    (∀ rawE, currentFault s = StepFault.fail rawE → sanitizeErrno rawE = EINTR) ∧
    (∀ rawE, currentFault s = StepFault.seccomp rawE → sanitizeErrno rawE = EINTR) := by
  by_cases hlt : s.trace.length < s.oracle.length
  · have hdrop : s.oracle.drop s.trace.length =
        s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
      List.drop_eq_getElem_cons hlt
    have hget : currentFault s = s.oracle[s.trace.length] := by
      simp [currentFault, List.getElem?_eq_getElem hlt]
    rw [hdrop] at hNo
    refine ⟨fun f hf => hNo f (List.mem_cons_of_mem _ hf), ?_, ?_⟩
    · intro rawE hcf
      have heq : s.oracle[s.trace.length] = StepFault.fail rawE := hget.symm.trans hcf
      have hm := hNo (s.oracle[s.trace.length]) List.mem_cons_self
      rw [heq] at hm
      exact hm
    · intro rawE hcf
      have heq : s.oracle[s.trace.length] = StepFault.seccomp rawE := hget.symm.trans hcf
      have hm := hNo (s.oracle[s.trace.length]) List.mem_cons_self
      rw [heq] at hm
      exact hm
  · have hge : s.oracle.length ≤ s.trace.length := Nat.le_of_not_lt hlt
    have hnorm := currentFault_ge_oracle s hge
    refine ⟨?_, ?_, ?_⟩
    · rw [List.drop_of_length_le (Nat.le_trans hge (Nat.le_succ _))]
      intro f hf; cases hf
    · intro rawE hcf; rw [hnorm] at hcf; cases hcf
    · intro rawE hcf; rw [hnorm] at hcf; cases hcf

private theorem noSeccomp_drop_step (s : ChildState)
    (hNo : oracleHasSeccomp (s.oracle.drop s.trace.length) = false) :
    oracleHasSeccomp (s.oracle.drop (s.trace.length + 1)) = false ∧
    (∀ rawE, currentFault s ≠ StepFault.seccomp rawE) := by
  by_cases hlt : s.trace.length < s.oracle.length
  · have hdrop : s.oracle.drop s.trace.length =
        s.oracle[s.trace.length] :: s.oracle.drop (s.trace.length + 1) :=
      List.drop_eq_getElem_cons hlt
    have hget : currentFault s = s.oracle[s.trace.length] := by
      simp [currentFault, List.getElem?_eq_getElem hlt]
    have hAny : (s.oracle.drop s.trace.length).any isSeccompFault = false := hNo
    rw [hdrop, List.any_cons, Bool.or_eq_false_iff] at hAny
    refine ⟨hAny.2, fun rawE hcf => ?_⟩
    have heq : s.oracle[s.trace.length] = StepFault.seccomp rawE := hget.symm.trans hcf
    have hF := hAny.1
    rw [heq] at hF
    simp [isSeccompFault] at hF
  · have hge : s.oracle.length ≤ s.trace.length := Nat.le_of_not_lt hlt
    have hnorm := currentFault_ge_oracle s hge
    refine ⟨?_, fun rawE hcf => by rw [hnorm] at hcf; cases hcf⟩
    rw [oracleHasSeccomp, List.drop_of_length_le (Nat.le_trans hge (Nat.le_succ _))]
    rfl

/-- Postcondition for `postfork.child.write_all`. -/
def WriteAllPost (s : ChildState) (fd : I32) (buf : Slice U8)
    (res : core.result.Result Unit I32) (s' : ChildState) : Prop :=
  if fd < 0#i32 then
    res = .Err EBADF ∧ s' = s
  else if s.status ≠ Status.running then
    res = (if buf.val.isEmpty then .Ok () else .Err EIO) ∧ s' = s
  else
    s'.fds = s.fds ∧
    s'.descs = s.descs ∧
    s'.cwd = s.cwd ∧
    s'.pgid = s.pgid ∧
    s'.sig = s.sig ∧
    s'.oracle = s.oracle ∧
    s'.fdLimit = s.fdLimit ∧
    s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
    s'.closeRangeSupported = s.closeRangeSupported ∧
    s'.closeRangeErrno = s.closeRangeErrno ∧
    s'.procSelfFdAvailable = s.procSelfFdAvailable ∧
    s'.procOpenErrno = s.procOpenErrno ∧
    s'.pid = s.pid ∧
    s'.sid = s.sid ∧
    (∃ suf, s'.trace = s.trace ++ suf) ∧
    match s.getFd fd.val with
    | none =>
      (oracleHasSeccomp (s.oracle.drop s.trace.length) = false → res = .Err EBADF) ∧
      s'.status = Status.running ∧ s'.writeLog = s.writeLog
    | some e =>
      match s.getDesc e.desc with
      | .stream _ true true _ =>
        s'.writeLog = s.writeLog ∧
        (if buf.val.isEmpty then
          s'.status = Status.running ∧ (res = .Ok () ∨ ∃ err, res = .Err err ∧ err ≠ EINTR)
        else
          (oracleHasSeccomp (s.oracle.drop s.trace.length) = false →
            res = .Err EPIPE ∧
            s'.status = (if s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13 then .signaled 13#i32 else .running)) ∧
          (s'.status = Status.running ∨ ((s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13) = true ∧ s'.status = .signaled 13#i32)))
      | .stream _ true false _ =>
        s'.status = Status.running ∧
        (∀ d : Desc, d ≠ e.desc → appendedBytesForDesc s.writeLog s'.writeLog d = []) ∧
        ((res = .Ok () ∧ appendedBytesForDesc s.writeLog s'.writeLog e.desc = buf.val) ∨
         (∃ err k, res = .Err err ∧ err ≠ EINTR ∧ k ≤ buf.val.length ∧
           appendedBytesForDesc s.writeLog s'.writeLog e.desc = buf.val.take k)) ∧
        ((∀ f ∈ s.oracle.drop s.trace.length,
            match f with | .fail rawE | .seccomp rawE => sanitizeErrno rawE = EINTR | _ => True) →
          res = .Ok ())
      | _ =>
        (oracleHasSeccomp (s.oracle.drop s.trace.length) = false → res = .Err EBADF) ∧
        s'.status = Status.running ∧ s'.writeLog = s.writeLog

private theorem write_all_loop0_seccomp_or_err (s : ChildState) (fd : I32) (buf : Slice U8)
    (err : I32) (hNe : err ≠ EINTR) (hRun : s.status = Status.running)
    (hWriteNonSec : ∀ cur : ChildState, cur.status = Status.running →
      cur.fds = s.fds → cur.descs = s.descs →
      (∀ rawE, currentFault cur ≠ StepFault.seccomp rawE) →
      sys.write cur fd buf = Result.ok (.Err err,
        { cur with trace := cur.trace ++ [⟨.write fd buf.val, .err err⟩] })) :
    OkPost (postfork.child.write_all_loop0 buf s fd) fun out =>
      let s' := out.1
      out.2.2 = true ∧
      s'.status = Status.running ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.cwd = s.cwd ∧
      s'.pgid = s.pgid ∧ s'.sig = s.sig ∧ s'.oracle = s.oracle ∧
      s'.fdLimit = s.fdLimit ∧ s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
      s'.closeRangeSupported = s.closeRangeSupported ∧ s'.closeRangeErrno = s.closeRangeErrno ∧
      s'.procSelfFdAvailable = s.procSelfFdAvailable ∧ s'.procOpenErrno = s.procOpenErrno ∧
      s'.pid = s.pid ∧ s'.sid = s.sid ∧ s'.writeLog = s.writeLog ∧
      (∃ suf, s'.trace = s.trace ++ suf) ∧
      (oracleHasSeccomp (s.oracle.drop s.trace.length) = false → out.2.1 = err) := by
  let measure : sys.Sys → Nat := fun cur => cur.oracle.length - cur.trace.length
  let inv : sys.Sys → Prop := fun cur =>
    cur.status = Status.running ∧
    cur.fds = s.fds ∧ cur.descs = s.descs ∧ cur.cwd = s.cwd ∧
    cur.pgid = s.pgid ∧ cur.sig = s.sig ∧ cur.oracle = s.oracle ∧
    cur.fdLimit = s.fdLimit ∧ cur.kernelMasksSetfd = s.kernelMasksSetfd ∧
    cur.closeRangeSupported = s.closeRangeSupported ∧ cur.closeRangeErrno = s.closeRangeErrno ∧
    cur.procSelfFdAvailable = s.procSelfFdAvailable ∧ cur.procOpenErrno = s.procOpenErrno ∧
    cur.pid = s.pid ∧ cur.sid = s.sid ∧ cur.writeLog = s.writeLog ∧
    (∃ suf, cur.trace = s.trace ++ suf) ∧
    (oracleHasSeccomp (s.oracle.drop s.trace.length) = false →
      oracleHasSeccomp (cur.oracle.drop cur.trace.length) = false)
  rw [postfork.child.write_all_loop0]
  refine okPost_loop_decr_nat measure inv _
    (fun p => postfork.child.write_all_loop0.body buf fd p) s ?_
    ⟨hRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun h => h⟩
  intro cur hInv
  rcases hInv with ⟨hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr,
    hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid, hWlog, ⟨suf, hTrace⟩, hNoSec⟩
  unfold postfork.child.write_all_loop0.body
  by_cases hSec : ∃ rawE, currentFault cur = StepFault.seccomp rawE
  · rcases hSec with ⟨rawE, hcf⟩
    have hW : sys.write cur fd buf = Result.ok (.Err (sanitizeErrno rawE),
        { cur with trace := cur.trace ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩] }) := by
      unfold sys.write
      by_cases hEmpty : (↑buf : List U8).isEmpty = true <;>
        simp [hCurRun, hcf]
    rw [hW]
    simp only [bind_ok, Aeneas.Std.uncurry]
    by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
    · simp only [hEintr, ↓reduceIte]
      refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
      exact ⟨rfl, hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
        hProcAv, hProcErr, hPid, hSid, hWlog,
        ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
        fun h0 => absurd hcf ((noSeccomp_drop_step cur (hNoSec h0)).2 rawE)⟩
    · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
      have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_seccomp hcf
      have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
      refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
      · exact ⟨hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
          hProcAv, hProcErr, hPid, hSid, hWlog,
          ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
          fun h0 => by
            have hStep := (noSeccomp_drop_step cur (hNoSec h0)).1
            simpa [List.length_append] using hStep⟩
      · simp only [measure, List.length_append, List.length_singleton, hOr]; omega
  · have hNonSec : ∀ rawE, currentFault cur ≠ StepFault.seccomp rawE := fun rawE h => hSec ⟨rawE, h⟩
    rw [hWriteNonSec cur hCurRun hFds hDescs hNonSec]
    simp only [bind_ok, Aeneas.Std.uncurry]
    have hNeBool : (err != postfork.fd_ops.EINTR) = true := by
      rw [fd_ops_eintr_eq]; exact bne_iff_ne.mpr hNe
    simp only [hNeBool, ↓reduceIte]
    refine ⟨ControlFlow.done (_, err, true), rfl, ?_⟩
    exact ⟨rfl, hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
      hProcAv, hProcErr, hPid, hSid, hWlog,
      ⟨suf ++ [⟨.write fd buf.val, .err err⟩], by simp [hTrace, List.append_assoc]⟩, fun _ => rfl⟩

private theorem write_all_loop0_one_step_err (s : ChildState) (fd : I32) (buf : Slice U8)
    (err : I32) (s1 : ChildState)
    (hWrite : sys.write s fd buf = Result.ok (.Err err, s1))
    (hNe : err ≠ EINTR) :
    OkPost (postfork.child.write_all_loop0 buf s fd) fun out =>
      out = (s1, err, true) := by
  rw [postfork.child.write_all_loop0]
  refine okPost_loop_decr_nat (fun _ => 0) (fun p => p = s) _
    (fun p => postfork.child.write_all_loop0.body buf fd p) s ?_ rfl
  intro p hp
  subst hp
  unfold postfork.child.write_all_loop0.body
  rw [hWrite]
  simp only [bind_ok, Aeneas.Std.uncurry]
  have hNeBool : (err != postfork.fd_ops.EINTR) = true := by
    rw [fd_ops_eintr_eq]
    exact bne_iff_ne.mpr hNe
  simp only [hNeBool, ↓reduceIte]
  exact ⟨ControlFlow.done (s1, err, true), rfl, rfl⟩

private theorem write_all_loop0_stream (s : ChildState) (fd : I32) (buf : Slice U8)
    (hEmpty : buf.val.isEmpty = true)
    (hRun : s.status = Status.running)
    (e : FdEntry) (hFd : s.getFd fd.val = some e)
    (rd brk : Bool) (rbs : Bytes) (hDesc : s.getDesc e.desc = .stream rd true brk rbs) :
    OkPost (postfork.child.write_all_loop0 buf s fd) fun out =>
      let s' := out.1
      let err := out.2.1
      let failed := out.2.2
      s'.status = Status.running ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.cwd = s.cwd ∧
      s'.pgid = s.pgid ∧ s'.sig = s.sig ∧ s'.oracle = s.oracle ∧
      s'.fdLimit = s.fdLimit ∧ s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
      s'.closeRangeSupported = s.closeRangeSupported ∧ s'.closeRangeErrno = s.closeRangeErrno ∧
      s'.procSelfFdAvailable = s.procSelfFdAvailable ∧ s'.procOpenErrno = s.procOpenErrno ∧
      s'.pid = s.pid ∧ s'.sid = s.sid ∧ s'.writeLog = s.writeLog ∧
      (∃ suf, s'.trace = s.trace ++ suf) ∧
      ((failed = false) ∨ (failed = true ∧ err ≠ EINTR)) ∧
      (noNonEintrFail (s.oracle.drop s.trace.length) → failed = false) := by
  let measure : sys.Sys → Nat := fun cur => cur.oracle.length - cur.trace.length
  let inv : sys.Sys → Prop := fun cur =>
    cur.status = Status.running ∧
    cur.fds = s.fds ∧ cur.descs = s.descs ∧ cur.cwd = s.cwd ∧
    cur.pgid = s.pgid ∧ cur.sig = s.sig ∧ cur.oracle = s.oracle ∧
    cur.fdLimit = s.fdLimit ∧ cur.kernelMasksSetfd = s.kernelMasksSetfd ∧
    cur.closeRangeSupported = s.closeRangeSupported ∧ cur.closeRangeErrno = s.closeRangeErrno ∧
    cur.procSelfFdAvailable = s.procSelfFdAvailable ∧ cur.procOpenErrno = s.procOpenErrno ∧
    cur.pid = s.pid ∧ cur.sid = s.sid ∧ cur.writeLog = s.writeLog ∧
    (∃ suf, cur.trace = s.trace ++ suf) ∧
    (noNonEintrFail (s.oracle.drop s.trace.length) → noNonEintrFail (cur.oracle.drop cur.trace.length))
  rw [postfork.child.write_all_loop0]
  refine okPost_loop_decr_nat measure inv _
    (fun p => postfork.child.write_all_loop0.body buf fd p) s ?_ ?_
  · intro cur hInv
    rcases hInv with ⟨hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr,
      hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid, hWlog, ⟨suf, hTrace⟩, hNoFail⟩
    dsimp only at *
    unfold postfork.child.write_all_loop0.body
    have hCurFd : cur.getFd fd.val = some e := by
      rw [ChildState.getFd, hFds]; exact hFd
    have hCurDesc : cur.getDesc e.desc = .stream rd true brk rbs := by
      rw [ChildState.getDesc, hDescs]; exact hDesc
    unfold sys.write
    simp only [hCurRun, hCurFd, hCurDesc, hEmpty, ↓reduceIte]
    cases hcf : currentFault cur with
    | seccomp rawE =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
      · simp only [hEintr, ↓reduceIte]
        have hNe : sanitizeErrno rawE ≠ EINTR := by
          intro heq
          rw [fd_ops_eintr_eq, heq] at hEintr
          simp at hEintr
        refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
        exact ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
          hProcAv, hProcErr, hPid, hSid, hWlog,
          ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
          Or.inr ⟨rfl, hNe⟩, fun hNo0 => by
            have hIsEintr := (noNonEintrFail_drop_step cur (hNoFail hNo0)).2.2 rawE hcf
            exact absurd hIsEintr hNe⟩
      · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
        have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_seccomp hcf
        have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
        refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
        · exact ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
            hProcAv, hProcErr, hPid, hSid, hWlog,
            ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
            fun hNo0 => by
              have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
              simpa [List.length_append] using hStep⟩
        · simp only [measure, List.length_append, List.length_singleton, hOr]
          omega
    | fail rawE =>
      simp only [bind_ok, Aeneas.Std.uncurry]
      by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
      · simp only [hEintr, ↓reduceIte]
        have hNe : sanitizeErrno rawE ≠ EINTR := by
          intro heq
          rw [fd_ops_eintr_eq, heq] at hEintr
          simp at hEintr
        refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
        exact ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
          hProcAv, hProcErr, hPid, hSid, hWlog,
          ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
          Or.inr ⟨rfl, hNe⟩, fun hNo0 => by
            have hIsEintr := (noNonEintrFail_drop_step cur (hNoFail hNo0)).2.1 rawE hcf
            exact absurd hIsEintr hNe⟩
      · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
        have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_fail hcf
        have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
        refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
        · exact ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
            hProcAv, hProcErr, hPid, hSid, hWlog,
            ⟨suf ++ [⟨.write fd buf.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
            fun hNo0 => by
              have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
              simpa [List.length_append] using hStep⟩
        · simp only [measure, List.length_append, List.length_singleton, hOr]
          omega
    | normal | partialWrite _ | dentsBatch _ =>
      all_goals
        simp only [bind_ok, Aeneas.Std.uncurry]
        refine ⟨ControlFlow.done (_, 0#i32, false), rfl, ?_⟩
        exact ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
          hProcAv, hProcErr, hPid, hSid, hWlog,
          ⟨suf ++ [⟨.write fd buf.val, .okVal 0⟩], by simp [hTrace, List.append_assoc]⟩,
          Or.inl rfl, fun _ => rfl⟩
  · exact ⟨hRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨[], by simp⟩, fun h => h⟩

private theorem write_all_loop_stream_ok (s : ChildState) (fd : I32) (buf : Slice U8)
    (_hNonempty : buf.val.isEmpty = false)
    (hRun : s.status = Status.running)
    (e : FdEntry) (hFd : s.getFd fd.val = some e)
    (rd : Bool) (rbs : Bytes) (hDesc : s.getDesc e.desc = .stream rd true false rbs) :
    OkPost (postfork.child.write_all_loop1 s fd buf buf.len 0#usize) fun out =>
      let s' := out.1
      let err := out.2.1
      let failed := out.2.2
      s'.status = Status.running ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.cwd = s.cwd ∧
      s'.pgid = s.pgid ∧ s'.sig = s.sig ∧ s'.oracle = s.oracle ∧
      s'.fdLimit = s.fdLimit ∧ s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
      s'.closeRangeSupported = s.closeRangeSupported ∧ s'.closeRangeErrno = s.closeRangeErrno ∧
      s'.procSelfFdAvailable = s.procSelfFdAvailable ∧ s'.procOpenErrno = s.procOpenErrno ∧
      s'.pid = s.pid ∧ s'.sid = s.sid ∧
      (∃ suf, s'.trace = s.trace ++ suf) ∧
      (∀ d : Desc, d ≠ e.desc → appendedBytesForDesc s.writeLog s'.writeLog d = []) ∧
      ((failed = false ∧ appendedBytesForDesc s.writeLog s'.writeLog e.desc = buf.val) ∨
       (failed = true ∧ err ≠ EINTR ∧ ∃ k, k ≤ buf.val.length ∧
         appendedBytesForDesc s.writeLog s'.writeLog e.desc = buf.val.take k)) ∧
      (noNonEintrFail (s.oracle.drop s.trace.length) → failed = false) := by
  let len := buf.len
  let measure : sys.Sys × Usize → Nat :=
    fun p => (len.val - p.2.val) + (p.1.oracle.length - p.1.trace.length)
  let inv : sys.Sys × Usize → Prop := fun p =>
    let cur := p.1
    let off := p.2
    off.val ≤ len.val ∧
    cur.status = Status.running ∧
    cur.fds = s.fds ∧ cur.descs = s.descs ∧ cur.cwd = s.cwd ∧
    cur.pgid = s.pgid ∧ cur.sig = s.sig ∧ cur.oracle = s.oracle ∧
    cur.fdLimit = s.fdLimit ∧ cur.kernelMasksSetfd = s.kernelMasksSetfd ∧
    cur.closeRangeSupported = s.closeRangeSupported ∧ cur.closeRangeErrno = s.closeRangeErrno ∧
    cur.procSelfFdAvailable = s.procSelfFdAvailable ∧ cur.procOpenErrno = s.procOpenErrno ∧
    cur.pid = s.pid ∧ cur.sid = s.sid ∧
    (∃ suf, cur.trace = s.trace ++ suf) ∧
    (∃ extra, cur.writeLog = s.writeLog ++ extra ∧
      (∀ d : Desc, d ≠ e.desc → appendedBytesForDesc s.writeLog cur.writeLog d = []) ∧
      appendedBytesForDesc s.writeLog cur.writeLog e.desc = buf.val.take off.val) ∧
    (noNonEintrFail (s.oracle.drop s.trace.length) → noNonEintrFail (cur.oracle.drop cur.trace.length))
  rw [postfork.child.write_all_loop1]
  refine okPost_loop_decr_nat measure inv _
    (fun p => postfork.child.write_all_loop1.body fd buf len p.1 p.2) (s, 0#usize) ?_ ?_
  · intro ⟨cur, off⟩ hInv
    rcases hInv with ⟨hOffLe, hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hOr,
      hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid, ⟨suf, hTrace⟩,
      ⟨extra, hWlog, hOther, hApp⟩, hNoFail⟩
    dsimp only at *
    unfold postfork.child.write_all_loop1.body
    by_cases hLt : off < len
    · have hOffLt : off.val < len.val := hLt
      have hLenEq : len.val = buf.length := rfl
      have hBufLen : buf.val.length = buf.length := rfl
      have hOffLt' : off.val < buf.val.length := by rw [hBufLen, ← hLenEq]; exact hOffLt
      simp only [hLt, ↓reduceIte]
      obtain ⟨sl, hSlEq, hSlVal⟩ := slice_index_from_ok buf off (by omega)
      rw [hSlEq, bind_ok]
      have hCurFd : cur.getFd fd.val = some e := by
        rw [ChildState.getFd, hFds]
        exact hFd
      have hCurDesc : cur.getDesc e.desc = .stream rd true false rbs := by
        rw [ChildState.getDesc, hDescs]
        exact hDesc
      have hSlNonempty : sl.val.isEmpty = false := by
        cases hs : sl.val with
        | nil =>
          have hLen0 : sl.val.length = 0 := by simp [hs]
          rw [hSlVal, List.length_drop] at hLen0
          omega
        | cons _ _ => rfl
      unfold sys.write
      simp only [hCurRun, hCurFd, hCurDesc, hSlNonempty, Bool.false_eq_true, ↓reduceIte]
      cases hcf : currentFault cur with
      | seccomp rawE =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
        · simp only [hEintr, ↓reduceIte]
          have hNe : sanitizeErrno rawE ≠ EINTR := by
            intro heq
            rw [fd_ops_eintr_eq, heq] at hEintr
            simp at hEintr
          refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
          dsimp only
          refine ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
            hProcAv, hProcErr, hPid, hSid,
            ⟨suf ++ [⟨.write fd sl.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
            hOther, Or.inr ⟨rfl, hNe, off.val, by omega, hApp⟩, fun hNo0 => by
              have hNoCur := hNoFail hNo0
              have hIsEintr := (noNonEintrFail_drop_step cur hNoCur).2.2 rawE hcf
              exact absurd hIsEintr hNe⟩
        · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
          have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_seccomp hcf
          have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
          refine ⟨ControlFlow.cont (_, off), rfl, ?_, ?_⟩
          · exact ⟨hOffLe, rfl, hFds, hDescs, hCwd, hPgid, hSig,
              hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
              ⟨suf ++ [⟨.write fd sl.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
              ⟨extra, hWlog, hOther, hApp⟩, fun hNo0 => by
                have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
                simpa [List.length_append] using hStep⟩
          · simp only [measure, List.length_append, List.length_singleton, hOr]
            omega
      | fail rawE =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
        · simp only [hEintr, ↓reduceIte]
          have hNe : sanitizeErrno rawE ≠ EINTR := by
            intro heq
            rw [fd_ops_eintr_eq, heq] at hEintr
            simp at hEintr
          refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
          dsimp only
          refine ⟨rfl, hFds, hDescs, hCwd, hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr,
            hProcAv, hProcErr, hPid, hSid,
            ⟨suf ++ [⟨.write fd sl.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
            hOther, Or.inr ⟨rfl, hNe, off.val, by omega, hApp⟩, fun hNo0 => by
              have hNoCur := hNoFail hNo0
              have hIsEintr := (noNonEintrFail_drop_step cur hNoCur).2.1 rawE hcf
              exact absurd hIsEintr hNe⟩
        · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
          have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_fail hcf
          have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
          refine ⟨ControlFlow.cont (_, off), rfl, ?_, ?_⟩
          · exact ⟨hOffLe, rfl, hFds, hDescs, hCwd, hPgid, hSig,
              hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
              ⟨suf ++ [⟨.write fd sl.val, .err (sanitizeErrno rawE)⟩], by simp [hTrace, List.append_assoc]⟩,
              ⟨extra, hWlog, hOther, hApp⟩, fun hNo0 => by
                have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
                simpa [List.length_append] using hStep⟩
          · simp only [measure, List.length_append, List.length_singleton, hOr]
            omega
      | partialWrite maxMinusOne =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        let nNat := Nat.min sl.val.length (maxMinusOne + 1)
        have hSlLen : sl.val.length = buf.val.length - off.val := by
          rw [hSlVal, List.length_drop]
        have hSlPos : 1 ≤ sl.val.length := by omega
        have hNPos : 1 ≤ nNat := Nat.lt_min.mpr ⟨hSlPos, Nat.succ_pos _⟩
        have hNLeSl : nNat ≤ sl.val.length := Nat.min_le_left _ _
        have hNVal : (mkUsize nNat).val = nNat := mkUsize_val_le_slice nNat buf (by omega)
        rw [show (mkUsize nNat).val = (nNat - 1) + 1 by omega]
        obtain ⟨rem, hRemEq, hRemVal⟩ := usize_sub_ok len off (by omega)
        rw [hRemEq, bind_ok]
        have hLeRem : mkUsize nNat ≤ rem := by
          change (mkUsize nNat).val ≤ rem.val
          rw [hNVal, hRemVal]
          omega
        rw [ite_eq_left_iff.mpr (fun h => absurd hLeRem h)]
        have hAddBound : off.val + (mkUsize nNat).val ≤ Usize.max := by
          rw [hNVal]
          have hLenMax : len.val ≤ Usize.max := by scalar_tac
          omega
        obtain ⟨off1, hOff1Eq, hOff1Val⟩ := usize_add_ok off (mkUsize nNat) hAddBound
        rw [hOff1Eq, bind_ok]
        have hOff1Val' : off1.val = off.val + nNat := by rw [hOff1Val, hNVal]
        have hOff1Le : off1.val ≤ len.val := by omega
        refine ⟨ControlFlow.cont (_, off1), rfl, ?_, ?_⟩
        · refine ⟨hOff1Le, rfl, hFds, hDescs, hCwd, hPgid, hSig,
            hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
            ⟨suf ++ [⟨.write fd sl.val, .okVal (Int.ofNat nNat)⟩], by simp [nNat, hTrace, List.append_assoc]⟩,
            ⟨extra ++ [(e.desc, sl.val.take nNat)], by simp [nNat, hWlog, List.append_assoc], ?_, ?_⟩, ?_⟩
          · intro d hd
            rw [hWlog, appendedBytesForDesc_append_one]
            have hBeq : (e.desc == d) = false := beq_false_of_ne hd.symm
            rw [hBeq, ← hWlog]
            exact hOther d hd
          · rw [hWlog, appendedBytesForDesc_append_one]
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [← hWlog, hApp, hSlVal, list_take_add_drop, hOff1Val']
            dsimp only [nNat]
            rw [hSlVal]
          · intro hNo0
            have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
            simpa [List.length_append] using hStep
        · simp only [measure, List.length_append, List.length_singleton, hOr]
          omega
      | normal =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        let nNat := sl.val.length
        have hSlLen : sl.val.length = buf.val.length - off.val := by
          rw [hSlVal, List.length_drop]
        have hNVal : (mkUsize nNat).val = nNat := mkUsize_val_le_slice nNat buf (by omega)
        have hNPos : 1 ≤ nNat := by omega
        rw [show (mkUsize nNat).val = (nNat - 1) + 1 by omega]
        obtain ⟨rem, hRemEq, hRemVal⟩ := usize_sub_ok len off (by omega)
        rw [hRemEq, bind_ok]
        have hLeRem : mkUsize nNat ≤ rem := by
          change (mkUsize nNat).val ≤ rem.val
          rw [hNVal, hRemVal]
          omega
        rw [ite_eq_left_iff.mpr (fun h => absurd hLeRem h)]
        have hAddBound : off.val + (mkUsize nNat).val ≤ Usize.max := by
          rw [hNVal]
          have hLenMax : len.val ≤ Usize.max := by scalar_tac
          omega
        obtain ⟨off1, hOff1Eq, hOff1Val⟩ := usize_add_ok off (mkUsize nNat) hAddBound
        rw [hOff1Eq, bind_ok]
        have hOff1Val' : off1.val = len.val := by rw [hOff1Val, hNVal]; omega
        have hOff1Le : off1.val ≤ len.val := by omega
        refine ⟨ControlFlow.cont (_, off1), rfl, ?_, ?_⟩
        · refine ⟨hOff1Le, rfl, hFds, hDescs, hCwd, hPgid, hSig,
            hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
            ⟨suf ++ [⟨.write fd sl.val, .okVal (Int.ofNat nNat)⟩], by simp [nNat, hTrace, List.append_assoc]⟩,
            ⟨extra ++ [(e.desc, sl.val)], by simp [hWlog, List.append_assoc], ?_, ?_⟩, ?_⟩
          · intro d hd
            rw [hWlog, appendedBytesForDesc_append_one]
            have hBeq : (e.desc == d) = false := beq_false_of_ne hd.symm
            rw [hBeq, ← hWlog]
            exact hOther d hd
          · rw [hWlog, appendedBytesForDesc_append_one]
            simp only [beq_self_eq_true, ↓reduceIte]
            have hSlTake : sl.val = (buf.val.drop off.val).take nNat := by
              rw [← hSlVal, List.take_length]
            rw [← hWlog, hApp, hSlTake, list_take_add_drop, show off.val + nNat = off1.val by omega]
          · intro hNo0
            have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
            simpa [List.length_append] using hStep
        · simp only [measure, List.length_append, List.length_singleton, hOr]
          omega
      | dentsBatch _ =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        let nNat := sl.val.length
        have hSlLen : sl.val.length = buf.val.length - off.val := by
          rw [hSlVal, List.length_drop]
        have hNVal : (mkUsize nNat).val = nNat := mkUsize_val_le_slice nNat buf (by omega)
        have hNPos : 1 ≤ nNat := by omega
        rw [show (mkUsize nNat).val = (nNat - 1) + 1 by omega]
        obtain ⟨rem, hRemEq, hRemVal⟩ := usize_sub_ok len off (by omega)
        rw [hRemEq, bind_ok]
        have hLeRem : mkUsize nNat ≤ rem := by
          change (mkUsize nNat).val ≤ rem.val
          rw [hNVal, hRemVal]
          omega
        rw [ite_eq_left_iff.mpr (fun h => absurd hLeRem h)]
        have hAddBound : off.val + (mkUsize nNat).val ≤ Usize.max := by
          rw [hNVal]
          have hLenMax : len.val ≤ Usize.max := by scalar_tac
          omega
        obtain ⟨off1, hOff1Eq, hOff1Val⟩ := usize_add_ok off (mkUsize nNat) hAddBound
        rw [hOff1Eq, bind_ok]
        have hOff1Val' : off1.val = len.val := by rw [hOff1Val, hNVal]; omega
        have hOff1Le : off1.val ≤ len.val := by omega
        refine ⟨ControlFlow.cont (_, off1), rfl, ?_, ?_⟩
        · refine ⟨hOff1Le, rfl, hFds, hDescs, hCwd, hPgid, hSig,
            hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
            ⟨suf ++ [⟨.write fd sl.val, .okVal (Int.ofNat nNat)⟩], by simp [nNat, hTrace, List.append_assoc]⟩,
            ⟨extra ++ [(e.desc, sl.val)], by simp [hWlog, List.append_assoc], ?_, ?_⟩, ?_⟩
          · intro d hd
            rw [hWlog, appendedBytesForDesc_append_one]
            have hBeq : (e.desc == d) = false := beq_false_of_ne hd.symm
            rw [hBeq, ← hWlog]
            exact hOther d hd
          · rw [hWlog, appendedBytesForDesc_append_one]
            simp only [beq_self_eq_true, ↓reduceIte]
            have hSlTake : sl.val = (buf.val.drop off.val).take nNat := by
              rw [← hSlVal, List.take_length]
            rw [← hWlog, hApp, hSlTake, list_take_add_drop, show off.val + nNat = off1.val by omega]
          · intro hNo0
            have hStep := (noNonEintrFail_drop_step cur (hNoFail hNo0)).1
            simpa [List.length_append] using hStep
        · simp only [measure, List.length_append, List.length_singleton, hOr]
          omega
    · simp only [hLt, ↓reduceIte]
      have hOffEq : off.val = buf.val.length := by
        have hNotLt : ¬ off.val < len.val := hLt
        have hLenEq : len.val = buf.val.length := rfl
        omega
      rw [hOffEq, List.take_length] at hApp
      exact ⟨ControlFlow.done (cur, 0#i32, false), rfl, hCurRun, hFds, hDescs, hCwd,
        hPgid, hSig, hOr, hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid,
        ⟨suf, hTrace⟩, hOther, Or.inl ⟨rfl, hApp⟩, fun _ => rfl⟩
  · refine ⟨Nat.zero_le _, hRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨[], by simp⟩, ⟨[], by simp, ?_, ?_⟩, fun h => h⟩
    · intro d _
      simp [appendedBytesForDesc, writtenBytesForDesc]
    · simp [appendedBytesForDesc, writtenBytesForDesc]

private theorem write_all_loop1_seccomp_or_err (s : ChildState) (fd : I32) (buf : Slice U8)
    (hNonempty : buf.val.isEmpty = false)
    (err : I32) (hNe : err ≠ EINTR) (hRun : s.status = Status.running)
    (onNonSecSt : ChildState → Status)
    (hStPred : ∀ cur : ChildState, cur.status = Status.running → cur.fds = s.fds →
      cur.descs = s.descs → cur.sig = s.sig → cur.pid = s.pid → cur.blockedSigs = s.blockedSigs →
      onNonSecSt cur = Status.running ∨ onNonSecSt cur = onNonSecSt s)
    (hStMatch : ∀ cur : ChildState, cur.sig = s.sig → cur.pid = s.pid → cur.blockedSigs = s.blockedSigs →
      onNonSecSt cur = onNonSecSt s)
    (hWriteNonSec : ∀ cur : ChildState, cur.status = Status.running →
      cur.fds = s.fds → cur.descs = s.descs → cur.sig = s.sig → cur.pid = s.pid → cur.blockedSigs = s.blockedSigs →
      (∀ rawE, currentFault cur ≠ StepFault.seccomp rawE) →
      ∀ sl : Slice U8, sl.val = buf.val →
      sys.write cur fd sl = Result.ok (.Err err,
        { cur with
          trace := cur.trace ++ [⟨.write fd sl.val,
            if onNonSecSt cur = .signaled 13#i32 then .fatalSig 13#i32 else .err err⟩]
          status := onNonSecSt cur })) :
    OkPost (postfork.child.write_all_loop1 s fd buf buf.len 0#usize) fun out =>
      let s' := out.1
      out.2.2 = true ∧
      (s'.status = Status.running ∨ s'.status = onNonSecSt s) ∧
      s'.fds = s.fds ∧ s'.descs = s.descs ∧ s'.cwd = s.cwd ∧
      s'.pgid = s.pgid ∧ s'.sig = s.sig ∧ s'.blockedSigs = s.blockedSigs ∧ s'.oracle = s.oracle ∧
      s'.fdLimit = s.fdLimit ∧ s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
      s'.closeRangeSupported = s.closeRangeSupported ∧ s'.closeRangeErrno = s.closeRangeErrno ∧
      s'.procSelfFdAvailable = s.procSelfFdAvailable ∧ s'.procOpenErrno = s.procOpenErrno ∧
      s'.pid = s.pid ∧ s'.sid = s.sid ∧ s'.writeLog = s.writeLog ∧
      (∃ suf, s'.trace = s.trace ++ suf) ∧
      (oracleHasSeccomp (s.oracle.drop s.trace.length) = false →
        out.2.1 = err ∧ s'.status = onNonSecSt s) := by
  have hLenPos : 0#usize < buf.len := by
    change 0 < buf.length
    cases h : buf.val with
    | nil => simp [h] at hNonempty
    | cons _ _ => simp [Slice.length, h]
  obtain ⟨sl0, hSlEq, hSlVal⟩ := slice_index_from_ok buf 0#usize (Nat.zero_le _)
  have hSl0Val : sl0.val = buf.val := by simpa using hSlVal
  have hSl0Nonempty : sl0.val.isEmpty = false := by rw [hSl0Val]; exact hNonempty
  let measure : sys.Sys × Usize → Nat := fun p => p.1.oracle.length - p.1.trace.length
  let inv : sys.Sys × Usize → Prop := fun p =>
    let cur := p.1
    p.2 = 0#usize ∧
    cur.status = Status.running ∧
    cur.fds = s.fds ∧ cur.descs = s.descs ∧ cur.cwd = s.cwd ∧
    cur.pgid = s.pgid ∧ cur.sig = s.sig ∧ cur.blockedSigs = s.blockedSigs ∧ cur.oracle = s.oracle ∧
    cur.fdLimit = s.fdLimit ∧ cur.kernelMasksSetfd = s.kernelMasksSetfd ∧
    cur.closeRangeSupported = s.closeRangeSupported ∧ cur.closeRangeErrno = s.closeRangeErrno ∧
    cur.procSelfFdAvailable = s.procSelfFdAvailable ∧ cur.procOpenErrno = s.procOpenErrno ∧
    cur.pid = s.pid ∧ cur.sid = s.sid ∧ cur.writeLog = s.writeLog ∧
    (∃ suf, cur.trace = s.trace ++ suf) ∧
    (oracleHasSeccomp (s.oracle.drop s.trace.length) = false →
      oracleHasSeccomp (cur.oracle.drop cur.trace.length) = false)
  rw [postfork.child.write_all_loop1]
  refine okPost_loop_decr_nat measure inv _
    (fun p => postfork.child.write_all_loop1.body fd buf buf.len p.1 p.2) (s, 0#usize) ?_
    ⟨rfl, hRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun h => h⟩
  intro ⟨cur, off⟩ hInv
  rcases hInv with ⟨hOff, hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hBlocked, hOr,
    hLim, hMask, hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid, hWlog, ⟨suf, hTrace⟩, hNoSec⟩
  dsimp only at *
  subst hOff
  unfold postfork.child.write_all_loop1.body
  rw [hSlEq]
  simp only [hLenPos, ↓reduceIte, bind_ok]
  by_cases hSec : ∃ rawE, currentFault cur = StepFault.seccomp rawE
  · rcases hSec with ⟨rawE, hcf⟩
    have hW : sys.write cur fd sl0 = Result.ok (.Err (sanitizeErrno rawE),
        { cur with trace := cur.trace ++ [⟨.write fd sl0.val, .err (sanitizeErrno rawE)⟩] }) := by
      unfold sys.write
      simp [hCurRun, hcf]
    rw [hW]
    simp only [bind_ok, Aeneas.Std.uncurry]
    by_cases hEintr : (sanitizeErrno rawE != postfork.fd_ops.EINTR) = true
    · simp only [hEintr, ↓reduceIte]
      refine ⟨ControlFlow.done (_, sanitizeErrno rawE, true), rfl, ?_⟩
      exact ⟨rfl, Or.inl hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hBlocked, hOr, hLim, hMask, hCrSup, hCrErr,
        hProcAv, hProcErr, hPid, hSid, hWlog,
        ⟨suf ++ [⟨.write fd sl0.val, .err (sanitizeErrno rawE)⟩], by rw [hTrace, List.append_assoc]⟩,
        fun h0 => absurd hcf ((noSeccomp_drop_step cur (hNoSec h0)).2 rawE)⟩
    · simp only [hEintr, Bool.false_eq_true, ↓reduceIte]
      have hltOr : cur.trace.length < cur.oracle.length := lt_oracle_of_currentFault_seccomp hcf
      have hltOr' : cur.trace.length < s.oracle.length := hOr ▸ hltOr
      refine ⟨ControlFlow.cont _, rfl, ?_, ?_⟩
      · exact ⟨rfl, hCurRun, hFds, hDescs, hCwd, hPgid, hSig, hBlocked, hOr, hLim, hMask, hCrSup, hCrErr,
          hProcAv, hProcErr, hPid, hSid, hWlog,
          ⟨suf ++ [⟨.write fd sl0.val, .err (sanitizeErrno rawE)⟩], by rw [hTrace, List.append_assoc]⟩,
          fun h0 => by
            have hStep := (noSeccomp_drop_step cur (hNoSec h0)).1
            simpa [List.length_append] using hStep⟩
      · simp only [measure, List.length_append, List.length_singleton, hOr]; omega
  · have hNonSec : ∀ rawE, currentFault cur ≠ StepFault.seccomp rawE := fun rawE h => hSec ⟨rawE, h⟩
    rw [hWriteNonSec cur hCurRun hFds hDescs hSig hPid hBlocked hNonSec sl0 hSl0Val]
    simp only [bind_ok, Aeneas.Std.uncurry]
    have hNeBool : (err != postfork.fd_ops.EINTR) = true := by
      rw [fd_ops_eintr_eq]; exact bne_iff_ne.mpr hNe
    simp only [hNeBool, ↓reduceIte]
    refine ⟨ControlFlow.done (_, err, true), rfl, ?_⟩
    refine ⟨rfl, hStPred cur hCurRun hFds hDescs hSig hPid hBlocked, hFds, hDescs, hCwd, hPgid, hSig, hBlocked, hOr, hLim, hMask,
      hCrSup, hCrErr, hProcAv, hProcErr, hPid, hSid, hWlog, ?_, fun _ => ⟨rfl, hStMatch cur hSig hPid hBlocked⟩⟩
    exact ⟨suf ++ _, by rw [hTrace, List.append_assoc]⟩

private theorem write_all_loop_one_step_err (s : ChildState) (fd : I32) (buf : Slice U8)
    (hNonempty : buf.val.isEmpty = false)
    (err : I32) (s1 : ChildState) (sl : Slice U8)
    (hSl : sl.val = buf.val)
    (hWrite : sys.write s fd sl = Result.ok (.Err err, s1))
    (hNe : err ≠ EINTR) :
    OkPost (postfork.child.write_all_loop1 s fd buf buf.len 0#usize) fun out =>
      out = (s1, err, true) := by
  rw [postfork.child.write_all_loop1]
  refine okPost_loop_decr_nat (fun _ => 0) (fun p => p = (s, 0#usize)) _
    (fun p => postfork.child.write_all_loop1.body fd buf buf.len p.1 p.2) (s, 0#usize) ?_ rfl
  intro p hp
  subst hp
  have hLenPos : 0#usize < buf.len := by
    change 0 < buf.length
    cases h : buf.val with
    | nil => simp [h] at hNonempty
    | cons _ _ => simp [Slice.length, h]
  obtain ⟨sl0, hSlEq, hSlVal⟩ := slice_index_from_ok buf 0#usize (Nat.zero_le _)
  have hSlEqVal : sl0 = sl := by
    apply Slice.ext
    rw [hSlVal, hSl]
    simp
  subst hSlEqVal
  unfold postfork.child.write_all_loop1.body
  rw [hSlEq]
  simp only [hLenPos, ↓reduceIte, bind_ok, hWrite, Aeneas.Std.uncurry]
  have hNeBool : (err != postfork.fd_ops.EINTR) = true := by
    rw [fd_ops_eintr_eq]
    exact bne_iff_ne.mpr hNe
  simp only [hNeBool, ↓reduceIte]
  exact ⟨ControlFlow.done (s1, err, true), rfl, rfl⟩

/-- Reusable `OkPost` specification for `postfork.child.write_all`. -/
theorem write_all_spec (s : ChildState) (fd : I32) (buf : Slice U8) :
    OkPost (postfork.child.write_all s fd buf) fun p => WriteAllPost s fd buf p.1 p.2 := by
  unfold postfork.child.write_all
  by_cases hNeg : fd < 0#i32
  · simp only [hNeg, ↓reduceIte]
    have hEb : postfork.fd_ops.EBADF = EBADF := by
      unfold postfork.fd_ops.EBADF EBADF
      rfl
    rw [hEb]
    refine ⟨(.Err EBADF, s), rfl, ?_⟩
    simp only [WriteAllPost, hNeg, ↓reduceIte, and_self]
  · simp only [hNeg, ↓reduceIte]
    by_cases hEmpty : buf.val.isEmpty = true
    · have hLen0 : buf.len = 0#usize := by
        apply UScalar.eq_of_val_eq
        change buf.length = 0
        simp [Slice.length, List.isEmpty_iff.mp hEmpty]
      have hBufNil : buf.val = [] := List.isEmpty_iff.mp hEmpty
      simp only [hLen0, ↓reduceIte]
      by_cases hRun : s.status = Status.running
      · cases hFd : s.getFd fd.val with
        | none =>
          have hLoop := write_all_loop0_seccomp_or_err s fd buf EBADF ebadf_ne_eintr hRun
            (fun cur hCurRun hFds _ hNonSec => by
              have hCurFd : cur.getFd fd.val = none := by rw [ChildState.getFd, hFds]; exact hFd
              cases hcf : currentFault cur with
              | seccomp rawE => exact absurd hcf (hNonSec rawE)
              | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hcf])
          refine okPost_bind hLoop ?_
          intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
            hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
          subst hFail
          simp only [Aeneas.Std.uncurry, ↓reduceIte]
          refine ⟨(.Err err, s1), rfl, ?_⟩
          simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd]
          exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
            hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0), hSt1, hWlog1⟩
        | some e =>
          cases hDesc : s.getDesc e.desc with
          | directory cursor =>
            have hLoop := write_all_loop0_seccomp_or_err s fd buf EBADF ebadf_ne_eintr hRun
              (fun cur hCurRun hFds hDescs hNonSec => by
                have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                have hCurDesc : cur.getDesc e.desc = .directory cursor := by rw [ChildState.getDesc, hDescs]; exact hDesc
                cases hcf : currentFault cur with
                | seccomp rawE => exact absurd hcf (hNonSec rawE)
                | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
            refine okPost_bind hLoop ?_
            intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
              hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
            subst hFail
            simp only [Aeneas.Std.uncurry, ↓reduceIte]
            refine ⟨(.Err err, s1), rfl, ?_⟩
            simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
            exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
              hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0), hSt1, hWlog1⟩
          | procSelfFd cursor =>
            have hLoop := write_all_loop0_seccomp_or_err s fd buf EBADF ebadf_ne_eintr hRun
              (fun cur hCurRun hFds hDescs hNonSec => by
                have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                have hCurDesc : cur.getDesc e.desc = .procSelfFd cursor := by rw [ChildState.getDesc, hDescs]; exact hDesc
                cases hcf : currentFault cur with
                | seccomp rawE => exact absurd hcf (hNonSec rawE)
                | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
            refine okPost_bind hLoop ?_
            intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
              hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
            subst hFail
            simp only [Aeneas.Std.uncurry, ↓reduceIte]
            refine ⟨(.Err err, s1), rfl, ?_⟩
            simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
            exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
              hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0), hSt1, hWlog1⟩
          | stream rd wr brk rbs =>
            cases wr
            · have hLoop := write_all_loop0_seccomp_or_err s fd buf EBADF ebadf_ne_eintr hRun
                (fun cur hCurRun hFds hDescs hNonSec => by
                  have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                  have hCurDesc : cur.getDesc e.desc = .stream rd false brk rbs := by rw [ChildState.getDesc, hDescs]; exact hDesc
                  cases hcf : currentFault cur with
                  | seccomp rawE => exact absurd hcf (hNonSec rawE)
                  | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
              refine okPost_bind hLoop ?_
              intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
                hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
              subst hFail
              simp only [Aeneas.Std.uncurry, ↓reduceIte]
              refine ⟨(.Err err, s1), rfl, ?_⟩
              simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
              exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0), hSt1, hWlog1⟩
            · refine okPost_bind (write_all_loop0_stream s fd buf hEmpty hRun e hFd rd brk rbs hDesc) ?_
              intro ⟨s1, err, failed⟩ hLoop
              rcases hLoop with ⟨hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
                hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1,
                hTr1, hCases, hNoFail⟩
              dsimp only [Aeneas.Std.uncurry]
              have hAppSelf : appendedBytesForDesc s.writeLog s1.writeLog e.desc = [] := by
                rw [hWlog1]; simp [appendedBytesForDesc, writtenBytesForDesc]
              have hAppOther : ∀ d : Desc, d ≠ e.desc → appendedBytesForDesc s.writeLog s1.writeLog d = [] := by
                intro d _; rw [hWlog1]; simp [appendedBytesForDesc, writtenBytesForDesc]
              cases failed
              · simp only [Bool.false_eq_true, ↓reduceIte]
                refine ⟨(.Ok (), s1), rfl, ?_⟩
                dsimp only [WriteAllPost]
                rw [ite_eq_right_iff.mpr (fun h => absurd h hNeg),
                  ite_eq_right_iff.mpr (fun h => absurd hRun h), hFd]
                dsimp only
                rw [hDesc]
                cases brk
                · refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hSt1, hAppOther,
                    Or.inl ⟨rfl, by rw [hBufNil]; exact hAppSelf⟩, fun _ => rfl⟩
                · refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hWlog1, ?_⟩
                  rw [hEmpty]; exact ⟨hSt1, Or.inl rfl⟩
              · simp only [↓reduceIte]
                refine ⟨(.Err err, s1), rfl, ?_⟩
                have hNe : err ≠ EINTR := by
                  rcases hCases with hFalse | ⟨_, hNe⟩
                  · cases hFalse
                  · exact hNe
                dsimp only [WriteAllPost]
                rw [ite_eq_right_iff.mpr (fun h => absurd h hNeg),
                  ite_eq_right_iff.mpr (fun h => absurd hRun h), hFd]
                dsimp only
                rw [hDesc]
                cases brk
                · refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hSt1, hAppOther,
                    Or.inr ⟨err, 0, rfl, hNe, Nat.zero_le _, by simp [hAppSelf]⟩, fun hNo => by
                      cases hNoFail hNo⟩
                · refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hWlog1, ?_⟩
                  rw [hEmpty]; exact ⟨hSt1, Or.inr ⟨err, rfl, hNe⟩⟩
      · have hLoop : OkPost (postfork.child.write_all_loop0 buf s fd) fun out =>
            out = (s, 0#i32, false) := by
          rw [postfork.child.write_all_loop0]
          refine okPost_loop_decr_nat (fun _ => 0) (fun p => p = s) _
            (fun p => postfork.child.write_all_loop0.body buf fd p) s ?_ rfl
          intro p hp
          rw [hp]
          unfold postfork.child.write_all_loop0.body
          unfold sys.write
          cases hSt : s.status with
          | running => exact absurd hSt hRun
          | exited _ | signaled _ | execd _ =>
            simp only [bind_ok, Aeneas.Std.uncurry]
            exact ⟨ControlFlow.done (s, 0#i32, false), rfl, rfl⟩
        refine okPost_bind hLoop ?_
        intro out hout
        subst hout
        refine ⟨(.Ok (), s), rfl, ?_⟩
        simp [WriteAllPost, hNeg, hRun, hEmpty]
    · have hNonempty : buf.val.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
      have hLenNe0 : buf.len ≠ 0#usize := by
        intro hEq0
        have hLenVal0 : buf.length = 0 := by simpa using congrArg UScalar.val hEq0
        cases h : buf.val with
        | nil => simp [h] at hNonempty
        | cons _ _ => simp [Slice.length, h] at hLenVal0
      simp only [hLenNe0, ↓reduceIte]
      by_cases hRun : s.status = Status.running
      · cases hFd : s.getFd fd.val with
        | none =>
          have hLoop := write_all_loop1_seccomp_or_err s fd buf hNonempty EBADF ebadf_ne_eintr hRun
            (fun _ => Status.running) (fun _ _ _ _ _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl)
            (fun cur hCurRun hFds _ _ _ _ hNonSec sl _ => by
              have hCurFd : cur.getFd fd.val = none := by rw [ChildState.getFd, hFds]; exact hFd
              cases hcf : currentFault cur with
              | seccomp rawE => exact absurd hcf (hNonSec rawE)
              | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hcf])
          refine okPost_bind hLoop ?_
          intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, _, hOr1,
            hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
          subst hFail
          simp only [Aeneas.Std.uncurry, ↓reduceIte]
          refine ⟨(.Err err, s1), rfl, ?_⟩
          simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd]
          exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
            hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0).1, by rcases hSt1 with h | h <;> exact h, hWlog1⟩
        | some e =>
          cases hDesc : s.getDesc e.desc with
          | directory cursor =>
            have hLoop := write_all_loop1_seccomp_or_err s fd buf hNonempty EBADF ebadf_ne_eintr hRun
              (fun _ => Status.running) (fun _ _ _ _ _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl)
              (fun cur hCurRun hFds hDescs _ _ _ hNonSec sl _ => by
                have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                have hCurDesc : cur.getDesc e.desc = .directory cursor := by rw [ChildState.getDesc, hDescs]; exact hDesc
                cases hcf : currentFault cur with
                | seccomp rawE => exact absurd hcf (hNonSec rawE)
                | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
            refine okPost_bind hLoop ?_
            intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, _, hOr1,
              hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
            subst hFail
            simp only [Aeneas.Std.uncurry, ↓reduceIte]
            refine ⟨(.Err err, s1), rfl, ?_⟩
            simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
            exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
              hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0).1, by rcases hSt1 with h | h <;> exact h, hWlog1⟩
          | procSelfFd cursor =>
            have hLoop := write_all_loop1_seccomp_or_err s fd buf hNonempty EBADF ebadf_ne_eintr hRun
              (fun _ => Status.running) (fun _ _ _ _ _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl)
              (fun cur hCurRun hFds hDescs _ _ _ hNonSec sl _ => by
                have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                have hCurDesc : cur.getDesc e.desc = .procSelfFd cursor := by rw [ChildState.getDesc, hDescs]; exact hDesc
                cases hcf : currentFault cur with
                | seccomp rawE => exact absurd hcf (hNonSec rawE)
                | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
            refine okPost_bind hLoop ?_
            intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, _, hOr1,
              hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
            subst hFail
            simp only [Aeneas.Std.uncurry, ↓reduceIte]
            refine ⟨(.Err err, s1), rfl, ?_⟩
            simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
            exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
              hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0).1, by rcases hSt1 with h | h <;> exact h, hWlog1⟩
          | stream rd wr brk rbs =>
            cases wr
            · have hLoop := write_all_loop1_seccomp_or_err s fd buf hNonempty EBADF ebadf_ne_eintr hRun
                (fun _ => Status.running) (fun _ _ _ _ _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl)
                (fun cur hCurRun hFds hDescs _ _ _ hNonSec sl _ => by
                  have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                  have hCurDesc : cur.getDesc e.desc = .stream rd false brk rbs := by rw [ChildState.getDesc, hDescs]; exact hDesc
                  cases hcf : currentFault cur with
                  | seccomp rawE => exact absurd hcf (hNonSec rawE)
                  | fail _ | normal | partialWrite _ | dentsBatch _ => simp [sys.write, hCurRun, hCurFd, hCurDesc, hcf])
              refine okPost_bind hLoop ?_
              intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, _, hOr1,
                hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
              subst hFail
              simp only [Aeneas.Std.uncurry, ↓reduceIte]
              refine ⟨(.Err err, s1), rfl, ?_⟩
              simp only [WriteAllPost, hNeg, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
              exact ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                hProcAv1, hProcErr1, hPid1, hSid1, hTr1, fun h0 => congrArg core.result.Result.Err (hNoSec1 h0).1, by rcases hSt1 with h | h <;> exact h, hWlog1⟩
            · cases brk
              · refine okPost_bind (write_all_loop_stream_ok s fd buf hNonempty hRun e hFd rd rbs hDesc) ?_
                intro ⟨s1, err, failed⟩ hLoop
                rcases hLoop with ⟨hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1,
                  hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1,
                  hTr1, hOth1, hCases, hNoFail⟩
                dsimp only [Aeneas.Std.uncurry]
                cases failed
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  refine ⟨(.Ok (), s1), rfl, ?_⟩
                  dsimp only [WriteAllPost]
                  rw [ite_eq_right_iff.mpr (fun h => absurd h hNeg),
                    ite_eq_right_iff.mpr (fun h => absurd hRun h),
                    hFd]
                  dsimp only
                  rw [hDesc]
                  dsimp only
                  refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hSt1, hOth1, ?_, fun _ => rfl⟩
                  rcases hCases with ⟨_, hApp⟩ | ⟨hFalse, _⟩
                  · exact Or.inl ⟨rfl, hApp⟩
                  · cases hFalse
                · simp only [↓reduceIte]
                  refine ⟨(.Err err, s1), rfl, ?_⟩
                  dsimp only [WriteAllPost]
                  rw [ite_eq_right_iff.mpr (fun h => absurd h hNeg),
                    ite_eq_right_iff.mpr (fun h => absurd hRun h),
                    hFd]
                  dsimp only
                  rw [hDesc]
                  dsimp only
                  refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                    hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hSt1, hOth1, ?_, ?_⟩
                  · rcases hCases with ⟨hFalse, _⟩ | ⟨_, hNe, k, hkLe, hApp⟩
                    · cases hFalse
                    · exact Or.inr ⟨err, k, rfl, hNe, hkLe, hApp⟩
                  · intro hNo
                    exact False.elim (by cases hNoFail hNo)
              · have hLoop := write_all_loop1_seccomp_or_err s fd buf hNonempty EPIPE epipe_ne_eintr hRun
                  (fun cur => if cur.getSig 13 == .default && cur.pid != 1 && !cur.isSigBlocked 13 then .signaled 13#i32 else .running)
                  (fun cur _ _ _ hSig hPid hBlocked => Or.inr (by
                    simp [ChildState.getSig, ChildState.isSigBlocked, hSig, hPid, hBlocked]))
                  (fun cur hSig hPid hBlocked => by
                    simp [ChildState.getSig, ChildState.isSigBlocked, hSig, hPid, hBlocked])
                  (fun cur hCurRun hFds hDescs hSig hPid hBlocked hNonSec sl hSl => by
                    have hCurFd : cur.getFd fd.val = some e := by rw [ChildState.getFd, hFds]; exact hFd
                    have hCurDesc : cur.getDesc e.desc = .stream rd true true rbs := by rw [ChildState.getDesc, hDescs]; exact hDesc
                    have hSlEmpty : sl.val.isEmpty = false := by rw [hSl]; exact hNonempty
                    cases hcf : currentFault cur with
                    | seccomp rawE => exact absurd hcf (hNonSec rawE)
                    | fail _ | normal | partialWrite _ | dentsBatch _ =>
                      by_cases hSigDef : (cur.getSig 13 == Disp.default && cur.pid != 1 && !cur.isSigBlocked 13) = true
                      · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne] at hSigDef
                        simp [sys.write, hCurRun, hCurFd, hCurDesc, hSlEmpty, hcf, hSigDef]
                      · simp only [Bool.not_eq_true] at hSigDef
                        simp [sys.write, hCurRun, hCurFd, hCurDesc, hSlEmpty, hcf, hSigDef])
                refine okPost_bind hLoop ?_
                intro ⟨s1, err, failed⟩ ⟨hFail, hSt1, hFds1, hDescs1, hCwd1, hPgid1, hSig1, _, hOr1,
                  hLim1, hMask1, hCrSup1, hCrErr1, hProcAv1, hProcErr1, hPid1, hSid1, hWlog1, hTr1, hNoSec1⟩
                subst hFail
                simp only [Aeneas.Std.uncurry, ↓reduceIte]
                refine ⟨(.Err err, s1), rfl, ?_⟩
                simp only [WriteAllPost, hNeg, hNonempty, hRun, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc]
                refine ⟨hFds1, hDescs1, hCwd1, hPgid1, hSig1, hOr1, hLim1, hMask1, hCrSup1, hCrErr1,
                  hProcAv1, hProcErr1, hPid1, hSid1, hTr1, hWlog1, fun h0 => ⟨congrArg core.result.Result.Err (hNoSec1 h0).1, (hNoSec1 h0).2⟩, ?_⟩
                rcases hSt1 with hSt | hSt
                · exact Or.inl hSt
                · by_cases hDef : (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true
                  · simp only [hDef, ↓reduceIte] at hSt
                    exact Or.inr ⟨hDef, hSt⟩
                  · simp only [hDef, Bool.false_eq_true, ↓reduceIte] at hSt
                    exact Or.inl hSt
      · have hLenPos : 0#usize < buf.len := by
          change 0 < buf.length
          cases h : buf.val with
          | nil => simp [h] at hNonempty
          | cons _ _ => simp [Slice.length, h]
        obtain ⟨sl0, hSlEq, _⟩ := slice_index_from_ok buf 0#usize (Nat.zero_le _)
        have hLoop : OkPost (postfork.child.write_all_loop1 s fd buf buf.len 0#usize) fun out =>
            out = (s, World.EIO, true) := by
          rw [postfork.child.write_all_loop1]
          refine okPost_loop_decr_nat (fun _ => 0) (fun p => p = (s, 0#usize)) _
            (fun p => postfork.child.write_all_loop1.body fd buf buf.len p.1 p.2) (s, 0#usize) ?_ rfl
          intro p hp
          subst hp
          unfold postfork.child.write_all_loop1.body
          simp only [hLenPos, ↓reduceIte, hSlEq, bind_ok]
          unfold sys.write
          cases hSt : s.status with
          | running => exact absurd hSt hRun
          | exited _ | signaled _ | execd _ =>
            simp only [bind_ok, Aeneas.Std.uncurry]
            unfold postfork.fd_ops.EIO World.EIO
            exact ⟨ControlFlow.done (s, World.EIO, true), rfl, rfl⟩
        refine okPost_bind hLoop ?_
        intro out hout
        subst hout
        refine ⟨(.Err World.EIO, s), rfl, ?_⟩
        simp [WriteAllPost, hNeg, hNonempty, hRun]

end WriteAll

section ReportAndExit

/-- Postcondition for `postfork.child.report_bytes_and_exit` and its typed wrappers. -/
def ReportBytesPost (s : ChildState) (repW : I32) (payload : Bytes) (s' : ChildState) : Prop :=
  if s.status ≠ Status.running then
    s' = s
  else
    s'.status = Status.exited 127#i32 ∧
    s'.fds = s.fds ∧
    s'.descs = s.descs ∧
    s'.cwd = s.cwd ∧
    s'.pgid = s.pgid ∧
    s'.oracle = s.oracle ∧
    s'.fdLimit = s.fdLimit ∧
    s'.kernelMasksSetfd = s.kernelMasksSetfd ∧
    s'.closeRangeSupported = s.closeRangeSupported ∧
    s'.closeRangeErrno = s.closeRangeErrno ∧
    s'.procSelfFdAvailable = s.procSelfFdAvailable ∧
    s'.procOpenErrno = s.procOpenErrno ∧
    s'.pid = s.pid ∧
    s'.sid = s.sid ∧
    (∃ suf, s'.trace = s.trace ++ suf) ∧
    (repW < 0#i32 → s'.writeLog = s.writeLog) ∧
    (0#i32 ≤ repW →
      match s.getFd repW.val with
      | none => s'.writeLog = s.writeLog
      | some e =>
        match s.getDesc e.desc with
        | .stream _ true false _ =>
          (∀ d : Desc, d ≠ e.desc → appendedBytesForDesc s.writeLog s'.writeLog d = []) ∧
          ((∀ rawE, currentFault s ≠ .fail rawE ∧ currentFault s ≠ .seccomp rawE) →
           (∀ f ∈ s.oracle.drop (s.trace.length + 1),
              match f with | .fail rawE | .seccomp rawE => sanitizeErrno rawE = EINTR | _ => True) →
            appendedBytesForDesc s.writeLog s'.writeLog e.desc = payload)
        | _ => s'.writeLog = s.writeLog)

private theorem exit_exec_failed_eq : postfork.child.EXIT_EXEC_FAILED = 127#i32 := by
  unfold postfork.child.EXIT_EXEC_FAILED
  rfl

/-- Reusable `OkPost` specification for `postfork.child.report_bytes_and_exit`. -/
theorem report_bytes_and_exit_spec (s : ChildState) (repW : I32) (bytes : Slice U8) :
    OkPost (postfork.child.report_bytes_and_exit s repW bytes) fun s' =>
      ReportBytesPost s repW bytes.val s' := by
  unfold postfork.child.report_bytes_and_exit
  by_cases hRun : s.status = Status.running
  · by_cases hGe : repW ≥ 0#i32
    · have hNotNeg : ¬ (repW < 0#i32) := by
        change ¬ ((↑repW : Int) < 0)
        change (0 : Int) ≤ (↑repW : Int) at hGe
        omega
      simp only [hGe, ↓reduceIte]
      have hSigUs : isUserspaceInvalidSigactionSig postfork.child.SIGPIPE = false := by
        simp [postfork.child.SIGPIPE, isUserspaceInvalidSigactionSig]
      have hSigKn : isKernelInvalidSigactionSig postfork.child.SIGPIPE = false := by
        simp [postfork.child.SIGPIPE, isKernelInvalidSigactionSig]
      unfold sys.sig_ign runUnitSyscall
      simp only [hRun, hSigUs, hSigKn, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      cases hcf : currentFault s with
      | seccomp rawE =>
        simp only [bind_ok, Aeneas.Std.uncurry]
        rw [sys_exit_eq]
        simp only [↓reduceIte]
        refine ⟨_, rfl, ?_⟩
        dsimp only [ReportBytesPost]
        rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
          show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          ⟨[⟨.sigIgn postfork.child.SIGPIPE, .err (sanitizeErrno rawE)⟩, ⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
            by simp [List.append_assoc]⟩,
          fun h => absurd h hNotNeg, fun _ => ?_⟩
        cases hFd : s.getFd repW.val with
        | none => dsimp only
        | some e =>
          dsimp only
          cases hDesc : s.getDesc e.desc with
          | directory _ | procSelfFd _ => dsimp only
          | stream rd wr brk rbs =>
            cases wr
            · rfl
            · cases brk
              · refine ⟨fun _ _ => by simp [appendedBytesForDesc, writtenBytesForDesc],
                  fun hNoCur _ => absurd hcf (hNoCur rawE).2⟩
              · rfl
      | fail rawE =>
        simp only [bind_ok, Aeneas.Std.uncurry, id_eq]
        rw [sys_exit_eq]
        simp only [hRun, ↓reduceIte]
        refine ⟨_, rfl, ?_⟩
        dsimp only [ReportBytesPost]
        rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
          show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          ⟨[⟨.sigIgn postfork.child.SIGPIPE, .err (sanitizeErrno rawE)⟩, ⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
            by simp [List.append_assoc]⟩,
          fun h => absurd h hNotNeg, fun _ => ?_⟩
        cases hFd : s.getFd repW.val with
        | none => dsimp only
        | some e =>
          dsimp only
          cases hDesc : s.getDesc e.desc with
          | directory _ | procSelfFd _ => dsimp only
          | stream rd wr brk rbs =>
            cases wr
            · rfl
            · cases brk
              · refine ⟨fun _ _ => by simp [appendedBytesForDesc, writtenBytesForDesc],
                  fun hNoCur _ => absurd hcf (hNoCur rawE).1⟩
              · rfl
      | normal | partialWrite _ | dentsBatch _ =>
        all_goals
          simp only [bind_ok, Aeneas.Std.uncurry]
          let s2 : ChildState := { s.putSig (↑postfork.child.SIGPIPE : Int) Disp.ignore with
            trace := s.trace ++ [{ req := Req.sigIgn postfork.child.SIGPIPE, out := EventOutcome.okVal 0 }] }
          have hRun2 : s2.status = Status.running := hRun
          have hSig13 : s2.getSig 13 = Disp.ignore := by
            simp only [s2, postfork.child.SIGPIPE, ChildState.getSig, ChildState.putSig]
            exact getSig_putSig_self s 13 Disp.ignore
          have hFdEq : ∀ k, s2.getFd k = s.getFd k := fun _ => rfl
          have hDescEq : ∀ d, s2.getDesc d = s.getDesc d := fun _ => rfl
          have hS2Eq : ({ pid := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).pid
                          sid := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).sid
                          pgid := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).pgid
                          fds := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).fds
                          descs := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).descs
                          fdLimit := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).fdLimit
                          kernelMasksSetfd := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).kernelMasksSetfd
                          closeRangeSupported := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).closeRangeSupported
                          closeRangeErrno := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).closeRangeErrno
                          procSelfFdAvailable := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).procSelfFdAvailable
                          procOpenErrno := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).procOpenErrno
                          cwd := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).cwd
                          chdirResolved := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).chdirResolved
                          sig := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).sig
                          blockedSigs := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).blockedSigs
                          procMaxFds := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).procMaxFds
                          writeLog := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).writeLog
                          trace := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).trace ++
                            [{ req := Req.sigIgn postfork.child.SIGPIPE, out := EventOutcome.okVal 0 }]
                          oracle := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).oracle
                          status := (s.putSig (↑postfork.child.SIGPIPE) Disp.ignore).status } : ChildState) = s2 := by
            simp only [s2, ChildState.putSig]
          rw [hS2Eq]
          have hWS3 : OkPost
              (do let (_, s3) ← postfork.child.write_all s2 repW bytes; Result.ok s3)
              (fun s3 => ∃ r3, WriteAllPost s2 repW bytes r3 s3) :=
            okPost_bind (write_all_spec s2 repW bytes) (fun p hp => ⟨p.2, rfl, ⟨p.1, hp⟩⟩)
          refine okPost_bind hWS3 ?_
          rintro s3 ⟨r3, hW⟩
          simp only [WriteAllPost, hNotNeg, hRun2, ne_eq, not_true_eq_false, ↓reduceIte] at hW
          rcases hW with ⟨hFds3, hDescs3, hCwd3, hPgid3, _, hOr3, hLim3, hMask3,
            hCrSup3, hCrErr3, hProcAv3, hProcErr3, hPid3, hSid3, ⟨suf3, hTr3⟩, hMatch3⟩
          rw [sys_exit_eq]
          cases hFd : s.getFd repW.val with
          | none =>
            rw [hFdEq, hFd] at hMatch3
            rcases hMatch3 with ⟨_, hSt3, hWlog3⟩
            simp only [hSt3, ↓reduceIte]
            refine ⟨_, rfl, ?_⟩
            dsimp only [ReportBytesPost]
            rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
              show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
            refine ⟨rfl, hFds3, hDescs3, hCwd3, hPgid3, hOr3, hLim3, hMask3, hCrSup3, hCrErr3,
              hProcAv3, hProcErr3, hPid3, hSid3,
              ⟨[⟨.sigIgn postfork.child.SIGPIPE, .okVal 0⟩] ++ suf3 ++
                [⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
                by simp [hTr3, s2, List.append_assoc]⟩,
              fun h => absurd h hNotNeg, fun _ => ?_⟩
            rw [hFd]
            dsimp only
            rw [hWlog3]; rfl
          | some e =>
            rw [hFdEq, hFd] at hMatch3
            dsimp only at hMatch3
            cases hDesc : s.getDesc e.desc with
            | directory _ | procSelfFd _ =>
              rw [hDescEq, hDesc] at hMatch3
              rcases hMatch3 with ⟨_, hSt3, hWlog3⟩
              simp only [hSt3, ↓reduceIte]
              refine ⟨_, rfl, ?_⟩
              dsimp only [ReportBytesPost]
              rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
                show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
              refine ⟨rfl, hFds3, hDescs3, hCwd3, hPgid3, hOr3, hLim3, hMask3, hCrSup3, hCrErr3,
                hProcAv3, hProcErr3, hPid3, hSid3,
                ⟨[⟨.sigIgn postfork.child.SIGPIPE, .okVal 0⟩] ++ suf3 ++
                  [⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
                  by simp [hTr3, s2, List.append_assoc]⟩,
                fun h => absurd h hNotNeg, fun _ => ?_⟩
              rw [hFd]
              dsimp only
              rw [hDesc]
              dsimp only
              rw [hWlog3]; rfl
            | stream rd wr brk rbs =>
              rw [hDescEq, hDesc] at hMatch3
              cases wr
              · rcases hMatch3 with ⟨_, hSt3, hWlog3⟩
                simp only [hSt3, ↓reduceIte]
                refine ⟨_, rfl, ?_⟩
                dsimp only [ReportBytesPost]
                rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
                  show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
                refine ⟨rfl, hFds3, hDescs3, hCwd3, hPgid3, hOr3, hLim3, hMask3, hCrSup3, hCrErr3,
                  hProcAv3, hProcErr3, hPid3, hSid3,
                  ⟨[⟨.sigIgn postfork.child.SIGPIPE, .okVal 0⟩] ++ suf3 ++
                    [⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
                    by simp [hTr3, s2, List.append_assoc]⟩,
                  fun h => absurd h hNotNeg, fun _ => ?_⟩
                rw [hFd]
                dsimp only
                rw [hDesc]
                dsimp only
                rw [hWlog3]; rfl
              · cases brk
                · rcases hMatch3 with ⟨hSt3, hOth3, hCases3, hAllOk3⟩
                  simp only [hSt3, ↓reduceIte]
                  refine ⟨_, rfl, ?_⟩
                  dsimp only [ReportBytesPost]
                  rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
                    show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
                  refine ⟨rfl, hFds3, hDescs3, hCwd3, hPgid3, hOr3, hLim3, hMask3, hCrSup3, hCrErr3,
                    hProcAv3, hProcErr3, hPid3, hSid3,
                    ⟨[⟨.sigIgn postfork.child.SIGPIPE, .okVal 0⟩] ++ suf3 ++
                      [⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
                      by simp [hTr3, s2, List.append_assoc]⟩,
                    fun h => absurd h hNotNeg, fun _ => ?_⟩
                  rw [hFd]
                  dsimp only
                  rw [hDesc]
                  dsimp only
                  refine ⟨hOth3, fun _ hNo2' => ?_⟩
                  have hNo2 : ∀ f ∈ s2.oracle.drop s2.trace.length,
                      match f with | .fail rawE | .seccomp rawE => sanitizeErrno rawE = EINTR | _ => True := by
                    dsimp only [s2, ChildState.putSig]
                    simpa [List.length_append] using hNo2'
                  have hOk := hAllOk3 hNo2
                  rcases hCases3 with ⟨_, hApp⟩ | ⟨err, _, hErrEq, _⟩
                  · exact hApp
                  · rw [hOk] at hErrEq; cases hErrEq
                · have hStWlog : s3.status = Status.running ∧ s3.writeLog = s2.writeLog := by
                    rcases hMatch3 with ⟨hWlog3, hBrk⟩
                    by_cases hEmpty : bytes.val.isEmpty = true
                    · simp only [hEmpty, ↓reduceIte] at hBrk
                      exact ⟨hBrk.1, hWlog3⟩
                    · simp only [hEmpty, Bool.false_eq_true, ↓reduceIte] at hBrk
                      have hNotDef : ¬ (s2.getSig 13 == Disp.default && s2.pid != 1 && !s2.isSigBlocked 13) = true := by
                        simp [hSig13]
                      rcases hBrk.2 with hSt | ⟨hDef, _⟩
                      · exact ⟨hSt, hWlog3⟩
                      · exact absurd hDef hNotDef
                  rcases hStWlog with ⟨hSt3, hWlog3⟩
                  simp only [hSt3, ↓reduceIte]
                  refine ⟨_, rfl, ?_⟩
                  dsimp only [ReportBytesPost]
                  rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
                    show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
                  refine ⟨rfl, hFds3, hDescs3, hCwd3, hPgid3, hOr3, hLim3, hMask3, hCrSup3, hCrErr3,
                    hProcAv3, hProcErr3, hPid3, hSid3,
                    ⟨[⟨.sigIgn postfork.child.SIGPIPE, .okVal 0⟩] ++ suf3 ++
                      [⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩],
                      by simp [hTr3, s2, List.append_assoc]⟩,
                    fun h => absurd h hNotNeg, fun _ => ?_⟩
                  rw [hFd]
                  dsimp only
                  rw [hDesc]
                  dsimp only
                  rw [hWlog3]; rfl
    · have hNeg : repW < 0#i32 := by
        change (↑repW : Int) < 0
        change ¬ ((0 : Int) ≤ (↑repW : Int)) at hGe
        omega
      simp only [hGe, ↓reduceIte, bind_ok]
      rw [sys_exit_eq]
      simp only [hRun, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      dsimp only [ReportBytesPost]
      rw [ite_eq_right_iff.mpr (fun h => absurd hRun h),
        show Status.exited postfork.child.EXIT_EXEC_FAILED = Status.exited 127#i32 by rw [exit_exec_failed_eq]]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ⟨[⟨.exit postfork.child.EXIT_EXEC_FAILED, .okVal 0⟩], rfl⟩,
        fun _ => rfl, fun h => by
          change (0 : Int) ≤ (↑repW : Int) at h
          change ¬ ((0 : Int) ≤ (↑repW : Int)) at hGe
          exact False.elim (hGe h)⟩
  · by_cases hGe : repW ≥ 0#i32
    · simp only [hGe, ↓reduceIte]
      have hNotRunB : (s.status == Status.running) = false := beq_false_of_ne hRun
      unfold sys.sig_ign
      simp only [hNotRunB, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [runUnitSyscall_not_running s hRun _ _ _ _, bind_ok]
      dsimp only [Aeneas.Std.uncurry]
      have hWS3 : OkPost
          (do let (_, s3) ← postfork.child.write_all s repW bytes; Result.ok s3)
          (fun s3 => ∃ r3, WriteAllPost s repW bytes r3 s3) :=
        okPost_bind (write_all_spec s repW bytes) (fun p hp => ⟨p.2, rfl, ⟨p.1, hp⟩⟩)
      refine okPost_bind hWS3 ?_
      rintro s3 ⟨r3, hW⟩
      have hS3Eq : s3 = s := by
        by_cases hNeg : repW < 0#i32
        · simp [WriteAllPost, hNeg] at hW; exact hW.2
        · simp [WriteAllPost, hNeg, hRun] at hW; exact hW.2
      subst hS3Eq
      rw [sys_exit_eq]
      simp only [hRun, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      simp [ReportBytesPost, hRun]
    · simp only [hGe, ↓reduceIte, bind_ok]
      rw [sys_exit_eq]
      simp only [hRun, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      simp [ReportBytesPost, hRun]

/-- Reusable `OkPost` specification for unified `postfork.child.report_and_exit`. -/
theorem report_and_exit_spec (s : ChildState) (repW : I32) (stage : U8) (errnum fallback : I32) :
    OkPost (postfork.child.report_and_exit s repW stage errnum fallback) fun s' =>
      ReportBytesPost s repW (expectedFailureWireBytes stage (normalizeErrnoSpec errnum fallback)) s' := by
  unfold postfork.child.report_and_exit
  have hNorm : postfork.child.normalize_errno errnum fallback =
      Result.ok (normalizeErrnoSpec errnum fallback) := by
    unfold postfork.child.normalize_errno normalizeErrnoSpec
    by_cases hPos : errnum > 0#i32 <;> simp [hPos]
  rw [hNorm, bind_ok]
  refine okPost_bind (encode_failure_report_spec stage (normalizeErrnoSpec errnum fallback)) ?_
  intro msg hMsg
  simp only [lift, bind_ok]
  have hRep := report_bytes_and_exit_spec s repW (Array.to_slice msg)
  have hSliceVal : (Array.to_slice msg).val =
      expectedFailureWireBytes stage (normalizeErrnoSpec errnum fallback) := by
    simpa [Array.to_slice] using hMsg
  simpa [hSliceVal] using hRep

end ReportAndExit

section SpecPromises

/-- Kernel proof of `test_postfork_readSyncByte_eintrRetryAndClose` for `rustAeneasApi`. -/
theorem test_postfork_readSyncByte_eintrRetryAndClose_allPass :
    Core.AllPass (test_postfork_readSyncByte_eintrRetryAndClose rustAeneasApi) := by
  intro s syncR
  dsimp only [Core.AllPass, test_postfork_readSyncByte_eintrRetryAndClose]
  have hA2 : OkPost
      (rustAeneasApi.readSyncByte
        { fds := [(5, { desc := 55, cloexec := true })]
          descs := [(55, DescState.stream true false false [1#u8])]
          oracle := [StepFault.fail EINTR, StepFault.fail EINTR] }
        5#i32)
      fun p => p.1 = true ∧ p.2.isOpen 5 = false := by
    refine okPost_mono (read_sync_byte_spec _ 5#i32) ?_
    intro p hp
    simp only [SyncBytePost, show ¬ ((5#i32 : I32) < 0#i32) from by decide, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, hClosed, _, _, hGot⟩
    refine ⟨?_, hClosed (by decide)⟩
    exact hGot.mpr ⟨{ desc := 55, cloexec := true }, false, false, 1#u8, [], rfl, rfl, by
      simp [firstNonEintrFault, sanitizeErrno, EINTR]⟩
  have hA3 : OkPost
      (rustAeneasApi.readSyncByte
        { fds := [(5, { desc := 55, cloexec := true })]
          descs := [(55, DescState.stream true false false [])]
          oracle := [StepFault.fail EINTR] }
        5#i32)
      fun p => p.1 = false ∧ p.2.isOpen 5 = false := by
    refine okPost_mono (read_sync_byte_spec _ 5#i32) ?_
    intro p hp
    simp only [SyncBytePost, show ¬ ((5#i32 : I32) < 0#i32) from by decide, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, hClosed, _, _, hGot⟩
    refine ⟨?_, hClosed (by decide)⟩
    cases hb : p.1 with
    | false => rfl
    | true =>
      exfalso
      rcases hGot.mp hb with ⟨e, _, _, _, _, he, hd, _⟩
      have h5 : ({ fds := [(5, { desc := 55, cloexec := true })]
                   descs := [(55, DescState.stream true false false [])]
                   oracle := [StepFault.fail EINTR] } : ChildState).getFd (5#i32).val =
          some { desc := 55, cloexec := true } := rfl
      rw [h5] at he
      injection he with heq
      subst heq
      have h55 : ({ fds := [(5, { desc := 55, cloexec := true })]
                    descs := [(55, DescState.stream true false false [])]
                    oracle := [StepFault.fail EINTR] } : ChildState).getDesc 55 = DescState.stream true false false [] := rfl
      rw [h55] at hd
      cases hd
  have hA4 : OkPost
      (rustAeneasApi.readSyncByte
        { fds := [(5, { desc := 55, cloexec := true })]
          descs := [(55, DescState.stream true false false [1#u8])]
          oracle := [StepFault.fail World.EIO] }
        5#i32)
      fun p => p.1 = false ∧ p.2.isOpen 5 = false := by
    refine okPost_mono (read_sync_byte_spec _ 5#i32) ?_
    intro p hp
    simp only [SyncBytePost, show ¬ ((5#i32 : I32) < 0#i32) from by decide, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, hClosed, _, _, hGot⟩
    refine ⟨?_, hClosed (by decide)⟩
    cases hb : p.1 with
    | false => rfl
    | true =>
      exfalso
      rcases hGot.mp hb with ⟨_, _, _, _, _, _, _, hNoFail⟩
      exfalso
      simp [firstNonEintrFault, sanitizeErrno, World.EIO, EINTR] at hNoFail
  by_cases hNeg : decide (syncR < 0#i32) = true
  · simp only [hNeg, ↓reduceIte]
    have hLt : syncR < 0#i32 := by simpa using hNeg
    refine ⟨?_, hA2, hA3, hA4, trivial⟩
    refine okPost_mono (read_sync_byte_spec s syncR) ?_
    intro p hp
    simp [SyncBytePost, hLt] at hp
    exact hp
  · simp only [hNeg, Bool.false_eq_true, ↓reduceIte]
    have hNotLt : ¬ (syncR < 0#i32) := by simpa using hNeg
    by_cases hRun : (s.status == Status.running) = true
    · simp only [hRun, ↓reduceIte]
      have hEqRun : s.status = Status.running := by simpa using hRun
      by_cases hNoSec : (!oracleHasSeccomp s.oracle) = true
      · simp only [hNoSec, ↓reduceIte]
        have hNoSec' : oracleHasSeccomp s.oracle = false := by simpa using hNoSec
        refine ⟨?_, hA2, hA3, hA4, trivial⟩
        refine okPost_mono (read_sync_byte_spec s syncR) ?_
        intro p hp
        simp [SyncBytePost, hNotLt, hEqRun] at hp
        exact hp.2.2.2.2.2.2.1 hNoSec'
      · simp only [hNoSec, Bool.false_eq_true, ↓reduceIte]
        exact ⟨okPost_mono (read_sync_byte_spec s syncR) (fun _ _ => trivial), hA2, hA3, hA4, trivial⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte]
      exact ⟨okPost_mono (read_sync_byte_spec s syncR) (fun _ _ => trivial), hA2, hA3, hA4, trivial⟩

/-- Kernel proof of `test_postfork_writeAll_eintrPartialWriteAndReassembly` for `rustAeneasApi`. -/
theorem test_postfork_writeAll_eintrPartialWriteAndReassembly_allPass :
    Core.AllPass (test_postfork_writeAll_eintrPartialWriteAndReassembly rustAeneasApi) := by
  dsimp only [Core.AllPass, test_postfork_writeAll_eintrPartialWriteAndReassembly]
  intro s fd payload
  have hChunked : OkPost (postfork.child.write_all
      { fds := [(4, { desc := 90, cloexec := true })]
        descs := [(90, .stream false true false [])]
        sig := [(13, .ignore)]
        oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] }
      4#i32 (mkSliceU8 8#usize [10#u8, 20#u8, 30#u8, 40#u8, 50#u8, 60#u8, 70#u8, 80#u8]))
      fun p =>
        p.1 = .Ok () ∧
        appendedBytesForDesc
          ({ fds := [(4, { desc := 90, cloexec := true })]
             descs := [(90, .stream false true false [])]
             sig := [(13, .ignore)]
             oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] } : ChildState).writeLog
          p.2.writeLog 90 =
          (mkSliceU8 8#usize [10#u8, 20#u8, 30#u8, 40#u8, 50#u8, 60#u8, 70#u8, 80#u8]).val := by
    refine okPost_mono (write_all_spec _ 4#i32 _) ?_
    intro p hp
    simp only [WriteAllPost, show ¬ ((4#i32 : I32) < 0#i32) from by decide,
      ne_eq, not_true_eq_false, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hMatch⟩
    have hFd : ({ fds := [(4, { desc := 90, cloexec := true })]
                  descs := [(90, .stream false true false [])]
                  sig := [(13, .ignore)]
                  oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] } : ChildState).getFd (4#i32).val =
        some { desc := 90, cloexec := true } := rfl
    have hDesc : ({ fds := [(4, { desc := 90, cloexec := true })]
                    descs := [(90, .stream false true false [])]
                    sig := [(13, .ignore)]
                    oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] } : ChildState).getDesc 90 =
        .stream false true false [] := rfl
    rw [hFd] at hMatch
    dsimp only at hMatch
    rw [hDesc] at hMatch
    rcases hMatch with ⟨_, _, hCases, hNoFail⟩
    have hOk := hNoFail (by
      intro f hf
      simp only [List.length_nil, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact trivial | exact rfl)
    rcases hCases with hGoal | ⟨_, _, hErr, _⟩
    · exact hGoal
    · rw [hOk] at hErr; cases hErr
  by_cases hNeg : decide (fd < 0#i32) = true
  · simp only [hNeg, ↓reduceIte]
    have hLt : fd < 0#i32 := by simpa using hNeg
    refine ⟨okPost_mono (write_all_spec s fd payload) (fun p hp => by simp [WriteAllPost, hLt] at hp; exact hp),
      hChunked, ?_⟩
    rintro ⟨hSt, hOr, hNonneg⟩
    have hNotNeg : ¬ (fd < 0#i32) := by
      change ¬ ((↑fd : Int) < 0)
      change (0 : Int) ≤ (↑fd : Int) at hNonneg
      omega
    cases hFd : s.getFd fd.val with
    | some e =>
      dsimp only
      intro hDesc
      refine ⟨okPost_mono (write_all_spec s fd payload) ?_, trivial⟩
      intro p hpW
      simp only [WriteAllPost, hNotNeg, hSt, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc] at hpW
      rcases hpW with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCases, hNoFail⟩
      have hOk := hNoFail (by simp [hOr])
      rcases hCases with hGoal | ⟨_, _, hErr, _⟩
      · exact hGoal
      · rw [hOk] at hErr; cases hErr
    | none =>
      dsimp only
      refine ⟨okPost_mono (write_all_spec s fd payload) ?_, trivial⟩
      intro p hpW
      simp only [WriteAllPost, hNotNeg, hSt, ne_eq, not_true_eq_false, ↓reduceIte, hFd] at hpW
      exact hpW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by simp [hOr, oracleHasSeccomp])
  · simp only [hNeg, Bool.false_eq_true, ↓reduceIte]
    refine ⟨okPost_mono (write_all_spec s fd payload) (fun _ _ => trivial), hChunked, ?_⟩
    rintro ⟨hSt, hOr, hNonneg⟩
    have hNotNeg : ¬ (fd < 0#i32) := by
      change ¬ ((↑fd : Int) < 0)
      change (0 : Int) ≤ (↑fd : Int) at hNonneg
      omega
    cases hFd : s.getFd fd.val with
    | some e =>
      dsimp only
      intro hDesc
      refine ⟨okPost_mono (write_all_spec s fd payload) ?_, trivial⟩
      intro p hpW
      simp only [WriteAllPost, hNotNeg, hSt, ne_eq, not_true_eq_false, ↓reduceIte, hFd, hDesc] at hpW
      rcases hpW with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCases, hNoFail⟩
      have hOk := hNoFail (by simp [hOr])
      rcases hCases with hGoal | ⟨_, _, hErr, _⟩
      · exact hGoal
      · rw [hOk] at hErr; cases hErr
    | none =>
      dsimp only
      refine ⟨okPost_mono (write_all_spec s fd payload) ?_, trivial⟩
      intro p hpW
      simp only [WriteAllPost, hNotNeg, hSt, ne_eq, not_true_eq_false, ↓reduceIte, hFd] at hpW
      exact hpW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by simp [hOr, oracleHasSeccomp])

/-- Witness reachability for `test_postfork_writeAll_eintrPartialWriteAndReassembly`. -/
theorem test_postfork_writeAll_eintrPartialWriteAndReassembly_canReach :
    Core.CanReach (test_postfork_writeAll_eintrPartialWriteAndReassembly rustAeneasApi) := by
  let s0 : ChildState :=
    { fds := [(4, { desc := 90, cloexec := true })]
      descs := [(90, .stream false true false [])] }
  let fd0 : I32 := 4#i32
  let pay0 : Slice U8 := mkSliceU8 1#usize [42#u8]
  let sChunked : ChildState :=
    { fds := [(4, { desc := 90, cloexec := true })]
      descs := [(90, .stream false true false [])]
      sig := [(13, .ignore)]
      oracle := [.partialWrite 1, .fail EINTR, .partialWrite 2, .fail EINTR, .normal] }
  let msg := mkSliceU8 8#usize [10#u8, 20#u8, 30#u8, 40#u8, 50#u8, 60#u8, 70#u8, 80#u8]
  have hChunked : OkPost (postfork.child.write_all sChunked 4#i32 msg) fun p =>
      p.1 = .Ok () ∧ appendedBytesForDesc sChunked.writeLog p.2.writeLog 90 = msg.val := by
    refine okPost_mono (write_all_spec sChunked 4#i32 msg) ?_
    intro p hp
    simp only [WriteAllPost, show ¬ ((4#i32 : I32) < 0#i32) from by decide, ↓reduceIte] at hp
    have hRun : sChunked.status = Status.running := rfl
    simp only [hRun, ne_eq, not_true_eq_false, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hMatch⟩
    have hFd : sChunked.getFd (4#i32).val = some { desc := 90, cloexec := true } := rfl
    have hDesc : sChunked.getDesc 90 = .stream false true false [] := rfl
    rw [hFd] at hMatch
    dsimp only at hMatch
    rw [hDesc] at hMatch
    rcases hMatch with ⟨_, _, hCases, hNoFail⟩
    have hOk := hNoFail (by
      intro f hf
      dsimp only [sChunked] at hf
      simp only [List.length_nil, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact trivial | exact rfl)
    rcases hCases with hGoal | ⟨_, _, hErr, _⟩
    · exact hGoal
    · rw [hOk] at hErr; cases hErr
  have hMain : OkPost (postfork.child.write_all s0 fd0 pay0) fun p =>
      p.1 = .Ok () ∧ appendedBytesForDesc s0.writeLog p.2.writeLog 90 = pay0.val := by
    refine okPost_mono (write_all_spec s0 fd0 pay0) ?_
    intro p hp
    simp only [WriteAllPost, show ¬ (fd0 < 0#i32) from by decide, ↓reduceIte] at hp
    have hRun : s0.status = Status.running := rfl
    simp only [hRun, ne_eq, not_true_eq_false, ↓reduceIte] at hp
    rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hMatch⟩
    have hFd : s0.getFd fd0.val = some { desc := 90, cloexec := true } := rfl
    have hDesc : s0.getDesc 90 = .stream false true false [] := rfl
    rw [hFd] at hMatch
    dsimp only at hMatch
    rw [hDesc] at hMatch
    rcases hMatch with ⟨_, _, hCases, hNoFail⟩
    have hOk := hNoFail (by intro f hf; cases hf)
    rcases hCases with hGoal | ⟨_, _, hErr, _⟩
    · exact hGoal
    · rw [hOk] at hErr; cases hErr
  dsimp only [Core.CanReach, test_postfork_writeAll_eintrPartialWriteAndReassembly]
  refine ⟨s0, fd0, pay0, ?_, hChunked, ⟨rfl, rfl, by decide⟩, rfl, hMain, trivial⟩
  exact okPost_mono (write_all_spec s0 fd0 pay0) (fun _ _ => trivial)

end SpecPromises

end LeanSwe.PostFork.Proofs

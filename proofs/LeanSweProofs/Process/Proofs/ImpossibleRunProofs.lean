import LeanSweProofs.Process.Proofs.ImpossibleHelpers

/-!
`NeverErrorKindPure` and `NeverErrorKindIO` proofs for `validateRequest`, `run`, `runCommand`,
and `runCommandChecked` in `LeanSwe.Process`.
-/

namespace LeanSwe.Process.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

theorem awaitOsPhase_sat {fd : Type}
    (deps : SysDepsM IO fd) (eintrFuel ioFuel : Nat) (pid : UInt32)
    (inFd0? outFd0? errFd0? : Option fd) (stdin : ByteArray) (timeoutMs? maxOut? : Option Nat) :
    SatisfiesIO (exceptBasicPred (fun p => outcomePred timeoutMs? maxOut? p.2))
      (awaitOsPhase deps eintrFuel ioFuel pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOut?) := by
  unfold awaitOsPhase
  apply sat_seq; intro inFd?; apply sat_seq; intro _; apply sat_seq; intro _
  refine sat_bind (readStartMsOpt_sat deps.timeRand timeoutMs?) fun rs hrs => ?_
  cases rs with
  | error _ => apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure hrs
  | ok startMs =>
    refine sat_bind (streamPipesLoop_sat deps.files deps.poll deps.timeRand stdin startMs timeoutMs? maxOut? eintrFuel
      { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? } ioFuel) fun rsp hrsp => ?_
    cases rsp with
    | error _ => exact sat_pure hrsp
    | ok spOut =>
      cases spOut with
      | timedOut _ _ => exact sat_pure hrsp
      | limitExceeded _ _ => exact sat_pure hrsp
      | eof out err =>
        dsimp only
        cases timeoutMs? with
        | none =>
          dsimp only
          refine sat_bind (waitBlockingLoop_sat deps.proc pid.toInt32 out err eintrFuel) fun rwb hrwb => ?_
          cases rwb with
          | error _ => exact sat_pure hrwb
          | ok outcome =>
            cases outcome with
            | exited _ | signaled _ _ _ => exact sat_pure trivial
            | timedOut _ _ | outputLimitExceeded _ _ => exact False.elim hrwb
        | some timeoutMs =>
          dsimp only
          refine sat_mono (waitTimedLoop_sat deps.proc deps.timeRand pid.toInt32 startMs timeoutMs out err ioFuel) ?_
          intro rwt hrwt
          cases rwt with
          | error _ => exact hrwt
          | ok pair =>
            rcases pair with ⟨_, outcome⟩
            cases outcome with
            | exited _ | signaled _ _ _ => exact trivial
            | timedOut _ _ => exact fun hc => by cases hc
            | outputLimitExceeded _ _ => exact False.elim hrwt

theorem killGroupOsPhase_sat {fd : Type}
    (deps : SysDepsM IO fd) (eintrFuel : Nat) (pgid : UInt32) :
    SatisfiesIO (exceptBasicPred (fun _ => True)) (killGroupOsPhase deps eintrFuel pgid) := by
  unfold killGroupOsPhase; split
  · exact sat_pure trivial
  · apply sat_seq; intro r1
    cases r1 with
    | error e => dsimp only; split; exact sat_pure trivial; exact sat_pure (mapErrno_basic _ _ e)
    | ok _ =>
      apply sat_seq; intro _; split
      · exact sat_pure trivial
      · apply sat_seq; intro r2
        cases r2 with
        | error e => dsimp only; split; exact sat_pure trivial; exact sat_pure (mapErrno_basic _ _ e)
        | ok _ => exact sat_pure trivial

theorem reapOsPhase_sat {fd : Type}
    (deps : SysDepsM IO fd) (eintrFuel : Nat) (slot : ProcSlotM fd) :
    SatisfiesIO (exceptBasicPred (fun _ => True)) (reapOsPhase deps eintrFuel slot) := by
  unfold reapOsPhase
  apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
  split
  · apply sat_seq; intro r
    cases r with
    | ok _ => exact sat_pure trivial
    | error oe =>
      cases oe with
      | none => exact sat_pure (basic_io rfl)
      | some e => exact sat_pure (mapErrno_basic _ _ e)
  · exact sat_pure trivial

theorem validateSpawnRequest_err_is_invalidInput (req : SpawnRequest) (err : ProcessError)
    (h : Internal.validateSpawnRequest req = .error err) : err.kind = .invalidInput := by
  unfold Internal.validateSpawnRequest at h
  repeat (first | (rw [Except.error.injEq] at h; subst h; rfl) | (rw [Except.ok.injEq] at h; cases h) | split at h | cases h)

theorem validateRequest_err_is_invalidInput (req : ExecRequest) (err : ProcessError)
    (h : Internal.validateRequest req = .error err) : err.kind = .invalidInput := by
  unfold Internal.validateRequest at h
  cases hS : Internal.validateSpawnRequest req.toSpawnRequest with
  | error e => simp only [hS, Except.error.injEq] at h; subst h; exact validateSpawnRequest_err_is_invalidInput req.toSpawnRequest e hS
  | ok _ => simp only [hS] at h; split at h <;> first | (rw [Except.error.injEq] at h; subst h; rfl) | cases h

private theorem validateRequest_ok_limits {req norm : ExecRequest} (h : Internal.validateRequest req = .ok norm) :
    norm.timeoutMs = req.timeoutMs ∧ norm.maxOutputBytes = req.maxOutputBytes := by
  unfold Internal.validateRequest at h
  cases hS : Internal.validateSpawnRequest req.toSpawnRequest with
  | error _ => simp [hS] at h
  | ok _ => simp only [hS] at h; split at h <;> first | (rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩) | cases h

theorem spawnConc_sat (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState RawFd)) (fuel : Nat)
    (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', spawnConc sys Core.ioConcOps (Core.ioStateCell r) fuel req w = .ok res w' ∧
      basicErrOrOk res := by
  unfold spawnConc
  rcases ioConcOps_tryCatchMsg_sat (spawnOsPhase (sysDepsOfCaps sys) fuel req)
      (spawnOsPhase_sat sys fuel req) w with ⟨tr, w1, h1, htr⟩
  rw [imp_io_bind_ok _ _ _ h1]
  cases tr with
  | error msg => exact ⟨_, w1, rfl, mapCaughtMsg_basic (some req.program) msg⟩
  | ok osRes =>
    cases osRes with
    | error err => exact ⟨.error err, w1, rfl, htr⟩
    | ok slot =>
      dsimp only
      rcases ioStateCell_modifyGet_ok r (fun st => insertSlotPure st slot) w1 with ⟨hid, w2, h2⟩
      rw [imp_io_bind_ok _ _ _ h2]
      exact ⟨_, w2, rfl, trivial⟩

theorem awaitOutputConc_sat (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState RawFd)) (ef iof : Nat)
    (h : ProcessHandle) (stdin : ByteArray) (timeoutMs? maxOut? : Option Nat)
    (w : Void IO.RealWorld) :
    ∃ res w', awaitOutputConc sys Core.ioConcOps (Core.ioStateCell r) ef iof
        h stdin timeoutMs? maxOut? w = .ok res w' ∧
      exceptBasicPred (outcomePred timeoutMs? maxOut?) res := by
  unfold awaitOutputConc
  rcases ioStateCell_modifyGet_ok r (fun st => takeSlotIoPure st h.handleId) w with ⟨tk, w1, h1⟩
  rw [imp_io_bind_ok _ _ _ h1]
  cases tk with
  | none => exact ⟨_, w1, rfl, basic_io rfl⟩
  | some tup =>
    rcases tup with ⟨pid, inFd0?, outFd0?, errFd0?⟩
    dsimp only
    rcases ioConcOps_tryCatchMsg_sat
        (awaitOsPhase (sysDepsOfCaps sys) ef iof pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOut?)
        (awaitOsPhase_sat (sysDepsOfCaps sys) ef iof pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOut?) w1 with
      ⟨tr, w2, h2, htr⟩
    rw [imp_io_bind_ok _ _ _ h2]
    cases tr with
    | error msg => exact ⟨_, w2, rfl, mapCaughtMsg_basic none msg⟩
    | ok osRes =>
      cases osRes with
      | error err => exact ⟨.error err, w2, rfl, htr⟩
      | ok pair =>
        rcases pair with ⟨waitedFlag, outcome⟩
        dsimp only
        rcases ioStateCell_modifyGet_ok r (fun st => markWaitedPure st h.handleId waitedFlag) w2 with
          ⟨okFlag, w3, h3⟩
        rw [imp_io_bind_ok _ _ _ h3]
        cases okFlag with
        | false => exact ⟨_, w3, rfl, basic_io rfl⟩
        | true => exact ⟨.ok outcome, w3, rfl, htr⟩

theorem killProcessGroupConc_sat (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState RawFd)) (ef : Nat)
    (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', killProcessGroupConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = .ok res w' ∧
      basicErrOrOk res := by
  unfold killProcessGroupConc
  rcases ioStateCell_get_ok r w with ⟨st, w1, h1⟩
  rw [imp_io_bind_ok _ _ _ h1]
  cases (findSlotPure h.handleId st.slots).map (·.pgid) with
  | none => exact ⟨.ok (), w1, rfl, trivial⟩
  | some pgid =>
    dsimp only
    rcases ioConcOps_tryCatchMsg_sat (killGroupOsPhase (sysDepsOfCaps sys) ef pgid)
        (killGroupOsPhase_sat (sysDepsOfCaps sys) ef pgid) w1 with ⟨tr, w2, h2, htr⟩
    rw [imp_io_bind_ok _ _ _ h2]
    cases tr with
    | error msg => exact ⟨_, w2, rfl, mapCaughtMsg_basic none msg⟩
    | ok osRes => cases osRes <;> exact ⟨_, w2, rfl, htr⟩

theorem reapConc_sat (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState RawFd)) (ef : Nat)
    (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', reapConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = .ok res w' ∧
      basicErrOrOk res := by
  unfold reapConc
  rcases ioStateCell_modifyGet_ok r (fun st => detachSlotPure st h.handleId) w with ⟨det, w1, h1⟩
  rw [imp_io_bind_ok _ _ _ h1]
  cases det with
  | none => exact ⟨.ok (), w1, rfl, trivial⟩
  | some slot =>
    dsimp only
    rcases ioConcOps_tryCatchMsg_sat (reapOsPhase (sysDepsOfCaps sys) ef slot)
        (reapOsPhase_sat (sysDepsOfCaps sys) ef slot) w1 with ⟨tr, w2, h2, htr⟩
    rw [imp_io_bind_ok _ _ _ h2]
    cases tr with
    | error msg => exact ⟨_, w2, rfl, mapCaughtMsg_basic none msg⟩
    | ok osRes => cases osRes <;> exact ⟨_, w2, rfl, htr⟩

private theorem mkFullRawOps_run_inv (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState RawFd))
    (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', Internal.run (mkFullRawOpsM sys Core.ioConcOps (Core.ioStateCell r)) req w = .ok res w' ∧
      match res with
      | .ok _ => True
      | .error e =>
        e.kind ≠ .nonZeroExit ∧
        (req.timeoutMs = none → e.kind ≠ .timedOut) ∧
        (req.maxOutputBytes = none → e.kind ≠ .outputLimitExceeded) := by
  unfold Internal.run mkFullRawOpsM
  cases hVal : Internal.validateRequest req with
  | error err =>
    have hk := validateRequest_err_is_invalidInput req err hVal
    refine ⟨.error err, w, rfl, ?_⟩
    dsimp only; rw [hk]
    exact ⟨by decide, fun _ => by decide, fun _ => by decide⟩
  | ok norm =>
    have hlim := validateRequest_ok_limits hVal
    dsimp only
    rcases spawnConc_sat sys r _ norm w with ⟨rSpawn, w1, hSpawn, hSpawnInv⟩
    rw [imp_io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error err =>
      have hb := ensureNonEmptyMsg_basic "process spawn failed" hSpawnInv
      exact ⟨_, w1, rfl, ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩⟩
    | ok h =>
      dsimp only
      rcases awaitOutputConc_sat sys r _ _ h norm.stdin norm.timeoutMs norm.maxOutputBytes w1 with
        ⟨rAwait, w2, hAwait, hAwaitInv⟩
      rw [imp_io_bind_ok _ _ _ hAwait]
      cases rAwait with
      | error err =>
        dsimp only
        rcases killProcessGroupConc_sat sys r _ h w2 with ⟨_, w3, hKill, _⟩
        rw [imp_io_bind_ok _ _ _ hKill]
        rcases reapConc_sat sys r _ h w3 with ⟨_, w4, hReap, _⟩
        rw [imp_io_bind_ok _ _ _ hReap]
        have hb := ensureNonEmptyMsg_basic "process I/O failed" hAwaitInv
        exact ⟨_, w4, rfl, ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩⟩
      | ok outcome =>
        cases outcome with
        | exited res =>
          dsimp only
          rcases reapConc_sat sys r _ h w2 with ⟨rReap, w3, hReap, hReapInv⟩
          rw [imp_io_bind_ok _ _ _ hReap]
          cases rReap with
          | error err =>
            have hb := ensureNonEmptyMsg_basic "process reap failed" hReapInv
            exact ⟨_, w3, rfl, ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩⟩
          | ok _ => exact ⟨.ok res, w3, rfl, trivial⟩
        | signaled _ _ _ =>
          dsimp only
          rcases killProcessGroupConc_sat sys r _ h w2 with ⟨_, w3, hKill, _⟩
          rw [imp_io_bind_ok _ _ _ hKill]
          rcases reapConc_sat sys r _ h w3 with ⟨_, w4, hReap, _⟩
          rw [imp_io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun _ hc => by cases hc), (fun _ hc => by cases hc)⟩⟩
        | timedOut _ _ =>
          dsimp only
          rcases killProcessGroupConc_sat sys r _ h w2 with ⟨_, w3, hKill, _⟩
          rw [imp_io_bind_ok _ _ _ hKill]
          rcases reapConc_sat sys r _ h w3 with ⟨_, w4, hReap, _⟩
          rw [imp_io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun hnone => False.elim (hAwaitInv (hlim.1.trans hnone))), (fun _ hc => by cases hc)⟩⟩
        | outputLimitExceeded _ _ =>
          dsimp only
          rcases killProcessGroupConc_sat sys r _ h w2 with ⟨_, w3, hKill, _⟩
          rw [imp_io_bind_ok _ _ _ hKill]
          rcases reapConc_sat sys r _ h w3 with ⟨_, w4, hReap, _⟩
          rw [imp_io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun _ hc => by cases hc), (fun hnone => False.elim (hAwaitInv (hlim.2.trans hnone)))⟩⟩

private theorem validateRequest_never_kind (kind : ProcessErrorKind) (hne : .invalidInput ≠ kind)
    (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind kind (LeanSwe.Process.validateRequest req) := by
  unfold Core.NeverErrorKindPure LeanSwe.Process.validateRequest defaultApi Internal.mkFullApiM
  dsimp only
  cases h : Internal.validateRequest req with
  | ok _ => exact trivial
  | error e => dsimp only; rw [validateRequest_err_is_invalidInput req e h]; exact hne

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.notFound`. -/
theorem process_validateRequest_never_notFound (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .notFound (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .notFound (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.permissionDenied`. -/
theorem process_validateRequest_never_permissionDenied (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .permissionDenied (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .permissionDenied (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.timedOut`. -/
theorem process_validateRequest_never_timedOut (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .timedOut (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .timedOut (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.outputLimitExceeded`. -/
theorem process_validateRequest_never_outputLimitExceeded (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .outputLimitExceeded (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .outputLimitExceeded (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.terminatedBySignal`. -/
theorem process_validateRequest_never_terminatedBySignal (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .terminatedBySignal (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .terminatedBySignal (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.nonZeroExit`. -/
theorem process_validateRequest_never_nonZeroExit (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .nonZeroExit (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .nonZeroExit (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.ioError`. -/
theorem process_validateRequest_never_ioError (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .ioError (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .ioError (by decide) req

/-- `Process.run` returns non-zero exit codes inside `ExecResult`, so it never fails with `.nonZeroExit`. -/
theorem process_run_never_nonZeroExit (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.run req) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.run defaultApi Internal.mkFullApiM
  dsimp only
  rcases mkFullRawOps_run_inv _ _ req w with ⟨r, _, hrun, hinv⟩
  rw [hrun]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.runCommand` configures `timeoutMs := none`, so it never fails with `.timedOut`. -/
theorem process_runCommand_never_timedOut (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkFullApiM Internal.mkCommandRequest
  dsimp only
  rcases mkFullRawOps_run_inv _ _ { program := program, args := args } w with ⟨r, _, hrun, hinv⟩
  rw [hrun]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1 rfl

/-- `Process.runCommand` configures `maxOutputBytes := none`, so it never fails with `.outputLimitExceeded`. -/
theorem process_runCommand_never_outputLimitExceeded (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkFullApiM Internal.mkCommandRequest
  dsimp only
  rcases mkFullRawOps_run_inv _ _ { program := program, args := args } w with ⟨r, _, hrun, hinv⟩
  rw [hrun]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2 rfl

/-- `Process.runCommand` delegates to `Process.run`, so it never fails with `.nonZeroExit`. -/
theorem process_runCommand_never_nonZeroExit (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit
      (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkFullApiM Internal.mkCommandRequest
  dsimp only
  rcases mkFullRawOps_run_inv _ _ { program := program, args := args } w with ⟨r, _, hrun, hinv⟩
  rw [hrun]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.runCommandChecked` configures `timeoutMs := none`, so it never fails with `.timedOut`. -/
theorem process_runCommandChecked_never_timedOut (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut
      (LeanSwe.Process.runCommandChecked program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommandChecked defaultApi Internal.mkFullApiM
    Internal.mkCommandRequest Internal.runChecked
  dsimp only
  rcases mkFullRawOps_run_inv _ _ { program := program, args := args } w with ⟨r, _, hrun, hinv⟩
  rw [imp_io_bind_ok _ _ _ hrun]
  cases r with
  | error _ => exact hinv.2.1 rfl
  | ok res =>
    dsimp only
    cases (res.exitCode == 0) with
    | true => exact trivial
    | false => show ProcessErrorKind.nonZeroExit ≠ ProcessErrorKind.timedOut; decide

/-- `Process.runCommandChecked` configures `maxOutputBytes := none`, so it never fails with `.outputLimitExceeded`. -/
theorem process_runCommandChecked_never_outputLimitExceeded (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.runCommandChecked program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommandChecked defaultApi Internal.mkFullApiM
    Internal.mkCommandRequest Internal.runChecked
  dsimp only
  rcases mkFullRawOps_run_inv _ _ { program := program, args := args } w with ⟨r, _, hrun, hinv⟩
  rw [imp_io_bind_ok _ _ _ hrun]
  cases r with
  | error _ => exact hinv.2.2 rfl
  | ok res =>
    dsimp only
    cases (res.exitCode == 0) with
    | true => exact trivial
    | false => show ProcessErrorKind.nonZeroExit ≠ ProcessErrorKind.outputLimitExceeded; decide

end LeanSwe.Process.Proofs

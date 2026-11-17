import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.SpecTests
import LeanSwe.ProcessSandbox.Proofs.SeccompBytesLemma
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core Core.NondetTest LeanSwe.ProcessSandbox.Model

private theorem mock_ioBracket_none (bh : BoxHandle) (stdin : ByteArray) (timeoutMs : Nat)
    (maxOut? : Option Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hActive : s.activeBoxes.contains bh.handleId = true) :
    ((do
      let (ioRes, _) ← tryFinally'
        (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?)
        (fun _ => pure ())
      match ioRes with
      | .error e => return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
      | .ok out => return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
      (match mockReadResult s.scriptedOutput maxOut? with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         guestExecCalls := s.guestExecCalls + 1
         lastReadStdin := some stdin
         lastReadTimeoutMs := some timeoutMs }) := by
  rw [stateM_bind_apply, stateM_tryFinally'_apply,
    mockRawOps_readBoxOutput_eq bh stdin timeoutMs maxOut? s hValid hActive]
  dsimp only [Pure.pure, StateT.pure]
  cases mockReadResult s.scriptedOutput maxOut? <;> rfl

private theorem mock_ioBracket_some (bh : BoxHandle) (fh : PortForwarderHandle)
    (stdin : ByteArray) (timeoutMs : Nat) (maxOut? : Option Nat) (s : MockSandboxState)
    (baseFwds : List (Nat × Nat))
    (hBhValid : isValidSandboxHandleId bh.handleId = true)
    (hBhActive : s.activeBoxes.contains bh.handleId = true)
    (hFhValid : isValidSandboxHandleId fh.handleId = true)
    (hFwdsEq : s.activeForwarders = (fh.handleId, fh.boxHandleId) :: baseFwds) :
    ((do
      let (ioRes, _) ← tryFinally'
        (mockRawOps.readBoxOutput bh stdin timeoutMs maxOut?)
        (fun _ => do
          let _ ← mockRawOps.stopPortForwarders fh
          pure ())
      match ioRes with
      | .error e => return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
      | .ok out => return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
      (match mockReadResult s.scriptedOutput maxOut? with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         activeForwarders := baseFwds
         guestExecCalls := s.guestExecCalls + 1
         lastReadStdin := some stdin
         lastReadTimeoutMs := some timeoutMs }) := by
  rw [stateM_bind_apply, stateM_tryFinally'_apply,
    mockRawOps_readBoxOutput_eq bh stdin timeoutMs maxOut? s hBhValid hBhActive]
  dsimp only
  have hStop :
      (mockRawOps.stopPortForwarders fh)
        { s with
          guestExecCalls := s.guestExecCalls + 1
          lastReadStdin := some stdin
          lastReadTimeoutMs := some timeoutMs } =
        (.ok (),
          { s with
            activeForwarders := baseFwds
            guestExecCalls := s.guestExecCalls + 1
            lastReadStdin := some stdin
            lastReadTimeoutMs := some timeoutMs }) := by
    dsimp only [mockRawOps]
    have hAny : s.activeForwarders.any (fun p => p.1 == fh.handleId) = true := by
      rw [hFwdsEq]; simp
    have hBad : (!isValidSandboxHandleId fh.handleId ||
        !s.activeForwarders.any (fun p => p.1 == fh.handleId)) = false := by
      rw [hFhValid, hAny]; rfl
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hEr : eraseFirstForwarder fh.handleId s.activeForwarders = baseFwds := by
      rw [hFwdsEq]; simp [eraseFirstForwarder]
    rw [hEr]
  rw [stateM_bind_apply, hStop]
  dsimp only [Pure.pure, StateT.pure]
  cases mockReadResult s.scriptedOutput maxOut? <;> rfl

private theorem mock_boxKillReap (bh : BoxHandle) (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes) :
    (do
      let _ ← mockRawOps.killProcessGroup bh
      let _ ← mockRawOps.pidfdKill bh
      let _ ← mockRawOps.reapBox bh
      pure ()) s =
      ((),
       { s with
         activeBoxes := baseBoxes
         killPgCalls := s.killPgCalls + 1
         pidfdKillCalls := s.pidfdKillCalls + 1
         reapCalls := s.reapCalls + 1 }) := by
  have hMem : s.activeBoxes.contains bh.handleId = true := by
    rw [hBoxesEq]; simp
  have hBad : (!isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId) = false := by
    rw [hValid, hMem]; rfl
  have hK : (mockRawOps.killProcessGroup bh) s =
      (.ok (), { s with killPgCalls := s.killPgCalls + 1 }) := by
    dsimp only [mockRawOps]; simp only [hBad, Bool.false_eq_true, ↓reduceIte]
  have hP : (mockRawOps.pidfdKill bh) { s with killPgCalls := s.killPgCalls + 1 } =
      (.ok (), { s with killPgCalls := s.killPgCalls + 1, pidfdKillCalls := s.pidfdKillCalls + 1 }) := by
    dsimp only [mockRawOps]; simp only [hBad, Bool.false_eq_true, ↓reduceIte]
  have hR : (mockRawOps.reapBox bh)
      { s with killPgCalls := s.killPgCalls + 1, pidfdKillCalls := s.pidfdKillCalls + 1 } =
      (.ok (),
        { s with
          activeBoxes := baseBoxes
          killPgCalls := s.killPgCalls + 1
          pidfdKillCalls := s.pidfdKillCalls + 1
          reapCalls := s.reapCalls + 1 }) := by
    dsimp only [mockRawOps]
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hEr : s.activeBoxes.erase bh.handleId = baseBoxes := by
      rw [hBoxesEq]; simp [List.erase]
    rw [hEr]
  rw [stateM_bind_apply, hK]
  dsimp only
  rw [stateM_bind_apply, hP]
  dsimp only
  rw [stateM_bind_apply, hR]
  rfl

/-- Inner box bracket action for `Internal.runGeneric` over `mockRawOps`. -/
def mockBoxBracket (bh : BoxHandle) (valid : ValidBoxSpec) :
    StateM MockSandboxState (Except SandboxError SandboxResult) := do
  let (boxRes, _) ← tryFinally' (do
    let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
      if valid.portForwards.isEmpty then
        pure (.ok none)
      else do
        match ← mockRawOps.startPortForwarders bh valid.portForwards with
        | .error e =>
          pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
        | .ok fh =>
          pure (.ok (some fh))
    match fwdRes with
    | .error e => return .error e
    | .ok fwdOpt =>
      let (ioRes, _) ← tryFinally'
        (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
        (fun _ =>
          match fwdOpt with
          | some fh => do
            let _ ← mockRawOps.stopPortForwarders fh
            pure ()
          | none => pure ())
      match ioRes with
      | .error e =>
        return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
      | .ok out =>
        return .ok out
  ) (fun _ => do
    let _ ← mockRawOps.killProcessGroup bh
    let _ ← mockRawOps.pidfdKill bh
    let _ ← mockRawOps.reapBox bh
    pure ())
  return boxRes

/-- Symbolic `StateM` evaluation of the inner box bracket when no port forwarders are configured. -/
theorem mock_boxBracket_none (bh : BoxHandle) (valid : ValidBoxSpec)
    (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes)
    (hEmpty : valid.portForwards.isEmpty = true) :
    mockBoxBracket bh valid s =
      (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
       | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
       | .ok out => .ok out,
       { s with
         activeBoxes := baseBoxes
         lastReadStdin := some valid.stdin
         lastReadTimeoutMs := some valid.limits.timeoutMs
         guestExecCalls := s.guestExecCalls + 1
         killPgCalls := s.killPgCalls + 1
         pidfdKillCalls := s.pidfdKillCalls + 1
         reapCalls := s.reapCalls + 1 }) := by
  unfold mockBoxBracket
  have hActive : s.activeBoxes.contains bh.handleId = true := by rw [hBoxesEq]; simp
  have hIo := mock_ioBracket_none bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes s hValid hActive
  let sIo :=
    { s with
      guestExecCalls := s.guestExecCalls + 1
      lastReadStdin := some valid.stdin
      lastReadTimeoutMs := some valid.limits.timeoutMs }
  have hKill := mock_boxKillReap bh baseBoxes sIo hValid (by simp [sIo, hBoxesEq])
  have hBody :
      ((do
        let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
          if valid.portForwards.isEmpty then
            pure (.ok none)
          else do
            match ← mockRawOps.startPortForwarders bh valid.portForwards with
            | .error e =>
              pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
            | .ok fh =>
              pure (.ok (some fh))
        match fwdRes with
        | .error e => return .error e
        | .ok fwdOpt =>
          let (ioRes, _) ← tryFinally'
            (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
            (fun _ =>
              match fwdOpt with
              | some fh => do
                let _ ← mockRawOps.stopPortForwarders fh
                pure ()
              | none => pure ())
          match ioRes with
          | .error e =>
            return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
          | .ok out =>
            return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
        (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out, sIo) := by
    simp only [hEmpty, ↓reduceIte]
    rw [stateM_bind_eq (x := pure (Except.ok none)) rfl]
    dsimp only
    exact hIo
  exact stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)

/-- Symbolic `StateM` evaluation of the inner box bracket when port forwarders are configured. -/
theorem mock_boxBracket_fwd (bh : BoxHandle) (valid : ValidBoxSpec)
    (baseBoxes : List Nat) (s : MockSandboxState)
    (hValid : isValidSandboxHandleId bh.handleId = true)
    (hBoxesEq : s.activeBoxes = bh.handleId :: baseBoxes)
    (hNotEmpty : valid.portForwards.isEmpty = false) :
    match s.failForwarderStartWith with
    | some ferr =>
      let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
        { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
      mockBoxBracket bh valid s =
        (.error err',
         { s with
           activeBoxes := baseBoxes
           lastStartedForwards := some valid.portForwards
           killPgCalls := s.killPgCalls + 1
           pidfdKillCalls := s.pidfdKillCalls + 1
           reapCalls := s.reapCalls + 1 })
    | none =>
      let sStart := { s with lastStartedForwards := some valid.portForwards }
      let idFwd := allocMockHandleId sStart
      mockBoxBracket bh valid s =
        (match mockReadResult s.scriptedOutput valid.limits.maxOutputBytes with
         | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
         | .ok out => .ok out,
         { s with
           nextHandleId := idFwd + 1
           activeBoxes := baseBoxes
           lastStartedForwards := some valid.portForwards
           lastReadStdin := some valid.stdin
           lastReadTimeoutMs := some valid.limits.timeoutMs
           guestExecCalls := s.guestExecCalls + 1
           killPgCalls := s.killPgCalls + 1
           pidfdKillCalls := s.pidfdKillCalls + 1
           reapCalls := s.reapCalls + 1 }) := by
  unfold mockBoxBracket
  have hActive : s.activeBoxes.contains bh.handleId = true := by rw [hBoxesEq]; simp
  have hBad : (!isValidSandboxHandleId bh.handleId || !s.activeBoxes.contains bh.handleId) = false := by
    rw [hValid, hActive]; rfl
  cases hFail : s.failForwarderStartWith with
  | some ferr =>
    dsimp only
    have hStart : (mockRawOps.startPortForwarders bh valid.portForwards) s =
        (.error { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message },
         { s with lastStartedForwards := some valid.portForwards }) := by
      dsimp only [mockRawOps]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      rw [hFail]
    let sStart := { s with lastStartedForwards := some valid.portForwards }
    have hKill := mock_boxKillReap bh baseBoxes sStart hValid (by simp [sStart, hBoxesEq])
    let err' := Internal.ensureNonEmptyMsg "failed to start port forwarders"
      { ferr with message := if ferr.message.isEmpty then "forwarder start failed" else ferr.message }
    have hBody :
        ((do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
          (.error err', sStart) := by
      simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_eq hStart]
      dsimp only
      rw [stateM_bind_eq (x := pure (Except.error _)) rfl]
      rfl
    rw [stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)]
    dsimp only [Pure.pure, StateT.pure, sStart]
    rw [hFail]
  | none =>
    dsimp only
    let sStart := { s with lastStartedForwards := some valid.portForwards }
    let idFwd := allocMockHandleId sStart
    let fh : PortForwarderHandle := { handleId := idFwd, boxHandleId := bh.handleId }
    let sFwd := { sStart with nextHandleId := idFwd + 1, activeForwarders := (idFwd, bh.handleId) :: s.activeForwarders }
    have hFhValid : isValidSandboxHandleId idFwd = true := isValidSandboxHandleId_alloc sStart
    have hStart : (mockRawOps.startPortForwarders bh valid.portForwards) s = (.ok fh, sFwd) := by
      dsimp only [mockRawOps]
      simp only [hBad, Bool.false_eq_true, ↓reduceIte]
      dsimp only [sStart, idFwd, fh, sFwd]
      rw [hFail]
    have hActiveFwd : sFwd.activeBoxes.contains bh.handleId = true := by simp [sFwd, sStart, hBoxesEq]
    have hIo := mock_ioBracket_some bh fh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes
      sFwd s.activeForwarders hValid hActiveFwd hFhValid rfl
    let sIo :=
      { sFwd with
        activeForwarders := s.activeForwarders
        guestExecCalls := s.guestExecCalls + 1
        lastReadStdin := some valid.stdin
        lastReadTimeoutMs := some valid.limits.timeoutMs }
    have hKill := mock_boxKillReap bh baseBoxes sIo hValid (by simp [sIo, sFwd, sStart, hBoxesEq])
    have hBody :
        ((do
          let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
            if valid.portForwards.isEmpty then
              pure (.ok none)
            else do
              match ← mockRawOps.startPortForwarders bh valid.portForwards with
              | .error e =>
                pure (.error (Internal.ensureNonEmptyMsg "failed to start port forwarders" e))
              | .ok fh =>
                pure (.ok (some fh))
          match fwdRes with
          | .error e => return .error e
          | .ok fwdOpt =>
            let (ioRes, _) ← tryFinally'
              (mockRawOps.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
              (fun _ =>
                match fwdOpt with
                | some fh => do
                  let _ ← mockRawOps.stopPortForwarders fh
                  pure ()
                | none => pure ())
            match ioRes with
            | .error e =>
              return .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
            | .ok out =>
              return .ok out) : StateM MockSandboxState (Except SandboxError SandboxResult)) s =
          (match mockReadResult sFwd.scriptedOutput valid.limits.maxOutputBytes with
           | .error e => .error (Internal.ensureNonEmptyMsg "sandbox I/O failed" e)
           | .ok out => .ok out, sIo) := by
      simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_eq hStart]
      dsimp only
      rw [stateM_bind_eq (x := pure (Except.ok (some fh))) rfl]
      dsimp only
      exact hIo
    rw [stateM_bind_eq (stateM_tryFinally'_eq hBody hKill)]
    dsimp only [Pure.pure, StateT.pure, sIo, sFwd, sStart, idFwd]
    rw [hFail]

end LeanSwe.ProcessSandbox.Proofs

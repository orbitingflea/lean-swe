import LeanSwe.ConnectProxy.Model.HealthySys

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

/-!
Non-vacuity healthy OS world witness `sampleHealthySys` inhabiting `RefinesHealthyCProxySys`
(used to discharge `Core.CanReach` for all `RefinesHealthyCProxySys` promises and `SpecMutants`).
-/

private def liftFilesOp {α : Type} (act : StateM Files.FilesState α) :
    StateM HealthySysWorld α := fun w =>
  let (r, s') := act.run w.filesEnv.state
  (r, { w with filesEnv := { w.filesEnv with state := s' } })

/-- Sample `FilesOpsM` lifting `Files.modelOps` onto `HealthySysWorld.filesEnv`. -/
def sampleHealthyFilesOps : Files.FilesOpsM (StateM HealthySysWorld) Nat :=
  { openat := fun d p fl m => liftFilesOp (Files.modelOps.openat d p fl m)
    openat2 := fun d p how => liftFilesOp (Files.modelOps.openat2 d p how)
    close := fun h => liftFilesOp (Files.modelOps.close h)
    read := fun h n => liftFilesOp (Files.modelOps.read h n)
    write := fun h bs => liftFilesOp (Files.modelOps.write h bs)
    fstat := fun h => liftFilesOp (Files.modelOps.fstat h)
    fstatat := fun d p fl => liftFilesOp (Files.modelOps.fstatat d p fl)
    faccessat := fun d p m fl => liftFilesOp (Files.modelOps.faccessat d p m fl)
    mkdirat := fun d p m => liftFilesOp (Files.modelOps.mkdirat d p m)
    unlinkat := fun d p rd => liftFilesOp (Files.modelOps.unlinkat d p rd)
    renameat2 := fun od op nd np fl => liftFilesOp (Files.modelOps.renameat2 od op nd np fl)
    symlinkat := fun t d lp => liftFilesOp (Files.modelOps.symlinkat t d lp)
    readlinkat := fun d p c => liftFilesOp (Files.modelOps.readlinkat d p c)
    getdents64 := fun h c => liftFilesOp (Files.modelOps.getdents64 h c)
    fchmodat := fun d p m => liftFilesOp (Files.modelOps.fchmodat d p m)
    fchmod := fun h m => liftFilesOp (Files.modelOps.fchmod h m)
    flock := fun h op => liftFilesOp (Files.modelOps.flock h op)
    fcntl := fun h cmd => liftFilesOp (Files.modelOps.fcntl h cmd)
    fsync := fun h => liftFilesOp (Files.modelOps.fsync h)
    getcwd := fun c => liftFilesOp (Files.modelOps.getcwd c)
    lseek := fun h off wh => liftFilesOp (Files.modelOps.lseek h off wh)
    reopenReadOnly := fun h => liftFilesOp (Files.modelOps.reopenReadOnly h)
    dupStdio := fun sl => liftFilesOp (Files.modelOps.dupStdio sl) }

/-- Internal ConnectProxy proof helper `sampleHealthyFilesOps_close`. -/
theorem sampleHealthyFilesOps_close (w : HealthySysWorld) (h : Nat)
    (hWf : w.filesEnv.wf = true) :
    let (r, w') := (sampleHealthyFilesOps.close h).run w
    Files.healthyStep w.filesEnv (.close h) (Files.outcomeOfUnit r) = some w'.filesEnv ∧
    w'.filesEnv.wf = true := by
  have hNotWf : (!w.filesEnv.wf) = false := by simp [hWf]
  unfold Files.outcomeOfUnit Files.healthyStep Files.isCriticalFault Errno.isCriticalOsErrno
    Files.isCloseEbusy Files.allowedStep Files.allowedCloseStep Files.verifyStep
    Files.isOutcomeErr Files.isEintrOutcome
  dsimp only [sampleHealthyFilesOps, liftFilesOp, Files.modelOps, Files.runOp, Files.evalModel,
    Files.evalReq, Files.precheckNul, StateT.run, bind, StateT.bind, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run]
  rw [hNotWf]
  cases hGet : Files.assocGet w.filesEnv.state.fds h with
  | none =>
    exact ⟨rfl, hWf⟩
  | some desc =>
    have hWfNext : ({ w.filesEnv with state := Files.closeDescInState w.filesEnv.state h desc }).wf = true := by
      unfold Files.HealthyEnv.wf at hWf ⊢
      unfold Files.closeDescInState
      exact hWf
    exact ⟨rfl, hWfNext⟩

/-- Chosen non-critical, non-`EINTR`, non-`soError` fallback errno (`ENOSPC` or `ENOBUFS`). -/
def chosenSockFallbackErrno (soErr : Errno) : Errno :=
  if soErr == Errno.ENOSPC then Errno.ENOBUFS else Errno.ENOSPC

/-- Everyday non-critical, non-`EINTR` fallback errno accepted by `Net.healthyStep` on any `NetState`. -/
def fallbackNetErrno (s : Net.NetState) (req : Net.NetReq) : Errno :=
  match Net.preCheckNet req with
  | some err => err
  | none =>
    let sockErr (hid : Nat) : Errno :=
      match Net.lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        match Net.lookupFileSocket s fid with
        | .error fdErr => fdErr
        | .ok d => chosenSockFallbackErrno d.soError
    match req with
    | .socket .. | .socketpair .. => Errno.ENOSPC
    | .sendmsg hid fds =>
      match Net.lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        if !fds.toList.all (Net.isLiveHandle s) then Errno.EBADF
        else
          match Net.lookupFileSocket s fid with
          | .error fdErr => fdErr
          | .ok d => chosenSockFallbackErrno d.soError
    | .ioctl hid _ _ =>
      match Net.lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        match Net.lookupFileSocket s fid with
        | .error fdErr => if fdErr == Errno.ENOTSOCK then Errno.ENOTTY else fdErr
        | .ok _ => Errno.ENOSPC
    | .bind hid _ | .listen hid _ | .accept4 hid _ | .connect hid _
    | .getsockopt hid _ | .setsockopt hid _ _ | .getsockname hid
    | .recvfrom hid _ _ | .sendto hid _ _ | .shutdown hid _
    | .recvmsg hid _ => sockErr hid

/-- Internal ConnectProxy proof helper `preCheckNet_safe`. -/
theorem preCheckNet_safe (req : Net.NetReq) (err : Errno)
    (h : Net.preCheckNet req = some err) :
    Errno.isCriticalOsErrno err = false ∧ (err == Errno.EINTR) = false := by
  unfold Net.preCheckNet Net.validateSocketArgs Net.validateSocketpairArgs at h
  cases req <;> simp only at h
  all_goals
    repeat (first
      | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
      | split at h
      | cases h)

/-- Internal ConnectProxy proof helper `lookupFileSocket_err_safe`. -/
theorem lookupFileSocket_err_safe (s : Net.NetState) (fid : Net.FileId) (e : Errno)
    (h : Net.lookupFileSocket s fid = .error e) :
    e = Errno.EBADF ∨ e = Errno.ENOTSOCK := by
  unfold Net.lookupFileSocket at h
  cases hGet : Net.assocGet s.files fid with
  | none =>
    rw [hGet] at h
    injection h with hEq
    exact Or.inl hEq.symm
  | some ent =>
    rw [hGet] at h
    cases ent with
    | socket _ => cases h
    | nonSocket =>
      injection h with hEq
      exact Or.inr hEq.symm

/-- Internal ConnectProxy proof helper `chosen_cases`. -/
theorem chosen_cases (soErr : Errno) :
    (chosenSockFallbackErrno soErr = Errno.ENOSPC ∨ chosenSockFallbackErrno soErr = Errno.ENOBUFS) ∧
    (chosenSockFallbackErrno soErr == soErr) = false ∧
    Errno.isCriticalOsErrno (chosenSockFallbackErrno soErr) = false ∧
    (chosenSockFallbackErrno soErr == Errno.EINTR) = false := by
  unfold chosenSockFallbackErrno
  by_cases h : (soErr == Errno.ENOSPC) = true
  · have hEq : soErr = Errno.ENOSPC := beq_iff_eq.mp h
    subst hEq
    exact ⟨Or.inr (by decide), by decide, by decide, by decide⟩
  · have hF : (soErr == Errno.ENOSPC) = false := Bool.eq_false_iff.mpr h
    have hCh : (if soErr == Errno.ENOSPC then Errno.ENOBUFS else Errno.ENOSPC) = Errno.ENOSPC := by
      simp [hF]
    rw [hCh]
    have hSym : (Errno.ENOSPC == soErr) = false :=
      Bool.eq_false_iff.mpr (fun hs => h (beq_iff_eq.mpr (beq_iff_eq.mp hs).symm))
    exact ⟨Or.inl rfl, hSym, by decide, by decide⟩

/-- Internal ConnectProxy proof helper `asyncConnect_false_of_chosen`. -/
theorem asyncConnect_false_of_chosen (d : Net.SockDesc) (pendErr e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNe : (e == pendErr) = false) :
    Net.isAsyncConnectErrno pendErr e d = false := by
  unfold Net.isAsyncConnectErrno
  have hNotCr : (e == Errno.ECONNRESET) = false := by
    rcases hSpc with rfl | rfl <;> decide
  have hRest : (e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT ||
      e == Errno.ENETUNREACH || e == Errno.EHOSTUNREACH) = false := by
    rcases hSpc with rfl | rfl <;> decide
  rw [hNe, Bool.false_or]
  cases d.proto <;> simp [hNotCr, hRest]

/-- Internal ConnectProxy proof helper `consumePending_eq_soError`. -/
theorem consumePending_eq_soError (d : Net.SockDesc) (pendErr : Errno) (dClr : Net.SockDesc)
    (h : Net.consumePendingSoError d = some (pendErr, dClr)) :
    pendErr = d.soError := by
  unfold Net.consumePendingSoError at h
  by_cases h0 : (d.soError == 0) = true
  · simp [h0] at h
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    injection h with hPair
    exact (congrArg Prod.fst hPair).symm

/-- Internal ConnectProxy proof helper `consumeRecvPending_eq_soError`. -/
theorem consumeRecvPending_eq_soError (d : Net.SockDesc) (pendErr : Errno) (dClr : Net.SockDesc)
    (h : Net.consumeRecvPendingSoError d = some (pendErr, dClr)) :
    pendErr = d.soError := by
  unfold Net.consumeRecvPendingSoError at h
  by_cases h1 : d.proto.isListening = true
  · simp [h1] at h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    have hPeerShut : ∀ b : Bool,
        (if (b && d.soError == Errno.EPIPE) = true then none else Net.consumePendingSoError d) =
          some (pendErr, dClr) →
        pendErr = d.soError := by
      intro b
      cases b <;> cases (d.soError == Errno.EPIPE) <;> intro hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · cases hb
    exact hPeerShut _ h

/-- Internal ConnectProxy proof helper `emitUnit_spc`. -/
theorem emitUnit_spc (sBase sOk : Net.NetState) (e : Errno)
    (alts : List Errno) (onAlt : Errno → Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitUnit (some (.err e)) sBase sOk alts onAlt true = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (Net.NetOutcome.err e, onAlt e)
          else if (true && Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- Internal ConnectProxy proof helper `emitU32_spc`. -/
theorem emitU32_spc (sBase sOk : Net.NetState) (e : Errno) (c : UInt32)
    (alts : List Errno) (z : Bool) (onAlt : Errno → Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitU32 (some (.err e)) sBase c sOk alts z onAlt true = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (Net.NetOutcome.err e, onAlt e)
          else if (true && Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- Internal ConnectProxy proof helper `emitBytes_spc`. -/
theorem emitBytes_spc (sBase : Net.NetState) (e : Errno) (c : ByteArray)
    (v : ByteArray → Option Net.NetState) (alts : List Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitBytes (some (.err e)) sBase c v alts = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if (alts.contains e || Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- Internal ConnectProxy proof helper `emitAddr_spc`. -/
theorem emitAddr_spc (sBase : Net.NetState) (e : Errno) (c : Net.SockAddr)
    (v : Net.SockAddr → Option Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.emitAddr (some (.err e)) sBase c v = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if Net.isTransientNetErrno e = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hTr]; rfl

/-- Internal ConnectProxy proof helper `emitErr_spc`. -/
theorem emitErr_spc (sBase : Net.NetState) (e canon : Errno)
    (alts : List Errno) (onErr : Errno → Net.NetState)
    (u1 : Option Net.NetState) (u2 : Option (UInt32 → Option Net.NetState))
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNe : (e == canon) = false)
    (hNotMem : alts.contains e = false) :
    Net.emitErr (some (.err e)) sBase canon alts onErr true u1 u2 = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if (e == canon || alts.contains e) = true then some (Net.NetOutcome.err e, onErr e)
          else if (true && Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNe, hNotMem, hTr]; rfl

private theorem emitAccept_spc (sBase : Net.NetState) (lFid : Net.FileId) (ld : Net.SockDesc)
    (aq : List Net.AcceptEntry) (fl : Net.SockFlags) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.emitAccept (some (.err e)) sBase lFid ld aq fl = some (.err e, sBase) := by
  unfold Net.emitAccept
  cases aq with
  | nil =>
    exact emitErr_spc sBase e Errno.EAGAIN [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]
      (fun _ => sBase) none none hSpc
      (by rcases hSpc with rfl | rfl <;> decide)
      (by rcases hSpc with rfl | rfl <;> decide)
  | cons acc rest =>
    dsimp only
    have h1 : ([Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.ECONNABORTED].contains e) = false := by
      rcases hSpc with rfl | rfl <;> decide
    have h2 : (e == Errno.EAGAIN) = false := by rcases hSpc with rfl | rfl <;> decide
    have h3 : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
    rw [h2, Bool.false_and, Bool.false_and, h1, h3]
    rfl

/-- Internal ConnectProxy proof helper `familyMismatch_ne_spc`. -/
theorem familyMismatch_ne_spc (dom : Net.SockDomain) (addr : Net.SockAddr) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (e == Net.familyMismatchErrno dom addr) = false := by
  unfold Net.familyMismatchErrno
  rcases hSpc with rfl | rfl <;>
    cases dom <;> cases addr <;> dsimp only <;> (try split) <;> decide

/-- Internal ConnectProxy proof helper `list_not_contains_spc`. -/
theorem list_not_contains_spc {a b : List Errno} {e : Errno}
    (ha : a.contains e = false) (hb : b.contains e = false) :
    (a ++ b).contains e = false := by
  rw [List.contains_append, ha, hb]; rfl

/-- Internal ConnectProxy proof helper `list_cons_not_contains_spc`. -/
theorem list_cons_not_contains_spc {x e : Errno} {xs : List Errno}
    (hx : [x].contains e = false) (hxs : xs.contains e = false) :
    (x :: xs).contains e = false :=
  list_not_contains_spc hx hxs

/-- Internal ConnectProxy proof helper `setFileSocket_sec`. -/
theorem setFileSocket_sec (s : Net.NetState) (fid : Net.FileId) (d : Net.SockDesc) :
    (Net.setFileSocket s fid d).ambientSeccomp = s.ambientSeccomp := rfl

private theorem bindConflictAlts_not_spc (st : Net.NetState) (na : Net.SockAddr) (hs : Bool) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (([Errno.EACCES] ++
      (if Net.isIpv4MappedV6Addr na ||
          (match st.loState with | .up _ => false | _ => Net.isLocalNonWildcardV6 na) then
        [Errno.EINVAL, Errno.EADDRNOTAVAIL]
       else []) ++
      (if hs then [Errno.ENODEV] else [])).contains e) = false := by
  repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))

/-- Internal ConnectProxy proof helper `udpLoDownAlts_not_spc`. -/
theorem udpLoDownAlts_not_spc (st : Net.NetState) (dX : Net.SockDesc) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ((match dX.proto with
      | .udp fam bind (some targetAddr) =>
        let bcastAlts :=
          if (bind.addr?.map Net.isBcastTargetAddr).getD false || Net.isBcastTargetAddr targetAddr then
            [Errno.ENETUNREACH, Errno.EACCES]
          else []
        let loAlts :=
          match st.loState with
          | .down _ _ | .unpinned _ =>
            if fam == Net.InetFamily.v6 || !Net.isLoopbackTargetAddr targetAddr then [Errno.ENETUNREACH] else []
          | .up _ => []
        bcastAlts ++ loAlts
      | _ => []).contains e) = false := by
  cases dX.proto with
  | udp fam bind p? =>
    cases p? with
    | none => dsimp only; rcases hSpc with rfl | rfl <;> decide
    | some targetAddr =>
      dsimp only
      repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
  | _ => dsimp only; rcases hSpc with rfl | rfl <;> decide

/-- Internal ConnectProxy proof helper `ite_not_contains_spc`. -/
theorem ite_not_contains_spc {c : Prop} [inst : Decidable c] {l1 l2 : List Errno} {e : Errno}
    (h1 : l1.contains e = false) (h2 : l2.contains e = false) :
    (if c then l1 else l2).contains e = false := by
  cases inst <;> assumption

/-- Internal ConnectProxy proof helper `exists_ite_spc`. -/
theorem exists_ite_spc {c : Prop} [inst : Decidable c]
    {t f : Option (Net.NetOutcome × Net.NetState)} {e : Errno} {sec : Bool}
    (ht : ∃ s', t = some (.err e, s') ∧ s'.ambientSeccomp = sec)
    (hf : ∃ s', f = some (.err e, s') ∧ s'.ambientSeccomp = sec) :
    ∃ s', (if c then t else f) = some (.err e, s') ∧ s'.ambientSeccomp = sec := by
  cases inst <;> assumption

/-- Internal ConnectProxy proof helper `ite_sec_spc`. -/
theorem ite_sec_spc {c : Prop} [inst : Decidable c] {s1 s2 : Net.NetState} {sec : Bool}
    (h1 : s1.ambientSeccomp = sec) (h2 : s2.ambientSeccomp = sec) :
    (if c then s1 else s2).ambientSeccomp = sec := by
  cases inst <;> assumption

private theorem stepBindInet_spc (s0 : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d0 : Net.SockDesc) (addr : Net.SockAddr) (port : UInt16) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepBindInet s0 hid selfFid d0 addr port (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s0.ambientSeccomp := by
  unfold Net.stepBindInet
  dsimp only
  repeat (first
    | (with_reducible apply exists_ite_spc)
    | (refine ⟨s0, emitErr_spc s0 e _ _ _ _ _ hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · first
         | exact bindConflictAlts_not_spc _ _ _ e hSpc
         | repeat (first
             | (with_reducible apply list_not_contains_spc)
             | (with_reducible apply ite_not_contains_spc)
             | (rcases hSpc with rfl | rfl <;> decide)))
    | (refine ⟨s0, emitUnit_spc s0 _ e _ _ hSpc ?_, rfl⟩;
       repeat (first
         | (with_reducible apply list_not_contains_spc)
         | (with_reducible apply ite_not_contains_spc)
         | (rcases hSpc with rfl | rfl <;> decide))))

/-- Internal ConnectProxy proof helper `stepBind_spc`. -/
theorem stepBind_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (addr : Net.SockAddr) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepBind s hid addr (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepBind Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  split
  · exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (familyMismatch_ne_spc d.domain addr e hSpc)
      (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
  · cases addr with
    | ipv4 _ port => exact stepBindInet_spc s hid selfFid d _ port e hSpc
    | ipv6 _ _ port _ _ => exact stepBindInet_spc s hid selfFid d _ port e hSpc
    | unix path =>
      dsimp only
      repeat (first
        | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
           · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
           · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
        | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
           repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
        | split)

/-- Internal ConnectProxy proof helper `stepListen_spc`. -/
theorem stepListen_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (bl : UInt32) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepListen s hid bl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepListen Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
       rcases hSpc with rfl | rfl <;> decide)
    | split)

/-- Internal ConnectProxy proof helper `stepAccept4_spc`. -/
theorem stepAccept4_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (fl : Net.SockFlags) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepAccept4 s hid fl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepAccept4 Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | exact ⟨s, emitAccept_spc s selfFid d _ fl e hSpc, rfl⟩
    | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | split)


end LeanSwe.ConnectProxy.Proofs

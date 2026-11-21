import LeanSwe.LinuxSyscall.Dns.Proofs
import LeanSwe.LinuxSyscall.TimeRand.Proofs
import LeanSwe.ConnectProxy.HealthySys

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.HealthySys

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

private theorem sampleHealthyFilesOps_close (w : HealthySysWorld) (h : Nat)
    (hWf : w.filesEnv.wf = true) :
    let (r, w') := (sampleHealthyFilesOps.close h).run w
    healthyFilesStep w.filesEnv (.close h) (filesOutcomeUnit r) = some w'.filesEnv ∧
    w'.filesEnv.wf = true := by
  have hNotWf : (!w.filesEnv.wf) = false := by simp [hWf]
  unfold filesOutcomeUnit healthyFilesStep isFilesCriticalFault isCriticalOsErrno
    isFilesCloseEbusy Files.allowedStep Files.allowedCloseStep Files.verifyStep
    Files.isOutcomeErr isFilesEintrOutcome
  dsimp only [sampleHealthyFilesOps, liftFilesOp, Files.modelOps, Files.runOp, Files.evalModel,
    Files.evalReq, Files.precheckNul, StateT.run, bind, StateT.bind, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run]
  rw [hNotWf]
  cases hGet : Files.assocGet w.filesEnv.state.fds h with
  | none =>
    exact ⟨rfl, hWf⟩
  | some desc =>
    have hWfNext : ({ w.filesEnv with state := Files.closeDescInState w.filesEnv.state h desc }).wf = true := by
      unfold FilesHealthyEnv.wf at hWf ⊢
      unfold Files.closeDescInState
      exact hWf
    exact ⟨rfl, hWfNext⟩

/-- Chosen non-critical, non-`EINTR`, non-`soError` fallback errno (`ENOSPC` or `ENOBUFS`). -/
def chosenSockFallbackErrno (soErr : Errno) : Errno :=
  if soErr == Errno.ENOSPC then Errno.ENOBUFS else Errno.ENOSPC

/-- Everyday non-critical, non-`EINTR` fallback errno accepted by `healthyNetStep` on any `NetState`. -/
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

private theorem preCheckNet_safe (req : Net.NetReq) (err : Errno)
    (h : Net.preCheckNet req = some err) :
    isCriticalOsErrno err = false ∧ (err == Errno.EINTR) = false := by
  unfold Net.preCheckNet Net.validateSocketArgs Net.validateSocketpairArgs at h
  cases req <;> simp only at h
  all_goals
    repeat (first
      | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
      | split at h
      | cases h)

private theorem lookupFileSocket_err_safe (s : Net.NetState) (fid : Net.FileId) (e : Errno)
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

private theorem chosen_cases (soErr : Errno) :
    (chosenSockFallbackErrno soErr = Errno.ENOSPC ∨ chosenSockFallbackErrno soErr = Errno.ENOBUFS) ∧
    (chosenSockFallbackErrno soErr == soErr) = false ∧
    isCriticalOsErrno (chosenSockFallbackErrno soErr) = false ∧
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

private theorem asyncConnect_false_of_chosen (d : Net.SockDesc) (pendErr e : Errno)
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

private theorem consumePending_eq_soError (d : Net.SockDesc) (pendErr : Errno) (dClr : Net.SockDesc)
    (h : Net.consumePendingSoError d = some (pendErr, dClr)) :
    pendErr = d.soError := by
  unfold Net.consumePendingSoError at h
  by_cases h0 : (d.soError == 0) = true
  · simp [h0] at h
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    injection h with hPair
    exact (congrArg Prod.fst hPair).symm

private theorem consumeRecvPending_eq_soError (d : Net.SockDesc) (pendErr : Errno) (dClr : Net.SockDesc)
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

private theorem emitUnit_spc (sBase sOk : Net.NetState) (e : Errno)
    (alts : List Errno) (onAlt : Errno → Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitUnit (some (.err e)) sBase sOk alts onAlt true = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (Net.NetOutcome.err e, onAlt e)
          else if (true && Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

private theorem emitU32_spc (sBase sOk : Net.NetState) (e : Errno) (c : UInt32)
    (alts : List Errno) (z : Bool) (onAlt : Errno → Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitU32 (some (.err e)) sBase c sOk alts z onAlt true = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (Net.NetOutcome.err e, onAlt e)
          else if (true && Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

private theorem emitBytes_spc (sBase : Net.NetState) (e : Errno) (c : ByteArray)
    (v : ByteArray → Option Net.NetState) (alts : List Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    Net.emitBytes (some (.err e)) sBase c v alts = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if (alts.contains e || Net.isTransientNetErrno e) = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

private theorem emitAddr_spc (sBase : Net.NetState) (e : Errno) (c : Net.SockAddr)
    (v : Net.SockAddr → Option Net.NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.emitAddr (some (.err e)) sBase c v = some (.err e, sBase) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if Net.isTransientNetErrno e = true then some (Net.NetOutcome.err e, sBase)
          else none) = some (Net.NetOutcome.err e, sBase)
  rw [hTr]; rfl

private theorem emitErr_spc (sBase : Net.NetState) (e canon : Errno)
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

private theorem familyMismatch_ne_spc (dom : Net.SockDomain) (addr : Net.SockAddr) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (e == Net.familyMismatchErrno dom addr) = false := by
  unfold Net.familyMismatchErrno
  rcases hSpc with rfl | rfl <;>
    cases dom <;> cases addr <;> dsimp only <;> (try split) <;> decide

private theorem list_not_contains_spc {a b : List Errno} {e : Errno}
    (ha : a.contains e = false) (hb : b.contains e = false) :
    (a ++ b).contains e = false := by
  rw [List.contains_append, ha, hb]; rfl

private theorem list_cons_not_contains_spc {x e : Errno} {xs : List Errno}
    (hx : [x].contains e = false) (hxs : xs.contains e = false) :
    (x :: xs).contains e = false :=
  list_not_contains_spc hx hxs

private theorem setFileSocket_sec (s : Net.NetState) (fid : Net.FileId) (d : Net.SockDesc) :
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

private theorem udpLoDownAlts_not_spc (st : Net.NetState) (dX : Net.SockDesc) (e : Errno)
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

private theorem ite_not_contains_spc {c : Prop} [inst : Decidable c] {l1 l2 : List Errno} {e : Errno}
    (h1 : l1.contains e = false) (h2 : l2.contains e = false) :
    (if c then l1 else l2).contains e = false := by
  cases inst <;> assumption

private theorem exists_ite_spc {c : Prop} [inst : Decidable c]
    {t f : Option (Net.NetOutcome × Net.NetState)} {e : Errno} {sec : Bool}
    (ht : ∃ s', t = some (.err e, s') ∧ s'.ambientSeccomp = sec)
    (hf : ∃ s', f = some (.err e, s') ∧ s'.ambientSeccomp = sec) :
    ∃ s', (if c then t else f) = some (.err e, s') ∧ s'.ambientSeccomp = sec := by
  cases inst <;> assumption

private theorem ite_sec_spc {c : Prop} [inst : Decidable c] {s1 s2 : Net.NetState} {sec : Bool}
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

private theorem stepBind_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

private theorem stepListen_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

private theorem stepAccept4_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

private theorem v6MappedMismatch_ne_spc (bSa? : Option Net.SockAddr) (addr : Net.SockAddr)
    (al lw : Bool) (m e : Errno)
    (hm : Net.v6MappedNativeMismatchErrno? bSa? addr al lw = some m)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (e == m) = false := by
  cases bSa? with
  | none => cases hm
  | some loc =>
    cases loc <;> cases addr <;> dsimp only [Net.v6MappedNativeMismatchErrno?] at hm
    all_goals
      repeat (first
        | (injection hm with hEq; subst hEq; rcases hSpc with rfl | rfl <;> decide)
        | split at hm
        | cases hm)

private theorem stepTcpConnectNewCore_spc (s0 s : Net.NetState) (selfFid : Net.FileId) (d : Net.SockDesc)
    (fam : Net.InetFamily) (bind : Net.InetBind) (taint : Bool) (addr : Net.SockAddr) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hsSec : s.ambientSeccomp = s0.ambientSeccomp)
    (hSelfSpc : ∀ sBase sF dF fm nb nt tgt,
      sBase.ambientSeccomp = s0.ambientSeccomp →
      ∃ s', Net.stepTcpSelfConnect sBase sF dF fm nb nt tgt (some (.err e)) = some (.err e, s') ∧
        s'.ambientSeccomp = s0.ambientSeccomp)
    (hLookSpc : ∀ sBase sF dF fm nb nt ep np tgt,
      sBase.ambientSeccomp = s0.ambientSeccomp →
      ∃ s', Net.stepTcpConnectLookupListener sBase sF dF fm nb nt ep np tgt (some (.err e)) = some (.err e, s') ∧
        s'.ambientSeccomp = s0.ambientSeccomp) :
    ∃ s', Net.stepTcpConnectNewCore s selfFid d fam bind taint addr (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s0.ambientSeccomp := by
  unfold Net.stepTcpConnectNewCore
  dsimp only
  cases hm : Net.v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (Net.loDownWasUp s.loState) with
  | some misErr =>
    dsimp only
    refine ⟨s, emitErr_spc s e misErr _ _ none none hSpc (v6MappedMismatch_ne_spc _ _ _ _ misErr e hm hSpc) ?_, hsSec⟩
    repeat (first
      | (with_reducible apply list_not_contains_spc)
      | (with_reducible apply ite_not_contains_spc)
      | (rcases hSpc with rfl | rfl <;> decide))
  | none =>
    dsimp only
    repeat (first
      | (with_reducible apply exists_ite_spc)
      | exact hSelfSpc s _ _ _ _ _ _ hsSec
      | exact hLookSpc s _ _ _ _ _ _ _ _ hsSec
      | (refine ⟨_, emitErr_spc _ e _ _ _ _ _ hSpc ?_ ?_, ?_⟩;
         · rcases hSpc with rfl | rfl <;> decide
         · repeat (first
             | (with_reducible apply list_not_contains_spc)
             | (with_reducible apply ite_not_contains_spc)
             | (rcases hSpc with rfl | rfl <;> decide))
         · repeat (first
             | exact hsSec
             | (rw [setFileSocket_sec]; exact hsSec)
             | (with_reducible apply ite_sec_spc))))

private theorem stepTcpConnectNew_spc (s0 : Net.NetState) (selfFid : Net.FileId) (d0 : Net.SockDesc)
    (fam : Net.InetFamily) (bind : Net.InetBind) (taint : Bool) (addr : Net.SockAddr) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepTcpConnectNew s0 selfFid d0 fam bind taint addr (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s0.ambientSeccomp := by
  have hSelfSpc : ∀ sBase sF dF fm nb nt tgt,
      sBase.ambientSeccomp = s0.ambientSeccomp →
      ∃ s', Net.stepTcpSelfConnect sBase sF dF fm nb nt tgt (some (.err e)) = some (.err e, s') ∧
        s'.ambientSeccomp = s0.ambientSeccomp := by
    intro sBase sF dF fm nb nt tgt hSec
    unfold Net.stepTcpSelfConnect
    dsimp only
    split
    · have h1 : (e == Errno.EINPROGRESS) = false := by rcases hSpc with rfl | rfl <;> decide
      have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
      refine ⟨sBase, ?_, hSec⟩
      simp only [h1, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
    · split
      · refine ⟨sBase, emitErr_spc sBase e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) ?_, hSec⟩
        repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
      · refine ⟨sBase, emitUnit_spc sBase _ e _ _ hSpc ?_, hSec⟩
        repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
  have hLookSpc : ∀ sBase sF dF fm nb nt ep np tgt,
      sBase.ambientSeccomp = s0.ambientSeccomp →
      ∃ s', Net.stepTcpConnectLookupListener sBase sF dF fm nb nt ep np tgt (some (.err e)) = some (.err e, s') ∧
        s'.ambientSeccomp = s0.ambientSeccomp := by
    intro sBase sF dF fm nb nt ep np tgt hSec
    unfold Net.stepTcpConnectLookupListener
    dsimp only
    apply exists_ite_spc
    · refine ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc ?_ ?_, hSec⟩
      · rcases hSpc with rfl | rfl <;> decide
      · rcases hSpc with rfl | rfl <;> decide
    · cases Net.findMatchingListener sBase sF dF.domain Net.SockType.stream
        (Net.resolveTargetAddrForClient
          (some (Net.tcpConnectLocalBind dF.domain nb tgt ep np sBase.nextPort false dF.inetSaddrZero).fst)
          tgt) with
      | none =>
        dsimp only
        apply exists_ite_spc
        · refine ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc ?_ ?_, hSec⟩
          · rcases hSpc with rfl | rfl <;> decide
          · rcases hSpc with rfl | rfl <;> decide
        · refine ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc ?_ ?_, hSec⟩
          · rcases hSpc with rfl | rfl <;> decide
          · rcases hSpc with rfl | rfl <;> decide
      | some hit =>
        rcases hit with ⟨lFid, lDesc, matchKind⟩
        dsimp only
        cases lDesc.proto with
        | tcp lFam lBind lSs tstate lTaint =>
          cases tstate with
          | listen lBacklog aq =>
            dsimp only
            apply exists_ite_spc
            · refine ⟨sBase, emitErr_spc sBase e _ _ _ _ none hSpc ?_ ?_, hSec⟩
              · rcases hSpc with rfl | rfl <;> decide
              · repeat (first
                  | (with_reducible apply list_not_contains_spc)
                  | (with_reducible apply ite_not_contains_spc)
                  | (cases sBase.loState <;> dsimp only <;> rcases hSpc with rfl | rfl <;> decide)
                  | (rcases hSpc with rfl | rfl <;> decide))
            · apply exists_ite_spc
              · refine ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc ?_ ?_, hSec⟩
                · rcases hSpc with rfl | rfl <;> decide
                · repeat (first
                    | (with_reducible apply list_not_contains_spc)
                    | (with_reducible apply ite_not_contains_spc)
                    | (cases sBase.loState <;> dsimp only <;> rcases hSpc with rfl | rfl <;> decide)
                    | (rcases hSpc with rfl | rfl <;> decide))
              · refine ⟨sBase, emitUnit_spc sBase _ e _ _ hSpc ?_, hSec⟩
                repeat (first
                  | (with_reducible apply list_not_contains_spc)
                  | (with_reducible apply ite_not_contains_spc)
                  | (cases sBase.loState <;> dsimp only <;> rcases hSpc with rfl | rfl <;> decide)
                  | (rcases hSpc with rfl | rfl <;> decide))
          | _ =>
            exact ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc
              (by rcases hSpc with rfl | rfl <;> decide)
              (by rcases hSpc with rfl | rfl <;> decide), hSec⟩
        | _ =>
          exact ⟨sBase, emitErr_spc sBase e _ _ _ none none hSpc
            (by rcases hSpc with rfl | rfl <;> decide)
            (by rcases hSpc with rfl | rfl <;> decide), hSec⟩
  unfold Net.stepTcpConnectNew
  dsimp only
  by_cases hDom : (addr.domain != d0.domain) = true
  · simp only [hDom, ↓reduceIte]
    refine ⟨s0, emitErr_spc s0 e _ _ _ none none hSpc (familyMismatch_ne_spc _ addr e hSpc) ?_, rfl⟩
    repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
  · have hDomF := Bool.eq_false_iff.mpr hDom
    rw [hDomF]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hIfEx : ∀ (b : Bool) (thenBr elseBr : Option (Net.NetOutcome × Net.NetState)),
        (∃ s', thenBr = some (.err e, s') ∧ s'.ambientSeccomp = s0.ambientSeccomp) →
        (∃ s', elseBr = some (.err e, s') ∧ s'.ambientSeccomp = s0.ambientSeccomp) →
        ∃ s', (if b = true then thenBr else elseBr) = some (.err e, s') ∧ s'.ambientSeccomp = s0.ambientSeccomp := by
      intro b _ _ ht he
      cases b
      · exact he
      · exact ht
    apply hIfEx
    · refine ⟨s0, emitErr_spc s0 e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide) ?_, rfl⟩
      repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
    · apply stepTcpConnectNewCore_spc s0 _ selfFid _ fam bind taint addr e hSpc _ hSelfSpc hLookSpc
      split <;> split <;> rfl

private theorem stepConnect_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (addr : Net.SockAddr) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', Net.stepConnect s hid addr (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepConnect Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  cases hp : d.proto with
  | unixDgram bp p? =>
    unfold Net.stepUnixDgramConnect
    dsimp only
    repeat (first
      | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
         · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
         · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
      | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
         repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
      | split)
  | udp fam bind p? =>
    refine ⟨s, ?_, rfl⟩
    unfold Net.stepUdpConnect
    dsimp only
    cases hDom : ((Net.normalizeUdpTarget d.domain addr bind.addr?).domain != d.domain) with
    | true =>
      simp only [↓reduceIte]
      apply emitErr_spc s e _ _ _ _ _ hSpc (familyMismatch_ne_spc _ _ e hSpc)
      repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hUdpSc : ∀ (bSc : Bool) (thenBr elseBr : Option (Net.NetOutcome × Net.NetState)),
          thenBr = some (.err e, s) →
          elseBr = some (.err e, s) →
          (if bSc = true then thenBr else elseBr) = some (.err e, s) := by
        intro bSc _ _ ht he
        cases bSc
        · exact he
        · exact ht
      apply hUdpSc
      · apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
        repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
      · generalize hm : Net.v6MappedNativeMismatchErrno? _ _ _ _ = mOpt
        cases mOpt with
        | some misErr =>
          dsimp only
          apply emitErr_spc s e misErr _ _ _ _ hSpc (v6MappedMismatch_ne_spc _ _ _ _ misErr e hm hSpc)
          repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
        | none =>
          dsimp only
          repeat (first
            | (apply emitErr_spc s e _ _ _ _ _ hSpc;
               · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
               · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
            | (apply emitUnit_spc s _ e _ _ hSpc;
               repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
            | split)
  | unixStream isSeq bp conn =>
    unfold Net.stepUnixStreamConnect
    dsimp only
    repeat (first
      | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
         · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
         · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
      | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
         repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
      | split)
  | tcp fam bind ss ts taint =>
    cases ss with
    | connected =>
      unfold Net.stepConnectConnected
      dsimp only
      cases d.tcpSelfSynPending with
      | false =>
        exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide)
          (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
      | true =>
        have hIs : (e == Errno.EISCONN || Net.isTransientNetErrno e) = true := by
          rcases hSpc with rfl | rfl <;> decide
        refine ⟨s, ?_, rfl⟩
        dsimp only; rw [hIs]; rfl
    | disconnecting =>
      exact ⟨s, emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
        (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
    | connecting cf =>
      unfold Net.stepConnectConnecting Net.stepConnectConnectingReady
      dsimp only
      cases hCons : Net.consumePendingSoError d with
      | some pair =>
        rcases pair with ⟨pendErr, dClr⟩
        have hEqSo := consumePending_eq_soError d pendErr dClr hCons
        subst hEqSo
        have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
        have hAb : (e == Errno.ECONNABORTED) = false := by rcases hSpc with rfl | rfl <;> decide
        have hTr : (e == Errno.EALREADY || (d.tcpLoFinPending && e == Errno.EISCONN) || Net.isTransientNetErrno e) = true := by
          rcases hSpc with rfl | rfl <;> simp [Net.isTransientNetErrno, Errno.isTransientOsErrno]
        refine ⟨s, ?_, rfl⟩
        dsimp only
        simp only [hAsync, hAb, hTr, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      | none =>
        have hCfF : (cf && (e == Errno.ECONNREFUSED || e == Errno.ECONNABORTED)) = false := by
          have : (e == Errno.ECONNREFUSED || e == Errno.ECONNABORTED) = false := by rcases hSpc with rfl | rfl <;> decide
          rw [this, Bool.and_false]
        have hTr : (e == Errno.EISCONN || e == Errno.EALREADY || Net.isTransientNetErrno e) = true := by
          rcases hSpc with rfl | rfl <;> decide
        cases ts <;> dsimp only
        all_goals
          first
          | (refine ⟨s, ?_, rfl⟩; simp only [hCfF, hTr, Bool.false_eq_true, ↓reduceIte])
          | (refine ⟨s, emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
               (by rcases hSpc with rfl | rfl <;> decide), rfl⟩)
    | unconnected =>
      cases ts with
      | listen _ _ =>
        exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide)
          (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
      | _ =>
        exact stepTcpConnectNew_spc s selfFid d fam bind taint addr e hSpc

private theorem stepGetsockopt_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (opt : Net.SockOpt) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepGetsockopt s hid opt (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepGetsockopt Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  cases opt with
  | reuseAddr =>
    exact ⟨s, emitU32_spc s _ e _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
  | error =>
    dsimp only
    cases Net.consumePendingSoError d with
    | some pair =>
      rcases pair with ⟨_, _⟩
      refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl
    | none =>
      dsimp only
      cases d.proto with
      | unixStream _ _ conn =>
        cases conn with
        | connected _ _ _ pr _ => cases pr <;> (refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl)
        | _ => refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl
      | tcp _ _ _ ts _ =>
        cases ts with
        | closedAfterConn _ rsn => cases rsn <;> (refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl)
        | _ => refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl
      | _ => refine ⟨s, ?_, rfl⟩; dsimp only; rw [hTr]; rfl

private theorem stepSetsockopt_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (opt : Net.SetSockOpt) (val : UInt32) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepSetsockopt s hid opt val (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepSetsockopt Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  cases opt
  exact ⟨s, emitUnit_spc s _ e _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide), rfl⟩

private theorem stepGetsockname_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepGetsockname s hid (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepGetsockname Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  cases d.localAddr? <;> exact ⟨s, emitAddr_spc s e _ _ hSpc, rfl⟩

private theorem stepRecvfromBody_spc (s : Net.NetState) (selfFid : Net.FileId) (d : Net.SockDesc)
    (maxBytes : UInt32) (fl : Net.MsgFlags) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.stepRecvfromBody s selfFid d maxBytes fl (some (.err e)) = some (.err e, s) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotCr : (e == Errno.ECONNRESET) = false := by rcases hSpc with rfl | rfl <;> decide
  unfold Net.stepRecvfromBody
  dsimp only
  repeat (first
    | (apply emitBytes_spc s e _ _ _ hSpc;
       repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
    | (apply emitErr_spc s e _ _ _ none none hSpc;
       · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
       · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
    | (simp only [hNotCr, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte])
    | split)

private theorem stepRecvfrom_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (maxBytes : UInt32) (fl : Net.MsgFlags) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', Net.stepRecvfrom s hid maxBytes fl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepRecvfrom Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hBody := stepRecvfromBody_spc s selfFid d maxBytes fl e hSpc
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  cases hCons : Net.consumeRecvPendingSoError d with
  | some pair =>
    rcases pair with ⟨pendErr, dClr⟩
    have hEqSo := consumeRecvPending_eq_soError d pendErr dClr hCons
    subst hEqSo
    have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
    refine ⟨s, ?_, rfl⟩
    dsimp only
    rw [hBody, Option.isSome_some, Bool.and_true]
    split
    · exact rfl
    · simp only [hAsync, Bool.false_eq_true, ↓reduceIte, ite_self]
  | none =>
    have hNotCr : (e == Errno.ECONNRESET) = false := by
      rcases hSpc with rfl | rfl <;> decide
    refine ⟨s, ?_, rfl⟩
    dsimp only
    simp only [hNotCr, Bool.false_eq_true, ↓reduceIte]
    exact hBody

private theorem dgramTooBig_not_spc (d : Net.SockDesc) (data : ByteArray) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (if d.sockType != .stream && decide (data.size > 65507) then [Errno.EMSGSIZE] else []).contains e = false := by
  split <;> (rcases hSpc with rfl | rfl <;> decide)

private theorem stepSendtoBody_spc (s : Net.NetState) (selfFid : Net.FileId) (d : Net.SockDesc)
    (data : ByteArray) (fl : Net.MsgFlags) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.stepSendtoBody s selfFid d data fl (some (.err e)) = some (.err e, s) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNoRst : (e == Errno.EPIPE || e == Errno.ECONNRESET) = false := by
    rcases hSpc with rfl | rfl <;> decide
  have hDtb := dgramTooBig_not_spc d data e hSpc
  have hUld := udpLoDownAlts_not_spc s d e hSpc
  unfold Net.stepSendtoBody
  dsimp only
  by_cases h1 : (d.sockType == .dgram && !Net.isEstablished d) = true
  · simp only [h1, ↓reduceIte]
    apply emitErr_spc s e _ _ _ _ _ hSpc
    · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
    · exact hDtb
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!Net.isEstablished d) = true
    · simp only [h2, ↓reduceIte]
      apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
      repeat (first | apply list_not_contains_spc | exact hDtb | split | (rcases hSpc with rfl | rfl <;> decide))
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (d.domain == .unix && d.sockType == .seqpacket) = true
      · simp only [h3, ↓reduceIte]
        cases d.proto with
        | unixStream isSeq bp conn =>
          cases conn with
          | connected pf? psw pwb pr prGc =>
            cases pr <;> dsimp only
            · by_cases hw : d.shut.wr = true
              · simp only [hw, ↓reduceIte]
                exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                  (list_cons_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
              · simp only [hw, Bool.false_eq_true, ↓reduceIte]
                cases pwb
                · cases pf? <;> dsimp only
                  · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                      (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
                  · apply emitU32_spc s _ e _ _ _ _ hSpc
                    apply list_not_contains_spc _ hDtb
                    split <;> (rcases hSpc with rfl | rfl <;> decide)
                · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                    (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
            · apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
              apply list_not_contains_spc _ hDtb
              split <;> (rcases hSpc with rfl | rfl <;> decide)
          | _ =>
            dsimp only
            split
            · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                (list_cons_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
            · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
        | _ =>
          dsimp only
          split
          · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
              (list_cons_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
          · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
              (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) hDtb)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : d.shut.wr = true
        · simp only [h4, ↓reduceIte]
          apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
          exact list_not_contains_spc
            (list_not_contains_spc
              (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide)
                (ite_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) rfl))
              hUld)
            hDtb
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          cases Net.disconnectUnixDgramIfPeerClosed s d with
          | some _ =>
            exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) hDtb
          | none =>
            dsimp only
            cases d.proto with
            | unixDgram _ peer? =>
              cases peer? with
              | none => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
              | some pair =>
                dsimp only
                cases Net.lookupFileSocket s pair.1 with
                | error _ => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) hDtb
                | ok pd =>
                  dsimp only
                  split
                  · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) hDtb
                  · split
                    · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) hDtb
                    · apply emitU32_spc s _ e _ _ _ _ hSpc
                      apply list_not_contains_spc _ hDtb
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
            | unixStream _ _ conn =>
              cases conn with
              | connected pf? _ pwb _ _ =>
                cases pf? with
                | none =>
                  exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                    (by rcases hSpc with rfl | rfl <;> decide)
                | some peerFid =>
                  dsimp only
                  split
                  · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                      (by rcases hSpc with rfl | rfl <;> decide)
                  · split
                    · apply emitU32_spc s _ e _ _ _ _ hSpc
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
                    · simp only [hTr, Bool.or_true, ↓reduceIte]
              | _ =>
                exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
            | tcp _ _ _ tcpState _ =>
              cases tcpState with
              | established pf? pa | finWait pf? pa =>
                dsimp only
                split
                · apply emitU32_spc s _ e _ _ _ _ hSpc
                  repeat (first
                    | (with_reducible apply list_not_contains_spc)
                    | (with_reducible apply ite_not_contains_spc)
                    | (rcases hSpc with rfl | rfl <;> decide))
                · simp only [hNoRst, Bool.and_false, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
              | closeWait pf? pa pcc =>
                cases pcc with
                | false =>
                  dsimp only
                  split
                  · apply emitU32_spc s _ e _ _ _ _ hSpc
                    repeat (first
                      | (with_reducible apply list_not_contains_spc)
                      | (with_reducible apply ite_not_contains_spc)
                      | (rcases hSpc with rfl | rfl <;> decide))
                  · simp only [hNoRst, Bool.and_false, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
                | true =>
                  cases pf? with
                  | none =>
                    dsimp only
                    split
                    · apply emitU32_spc s _ e _ _ _ _ hSpc
                      repeat (first
                        | (with_reducible apply list_not_contains_spc)
                        | (with_reducible apply ite_not_contains_spc)
                        | (rcases hSpc with rfl | rfl <;> decide))
                    · simp only [hNoRst, Bool.and_false, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
                  | some _ =>
                    exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                      (by rcases hSpc with rfl | rfl <;> decide)
              | _ =>
                exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                  (by rcases hSpc with rfl | rfl <;> decide)
            | udp fam _ targetAddr? =>
              cases targetAddr? with
              | none => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
              | some targetAddr =>
                dsimp only
                split
                · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) hDtb
                · split
                  · apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                    exact list_not_contains_spc
                      (list_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide)
                        (ite_not_contains_spc (by rcases hSpc with rfl | rfl <;> decide) rfl))
                      hDtb
                  · cases Net.ipv4AllHostsMcastPort? targetAddr with
                    | some _ =>
                      dsimp only
                      apply emitU32_spc s _ e _ _ _ _ hSpc
                      apply list_not_contains_spc (list_not_contains_spc hUld _) hDtb
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
                    | none =>
                      dsimp only
                      cases Net.findBoundUdpPeer s d targetAddr with
                      | some _ =>
                        dsimp only
                        apply emitU32_spc s _ e _ _ _ _ hSpc
                        apply list_not_contains_spc (list_not_contains_spc hUld _) hDtb
                        split <;> (rcases hSpc with rfl | rfl <;> decide)
                      | none =>
                        dsimp only
                        apply emitU32_spc s _ e _ _ _ _ hSpc
                        apply list_not_contains_spc (list_not_contains_spc (list_not_contains_spc hUld _) _) hDtb
                        · rcases hSpc with rfl | rfl <;> decide
                        · split <;> (rcases hSpc with rfl | rfl <;> decide)

private theorem stepSendto_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (data : ByteArray) (fl : Net.MsgFlags) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', Net.stepSendto s hid data fl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepSendto Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hBody := stepSendtoBody_spc s selfFid d data fl e hSpc
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotPipe : (e == Errno.EPIPE) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotShut : (e == Errno.ESHUTDOWN) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotAg : (e == Errno.EAGAIN) = false := by rcases hSpc with rfl | rfl <;> decide
  cases hCons : Net.consumePendingSoError d with
  | some pair =>
    rcases pair with ⟨pendErr, dClr⟩
    have hEqSo := consumePending_eq_soError d pendErr dClr hCons
    subst hEqSo
    have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
    refine ⟨s, ?_, rfl⟩
    simp only [hAsync, hNotPipe, hNotShut, hNotAg, hTr, Bool.and_false, Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
  | none => exact ⟨s, hBody, rfl⟩

private theorem stepShutdown_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (how : Net.ShutHow) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', Net.stepShutdown s hid how (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepShutdown Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | (refine ⟨s, emitErr_spc s e _ _ _ _ _ hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
       rcases hSpc with rfl | rfl <;> decide)
    | split)

private theorem stepSendmsg_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (fds : Array Net.HandleId) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hAllLive : (!fds.toList.all (Net.isLiveHandle s)) = false)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', Net.stepSendmsg s hid fds (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepSendmsg
  rw [hFid]; dsimp only
  simp only [hAllLive, Bool.false_eq_true, ↓reduceIte]
  rw [hSock]; dsimp only
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotPipe : (e == Errno.EPIPE) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotAg : (e == Errno.EAGAIN) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNoRst : (e == Errno.EPIPE || e == Errno.ECONNRESET) = false := by
    rcases hSpc with rfl | rfl <;> decide
  split
  · exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide)
      (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
  · cases hCons : Net.consumePendingSoError d with
    | some pair =>
      rcases pair with ⟨pendErr, dClr⟩
      have hEqSo := consumePending_eq_soError d pendErr dClr hCons
      subst hEqSo
      have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
      refine ⟨s, ?_, rfl⟩
      simp only [hAsync, hNotPipe, hNotAg, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    | none =>
      refine ⟨s, ?_, rfl⟩
      have hUld := udpLoDownAlts_not_spc s d e hSpc
      by_cases h1 : (!Net.isEstablished d) = true
      · simp only [h1, ↓reduceIte]
        apply emitErr_spc s e _ _ _ _ _ hSpc
        · split <;> (rcases hSpc with rfl | rfl <;> decide)
        · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (d.domain == .unix && d.sockType == .seqpacket) = true
        · simp only [h2, ↓reduceIte]
          cases d.proto with
          | unixStream isSeq bp conn =>
            cases conn with
            | connected pf? psw pwb pr prGc =>
              cases pr <;> dsimp only
              · by_cases hw : d.shut.wr = true
                · simp only [hw, ↓reduceIte]
                  exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                    (by rcases hSpc with rfl | rfl <;> decide)
                · simp only [hw, Bool.false_eq_true, ↓reduceIte]
                  cases pwb
                  · cases pf? <;> dsimp only
                    · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                        (by rcases hSpc with rfl | rfl <;> decide)
                    · apply emitUnit_spc s _ e _ _ hSpc
                      apply list_not_contains_spc _ (by rcases hSpc with rfl | rfl <;> decide)
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
                  · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                      (by rcases hSpc with rfl | rfl <;> decide)
              · apply emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                split <;> (rcases hSpc with rfl | rfl <;> decide)
            | _ =>
              dsimp only
              split <;> exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                (by rcases hSpc with rfl | rfl <;> decide)
          | _ =>
            dsimp only
            split <;> exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
              (by rcases hSpc with rfl | rfl <;> decide)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : d.shut.wr = true
          · simp only [h3, ↓reduceIte]
            exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
              (by rcases hSpc with rfl | rfl <;> decide)
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            cases Net.disconnectUnixDgramIfPeerClosed s d with
            | some _ =>
              exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
            | none =>
              dsimp only
              cases d.proto with
              | unixDgram _ peer? =>
                cases peer? with
                | none => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
                | some pair =>
                  dsimp only
                  cases Net.lookupFileSocket s pair.1 with
                  | error _ => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
                  | ok pd =>
                    dsimp only
                    split
                    · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
                    · split
                      · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
                      · apply emitUnit_spc s _ e _ _ hSpc
                        apply list_not_contains_spc _ (by rcases hSpc with rfl | rfl <;> decide)
                        split <;> (rcases hSpc with rfl | rfl <;> decide)
              | unixStream _ _ conn =>
                cases conn with
                | connected pf? _ pwb _ _ =>
                  cases pf? with
                  | none =>
                    exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                      (by rcases hSpc with rfl | rfl <;> decide)
                  | some _ =>
                    dsimp only
                    split
                    · exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                        (by rcases hSpc with rfl | rfl <;> decide)
                    · apply emitUnit_spc s _ e _ _ hSpc
                      apply list_not_contains_spc _ (by rcases hSpc with rfl | rfl <;> decide)
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
                | _ => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
              | udp _ _ targetAddr? =>
                cases targetAddr? with
                | none => exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl
                | some targetAddr =>
                  dsimp only
                  cases Net.findBoundUdpPeer s d targetAddr with
                  | some _ =>
                    dsimp only
                    apply emitUnit_spc s _ e _ _ hSpc
                    apply list_not_contains_spc hUld
                    split <;> (rcases hSpc with rfl | rfl <;> decide)
                  | none =>
                    dsimp only
                    apply emitUnit_spc s _ e _ _ hSpc
                    apply list_not_contains_spc (list_not_contains_spc hUld (by rcases hSpc with rfl | rfl <;> decide))
                    split <;> (rcases hSpc with rfl | rfl <;> decide)
              | tcp _ _ _ tcpState _ =>
                cases tcpState with
                | established _ _ | finWait _ _ =>
                  dsimp only
                  rw [show (d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET)) = false by
                    rw [hNoRst, Bool.and_false]]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  apply emitUnit_spc s _ e _ _ hSpc
                  split <;> (rcases hSpc with rfl | rfl <;> decide)
                | closeWait pf? pa pcc =>
                  cases pcc with
                  | false =>
                    dsimp only
                    rw [show (d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET)) = false by
                      rw [hNoRst, Bool.and_false]]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    apply emitUnit_spc s _ e _ _ hSpc
                    split <;> (rcases hSpc with rfl | rfl <;> decide)
                  | true =>
                    cases pf? with
                    | none =>
                      dsimp only
                      simp only [hTr, Bool.or_true, ↓reduceIte]
                    | some _ =>
                      exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                        (by rcases hSpc with rfl | rfl <;> decide)
                | _ =>
                  exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
                    (by rcases hSpc with rfl | rfl <;> decide)

private theorem stepRecvmsgBody_spc (s : Net.NetState) (selfFid : Net.FileId) (d : Net.SockDesc)
    (maxFds : UInt32) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    Net.stepRecvmsgBody s selfFid d maxFds (some (.err e)) = some (.err e, s) := by
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotCr : (e == Errno.ECONNRESET) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotPr : (e == Errno.EPROTO) = false := by rcases hSpc with rfl | rfl <;> decide
  unfold Net.stepRecvmsgBody
  dsimp only
  repeat (first
    | (apply emitErr_spc s e _ _ _ none none hSpc;
       · rcases hSpc with rfl | rfl <;> decide
       · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
    | (simp only [hNotCr, hNotPr, Bool.and_false, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte])
    | split)

private theorem stepRecvmsg_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (maxFds : UInt32) (e : Errno)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', Net.stepRecvmsg s hid maxFds (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold Net.stepRecvmsg Net.withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hBody := stepRecvmsgBody_spc s selfFid d maxFds e hSpc
  have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  cases hCons : Net.consumeRecvPendingSoError d with
  | some pair =>
    rcases pair with ⟨pendErr, dClr⟩
    have hEqSo := consumeRecvPending_eq_soError d pendErr dClr hCons
    subst hEqSo
    have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
    refine ⟨s, ?_, rfl⟩
    dsimp only
    rw [hBody, Option.isSome_some, Bool.and_true]
    split
    · exact rfl
    · simp only [hAsync, Bool.false_eq_true, ↓reduceIte, ite_self]
  | none =>
    have hNotCr : (e == Errno.ECONNRESET) = false := by
      rcases hSpc with rfl | rfl <;> decide
    refine ⟨s, ?_, rfl⟩
    dsimp only
    simp only [hNotCr, Bool.false_eq_true, ↓reduceIte]
    exact hBody

private theorem stepIoctl_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
    (d : Net.SockDesc) (op : Net.NetIoctlOp) (ifn : ByteArray)
    (hFid : Net.lookupHandleFileId s hid = some selfFid)
    (hSock : Net.lookupFileSocket s selfFid = .ok d) :
    ∃ s', Net.stepIoctl s hid op ifn (some (.err Errno.ENOSPC)) = some (.err Errno.ENOSPC, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  refine ⟨s, ?_, rfl⟩
  unfold Net.stepIoctl
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hTr : Net.isTransientNetErrno Errno.ENOSPC = true := by decide
  by_cases h0 : (ifn.size == 0) = true
  · simp only [h0, ↓reduceIte]
    cases op <;> exact emitErr_spc s Errno.ENOSPC _ _ _ _ _ (Or.inl rfl) (by decide) (by decide)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases hLo : Net.bytesEq ifn Net.loIfname = true
    · simp only [hLo, ↓reduceIte]
      cases s.loState <;> cases op <;> dsimp only
      all_goals
        first
        | exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide)
        | (rw [hTr]; rfl)
        | (split
           · exact emitErr_spc s Errno.ENOSPC _ _ _ _ _ (Or.inl rfl) (by decide) (by decide)
           · exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide))
    · simp only [hLo, Bool.false_eq_true, ↓reduceIte]
      cases Net.bytesAssocGet s.otherIfaces ifn <;> cases op <;> dsimp only
      all_goals
        first
        | exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide)
        | (simp only [hTr, Bool.or_true, ↓reduceIte]; done)
        | (split
           · exact emitErr_spc s Errno.ENOSPC _ _ _ _ _ (Or.inl rfl) (by decide) (by decide)
           · first
             | exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide)
             | simp only [hTr, Bool.or_true, ↓reduceIte])

private theorem emitErr_self_eq (s : Net.NetState) (e : Errno) (alTr : Bool) :
    Net.emitErr (some (.err e)) s e [] (fun _ => s) alTr none none = some (.err e, s) := by
  unfold Net.emitErr
  dsimp only
  rw [beq_self_eq_true, Bool.true_or]
  rfl

private theorem fallbackNetErrno_healthy (env : NetHealthyEnv) (req : Net.NetReq)
    (hWf : env.wf = true) :
    ∃ env', healthyNetStep env req (.err (fallbackNetErrno env.state req)) = some env' ∧
      env'.wf = true := by
  have hCore :
      isCriticalOsErrno (fallbackNetErrno env.state req) = false ∧
      (fallbackNetErrno env.state req == Errno.EINTR) = false ∧
      ∃ s', Net.stepNetCore env.state req (some (.err (fallbackNetErrno env.state req))) =
        some (.err (fallbackNetErrno env.state req), s') ∧
        s'.ambientSeccomp = env.state.ambientSeccomp := by
    unfold fallbackNetErrno Net.stepNetCore
    cases hPre : Net.preCheckNet req with
    | some preErr =>
      dsimp only
      obtain ⟨hCrit, hEi⟩ := preCheckNet_safe req preErr hPre
      exact ⟨hCrit, hEi, env.state, emitErr_self_eq env.state preErr false, rfl⟩
    | none =>
      dsimp only
      cases req <;> dsimp only
      · exact ⟨by decide, by decide, env.state, rfl, rfl⟩
      · exact ⟨by decide, by decide, env.state, rfl, rfl⟩
      · rename_i hid addr
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepBind Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepBind Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepBind_spc env.state hid fid d addr _ hFid hSock hSpc⟩
      · rename_i hid bl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepListen Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepListen Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepListen_spc env.state hid fid d bl _ hFid hSock hSpc⟩
      · rename_i hid fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepAccept4 Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepAccept4 Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepAccept4_spc env.state hid fid d fl _ hFid hSock hSpc⟩
      · rename_i hid addr
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepConnect Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepConnect Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepConnect_spc env.state hid fid d addr _ hFid hSock hSpc hNe⟩
      · rename_i hid opt
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepGetsockopt Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepGetsockopt Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockopt_spc env.state hid fid d opt _ hFid hSock hSpc⟩
      · rename_i hid opt val
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSetsockopt Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepSetsockopt Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSetsockopt_spc env.state hid fid d opt val _ hFid hSock hSpc⟩
      · rename_i hid
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepGetsockname Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepGetsockname Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockname_spc env.state hid fid d _ hFid hSock hSpc⟩
      · rename_i hid maxBytes fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepRecvfrom Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepRecvfrom Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvfrom_spc env.state hid fid d maxBytes fl _ hFid hSock hSpc hNe⟩
      · rename_i hid data fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSendto Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepSendto Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSendto_spc env.state hid fid d data fl _ hFid hSock hSpc hNe⟩
      · rename_i hid how
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepShutdown Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepShutdown Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepShutdown_spc env.state hid fid d how _ hFid hSock hSpc⟩
      · rename_i hid fds
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSendmsg; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          by_cases hLive : (!fds.toList.all (Net.isLiveHandle env.state)) = true
          · simp only [hLive, ↓reduceIte]
            exact ⟨by decide, by decide, env.state,
              by unfold Net.stepSendmsg; rw [hFid]; simp only [hLive, ↓reduceIte]; exact emitErr_self_eq _ _ false, rfl⟩
          · have hLiveF : (!fds.toList.all (Net.isLiveHandle env.state)) = false := Bool.eq_false_iff.mpr hLive
            simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]
            cases hSock : Net.lookupFileSocket env.state fid with
            | error fdErr =>
              dsimp only
              rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
                exact ⟨by decide, by decide, env.state,
                  by unfold Net.stepSendmsg; rw [hFid]; simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
            | ok d =>
              dsimp only
              obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
              exact ⟨hCrit, hEi, stepSendmsg_spc env.state hid fid d fds _ hFid hLiveF hSock hSpc hNe⟩
      · rename_i hid maxFds
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepRecvmsg Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepRecvmsg Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvmsg_spc env.state hid fid d maxFds _ hFid hSock hSpc hNe⟩
      · rename_i hid op ifn
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepIoctl; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepIoctl; rw [hFid]; dsimp only; rw [hSock]; rfl, rfl⟩
          | ok d =>
            dsimp only
            exact ⟨by decide, by decide, stepIoctl_spc env.state hid fid d op ifn hFid hSock⟩
  rcases hCore with ⟨hCrit, hEi, s', hStep, hSec⟩
  have hNotWf : (!env.wf) = false := by simp [hWf]
  refine ⟨{ state := s', eintrBudget := env.eintrBudget }, ?_, ?_⟩
  · simp [healthyNetStep, hNotWf, isNetCriticalFault, hCrit, Net.allowedStep, hStep,
      isNetEintrOutcome, hEi]
  · unfold NetHealthyEnv.wf at hWf ⊢
    rw [hSec]; exact hWf

private def runSampleNetOp {α : Type}
    (req : Net.NetReq)
    (pack : Except Errno α → Net.NetOutcome)
    (unpack : Net.NetOutcome → Option (Except Errno α)) :
    StateM HealthySysWorld (Except Errno α) := fun w =>
  let env := w.netEnv
  let fbErr := fallbackNetErrno env.state req
  let runFb (_ : Unit) : Except Errno α × HealthySysWorld :=
    match healthyNetStep env req (.err fbErr) with
    | some envFb => (.error fbErr, { w with netEnv := envFb })
    | none => (.error fbErr, w)
  match Net.stepNetCore env.state req none with
  | some (candOut, _) =>
    match unpack candOut with
    | some candRes =>
      match healthyNetStep env req (pack candRes) with
      | some env' =>
        if env'.wf then (candRes, { w with netEnv := env' })
        else runFb ()
      | none => runFb ()
    | none => runFb ()
  | none => runFb ()

private theorem runSampleNetOp_healthy {α : Type}
    (req : Net.NetReq)
    (pack : Except Errno α → Net.NetOutcome)
    (unpack : Net.NetOutcome → Option (Except Errno α))
    (hPackErr : ∀ e, pack (.error e) = .err e)
    (w : HealthySysWorld)
    (hWf : w.netEnv.wf = true) :
    healthyNetStep w.netEnv req (pack ((runSampleNetOp req pack unpack).run w).1) =
      some ((runSampleNetOp req pack unpack).run w).2.netEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.netEnv.wf = true ∧
    ((runSampleNetOp req pack unpack).run w).2.filesEnv = w.filesEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.pollEnv = w.pollEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.dnsEnv = w.dnsEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.timeEnv = w.timeEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.proxyTable = w.proxyTable := by
  obtain ⟨envFb, hFbStep, hFbWf⟩ := fallbackNetErrno_healthy w.netEnv req hWf
  unfold runSampleNetOp
  dsimp only [StateT.run, Id.run]
  let fbPair : Except Errno α × HealthySysWorld :=
    match healthyNetStep w.netEnv req (.err (fallbackNetErrno w.netEnv.state req)) with
    | some ef => (.error (fallbackNetErrno w.netEnv.state req), { w with netEnv := ef })
    | none => (.error (fallbackNetErrno w.netEnv.state req), w)
  have hFbBranch :
      healthyNetStep w.netEnv req (pack fbPair.1) = some fbPair.2.netEnv ∧
      fbPair.2.netEnv.wf = true ∧
      fbPair.2.filesEnv = w.filesEnv ∧
      fbPair.2.pollEnv = w.pollEnv ∧
      fbPair.2.dnsEnv = w.dnsEnv ∧
      fbPair.2.timeEnv = w.timeEnv ∧
      fbPair.2.proxyTable = w.proxyTable := by
    dsimp only [fbPair]
    rw [hFbStep]
    dsimp only
    rw [hPackErr]
    exact ⟨hFbStep, hFbWf, rfl, rfl, rfl, rfl, rfl⟩
  cases Net.stepNetCore w.netEnv.state req none with
  | none => exact hFbBranch
  | some pair =>
    dsimp only
    cases unpack pair.1 with
    | none => exact hFbBranch
    | some candRes =>
      dsimp only
      cases hStep : healthyNetStep w.netEnv req (pack candRes) with
      | none => exact hFbBranch
      | some env' =>
        dsimp only
        by_cases hNextWf : env'.wf = true
        · have hIf : (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair) =
              (candRes, { w with netEnv := env' }) := by simp [hNextWf]
          change healthyNetStep w.netEnv req (pack (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair).1) = _ ∧ _
          rw [hIf]; dsimp only
          exact ⟨hStep, hNextWf, rfl, rfl, rfl, rfl, rfl⟩
        · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
          have hIf : (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair) = fbPair := by
            simp [hNextWfF]
          change healthyNetStep w.netEnv req (pack (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair).1) = _ ∧ _
          rw [hIf]
          exact hFbBranch

/-- Sample `NetOpsM` executing `Net.stepNetCore` with verified healthy fallback. -/
def sampleHealthyNetOps : Net.NetOpsM (StateM HealthySysWorld) Nat :=
  { socket := fun dom st fl p =>
      runSampleNetOp (.socket dom st fl p) netOutcomeOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    socketpair := fun dom st fl =>
      runSampleNetOp (.socketpair dom st fl) netOutcomePair
        (fun | .pair a b => some (.ok (a, b)) | .err e => some (.error e) | _ => none)
    bind := fun h sa =>
      runSampleNetOp (.bind h sa) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    listen := fun h bl =>
      runSampleNetOp (.listen h bl) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    accept4 := fun h fl =>
      runSampleNetOp (.accept4 h fl) netOutcomeAccepted
        (fun | .accepted c sa => some (.ok (c, sa)) | .err e => some (.error e) | _ => none)
    connect := fun h sa =>
      runSampleNetOp (.connect h sa) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockopt := fun h opt =>
      runSampleNetOp (.getsockopt h opt) netOutcomeU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    setsockopt := fun h opt val =>
      runSampleNetOp (.setsockopt h opt val) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockname := fun h =>
      runSampleNetOp (.getsockname h) netOutcomeAddr
        (fun | .addr sa => some (.ok sa) | .err e => some (.error e) | _ => none)
    recvfrom := fun h n fl =>
      runSampleNetOp (.recvfrom h n fl) netOutcomeBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    sendto := fun h bs fl =>
      runSampleNetOp (.sendto h bs fl) netOutcomeU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    shutdown := fun h how =>
      runSampleNetOp (.shutdown h how) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    sendmsg := fun h fds =>
      runSampleNetOp (.sendmsg h fds) netOutcomeUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    recvmsg := fun h mf =>
      runSampleNetOp (.recvmsg h mf) netOutcomeFds
        (fun | .fds fs => some (.ok fs) | .err e => some (.error e) | _ => none)
    ioctl := fun h op ifn =>
      runSampleNetOp (.ioctl h op ifn) netOutcomeU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none) }

private def fallbackPollErrno (s : Poll.PollState) : Poll.PollReq → Errno
  | .eventfd2 _ _ => Errno.EMFILE
  | .ppoll entries timeout =>
    match Poll.preCheckPoll (.ppoll entries timeout) with
    | some preErr => preErr
    | none =>
      match Poll.evalPollList s entries.toList with
      | .error pinErr => pinErr
      | .ok _ => Errno.EMFILE

private theorem evalPollListAux_err_ebadf (s : Poll.PollState) :
    ∀ (xs : List (Poll.HandleId × Poll.PollEvents)) (acc : List Poll.PollEvents) (e : Errno),
      Poll.evalPollListAux s xs acc = .error e → e = Errno.EBADF
  | [], _, _, h => nomatch h
  | (hid, reqEv) :: rest, acc, e, h => by
    unfold Poll.evalPollListAux at h
    cases hGet : Poll.assocGet s.fds hid with
    | none =>
      rw [hGet] at h
      injection h with hEq
      exact hEq.symm
    | some desc =>
      rw [hGet] at h
      exact evalPollListAux_err_ebadf s rest (Poll.computeDescRevents desc reqEv :: acc) e h

private theorem preCheckPoll_ppoll_err (entries : Array (Poll.HandleId × Poll.PollEvents))
    (timeout : Option Poll.Timespec) (preErr : Errno)
    (hPre : Poll.preCheckPoll (.ppoll entries timeout) = some preErr) :
    preErr = Errno.EINVAL := by
  dsimp only [Poll.preCheckPoll] at hPre
  have hCond : ∀ b : Bool, (if b = true then some Errno.EINVAL else none) = some preErr → preErr = Errno.EINVAL := by
    intro b hb
    cases b
    · cases hb
    · injection hb with he; exact he.symm
  exact hCond _ hPre

private theorem fallbackPollErrno_healthy (env : PollHealthyEnv) (req : Poll.PollReq)
    (hWf : env.wf = true) :
    healthyPollStep env req (.err (fallbackPollErrno env.state req)) = some env := by
  have hNotWf : (!env.wf) = false := by simp [hWf]
  cases req with
  | eventfd2 iv fl =>
    unfold fallbackPollErrno healthyPollStep isPollCriticalFault Poll.allowedStep Poll.stepPollCore isPollEintrOutcome
    rw [hNotWf]
    have h1 : isCriticalOsErrno Errno.EMFILE = false := by decide
    have h2 : (Errno.EMFILE.isTransientOsErrno || Errno.EMFILE == Errno.ENODEV) = true := by decide
    have h3 : (Errno.EMFILE == Errno.EINTR) = false := by decide
    simp [h1, h2, h3]
  | ppoll entries timeout =>
    unfold fallbackPollErrno
    dsimp only
    cases hPre : Poll.preCheckPoll (.ppoll entries timeout) with
    | some preErr =>
      have hEq : preErr = Errno.EINVAL := preCheckPoll_ppoll_err entries timeout preErr hPre
      subst hEq
      unfold healthyPollStep isPollCriticalFault Poll.allowedStep Poll.stepPollCore isPollEintrOutcome
      dsimp only
      rw [hNotWf, hPre]
      have h1 : isCriticalOsErrno Errno.EINVAL = false := by decide
      have h3 : (Errno.EINVAL == Errno.EINTR) = false := by decide
      simp [h1, h3]
    | none =>
      dsimp only
      cases hPin : Poll.evalPollList env.state entries.toList with
      | error pinErr =>
        have hEq : pinErr = Errno.EBADF := evalPollListAux_err_ebadf env.state entries.toList [] pinErr hPin
        subst hEq
        unfold healthyPollStep isPollCriticalFault Poll.allowedStep Poll.stepPollCore isPollEintrOutcome
        dsimp only
        rw [hNotWf, hPre, hPin]
        have h1 : isCriticalOsErrno Errno.EBADF = false := by decide
        have h3 : (Errno.EBADF == Errno.EINTR) = false := by decide
        simp [h1, h3]
      | ok revList =>
        dsimp only
        unfold healthyPollStep isPollCriticalFault Poll.allowedStep Poll.stepPollCore isPollEintrOutcome
        dsimp only
        rw [hNotWf, hPre, hPin]
        have h1 : isCriticalOsErrno Errno.EMFILE = false := by decide
        have h2 : Errno.EMFILE.isTransientOsErrno = true := by decide
        have h3 : (Errno.EMFILE == Errno.EINTR) = false := by decide
        simp [h1, h2, h3]

private def runSamplePollOp {α : Type}
    (req : Poll.PollReq)
    (pack : Except Errno α → Poll.PollOutcome)
    (unpack : Poll.PollOutcome → Option (Except Errno α)) :
    StateM HealthySysWorld (Except Errno α) := fun w =>
  let env := w.pollEnv
  let fbErr := fallbackPollErrno env.state req
  match Poll.stepPollCore env.state req none with
  | some (candOut, _) =>
    match unpack candOut with
    | some candRes =>
      match healthyPollStep env req (pack candRes) with
      | some env' =>
        if env'.wf then (candRes, { w with pollEnv := env' })
        else (.error fbErr, w)
      | none => (.error fbErr, w)
    | none => (.error fbErr, w)
  | none => (.error fbErr, w)

/-- Sample `PollOpsM` executing `Poll.stepPollCore` with verified healthy fallback. -/
def sampleHealthyPollOps : Poll.PollOpsM (StateM HealthySysWorld) Nat :=
  { ppoll := fun fds to? =>
      runSamplePollOp (.ppoll fds to?) pollOutcomePolled
        (fun | .polled rev => some (.ok rev) | .err e => some (.error e) | _ => none)
    eventfd2 := fun iv fl =>
      runSamplePollOp (.eventfd2 iv fl) pollOutcomeOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none) }

/-- Sample `DnsOpsM` lifting canonical `Dns.healthyModelOps` onto `HealthySysWorld.dnsEnv`. -/
def sampleHealthyDnsOps : Dns.DnsOpsM (StateM HealthySysWorld) :=
  { getaddrinfo := fun host hints w =>
      let (r, e') := (Dns.healthyModelOps.getaddrinfo host hints).run w.dnsEnv
      (r, { w with dnsEnv := e' }) }

private def liftTimeOp {α : Type} (act : StateM TimeRand.HealthyEnv α) :
    StateM HealthySysWorld α := fun w =>
  let (r, e') := act.run w.timeEnv
  (r, { w with timeEnv := e' })

/-- Sample `TimeRandOpsM` lifting canonical `TimeRand.healthyModelOps` onto `HealthySysWorld.timeEnv`. -/
def sampleHealthyTimeOps : TimeRand.TimeRandOpsM (StateM HealthySysWorld) :=
  { clock_gettime := fun clk => liftTimeOp (TimeRand.healthyModelOps.clock_gettime clk)
    clock_nanosleep := fun clk abs ts => liftTimeOp (TimeRand.healthyModelOps.clock_nanosleep clk abs ts)
    getrandom := fun n fl => liftTimeOp (TimeRand.healthyModelOps.getrandom n fl) }

/-- Canonical concrete healthy OS syscall bundle inhabiting `RefinesHealthyCProxySys`. -/
def sampleHealthySys : CProxySysOpsM (StateM HealthySysWorld) Nat :=
  { files := sampleHealthyFilesOps
    net := sampleHealthyNetOps
    poll := sampleHealthyPollOps
    dns := sampleHealthyDnsOps
    timeRand := sampleHealthyTimeOps }

/-- Non-vacuity theorem: `sampleHealthySys` refines the relational healthy OS world `RefinesHealthyCProxySys`. -/
theorem sampleHealthySys_refines : RefinesHealthyCProxySys sampleHealthySys := by
  unfold RefinesHealthyCProxySys RefinesHealthyCProxySysAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w h hWf
    have hCl := sampleHealthyFilesOps_close w h hWf.1
    dsimp only [sampleHealthySys] at hCl ⊢
    exact ⟨hCl.1, ⟨hCl.2, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl⟩
  · intro w req hWf
    have hPack : ∀ {α : Type} (r : Net.NetReq)
        (pack : Except Errno α → Net.NetOutcome)
        (unpack : Net.NetOutcome → Option (Except Errno α)),
        (∀ e, pack (.error e) = .err e) →
        healthyNetStep w.netEnv r (pack ((runSampleNetOp r pack unpack).run w).1) =
          some ((runSampleNetOp r pack unpack).run w).2.netEnv ∧
        (((runSampleNetOp r pack unpack).run w).2.filesEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.netEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.pollEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.dnsEnv.wf = true ∧
         ((runSampleNetOp r pack unpack).run w).2.timeEnv.wf = true) ∧
        ((runSampleNetOp r pack unpack).run w).2.proxyTable = w.proxyTable ∧
        ((w.filesEnv.state.fds.map Prod.fst).Nodup →
          (((runSampleNetOp r pack unpack).run w).2.filesEnv.state.fds.map Prod.fst).Nodup) := by
      intro α r pack unpack hPE
      have hN := runSampleNetOp_healthy r pack unpack hPE w hWf.2.1
      exact ⟨hN.1, ⟨by rw [hN.2.2.1]; exact hWf.1, hN.2.1, by rw [hN.2.2.2.1]; exact hWf.2.2.1,
        by rw [hN.2.2.2.2.1]; exact hWf.2.2.2.1, by rw [hN.2.2.2.2.2.1]; exact hWf.2.2.2.2⟩,
        hN.2.2.2.2.2.2, fun hNd => by rw [hN.2.2.1]; exact hNd⟩
    cases req <;>
      exact hPack _ _ _ (fun _ => rfl)
  · intro w req hWf
    have hPollOp : ∀ {α : Type} (r : Poll.PollReq)
        (pack : Except Errno α → Poll.PollOutcome)
        (unpack : Poll.PollOutcome → Option (Except Errno α)),
        (∀ e, pack (.error e) = .err e) →
        healthyPollStep w.pollEnv r (pack ((runSamplePollOp r pack unpack).run w).1) =
          some ((runSamplePollOp r pack unpack).run w).2.pollEnv ∧
        (((runSamplePollOp r pack unpack).run w).2.filesEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.netEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.pollEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.dnsEnv.wf = true ∧
         ((runSamplePollOp r pack unpack).run w).2.timeEnv.wf = true) ∧
        ((runSamplePollOp r pack unpack).run w).2.proxyTable = w.proxyTable ∧
        ((w.filesEnv.state.fds.map Prod.fst).Nodup →
          (((runSamplePollOp r pack unpack).run w).2.filesEnv.state.fds.map Prod.fst).Nodup) := by
      intro α r pack unpack hPE
      have hFb : healthyPollStep w.pollEnv r (pack (.error (fallbackPollErrno w.pollEnv.state r))) = some w.pollEnv := by
        rw [hPE]; exact fallbackPollErrno_healthy w.pollEnv r hWf.2.2.1
      unfold runSamplePollOp
      dsimp only [StateT.run, Id.run]
      cases Poll.stepPollCore w.pollEnv.state r none with
      | none => exact ⟨hFb, hWf, rfl, id⟩
      | some pair =>
        dsimp only
        cases unpack pair.1 with
        | none => exact ⟨hFb, hWf, rfl, id⟩
        | some candRes =>
          dsimp only
          cases hSt : healthyPollStep w.pollEnv r (pack candRes) with
          | none => exact ⟨hFb, hWf, rfl, id⟩
          | some env' =>
            dsimp only
            by_cases hNextWf : env'.wf = true
            · have hIf : (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)) =
                  (candRes, { w with pollEnv := env' }) := by simp [hNextWf]
              change healthyPollStep w.pollEnv r (pack (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)).1) = _ ∧ _
              rw [hIf]; dsimp only
              exact ⟨hSt, ⟨hWf.1, hWf.2.1, hNextWf, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl, id⟩
            · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
              have hIf : (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)) =
                  (.error (fallbackPollErrno w.pollEnv.state r), w) := by simp [hNextWfF]
              change healthyPollStep w.pollEnv r (pack (if env'.wf = true then (candRes, { w with pollEnv := env' })
                  else (.error (fallbackPollErrno w.pollEnv.state r), w)).1) = _ ∧ _
              rw [hIf]; dsimp only
              exact ⟨hFb, hWf, rfl, id⟩
    cases req <;>
      exact hPollOp _ _ _ (fun _ => rfl)
  · intro w req hWf
    have hD := Dns.Proofs.healthyModelOps_refinesHealthyDns w.dnsEnv req hWf.2.2.2.1
    dsimp only [Dns.execDnsReq, Dns.healthyModelOps, sampleHealthySys, sampleHealthyDnsOps,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
      StateT.run, Id.run] at hD ⊢
    have hWf' := (Dns.Proofs.healthyStep_implies_allowedStep w.dnsEnv w.dnsEnv req _ hD).2.2.2.1
    exact ⟨hD, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf', hWf.2.2.2.2⟩, rfl, id⟩
  · intro w req hWf
    have hT := TimeRand.Proofs.healthyModelOps_refinesHealthyTimeRand w.timeEnv req hWf.2.2.2.2
    cases req with
    | clock_gettime clk =>
      rcases hRun : (TimeRand.healthyModelOps.clock_gettime clk).run w.timeEnv with ⟨res, e'⟩
      have hRun0 : TimeRand.healthyModelOps.clock_gettime clk w.timeEnv = (res, e') := hRun
      dsimp only [execTimeRandReq, TimeRand.execTimeRandReq, sampleHealthySys, sampleHealthyTimeOps, liftTimeOp,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run] at hT ⊢
      rw [hRun0] at hT ⊢
      dsimp only at hT ⊢
      have hWf' := (TimeRand.Proofs.healthyStep_implies_allowedStep w.timeEnv e' (.clock_gettime clk) _ hT).2.2.1
      exact ⟨hT, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf'⟩, rfl, id⟩
    | clock_nanosleep clk abs ts =>
      rcases hRun : (TimeRand.healthyModelOps.clock_nanosleep clk abs ts).run w.timeEnv with ⟨res, e'⟩
      have hRun0 : TimeRand.healthyModelOps.clock_nanosleep clk abs ts w.timeEnv = (res, e') := hRun
      dsimp only [execTimeRandReq, TimeRand.execTimeRandReq, sampleHealthySys, sampleHealthyTimeOps, liftTimeOp,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run] at hT ⊢
      rw [hRun0] at hT ⊢
      dsimp only at hT ⊢
      have hWf' := (TimeRand.Proofs.healthyStep_implies_allowedStep w.timeEnv e' (.clock_nanosleep clk abs ts) _ hT).2.2.1
      exact ⟨hT, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf'⟩, rfl, id⟩
    | getrandom len fl =>
      rcases hRun : (TimeRand.healthyModelOps.getrandom len fl).run w.timeEnv with ⟨res, e'⟩
      have hRun0 : TimeRand.healthyModelOps.getrandom len fl w.timeEnv = (res, e') := hRun
      dsimp only [execTimeRandReq, TimeRand.execTimeRandReq, sampleHealthySys, sampleHealthyTimeOps, liftTimeOp,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.run] at hT ⊢
      rw [hRun0] at hT ⊢
      dsimp only at hT ⊢
      have hWf' := (TimeRand.Proofs.healthyStep_implies_allowedStep w.timeEnv e' (.getrandom len fl) _ hT).2.2.1
      exact ⟨hT, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf'⟩, rfl, id⟩
  · intro _ _; rfl
  · intro _ _; exact ⟨id, id⟩

end LeanSwe.ConnectProxy.Proofs

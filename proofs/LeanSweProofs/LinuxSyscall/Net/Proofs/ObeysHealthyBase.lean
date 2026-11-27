import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysRaw

/-!
# Base Transient-Fallback & Passive-Socket Lemmas for `LeanSwe.LinuxSyscall.Net`

Proves `emit*_spc`, `stepBind_spc`, `stepListen_spc`, and `stepAccept4_spc`
used to establish `healthyModelOps_obeysStep`.
-/

namespace LeanSwe.LinuxSyscall.Net.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

/-- `lookupFileSocket` failures only return `EBADF` or `ENOTSOCK`. -/
theorem lookupFileSocket_err_safe (s : NetState) (fid : FileId) (e : Errno)
    (h : lookupFileSocket s fid = .error e) :
    e = Errno.EBADF ∨ e = Errno.ENOTSOCK := by
  unfold lookupFileSocket at h
  cases hGet : assocGet s.files fid with
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

/-- `Model.chosenSockFallbackErrno` chooses `ENOSPC` or `ENOBUFS` distinct from `soErr` and `EINTR`. -/
theorem chosen_cases (soErr : Errno) :
    (Model.chosenSockFallbackErrno soErr = Errno.ENOSPC ∨
      Model.chosenSockFallbackErrno soErr = Errno.ENOBUFS) ∧
    (Model.chosenSockFallbackErrno soErr == soErr) = false ∧
    Errno.isCriticalOsErrno (Model.chosenSockFallbackErrno soErr) = false ∧
    (Model.chosenSockFallbackErrno soErr == Errno.EINTR) = false := by
  unfold Model.chosenSockFallbackErrno
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

/-- Chosen `ENOSPC`/`ENOBUFS` fallback never triggers `isAsyncConnectErrno`. -/
theorem asyncConnect_false_of_chosen (d : SockDesc) (pendErr e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNe : (e == pendErr) = false) :
    isAsyncConnectErrno pendErr e d = false := by
  unfold isAsyncConnectErrno
  have hNotCr : (e == Errno.ECONNRESET) = false := by
    rcases hSpc with rfl | rfl <;> decide
  have hRest : (e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT ||
      e == Errno.ENETUNREACH || e == Errno.EHOSTUNREACH) = false := by
    rcases hSpc with rfl | rfl <;> decide
  rw [hNe, Bool.false_or]
  cases d.proto <;> simp [hNotCr, hRest]

/-- `consumePendingSoError` yields `d.soError`. -/
theorem consumePending_eq_soError (d : SockDesc) (pendErr : Errno) (dClr : SockDesc)
    (h : consumePendingSoError d = some (pendErr, dClr)) :
    pendErr = d.soError := by
  unfold consumePendingSoError at h
  by_cases h0 : (d.soError == 0) = true
  · simp [h0] at h
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    injection h with hPair
    exact (congrArg Prod.fst hPair).symm

/-- `consumeRecvPendingSoError` yields `d.soError`. -/
theorem consumeRecvPending_eq_soError (d : SockDesc) (pendErr : Errno) (dClr : SockDesc)
    (h : consumeRecvPendingSoError d = some (pendErr, dClr)) :
    pendErr = d.soError := by
  unfold consumeRecvPendingSoError at h
  by_cases h1 : d.proto.isListening = true
  · simp [h1] at h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    have hPeerShut : ∀ b : Bool,
        (if (b && d.soError == Errno.EPIPE) = true then none else consumePendingSoError d) =
          some (pendErr, dClr) →
        pendErr = d.soError := by
      intro b
      cases b <;> cases (d.soError == Errno.EPIPE) <;> intro hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · exact consumePending_eq_soError d pendErr dClr hb
      · cases hb
    exact hPeerShut _ h

/-- `emitUnit` accepts transient `ENOSPC`/`ENOBUFS` without mutating `sBase`. -/
theorem emitUnit_spc (sBase sOk : NetState) (e : Errno)
    (alts : List Errno) (onAlt : Errno → NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    emitUnit (some (.err e)) sBase sOk alts onAlt true = some (.err e, sBase) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (NetOutcome.err e, onAlt e)
          else if (true && isTransientNetErrno e) = true then some (NetOutcome.err e, sBase)
          else none) = some (NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- `emitU32` accepts transient `ENOSPC`/`ENOBUFS` without mutating `sBase`. -/
theorem emitU32_spc (sBase sOk : NetState) (e : Errno) (c : UInt32)
    (alts : List Errno) (z : Bool) (onAlt : Errno → NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    emitU32 (some (.err e)) sBase c sOk alts z onAlt true = some (.err e, sBase) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if alts.contains e = true then some (NetOutcome.err e, onAlt e)
          else if (true && isTransientNetErrno e) = true then some (NetOutcome.err e, sBase)
          else none) = some (NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- `emitBytes` accepts transient `ENOSPC`/`ENOBUFS` without mutating `sBase`. -/
theorem emitBytes_spc (sBase : NetState) (e : Errno) (c : ByteArray)
    (v : ByteArray → Option NetState) (alts : List Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNotMem : alts.contains e = false) :
    emitBytes (some (.err e)) sBase c v alts = some (.err e, sBase) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if (alts.contains e || isTransientNetErrno e) = true then some (NetOutcome.err e, sBase)
          else none) = some (NetOutcome.err e, sBase)
  rw [hNotMem, hTr]; rfl

/-- `emitAddr` accepts transient `ENOSPC`/`ENOBUFS` without mutating `sBase`. -/
theorem emitAddr_spc (sBase : NetState) (e : Errno) (c : SockAddr)
    (v : SockAddr → Option NetState)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    emitAddr (some (.err e)) sBase c v = some (.err e, sBase) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if isTransientNetErrno e = true then some (NetOutcome.err e, sBase)
          else none) = some (NetOutcome.err e, sBase)
  rw [hTr]; rfl

/-- `emitErr` with `allowTransient = true` accepts `ENOSPC`/`ENOBUFS` without mutating `sBase`. -/
theorem emitErr_spc (sBase : NetState) (e canon : Errno)
    (alts : List Errno) (onErr : Errno → NetState)
    (u1 : Option NetState) (u2 : Option (UInt32 → Option NetState))
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNe : (e == canon) = false)
    (hNotMem : alts.contains e = false) :
    emitErr (some (.err e)) sBase canon alts onErr true u1 u2 = some (.err e, sBase) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  change (if (e == canon || alts.contains e) = true then some (NetOutcome.err e, onErr e)
          else if (true && isTransientNetErrno e) = true then some (NetOutcome.err e, sBase)
          else none) = some (NetOutcome.err e, sBase)
  rw [hNe, hNotMem, hTr]; rfl

private theorem emitAccept_spc (sBase : NetState) (lFid : FileId) (ld : SockDesc)
    (aq : List AcceptEntry) (fl : SockFlags) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    emitAccept (some (.err e)) sBase lFid ld aq fl = some (.err e, sBase) := by
  unfold emitAccept
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
    have h3 : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
    rw [h2, Bool.false_and, Bool.false_and, h1, h3]
    rfl

/-- `familyMismatchErrno` never equals `ENOSPC` or `ENOBUFS`. -/
theorem familyMismatch_ne_spc (dom : SockDomain) (addr : SockAddr) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (e == familyMismatchErrno dom addr) = false := by
  unfold familyMismatchErrno
  rcases hSpc with rfl | rfl <;>
    cases dom <;> cases addr <;> dsimp only <;> (try split) <;> decide

/-- `List.contains` distributes over `++` when both sides are `false`. -/
theorem list_not_contains_spc {a b : List Errno} {e : Errno}
    (ha : a.contains e = false) (hb : b.contains e = false) :
    (a ++ b).contains e = false := by
  rw [List.contains_append, ha, hb]; rfl

/-- `List.contains` on `x :: xs` is `false` when `[x]` and `xs` exclude `e`. -/
theorem list_cons_not_contains_spc {x e : Errno} {xs : List Errno}
    (hx : [x].contains e = false) (hxs : xs.contains e = false) :
    (x :: xs).contains e = false :=
  list_not_contains_spc hx hxs

/-- `setFileSocket` preserves `ambientSeccomp`. -/
theorem setFileSocket_sec (s : NetState) (fid : FileId) (d : SockDesc) :
    (setFileSocket s fid d).ambientSeccomp = s.ambientSeccomp := rfl

private theorem bindConflictAlts_not_spc (st : NetState) (na : SockAddr) (hs : Bool) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (([Errno.EACCES] ++
      (if isIpv4MappedV6Addr na ||
          (match st.loState with | .up _ => false | _ => isLocalNonWildcardV6 na) then
        [Errno.EINVAL, Errno.EADDRNOTAVAIL]
       else []) ++
      (if hs then [Errno.ENODEV] else [])).contains e) = false := by
  repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide))

/-- UDP loopback-down alternative errno lists never contain `ENOSPC` or `ENOBUFS`. -/
theorem udpLoDownAlts_not_spc (st : NetState) (dX : SockDesc) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ((match dX.proto with
      | .udp fam bind (some targetAddr) =>
        let bcastAlts :=
          if (bind.addr?.map isBcastTargetAddr).getD false || isBcastTargetAddr targetAddr then
            [Errno.ENETUNREACH, Errno.EACCES]
          else []
        let loAlts :=
          match st.loState with
          | .down _ _ | .unpinned _ =>
            if fam == InetFamily.v6 || !isLoopbackTargetAddr targetAddr then [Errno.ENETUNREACH] else []
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

/-- `if c then l1 else l2` excludes `e` when both `l1` and `l2` exclude `e`. -/
theorem ite_not_contains_spc {c : Prop} [inst : Decidable c] {l1 l2 : List Errno} {e : Errno}
    (h1 : l1.contains e = false) (h2 : l2.contains e = false) :
    (if c then l1 else l2).contains e = false := by
  cases inst <;> assumption

/-- Lift existential `spc` transition across `if c then t else f`. -/
theorem exists_ite_spc {c : Prop} [inst : Decidable c]
    {t f : Option (NetOutcome × NetState)} {e : Errno} {sec : Bool}
    (ht : ∃ s', t = some (.err e, s') ∧ s'.ambientSeccomp = sec)
    (hf : ∃ s', f = some (.err e, s') ∧ s'.ambientSeccomp = sec) :
    ∃ s', (if c then t else f) = some (.err e, s') ∧ s'.ambientSeccomp = sec := by
  cases inst <;> assumption

/-- Lift `ambientSeccomp` equality across `if c then s1 else s2`. -/
theorem ite_sec_spc {c : Prop} [inst : Decidable c] {s1 s2 : NetState} {sec : Bool}
    (h1 : s1.ambientSeccomp = sec) (h2 : s2.ambientSeccomp = sec) :
    (if c then s1 else s2).ambientSeccomp = sec := by
  cases inst <;> assumption

private theorem stepBindInet_spc (s0 : NetState) (hid : HandleId) (selfFid : FileId)
    (d0 : SockDesc) (addr : SockAddr) (port : UInt16) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', stepBindInet s0 hid selfFid d0 addr port (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s0.ambientSeccomp := by
  unfold stepBindInet
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

/-- `stepBind` accepts `ENOSPC`/`ENOBUFS` on any live socket while preserving `ambientSeccomp`. -/
theorem stepBind_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (addr : SockAddr) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', stepBind s hid addr (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepBind withSock
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

/-- `stepListen` accepts `ENOSPC`/`ENOBUFS` on any live socket while preserving `ambientSeccomp`. -/
theorem stepListen_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (bl : UInt32) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', stepListen s hid bl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepListen withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
       rcases hSpc with rfl | rfl <;> decide)
    | split)

/-- `stepAccept4` accepts `ENOSPC`/`ENOBUFS` on any live socket while preserving `ambientSeccomp`. -/
theorem stepAccept4_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (fl : SockFlags) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', stepAccept4 s hid fl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepAccept4 withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | exact ⟨s, emitAccept_spc s selfFid d _ fl e hSpc, rfl⟩
    | (refine ⟨s, emitErr_spc s e _ _ _ none none hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | split)

end LeanSwe.LinuxSyscall.Net.Proofs

import LeanSweProofs.LinuxSyscall.Net.Proofs.ObeysHealthyConn

/-!
# Send, Shutdown, `SCM_RIGHTS`, & `ioctl` Fallback Lemmas for `LeanSwe.LinuxSyscall.Net`

Proves `stepSendto_spc`, `stepShutdown_spc`, `stepSendmsg_spc`,
`stepRecvmsg_spc`, and `stepIoctl_spc`.
-/

namespace LeanSwe.LinuxSyscall.Net.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

private theorem dgramTooBig_not_spc (d : SockDesc) (data : ByteArray) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    (if d.sockType != .stream && decide (data.size > 65507) then [Errno.EMSGSIZE] else []).contains e = false := by
  split <;> (rcases hSpc with rfl | rfl <;> decide)

private theorem stepSendtoBody_spc (s : NetState) (selfFid : FileId) (d : SockDesc)
    (data : ByteArray) (fl : MsgFlags) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    stepSendtoBody s selfFid d data fl (some (.err e)) = some (.err e, s) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNoRst : (e == Errno.EPIPE || e == Errno.ECONNRESET) = false := by
    rcases hSpc with rfl | rfl <;> decide
  have hDtb := dgramTooBig_not_spc d data e hSpc
  have hUld := udpLoDownAlts_not_spc s d e hSpc
  unfold stepSendtoBody
  dsimp only
  by_cases h1 : (d.sockType == .dgram && !isEstablished d) = true
  · simp only [h1, ↓reduceIte]
    apply emitErr_spc s e _ _ _ _ _ hSpc
    · repeat (first | split | (rcases hSpc with rfl | rfl <;> decide))
    · exact hDtb
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!isEstablished d) = true
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
          cases disconnectUnixDgramIfPeerClosed s d with
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
                cases lookupFileSocket s pair.1 with
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
                  · cases ipv4AllHostsMcastPort? targetAddr with
                    | some _ =>
                      dsimp only
                      apply emitU32_spc s _ e _ _ _ _ hSpc
                      apply list_not_contains_spc (list_not_contains_spc hUld _) hDtb
                      split <;> (rcases hSpc with rfl | rfl <;> decide)
                    | none =>
                      dsimp only
                      cases findBoundUdpPeer s d targetAddr with
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

/-- `stepSendto` accepts chosen `ENOSPC`/`ENOBUFS` (`!= d.soError`) while preserving `ambientSeccomp`. -/
theorem stepSendto_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (data : ByteArray) (fl : MsgFlags) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', stepSendto s hid data fl (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepSendto withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hBody := stepSendtoBody_spc s selfFid d data fl e hSpc
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotPipe : (e == Errno.EPIPE) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotShut : (e == Errno.ESHUTDOWN) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotAg : (e == Errno.EAGAIN) = false := by rcases hSpc with rfl | rfl <;> decide
  cases hCons : consumePendingSoError d with
  | some pair =>
    rcases pair with ⟨pendErr, dClr⟩
    have hEqSo := consumePending_eq_soError d pendErr dClr hCons
    subst hEqSo
    have hAsync := asyncConnect_false_of_chosen d d.soError e hSpc hNeSo
    refine ⟨s, ?_, rfl⟩
    simp only [hAsync, hNotPipe, hNotShut, hNotAg, hTr, Bool.and_false, Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
  | none => exact ⟨s, hBody, rfl⟩

/-- `stepShutdown` accepts `ENOSPC`/`ENOBUFS` on any live socket while preserving `ambientSeccomp`. -/
theorem stepShutdown_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (how : ShutHow) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    ∃ s', stepShutdown s hid how (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepShutdown withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  repeat (first
    | (refine ⟨s, emitErr_spc s e _ _ _ _ _ hSpc ?_ ?_, rfl⟩;
       · rcases hSpc with rfl | rfl <;> decide
       · rcases hSpc with rfl | rfl <;> decide)
    | (refine ⟨s, emitUnit_spc s _ e _ _ hSpc ?_, rfl⟩;
       rcases hSpc with rfl | rfl <;> decide)
    | split)

/-- `stepSendmsg` accepts chosen `ENOSPC`/`ENOBUFS` (`!= d.soError`) while preserving `ambientSeccomp`. -/
theorem stepSendmsg_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (fds : Array HandleId) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hAllLive : (!fds.toList.all (isLiveHandle s)) = false)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', stepSendmsg s hid fds (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepSendmsg
  rw [hFid]; dsimp only
  simp only [hAllLive, Bool.false_eq_true, ↓reduceIte]
  rw [hSock]; dsimp only
  have hNotPipe : (e == Errno.EPIPE) = false := by rcases hSpc with rfl | rfl <;> decide
  split
  · exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide)
      (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
  · cases hCons : consumePendingSoError d with
    | some pair =>
      rcases pair with ⟨pendErr, dClr⟩
      have hEqSo := consumePending_eq_soError d pendErr dClr hCons
      subst hEqSo
      refine ⟨s, ?_, rfl⟩
      have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
      simp only [hNeSo, hNotPipe, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [hTr]; rfl
    | none =>
      refine ⟨s, ?_, rfl⟩
      by_cases h1 : (!isEstablished d) = true
      · simp only [h1, ↓reduceIte]
        exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide)
          (by rcases hSpc with rfl | rfl <;> decide)
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (d.sockType == .seqpacket) = true
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
            cases disconnectUnixDgramIfPeerClosed s d with
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
                  cases lookupFileSocket s pair.1 with
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
              | udp _ _ _ | tcp _ _ _ _ _ =>
                exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl

private theorem stepRecvmsgBody_spc (s : NetState) (selfFid : FileId) (d : SockDesc)
    (maxFds : UInt32) (e : Errno)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS) :
    stepRecvmsgBody s selfFid d maxFds (some (.err e)) = some (.err e, s) := by
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  have hNotCr : (e == Errno.ECONNRESET) = false := by rcases hSpc with rfl | rfl <;> decide
  have hNotPr : (e == Errno.EPROTO) = false := by rcases hSpc with rfl | rfl <;> decide
  unfold stepRecvmsgBody
  dsimp only
  repeat (first
    | (apply emitErr_spc s e _ _ _ none none hSpc;
       · rcases hSpc with rfl | rfl <;> decide
       · repeat (first | apply list_not_contains_spc | split | (rcases hSpc with rfl | rfl <;> decide)))
    | (simp only [hNotCr, hNotPr, Bool.and_false, hTr, Bool.or_true, Bool.false_eq_true, ↓reduceIte])
    | split)

/-- `stepRecvmsg` accepts chosen `ENOSPC`/`ENOBUFS` (`!= d.soError`) while preserving `ambientSeccomp`. -/
theorem stepRecvmsg_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (maxFds : UInt32) (e : Errno)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d)
    (hSpc : e = Errno.ENOSPC ∨ e = Errno.ENOBUFS)
    (hNeSo : (e == d.soError) = false) :
    ∃ s', stepRecvmsg s hid maxFds (some (.err e)) = some (.err e, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  unfold stepRecvmsg withSock
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hBody := stepRecvmsgBody_spc s selfFid d maxFds e hSpc
  have hTr : isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
  cases hCons : consumeRecvPendingSoError d with
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

/-- `stepIoctl` accepts `ENOSPC` on any live socket while preserving `ambientSeccomp`. -/
theorem stepIoctl_spc (s : NetState) (hid : HandleId) (selfFid : FileId)
    (d : SockDesc) (op : NetIoctlOp) (ifn : ByteArray)
    (hFid : lookupHandleFileId s hid = some selfFid)
    (hSock : lookupFileSocket s selfFid = .ok d) :
    ∃ s', stepIoctl s hid op ifn (some (.err Errno.ENOSPC)) = some (.err Errno.ENOSPC, s') ∧
      s'.ambientSeccomp = s.ambientSeccomp := by
  refine ⟨s, ?_, rfl⟩
  unfold stepIoctl
  rw [hFid]; dsimp only; rw [hSock]
  dsimp only
  have hTr : isTransientNetErrno Errno.ENOSPC = true := by decide
  by_cases h0 : (ifn.size == 0) = true
  · simp only [h0, ↓reduceIte]
    cases op <;> exact emitErr_spc s Errno.ENOSPC _ _ _ _ _ (Or.inl rfl) (by decide) (by decide)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases hLo : bytesEq ifn loIfname = true
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
      cases bytesAssocGet s.otherIfaces ifn <;> cases op <;> dsimp only
      all_goals
        first
        | exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide)
        | (simp only [hTr, Bool.or_true, ↓reduceIte]; done)
        | (split
           · exact emitErr_spc s Errno.ENOSPC _ _ _ _ _ (Or.inl rfl) (by decide) (by decide)
           · first
             | exact emitU32_spc s _ Errno.ENOSPC _ _ _ _ (Or.inl rfl) (by decide)
             | simp only [hTr, Bool.or_true, ↓reduceIte])

end LeanSwe.LinuxSyscall.Net.Proofs

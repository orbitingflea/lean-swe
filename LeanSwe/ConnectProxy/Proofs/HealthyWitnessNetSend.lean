import LeanSwe.ConnectProxy.Proofs.HealthyWitnessNetConn

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

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

/-- Internal ConnectProxy proof helper `stepSendto_spc`. -/
theorem stepSendto_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepShutdown_spc`. -/
theorem stepShutdown_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepSendmsg_spc`. -/
theorem stepSendmsg_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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
  have hNotPipe : (e == Errno.EPIPE) = false := by rcases hSpc with rfl | rfl <;> decide
  split
  · exact ⟨s, emitErr_spc s e _ _ _ none none hSpc (by rcases hSpc with rfl | rfl <;> decide)
      (by rcases hSpc with rfl | rfl <;> decide), rfl⟩
  · cases hCons : Net.consumePendingSoError d with
    | some pair =>
      rcases pair with ⟨pendErr, dClr⟩
      have hEqSo := consumePending_eq_soError d pendErr dClr hCons
      subst hEqSo
      refine ⟨s, ?_, rfl⟩
      have hTr : Net.isTransientNetErrno e = true := by rcases hSpc with rfl | rfl <;> decide
      simp only [hNeSo, hNotPipe, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [hTr]; rfl
    | none =>
      refine ⟨s, ?_, rfl⟩
      by_cases h1 : (!Net.isEstablished d) = true
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
              | udp _ _ _ | tcp _ _ _ _ _ =>
                exact emitErr_spc s e _ _ _ _ _ hSpc (by rcases hSpc with rfl | rfl <;> decide) rfl

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

/-- Internal ConnectProxy proof helper `stepRecvmsg_spc`. -/
theorem stepRecvmsg_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepIoctl_spc`. -/
theorem stepIoctl_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `emitErr_self_eq`. -/
theorem emitErr_self_eq (s : Net.NetState) (e : Errno) (alTr : Bool) :
    Net.emitErr (some (.err e)) s e [] (fun _ => s) alTr none none = some (.err e, s) := by
  unfold Net.emitErr
  dsimp only
  rw [beq_self_eq_true, Bool.true_or]
  rfl


end LeanSwe.ConnectProxy.Proofs

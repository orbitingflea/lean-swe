import LeanSwe.ConnectProxy.Proofs.HealthyWitnessBase

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

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

/-- Internal ConnectProxy proof helper `stepConnect_spc`. -/
theorem stepConnect_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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
    cases hDom : ((Net.normalizeUdpTarget d.domain addr bind.addr? d.inetSaddrZero).domain != d.domain) with
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

/-- Internal ConnectProxy proof helper `stepGetsockopt_spc`. -/
theorem stepGetsockopt_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepSetsockopt_spc`. -/
theorem stepSetsockopt_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepGetsockname_spc`. -/
theorem stepGetsockname_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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

/-- Internal ConnectProxy proof helper `stepRecvfrom_spc`. -/
theorem stepRecvfrom_spc (s : Net.NetState) (hid : Net.HandleId) (selfFid : Net.FileId)
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


end LeanSwe.ConnectProxy.Proofs

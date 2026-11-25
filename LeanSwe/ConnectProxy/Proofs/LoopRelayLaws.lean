import LeanSwe.ConnectProxy.Proofs.LoopPreservesWf

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


private theorem init_u2c_writeAvail_pos :
    decide ((({} : RingBuf).push Relay.reply200Bytes).writeAvail > 0) = true := by
  decide

private theorem init_u2c_len_le_cap :
    (({} : RingBuf).push Relay.reply200Bytes).len ≤ RING_CAP := by
  decide

/-- Internal ConnectProxy proof helper `stateT_bind_app`. -/
theorem stateT_bind_app {σ₁ σ₂ α β : Type}
    {x : StateM (σ₁ × σ₂) α} {k : α → StateM (σ₁ × σ₂) β}
    {w w' : σ₁} {tr tr' : σ₂} {res : β}
    (h : (x >>= k) (w, tr) = (res, (w', tr'))) :
    ∃ a w1 tr1, StateT.run x (w, tr) = (a, (w1, tr1)) ∧
      StateT.run (k a) (w1, tr1) = (res, (w', tr')) :=
  stateT_bind_eq h

private theorem stepBidirectionalRelay_pipe_of_u2c
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd ufd : Nat) (pipelined : ByteArray) (u2c0 : RingBuf)
    (hU2cList : u2c0.toList = Relay.reply200Bytes.data.toList)
    (fuel : Nat) (hFuel : fuel = Relay.MAX_RELAY_IO_STEPS)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true) :
    let st0 : RelayState Nat :=
      { clientFd? := some fd, upstreamFd? := some ufd,
        pendingPrefix := pipelined,
        pendingOff := 0, c2u := {}, u2c := u2c0 }
    let (stPipe, (w₃, tr₃)) :=
      (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
        st0 {} { pollout := true }).run (w₀, {})
    w₃.wf = true ∧
    (stPipe.uWrClosed = false →
      tr₃.sentBytes.toList ++
        (stPipe.pendingPrefix.extract stPipe.pendingOff stPipe.pendingPrefix.size).data.toList =
        pipelined.data.toList ∧
      (w₀.netEnv.eintrBudget + pipelined.size ≤ fuel →
        stPipe.prefixFlushed = true ∨ Errno.EAGAIN ∈ tr₃.netErrs.toList ∨ tr₃.sawZeroSend = true)) ∧
    (stPipe.uWrClosed = true →
      stPipe.clientFd? = some fd ∧ stPipe.u2c.toList = Relay.reply200Bytes.data.toList) := by
  dsimp only
  have hC2uEmp : ({} : RingBuf).isEmpty = true := rfl
  let st0 : RelayState Nat :=
    { clientFd? := some fd, upstreamFd? := some ufd,
      pendingPrefix := pipelined,
      pendingOff := 0, c2u := {}, u2c := u2c0 }
  rcases hTop : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    st0 {} { pollout := true }).run (w₀, {}) with ⟨stPipe, w₃, tr₃⟩
  have hRun : StateT.run (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    st0 {} { pollout := true }) (w₀, {}) = (stPipe, (w₃, tr₃)) := hTop
  clear hTop
  dsimp only
  unfold Relay.stepBidirectionalRelay at hRun
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
  obtain ⟨st1, w1, tr1, hPfx, hRun⟩ := stateT_bind_app hRun
  by_cases hPipe0 : (pipelined.size == 0) = true
  · have hSz0 : pipelined.size = 0 := beq_iff_eq.mp hPipe0
    have hPf : decide (0 ≥ pipelined.size) = true := decide_eq_true (by omega)
    unfold Relay.stepRelayPrefix Relay.RelayState.prefixFlushed at hPfx
    dsimp only [st0] at hPfx
    simp only [hPf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hPfx
    injection hPfx with hs1 hwt1; injection hwt1 with hw1 ht1
    subst hw1; subst ht1
    let st1Val : RelayState Nat :=
      { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := pipelined,
        pendingOff := 0, c2u := {}, u2c := u2c0 }
    have hSt1 : st1 = st1Val := hs1.symm
    rw [hSt1] at hRun
    simp only [st1Val, Relay.stepRelayClientRx, Relay.stepRelayUpstreamRx, Relay.stepRelayUpstreamTx,
      Relay.stepRelayClientTx, Relay.stepRelayShutdownUpstream, Relay.stepRelayShutdownClient,
      Relay.stepRelayReapIdle, Relay.reapIdleFd, hC2uEmp,
      StateT.run, bind, StateT.bind, pure, StateT.pure,
      Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
    injection hRun with hsp hwt; injection hwt with hw ht
    subst hw; subst ht; rw [← hsp]
    refine ⟨hWf₀, fun _ => ⟨?_, fun _ => Or.inl hPf⟩, fun hBad => (nomatch hBad)⟩
    dsimp only [st1Val]
    rw [byteArray_extract_end_toList]
    simp
  · have hPipePos : pipelined.size > 0 := by
      have hNe : pipelined.size ≠ 0 := fun hc => hPipe0 (beq_iff_eq.mpr hc)
      omega
    have hPf : decide (0 ≥ pipelined.size) = false := decide_eq_false (by omega)
    have hFl := flushBytesNonblock_instrumented_laws sys hRef ufd pipelined fuel 0 w₀ {} hWf₀
    unfold Relay.stepRelayPrefix Relay.RelayState.prefixFlushed at hPfx
    dsimp only [st0] at hPfx
    simp only [hPf, Bool.not_false, Bool.true_and, Bool.or_false, ↓reduceIte, ← hFuel] at hPfx
    obtain ⟨flRes, wFl, trFl, hFRun, hPfx⟩ := stateT_bind_app hPfx
    have hFRun' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net ufd pipelined fuel 0).run (w₀, {}) = (flRes, (wFl, trFl)) := hFRun
    rw [hFRun'] at hFl; dsimp only at hFl
    cases flRes with
    | none =>
      dsimp only [stateT_pure_run] at hPfx
      injection hPfx with hs1 hwt1; injection hwt1 with hw1 ht1
      subst hw1; subst ht1
      let st1Val : RelayState Nat :=
        { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := ByteArray.empty,
          pendingOff := 0, c2u := {}, u2c := u2c0, uWrClosed := true }
      have hSt1 : st1 = st1Val := hs1.symm
      rw [hSt1] at hRun
      simp only [st1Val, Relay.stepRelayClientRx, Relay.stepRelayUpstreamRx, Relay.stepRelayUpstreamTx,
        Relay.stepRelayClientTx, Relay.stepRelayShutdownUpstream, Relay.stepRelayShutdownClient,
        Relay.stepRelayReapIdle, Relay.reapIdleFd, hC2uEmp,
        StateT.run, bind, StateT.bind, pure, StateT.pure,
        Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
      injection hRun with hsp hwt; injection hwt with hw ht
      subst hw; subst ht; rw [← hsp]
      exact ⟨hFl.1, fun hBad => (nomatch hBad), fun _ => ⟨rfl, hU2cList⟩⟩
    | some nextOff =>
      dsimp only at hPfx
      rcases hFl.2.2.2.2.2.2.2 with ⟨⟨txDelta, hSentEq, hCons⟩, hProg⟩
      simp only [List.nil_append, List.drop_zero] at hSentEq hCons
      by_cases hDone : nextOff ≥ pipelined.size
      · simp only [hDone, ↓reduceIte, stateT_pure_run] at hPfx
        injection hPfx with hs1 hwt1; injection hwt1 with hw1 ht1
        subst hw1; subst ht1
        let st1Val : RelayState Nat :=
          { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := ByteArray.empty,
            pendingOff := 0, c2u := {}, u2c := u2c0 }
        have hSt1 : st1 = st1Val := hs1.symm
        rw [hSt1] at hRun
        simp only [st1Val, Relay.stepRelayClientRx, Relay.stepRelayUpstreamRx, Relay.stepRelayUpstreamTx,
          Relay.stepRelayClientTx, Relay.stepRelayShutdownUpstream, Relay.stepRelayShutdownClient,
          Relay.stepRelayReapIdle, Relay.reapIdleFd, hC2uEmp,
          StateT.run, bind, StateT.bind, pure, StateT.pure,
          Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
        injection hRun with hsp hwt; injection hwt with hw ht
        subst hw; subst ht; rw [← hsp]
        have hDropNil : pipelined.data.toList.drop nextOff = [] :=
          List.drop_eq_nil_of_le (by simp; omega)
        rw [hDropNil, List.append_nil] at hCons
        have hPfEmpty : decide (0 ≥ ByteArray.empty.size) = true := by decide
        have hPfDone : st1Val.prefixFlushed = true := hPfEmpty
        refine ⟨hFl.1, fun _ => ⟨?_, fun _ => Or.inl hPfDone⟩, fun hBad => (nomatch hBad)⟩
        rw [hSentEq, byteArray_extract_end_toList]
        simpa [st1Val] using hCons
      · simp only [hDone, ↓reduceIte, stateT_pure_run] at hPfx
        injection hPfx with hs1 hwt1; injection hwt1 with hw1 ht1
        subst hw1; subst ht1
        let st1Val : RelayState Nat :=
          { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := pipelined,
            pendingOff := nextOff, c2u := {}, u2c := u2c0 }
        have hSt1 : st1 = st1Val := hs1.symm
        rw [hSt1] at hRun
        simp only [st1Val, Relay.stepRelayClientRx, Relay.stepRelayUpstreamRx, Relay.stepRelayUpstreamTx,
          Relay.stepRelayClientTx, Relay.stepRelayShutdownUpstream, Relay.stepRelayShutdownClient,
          Relay.stepRelayReapIdle, Relay.reapIdleFd, hC2uEmp,
          StateT.run, bind, StateT.bind, pure, StateT.pure,
          Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
        injection hRun with hsp hwt; injection hwt with hw ht
        subst hw; subst ht; rw [← hsp]
        refine ⟨hFl.1, fun _ => ⟨?_, fun hB => ?_⟩, fun hBad => (nomatch hBad)⟩
        · dsimp only [st1Val]
          rw [hSentEq, byteArray_extract_end_toList]
          exact hCons
        · rcases hProg (by simpa using hB) with hGe | hRest
          · exact absurd hGe hDone
          · exact Or.inr hRest

/-- Pipelined `pendingPrefix` conservation and `200` reply preservation on `Relay.stepBidirectionalRelay`. -/
theorem healthy_stepBidirectionalRelay_pipe_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd ufd : Nat) (pipelined : ByteArray)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true) :
    let (stPipe, (w₃, tr₃)) :=
      (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
        (Relay.RelayState.init fd ufd pipelined) {} { pollout := true }).run (w₀, {})
    w₃.wf = true ∧
    (stPipe.uWrClosed = false →
      tr₃.sentBytes.toList ++
        (stPipe.pendingPrefix.extract stPipe.pendingOff stPipe.pendingPrefix.size).data.toList =
        pipelined.data.toList ∧
      (w₀.netEnv.eintrBudget + pipelined.size ≤ Relay.MAX_RELAY_IO_STEPS →
        stPipe.prefixFlushed = true ∨ Errno.EAGAIN ∈ tr₃.netErrs.toList ∨ tr₃.sawZeroSend = true)) ∧
    (stPipe.uWrClosed = true →
      stPipe.clientFd? = some fd ∧ stPipe.u2c.toList = Relay.reply200Bytes.data.toList) := by
  have hInitEq : Relay.RelayState.init fd ufd pipelined =
      { clientFd? := some fd, upstreamFd? := some ufd,
        pendingPrefix := pipelined,
        pendingOff := 0, c2u := {}, u2c := ({} : RingBuf).push Relay.reply200Bytes } := rfl
  rw [hInitEq]
  exact stepBidirectionalRelay_pipe_of_u2c sys hRef fd ufd pipelined
    (({} : RingBuf).push Relay.reply200Bytes) reply200_init_u2c_toList
    Relay.MAX_RELAY_IO_STEPS rfl w₀ hWf₀

private theorem stepBidirectionalRelay_rst_of_u2c
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd ufd : Nat) (u2c0 : RingBuf) (replyList : List UInt8)
    (hReplyNE : replyList ≠ [])
    (hAvPos : decide (u2c0.writeAvail > 0) = true)
    (hCap : u2c0.len ≤ u2c0.cap)
    (hU2cList : u2c0.toList = replyList)
    (fuel : Nat) (hFuel : fuel = Relay.MAX_RELAY_IO_STEPS)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true) :
    let st0 : RelayState Nat :=
      { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := ByteArray.empty, pendingOff := 0,
        c2u := {}, u2c := u2c0 }
    let (stRst, (w₄, tr₄)) :=
      (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
        st0 {} { pollin := true, pollerr := true, pollhup := true }).run (w₀, {})
    w₄.wf = true ∧
    ((∃ e ∈ tr₄.netErrs.toList,
        e = Errno.EBADF ∨ e = Errno.EINVAL ∨ e = Errno.ENOTSOCK) ∨
      (stRst.clientFd? = some fd ∧ stRst.u2c.toList = replyList ++ tr₄.recvBytes.toList)) := by
  dsimp only
  let st0 : RelayState Nat :=
    { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := ByteArray.empty, pendingOff := 0,
      c2u := {}, u2c := u2c0 }
  rcases hTop : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    st0 {} { pollin := true, pollerr := true, pollhup := true }).run (w₀, {}) with ⟨stRst, w₄, tr₄⟩
  have hRun : StateT.run (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    st0 {} { pollin := true, pollerr := true, pollhup := true }) (w₀, {}) = (stRst, (w₄, tr₄)) := hTop
  clear hTop
  dsimp only
  have hPf : decide (0 ≥ ByteArray.empty.size) = true := by decide
  have hRx := healthy_recvIntoRing_laws sys hRef ufd fuel u2c0 w₀ {} hWf₀ hCap
  unfold Relay.stepBidirectionalRelay at hRun
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
  obtain ⟨st1, w1a, tr1a, hPfx, hRun⟩ := stateT_bind_app hRun
  unfold Relay.stepRelayPrefix Relay.RelayState.prefixFlushed at hPfx
  dsimp only [st0] at hPfx
  simp only [hPf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hPfx
  injection hPfx with hs1 hwt1; injection hwt1 with hw1a ht1a
  subst hs1; subst hw1a; subst ht1a
  obtain ⟨st2?, w1b, tr1b, hCrx, hRun⟩ := stateT_bind_eq hRun
  unfold Relay.stepRelayClientRx at hCrx
  simp only [Bool.or_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hCrx
  injection hCrx with hs2 hwt2; injection hwt2 with hw1b ht1b
  subst hs2; subst hw1b; subst ht1b
  dsimp only at hRun
  obtain ⟨st3?, w1, tr1, hUrx, hRun⟩ := stateT_bind_eq hRun
  unfold Relay.stepRelayUpstreamRx at hUrx
  dsimp only at hUrx
  simp only [Bool.not_false, hAvPos, Bool.true_and, Bool.true_or, ↓reduceIte, ← hFuel] at hUrx
  obtain ⟨rxRes, wRx, trRx, hRR, hUrx⟩ := stateT_bind_app hUrx
  have hRR' : (NetRelay.recvIntoRing (instrumentSysOps sys).net ufd fuel u2c0).run (w₀, {}) = (rxRes, (wRx, trRx)) := hRR
  rw [hRR'] at hRx; dsimp only at hRx
  cases rxRes with
  | none =>
    dsimp only [stateT_pure_run] at hUrx
    injection hUrx with hs3 hwt3; injection hwt3 with hw1 ht1
    subst hs3; subst hw1; subst ht1
    dsimp only at hRun
    have hc := closeRelayBoth_wf_poll_netErrs sys hRef st0 wRx trRx hRx.1
    have hRun' : (Relay.closeRelayBoth (instrumentSysOps sys).closeFd st0).run (wRx, trRx) = (stRst, (w₄, tr₄)) := hRun
    rw [hRun'] at hc; dsimp only at hc
    refine ⟨hc.1, Or.inl ?_⟩
    rcases hRx.2.2.2 with ⟨e, heMem, hOr⟩
    rcases hOr with hNil | hBad
    · cases hNil
    · exact ⟨e, hc.2.2 ▸ heMem, hBad⟩
  | some pair =>
    rcases pair with ⟨u2c', eof'⟩
    simp only [stateT_pure_run, Bool.false_or] at hUrx
    injection hUrx with hs3 hwt3; injection hwt3 with hw1 ht1
    subst hs3; subst hw1; subst ht1
    dsimp only at hRun
    rcases hRx.2.2.2 with ⟨_, _, ⟨rxDelta, hRecvEq, hU2cEq⟩, _⟩
    simp only [List.nil_append] at hRecvEq
    rw [hU2cList] at hU2cEq
    have hU2cNonEmpty : u2c'.isEmpty = false := by
      apply ringBuf_not_empty_of_nonempty_toList
      rw [hU2cEq]
      intro hc
      exact hReplyNE (List.append_eq_nil_iff.mp hc).1
    have hC2uEmp : ({} : RingBuf).isEmpty = true := rfl
    cases eof' <;>
      simp only [Relay.stepRelayUpstreamTx, Relay.stepRelayClientTx,
        Relay.stepRelayShutdownUpstream, Relay.stepRelayShutdownClient,
        Relay.stepRelayReapIdle, Relay.reapIdleFd, hC2uEmp, hU2cNonEmpty,
        StateT.run, bind, StateT.bind, pure, StateT.pure,
        Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hRun
    all_goals
      injection hRun with hsr hwt4
      injection hwt4 with hw4 ht4
      subst hw4; subst ht4; rw [← hsr]
      exact ⟨hRx.1, Or.inr ⟨rfl, by rw [hU2cEq, hRecvEq]⟩⟩

private theorem reply200_list_ne_nil : Relay.reply200Bytes.data.toList ≠ [] := by
  decide

/-- Upstream `TCP RST` (`POLLIN | POLLERR | POLLHUP`) response preservation on `Relay.stepBidirectionalRelay`. -/
theorem healthy_stepBidirectionalRelay_rst_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd ufd : Nat)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true) :
    let (stRst, (w₄, tr₄)) :=
      (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
        (Relay.RelayState.init fd ufd ByteArray.empty)
        {} { pollin := true, pollerr := true, pollhup := true }).run (w₀, {})
    w₄.wf = true ∧
    ((∃ e ∈ tr₄.netErrs.toList,
        e = Errno.EBADF ∨ e = Errno.EINVAL ∨ e = Errno.ENOTSOCK) ∨
      (stRst.clientFd? = some fd ∧ stRst.u2c.toList = Relay.reply200Bytes.data.toList ++ tr₄.recvBytes.toList)) := by
  have hInitEq : Relay.RelayState.init fd ufd ByteArray.empty =
      { clientFd? := some fd, upstreamFd? := some ufd, pendingPrefix := ByteArray.empty, pendingOff := 0,
        c2u := {}, u2c := ({} : RingBuf).push Relay.reply200Bytes } := rfl
  rw [hInitEq]
  exact stepBidirectionalRelay_rst_of_u2c sys hRef fd ufd
    (({} : RingBuf).push Relay.reply200Bytes) Relay.reply200Bytes.data.toList
    reply200_list_ne_nil init_u2c_writeAvail_pos init_u2c_len_le_cap reply200_init_u2c_toList
    Relay.MAX_RELAY_IO_STEPS rfl w₀ hWf₀

private theorem array_push_preserve_01 {α : Type} (reqs : Array α) (x : α) (h2 : 2 ≤ reqs.size) :
    (reqs.push x)[0]? = reqs[0]? ∧ (reqs.push x)[1]? = reqs[1]? ∧ 2 ≤ (reqs.push x).size := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.getElem?_push]
    split
    · omega
    · rfl
  · rw [Array.getElem?_push]
    split
    · omega
    · rfl
  · rw [Array.size_push]; omega

private theorem buildPollBatchAux_laws
    (nowMs : Nat) :
    ∀ (slots : List (ClientSlot Nat Unit))
      (reqs : Array (Nat × Poll.PollEvents))
      (indices : Array (Option Nat × Option Nat))
      (minRem? : Option Nat),
      2 ≤ reqs.size →
      let (reqs', indices', _) :=
        Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs slots reqs indices minRem?)
      reqs'[0]? = reqs[0]? ∧
      reqs'[1]? = reqs[1]? ∧
      indices'.size = indices.size + slots.length
  | [], reqs, indices, minRem?, _ => by
    simp [buildPollBatchAux]
  | slot :: rest, reqs, indices, minRem?, hGe2 => by
    have hConsLen : (slot :: rest).length = rest.length + 1 := rfl
    unfold buildPollBatchAux
    cases slot.phase with
    | handshake cfd _ dl =>
      obtain ⟨h0, h1, hSz⟩ := array_push_preserve_01 reqs (cfd, { pollin := true }) hGe2
      have hSub := buildPollBatchAux_laws nowMs rest (reqs.push (cfd, { pollin := true }))
        (indices.push (some reqs.size, none)) (updatePollMinRem nowMs minRem? dl) hSz
      rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        (reqs.push (cfd, { pollin := true })) (indices.push (some reqs.size, none))
        (updatePollMinRem nowMs minRem? dl)) with ⟨r', i', m'⟩
      have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        (reqs.push (cfd, { pollin := true })) (indices.push (some reqs.size, none))
        (updatePollMinRem nowMs minRem? dl) = (r', i', m') := hB
      rw [hB] at hSub
      dsimp only at hSub
      dsimp only [Id.run]
      rw [hB']
      change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
      have hISz := hSub.2.2
      rw [Array.size_push] at hISz
      exact ⟨hSub.1.trans h0, hSub.2.1.trans h1, by omega⟩
    | dns cfd _ _ job =>
      obtain ⟨h0, h1, hSz⟩ := array_push_preserve_01 reqs (cfd, {}) hGe2
      have hSub := buildPollBatchAux_laws nowMs rest (reqs.push (cfd, {}))
        (indices.push (some reqs.size, none)) minRem? hSz
      rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        (reqs.push (cfd, {})) (indices.push (some reqs.size, none)) minRem?) with ⟨r', i', m'⟩
      have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        (reqs.push (cfd, {})) (indices.push (some reqs.size, none)) minRem? = (r', i', m') := hB
      rw [hB] at hSub
      dsimp only at hSub
      simp only [Id.run, bind, Bool.false_eq_true, ↓reduceIte]
      rw [hB']
      change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
      have hISz := hSub.2.2
      rw [Array.size_push] at hISz
      exact ⟨hSub.1.trans h0, hSub.2.1.trans h1, by omega⟩
    | connecting cfd ufd _ _ _ _ _ dl =>
      obtain ⟨h0a, h1a, hSza⟩ := array_push_preserve_01 reqs (cfd, {}) hGe2
      obtain ⟨h0b, h1b, hSzb⟩ := array_push_preserve_01 (reqs.push (cfd, {})) (ufd, { pollout := true }) hSza
      have hSub := buildPollBatchAux_laws nowMs rest ((reqs.push (cfd, {})).push (ufd, { pollout := true }))
        (indices.push (some reqs.size, some (reqs.push (cfd, {})).size)) (updatePollMinRem nowMs minRem? dl) hSzb
      rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        ((reqs.push (cfd, {})).push (ufd, { pollout := true }))
        (indices.push (some reqs.size, some (reqs.push (cfd, {})).size))
        (updatePollMinRem nowMs minRem? dl)) with ⟨r', i', m'⟩
      have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
        ((reqs.push (cfd, {})).push (ufd, { pollout := true }))
        (indices.push (some reqs.size, some (reqs.push (cfd, {})).size))
        (updatePollMinRem nowMs minRem? dl) = (r', i', m') := hB
      rw [hB] at hSub
      dsimp only at hSub
      dsimp only [Id.run]
      rw [hB']
      change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
      have hISz := hSub.2.2
      rw [Array.size_push] at hISz
      exact ⟨hSub.1.trans (h0b.trans h0a), hSub.2.1.trans (h1b.trans h1a), by omega⟩
    | relay st =>
      have finishCase : ∀ (reqs2 : Array (Nat × Poll.PollEvents)) (pairIdx : Option Nat × Option Nat),
          reqs2[0]? = reqs[0]? → reqs2[1]? = reqs[1]? → 2 ≤ reqs2.size →
          let (reqs', indices', _) :=
            buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs2 (indices.push pairIdx) minRem?
          reqs'[0]? = reqs[0]? ∧ reqs'[1]? = reqs[1]? ∧ indices'.size = indices.size + (slot :: rest).length := by
        intro reqs2 pairIdx hr0 hr1 hr2
        have hSub := buildPollBatchAux_laws nowMs rest reqs2 (indices.push pairIdx) minRem? hr2
        rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs2 (indices.push pairIdx) minRem?) with ⟨r', i', m'⟩
        have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs2 (indices.push pairIdx) minRem? = (r', i', m') := hB
        rw [hB] at hSub; rw [hB']; dsimp only at hSub ⊢
        have hISz := hSub.2.2
        rw [Array.size_push] at hISz
        exact ⟨hSub.1.trans hr0, hSub.2.1.trans hr1, by omega⟩
      cases hCFd : st.clientFd? with
      | none =>
        cases hUFd : st.upstreamFd? with
        | none =>
          simp only [Id.run, hCFd, hUFd]
          exact finishCase reqs (none, none) rfl rfl hGe2
        | some ufd =>
          cases hUEv : (!st.upstreamPollEvents.isEmpty) with
          | false =>
            simp only [Id.run, hCFd, hUFd, hUEv, Bool.false_eq_true, ↓reduceIte]
            exact finishCase reqs (none, none) rfl rfl hGe2
          | true =>
            simp only [Id.run, hCFd, hUFd, hUEv, ↓reduceIte]
            obtain ⟨h0, h1, hSz⟩ := array_push_preserve_01 reqs (ufd, st.upstreamPollEvents) hGe2
            exact finishCase _ _ h0 h1 hSz
      | some cfd =>
        cases hCEv : (!st.clientPollEvents.isEmpty) with
        | false =>
          cases hUFd : st.upstreamFd? with
          | none =>
            simp only [Id.run, hCFd, hCEv, hUFd, Bool.false_eq_true, ↓reduceIte]
            exact finishCase reqs (none, none) rfl rfl hGe2
          | some ufd =>
            cases hUEv : (!st.upstreamPollEvents.isEmpty) with
            | false =>
              simp only [Id.run, hCFd, hCEv, hUFd, hUEv, Bool.false_eq_true, ↓reduceIte]
              exact finishCase reqs (none, none) rfl rfl hGe2
            | true =>
              simp only [Id.run, hCFd, hCEv, hUFd, hUEv, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨h0, h1, hSz⟩ := array_push_preserve_01 reqs (ufd, st.upstreamPollEvents) hGe2
              exact finishCase _ _ h0 h1 hSz
        | true =>
          obtain ⟨h0a, h1a, hSza⟩ := array_push_preserve_01 reqs (cfd, st.clientPollEvents) hGe2
          cases hUFd : st.upstreamFd? with
          | none =>
            simp only [Id.run, hCFd, hCEv, hUFd, ↓reduceIte]
            exact finishCase _ _ h0a h1a hSza
          | some ufd =>
            cases hUEv : (!st.upstreamPollEvents.isEmpty) with
            | false =>
              simp only [Id.run, hCFd, hCEv, hUFd, hUEv, Bool.false_eq_true, ↓reduceIte]
              exact finishCase _ _ h0a h1a hSza
            | true =>
              simp only [Id.run, hCFd, hCEv, hUFd, hUEv, ↓reduceIte]
              obtain ⟨h0b, h1b, hSzb⟩ := array_push_preserve_01 (reqs.push (cfd, st.clientPollEvents)) (ufd, st.upstreamPollEvents) hSza
              exact finishCase _ _ (h0b.trans h0a) (h1b.trans h1a) hSzb
    | closingReply cfd? _ _ shutWr _ dl =>
      cases cfd? with
      | some cfd =>
        let ev : Poll.PollEvents := if shutWr then { pollin := true } else { pollout := true }
        obtain ⟨h0, h1, hSz⟩ := array_push_preserve_01 reqs (cfd, ev) hGe2
        have hSub := buildPollBatchAux_laws nowMs rest (reqs.push (cfd, ev))
          (indices.push (some reqs.size, none)) (updatePollMinRem nowMs minRem? dl) hSz
        rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
          (reqs.push (cfd, ev)) (indices.push (some reqs.size, none))
          (updatePollMinRem nowMs minRem? dl)) with ⟨r', i', m'⟩
        have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest
          (reqs.push (cfd, ev)) (indices.push (some reqs.size, none))
          (updatePollMinRem nowMs minRem? dl) = (r', i', m') := hB
        rw [hB] at hSub; dsimp only at hSub
        dsimp only [Id.run]
        dsimp only [ev] at hB'
        rw [hB']
        change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
        have hISz := hSub.2.2
        rw [Array.size_push] at hISz
        exact ⟨hSub.1.trans h0, hSub.2.1.trans h1, by omega⟩
      | none =>
        have hSub := buildPollBatchAux_laws nowMs rest reqs (indices.push (none, none)) minRem? hGe2
        rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs (indices.push (none, none)) minRem?) with ⟨r', i', m'⟩
        have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs (indices.push (none, none)) minRem? = (r', i', m') := hB
        rw [hB] at hSub; dsimp only at hSub
        dsimp only [Id.run]
        rw [hB']
        change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
        have hISz := hSub.2.2
        rw [Array.size_push] at hISz
        exact ⟨hSub.1, hSub.2.1, by omega⟩
    | done =>
      have hSub := buildPollBatchAux_laws nowMs rest reqs (indices.push (none, none)) minRem? hGe2
      rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs (indices.push (none, none)) minRem?) with ⟨r', i', m'⟩
      have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs rest reqs (indices.push (none, none)) minRem? = (r', i', m') := hB
      rw [hB] at hSub; dsimp only at hSub
      dsimp only [Id.run]
      rw [hB']
      change r'[0]? = reqs[0]? ∧ r'[1]? = reqs[1]? ∧ i'.size = indices.size + (slot :: rest).length
      have hISz := hSub.2.2
      rw [Array.size_push] at hISz
      exact ⟨hSub.1, hSub.2.1, by omega⟩

/-- Structural laws for `SysBridge.buildPollBatchSync`. -/
theorem buildPollBatchSync_laws
    (wakeR lfd maxTunnels nowMs : Nat)
    (slots : Array (ClientSlot Nat Unit)) :
    let (reqs, indices, timeout?) := buildPollBatchSync wakeR lfd maxTunnels nowMs slots
    reqs[0]? = some (wakeR, { pollin := true }) ∧
    reqs[1]? = some (lfd, { pollin := decide (slots.size < maxTunnels) }) ∧
    indices.size = slots.size ∧
    ∀ ts, timeout? = some ts → ts.isValid = true := by
  let initReqs : Array (Nat × Poll.PollEvents) :=
    #[(wakeR, { pollin := true }), (lfd, { pollin := decide (slots.size < maxTunnels) })]
  have hInitSz : 2 ≤ initReqs.size := by simp [initReqs]
  have hAux := buildPollBatchAux_laws nowMs slots.toList initReqs (Array.emptyWithCapacity slots.size) none hInitSz
  rcases hB : Id.run (buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs slots.toList initReqs
    (Array.emptyWithCapacity slots.size) none) with ⟨reqs, indices, minRem?⟩
  have hB' : buildPollBatchAux (m := Id) (fun () => (false : Id Bool)) nowMs slots.toList initReqs
    (Array.emptyWithCapacity slots.size) none = (reqs, indices, minRem?) := hB
  rw [hB] at hAux
  dsimp only [buildPollBatchSync, buildPollBatchM, listenPollEventsWithBackoff, initPollBackoffRem,
    listenPollEvents, Id.run, bind]
  dsimp only [initReqs] at hB'
  have hB'' : buildPollBatchAux (m := Id) (fun () => false) nowMs slots.toList
      #[(wakeR, { pollin := true }), (lfd, { pollin := decide (slots.size < maxTunnels) })]
      (Array.emptyWithCapacity slots.size) none (fun _ => none) = (reqs, indices, minRem?) := by
    simpa [Pure.pure] using hB'
  dsimp only [pure]
  rw [hB'']
  dsimp only [initReqs] at hAux
  have hISz : indices.size = slots.size := by
    have h0 : (Array.emptyWithCapacity slots.size : Array (Option Nat × Option Nat)).size = 0 := rfl
    have hL : slots.toList.length = slots.size := Array.length_toList
    have hA := hAux.2.2
    omega
  refine ⟨hAux.1, hAux.2.1, hISz, fun ts hTs => ?_⟩
  cases minRem? with
  | none => cases hTs
  | some ms =>
    dsimp only [Option.map] at hTs
    injection hTs with hEq
    subst hEq
    unfold Poll.msToPollTimespec Poll.Timespec.isValid Poll.NANOS_PER_SEC
    simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]
    have hCap : Nat.min (ms / 1000) 9223372036854775807 ≤ 9223372036854775807 := Nat.min_le_right _ _
    have hMod : ms % 1000 < 1000 := Nat.mod_lt ms (by decide)
    refine ⟨?_, ?_⟩
    · rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt, Int.bmod_eq_of_le]
      · have : (0 : Int64).toInt = 0 := rfl; omega
      · change -9223372036854775808 ≤ (↑(Nat.min (ms / 1000) 9223372036854775807) : Int); omega
      · change (↑(Nat.min (ms / 1000) 9223372036854775807) : Int) < 9223372036854775808; omega
    · rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by change ms % 1000 * 1000000 < 4294967296; omega)]
      have : (1000000000 : UInt32).toNat = 1000000000 := rfl
      omega


end LeanSwe.ConnectProxy.Proofs

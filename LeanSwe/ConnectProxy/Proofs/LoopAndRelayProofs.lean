import LeanSwe.ConnectProxy.Proofs.SysBridgeProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Proofs
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

private def PreservesWfPoll (tr₀ : SysAuditTrace Nat) {α : Type}
    (m : StateM (HealthySysWorld × SysAuditTrace Nat) α) : Prop :=
  ∀ w tr, w.wf = true → tr.pollOutcomes = tr₀.pollOutcomes →
    let (_, (w', tr')) := m.run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr₀.pollOutcomes

private theorem pres_pure {tr₀ : SysAuditTrace Nat} {α : Type} (a : α) :
    PreservesWfPoll tr₀ (pure a) :=
  fun _ _ hw hp => ⟨hw, hp⟩

private theorem pres_bind {tr₀ : SysAuditTrace Nat} {α β : Type}
    {m : StateM (HealthySysWorld × SysAuditTrace Nat) α}
    {k : α → StateM (HealthySysWorld × SysAuditTrace Nat) β}
    (hm : PreservesWfPoll tr₀ m)
    (hk : ∀ a, PreservesWfPoll tr₀ (k a)) :
    PreservesWfPoll tr₀ (m >>= k) := by
  intro w tr hw hp
  have h1 := hm w tr hw hp
  dsimp only [StateT.run, bind, StateT.bind] at h1 ⊢
  rcases hR : m (w, tr) with ⟨a, wt1⟩
  rcases wt1 with ⟨w1, tr1⟩
  rw [hR] at h1
  exact hk a w1 tr1 h1.1 h1.2

private theorem pres_closeFd (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (d : Nat) :
    PreservesWfPoll tr₀ ((instrumentSysOps sys).closeFd d) := by
  intro w tr hw hp
  have hc := healthy_closeFd_instrumented_laws sys hRef w tr d hw
  rcases hR : ((instrumentSysOps sys).closeFd d).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hc
  exact ⟨hc.1, (by rw [hc.2.2.1] : tr'.pollOutcomes = tr.pollOutcomes).trans hp⟩

private theorem closeOptFd_wf_poll_netErrs
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (optFd : Option Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := (NetRelay.closeOptFd (instrumentSysOps sys).closeFd optFd).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes ∧ tr'.netErrs = tr.netErrs := by
  cases optFd with
  | none => exact ⟨hWf, rfl, rfl⟩
  | some d =>
    unfold NetRelay.closeOptFd NetRelay.Internal.closeOptFd
    have hCl := healthy_closeFd_instrumented_laws sys hRef w tr d hWf
    rcases hR : ((instrumentSysOps sys).closeFd d).run (w, tr) with ⟨_, w', tr'⟩
    rw [hR] at hCl
    dsimp only at hCl ⊢
    exact ⟨hCl.1, by rw [hCl.2.2.1], by rw [hCl.2.2.1]⟩

private theorem closeRelayBoth_wf_poll_netErrs
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (st : RelayState Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := (Relay.closeRelayBoth (instrumentSysOps sys).closeFd st).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes ∧ tr'.netErrs = tr.netErrs := by
  unfold Relay.closeRelayBoth
  rw [stateT_bind_run]
  have h1 := closeOptFd_wf_poll_netErrs sys hRef st.clientFd? w tr hWf
  rcases hR1 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.clientFd?).run (w, tr) with ⟨_, w1, tr1⟩
  rw [hR1] at h1
  dsimp only at h1 ⊢
  rw [stateT_bind_run]
  have h2 := closeOptFd_wf_poll_netErrs sys hRef st.upstreamFd? w1 tr1 h1.1
  rcases hR2 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.upstreamFd?).run (w1, tr1) with ⟨_, w2, tr2⟩
  rw [hR2] at h2
  dsimp only [stateT_pure_run] at h2 ⊢
  exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

private theorem pres_closeRelayBoth (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st : RelayState Nat) :
    PreservesWfPoll tr₀ (Relay.closeRelayBoth (instrumentSysOps sys).closeFd st) := by
  intro w tr hw hp
  have hc := closeRelayBoth_wf_poll_netErrs sys hRef st w tr hw
  rcases hR : (Relay.closeRelayBoth (instrumentSysOps sys).closeFd st).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hc
  exact ⟨hc.1, hc.2.1.trans hp⟩

private theorem recvIntoRing_wf_poll
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      ((NetRelay.recvIntoRing (instrumentSysOps sys).net fd fuel rb).run (w, tr)).2.1.wf = true ∧
      ((NetRelay.recvIntoRing (instrumentSysOps sys).net fd fuel rb).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, _, w, _, hWf => ⟨hWf, rfl⟩
  | fuel + 1, rb, w, tr, hWf => by
    unfold NetRelay.recvIntoRing NetRelay.Internal.recvIntoRing
    by_cases hAv0 : (NetRelay.Internal.ringBufWriteAvail rb == 0) = true
    · simp only [hAv0, ↓reduceIte]; exact ⟨hWf, rfl⟩
    · simp only [Bool.eq_false_iff.mpr hAv0, Bool.false_eq_true, ↓reduceIte]
      let reqCap := Nat.min (NetRelay.Internal.ringBufWriteAvail rb) MAX_READ_BYTES.toNat
      have hNet := hRef.2.1 w (.recvfrom fd (UInt32.ofNat reqCap) { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [inst_net_recvfrom]
      rcases hR : sys.net.recvfrom fd (UInt32.ofNat reqCap) { dontwait := true } w with ⟨r, w1⟩
      rw [hR] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      cases r with
      | ok bs =>
        by_cases h0 : (bs.size == 0) = true
        · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl⟩
        · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
          let chunk := if bs.size ≤ reqCap then bs else bs.extract 0 reqCap
          exact recvIntoRing_wf_poll sys hRef fd fuel (rb.push chunk) w1 _ hWf1
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          exact recvIntoRing_wf_poll sys hRef fd fuel rb w1 tr hWf1
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte]; exact ⟨hWf1, rfl⟩
          · simp only [Bool.eq_false_iff.mpr hAg, Bool.false_eq_true, ↓reduceIte]
            split <;> exact ⟨hWf1, rfl⟩

private theorem flushRingNonblock_wf_poll
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      ((NetRelay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb).run (w, tr)).2.1.wf = true ∧
      ((NetRelay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, _, w, _, hWf => ⟨hWf, rfl⟩
  | fuel + 1, rb, w, tr, hWf => by
    unfold NetRelay.flushRingNonblock NetRelay.Internal.flushRingNonblock
    by_cases hEmp : NetRelay.Internal.ringBufIsEmpty rb = true
    · simp only [hEmp, ↓reduceIte]; exact ⟨hWf, rfl⟩
    · simp only [Bool.eq_false_iff.mpr hEmp, Bool.false_eq_true, ↓reduceIte]
      have hNet := hRef.2.1 w (.sendto fd (NetRelay.Internal.ringBufFrontSlice rb) { nosignal := true, dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [inst_net_sendto]
      rcases hR : sys.net.sendto fd (NetRelay.Internal.ringBufFrontSlice rb) { nosignal := true, dontwait := true } w with ⟨r, w1⟩
      rw [hR] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      cases r with
      | ok n =>
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte]; exact ⟨hWf1, rfl⟩
        · simp only [Bool.eq_false_iff.mpr hn0, Bool.false_eq_true, ↓reduceIte]
          exact flushRingNonblock_wf_poll sys hRef fd fuel (rb.consume n.toNat) w1 _ hWf1
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          exact flushRingNonblock_wf_poll sys hRef fd fuel rb w1 tr hWf1
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
          split <;> exact ⟨hWf1, rfl⟩

private theorem flushBytesNonblock_pollOutcomes_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (fd : Nat) (bytes : ByteArray) :
    ∀ (fuel off : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      ((NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, _, _, _ => rfl
  | fuel + 1, off, w, tr => by
    unfold NetRelay.flushBytesNonblock NetRelay.Internal.flushBytesNonblock
    by_cases hGe : off ≥ bytes.size
    · simp only [hGe, ↓reduceIte]; rfl
    · simp only [hGe, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [inst_net_sendto]
      rcases sys.net.sendto fd (if off == 0 then bytes else bytes.extract off bytes.size) { nosignal := true, dontwait := true } w with ⟨r, w1⟩
      dsimp only
      cases r with
      | ok n =>
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte]; rfl
        · simp only [Bool.eq_false_iff.mpr hn0, Bool.false_eq_true, ↓reduceIte]
          exact flushBytesNonblock_pollOutcomes_eq sys fd bytes fuel _ w1 _
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          exact flushBytesNonblock_pollOutcomes_eq sys fd bytes fuel off w1 tr
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
          split <;> rfl

private theorem drainDeadPeerRx_wf_poll
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      ((NetRelay.drainDeadPeerRx (instrumentSysOps sys).net fd fuel).run (w, tr)).2.1.wf = true ∧
      ((NetRelay.drainDeadPeerRx (instrumentSysOps sys).net fd fuel).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, w, _, hWf => ⟨hWf, rfl⟩
  | fuel + 1, w, tr, hWf => by
    unfold NetRelay.drainDeadPeerRx NetRelay.Internal.drainDeadPeerRx
    have hNet := hRef.2.1 w (.recvfrom fd 4096 { dontwait := true }) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    rw [inst_net_recvfrom]
    rcases hR : sys.net.recvfrom fd 4096 { dontwait := true } w with ⟨r, w1⟩
    rw [hR] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    cases r with
    | ok bs =>
      by_cases h0 : (bs.size == 0) = true
      · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl⟩
      · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
        exact drainDeadPeerRx_wf_poll sys hRef fd fuel w1 _ hWf1
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        exact drainDeadPeerRx_wf_poll sys hRef fd fuel w1 tr hWf1
      · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
        split <;> exact ⟨hWf1, rfl⟩

private theorem pres_drainDeadPeerRx (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (fd fuel : Nat) :
    PreservesWfPoll tr₀ (NetRelay.drainDeadPeerRx (instrumentSysOps sys).net fd fuel) := by
  intro w tr hw hp
  have hL := drainDeadPeerRx_wf_poll sys hRef fd fuel w tr hw
  rcases hR : (NetRelay.drainDeadPeerRx (instrumentSysOps sys).net fd fuel).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hL
  exact ⟨hL.1, hL.2.trans hp⟩

private theorem pres_recvIntoRing (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (fd fuel : Nat) (rb : RingBuf) :
    PreservesWfPoll tr₀ (NetRelay.recvIntoRing (instrumentSysOps sys).net fd fuel rb) := by
  intro w tr hw hp
  have hL := recvIntoRing_wf_poll sys hRef fd fuel rb w tr hw
  rcases hR : (NetRelay.recvIntoRing (instrumentSysOps sys).net fd fuel rb).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hL
  exact ⟨hL.1, hL.2.trans hp⟩

private theorem pres_flushRing (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (fd fuel : Nat) (rb : RingBuf) :
    PreservesWfPoll tr₀ (NetRelay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb) := by
  intro w tr hw hp
  have hL := flushRingNonblock_wf_poll sys hRef fd fuel rb w tr hw
  rcases hR : (NetRelay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hL
  exact ⟨hL.1, hL.2.trans hp⟩

private theorem pres_flushBytes (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat)
    (fd : Nat) (bytes : ByteArray) (fuel off : Nat) :
    PreservesWfPoll tr₀ (NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off) := by
  intro w tr hw hp
  have hL := flushBytesNonblock_instrumented_laws sys hRef fd bytes fuel off w tr hw
  have hPo := flushBytesNonblock_pollOutcomes_eq sys fd bytes fuel off w tr
  rcases hR : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hL hPo
  exact ⟨hL.1, hPo.trans hp⟩

private theorem pres_shutdownWr (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (fd fuel : Nat) :
    PreservesWfPoll tr₀ (NetRelay.shutdownWrClean (instrumentSysOps sys).net fd fuel) := by
  intro w tr hw hp
  have hs := shutdownWrClean_instrumented_laws sys hRef fd fuel w tr hw
  rcases hR : (NetRelay.shutdownWrClean (instrumentSysOps sys).net fd fuel).run (w, tr) with ⟨_, w', tr'⟩
  rw [hR] at hs
  exact ⟨hs.1, (congrArg SysAuditTrace.pollOutcomes hs.2.1).trans hp⟩

private theorem pres_stepRelayPrefix (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st0 : RelayState Nat) (uRev : Poll.PollEvents) :
    PreservesWfPoll tr₀ (Relay.stepRelayPrefix (instrumentSysOps sys).net st0 uRev) := by
  unfold Relay.stepRelayPrefix
  split
  · cases st0.upstreamFd? with
    | none => exact pres_pure _
    | some ufd =>
      refine pres_bind (pres_flushBytes sys hRef tr₀ ufd st0.pendingPrefix MAX_RELAY_IO_STEPS st0.pendingOff) (fun r => ?_)
      cases r with
      | none => exact pres_pure _
      | some _ => dsimp only; split <;> exact pres_pure _
  · exact pres_pure _

private theorem pres_stepRelayClientRx (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st1 : RelayState Nat) (cRev : Poll.PollEvents) :
    PreservesWfPoll tr₀ (Relay.stepRelayClientRx (instrumentSysOps sys).net st1 cRev) := by
  unfold Relay.stepRelayClientRx
  split
  · split
    · cases st1.clientFd? with
      | none => exact pres_pure _
      | some cfd =>
        exact pres_bind (pres_drainDeadPeerRx sys hRef tr₀ cfd MAX_RELAY_IO_STEPS) (fun _ => pres_pure _)
    · split
      · cases st1.clientFd? with
        | none => exact pres_pure _
        | some cfd =>
          refine pres_bind (pres_recvIntoRing sys hRef tr₀ cfd MAX_RELAY_IO_STEPS st1.c2u) (fun r => ?_)
          rcases r with _ | ⟨_, _⟩ <;> exact pres_pure _
      · exact pres_pure _
  · exact pres_pure _

private theorem pres_stepRelayUpstreamRx (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st2 : RelayState Nat) (uRev : Poll.PollEvents) :
    PreservesWfPoll tr₀ (Relay.stepRelayUpstreamRx (instrumentSysOps sys).net st2 uRev) := by
  unfold Relay.stepRelayUpstreamRx
  split
  · cases st2.upstreamFd? with
    | none => exact pres_pure _
    | some ufd =>
      refine pres_bind (pres_recvIntoRing sys hRef tr₀ ufd MAX_RELAY_IO_STEPS st2.u2c) (fun r => ?_)
      rcases r with _ | ⟨_, _⟩ <;> exact pres_pure _
  · exact pres_pure _

private theorem pres_stepRelayUpstreamTx (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st3 : RelayState Nat) (uRev : Poll.PollEvents) :
    PreservesWfPoll tr₀ (Relay.stepRelayUpstreamTx (instrumentSysOps sys).net st3 uRev) := by
  unfold Relay.stepRelayUpstreamTx
  split
  · cases st3.upstreamFd? with
    | none => exact pres_pure _
    | some ufd =>
      exact pres_bind (pres_flushRing sys hRef tr₀ ufd MAX_RELAY_IO_STEPS st3.c2u) (fun r => by cases r <;> exact pres_pure _)
  · exact pres_pure _

private theorem pres_stepRelayClientTx (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st4 : RelayState Nat) (cRev : Poll.PollEvents) :
    PreservesWfPoll tr₀ (Relay.stepRelayClientTx (instrumentSysOps sys).net st4 cRev) := by
  unfold Relay.stepRelayClientTx
  split
  · cases st4.clientFd? with
    | none => exact pres_pure _
    | some cfd =>
      refine pres_bind (pres_flushRing sys hRef tr₀ cfd MAX_RELAY_IO_STEPS st4.u2c) (fun r => ?_)
      cases r with
      | none => dsimp only; split <;> exact pres_pure _
      | some _ => exact pres_pure _
  · exact pres_pure _

private theorem pres_stepRelayShutdownUpstream (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st5 : RelayState Nat) :
    PreservesWfPoll tr₀ (Relay.stepRelayShutdownUpstream (instrumentSysOps sys).net st5) := by
  unfold Relay.stepRelayShutdownUpstream
  split
  · cases st5.upstreamFd? with
    | none => exact pres_pure _
    | some ufd =>
      exact pres_bind (pres_shutdownWr sys hRef tr₀ ufd MAX_RELAY_IO_STEPS) (fun ok => by cases ok <;> exact pres_pure _)
  · exact pres_pure _

private theorem pres_stepRelayShutdownClient (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st6 : RelayState Nat) :
    PreservesWfPoll tr₀ (Relay.stepRelayShutdownClient (instrumentSysOps sys).net st6) := by
  unfold Relay.stepRelayShutdownClient
  split
  · cases st6.clientFd? with
    | none => exact pres_pure _
    | some cfd =>
      exact pres_bind (pres_shutdownWr sys hRef tr₀ cfd MAX_RELAY_IO_STEPS) (fun ok => by cases ok <;> exact pres_pure _)
  · exact pres_pure _

private theorem pres_reapIdleFd (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (optFd : Option Nat) (done : Bool) :
    PreservesWfPoll tr₀ (Relay.reapIdleFd (instrumentSysOps sys).closeFd optFd done) := by
  unfold Relay.reapIdleFd
  cases optFd with
  | none => exact pres_pure _
  | some d =>
    dsimp only; split
    · exact pres_bind (pres_closeFd sys hRef tr₀ d) (fun _ => pres_pure _)
    · exact pres_pure _

private theorem pres_stepRelayReapIdle (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) (tr₀ : SysAuditTrace Nat) (st7 : RelayState Nat) :
    PreservesWfPoll tr₀ (Relay.stepRelayReapIdle (instrumentSysOps sys).closeFd st7) := by
  unfold Relay.stepRelayReapIdle
  refine pres_bind (pres_reapIdleFd sys hRef tr₀ st7.clientFd? (st7.cEof && st7.cWrClosed)) (fun _ => ?_)
  exact pres_bind (pres_reapIdleFd sys hRef tr₀ st7.upstreamFd? (st7.uEof && st7.uWrClosed)) (fun _ => pres_pure _)

/-- General `wf` and `pollOutcomes` preservation of `Relay.stepBidirectionalRelay`. -/
theorem healthy_stepBidirectionalRelay_wf
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (st0 : RelayState Nat) (cRev uRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) :=
      (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd st0 cRev uRev).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  suffices hPres : PreservesWfPoll tr (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd st0 cRev uRev) from
    hPres w tr hWf rfl
  unfold Relay.stepBidirectionalRelay
  split
  · exact pres_closeRelayBoth sys hRef tr st0
  · refine pres_bind (pres_stepRelayPrefix sys hRef tr st0 uRev) (fun st1 => ?_)
    refine pres_bind (pres_stepRelayClientRx sys hRef tr st1 cRev) (fun st2? => ?_)
    cases st2? with
    | none => exact pres_closeRelayBoth sys hRef tr st1
    | some st2 =>
      refine pres_bind (pres_stepRelayUpstreamRx sys hRef tr st2 uRev) (fun st3? => ?_)
      cases st3? with
      | none => exact pres_closeRelayBoth sys hRef tr st2
      | some st3 =>
        refine pres_bind (pres_stepRelayUpstreamTx sys hRef tr st3 uRev) (fun st4 => ?_)
        refine pres_bind (pres_stepRelayClientTx sys hRef tr st4 cRev) (fun st5? => ?_)
        cases st5? with
        | none => exact pres_closeRelayBoth sys hRef tr st4
        | some st5 =>
          refine pres_bind (pres_stepRelayShutdownUpstream sys hRef tr st5) (fun st6? => ?_)
          cases st6? with
          | none => exact pres_closeRelayBoth sys hRef tr st5
          | some st6 =>
            refine pres_bind (pres_stepRelayShutdownClient sys hRef tr st6) (fun st7? => ?_)
            cases st7? with
            | none => exact pres_closeRelayBoth sys hRef tr st6
            | some st7 => exact pres_stepRelayReapIdle sys hRef tr st7

private theorem init_u2c_writeAvail_pos :
    decide ((({} : RingBuf).push Relay.reply200Bytes).writeAvail > 0) = true := by
  decide

private theorem init_u2c_len_le_cap :
    (({} : RingBuf).push Relay.reply200Bytes).len ≤ RING_CAP := by
  decide

private theorem stateT_bind_app {σ₁ σ₂ α β : Type}
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
    exact Poll.msToPollTimespec_isValid ms

private theorem drainWakeSocket_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (wakeR : Nat) :
    ∀ (fuel : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      ((drainWakeSocket (instrumentSysOps sys).net wakeR fuel).run (w, tr)).2.1.wf = true ∧
      ((drainWakeSocket (instrumentSysOps sys).net wakeR fuel).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, w, _, hWf => ⟨hWf, rfl⟩
  | fuel + 1, w, tr, hWf => by
    unfold drainWakeSocket
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    have hNet := hRef.2.1 w (.recvfrom wakeR 256 { dontwait := true }) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    rw [inst_net_recvfrom]
    rcases hRun : sys.net.recvfrom wakeR 256 { dontwait := true } w with ⟨r, w1⟩
    rw [hRun] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    cases r with
    | ok bs =>
      by_cases h0 : (bs.size == 0) = true
      · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl⟩
      · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
        exact drainWakeSocket_laws sys hRef wakeR fuel w1 _ hWf1
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        exact drainWakeSocket_laws sys hRef wakeR fuel w1 tr hWf1
      · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hWf1, rfl⟩

private theorem drainClosingClient_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) :
    ∀ (fuel drained : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (_, (w', tr')) := (drainClosingClient (instrumentSysOps sys).net cfd fuel drained).run (w, tr)
      w'.wf = true ∧
      tr'.pollOutcomes = tr.pollOutcomes ∧
      tr'.closedFds = tr.closedFds ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup)
  | 0, _, w, _, hWf => ⟨hWf, rfl, rfl, id⟩
  | fuel + 1, drained, w, tr, hWf => by
    unfold drainClosingClient
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    have hNet := hRef.2.1 w (.recvfrom cfd 1024 { dontwait := true }) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    rw [inst_net_recvfrom]
    rcases hRun : sys.net.recvfrom cfd 1024 { dontwait := true } w with ⟨r, w1⟩
    rw [hRun] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    have hNd1 := hNet.2.2.2
    cases r with
    | ok bs =>
      by_cases h0 : (bs.size == 0) = true
      · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
      · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
        by_cases hMax : drained + bs.size ≥ CLOSING_DRAIN_MAX
        · simp only [hMax, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
        · simp only [hMax, ↓reduceIte]
          let k := Nat.min bs.size (1024 : UInt32).toNat
          let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
          let tr1 : SysAuditTrace Nat := { tr with recvBytes := tr.recvBytes ++ accepted }
          have hSub := drainClosingClient_laws sys hRef cfd fuel (drained + bs.size) w1 tr1 hWf1
          dsimp only [StateT.run, tr1, accepted, k] at hSub ⊢
          rcases hRec : drainClosingClient (instrumentSysOps sys).net cfd fuel (drained + bs.size)
            (w1, { tr with recvBytes := tr.recvBytes ++ if (Nat.min bs.size (1024 : UInt32).toNat) == bs.size then bs.data else (bs.extract 0 (Nat.min bs.size (1024 : UInt32).toNat)).data }) with ⟨r2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRec] at hSub
          exact ⟨hSub.1, hSub.2.1, hSub.2.2.1, fun h0 => hSub.2.2.2 (hNd1 h0)⟩
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        have hSub := drainClosingClient_laws sys hRef cfd fuel drained w1 tr hWf1
        dsimp only [StateT.run] at hSub ⊢
        rcases hRec : drainClosingClient (instrumentSysOps sys).net cfd fuel drained (w1, tr) with ⟨r2, wt2⟩
        rcases wt2 with ⟨w2, tr2⟩
        rw [hRec] at hSub
        exact ⟨hSub.1, hSub.2.1, hSub.2.2.1, fun h0 => hSub.2.2.2 (hNd1 h0)⟩
      · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
        by_cases hAg : (e == Errno.EAGAIN) = true
        · simp only [hAg, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
        · simp only [Bool.eq_false_iff.mpr hAg, Bool.false_eq_true, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩

private theorem closingSendStep_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (cRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  rcases hTop : (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr) with ⟨res, w', tr'⟩
  have hRun : StateT.run (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev) (w, tr) = (res, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold closingSendStep at hRun
  split at hRun
  · split at hRun
    · dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl, id⟩
    · split at hRun
      · obtain ⟨flRes, w1a, tr1a, hFl, hRun⟩ := stateT_bind_app hRun
        have hL := flushBytesNonblock_instrumented_laws sys hRef cfd replyBytes MAX_CLOSING_STEPS replyOff w tr hWf
        have hPo := flushBytesNonblock_pollOutcomes_eq sys cfd replyBytes MAX_CLOSING_STEPS replyOff w tr
        have hFl' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net cfd replyBytes MAX_CLOSING_STEPS replyOff).run (w, tr) = (flRes, (w1a, tr1a)) := hFl
        rw [hFl'] at hL hPo; dsimp only at hL hPo
        cases flRes with
        | none =>
          dsimp only [stateT_pure_run] at hRun
          injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
          exact ⟨hL.1, hPo, hL.2.2.2.2.1⟩
        | some nextOff =>
          dsimp only at hRun
          split at hRun
          · obtain ⟨okS, w1b, tr1b, hSh, hRun⟩ := stateT_bind_eq hRun
            have hShL := shutdownWrClean_instrumented_laws sys hRef cfd 16 w1a tr1a hL.1
            have hSh' : (NetRelay.shutdownWrClean (instrumentSysOps sys).net cfd 16).run (w1a, tr1a) = (okS, (w1b, tr1b)) := hSh
            rw [hSh'] at hShL; dsimp only at hShL
            cases okS
            · simp only [Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hRun
              injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
              exact ⟨hShL.1, (congrArg SysAuditTrace.pollOutcomes hShL.2.1).trans hPo, fun h0 => hShL.2.2 (hL.2.2.2.2.1 h0)⟩
            · simp only [↓reduceIte, stateT_pure_run] at hRun
              injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
              exact ⟨hShL.1, (congrArg SysAuditTrace.pollOutcomes hShL.2.1).trans hPo, fun h0 => hShL.2.2 (hL.2.2.2.2.1 h0)⟩
          · dsimp only [stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
            exact ⟨hL.1, hPo, hL.2.2.2.2.1⟩
      · dsimp only [stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact ⟨hWf, rfl, id⟩
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl, id⟩

private theorem closingDrainStep_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) (shut1 : Bool) (drained : Nat) (cRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  rcases hTop : (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w, tr) with ⟨res, w', tr'⟩
  have hRun : StateT.run (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev) (w, tr) = (res, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold closingDrainStep at hRun
  split at hRun
  · have hDr := drainClosingClient_laws sys hRef cfd MAX_CLOSING_STEPS drained w tr hWf
    have hRun' : (drainClosingClient (instrumentSysOps sys).net cfd MAX_CLOSING_STEPS drained).run (w, tr) = (res, (w', tr')) := hRun
    rw [hRun'] at hDr
    exact ⟨hDr.1, hDr.2.1, hDr.2.2.2⟩
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl, id⟩

/-- Relational laws for `stepClosingReply` (and `stepSlotSync` on `.closingReply`). -/
theorem healthy_stepClosingReply_laws {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (slot : ClientSlot Nat dnsJob)
    (cfd? : Option Nat)
    (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (drained deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (slot', (w', tr')) :=
      (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    (∀ d, cfd? = some d →
      (nowMs ≥ deadlineMs → slot'.phase = .done) ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → slot'.phase = .done →
        d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none)) := by
  rcases hTop : (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs).run (w, tr) with ⟨slot', w', tr'⟩
  have hRun : StateT.run (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs) (w, tr) = (slot', (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold stepClosingReply at hRun
  cases cfd? with
  | none =>
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
    exact ⟨hWf, rfl, fun _ hc => nomatch hc⟩
  | some cfd =>
    have hCloseDone : ∀ wx trx,
        wx.wf = true →
        trx.pollOutcomes = tr.pollOutcomes →
        ((w.filesEnv.state.fds.map Prod.fst).Nodup → (wx.filesEnv.state.fds.map Prod.fst).Nodup) →
        StateT.run (do (instrumentSysOps sys).closeFd cfd; pure { slot with phase := SlotPhase.done }) (wx, trx) = (slot', (w', tr')) →
        w'.wf = true ∧
        tr'.pollOutcomes = tr.pollOutcomes ∧
        (∀ d, some cfd = some d →
          (nowMs ≥ deadlineMs → slot'.phase = SlotPhase.done) ∧
          ((w.filesEnv.state.fds.map Prod.fst).Nodup → slot'.phase = SlotPhase.done →
            d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none)) := by
      intro wx trx hWfx hPox hNdx hCRun
      obtain ⟨u, wc, trc, hCl, hCRun⟩ := stateT_bind_eq hCRun
      dsimp only [stateT_pure_run] at hCRun
      injection hCRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
      have hc := healthy_closeFd_instrumented_laws sys hRef wx trx cfd hWfx
      have hCl' : ((instrumentSysOps sys).closeFd cfd).run (wx, trx) = (u, (wc, trc)) := hCl
      rw [hCl'] at hc; dsimp only at hc
      refine ⟨hc.1, (by rw [hc.2.2.1] : trc.pollOutcomes = trx.pollOutcomes).trans hPox, fun d hd => ?_⟩
      injection hd with heq; subst heq
      refine ⟨fun _ => rfl, fun hNd0 _ => ⟨?_, (hc.2.2.2.2 (hNdx hNd0)).2⟩⟩
      rw [hc.2.2.1]; simp [Array.toList_push]
    dsimp only at hRun
    obtain ⟨sendRes, w1, tr1, hR1, hRun⟩ := stateT_bind_eq hRun
    have hS1 := closingSendStep_laws sys hRef cfd replyBytes replyOff shutWr cRev w tr hWf
    have hR1' : (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr) = (sendRes, (w1, tr1)) := hR1
    rw [hR1'] at hS1; dsimp only at hS1
    cases sendRes with
    | none => exact hCloseDone w1 tr1 hS1.1 hS1.2.1 hS1.2.2 hRun
    | some pair =>
      rcases pair with ⟨off1, shut1⟩
      dsimp only at hRun
      obtain ⟨drainRes, w2, tr2, hR2, hRun⟩ := stateT_bind_eq hRun
      have hS2 := closingDrainStep_laws sys hRef cfd shut1 drained cRev w1 tr1 hS1.1
      have hR2' : (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w1, tr1) = (drainRes, (w2, tr2)) := hR2
      rw [hR2'] at hS2; dsimp only at hS2
      cases drainRes with
      | none =>
        exact hCloseDone w2 tr2 hS2.1 (hS2.2.1.trans hS1.2.1) (fun h0 => hS2.2.2 (hS1.2.2 h0)) hRun
      | some drained1 =>
        dsimp only at hRun
        by_cases hTo : nowMs ≥ deadlineMs
        · simp only [hTo, ↓reduceIte] at hRun
          exact hCloseDone w2 tr2 hS2.1 (hS2.2.1.trans hS1.2.1) (fun h0 => hS2.2.2 (hS1.2.2 h0)) hRun
        · simp only [hTo, ↓reduceIte, stateT_pure_run] at hRun
          injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
          exact ⟨hS2.1, hS2.2.1.trans hS1.2.1, fun _ _ => ⟨fun hGe => absurd hGe hTo, fun _ hDone => nomatch hDone⟩⟩

private theorem enterClosingReply_wf_poll_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    {limits : ProxyLimits} {slot slot' : ClientSlot Nat dnsJob}
    {cfd code : Nat}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run (enterClosingReply (instrumentSysOps sys) limits slot cfd code) (w, tr) = (slot', (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  have hWfOut := (enterClosingReply_laws_of_eq sys hRef limits slot cfd code w tr hWf slot' w' tr' hRun).1
  unfold enterClosingReply at hRun
  dsimp only at hRun
  obtain ⟨now, w1, tr1, hM, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf1, hTr1⟩ := monoNowMs_of_eq sys hRef w w1 tr tr1 now hWf hM; clear hM
  obtain ⟨flRes, w2, tr2, hF, hRun⟩ := stateT_bind_eq hRun
  have hPo2 := flushBytesNonblock_pollOutcomes_eq sys cfd (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes) MAX_CLOSING_STEPS 0 w1 tr1
  have hFl2 := flushBytesNonblock_of_eq sys hRef cfd _ MAX_CLOSING_STEPS 0 w1 w2 tr1 tr2 flRes hWf1 hF
  have hF' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net cfd (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes) MAX_CLOSING_STEPS 0).run (w1, tr1) = (flRes, (w2, tr2)) := hF
  rw [hF'] at hPo2; dsimp only at hPo2; clear hF hF'
  have hPo20 : tr2.pollOutcomes = tr.pollOutcomes := hPo2.trans (congrArg _ hTr1)
  refine ⟨hWfOut, ?_⟩
  cases flRes with
  | none =>
    dsimp only at hRun
    obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
    have hc := healthy_closeFd_instrumented_laws sys hRef w2 tr2 cfd hFl2.1
    have hC' : ((instrumentSysOps sys).closeFd cfd).run (w2, tr2) = (u, (w3, tr3)) := hC
    rw [hC'] at hc; dsimp only at hc
    dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with _ ht; subst ht
    exact (by rw [hc.2.2.1] : tr3.pollOutcomes = tr2.pollOutcomes).trans hPo20
  | some sentOff =>
    dsimp only at hRun
    by_cases hSent : sentOff ≥ (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes).size
    · simp only [hSent, ↓reduceIte] at hRun
      obtain ⟨okS, w3, tr3, hS, hRun⟩ := stateT_bind_eq hRun
      obtain ⟨hWf3, hTr3⟩ := shutdownWrClean_of_eq sys hRef cfd 16 w2 w3 tr2 tr3 okS hFl2.1 hS; clear hS
      cases okS with
      | true =>
        simp only [↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with _ ht; subst ht
        rw [hTr3]
        exact hPo20
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hRun
        obtain ⟨u, w4, tr4, hC, hRun⟩ := stateT_bind_eq hRun
        have hc := healthy_closeFd_instrumented_laws sys hRef w3 tr3 cfd hWf3
        have hC' : ((instrumentSysOps sys).closeFd cfd).run (w3, tr3) = (u, (w4, tr4)) := hC
        rw [hC'] at hc; dsimp only at hc
        dsimp only [stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with _ ht; subst ht
        exact (by rw [hc.2.2.1] : tr4.pollOutcomes = tr3.pollOutcomes).trans
          ((congrArg SysAuditTrace.pollOutcomes hTr3).trans hPo20)
    · simp only [hSent, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with _ ht; subst ht
      exact hPo20

private theorem emitAndClosingReply_wf_poll_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    {limits : ProxyLimits} {slot1 : ClientSlot Nat dnsJob} {events1 : Array ConnectEvent}
    {slot' : ClientSlot Nat dnsJob} {evs' : Array ConnectEvent}
    {cfd code : Nat}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run
      (do
        let s2 ← enterClosingReply (instrumentSysOps sys) limits slot1 cfd code
        pure (s2, events1))
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  obtain ⟨s2, w1, tr1, hCr, hRun⟩ := stateT_bind_eq hRun
  dsimp only [stateT_pure_run] at hRun
  injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
  exact enterClosingReply_wf_poll_of_eq sys hRef hWf hCr

private theorem startNextConnectAux_pollOutcomes_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (slot : ClientSlot Nat dnsJob) (events : Array ConnectEvent)
    (cfd : Nat) (host : String) (port : UInt16) (candidates : Array IpAddr) :
    ∀ (fuel candIdx : Nat) (lastErr? : Option Errno)
      {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
      {slot' : ClientSlot Nat dnsJob} {evs' : Array ConnectEvent},
      w.wf = true →
      StateT.run (startNextConnectAux (instrumentSysOps sys) limits slot events cfd host port candidates fuel candIdx lastErr?)
        (w, tr) = ((slot', evs'), (w', tr')) →
      tr'.pollOutcomes = tr.pollOutcomes
  | 0, _, lastErr?, _, _, _, _, _, _, hWf, hRun => by
    unfold startNextConnectAux at hRun
    exact (emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun).2
  | fuel + 1, candIdx, lastErr?, w, w', tr, tr', slot', evs', hWf, hRun => by
    unfold startNextConnectAux at hRun
    by_cases hLt : candIdx < candidates.size
    · simp only [hLt, ↓reduceDIte] at hRun
      let sa := ipAddrToDialSockAddr (candidates[candIdx]'hLt) port
      obtain ⟨rSock, w1, tr1, hSR, hRun⟩ := stateT_bind_app hRun
      have hSock := retryEintr_preserves
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.wf = true ∧ wt.2.pollOutcomes = tr.pollOutcomes)
        (fun _ _ => True)
        ((instrumentSysOps sys).net.socket sa.domain .stream { nonblock := true, cloexec := true } 0)
        (fun (wx, trx) ⟨hwx, hpo⟩ => by
          have hn := hRef.2.1 wx (.socket sa.domain .stream { nonblock := true, cloexec := true } 0) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]; rw [inst_net_socket]
          rcases hS : sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
          rw [hS] at hn; cases sr <;> exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, hpo⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w, tr) ⟨hWf, rfl⟩
      dsimp only [sa] at hSock
      have hSR' : (retryEintr ((instrumentSysOps sys).net.socket
        (ipAddrToDialSockAddr (candidates[candIdx]'hLt) port).domain .stream { nonblock := true, cloexec := true } 0)
        MAX_EINTR_RETRIES).run (w, tr) = (rSock, (w1, tr1)) := hSR
      rw [hSR'] at hSock; dsimp only at hSock
      cases rSock with
      | error e =>
        exact (startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) hSock.1.1 hRun).trans hSock.1.2
      | ok ufd =>
        dsimp only at hRun
        obtain ⟨rc, w2, tr2, hCR, hRun⟩ := stateT_bind_eq hRun
        have hn := hRef.2.1 w1 (.connect ufd sa) ((wf_iff_parts w1).mp hSock.1.1)
        dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
        have hCR' : (instrumentSysOps sys).net.connect ufd sa (w1, tr1) = (rc, (w2, tr2)) := hCR
        rw [inst_net_connect] at hCR'
        rcases hSysC : sys.net.connect ufd sa w1 with ⟨rcSys, w2Sys⟩
        rw [hSysC] at hn hCR'; dsimp only at hn hCR'
        injection hCR' with hrc hwt; injection hwt with hw2 ht2
        subst hrc; subst hw2; subst ht2
        have hWf2 : w2Sys.wf = true := (wf_iff_parts w2Sys).mpr hn.2.1
        let trDial : SysAuditTrace Nat := { tr1 with dialedAddrs := tr1.dialedAddrs.push sa }
        cases rcSys with
        | ok _ =>
          dsimp only [stateT_pure_run] at hRun
          injection hRun with _ hwt; injection hwt with _ ht; subst ht
          exact hSock.1.2
        | error e =>
          dsimp only at hRun
          split at hRun
          · obtain ⟨now, w3, tr3, hM, hRun⟩ := stateT_bind_eq hRun
            obtain ⟨_, hTr3⟩ := monoNowMs_of_eq sys hRef w2Sys w3 trDial tr3 now hWf2 hM
            dsimp only [stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with _ ht; subst ht
            rw [hTr3]; exact hSock.1.2
          · obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
            have hc := healthy_closeFd_instrumented_laws sys hRef w2Sys trDial ufd hWf2
            have hC' : ((instrumentSysOps sys).closeFd ufd).run (w2Sys, trDial) = (u, (w3, tr3)) := hC
            rw [hC'] at hc; dsimp only at hc
            exact (startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) hc.1 hRun).trans
              ((by rw [hc.2.2.1] : tr3.pollOutcomes = tr1.pollOutcomes).trans hSock.1.2)
    · simp only [hLt, ↓reduceDIte] at hRun
      exact startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates 0 candIdx lastErr? hWf hRun

/-- Relational laws for `stepConnecting` (and `stepSlotSync` on `.connecting`). -/
theorem healthy_stepConnecting_laws {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat dnsJob)
    (events : Array ConnectEvent)
    (cfd ufd : Nat) (host : String) (port : UInt16)
    (candidates : Array IpAddr) (candIdx : Nat) (lastErr? : Option Errno) (dlMs : Nat)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat)
    (w₀ : HealthySysWorld) (tr₀ : SysAuditTrace Nat)
    (hWf₀ : w₀.wf = true) :
    let ((slot', evs'), (wC, trC)) :=
      (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs).run (w₀, tr₀)
    wC.wf = true ∧
    trC.pollOutcomes = tr₀.pollOutcomes ∧
    trC.dnsQueries = tr₀.dnsQueries ∧
    ((∀ ip ∈ candidates.toList, Model.allowsIp cfg.ipPolicy ip = true) →
      ∀ sa ∈ trC.dialedAddrs.toList,
        sa ∈ tr₀.dialedAddrs.toList ∨
        ∃ ip ∈ candidates.toList,
          sa = ipAddrToDialSockAddr ip port ∧
          Model.allowsIp cfg.ipPolicy ip = true ∧
          Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp ip) = false) ∧
    (∀ st, slot'.phase = .relay st →
      (slot.phase ≠ .relay st) →
      st.pendingPrefix = slot.pipelined ∧ st.pendingOff = 0 ∧
      st.u2c.toList = Relay.reply200Bytes.data.toList ∧
      evs'.size = events.size + (if slot.eventEmitted then 0 else 1)) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = true →
      (w₀.filesEnv.state.fds.map Prod.fst).Nodup →
      ufd ∈ trC.closedFds.toList ∧ cfd ∈ trC.closedFds.toList ∧
      Files.assocGet wC.filesEnv.state.fds ufd = none ∧
      Files.assocGet wC.filesEnv.state.fds cfd = none) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = false ∧
        (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = false ∧
        nowMs ≥ dlMs →
      ufd ∈ trC.closedFds.toList) := by
  rcases hTop : (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs).run (w₀, tr₀) with ⟨⟨slot', evs'⟩, wC, trC⟩
  have hRun : StateT.run (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs) (w₀, tr₀) = ((slot', evs'), (wC, trC)) := hTop
  clear hTop
  dsimp only
  unfold stepConnecting at hRun
  by_cases hCErr : (cRev.pollerr || cRev.pollhup || cRev.pollnval) = true
  · simp only [hCErr, ↓reduceIte] at hRun
    obtain ⟨u1, w1, tr1, hC1, hRun⟩ := stateT_bind_app hRun
    obtain ⟨u2, w2, tr2, hC2, hRun⟩ := stateT_bind_eq hRun
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hp hwt; injection hp with hs he; injection hwt with hw ht
    subst hs; subst he; subst hw; subst ht
    have hc1 := healthy_closeFd_instrumented_laws sys hRef w₀ tr₀ ufd hWf₀
    have hC1' : ((instrumentSysOps sys).closeFd ufd).run (w₀, tr₀) = (u1, (w1, tr1)) := hC1
    rw [hC1'] at hc1; dsimp only at hc1
    have hc2 := healthy_closeFd_instrumented_laws sys hRef w1 tr1 cfd hc1.1
    have hC2' : ((instrumentSysOps sys).closeFd cfd).run (w1, tr1) = (u2, (w2, tr2)) := hC2
    rw [hC2'] at hc2; dsimp only at hc2
    refine ⟨hc2.1,
      by rw [hc2.2.2.1, hc1.2.2.1],
      by rw [hc2.2.2.1, hc1.2.2.1],
      fun _ sa hm => Or.inl (by rw [hc2.2.2.1, hc1.2.2.1] at hm; exact hm),
      ?_, ?_,
      fun ⟨hCF, _⟩ => by rw [hCErr] at hCF; cases hCF⟩
    · intro _ hRel _; cases hRel
    · intro _ hNd₀
      obtain ⟨hNd1, hNoneU⟩ := hc1.2.2.2.2 hNd₀
      obtain ⟨_, hNoneC⟩ := hc2.2.2.2.2 hNd1
      refine ⟨?_, ?_, hc2.2.2.2.1 ufd hNoneU, hNoneC⟩
      · rw [hc2.2.2.1, hc1.2.2.1]; simp [Array.toList_push]
      · rw [hc2.2.2.1]; simp [Array.toList_push]
  · have hCErrF : (cRev.pollerr || cRev.pollhup || cRev.pollnval) = false := Bool.eq_false_iff.mpr hCErr
    simp only [hCErrF, Bool.false_eq_true, ↓reduceIte] at hRun
    by_cases hUEv : (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = true
    · simp only [hUEv, ↓reduceIte] at hRun
      obtain ⟨gRes, w1, tr1, hGR, hRun⟩ := stateT_bind_app hRun
      have hGs := retryEintr_preserves
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.wf = true ∧ wt.2 = tr₀)
        (fun _ _ => True)
        ((instrumentSysOps sys).net.getsockopt ufd .error)
        (fun (wx, trx) ⟨hwx, htrx⟩ => by
          have hn := hRef.2.1 wx (.getsockopt ufd .error) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]; rw [inst_net_getsockopt]
          rcases hG : sys.net.getsockopt ufd .error wx with ⟨gr, wx'⟩
          rw [hG] at hn; exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, htrx⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w₀, tr₀) ⟨hWf₀, rfl⟩
      have hGR' : (retryEintr ((instrumentSysOps sys).net.getsockopt ufd .error) MAX_EINTR_RETRIES).run (w₀, tr₀) = (gRes, (w1, tr1)) := hGR
      rw [hGR'] at hGs; dsimp only at hGs
      rcases hGs.1 with ⟨hWf1, hTr1Eq⟩
      rw [hTr1Eq] at hRun
      let soErr : Errno := match gRes with | .ok code => code | .error e => e
      have hSoNorm : StateT.run
          (if soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval then
            pure (enterRelay slot events cfd ufd host port)
          else do
            let recErr := if soErr != 0 then soErr else Errno.ECONNREFUSED
            (instrumentSysOps sys).closeFd ufd
            startNextConnect (instrumentSysOps sys) cfg.limits slot events cfd host port candidates candIdx (some recErr))
          (w1, tr₀) = ((slot', evs'), (wC, trC)) := by
        cases gRes <;> simpa [soErr, StateT.run, bind, StateT.bind, pure, StateT.pure] using hRun
      by_cases hOkConn : (soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval) = true
      · simp only [hOkConn, ↓reduceIte, stateT_pure_run] at hSoNorm
        injection hSoNorm with hp hwt; injection hp with hs he; injection hwt with hw ht
        subst hs; subst he; subst hw; subst ht
        refine ⟨hWf1, rfl, rfl, fun _ sa hm => Or.inl hm, fun st hRel _ => ?_,
          fun hBad => absurd hBad hCErr, fun ⟨_, hUF, _⟩ => by rw [hUEv] at hUF; cases hUF⟩
        dsimp only [enterRelay] at hRel
        injection hRel with hStEq
        subst hStEq
        exact ⟨emitSlotEvent_fst_pipelined slot events _, rfl, reply200_init_u2c_toList, emitSlotEvent_snd_size slot events _⟩
      · simp only [Bool.eq_false_iff.mpr hOkConn, Bool.false_eq_true, ↓reduceIte] at hSoNorm
        obtain ⟨u, w2, tr2, hC, hSnc⟩ := stateT_bind_app hSoNorm
        have hc := healthy_closeFd_instrumented_laws sys hRef w1 tr₀ ufd hWf1
        have hC' : ((instrumentSysOps sys).closeFd ufd).run (w1, tr₀) = (u, (w2, tr2)) := hC
        rw [hC'] at hc; dsimp only [startNextConnect] at hc hSnc
        have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx _ hc.1 hSnc
        have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx _ w2 wC tr2 trC slot' evs' hc.1 hSnc
        refine ⟨hSub.1,
          hPo.trans (by rw [hc.2.2.1]),
          hSub.2.1.trans (by rw [hc.2.2.1]),
          fun hCands sa hm => ?_,
          fun st hRel _ => hSub.2.2.2.2.2.2.1 st hRel,
          fun hBad => absurd hBad hCErr,
          fun ⟨_, hUF, _⟩ => by rw [hUEv] at hUF; cases hUF⟩
        rcases hSub.2.2.2.2.1 sa hm with hIn2 | ⟨ip, hMem, rfl⟩
        · rw [hc.2.2.1] at hIn2; exact Or.inl hIn2
        · have hAl := hCands ip hMem
          exact Or.inr ⟨ip, hMem, rfl, hAl, (dialSockAddr_never_banned cfg.ipPolicy ip hAl).1⟩
    · have hUEvF : (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = false := Bool.eq_false_iff.mpr hUEv
      simp only [hUEvF, Bool.false_eq_true, ↓reduceIte] at hRun
      by_cases hTo : nowMs ≥ dlMs
      · simp only [hTo, ↓reduceIte] at hRun
        obtain ⟨u, w1, tr1, hC, hSnc⟩ := stateT_bind_app hRun
        have hc := healthy_closeFd_instrumented_laws sys hRef w₀ tr₀ ufd hWf₀
        have hC' : ((instrumentSysOps sys).closeFd ufd).run (w₀, tr₀) = (u, (w1, tr1)) := hC
        rw [hC'] at hc; dsimp only [startNextConnect] at hc hSnc
        have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx (some Errno.ETIMEDOUT) hc.1 hSnc
        have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx (some Errno.ETIMEDOUT) w1 wC tr1 trC slot' evs' hc.1 hSnc
        refine ⟨hSub.1,
          hPo.trans (by rw [hc.2.2.1]),
          hSub.2.1.trans (by rw [hc.2.2.1]),
          fun hCands sa hm => ?_,
          fun st hRel _ => hSub.2.2.2.2.2.2.1 st hRel,
          fun hBad => absurd hBad hCErr,
          fun _ => hSub.2.2.2.1 ufd (by rw [hc.2.2.1]; simp [Array.toList_push])⟩
        rcases hSub.2.2.2.2.1 sa hm with hIn1 | ⟨ip, hMem, rfl⟩
        · rw [hc.2.2.1] at hIn1; exact Or.inl hIn1
        · have hAl := hCands ip hMem
          exact Or.inr ⟨ip, hMem, rfl, hAl, (dialSockAddr_never_banned cfg.ipPolicy ip hAl).1⟩
      · simp only [hTo, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with hp hwt; injection hp with hs he; injection hwt with hw ht
        subst hs; subst he; subst hw; subst ht
        exact ⟨hWf₀, rfl, rfl, fun _ sa hm => Or.inl hm,
          fun st hRel hNe => absurd hRel hNe,
          fun hBad => absurd hBad hCErr,
          fun ⟨_, _, hGe⟩ => absurd hGe hTo⟩

private theorem handleResolveDecision_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) {slot slot' : ClientSlot Nat Unit} {events evs' : Array ConnectEvent}
    {cfd : Nat} {host : String} {port : UInt16} {ips : Array IpAddr}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run (handleResolveDecision (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy) slot events cfd host port ips) (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold handleResolveDecision at hRun
  cases hDec : Model.decideResolvedIps cfg.ipPolicy host port ips with
  | deny r =>
    rw [hDec] at hRun; dsimp only at hRun
    exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
  | dial primary fallbacks =>
    rw [hDec] at hRun; dsimp only [startNextConnect] at hRun
    have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port (#[primary] ++ fallbacks) ((#[primary] ++ fallbacks).size - 0) 0 none hWf hRun
    have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port (#[primary] ++ fallbacks) ((#[primary] ++ fallbacks).size - 0) 0 none w w' tr tr' slot' evs' hWf hRun
    exact ⟨hSub.1, hPo⟩

private theorem handleCompleteHead_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) {slot slot' : ClientSlot Nat Unit} {events evs' : Array ConnectEvent}
    {cfd : Nat} {headBytes pipelined : ByteArray}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run
      (handleCompleteHead (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events cfd headBytes pipelined)
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold handleCompleteHead at hRun
  dsimp only at hRun
  cases hDec : Model.decideConnectHead cfg headBytes with
  | deny h? p? reason =>
    rw [hDec] at hRun; dsimp only at hRun
    exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
  | needResolve host port litIp? =>
    rw [hDec] at hRun; dsimp only at hRun
    cases litIp? with
    | some litIp =>
      exact handleResolveDecision_wf_poll_of_eq sys hRef cfg hWf hRun
    | none =>
      dsimp only [startDnsSync] at hRun
      obtain ⟨dnsRes, w1, tr1, hD, hRun⟩ := stateT_bind_eq hRun
      have hDns := hRef.2.2.2.1 w { host := host, hints := { family := .any, sockType := .stream } } ((wf_iff_parts w).mp hWf)
      dsimp only [Dns.execDnsReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hDns
      have hD' : (instrumentSysOps sys).dns.getaddrinfo host { family := .any, sockType := .stream } (w, tr) = (dnsRes, (w1, tr1)) := hD
      rw [inst_dns_getaddrinfo] at hD'
      rcases hSysD : sys.dns.getaddrinfo host { family := .any, sockType := .stream } w with ⟨dSys, w1Sys⟩
      rw [hSysD] at hDns hD'; dsimp only at hDns hD'
      injection hD' with hd hwt; injection hwt with hw1 ht1
      subst hd; subst hw1; subst ht1
      have hWf1 : w1Sys.wf = true := (wf_iff_parts w1Sys).mpr hDns.2.1
      cases dSys with
      | error _ =>
        dsimp only at hRun
        have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
        exact ⟨hSub.1, hSub.2⟩
      | ok addrs =>
        dsimp only at hRun
        have hSub := handleResolveDecision_wf_poll_of_eq sys hRef cfg hWf1 hRun
        exact ⟨hSub.1, hSub.2⟩

private theorem stepHandshakeReadAux_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cfd deadlineMs : Nat) :
    ∀ (fuel : Nat) (headBuf : ByteArray)
      {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
      {slot' : ClientSlot Nat Unit} {evs' : Array ConnectEvent},
      w.wf = true →
      StateT.run
        (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          slot events cfd deadlineMs fuel headBuf)
        (w, tr) = ((slot', evs'), (w', tr')) →
      w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes
  | 0, _, _, _, _, _, _, _, hWf, hRun => by
    unfold stepHandshakeReadAux at hRun
    dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl⟩
  | fuel + 1, headBuf, w, w', tr, tr', slot', evs', hWf, hRun => by
    unfold stepHandshakeReadAux at hRun
    by_cases hMax : headBuf.size ≥ cfg.limits.maxHeaderBytes
    · simp only [hMax, ↓reduceIte] at hRun
      exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
    · simp only [hMax, ↓reduceIte] at hRun
      let want := UInt32.ofNat (Nat.min (cfg.limits.maxHeaderBytes - headBuf.size) HANDSHAKE_CHUNK_MAX)
      obtain ⟨recvRes, w1, tr1, hR, hRun⟩ := stateT_bind_app hRun
      have hR' : (instrumentSysOps sys).net.recvfrom cfd want { dontwait := true } (w, tr) = (recvRes, (w1, tr1)) := hR
      clear hR
      rw [inst_net_recvfrom sys cfd want { dontwait := true } w tr] at hR'
      have hNet := hRef.2.1 w (.recvfrom cfd want { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      rcases hRNet : sys.net.recvfrom cfd want { dontwait := true } w with ⟨rSys, w1Sys⟩
      rw [hRNet] at hNet hR'; dsimp only at hNet hR'
      injection hR' with hrr hwt; injection hwt with hw1 ht1
      subst hrr; subst hw1; subst ht1
      have hWf1 : w1Sys.wf = true := (wf_iff_parts w1Sys).mpr hNet.2.1
      cases rSys with
      | error e =>
        dsimp only at hRun
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte] at hRun
          exact stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd deadlineMs fuel headBuf hWf1 hRun
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte] at hRun
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte, stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
            exact ⟨hWf1, rfl⟩
          · simp only [Bool.eq_false_iff.mpr hAg, Bool.false_eq_true, ↓reduceIte] at hRun
            have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
            exact ⟨hSub.1, hSub.2⟩
      | ok chunk =>
        dsimp only at hRun
        by_cases h0 : (chunk.size == 0) = true
        · simp only [h0, ↓reduceIte] at hRun
          have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
          exact ⟨hSub.1, hSub.2⟩
        · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte] at hRun
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          cases hScan : findCrlfCrlf nextBuf (headBuf.size - 3) with
          | some pos =>
            rw [hScan] at hRun; dsimp only at hRun
            have hSub := handleCompleteHead_wf_poll_of_eq sys hRef cfg hWf1 hRun
            exact ⟨hSub.1, hSub.2⟩
          | none =>
            rw [hScan] at hRun; dsimp only at hRun
            by_cases hNextGe : nextBuf.size ≥ cfg.limits.maxHeaderBytes
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
              exact ⟨hSub.1, hSub.2⟩
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd deadlineMs fuel _ hWf1 hRun
              exact ⟨hSub.1, hSub.2⟩

private theorem stepHandshake_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cfd : Nat) (headBuf : ByteArray) (dl nowMs : Nat) (cRev : Poll.PollEvents)
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
    {slot' : ClientSlot Nat Unit} {evs' : Array ConnectEvent}
    (hWf : w.wf = true)
    (hRun : StateT.run
      (stepHandshake (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events cfd headBuf dl cRev nowMs)
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold stepHandshake at hRun
  dsimp only at hRun
  by_cases hEv : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true
  · simp only [hEv, ↓reduceIte] at hRun
    obtain ⟨⟨s1, e1⟩, w1, tr1, hFirst, hRun⟩ := stateT_bind_app hRun
    dsimp only at hRun
    have hRd := stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd dl MAX_HANDSHAKE_STEPS headBuf hWf hFirst
    cases hPh : s1.phase with
    | handshake cfd1 _ dl1 =>
      rw [hPh] at hRun; dsimp only at hRun
      by_cases hGe : nowMs ≥ dl1
      · simp only [hGe, ↓reduceIte] at hRun
        have hCr := emitAndClosingReply_wf_poll_of_eq sys hRef hRd.1 hRun
        exact ⟨hCr.1, hCr.2.trans hRd.2⟩
      · simp only [hGe, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact hRd
    | dns _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | relay _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | done =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
  · simp only [Bool.eq_false_iff.mpr hEv, Bool.false_eq_true, ↓reduceIte] at hRun
    obtain ⟨⟨s1, e1⟩, w1, tr1, hFirst, hRun⟩ := stateT_bind_app hRun
    dsimp only [stateT_pure_run] at hFirst
    injection hFirst with hp hwt; injection hp with hs he; injection hwt with hw ht
    subst hs; subst he; subst hw; subst ht
    dsimp only at hRun
    cases hPh : slot.phase with
    | handshake cfd1 _ dl1 =>
      rw [hPh] at hRun; dsimp only at hRun
      by_cases hGe : nowMs ≥ dl1
      · simp only [hGe, ↓reduceIte] at hRun
        exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
      · simp only [hGe, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact ⟨hWf, rfl⟩
    | dns _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | relay _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | done =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩

private theorem stepSlotTick_wf_poll
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) :=
      (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        (fun () => pure none) (fun () => pure ()) slot events cRev uRev nowMs).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  suffices hPres : PreservesWfPoll tr
      (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        (fun () => pure none) (fun () => pure ()) slot events cRev uRev nowMs) from
    hPres w tr hWf rfl
  unfold stepSlotM
  cases slot.phase with
  | handshake cfd headBuf dl =>
    intro wx trx hwx hpox
    rcases hR : (stepHandshake (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      slot events cfd headBuf dl cRev nowMs).run (wx, trx) with ⟨⟨s', e'⟩, w1, tr1⟩
    have hHs := stepHandshake_wf_poll_of_eq sys hRef cfg slot events cfd headBuf dl nowMs cRev hwx hR
    exact ⟨hHs.1, hHs.2.trans hpox⟩
  | dns cfd host port job =>
    dsimp only; split
    · exact pres_bind (pres_pure ()) (fun _ => pres_bind (pres_closeFd sys hRef tr cfd) (fun _ => pres_pure _))
    · intro wx trx hwx hpox
      exact ⟨hwx, hpox⟩
  | connecting cfd ufd host port cands idx lastErr? dl =>
    intro wx trx hwx hpox
    have hConn := healthy_stepConnecting_laws sys hRef cfg slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs wx trx hwx
    rcases hR : (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hConn
    exact ⟨hConn.1, hConn.2.1.trans hpox⟩
  | relay st =>
    dsimp only
    refine pres_bind ?_ (fun _ => by split <;> exact pres_pure _)
    intro wx trx hwx hpox
    have hRel := healthy_stepBidirectionalRelay_wf sys hRef st cRev uRev wx trx hwx
    rcases hR : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd st cRev uRev).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hRel
    exact ⟨hRel.1, hRel.2.trans hpox⟩
  | closingReply cfd? rb roff sw dr dl =>
    dsimp only
    refine pres_bind ?_ (fun _ => pres_pure _)
    intro wx trx hwx hpox
    have hCl := healthy_stepClosingReply_laws sys hRef slot cfd? rb roff sw dr dl cRev nowMs wx trx hwx
    rcases hR : (stepClosingReply (instrumentSysOps sys) slot cfd? rb roff sw dr dl cRev nowMs).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hCl
    exact ⟨hCl.1, hCl.2.1.trans hpox⟩
  | done => exact pres_pure _

private theorem stepSlotsListM_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (indices : Array (Option Nat × Option Nat))
    (revents : Array Poll.PollEvents)
    (nowMs : Nat) :
    ∀ (idx : Nat) (slots : List (ClientSlot Nat Unit))
      (accSlots : Array (ClientSlot Nat Unit)) (accEvents : Array ConnectEvent)
      (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      (∀ s ∈ accSlots.toList, s.isFinished = false) →
      let ((outSlots, _), (w', tr')) :=
        (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          (fun () => pure none) (fun () => pure ()) indices revents nowMs
          idx slots accSlots accEvents).run (w, tr)
      w'.wf = true ∧
      tr'.pollOutcomes = tr.pollOutcomes ∧
      outSlots.size ≤ accSlots.size + slots.length ∧
      (∀ s ∈ outSlots.toList, s.isFinished = false)
  | _, [], accSlots, _, w, _, hWf, hFin =>
    ⟨hWf, rfl, by simp, hFin⟩
  | idx, slot :: rest, accSlots, accEvents, w, tr, hWf, hFin => by
    rcases hTop : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      idx (slot :: rest) accSlots accEvents).run (w, tr) with ⟨⟨outSlots, outEvs⟩, w2, tr2⟩
    have hRun : StateT.run (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      idx (slot :: rest) accSlots accEvents) (w, tr) = ((outSlots, outEvs), (w2, tr2)) := hTop
    clear hTop
    dsimp only
    unfold stepSlotsListM at hRun
    rcases hIdx : indices[idx]?.getD (none, none) with ⟨cIdx?, uIdx?⟩
    rw [hIdx] at hRun
    dsimp only at hRun
    obtain ⟨⟨slot', evs'⟩, w1, tr1, hSRun, hRun⟩ := stateT_bind_eq hRun
    let cRev := match cIdx? with | some ci => revents[ci]?.getD {} | none => {}
    let uRev := match uIdx? with | some ui => revents[ui]?.getD {} | none => {}
    have hStep := stepSlotTick_wf_poll sys hRef cfg slot accEvents cRev uRev nowMs w tr hWf
    have hSRun' : (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) slot accEvents cRev uRev nowMs).run (w, tr) = ((slot', evs'), (w1, tr1)) := hSRun
    rw [hSRun'] at hStep; dsimp only at hStep
    let accSlots' := if !slot'.isFinished then accSlots.push slot' else accSlots
    have hAccFin : ∀ s ∈ accSlots'.toList, s.isFinished = false := by
      dsimp only [accSlots']
      cases hF : slot'.isFinished
      · simp only [Bool.not_false, ↓reduceIte, Array.toList_push, List.mem_append, List.mem_singleton]
        rintro s (hOld | rfl)
        · exact hFin s hOld
        · exact hF
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hFin
    have hAccSz : accSlots'.size ≤ accSlots.size + 1 := by
      dsimp only [accSlots']
      split <;> simp [Array.size_push] <;> omega
    have hSub := stepSlotsListM_laws sys hRef cfg indices revents nowMs (idx + 1) rest accSlots' evs' w1 tr1 hStep.1 hAccFin
    have hRun' : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      (idx + 1) rest accSlots' evs').run (w1, tr1) = ((outSlots, outEvs), (w2, tr2)) := hRun
    rw [hRun'] at hSub; dsimp only at hSub
    have hLen : (slot :: rest).length = rest.length + 1 := rfl
    have hOutSz := hSub.2.2.1
    exact ⟨hSub.1, hSub.2.1.trans hStep.2, by omega, hSub.2.2.2⟩

private theorem acceptNewClientsAux_pollOutcomes_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (limits : ProxyLimits) (lfd nowMs : Nat) :
    ∀ (fuel : Nat) (slots : Array (ClientSlot Nat dnsJob)) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      ((acceptNewClientsAux (instrumentSysOps sys) limits lfd nowMs fuel slots).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, _, _, _ => rfl
  | fuel + 1, slots, w, tr => by
    unfold acceptNewClientsAux
    by_cases hCap : slots.size ≥ limits.maxConcurrentTunnels
    · simp only [hCap, ↓reduceIte]; rfl
    · simp only [hCap, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [inst_net_accept4]
      rcases sys.net.accept4 lfd { nonblock := true, cloexec := true } w with ⟨r, w1⟩
      dsimp only
      cases r with
      | ok pair =>
        rcases pair with ⟨cfd, _⟩
        exact acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs fuel _ w1 _
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          exact acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs fuel slots w1 tr
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem maybeDrainWakeSocket_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (wakeR : Nat) (wakeRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  rcases hTop : (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev).run (w, tr) with ⟨u, w', tr'⟩
  have hRun : StateT.run (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev) (w, tr) = (u, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold maybeDrainWakeSocket at hRun
  split at hRun
  · have hD := drainWakeSocket_laws sys hRef wakeR 64 w tr hWf
    have hRun' : (drainWakeSocket (instrumentSysOps sys).net wakeR 64).run (w, tr) = (u, (w', tr')) := hRun
    rw [hRun'] at hD
    exact hD
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl⟩

private theorem maybeAcceptNewClients_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (lfd nowMs : Nat) (listenRev : Poll.PollEvents)
    (slots : Array (ClientSlot Nat Unit))
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : slots.size ≤ limits.maxConcurrentTunnels)
    (hFin : ∀ s ∈ slots.toList, s.isFinished = false) :
    let (accSlots, (w', tr')) :=
      (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    accSlots.size ≤ limits.maxConcurrentTunnels ∧
    (∀ s ∈ accSlots.toList, s.isFinished = false) := by
  rcases hTop : (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots).run (w, tr) with ⟨accSlots, w', tr'⟩
  have hRun : StateT.run (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots) (w, tr) = (accSlots, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold maybeAcceptNewClients at hRun
  split at hRun
  · unfold acceptNewClients at hRun
    have hA := healthy_acceptNewClientsAux_laws sys hRef limits lfd nowMs MAX_ACCEPT_BATCH slots w tr hWf hLe
    have hPoA := acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs MAX_ACCEPT_BATCH slots w tr
    have hRun' : (acceptNewClientsAux (instrumentSysOps sys) limits lfd nowMs MAX_ACCEPT_BATCH slots).run (w, tr) = (accSlots, (w', tr')) := hRun
    rw [hRun'] at hA hPoA; dsimp only at hA hPoA
    refine ⟨hA.1, hPoA, hA.2.1, fun s hs => ?_⟩
    rcases hA.2.2.1 s hs with hOld | hNF
    · exact hFin s hOld
    · exact hNF
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
    exact ⟨hWf, rfl, hLe, hFin⟩

/-- Relational laws for `SysBridge.pollAndStepTickSync`. -/
theorem healthy_pollAndStepTickSync_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (stopFlag : Bool)
    (wakeR lfd : Nat)
    (slots : Array (ClientSlot Nat Unit))
    (events : Array ConnectEvent)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true)
    (hSlotsLe : slots.size ≤ cfg.limits.maxConcurrentTunnels) :
    let (tickOut, (wT, trT)) :=
      (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        stopFlag wakeR lfd slots events).run (w₀, {})
    wT.wf = true ∧
    (tickOut = .retryEintr ↔ trT.pollOutcomes = #[some Errno.EINTR]) ∧
    (stopFlag = true → tickOut = .retryEintr ∨ tickOut = .stopOrFatal) ∧
    (stopFlag = false ∧ trT.pollOutcomes = #[none] →
      ∃ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs) ∧
    (∀ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs →
      stopFlag = false ∧
      nextSlots.size ≤ cfg.limits.maxConcurrentTunnels ∧
      ∀ s ∈ nextSlots.toList, s.isFinished = false) := by
  rcases hTop : (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    stopFlag wakeR lfd slots events).run (w₀, {}) with ⟨tickOut, wT, trT⟩
  have hRun : StateT.run (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    stopFlag wakeR lfd slots events) (w₀, {}) = (tickOut, (wT, trT)) := hTop
  clear hTop
  dsimp only
  unfold pollAndStepTickSync pollAndStepTickM at hRun
  obtain ⟨now0, w1, tr1, hM0, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf1, hTr1⟩ := monoNowMs_of_eq sys hRef w₀ w1 {} tr1 now0 hWf₀ hM0; clear hM0
  subst hTr1
  have hAuxEq : ∀ (ls : List (ClientSlot Nat Unit)) (r : Array (Nat × Poll.PollEvents))
      (ix : Array (Option Nat × Option Nat)) (mr : Option Nat) (wx : HealthySysWorld) (trx : SysAuditTrace Nat),
      StateT.run (buildPollBatchAux (m := StateM (HealthySysWorld × SysAuditTrace Nat)) (fun () => pure false) now0 ls r ix mr) (wx, trx) =
      (Id.run (buildPollBatchAux (m := Id) (fun () => pure false) now0 ls r ix mr), (wx, trx)) := by
    intro ls
    induction ls with
    | nil => intro r ix mr wx trx; rfl
    | cons hd tl ih =>
      intro r ix mr wx trx
      unfold buildPollBatchAux
      cases hd.phase with
      | handshake c _ dl => exact ih _ _ _ wx trx
      | dns c _ _ _ => exact ih _ _ _ wx trx
      | connecting c u _ _ _ _ _ dl => exact ih _ _ _ wx trx
      | relay st => exact ih _ _ _ wx trx
      | closingReply c? _ _ _ _ dl => cases c? <;> exact ih _ _ _ wx trx
      | done => exact ih _ _ _ wx trx
  have hBatchEq :
      StateT.run
        (buildPollBatchM (m := StateM (HealthySysWorld × SysAuditTrace Nat))
          (fun () => pure false) wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots)
        (w1, {}) =
      (buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots, (w1, {})) := by
    unfold buildPollBatchSync buildPollBatchM
    rw [stateT_bind_run, hAuxEq]
    rfl
  obtain ⟨bOut, w1b, tr1b, hBRun, hRun⟩ := stateT_bind_eq hRun
  rw [hBatchEq] at hBRun
  injection hBRun with hb hwt; injection hwt with hw1b ht1b
  subst hb; subst hw1b; subst ht1b
  let bRes := buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots
  dsimp only at hRun
  obtain ⟨pRes, w2, tr2, hPRun, hRun⟩ := stateT_bind_eq hRun
  have hPRun' : (instrumentSysOps sys).poll.ppoll bRes.1 bRes.2.2 (w1, {}) = (pRes, (w2, tr2)) := hPRun
  clear hPRun
  rw [inst_poll_ppoll] at hPRun'
  have hPoll := hRef.2.2.1 w1 (.ppoll bRes.1 bRes.2.2) ((wf_iff_parts w1).mp hWf1)
  dsimp only [Poll.execPollReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hPoll
  rcases hSysP : sys.poll.ppoll bRes.1 bRes.2.2 w1 with ⟨pSys, w2Sys⟩
  rw [hSysP] at hPoll hPRun'; dsimp only at hPoll hPRun'
  injection hPRun' with hp hwt; injection hwt with hw2 ht2
  subst hp; subst hw2; subst ht2
  have hWf2 : w2Sys.wf = true := (wf_iff_parts w2Sys).mpr hPoll.2.1
  cases pSys with
  | error e =>
    dsimp only at hRun
    by_cases hEi : (e == Errno.EINTR) = true
    · simp only [hEi, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have heq := beq_iff_eq.mp hEi
      subst heq
      have hNotNone : (#[some Errno.EINTR] : Array (Option Errno)) ≠ #[none] := by
        intro hBad
        have hList := congrArg Array.toList hBad
        cases hList
      exact And.intro hWf2
        (And.intro (Iff.intro (fun _ => rfl) (fun _ => rfl))
          (And.intro (fun _ => Or.inl rfl)
            (And.intro (fun ⟨_, hBad⟩ => absurd hBad hNotNone)
              (fun _ _ hBad => nomatch hBad))))
    · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hNe : e ≠ Errno.EINTR := fun hc => hEi (beq_iff_eq.mpr hc)
      have hNotNone : (#[some e] : Array (Option Errno)) ≠ #[none] := by
        intro hBad
        have hList := congrArg Array.toList hBad
        cases hList
      have hNotEintr : (#[some e] : Array (Option Errno)) ≠ #[some Errno.EINTR] := by
        intro hArr
        have hList := congrArg Array.toList hArr
        injection hList with hHead _
        injection hHead with he
        exact hNe he
      exact And.intro hWf2
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun _ => Or.inr rfl)
            (And.intro (fun ⟨_, hBad⟩ => absurd hBad hNotNone)
              (fun _ _ hBad => nomatch hBad))))
  | ok revents =>
    dsimp only at hRun
    obtain ⟨_, w3, tr3, hWRun, hRun⟩ := stateT_bind_eq hRun
    have hWake := maybeDrainWakeSocket_laws sys hRef wakeR (revents[0]?.getD {}) w2Sys { pollOutcomes := #[none] } hWf2
    have hWRun' : (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR (revents[0]?.getD {})).run (w2Sys, { pollOutcomes := #[none] }) = ((), (w3, tr3)) := hWRun
    rw [hWRun'] at hWake; dsimp only at hWake
    obtain ⟨sfVal, w3b, tr3b, hSfRun, hRun⟩ := stateT_bind_eq hRun
    dsimp only [stateT_pure_run] at hSfRun
    injection hSfRun with hsf hwt; injection hwt with hw3b ht3b
    subst hsf; subst hw3b; subst ht3b
    cases stopFlag with
    | true =>
      simp only [↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hNotEintr : tr3.pollOutcomes ≠ #[some Errno.EINTR] := by
        rw [hWake.2]
        intro hArr
        have hList := congrArg Array.toList hArr
        cases hList
      exact And.intro hWake.1
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun _ => Or.inr rfl)
            (And.intro (fun ⟨hBad, _⟩ => nomatch hBad)
              (fun _ _ hBad => nomatch hBad))))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hRun
      obtain ⟨now1, w4, tr4, hM1, hRun⟩ := stateT_bind_eq hRun
      obtain ⟨hWf4, hTr4⟩ := monoNowMs_of_eq sys hRef w3 w4 tr3 tr4 now1 hWake.1 hM1; clear hM1
      obtain ⟨⟨nextSlots, nextEvents⟩, w5, tr5, hSLRun, hRun⟩ := stateT_bind_eq hRun
      have hStepL := stepSlotsListM_laws sys hRef cfg bRes.2.1 revents now1 0 slots.toList
        (Array.emptyWithCapacity slots.size) events w4 tr4 hWf4 (fun _ hm => nomatch hm)
      have hSLRun' : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          (fun () => pure none) (fun () => pure ())
          bRes.2.1 revents now1 0 slots.toList
          (Array.emptyWithCapacity slots.size) events).run (w4, tr4) = ((nextSlots, nextEvents), (w5, tr5)) := hSLRun
      rw [hSLRun'] at hStepL; dsimp only at hStepL
      have hNextLe : nextSlots.size ≤ cfg.limits.maxConcurrentTunnels := by
        have hSz0 : (Array.emptyWithCapacity slots.size : Array (ClientSlot Nat Unit)).size = 0 := rfl
        have hLen : slots.toList.length = slots.size := Array.length_toList
        have hOut := hStepL.2.2.1
        omega
      obtain ⟨postDetached, w5b, tr5b, hPDRun, hRun⟩ := stateT_bind_eq hRun
      dsimp only [stateT_pure_run] at hPDRun
      injection hPDRun with hpd hwt; injection hwt with hw5b ht5b
      subst hpd; subst hw5b; subst ht5b
      dsimp only at hRun
      obtain ⟨acceptedSlots, w6, tr6, hARun, hRun⟩ := stateT_bind_eq hRun
      have hAcc := maybeAcceptNewClients_laws sys hRef cfg.limits lfd now1 (revents[1]?.getD {}) nextSlots w5 tr5 hStepL.1 hNextLe hStepL.2.2.2
      have hARun' : (maybeAcceptNewClients (instrumentSysOps sys) cfg.limits lfd now1 (revents[1]?.getD {}) nextSlots).run (w5, tr5) = (acceptedSlots, (w6, tr6)) := hARun
      rw [hARun'] at hAcc; dsimp only at hAcc
      dsimp only [stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hPoFinal : tr6.pollOutcomes = #[none] :=
        hAcc.2.1.trans (hStepL.2.1.trans ((congrArg _ hTr4).trans hWake.2))
      have hNotEintr : tr6.pollOutcomes ≠ #[some Errno.EINTR] := by
        rw [hPoFinal]
        intro hArr
        have hList := congrArg Array.toList hArr
        cases hList
      refine And.intro hAcc.1
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun hBad => nomatch hBad)
            (And.intro (fun _ => ⟨acceptedSlots, nextEvents, rfl⟩)
              (fun ns ne hEq => ?_))))
      injection hEq with hns _
      subst hns
      exact ⟨rfl, hAcc.2.2.1, hAcc.2.2.2⟩

end LeanSwe.ConnectProxy.Proofs

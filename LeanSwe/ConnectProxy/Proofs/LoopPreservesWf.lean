import LeanSwe.ConnectProxy.Proofs.SysBridgeProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

/-- Internal ConnectProxy proof helper `PreservesWfPoll`. -/
def PreservesWfPoll (tr₀ : SysAuditTrace Nat) {α : Type}
    (m : StateM (HealthySysWorld × SysAuditTrace Nat) α) : Prop :=
  ∀ w tr, w.wf = true → tr.pollOutcomes = tr₀.pollOutcomes →
    let (_, (w', tr')) := m.run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr₀.pollOutcomes

/-- Internal ConnectProxy proof helper `pres_pure`. -/
theorem pres_pure {tr₀ : SysAuditTrace Nat} {α : Type} (a : α) :
    PreservesWfPoll tr₀ (pure a) :=
  fun _ _ hw hp => ⟨hw, hp⟩

/-- Internal ConnectProxy proof helper `pres_bind`. -/
theorem pres_bind {tr₀ : SysAuditTrace Nat} {α β : Type}
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

/-- Internal ConnectProxy proof helper `pres_closeFd`. -/
theorem pres_closeFd (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
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

/-- Internal ConnectProxy proof helper `closeRelayBoth_wf_poll_netErrs`. -/
theorem closeRelayBoth_wf_poll_netErrs
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

/-- Internal ConnectProxy proof helper `flushBytesNonblock_pollOutcomes_eq`. -/
theorem flushBytesNonblock_pollOutcomes_eq
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


end LeanSwe.ConnectProxy.Proofs

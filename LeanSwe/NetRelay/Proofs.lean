import Core.Obeys
import Core.NondetTest
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.NetRelay.Impl
import LeanSwe.NetRelay.Interface
import LeanSwe.NetRelay.SpecTests
import LeanSwe.NetRelay.Proofs.RingBufProofs
import LeanSwe.NetRelay.Proofs.StepProofs

namespace LeanSwe.NetRelay.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Model

private theorem shutdownWrClean_obeys {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.ObeysStep proj relayStepWf (execRawStep raw) allowedRawStep)
    (fd : Nat) :
    ∀ (fuel : Nat) (w : W), (proj w).wf = true →
      let r := (Internal.shutdownWrClean raw.net fd fuel).run w
      allowedPkgStep (proj w) (.shutdownWrClean fd fuel) (.flag r.1) (proj r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hWf
    exact ⟨hWf, rfl, rfl, rfl, rfl⟩
  | succ fuel ih =>
    intro w hWf
    rcases hCall : (raw.net.shutdown fd .wr).run w with ⟨res, w1⟩
    have hStep := hRaw w (.shutdown fd .wr) hWf
    have hMap : (execRawStep raw (.shutdown fd .wr)).run w = (.shut res, w1) :=
      stateM_map_eq RelayRawOut.shut _ w hCall
    dsimp only at hStep
    rw [hMap] at hStep
    rcases hStep with ⟨hWf1, hBody⟩
    have hBind : (Internal.shutdownWrClean raw.net fd (fuel + 1)).run w =
        (match res with
          | .ok () => pure true
          | .error e =>
            if e == Errno.EINTR then Internal.shutdownWrClean raw.net fd fuel
            else if e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE then pure true
            else pure false : StateM W Bool).run w1 := by
      conv => lhs; unfold Internal.shutdownWrClean
      rw [stateM_bind_eq (h := hCall)]
      cases res <;> rfl
    dsimp only
    rw [hBind]
    cases res with
    | ok u =>
      cases u
      rcases hBody with ⟨hCl1, hRx1, hTx1, _, hSh1⟩
      exact ⟨hWf1, hCl1, hRx1, hTx1, Or.inl hSh1⟩
    | error e =>
      rcases hBody with ⟨hCl1, hRx1, hTx1, hErr1, hSh1⟩
      by_cases hEintr : (e == Errno.EINTR) = true
      · simp only [hEintr, ↓reduceIte]
        have hRec := ih w1 hWf1
        rcases hSub : (Internal.shutdownWrClean raw.net fd fuel).run w1 with ⟨b, w2⟩
        dsimp only at hRec
        rw [hSub] at hRec
        cases b with
        | false =>
          rcases hRec with ⟨hWf2, hCl2, hRx2, hTx2, hSh2⟩
          exact ⟨hWf2, hCl2.trans hCl1, hRx2.trans hRx1, hTx2.trans hTx1, hSh2.trans hSh1⟩
        | true =>
          rcases hRec with ⟨hWf2, hCl2, hRx2, hTx2, hBranch⟩
          refine ⟨hWf2, hCl2.trans hCl1, hRx2.trans hRx1, hTx2.trans hTx1, ?_⟩
          rcases hBranch with hSd | ⟨hSdEq, errTail, hErr2, e', heIn, heBen⟩
          · exact Or.inl (by rw [hSd, hSh1])
          · exact Or.inr ⟨hSdEq.trans hSh1, e :: errTail,
              by rw [hErr2, hErr1, List.append_assoc]; rfl,
              e', List.mem_cons_of_mem _ heIn, heBen⟩
      · have hEintrF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEintr
        simp only [hEintrF, Bool.false_eq_true, ↓reduceIte]
        by_cases hBen : (e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE) = true
        · simp only [hBen, ↓reduceIte, pure, StateT.pure, StateT.run]
          exact ⟨hWf1, hCl1, hRx1, hTx1,
            Or.inr ⟨hSh1, [e], hErr1, e, List.mem_singleton_self _, hBen⟩⟩
        · have hBenF : (e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE) = false :=
            Bool.eq_false_iff.mpr hBen
          simp only [hBenF, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
          exact ⟨hWf1, hCl1, hRx1, hTx1, hSh1⟩

private theorem drainDeadPeerRx_obeys {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.ObeysStep proj relayStepWf (execRawStep raw) allowedRawStep)
    (fd : Nat) :
    ∀ (fuel : Nat) (w : W), (proj w).wf = true →
      let r := (Internal.drainDeadPeerRx raw.net fd fuel).run w
      allowedPkgStep (proj w) (.drainDeadPeerRx fd fuel) (.flag r.1) (proj r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hWf
    change allowedPkgStep (proj w) (.drainDeadPeerRx fd 0) (.flag false) (proj w)
    exact ⟨hWf, fun h => Bool.noConfusion h, rfl, rfl, rfl, [], by simp⟩
  | succ fuel ih =>
    intro w hWf
    rcases hCall : (raw.net.recvfrom fd 4096 { dontwait := true }).run w with ⟨res, w1⟩
    have hStep := hRaw w (.recvfrom fd 4096 { dontwait := true }) hWf
    have hMap : (execRawStep raw (.recvfrom fd 4096 { dontwait := true })).run w = (.bytes res, w1) :=
      stateM_map_eq RelayRawOut.bytes _ w hCall
    dsimp only at hStep
    rw [hMap] at hStep
    rcases hStep with ⟨hWf1, hBody⟩
    have hBind : (Internal.drainDeadPeerRx raw.net fd (fuel + 1)).run w =
        (match res with
          | .ok bs => if bs.size == 0 then pure true else Internal.drainDeadPeerRx raw.net fd fuel
          | .error e =>
            if e == Errno.EINTR then Internal.drainDeadPeerRx raw.net fd fuel
            else if e == Errno.EAGAIN then pure false else pure true : StateM W Bool).run w1 := by
      conv => lhs; unfold Internal.drainDeadPeerRx
      rw [stateM_bind_eq (h := hCall)]
      cases res <;> rfl
    dsimp only
    rw [hBind]
    cases res with
    | ok bs =>
      rcases hBody with ⟨_, hCl1, hRx1, hTx1, _, hSh1⟩
      by_cases hEmpty : (bs.size == 0) = true
      · simp only [hEmpty, ↓reduceIte, pure, StateT.pure, StateT.run]
        exact ⟨hWf1, fun _ => Nat.succ_pos _, hCl1, hTx1, hSh1, bs.data.toList, hRx1⟩
      · have hEmptyF : (bs.size == 0) = false := Bool.eq_false_iff.mpr hEmpty
        simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
        have hRec := ih w1 hWf1
        rcases hSub : (Internal.drainDeadPeerRx raw.net fd fuel).run w1 with ⟨b, w2⟩
        dsimp only at hRec
        rw [hSub] at hRec
        rcases hRec with ⟨hWf2, _, hCl2, hTx2, hSh2, rxTail, hRx2⟩
        exact ⟨hWf2, fun _ => Nat.succ_pos _, hCl2.trans hCl1, hTx2.trans hTx1,
          hSh2.trans hSh1, bs.data.toList ++ rxTail, by rw [hRx2, hRx1, List.append_assoc]⟩
    | error e =>
      rcases hBody with ⟨hCl1, hRx1, hTx1, _, hSh1⟩
      by_cases hEintr : (e == Errno.EINTR) = true
      · simp only [hEintr, ↓reduceIte]
        have hRec := ih w1 hWf1
        rcases hSub : (Internal.drainDeadPeerRx raw.net fd fuel).run w1 with ⟨b, w2⟩
        dsimp only at hRec
        rw [hSub] at hRec
        rcases hRec with ⟨hWf2, _, hCl2, hTx2, hSh2, rxTail, hRx2⟩
        exact ⟨hWf2, fun _ => Nat.succ_pos _, hCl2.trans hCl1, hTx2.trans hTx1,
          hSh2.trans hSh1, rxTail, by rw [hRx2, hRx1]⟩
      · have hEintrF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEintr
        simp only [hEintrF, Bool.false_eq_true, ↓reduceIte]
        by_cases hAgain : (e == Errno.EAGAIN) = true
        · simp only [hAgain, ↓reduceIte, pure, StateT.pure, StateT.run]
          exact ⟨hWf1, fun h => Bool.noConfusion h, hCl1, hTx1, hSh1, [], by simpa using hRx1⟩
        · have hAgainF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAgain
          simp only [hAgainF, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
          exact ⟨hWf1, fun _ => Nat.succ_pos _, hCl1, hTx1, hSh1, [], by simpa using hRx1⟩

private theorem obeysStepFrom_mkRelayApiM :
    Core.ObeysStepFrom id Model.relayStepWf
      Model.execRawStep Model.allowedRawStep
      Model.relayStepWf Internal.mkRelayApiM
      Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  cases req with
  | closeOptFd fd? =>
    cases fd? with
    | none =>
      exact ⟨hWf, by simp [execPkgStep, Internal.mkRelayApiM, Internal.closeOptFd,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run], rfl, rfl, rfl, rfl⟩
    | some fd =>
      rcases hCall : (raw.closeFd fd).run w with ⟨u, w1⟩
      have hStep := hRaw w (.closeFd fd) hWf
      have hRawEq : (execRawStep raw (.closeFd fd)).run w = (.unit, w1) := by
        unfold execRawStep
        exact stateM_bind_eq _ _ w hCall
      have hPkgEq : (execPkgStep (Internal.mkRelayApiM raw) (.closeOptFd (some fd))).run w =
          (.unit, w1) := by
        unfold execPkgStep Internal.mkRelayApiM Internal.closeOptFd
        exact stateM_bind_eq _ _ w hCall
      dsimp only at hStep ⊢
      rw [hRawEq] at hStep
      rw [hPkgEq]
      rcases hStep with ⟨hWf1, hCl1, hRx1, hTx1, hErr1, hSh1⟩
      exact ⟨hWf1, hCl1, hRx1, hTx1, hErr1, hSh1⟩
  | flushBytesNonblock fd bytes fuel off =>
    rcases hCall : (Internal.flushBytesNonblock raw.net fd bytes fuel off).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.flushBytesNonblock fd bytes fuel off)).run w = (.optNat res, w1) :=
      stateM_map_eq RelayPkgOut.optNat _ w hCall
    have hSub := flushBytesNonblock_obeys proj raw hRaw fd bytes fuel off w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | recvIntoRing fd fuel rb =>
    rcases hCall : (Internal.recvIntoRing raw.net fd fuel rb).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.recvIntoRing fd fuel rb)).run w = (.optRecv res, w1) :=
      stateM_map_eq RelayPkgOut.optRecv _ w hCall
    have hSub := recvIntoRing_obeys proj raw hRaw fd fuel rb w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | flushRingNonblock fd fuel rb =>
    rcases hCall : (Internal.flushRingNonblock raw.net fd fuel rb).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.flushRingNonblock fd fuel rb)).run w = (.optBuf res, w1) :=
      stateM_map_eq RelayPkgOut.optBuf _ w hCall
    have hSub := flushRingNonblock_obeys proj raw hRaw fd fuel rb w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | shutdownWrClean fd fuel =>
    rcases hCall : (Internal.shutdownWrClean raw.net fd fuel).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.shutdownWrClean fd fuel)).run w = (.flag res, w1) :=
      stateM_map_eq RelayPkgOut.flag _ w hCall
    have hSub := shutdownWrClean_obeys proj raw hRaw fd fuel w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | drainDeadPeerRx fd fuel =>
    rcases hCall : (Internal.drainDeadPeerRx raw.net fd fuel).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.drainDeadPeerRx fd fuel)).run w = (.flag res, w1) :=
      stateM_map_eq RelayPkgOut.flag _ w hCall
    have hSub := drainDeadPeerRx_obeys proj raw hRaw fd fuel w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub

/-- Full public `Interface` obedience of `LeanSwe.NetRelay` against `LeanSwe.NetRelay.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.NetRelay.RingBuf.len Model.ringBufLen ∧
    Core.ObeysPureEq LeanSwe.NetRelay.RingBuf.isEmpty Model.ringBufIsEmpty ∧
    Core.ObeysPureEq LeanSwe.NetRelay.RingBuf.writeAvail Model.ringBufWriteAvail ∧
    Core.ObeysPureEq LeanSwe.NetRelay.RingBuf.toList Model.ringBufToList ∧
    Core.ObeysPureEq LeanSwe.NetRelay.RingBuf.frontSlice Model.ringBufFrontSlice ∧
    Core.ObeysPure2 LeanSwe.NetRelay.RingBuf.push Model.allowedRingBufPush ∧
    Core.ObeysPureEq2 LeanSwe.NetRelay.RingBuf.consume Model.ringBufConsumeModel ∧
    Core.ObeysStepFrom id Model.relayStepWf
      Model.execRawStep Model.allowedRawStep
      Model.relayStepWf Internal.mkRelayApiM
      Model.execPkgStep Model.allowedPkgStep :=
  ⟨fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   ringBuf_frontSlice_eq_model,
   ringBuf_push_obeys_allowed,
   fun _ _ => rfl,
   obeysStepFrom_mkRelayApiM⟩

/-- `defaultRingBufApi` satisfies `test_netRelay_ringBuf_pushAndViewLaws`. -/
theorem test_netRelay_ringBuf_pushAndViewLaws_allPass :
    Core.AllPass (test_netRelay_ringBuf_pushAndViewLaws Internal.defaultRingBufApi) := by
  intro rb chunk
  have hPush := ringBuf_push_obeys_allowed rb chunk
  refine ⟨rfl, rfl, rfl, rfl, ringBuf_frontSlice_toList rb,
    ringBuf_frontSlice_size_le_cap rb, hPush.1, hPush.2.1, hPush.2.2, trivial⟩

/-- `defaultRingBufApi` satisfies `test_netRelay_ringBuf_consumePreservesCapAndFifo`. -/
theorem test_netRelay_ringBuf_consumePreservesCapAndFifo_allPass :
    Core.AllPass (test_netRelay_ringBuf_consumePreservesCapAndFifo Internal.defaultRingBufApi) := by
  intro rb n hLe
  exact ⟨ringBuf_consume_cap rb n, ringBuf_consume_len_le_cap rb n hLe,
    ringBuf_consume_toList rb n hLe, trivial⟩

/-- Reachability witness for `test_netRelay_ringBuf_consumePreservesCapAndFifo`. -/
theorem test_netRelay_ringBuf_consumePreservesCapAndFifo_canReach :
    Core.CanReach (test_netRelay_ringBuf_consumePreservesCapAndFifo Internal.defaultRingBufApi) := by
  exact ⟨{}, 0, by decide, ⟨rfl, by decide, rfl, trivial⟩⟩

/-- `Internal.mkRelayApiM` satisfies `test_netRelay_recvIntoRing_eintrCapAndErrors`. -/
theorem test_netRelay_recvIntoRing_eintrCapAndErrors_allPass :
    Core.AllPass (test_netRelay_recvIntoRing_eintrCapAndErrors Internal.mkRelayApiM) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- `Internal.mkRelayApiM` satisfies `test_netRelay_flushRingNonblock_shortWritesAndEintr`. -/
theorem test_netRelay_flushRingNonblock_shortWritesAndEintr_allPass :
    Core.AllPass (test_netRelay_flushRingNonblock_shortWritesAndEintr Internal.mkRelayApiM) := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, trivial⟩

/-- `Internal.mkRelayApiM` satisfies `test_netRelay_flushBytesShutdownDrainAndClose`. -/
theorem test_netRelay_flushBytesShutdownDrainAndClose_allPass :
    Core.AllPass (test_netRelay_flushBytesShutdownDrainAndClose Internal.mkRelayApiM) := by
  refine ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩

end LeanSwe.NetRelay.Proofs

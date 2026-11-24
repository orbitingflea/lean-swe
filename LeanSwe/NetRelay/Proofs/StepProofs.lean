import Core.Obeys
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.NetRelay.Impl
import LeanSwe.NetRelay.Interface
import LeanSwe.NetRelay.Proofs.RingBufProofs

namespace LeanSwe.NetRelay.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Model

/-- Unfold `StateM` bind along a concrete step run. -/
theorem stateM_bind_eq {W α β : Type} (ma : StateM W α) (f : α → StateM W β)
    (w : W) {a : α} {w1 : W} (h : ma.run w = (a, w1)) :
    (ma >>= f).run w = (f a).run w1 := by
  change (match ma.run w with | (x, s) => (f x).run s) = (f a).run w1
  rw [h]

/-- Unfold `StateM` map along a concrete step run. -/
theorem stateM_map_eq {W α β : Type} (g : α → β) (ma : StateM W α)
    (w : W) {a : α} {w1 : W} (h : ma.run w = (a, w1)) :
    (g <$> ma).run w = (g a, w1) := by
  change (match ma.run w with | (x, s) => (g x, s)) = (g a, w1)
  rw [h]

private theorem reqCap_toNat_le (avail : Nat) :
    (UInt32.ofNat (Nat.min avail MAX_READ_BYTES.toNat)).toNat ≤ avail := by
  have hMax : MAX_READ_BYTES.toNat = 16777216 := rfl
  have hLt : Nat.min avail MAX_READ_BYTES.toNat < UInt32.size := by
    have hLe : Nat.min avail MAX_READ_BYTES.toNat ≤ MAX_READ_BYTES.toNat := Nat.min_le_right _ _
    change Nat.min avail MAX_READ_BYTES.toNat < 4294967296
    omega
  have hMod : (UInt32.ofNat (Nat.min avail MAX_READ_BYTES.toNat)).toNat =
      Nat.min avail MAX_READ_BYTES.toNat % 2 ^ 32 := UInt32.toNat_ofNat'
  rw [hMod, Nat.mod_eq_of_lt hLt]
  exact Nat.min_le_left _ _

/-- `Internal.flushBytesNonblock` obeys `allowedPkgStep` when `raw` obeys `allowedRawStep`. -/
theorem flushBytesNonblock_obeys {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.ObeysStep proj relayStepWf (execRawStep raw) allowedRawStep)
    (fd : Nat) (bytes : ByteArray) :
    ∀ (fuel off : Nat) (w : W), (proj w).wf = true →
      let r := (Internal.flushBytesNonblock raw.net fd bytes fuel off).run w
      allowedPkgStep (proj w) (.flushBytesNonblock fd bytes fuel off) (.optNat r.1) (proj r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro off w hWf
    change allowedPkgStep (proj w) (.flushBytesNonblock fd bytes 0 off) (.optNat (some off)) (proj w)
    exact ⟨hWf, Nat.le_refl _, Nat.le_max_left _ _, rfl, rfl, by simp, rfl⟩
  | succ fuel ih =>
    intro off w hWf
    by_cases hDone : off ≥ bytes.size
    · have hRun : (Internal.flushBytesNonblock raw.net fd bytes (fuel + 1) off).run w = (some off, w) := by
        unfold Internal.flushBytesNonblock; simp [hDone, Pure.pure, StateT.pure, StateT.run]
      dsimp only
      rw [hRun]
      exact ⟨hWf, Nat.le_refl _, Nat.le_max_left _ _, rfl, rfl, by simp, rfl⟩
    · have hOffLt : off < bytes.size := Nat.lt_of_not_le hDone
      let slice := if off == 0 then bytes else bytes.extract off bytes.size
      have hSliceList : slice.data.toList = bytes.data.toList.drop off := by
        dsimp only [slice]
        by_cases h0 : (off == 0) = true
        · have hOff0 : off = 0 := beq_iff_eq.mp h0
          subst hOff0; simp
        · have hF : (off == 0) = false := Bool.eq_false_iff.mpr h0
          simp only [hF, Bool.false_eq_true, ↓reduceIte, byteArray_extract_end_toList]
      have hSliceSz : slice.size = bytes.size - off := by
        have := congrArg List.length hSliceList
        simpa [ByteArray.size_data, Array.length_toList] using this
      rcases hCall : (raw.net.sendto fd slice { nosignal := true, dontwait := true }).run w with ⟨res, w1⟩
      have hStep := hRaw w (.sendto fd slice { nosignal := true, dontwait := true }) hWf
      have hMap : (execRawStep raw (.sendto fd slice { nosignal := true, dontwait := true })).run w =
          (.sent res, w1) := stateM_map_eq RelayRawOut.sent _ w hCall
      dsimp only at hStep
      rw [hMap] at hStep
      rcases hStep with ⟨hWf1, hBody⟩
      have hBind : (Internal.flushBytesNonblock raw.net fd bytes (fuel + 1) off).run w =
          (match res with
            | .ok n => if n == 0 then pure (some off)
                else Internal.flushBytesNonblock raw.net fd bytes fuel (off + Nat.min n.toNat slice.size)
            | .error e => if e == Errno.EINTR then Internal.flushBytesNonblock raw.net fd bytes fuel off
              else if e == Errno.EAGAIN then pure (some off) else pure none).run w1 := by
        conv => lhs; unfold Internal.flushBytesNonblock
        simp only [ge_iff_le, hDone, ↓reduceIte]
        rw [stateM_bind_eq (h := hCall)]
        cases res <;> rfl
      dsimp only
      rw [hBind]
      cases res with
      | ok n =>
        rcases hBody with ⟨hnLe, hClosed1, hRx1, hTx1, hErr1, hShut1⟩
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte, pure, StateT.pure, StateT.run]
          have hnEq0 : n.toNat = 0 := by have : n = 0 := beq_iff_eq.mp hn0; subst this; rfl
          rw [hnEq0, List.take_zero, List.append_nil] at hTx1
          exact ⟨hWf1, Nat.le_refl _, Nat.le_max_left _ _, hClosed1, hRx1, by simpa using hTx1, hShut1⟩
        · have hnF : (n == 0) = false := Bool.eq_false_iff.mpr hn0
          simp only [hnF, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_left hnLe]
          have hRec := ih (off + n.toNat) w1 hWf1
          rcases hSub : (Internal.flushBytesNonblock raw.net fd bytes fuel (off + n.toNat)).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hRx2, hSh2, errTail, hErr2, e, heIn, heNe⟩
            exact ⟨hWf2, hCl2.trans hClosed1, hRx2.trans hRx1, hSh2.trans hShut1,
              errTail, hErr2.trans (by rw [hErr1]), e, heIn, heNe⟩
          | some nextOff =>
            rcases hRec with ⟨hWf2, hOffLe, hMaxLe, hCl2, hRx2, hTx2, hSh2⟩
            refine ⟨hWf2, by omega, by omega, hCl2.trans hClosed1, hRx2.trans hRx1, ?_, hSh2.trans hShut1⟩
            rw [hTx2, hTx1, hSliceList, List.append_assoc]
            congr 1
            have hDrop : bytes.data.toList.drop (off + n.toNat) =
                (bytes.data.toList.drop off).drop n.toNat := by
              rw [List.drop_drop, Nat.add_comm]
            have hSplit :
                (bytes.data.toList.drop off).take (n.toNat + (nextOff - (off + n.toNat))) =
                  (bytes.data.toList.drop off).take n.toNat ++
                    ((bytes.data.toList.drop off).drop n.toNat).take (nextOff - (off + n.toNat)) :=
              List.take_add
            rw [hDrop, ← hSplit]
            congr 1
            omega
      | error e =>
        rcases hBody with ⟨hCl1, hRx1, hTx1, hErr1, hSh1⟩
        by_cases hEintr : (e == Errno.EINTR) = true
        · simp only [hEintr, ↓reduceIte]
          have hRec := ih off w1 hWf1
          rcases hSub : (Internal.flushBytesNonblock raw.net fd bytes fuel off).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hRx2, hSh2, errTail, hErr2, e', heIn, heNe⟩
            refine ⟨hWf2, hCl2.trans hCl1, hRx2.trans hRx1, hSh2.trans hSh1,
              e :: errTail, ?_, e', List.mem_cons_of_mem _ heIn, heNe⟩
            rw [hErr2, hErr1, List.append_assoc]; rfl
          | some nextOff =>
            rcases hRec with ⟨hWf2, hOffLe, hMaxLe, hCl2, hRx2, hTx2, hSh2⟩
            exact ⟨hWf2, hOffLe, hMaxLe, hCl2.trans hCl1, hRx2.trans hRx1,
              by rw [hTx2, hTx1], hSh2.trans hSh1⟩
        · have hEintrF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEintr
          simp only [hEintrF, Bool.false_eq_true, ↓reduceIte]
          by_cases hAgain : (e == Errno.EAGAIN) = true
          · simp only [hAgain, ↓reduceIte, pure, StateT.pure, StateT.run]
            exact ⟨hWf1, Nat.le_refl _, Nat.le_max_left _ _, hCl1, hRx1, by simpa using hTx1, hSh1⟩
          · have hAgainF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAgain
            simp only [hAgainF, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
            refine ⟨hWf1, hCl1, hRx1, hSh1, [e], hErr1, e, List.mem_singleton_self _, ?_, ?_⟩
            · intro hEq; exact hEintr (beq_iff_eq.mpr hEq)
            · intro hEq; exact hAgain (beq_iff_eq.mpr hEq)

/-- `Internal.recvIntoRing` obeys `allowedPkgStep` when `raw` obeys `allowedRawStep`. -/
theorem recvIntoRing_obeys {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.ObeysStep proj relayStepWf (execRawStep raw) allowedRawStep)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : W), (proj w).wf = true →
      let r := (Internal.recvIntoRing raw.net fd fuel rb).run w
      allowedPkgStep (proj w) (.recvIntoRing fd fuel rb) (.optRecv r.1) (proj r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rb w hWf
    change allowedPkgStep (proj w) (.recvIntoRing fd 0 rb) (.optRecv (some (rb, false))) (proj w)
    exact ⟨hWf, rfl, rfl, rfl, rfl, ⟨[], by simp, by simp⟩⟩
  | succ fuel ih =>
    intro rb w hWf
    by_cases hAvail0 : (Internal.ringBufWriteAvail rb == 0) = true
    · have hRun : (Internal.recvIntoRing raw.net fd (fuel + 1) rb).run w = (some (rb, false), w) := by
        unfold Internal.recvIntoRing; simp [hAvail0, Pure.pure, StateT.pure, StateT.run]
      dsimp only
      rw [hRun]
      exact ⟨hWf, rfl, rfl, rfl, rfl, ⟨[], by simp, by simp⟩⟩
    · have hAvailF : (Internal.ringBufWriteAvail rb == 0) = false := Bool.eq_false_iff.mpr hAvail0
      let avail := Internal.ringBufWriteAvail rb
      let reqCap := Nat.min avail MAX_READ_BYTES.toNat
      rcases hCall : (raw.net.recvfrom fd (UInt32.ofNat reqCap) { dontwait := true }).run w with ⟨res, w1⟩
      have hStep := hRaw w (.recvfrom fd (UInt32.ofNat reqCap) { dontwait := true }) hWf
      have hMap : (execRawStep raw (.recvfrom fd (UInt32.ofNat reqCap) { dontwait := true })).run w =
          (.bytes res, w1) := stateM_map_eq RelayRawOut.bytes _ w hCall
      dsimp only at hStep
      rw [hMap] at hStep
      rcases hStep with ⟨hWf1, hBody⟩
      have hBind : (Internal.recvIntoRing raw.net fd (fuel + 1) rb).run w =
          (match res with
            | .ok bs => if bs.size == 0 then pure (some (rb, true))
                else
                  let chunk := if bs.size <= reqCap then bs else bs.extract 0 reqCap
                  Internal.recvIntoRing raw.net fd fuel (Internal.ringBufPush rb chunk)
            | .error e => if e == Errno.EINTR then Internal.recvIntoRing raw.net fd fuel rb
              else if e == Errno.EAGAIN then pure (some (rb, false))
              else if e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK then pure none
              else pure (some (rb, true))).run w1 := by
        conv => lhs; unfold Internal.recvIntoRing
        simp only [hAvailF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_eq (h := hCall)]
        cases res <;> rfl
      dsimp only
      rw [hBind]
      cases res with
      | ok bs =>
        rcases hBody with ⟨hSzLe, hCl1, hRx1, hTx1, hErr1, hSh1⟩
        by_cases hEmpty : (bs.size == 0) = true
        · simp only [hEmpty, ↓reduceIte, pure, StateT.pure, StateT.run]
          have hBs0 : bs.data.toList = [] := List.eq_nil_of_length_eq_zero (by
            have : bs.size = 0 := beq_iff_eq.mp hEmpty; simpa using this)
          rw [hBs0, List.append_nil] at hRx1
          exact ⟨hWf1, rfl, hCl1, hTx1, hSh1, ⟨[], by simpa using hRx1, by simp⟩⟩
        · have hEmptyF : (bs.size == 0) = false := Bool.eq_false_iff.mpr hEmpty
          have hMax : MAX_READ_BYTES.toNat = 16777216 := rfl
          have hReqLt : reqCap < UInt32.size := by
            have : reqCap ≤ MAX_READ_BYTES.toNat := Nat.min_le_right _ _
            change reqCap < 4294967296; omega
          have hReqEq : (UInt32.ofNat reqCap).toNat = reqCap := by
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hReqLt]
          have hBsLeReq : bs.size ≤ reqCap := by rwa [← hReqEq]
          simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte, hBsLeReq]
          have hCapPush : (Internal.ringBufPush rb bs).cap = rb.cap := ringBuf_push_cap rb bs
          have hListLe : bs.size ≤ avail := Nat.le_trans hSzLe (reqCap_toNat_le avail)
          have hAvailEq : avail = rb.cap - rb.toList.length := by
            show rb.cap - Nat.min (rb.buf.size - rb.off) rb.cap = rb.cap - rb.toList.length
            rw [ringBuf_toList_length rb]; rfl
          have hPushList : ringBufToList (Internal.ringBufPush rb bs) =
              ringBufToList rb ++ bs.data.toList := by
            have hTakeAll : bs.data.toList.take (rb.cap - rb.toList.length) = bs.data.toList :=
              List.take_of_length_le (by
                have hLen : bs.data.toList.length = bs.size := by simp
                omega)
            have hEq := ringBuf_push_toList rb bs
            change ringBufToList (Internal.ringBufPush rb bs) =
                ringBufToList rb ++ bs.data.toList.take (rb.cap - rb.toList.length) at hEq
            rw [hEq, hTakeAll]
          have hRec := ih (Internal.ringBufPush rb bs) w1 hWf1
          rcases hSub : (Internal.recvIntoRing raw.net fd fuel (Internal.ringBufPush rb bs)).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hTx2, hSh2, errTail, hErr2, e, heIn, heFat⟩
            exact ⟨hWf2, hCl2.trans hCl1, hTx2.trans hTx1, hSh2.trans hSh1,
              errTail, hErr2.trans (by rw [hErr1]), e, heIn, heFat⟩
          | some pair =>
            rcases pair with ⟨rb', eof'⟩
            rcases hRec with ⟨hWf2, hCap', hCl2, hTx2, hSh2, rxTail, hRx2, hList2⟩
            refine ⟨hWf2, hCap'.trans hCapPush, hCl2.trans hCl1, hTx2.trans hTx1, hSh2.trans hSh1,
              bs.data.toList ++ rxTail, ?_, ?_⟩
            · rw [hRx2, hRx1, List.append_assoc]
            · rw [hList2, hPushList, List.append_assoc]
      | error e =>
        rcases hBody with ⟨hCl1, hRx1, hTx1, hErr1, hSh1⟩
        by_cases hEintr : (e == Errno.EINTR) = true
        · simp only [hEintr, ↓reduceIte]
          have hRec := ih rb w1 hWf1
          rcases hSub : (Internal.recvIntoRing raw.net fd fuel rb).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hTx2, hSh2, errTail, hErr2, e', heIn, heFat⟩
            refine ⟨hWf2, hCl2.trans hCl1, hTx2.trans hTx1, hSh2.trans hSh1,
              e :: errTail, ?_, e', List.mem_cons_of_mem _ heIn, heFat⟩
            rw [hErr2, hErr1, List.append_assoc]; rfl
          | some pair =>
            rcases pair with ⟨rb', eof'⟩
            rcases hRec with ⟨hWf2, hCap', hCl2, hTx2, hSh2, rxTail, hRx2, hList2⟩
            exact ⟨hWf2, hCap', hCl2.trans hCl1, hTx2.trans hTx1, hSh2.trans hSh1,
              rxTail, by rw [hRx2, hRx1], hList2⟩
        · have hEintrF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEintr
          simp only [hEintrF, Bool.false_eq_true, ↓reduceIte]
          by_cases hAgain : (e == Errno.EAGAIN) = true
          · simp only [hAgain, ↓reduceIte, pure, StateT.pure, StateT.run]
            exact ⟨hWf1, rfl, hCl1, hTx1, hSh1, ⟨[], by simpa using hRx1, by simp⟩⟩
          · have hAgainF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAgain
            simp only [hAgainF, Bool.false_eq_true, ↓reduceIte]
            by_cases hFat : (e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK) = true
            · simp only [hFat, ↓reduceIte, pure, StateT.pure, StateT.run]
              exact ⟨hWf1, hCl1, hTx1, hSh1, [e], hErr1, e, List.mem_singleton_self _, hFat⟩
            · have hFatF : (e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK) = false :=
                Bool.eq_false_iff.mpr hFat
              simp only [hFatF, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
              exact ⟨hWf1, rfl, hCl1, hTx1, hSh1, ⟨[], by simpa using hRx1, by simp⟩⟩

/-- `Internal.flushRingNonblock` obeys `allowedPkgStep` when `raw` obeys `allowedRawStep`. -/
theorem flushRingNonblock_obeys {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.ObeysStep proj relayStepWf (execRawStep raw) allowedRawStep)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : W), (proj w).wf = true →
      let r := (Internal.flushRingNonblock raw.net fd fuel rb).run w
      allowedPkgStep (proj w) (.flushRingNonblock fd fuel rb) (.optBuf r.1) (proj r.2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rb w hWf
    change allowedPkgStep (proj w) (.flushRingNonblock fd 0 rb) (.optBuf (some rb)) (proj w)
    exact ⟨hWf, rfl, rfl, rfl, rfl, [], by simp, fun hLe => ⟨hLe, by simp⟩⟩
  | succ fuel ih =>
    intro rb w hWf
    by_cases hEmpty : Internal.ringBufIsEmpty rb = true
    · have hRun : (Internal.flushRingNonblock raw.net fd (fuel + 1) rb).run w = (some rb, w) := by
        unfold Internal.flushRingNonblock; simp [hEmpty, Pure.pure, StateT.pure, StateT.run]
      dsimp only
      rw [hRun]
      exact ⟨hWf, rfl, rfl, rfl, rfl, [], by simp, fun hLe => ⟨hLe, by simp⟩⟩
    · have hEmptyF : Internal.ringBufIsEmpty rb = false := Bool.eq_false_iff.mpr hEmpty
      let slice := Internal.ringBufFrontSlice rb
      rcases hCall : (raw.net.sendto fd slice { nosignal := true, dontwait := true }).run w with ⟨res, w1⟩
      have hStep := hRaw w (.sendto fd slice { nosignal := true, dontwait := true }) hWf
      have hMap : (execRawStep raw (.sendto fd slice { nosignal := true, dontwait := true })).run w =
          (.sent res, w1) := stateM_map_eq RelayRawOut.sent _ w hCall
      dsimp only at hStep
      rw [hMap] at hStep
      rcases hStep with ⟨hWf1, hBody⟩
      have hBind : (Internal.flushRingNonblock raw.net fd (fuel + 1) rb).run w =
          (match res with
            | .ok n => if n == 0 then pure (some rb)
                else Internal.flushRingNonblock raw.net fd fuel (Internal.ringBufConsume rb n.toNat)
            | .error e => if e == Errno.EINTR then Internal.flushRingNonblock raw.net fd fuel rb
              else if e == Errno.EAGAIN then pure (some rb) else pure none).run w1 := by
        conv => lhs; unfold Internal.flushRingNonblock
        simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_eq (h := hCall)]
        cases res <;> rfl
      dsimp only
      rw [hBind]
      cases res with
      | ok n =>
        rcases hBody with ⟨_, hCl1, hRx1, hTx1, hErr1, hSh1⟩
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte, pure, StateT.pure, StateT.run]
          have hnEq0 : n.toNat = 0 := by have : n = 0 := beq_iff_eq.mp hn0; subst this; rfl
          rw [hnEq0, List.take_zero, List.append_nil] at hTx1
          exact ⟨hWf1, rfl, hCl1, hRx1, hSh1, [], by simpa using hTx1, fun hLe => ⟨hLe, by simp⟩⟩
        · have hnF : (n == 0) = false := Bool.eq_false_iff.mpr hn0
          simp only [hnF, Bool.false_eq_true, ↓reduceIte]
          have hCapCon : (Internal.ringBufConsume rb n.toNat).cap = rb.cap :=
            ringBuf_consume_cap rb n.toNat
          have hSliceList : slice.data.toList = ringBufToList rb :=
            ringBuf_frontSlice_toList rb
          have hRec := ih (Internal.ringBufConsume rb n.toNat) w1 hWf1
          rcases hSub : (Internal.flushRingNonblock raw.net fd fuel (Internal.ringBufConsume rb n.toNat)).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hRx2, hSh2, errTail, hErr2, e, heIn, heNe⟩
            exact ⟨hWf2, hCl2.trans hCl1, hRx2.trans hRx1, hSh2.trans hSh1,
              errTail, hErr2.trans (by rw [hErr1]), e, heIn, heNe⟩
          | some rb' =>
            rcases hRec with ⟨hWf2, hCap', hCl2, hRx2, hSh2, txTail, hTx2, hCons⟩
            refine ⟨hWf2, hCap'.trans hCapCon, hCl2.trans hCl1, hRx2.trans hRx1, hSh2.trans hSh1,
              slice.data.toList.take n.toNat ++ txTail,
              by rw [hTx2, hTx1, List.append_assoc], ?_⟩
            intro hLe
            have hConLe : ringBufLen (Internal.ringBufConsume rb n.toNat) ≤
                (Internal.ringBufConsume rb n.toNat).cap := by
              rw [hCapCon]
              exact ringBuf_consume_len_le_cap rb n.toNat hLe
            rcases hCons hConLe with ⟨hRb'Le, hConsEq⟩
            refine ⟨by simpa [hCapCon] using hRb'Le, ?_⟩
            rw [List.append_assoc, hConsEq, hSliceList]
            have hDropEq : ringBufToList (Internal.ringBufConsume rb n.toNat) =
                (ringBufToList rb).drop n.toNat :=
              ringBuf_consume_toList rb n.toNat hLe
            rw [hDropEq, List.take_append_drop]
      | error e =>
        rcases hBody with ⟨hCl1, hRx1, hTx1, hErr1, hSh1⟩
        by_cases hEintr : (e == Errno.EINTR) = true
        · simp only [hEintr, ↓reduceIte]
          have hRec := ih rb w1 hWf1
          rcases hSub : (Internal.flushRingNonblock raw.net fd fuel rb).run w1 with ⟨out2, w2⟩
          dsimp only at hRec
          rw [hSub] at hRec
          cases out2 with
          | none =>
            rcases hRec with ⟨hWf2, hCl2, hRx2, hSh2, errTail, hErr2, e', heIn, heNe⟩
            refine ⟨hWf2, hCl2.trans hCl1, hRx2.trans hRx1, hSh2.trans hSh1,
              e :: errTail, ?_, e', List.mem_cons_of_mem _ heIn, heNe⟩
            rw [hErr2, hErr1, List.append_assoc]; rfl
          | some rb' =>
            rcases hRec with ⟨hWf2, hCap', hCl2, hRx2, hSh2, txTail, hTx2, hCons⟩
            exact ⟨hWf2, hCap', hCl2.trans hCl1, hRx2.trans hRx1, hSh2.trans hSh1,
              txTail, by rw [hTx2, hTx1], hCons⟩
        · have hEintrF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEintr
          simp only [hEintrF, Bool.false_eq_true, ↓reduceIte]
          by_cases hAgain : (e == Errno.EAGAIN) = true
          · simp only [hAgain, ↓reduceIte, pure, StateT.pure, StateT.run]
            exact ⟨hWf1, rfl, hCl1, hRx1, hSh1, [], by simpa using hTx1, fun hLe => ⟨hLe, by simp⟩⟩
          · have hAgainF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAgain
            simp only [hAgainF, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, StateT.run]
            refine ⟨hWf1, hCl1, hRx1, hSh1, [e], hErr1, e, List.mem_singleton_self _, ?_, ?_⟩
            · intro hEq; exact hEintr (beq_iff_eq.mpr hEq)
            · intro hEq; exact hAgain (beq_iff_eq.mpr hEq)

end LeanSwe.NetRelay.Proofs

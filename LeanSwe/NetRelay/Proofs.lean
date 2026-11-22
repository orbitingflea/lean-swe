import Core.Refines
import Core.NondetTest
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.NetRelay.Impl
import LeanSwe.NetRelay.Interface
import LeanSwe.NetRelay.SpecTests

namespace LeanSwe.NetRelay.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Model

private theorem nat_min_eq_min (a b : Nat) : Nat.min a b = min a b := rfl

private theorem stateM_bind_eq {W α β : Type} (ma : StateM W α) (f : α → StateM W β)
    (w : W) {a : α} {w1 : W} (h : ma.run w = (a, w1)) :
    (ma >>= f).run w = (f a).run w1 := by
  change (match ma.run w with | (x, s) => (f x).run s) = (f a).run w1
  rw [h]

private theorem stateM_map_eq {W α β : Type} (g : α → β) (ma : StateM W α)
    (w : W) {a : α} {w1 : W} (h : ma.run w = (a, w1)) :
    (g <$> ma).run w = (g a, w1) := by
  change (match ma.run w with | (x, s) => (g x, s)) = (g a, w1)
  rw [h]

/-- Byte extraction view as `List.take`/`List.drop` over `ByteArray.data.toList`. -/
theorem byteArray_extract_toList (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

/-- Extracting a suffix `b.extract off b.size` matches `b.data.toList.drop off`. -/
theorem byteArray_extract_end_toList (b : ByteArray) (off : Nat) :
    (b.extract off b.size).data.toList = b.data.toList.drop off := by
  rw [byteArray_extract_toList]
  have hLen : (b.data.toList.drop off).length = b.size - off := by simp
  exact List.take_of_length_le (by omega)

/-- `RingBuf.push` preserves the configured capacity `rb.cap`. -/
theorem ringBuf_push_cap (rb : RingBuf) (chunk : ByteArray) :
    (rb.push chunk).cap = rb.cap := by
  unfold RingBuf.push Internal.ringBufPush
  dsimp only
  split <;> rfl

/-- `RingBuf.consume` preserves the configured capacity `rb.cap`. -/
theorem ringBuf_consume_cap (rb : RingBuf) (n : Nat) :
    (rb.consume n).cap = rb.cap := by
  unfold RingBuf.consume Internal.ringBufConsume
  dsimp only
  split <;> rfl

/-- `RingBuf.frontSlice` never exceeds `rb.cap`. -/
theorem ringBuf_frontSlice_size_le_cap (rb : RingBuf) :
    rb.frontSlice.size ≤ rb.cap := by
  unfold RingBuf.frontSlice Internal.ringBufFrontSlice Internal.ringBufLen
  simp only [nat_min_eq_min]
  split
  · simp
  · split
    · rename_i hEq
      simp only [Bool.and_eq_true, beq_iff_eq] at hEq
      omega
    · simp only [ByteArray.size_extract]
      omega

/-- `RingBuf.push` maintains the capacity invariant `len ≤ rb.cap` across all chunk sizes. -/
theorem ringBuf_push_len_le_cap (rb : RingBuf) (chunk : ByteArray) :
    (rb.push chunk).len ≤ rb.cap := by
  have hAct : (Internal.ringBufFrontSlice rb).size ≤ rb.cap := ringBuf_frontSlice_size_le_cap rb
  unfold RingBuf.push RingBuf.len Internal.ringBufPush Internal.ringBufLen
  simp only [nat_min_eq_min]
  split
  · simp only [Nat.sub_zero]; exact hAct
  · split
    · split
      · rename_i hEq; rw [beq_iff_eq] at hEq; dsimp only; omega
      · dsimp only; simp only [ByteArray.size_extract]; omega
    · split
      · rename_i hEq; rw [beq_iff_eq] at hEq; dsimp only; simp only [ByteArray.size_append]; omega
      · dsimp only; simp only [ByteArray.size_append, ByteArray.size_extract]; omega

/-- `RingBuf.consume` maintains `len ≤ rb.cap` for every well-formed buffer (`rb.len ≤ rb.cap`). -/
theorem ringBuf_consume_len_le_cap (rb : RingBuf) (n : Nat) (h : rb.len ≤ rb.cap) :
    (rb.consume n).len ≤ rb.cap := by
  unfold RingBuf.consume RingBuf.len Internal.ringBufConsume Internal.ringBufLen at *
  simp only [nat_min_eq_min] at *
  split
  · simp
  · dsimp only; omega

/-- `RingBuf.frontSlice` exposes the exact logical FIFO byte stream `rb.toList`. -/
theorem ringBuf_frontSlice_toList (rb : RingBuf) :
    rb.frontSlice.data.toList = rb.toList := by
  unfold RingBuf.frontSlice RingBuf.toList Internal.ringBufFrontSlice Internal.ringBufToList Internal.ringBufLen
  simp only [nat_min_eq_min]
  split
  · rename_i hZero
    have hEq0 : min (rb.buf.size - rb.off) rb.cap = 0 := beq_iff_eq.mp hZero
    have hDropLen : (rb.buf.data.toList.drop rb.off).length = rb.buf.size - rb.off := by simp
    rcases Nat.min_eq_zero_iff.mp hEq0 with hLen0 | hCap0
    · have hNil : rb.buf.data.toList.drop rb.off = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      rw [hNil, List.take_nil]
      rfl
    · rw [hCap0, List.take_zero]
      rfl
  · split
    · rename_i hFast
      simp only [Bool.and_eq_true, beq_iff_eq] at hFast
      rcases hFast with ⟨hOff0, hSzEq⟩
      rw [hOff0, List.drop_zero]
      have hLe : rb.buf.data.toList.length ≤ rb.cap := by
        have : rb.buf.size ≤ rb.cap := by omega
        simpa using this
      exact (List.take_of_length_le hLe).symm
    · rw [byteArray_extract_toList]
      have hSub : rb.off + min (rb.buf.size - rb.off) rb.cap - rb.off =
          min (rb.buf.size - rb.off) rb.cap := by omega
      rw [hSub]
      have hDropLen : (rb.buf.data.toList.drop rb.off).length = rb.buf.size - rb.off := by simp
      by_cases hLe : rb.buf.size - rb.off ≤ rb.cap
      · rw [Nat.min_eq_left hLe]
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      · rw [Nat.min_eq_right (by omega)]

/-- `RingBuf.push` preserves exact FIFO byte order across arbitrary short `recvfrom` chunks (`(rb.push chunk).toList = rb.toList ++ chunk.take avail`). -/
theorem ringBuf_push_toList (rb : RingBuf) (chunk : ByteArray) :
    (rb.push chunk).toList =
      rb.toList ++ chunk.data.toList.take (rb.cap - rb.toList.length) := by
  have hFront := ringBuf_frontSlice_toList rb
  have hFrontSz : rb.frontSlice.size = rb.toList.length := by
    simpa using congrArg List.length hFront
  have hCap : rb.frontSlice.size ≤ rb.cap := ringBuf_frontSlice_size_le_cap rb
  unfold RingBuf.push Internal.ringBufPush
  simp only [nat_min_eq_min]
  by_cases hTake0 : (min chunk.size (rb.cap - rb.frontSlice.size) == 0) = true
  · simp only [show Internal.ringBufFrontSlice rb = rb.frontSlice from rfl, hTake0, ↓reduceIte]
    change (rb.frontSlice.data.toList.drop 0).take rb.cap = _
    rw [List.drop_zero]
    have hEq0 : min chunk.size (rb.cap - rb.frontSlice.size) = 0 := beq_iff_eq.mp hTake0
    have hTakeNil : chunk.data.toList.take (rb.cap - rb.toList.length) = [] := by
      rw [← hFrontSz]
      rcases Nat.min_eq_zero_iff.mp hEq0 with hc0 | ha0
      · have hNil : chunk.data.toList = [] :=
          List.eq_nil_of_length_eq_zero (by simpa using hc0)
        simp [hNil]
      · simp [ha0]
    rw [hTakeNil, List.append_nil, hFront]
    exact List.take_of_length_le (by omega)
  · have hTakeF : (min chunk.size (rb.cap - rb.frontSlice.size) == 0) = false :=
      Bool.eq_false_iff.mpr hTake0
    simp only [show Internal.ringBufFrontSlice rb = rb.frontSlice from rfl, hTakeF, Bool.false_eq_true, ↓reduceIte]
    let takeN := min chunk.size (rb.cap - rb.frontSlice.size)
    let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
    have hPartList : part.data.toList = chunk.data.toList.take (rb.cap - rb.toList.length) := by
      dsimp only [part, takeN]
      rw [← hFrontSz]
      by_cases hAll : (min chunk.size (rb.cap - rb.frontSlice.size) == chunk.size) = true
      · simp only [hAll, ↓reduceIte]
        have hLe : chunk.size ≤ rb.cap - rb.frontSlice.size := by
          have := beq_iff_eq.mp hAll; omega
        exact (List.take_of_length_le (by simpa using hLe)).symm
      · have hAllF : (min chunk.size (rb.cap - rb.frontSlice.size) == chunk.size) = false :=
          Bool.eq_false_iff.mpr hAll
        simp only [hAllF, Bool.false_eq_true, ↓reduceIte, byteArray_extract_toList, List.drop_zero, Nat.sub_zero]
        have hLt : rb.cap - rb.frontSlice.size < chunk.size := by
          have hNe : min chunk.size (rb.cap - rb.frontSlice.size) ≠ chunk.size :=
            fun h => hAll (beq_iff_eq.mpr h)
          omega
        rw [Nat.min_eq_right (Nat.le_of_lt hLt)]
    have hPartLen : part.data.toList.length ≤ rb.cap - rb.frontSlice.size := by
      rw [hPartList, List.length_take, hFrontSz]; omega
    by_cases hAct0 : (rb.frontSlice.size == 0) = true
    · simp only [hAct0, ↓reduceIte]
      change (part.data.toList.drop 0).take rb.cap = _
      rw [List.drop_zero]
      have hNil : rb.toList = [] :=
        List.eq_nil_of_length_eq_zero (by have := beq_iff_eq.mp hAct0; omega)
      rw [hNil, List.nil_append]
      rw [List.take_of_length_le (by omega)]
      simpa [hNil] using hPartList
    · have hActF : (rb.frontSlice.size == 0) = false := Bool.eq_false_iff.mpr hAct0
      simp only [hActF, Bool.false_eq_true, ↓reduceIte]
      change ((rb.frontSlice ++ part).data.toList.drop 0).take rb.cap = _
      rw [List.drop_zero]
      have hAppList : (rb.frontSlice ++ part).data.toList = rb.frontSlice.data.toList ++ part.data.toList := by
        simp [ByteArray.data_append]
      rw [hAppList, List.take_of_length_le (by rw [List.length_append, hFront]; omega), hFront, hPartList]

/-- `RingBuf.consume` drops the exact `n` sent bytes from the front of `rb.toList` across arbitrary short `sendto` completions. -/
theorem ringBuf_consume_toList (rb : RingBuf) (n : Nat) (hCap : rb.len ≤ rb.cap) :
    (rb.consume n).toList = rb.toList.drop n := by
  have hDropLen : (rb.buf.data.toList.drop rb.off).length = rb.len := by
    unfold RingBuf.len Internal.ringBufLen; simp
  have hToListEq : rb.toList = rb.buf.data.toList.drop rb.off := by
    unfold RingBuf.toList Internal.ringBufToList
    exact List.take_of_length_le (by omega)
  unfold RingBuf.consume Internal.ringBufConsume Internal.ringBufLen
  dsimp only
  split
  · rename_i hGe
    simp only [nat_min_eq_min] at hGe
    have hLenEq : rb.buf.size - rb.off = rb.len := rfl
    rw [hToListEq]
    have hNil : (rb.buf.data.toList.drop rb.off).drop n = [] := by
      apply List.drop_eq_nil_of_le
      omega
    rw [hNil]
    unfold RingBuf.toList Internal.ringBufToList
    simp
  · rename_i hLt
    simp only [nat_min_eq_min] at hLt
    rw [hToListEq]
    unfold RingBuf.toList Internal.ringBufToList
    dsimp only
    rw [← List.drop_drop]
    apply List.take_of_length_le
    rw [List.length_drop, hDropLen]
    change rb.len - n ≤ rb.cap
    omega

/-- Logical list length equals `rb.len` whenever `rb.len ≤ rb.cap`. -/
theorem ringBuf_toList_length_of_le_cap (rb : RingBuf) (hCap : rb.len ≤ rb.cap) :
    rb.toList.length = rb.len := by
  have hDropLen : (rb.buf.data.toList.drop rb.off).length = rb.len := by
    unfold RingBuf.len Internal.ringBufLen; simp
  unfold RingBuf.toList Internal.ringBufToList
  rw [List.length_take, hDropLen, Nat.min_eq_right hCap]

/-- Logical list length equals `min rb.len rb.cap` for every `rb : RingBuf`. -/
theorem ringBuf_toList_length (rb : RingBuf) :
    rb.toList.length = min rb.len rb.cap := by
  unfold RingBuf.toList Internal.ringBufToList RingBuf.len Internal.ringBufLen
  rw [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
  exact Nat.min_comm _ _

/-- Any `RingBuf` with a non-empty logical FIFO stream reports `isEmpty = false`. -/
theorem ringBuf_not_empty_of_nonempty_toList (rb : RingBuf) (h : rb.toList ≠ []) :
    rb.isEmpty = false := by
  unfold RingBuf.isEmpty Internal.ringBufIsEmpty
  apply Bool.eq_false_iff.mpr
  intro hEq
  have hLen0 : rb.buf.size - rb.off = 0 := beq_iff_eq.mp hEq
  unfold RingBuf.toList Internal.ringBufToList at h
  have hDropNil : rb.buf.data.toList.drop rb.off = [] := by
    apply List.eq_nil_of_length_eq_zero
    have : (rb.buf.data.toList.drop rb.off).length = rb.buf.size - rb.off := by simp
    omega
  rw [hDropNil, List.take_nil] at h
  exact h rfl

private theorem ringBuf_frontSlice_eq_model (rb : RingBuf) :
    rb.frontSlice = Model.ringBufFrontSlice rb := by
  have h := ringBuf_frontSlice_toList rb
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa [Model.ringBufFrontSlice, Model.ringBufToList, RingBuf.toList, Internal.ringBufToList] using h

private theorem ringBuf_toList_take_cap (rb : RingBuf) :
    (ringBufToList rb).take rb.cap = ringBufToList rb := by
  apply List.take_of_length_le
  exact List.length_take_le rb.cap _

private theorem ringBuf_push_refines_allowed (rb : RingBuf) (chunk : ByteArray) :
    Model.allowedRingBufPush rb chunk (rb.push chunk) := by
  refine ⟨ringBuf_push_cap rb chunk, ringBuf_push_len_le_cap rb chunk, ?_⟩
  unfold Model.fifoPush
  rw [ringBuf_toList_take_cap rb]
  simpa [RingBuf.toList, Internal.ringBufToList, Model.ringBufToList] using
    ringBuf_push_toList rb chunk

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

private theorem flushBytesNonblock_refines {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.RefinesStep proj relayStepWf (execRawStep raw) allowedRawStep)
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

private theorem recvIntoRing_refines {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.RefinesStep proj relayStepWf (execRawStep raw) allowedRawStep)
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

private theorem flushRingNonblock_refines {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.RefinesStep proj relayStepWf (execRawStep raw) allowedRawStep)
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

private theorem shutdownWrClean_refines {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.RefinesStep proj relayStepWf (execRawStep raw) allowedRawStep)
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

private theorem drainDeadPeerRx_refines {W : Type}
    (proj : W → RelayTraceState) (raw : RelayRawOps (StateM W))
    (hRaw : Core.RefinesStep proj relayStepWf (execRawStep raw) allowedRawStep)
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

private theorem refinesStepFrom_mkRelayApiM :
    Core.RefinesStepFrom id Model.relayStepWf
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
    have hSub := flushBytesNonblock_refines proj raw hRaw fd bytes fuel off w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | recvIntoRing fd fuel rb =>
    rcases hCall : (Internal.recvIntoRing raw.net fd fuel rb).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.recvIntoRing fd fuel rb)).run w = (.optRecv res, w1) :=
      stateM_map_eq RelayPkgOut.optRecv _ w hCall
    have hSub := recvIntoRing_refines proj raw hRaw fd fuel rb w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | flushRingNonblock fd fuel rb =>
    rcases hCall : (Internal.flushRingNonblock raw.net fd fuel rb).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.flushRingNonblock fd fuel rb)).run w = (.optBuf res, w1) :=
      stateM_map_eq RelayPkgOut.optBuf _ w hCall
    have hSub := flushRingNonblock_refines proj raw hRaw fd fuel rb w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | shutdownWrClean fd fuel =>
    rcases hCall : (Internal.shutdownWrClean raw.net fd fuel).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.shutdownWrClean fd fuel)).run w = (.flag res, w1) :=
      stateM_map_eq RelayPkgOut.flag _ w hCall
    have hSub := shutdownWrClean_refines proj raw hRaw fd fuel w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub
  | drainDeadPeerRx fd fuel =>
    rcases hCall : (Internal.drainDeadPeerRx raw.net fd fuel).run w with ⟨res, w1⟩
    have hMap : (execPkgStep (Internal.mkRelayApiM raw)
        (.drainDeadPeerRx fd fuel)).run w = (.flag res, w1) :=
      stateM_map_eq RelayPkgOut.flag _ w hCall
    have hSub := drainDeadPeerRx_refines proj raw hRaw fd fuel w hWf
    dsimp only at hSub ⊢
    rw [hCall] at hSub
    rw [hMap]
    exact hSub

/-- Full public `Interface` refinement of `LeanSwe.NetRelay` against `LeanSwe.NetRelay.Model`. -/
theorem refines_model :
    Core.RefinesPureEq LeanSwe.NetRelay.RingBuf.len Model.ringBufLen ∧
    Core.RefinesPureEq LeanSwe.NetRelay.RingBuf.isEmpty Model.ringBufIsEmpty ∧
    Core.RefinesPureEq LeanSwe.NetRelay.RingBuf.writeAvail Model.ringBufWriteAvail ∧
    Core.RefinesPureEq LeanSwe.NetRelay.RingBuf.toList Model.ringBufToList ∧
    Core.RefinesPureEq LeanSwe.NetRelay.RingBuf.frontSlice Model.ringBufFrontSlice ∧
    Core.RefinesPure2 LeanSwe.NetRelay.RingBuf.push Model.allowedRingBufPush ∧
    Core.RefinesPureEq2 LeanSwe.NetRelay.RingBuf.consume Model.ringBufConsumeModel ∧
    Core.RefinesStepFrom id Model.relayStepWf
      Model.execRawStep Model.allowedRawStep
      Model.relayStepWf Internal.mkRelayApiM
      Model.execPkgStep Model.allowedPkgStep :=
  ⟨fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   ringBuf_frontSlice_eq_model,
   ringBuf_push_refines_allowed,
   fun _ _ => rfl,
   refinesStepFrom_mkRelayApiM⟩

/-- `defaultRingBufApi` satisfies `test_netRelay_ringBuf_pushAndViewLaws`. -/
theorem test_netRelay_ringBuf_pushAndViewLaws_allPass :
    Core.AllPass (test_netRelay_ringBuf_pushAndViewLaws Internal.defaultRingBufApi) := by
  intro rb chunk
  have hPush := ringBuf_push_refines_allowed rb chunk
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

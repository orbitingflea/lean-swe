import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.NetRelay.Impl
import LeanSwe.NetRelay.Interface

namespace LeanSwe.NetRelay.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Model

private theorem nat_min_eq_min (a b : Nat) : Nat.min a b = min a b := rfl

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

/-- `RingBuf.frontSlice` equals `Model.ringBufFrontSlice`. -/
theorem ringBuf_frontSlice_eq_model (rb : RingBuf) :
    rb.frontSlice = Model.ringBufFrontSlice rb := by
  have h := ringBuf_frontSlice_toList rb
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa [Model.ringBufFrontSlice, Model.ringBufToList, RingBuf.toList, Internal.ringBufToList] using h

private theorem ringBuf_toList_take_cap (rb : RingBuf) :
    (ringBufToList rb).take rb.cap = ringBufToList rb := by
  apply List.take_of_length_le
  exact List.length_take_le rb.cap _

/-- `RingBuf.push` obeys `Model.allowedRingBufPush`. -/
theorem ringBuf_push_obeys_allowed (rb : RingBuf) (chunk : ByteArray) :
    Model.allowedRingBufPush rb chunk (rb.push chunk) := by
  refine ⟨ringBuf_push_cap rb chunk, ringBuf_push_len_le_cap rb chunk, ?_⟩
  unfold Model.fifoPush
  rw [ringBuf_toList_take_cap rb]
  simpa [RingBuf.toList, Internal.ringBufToList, Model.ringBufToList] using
    ringBuf_push_toList rb chunk

end LeanSwe.NetRelay.Proofs

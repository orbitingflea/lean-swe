import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model

/-!
Byte-length and framing bounds for `Model.encodeStored` across `.gzip`, `.zstd`, and `.xz`.
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Compress

private theorem byteArray_get!_push_lt {a : ByteArray} {x : UInt8} {i : Nat} (hi : i < a.size) :
    (a.push x).get! i = a.get! i := by
  have h1 : i < a.data.size := hi
  have h2 : i < (a.data.push x).size := by simp [Array.size_push]; exact Nat.lt_succ_of_lt h1
  change (a.data.push x)[i]! = a.data[i]!
  rw [getElem!_pos (a.data.push x) i h2, getElem!_pos a.data i h1, Array.getElem_push_lt h1]

private theorem byteArray_get!_append_lt {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have h1 : i < a.data.size := hi
  have h2 : i < (a ++ b).data.size := by
    simp [ByteArray.data_append, Array.size_append]
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  have hEq1 : (a ++ b).get! i = (a ++ b).data[i]! := rfl
  have hEq2 : a.get! i = a.data[i]! := rfl
  rw [hEq1, hEq2, getElem!_pos (a ++ b).data i h2, getElem!_pos a.data i h1]
  simp [ByteArray.data_append, Array.getElem_append_left h1]

private theorem pushU16LE_size (a : ByteArray) (v : UInt16) : (pushU16LE a v).size = a.size + 2 := by
  simp [pushU16LE, ByteArray.size_push]

private theorem pushU32LE_size (a : ByteArray) (v : UInt32) : (pushU32LE a v).size = a.size + 4 := by
  simp [pushU32LE, ByteArray.size_push]

private theorem pushU64LE_size (a : ByteArray) (v : UInt64) : (pushU64LE a v).size = a.size + 8 := by
  simp [pushU64LE, pushU32LE_size]

private theorem pushReplicateByte_size (dst : ByteArray) (b : UInt8) (count : Nat) :
    (pushReplicateByte dst b count).size = dst.size + count := by
  unfold pushReplicateByte
  suffices h : ∀ (fuel : Nat) (acc : ByteArray), (pushReplicateByte.go b fuel acc).size = acc.size + fuel by
    exact h count dst
  intro fuel
  induction fuel with
  | zero => intro acc; rfl
  | succ f ih => intro acc; simp [pushReplicateByte.go, ih, ByteArray.size_push]; omega

private theorem pushBytesRange_size_le (dst src : ByteArray) (start stop : Nat) :
    (pushBytesRange dst src start stop).size ≤ dst.size + (stop - start) := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray),
      (pushBytesRange.go src (min stop src.size) fuel idx acc).size ≤ acc.size + fuel by
    have h1 := h (min stop src.size - start) start dst
    omega
  intro fuel
  induction fuel with
  | zero => intro _ _; exact Nat.le_refl _
  | succ _ ih =>
    intro idx acc
    unfold pushBytesRange.go
    split
    · omega
    · have h2 := ih (idx + 1) (acc.push (src.get! idx))
      simp only [ByteArray.size_push] at h2
      omega

private theorem pushBytesRange_size_ge (dst src : ByteArray) (start stop : Nat) :
    dst.size ≤ (pushBytesRange dst src start stop).size := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray),
      acc.size ≤ (pushBytesRange.go src (min stop src.size) fuel idx acc).size by
    exact h (min stop src.size - start) start dst
  intro fuel
  induction fuel with
  | zero => intro _ _; exact Nat.le_refl _
  | succ _ ih =>
    intro idx acc
    unfold pushBytesRange.go
    split
    · exact Nat.le_refl _
    · have h2 := ih (idx + 1) (acc.push (src.get! idx))
      simp only [ByteArray.size_push] at h2
      omega

private theorem pushU16LE_get!_lt {a : ByteArray} {v : UInt16} {i : Nat} (hi : i < a.size) :
    (pushU16LE a v).get! i = a.get! i := by
  unfold pushU16LE
  rw [byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega), byteArray_get!_push_lt hi]

private theorem pushU32LE_get!_lt {a : ByteArray} {v : UInt32} {i : Nat} (hi : i < a.size) :
    (pushU32LE a v).get! i = a.get! i := by
  unfold pushU32LE
  rw [byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt hi]

private theorem pushU64LE_get!_lt {a : ByteArray} {v : UInt64} {i : Nat} (hi : i < a.size) :
    (pushU64LE a v).get! i = a.get! i := by
  unfold pushU64LE
  rw [pushU32LE_get!_lt (by rw [pushU32LE_size]; omega), pushU32LE_get!_lt hi]

private theorem pushBytesRange_get!_lt (dst src : ByteArray) (start stop i : Nat) (hi : i < dst.size) :
    (pushBytesRange dst src start stop).get! i = dst.get! i := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray), i < acc.size →
      (pushBytesRange.go src (min stop src.size) fuel idx acc).get! i = acc.get! i from
    h (min stop src.size - start) start dst hi
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ _ ih =>
    intro idx acc hacc
    unfold pushBytesRange.go
    split
    · rfl
    · rw [ih (idx + 1) (acc.push (src.get! idx)) (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]

private theorem encodeXzVli_size_le (n : Nat) : (Model.encodeXzVli n).size ≤ 9 := by
  unfold Model.encodeXzVli
  suffices h : ∀ (fuel v : Nat) (acc : ByteArray), (Model.encodeXzVli.go fuel v acc).size ≤ acc.size + fuel by
    have h1 := h 9 n ByteArray.empty
    simpa using h1
  intro fuel
  induction fuel with
  | zero => intro _ _; exact Nat.le_refl _
  | succ _ ih =>
    intro v acc
    unfold Model.encodeXzVli.go
    dsimp only
    split
    · simp [ByteArray.size_push]
    · exact Nat.le_trans (ih _ _) (by simp only [ByteArray.size_push]; omega)

private theorem encodeGzipStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (acc : ByteArray),
      pos ≤ input.size →
      acc.size ≤ (Model.encodeGzipStored.chunkLoop input fuel pos acc).size ∧
      (Model.encodeGzipStored.chunkLoop input fuel pos acc).size ≤
        acc.size + (input.size - pos) + fuel * 5
  | 0, _, acc, _ => by simp [Model.encodeGzipStored.chunkLoop]
  | fuel + 1, pos, acc, _ => by
    unfold Model.encodeGzipStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 65535 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · exact ⟨Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
          (pushBytesRange_size_ge _ _ _ _),
        Nat.le_trans (pushBytesRange_size_le _ _ _ _)
          (by simp only [pushU16LE_size, ByteArray.size_push]; omega)⟩
    · refine ⟨Nat.le_trans (Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
            (pushBytesRange_size_ge _ _ _ _))
          (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).1,
        Nat.le_trans
          (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).2
          (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _)
            (by simp only [pushU16LE_size, ByteArray.size_push]; omega))⟩

private theorem encodeGzipStored_chunkLoop_size_succ (input : ByteArray)
    (fuel pos : Nat) (acc : ByteArray) (_hpos : pos ≤ input.size) :
    acc.size + 5 ≤ (Model.encodeGzipStored.chunkLoop input (fuel + 1) pos acc).size := by
  unfold Model.encodeGzipStored.chunkLoop
  dsimp only
  have hT : min (input.size - pos) 65535 ≤ input.size - pos := Nat.min_le_left _ _
  split
  · exact Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
      (pushBytesRange_size_ge _ _ _ _)
  · exact Nat.le_trans (Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
        (pushBytesRange_size_ge _ _ _ _))
      (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).1

private theorem encodeGzipStored_chunkLoop_get!_lt (input : ByteArray) (i : Nat) :
    ∀ (fuel pos : Nat) (acc : ByteArray), i < acc.size →
      (Model.encodeGzipStored.chunkLoop input fuel pos acc).get! i = acc.get! i
  | 0, _, _, _ => rfl
  | fuel + 1, pos, acc, hacc => by
    unfold Model.encodeGzipStored.chunkLoop
    dsimp only
    have hAcc2 (b : UInt8) (u1 u2 : UInt16) :
        i < (pushBytesRange (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)).size := by
      have h1 := pushBytesRange_size_ge (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)
      simp only [pushU16LE_size, ByteArray.size_push] at h1
      omega
    have hStep (b : UInt8) (u1 u2 : UInt16) :
        (pushBytesRange (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)).get! i = acc.get! i := by
      rw [pushBytesRange_get!_lt _ _ _ _ i (by simp [pushU16LE_size, ByteArray.size_push]; omega),
        pushU16LE_get!_lt (by simp [pushU16LE_size, ByteArray.size_push]; omega),
        pushU16LE_get!_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]
    split
    · exact hStep _ _ _
    · rw [encodeGzipStored_chunkLoop_get!_lt input i fuel (pos + min (input.size - pos) 65535) _ (hAcc2 _ _ _)]
      exact hStep _ _ _

private theorem encodeZstdStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (acc : ByteArray),
      pos ≤ input.size →
      acc.size ≤ (Model.encodeZstdStored.chunkLoop input fuel pos acc).size ∧
      (Model.encodeZstdStored.chunkLoop input fuel pos acc).size ≤
        acc.size + (input.size - pos) + fuel * 3
  | 0, _, acc, _ => by simp [Model.encodeZstdStored.chunkLoop]
  | fuel + 1, pos, acc, _ => by
    unfold Model.encodeZstdStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 131072 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · exact ⟨Nat.le_trans (by simp only [ByteArray.size_push]; omega)
          (pushBytesRange_size_ge _ _ _ _),
        Nat.le_trans (pushBytesRange_size_le _ _ _ _)
          (by simp only [ByteArray.size_push]; omega)⟩
    · refine ⟨Nat.le_trans (Nat.le_trans (by simp only [ByteArray.size_push]; omega)
            (pushBytesRange_size_ge _ _ _ _))
          (encodeZstdStored_chunkLoop_size input fuel (pos + min (input.size - pos) 131072) _ (by omega)).1,
        Nat.le_trans
          (encodeZstdStored_chunkLoop_size input fuel (pos + min (input.size - pos) 131072) _ (by omega)).2
          (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _)
            (by simp only [ByteArray.size_push]; omega))⟩

private theorem encodeZstdStored_chunkLoop_get!_lt (input : ByteArray) (i : Nat) :
    ∀ (fuel pos : Nat) (acc : ByteArray), i < acc.size →
      (Model.encodeZstdStored.chunkLoop input fuel pos acc).get! i = acc.get! i
  | 0, _, _, _ => rfl
  | fuel + 1, pos, acc, hacc => by
    unfold Model.encodeZstdStored.chunkLoop
    dsimp only
    have hAcc2 (b0 b1 b2 : UInt8) :
        i < (pushBytesRange (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)).size := by
      have h1 := pushBytesRange_size_ge (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)
      simp only [ByteArray.size_push] at h1
      omega
    have hStep (b0 b1 b2 : UInt8) :
        (pushBytesRange (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)).get! i = acc.get! i := by
      rw [pushBytesRange_get!_lt _ _ _ _ i (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]
    split
    · exact hStep _ _ _
    · rw [encodeZstdStored_chunkLoop_get!_lt input i fuel (pos + min (input.size - pos) 131072) _ (hAcc2 _ _ _)]
      exact hStep _ _ _

private theorem encodeXzStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (first : Bool) (acc : ByteArray),
      pos ≤ input.size →
      (Model.encodeXzStored.chunkLoop input fuel pos first acc).size ≤
        acc.size + (input.size - pos) + fuel * 3 + 1
  | 0, _, _, acc, _ => by simp [Model.encodeXzStored.chunkLoop]; omega
  | fuel + 1, pos, first, acc, _ => by
    unfold Model.encodeXzStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 65536 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · simp only [ByteArray.size_push]
      exact Nat.le_trans (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) 1)
        (by simp only [ByteArray.size_push]; omega)
    · exact Nat.le_trans
        (encodeXzStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65536) false _ (by omega))
        (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _) 1)
          (by simp only [ByteArray.size_push]; omega))

/-- `Model.encodeStored codec input` never exceeds `Model.maxCompressedBound codec input.size`. -/
theorem encodeStored_size_le_maxCompressedBound (codec : Codec) (input : ByteArray) :
    (Model.encodeStored codec input).size ≤ Model.maxCompressedBound codec input.size := by
  unfold Model.encodeStored Model.maxCompressedBound
  cases codec with
  | gzip =>
    unfold Model.encodeGzipStored
    dsimp only
    have h10 : (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]).size = 10 := rfl
    have h5 : (ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]).size = 5 := rfl
    have hBodyLe :
        (if input.isEmpty then (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]) ++ ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]
         else Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0
           (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03])).size ≤
        10 + input.size + (input.size / 65535 + 2) * 5 := by
      split
      · simp only [ByteArray.size_append]; rw [h10, h5]; omega
      · have h := (encodeGzipStored_chunkLoop_size input (input.size / 65535 + 2) 0
          (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]) (Nat.zero_le _)).2
        rw [h10] at h; exact h
    simp only [pushU32LE_size]
    omega
  | zstd =>
    unfold Model.encodeZstdStored
    dsimp only
    have h4 : (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).size = 4 := rfl
    have h3 : (ByteArray.mk #[0x01, 0x00, 0x00]).size = 3 := rfl
    let hdr :=
      if input.size >= 4294967296 then
        pushU64LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push (if input.size >= 4294967296 then 0xC4 else 0x84) |>.push 0x38) (UInt64.ofNat input.size)
      else
        pushU32LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push (if input.size >= 4294967296 then 0xC4 else 0x84) |>.push 0x38) (UInt32.ofNat input.size)
    have hHdrSize : hdr.size ≤ 14 := by
      dsimp only [hdr]
      split <;> simp only [pushU64LE_size, pushU32LE_size, ByteArray.size_push, h4] <;> omega
    have hBodyLe :
        (if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
         else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr).size ≤
        14 + input.size + (input.size / 131072 + 2) * 3 := by
      split
      · simp only [ByteArray.size_append, h3]; omega
      · have h := (encodeZstdStored_chunkLoop_size input (input.size / 131072 + 2) 0 hdr (Nat.zero_le _)).2
        omega
    simp only [pushU32LE_size]
    change (if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
            else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr).size + 4 ≤ _
    omega
  | xz =>
    unfold Model.encodeXzStored
    dsimp only
    have h8s : (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]).size = 8 := rfl
    have h8b : (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]).size = 8 := rfl
    have hEmptySz : ByteArray.empty.size = 0 := rfl
    have h2 : (ByteArray.mk #[0x00, 0x04]).size = 2 := rfl
    have h2yz : (ByteArray.mk #[0x59, 0x5A]).size = 2 := rfl
    simp only [ByteArray.size_append, pushU32LE_size, pushReplicateByte_size]
    rw [h8s, h8b, hEmptySz, h2, h2yz]
    let blkPair :=
      if input.isEmpty = true then (ByteArray.empty, (#[] : Array (Nat × Nat)))
      else
        (pushU32LE (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00])
            (crc32 (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]) 0 8) ++
          pushReplicateByte (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty) 0x00
            ((4 - (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size % 4) % 4) ++
          pushU64LE ByteArray.empty (crc64Xz input 0 input.size),
          #[(8 + 4 + (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size + 8, input.size)])
    have hIfBlk : blkPair.1.size ≤ 24 + input.size + (input.size / 65536 + 2) * 3 := by
      dsimp only [blkPair]
      split
      · simp only [hEmptySz]; omega
      · dsimp only
        have hL2 := encodeXzStored_chunkLoop_size input (input.size / 65536 + 2) 0 true ByteArray.empty (Nat.zero_le _)
        have hPad := pushReplicateByte_size (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty) 0x00
          ((4 - (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size % 4) % 4)
        simp only [ByteArray.size_append, pushU32LE_size, pushU64LE_size]
        rw [hEmptySz, h8b, hPad]
        rw [hEmptySz] at hL2
        omega
    have hBuildIdx : ∀ (recs : Array (Nat × Nat)) (fuel i : Nat) (buf : ByteArray),
        (Model.encodeXzStored.buildIdx recs fuel i buf).size ≤ buf.size + fuel * 18 := by
      intro recs fuel
      induction fuel with
      | zero => intro _ _; simp only [Model.encodeXzStored.buildIdx]; omega
      | succ _ ih =>
        intro i buf
        unfold Model.encodeXzStored.buildIdx
        dsimp only
        split
        · omega
        · have h1 := ih (i + 1) (buf ++ Model.encodeXzVli recs[i]!.1 ++ Model.encodeXzVli recs[i]!.2)
          simp only [ByteArray.size_append] at h1
          have hv1 := encodeXzVli_size_le recs[i]!.1
          have hv2 := encodeXzVli_size_le recs[i]!.2
          omega
    have hRecsLen : blkPair.2.size ≤ 1 := by
      dsimp only [blkPair]; split <;> simp
    have hBuf1 : ∀ (recs : Array (Nat × Nat)), recs.size ≤ 1 →
        (Model.encodeXzStored.buildIdx recs recs.size 0
          ((ByteArray.empty.push 0x00) ++ Model.encodeXzVli recs.size)).size ≤ 28 := by
      intro recs _
      have hB := hBuildIdx recs recs.size 0 ((ByteArray.empty.push 0x00) ++ Model.encodeXzVli recs.size)
      have hV := encodeXzVli_size_le recs.size
      simp only [ByteArray.size_append, ByteArray.size_push] at hB
      rw [hEmptySz] at hB
      omega
    have hBuf1App := hBuf1 blkPair.2 hRecsLen
    have hDiv : input.size / 65536 ≤ input.size / 1024 := Nat.div_le_div_left (by decide) (by decide)
    change 8 + 4 + blkPair.1.size +
      ((Model.encodeXzStored.buildIdx blkPair.2 blkPair.2.size 0
          (ByteArray.empty.push 0x00 ++ Model.encodeXzVli blkPair.2.size)).size +
        (4 - (Model.encodeXzStored.buildIdx blkPair.2 blkPair.2.size 0
          (ByteArray.empty.push 0x00 ++ Model.encodeXzVli blkPair.2.size)).size % 4) % 4 + 4) +
      (4 + (0 + 4 + 2) + 2) ≤ input.size + (input.size / 1024 + 1) * 64 + 256
    omega

private theorem byteArray_push_eq_append (a : ByteArray) (b : UInt8) :
    a.push b = a ++ ByteArray.mk #[b] := by
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_append]
  exact Array.push_eq_append

private theorem xz_shdr_split (c : UInt32) :
    ∃ tail : ByteArray,
      pushU32LE (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]) c =
        ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ tail := by
  dsimp only [pushU32LE]
  simp only [byteArray_push_eq_append]
  have hBodyEq : ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04] =
      ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ ByteArray.mk #[0x00, 0x04] := rfl
  rw [hBodyEq]
  simp only [ByteArray.append_assoc]
  exact ⟨_, rfl⟩

private theorem hasCanonicalCompressedFraming_xz_parts (shdr tail blocks idx ftrBody : ByteArray) (c : UInt32)
    (hSh : shdr = ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ tail)
    (_hShSz : shdr.size ≥ 12) (_hIdx : idx.size ≥ 8) (hFtrSz : ftrBody.size = 6) :
    Model.hasCanonicalCompressedFraming .xz
      (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])) = true := by
  unfold Model.hasCanonicalCompressedFraming
  have hEmpty : ByteArray.empty.size = 0 := rfl
  have h2 : (ByteArray.mk #[0x59, 0x5A]).size = 2 := rfl
  have hSfx : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size =
      ((shdr ++ blocks ++ idx) ++ (pushU32LE ByteArray.empty c ++ ftrBody)).size + 2 := by
    simp only [ByteArray.size_append, h2]
    omega
  have hTotSz : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size ≥ 32 := by
    simp only [ByteArray.size_append, pushU32LE_size, hEmpty, hFtrSz, h2]
    omega
  have hPfx : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).extract 0 6 =
      ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] := by
    rw [hSh]
    simp only [ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left rfl
  have hSfxEq : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).extract
      ((shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size - 2)
      (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size =
      ByteArray.mk #[0x59, 0x5A] := by
    rw [hSfx, Nat.add_sub_cancel, ← ByteArray.append_assoc (a := shdr ++ blocks ++ idx)]
    exact ByteArray.extract_append_eq_right rfl (by simp only [ByteArray.size_append, h2])
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hTotSz, hPfx⟩, hSfxEq⟩

/-- `Model.encodeStored codec input` always satisfies `Model.hasCanonicalCompressedFraming codec`. -/
theorem hasCanonicalCompressedFraming_encodeStored (codec : Codec) (input : ByteArray) :
    Model.hasCanonicalCompressedFraming codec (Model.encodeStored codec input) = true := by
  unfold Model.hasCanonicalCompressedFraming Model.encodeStored
  cases codec with
  | gzip =>
    unfold Model.encodeGzipStored
    dsimp only
    let hdr := ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]
    let body :=
      if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]
      else Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0 hdr
    let enc := pushU32LE (pushU32LE body (crc32 input 0 input.size)) (UInt32.ofNat (input.size % 4294967296))
    have hHdrSize : hdr.size = 10 := rfl
    have h5 : (ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]).size = 5 := rfl
    have hBodyGe : 10 ≤ body.size := by
      simp only [body]; split
      · simp only [ByteArray.size_append]; rw [hHdrSize]; omega
      · have h := (encodeGzipStored_chunkLoop_size input (input.size / 65535 + 2) 0 hdr (Nat.zero_le _)).1
        rw [hHdrSize] at h; exact h
    have hSz : 20 ≤ enc.size := by
      dsimp only [enc]; simp only [pushU32LE_size]
      simp only [body]; split
      · simp only [ByteArray.size_append]; rw [hHdrSize, h5]; omega
      · have h : hdr.size + 5 ≤ (Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0 hdr).size :=
          encodeGzipStored_chunkLoop_size_succ input (input.size / 65535 + 1) 0 hdr (Nat.zero_le _)
        rw [hHdrSize] at h; omega
    have hGet : ∀ i : Nat, i < 10 → enc.get! i = hdr.get! i := by
      intro i hi
      dsimp only [enc]
      rw [pushU32LE_get!_lt (by rw [pushU32LE_size]; omega),
        pushU32LE_get!_lt (by omega)]
      simp only [body]; split
      · exact byteArray_get!_append_lt (by rw [hHdrSize]; exact hi)
      · exact encodeGzipStored_chunkLoop_get!_lt input i (input.size / 65535 + 2) 0 hdr (by rw [hHdrSize]; exact hi)
    have hb0 : enc.get! 0 = (0x1F : UInt8) := by rw [hGet 0 (by omega)]; rfl
    have hb1 : enc.get! 1 = (0x8B : UInt8) := by rw [hGet 1 (by omega)]; rfl
    have hb2 : enc.get! 2 = (0x08 : UInt8) := by rw [hGet 2 (by omega)]; rfl
    have hb3 : enc.get! 3 = (0x00 : UInt8) := by rw [hGet 3 (by omega)]; rfl
    have hb4 : enc.get! 4 = (0x00 : UInt8) := by rw [hGet 4 (by omega)]; rfl
    have hb5 : enc.get! 5 = (0x00 : UInt8) := by rw [hGet 5 (by omega)]; rfl
    have hb6 : enc.get! 6 = (0x00 : UInt8) := by rw [hGet 6 (by omega)]; rfl
    have hb7 : enc.get! 7 = (0x00 : UInt8) := by rw [hGet 7 (by omega)]; rfl
    change (decide (enc.size ≥ 20) && (enc.get! 0 == 0x1F) && (enc.get! 1 == 0x8B) && (enc.get! 2 == 0x08) &&
      (enc.get! 3 == 0x00) && (enc.get! 4 == 0x00) && (enc.get! 5 == 0x00) && (enc.get! 6 == 0x00) && (enc.get! 7 == 0x00)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hSz, hb0⟩, hb1⟩, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hb7⟩
  | zstd =>
    unfold Model.encodeZstdStored
    dsimp only
    let fhd : UInt8 := if input.size >= 4294967296 then 0xC4 else 0x84
    let hdr :=
      if input.size >= 4294967296 then
        pushU64LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push fhd |>.push 0x38) (UInt64.ofNat input.size)
      else
        pushU32LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push fhd |>.push 0x38) (UInt32.ofNat input.size)
    have hMSize : (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).size = 4 := rfl
    have hHdrSize : 10 ≤ hdr.size := by
      simp only [hdr]; split <;> simp only [pushU64LE_size, pushU32LE_size, ByteArray.size_push, hMSize] <;> omega
    have hHdrGet : ∀ i : Nat, i < 4 → hdr.get! i = (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).get! i := by
      intro i hi
      simp only [hdr]; split
      · rw [pushU64LE_get!_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by rw [hMSize]; exact hi)]
      · rw [pushU32LE_get!_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by rw [hMSize]; exact hi)]
    let body :=
      if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
      else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr
    have hBodyGe : 10 ≤ body.size := by
      simp only [body]; split
      · simp only [ByteArray.size_append]; omega
      · exact Nat.le_trans hHdrSize (encodeZstdStored_chunkLoop_size input (input.size / 131072 + 2) 0 hdr (Nat.zero_le _)).1
    let enc := pushU32LE body (xxh64Low32 input)
    have hSz : 9 ≤ enc.size := by
      dsimp only [enc]; simp only [pushU32LE_size]; omega
    have hGet : ∀ i : Nat, i < 4 → enc.get! i = (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).get! i := by
      intro i hi
      dsimp only [enc]
      rw [pushU32LE_get!_lt (by omega)]
      simp only [body]; split
      · rw [byteArray_get!_append_lt (by omega)]; exact hHdrGet i hi
      · rw [encodeZstdStored_chunkLoop_get!_lt input i (input.size / 131072 + 2) 0 hdr (by omega)]; exact hHdrGet i hi
    have hb0 : enc.get! 0 = (0x28 : UInt8) := by rw [hGet 0 (by omega)]; rfl
    have hb1 : enc.get! 1 = (0xB5 : UInt8) := by rw [hGet 1 (by omega)]; rfl
    have hb2 : enc.get! 2 = (0x2F : UInt8) := by rw [hGet 2 (by omega)]; rfl
    have hb3 : enc.get! 3 = (0xFD : UInt8) := by rw [hGet 3 (by omega)]; rfl
    change (decide (enc.size ≥ 9) && (enc.get! 0 == 0x28) && (enc.get! 1 == 0xB5) && (enc.get! 2 == 0x2F) && (enc.get! 3 == 0xFD)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨hSz, hb0⟩, hb1⟩, hb2⟩, hb3⟩
  | xz =>
    unfold Model.encodeXzStored
    rcases xz_shdr_split (crc32 (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]) 6 8) with ⟨tail, hSh⟩
    refine hasCanonicalCompressedFraming_xz_parts _ tail _ _ _ _ hSh ?_ ?_ ?_
    · simp only [pushU32LE_size]; decide
    · have hBuf1Ge : ∀ (recs : Array (Nat × Nat)) (fuel i : Nat) (buf : ByteArray),
          buf.size ≤ (Model.encodeXzStored.buildIdx recs fuel i buf).size := by
        intro recs fuel
        induction fuel with
        | zero => intro _ _; simp only [Model.encodeXzStored.buildIdx]; exact Nat.le_refl _
        | succ _ ih =>
          intro i buf
          unfold Model.encodeXzStored.buildIdx
          dsimp only
          split
          · exact Nat.le_refl _
          · have := ih (i + 1) (buf ++ Model.encodeXzVli recs[i]!.1 ++ Model.encodeXzVli recs[i]!.2)
            simp only [ByteArray.size_append] at this
            omega
      have hPad8 : ∀ (b : ByteArray) (c : UInt32), 1 ≤ b.size →
          8 ≤ (pushU32LE (pushReplicateByte b 0x00 ((4 - b.size % 4) % 4)) c).size := by
        intro b _ hb; simp only [pushU32LE_size, pushReplicateByte_size]; omega
      apply hPad8
      exact Nat.le_trans (by have hE : ByteArray.empty.size = 0 := rfl; simp only [ByteArray.size_append, ByteArray.size_push, hE]; omega)
        (hBuf1Ge _ _ _ _)
    · have hEmptySz : ByteArray.empty.size = 0 := rfl
      have h2 : (ByteArray.mk #[0x00, 0x04]).size = 2 := rfl
      simp only [ByteArray.size_append, pushU32LE_size, hEmptySz, h2]

end LeanSwe.Compress.Proofs

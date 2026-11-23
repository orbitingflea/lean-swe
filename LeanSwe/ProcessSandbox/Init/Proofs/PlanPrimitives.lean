import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.Init.Proofs.Base

/-!
# ProcessSandbox Init `LSWP0002` Primitive Reader and Seccomp Trailer Proofs

Machine-checked round-trip and rejection lemmas on `psandbox_init::plan` primitives:
- `AtOffset` cursor composition over `Slice U8`,
- Little-endian integer decoders (`read_u8`, `read_u16_le`, `read_u32_le`, `read_u64_le`)
  agreeing with `LeanSwe.ProcessSandbox.Raw.Internal.pushU*`,
- `check_magic` (`"LSWP0002"` acceptance and invalid-magic rejection),
- `has_nul_in_range` and `read_str_span` agreeing with `pushStr` (including NUL rejection),
- `read_bounded_count` cap enforcement,
- `decode_sock_filter` round-tripping `LeanSwe.ProcessSandbox.Seccomp.Impl.encodeSockFilterList`,
- `validate_seccomp_trailer` enforcing `1 ≤ seccomp_n ≤ 160` and exact `8 * seccomp_n` trailer size.
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World
open LeanSwe.ProcessSandbox.Raw (SeccompArch SockFilter SECCOMP_MAX_INSNS)
open LeanSwe.ProcessSandbox.Raw.Internal
  (pushU8 pushU16LE pushU32LE pushU64LE hasNulByte pushStr boolU8)

/-- Cursor invariant stating `pos` lies within `data` and `data.val.drop pos.val = seg ++ tail`. -/
def AtOffset (data : Slice U8) (pos : Usize) (seg tail : Bytes) : Prop :=
  pos.val ≤ data.val.length ∧ data.val.drop pos.val = seg ++ tail

/-- Reassociate `AtOffset` across `a ++ b`. -/
theorem atOffset_assoc (data : Slice U8) (pos : Usize) (a b tail : Bytes)
    (h : AtOffset data pos (a ++ b) tail) :
    AtOffset data pos a (b ++ tail) := by
  refine ⟨h.1, ?_⟩
  rw [h.2, List.append_assoc]

/-- Total bound `pos.val + seg.length + tail.length = data.val.length` from `AtOffset`. -/
theorem atOffset_len_eq {data : Slice U8} {pos : Usize} {seg tail : Bytes}
    (h : AtOffset data pos seg tail) :
    pos.val + seg.length + tail.length = data.val.length := by
  have hDrop := congrArg List.length h.2
  rw [List.length_drop, List.length_append] at hDrop
  have hLe := h.1
  omega

/-- Advance `AtOffset` after consuming `seg` to `pos'` with `pos'.val = pos.val + seg.length`. -/
theorem atOffset_step {data : Slice U8} {pos pos' : Usize} {seg next tail : Bytes}
    (h : AtOffset data pos seg (next ++ tail))
    (hPos' : pos'.val = pos.val + seg.length) :
    AtOffset data pos' next tail := by
  have hTot := atOffset_len_eq h
  rw [List.length_append] at hTot
  refine ⟨by omega, ?_⟩
  have hDrop : data.val.drop pos'.val = (data.val.drop pos.val).drop seg.length := by
    rw [hPos', ← List.drop_drop]
  rw [hDrop, h.2, List.drop_left]

/-- Element lookup inside `seg` from `AtOffset`. -/
theorem atOffset_getElem {data : Slice U8} {pos : Usize} {seg tail : Bytes}
    (h : AtOffset data pos seg tail) (k : Nat) (hk : k < seg.length) :
    data.val[pos.val + k]'(by have := atOffset_len_eq h; omega) = seg[k]'hk := by
  have hDrop := h.2
  have hElem : (data.val.drop pos.val)[k]'(by rw [hDrop, List.length_append]; omega) =
      (seg ++ tail)[k]'(by rw [List.length_append]; omega) := by
    simp [hDrop]
  rw [List.getElem_drop] at hElem
  rw [hElem, List.getElem_append_left hk]

/-- Append homomorphism for `pushU8`. -/
theorem pushU8_eq_append (ba : ByteArray) (v : UInt8) :
    pushU8 ba v = ba ++ ByteArray.mk #[v] := by
  cases ba with
  | mk arr =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [pushU8, ByteArray.push]

/-- Append homomorphism for `pushU16LE`. -/
theorem pushU16LE_eq_append (ba : ByteArray) (v : UInt16) :
    pushU16LE ba v = ba ++ pushU16LE ByteArray.empty v := by
  cases ba with
  | mk arr =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [pushU16LE, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl

/-- Append homomorphism for `pushU32LE`. -/
theorem pushU32LE_eq_append (ba : ByteArray) (v : UInt32) :
    pushU32LE ba v = ba ++ pushU32LE ByteArray.empty v := by
  cases ba with
  | mk arr =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [pushU32LE, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl

/-- Append homomorphism for `pushU64LE`. -/
theorem pushU64LE_eq_append (ba : ByteArray) (v : UInt64) :
    pushU64LE ba v = ba ++ pushU64LE ByteArray.empty v := by
  cases ba with
  | mk arr =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [pushU64LE, pushU64LE.go, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl

/-- Append homomorphism for `pushStr`. -/
theorem pushStr_eq_append (ba : ByteArray) (s : String) :
    pushStr ba s = (pushStr ByteArray.empty s).map (ba ++ ·) := by
  unfold pushStr
  by_cases hNul : hasNulByte s = true
  · simp only [hNul, ↓reduceIte]
    rfl
  · simp only [hNul, Bool.false_eq_true, ↓reduceIte, _root_.Bind.bind, pure, Except.pure]
    by_cases hBig : s.toUTF8.size ≥ UInt32.size
    · simp only [hBig, ↓reduceIte]
      rfl
    · simp only [hBig, ↓reduceIte]
      change Except.ok (pushU32LE ba (UInt32.ofNat s.toUTF8.size) ++ s.toUTF8) =
        Except.ok (ba ++ (pushU32LE ByteArray.empty (UInt32.ofNat s.toUTF8.size) ++ s.toUTF8))
      congr 1
      rw [pushU32LE_eq_append]
      cases ba with
      | mk da =>
        apply ByteArray.ext
        apply Array.toList_inj.mp
        simp

/-- `plan.read_u8` reads the exact byte at `pos` and advances `pos` by `1`. -/
theorem read_u8_atOffset (data : Slice U8) (pos : Usize) (b : U8) (tail : Bytes)
    (h : AtOffset data pos [b] tail) :
    ∃ pos1 : Usize,
      plan.read_u8 data pos = Result.ok (.Ok (b, pos1)) ∧
      pos1.val = pos.val + 1 ∧
      AtOffset data pos1 tail [] := by
  have hTot := atOffset_len_eq h
  simp only [List.length_singleton] at hTot
  have hDataMax := data.property
  have h1u : (1#usize).val = 1 := rfl
  unfold plan.read_u8
  have hNotGe : ¬ (pos ≥ Slice.len data) := by
    have : (Slice.len data).val = data.val.length := by simp
    intro hGe
    have hGeVal : data.val.length ≤ pos.val := by simpa [this] using hGe
    omega
  simp only [hNotGe, ↓reduceIte]
  rw [slice_index_usize_ok data pos (by omega), bind_ok]
  obtain ⟨pos1, hAdd, hPos1⟩ := usize_add_ok pos 1#usize (by change pos.val + 1 ≤ Usize.max; omega)
  rw [hAdd, bind_ok]
  have hElem : data.val[pos.val]'(by omega) = b := by
    simpa using atOffset_getElem h 0 (by simp)
  rw [hElem]
  have hStep : AtOffset data pos1 tail [] :=
    atOffset_step (next := tail) (tail := []) (by simpa using h) (by simp; omega)
  exact ⟨pos1, rfl, by omega, hStep⟩

private theorem u16_reconstruct_bv (v : UInt16) :
    ((BitVec.ofNat 8 (v.toNat % 256)).zeroExtend 16 |||
     BitVec.shiftLeft ((BitVec.ofNat 8 ((v.toNat / 256) % 256)).zeroExtend 16) 8) = v.toBitVec := by
  have h0 : BitVec.ofNat 8 (v.toNat % 256) = v.toBitVec.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 ((v.toNat / 256) % 256) = (BitVec.ushiftRight v.toBitVec 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    change _ = (v.toBitVec >>> 8).toNat % 256
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    change v.toBitVec.toNat / 256 % 256 % 256 = v.toBitVec.toNat / 256 % 256
    omega
  rw [h0, h1]
  ext i hi
  simp only [BitVec.zeroExtend, BitVec.shiftLeft_eq, BitVec.ushiftRight_eq,
    BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h8 : i < 8
  · simp [h8, hi]
  · have hSub : i - 8 < 8 := by omega
    have hAdd : 8 + (i - 8) = i := by omega
    simp [h8, hSub, hAdd, hi]

/-- `plan.read_u16_le` decodes 2 little-endian bytes `[v%256, (v/256)%256]` back to `⟨v.toBitVec⟩`. -/
theorem read_u16_le_bytes_atOffset (data : Slice U8) (pos : Usize) (v : UInt16) (tail : Bytes)
    (h : AtOffset data pos
      [u8OfUInt8 (UInt8.ofNat (v.toNat % 256)),
       u8OfUInt8 (UInt8.ofNat ((v.toNat / 256) % 256))] tail) :
    ∃ pos2 : Usize,
      plan.read_u16_le data pos = Result.ok (.Ok (⟨v.toBitVec⟩, pos2)) ∧
      pos2.val = pos.val + 2 ∧
      AtOffset data pos2 tail [] := by
  have hTot := atOffset_len_eq h
  simp only [List.length_cons, List.length_nil] at hTot
  have hDataMax := data.property
  have h1u : (1#usize).val = 1 := rfl
  have h2u : (2#usize).val = 2 := rfl
  unfold plan.read_u16_le
  have hLenVal : (Slice.len data).val = data.val.length := by simp
  have hNotLt2 : ¬ (Slice.len data < 2#usize) := by
    intro hLt
    have : data.val.length < 2 := by simpa [hLenVal, h2u] using hLt
    omega
  simp only [hNotLt2, ↓reduceIte]
  obtain ⟨lim, hSub, hLim⟩ := usize_sub_ok (Slice.len data) 2#usize (by rw [hLenVal]; omega)
  rw [hSub, bind_ok]
  have hNotGt : ¬ (pos > lim) := by
    intro hGt
    have : lim.val < pos.val := by simpa using hGt
    omega
  simp only [hNotGt, ↓reduceIte]
  obtain ⟨p1, hp1, hp1Val⟩ := usize_add_ok pos 1#usize (by change pos.val + 1 ≤ Usize.max; omega)
  obtain ⟨p2, hp2, hp2Val⟩ := usize_add_ok pos 2#usize (by change pos.val + 2 ≤ Usize.max; omega)
  dsimp only [lift]
  rw [slice_index_usize_ok data pos (by omega), bind_ok, bind_ok,
    hp1, bind_ok,
    slice_index_usize_ok data p1 (by omega), bind_ok, bind_ok,
    uscalar_shl_i32_ok _ 8#i32 8 (by decide) rfl (by rw [UScalarTy.U16_numBits_eq]; decide), bind_ok,
    bind_ok, hp2, bind_ok]
  have hb0 : data.val[pos.val]'(by omega) = u8OfUInt8 (UInt8.ofNat (v.toNat % 256)) := by
    simpa using atOffset_getElem h 0 (by simp)
  have hb1 : data.val[p1.val]'(by omega) = u8OfUInt8 (UInt8.ofNat ((v.toNat / 256) % 256)) := by
    have hp1Eq : p1.val = pos.val + 1 := by omega
    simpa [hp1Eq] using atOffset_getElem h 1 (by simp)
  rw [hb0, hb1]
  have hValEq :
      ((UScalar.cast .U16 (u8OfUInt8 (UInt8.ofNat (v.toNat % 256))) : U16) |||
       ⟨BitVec.shiftLeft (UScalar.cast .U16 (u8OfUInt8 (UInt8.ofNat ((v.toNat / 256) % 256))) : U16).bv 8⟩) =
      (⟨v.toBitVec⟩ : U16) := by
    apply uscalar_eq_of_bv
    exact u16_reconstruct_bv v
  rw [hValEq]
  have hStep : AtOffset data p2 tail [] :=
    atOffset_step (next := tail) (tail := []) (by simpa using h) (by simp; omega)
  exact ⟨p2, rfl, by omega, hStep⟩

/-- `plan.read_u16_le` decodes `pushU16LE ByteArray.empty v` back to `⟨v.toBitVec⟩` and advances `pos` by `2`. -/
theorem read_u16_le_atOffset (data : Slice U8) (pos : Usize) (v : UInt16) (tail : Bytes)
    (h : AtOffset data pos (byteArrayToBytes (pushU16LE ByteArray.empty v)) tail) :
    ∃ pos2 : Usize,
      plan.read_u16_le data pos = Result.ok (.Ok (⟨v.toBitVec⟩, pos2)) ∧
      pos2.val = pos.val + 2 ∧
      AtOffset data pos2 tail [] :=
  read_u16_le_bytes_atOffset data pos v tail h

private theorem u32_reconstruct_bv_from_shifts (bv : BitVec 32) :
    (((((bv.setWidth 8).zeroExtend 32 |||
        BitVec.shiftLeft (((BitVec.ushiftRight bv 8).setWidth 8).zeroExtend 32) 8) |||
        BitVec.shiftLeft (((BitVec.ushiftRight bv 16).setWidth 8).zeroExtend 32) 16) |||
        BitVec.shiftLeft (((BitVec.ushiftRight bv 24).setWidth 8).zeroExtend 32) 24)) = bv := by
  ext i hi
  simp only [BitVec.zeroExtend, BitVec.shiftLeft_eq, BitVec.ushiftRight_eq,
    BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h8 : i < 8
  · have h16 : i < 16 := by omega
    have h24 : i < 24 := by omega
    simp [h8, h16, h24, hi]
  · by_cases h16 : i < 16
    · have h24 : i < 24 := by omega
      have hs : i - 8 < 8 := by omega
      have hb : 8 + (i - 8) = i := by omega
      simp [h8, h16, h24, hs, hb, hi]
    · by_cases h24 : i < 24
      · have hs1 : ¬ (i - 8 < 8) := by omega
        have hs2 : i - 16 < 8 := by omega
        have hb : 16 + (i - 16) = i := by omega
        simp [h8, h16, h24, hs1, hs2, hb, hi]
      · have hs1 : ¬ (i - 8 < 8) := by omega
        have hs2 : ¬ (i - 16 < 8) := by omega
        have hs3 : i - 24 < 8 := by omega
        have hb : 24 + (i - 24) = i := by omega
        simp [h8, h16, h24, hs1, hs2, hs3, hb, hi]

private theorem u32_byte_eq_shift (v : UInt32) (sh : Nat) :
    (u8OfUInt8 (UInt8.ofNat ((v.toNat / (2 ^ sh)) % 256))).bv =
      (BitVec.ushiftRight v.toBitVec sh).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 8 ((v.toNat / (2 ^ sh)) % 256)).toNat = (v.toBitVec >>> sh).toNat % 256
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  simp

/-- `plan.read_u32_le` decodes any 4 little-endian bytes of `bv : BitVec 32` back to `⟨bv⟩`. -/
theorem read_u32_le_bv_atOffset (data : Slice U8) (pos : Usize) (bv : BitVec 32) (tail : Bytes)
    (h : AtOffset data pos
      [⟨bv.setWidth 8⟩,
       ⟨(BitVec.ushiftRight bv 8).setWidth 8⟩,
       ⟨(BitVec.ushiftRight bv 16).setWidth 8⟩,
       ⟨(BitVec.ushiftRight bv 24).setWidth 8⟩] tail) :
    ∃ pos4 : Usize,
      plan.read_u32_le data pos = Result.ok (.Ok (⟨bv⟩, pos4)) ∧
      pos4.val = pos.val + 4 ∧
      AtOffset data pos4 tail [] := by
  have hTot := atOffset_len_eq h
  simp only [List.length_cons, List.length_nil] at hTot
  have hDataMax := data.property
  have h1u : (1#usize).val = 1 := rfl
  have h2u : (2#usize).val = 2 := rfl
  have h3u : (3#usize).val = 3 := rfl
  have h4u : (4#usize).val = 4 := rfl
  unfold plan.read_u32_le
  have hLenVal : (Slice.len data).val = data.val.length := by simp
  have hNotLt4 : ¬ (Slice.len data < 4#usize) := by
    intro hLt
    have : data.val.length < 4 := by simpa [hLenVal, h4u] using hLt
    omega
  simp only [hNotLt4, ↓reduceIte]
  obtain ⟨lim, hSub, hLim⟩ := usize_sub_ok (Slice.len data) 4#usize (by rw [hLenVal]; omega)
  rw [hSub, bind_ok]
  have hNotGt : ¬ (pos > lim) := by
    intro hGt
    have : lim.val < pos.val := by simpa using hGt
    omega
  simp only [hNotGt, ↓reduceIte]
  obtain ⟨p1, hp1, hp1Val⟩ := usize_add_ok pos 1#usize (by change pos.val + 1 ≤ Usize.max; omega)
  obtain ⟨p2, hp2, hp2Val⟩ := usize_add_ok pos 2#usize (by change pos.val + 2 ≤ Usize.max; omega)
  obtain ⟨p3, hp3, hp3Val⟩ := usize_add_ok pos 3#usize (by change pos.val + 3 ≤ Usize.max; omega)
  obtain ⟨p4, hp4, hp4Val⟩ := usize_add_ok pos 4#usize (by change pos.val + 4 ≤ Usize.max; omega)
  dsimp only [lift]
  rw [slice_index_usize_ok data pos (by omega), bind_ok, bind_ok,
    hp1, bind_ok, slice_index_usize_ok data p1 (by omega), bind_ok, bind_ok,
    uscalar_shl_i32_ok _ 8#i32 8 (by decide) rfl (by rw [UScalarTy.U32_numBits_eq]; decide), bind_ok,
    hp2, bind_ok, slice_index_usize_ok data p2 (by omega), bind_ok, bind_ok,
    uscalar_shl_i32_ok _ 16#i32 16 (by decide) rfl (by rw [UScalarTy.U32_numBits_eq]; decide), bind_ok,
    hp3, bind_ok, slice_index_usize_ok data p3 (by omega), bind_ok, bind_ok,
    uscalar_shl_i32_ok _ 24#i32 24 (by decide) rfl (by rw [UScalarTy.U32_numBits_eq]; decide), bind_ok,
    bind_ok, bind_ok, bind_ok, hp4, bind_ok]
  have hp1Eq : p1.val = pos.val + 1 := by omega
  have hp2Eq : p2.val = pos.val + 2 := by omega
  have hp3Eq : p3.val = pos.val + 3 := by omega
  have e0 : data.val[pos.val]'(by omega) = ⟨bv.setWidth 8⟩ := by
    simpa using atOffset_getElem h 0 (by simp)
  have e1 : data.val[p1.val]'(by omega) = ⟨(BitVec.ushiftRight bv 8).setWidth 8⟩ := by
    simpa [hp1Eq] using atOffset_getElem h 1 (by simp)
  have e2 : data.val[p2.val]'(by omega) = ⟨(BitVec.ushiftRight bv 16).setWidth 8⟩ := by
    simpa [hp2Eq] using atOffset_getElem h 2 (by simp)
  have e3 : data.val[p3.val]'(by omega) = ⟨(BitVec.ushiftRight bv 24).setWidth 8⟩ := by
    simpa [hp3Eq] using atOffset_getElem h 3 (by simp)
  rw [e0, e1, e2, e3]
  have hValEq :
      ((((UScalar.cast .U32 (⟨bv.setWidth 8⟩ : U8) : U32) |||
         ⟨BitVec.shiftLeft (UScalar.cast .U32 (⟨(BitVec.ushiftRight bv 8).setWidth 8⟩ : U8) : U32).bv 8⟩) |||
         ⟨BitVec.shiftLeft (UScalar.cast .U32 (⟨(BitVec.ushiftRight bv 16).setWidth 8⟩ : U8) : U32).bv 16⟩) |||
         ⟨BitVec.shiftLeft (UScalar.cast .U32 (⟨(BitVec.ushiftRight bv 24).setWidth 8⟩ : U8) : U32).bv 24⟩) =
      (⟨bv⟩ : U32) := by
    apply uscalar_eq_of_bv
    exact u32_reconstruct_bv_from_shifts bv
  rw [hValEq]
  have hStep : AtOffset data p4 tail [] :=
    atOffset_step (next := tail) (tail := []) (by simpa using h) (by simp; omega)
  exact ⟨p4, rfl, by omega, hStep⟩

/-- `plan.read_u32_le` decodes `pushU32LE ByteArray.empty v` back to `⟨v.toBitVec⟩` and advances `pos` by `4`. -/
theorem read_u32_le_atOffset (data : Slice U8) (pos : Usize) (v : UInt32) (tail : Bytes)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty v)) tail) :
    ∃ pos4 : Usize,
      plan.read_u32_le data pos = Result.ok (.Ok (⟨v.toBitVec⟩, pos4)) ∧
      pos4.val = pos.val + 4 ∧
      AtOffset data pos4 tail [] := by
  have hSeg : byteArrayToBytes (pushU32LE ByteArray.empty v) =
      [⟨v.toBitVec.setWidth 8⟩,
       ⟨(BitVec.ushiftRight v.toBitVec 8).setWidth 8⟩,
       ⟨(BitVec.ushiftRight v.toBitVec 16).setWidth 8⟩,
       ⟨(BitVec.ushiftRight v.toBitVec 24).setWidth 8⟩] := by
    change [u8OfUInt8 (UInt8.ofNat (v.toNat % 256)),
            u8OfUInt8 (UInt8.ofNat ((v.toNat / 256) % 256)),
            u8OfUInt8 (UInt8.ofNat ((v.toNat / 65536) % 256)),
            u8OfUInt8 (UInt8.ofNat ((v.toNat / 16777216) % 256))] = _
    congr 1
    · exact uscalar_eq_of_bv (by simpa using u32_byte_eq_shift v 0)
    · congr 1
      · exact uscalar_eq_of_bv (by simpa using u32_byte_eq_shift v 8)
      · congr 1
        · exact uscalar_eq_of_bv (by simpa using u32_byte_eq_shift v 16)
        · congr 1
          exact uscalar_eq_of_bv (by simpa using u32_byte_eq_shift v 24)
  rw [hSeg] at h
  exact read_u32_le_bv_atOffset data pos v.toBitVec tail h

private theorem u64_step_byte (cur : UInt64) :
    u8OfUInt8 (UInt8.ofNat (cur.toNat % 256)) = ⟨cur.toBitVec.setWidth 8⟩ := by
  apply uscalar_eq_of_bv
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 8 (cur.toNat % 256)).toNat = cur.toNat % 256
  simp

private theorem u64_shr8_bv (cur : UInt64) :
    (cur >>> 8).toBitVec = BitVec.ushiftRight cur.toBitVec 8 := by
  rfl

private theorem pushU64LE_bytes_eq (v : UInt64) :
    byteArrayToBytes (pushU64LE ByteArray.empty v) =
      [⟨(v.toBitVec.setWidth 32).setWidth 8⟩,
       ⟨(BitVec.ushiftRight (v.toBitVec.setWidth 32) 8).setWidth 8⟩,
       ⟨(BitVec.ushiftRight (v.toBitVec.setWidth 32) 16).setWidth 8⟩,
       ⟨(BitVec.ushiftRight (v.toBitVec.setWidth 32) 24).setWidth 8⟩] ++
      [⟨((BitVec.ushiftRight v.toBitVec 32).setWidth 32).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 8).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 16).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 24).setWidth 8⟩] := by
  change [u8OfUInt8 (UInt8.ofNat (v.toNat % 256)),
          u8OfUInt8 (UInt8.ofNat ((v >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat (((v >>> 8) >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat ((((v >>> 8) >>> 8) >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat (((((v >>> 8) >>> 8) >>> 8) >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat ((((((v >>> 8) >>> 8) >>> 8) >>> 8) >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat (((((((v >>> 8) >>> 8) >>> 8) >>> 8) >>> 8) >>> 8).toNat % 256)),
          u8OfUInt8 (UInt8.ofNat ((((((((v >>> 8) >>> 8) >>> 8) >>> 8) >>> 8) >>> 8) >>> 8).toNat % 256))] = _
  simp only [u64_step_byte, u64_shr8_bv, List.cons_append, List.nil_append]
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change v.toBitVec.setWidth 8 = (v.toBitVec.setWidth 32).setWidth 8
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
    simp [show i < 32 by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight v.toBitVec 8).setWidth 8 =
      (BitVec.ushiftRight (v.toBitVec.setWidth 32) 8).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 8 + i < 32 by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8).setWidth 8 =
      (BitVec.ushiftRight (v.toBitVec.setWidth 32) 16).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 16 + i < 32 by omega, show 8 + (8 + i) = 16 + i by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8) 8).setWidth 8 =
      (BitVec.ushiftRight (v.toBitVec.setWidth 32) 24).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 24 + i < 32 by omega, show 8 + (8 + (8 + i)) = 24 + i by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8) 8) 8).setWidth 8 =
      ((BitVec.ushiftRight v.toBitVec 32).setWidth 32).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show i < 32 by omega, show 8 + (8 + (8 + (8 + i))) = 32 + i by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8) 8) 8) 8).setWidth 8 =
      (BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 8).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 8 + i < 32 by omega, show 8 + (8 + (8 + (8 + (8 + i)))) = 32 + (8 + i) by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8) 8) 8) 8) 8).setWidth 8 =
      (BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 16).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 16 + i < 32 by omega, show 8 + (8 + (8 + (8 + (8 + (8 + i))))) = 32 + (16 + i) by omega])) ?_
  refine congrArg₂ List.cons (uscalar_eq_of_bv (by
    change (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight (BitVec.ushiftRight v.toBitVec 8) 8) 8) 8) 8) 8) 8).setWidth 8 =
      (BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 24).setWidth 8
    ext i hi
    simp only [BitVec.ushiftRight_eq, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp [show 24 + i < 32 by omega, show 8 + (8 + (8 + (8 + (8 + (8 + (8 + i)))))) = 32 + (24 + i) by omega])) rfl

/-- `plan.read_u64_le` decodes `pushU64LE ByteArray.empty v` back to `⟨v.toBitVec⟩` and advances `pos` by `8`. -/
theorem read_u64_le_atOffset (data : Slice U8) (pos : Usize) (v : UInt64) (tail : Bytes)
    (h : AtOffset data pos (byteArrayToBytes (pushU64LE ByteArray.empty v)) tail) :
    ∃ pos8 : Usize,
      plan.read_u64_le data pos = Result.ok (.Ok (⟨v.toBitVec⟩, pos8)) ∧
      pos8.val = pos.val + 8 ∧
      AtOffset data pos8 tail [] := by
  rw [pushU64LE_bytes_eq v] at h
  have h1 := atOffset_assoc data pos _ _ tail h
  obtain ⟨pos4, hrLo, hp4, hMid⟩ := read_u32_le_bv_atOffset data pos (v.toBitVec.setWidth 32) _ h1
  have hMid' : AtOffset data pos4
      [⟨((BitVec.ushiftRight v.toBitVec 32).setWidth 32).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 8).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 16).setWidth 8⟩,
       ⟨(BitVec.ushiftRight ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) 24).setWidth 8⟩] tail := by
    refine ⟨hMid.1, ?_⟩
    simpa [List.append_nil] using hMid.2
  obtain ⟨pos8, hrHi, hp8, hEnd⟩ :=
    read_u32_le_bv_atOffset data pos4 ((BitVec.ushiftRight v.toBitVec 32).setWidth 32) tail hMid'
  refine ⟨pos8, ?_, by omega, hEnd⟩
  rw [plan.read_u64_le]
  refine eq_ok_of_try_ok hrLo ?_
  refine eq_ok_of_try_ok hrHi ?_
  refine eq_ok_of_bind rfl ?_
  refine eq_ok_of_bind rfl ?_
  refine eq_ok_of_bind
    (uscalar_shl_i32_ok _ 32#i32 32 (by decide) rfl (by rw [UScalarTy.U64_numBits_eq]; decide)) ?_
  refine eq_ok_of_bind rfl ?_
  have hComb :
      ((UScalar.cast .U64 (⟨v.toBitVec.setWidth 32⟩ : U32) : U64) |||
       ⟨BitVec.shiftLeft (UScalar.cast .U64 (⟨(BitVec.ushiftRight v.toBitVec 32).setWidth 32⟩ : U32) : U64).bv 32⟩) =
      (⟨v.toBitVec⟩ : U64) := by
    apply uscalar_eq_of_bv
    change (v.toBitVec.setWidth 32).zeroExtend 64 |||
        BitVec.shiftLeft (((BitVec.ushiftRight v.toBitVec 32).setWidth 32).zeroExtend 64) 32 = v.toBitVec
    ext i hi
    simp only [BitVec.zeroExtend, BitVec.shiftLeft_eq, BitVec.ushiftRight_eq,
      BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    by_cases h32 : i < 32
    · simp [h32, hi]
    · have hs : i - 32 < 32 := by omega
      have hb : 32 + (i - 32) = i := by omega
      simp [h32, hs, hb, hi]
  rw [hComb]

/-- `plan.check_magic` accepts `"LSWP0002"` at offset `0` and returns `.Ok 8#usize`. -/
theorem check_magic_atOffset (data : Slice U8) (tail : Bytes)
    (h : AtOffset data 0#usize (byteArrayToBytes "LSWP0002".toUTF8) tail) :
    plan.check_magic data = Result.ok (.Ok 8#usize) ∧
    AtOffset data 8#usize tail [] := by
  have hMag : byteArrayToBytes "LSWP0002".toUTF8 =
      [76#u8, 83#u8, 87#u8, 80#u8, 48#u8, 48#u8, 48#u8, 50#u8] := by decide
  have h' := h
  rw [hMag] at h'
  have hTot := atOffset_len_eq h'
  have h0Val : (0#usize).val = 0 := rfl
  have h1u : (1#usize).val = 1 := rfl
  have h8u : (8#usize).val = 8 := rfl
  simp only [h0Val, List.length_cons, List.length_nil] at hTot
  let mArr := Array.make 8#usize [76#u8, 83#u8, 87#u8, 80#u8, 48#u8, 48#u8, 48#u8, 50#u8]
  have hLoop : OkPost (plan.check_magic_loop data mArr 0#usize) (fun b => b = true) := by
    unfold plan.check_magic_loop
    refine okPost_loop_decr_nat
      (fun i : Usize => 8 - i.val)
      (fun i => i.val ≤ 8)
      (fun b => b = true)
      _ 0#usize ?_ (by decide)
    intro i hi
    unfold plan.check_magic_loop.body
    by_cases hLt8 : i < 8#usize
    · have hiVal : i.val < 8 := by simpa [h8u] using hLt8
      simp only [hLt8, ↓reduceIte]
      rw [slice_index_usize_ok data i (by omega), bind_ok,
        array_index_usize_ok mArr i hiVal, bind_ok]
      have hElemD : data.val[i.val]'(by omega) =
          ([76#u8, 83#u8, 87#u8, 80#u8, 48#u8, 48#u8, 48#u8, 50#u8])[i.val]'hiVal := by
        simpa [h0Val] using atOffset_getElem h' i.val hiVal
      have hElemM : mArr.val[i.val]'(by rw [mArr.property]; exact hiVal) =
          ([76#u8, 83#u8, 87#u8, 80#u8, 48#u8, 48#u8, 48#u8, 50#u8])[i.val]'hiVal := rfl
      rw [hElemD, hElemM]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨i1, hi1, hi1Val⟩ := usize_add_ok i 1#usize
        (by have := usize_max_ge_u32_max; change i.val + 1 ≤ Usize.max; omega)
      rw [hi1, bind_ok]
      exact ⟨cont i1, rfl, by omega, by omega⟩
    · simp only [hLt8, ↓reduceIte]
      exact ⟨done true, rfl, rfl⟩
  obtain ⟨okB, hRun, hTrue⟩ := hLoop
  subst hTrue
  have hStep : AtOffset data 8#usize tail [] :=
    atOffset_step (next := tail) (tail := []) (by simpa using h') (by decide)
  refine ⟨?_, hStep⟩
  unfold plan.check_magic
  have hNotLt8 : ¬ (Slice.len data < 8#usize) := by
    have : (Slice.len data).val = data.val.length := by simp
    intro hLt
    have : data.val.length < 8 := by simpa [this, h8u] using hLt
    omega
  rw [if_false_eq hNotLt8, hRun, bind_ok, if_true_eq rfl]

/-- Evaluation of `plan.EINVAL` to `22#i32`. -/
theorem plan_einval_eq : plan.EINVAL = 22#i32 := by
  simp [plan.EINVAL]

/-- `plan.check_magic` rejects buffers shorter than 8 bytes with `Err plan.EINVAL` (`22`). -/
theorem check_magic_rejects_short (data : Slice U8) (hShort : data.val.length < 8) :
    plan.check_magic data = Result.ok (.Err plan.EINVAL) := by
  rw [plan.check_magic]
  have hLt : Slice.len data < 8#usize := by
    change (Slice.len data).val < (8#usize).val
    simpa using hShort
  rw [if_true_eq hLt]

/-- `plan.has_nul_in_range` returns `false` when no byte in `[start, stop)` equals `0#u8`. -/
theorem has_nul_in_range_false_of_forall (data : Slice U8) (start stop : Usize)
    (hLe : start.val ≤ stop.val) (hStop : stop.val ≤ data.val.length)
    (hNoNul : ∀ k : Nat, start.val ≤ k → (hk : k < stop.val) →
      data.val[k]'(by omega) ≠ 0#u8) :
    plan.has_nul_in_range data start stop = Result.ok false := by
  have h1u : (1#usize).val = 1 := rfl
  suffices hPost : OkPost (plan.has_nul_in_range_loop data stop start) (fun b => b = false) by
    rcases hPost with ⟨b, hb, rfl⟩
    exact hb
  unfold plan.has_nul_in_range_loop
  refine okPost_loop_decr_nat
    (fun i : Usize => stop.val - i.val)
    (fun i => start.val ≤ i.val ∧ i.val ≤ stop.val)
    (fun b => b = false)
    _ start ?_ ⟨Nat.le_refl _, hLe⟩
  rintro cur ⟨hGe, hCurStop⟩
  unfold plan.has_nul_in_range_loop.body
  by_cases hLt : cur < stop
  · have hLtVal : cur.val < stop.val := by simpa using hLt
    have hLtLen : cur < Slice.len data := by
      change cur.val < (Slice.len data).val
      simp only [Slice.len_val, Slice.length]
      omega
    simp only [hLt, hLtLen, ↓reduceIte]
    rw [slice_index_usize_ok data cur (by omega), bind_ok]
    have hNe0 : data.val[cur.val]'(by omega) ≠ 0#u8 := hNoNul cur.val hGe hLtVal
    simp only [hNe0, ↓reduceIte]
    have hMax := data.property
    obtain ⟨next, hNext, hNextVal⟩ := usize_add_ok cur 1#usize
      (by change cur.val + 1 ≤ Usize.max; omega)
    rw [hNext, bind_ok]
    exact ⟨cont next, rfl, ⟨by omega, by omega⟩, by omega⟩
  · simp only [hLt, ↓reduceIte]
    exact ⟨done false, rfl, rfl⟩

/-- `plan.read_str_span` decodes a `pushStr`-encoded string into a `Span` over `s.toUTF8` and advances `pos`. -/
theorem read_str_span_atOffset (data : Slice U8) (pos : Usize) (s : String)
    (strBytes : ByteArray) (tail : Bytes)
    (hPush : pushStr ByteArray.empty s = .ok strBytes)
    (h : AtOffset data pos (byteArrayToBytes strBytes) tail) :
    ∃ (sp : plan.Span) (pos' : Usize),
      plan.read_str_span data pos = Result.ok (.Ok (sp, pos')) ∧
      sp.start.val = pos.val + 4 ∧
      sp.len.val = s.toUTF8.size ∧
      (data.val.drop sp.start.val).take sp.len.val = byteArrayToBytes s.toUTF8 ∧
      pos'.val = pos.val + strBytes.size ∧
      AtOffset data pos' tail [] := by
  unfold pushStr at hPush
  by_cases hNul : hasNulByte s = true
  · simp only [hNul, ↓reduceIte] at hPush
    cases hPush
  · simp only [hNul, Bool.false_eq_true, ↓reduceIte, _root_.Bind.bind, pure, Except.pure] at hPush
    by_cases hBig : s.toUTF8.size ≥ UInt32.size
    · simp only [hBig, ↓reduceIte] at hPush
      cases hPush
    · simp only [hBig, ↓reduceIte] at hPush
      have hBytesEq : strBytes = pushU32LE ByteArray.empty (UInt32.ofNat s.toUTF8.size) ++ s.toUTF8 := by
        cases hPush
        rfl
      have hSeg : byteArrayToBytes strBytes =
          byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat s.toUTF8.size)) ++
          byteArrayToBytes s.toUTF8 := by
        rw [hBytesEq, byteArrayToBytes_append]
      have h1 : AtOffset data pos
          (byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat s.toUTF8.size)))
          (byteArrayToBytes s.toUTF8 ++ tail) := by
        refine ⟨h.1, ?_⟩
        rw [h.2, hSeg, List.append_assoc]
      obtain ⟨p1, hrLen, hp1Val, hAfterLen⟩ :=
        read_u32_le_atOffset data pos (UInt32.ofNat s.toUTF8.size) (byteArrayToBytes s.toUTF8 ++ tail) h1
      have hAfter' : AtOffset data p1 (byteArrayToBytes s.toUTF8) tail := by
        refine ⟨hAfterLen.1, ?_⟩
        simpa [List.append_nil] using hAfterLen.2
      have hTot := atOffset_len_eq hAfter'
      rw [length_byteArrayToBytes] at hTot
      have hDataMax := data.property
      have hU32Val : (⟨(UInt32.ofNat s.toUTF8.size).toBitVec⟩ : U32).val = s.toUTF8.size := by
        change (UInt32.ofNat s.toUTF8.size).toNat = s.toUTF8.size
        have hLt : s.toUTF8.size < UInt32.size := by omega
        exact Nat.mod_eq_of_lt hLt
      let slen : Usize := UScalar.cast .Usize (⟨(UInt32.ofNat s.toUTF8.size).toBitVec⟩ : U32)
      have hSlenVal : slen.val = s.toUTF8.size := by
        rw [u32_cast_usize_val, hU32Val]
      have hLenData : (Slice.len data).val = data.val.length := by simp
      obtain ⟨rem, hSub, hRem⟩ := usize_sub_ok (Slice.len data) p1 (by rw [hLenData]; omega)
      have hNotGt : ¬ (slen > rem) := by
        intro hGt
        have : rem.val < slen.val := by simpa using hGt
        omega
      obtain ⟨stop, hAddStop, hStopVal⟩ := usize_add_ok p1 slen (by omega)
      have hNoNulRange : ∀ k : Nat, p1.val ≤ k → (hk : k < stop.val) → data.val[k]'(by omega) ≠ 0#u8 := by
        intro k hkLo hkHi hZero
        have hRelLt : k - p1.val < (byteArrayToBytes s.toUTF8).length := by
          rw [length_byteArrayToBytes]
          omega
        have hAt := atOffset_getElem hAfter' (k - p1.val) hRelLt
        have hkEq : p1.val + (k - p1.val) = k := by omega
        have hAt' : data.val[k]'(by omega) = (byteArrayToBytes s.toUTF8)[k - p1.val]'hRelLt := by
          simpa [hkEq] using hAt
        rw [hZero] at hAt'
        have hUtfZero : s.toUTF8.data.toList[k - p1.val]'(by
            have := hRelLt; rw [byteArrayToBytes, List.length_map] at this; exact this) = 0 := by
          have hMap : u8OfUInt8 (s.toUTF8.data.toList[k - p1.val]'(by
              have := hRelLt; rw [byteArrayToBytes, List.length_map] at this; exact this)) = 0#u8 := by
            simpa [byteArrayToBytes] using hAt'.symm
          have := congrArg uint8OfU8 hMap
          exact this
        have hCont : hasNulByte s = true := by
          unfold hasNulByte
          rw [List.contains_iff_exists_mem_beq]
          exact ⟨0, List.mem_of_getElem hUtfZero, rfl⟩
        exact hNul hCont
      have hTake : (data.val.drop p1.val).take slen.val = byteArrayToBytes s.toUTF8 := by
        rw [hAfter'.2, hSlenVal]
        have hLenEq : s.toUTF8.size = (byteArrayToBytes s.toUTF8).length :=
          (length_byteArrayToBytes s.toUTF8).symm
        rw [hLenEq, List.take_left]
      have hStep : AtOffset data stop tail [] :=
        atOffset_step (next := tail) (tail := [])
          (by simpa [List.append_nil] using hAfter')
          (by rw [hStopVal, hSlenVal, length_byteArrayToBytes]; rfl)
      have hStrBytesSize : strBytes.size = 4 + s.toUTF8.size := by
        have hL := congrArg List.length hSeg
        rw [length_byteArrayToBytes, List.length_append, length_byteArrayToBytes, length_byteArrayToBytes] at hL
        have h4 : (pushU32LE ByteArray.empty (UInt32.ofNat s.toUTF8.size)).size = 4 := rfl
        omega
      refine ⟨{ start := p1, len := slen }, stop, ?_, hp1Val, hSlenVal, hTake, by omega, hStep⟩
      rw [plan.read_str_span]
      refine eq_ok_of_try_ok hrLen ?_
      refine eq_ok_of_bind rfl ?_
      refine eq_ok_of_bind hSub ?_
      rw [if_false_eq hNotGt]
      refine eq_ok_of_bind hAddStop ?_
      refine eq_ok_of_bind
        (has_nul_in_range_false_of_forall data p1 stop (by omega) (by omega) hNoNulRange) ?_
      rw [if_false_eq Bool.false_ne_true]

/-- `plan.read_bounded_count` accepts `n ≤ max_count` and rejects `n > max_count` with `Err EINVAL`. -/
theorem read_bounded_count_atOffset (data : Slice U8) (pos : Usize) (n : Nat) (maxCount : U32) (tail : Bytes)
    (hBound : n ≤ maxCount.val)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat n))) tail) :
    ∃ (cnt : U32) (pos4 : Usize),
      plan.read_bounded_count data pos maxCount = Result.ok (.Ok (cnt, pos4)) ∧
      cnt.val = n ∧
      pos4.val = pos.val + 4 ∧
      AtOffset data pos4 tail [] := by
  obtain ⟨pos4, hr, hp4, hStep⟩ := read_u32_le_atOffset data pos (UInt32.ofNat n) tail h
  have hCntVal : (⟨(UInt32.ofNat n).toBitVec⟩ : U32).val = n := by
    change (UInt32.ofNat n).toNat = n
    have hMax : maxCount.val < 4294967296 := maxCount.bv.isLt
    exact Nat.mod_eq_of_lt (by omega)
  have hNotGt : ¬ ((⟨(UInt32.ofNat n).toBitVec⟩ : U32) > maxCount) := by
    intro hGt
    have : maxCount.val < (⟨(UInt32.ofNat n).toBitVec⟩ : U32).val := by simpa using hGt
    omega
  refine ⟨⟨(UInt32.ofNat n).toBitVec⟩, pos4, ?_, hCntVal, hp4, hStep⟩
  rw [plan.read_bounded_count]
  refine eq_ok_of_try_ok hr ?_
  change (if (⟨(UInt32.ofNat n).toBitVec⟩ : U32) > maxCount then _ else _) = _
  rw [if_false_eq hNotGt]

/-- Round-trip theorem: `plan.decode_sock_filter` recovers the exact `SockFilter` encoded by `Seccomp.Impl.encodeSockFilterList`. -/
theorem decode_sock_filter_roundTrip (data : Slice U8) (pos : Usize)
    (insn : SockFilter) (tail : Bytes)
    (h : AtOffset data pos ((LeanSwe.ProcessSandbox.Seccomp.Impl.encodeSockFilterList insn).map u8OfUInt8) tail) :
    ∃ pos8 : Usize,
      plan.decode_sock_filter data pos =
        Result.ok (.Ok ({ code := ⟨insn.code.toBitVec⟩
                          jt := u8OfUInt8 insn.jt
                          jf := u8OfUInt8 insn.jf
                          k := ⟨insn.k.toBitVec⟩ }, pos8)) ∧
      pos8.val = pos.val + 8 ∧
      AtOffset data pos8 tail [] := by
  have hDecomp :
      (LeanSwe.ProcessSandbox.Seccomp.Impl.encodeSockFilterList insn).map u8OfUInt8 =
        [u8OfUInt8 (UInt8.ofNat (insn.code.toNat % 256)),
         u8OfUInt8 (UInt8.ofNat ((insn.code.toNat / 256) % 256))] ++
        [u8OfUInt8 insn.jt] ++
        [u8OfUInt8 insn.jf] ++
        byteArrayToBytes (pushU32LE ByteArray.empty insn.k) := rfl
  have h1 : AtOffset data pos
      [u8OfUInt8 (UInt8.ofNat (insn.code.toNat % 256)),
       u8OfUInt8 (UInt8.ofNat ((insn.code.toNat / 256) % 256))]
      ([u8OfUInt8 insn.jt] ++ [u8OfUInt8 insn.jf] ++ byteArrayToBytes (pushU32LE ByteArray.empty insn.k) ++ tail) := by
    refine ⟨h.1, ?_⟩
    rw [h.2, hDecomp]
    simp
  obtain ⟨p1, hrCode, hp1, hS1⟩ := read_u16_le_bytes_atOffset data pos insn.code _ h1
  have h2 : AtOffset data p1 [u8OfUInt8 insn.jt]
      ([u8OfUInt8 insn.jf] ++ byteArrayToBytes (pushU32LE ByteArray.empty insn.k) ++ tail) := by
    refine ⟨hS1.1, ?_⟩
    simpa [List.append_assoc] using hS1.2
  obtain ⟨p2, hrJt, hp2, hS2⟩ := read_u8_atOffset data p1 (u8OfUInt8 insn.jt) _ h2
  have h3 : AtOffset data p2 [u8OfUInt8 insn.jf]
      (byteArrayToBytes (pushU32LE ByteArray.empty insn.k) ++ tail) := by
    refine ⟨hS2.1, ?_⟩
    simpa [List.append_assoc] using hS2.2
  obtain ⟨p3, hrJf, hp3, hS3⟩ := read_u8_atOffset data p2 (u8OfUInt8 insn.jf) _ h3
  have h4 : AtOffset data p3 (byteArrayToBytes (pushU32LE ByteArray.empty insn.k)) tail := by
    refine ⟨hS3.1, ?_⟩
    simpa [List.append_nil] using hS3.2
  obtain ⟨p4, hrK, hp4, hS4⟩ := read_u32_le_atOffset data p3 insn.k tail h4
  refine ⟨p4, ?_, by omega, hS4⟩
  rw [plan.decode_sock_filter]
  refine eq_ok_of_try_ok hrCode ?_
  refine eq_ok_of_try_ok hrJt ?_
  refine eq_ok_of_try_ok hrJf ?_
  refine eq_ok_of_try_ok hrK rfl

/-- Exact characterization of `plan.validate_seccomp_trailer`: succeeds iff `1 ≤ seccomp_n ≤ 160` and the remaining bytes equal `8 * seccomp_n`. -/
theorem validate_seccomp_trailer_atOffset (data : Slice U8) (pos : Usize)
    (n : UInt32) (seccompBytes : Bytes)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty n)) seccompBytes) :
    ∃ seccompPos : Usize,
      seccompPos.val = pos.val + 4 ∧
      AtOffset data seccompPos seccompBytes [] ∧
      plan.validate_seccomp_trailer data pos =
        Result.ok
          (if 1 ≤ n.toNat ∧ n.toNat ≤ 160 ∧ seccompBytes.length = 8 * n.toNat then
            .Ok (⟨n.toBitVec⟩, seccompPos)
          else
            .Err plan.EINVAL) := by
  obtain ⟨seccompPos, hr, hp, hRem⟩ := read_u32_le_atOffset data pos n seccompBytes h
  have hRem' : AtOffset data seccompPos seccompBytes [] := by
    refine ⟨hRem.1, ?_⟩
    simpa using hRem.2
  refine ⟨seccompPos, hp, hRem', ?_⟩
  have hTot := atOffset_len_eq hRem'
  simp only [List.length_nil] at hTot
  have h8u : (8#usize).val = 8 := rfl
  have hnVal : (⟨n.toBitVec⟩ : U32).val = n.toNat := rfl
  have hMaxConst : plan.PS_SECCOMP_MAX_INSNS = 160#u32 := by simp [plan.PS_SECCOMP_MAX_INSNS]
  rw [plan.validate_seccomp_trailer]
  refine eq_ok_of_try_ok hr ?_
  change
    (if (⟨n.toBitVec⟩ : U32) = 0#u32 then Result.ok (core.result.Result.Err plan.EINVAL)
     else if (⟨n.toBitVec⟩ : U32) > plan.PS_SECCOMP_MAX_INSNS then
       Result.ok (core.result.Result.Err plan.EINVAL)
     else do
       let i ← lift (UScalar.cast .Usize (⟨n.toBitVec⟩ : U32))
       let seccomp_bytes ← i * 8#usize
       let i2 ← Slice.len data - seccompPos
       if i2 != seccomp_bytes then ok (core.result.Result.Err plan.EINVAL)
       else ok (core.result.Result.Ok ((⟨n.toBitVec⟩ : U32), seccompPos))) = _
  rw [hMaxConst]
  by_cases hz : (⟨n.toBitVec⟩ : U32) = 0#u32
  · have hzVal : n.toNat = 0 := by
      have h0 : (⟨n.toBitVec⟩ : U32).val = (0#u32).val := congrArg UScalar.val hz
      exact h0
    have hCond : ¬ (1 ≤ n.toNat ∧ n.toNat ≤ 160 ∧ seccompBytes.length = 8 * n.toNat) := by omega
    rw [if_true_eq hz, if_false_eq hCond]
  · have hGe1 : 1 ≤ n.toNat := by
      by_contra hNot
      apply hz
      apply UScalar.eq_of_val_eq
      change n.toNat = 0
      omega
    rw [if_false_eq hz]
    by_cases hGt : (⟨n.toBitVec⟩ : U32) > 160#u32
    · have hGtVal : 160 < n.toNat := by
        have h160 : (160#u32).val = 160 := rfl
        simpa [hnVal, h160] using hGt
      have hCond : ¬ (1 ≤ n.toNat ∧ n.toNat ≤ 160 ∧ seccompBytes.length = 8 * n.toNat) := by omega
      rw [if_true_eq hGt, if_false_eq hCond]
    · have hLe160 : n.toNat ≤ 160 := by
        have h160 : (160#u32).val = 160 := rfl
        have : ¬ (160 < n.toNat) := by simpa [hnVal, h160] using hGt
        omega
      rw [if_false_eq hGt]
      have hCastVal : (UScalar.cast .Usize (⟨n.toBitVec⟩ : U32) : Usize).val = n.toNat := by
        rw [u32_cast_usize_val, hnVal]
      obtain ⟨sb, hMul, hSb⟩ := usize_mul_ok
        (UScalar.cast .Usize (⟨n.toBitVec⟩ : U32)) 8#usize
        (by have := usize_max_ge_u32_max; change (UScalar.cast .Usize (⟨n.toBitVec⟩ : U32) : Usize).val * 8 ≤ Usize.max; omega)
      have hLenData : (Slice.len data).val = data.val.length := by simp
      obtain ⟨remBytes, hSub, hRemVal⟩ := usize_sub_ok (Slice.len data) seccompPos
        (by rw [hLenData]; omega)
      refine eq_ok_of_bind rfl ?_
      refine eq_ok_of_bind hMul ?_
      refine eq_ok_of_bind hSub ?_
      have hSbEq : sb.val = 8 * n.toNat := by
        rw [hSb, hCastVal, h8u, Nat.mul_comm]
      have hRemEq : remBytes.val = seccompBytes.length := by omega
      by_cases hNe : (remBytes != sb) = true
      · have hLenNe : seccompBytes.length ≠ 8 * n.toNat := by
          intro hEq
          have : remBytes = sb := by
            apply UScalar.eq_of_val_eq
            omega
          simp [this] at hNe
        have hCond : ¬ (1 ≤ n.toNat ∧ n.toNat ≤ 160 ∧ seccompBytes.length = 8 * n.toNat) := by
          intro hc; exact hLenNe hc.2.2
        rw [if_true_eq hNe, if_false_eq hCond]
      · have hNeF : (remBytes != sb) = false := Bool.eq_false_iff.mpr hNe
        have hLenEq : seccompBytes.length = 8 * n.toNat := by
          have : remBytes.val = sb.val := by simpa using hNe
          omega
        have hCond : 1 ≤ n.toNat ∧ n.toNat ≤ 160 ∧ seccompBytes.length = 8 * n.toNat :=
          ⟨hGe1, hLe160, hLenEq⟩
        rw [hNeF, if_false_eq Bool.false_ne_true, if_true_eq hCond]

end LeanSwe.ProcessSandbox.Init.Proofs

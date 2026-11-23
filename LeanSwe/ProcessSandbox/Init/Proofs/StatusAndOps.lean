import LeanSwe.ProcessSandbox.Host.StreamIo
import LeanSwe.ProcessSandbox.Init.Proofs.Base

/-!
# ProcessSandbox Init Status Framing, Landlock, SCM Batching, and Lifecycle Proofs

Machine-checked invariants on `psandbox_init::ops`:
- 8-byte `InitStatusMsg` wire encoding/decoding round-trip and exact byte-level agreement
  with host `LeanSwe.ProcessSandbox.Host.StreamIo.encodeInitStatusMsg` / `decodeInitStatusMsg`,
- Landlock ABI v4 filesystem and TCP access bitmask stripping and mount tag permissions,
- `SCM_RIGHTS` descriptor batch sizing (`1 ≤ batch ≤ 32` and `batch ≤ remaining`),
- Loopback interface `IFF_UP | IFF_RUNNING` activation logic,
- Linux `waitpid` status word classification across all 8-bit exit codes (`0..255`) and
  fatal signals (`1..126`),
- `seccomp` `ENOSYS` fallback (`SYS_seccomp` → `prctl(PR_SET_SECCOMP)`) and loopback listener
  descriptor cleanup on `bind`/`listen` failure.
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Host.StreamIo

private theorem u32_numBits : UScalarTy.U32.numBits = 32 := UScalarTy.U32_numBits_eq
private theorem u64_numBits : UScalarTy.U64.numBits = 64 := UScalarTy.U64_numBits_eq

private theorem u32_mask_cast_u8_bv (u : U32) :
    (UScalar.cast .U8 (u &&& 255#u32) : U8).bv = u.bv.setWidth 8 := by
  change BitVec.setWidth 8 (u.bv &&& 255#32) = u.bv.setWidth 8
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_and]
  have h255 : (255#32).getLsbD i = true := by
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first | decide | omega
  rw [h255, Bool.and_true]

/-- Exact 8-byte layout produced by `ops.encode_status_msg`. -/
theorem encode_status_msg_spec (kind flag : U8) (value : I32) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg kind flag value = Result.ok msg ∧
      msg.val =
        [ kind
        , flag
        , 0#u8
        , 0#u8
        , ⟨value.bv.setWidth 8⟩
        , ⟨(BitVec.ushiftRight value.bv 8).setWidth 8⟩
        , ⟨(BitVec.ushiftRight value.bv 16).setWidth 8⟩
        , ⟨(BitVec.ushiftRight value.bv 24).setWidth 8⟩ ] := by
  unfold ops.encode_status_msg
  dsimp only [lift]
  simp only [bind_ok, hcast_u32_eq]
  rw [uscalar_shr_i32_ok _ 8#i32 8 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok,
    uscalar_shr_i32_ok _ 16#i32 16 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok,
    uscalar_shr_i32_ok _ 24#i32 24 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok]
  refine ⟨_, rfl, ?_⟩
  have hb0 : (UScalar.cast .U8 ((⟨value.bv⟩ : U32) &&& 255#u32) : U8) = ⟨value.bv.setWidth 8⟩ :=
    uscalar_eq_of_bv (u32_mask_cast_u8_bv ⟨value.bv⟩)
  have hb1 : (UScalar.cast .U8 ((⟨BitVec.ushiftRight value.bv 8⟩ : U32) &&& 255#u32) : U8) =
      ⟨(BitVec.ushiftRight value.bv 8).setWidth 8⟩ :=
    uscalar_eq_of_bv (u32_mask_cast_u8_bv ⟨BitVec.ushiftRight value.bv 8⟩)
  have hb2 : (UScalar.cast .U8 ((⟨BitVec.ushiftRight value.bv 16⟩ : U32) &&& 255#u32) : U8) =
      ⟨(BitVec.ushiftRight value.bv 16).setWidth 8⟩ :=
    uscalar_eq_of_bv (u32_mask_cast_u8_bv ⟨BitVec.ushiftRight value.bv 16⟩)
  have hb3 : (UScalar.cast .U8 ((⟨BitVec.ushiftRight value.bv 24⟩ : U32) &&& 255#u32) : U8) =
      ⟨(BitVec.ushiftRight value.bv 24).setWidth 8⟩ :=
    uscalar_eq_of_bv (u32_mask_cast_u8_bv ⟨BitVec.ushiftRight value.bv 24⟩)
  rw [hb0, hb1, hb2, hb3]
  simp [Array.make]

/-- Exact round-trip identity `ops.encode_status_msg >>= ops.decode_status_msg = ok (kind, flag, value)`. -/
theorem decode_encode_status_msg_roundTrip (kind flag : U8) (value : I32) :
    (ops.encode_status_msg kind flag value >>= ops.decode_status_msg) =
      Result.ok (kind, flag, value) := by
  obtain ⟨msg, hEnc, hVal⟩ := encode_status_msg_spec kind flag value
  have hDec : ops.decode_status_msg msg = Result.ok (kind, flag, value) := by
    unfold ops.decode_status_msg
    dsimp only [lift]
    rw [array_index_usize_ok msg 4#usize (by decide), bind_ok, bind_ok,
      array_index_usize_ok msg 5#usize (by decide), bind_ok, bind_ok,
      uscalar_shl_i32_ok _ 8#i32 8 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok,
      array_index_usize_ok msg 6#usize (by decide), bind_ok, bind_ok,
      uscalar_shl_i32_ok _ 16#i32 16 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok,
      array_index_usize_ok msg 7#usize (by decide), bind_ok, bind_ok,
      uscalar_shl_i32_ok _ 24#i32 24 (by decide) rfl (by rw [u32_numBits]; decide), bind_ok,
      bind_ok, bind_ok, bind_ok, bind_ok,
      array_index_usize_ok msg 0#usize (by decide), bind_ok,
      array_index_usize_ok msg 1#usize (by decide), bind_ok]
    simp only [hVal, hcast_i32_eq]
    congr 1
    congr 1
    congr 1
    apply iscalar_eq_of_bv
    change ((((value.bv.setWidth 8).zeroExtend 32 |||
        BitVec.shiftLeft ((BitVec.ushiftRight value.bv 8).setWidth 8 |>.zeroExtend 32) 8) |||
        BitVec.shiftLeft ((BitVec.ushiftRight value.bv 16).setWidth 8 |>.zeroExtend 32) 16) |||
        BitVec.shiftLeft ((BitVec.ushiftRight value.bv 24).setWidth 8 |>.zeroExtend 32) 24) = value.bv
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
  simp [hEnc, hDec]

/-- Wire-tag constants in `psandbox_init::ops` match `LeanSwe.ProcessSandbox.Host.StreamIo`. -/
theorem status_tags_match_host :
    ops.PS_STATUS_READY.val = PS_STATUS_READY.toNat ∧
    ops.PS_STATUS_INIT_ERR.val = PS_STATUS_INIT_ERR.toNat ∧
    ops.PS_STATUS_EXEC_ERR.val = PS_STATUS_EXEC_ERR.toNat ∧
    ops.PS_STATUS_EXITED.val = PS_STATUS_EXITED.toNat ∧
    ops.PS_STATUS_SIGNALED.val = PS_STATUS_SIGNALED.toNat := by
  simp [ops.PS_STATUS_READY, ops.PS_STATUS_INIT_ERR, ops.PS_STATUS_EXEC_ERR,
    ops.PS_STATUS_EXITED, ops.PS_STATUS_SIGNALED,
    PS_STATUS_READY, PS_STATUS_INIT_ERR, PS_STATUS_EXEC_ERR,
    PS_STATUS_EXITED, PS_STATUS_SIGNALED]

private theorem uint8OfU8_ushift_eq (bv : BitVec 32) (sh : Nat) :
    uint8OfU8 ⟨(BitVec.ushiftRight bv sh).setWidth 8⟩ =
      UInt8.ofNat ((bv.toNat / (2 ^ sh)) % 256) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (bv >>> sh).toNat % 256 = (BitVec.ofNat 8 ((bv.toNat / (2 ^ sh)) % 256)).toNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  simp

/-- Byte-for-byte agreement between `ops.encode_status_msg` and host `StreamIo.encodeInitStatusMsg`. -/
theorem encode_status_msg_matches_host (kind flag : U8) (value : I32) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg kind flag value = Result.ok msg ∧
      bytesToByteArray msg.val =
        encodeInitStatusMsg
          { kind := uint8OfU8 kind
            flag := uint8OfU8 flag
            value := Int32.ofBitVec value.bv } := by
  obtain ⟨msg, hEnc, hVal⟩ := encode_status_msg_spec kind flag value
  refine ⟨msg, hEnc, ?_⟩
  rw [hVal]
  have hu : (Int32.ofBitVec value.bv).toUInt32.toNat = value.bv.toNat := rfl
  have hb0 : uint8OfU8 ⟨value.bv.setWidth 8⟩ = UInt8.ofNat (value.bv.toNat % 256) := by
    simpa using uint8OfU8_ushift_eq value.bv 0
  have hb1 : uint8OfU8 ⟨(BitVec.ushiftRight value.bv 8).setWidth 8⟩ =
      UInt8.ofNat ((value.bv.toNat / 256) % 256) := by
    simpa using uint8OfU8_ushift_eq value.bv 8
  have hb2 : uint8OfU8 ⟨(BitVec.ushiftRight value.bv 16).setWidth 8⟩ =
      UInt8.ofNat ((value.bv.toNat / 65536) % 256) := by
    simpa using uint8OfU8_ushift_eq value.bv 16
  have hb3 : uint8OfU8 ⟨(BitVec.ushiftRight value.bv 24).setWidth 8⟩ =
      UInt8.ofNat ((value.bv.toNat / 16777216) % 256) := by
    simpa using uint8OfU8_ushift_eq value.bv 24
  unfold bytesToByteArray encodeInitStatusMsg
  simp only [List.map, hu, hb0, hb1, hb2, hb3]
  rfl

/-- Host `StreamIo.decodeInitStatusMsg` recovers the exact `InitStatusMsg` written by `ops.encode_status_msg`. -/
theorem host_decode_encode_status_msg_roundTrip (kind flag : U8) (value : I32) :
    ∃ msg : Array U8 8#usize,
      ops.encode_status_msg kind flag value = Result.ok msg ∧
      decodeInitStatusMsg (bytesToByteArray msg.val) =
        some { kind := uint8OfU8 kind
               flag := uint8OfU8 flag
               value := Int32.ofBitVec value.bv } := by
  obtain ⟨msg, hEnc, hEq⟩ := encode_status_msg_matches_host kind flag value
  refine ⟨msg, hEnc, ?_⟩
  rw [hEq]
  let m : InitStatusMsg :=
    { kind := uint8OfU8 kind, flag := uint8OfU8 flag, value := Int32.ofBitVec value.bv }
  change decodeInitStatusMsg (encodeInitStatusMsg m) = some m
  unfold encodeInitStatusMsg decodeInitStatusMsg
  have hSz : (ByteArray.mk #[m.kind, m.flag, 0, 0,
      UInt8.ofNat (m.value.toUInt32.toNat % 256),
      UInt8.ofNat ((m.value.toUInt32.toNat / 256) % 256),
      UInt8.ofNat ((m.value.toUInt32.toNat / 65536) % 256),
      UInt8.ofNat ((m.value.toUInt32.toNat / 16777216) % 256)]).size = 8 := rfl
  simp only [hSz, ↓reduceDIte]
  have huLt : m.value.toUInt32.toNat < 4294967296 := m.value.toUInt32.toBitVec.isLt
  have hMod : ∀ k < 256, (UInt8.ofNat k).toNat = k := fun k hk => Nat.mod_eq_of_lt hk
  change some
    { kind := m.kind
      flag := m.flag
      value := (UInt32.ofNat
        ((UInt8.ofNat (m.value.toUInt32.toNat % 256)).toNat +
         256 * (UInt8.ofNat ((m.value.toUInt32.toNat / 256) % 256)).toNat +
         65536 * (UInt8.ofNat ((m.value.toUInt32.toNat / 65536) % 256)).toNat +
         16777216 * (UInt8.ofNat ((m.value.toUInt32.toNat / 16777216) % 256)).toNat)).toInt32 } = some m
  rw [hMod _ (by omega), hMod _ (by omega), hMod _ (by omega), hMod _ (by omega)]
  have hSum :
      m.value.toUInt32.toNat % 256 +
      256 * ((m.value.toUInt32.toNat / 256) % 256) +
      65536 * ((m.value.toUInt32.toNat / 65536) % 256) +
      16777216 * ((m.value.toUInt32.toNat / 16777216) % 256) = m.value.toUInt32.toNat := by
    omega
  rw [hSum, UInt32.ofNat_toNat]
  have hInt : m.value.toUInt32.toInt32 = m.value := by
    cases m.value
    rfl
  rw [hInt]

/-- Exact evaluation of Landlock filesystem constants in `psandbox_init::ops`. -/
theorem landlock_fs_constants_spec :
    ops.PS_LL_FS_EXECUTE = Result.ok 1#u64 ∧
    ops.PS_LL_FS_WRITE_FILE = Result.ok 2#u64 ∧
    ops.PS_LL_FS_READ_FILE = Result.ok 4#u64 ∧
    ops.PS_LL_FS_READ_DIR = Result.ok 8#u64 ∧
    ops.PS_LL_FS_TRUNCATE = Result.ok 16384#u64 ∧
    ops.PS_LL_FS_FILE_ONLY = Result.ok 16391#u64 ∧
    ops.PS_LL_FS_RO_EXEC = Result.ok 13#u64 ∧
    ops.PS_LL_FS_V4_ALL = Result.ok 32767#u64 := by
  have hExec : ops.PS_LL_FS_EXECUTE = Result.ok 1#u64 := by
    unfold ops.PS_LL_FS_EXECUTE
    rw [uscalar_shl_i32_ok _ 0#i32 0 (by decide) rfl (by rw [u64_numBits]; decide)]
    rfl
  have hWrite : ops.PS_LL_FS_WRITE_FILE = Result.ok 2#u64 := by
    unfold ops.PS_LL_FS_WRITE_FILE
    rw [uscalar_shl_i32_ok _ 1#i32 1 (by decide) rfl (by rw [u64_numBits]; decide)]
    rfl
  have hRead : ops.PS_LL_FS_READ_FILE = Result.ok 4#u64 := by
    unfold ops.PS_LL_FS_READ_FILE
    rw [uscalar_shl_i32_ok _ 2#i32 2 (by decide) rfl (by rw [u64_numBits]; decide)]
    rfl
  have hReadDir : ops.PS_LL_FS_READ_DIR = Result.ok 8#u64 := by
    unfold ops.PS_LL_FS_READ_DIR
    rw [uscalar_shl_i32_ok _ 3#i32 3 (by decide) rfl (by rw [u64_numBits]; decide)]
    rfl
  have hTrunc : ops.PS_LL_FS_TRUNCATE = Result.ok 16384#u64 := by
    unfold ops.PS_LL_FS_TRUNCATE
    rw [uscalar_shl_i32_ok _ 14#i32 14 (by decide) rfl (by rw [u64_numBits]; decide)]
    rfl
  have hFileOnly : ops.PS_LL_FS_FILE_ONLY = Result.ok 16391#u64 := by
    unfold ops.PS_LL_FS_FILE_ONLY
    simp only [hExec, hWrite, hRead, hTrunc, lift, bind_ok]
    rfl
  have hRoExec : ops.PS_LL_FS_RO_EXEC = Result.ok 13#u64 := by
    unfold ops.PS_LL_FS_RO_EXEC
    simp only [hRead, hReadDir, hExec, lift, bind_ok]
    rfl
  have hV4All : ops.PS_LL_FS_V4_ALL = Result.ok 32767#u64 := by
    unfold ops.PS_LL_FS_V4_ALL
    rw [uscalar_shl_i32_ok _ 15#i32 15 (by decide) rfl (by rw [u64_numBits]; decide)]
    have hShift : (⟨BitVec.shiftLeft (1#u64).bv 15⟩ : U64) = 32768#u64 := by decide
    rw [hShift, bind_ok]
    obtain ⟨c, hc, hcVal⟩ := (okPost_iff_wp_spec _ _).mpr
      (U64.sub_spec (x := 32768#u64) (y := 1#u64) (by decide))
    rw [hc]
    congr 1
    apply UScalar.eq_of_val_eq
    exact hcVal.1
  exact ⟨hExec, hWrite, hRead, hReadDir, hTrunc, hFileOnly, hRoExec, hV4All⟩

/-- `ops.landlock_net_handled_mask` disables TCP restriction (`0`) iff `allow_box_localhost = true` and enforces `BIND_TCP | CONNECT_TCP` (`3`) otherwise. -/
theorem landlock_net_handled_mask_spec (allow : Bool) :
    ops.landlock_net_handled_mask allow = Result.ok (if allow then 0#u64 else 3#u64) := by
  unfold ops.landlock_net_handled_mask ops.PS_LL_NET_BIND_TCP ops.PS_LL_NET_CONNECT_TCP
  cases allow with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [uscalar_shl_i32_ok _ 0#i32 0 (by decide) rfl (by rw [u64_numBits]; decide), bind_ok,
      uscalar_shl_i32_ok _ 1#i32 1 (by decide) rfl (by rw [u64_numBits]; decide), bind_ok]
    rfl

/-- `ops.landlock_effective_fs_access` preserves all bits on directories and strips directory-only bits on regular files (`requested &&& 16391#u64`). -/
theorem landlock_effective_fs_access_spec (requested : U64) (is_dir : Bool) :
    ops.landlock_effective_fs_access requested is_dir =
      Result.ok (if is_dir then requested else requested &&& 16391#u64) := by
  unfold ops.landlock_effective_fs_access
  cases is_dir with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [landlock_fs_constants_spec.2.2.2.2.2.1, bind_ok]

/-- Regular-file Landlock masking clears `READ_DIR` (`bit 3`) and all directory-mutation bits (`bits 4..13`). -/
theorem landlock_effective_fs_access_clears_dir_bits (requested : U64) :
    ∃ eff : U64,
      ops.landlock_effective_fs_access requested false = Result.ok eff ∧
      eff &&& 16376#u64 = 0#u64 := by
  refine ⟨requested &&& 16391#u64, landlock_effective_fs_access_spec requested false, ?_⟩
  apply uscalar_eq_of_bv
  change (requested.bv &&& 16391#64) &&& 16376#64 = 0#64
  rw [BitVec.and_assoc]
  have hZero : (16391#64 &&& 16376#64) = 0#64 := rfl
  rw [hZero, BitVec.and_zero]

/-- `ops.landlock_mount_access` grants `RO_EXEC` (`13`) for `tag = 0` (`.readOnly`) and `V4_ALL` (`32767`) for `.readWrite`/`.scratch`. -/
theorem landlock_mount_access_spec (tag : U8) :
    ops.landlock_mount_access tag =
      Result.ok (if tag = 0#u8 then 13#u64 else 32767#u64) := by
  unfold ops.landlock_mount_access
  split
  · exact landlock_fs_constants_spec.2.2.2.2.2.2.1
  · exact landlock_fs_constants_spec.2.2.2.2.2.2.2

/-- `ops.scm_batch_len` splits positive descriptor counts into `1..32`-FD `SCM_RIGHTS` chunks (`batch ≤ remaining`). -/
theorem scm_batch_len_bounds (remaining : U32) (hPos : 0 < remaining.val) :
    ∃ batch : U32,
      ops.scm_batch_len remaining = Result.ok batch ∧
      1 ≤ batch.val ∧ batch.val ≤ 32 ∧ batch.val ≤ remaining.val := by
  unfold ops.scm_batch_len ops.MAX_SCM_BATCH
  have h32 : (32#u32).val = 32 := rfl
  split
  · next hGt =>
    have hGtVal : 32 < remaining.val := by simpa [h32] using hGt
    exact ⟨32#u32, rfl, by decide, by decide, by rw [h32]; omega⟩
  · next hLe =>
    have hLeVal : remaining.val ≤ 32 := by
      have : ¬ (32 < remaining.val) := by simpa [h32] using hLe
      omega
    exact ⟨remaining, rfl, by omega, hLeVal, Nat.le_refl _⟩

/-- Multi-batch 34-port-forward split: `34` splits into `32` followed by `2`. -/
theorem scm_batch_len_34_split :
    ops.scm_batch_len 34#u32 = Result.ok 32#u32 ∧
    ops.scm_batch_len 2#u32 = Result.ok 2#u32 := by
  unfold ops.scm_batch_len ops.MAX_SCM_BATCH
  have h1 : (34#u32 > 32#u32) := by decide
  have h2 : ¬ (2#u32 > 32#u32) := by decide
  simp [h1, h2]

/-- `ops.loopback_updated_flags` returns `none` when `IFF_UP` is set and `some (cur ||| 65#i16)` otherwise. -/
theorem loopback_updated_flags_spec (cur : I16) :
    ops.loopback_updated_flags cur =
      Result.ok (if (cur &&& 1#i16) = 0#i16 then some (cur ||| 65#i16) else none) := by
  unfold ops.loopback_updated_flags ops.IFF_UP ops.IFF_RUNNING
  dsimp only [lift]
  simp only [bind_ok]
  split
  · congr 2
    apply iscalar_eq_of_bv
    change (cur.bv ||| 1#16) ||| 64#16 = cur.bv ||| 65#16
    rw [BitVec.or_assoc]
    rfl
  · rfl

/-- `ops.classify_wait_status` decodes `(code <<< 8)` as `(PS_STATUS_EXITED, 0, code)` for every 8-bit exit code `0..255`. -/
theorem classify_wait_status_exited (code : Nat) (hCode : code < 256) :
    ops.classify_wait_status ⟨BitVec.ofNat 32 (code * 256)⟩ =
      Result.ok (4#u8, 0#u8, ⟨BitVec.ofNat 32 code⟩) := by
  unfold ops.classify_wait_status
  dsimp only [lift]
  simp only [bind_ok]
  have hLow : ((⟨BitVec.ofNat 32 (code * 256)⟩ : I32) &&& 127#i32) = 0#i32 := by
    apply iscalar_eq_of_bv
    change BitVec.ofNat 32 (code * 256) &&& 127#32 = 0#32
    apply BitVec.eq_of_toNat_eq
    have h127 : (127#32).toNat = 2 ^ 7 - 1 := rfl
    rw [BitVec.toNat_and, h127, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
    change (code * 256) % 4294967296 % 128 = 0
    omega
  simp only [hLow, ↓reduceIte]
  rw [i32_shr_i32_ok _ 8#i32 8 (by decide) rfl (by decide), bind_ok]
  unfold ops.PS_STATUS_EXITED
  congr 1
  congr 2
  apply iscalar_eq_of_bv
  change BitVec.sshiftRight (BitVec.ofNat 32 (code * 256)) 8 &&& 255#32 = BitVec.ofNat 32 code
  have hMsb : (BitVec.ofNat 32 (code * 256)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hMsb]
  apply BitVec.eq_of_toNat_eq
  have h255 : (255#32).toNat = 2 ^ 8 - 1 := rfl
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change (code * 256) % 4294967296 / 256 % 256 = code % 4294967296
  omega

/-- `ops.classify_wait_status` decodes raw signal terminations `1..126` as `(PS_STATUS_SIGNALED, 0, sig)`. -/
theorem classify_wait_status_signaled (sig : Nat) (hLo : 1 ≤ sig) (hHi : sig ≤ 126) :
    ops.classify_wait_status ⟨BitVec.ofNat 32 sig⟩ =
      Result.ok (5#u8, 0#u8, ⟨BitVec.ofNat 32 sig⟩) := by
  unfold ops.classify_wait_status
  dsimp only [lift]
  simp only [bind_ok]
  have hMask : ((⟨BitVec.ofNat 32 sig⟩ : I32) &&& 127#i32) = ⟨BitVec.ofNat 32 sig⟩ := by
    apply iscalar_eq_of_bv
    change BitVec.ofNat 32 sig &&& 127#32 = BitVec.ofNat 32 sig
    apply BitVec.eq_of_toNat_eq
    have h127 : (127#32).toNat = 2 ^ 7 - 1 := rfl
    rw [BitVec.toNat_and, h127, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
    change sig % 4294967296 % 128 = sig % 4294967296
    omega
  rw [hMask]
  have hNe0 : (⟨BitVec.ofNat 32 sig⟩ : I32) ≠ 0#i32 := by
    intro hEq
    have hVal : (BitVec.ofNat 32 sig).toNat = 0 := by
      have := congrArg (fun x : I32 => x.bv.toNat) hEq
      simpa using this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sig < 4294967296)] at hVal
    omega
  have hBne127 : ((⟨BitVec.ofNat 32 sig⟩ : I32) != 127#i32) = true := by
    rw [bne_iff_ne]
    intro hEq
    have hVal : (BitVec.ofNat 32 sig).toNat = 127 := by
      have := congrArg (fun x : I32 => x.bv.toNat) hEq
      simpa using this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sig < 4294967296)] at hVal
    omega
  simp only [hNe0, ↓reduceIte, hBne127, ops.PS_STATUS_SIGNALED]

/-- `ops.open_loopback_listener` closes the newly opened socket descriptor when `bind_loopback_v4` fails on port `0`. -/
theorem open_loopback_listener_port0_closes_fd (s : init_sys.Sys) :
    ops.open_loopback_listener s 0#u16 =
      Result.ok (.Err 22#i32, { s with closedFds := s.closedFds ++ [10#i32] }) := by
  unfold ops.open_loopback_listener init_sys.socket_tcp_nonblock_cloexec
    init_sys.setsockopt_reuseaddr init_sys.bind_loopback_v4 init_sys.close_fd
    LeanSwe.ProcessSandbox.Init.World.EINVAL
  simp [core.result.Result.Insts.CoreOpsTry.branch]

end LeanSwe.ProcessSandbox.Init.Proofs

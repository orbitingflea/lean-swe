import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Api
import LeanSwe.PostFork.Aeneas.Bridge
import LeanSwe.PostFork.Proofs.Base

/-!
Kernel proofs for pure encoders, `/proc/self/fd` dirent parsing, and kernel edge invariants:
- `test_postfork_wireEncoder_uniformAndRoundTrip` (`Core.AllPass` + `Core.CanReach`),
- `test_postfork_parseDirentName_canonicalDecimalAndRoundTrip` (`Core.AllPass` + `Core.CanReach`),
- `test_postfork_worldModel_linuxKernelEdgeInvariants` (`Core.AllPass` + `Core.CanReach`).
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

section WireEncoders

/-- Byte extraction from a `U32` shifted right by `0`, `8`, `16`, or `24` bits. -/
theorem u32_byte_shift (u : U32) (sh : Nat) (hsh : sh = 0 ∨ sh = 8 ∨ sh = 16 ∨ sh = 24) :
    ((u.bv >>> sh) &&& 255#32).extractLsb' 0 8 = u.bv.extractLsb' sh 8 := by
  rcases hsh with hsh | hsh | hsh | hsh <;> subst hsh <;> (
    ext i hi
    have h255 : (255#32).getLsbD i = true := by
      have : i ∈ List.range 8 := List.mem_range.mpr hi
      revert i; decide
    simp [h255])

/-- Right shift of a `U32` by a constant non-negative shift strictly below `32`. -/
theorem u32_shr_lt32 (u : U32) (sh : I32) (h0 : 0 ≤ (↑sh : Int)) (h32 : sh.toNat < 32) :
    u >>> sh = Result.ok ⟨BitVec.ushiftRight u.bv sh.toNat⟩ := by
  change UScalar.shiftRight_IScalar u sh = _
  unfold UScalar.shiftRight_IScalar
  have hge : (↑sh : Int) ≥ 0 := h0
  simp only [hge, ↓reduceIte]
  unfold UScalar.shiftRight
  have hlt : sh.toNat < UScalarTy.U32.numBits := by
    rw [UScalarTy.U32_numBits_eq]; exact h32
  simp only [hlt, ↓reduceIte]

private theorem uscalar_eq_of_bv {ty : UScalarTy} {x y : UScalar ty} (h : x.bv = y.bv) : x = y := by
  apply UScalar.eq_of_val_eq
  change x.bv.toNat = y.bv.toNat
  rw [h]

private theorem hcast_u32_bv (v : I32) : (IScalar.hcast .U32 v).bv = v.bv := by
  have h : (IScalar.hcast .U32 v : U32).bv = BitVec.signExtend 32 v.bv := rfl
  rw [h]
  ext i hi
  simp

private theorem hcast_u32_eq (v : I32) : (IScalar.hcast .U32 v : U32) = ⟨v.bv⟩ :=
  uscalar_eq_of_bv (hcast_u32_bv v)

/-- Converting `U32` masked with `255#u32` to `U8` extracts its low byte. -/
theorem uscalar_cast_u8_mask (u : U32) :
    (UScalar.cast .U8 (u &&& 255#u32) : U8) =
      ⟨(u.bv &&& 255#32).extractLsb' 0 8⟩ := by
  apply uscalar_eq_of_bv
  change BitVec.setWidth 8 (u.bv &&& 255#32) = (u.bv &&& 255#32).extractLsb' 0 8
  ext i hi
  have h8 : (255#8)[i] = true := by
    have hList : ∀ j ∈ List.range 8, (255#8)[j]! = true := by decide
    simpa [BitVec.getElem!_eq_getElem, hi] using hList i (List.mem_range.mpr hi)
  have h32 : (255#32).getLsbD i = true := by
    have hList : ∀ j ∈ List.range 8, (255#32).getLsbD j = true := by decide
    exact hList i (List.mem_range.mpr hi)
  simp [BitVec.getElem_setWidth, h8, h32]

private theorem cast_shr_byte (w : I32) (sh : Nat) (hsh : sh = 0 ∨ sh = 8 ∨ sh = 16 ∨ sh = 24) :
    (UScalar.cast .U8 ((⟨BitVec.ushiftRight w.bv sh⟩ : U32) &&& 255#u32) : U8) =
      ⟨w.bv.extractLsb' sh 8⟩ := by
  rw [uscalar_cast_u8_mask]
  apply uscalar_eq_of_bv
  exact u32_byte_shift ⟨w.bv⟩ sh hsh

private theorem cast_low_byte (w : I32) :
    (UScalar.cast .U8 ((⟨w.bv⟩ : U32) &&& 255#u32) : U8) = ⟨w.bv.extractLsb' 0 8⟩ :=
  cast_shr_byte w 0 (Or.inl rfl)

private theorem u32_shr_const (v : I32) (sh : I32) (n : Nat)
    (h0 : 0 ≤ (↑sh : Int)) (hn : sh.toNat = n) (hlt : n < 32) :
    IScalar.hcast .U32 v >>> sh = Result.ok ⟨BitVec.ushiftRight v.bv n⟩ := by
  rw [hcast_u32_eq v, u32_shr_lt32 _ sh h0 (by omega), hn]

/-- Byte-level exactness for `child.encode_i32_le`. -/
theorem encode_i32_le_spec (v : I32) :
    OkPost (postfork.child.encode_i32_le v) (fun a => a.val = expectedI32LeBytes v) := by
  unfold postfork.child.encode_i32_le
  dsimp only [lift]
  simp only [bind_ok]
  rw [u32_shr_const v 8#i32 8 (by decide) rfl (by decide), bind_ok,
    u32_shr_const v 16#i32 16 (by decide) rfl (by decide), bind_ok,
    u32_shr_const v 24#i32 24 (by decide) rfl (by decide), bind_ok,
    hcast_u32_eq v]
  refine ⟨_, rfl, ?_⟩
  rw [cast_low_byte v, cast_shr_byte v 8 (Or.inr (Or.inl rfl)),
    cast_shr_byte v 16 (Or.inr (Or.inr (Or.inl rfl))),
    cast_shr_byte v 24 (Or.inr (Or.inr (Or.inr rfl)))]
  simp [Array.make, expectedI32LeBytes]

/-- Byte-level exactness for `child.encode_failure_report`. -/
theorem encode_failure_report_spec (stage : U8) (errnum : I32) :
    OkPost (postfork.child.encode_failure_report stage errnum)
      (fun a => a.val = expectedFailureWireBytes stage errnum) := by
  unfold postfork.child.encode_failure_report
  dsimp only [lift]
  simp only [bind_ok]
  rw [u32_shr_const errnum 8#i32 8 (by decide) rfl (by decide), bind_ok,
    u32_shr_const errnum 16#i32 16 (by decide) rfl (by decide), bind_ok,
    u32_shr_const errnum 24#i32 24 (by decide) rfl (by decide), bind_ok,
    hcast_u32_eq errnum, postfork.child.WIRE_MAGIC, postfork.child.WIRE_VERSION]
  refine ⟨_, rfl, ?_⟩
  rw [cast_low_byte errnum, cast_shr_byte errnum 8 (Or.inr (Or.inl rfl)),
    cast_shr_byte errnum 16 (Or.inr (Or.inr (Or.inl rfl))),
    cast_shr_byte errnum 24 (Or.inr (Or.inr (Or.inr rfl)))]
  simp [Array.make, expectedFailureWireBytes, expectedI32LeBytes]

private theorem u8_ofNat_lt_toNat (n : Nat) (hn : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

/-- Round-trip proof for pure `PostFork.Model.encodeFailureReport` and `PostFork.Model.decodeChildFailure`. -/
theorem decodeChildFailure_encode_roundTrip
    (fStage : FailureStage) (errU : UInt32)
    (hStage : fStage ≠ .wireTruncated)
    (hLo : 1 ≤ errU.toNat) (hHi : errU.toNat ≤ 4095) :
    LeanSwe.PostFork.Model.decodeChildFailure
        (LeanSwe.PostFork.Model.encodeFailureReport fStage errU) =
      some { stage := fStage, errno := errU } := by
  have hNorm : LeanSwe.PostFork.Model.normalizeWireErrno errU = errU := by
    unfold LeanSwe.PostFork.Model.normalizeWireErrno
    have hb : (decide (1 ≤ errU.toNat) && decide (errU.toNat ≤ 4095)) = true := by
      simp [hLo, hHi]
    simp [hb]
  have hu : errU.toNat ≤ 4095 := hHi
  have hTag :
      ∃ tag : UInt8,
        LeanSwe.PostFork.Model.FailureStage.toTag? fStage = some tag ∧
        LeanSwe.PostFork.Model.FailureStage.ofTag? tag = some fStage := by
    cases fStage <;> simp [LeanSwe.PostFork.Model.FailureStage.toTag?,
      LeanSwe.PostFork.Model.FailureStage.ofTag?] at hStage ⊢ <;> decide
  rcases hTag with ⟨tag, hTo, hOf⟩
  unfold LeanSwe.PostFork.Model.encodeFailureReport LeanSwe.PostFork.Model.decodeChildFailure
  rw [hTo, hNorm]
  dsimp only [Option.getD]
  have hsz : (ByteArray.mk #[LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION, tag, 0,
      UInt8.ofNat (errU.toNat % 256), UInt8.ofNat ((errU.toNat / 256) % 256),
      UInt8.ofNat ((errU.toNat / 65536) % 256), UInt8.ofNat ((errU.toNat / 16777216) % 256)]).size = 8 := rfl
  simp only [hsz, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
  change (if LeanSwe.PostFork.Model.WIRE_MAGIC != LeanSwe.PostFork.Model.WIRE_MAGIC ||
      LeanSwe.PostFork.Model.WIRE_VERSION != LeanSwe.PostFork.Model.WIRE_VERSION ||
      (0 : UInt8) != 0 then _ else
      match LeanSwe.PostFork.Model.FailureStage.ofTag? tag with
      | none => _
      | some stage => _) = _
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hOf]
  have hb4 : (ByteArray.mk #[LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION, tag, 0,
      UInt8.ofNat (errU.toNat % 256), UInt8.ofNat ((errU.toNat / 256) % 256),
      UInt8.ofNat ((errU.toNat / 65536) % 256), UInt8.ofNat ((errU.toNat / 16777216) % 256)]).get! 4 =
      UInt8.ofNat (errU.toNat % 256) := rfl
  have hb5 : (ByteArray.mk #[LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION, tag, 0,
      UInt8.ofNat (errU.toNat % 256), UInt8.ofNat ((errU.toNat / 256) % 256),
      UInt8.ofNat ((errU.toNat / 65536) % 256), UInt8.ofNat ((errU.toNat / 16777216) % 256)]).get! 5 =
      UInt8.ofNat ((errU.toNat / 256) % 256) := rfl
  have hb6 : (ByteArray.mk #[LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION, tag, 0,
      UInt8.ofNat (errU.toNat % 256), UInt8.ofNat ((errU.toNat / 256) % 256),
      UInt8.ofNat ((errU.toNat / 65536) % 256), UInt8.ofNat ((errU.toNat / 16777216) % 256)]).get! 6 =
      UInt8.ofNat ((errU.toNat / 65536) % 256) := rfl
  have hb7 : (ByteArray.mk #[LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION, tag, 0,
      UInt8.ofNat (errU.toNat % 256), UInt8.ofNat ((errU.toNat / 256) % 256),
      UInt8.ofNat ((errU.toNat / 65536) % 256), UInt8.ofNat ((errU.toNat / 16777216) % 256)]).get! 7 =
      UInt8.ofNat ((errU.toNat / 16777216) % 256) := rfl
  rw [hb4, hb5, hb6, hb7]
  rw [u8_ofNat_lt_toNat _ (by omega), u8_ofNat_lt_toNat _ (by omega),
    u8_ofNat_lt_toNat _ (by omega), u8_ofNat_lt_toNat _ (by omega)]
  have hRe : errU.toNat % 256 + 256 * ((errU.toNat / 256) % 256) +
      65536 * ((errU.toNat / 65536) % 256) + 16777216 * ((errU.toNat / 16777216) % 256) = errU.toNat := by
    omega
  rw [hRe]
  have hIn : (decide (1 ≤ errU.toNat) && decide (errU.toNat ≤ 4095)) = true := by simp [hLo, hHi]
  simp only [hIn, ↓reduceIte, UInt32.ofNat_toNat]

private theorem i32_bv_toNat_eq_toNat_of_pos (v : I32) (hLo : 1 ≤ v.val) :
    v.bv.toNat = v.toNat := by
  have h1 : (v.val : Int) = v.bv.toInt := rfl
  have h2 : v.toNat = v.val.toNat := rfl
  have h3 := BitVec.toInt_eq_toNat_cond v.bv
  have hlt : 2 * v.bv.toNat < 2 ^ 32 := by
    by_contra hge
    simp only [hge, ↓reduceIte] at h3
    have hpow : v.bv.toNat < 2 ^ 32 := v.bv.isLt
    omega
  simp only [hlt, ↓reduceIte] at h3
  omega

private theorem stageToU8_toNat_eq_tag (fStage : FailureStage) (hStage : fStage ≠ .wireTruncated) :
    UInt8.ofNat (LeanSwe.PostFork.Aeneas.Bridge.stageToU8 fStage).bv.toNat =
      (LeanSwe.PostFork.Model.FailureStage.toTag? fStage).getD LeanSwe.PostFork.Model.STAGE_EXECVE := by
  cases fStage <;> simp [LeanSwe.PostFork.Aeneas.Bridge.stageToU8,
    LeanSwe.PostFork.Model.FailureStage.toTag?] at hStage ⊢ <;> rfl

/-- Exact wire-level refinement between Aeneas `expectedFailureWireBytes` and pure `PostFork.Model.encodeFailureReport`. -/
theorem bytesToByteArray_expectedFailureWireBytes_eq_model
    (fStage : FailureStage) (errnum : I32)
    (hStage : fStage ≠ .wireTruncated)
    (hLo : 1 ≤ errnum.val) (hHi : errnum.val ≤ 4095) :
    LeanSwe.PostFork.Aeneas.Bridge.bytesToByteArray
        (expectedFailureWireBytes (LeanSwe.PostFork.Aeneas.Bridge.stageToU8 fStage) errnum) =
      LeanSwe.PostFork.Model.encodeFailureReport fStage (UInt32.ofNat errnum.toNat) := by
  have hToNatLo : 1 ≤ errnum.toNat := by
    have : errnum.toNat = errnum.val.toNat := rfl
    omega
  have hToNatHi : errnum.toNat ≤ 4095 := by
    have : errnum.toNat = errnum.val.toNat := rfl
    omega
  have hBvNat : errnum.bv.toNat = errnum.toNat := i32_bv_toNat_eq_toNat_of_pos errnum hLo
  have hU32Nat : (UInt32.ofNat errnum.toNat).toNat = errnum.toNat := by
    simp [Nat.mod_eq_of_lt (by omega : errnum.toNat < 4294967296)]
  have hNorm :
      LeanSwe.PostFork.Model.normalizeWireErrno (UInt32.ofNat errnum.toNat) =
        UInt32.ofNat errnum.toNat := by
    unfold LeanSwe.PostFork.Model.normalizeWireErrno
    simp only [hU32Nat, hToNatLo, hToNatHi, decide_true, Bool.and_self, ↓reduceIte]
  have he0 : (errnum.bv.extractLsb' 0 8).toNat = errnum.toNat % 256 := by
    change (errnum.bv.toNat >>> 0) % 256 = errnum.toNat % 256
    rw [hBvNat]
    simp
  have he1 : (errnum.bv.extractLsb' 8 8).toNat = (errnum.toNat / 256) % 256 := by
    change (errnum.bv.toNat >>> 8) % 256 = (errnum.toNat / 256) % 256
    rw [hBvNat, Nat.shiftRight_eq_div_pow]
  have he2 : (errnum.bv.extractLsb' 16 8).toNat = (errnum.toNat / 65536) % 256 := by
    change (errnum.bv.toNat >>> 16) % 256 = (errnum.toNat / 65536) % 256
    rw [hBvNat, Nat.shiftRight_eq_div_pow]
  have he3 : (errnum.bv.extractLsb' 24 8).toNat = (errnum.toNat / 16777216) % 256 := by
    change (errnum.bv.toNat >>> 24) % 256 = (errnum.toNat / 16777216) % 256
    rw [hBvNat, Nat.shiftRight_eq_div_pow]
  unfold LeanSwe.PostFork.Aeneas.Bridge.bytesToByteArray expectedFailureWireBytes expectedI32LeBytes
    LeanSwe.PostFork.Model.encodeFailureReport
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  rw [stageToU8_toNat_eq_tag fStage hStage, hNorm, hU32Nat, he0, he1, he2, he3]
  rfl

private theorem model_wire_constants_match_aeneas :
    LeanSwe.PostFork.Model.WIRE_MAGIC.toNat = postfork.child.WIRE_MAGIC.val ∧
    LeanSwe.PostFork.Model.WIRE_VERSION.toNat = postfork.child.WIRE_VERSION.val ∧
    LeanSwe.PostFork.Model.STAGE_VALIDATE.toNat = postfork.child.STAGE_VALIDATE.val ∧
    LeanSwe.PostFork.Model.STAGE_PROCESS_GROUP.toNat = postfork.child.STAGE_PROCESS_GROUP.val ∧
    LeanSwe.PostFork.Model.STAGE_SIGNAL_RESET.toNat = postfork.child.STAGE_SIGNAL_RESET.val ∧
    LeanSwe.PostFork.Model.STAGE_FD_SETUP.toNat = postfork.child.STAGE_FD_SETUP.val ∧
    LeanSwe.PostFork.Model.STAGE_CLOSE_UNKEPT.toNat = postfork.child.STAGE_CLOSE_UNKEPT.val ∧
    LeanSwe.PostFork.Model.STAGE_CHDIR.toNat = postfork.child.STAGE_CHDIR.val ∧
    LeanSwe.PostFork.Model.STAGE_EXECVE.toNat = postfork.child.STAGE_EXECVE.val := by
  simp [LeanSwe.PostFork.Model.WIRE_MAGIC, LeanSwe.PostFork.Model.WIRE_VERSION,
    LeanSwe.PostFork.Model.STAGE_VALIDATE, LeanSwe.PostFork.Model.STAGE_PROCESS_GROUP,
    LeanSwe.PostFork.Model.STAGE_SIGNAL_RESET, LeanSwe.PostFork.Model.STAGE_FD_SETUP,
    LeanSwe.PostFork.Model.STAGE_CLOSE_UNKEPT, LeanSwe.PostFork.Model.STAGE_CHDIR,
    LeanSwe.PostFork.Model.STAGE_EXECVE,
    postfork.child.WIRE_MAGIC, postfork.child.WIRE_VERSION,
    postfork.child.STAGE_VALIDATE, postfork.child.STAGE_PROCESS_GROUP,
    postfork.child.STAGE_SIGNAL_RESET, postfork.child.STAGE_FD_SETUP,
    postfork.child.STAGE_CLOSE_UNKEPT, postfork.child.STAGE_CHDIR,
    postfork.child.STAGE_EXECVE]

/-- Kernel proof of `test_postfork_wireEncoder_uniformAndRoundTrip` for `rustAeneasApi`. -/
theorem test_postfork_wireEncoder_uniformAndRoundTrip_allPass :
    Core.AllPass (test_postfork_wireEncoder_uniformAndRoundTrip rustAeneasApi) := by
  intro stage errnum fStage errU
  refine ⟨encode_failure_report_spec stage errnum, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨hStage, hLo, hHi, hLoN, hHiN⟩
  have hSpec := encode_failure_report_spec (LeanSwe.PostFork.Aeneas.Bridge.stageToU8 fStage) errnum
  rcases hSpec with ⟨arr, hArrOk, hArrVal⟩
  have hBytesEq := bytesToByteArray_expectedFailureWireBytes_eq_model fStage errnum hStage hLoN hHiN
  have hToNatLo : 1 ≤ (UInt32.ofNat errnum.toNat).toNat := by
    have ht : errnum.toNat = errnum.val.toNat := rfl
    simp [Nat.mod_eq_of_lt (by omega : errnum.toNat < 4294967296)]
    omega
  have hToNatHi : (UInt32.ofNat errnum.toNat).toNat ≤ 4095 := by
    have ht : errnum.toNat = errnum.val.toNat := rfl
    simp [Nat.mod_eq_of_lt (by omega : errnum.toNat < 4294967296)]
    omega
  have hDecModel := decodeChildFailure_encode_roundTrip fStage (UInt32.ofNat errnum.toNat) hStage hToNatLo hToNatHi
  refine ⟨decodeChildFailure_encode_roundTrip fStage errU hStage hLo hHi,
    model_wire_constants_match_aeneas,
    ⟨arr, hArrOk, ?_⟩,
    trivial⟩
  dsimp only
  rw [hArrVal, hBytesEq]
  exact ⟨rfl, hDecModel⟩

/-- Witness reachability for `test_postfork_wireEncoder_uniformAndRoundTrip`. -/
theorem test_postfork_wireEncoder_uniformAndRoundTrip_canReach :
    Core.CanReach (test_postfork_wireEncoder_uniformAndRoundTrip rustAeneasApi) := by
  have hAll := test_postfork_wireEncoder_uniformAndRoundTrip_allPass 7#u8 2#i32 .execve 2
  dsimp only [Core.CanReach, test_postfork_wireEncoder_uniformAndRoundTrip]
  have hPre :
      FailureStage.execve ≠ .wireTruncated ∧
      1 ≤ (2 : UInt32).toNat ∧ (2 : UInt32).toNat ≤ 4095 ∧
      1 ≤ (2#i32).val ∧ (2#i32).val ≤ 4095 := by
    refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  refine ⟨7#u8, 2#i32, .execve, 2, hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1,
    hAll.2.2.2.2.1, hAll.2.2.2.2.2.1, hAll.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.1,
    hAll.2.2.2.2.2.2.2.2.1, hPre, hAll.2.2.2.2.2.2.2.2.2 hPre⟩

end WireEncoders

section DirentParse

private theorem list_findIdx?_eq_some_of_getElem {α : Type} (p : α → Bool) (xs : List α)
    (idx : Nat) (hIdx : idx < xs.length)
    (hBefore : ∀ j (hj : j < idx), p (xs[j]'(Nat.lt_trans hj hIdx)) = false)
    (hAt : p (xs[idx]'hIdx) = true) :
    xs.findIdx? p = some idx := by
  induction xs generalizing idx with
  | nil => simp at hIdx
  | cons x xs ih =>
    cases idx with
    | zero =>
      simp only [List.getElem_cons_zero] at hAt
      simp [List.findIdx?_cons, hAt]
    | succ idx' =>
      have hx : p x = false := hBefore 0 (Nat.zero_lt_succ idx')
      have hSub := ih idx' (Nat.lt_of_succ_lt_succ hIdx)
        (fun j hj => hBefore (j + 1) (Nat.succ_lt_succ hj)) hAt
      simp [List.findIdx?_cons, hx, hSub]

private theorem list_findIdx?_eq_none_of_forall {α : Type} (p : α → Bool) (xs : List α)
    (hAll : ∀ j (hj : j < xs.length), p (xs[j]'hj) = false) :
    xs.findIdx? p = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = false := hAll 0 (by simp)
    have hRest : xs.findIdx? p = none := ih (fun j hj => hAll (j + 1) (Nat.succ_lt_succ hj))
    simp [List.findIdx?_cons, hx, hRest]

private theorem usize_256_val : (↑(256#usize) : Nat) = 256 := rfl

private theorem buf_len_256 (buf : Array U8 256#usize) : buf.val.length = 256 :=
  buf.property

private theorem usize_max_ge_4294967295 : 4294967295 ≤ Usize.max := by
  have h1 := Usize.cMax_bound.1
  have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
  omega

private theorem u64_max_eq : U64.max = 18446744073709551615 := by
  rw [U64.max_def, U64.numBits_def, UScalarTy.U64_numBits_eq]
  decide

private theorem array_index_usize_ok (buf : Array U8 256#usize) (i : Usize) (hi : i.val < 256) :
    buf.index_usize i = Result.ok (buf.val[i.val]'(by rw [buf_len_256]; exact hi)) := by
  have hLen : i.val < buf.length := by
    change i.val < buf.val.length; rw [buf_len_256]; exact hi
  obtain ⟨x, hx, hEq⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec buf i hLen)
  rw [hx, hEq]

private theorem usize_add_one_ok (p : Usize) (hp : p.val ≤ 256) :
    ∃ p1 : Usize, p + 1#usize = Result.ok p1 ∧ p1.val = p.val + 1 := by
  have hMax : 4294967295 ≤ Usize.max := usize_max_ge_4294967295
  have hBound : p.val + (1#usize).val ≤ Usize.max := by
    change p.val + 1 ≤ Usize.max; omega
  obtain ⟨z, hz, hzVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.add_spec hBound)
  exact ⟨z, hz, by simpa using hzVal⟩

/-- Recursive equivalence between `parse_dirent_name_loop0` and `List.findIdx?` on the bounded slice. -/
theorem parse_dirent_name_loop0_spec (buf : Array U8 256#usize) (stop start : Usize)
    (hStop : stop.val ≤ 256) (hLe : start.val ≤ stop.val) :
    OkPost (postfork.fd_ops.parse_dirent_name_loop0 buf stop start) fun nul =>
      start.val ≤ nul.val ∧ nul.val ≤ stop.val ∧
      match ((buf.val.take stop.val).drop start.val).findIdx? (fun b => b == 0#u8) with
      | none => nul.val = stop.val
      | some relIdx =>
        nul.val < stop.val ∧ nul.val = start.val + relIdx := by
  let measure : Usize → Nat := fun k => stop.val - k.val
  suffices h :
      (∀ (k : Usize), k.val ≤ stop.val →
        OkPost (postfork.fd_ops.parse_dirent_name_loop0 buf stop k) fun nul =>
          k.val ≤ nul.val ∧ nul.val ≤ stop.val ∧
          match ((buf.val.take stop.val).drop k.val).findIdx? (fun b => b == 0#u8) with
          | none => nul.val = stop.val
          | some relIdx =>
            nul.val < stop.val ∧ nul.val = k.val + relIdx) from
    h start hLe
  intro k hk
  let invK : Usize → Prop := fun p =>
    k.val ≤ p.val ∧ p.val ≤ stop.val ∧
    (∀ idx, k.val ≤ idx → idx < p.val → buf.val[idx]? ≠ some 0#u8)
  refine okPost_loop_decr_nat measure invK _ (postfork.fd_ops.parse_dirent_name_loop0.body buf stop) k ?_
    ⟨Nat.le_refl _, hk, fun _ h1 h2 => by omega⟩
  intro p ⟨hkp, hpStop, hno0⟩
  unfold postfork.fd_ops.parse_dirent_name_loop0.body
  by_cases hlt : p < stop
  · have hpLtStop : p.val < stop.val := hlt
    have hp256 : p.val < 256 := by omega
    have hlt256 : p < 256#usize := hp256
    simp only [hlt, hlt256, ↓reduceIte]
    have hBufLen : buf.val.length = 256 := buf_len_256 buf
    have hpLen : p.val < buf.val.length := by rw [hBufLen]; exact hp256
    rw [array_index_usize_ok buf p hp256, bind_ok]
    by_cases hz : buf.val[p.val] = 0#u8
    · simp only [hz, ↓reduceIte]
      refine ⟨ControlFlow.done p, rfl, hkp, hpStop, ?_⟩
      have hfind :
          ((buf.val.take stop.val).drop k.val).findIdx? (fun b => b == 0#u8) =
            some (p.val - k.val) := by
        have hSliceLen : ((buf.val.take stop.val).drop k.val).length = stop.val - k.val := by
          simp [List.length_drop, List.length_take, hBufLen]
          omega
        have hIdx : p.val - k.val < ((buf.val.take stop.val).drop k.val).length := by
          rw [hSliceLen]
          exact Nat.sub_lt_sub_right hkp hpLtStop
        refine list_findIdx?_eq_some_of_getElem _ _ (p.val - k.val) hIdx ?_ ?_
        · intro j hj
          have hjLt : k.val + j < stop.val := by omega
          have hGet : ((buf.val.take stop.val).drop k.val)[j]'(Nat.lt_trans hj hIdx) =
              buf.val[k.val + j]'(by omega) := by
            simp [List.getElem_drop, List.getElem_take]
          rw [hGet]
          have hNe := hno0 (k.val + j) (by omega) (by omega)
          have hSome : buf.val[k.val + j]? = some (buf.val[k.val + j]'(by omega)) :=
            List.getElem?_eq_getElem (by omega)
          rw [hSome] at hNe
          cases hEq : (buf.val[k.val + j]'(by omega) == 0#u8)
          · rfl
          · exact False.elim (hNe (by simpa using hEq))
        · have hGet : ((buf.val.take stop.val).drop k.val)[p.val - k.val]'hIdx =
              buf.val[p.val] := by
            simp [List.getElem_drop, List.getElem_take, Nat.add_sub_cancel' hkp]
          rw [hGet, hz]
          rfl
      rw [hfind]
      exact ⟨hpLtStop, by omega⟩
    · simp only [hz, ↓reduceIte]
      obtain ⟨p1, hp1Eq, hp1Val⟩ := usize_add_one_ok p (by omega)
      rw [hp1Eq, bind_ok]
      refine ⟨ControlFlow.cont p1, rfl, ?_, ?_⟩
      · refine ⟨by omega, by omega, ?_⟩
        intro idx h1 h2
        by_cases hIdx : idx < p.val
        · exact hno0 idx h1 hIdx
        · have hEqP : idx = p.val := by omega
          subst hEqP
          simp [List.getElem?_eq_getElem hpLen, hz]
      · simp [measure]; omega
  · simp only [hlt, ↓reduceIte]
    have hpNotLt : ¬ p.val < stop.val := hlt
    have hpStopEq : p.val = stop.val := by omega
    refine ⟨ControlFlow.done p, rfl, hkp, hpStop, ?_⟩
    have hBufLen : buf.val.length = 256 := buf_len_256 buf
    have hnone :
        ((buf.val.take stop.val).drop k.val).findIdx? (fun b => b == 0#u8) = none := by
      apply list_findIdx?_eq_none_of_forall
      intro j hj
      have hjLen : j < stop.val - k.val := by
        simp [List.length_drop, List.length_take, hBufLen] at hj
        omega
      have hGet : ((buf.val.take stop.val).drop k.val)[j]'hj =
          buf.val[k.val + j]'(by omega) := by
        simp [List.getElem_drop, List.getElem_take]
      rw [hGet]
      have hNe := hno0 (k.val + j) (by omega) (by omega)
      have hSome : buf.val[k.val + j]? = some (buf.val[k.val + j]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      rw [hSome] at hNe
      cases hEq : (buf.val[k.val + j]'(by omega) == 0#u8)
      · rfl
      · exact False.elim (hNe (by simpa using hEq))
    rw [hnone]
    exact hpStopEq

private def isAsciiDigit (b : U8) : Bool :=
  decide (48#u8 ≤ b) && decide (b ≤ 57#u8)

private def foldDigits (init : Nat) (xs : List U8) : Nat :=
  xs.foldl (fun acc b => acc * 10 + (b.val - 48)) init

private theorem foldDigits_cons (init : Nat) (b : U8) (xs : List U8) :
    foldDigits init (b :: xs) = foldDigits (init * 10 + (b.val - 48)) xs := by
  simp only [foldDigits, List.foldl_cons]

private theorem foldDigits_ge_init (init : Nat) (xs : List U8) :
    init ≤ foldDigits init xs := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    rw [foldDigits_cons]
    have h1 : init ≤ init * 10 + (x.val - 48) := by omega
    exact Nat.le_trans h1 (ih _)

private theorem foldDigits_eq_eval (xs : List U8) (init : Nat) :
    foldDigits init xs = init * 10 ^ xs.length + foldDigits 0 xs := by
  induction xs generalizing init with
  | nil => simp [foldDigits]
  | cons x xs ih =>
    rw [foldDigits_cons, foldDigits_cons]
    rw [ih (init * 10 + (x.val - 48)), ih (0 * 10 + (x.val - 48))]
    simp [List.length_cons, Nat.pow_succ]
    ring

private theorem parse_dirent_name_digits_body_spec
    (buf : Array U8 256#usize) (nul : Usize) (hNul : nul.val ≤ 256)
    (body : U64 → Usize → Result (ControlFlow (U64 × Usize) (U64 × Bool)))
    (hBody : ∀ acc j, body acc j =
      if j < nul then
        if j < 256#usize then do
          let b ← buf.index_usize j
          if b < 48#u8 then Result.ok (ControlFlow.done (acc, false))
          else if b > 57#u8 then Result.ok (ControlFlow.done (acc, false))
          else do
            let i ← acc * 10#u64
            let i1 ← b - 48#u8
            let i2 ← lift (UScalar.cast UScalarTy.U64 i1)
            let acc1 ← i + i2
            let i3 ← lift (IScalar.hcast UScalarTy.U64 core.num.I32.MAX)
            if acc1 > i3 then Result.ok (ControlFlow.done (acc1, false))
            else do
              let j1 ← j + 1#usize
              Result.ok (ControlFlow.cont (acc1, j1))
        else Result.ok (ControlFlow.done (acc, true))
      else Result.ok (ControlFlow.done (acc, true)))
    (acc : U64) (j : Usize) (hAcc : acc.val ≤ 2147483647) (hj : j.val ≤ nul.val) :
    OkPost (loop (fun x => match x with | (a, k) => body a k) (acc, j)) fun res =>
      let seg := (buf.val.take nul.val).drop j.val
      let val := foldDigits acc.val seg
      if res.2 then seg.all isAsciiDigit = true ∧ val ≤ 2147483647 ∧ res.1.val = val
      else seg.all isAsciiDigit = false ∨ val > 2147483647 := by
  let measure : (U64 × Usize) → Nat := fun x => nul.val - x.2.val
  let inv : (U64 × Usize) → Prop := fun x =>
    x.1.val ≤ 2147483647 ∧ x.2.val ≤ nul.val ∧
    (let segX := (buf.val.take nul.val).drop x.2.val
     let segJ := (buf.val.take nul.val).drop j.val
     (segJ.all isAsciiDigit = true → segX.all isAsciiDigit = true ∧
       foldDigits acc.val segJ = foldDigits x.1.val segX) ∧
     (segJ.all isAsciiDigit = false → segX.all isAsciiDigit = false))
  refine okPost_loop_decr_nat measure inv _
    (fun x => match x with | (a, k) => body a k) (acc, j) ?_
    ⟨hAcc, hj, fun h => ⟨h, rfl⟩, id⟩
  rintro ⟨a, k⟩ ⟨ha, hk, hkAll, hkNotAll⟩
  dsimp only at ha hk hkAll hkNotAll ⊢
  rw [hBody a k]
  have hBufLen : buf.val.length = 256 := buf_len_256 buf
  by_cases hlt : k < nul
  · have hkLtNul : k.val < nul.val := hlt
    have hk256 : k.val < 256 := by omega
    have hlt256 : k < 256#usize := hk256
    simp only [hlt, hlt256, ↓reduceIte]
    have hkLen : k.val < buf.val.length := by rw [hBufLen]; exact hk256
    rw [array_index_usize_ok buf k hk256, bind_ok]
    set b := buf.val[k.val]
    have hSegCons :
        (buf.val.take nul.val).drop k.val =
          b :: (buf.val.take nul.val).drop (k.val + 1) := by
      have hElemLt : k.val < (buf.val.take nul.val).length := by
        simp [List.length_take, hBufLen]; omega
      have hDrop := List.getElem_cons_drop hElemLt
      have hTakeElem : (buf.val.take nul.val)[k.val]'hElemLt = b := by
        simp [b, List.getElem_take]
      rw [hTakeElem] at hDrop
      exact hDrop.symm
    by_cases hLow : b < 48#u8
    · have hbLow : b.val < 48 := hLow
      simp only [hLow, ↓reduceIte]
      refine ⟨ControlFlow.done (a, false), rfl, ?_⟩
      dsimp only
      by_cases hJ : ((buf.val.take nul.val).drop j.val).all isAsciiDigit = true
      · have hK := (hkAll hJ).1
        rw [hSegCons] at hK
        have hbDig : isAsciiDigit b = false := by
          simp [isAsciiDigit]; intro hge; change 48 ≤ b.val at hge; omega
        simp [List.all_cons, hbDig] at hK
      · left; exact Bool.eq_false_iff.mpr hJ
    · have hbGe48 : 48 ≤ b.val := by change ¬ b.val < 48 at hLow; omega
      simp only [hLow, ↓reduceIte]
      by_cases hHigh : b > 57#u8
      · have hbHigh : b.val > 57 := hHigh
        simp only [hHigh, ↓reduceIte]
        refine ⟨ControlFlow.done (a, false), rfl, ?_⟩
        dsimp only
        by_cases hJ : ((buf.val.take nul.val).drop j.val).all isAsciiDigit = true
        · have hK := (hkAll hJ).1
          rw [hSegCons] at hK
          have hbDig : isAsciiDigit b = false := by
            simp [isAsciiDigit]; omega
          simp [List.all_cons, hbDig] at hK
        · left; exact Bool.eq_false_iff.mpr hJ
      · have hbLe57 : b.val ≤ 57 := by change ¬ b.val > 57 at hHigh; omega
        simp only [hHigh, ↓reduceIte]
        have hu64 : U64.max = 18446744073709551615 := u64_max_eq
        have hm10 : ∃ m : U64, a * 10#u64 = Result.ok m ∧ m.val = a.val * 10 := by
          have hMulBound : a.val * (10#u64).val ≤ U64.max := by
            change a.val * 10 ≤ U64.max; rw [hu64]; omega
          obtain ⟨m, hmEq, hmVal⟩ := (okPost_iff_wp_spec _ _).mpr (U64.mul_spec hMulBound)
          exact ⟨m, hmEq, by simpa using hmVal⟩
        rcases hm10 with ⟨m, hmEq, hmVal⟩
        have hSub : ∃ d : U8, b - 48#u8 = Result.ok d ∧ d.val = b.val - 48 := by
          have hGe48 : (48#u8).val ≤ b.val := by change 48 ≤ b.val; omega
          obtain ⟨d, hdEq, hdVal, _⟩ := (okPost_iff_wp_spec _ _).mpr (U8.sub_spec hGe48)
          exact ⟨d, hdEq, by simpa using hdVal⟩
        rcases hSub with ⟨d, hdEq, hdVal⟩
        have hCast : (UScalar.cast UScalarTy.U64 d).val = b.val - 48 := by
          have hdLe : d.val ≤ 9 := by omega
          have h3 : (UScalar.cast UScalarTy.U64 d).val = (BitVec.setWidth 64 d.bv).toNat := rfl
          rw [h3, BitVec.toNat_setWidth]
          have hdBv : d.bv.toNat = d.val := rfl
          rw [hdBv, Nat.mod_eq_of_lt (by omega), hdVal]
        have hAdd : ∃ a1 : U64, m + UScalar.cast UScalarTy.U64 d = Result.ok a1 ∧
            a1.val = a.val * 10 + (b.val - 48) := by
          have hSumBound : m.val + (UScalar.cast UScalarTy.U64 d).val ≤ U64.max := by
            rw [hu64]; omega
          obtain ⟨a1, ha1Eq, ha1Val⟩ := (okPost_iff_wp_spec _ _).mpr (U64.add_spec hSumBound)
          exact ⟨a1, ha1Eq, by omega⟩
        rcases hAdd with ⟨a1, ha1Eq, ha1Val⟩
        have hMaxVal : (IScalar.hcast UScalarTy.U64 core.num.I32.MAX).val = 2147483647 := by
          decide
        rw [hmEq, bind_ok, hdEq, bind_ok]
        simp only [lift, bind_ok]
        rw [ha1Eq, bind_ok]
        by_cases hOver : a1 > IScalar.hcast UScalarTy.U64 core.num.I32.MAX
        · simp only [hOver, ↓reduceIte]
          refine ⟨ControlFlow.done (a1, false), rfl, ?_⟩
          dsimp only
          have ha1Gt : a1.val > 2147483647 := by
            change a1.val > (IScalar.hcast UScalarTy.U64 core.num.I32.MAX).val at hOver
            omega
          by_cases hJ : ((buf.val.take nul.val).drop j.val).all isAsciiDigit = true
          · right
            have hFold := (hkAll hJ).2
            rw [hFold, hSegCons, foldDigits_cons]
            have hGe := foldDigits_ge_init (a.val * 10 + (b.val - 48))
              ((buf.val.take nul.val).drop (k.val + 1))
            omega
          · left; exact Bool.eq_false_iff.mpr hJ
        · simp only [hOver, ↓reduceIte]
          have ha1Le : a1.val ≤ 2147483647 := by
            change ¬ a1.val > (IScalar.hcast UScalarTy.U64 core.num.I32.MAX).val at hOver
            omega
          obtain ⟨k1, hk1Eq, hk1Val⟩ := usize_add_one_ok k (by omega)
          rw [hk1Eq, bind_ok]
          refine ⟨ControlFlow.cont (a1, k1), rfl, ?_, ?_⟩
          · refine ⟨ha1Le, by dsimp only; omega, ?_, ?_⟩
            · intro hJ
              have ⟨hKAll, hKFold⟩ := hkAll hJ
              rw [hSegCons] at hKAll hKFold
              have hbDig : isAsciiDigit b = true := by
                simp [isAsciiDigit]; exact ⟨hbGe48, hbLe57⟩
              simp only [List.all_cons, hbDig, Bool.true_and] at hKAll
              refine ⟨by simpa [hk1Val] using hKAll, ?_⟩
              rw [hKFold, foldDigits_cons, hk1Val, ha1Val]
            · intro hJFalse
              have hKFalse := hkNotAll hJFalse
              rw [hSegCons] at hKFalse
              have hbDig : isAsciiDigit b = true := by
                simp [isAsciiDigit]; exact ⟨hbGe48, hbLe57⟩
              simp only [List.all_cons, hbDig, Bool.true_and] at hKFalse
              simpa [hk1Val] using hKFalse
          · simp [measure]; omega
  · simp only [hlt, ↓reduceIte]
    have hkNotLt : ¬ k.val < nul.val := hlt
    refine ⟨ControlFlow.done (a, true), rfl, ?_⟩
    dsimp only
    have hkEq : k.val = nul.val := by omega
    have hSegNil : (buf.val.take nul.val).drop k.val = [] := by
      simp [hkEq, List.length_take, hBufLen]
    have hJTrue : ((buf.val.take nul.val).drop j.val).all isAsciiDigit = true := by
      cases hJ : ((buf.val.take nul.val).drop j.val).all isAsciiDigit
      · have hKFalse := hkNotAll hJ
        rw [hSegNil] at hKFalse
        simp at hKFalse
      · rfl
    have ⟨_, hFold⟩ := hkAll hJTrue
    rw [hSegNil] at hFold
    have hValLe : foldDigits acc.val ((buf.val.take nul.val).drop j.val) ≤ 2147483647 := by
      rw [hFold]
      simpa [foldDigits] using ha
    have hValEq : a.val = foldDigits acc.val ((buf.val.take nul.val).drop j.val) := by
      rw [hFold]
      simp [foldDigits]
    exact ⟨hJTrue, hValLe, hValEq⟩

/-- Exact agreement between `postfork.fd_ops.parse_dirent_name` and `Model.expectedDirentParse`. -/
theorem parse_dirent_name_eq_expected (buf : Array U8 256#usize) (start stop : Usize) :
    postfork.fd_ops.parse_dirent_name buf start stop =
      Result.ok (Model.expectedDirentParse buf start stop) := by
  unfold postfork.fd_ops.parse_dirent_name Model.expectedDirentParse
  rw [postfork.fd_ops.DIRENT_MALFORMED, postfork.fd_ops.DIRENT_OTHER]
  have hBufLen : buf.val.length = 256 := buf_len_256 buf
  by_cases hStop : stop > 256#usize
  · have hStopNat : stop.val > 256 := hStop
    simp only [hStop, hStopNat, decide_true, Bool.true_or, ↓reduceIte]
  · have hStopLe : stop.val ≤ 256 := by change ¬ stop.val > 256 at hStop; omega
    simp only [hStop, ↓reduceIte]
    by_cases hStartGe : start ≥ stop
    · have hStartNat : start.val ≥ stop.val := hStartGe
      simp only [hStartGe, hStartNat, decide_true, Bool.or_true, ↓reduceIte]
    · have hStartLt : start.val < stop.val := by change ¬ start.val ≥ stop.val at hStartGe; omega
      have hStartLt256 : ¬ start ≥ 256#usize := by change ¬ start.val ≥ 256; omega
      simp only [hStartGe, hStartLt256, ↓reduceIte]
      have hCondFalse : (decide (stop.val > 256) || decide (start.val ≥ stop.val)) = false := by
        simp; omega
      simp only [hCondFalse, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨nul, hLoop0Eq, hStartNul, hNulStop, hFind⟩ :=
        parse_dirent_name_loop0_spec buf stop start hStopLe (Nat.le_of_lt hStartLt)
      rw [hLoop0Eq, bind_ok]
      set region := (buf.val.take stop.val).drop start.val
      have hRegLen : region.length = stop.val - start.val := by
        simp [region, List.length_drop, List.length_take, hBufLen]; omega
      cases hFindEq : region.findIdx? (fun b => b == 0#u8) with
      | none =>
        rw [hFindEq] at hFind
        have hNulGe : nul ≥ stop := by change nul.val ≥ stop.val; omega
        simp only [hNulGe, ↓reduceIte]
      | some relIdx =>
        rw [hFindEq] at hFind
        rcases hFind with ⟨hNulLtStop, hNulSum⟩
        have hNotGe : ¬ nul ≥ stop := by change ¬ nul.val ≥ stop.val; omega
        simp only [hNotGe, ↓reduceIte]
        cases relIdx with
        | zero =>
          have hNulEqStart : nul = start := by apply UScalar.eq_of_val_eq; omega
          simp only [hNulEqStart, ↓reduceIte]
        | succ m =>
          have hNulNeStart : ¬ nul = start := by intro h; subst h; omega
          simp only [hNulNeStart, ↓reduceIte]
          have hSubOk : ∃ lenU : Usize, nul - start = Result.ok lenU ∧ lenU.val = m + 1 := by
            have hLeNul : start.val ≤ nul.val := by omega
            obtain ⟨lenU, hSubEq, hLenVal, _⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.sub_spec hLeNul)
            exact ⟨lenU, hSubEq, by omega⟩
          rcases hSubOk with ⟨lenU, hSubEq, hLenUVal⟩
          rw [hSubEq, bind_ok]
          have hNotGeLen : ¬ (m + 1 ≥ region.length) := by omega
          simp only [hNotGeLen, ↓reduceIte]
          have hNmEq : List.take (m + 1) region = (buf.val.take nul.val).drop start.val := by
            simp only [region]
            rw [List.take_drop, List.take_take]
            congr 2
            omega
          by_cases hmPos : m > 0
          · have hGt1 : lenU > 1#usize := by change lenU.val > 1; omega
            simp only [hGt1, ↓reduceIte]
            have hStart256 : start.val < 256 := by omega
            rw [array_index_usize_ok buf start hStart256, bind_ok]
            have hNmGt1 : (List.take (m + 1) region).length > 1 := by
              simp [List.length_take, hRegLen]; omega
            have hHeadSome : (List.take (m + 1) region).head? = some (buf.val[start.val]'(by rw [hBufLen]; exact hStart256)) := by
              rw [hNmEq]
              have hElemLt : start.val < (buf.val.take nul.val).length := by
                simp [List.length_take, hBufLen]; omega
              have hDrop := List.getElem_cons_drop hElemLt
              rw [← hDrop]
              simp only [List.getElem_take]
              rfl
            by_cases hLeadZero : (buf.val[start.val]'(by rw [hBufLen]; exact hStart256)) = 48#u8
            · simp only [hLeadZero, ↓reduceIte]
              by_cases hAllD : (List.take (m + 1) region).all (fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true
              · have hNotAll : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = false := by
                  simp only [hAllD, Bool.not_true]
                have hCondLead : (decide ((List.take (m + 1) region).length > 1) &&
                    ((List.take (m + 1) region).head? == some 48#u8)) = true := by
                  simp only [hNmGt1, hHeadSome, hLeadZero, decide_true, beq_self_eq_true, Bool.and_self]
                simp only [hNotAll, Bool.false_eq_true, ↓reduceIte, hCondLead]
              · have hNotAll : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = true := by
                  simp only [Bool.eq_false_iff.mpr hAllD, Bool.not_false]
                simp only [hNotAll, ↓reduceIte]
            · simp only [hLeadZero, ↓reduceIte]
              have hNot48 : (some (buf.val[start.val]'(by rw [hBufLen]; exact hStart256)) == some 48#u8) = false := by
                simpa using hLeadZero
              have hCondLeadFalse : (decide ((List.take (m + 1) region).length > 1) &&
                  ((List.take (m + 1) region).head? == some 48#u8)) = false := by
                simp only [hHeadSome, hNot48, Bool.and_false]
              obtain ⟨⟨resAcc, ok⟩, hL1Eq, hL1Post⟩ :=
                parse_dirent_name_digits_body_spec buf nul (by omega)
                  (postfork.fd_ops.parse_dirent_name_loop1.body buf nul)
                  (fun _ _ => rfl) 0#u64 start (by decide) (by omega)
              change postfork.fd_ops.parse_dirent_name_loop1 buf nul 0#u64 start = Result.ok (resAcc, ok) at hL1Eq
              rw [hL1Eq, bind_ok]
              change (if ok = true then Result.ok (UScalar.hcast IScalarTy.I32 resAcc) else Result.ok (-1)#i32) = _
              dsimp only at hL1Post ⊢
              rw [← hNmEq] at hL1Post
              have hZero64 : (0#u64).val = 0 := rfl
              rw [hZero64] at hL1Post
              cases ok
              · simp only [Bool.false_eq_true, ↓reduceIte] at hL1Post ⊢
                rcases hL1Post with hNotAll | hGtMax
                · have hNotAll' : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = false := hNotAll
                  have hNotAllTrue : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = true := by
                    simp only [hNotAll', Bool.not_false]
                  simp only [hNotAllTrue, ↓reduceIte]
                · by_cases hAll : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true
                  · simp only [foldDigits] at hGtMax
                    have hGtVal : List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 (List.take (m + 1) region) > 2147483647 := hGtMax
                    have hNotAllF : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = false := by
                      simp only [hAll, Bool.not_true]
                    simp only [hNotAllF, Bool.false_eq_true, ↓reduceIte, hCondLeadFalse, hGtVal]
                  · have hNot : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = true := by
                      simp only [Bool.eq_false_iff.mpr hAll, Bool.not_false]
                    simp only [hNot, ↓reduceIte]
              · simp only [↓reduceIte] at hL1Post ⊢
                rcases hL1Post with ⟨hAll, hLeMax, hValEq⟩
                have hAll' : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true := hAll
                simp only [foldDigits] at hLeMax hValEq
                have hLeMax' : ¬ (List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 (List.take (m + 1) region) > 2147483647) := by
                  omega
                simp only [hAll', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCondLeadFalse, hLeMax']
                congr 1
                apply IScalar.eq_of_val_eq
                have hResLe : resAcc.val ≤ 2147483647 := by omega
                have hValNatEq : resAcc.val = List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region) := hValEq
                have hCastVal : (UScalar.hcast IScalarTy.I32 resAcc).val = Int.ofNat resAcc.val := by
                  have hCastEq : (UScalar.hcast IScalarTy.I32 resAcc).bv = BitVec.setWidth 32 resAcc.bv := rfl
                  change (UScalar.hcast IScalarTy.I32 resAcc).bv.toInt = Int.ofNat resAcc.val
                  rw [hCastEq, BitVec.toInt_eq_toNat_cond]
                  have hNatLt : resAcc.bv.toNat < 2 ^ 31 := by change resAcc.val < 2 ^ 31; omega
                  simp [BitVec.toNat_setWidth]
                  split_ifs <;> omega
                have hMkVal : (mkI32 (Int.ofNat (List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region)))).val =
                    Int.ofNat (List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region)) := by
                  rw [← hValNatEq]
                  exact mkI32_val_nonneg (Int.natCast_nonneg _) (Int.ofNat_le.mpr hResLe)
                rw [hCastVal, hMkVal, hValNatEq]
          · have hm0 : m = 0 := by omega
            have hNotGt1 : ¬ (lenU > 1#usize) := by change ¬ (lenU.val > 1); omega
            simp only [hNotGt1, ↓reduceIte]
            have hNmLe1 : ¬ ((List.take (m + 1) region).length > 1) := by
              simp [List.length_take, hm0]
            have hCondLeadFalse : (decide ((List.take (m + 1) region).length > 1) &&
                ((List.take (m + 1) region).head? == some 48#u8)) = false := by
              simp only [hNmLe1, decide_false, Bool.false_and]
            obtain ⟨⟨resAcc, ok⟩, hL2Eq, hL2Post⟩ :=
              parse_dirent_name_digits_body_spec buf nul (by omega)
                (postfork.fd_ops.parse_dirent_name_loop2.body buf nul)
                (fun _ _ => rfl) 0#u64 start (by decide) (by omega)
            change postfork.fd_ops.parse_dirent_name_loop2 buf nul 0#u64 start = Result.ok (resAcc, ok) at hL2Eq
            rw [hL2Eq, bind_ok]
            change (if ok = true then Result.ok (UScalar.hcast IScalarTy.I32 resAcc) else Result.ok (-1)#i32) = _
            dsimp only at hL2Post ⊢
            rw [← hNmEq] at hL2Post
            have hZero64 : (0#u64).val = 0 := rfl
            rw [hZero64] at hL2Post
            cases ok
            · simp only [Bool.false_eq_true, ↓reduceIte] at hL2Post ⊢
              rcases hL2Post with hNotAll | hGtMax
              · have hNotAll' : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = false := hNotAll
                have hNotAllTrue : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = true := by
                  simp only [hNotAll', Bool.not_false]
                simp only [hNotAllTrue, ↓reduceIte]
              · by_cases hAll : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true
                · simp only [foldDigits] at hGtMax
                  have hGtVal : List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 (List.take (m + 1) region) > 2147483647 := hGtMax
                  have hNotAllF : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = false := by
                    simp only [hAll, Bool.not_true]
                  simp only [hNotAllF, Bool.false_eq_true, ↓reduceIte, hCondLeadFalse, hGtVal]
                · have hNot : (!((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8))) = true := by
                    simp only [Bool.eq_false_iff.mpr hAll, Bool.not_false]
                  simp only [hNot, ↓reduceIte]
            · simp only [↓reduceIte] at hL2Post ⊢
              rcases hL2Post with ⟨hAll, hLeMax, hValEq⟩
              have hAll' : ((List.take (m + 1) region).all fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true := hAll
              simp only [foldDigits] at hLeMax hValEq
              have hLeMax' : ¬ (List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 (List.take (m + 1) region) > 2147483647) := by
                omega
              simp only [hAll', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCondLeadFalse, hLeMax']
              congr 1
              apply IScalar.eq_of_val_eq
              have hResLe : resAcc.val ≤ 2147483647 := by omega
              have hValNatEq : resAcc.val = List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region) := hValEq
              have hCastVal : (UScalar.hcast IScalarTy.I32 resAcc).val = Int.ofNat resAcc.val := by
                have hCastEq : (UScalar.hcast IScalarTy.I32 resAcc).bv = BitVec.setWidth 32 resAcc.bv := rfl
                change (UScalar.hcast IScalarTy.I32 resAcc).bv.toInt = Int.ofNat resAcc.val
                rw [hCastEq, BitVec.toInt_eq_toNat_cond]
                have hNatLt : resAcc.bv.toNat < 2 ^ 31 := by change resAcc.val < 2 ^ 31; omega
                simp [BitVec.toNat_setWidth]
                split_ifs <;> omega
              have hMkVal : (mkI32 (Int.ofNat (List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region)))).val =
                  Int.ofNat (List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 (List.take (m + 1) region)) := by
                rw [← hValNatEq]
                exact mkI32_val_nonneg (Int.natCast_nonneg _) (Int.ofNat_le.mpr hResLe)
              rw [hCastVal, hMkVal, hValNatEq]

private theorem natDigitsFuel_spec (fuel n : Nat) (acc : Bytes)
    (hFuel : 0 < fuel) (hBound : n < 10 ^ fuel)
    (hAccDig : ∀ b ∈ acc, isAsciiDigit b = true)
    (hAccZero : n = 0 → acc = []) :
    let res := natDigitsFuel fuel n acc
    1 ≤ res.length ∧ res.length ≤ fuel + acc.length ∧
    (∀ b ∈ res, isAsciiDigit b = true) ∧
    (res.length > 1 → res.head? ≠ some 48#u8) ∧
    foldDigits 0 res = n * 10 ^ acc.length + foldDigits 0 acc := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ f ih =>
    cases f with
    | zero =>
      have hn : n < 10 := by simpa using hBound
      have hq : n / 10 = 0 := Nat.div_eq_of_lt hn
      rw [natDigitsFuel.eq_def]
      dsimp only
      have hdVal : (mkU8 (48 + n % 10)).val = 48 + n % 10 := mkU8_val (n := 48 + n % 10) (by omega)
      have hd : isAsciiDigit (mkU8 (48 + n % 10)) = true := by
        simp [isAsciiDigit, hdVal]; omega
      simp only [hq, beq_self_eq_true, ↓reduceIte]
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hbAcc
        · exact hd
        · exact hAccDig b hbAcc
      · intro hLenGt
        by_cases hn0 : n = 0
        · have := hAccZero hn0
          subst this
          simp at hLenGt
        · simp only [List.head?_cons, ne_eq, Option.some.injEq]
          intro hEq
          have hVal := congrArg UScalar.val hEq
          rw [hdVal] at hVal
          have h48 : (48#u8).val = 48 := rfl
          rw [h48] at hVal
          omega
      · rw [foldDigits_cons, foldDigits_eq_eval]
        have hMod : n % 10 = n := Nat.mod_eq_of_lt hn
        rw [hdVal, hMod]
        simp
    | succ f' =>
      rw [natDigitsFuel.eq_def]
      dsimp only
      have hdVal : (mkU8 (48 + n % 10)).val = 48 + n % 10 := mkU8_val (n := 48 + n % 10) (by omega)
      have hd : isAsciiDigit (mkU8 (48 + n % 10)) = true := by
        simp [isAsciiDigit, hdVal]; omega
      by_cases hq : n / 10 == 0
      · have hq0 : n / 10 = 0 := beq_iff_eq.mp hq
        have hn : n < 10 := Nat.lt_of_div_eq_zero (by decide) hq0
        simp only [hq, ↓reduceIte]
        refine ⟨by simp, by simp, ?_, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hbAcc
          · exact hd
          · exact hAccDig b hbAcc
        · intro hLenGt
          by_cases hn0 : n = 0
          · have := hAccZero hn0
            subst this
            simp at hLenGt
          · simp only [List.head?_cons, ne_eq, Option.some.injEq]
            intro hEq
            have hVal := congrArg UScalar.val hEq
            rw [hdVal] at hVal
            have h48 : (48#u8).val = 48 := rfl
            rw [h48] at hVal
            omega
        · rw [foldDigits_cons, foldDigits_eq_eval]
          have hMod : n % 10 = n := Nat.mod_eq_of_lt hn
          rw [hdVal, hMod]
          simp
      · have hqPos : 0 < n / 10 := by
          have hqNe : n / 10 ≠ 0 := by simpa using hq
          omega
        have hqBound : n / 10 < 10 ^ (f' + 1) := by
          rw [Nat.pow_succ'] at hBound
          exact Nat.div_lt_of_lt_mul hBound
        have hSub := ih (n / 10) (mkU8 (48 + n % 10) :: acc) (Nat.zero_lt_succ f') hqBound
          (fun b hb => by
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hbAcc
            · exact hd
            · exact hAccDig b hbAcc)
          (fun h => False.elim (by omega))
        simp only [hq, Bool.false_eq_true, ↓reduceIte]
        rcases hSub with ⟨hL1, hL2, hDig, hHead, hEval⟩
        refine ⟨hL1, by simp at hL2; omega, hDig, hHead, ?_⟩
        rw [hEval, foldDigits_cons, foldDigits_eq_eval]
        simp only [List.length_cons, hdVal, Nat.zero_mul, Nat.zero_add]
        have hSub48 : 48 + n % 10 - 48 = n % 10 := by omega
        rw [hSub48]
        have hDivMod : (n / 10) * 10 + n % 10 = n := Nat.div_add_mod' n 10
        calc
          (n / 10) * 10 ^ (acc.length + 1) + (n % 10 * 10 ^ acc.length + foldDigits 0 acc)
              = ((n / 10) * 10 + n % 10) * 10 ^ acc.length + foldDigits 0 acc := by
                rw [Nat.pow_succ]; ring
          _ = n * 10 ^ acc.length + foldDigits 0 acc := by rw [hDivMod]

private theorem encodeU64Le_len (n : Nat) : (encodeU64Le n).length = 8 := rfl

private theorem mkUsize_val_small {n : Nat} (hn : n ≤ 256) : (mkUsize n).val = n :=
  mkUsize_val_le_scalar 256#usize hn

private theorem overlayBuf256_take (bs : Bytes) (hbs : bs.length ≤ 256) (z : Array U8 256#usize) :
    List.take bs.length (overlayBuf256 bs z).val = bs := by
  simp [World.overlayBuf256, List.take_of_length_le hbs]

private theorem expectedDirentParse_overlay_neg1_dot :
    expectedDirentParse (overlayBuf256 (encodeDirent64 1 1 4#u8 [46#u8]) (Array.repeat 256#usize 0#u8)) 19#usize
      (mkUsize (List.length (encodeDirent64 1 1 4#u8 [46#u8]))) = (-1)#i32 := by
  have hRecLen : List.length (encodeDirent64 1 1 4#u8 [46#u8]) = 24 := by
    simp [encodeDirent64, encodeU64Le_len]
  have hStopVal : (mkUsize (List.length (encodeDirent64 1 1 4#u8 [46#u8]))).val = 24 := by
    rw [hRecLen]
    exact mkUsize_val_small (by omega)
  unfold expectedDirentParse
  rw [hStopVal]
  have hNotBad : (decide (24 > 256) || decide ((19#usize).val ≥ 24)) = false := by decide
  simp only [hNotBad, Bool.false_eq_true, ↓reduceIte]
  have hRegion : List.drop (19#usize).val (List.take 24 (overlayBuf256 (encodeDirent64 1 1 4#u8 [46#u8])
      (Array.repeat 256#usize 0#u8)).val) = [46#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    have hTake : List.take 24 (overlayBuf256 (encodeDirent64 1 1 4#u8 [46#u8])
        (Array.repeat 256#usize 0#u8)).val = encodeDirent64 1 1 4#u8 [46#u8] := by
      rw [← hRecLen]
      exact overlayBuf256_take _ (by omega) _
    rw [hTake]
    decide
  rw [hRegion]
  decide

private theorem expectedDirentParse_overlay_neg1_dotdot :
    expectedDirentParse (overlayBuf256 (encodeDirent64 2 2 4#u8 [46#u8, 46#u8]) (Array.repeat 256#usize 0#u8)) 19#usize
      (mkUsize (List.length (encodeDirent64 2 2 4#u8 [46#u8, 46#u8]))) = (-1)#i32 := by
  have hRecLen : List.length (encodeDirent64 2 2 4#u8 [46#u8, 46#u8]) = 24 := by
    simp [encodeDirent64, encodeU64Le_len]
  have hStopVal : (mkUsize (List.length (encodeDirent64 2 2 4#u8 [46#u8, 46#u8]))).val = 24 := by
    rw [hRecLen]
    exact mkUsize_val_small (by omega)
  unfold expectedDirentParse
  rw [hStopVal]
  have hNotBad : (decide (24 > 256) || decide ((19#usize).val ≥ 24)) = false := by decide
  simp only [hNotBad, Bool.false_eq_true, ↓reduceIte]
  have hRegion : List.drop (19#usize).val (List.take 24 (overlayBuf256 (encodeDirent64 2 2 4#u8 [46#u8, 46#u8])
      (Array.repeat 256#usize 0#u8)).val) = [46#u8, 46#u8, 0#u8, 0#u8, 0#u8] := by
    have hTake : List.take 24 (overlayBuf256 (encodeDirent64 2 2 4#u8 [46#u8, 46#u8])
        (Array.repeat 256#usize 0#u8)).val = encodeDirent64 2 2 4#u8 [46#u8, 46#u8] := by
      rw [← hRecLen]
      exact overlayBuf256_take _ (by omega) _
    rw [hTake]
    decide
  rw [hRegion]
  decide

private theorem expectedDirentParse_overlay_neg1_lead0 :
    expectedDirentParse (overlayBuf256 (encodeDirent64 3 3 10#u8 [48#u8, 51#u8]) (Array.repeat 256#usize 0#u8)) 19#usize
      (mkUsize (List.length (encodeDirent64 3 3 10#u8 [48#u8, 51#u8]))) = (-1)#i32 := by
  have hRecLen : List.length (encodeDirent64 3 3 10#u8 [48#u8, 51#u8]) = 24 := by
    simp [encodeDirent64, encodeU64Le_len]
  have hStopVal : (mkUsize (List.length (encodeDirent64 3 3 10#u8 [48#u8, 51#u8]))).val = 24 := by
    rw [hRecLen]
    exact mkUsize_val_small (by omega)
  unfold expectedDirentParse
  rw [hStopVal]
  have hNotBad : (decide (24 > 256) || decide ((19#usize).val ≥ 24)) = false := by decide
  simp only [hNotBad, Bool.false_eq_true, ↓reduceIte]
  have hRegion : List.drop (19#usize).val (List.take 24 (overlayBuf256 (encodeDirent64 3 3 10#u8 [48#u8, 51#u8])
      (Array.repeat 256#usize 0#u8)).val) = [48#u8, 51#u8, 0#u8, 0#u8, 0#u8] := by
    have hTake : List.take 24 (overlayBuf256 (encodeDirent64 3 3 10#u8 [48#u8, 51#u8])
        (Array.repeat 256#usize 0#u8)).val = encodeDirent64 3 3 10#u8 [48#u8, 51#u8] := by
      rw [← hRecLen]
      exact overlayBuf256_take _ (by omega) _
    rw [hTake]
    decide
  rw [hRegion]
  decide

/-- Kernel proof of `test_postfork_parseDirentName_canonicalDecimalAndRoundTrip` for `rustAeneasApi`. -/
theorem test_postfork_parseDirentName_canonicalDecimalAndRoundTrip_allPass :
    Core.AllPass (test_postfork_parseDirentName_canonicalDecimalAndRoundTrip rustAeneasApi) := by
  intro buf start stop fdNat
  dsimp only
  refine ⟨parse_dirent_name_eq_expected buf start stop, ?_, ?_, ?_, ?_⟩
  · simp [rustAeneasApi, parse_dirent_name_eq_expected, expectedDirentParse_overlay_neg1_dot]
  · simp [rustAeneasApi, parse_dirent_name_eq_expected, expectedDirentParse_overlay_neg1_dotdot]
  · simp [rustAeneasApi, parse_dirent_name_eq_expected, expectedDirentParse_overlay_neg1_lead0]
  · intro hFd
    refine ⟨?_, trivial⟩
    simp only [rustAeneasApi, parse_dirent_name_eq_expected]
    congr 1
    set nm := natToAsciiBytes fdNat
    have hNmDef : nm = natDigitsFuel 12 fdNat [] := rfl
    have hBound : fdNat < 10 ^ 12 := by omega
    have hSpec := natDigitsFuel_spec 12 fdNat [] (by decide) hBound
      (fun _ h => nomatch h) (fun _ => rfl)
    dsimp only at hSpec
    rcases hSpec with ⟨hNmGe1, hNmLe12, hNmDig, hNmHead, hNmEval⟩
    simp only [List.length_nil, Nat.add_zero, Nat.pow_zero] at hNmLe12 hNmEval
    have hNmEval0 : foldDigits 0 nm = fdNat := by
      simpa [hNmDef, foldDigits] using hNmEval
    have hNmLen12 : nm.length ≤ 12 := by simpa [← hNmDef] using hNmLe12
    have hNmLenGe1 : 1 ≤ nm.length := by simpa [← hNmDef] using hNmGe1
    let reclen := (20 + nm.length + 7) / 8 * 8
    let padLen := reclen - 19 - nm.length
    have hSumGe : 19 + nm.length < reclen := by
      dsimp only [reclen]
      omega
    have hPadGe1 : 1 ≤ padLen := by dsimp only [padLen]; omega
    have hRecLe40 : reclen ≤ 40 := by dsimp only [reclen]; omega
    have hHdrLen : ∀ b0 b1 b2 : U8, (encodeU64Le 10 ++ encodeU64Le 10 ++ [b0, b1, b2]).length = 19 := by
      intro b0 b1 b2
      simp [encodeU64Le_len]
    have hRecLen : (encodeDirent64 10 10 10#u8 nm).length = reclen := by
      unfold encodeDirent64
      dsimp only
      rw [List.length_append, List.length_append, hHdrLen, List.length_replicate]
      change 19 + nm.length + (reclen - 19 - nm.length) = reclen
      omega
    set fdRec := encodeDirent64 10 10 10#u8 nm
    set zeroBuf := Array.repeat 256#usize 0#u8
    have hStopVal : (mkUsize fdRec.length).val = reclen := by
      rw [hRecLen]
      exact mkUsize_val_small (by omega)
    unfold expectedDirentParse
    have hNotBad : (decide ((mkUsize fdRec.length).val > 256) || decide ((19#usize).val ≥ (mkUsize fdRec.length).val)) = false := by
      rw [hStopVal]
      simp; omega
    simp only [hNotBad, Bool.false_eq_true, ↓reduceIte]
    have hOverlay : List.drop 19 (List.take reclen (overlayBuf256 fdRec zeroBuf).val) =
        nm ++ List.replicate padLen 0#u8 := by
      have hTake : List.take reclen (overlayBuf256 fdRec zeroBuf).val = fdRec := by
        rw [← hRecLen]
        exact overlayBuf256_take _ (by omega) _
      rw [hTake]
      unfold fdRec encodeDirent64
      dsimp only
      rw [List.append_assoc]
      exact List.drop_left' (hHdrLen _ _ _)
    have hRegionEq :
        List.drop (19#usize).val (List.take (mkUsize fdRec.length).val
          (overlayBuf256 fdRec zeroBuf).val) = nm ++ List.replicate padLen 0#u8 := by
      rw [show (19#usize).val = 19 from rfl, hStopVal, hOverlay]
    rw [hRegionEq]
    have hNoZeroInNm : ∀ b ∈ nm, (b == 0#u8) = false := by
      intro b hb
      have hbD := hNmDig b hb
      simp [isAsciiDigit] at hbD
      cases hEq : (b == 0#u8)
      · rfl
      · exfalso
        have hVal : b.val = 0 := congrArg UScalar.val (beq_iff_eq.mp hEq)
        omega
    have hFindNm : (nm ++ List.replicate padLen 0#u8).findIdx? (fun b => b == 0#u8) = some nm.length := by
      have hIdx : nm.length < (nm ++ List.replicate padLen 0#u8).length := by simp; omega
      refine list_findIdx?_eq_some_of_getElem _ _ nm.length hIdx ?_ ?_
      · intro j hj
        rw [List.getElem_append_left hj]
        exact hNoZeroInNm _ (List.getElem_mem _)
      · rw [List.getElem_append_right (Nat.le_refl _)]
        simp
    have hNmSucc : nm.length = Nat.succ (nm.length - 1) := by omega
    rw [hFindNm, hNmSucc]
    simp only
    rw [← hNmSucc]
    have hNotGeLen : ¬ (nm.length ≥ (nm ++ List.replicate padLen 0#u8).length) := by
      simp; omega
    simp only [hNotGeLen, ↓reduceIte]
    have hTakeNm : List.take nm.length (nm ++ List.replicate padLen 0#u8) = nm := by
      simp
    rw [hTakeNm]
    have hAllTrue : nm.all (fun b => decide (48#u8 ≤ b) && decide (b ≤ 57#u8)) = true := by
      rw [List.all_eq_true]
      intro b hb
      simpa [isAsciiDigit] using hNmDig b hb
    have hNotLead : (decide (nm.length > 1) && nm.head? == some 48#u8) = false := by
      by_cases h1 : nm.length > 1
      · simp only [h1, decide_true, Bool.true_and]
        exact beq_false_of_ne (hNmHead (by rwa [← hNmDef]))
      · simp [h1]
    have hNotGt : ¬ (List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 nm > 2147483647) := by
      have : List.foldl (fun acc b => acc * 10 + (b.val - 48)) 0 nm = fdNat := hNmEval0
      omega
    have hFoldNat : List.foldl (fun acc (b : U8) => acc * 10 + ((↑b : Nat) - 48)) 0 nm = fdNat := hNmEval0
    have hNotGtNat : ¬ (fdNat > 2147483647) := by omega
    simp only [hAllTrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotLead, hFoldNat, hNotGtNat]

/-- Witness reachability for `test_postfork_parseDirentName_canonicalDecimalAndRoundTrip`. -/
theorem test_postfork_parseDirentName_canonicalDecimalAndRoundTrip_canReach :
    Core.CanReach (test_postfork_parseDirentName_canonicalDecimalAndRoundTrip rustAeneasApi) := by
  have hAll := test_postfork_parseDirentName_canonicalDecimalAndRoundTrip_allPass
    (Array.repeat 256#usize 0#u8) 0#usize 0#usize 0
  dsimp only at hAll
  rcases hAll with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨Array.repeat 256#usize 0#u8, 0#usize, 0#usize, 0, h1, h2, h3, h4, by decide, h5 (by decide)⟩

end DirentParse

section WorldModelEdges

private theorem allPass_cond_assert (c : Bool) (P : Prop) (k : Unit → Core.AllPassRun Unit) (post : Unit → Prop)
    (hP : c = true → P) (hk : k () post) :
    (if c = true then (do Core.NondetTest.assert P; k ()) else k ()) post := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    exact ⟨hP hc, hk⟩
  · simp only [hc]
    exact hk

private theorem allPass_cond_assert2 (c : Bool) (P1 P2 : Prop) (k : Unit → Core.AllPassRun Unit) (post : Unit → Prop)
    (hP1 : c = true → P1) (hP2 : c = true → P2) (hk : k () post) :
    (if c = true then (do Core.NondetTest.assert P1; let __r ← Core.NondetTest.assert P2; k __r) else k ()) post := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    exact ⟨hP1 hc, hP2 hc, hk⟩
  · simp only [hc]
    exact hk

private theorem sys_close_range_running (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (first last flags : U32) :
    (¬ s.closeRangeSupported →
      OkPost (sys.close_range s first last flags) fun p =>
        p.1 = core.result.Result.Err (sanitizeErrno s.closeRangeErrno) ∧ p.2.fds = s.fds) ∧
    (s.closeRangeSupported →
      (first.val > last.val ∨ (flags &&& 4294967289#u32) != 0#u32) →
      OkPost (sys.close_range s first last flags) fun p =>
        p.1 = core.result.Result.Err EINVAL ∧ p.2.fds = s.fds) := by
  have hFault := currentFault_oracle_nil s hOr
  constructor
  · intro hNosup
    unfold sys.close_range
    have hCond : (!s.closeRangeSupported) = true := by simp [hNosup]
    simp only [hCond, ↓reduceIte, runUnitSyscall, hRun, hFault]
    exact ⟨_, rfl, rfl, rfl⟩
  · intro hSup hBad
    unfold sys.close_range
    have hNotNosup : (!s.closeRangeSupported) = false := by simp [hSup]
    have hCond : (decide (first.val > last.val) || (flags &&& 4294967289#u32 != 0#u32)) = true := by
      rcases hBad with h1 | h2
      · simp [h1]
      · simp [h2]
    simp only [hNotNosup, Bool.false_eq_true, ↓reduceIte, hCond, runUnitSyscall, hRun, hFault]
    exact ⟨_, rfl, rfl, rfl⟩

private theorem slice_from_val {α : Type} (l : List α) (h : l.length ≤ Usize.max) :
    (Slice.from l h).val = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simpa [Slice.from, Slice.val, Aeneas.Data.ListN.ListN.fromList, Aeneas.Data.ListN.ListN.toList] using
      ih (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h))

private theorem writeAll_epipe_first_step (s : ChildState)
    (hRun : s.status = .running) (hOr : s.oracle = [])
    (fd : I32) (hFdGe : 0#i32 ≤ fd)
    (payload : Slice U8) (hNonempty : !(↑payload : List U8).isEmpty = true)
    (e : FdEntry) (hGetFd : s.getFd (↑fd : Int) = some e)
    (readable : Bool) (readBytes : Bytes)
    (hGetDesc : s.getDesc e.desc = .stream readable true true readBytes) :
    OkPost (postfork.child.write_all s fd payload) fun p =>
      p.1 = core.result.Result.Err EPIPE ∧
      p.2.status = (if s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13 then .signaled 13#i32 else .running) := by
  have hFault := currentFault_oracle_nil s hOr
  unfold postfork.child.write_all
  have hNotNeg : ¬ (fd < 0#i32) := by
    change ¬ ((↑fd : Int) < 0); change (0 : Int) ≤ (↑fd : Int) at hFdGe; omega
  simp only [hNotNeg, ↓reduceIte]
  have hLenPos : 0 < payload.length := by
    cases h : (↑payload : List U8) with
    | nil => simp [h] at hNonempty
    | cons _ _ => simp [Slice.length, h]
  have hLtLen : 0#usize < payload.len := by change 0 < payload.length; exact hLenPos
  have hSlice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) payload
      { start := 0#usize, «end» := payload.len } = Result.ok payload := by
    change core.slice.index.SliceIndexRangeUsizeSlice.index { start := 0#usize, «end» := payload.len } payload = _
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index
    have hCond : 0#usize ≤ payload.len ∧ payload.len.val ≤ payload.length :=
      ⟨by change 0 ≤ payload.length; omega, Nat.le_refl _⟩
    simp only [hCond, and_self, ↓reduceIte]
    congr 1
    apply Slice.ext
    rw [slice_from_val]
    simp only [List.slice, show (0#usize).val = 0 from rfl, List.drop_zero]
    exact List.take_length
  have hEmptyFalse : (↑payload : List U8).isEmpty = false := by
    cases h : (↑payload : List U8) with
    | nil => simp [h] at hNonempty
    | cons _ _ => rfl
  have hNeEintr : (EPIPE != postfork.fd_ops.EINTR) = true := by simp [EPIPE, postfork.fd_ops.EINTR]
  have hLenNe0 : payload.len ≠ 0#usize := by
    intro h0
    have h0' : payload.length = 0 := by simpa using congrArg UScalar.val h0
    omega
  simp only [hLenNe0, ↓reduceIte]
  refine okPost_bind
    (P := fun res : sys.Sys × I32 × Bool =>
      res.2.1 = EPIPE ∧ res.2.2 = true ∧
      res.1.status = (if s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13 then .signaled 13#i32 else .running))
    ?_ ?_
  · rw [postfork.child.write_all_loop1]
    refine okPost_loop_decr_nat (fun _ => 0) (fun p => p = (s, 0#usize)) _ _ (s, 0#usize) ?_ rfl
    intro p hp
    rcases hp with rfl
    dsimp only
    unfold postfork.child.write_all_loop1.body
    simp only [hLtLen, ↓reduceIte, hSlice, bind_ok]
    unfold sys.write
    simp only [hRun, hGetFd, hGetDesc, hEmptyFalse, hFault, Bool.false_eq_true, ↓reduceIte]
    by_cases hSig : (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true
    · simp only [hSig, ↓reduceIte]
      refine ⟨ControlFlow.done ({ s with status := .signaled 13#i32, trace := s.trace ++ [⟨.write fd payload.val, .fatalSig 13#i32⟩] }, EPIPE, true), ?_, rfl, rfl, rfl⟩
      simp [EPIPE, postfork.fd_ops.EINTR]
    · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ControlFlow.done ({ s with status := .running, trace := s.trace ++ [⟨.write fd payload.val, .err EPIPE⟩] }, EPIPE, true), ?_, rfl, rfl, rfl⟩
      simp [EPIPE, postfork.fd_ops.EINTR]
  · intro ⟨s1, err, failed⟩ ⟨hErr, hFail, hSt⟩
    cases hFail
    dsimp only at hErr hSt
    rw [hErr]
    exact ⟨_, rfl, rfl, hSt⟩

private theorem worldModel_tail_allPass (s : ChildState) (hRun : s.status = .running)
    (hOr : s.oracle = []) (sig : I32) :
    (have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
        if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
          Core.NondetTest.assert (runner := Core.AllPassRun)
            (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
        else
          Core.NondetTest.assert (runner := Core.AllPassRun)
            (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid);
      if World.isInvalidSigactionSig sig = true then do
        Core.NondetTest.assert (OkPost (sys.sig_dfl s sig) fun p => p.1 = core.result.Result.Err EINVAL)
        let __r ← Core.NondetTest.assert (OkPost (sys.sig_ign s sig) fun p => p.1 = core.result.Result.Err EINVAL)
        __do_jp __r
      else __do_jp ()) (fun _ => True) := by
  have hTail : (if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
      Core.NondetTest.assert (runner := Core.AllPassRun)
        (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
    else
      Core.NondetTest.assert (runner := Core.AllPassRun)
        (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid)) (fun _ => True) := by
    by_cases hPid : (decide (s.pid > 0) && decide (s.pid = s.sid)) = true
    · simp only [hPid, ↓reduceIte]
      refine ⟨?_, trivial⟩
      obtain ⟨r, s', hEq, _, _, _, _, _, _, _, hErr, _, hOrP⟩ := sys_setpgid_self_running s hRun
      have hCondP : (s.pid == s.sid && decide (s.pid > 0)) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hPid ⊢
        exact ⟨hPid.2, hPid.1⟩
      have hEperm := (hOrP hOr).1 hCondP
      subst hEperm
      exact ⟨(core.result.Result.Err EPERM, s'), hEq, rfl, hErr _ rfl⟩
    · simp only [hPid, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, trivial⟩
      obtain ⟨r, s', hEq, _, _, _, _, _, _, _, _, hOk, hOrP⟩ := sys_setpgid_self_running s hRun
      have hCondP : (s.pid == s.sid && decide (s.pid > 0)) = false := by
        cases hGt : decide (s.pid > 0) <;> cases hEqS : (s.pid == s.sid) <;> simp_all [beq_iff_eq]
      have hOkR := (hOrP hOr).2 hCondP
      subst hOkR
      exact ⟨(core.result.Result.Ok (), s'), hEq, rfl, hOk rfl⟩
  by_cases hInv : World.isInvalidSigactionSig sig = true
  · simp only [hInv, ↓reduceIte]
    refine ⟨?_, ?_, hTail⟩
    · obtain ⟨r, s', hEq, _, _, _, _, _, _, _, _, _, hOrS⟩ := sys_sig_dfl_running s hRun sig
      have hErr := (hOrS hOr).1 hInv
      subst hErr
      exact ⟨(core.result.Result.Err EINVAL, s'), hEq, rfl⟩
    · obtain ⟨r, s', hEq, _, _, _, _, _, _, _, _, _, hOrS⟩ := sys_sig_ign_running s hRun sig
      have hErr := (hOrS hOr).1 hInv
      subst hErr
      exact ⟨(core.result.Result.Err EINVAL, s'), hEq, rfl⟩
  · simp only [hInv, Bool.false_eq_true, ↓reduceIte]
    exact hTail

/-- Kernel proof of `test_postfork_worldModel_linuxKernelEdgeInvariants` for `rustAeneasApi`. -/
theorem test_postfork_worldModel_linuxKernelEdgeInvariants_allPass :
    Core.AllPass (test_postfork_worldModel_linuxKernelEdgeInvariants rustAeneasApi) := by
  intro s fd newFd minFd first last crFlags sig path argHead argTail envp payload ⟨hRun, hOr⟩
  have hFault := currentFault_oracle_nil s hOr
  dsimp only [Core.AllPass, test_postfork_worldModel_linuxKernelEdgeInvariants]
  suffices hCloseRange :
      (have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
          have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
            have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
              if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
                Core.NondetTest.assert (runner := Core.AllPassRun)
                  (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
              else
                Core.NondetTest.assert (runner := Core.AllPassRun)
                  (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid);
            if World.isInvalidSigactionSig sig = true then do
              Core.NondetTest.assert (OkPost (sys.sig_dfl s sig) fun p => p.1 = core.result.Result.Err EINVAL)
              let __r ← Core.NondetTest.assert (OkPost (sys.sig_ign s sig) fun p => p.1 = core.result.Result.Err EINVAL)
              __do_jp __r
            else __do_jp ();
          match s.getFd (↑fd : Int) with
          | some e => do
            Core.NondetTest.assert (OkPost (sys.dup2 s fd fd) fun p => p.1 = core.result.Result.Ok () ∧ p.2.getFd (↑fd : Int) = some e)
            have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
              have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
                if (decide (0#i32 ≤ fd) && !(↑payload : List U8).isEmpty) = true then
                  match s.getDesc e.desc with
                  | .stream readable true true readBytes =>
                    if (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true then do
                      let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                        p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.signaled 13#i32)
                      __do_jp __r
                    else do
                      let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                        p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.running)
                      __do_jp __r
                  | _ => __do_jp ()
                else __do_jp ();
              if (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true then do
                let __r ← Core.NondetTest.assert (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.1 = core.result.Result.Err EINVAL ∧ p.2.fds = s.fds)
                __do_jp __r
              else __do_jp ()
            if (fd != newFd && (decide ((↑newFd : Int) < 0) || decide ((↑newFd : Int) ≥ s.fdLimit))) = true then do
              let __r ← Core.NondetTest.assert (OkPost (sys.dup2 s fd newFd) fun p => p.1 = core.result.Result.Err EBADF ∧ p.2.fds = s.fds)
              __do_jp __r
            else __do_jp ()
          | none => do
            let __r ← Core.NondetTest.assert (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.1 = core.result.Result.Err EBADF ∧ p.2.fds = s.fds)
            __do_jp __r;
        if (!s.closeRangeSupported) = true then do
          let __r ← Core.NondetTest.assert (OkPost (sys.close_range s first last crFlags) fun p =>
            p.1 = core.result.Result.Err (sanitizeErrno s.closeRangeErrno) ∧ p.2.fds = s.fds)
          __do_jp __r
        else
          if (decide (first.val > last.val) || crFlags &&& 4294967289#u32 != 0#u32) = true then do
            let __r ← Core.NondetTest.assert (OkPost (sys.close_range s first last crFlags) fun p =>
              p.1 = core.result.Result.Err EINVAL ∧ p.2.fds = s.fds)
            __do_jp __r
          else __do_jp ()) (fun _ => True) by
    by_cases hPath : (!path.isEmpty) = true
    · simp only [hPath, ↓reduceIte]
      have hEmptyFalse : path.isEmpty = false := by simpa using hPath
      refine ⟨?_, ?_, hCloseRange⟩
      · obtain ⟨err, s', hEq, _, _, _, _, _, _, _, _, hRes⟩ := sys_execve_running s hRun path [] envp
        simp only [hEmptyFalse, Bool.false_eq_true, ↓reduceIte, hFault] at hRes
        rcases hRes with ⟨hErr, hSt⟩
        subst hErr
        exact ⟨(_, s'), hEq, rfl, _, hSt, rfl⟩
      · obtain ⟨err, s', hEq, _, _, _, _, _, _, _, _, hRes⟩ := sys_execve_running s hRun path (argHead :: argTail) envp
        simp only [hEmptyFalse, Bool.false_eq_true, ↓reduceIte, hFault] at hRes
        rcases hRes with ⟨hErr, hSt⟩
        subst hErr
        exact ⟨(_, s'), hEq, rfl, _, hSt, rfl⟩
    · simp only [hPath, Bool.false_eq_true, ↓reduceIte]
      exact hCloseRange
  suffices hFdMatch :
      (have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
          have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
            if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
              Core.NondetTest.assert (runner := Core.AllPassRun)
                (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
            else
              Core.NondetTest.assert (runner := Core.AllPassRun)
                (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid);
          if World.isInvalidSigactionSig sig = true then do
            Core.NondetTest.assert (OkPost (sys.sig_dfl s sig) fun p => p.1 = core.result.Result.Err EINVAL)
            let __r ← Core.NondetTest.assert (OkPost (sys.sig_ign s sig) fun p => p.1 = core.result.Result.Err EINVAL)
            __do_jp __r
          else __do_jp ();
        match s.getFd (↑fd : Int) with
        | some e => do
          Core.NondetTest.assert (OkPost (sys.dup2 s fd fd) fun p => p.1 = core.result.Result.Ok () ∧ p.2.getFd (↑fd : Int) = some e)
          have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
            have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
              if (decide (0#i32 ≤ fd) && !(↑payload : List U8).isEmpty) = true then
                match s.getDesc e.desc with
                | .stream readable true true readBytes =>
                  if (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true then do
                    let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                      p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.signaled 13#i32)
                    __do_jp __r
                  else do
                    let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                      p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.running)
                    __do_jp __r
                | _ => __do_jp ()
              else __do_jp ();
            if (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true then do
              let __r ← Core.NondetTest.assert (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.1 = core.result.Result.Err EINVAL ∧ p.2.fds = s.fds)
              __do_jp __r
            else __do_jp ()
          if (fd != newFd && (decide ((↑newFd : Int) < 0) || decide ((↑newFd : Int) ≥ s.fdLimit))) = true then do
            let __r ← Core.NondetTest.assert (OkPost (sys.dup2 s fd newFd) fun p => p.1 = core.result.Result.Err EBADF ∧ p.2.fds = s.fds)
            __do_jp __r
          else __do_jp ()
        | none => do
          let __r ← Core.NondetTest.assert (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.1 = core.result.Result.Err EBADF ∧ p.2.fds = s.fds)
          __do_jp __r) (fun _ => True) by
    by_cases hNoSup : (!s.closeRangeSupported) = true
    · simp only [hNoSup, ↓reduceIte]
      have hNs : ¬ s.closeRangeSupported := by simpa using hNoSup
      exact ⟨(sys_close_range_running s hRun hOr first last crFlags).1 hNs, hFdMatch⟩
    · simp only [hNoSup, Bool.false_eq_true, ↓reduceIte]
      have hSup : s.closeRangeSupported := by
        revert hNoSup
        cases s.closeRangeSupported <;> simp
      by_cases hBad : (decide (first.val > last.val) || crFlags &&& 4294967289#u32 != 0#u32) = true
      · simp only [hBad, ↓reduceIte]
        have hBad' : first.val > last.val ∨ (crFlags &&& 4294967289#u32 != 0#u32) = true := by
          simpa [Bool.or_eq_true, decide_eq_true_eq] using hBad
        exact ⟨(sys_close_range_running s hRun hOr first last crFlags).2 hSup hBad', hFdMatch⟩
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte]
        exact hFdMatch
  cases hGetFd : s.getFd (↑fd : Int) with
  | none =>
    dsimp only
    obtain ⟨r, s', hEq, _, _, _, _, _, _, _, hErr, _, hOrF⟩ := sys_fcntl_dupfd_cloexec_running s hRun fd minFd
    have hOrF' := hOrF hOr
    rw [hGetFd] at hOrF'
    dsimp only at hOrF'
    subst hOrF'
    exact ⟨⟨(core.result.Result.Err EBADF, s'), hEq, rfl, hErr _ rfl⟩, worldModel_tail_allPass s hRun hOr sig⟩
  | some e =>
    dsimp only
    refine ⟨?_, ?_⟩
    · obtain ⟨r, s', hEq, _, _, _, _, _, _, _, _, hOk, hOrD⟩ := sys_dup2_running s hRun fd fd
      have hOpen : s.isOpen (↑fd : Int) = true := by simp [ChildState.isOpen, hGetFd]
      have hOkR := (hOrD hOr).2.2 ⟨hOpen, Or.inl rfl⟩
      subst hOkR
      have hFds := hOk rfl
      simp only [↓reduceIte] at hFds
      exact ⟨(core.result.Result.Ok (), s'), hEq, rfl, by simp only [ChildState.getFd, hFds]; exact hGetFd⟩
    · have hPipeStep :
          (have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
              have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
                if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
                  Core.NondetTest.assert (runner := Core.AllPassRun)
                    (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
                else
                  Core.NondetTest.assert (runner := Core.AllPassRun)
                    (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid);
              if World.isInvalidSigactionSig sig = true then do
                Core.NondetTest.assert (OkPost (sys.sig_dfl s sig) fun p => p.1 = core.result.Result.Err EINVAL)
                let __r ← Core.NondetTest.assert (OkPost (sys.sig_ign s sig) fun p => p.1 = core.result.Result.Err EINVAL)
                __do_jp __r
              else __do_jp ();
            if (decide (0#i32 ≤ fd) && !(↑payload : List U8).isEmpty) = true then
              match s.getDesc e.desc with
              | .stream readable true true readBytes =>
                if (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true then do
                  let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                    p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.signaled 13#i32)
                  __do_jp __r
                else do
                  let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                    p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.running)
                  __do_jp __r
              | _ => __do_jp ()
            else __do_jp ()) (fun _ => True) := by
        dsimp only
        by_cases hCond : (decide (0#i32 ≤ fd) && !((↑payload : List U8).isEmpty)) = true
        · simp only [hCond, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
          rcases hCond with ⟨hFdGe, hNonempty⟩
          cases hDesc : s.getDesc e.desc with
          | stream readable writable peerClosed readBytes =>
            cases writable
            · exact worldModel_tail_allPass s hRun hOr sig
            · cases peerClosed
              · exact worldModel_tail_allPass s hRun hOr sig
              · dsimp only
                by_cases hSig13 : (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true
                · simp only [hSig13, ↓reduceIte]
                  refine ⟨?_, worldModel_tail_allPass s hRun hOr sig⟩
                  simpa [rustAeneasApi, hSig13] using
                    writeAll_epipe_first_step s hRun hOr fd hFdGe payload hNonempty e hGetFd readable readBytes hDesc
                · simp only [hSig13, Bool.false_eq_true, ↓reduceIte]
                  refine ⟨?_, worldModel_tail_allPass s hRun hOr sig⟩
                  simpa [rustAeneasApi, hSig13] using
                    writeAll_epipe_first_step s hRun hOr fd hFdGe payload hNonempty e hGetFd readable readBytes hDesc
          | directory _ => exact worldModel_tail_allPass s hRun hOr sig
          | procSelfFd _ => exact worldModel_tail_allPass s hRun hOr sig
        · simp only [hCond, Bool.false_eq_true, ↓reduceIte]
          exact worldModel_tail_allPass s hRun hOr sig
      have hMinBadStep :
          (have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
              have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
                have __do_jp : Unit → Core.AllPassRun Unit := fun _ =>
                  if (decide (s.pid > 0) && decide (s.pid = s.sid)) = true then
                    Core.NondetTest.assert (runner := Core.AllPassRun)
                      (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Err EPERM ∧ p.2.pgid = s.pgid)
                  else
                    Core.NondetTest.assert (runner := Core.AllPassRun)
                      (OkPost (sys.setpgid_self s) fun p => p.1 = core.result.Result.Ok () ∧ p.2.pgid = s.pid);
                if World.isInvalidSigactionSig sig = true then do
                  Core.NondetTest.assert (OkPost (sys.sig_dfl s sig) fun p => p.1 = core.result.Result.Err EINVAL)
                  let __r ← Core.NondetTest.assert (OkPost (sys.sig_ign s sig) fun p => p.1 = core.result.Result.Err EINVAL)
                  __do_jp __r
                else __do_jp ();
              if (decide (0#i32 ≤ fd) && !(↑payload : List U8).isEmpty) = true then
                match s.getDesc e.desc with
                | .stream readable true true readBytes =>
                  if (s.getSig 13 == Disp.default && s.pid != 1 && !s.isSigBlocked 13) = true then do
                    let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                      p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.signaled 13#i32)
                    __do_jp __r
                  else do
                    let __r ← Core.NondetTest.assert (OkPost (rustAeneasApi.writeAll s fd payload) fun p =>
                      p.1 = core.result.Result.Err EPIPE ∧ p.2.status = World.Status.running)
                    __do_jp __r
                | _ => __do_jp ()
              else __do_jp ();
            if (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true then do
              let __r ← Core.NondetTest.assert (OkPost (sys.fcntl_dupfd_cloexec s fd minFd) fun p => p.1 = core.result.Result.Err EINVAL ∧ p.2.fds = s.fds)
              __do_jp __r
            else __do_jp ()) (fun _ => True) := by
        dsimp only
        by_cases hMinBad : (decide ((↑minFd : Int) < 0) || decide ((↑minFd : Int) ≥ s.fdLimit)) = true
        · simp only [hMinBad, ↓reduceIte]
          refine ⟨?_, hPipeStep⟩
          obtain ⟨r, s', hEq, _, _, _, _, _, _, _, hErr, _, hOrF⟩ := sys_fcntl_dupfd_cloexec_running s hRun fd minFd
          have hOrF' := hOrF hOr
          rw [hGetFd] at hOrF'
          cases hLow : findLowestFreeFd s (↑minFd : Int) with
          | none =>
            rw [hLow] at hOrF'
            simp only [hMinBad, ↓reduceIte] at hOrF'
            subst hOrF'
            exact ⟨(core.result.Result.Err EINVAL, s'), hEq, rfl, hErr _ rfl⟩
          | some dstInt =>
            rw [hLow] at hOrF'
            simp only [hMinBad, ↓reduceIte] at hOrF'
            subst hOrF'
            exact ⟨(core.result.Result.Err EINVAL, s'), hEq, rfl, hErr _ rfl⟩
        · simp only [hMinBad, Bool.false_eq_true, ↓reduceIte]
          exact hPipeStep
      by_cases hBadNew : (fd != newFd && (decide ((↑newFd : Int) < 0) || decide ((↑newFd : Int) ≥ s.fdLimit))) = true
      · simp only [hBadNew, ↓reduceIte]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hBadNew
        obtain ⟨hNe, hLimNew⟩ := hBadNew
        have hNeInt : (↑fd : Int) ≠ (↑newFd : Int) := fun h => hNe (IScalar.eq_of_val_eq h)
        have hOpen : s.isOpen (↑fd : Int) = true := by simp [ChildState.isOpen, hGetFd]
        obtain ⟨r, s', hEq, _, _, _, _, _, _, _, hErr, _, hOrD⟩ := sys_dup2_running s hRun fd newFd
        have hBadR := (hOrD hOr).2.1 ⟨hOpen, hNeInt, hLimNew⟩
        subst hBadR
        exact ⟨⟨(core.result.Result.Err EBADF, s'), hEq, rfl, hErr _ rfl⟩, hMinBadStep⟩
      · simp only [hBadNew, Bool.false_eq_true, ↓reduceIte]
        exact hMinBadStep

/-- Witness reachability for `test_postfork_worldModel_linuxKernelEdgeInvariants`. -/
theorem test_postfork_worldModel_linuxKernelEdgeInvariants_canReach :
    Core.CanReach (test_postfork_worldModel_linuxKernelEdgeInvariants rustAeneasApi) := by
  let s₀ : ChildState := { status := .running, oracle := [] }
  let pay₀ : Slice U8 := Slice.from [] (by simp)
  have hAll := test_postfork_worldModel_linuxKernelEdgeInvariants_allPass
    s₀ 0#i32 0#i32 0#i32 0#u32 0#u32 0#u32 0#i32 [47#u8] [97#u8] [] [] pay₀ ⟨rfl, rfl⟩
  dsimp only [Core.AllPass, test_postfork_worldModel_linuxKernelEdgeInvariants] at hAll
  dsimp only [Core.CanReach, test_postfork_worldModel_linuxKernelEdgeInvariants]
  exact ⟨s₀, 0#i32, 0#i32, 0#i32, 0#u32, 0#u32, 0#u32, 0#i32, [47#u8], [97#u8], [], [], pay₀, ⟨rfl, rfl⟩, hAll⟩

end WorldModelEdges


end LeanSwe.PostFork.Proofs

import LeanSwe.Tar.Proofs.ConcreteUnpackHelpers

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem test6_paxZeroFile_ok :
    ∃ res, Impl.unpackWith { maxTotalBytes := 0 }
      (mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkRegularFrame "a.txt" ByteArray.empty ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  let pax := encodePaxRecord "path" "a.txt"
  let reg := mkRegularFrame "a.txt" ByteArray.empty
  let post := reg ++ twoZeroBlocks
  let bytes := mkPaxFrame pax ++ reg ++ twoZeroBlocks
  have hpax_rec_sz : pax.size = 14 := by
    dsimp only [pax]; unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : (mkPaxFrame pax).size = 1024 := by rw [mkPaxFrame_size, hpax_rec_sz]; decide
  have hreg_sz : reg.size = 512 := by
    dsimp only [reg]; rw [mkRegularFrame_size, ByteArray.size_empty]; decide
  have hsz : bytes.size = 2560 := by
    simp [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hpax_ext : parsePaxPayload pax 0 = .ok { path? := some "a.txt" } := parsePax_path_a 0
  have hstep1 := unpackLoop_mkPaxFrame_step_any { maxTotalBytes := 0 } ByteArray.empty post pax [] [] 0
    (by rw [hpax_rec_sz]; decide) { path? := some "a.txt" } hpax_ext
  have hassoc1 : ByteArray.empty ++ mkPaxFrame pax ++ post = bytes := by
    simp [bytes, post, ByteArray.empty_append, ByteArray.append_assoc]
  rw [hassoc1, ByteArray.size_empty, hpax_rec_sz] at hstep1
  have h1024 : (0 + 512 + pad512 14 : Nat) = 1024 := by decide
  rw [h1024] at hstep1
  let regHdr := mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" ""
  have hregHdr : regHdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hreg_eq : reg = regHdr := by
    dsimp only [reg, mkRegularFrame, regHdr, padBlock512, ByteArray.size_empty]
    simp [ByteArray.append_empty]
  have hext2 : bytes.extract 1024 (1024 + 512) = regHdr := by
    have hbytes' : bytes = mkPaxFrame pax ++ regHdr ++ twoZeroBlocks := by rw [← hreg_eq]
    have hsub := extract_append_mid (mkPaxFrame pax) regHdr twoZeroBlocks
    rw [hpax_sz, hregHdr] at hsub
    rw [hbytes', hsub]
  have hnz2 : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext2
  have hparse2 : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hsz]; omega) hext2
  have hdec2 := decodeTarEntry_mkUstarHeader_regular { maxTotalBytes := 0 } bytes regHdr 1024
    (some { path? := some "a.txt" }) [] 0 0
    (by rw [hsz]; omega) hext2 rfl
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by rw [hsz]; decide) (name := "a.txt") (normPath := "a.txt") rfl rfl
  have htail := unpackLoop_at_twoZeroBlocks { maxTotalBytes := 0 } (mkPaxFrame pax ++ reg) ["a.txt"]
    [{ path := "a.txt", kind := .regular, mode := 0o644 }] 0
  rw [ByteArray.size_append, hpax_sz, hreg_sz] at htail
  have hmod : (((0o644 : UInt32) &&& 0o7777).toNat).toUInt32 = 0o644 := rfl
  have hu : Impl.unpackWith { maxTotalBytes := 0 } bytes = .ok [{ path := "a.txt", kind := .regular, mode := 0o644 }] := by
    unfold Impl.unpackWith
    rw [hnz, hstep1, unpackLoop.eq_1]
    have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
    have hnotgt : ¬1024 + 512 > bytes.size := by rw [hsz]; omega
    have h78 : ((0x30 : UInt8) == 0x78) = false := rfl
    have hpad0 : pad512 0 = 0 := rfl
    simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
    rw [unpackStep.eq_1]
    simp only [List.length_nil, hnotge, ↓reduceIte, hnz2, Bool.false_eq_true, hnotgt, hparse2, h78, hdec2, hmod]
    simp only [Option.getD, beq_self_eq_true, ↓reduceIte, ByteArray.size_empty, Nat.add_zero, hpad0,
      (by decide : (1024 + 512 : Nat) > 1024)]
    rw [show bytes = mkPaxFrame pax ++ reg ++ (zeroBlock ++ zeroBlock) from rfl]
    rw [htail]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  dsimp only [bytes, pax, reg] at hu
  exact ⟨[{ path := "a.txt", kind := .regular }], hu, tarEquiv_singleton_self _⟩

private theorem test6_bigSizePax_errs :
    (∃ e, Impl.unpackWith { maxTotalBytes := 1024 }
        (mkPaxFrame (encodePaxRecord "size" "8589934592") ++ mkRegularFrame "big.bin" ByteArray.empty ++ twoZeroBlocks) =
        .error e ∧ e.kind = .resourceLimitExceeded ∧ e.message ≠ "") ∧
    (∃ e, Impl.unpackWith { maxTotalBytes := 10737418240 }
        (mkPaxFrame (encodePaxRecord "size" "8589934592") ++ mkRegularFrame "big.bin" ByteArray.empty ++ twoZeroBlocks) =
        .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ "") := by
  let pax := encodePaxRecord "size" "8589934592"
  let reg := mkRegularFrame "big.bin" ByteArray.empty
  let post := reg ++ twoZeroBlocks
  let bytes := mkPaxFrame pax ++ reg ++ twoZeroBlocks
  have hpax_rec_sz : pax.size = 19 := by
    dsimp only [pax]; unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : (mkPaxFrame pax).size = 1024 := by rw [mkPaxFrame_size, hpax_rec_sz]; decide
  have hreg_sz : reg.size = 512 := by
    dsimp only [reg]; rw [mkRegularFrame_size, ByteArray.size_empty]; decide
  have hsz : bytes.size = 2560 := by
    simp [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hpax_ext : parsePaxPayload pax 0 = .ok { size? := some 8589934592 } := parsePax_size_8g 0
  let regHdr := mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" ""
  have hregHdr : regHdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hreg_eq : reg = regHdr := by
    dsimp only [reg, mkRegularFrame, regHdr, padBlock512, ByteArray.size_empty]
    simp [ByteArray.append_empty]
  have hext2 : bytes.extract 1024 (1024 + 512) = regHdr := by
    have hbytes' : bytes = mkPaxFrame pax ++ regHdr ++ twoZeroBlocks := by rw [← hreg_eq]
    have hsub := extract_append_mid (mkPaxFrame pax) regHdr twoZeroBlocks
    rw [hpax_sz, hregHdr] at hsub
    rw [hbytes', hsub]
  have hnz2 : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext2
  have hparse2 : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hsz]; omega) hext2
  have hassoc1 : ByteArray.empty ++ mkPaxFrame pax ++ post = bytes := by
    simp [bytes, post, ByteArray.empty_append, ByteArray.append_assoc]
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬1024 + 512 > bytes.size := by rw [hsz]; omega
  have h1024 : (0 + 512 + pad512 19 : Nat) = 1024 := by decide
  constructor
  · have hstep1 := unpackLoop_mkPaxFrame_step_any { maxTotalBytes := 1024 } ByteArray.empty post pax [] [] 0
      (by rw [hpax_rec_sz]; decide) { size? := some 8589934592 } hpax_ext
    rw [hassoc1, ByteArray.size_empty, hpax_rec_sz, h1024] at hstep1
    have hu : ∃ e, Impl.unpackWith { maxTotalBytes := 1024 } bytes = .error e ∧
        e.kind = .resourceLimitExceeded ∧ e.message ≠ "" := by
      unfold Impl.unpackWith
      rw [hnz, hstep1, unpackLoop.eq_1]
      simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
      rw [unpackStep.eq_1]
      simp only [List.length_nil, hnotge, ↓reduceIte, hnz2, Bool.false_eq_true, hnotgt, hparse2,
        (by decide : ((0x30 : UInt8) == 0x78) = false)]
      rw [decodeTarEntry.eq_1]
      simp only [Option.getD, ↓reduceIte,
        (by decide : ((0x30 : UInt8) == 0x30) = true),
        (by decide : ¬(0 + 1 > ({ maxTotalBytes := 1024 } : UnpackOptions).maxEntries)),
        (by decide : 0 + 8589934592 > ({ maxTotalBytes := 1024 } : UnpackOptions).maxTotalBytes)]
      exact ⟨_, rfl, rfl, by decide⟩
    exact hu
  · have hstep1 := unpackLoop_mkPaxFrame_step_any { maxTotalBytes := 10737418240 } ByteArray.empty post pax [] [] 0
      (by rw [hpax_rec_sz]; decide) { size? := some 8589934592 } hpax_ext
    rw [hassoc1, ByteArray.size_empty, hpax_rec_sz, h1024] at hstep1
    have htrunc : 1024 + 512 + pad512 8589934592 > bytes.size := by
      rw [hsz]
      have hp := le_pad512 8589934592
      omega
    have hu : ∃ e, Impl.unpackWith { maxTotalBytes := 10737418240 } bytes = .error e ∧
        e.kind = .truncatedArchive ∧ e.message ≠ "" := by
      unfold Impl.unpackWith
      rw [hnz, hstep1, unpackLoop.eq_1]
      simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
      rw [unpackStep.eq_1]
      simp only [List.length_nil, hnotge, ↓reduceIte, hnz2, Bool.false_eq_true, hnotgt, hparse2,
        (by decide : ((0x30 : UInt8) == 0x78) = false)]
      rw [decodeTarEntry.eq_1]
      simp only [Option.getD, ↓reduceIte, htrunc,
        (by decide : ((0x30 : UInt8) == 0x30) = true),
        (by decide : ¬(0 + 1 > ({ maxTotalBytes := 10737418240 } : UnpackOptions).maxEntries)),
        (by decide : ¬(0 + 8589934592 > ({ maxTotalBytes := 10737418240 } : UnpackOptions).maxTotalBytes))]
      exact ⟨_, rfl, rfl, by decide⟩
    exact hu

private theorem test6_limits_errs :
    (let regFrame := mkRegularFrame "a.txt" "hello".toUTF8
     ∃ e, Impl.unpackWith { maxEntries := 0 } (regFrame ++ twoZeroBlocks) = .error e ∧
       e.kind = .resourceLimitExceeded ∧ e.message ≠ "") ∧
    (let regFrame := mkRegularFrame "a.txt" "hello".toUTF8
     ∃ e, Impl.unpackWith { maxTotalBytes := 4 } (regFrame ++ twoZeroBlocks) = .error e ∧
       e.kind = .resourceLimitExceeded ∧ e.message ≠ "") := by
  let regFrame := mkRegularFrame "a.txt" "hello".toUTF8
  have hhello_sz : ("hello".toUTF8).size = 5 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhello_sz]; decide
  let regHdr := mkUstarHeader "a.txt" 0o644 0 0 5 0 0x30 "" "" "" ""
  have hregHdr : regHdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hext_reg : ∀ bytes, bytes = regFrame ++ twoZeroBlocks →
      bytes.size = 2048 ∧ bytes.extract 0 512 = regHdr := by
    intro bytes hb
    have hsz : bytes.size = 2048 := by rw [hb, ByteArray.size_append, hreg_sz, twoZeroBlocks_size]
    have hsub := extract_append_mid ByteArray.empty regHdr (padBlock512 "hello".toUTF8 ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hregHdr] at hsub
    have hb' : bytes = regHdr ++ (padBlock512 "hello".toUTF8 ++ twoZeroBlocks) := by
      rw [hb]; simp only [regFrame, mkRegularFrame, regHdr, ByteArray.append_assoc, hhello_sz]
    exact ⟨hsz, by rw [hb', hsub]⟩
  constructor
  · have ⟨hsz, hext⟩ := hext_reg (regFrame ++ twoZeroBlocks) rfl
    have hnz : ((regFrame ++ twoZeroBlocks).size == 0 || (regFrame ++ twoZeroBlocks).size % 512 != 0) = false := by
      rw [hsz]; rfl
    have hnz0 : isZeroRange (regFrame ++ twoZeroBlocks) 0 512 = false :=
      isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
    have hparse0 : parseUstarHeader (regFrame ++ twoZeroBlocks) 0 =
        .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 5, mtime := 0, typeflag := 0x30 } :=
      parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
    change ∃ e, Impl.unpackWith { maxEntries := 0 } (regFrame ++ twoZeroBlocks) = .error e ∧
      e.kind = .resourceLimitExceeded ∧ e.message ≠ ""
    unfold Impl.unpackWith
    rw [hnz, unpackLoop.eq_1]
    have hnotge : ¬0 ≥ (regFrame ++ twoZeroBlocks).size := by rw [hsz]; omega
    have hnotgt : ¬0 + 512 > (regFrame ++ twoZeroBlocks).size := by rw [hsz]; omega
    simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
    rw [unpackStep.eq_1]
    simp only [List.length_nil, hnotge, ↓reduceIte, hnz0, Bool.false_eq_true, hnotgt, hparse0,
      (by decide : ((0x30 : UInt8) == 0x78) = false)]
    rw [decodeTarEntry.eq_1]
    simp only [Option.getD, ↓reduceIte,
      (by decide : ((0x30 : UInt8) == 0x30) = true),
      (by decide : 0 + 1 > ({ maxEntries := 0 } : UnpackOptions).maxEntries)]
    exact ⟨_, rfl, rfl, by decide⟩
  · have ⟨hsz, hext⟩ := hext_reg (regFrame ++ twoZeroBlocks) rfl
    have hnz : ((regFrame ++ twoZeroBlocks).size == 0 || (regFrame ++ twoZeroBlocks).size % 512 != 0) = false := by
      rw [hsz]; rfl
    have hnz0 : isZeroRange (regFrame ++ twoZeroBlocks) 0 512 = false :=
      isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
    have hparse0 : parseUstarHeader (regFrame ++ twoZeroBlocks) 0 =
        .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 5, mtime := 0, typeflag := 0x30 } :=
      parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
    change ∃ e, Impl.unpackWith { maxTotalBytes := 4 } (regFrame ++ twoZeroBlocks) = .error e ∧
      e.kind = .resourceLimitExceeded ∧ e.message ≠ ""
    unfold Impl.unpackWith
    rw [hnz, unpackLoop.eq_1]
    have hnotge : ¬0 ≥ (regFrame ++ twoZeroBlocks).size := by rw [hsz]; omega
    have hnotgt : ¬0 + 512 > (regFrame ++ twoZeroBlocks).size := by rw [hsz]; omega
    simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
    rw [unpackStep.eq_1]
    simp only [List.length_nil, hnotge, ↓reduceIte, hnz0, Bool.false_eq_true, hnotgt, hparse0,
      (by decide : ((0x30 : UInt8) == 0x78) = false)]
    rw [decodeTarEntry.eq_1]
    simp only [Option.getD, ↓reduceIte, Nat.zero_add,
      (by decide : ((0x30 : UInt8) == 0x30) = true),
      (by decide : ¬(0 + 1 > ({ maxTotalBytes := 4 } : UnpackOptions).maxEntries)),
      (by decide : 5 > ({ maxTotalBytes := 4 } : UnpackOptions).maxTotalBytes)]
    exact ⟨_, rfl, rfl, by decide⟩

private theorem test6_hugePax_err :
    ∃ e, Impl.unpackWith {}
      (mkUstarHeader "././@PaxHeader" 420 0 0 (maxPaxHeaderBytes + 1) 0 120 "" "" "" "" ++ twoZeroBlocks) = .error e ∧
      e.kind = .resourceLimitExceeded ∧ e.message ≠ "" := by
  let hugePaxHdr := mkUstarHeader "././@PaxHeader" 420 0 0 (maxPaxHeaderBytes + 1) 0 120 "" "" "" ""
  have hhuge : hugePaxHdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  let bytes := hugePaxHdr ++ twoZeroBlocks
  have hsz : bytes.size = 1536 := by
    simp [bytes, ByteArray.size_append, hhuge, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hext : bytes.extract 0 512 = hugePaxHdr := by
    have hsub := extract_append_mid ByteArray.empty hugePaxHdr twoZeroBlocks
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhuge] at hsub
    exact hsub
  have hnz0 : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
  have hparse0 : parseUstarHeader bytes 0 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := maxPaxHeaderBytes + 1, mtime := 0, typeflag := 120 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
  have hgt : maxPaxHeaderBytes + 1 > maxPaxHeaderBytes := by omega
  have h78 : ((120 : UInt8) == 0x78) = true := rfl
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .resourceLimitExceeded ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, unpackLoop.eq_1]
  have hnotge : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [hnotge, hnz0, Bool.false_eq_true, hnotgt, hparse0, h78, Option.isSome_none, hgt, ↓reduceIte]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem allPass_let_match_unpackWith_ok
    (opts : UnpackOptions) (bytes : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith opts bytes = .ok res)
    (p : List TarEntry → Prop) (k : Unit → Core.AllPassRun Unit) :
    AllPass (have x := bytes; have jp := k;
      match defaultApi.unpackWith opts x with
      | .error _ => Bind.bind (assert False) jp
      | .ok r => Bind.bind (assert (p r)) jp) ↔
    p res ∧ AllPass (k ()) := by
  dsimp only
  rw [defaultApi_unpackWith_eq, h]
  exact allPass_assert_bind (p res) k

private theorem allPass_app_let_checkUnpackError_bind2
    (bytes : ByteArray) (opts₁ opts₂ : UnpackOptions) (k₁ k₂ : TarErrorKind)
    (h₁ : ∃ e, Impl.unpackWith opts₁ bytes = .error e ∧ e.kind = k₁ ∧ e.message ≠ "")
    (h₂ : ∃ e, Impl.unpackWith opts₂ bytes = .error e ∧ e.kind = k₂ ∧ e.message ≠ "")
    (tail : Core.AllPassRun Unit) (ht : AllPass tail) :
    AllPass ((fun (_ : Unit) => have b := bytes;
      Bind.bind (checkUnpackError defaultApi opts₁ b k₁) fun _ =>
      Bind.bind (checkUnpackError defaultApi opts₂ b k₂) fun _ => tail) ()) := by
  dsimp only
  exact allPass_checkUnpackError_bind opts₁ bytes k₁ _ h₁
    (allPass_checkUnpackError_bind opts₂ bytes k₂ _ h₂ ht)

private theorem allPass_let_checkUnpackError
    (bytes : ByteArray) (opts : UnpackOptions) (k : TarErrorKind)
    (h : ∃ e, Impl.unpackWith opts (bytes ++ twoZeroBlocks) = .error e ∧ e.kind = k ∧ e.message ≠ "") :
    AllPass (have x : ByteArray := bytes; checkUnpackError defaultApi opts (x ++ twoZeroBlocks) k) := by
  dsimp only
  exact allPass_checkUnpackError opts (bytes ++ twoZeroBlocks) k h

/-- Prove `test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_resourceLimitsAndLargePaxSize_enforced :
    AllPass (test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced defaultApi) := by
  have ⟨herr_entries, herr_bytes⟩ := test6_limits_errs
  have herr_huge := test6_hugePax_err
  have ⟨resZero, hzero_ok, hzero_teq⟩ := test6_paxZeroFile_ok
  have ⟨hbig1, hbig2⟩ := test6_bigSizePax_errs
  unfold test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced
  refine allPass_checkUnpackError_bind { maxEntries := 0 } _ _ _ herr_entries ?_
  refine allPass_checkUnpackError_bind { maxTotalBytes := 4 } _ _ _ herr_bytes ?_
  refine (allPass_let_match_unpackWith_ok { maxTotalBytes := 0 } _ resZero hzero_ok _ _).mpr ⟨hzero_teq, ?_⟩
  refine allPass_app_let_checkUnpackError_bind2 _ { maxTotalBytes := 1024 } { maxTotalBytes := 10737418240 }
    .resourceLimitExceeded .truncatedArchive hbig1 hbig2 _ ?_
  exact allPass_let_checkUnpackError _ {} .resourceLimitExceeded herr_huge

end LeanSwe.Tar.Proofs

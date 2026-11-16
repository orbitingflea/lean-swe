import LeanSwe.Tar.Proofs.ConcreteUnpackHelpers

set_option Elab.async false

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem getElem_append_right_eq {a b : ByteArray} {i j : Nat}
    (hle : a.size ≤ i) (hab : i < (a ++ b).size) (hj : i - a.size = j) (_hb : j < b.size) :
    (a ++ b)[i] = b[j] := by
  subst hj
  exact getElem_append_right hle hab

private theorem getElem_append_right_idx {a b : ByteArray} {i : Nat} (j : Nat)
    (hle : a.size ≤ i) (hab : i < (a ++ b).size) (hj : i - a.size = j) (_hb : j < b.size) :
    (a ++ b)[i] = b[j] := by
  subst hj
  exact getElem_append_right hle hab

private theorem test4_h1 :
    ∃ e, Impl.unpackWith {} ByteArray.empty = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ "" :=
  ⟨_, rfl, rfl, by decide⟩

private theorem test4_h2 :
    ∃ e, Impl.unpackWith {} { data := #[0] } = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ "" :=
  ⟨_, rfl, rfl, by decide⟩

private theorem test4_h3 :
    ∃ e, Impl.unpackWith {} (twoZeroBlocks ++ { data := #[1] }) = .error e ∧
      e.kind = .truncatedArchive ∧ e.message ≠ "" := by
  have hsz : (twoZeroBlocks ++ { data := #[1] }).size = 1025 := by
    rw [ByteArray.size_append, twoZeroBlocks_size]; rfl
  have hbd : ((twoZeroBlocks ++ { data := #[1] }).size == 0 ||
      (twoZeroBlocks ++ { data := #[1] }).size % 512 != 0) = true := by rw [hsz]; rfl
  have hbd' : (twoZeroBlocks ++ { data := #[1] }).size == 0 ||
      (twoZeroBlocks ++ { data := #[1] }).size % 512 != 0 := hbd
  unfold Impl.unpackWith
  rw [ite_eq_left_of_eq_true _ _ (eq_true hbd')]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_h4 :
    let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
    ∃ e, Impl.unpackWith {} regFrame = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ "" := by
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhi_sz]; decide
  have hnz : (regFrame.size == 0 || regFrame.size % 512 != 0) = false := by rw [hreg_sz]; rfl
  have hassoc : ByteArray.empty ++ mkRegularFrame "a.txt" "hi".toUTF8 ++ ByteArray.empty = regFrame := by
    simp only [regFrame, ByteArray.empty_append, ByteArray.append_empty]
  have hstep := unpackLoop_mkRegularFrame_step {} ByteArray.empty ByteArray.empty "a.txt" "hi".toUTF8 [] [] 0
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by rw [hhi_sz]; decide) (by decide) (by rw [hhi_sz]; decide)
    (normPath := "a.txt") rfl rfl
  rw [hassoc, ByteArray.size_empty, hhi_sz] at hstep
  have hpad2 : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  rw [hpad2] at hstep
  change ∃ e, Impl.unpackWith {} regFrame = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  simp [hreg_sz]

private theorem test4_h5 :
    let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
    ∃ e, Impl.unpackWith {} (regFrame ++ zeroBlock) = .error e ∧
      e.kind = .truncatedArchive ∧ e.message ≠ "" := by
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhi_sz]; decide
  let bytes := regFrame ++ zeroBlock
  have hsz : bytes.size = 1536 := by simp [bytes, ByteArray.size_append, hreg_sz, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hassoc : ByteArray.empty ++ mkRegularFrame "a.txt" "hi".toUTF8 ++ zeroBlock = bytes := by
    simp only [bytes, regFrame, ByteArray.empty_append]
  have hstep := unpackLoop_mkRegularFrame_step {} ByteArray.empty zeroBlock "a.txt" "hi".toUTF8 [] [] 0
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by rw [hhi_sz]; decide) (by decide) (by rw [hhi_sz]; decide)
    (normPath := "a.txt") rfl rfl
  rw [hassoc, ByteArray.size_empty, hhi_sz] at hstep
  have hpad2 : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  rw [hpad2] at hstep
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1024 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi hlt
    change bytes[1024 + i] = 0
    have ha : regFrame.size ≤ 1024 + i := by rw [hreg_sz]; omega
    have hb : 1024 + i < (regFrame ++ zeroBlock).size := by rw [ByteArray.size_append, hreg_sz, zeroBlock_size]; omega
    simp only [bytes]
    rw [getElem_append_right ha hb]
    have h1024 : 1024 + i - regFrame.size = i := by rw [hreg_sz]; omega
    simp only [h1024]
    exact zeroBlock_getElem _
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  have hge2 : 1024 + 512 ≥ bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp [hnotge, hz1, hge2]

private theorem test4_h6 :
    let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
    ∃ e, Impl.unpackWith {} (regFrame ++ zeroBlock ++ regFrame) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhi_sz]; decide
  let bytes := regFrame ++ zeroBlock ++ regFrame
  have hsz : bytes.size = 2560 := by simp [bytes, ByteArray.size_append, hreg_sz, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hassoc : ByteArray.empty ++ mkRegularFrame "a.txt" "hi".toUTF8 ++ (zeroBlock ++ regFrame) = bytes := by
    simp only [bytes, regFrame, ByteArray.empty_append, ByteArray.append_assoc]
  have hstep := unpackLoop_mkRegularFrame_step {} ByteArray.empty (zeroBlock ++ regFrame) "a.txt" "hi".toUTF8 [] [] 0
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by rw [hhi_sz]; decide) (by decide) (by rw [hhi_sz]; decide)
    (normPath := "a.txt") rfl rfl
  rw [hassoc, ByteArray.size_empty, hhi_sz] at hstep
  have hpad2 : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  rw [hpad2] at hstep
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1024 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi hlt0
    change bytes[1024 + i] = 0
    have hlt : 1024 + i < (regFrame ++ zeroBlock).size := by rw [ByteArray.size_append, hreg_sz, zeroBlock_size]; omega
    have ha : regFrame.size ≤ 1024 + i := by rw [hreg_sz]; omega
    simp only [bytes]
    rw [getElem_append_left hlt hlt0, getElem_append_right ha hlt]
    have h1024 : 1024 + i - regFrame.size = i := by rw [hreg_sz]; omega
    simp only [h1024]
    exact zeroBlock_getElem _
  have hext2 : bytes.extract 1536 (1536 + 512) = mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" := by
    have ha : (regFrame ++ zeroBlock).size = 1536 := by rw [ByteArray.size_append, hreg_sz, zeroBlock_size]
    have hsub := extract_append_mid (regFrame ++ zeroBlock)
      (mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "") (padBlock512 "hi".toUTF8)
    rw [ha, mkUstarHeader_size] at hsub
    have hbytes' : bytes = (regFrame ++ zeroBlock) ++ mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" ++
        padBlock512 "hi".toUTF8 := by
      simp only [bytes, regFrame, mkRegularFrame, ByteArray.append_assoc, hhi_sz]
    rw [hbytes', hsub]
  have hnz2 : isZeroRange bytes 1536 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext2
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  have hnotge2 : ¬1024 + 512 ≥ bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp [hnotge, hz1, hnotge2, hnz2]

private theorem test4_h7 :
    let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
    ∃ e, Impl.unpackWith {} paxHdr = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ "" := by
  let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
  have hpax_rec_sz : (encodePaxRecord "path" "a.txt").size = 14 := by
    unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : paxHdr.size = 1024 := by dsimp only [paxHdr]; rw [mkPaxFrame_size, hpax_rec_sz]; decide
  have hnz : (paxHdr.size == 0 || paxHdr.size % 512 != 0) = false := by rw [hpax_sz]; rfl
  have hassoc : ByteArray.empty ++ mkPaxFrame (encodePaxRecord "path" "a.txt") ++ ByteArray.empty = paxHdr := by
    simp only [paxHdr, ByteArray.empty_append, ByteArray.append_empty]
  have hstep := unpackLoop_mkPaxFrame_step_any {} ByteArray.empty ByteArray.empty
    (encodePaxRecord "path" "a.txt") [] [] 0 (by rw [hpax_rec_sz]; decide)
    { path? := some "a.txt" } (parsePax_path_a 0)
  rw [hassoc, ByteArray.size_empty, hpax_rec_sz] at hstep
  have hpad14 : (0 + 512 + pad512 14 : Nat) = 1024 := by decide
  rw [hpad14] at hstep
  change ∃ e, Impl.unpackWith {} paxHdr = .error e ∧ e.kind = .truncatedArchive ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  simp [hpax_sz]

private theorem test4_h8 :
    let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
    ∃ e, Impl.unpackWith {} (paxHdr ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
  have hpax_rec_sz : (encodePaxRecord "path" "a.txt").size = 14 := by
    unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : paxHdr.size = 1024 := by dsimp only [paxHdr]; rw [mkPaxFrame_size, hpax_rec_sz]; decide
  let bytes := paxHdr ++ twoZeroBlocks
  have hsz : bytes.size = 2048 := by simp only [bytes, ByteArray.size_append, hpax_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hassoc : ByteArray.empty ++ mkPaxFrame (encodePaxRecord "path" "a.txt") ++ twoZeroBlocks = bytes := by
    simp only [bytes, paxHdr, ByteArray.empty_append]
  have hstep := unpackLoop_mkPaxFrame_step_any {} ByteArray.empty twoZeroBlocks
    (encodePaxRecord "path" "a.txt") [] [] 0 (by rw [hpax_rec_sz]; decide)
    { path? := some "a.txt" } (parsePax_path_a 0)
  rw [hassoc, ByteArray.size_empty, hpax_rec_sz] at hstep
  have hpad14 : (0 + 512 + pad512 14 : Nat) = 1024 := by decide
  rw [hpad14] at hstep
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1024 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi hlt0
    change bytes[1024 + i] = 0
    have ha : paxHdr.size ≤ 1024 + i := by rw [hpax_sz]; omega
    have hb : 1024 + i < (paxHdr ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hpax_sz, twoZeroBlocks_size]; omega
    simp only [bytes]
    rw [getElem_append_right_idx i ha hb (by rw [hpax_sz]; omega) (by rw [twoZeroBlocks_size]; omega)]
    unfold twoZeroBlocks
    rw [getElem_append_left (by rw [zeroBlock_size]; omega) (by rw [ByteArray.size_append, zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp [hnotge, hz1]

private theorem dupPax_err_abstract (bytes : ByteArray)
    (hsz : bytes.size = 4096)
    (hstep : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 1024 (some { path? := some "a.txt" }) [] [] 0)
    (hnz2 : isZeroRange bytes 1024 512 = false)
    (hparse2 : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 14, mtime := 0, typeflag := 0x78 }) :
    ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬1024 + 512 > bytes.size := by rw [hsz]; omega
  have h78 : ((0x78 : UInt8) == 0x78) = true := rfl
  have hsome : (some ({ path? := some "a.txt" } : PaxOverrides)).isSome = true := rfl
  unfold Impl.unpackWith
  rw [ite_eq_right (by rw [hnz]; decide), hstep, unpackLoop.eq_1, ite_eq_right hnotge, unpackStep.eq_1]
  rw [ite_eq_right hnotge, ite_eq_right (by rw [hnz2]; decide), ite_eq_right hnotgt, hparse2]
  dsimp only
  rw [ite_eq_left h78, ite_eq_left hsome]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_h9 :
    let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
    let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
    ∃ e, Impl.unpackWith {} (paxHdr ++ paxHdr ++ regFrame ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  let paxHdr := mkPaxFrame (encodePaxRecord "path" "a.txt")
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhi_sz]; decide
  have hpax_rec_sz : (encodePaxRecord "path" "a.txt").size = 14 := by
    unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : paxHdr.size = 1024 := by dsimp only [paxHdr]; rw [mkPaxFrame_size, hpax_rec_sz]; decide
  let post := paxHdr ++ regFrame ++ twoZeroBlocks
  let bytes := paxHdr ++ paxHdr ++ regFrame ++ twoZeroBlocks
  have hsz : bytes.size = 4096 := by
    simp only [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hassoc : ByteArray.empty ++ mkPaxFrame (encodePaxRecord "path" "a.txt") ++ post = bytes := by
    simp only [bytes, post, paxHdr, ByteArray.empty_append, ByteArray.append_assoc]
  have hstep := unpackLoop_mkPaxFrame_step_any {} ByteArray.empty post
    (encodePaxRecord "path" "a.txt") [] [] 0 (by rw [hpax_rec_sz]; decide)
    { path? := some "a.txt" } (parsePax_path_a 0)
  rw [hassoc, ByteArray.size_empty, hpax_rec_sz] at hstep
  have hpad14 : (0 + 512 + pad512 14 : Nat) = 1024 := by decide
  rw [hpad14] at hstep
  let paxUstar := mkUstarHeader "././@PaxHeader" 0o644 0 0 14 0 0x78 "" "" "" ""
  have hpaxU : paxUstar.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hext2 : bytes.extract 1024 (1024 + 512) = paxUstar := by
    have hbytes' : bytes = paxHdr ++ paxUstar ++ (padBlock512 (encodePaxRecord "path" "a.txt") ++ regFrame ++ twoZeroBlocks) := by
      simp only [bytes, paxHdr, mkPaxFrame, paxUstar, hpax_rec_sz, ByteArray.append_assoc]
    have hsub := extract_append_mid paxHdr paxUstar (padBlock512 (encodePaxRecord "path" "a.txt") ++ regFrame ++ twoZeroBlocks)
    rw [hpax_sz, hpaxU] at hsub
    rw [hbytes', hsub]
  have hnz2 : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext2
  have hparse2 : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 14, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hsz]; omega) hext2
  exact dupPax_err_abstract bytes hsz hstep hnz2 hparse2

private theorem test4_h10 :
    let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
    ∃ e, Impl.unpackWith {} (regFrame ++ twoZeroBlocks ++ regFrame) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let regFrame := mkRegularFrame "a.txt" "hi".toUTF8
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : regFrame.size = 1024 := by dsimp only [regFrame]; rw [mkRegularFrame_size, hhi_sz]; decide
  let bytes := regFrame ++ twoZeroBlocks ++ regFrame
  have hsz : bytes.size = 3072 := by
    simp only [bytes, ByteArray.size_append, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hassoc : ByteArray.empty ++ mkRegularFrame "a.txt" "hi".toUTF8 ++ (twoZeroBlocks ++ regFrame) = bytes := by
    simp only [bytes, regFrame, ByteArray.empty_append, ByteArray.append_assoc]
  have hstep := unpackLoop_mkRegularFrame_step {} ByteArray.empty (twoZeroBlocks ++ regFrame) "a.txt" "hi".toUTF8 [] [] 0
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by rw [hhi_sz]; decide) (by decide) (by rw [hhi_sz]; decide)
    (normPath := "a.txt") rfl rfl
  rw [hassoc, ByteArray.size_empty, hhi_sz] at hstep
  have hpad2 : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  rw [hpad2] at hstep
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1024 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi hlt0
    change bytes[1024 + i] = 0
    have hlt : 1024 + i < (regFrame ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]; omega
    have ha : regFrame.size ≤ 1024 + i := by rw [hreg_sz]; omega
    simp only [bytes]
    rw [getElem_append_left hlt hlt0,
      getElem_append_right_idx i ha hlt (by rw [hreg_sz]; omega) (by rw [twoZeroBlocks_size]; omega)]
    unfold twoZeroBlocks
    rw [getElem_append_left (by rw [zeroBlock_size]; omega) (by rw [ByteArray.size_append, zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  have hz2 : isZeroRange bytes 1536 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1536 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi hlt0
    change bytes[1536 + i] = 0
    have hlt : 1536 + i < (regFrame ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]; omega
    have ha : regFrame.size ≤ 1536 + i := by rw [hreg_sz]; omega
    simp only [bytes]
    rw [getElem_append_left hlt hlt0,
      getElem_append_right_idx (512 + i) ha hlt (by rw [hreg_sz]; omega) (by rw [twoZeroBlocks_size]; omega)]
    unfold twoZeroBlocks
    rw [getElem_append_right_idx i (by rw [zeroBlock_size]; omega) (by rw [ByteArray.size_append, zeroBlock_size]; omega)
      (by rw [zeroBlock_size]; omega) (by rw [zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  have hext3 : bytes.extract 2048 (2048 + 512) = mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" := by
    have ha : (regFrame ++ twoZeroBlocks).size = 2048 := by rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]
    have hsub := extract_append_mid (regFrame ++ twoZeroBlocks)
      (mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "") (padBlock512 "hi".toUTF8)
    rw [ha, mkUstarHeader_size] at hsub
    have hbytes' : bytes = (regFrame ++ twoZeroBlocks) ++ mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" ++
        padBlock512 "hi".toUTF8 := by
      simp only [bytes, regFrame, mkRegularFrame, ByteArray.append_assoc, hhi_sz]
    rw [hbytes', hsub]
  have hnz3 : isZeroRange bytes 2048 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext3
  have htr : allZeroTrailer bytes (1024 + 1024) = false := by
    rw [allZeroTrailer.eq_1]
    have hnotge3 : ¬1024 + 1024 ≥ bytes.size := by rw [hsz]; omega
    simp [hnotge3, hnz3]
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, hstep, unpackLoop.eq_1]
  have hnotge : ¬1024 ≥ bytes.size := by rw [hsz]; omega
  have hnotge2 : ¬1024 + 512 ≥ bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp [hnotge, hz1, hnotge2, hz2, htr]

private theorem test4_paddedArchive_ok (regFrame : ByteArray)
    (hreg : regFrame = mkRegularFrame "a.txt" "hi".toUTF8) :
    ∃ res, Impl.unpackWith {} (regFrame ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, data := "hi".toUTF8 }] res := by
  subst hreg
  let bytes := mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock
  have hhi_sz : ("hi".toUTF8).size = 2 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hreg_sz : (mkRegularFrame "a.txt" "hi".toUTF8).size = 1024 := by
    rw [mkRegularFrame_size, hhi_sz]; decide
  have hsz_bytes : bytes.size = 4096 := by
    simp only [bytes, ByteArray.size_append, hreg_sz, twoZeroBlocks_size, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by
    rw [hsz_bytes]; rfl
  let post := twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock
  have hassoc : bytes = ByteArray.empty ++ mkRegularFrame "a.txt" "hi".toUTF8 ++ post := by
    simp only [bytes, post, ByteArray.empty_append, ByteArray.append_assoc]
  have hstep1 := unpackLoop_mkRegularFrame_step {} ByteArray.empty post "a.txt" "hi".toUTF8 [] [] 0
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by rw [hhi_sz]; decide) (by decide) (by rw [hhi_sz]; decide)
    (normPath := "a.txt") rfl rfl
  rw [← hassoc, ByteArray.size_empty, hhi_sz] at hstep1
  have hpad2 : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  rw [hpad2] at hstep1
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1024 512 (by decide)).mpr ⟨by rw [hsz_bytes]; decide, ?_⟩
    intro i hi hlt0
    have hge1 : (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks).size = 2048 := by
      rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]
    have hlt1 : 1024 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks).size := by omega
    have hlt2 : 1024 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    have hlt3 : 1024 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    have hlt4 : 1024 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    change bytes[1024 + i] = 0
    simp only [bytes]
    rw [getElem_append_left hlt4 hlt0, getElem_append_left hlt3 hlt4, getElem_append_left hlt2 hlt3,
      getElem_append_left hlt1 hlt2,
      getElem_append_right_idx i (by rw [hreg_sz]; omega) hlt1 (by rw [hreg_sz]; omega) (by rw [twoZeroBlocks_size]; omega)]
    unfold twoZeroBlocks
    rw [getElem_append_left (by rw [zeroBlock_size]; omega) (by rw [ByteArray.size_append, zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  have hz2 : isZeroRange bytes 1536 512 = true := by
    refine (isZeroRange_eq_true_iff bytes 1536 512 (by decide)).mpr ⟨by rw [hsz_bytes]; decide, ?_⟩
    intro i hi hlt0
    have hlt1 : 1536 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks).size := by
      rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]; omega
    have hlt2 : 1536 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    have hlt3 : 1536 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    have hlt4 : 1536 + i < (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock).size := by
      rw [ByteArray.size_append]; omega
    change bytes[1536 + i] = 0
    simp only [bytes]
    rw [getElem_append_left hlt4 hlt0, getElem_append_left hlt3 hlt4, getElem_append_left hlt2 hlt3,
      getElem_append_left hlt1 hlt2,
      getElem_append_right_idx (512 + i) (by rw [hreg_sz]; omega) hlt1 (by rw [hreg_sz]; omega) (by rw [twoZeroBlocks_size]; omega)]
    unfold twoZeroBlocks
    rw [getElem_append_right_idx i (by rw [zeroBlock_size]; omega) (by rw [ByteArray.size_append, zeroBlock_size]; omega)
      (by rw [zeroBlock_size]; omega) (by rw [zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  have htr : allZeroTrailer bytes 2048 = true := by
    refine allZeroTrailer_of_zeros (by rw [hsz_bytes]) ?_
    intro j hj1 hj2 hj3
    change bytes[j] = 0
    have hz_end1 : (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks).size = 2048 := by
      rw [ByteArray.size_append, hreg_sz, twoZeroBlocks_size]
    have hz_end2 : (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock).size = 2560 := by
      rw [ByteArray.size_append, hz_end1, zeroBlock_size]
    have hz_end3 : (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock).size = 3072 := by
      rw [ByteArray.size_append, hz_end2, zeroBlock_size]
    have hz_end4 : (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock).size = 3584 := by
      rw [ByteArray.size_append, hz_end3, zeroBlock_size]
    by_cases hlt4 : j < 3584
    · by_cases hlt3 : j < 3072
      · by_cases hlt2 : j < 2560
        · simp only [bytes]
          rw [getElem_append_left (by omega) hj3, getElem_append_left (by omega) (by omega),
            getElem_append_left (by omega) (by omega), getElem_append_right (by omega) (by omega)]
          exact zeroBlock_getElem _
        · simp only [bytes]
          rw [getElem_append_left (by omega) hj3, getElem_append_left (by omega) (by omega),
            getElem_append_right (by omega) (by omega)]
          exact zeroBlock_getElem _
      · simp only [bytes]
        rw [getElem_append_left (by omega) hj3, getElem_append_right (by omega) (by omega)]
        exact zeroBlock_getElem _
    · simp only [bytes]
      rw [getElem_append_right (by omega) hj3]
      exact zeroBlock_getElem _
  have hu : Impl.unpackWith {} bytes = .ok [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] := by
    unfold Impl.unpackWith
    rw [hnz, hstep1, unpackLoop.eq_1]
    have hnotge : ¬1024 ≥ bytes.size := by rw [hsz_bytes]; omega
    have hnotge2 : ¬1024 + 512 ≥ bytes.size := by rw [hsz_bytes]; omega
    simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
    rw [unpackStep.eq_1]
    simp only [hnotge, hnotge2, ↓reduceIte, hz1, hz2, htr, Option.isSome_none, Bool.false_eq_true, Bool.not_true]
    rfl
  exact ⟨_, hu, tarEquiv_singleton_self _⟩

private theorem byteArray_mk_append_getElem_left (a b : Array UInt8) (k : Nat)
    (ha : k < a.size) (hab : k < ({ data := a ++ b } : ByteArray).size) :
    ({ data := a ++ b } : ByteArray)[k] = a[k] := by
  change (a ++ b)[k] = a[k]
  exact Array.getElem_append_left ha

private theorem dirtyData_ok_abstract (hdr dirtyData : ByteArray)
    (hhdr : hdr.size = 512) (hd_sz : dirtyData.size = 512)
    (hnz_hdr : isZeroRange (hdr ++ dirtyData ++ twoZeroBlocks) 0 512 = false)
    (hparse_hdr : parseUstarHeader (hdr ++ dirtyData ++ twoZeroBlocks) 0 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 2, mtime := 0, typeflag := 0x30 })
    (hdec : decodeTarEntry {} (hdr ++ dirtyData ++ twoZeroBlocks) 0
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 2, mtime := 0, typeflag := 0x30 }
      none [] 0 0 =
      .ok ({ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }, pad512 2)) :
    ∃ res, Impl.unpackWith {} (hdr ++ dirtyData ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] res := by
  let bytes := hdr ++ dirtyData ++ twoZeroBlocks
  have hsz : bytes.size = 2048 := by
    simp only [bytes, ByteArray.size_append, hhdr, hd_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hnotge : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  have h78 : ((0x30 : UInt8) == 0x78) = false := rfl
  have hpad : (0 + 512 + pad512 2 : Nat) = 1024 := by decide
  have hdata_sz : ("AB".toUTF8).size = "AB".utf8ByteSize := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have htail := unpackLoop_at_twoZeroBlocks {} (hdr ++ dirtyData) ["p.txt"]
    [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }]
    "AB".utf8ByteSize
  rw [ByteArray.size_append, hhdr, hd_sz] at htail
  have hu : Impl.unpackWith {} bytes = .ok [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] := by
    unfold Impl.unpackWith
    rw [ite_eq_right (by rw [hnz]; decide), unpackLoop.eq_1, ite_eq_right hnotge, unpackStep.eq_1]
    rw [ite_eq_right hnotge, ite_eq_right (by rw [hnz_hdr]; decide), ite_eq_right hnotgt, hparse_hdr]
    dsimp only
    rw [ite_eq_right (by rw [h78]; decide), List.length_nil, hdec]
    dsimp only
    rw [ite_eq_left (by rw [hpad]; omega), hpad, Nat.zero_add, hdata_sz]
    exact htail
  exact ⟨_, hu, tarEquiv_singleton_self _⟩

private theorem test4_dirtyData_ok :
    let hdr := mkUstarHeader "p.txt" 420 0 0 2 0 48 "" "" "" ""
    let dirtyData : ByteArray := { data := #[65, 66] ++ Array.replicate 510 255 }
    ∃ res, Impl.unpackWith {} (hdr ++ dirtyData ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] res := by
  let hdr := mkUstarHeader "p.txt" 420 0 0 2 0 48 "" "" "" ""
  let dirtyData : ByteArray := { data := #[65, 66] ++ Array.replicate 510 255 }
  let bytes := hdr ++ dirtyData ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hd_sz : dirtyData.size = 512 := by
    simp only [dirtyData, ByteArray.size, Array.size_append, Array.size_replicate]
    decide
  have hsz : bytes.size = 2048 := by
    simp only [bytes, ByteArray.size_append, hhdr, hd_sz, twoZeroBlocks_size]
  have hext_hdr : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr (dirtyData ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhdr] at h
    simpa only [bytes, ByteArray.append_assoc] using h
  have hnz_hdr : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 2, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hsz]; omega) hext_hdr
  have hdec := decodeTarEntry_mkUstarHeader_regular {} bytes hdr 0 none [] 0 0
    (by rw [hsz]; omega) hext_hdr rfl
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hsz]; decide) (name := "p.txt") (normPath := "p.txt") rfl rfl
  have hab : "AB".toUTF8 = { data := #[65, 66] } := by
    rw [toUTF8_eq_toByteArray]; rfl
  have hdata_ext : bytes.extract (0 + 512) (0 + 512 + 2) = "AB".toUTF8 := by
    rw [hab]
    change bytes.extract (0 + 512) (0 + 514) = { data := #[65, 66] }
    refine @extract_eq_of_getElem bytes { data := #[65, 66] } 0 512 514 (by decide) (by rw [hsz]; omega) rfl ?_
    intro k hk
    have hlt1 : 512 + k < (hdr ++ dirtyData).size := by
      rw [ByteArray.size_append, mkUstarHeader_size, hd_sz]; omega
    have hlt2 : 512 + k < bytes.size := by rw [hsz]; omega
    change bytes[0 + 512 + k] = (#[65, 66] : Array UInt8)[k]
    simp only [Nat.zero_add, bytes]
    rw [getElem_append_left hlt1 hlt2,
      getElem_append_right_idx k (by rw [hhdr]; omega) hlt1 (by rw [hhdr]; omega) (by rw [hd_sz]; omega)]
    dsimp only [dirtyData]
    exact byteArray_mk_append_getElem_left #[65, 66] _ k
      (by simp only [List.size_toArray, List.length_cons, List.length_nil]; omega) _
  have h2n0 : ((2 : Nat) == 0) = false := rfl
  have hmod : (((420 : UInt32) &&& 0o7777).toNat).toUInt32 = 0o644 := rfl
  have hdec' : decodeTarEntry {} bytes 0
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 2, mtime := 0, typeflag := 0x30 }
      none [] 0 0 =
      .ok ({ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }, pad512 2) := by
    simpa only [Option.getD_none, Nat.zero_add, h2n0, Bool.false_eq_true, ↓reduceIte, hdata_ext, hmod] using hdec
  exact dirtyData_ok_abstract hdr dirtyData hhdr hd_sz hnz_hdr hparse_hdr hdec'

private theorem allPass_checkUnpackError_bind3
    (b₁ b₂ b₃ : ByteArray) (k₁ k₂ k₃ : TarErrorKind)
    (h₁ : ∃ e, Impl.unpackWith {} b₁ = .error e ∧ e.kind = k₁ ∧ e.message ≠ "")
    (h₂ : ∃ e, Impl.unpackWith {} b₂ = .error e ∧ e.kind = k₂ ∧ e.message ≠ "")
    (h₃ : ∃ e, Impl.unpackWith {} b₃ = .error e ∧ e.kind = k₃ ∧ e.message ≠ "")
    (k : Unit → Core.AllPassRun Unit) (hk : AllPass (k ())) :
    AllPass (Bind.bind (checkUnpackError defaultApi {} b₁ k₁) fun _ =>
      Bind.bind (checkUnpackError defaultApi {} b₂ k₂) fun _ =>
      Bind.bind (checkUnpackError defaultApi {} b₃ k₃) k) :=
  allPass_checkUnpackError_bind {} b₁ k₁ _ h₁
    (allPass_checkUnpackError_bind {} b₂ k₂ _ h₂
      (allPass_checkUnpackError_bind {} b₃ k₃ _ h₃ hk))

private theorem allPass_test4_let_unpack_ok
    (bytes : ByteArray) (res : List TarEntry) (h : Impl.unpackWith {} bytes = .ok res)
    (p : List TarEntry → Prop) (k : Unit → Core.AllPassRun Unit) :
    AllPass (have x : ByteArray := bytes; have jp := k;
      match defaultApi.unpack x with
      | .error _ => Bind.bind (assert False) jp
      | .ok r => Bind.bind (assert (p r)) jp) ↔
    p res ∧ AllPass (k ()) := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  exact allPass_assert_bind (p res) k

private theorem allPass_test4_tail_ok (h1 h2 : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith {} (h1 ++ h2 ++ twoZeroBlocks) = .ok res)
    (p : List TarEntry → Prop) (hp : p res) :
    AllPass ((fun (_ : Unit) => have a := h1; have b := h2;
      match defaultApi.unpack (a ++ b ++ twoZeroBlocks) with
      | .error _ => assert False
      | .ok r => assert (p r)) ()) := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  simp only [AllPass, assert]
  exact ⟨hp, trivial⟩

/-- Prove `test_tar_unpackWith_framingAndTrailer_validated` for `defaultApi`. -/
theorem allPass_unpackWith_framingAndTrailer_validated :
    AllPass (test_tar_unpackWith_framingAndTrailer_validated defaultApi) := by
  have ⟨resPad, hpad_ok, hpad_teq⟩ := test4_paddedArchive_ok (mkRegularFrame "a.txt" "hi".toUTF8) rfl
  have ⟨resDirty, hdirty_ok, hdirty_teq⟩ := test4_dirtyData_ok
  unfold test_tar_unpackWith_framingAndTrailer_validated
  refine allPass_checkUnpackError_bind3 _ _ _ _ _ _ test4_h1 test4_h2 test4_h3 _ ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h4 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h5 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h6 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h7 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h8 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h9 ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test4_h10 ?_
  refine (allPass_test4_let_unpack_ok _ resPad hpad_ok _ _).mpr ⟨hpad_teq, ?_⟩
  exact allPass_test4_tail_ok _ _ resDirty hdirty_ok _ hdirty_teq

end LeanSwe.Tar.Proofs

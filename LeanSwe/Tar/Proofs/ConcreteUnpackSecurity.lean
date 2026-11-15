import LeanSwe.Tar.Proofs.ConcreteUnpackHelpers

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem test7_trav_err :
    ∃ e, Impl.unpackWith {} (mkUstarHeader "../evil" 420 0 0 0 0 48 "" "" "" "" ++ twoZeroBlocks) = .error e ∧
      e.kind = .unsafePath ∧ e.message ≠ "" := by
  let hdr := mkUstarHeader "../evil" 420 0 0 0 0 48 "" "" "" ""
  have hhdr : hdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  let bytes := hdr ++ twoZeroBlocks
  have hsz : bytes.size = 1536 := by simp [bytes, ByteArray.size_append, hhdr, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hext : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr twoZeroBlocks
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhdr] at h
    exact h
  have hnz0 : isZeroRange bytes 0 512 = false := isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
  have hparse0 : parseUstarHeader bytes 0 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
  have hs := mkUstarHeader_zero_decode_strings hdr twoZeroBlocks rfl
    (name := "../evil") (linkname := "") (mode := 420) (typeflag := 48)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide)
  have hbytes_eq : hdr ++ twoZeroBlocks = bytes := rfl
  rw [hbytes_eq] at hs
  have hval : ∃ err, validateEntryPath false false .regular "../evil" = .error err ∧
      err.kind = .unsafePath ∧ err.message ≠ "" :=
    ⟨_, rfl, rfl, by decide⟩
  rcases hval with ⟨err, hv, hk, hm⟩
  refine ⟨{ err with offset := some 0 }, ?_, hk, hm⟩
  change Impl.unpackWith {} bytes = .error { err with offset := some 0 }
  unfold Impl.unpackWith
  rw [hnz, unpackLoop.eq_1]
  have hnotge : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [List.length_nil, hnotge, ↓reduceIte, hnz0, Bool.false_eq_true, hnotgt, hparse0,
    (by decide : ((48 : UInt8) == 0x78) = false)]
  rw [decodeTarEntry.eq_1]
  simp only [Option.getD, Bool.true_or, Bool.false_eq_true,
    (by decide : (EntryKind.regular != EntryKind.regular) = false), Bool.false_and,
    ↓reduceIte, hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hv, hsz,
    (by decide : "".isEmpty = true),
    (by decide : ((48 : UInt8) == 0x30) = true),
    (by decide : ¬(0 + 1 > ({} : UnpackOptions).maxEntries)),
    (by decide : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes)),
    (by decide : ¬(0 + 512 + pad512 0 > 1536))]

private theorem test7_abs_err :
    ∃ e, Impl.unpackWith {} (mkUstarHeader "/etc/passwd" 420 0 0 0 0 48 "" "" "" "" ++ twoZeroBlocks) = .error e ∧
      e.kind = .unsafePath ∧ e.message ≠ "" := by
  let hdr := mkUstarHeader "/etc/passwd" 420 0 0 0 0 48 "" "" "" ""
  have hhdr : hdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  let bytes := hdr ++ twoZeroBlocks
  have hsz : bytes.size = 1536 := by simp [bytes, ByteArray.size_append, hhdr, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hext : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr twoZeroBlocks
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhdr] at h
    exact h
  have hnz0 : isZeroRange bytes 0 512 = false := isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
  have hparse0 : parseUstarHeader bytes 0 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
  have hs := mkUstarHeader_zero_decode_strings hdr twoZeroBlocks rfl
    (name := "/etc/passwd") (linkname := "") (mode := 420) (typeflag := 48)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide)
  have hbytes_eq : hdr ++ twoZeroBlocks = bytes := rfl
  rw [hbytes_eq] at hs
  have hval : ∃ err, validateEntryPath false false .regular "/etc/passwd" = .error err ∧
      err.kind = .unsafePath ∧ err.message ≠ "" :=
    ⟨_, rfl, rfl, by decide⟩
  rcases hval with ⟨err, hv, hk, hm⟩
  refine ⟨{ err with offset := some 0 }, ?_, hk, hm⟩
  change Impl.unpackWith {} bytes = .error { err with offset := some 0 }
  unfold Impl.unpackWith
  rw [hnz, unpackLoop.eq_1]
  have hnotge : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [List.length_nil, hnotge, ↓reduceIte, hnz0, Bool.false_eq_true, hnotgt, hparse0,
    (by decide : ((48 : UInt8) == 0x78) = false)]
  rw [decodeTarEntry.eq_1]
  simp only [Option.getD, Bool.true_or, Bool.false_eq_true,
    (by decide : (EntryKind.regular != EntryKind.regular) = false), Bool.false_and,
    ↓reduceIte, hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hv, hsz,
    (by decide : "".isEmpty = true),
    (by decide : ((48 : UInt8) == 0x30) = true),
    (by decide : ¬(0 + 1 > ({} : UnpackOptions).maxEntries)),
    (by decide : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes)),
    (by decide : ¬(0 + 512 + pad512 0 > 1536))]

private theorem test7_sym_err :
    ∃ e, Impl.unpackWith {} (mkUstarHeader "escape" 511 0 0 0 0 50 "../etc/passwd" "" "" "" ++ twoZeroBlocks) = .error e ∧
      e.kind = .unsafePath ∧ e.message ≠ "" := by
  let hdr := mkUstarHeader "escape" 511 0 0 0 0 50 "../etc/passwd" "" "" ""
  have hhdr : hdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  let bytes := hdr ++ twoZeroBlocks
  have hsz : bytes.size = 1536 := by simp [bytes, ByteArray.size_append, hhdr, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hext : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr twoZeroBlocks
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhdr] at h
    exact h
  have hnz0 : isZeroRange bytes 0 512 = false := isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hext
  have hparse0 : parseUstarHeader bytes 0 =
      .ok { mode := ((511 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 50 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hext
  have hs := mkUstarHeader_zero_decode_strings hdr twoZeroBlocks rfl
    (name := "escape") (linkname := "../etc/passwd") (mode := 511) (typeflag := 50)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide)
  have hbytes_eq : hdr ++ twoZeroBlocks = bytes := rfl
  rw [hbytes_eq] at hs
  have hval : validateEntryPath false false .symlink "escape" = .ok "escape" := rfl
  have hsym : ∃ err, validateSymlinkTarget false false "escape" "../etc/passwd" = .error err ∧
      err.kind = .unsafePath ∧ err.message ≠ "" :=
    ⟨_, rfl, rfl, by decide⟩
  rcases hsym with ⟨err, hv, hk, hm⟩
  refine ⟨{ err with offset := some 0 }, ?_, hk, hm⟩
  change Impl.unpackWith {} bytes = .error { err with offset := some 0 }
  unfold Impl.unpackWith
  rw [hnz, unpackLoop.eq_1]
  have hnotge : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [List.length_nil, hnotge, ↓reduceIte, hnz0, Bool.false_eq_true, hnotgt, hparse0,
    (by decide : ((50 : UInt8) == 0x78) = false)]
  rw [decodeTarEntry.eq_1]
  simp only [Option.getD, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hsz, hval, hv,
    (by decide : "".isEmpty = true),
    (by decide : ((0 : Nat) != 0) = false), Bool.and_false,
    (by decide : ((50 : UInt8) == 0x30) = false),
    (by decide : ((50 : UInt8) == 0x00) = false),
    (by decide : ((50 : UInt8) == 0x35) = false),
    (by decide : ((50 : UInt8) == 0x32) = true),
    (by decide : ¬(0 + 1 > ({} : UnpackOptions).maxEntries)),
    (by decide : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes)),
    (by decide : ¬(0 + 512 + pad512 0 > 1536))]

private theorem test7_dup_err :
    ∃ e, Impl.unpackWith {}
        (mkUstarHeader "sub/" 493 0 0 0 0 53 "" "" "" "" ++
         mkUstarHeader "sub" 420 0 0 0 0 48 "" "" "" "" ++ twoZeroBlocks) = .error e ∧
      e.kind = .duplicatePath ∧ e.message ≠ "" := by
  let dupA := mkUstarHeader "sub/" 493 0 0 0 0 53 "" "" "" ""
  let dupB := mkUstarHeader "sub" 420 0 0 0 0 48 "" "" "" ""
  have hdupA : dupA.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hdupB : dupB.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  let bytes := dupA ++ dupB ++ twoZeroBlocks
  have hsz : bytes.size = 2048 := by
    simp [bytes, ByteArray.size_append, hdupA, hdupB, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hextA : bytes.extract 0 512 = dupA := by
    have h := extract_append_mid ByteArray.empty dupA (dupB ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hdupA] at h
    simpa only [bytes, ByteArray.append_assoc] using h
  have hnzA : isZeroRange bytes 0 512 = false := isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hextA
  have hparseA : parseUstarHeader bytes 0 =
      .ok { mode := ((493 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 53 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hextA
  have hsA := mkUstarHeader_zero_decode_strings dupA (dupB ++ twoZeroBlocks) rfl
    (name := "sub/") (linkname := "") (mode := 493) (typeflag := 53)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide)
  have hbytesA : dupA ++ (dupB ++ twoZeroBlocks) = bytes := by simp only [bytes, ByteArray.append_assoc]
  rw [hbytesA] at hsA
  have hvalA : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
  have hextB : bytes.extract 512 1024 = dupB := by
    have h := extract_append_mid dupA dupB twoZeroBlocks
    rw [hdupA, hdupB] at h
    exact h
  have hextB' : bytes.extract 512 (512 + 512) =
      mkUstarHeader "sub" 420 0 0 0 0 48 "" "" "" "" := hextB
  have hnzB : isZeroRange bytes 512 512 = false := isZeroRange_mkUstarHeader_false (by rw [hsz]; omega) hextB
  have hparseB : parseUstarHeader bytes 512 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) (by rw [hsz]; omega) hextB
  have hbdB : 512 + 512 ≤ bytes.size := by rw [hsz]; decide
  have hsB := mkUstarHeader_extract_strings hbdB hextB'
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
  have hnmB : decodeCStringUtf8 bytes 512 (512 + 100) 512 "name" = .ok "sub" :=
    decodeCStringUtf8_padRightBytes (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by rw [hsz]; decide) hsB.1
  have hunB : decodeCStringUtf8 bytes (512 + 265) (512 + 265 + 32) 512 "uname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by rw [hsz]; decide) hsB.2.2.1
  have hgnB : decodeCStringUtf8 bytes (512 + 297) (512 + 297 + 32) 512 "gname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by rw [hsz]; decide) hsB.2.2.2.1
  have hpfB : decodeCStringUtf8 bytes (512 + 345) (512 + 345 + 155) 512 "prefix" = .ok "" :=
    decodeCStringUtf8_padRightBytes (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by rw [hsz]; decide) hsB.2.2.2.2
  have hvalB : validateEntryPath false false .regular "sub" = .ok "sub" := rfl
  have hpad0 : pad512 0 = 0 := rfl
  change ∃ e, Impl.unpackWith {} bytes = .error e ∧ e.kind = .duplicatePath ∧ e.message ≠ ""
  unfold Impl.unpackWith
  rw [hnz, unpackLoop.eq_1]
  have hnotge0 : ¬0 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt0 : ¬0 + 512 > bytes.size := by rw [hsz]; omega
  have hnotge1 : ¬512 ≥ bytes.size := by rw [hsz]; omega
  have hnotgt1 : ¬512 + 512 > bytes.size := by rw [hsz]; omega
  simp only [Bool.false_eq_true, hnotge0, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [List.length_nil, hnotge0, ↓reduceIte, hnzA, Bool.false_eq_true, hnotgt0, hparseA,
    (by decide : ((53 : UInt8) == 0x78) = false)]
  rw [decodeTarEntry.eq_1]
  simp only [Option.getD, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hsA.1, hsA.2.2.1, hsA.2.2.2.1, hsA.2.2.2.2, hvalA, hsz,
    Nat.add_zero, Nat.zero_add, hpad0, ByteArray.size_empty,
    (by decide : "".isEmpty = true),
    (by decide : ((0 : Nat) != 0) = false), Bool.and_false,
    (by decide : [].contains "sub" = false),
    (by decide : ((53 : UInt8) == 0x30) = false),
    (by decide : ((53 : UInt8) == 0x00) = false),
    (by decide : ((53 : UInt8) == 0x35) = true),
    (by decide : ¬(0 + 1 > ({} : UnpackOptions).maxEntries)),
    (by decide : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes)),
    (by decide : ¬(512 > 2048)),
    (by decide : ((0 : Nat) == 0) = true),
    (by decide : (512 : Nat) > 0)]
  rw [unpackLoop.eq_1]
  simp only [hnotge1, ↓reduceIte]
  rw [unpackStep.eq_1]
  simp only [List.length_singleton, hnotge1, ↓reduceIte, hnzB, Bool.false_eq_true, hnotgt1, hparseB,
    (by decide : ((48 : UInt8) == 0x78) = false)]
  rw [decodeTarEntry.eq_1]
  simp only [Option.getD, Bool.true_or, Bool.false_eq_true,
    (by decide : (EntryKind.regular != EntryKind.regular) = false), Bool.false_and,
    ↓reduceIte, hnmB, hunB, hgnB, hpfB, hvalB, hsz,
    (by decide : "".isEmpty = true),
    (by decide : ((48 : UInt8) == 0x30) = true),
    (by decide : ¬(1 + 1 > ({} : UnpackOptions).maxEntries)),
    (by decide : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes)),
    (by decide : ¬(512 + 512 + pad512 0 > 2048)),
    (by decide : ["sub"].contains "sub" = true)]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test7_safe_ok :
    ∃ res, Impl.unpackWith {}
        (mkPaxFrame (encodePaxRecord "path" "safe.txt") ++ mkRegularFrame "safe.txt" ByteArray.empty ++ twoZeroBlocks) =
        .ok res ∧
      TarEquiv [{ path := "safe.txt", kind := .regular }] res := by
  let pax := encodePaxRecord "path" "safe.txt"
  let reg := mkRegularFrame "safe.txt" ByteArray.empty
  let post := reg ++ twoZeroBlocks
  let bytes := mkPaxFrame pax ++ reg ++ twoZeroBlocks
  have hpax_rec_sz : pax.size = 17 := by
    dsimp only [pax]; unfold encodePaxRecord; rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpax_sz : (mkPaxFrame pax).size = 1024 := by rw [mkPaxFrame_size, hpax_rec_sz]; decide
  have hreg_sz : reg.size = 512 := by
    dsimp only [reg]; rw [mkRegularFrame_size, ByteArray.size_empty]; decide
  have hsz : bytes.size = 2560 := by
    simp [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hsz]; rfl
  have hpax_ext : parsePaxPayload pax 0 = .ok { path? := some "safe.txt" } := parsePax_path_safe 0
  have hstep1 := unpackLoop_mkPaxFrame_step_any {} ByteArray.empty post pax [] [] 0
    (by rw [hpax_rec_sz]; decide) { path? := some "safe.txt" } hpax_ext
  have hassoc1 : ByteArray.empty ++ mkPaxFrame pax ++ post = bytes := by
    simp [bytes, post, ByteArray.empty_append, ByteArray.append_assoc]
  rw [hassoc1, ByteArray.size_empty, hpax_rec_sz] at hstep1
  have h1024 : (0 + 512 + pad512 17 : Nat) = 1024 := by decide
  rw [h1024] at hstep1
  let regHdr := mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" ""
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
  have hdec2 := decodeTarEntry_mkUstarHeader_regular {} bytes regHdr 1024
    (some { path? := some "safe.txt" }) [] 0 0
    (by rw [hsz]; omega) hext2 rfl
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by rw [hsz]; decide) (name := "safe.txt") (normPath := "safe.txt") rfl rfl
  have htail := unpackLoop_at_twoZeroBlocks {} (mkPaxFrame pax ++ reg) ["safe.txt"]
    [{ path := "safe.txt", kind := .regular, mode := 0o644 }] 0
  rw [ByteArray.size_append, hpax_sz, hreg_sz] at htail
  have hmod : (((0o644 : UInt32) &&& 0o7777).toNat).toUInt32 = 0o644 := rfl
  have hu : Impl.unpackWith {} bytes = .ok [{ path := "safe.txt", kind := .regular, mode := 0o644 }] := by
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
  exact ⟨[{ path := "safe.txt", kind := .regular }], hu, tarEquiv_singleton_self _⟩

private theorem allPass_test7_match_tail_iff
    (bytes : ByteArray) (res : List TarEntry)
    (h : Impl.unpackWith {} bytes = .ok res)
    (p : List TarEntry → Prop) :
    AllPass (have safePax := bytes;
      match defaultApi.unpack safePax with
      | .error _ => assert False
      | .ok r => assert (p r)) ↔
    p res := by
  dsimp only
  rw [defaultApi_unpack_eq, h]
  simp only [AllPass, assert, and_true]

/-- Prove `test_tar_unpackWith_securityOnWire_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_securityOnWire_enforced :
    AllPass (test_tar_unpackWith_securityOnWire_enforced defaultApi) := by
  rcases test7_safe_ok with ⟨resSafe, hsafe_ok, hsafe_teq⟩
  unfold test_tar_unpackWith_securityOnWire_enforced
  refine allPass_checkUnpackError_bind {} _ _ _ test7_trav_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test7_abs_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test7_sym_err ?_
  refine allPass_checkUnpackError_bind {} _ _ _ test7_dup_err ?_
  exact (allPass_test7_match_tail_iff _ resSafe hsafe_ok _).mpr hsafe_teq

end LeanSwe.Tar.Proofs

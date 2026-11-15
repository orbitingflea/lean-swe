import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.Universal
import LeanSwe.Tar.Proofs.ConcreteHelpers

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Reduce `defaultApi.unpack` to `Impl.unpackWith {}`. -/
theorem defaultApi_unpack_eq (bytes : ByteArray) :
    defaultApi.unpack bytes = Impl.unpackWith {} bytes := rfl

/-- Reduce `defaultApi.unpackWith` to `Impl.unpackWith`. -/
theorem defaultApi_unpackWith_eq (opts : UnpackOptions) (bytes : ByteArray) :
    defaultApi.unpackWith opts bytes = Impl.unpackWith opts bytes := rfl

/-- Rewrite a `have`-bound `AllPass` computation to a universally quantified hypothesis. -/
theorem allPass_have {α : Type _} (v : α) (f : α → AllPassRun Unit) :
    AllPass (have x := v; f x) ↔ ∀ _x, _x = v → AllPass (f _x) :=
  ⟨fun h _x hx => hx ▸ h, fun h => h v rfl⟩

/-- Split `Bind.bind (NondetTest.assert p) k` under `AllPass`. -/
theorem allPass_assert_bind (p : Prop) (k : Unit → AllPassRun Unit) :
    AllPass (Bind.bind (NondetTest.assert p) k) ↔ p ∧ AllPass (k ()) := by
  simp [AllPass, Bind.bind, NondetTest.assert]

/-- Discharge a bound `checkUnpackError` step from an explicit `Impl.unpackWith` error witness. -/
theorem allPass_checkUnpackError_bind (opts : UnpackOptions) (bytes : ByteArray)
    (expectedKind : TarErrorKind) (k : Unit → AllPassRun Unit)
    (herr : ∃ e, Impl.unpackWith opts bytes = .error e ∧ e.kind = expectedKind ∧ e.message ≠ "")
    (hk : AllPass (k ())) :
    AllPass (Bind.bind (checkUnpackError defaultApi opts bytes expectedKind) k) := by
  rcases herr with ⟨e, hu, hkind, hmsg⟩
  unfold checkUnpackError
  rw [defaultApi_unpackWith_eq, hu]
  dsimp only
  rw [allPass_assert_bind]
  refine ⟨⟨hkind, ?_⟩, hk⟩
  have hne : e.message.isEmpty = false := by
    cases h : e.message.isEmpty with
    | false => rfl
    | true => exact absurd (String.isEmpty_iff.mp h) hmsg
  simp [hne]

/-- Discharge a terminal `checkUnpackError` step from an explicit `Impl.unpackWith` error witness. -/
theorem allPass_checkUnpackError (opts : UnpackOptions) (bytes : ByteArray)
    (expectedKind : TarErrorKind)
    (herr : ∃ e, Impl.unpackWith opts bytes = .error e ∧ e.kind = expectedKind ∧ e.message ≠ "") :
    AllPass (checkUnpackError defaultApi opts bytes expectedKind) := by
  rcases herr with ⟨e, hu, hkind, hmsg⟩
  unfold checkUnpackError
  rw [defaultApi_unpackWith_eq, hu]
  dsimp only [AllPass, NondetTest.assert]
  refine ⟨⟨hkind, ?_⟩, trivial⟩
  have hne : e.message.isEmpty = false := by
    cases h : e.message.isEmpty with
    | false => rfl
    | true => exact absurd (String.isEmpty_iff.mp h) hmsg
  simp [hne]

/-- Reflexivity of `TarEquiv` on singleton lists. -/
theorem tarEquiv_singleton_self (e : TarEntry) : TarEquiv [e] [e] := by
  refine ⟨?_, trivial⟩
  simp only [entryEquivBool]
  cases e.kind <;> simp <;> rfl

/-- Step `unpackLoop` across one valid PAX extended header frame `mkPaxFrame pax`. -/
theorem unpackLoop_mkPaxFrame_step_any (opts : UnpackOptions) (pre post pax : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes)
    (hov : PaxOverrides) (hparse_pax : parsePaxPayload pax pre.size = .ok hov) :
    unpackLoop opts (pre ++ mkPaxFrame pax ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkPaxFrame pax ++ post) (pre.size + 512 + pad512 pax.size)
        (some hov) seen acc totalBytes := by
  let frame := mkPaxFrame pax
  let hdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" ""
  let bytes := pre ++ frame ++ post
  change unpackLoop opts bytes pre.size none seen acc totalBytes =
    unpackLoop opts bytes (pre.size + 512 + pad512 pax.size) (some hov) seen acc totalBytes
  have hmax : maxPaxHeaderBytes < ustarOctal11Limit := by decide
  have hsz_frame : frame.size = 512 + pad512 pax.size := mkPaxFrame_size pax
  have hsz_bytes : bytes.size = pre.size + frame.size + post.size := by
    simp only [bytes, ByteArray.size_append]
  have hnotge : ¬pre.size ≥ bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hassoc : bytes = pre ++ hdr ++ (padBlock512 pax ++ post) := by
    simp only [bytes, frame, mkPaxFrame, hdr, ByteArray.append_assoc]
  have hext_hdr : bytes.extract pre.size (pre.size + 512) = hdr := by
    rw [hassoc]
    have h := extract_append_mid pre hdr (padBlock512 pax ++ post)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz : isZeroRange bytes pre.size 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hnotgt : ¬pre.size + 512 > bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hparse_hdr : parseUstarHeader bytes pre.size =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := pax.size, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by omega) (by decide)
      (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hpax_ext : bytes.extract (pre.size + 512) (pre.size + 512 + pax.size) = pax := by
    have h1 : bytes.extract (pre.size + 512) (pre.size + 512 + pad512 pax.size) = padBlock512 pax := by
      rw [hassoc]
      have ha : (pre ++ hdr).size = pre.size + 512 := by rw [ByteArray.size_append, mkUstarHeader_size]
      have hsub := extract_append_mid (pre ++ hdr) (padBlock512 pax) post
      rw [ha, padBlock512_size, ByteArray.append_assoc] at hsub
      exact hsub
    have hle : pax.size ≤ pad512 pax.size := le_pad512 pax.size
    have h2 : bytes.extract (pre.size + 512) (pre.size + 512 + pax.size) =
        (bytes.extract (pre.size + 512) (pre.size + 512 + pad512 pax.size)).extract 0 pax.size := by
      rw [ByteArray.extract_extract]
      exact congrArg (bytes.extract (pre.size + 512)) (by omega)
    rw [h2, h1, padBlock512_extract_prefix]
  have hnot_max : ¬pax.size > maxPaxHeaderBytes := by omega
  have hnot_trunc : ¬pre.size + 512 + pad512 pax.size > bytes.size := by
    rw [hsz_bytes, hsz_frame]; omega
  have hadv : pre.size + 512 + pad512 pax.size > pre.size := by omega
  have h78 : ((0x78 : UInt8) == 0x78) = true := rfl
  rw [unpackLoop.eq_1]
  simp only [hnotge, ↓reduceIte]
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt, hparse_hdr,
    Option.isSome_none, hnot_max, hnot_trunc, hpax_ext, hparse_pax, h78, hadv]

/-- Step `unpackLoop` across one concrete regular-file USTAR frame `mkRegularFrame p d`. -/
theorem unpackLoop_mkRegularFrame_step (opts : UnpackOptions) (pre post : ByteArray)
    (p : String) (d : ByteArray) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hp_sz : p.toUTF8.size ≤ 100) (hp_nul : !hasNulString p = true)
    (hd_sz : d.size < ustarOctal11Limit)
    (hmaxe : acc.length + 1 ≤ opts.maxEntries)
    (hmaxb : totalBytes + d.size ≤ opts.maxTotalBytes)
    {normPath : String}
    (hval : validateEntryPath opts.allowAbsolute opts.allowParentTraversal .regular p = .ok normPath)
    (hseen : seen.contains normPath = false) :
    unpackLoop opts (pre ++ mkRegularFrame p d ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkRegularFrame p d ++ post) (pre.size + 512 + pad512 d.size) none
        (normPath :: seen)
        ({ path := normPath, kind := .regular, mode := 0o644, data := d } :: acc)
        (totalBytes + d.size) := by
  let hdr := mkUstarHeader p 0o644 0 0 d.size 0 0x30 "" "" "" ""
  let frame := mkRegularFrame p d
  let bytes := pre ++ frame ++ post
  change unpackLoop opts bytes pre.size none seen acc totalBytes =
    unpackLoop opts bytes (pre.size + 512 + pad512 d.size) none
      (normPath :: seen)
      ({ path := normPath, kind := .regular, mode := 0o644, data := d } :: acc)
      (totalBytes + d.size)
  have hsz_frame : frame.size = 512 + pad512 d.size := mkRegularFrame_size p d
  have hsz_bytes : bytes.size = pre.size + frame.size + post.size := by
    simp only [bytes, ByteArray.size_append]
  have hnotge : ¬pre.size ≥ bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hassoc : bytes = pre ++ hdr ++ (padBlock512 d ++ post) := by
    simp only [bytes, frame, mkRegularFrame, hdr, ByteArray.append_assoc]
  have hext_hdr : bytes.extract pre.size (pre.size + 512) = hdr := by
    rw [hassoc]
    have h := extract_append_mid pre hdr (padBlock512 d ++ post)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz : isZeroRange bytes pre.size 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hnotgt : ¬pre.size + 512 > bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hparse_hdr : parseUstarHeader bytes pre.size =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := d.size, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) hd_sz (by decide)
      (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hdec := decodeTarEntry_mkUstarHeader_regular opts bytes hdr pre.size none seen acc.length totalBytes
    (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr rfl
    hp_sz (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    hp_nul (by decide) (by decide) (by decide)
    (by decide) (by decide) hd_sz (by decide)
    hmaxe (by simpa using hmaxb)
    (by rw [hsz_bytes, hsz_frame]; simp only [Option.getD_none]; omega)
    (by simpa using hval) hseen
  have hdata_ext : (if d.size == 0 then ByteArray.empty
      else bytes.extract (pre.size + 512) (pre.size + 512 + d.size)) = d := by
    by_cases hdz : d.size == 0
    · simp only [hdz, ↓reduceIte]
      have h0 : d.size = 0 := beq_iff_eq.mp hdz
      apply ByteArray.ext; apply Array.ext <;> simp [h0]
    · simp only [hdz, Bool.false_eq_true, ↓reduceIte]
      have hpad_ext : bytes.extract (pre.size + 512) (pre.size + 512 + pad512 d.size) = padBlock512 d := by
        rw [hassoc]
        have ha : (pre ++ hdr).size = pre.size + 512 := by rw [ByteArray.size_append, mkUstarHeader_size]
        have hsub := extract_append_mid (pre ++ hdr) (padBlock512 d) post
        rw [ha, padBlock512_size, ByteArray.append_assoc] at hsub
        exact hsub
      have hle : d.size ≤ pad512 d.size := le_pad512 d.size
      have h2 : bytes.extract (pre.size + 512) (pre.size + 512 + d.size) =
          (bytes.extract (pre.size + 512) (pre.size + 512 + pad512 d.size)).extract 0 d.size := by
        rw [ByteArray.extract_extract]
        exact congrArg (bytes.extract (pre.size + 512)) (by omega)
      rw [h2, hpad_ext, padBlock512_extract_prefix]
  have hmode : (((0o644 : UInt32) &&& 0o7777).toNat).toUInt32 = 0o644 := rfl
  have hadv : pre.size + 512 + pad512 d.size > pre.size := by omega
  have h78 : ((0x30 : UInt8) == 0x78) = false := rfl
  rw [unpackLoop.eq_1]
  simp only [hnotge, ↓reduceIte]
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt, hparse_hdr, h78, hdec, Option.getD_none,
    hdata_ext, hmode, hadv]

/-- Decode a single-record PAX payload `encodePaxRecord key val`. -/
theorem parsePaxPayload_kv_single (key val : String) (offset : Nat)
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ val ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ val ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_ne : !key.isEmpty = true) (hkey_nul : !hasNulString key = true)
    (hkey_nl : !key.toList.contains '\n' = true)
    (hkey_eq : ¬(0x3d : UInt8) ∈ key.toUTF8.toList)
    (hnot_sparse : !startsWithStr key "GNU.sparse." = true)
    {nextOv : PaxOverrides}
    (happly : applyPaxKey {} key val offset = .ok nextOv) :
    parsePaxPayload (encodePaxRecord key val) offset = .ok nextOv := by
  unfold parsePaxPayload
  have hext : (encodePaxRecord key val).extract 0 (encodePaxRecord key val).size =
      encodePaxRecord key val ++ ByteArray.empty := by
    rw [ByteArray.extract_zero_size, ByteArray.append_empty]
  have hstep := parsePaxPayload_go_step (bs := encodePaxRecord key val) (rest := ByteArray.empty)
    (offset := offset) (pos := 0) (seenKeys := []) (ov := {}) (nextOv := nextOv)
    hkvMin hkvMax hkey_ne hkey_nul hkey_nl hkey_eq (by simp) hnot_sparse happly hext
  rw [Nat.zero_add] at hstep
  rw [hstep, parsePaxPayload.go.eq_1]
  simp

/-- Decode `encodePaxRecord "path" "a.txt"`. -/
theorem parsePax_path_a (off : Nat) :
    parsePaxPayload (encodePaxRecord "path" "a.txt") off = .ok { path? := some "a.txt" } := by
  refine parsePaxPayload_kv_single "path" "a.txt" off ?_ ?_ (by decide) (by decide) (by decide) ?_ (by decide) ?_
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_toList]; decide
  · rfl

/-- Decode `encodePaxRecord "path" "safe.txt"`. -/
theorem parsePax_path_safe (off : Nat) :
    parsePaxPayload (encodePaxRecord "path" "safe.txt") off = .ok { path? := some "safe.txt" } := by
  refine parsePaxPayload_kv_single "path" "safe.txt" off ?_ ?_ (by decide) (by decide) (by decide) ?_ (by decide) ?_
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_toList]; decide
  · rfl

/-- Decode `encodePaxRecord "size" "8589934592"`. -/
theorem parsePax_size_8g (off : Nat) :
    parsePaxPayload (encodePaxRecord "size" "8589934592") off = .ok { size? := some 8589934592 } := by
  refine parsePaxPayload_kv_single "size" "8589934592" off ?_ ?_ (by decide) (by decide) (by decide) ?_ (by decide) ?_
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  · rw [toUTF8_toList]; decide
  · rfl

/-- Decode `name`, `linkname`, and empty `uname`/`gname`/`prefix` from a header at offset 0 followed by `post`. -/
theorem mkUstarHeader_zero_decode_strings {name linkname : String} {mode : UInt32}
    {typeflag : UInt8} (hdr post : ByteArray)
    (hhdr_eq : hdr = mkUstarHeader name mode 0 0 0 0 typeflag linkname "" "" "")
    (hnm : name.toUTF8.size ≤ 100) (hln : linkname.toUTF8.size ≤ 100)
    (hnm_nul : !hasNulString name = true) (hln_nul : !hasNulString linkname = true) :
    decodeCStringUtf8 (hdr ++ post) 0 100 0 "name" = .ok name ∧
    decodeCStringUtf8 (hdr ++ post) 157 257 0 "linkname" = .ok linkname ∧
    decodeCStringUtf8 (hdr ++ post) 265 297 0 "uname" = .ok "" ∧
    decodeCStringUtf8 (hdr ++ post) 297 329 0 "gname" = .ok "" ∧
    decodeCStringUtf8 (hdr ++ post) 345 500 0 "prefix" = .ok "" := by
  have hhdr : hdr.size = 512 := by rw [hhdr_eq, mkUstarHeader_size]
  have hbd : 0 + 512 ≤ (hdr ++ post).size := by rw [ByteArray.size_append, hhdr]; omega
  have hext : (hdr ++ post).extract 0 (0 + 512) =
      mkUstarHeader name mode 0 0 0 0 typeflag linkname "" "" "" := by
    have h := extract_append_mid ByteArray.empty hdr post
    simp only [ByteArray.size_empty, ByteArray.empty_append, Nat.zero_add, hhdr] at h
    rw [h, hhdr_eq]
  have hs := mkUstarHeader_extract_strings hbd hext hnm hln
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
  have h1 := decodeCStringUtf8_padRightBytes (bytes := hdr ++ post) (start := 0) (w := 100) (offset := 0) (fieldName := "name")
    hnm_nul hnm (by omega) hs.1
  have h2 := decodeCStringUtf8_padRightBytes (bytes := hdr ++ post) (start := 157) (w := 100) (offset := 0) (fieldName := "linkname")
    hln_nul hln (by omega) hs.2.1
  have h3 := decodeCStringUtf8_padRightBytes (bytes := hdr ++ post) (start := 265) (w := 32) (offset := 0) (fieldName := "uname")
    (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by omega) hs.2.2.1
  have h4 := decodeCStringUtf8_padRightBytes (bytes := hdr ++ post) (start := 297) (w := 32) (offset := 0) (fieldName := "gname")
    (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by omega) hs.2.2.2.1
  have h5 := decodeCStringUtf8_padRightBytes (bytes := hdr ++ post) (start := 345) (w := 155) (offset := 0) (fieldName := "prefix")
    (by decide) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by omega) hs.2.2.2.2
  exact ⟨h1, h2, h3, h4, h5⟩

end LeanSwe.Tar.Proofs

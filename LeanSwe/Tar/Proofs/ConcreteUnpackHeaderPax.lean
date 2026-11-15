import LeanSwe.Tar.Proofs.ConcreteUnpackHeaderHelpers

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem byteArray_getElem_of_eq' {a b : ByteArray} (h : a = b) {i : Nat}
    (ha : i < a.size) (hb : i < b.size) : a[i]'ha = b[i]'hb := by
  subst h; rfl

private theorem byteArray_getElem_of_idx' {a b : ByteArray} {i j : Nat}
    (ha : a = b) (hij : i = j) (hi : i < a.size) (hj : j < b.size) :
    a[i]'hi = b[j]'hj := by
  subst ha hij; rfl

private theorem byteArray_append_getElem_left' {a b : ByteArray} {i : Nat}
    (hi : i < a.size) {hab : i < (a ++ b).size} :
    (a ++ b)[i]'hab = a[i]'hi := getElem_append_left hi

private theorem byteArray_append_getElem_right' {a b : ByteArray} {i k : Nat}
    (hk : i = a.size + k) (hkb : k < b.size) {hab : i < (a ++ b).size} :
    (a ++ b)[i]'hab = b[k]'hkb := by
  subst hk
  rw [getElem_append_right (Nat.le_add_right _ _)]
  exact byteArray_getElem_of_idx' rfl (Nat.add_sub_cancel_left _ _) _ hkb

private theorem parsePaxPayload_go_dispatch {bs rest : ByteArray} {offset pos : Nat}
    {seenKeys : List String} {ov : PaxOverrides} {key value : String}
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_eq : (0x3d : UInt8) ∉ key.toUTF8.toList)
    (hsuf : bs.extract pos bs.size = encodePaxRecord key value ++ rest) :
    parsePaxPayload.go bs offset pos seenKeys ov =
      if key.isEmpty || hasNulString key || key.toList.contains '\n' then
        .error { kind := .invalidHeader, message := "invalid PAX record key", offset := some offset }
      else if seenKeys.contains key then
        .error { kind := .invalidHeader, message := s!"duplicate PAX key: {key}", offset := some offset }
      else if startsWithStr key "GNU.sparse." then
        .error { kind := .unsupportedEntry, message := "GNU sparse PAX archives are unsupported", offset := some offset }
      else
        match applyPaxKey ov key value offset with
        | .error err => .error err
        | .ok nextOv =>
          parsePaxPayload.go bs offset (pos + (encodePaxRecord key value).size) (key :: seenKeys) nextOv := by
  rcases encodePaxRecord_parts hkvMin hkvMax with ⟨recLen, hrecLen_eq, hge5, hrec_eq, hrec_sz⟩
  have hpos_le : pos ≤ bs.size := by
    rcases Nat.lt_or_ge bs.size pos with hlt | hle
    · have h0 : (bs.extract pos bs.size).size = 0 := by rw [ByteArray.size_extract]; omega
      rw [hsuf, ByteArray.size_append, hrec_sz] at h0
      omega
    · exact hle
  have hsz_suf : (bs.extract pos bs.size).size = bs.size - pos := by
    rw [ByteArray.size_extract]; omega
  have hbd_rec : pos + recLen ≤ bs.size := by
    have h1 := congrArg ByteArray.size hsuf
    rw [hsz_suf, ByteArray.size_append, hrec_sz] at h1
    omega
  have hnotge_pos : ¬(pos ≥ bs.size) := by omega
  have hget_bs : ∀ (j : Nat) (hj : j < recLen),
      bs[pos + j]'(by omega) = (encodePaxRecord key value)[j]'(by rw [hrec_sz]; exact hj) := by
    intro j hj
    have hidx_e : j < (bs.extract pos bs.size).size := by rw [hsz_suf]; omega
    have h1 := ByteArray.getElem_extract hidx_e
    have hidx_app : j < (encodePaxRecord key value ++ rest).size := by
      rw [ByteArray.size_append, hrec_sz]; omega
    have hfun := congrArg (fun ba : ByteArray => if h : j < ba.size then ba[j]'h else 0) hsuf
    simp only [hidx_e, hidx_app, ↓reduceDIte] at hfun
    rw [← h1, hfun, getElem_append_left (by rw [hrec_sz]; exact hj)]
  let d := (toString recLen).toUTF8.size
  rcases toString_toUTF8_bytes_eq (n := recLen) with ⟨ds, hdigs, _, _, _, _, hbytes_rec, _⟩
  have hrec_utf8_eq : encodePaxRecord key value =
      (toString recLen).toUTF8 ++ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 := by
    rw [hrec_eq, toUTF8_append]
  have hrec_utf8_sz : ((toString recLen).toUTF8 ++ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8).size = recLen := by
    rw [← hrec_utf8_eq, hrec_sz]
  have havoid_sp : ∀ j, pos ≤ j → j < pos + d → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x20 := by
    intro j hj1 hj2 hj
    let k := j - pos
    have hk_lt : k < d := by omega
    have hj_eq : j = pos + k := by omega
    have hk_rec : k < recLen := by rw [hrecLen_eq]; omega
    have hbsj : bs[j]'hj = (encodePaxRecord key value)[k]'(by rw [hrec_sz]; exact hk_rec) := by
      simpa [hj_eq] using hget_bs k hk_rec
    rw [hbsj, byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hk_rec),
      getElem_append_left hk_lt]
    have hk_ba : k < (ds.map (fun d => UInt8.ofNat (0x30 + d))).toByteArray.size := by
      rw [← hbytes_rec]; exact hk_lt
    rw [byteArray_getElem_of_eq' hbytes_rec hk_lt hk_ba, List.getElem_toByteArray]
    have hmem : (ds.map (fun d => UInt8.ofNat (0x30 + d)))[k]'(by
        rw [← List.size_toByteArray]; exact hk_ba) ∈ ds.map (fun d => UInt8.ofNat (0x30 + d)) :=
      List.getElem_mem _
    rw [List.mem_map] at hmem
    rcases hmem with ⟨dig, hdig_mem, hdig_eq⟩
    have hdig_lt := hdigs dig hdig_mem
    intro heq20
    have hn := congrArg UInt8.toNat (hdig_eq.trans heq20)
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
    change 48 + dig = 32 at hn
    omega
  have hsp_idx : bs[pos + d]'(by omega) = 0x20 := by
    have hd_rec : d < recLen := by omega
    rw [hget_bs d hd_rec, byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hd_rec)]
    have hsp_eq : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        " ".toUTF8 ++ (key ++ "=" ++ value ++ "\n").toUTF8 := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
    have hidx0 : d = (toString recLen).toUTF8.size + 0 := (Nat.add_zero d).symm
    rw [byteArray_append_getElem_right' hidx0 (by rw [hrem_sz]; omega)]
    rw [byteArray_getElem_of_eq' hsp_eq _ (by rw [← hsp_eq, hrem_sz]; omega),
      byteArray_append_getElem_left' (by decide : 0 < " ".toUTF8.size)]
    rfl
  have hfind_sp : findByteIn bs 0x20 pos bs.size = some (pos + d) :=
    findByteIn_eq (by omega) (by omega) (Nat.le_refl _) havoid_sp hsp_idx
  have hext_len : bs.extract pos (pos + d) = (toString recLen).toUTF8 := by
    apply ByteArray.ext; apply Array.ext
    · show (bs.extract pos (pos + d)).size = (toString recLen).toUTF8.size
      rw [ByteArray.size_extract]; omega
    · intro i hi1 hi2
      have hi1' : i < (bs.extract pos (pos + d)).size := hi1
      have hi2' : i < d := hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
      have hi_rec : i < recLen := by omega
      rw [hget_bs i hi_rec, byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hi_rec),
        getElem_append_left hi2']
  have hparse_len : parsePaxLen bs pos (pos + d) = some recLen :=
    parsePaxLen_toString (by omega) (by omega) hext_len
  have hnl_idx : bs[pos + recLen - 1]'(by omega) = 0x0a := by
    have hlt_rec : recLen - 1 < recLen := by omega
    have hnl1 : "\n".toUTF8.size = 1 := rfl
    have hsuf_nl : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        (" " ++ key ++ "=" ++ value).toUTF8 ++ "\n".toUTF8 := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        (" " ++ key ++ "=" ++ value).toUTF8.size + "\n".toUTF8.size := by
      rw [hsuf_nl, ByteArray.size_append]
    have hval_sz : (" " ++ key ++ "=" ++ value).toUTF8.size =
        1 + key.toUTF8.size + 1 + value.toUTF8.size := by
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have heq1 : "=".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1, Nat.add_assoc]
    rw [byteArray_getElem_of_idx' rfl (by omega : pos + recLen - 1 = pos + (recLen - 1)) _ (by omega)]
    rw [hget_bs (recLen - 1) hlt_rec,
      byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hlt_rec),
      byteArray_append_getElem_right' (by omega : recLen - 1 = (toString recLen).toUTF8.size + (" " ++ key ++ "=" ++ value).toUTF8.size)
        (by rw [hrem_sz, hnl1]; omega)]
    have hidx0 : (" " ++ key ++ "=" ++ value).toUTF8.size = (" " ++ key ++ "=" ++ value).toUTF8.size + 0 :=
      (Nat.add_zero _).symm
    rw [byteArray_getElem_of_eq' hsuf_nl _ (by rw [ByteArray.size_append, hnl1]; omega),
      byteArray_append_getElem_right' hidx0 (by decide : 0 < "\n".toUTF8.size)]
    rfl
  let eqPos := pos + d + 1 + key.toUTF8.size
  have havoid_eq : ∀ j, pos + d + 1 ≤ j → j < eqPos → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x3d := by
    intro j hj1 hj2 hj
    let k := j - (pos + d + 1)
    have hk_key : k < key.toUTF8.size := by omega
    have hj_rec : j - pos < recLen := by omega
    have hbsj : bs[j]'hj = (encodePaxRecord key value)[j - pos]'(by rw [hrec_sz]; exact hj_rec) := by
      rw [byteArray_getElem_of_idx' rfl (by omega : j = pos + (j - pos)) hj (by omega)]
      exact hget_bs (j - pos) hj_rec
    have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        " ".toUTF8 ++ (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)) := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hsp1 : " ".toUTF8.size = 1 := rfl
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        1 + (key.toUTF8.size + (1 + value.toUTF8.size + 1)) := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
    rw [hbsj, byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec),
      byteArray_append_getElem_right' (by omega : j - pos = (toString recLen).toUTF8.size + (1 + k)) (by rw [hrem_sz]; omega)]
    rw [byteArray_getElem_of_eq' hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega)]
    have htail_sz : (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)).size =
        key.toUTF8.size + (1 + value.toUTF8.size + 1) := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
    rw [byteArray_append_getElem_right' (by rw [hsp1] : 1 + k = " ".toUTF8.size + k) (by rw [htail_sz]; omega),
      getElem_append_left hk_key]
    intro heq3d
    apply hkey_eq
    have hi_ba : k < (key.toList.flatMap String.utf8EncodeChar).toByteArray.size := by
      rw [← toUTF8_eq_toByteArray]; exact hk_key
    rw [toUTF8_toList, ← heq3d, byteArray_getElem_of_eq' (toUTF8_eq_toByteArray key) hk_key hi_ba,
      List.getElem_toByteArray]
    exact List.getElem_mem _
  have heq_idx : bs[eqPos]'(by omega) = 0x3d := by
    have heq_rec : eqPos - pos < recLen := by omega
    rw [byteArray_getElem_of_idx' rfl (by omega : eqPos = pos + (eqPos - pos)) (by omega) (by omega),
      hget_bs (eqPos - pos) heq_rec,
      byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact heq_rec)]
    have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        (" " ++ key).toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8) := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hsp_key : (" " ++ key).toUTF8.size = 1 + key.toUTF8.size := by
      rw [toUTF8_size_append]; rfl
    have heq_tail_sz : ("=".toUTF8 ++ (value ++ "\n").toUTF8).size = 1 + value.toUTF8.size + 1 := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        (" " ++ key).toUTF8.size + ("=".toUTF8 ++ (value ++ "\n").toUTF8).size := by
      rw [hsuf_k, ByteArray.size_append]
    rw [byteArray_append_getElem_right' (by omega : eqPos - pos = (toString recLen).toUTF8.size + (" " ++ key).toUTF8.size)
      (by rw [hrem_sz, heq_tail_sz]; omega)]
    have hidx0 : (" " ++ key).toUTF8.size = (" " ++ key).toUTF8.size + 0 := (Nat.add_zero _).symm
    rw [byteArray_getElem_of_eq' hsuf_k _ (by rw [ByteArray.size_append, heq_tail_sz]; omega),
      byteArray_append_getElem_right' hidx0 (by rw [heq_tail_sz]; omega),
      byteArray_append_getElem_left' (by decide : 0 < "=".toUTF8.size)]
    rfl
  have hfind_eq : findByteIn bs 0x3d (pos + d + 1) (pos + recLen - 1) = some eqPos :=
    findByteIn_eq (by omega) (by omega) (by omega) havoid_eq heq_idx
  have hext_key : bs.extract (pos + d + 1) eqPos = key.toUTF8 := by
    apply ByteArray.ext; apply Array.ext
    · show (bs.extract (pos + d + 1) eqPos).size = key.toUTF8.size
      rw [ByteArray.size_extract]; omega
    · intro i hi1 hi2
      have hi1' : i < (bs.extract (pos + d + 1) eqPos).size := hi1
      have hi2' : i < key.toUTF8.size := hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
      have hj_rec : d + 1 + i < recLen := by omega
      rw [byteArray_getElem_of_idx' rfl (by omega : pos + d + 1 + i = pos + (d + 1 + i)) _ (by omega),
        hget_bs (d + 1 + i) hj_rec,
        byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec)]
      have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
          " ".toUTF8 ++ (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)) := by
        simp only [toUTF8_append, ByteArray.append_assoc]
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
          1 + (key.toUTF8.size + (1 + value.toUTF8.size + 1)) := by
        have heq1 : "=".toUTF8.size = 1 := rfl
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
      rw [byteArray_append_getElem_right' (by omega : d + 1 + i = (toString recLen).toUTF8.size + (1 + i))
        (by rw [hrem_sz]; omega),
        byteArray_getElem_of_eq' hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega)]
      have htail_sz : (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)).size =
          key.toUTF8.size + (1 + value.toUTF8.size + 1) := by
        have heq1 : "=".toUTF8.size = 1 := rfl
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
      rw [byteArray_append_getElem_right' (by rw [hsp1] : 1 + i = " ".toUTF8.size + i) (by rw [htail_sz]; omega),
        getElem_append_left hi2']
  have hext_val : bs.extract (eqPos + 1) (pos + recLen - 1) = value.toUTF8 := by
    apply ByteArray.ext; apply Array.ext
    · show (bs.extract (eqPos + 1) (pos + recLen - 1)).size = value.toUTF8.size
      rw [ByteArray.size_extract]; omega
    · intro i hi1 hi2
      have hi1' : i < (bs.extract (eqPos + 1) (pos + recLen - 1)).size := hi1
      have hi2' : i < value.toUTF8.size := hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
      have hj_rec : d + 1 + key.toUTF8.size + 1 + i < recLen := by omega
      rw [byteArray_getElem_of_idx' rfl (by omega : eqPos + 1 + i = pos + (d + 1 + key.toUTF8.size + 1 + i)) _ (by omega),
        hget_bs (d + 1 + key.toUTF8.size + 1 + i) hj_rec,
        byteArray_getElem_of_eq' hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec)]
      have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
          (" " ++ key ++ "=").toUTF8 ++ (value.toUTF8 ++ "\n".toUTF8) := by
        simp only [toUTF8_append, ByteArray.append_assoc]
      have hpre_sz : (" " ++ key ++ "=").toUTF8.size = 1 + key.toUTF8.size + 1 := by
        rw [toUTF8_size_append, toUTF8_size_append]; rfl
      have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
          (" " ++ key ++ "=").toUTF8.size + (value.toUTF8.size + 1) := by
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        rw [hsuf_k, ByteArray.size_append, ByteArray.size_append, hnl1]
      have hvalnl_sz : (value.toUTF8 ++ "\n".toUTF8).size = value.toUTF8.size + 1 := by
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        rw [ByteArray.size_append, hnl1]
      rw [byteArray_append_getElem_right' (by omega : d + 1 + key.toUTF8.size + 1 + i =
        (toString recLen).toUTF8.size + ((" " ++ key ++ "=").toUTF8.size + i))
        (by rw [hrem_sz, hpre_sz]; omega),
        byteArray_getElem_of_eq' hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega),
        byteArray_append_getElem_right' (by omega : (" " ++ key ++ "=").toUTF8.size + i =
          (" " ++ key ++ "=").toUTF8.size + i) (by rw [hvalnl_sz]; omega),
        getElem_append_left hi2']
  have hnl_bd : pos + recLen - 1 < bs.size := by omega
  rw [parsePaxPayload.go.eq_1]
  simp only [hnotge_pos, ↓reduceIte, hfind_sp, hparse_len, Nat.not_lt_of_ge hge5,
    Nat.not_lt_of_ge hbd_rec, hnl_bd, ↓reduceDIte, Bool.not_true, Bool.false_eq_true,
    hnl_idx, beq_self_eq_true, hfind_eq, hext_key, hext_val, fromUTF8?_toUTF8, hrec_sz]
  rfl

private theorem encodePaxRecord_size_le_max {key value : String}
    (_hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ 1000) :
    (encodePaxRecord key value).size ≤ 1024 := by
  rcases encodePaxRecord_parts _hkvMin (by have : maxPaxHeaderBytes = 1048576 := rfl; omega) with
    ⟨recLen, h1, hge5, _, hsz⟩
  have hd : (toString recLen).toUTF8.size ≤ 24 := by
    rcases toString_toUTF8_bytes_eq (n := recLen) with ⟨ds, _, _, hhead, _, hfold, _, hsz_ds⟩
    rcases hhead (by omega) with ⟨hd0, tl, hds_eq, hhd0⟩
    have hgen : ∀ (xs : List Nat) (init : Nat),
        xs.foldl (fun a d => a * 10 + d) init ≥ init * 10 ^ xs.length := by
      intro xs
      induction xs with
      | nil => intro init; simp
      | cons x xs ih =>
        intro init
        simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
        have hstep := ih (init * 10 + x)
        have hmul : init * (10 ^ xs.length * 10) = (init * 10) * 10 ^ xs.length := by
          rw [Nat.mul_comm (10 ^ xs.length) 10, ← Nat.mul_assoc]
        have hle : (init * 10) * 10 ^ xs.length ≤ (init * 10 + x) * 10 ^ xs.length :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        omega
    have hpow_ds : 10 ^ (ds.length - 1) ≤ recLen := by
      have hsub : ds.length - 1 = tl.length := by simp [hds_eq]
      rw [hsub, ← hfold, hds_eq]
      simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
      have hg := hgen tl hd0
      have h1_le : 1 * 10 ^ tl.length ≤ hd0 * 10 ^ tl.length := Nat.mul_le_mul_right _ hhd0
      omega
    have hgap : ∀ m, 6 ≤ m → m + 1000 < 10 ^ (m - 1) := by
      intro m hm
      induction m with
      | zero => omega
      | succ k ih =>
        rcases Nat.lt_or_ge k 6 with hk | hk
        · have hk5 : k = 5 := by omega
          subst hk5; decide
        · have ihk := ih hk
          have hsub : k + 1 - 1 = (k - 1) + 1 := by omega
          rw [hsub, Nat.pow_succ]
          omega
    have hrec_le : recLen ≤ ds.length + 1000 := by
      have hrem : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
          1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
        have hsp1 : " ".toUTF8.size = 1 := rfl
        have heq1 : "=".toUTF8.size = 1 := rfl
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
      omega
    rcases Nat.lt_or_ge ds.length 6 with hlt6 | hge6
    · omega
    · have hbig := hgap ds.length hge6
      omega
  rw [hsz]
  have hrem : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
      1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
    have hsp1 : " ".toUTF8.size = 1 := rfl
    have heq1 : "=".toUTF8.size = 1 := rfl
    have hnl1 : "\n".toUTF8.size = 1 := rfl
    simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
  omega

private theorem unpackWith_mkPaxFrame_err (pax : ByteArray)
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes)
    {e : TarError} (hparse_pax : parsePaxPayload pax 0 = .error e) :
    Impl.unpackWith {} (mkPaxFrame pax ++ baseHdr5 ++ twoZeroBlocks) = .error e := by
  let frame := mkPaxFrame pax
  let hdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" ""
  let post := baseHdr5 ++ twoZeroBlocks
  let bytes := frame ++ post
  have hframe_sz : frame.size = 512 + pad512 pax.size := mkPaxFrame_size pax
  have hpost_sz : post.size = 512 + 1024 := by
    simp only [post, ByteArray.size_append, baseHdr5_size, twoZeroBlocks_size]
  have hbytes_sz : bytes.size = frame.size + post.size := by
    simp only [bytes, ByteArray.size_append]
  have hmod_pad : pad512 pax.size % 512 = 0 := by
    unfold pad512
    exact Nat.mul_mod_left _ 512
  have hne : bytes.size ≠ 0 := by rw [hbytes_sz, hframe_sz]; omega
  have hmod : bytes.size % 512 = 0 := by rw [hbytes_sz, hframe_sz, hpost_sz]; omega
  have hstart : Impl.unpackWith {} bytes = unpackLoop {} bytes 0 none [] [] 0 := by
    unfold Impl.unpackWith
    have h1 : (bytes.size == 0) = false := beq_false_of_ne hne
    have h2 : (bytes.size % 512 != 0) = false := by simp [bne, hmod]
    rw [h1, h2]
    rfl
  have hassoc : bytes = ByteArray.empty ++ hdr ++ (padBlock512 pax ++ post) := by
    simp only [bytes, frame, mkPaxFrame, hdr, ByteArray.empty_append, ByteArray.append_assoc]
  have hhdr_sz : hdr.size = 512 := mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have hext_hdr : bytes.extract 0 (0 + 512) = hdr := by
    rw [hassoc]
    have ha := extract_append_mid (ByteArray.empty) hdr (padBlock512 pax ++ post)
    rw [ByteArray.size_empty, Nat.zero_add, hhdr_sz] at ha
    exact ha
  have hnz : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz, hframe_sz, hpost_sz]; omega) hext_hdr
  have hmax : maxPaxHeaderBytes < ustarOctal11Limit := by decide
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := pax.size, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by omega) (by decide)
      (by rw [hbytes_sz, hframe_sz, hpost_sz]; omega) hext_hdr
  have hpax_ext : bytes.extract (0 + 512) (0 + 512 + pax.size) = pax := by
    have h1 : bytes.extract (0 + 512) (0 + 512 + pad512 pax.size) = padBlock512 pax := by
      rw [hassoc]
      have ha : (ByteArray.empty ++ hdr).size = 0 + 512 := by
        rw [ByteArray.empty_append, hhdr_sz]
      have hsub := extract_append_mid (ByteArray.empty ++ hdr) (padBlock512 pax) post
      rw [ha, padBlock512_size, ByteArray.append_assoc] at hsub
      exact hsub
    have hle : pax.size ≤ pad512 pax.size := le_pad512 pax.size
    have h2 : bytes.extract (0 + 512) (0 + 512 + pax.size) =
        (bytes.extract (0 + 512) (0 + 512 + pad512 pax.size)).extract 0 pax.size := by
      rw [ByteArray.extract_extract]
      exact congrArg (bytes.extract (0 + 512)) (by omega)
    rw [h2, h1, padBlock512_extract_prefix]
  have hnotge : ¬(0 ≥ bytes.size) := by rw [hbytes_sz, hframe_sz]; omega
  have hnotgt : ¬(0 + 512 > bytes.size) := by rw [hbytes_sz, hframe_sz, hpost_sz]; omega
  have hnot_max : ¬(pax.size > maxPaxHeaderBytes) := by omega
  have hnot_trunc : ¬(0 + 512 + pad512 pax.size > bytes.size) := by
    rw [hbytes_sz, hframe_sz, hpost_sz]; omega
  have h78 : ((0x78 : UInt8) == 0x78) = true := rfl
  have hbytes_eq : (mkPaxFrame pax ++ baseHdr5 ++ twoZeroBlocks) = bytes := by
    simp only [bytes, frame, post, ByteArray.append_assoc]
  rw [hbytes_eq, hstart, unpackLoop.eq_1]
  simp only [hnotge, ↓reduceIte]
  rw [unpackStep.eq_1]
  have hnone : (none : Option PaxOverrides).isSome = false := rfl
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt, hparse_hdr,
    hnone, hnot_max, hnot_trunc, hpax_ext, hparse_pax, h78]

/-- Case 12 of Test 5: `sparsePax` fails with `.unsupportedEntry`. -/
theorem test5_sparsePax_err :
    ∃ e, Impl.unpackWith {} (mkPaxFrame (encodePaxRecord "GNU.sparse.major" "1") ++ baseHdr5 ++ twoZeroBlocks) =
      .error e ∧ e.kind = .unsupportedEntry ∧ e.message ≠ "" := by
  let pax := encodePaxRecord "GNU.sparse.major" "1"
  have hmin : 4 ≤ (" " ++ "GNU.sparse.major" ++ "=" ++ "1" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1 : (" " ++ "GNU.sparse.major" ++ "=" ++ "1" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax : (" " ++ "GNU.sparse.major" ++ "=" ++ "1" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hpax_sz : pax.size ≤ maxPaxHeaderBytes := by
    have h1 : pax.size ≤ 1024 := encodePaxRecord_size_le_max hmin hmax1
    have h2 : maxPaxHeaderBytes = 1048576 := rfl
    omega
  have heq61 : (0x3d : UInt8) ∉ ("GNU.sparse.major").toUTF8.toList := by
    rw [toUTF8_toList]; decide
  have hsuf : pax.extract 0 pax.size = pax ++ ByteArray.empty := by
    rw [ByteArray.extract_zero_size, ByteArray.append_empty]
  have hparse : parsePaxPayload pax 0 =
      .error { kind := .unsupportedEntry, message := "GNU sparse PAX archives are unsupported", offset := some 0 } := by
    unfold parsePaxPayload
    rw [parsePaxPayload_go_dispatch hmin hmax heq61 hsuf]
    have hc1 : ("GNU.sparse.major".isEmpty || hasNulString "GNU.sparse.major" ||
        "GNU.sparse.major".toList.contains '\n') = false := by decide
    have hc2 : ([].contains "GNU.sparse.major") = false := rfl
    have hc3 : startsWithStr "GNU.sparse.major" "GNU.sparse." = true := by decide
    simp only [hc1, hc2, hc3, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, unpackWith_mkPaxFrame_err pax hpax_sz hparse, rfl, by decide⟩

/-- Case 13 of Test 5: `nulUnamePax` fails with `.invalidHeader`. -/
theorem test5_nulUnamePax_err :
    ∃ e, Impl.unpackWith {} (mkPaxFrame (encodePaxRecord "uname" "a\x00b") ++ baseHdr5 ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let pax := encodePaxRecord "uname" "a\x00b"
  have hmin : 4 ≤ (" " ++ "uname" ++ "=" ++ "a\x00b" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1 : (" " ++ "uname" ++ "=" ++ "a\x00b" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax : (" " ++ "uname" ++ "=" ++ "a\x00b" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hpax_sz : pax.size ≤ maxPaxHeaderBytes := by
    have h1 : pax.size ≤ 1024 := encodePaxRecord_size_le_max hmin hmax1
    have h2 : maxPaxHeaderBytes = 1048576 := rfl
    omega
  have heq61 : (0x3d : UInt8) ∉ ("uname").toUTF8.toList := by
    rw [toUTF8_toList]; decide
  have hsuf : pax.extract 0 pax.size = pax ++ ByteArray.empty := by
    rw [ByteArray.extract_zero_size, ByteArray.append_empty]
  have happly : applyPaxKey {} "uname" "a\x00b" 0 =
      .error { kind := .invalidHeader, message := "NUL byte in PAX uname", offset := some 0 } := by
    unfold applyPaxKey
    have hn : hasNulString "a\x00b" = true := by decide
    simp [hn]
  have hparse : parsePaxPayload pax 0 =
      .error { kind := .invalidHeader, message := "NUL byte in PAX uname", offset := some 0 } := by
    unfold parsePaxPayload
    rw [parsePaxPayload_go_dispatch hmin hmax heq61 hsuf]
    have hc1 : ("uname".isEmpty || hasNulString "uname" || "uname".toList.contains '\n') = false := by decide
    have hc2 : ([].contains "uname") = false := rfl
    have hc3 : startsWithStr "uname" "GNU.sparse." = false := by decide
    simp only [hc1, hc2, hc3, Bool.false_eq_true, ↓reduceIte, happly]
  exact ⟨_, unpackWith_mkPaxFrame_err pax hpax_sz hparse, rfl, by decide⟩

/-- Case 14 of Test 5: `dupPathPax` fails with `.invalidHeader`. -/
theorem test5_dupPathPax_err :
    ∃ e, Impl.unpackWith {}
        (mkPaxFrame (encodePaxRecord "path" "a" ++ encodePaxRecord "path" "b") ++ baseHdr5 ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let r1 := encodePaxRecord "path" "a"
  let r2 := encodePaxRecord "path" "b"
  let pax := r1 ++ r2
  have hmin1 : 4 ≤ (" " ++ "path" ++ "=" ++ "a" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1' : (" " ++ "path" ++ "=" ++ "a" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1 : (" " ++ "path" ++ "=" ++ "a" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hmin2 : 4 ≤ (" " ++ "path" ++ "=" ++ "b" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax2' : (" " ++ "path" ++ "=" ++ "b" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax2 : (" " ++ "path" ++ "=" ++ "b" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hpax_sz : pax.size ≤ maxPaxHeaderBytes := by
    have hr1 : r1.size ≤ 1024 := encodePaxRecord_size_le_max hmin1 hmax1'
    have hr2 : r2.size ≤ 1024 := encodePaxRecord_size_le_max hmin2 hmax2'
    have h2 : maxPaxHeaderBytes = 1048576 := rfl
    rw [ByteArray.size_append]
    omega
  have heq61 : (0x3d : UInt8) ∉ ("path").toUTF8.toList := by
    rw [toUTF8_toList]; decide
  have hsuf1 : pax.extract 0 pax.size = r1 ++ r2 := by
    rw [ByteArray.extract_zero_size]
  have hsuf2 : pax.extract (0 + r1.size) pax.size = r2 ++ ByteArray.empty := by
    rw [Nat.zero_add, ByteArray.size_append, ByteArray.append_empty,
      extract_append_right r1 r2 r2.size, ByteArray.extract_zero_size]
  have hstep1 := parsePaxPayload_go_step (bs := pax) (rest := r2) (offset := 0) (pos := 0)
    (seenKeys := []) (ov := {}) (nextOv := { path? := some "a" }) (key := "path") (value := "a")
    hmin1 hmax1 (by decide) (by decide) (by decide) heq61 rfl (by decide) rfl hsuf1
  have hparse : parsePaxPayload pax 0 =
      .error { kind := .invalidHeader, message := "duplicate PAX key: path", offset := some 0 } := by
    unfold parsePaxPayload
    rw [hstep1, parsePaxPayload_go_dispatch hmin2 hmax2 heq61 hsuf2]
    have hc1 : ("path".isEmpty || hasNulString "path" || "path".toList.contains '\n') = false := by decide
    have hc2 : (["path"].contains "path") = true := by decide
    simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte]
    rfl
  exact ⟨_, unpackWith_mkPaxFrame_err pax hpax_sz hparse, rfl, by decide⟩

/-- Case 15 of Test 5: `badLenPax` fails with `.invalidHeader`. -/
theorem test5_badLenPax_err :
    ∃ e, Impl.unpackWith {} (mkPaxFrame "09 path=a\n".toUTF8 ++ baseHdr5 ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let pax := "09 path=a\n".toUTF8
  let lit : ByteArray := { data := #[0x30, 0x39, 0x20, 0x70, 0x61, 0x74, 0x68, 0x3d, 0x61, 0x0a] }
  have hpax_eq : pax = lit := by
    dsimp [pax, lit]
    rw [toUTF8_eq_toByteArray]
    decide
  have hpax_sz_val : pax.size = 10 := by rw [hpax_eq]; decide
  have hpax_sz : pax.size ≤ maxPaxHeaderBytes := by
    rw [hpax_sz_val]; decide
  have havoid : ∀ j, 0 ≤ j → j < 2 → ∀ hj : j < pax.size, pax[j]'hj ≠ 0x20 := by
    intro j _ hj2 hj
    rw [byteArray_getElem_of_eq' hpax_eq hj (by rw [← hpax_eq]; exact hj)]
    have h0 : lit[0]'(by decide) ≠ 0x20 := by decide
    have h1 : lit[1]'(by decide) ≠ 0x20 := by decide
    match j with
    | 0 => exact h0
    | 1 => exact h1
  have hsp : pax[2]'(by rw [hpax_sz_val]; omega) = 0x20 := by
    rw [byteArray_getElem_of_eq' hpax_eq (by rw [hpax_sz_val]; omega) (by decide)]
    decide
  have hfind : findByteIn pax 0x20 0 pax.size = some 2 :=
    findByteIn_eq (by omega) (by rw [hpax_sz_val]; omega) (by omega) havoid hsp
  have hext2 : pax.extract 0 2 = { data := #[0x30, 0x39] } := by
    let target : ByteArray := { data := #[0x30, 0x39] }
    have ht_sz : target.size = 2 := by decide
    have hlit_sz : lit.size = 10 := by decide
    change pax.extract (0 + 0) (0 + 2) = target
    apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [hpax_sz_val]; omega) ht_sz
    intro k hk
    have hl : pax[0 + 0 + k]'(by rw [hpax_sz_val]; omega) = pax[k]'(by rw [hpax_sz_val]; omega) := by
      congr 1; omega
    rw [hl, byteArray_getElem_of_eq' hpax_eq (by rw [hpax_sz_val]; omega) (by rw [hlit_sz]; omega)]
    rcases k with _ | k'
    · rfl
    · rcases k' with _ | _
      · rfl
      · omega
  have hlen : parsePaxLen pax 0 2 = none := by
    unfold parsePaxLen
    rw [hext2, byteArray_toList_eq]
    rfl
  have hparse : parsePaxPayload pax 0 =
      .error { kind := .invalidHeader, message := "invalid PAX record length", offset := some 0 } := by
    unfold parsePaxPayload
    rw [parsePaxPayload.go.eq_1]
    have hnotge : ¬(0 ≥ pax.size) := by rw [hpax_sz_val]; omega
    simp only [hnotge, ↓reduceIte, hfind, hlen]
  exact ⟨_, unpackWith_mkPaxFrame_err pax hpax_sz hparse, rfl, by decide⟩

private theorem validPax_abstract (pax : ByteArray)
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes)
    (hparse_pax : parsePaxPayload pax 0 = .ok { mtime? := some 1794744353 }) :
    ∃ res, Impl.unpackWith {} (mkPaxFrame pax ++ baseHdr5 ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }] res := by
  let ov1 : PaxOverrides := { mtime? := some 1794744353 }
  let pre := ByteArray.empty
  let post := baseHdr5 ++ twoZeroBlocks
  let bytes := pre ++ mkPaxFrame pax ++ post
  have hframe_sz : (mkPaxFrame pax).size = 512 + pad512 pax.size := mkPaxFrame_size pax
  have hpost_sz : post.size = 512 + 1024 := by
    simp only [post, ByteArray.size_append, baseHdr5_size, twoZeroBlocks_size]
  have hbytes_sz : bytes.size = (mkPaxFrame pax).size + post.size := by
    simp only [bytes, pre, ByteArray.empty_append, ByteArray.size_append]
  have hmod_pad : pad512 pax.size % 512 = 0 := by
    unfold pad512; exact Nat.mul_mod_left _ 512
  have hstart : Impl.unpackWith {} (mkPaxFrame pax ++ baseHdr5 ++ twoZeroBlocks) =
      unpackLoop {} bytes pre.size none [] [] 0 := by
    have heq : (mkPaxFrame pax ++ baseHdr5 ++ twoZeroBlocks) = bytes := by
      simp only [bytes, pre, post, ByteArray.empty_append, ByteArray.append_assoc]
    have hne : bytes.size ≠ 0 := by rw [hbytes_sz, hframe_sz]; omega
    have hmod : bytes.size % 512 = 0 := by rw [hbytes_sz, hframe_sz, hpost_sz]; omega
    rw [heq]
    unfold Impl.unpackWith
    have h1 : (bytes.size == 0) = false := beq_false_of_ne hne
    have h2 : (bytes.size % 512 != 0) = false := by simp [bne, hmod]
    rw [h1, h2]
    rfl
  have hstep_pax := unpackLoop_mkPaxFrame_step_any {} pre post pax [] [] 0 hpax_sz ov1
    (by simp only [pre, ByteArray.size_empty]; exact hparse_pax)
  let off1 := pre.size + 512 + pad512 pax.size
  have hoff1_eq : off1 = (pre ++ mkPaxFrame pax).size := by
    simp only [off1, pre, ByteArray.empty_append, ByteArray.size_empty, hframe_sz, Nat.zero_add]
  have hassoc1 : bytes = (pre ++ mkPaxFrame pax) ++ baseHdr5 ++ twoZeroBlocks := by
    simp only [bytes, post, ByteArray.append_assoc]
  have hext_hdr : bytes.extract off1 (off1 + 512) = baseHdr5 := by
    rw [hoff1_eq, hassoc1]
    have h := extract_append_mid (pre ++ mkPaxFrame pax) baseHdr5 twoZeroBlocks
    rw [baseHdr5_size] at h
    exact h
  have hbound : off1 + 512 ≤ bytes.size := by
    rw [hbytes_sz, hframe_sz, hpost_sz]
    dsimp only [off1, pre]
    rw [ByteArray.size_empty]
    omega
  have hnz : isZeroRange bytes off1 512 = false :=
    isZeroRange_mkUstarHeader_false hbound hext_hdr
  have hparse_hdr : parseUstarHeader bytes off1 =
      .ok { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      hbound hext_hdr
  have hval : validateEntryPath false false .regular "a.txt" = .ok "a.txt" := rfl
  let entry : TarEntry :=
    { path := "a.txt", kind := .regular, mode := ((420 : UInt32) &&& 0o7777).toNat.toUInt32,
      uid := 0, gid := 0, mtime := 1794744353, uname := "", gname := "",
      data := ByteArray.empty, linkTarget := "" }
  have hdec : decodeTarEntry {} bytes off1
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 }
      (some ov1) [] 0 0 = .ok (entry, 0) := by
    have hsz0 : ov1.size?.getD 0 = 0 := rfl
    have hpad0 : pad512 0 = 0 := rfl
    have h0 := decodeTarEntry_mkUstarHeader_regular {} bytes baseHdr5 off1 (some ov1) [] 0 0
      hbound hext_hdr rfl
      (by rw [toUTF8_eq_toByteArray]; decide) (by rw [toUTF8_eq_toByteArray]; decide)
      (by rw [toUTF8_eq_toByteArray]; decide) (by rw [toUTF8_eq_toByteArray]; decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by dsimp only [ov1]; decide)
      (by rw [Option.getD_some, hsz0, hpad0]; omega)
      (by dsimp only [ov1]; exact hval) rfl
    dsimp only [ov1, pad512, entry] at h0 ⊢
    exact h0
  have hstep_reg : unpackLoop {} bytes off1 (some ov1) [] [] 0 =
      unpackLoop {} bytes (off1 + 512) none ["a.txt"] [entry] 0 := by
    have hnotge : ¬(off1 ≥ bytes.size) := by omega
    have hnotgt : ¬(off1 + 512 > bytes.size) := by omega
    have hnot78 : ((48 : UInt8) == 0x78) = false := rfl
    have hadv : off1 + 512 + 0 > off1 := by omega
    have hdat0 : entry.data.size = 0 := rfl
    have hlen0 : ([] : List TarEntry).length = 0 := rfl
    have hpath : entry.path = "a.txt" := rfl
    rw [unpackLoop.eq_1]
    simp only [hnotge, ↓reduceIte]
    rw [unpackStep.eq_1]
    simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt, hparse_hdr,
      hnot78, hlen0, hdec, hadv, Nat.add_zero, hdat0, hpath]
  have hstep_end : unpackLoop {} bytes (off1 + 512) none ["a.txt"] [entry] 0 = .ok [entry] := by
    have hpre_sz : (pre ++ mkPaxFrame pax ++ baseHdr5).size = off1 + 512 := by
      rw [ByteArray.size_append, ← hoff1_eq, baseHdr5_size]
    have htwos : twoZeroBlocks = zeroBlock ++ zeroBlock := rfl
    rw [hassoc1, ← hpre_sz, htwos]
    exact unpackLoop_at_twoZeroBlocks {} (pre ++ mkPaxFrame pax ++ baseHdr5) ["a.txt"] [entry] 0
  refine ⟨[entry], ?_, ?_⟩
  · rw [hstart, hstep_pax, hstep_reg, hstep_end]
  · change TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }]
      [{ path := "a.txt", kind := .regular, mode := ((420 : UInt32) &&& 0o7777).toNat.toUInt32,
         uid := 0, gid := 0, mtime := 1794744353, uname := "", gname := "",
         data := ByteArray.empty, linkTarget := "" }]
    have hmod : ((420 : UInt32) &&& 0o7777).toNat.toUInt32 = 420 := by decide
    rw [hmod]
    exact tarEquiv_singleton_self { path := "a.txt", kind := .regular, mtime := 1794744353 }

/-- Case 16 of Test 5: `validPax` succeeds applying `mtime` and ignoring `SCHILY.xattr.user`. -/
theorem test5_validPax_ok :
    ∃ res, Impl.unpackWith {}
        (mkPaxFrame (encodePaxRecord "mtime" "1794744353.8699822" ++
          encodePaxRecord "SCHILY.xattr.user" "ok") ++ baseHdr5 ++ twoZeroBlocks) =
      .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }] res := by
  let r1 := encodePaxRecord "mtime" "1794744353.8699822"
  let r2 := encodePaxRecord "SCHILY.xattr.user" "ok"
  let pax := r1 ++ r2
  have hmin1 : 4 ≤ (" " ++ "mtime" ++ "=" ++ "1794744353.8699822" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1' : (" " ++ "mtime" ++ "=" ++ "1794744353.8699822" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax1 : (" " ++ "mtime" ++ "=" ++ "1794744353.8699822" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hmin2 : 4 ≤ (" " ++ "SCHILY.xattr.user" ++ "=" ++ "ok" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax2' : (" " ++ "SCHILY.xattr.user" ++ "=" ++ "ok" ++ "\n").toUTF8.size ≤ 1000 := by
    rw [toUTF8_eq_toByteArray]; decide
  have hmax2 : (" " ++ "SCHILY.xattr.user" ++ "=" ++ "ok" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl; omega
  have hpax_sz : pax.size ≤ maxPaxHeaderBytes := by
    have hr1 : r1.size ≤ 1024 := encodePaxRecord_size_le_max hmin1 hmax1'
    have hr2 : r2.size ≤ 1024 := encodePaxRecord_size_le_max hmin2 hmax2'
    have h2 : maxPaxHeaderBytes = 1048576 := rfl
    rw [ByteArray.size_append]
    omega
  let ov1 : PaxOverrides := { mtime? := some 1794744353 }
  have happly1 : applyPaxKey {} "mtime" "1794744353.8699822" 0 = .ok ov1 := by
    rfl
  have happly2 : applyPaxKey ov1 "SCHILY.xattr.user" "ok" 0 = .ok ov1 := by
    rfl
  have hsuf1 : pax.extract 0 pax.size = r1 ++ r2 := by
    rw [ByteArray.extract_zero_size]
  have hsuf2 : pax.extract (0 + r1.size) pax.size = r2 ++ ByteArray.empty := by
    rw [Nat.zero_add, ByteArray.size_append, ByteArray.append_empty,
      extract_append_right r1 r2 r2.size, ByteArray.extract_zero_size]
  have hstep1 := parsePaxPayload_go_step (bs := pax) (rest := r2) (offset := 0) (pos := 0)
    (seenKeys := []) (ov := {}) (nextOv := ov1) (key := "mtime") (value := "1794744353.8699822")
    hmin1 hmax1 (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide) rfl
    (by decide) happly1 hsuf1
  have hstep2 := parsePaxPayload_go_step (bs := pax) (rest := ByteArray.empty) (offset := 0) (pos := r1.size)
    (seenKeys := ["mtime"]) (ov := ov1) (nextOv := ov1) (key := "SCHILY.xattr.user") (value := "ok")
    hmin2 hmax2 (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide) (by decide)
    (by decide) happly2 (by simpa [ByteArray.size_append, ByteArray.append_empty] using hsuf2)
  have hparse_pax : parsePaxPayload pax 0 = .ok ov1 := by
    unfold parsePaxPayload
    rw [hstep1, Nat.zero_add, hstep2]
    rw [parsePaxPayload.go.eq_1]
    have hdone : r1.size + (encodePaxRecord "SCHILY.xattr.user" "ok").size ≥ pax.size := by
      change r1.size + r2.size ≥ pax.size
      rw [ByteArray.size_append]
      omega
    rw [ite_eq_left hdone]
  exact validPax_abstract pax hpax_sz hparse_pax

end LeanSwe.Tar.Proofs

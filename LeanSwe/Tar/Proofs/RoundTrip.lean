import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem utf8EncodeChar_all_lt128 {c : Char}
    (h : (String.utf8EncodeChar c).all (fun b => decide (b < 128)) = true) : c.toNat < 128 := by
  by_cases hc : c.val.toNat ≤ 127
  · exact Nat.lt_succ_of_le hc
  · exfalso; dsimp only [String.utf8EncodeChar] at h; simp only [hc, ↓reduceIte] at h
    by_cases hc2 : c.val.toNat ≤ 2047
    · simp only [hc2, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      have : (c.val.toNat / 64 % 32 + 192) % 256 < 128 := h.1; omega
    · simp only [hc2, ↓reduceIte] at h
      by_cases hc3 : c.val.toNat ≤ 65535
      · simp only [hc3, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
        have : (c.val.toNat / 4096 % 16 + 224) % 256 < 128 := h.1; omega
      · simp only [hc3, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
        have : (c.val.toNat / 262144 % 8 + 240) % 256 < 128 := h.1; have := c.valid; omega

private theorem utf8EncodeChar_length_pos (c : Char) : 1 ≤ (String.utf8EncodeChar c).length := by
  unfold String.utf8EncodeChar; dsimp only
  split <;> try simp
  split <;> try simp
  split <;> simp

private theorem isAsciiString_asciiFallback_eq {s : String} {maxChars : Nat}
    (hasc : isAsciiString s = true) (hsz : s.toUTF8.size ≤ maxChars) : asciiFallback s maxChars = s := by
  unfold isAsciiString at hasc; rw [toUTF8_toList] at hasc
  have hflat : ∀ cs : List Char, (cs.flatMap String.utf8EncodeChar).all (fun b => decide (b < 128)) = true →
      (∀ c ∈ cs, c.toNat < 128) ∧ cs.length ≤ (cs.flatMap String.utf8EncodeChar).length := by
    intro cs; induction cs with
    | nil => exact fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h), Nat.le_refl 0⟩
    | cons c cs ih =>
      intro h; rw [List.flatMap_cons, List.all_append, Bool.and_eq_true] at h
      have ⟨hcs, hlen⟩ := ih h.2; have hpos := utf8EncodeChar_length_pos c
      refine ⟨fun x hx => ?_, by rw [List.flatMap_cons, List.length_append, List.length_cons]; omega⟩
      exact (List.mem_cons.mp hx).elim (· ▸ utf8EncodeChar_all_lt128 h.1) (hcs x)
  have ⟨hchars, hlen_le⟩ := hflat s.toList hasc
  have hs_sz : s.toUTF8.size = (s.toList.flatMap String.utf8EncodeChar).length := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]
  have hmap : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
      List.map (fun c => if c.toNat < 128 then c else '?') cs = cs := by
    intro cs; induction cs with
    | nil => exact fun _ => rfl
    | cons c cs ih =>
      intro hc; simp only [List.map_cons, hc c (by simp), ↓reduceIte]
      exact congrArg (c :: ·) (ih fun x hx => hc x (by simp [hx]))
  unfold asciiFallback
  rw [List.take_of_length_le (by omega), hmap s.toList hchars, String.ofList_toList]

/-- Encode a list of `(key, val)` PAX extended header records by concatenation. -/
def encodePaxRecords : List (String × String) → ByteArray
  | [] => ByteArray.empty
  | (k, v) :: rest => encodePaxRecord k v ++ encodePaxRecords rest

private theorem encodePaxRecords_append (xs ys : List (String × String)) :
    encodePaxRecords (xs ++ ys) = encodePaxRecords xs ++ encodePaxRecords ys := by
  induction xs with
  | nil => simp [encodePaxRecords, ByteArray.empty_append]
  | cons _ _ ih => simp [encodePaxRecords, ih, ByteArray.append_assoc]

private def ValidPaxKey (key : String) : Prop :=
  !key.isEmpty = true ∧ !hasNulString key = true ∧ !key.toList.contains '\n' = true ∧
    (0x3d : UInt8) ∉ key.toUTF8.toList ∧ !startsWithStr key "GNU.sparse." = true

private def validPaxKeyBool (key : String) : Bool :=
  !key.isEmpty && !hasNulString key && !key.toList.contains '\n' &&
    !(key.toList.flatMap String.utf8EncodeChar).contains 0x3d && !startsWithStr key "GNU.sparse."

private theorem validPaxKey_of_bool {key : String} (h : validPaxKeyBool key = true) : ValidPaxKey key := by
  unfold validPaxKeyBool at h; simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, ?_, by simpa using h5⟩
  rw [toUTF8_toList]; intro hm; rw [List.contains_iff_mem.mpr hm] at h4; cases h4

private theorem paxRecord_size_bounds (key value : String) (hk : !key.isEmpty = true) :
    4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ∧
    (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ (encodePaxRecord key value).size := by
  have hk_pos : 1 ≤ key.toUTF8.size := by
    cases hcl : key.toList with
    | nil =>
      have : key = "" := by rw [← String.ofList_toList (s := key), hcl]
      subst this; simp at hk
    | cons c _ =>
      have := utf8EncodeChar_length_pos c
      rw [toUTF8_eq_toByteArray, List.size_toByteArray, hcl, List.flatMap_cons, List.length_append]; omega
  have hsuf : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size = 1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
    simp only [toUTF8_size_append]; rfl
  have hrec : (encodePaxRecord key value).size =
      (toString (paxRecordTotalLen (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)).toUTF8.size +
        (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size := by simp only [encodePaxRecord, toUTF8_size_append]
  exact ⟨by omega, by omega⟩

private def foldPaxKeys (offset : Nat) : List (String × String) → PaxOverrides → Except TarError PaxOverrides
  | [], ov => .ok ov
  | (k, v) :: rest, ov => applyPaxKey ov k v offset >>= foldPaxKeys offset rest

private theorem parsePaxPayload_go_records {bs : ByteArray} {offset fuel : Nat}
    (recs : List (String × String)) (pre : ByteArray) (seenKeys : List String) (ov finalOv : PaxOverrides)
    (hbs : bs = pre ++ encodePaxRecords recs) (hmax : bs.size ≤ maxPaxHeaderBytes)
    (hfuel : (encodePaxRecords recs).size < fuel) (hkeys : ∀ kv ∈ recs, ValidPaxKey kv.1)
    (hnodup : (recs.map Prod.fst).Nodup) (hseen : ∀ kv ∈ recs, kv.1 ∉ seenKeys)
    (hfold : foldPaxKeys offset recs ov = .ok finalOv) :
    parsePaxPayload.go bs offset fuel pre.size seenKeys ov = .ok finalOv := by
  induction recs generalizing fuel pre seenKeys ov with
  | nil =>
    simp only [encodePaxRecords, ByteArray.append_empty] at hbs; simp only [foldPaxKeys, Except.ok.injEq] at hfold
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encodePaxRecords] at hfuel; omega⟩
    subst hbs hfold; simp [parsePaxPayload.go]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩; simp only [foldPaxKeys, except_bind_eq_ok] at hfold
    rcases hfold with ⟨nextOv, happly, hfold_rest⟩
    have hk := hkeys (k, v) (List.Mem.head _); have ⟨h4, hsuf_le⟩ := paxRecord_size_bounds k v hk.1
    simp only [encodePaxRecords] at hbs hfuel; rw [ByteArray.size_append] at hfuel
    have hbs_sz : bs.size = pre.size + (encodePaxRecord k v).size + (encodePaxRecords rest).size := by
      rw [hbs]; simp only [ByteArray.size_append, Nat.add_assoc]
    have hext : bs.extract pre.size bs.size = encodePaxRecord k v ++ encodePaxRecords rest := by
      rw [hbs]; exact byteArray_extract_suffix pre _
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hnot_seen : !seenKeys.contains k = true := by
      cases hc : seenKeys.contains k <;> first | rfl | exact absurd (List.contains_iff_mem.mp hc) (hseen (k, v) (List.Mem.head _))
    rw [parsePaxPayload_go_step (by omega) h4 (by omega) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1
      hnot_seen hk.2.2.2.2 happly hext, ← ByteArray.size_append (a := pre)]
    refine ih (pre ++ encodePaxRecord k v) (k :: seenKeys) nextOv (by rw [hbs, ByteArray.append_assoc]) (by omega)
      (fun x hx => hkeys x (List.Mem.tail _ hx)) hnodup.2 (fun x hx hm => ?_) hfold_rest
    rcases List.mem_cons.mp hm with heq | hs
    · exact hnodup.1 (List.mem_map.mpr ⟨x, hx, heq⟩)
    · exact hseen x (List.Mem.tail _ hx) hs

private def optRec (c : Bool) (k v : String) : List (String × String) := if c then [(k, v)] else []

private theorem encodePaxRecords_optRec (c : Bool) (k v : String) :
    encodePaxRecords (optRec c k v) = if c then encodePaxRecord k v else ByteArray.empty := by
  cases c <;> simp [optRec, encodePaxRecords, ByteArray.append_empty]

private theorem map_fst_optRec_sublist (c : Bool) (k v : String) {xs : List (String × String)} {ks : List String}
    (h : (xs.map Prod.fst).Sublist ks) : ((optRec c k v ++ xs).map Prod.fst).Sublist (k :: ks) := by
  cases c with
  | false => simpa [optRec] using List.Sublist.cons k h
  | true => simpa [optRec] using List.Sublist.cons_cons k h

private theorem foldPaxKeys_optRec {offset : Nat} {c : Bool} {k v : String}
    {rest : List (String × String)} {ov nextOv : PaxOverrides}
    (h : c = true → applyPaxKey ov k v offset = .ok nextOv) :
    foldPaxKeys offset (optRec c k v ++ rest) ov = foldPaxKeys offset rest (if c then nextOv else ov) := by
  cases c with
  | false => rfl
  | true => simp only [optRec, List.singleton_append, foldPaxKeys, h rfl, ↓reduceIte]; rfl

private theorem buildPaxPayload_parse (e : TarEntry) (wp : String) (offset : Nat)
    (hnul_u : !hasNulString e.uname = true) (hnul_g : !hasNulString e.gname = true)
    (huid : e.uid < u64Limit) (hgid : e.gid < u64Limit)
    (hsz : e.data.size < u64Limit) (hmtime : e.mtime < u64Limit)
    (hpax_lim : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes) :
    parsePaxPayload (buildPaxPayload e wp) offset = .ok
      { path? := if !pathFitsUstar wp then some wp else none
      , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
      , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
      , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
      , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
      , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
      , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
      , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none } := by
  let c1 := !pathFitsUstar wp
  let c2 := e.kind == .symlink && (!isAsciiString e.linkTarget || decide (e.linkTarget.toUTF8.size > 100))
  let c3 := !isAsciiString e.uname || decide (e.uname.toUTF8.size > 32)
  let c4 := !isAsciiString e.gname || decide (e.gname.toUTF8.size > 32)
  let c5 := decide (e.data.size ≥ ustarOctal11Limit); let c6 := decide (e.mtime ≥ ustarOctal11Limit)
  let c7 := decide (e.uid ≥ ustarOctal7Limit); let c8 := decide (e.gid ≥ ustarOctal7Limit)
  let recs := optRec c1 "path" wp ++ (optRec c2 "linkpath" e.linkTarget ++
    (optRec c3 "uname" e.uname ++ (optRec c4 "gname" e.gname ++
    (optRec c5 "size" (toString e.data.size) ++ (optRec c6 "mtime" (toString e.mtime) ++
    (optRec c7 "uid" (toString e.uid) ++ (optRec c8 "gid" (toString e.gid) ++ [])))))))
  have hbs_eq : buildPaxPayload e wp = ByteArray.empty ++ encodePaxRecords recs := by
    simp only [recs, buildPaxPayload, encodePaxRecords_append, encodePaxRecords_optRec, encodePaxRecords,
      ByteArray.empty_append, ByteArray.append_empty, ByteArray.append_assoc, c1, c2, c3, c4, c5, c6, c7, c8, decide_eq_true_eq]
  have hsub : (recs.map Prod.fst).Sublist ["path", "linkpath", "uname", "gname", "size", "mtime", "uid", "gid"] :=
    map_fst_optRec_sublist _ _ _ (map_fst_optRec_sublist _ _ _ (map_fst_optRec_sublist _ _ _
      (map_fst_optRec_sublist _ _ _ (map_fst_optRec_sublist _ _ _ (map_fst_optRec_sublist _ _ _
        (map_fst_optRec_sublist _ _ _ (map_fst_optRec_sublist _ _ _ List.Sublist.slnil)))))))
  have hall_valid : (["path", "linkpath", "uname", "gname", "size", "mtime", "uid", "gid"] : List String).all validPaxKeyBool = true := by decide
  have hkeys : ∀ kv ∈ recs, ValidPaxKey kv.1 := fun kv hkv =>
    validPaxKey_of_bool (List.all_eq_true.mp hall_valid kv.1 (hsub.subset (List.mem_map_of_mem hkv)))
  let o0 : PaxOverrides := {}; let o1 : PaxOverrides := { o0 with path? := if c1 then some wp else none }
  let o2 : PaxOverrides := { o1 with linkpath? := if c2 then some e.linkTarget else none }
  let o3 : PaxOverrides := { o2 with uname? := if c3 then some e.uname else none }
  let o4 : PaxOverrides := { o3 with gname? := if c4 then some e.gname else none }
  let o5 : PaxOverrides := { o4 with size? := if c5 then some e.data.size else none }
  let o6 : PaxOverrides := { o5 with mtime? := if c6 then some e.mtime else none }
  let o7 : PaxOverrides := { o6 with uid? := if c7 then some e.uid else none }
  let o8 : PaxOverrides := { o7 with gid? := if c8 then some e.gid else none }
  have hu_f : hasNulString e.uname = false := Bool.eq_false_iff.mpr (by simpa using hnul_u)
  have hg_f : hasNulString e.gname = false := Bool.eq_false_iff.mpr (by simpa using hnul_g)
  have hfold : foldPaxKeys offset recs o0 = .ok o8 := by
    dsimp only [recs]
    rw [foldPaxKeys_optRec (nextOv := { o0 with path? := some wp }) (fun _ => rfl),
      show (if c1 then { o0 with path? := some wp } else o0) = o1 by dsimp only [o1, o0]; cases c1 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o1 with linkpath? := some e.linkTarget }) (fun _ => rfl),
      show (if c2 then { o1 with linkpath? := some e.linkTarget } else o1) = o2 by dsimp only [o2, o1, o0]; cases c2 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o2 with uname? := some e.uname }) (fun _ => by change (if hasNulString e.uname then _ else _) = _; rw [hu_f]; rfl),
      show (if c3 then { o2 with uname? := some e.uname } else o2) = o3 by dsimp only [o3, o2, o1, o0]; cases c3 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o3 with gname? := some e.gname }) (fun _ => by change (if hasNulString e.gname then _ else _) = _; rw [hg_f]; rfl),
      show (if c4 then { o3 with gname? := some e.gname } else o3) = o4 by dsimp only [o4, o3, o2, o1, o0]; cases c4 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o4 with size? := some e.data.size }) (fun _ => by change (parsePaxNat (toString e.data.size) offset "size").map _ = _; rw [parsePaxNat_toString hsz]; rfl),
      show (if c5 then { o4 with size? := some e.data.size } else o4) = o5 by dsimp only [o5, o4, o3, o2, o1, o0]; cases c5 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o5 with mtime? := some e.mtime }) (fun _ => by change (parsePaxMtime (toString e.mtime) offset).map _ = _; rw [parsePaxMtime_toString hmtime]; rfl),
      show (if c6 then { o5 with mtime? := some e.mtime } else o5) = o6 by dsimp only [o6, o5, o4, o3, o2, o1, o0]; cases c6 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o6 with uid? := some e.uid }) (fun _ => by change (parsePaxNat (toString e.uid) offset "uid").map _ = _; rw [parsePaxNat_toString huid]; rfl),
      show (if c7 then { o6 with uid? := some e.uid } else o6) = o7 by dsimp only [o7, o6, o5, o4, o3, o2, o1, o0]; cases c7 <;> rfl,
      foldPaxKeys_optRec (nextOv := { o7 with gid? := some e.gid }) (fun _ => by change (parsePaxNat (toString e.gid) offset "gid").map _ = _; rw [parsePaxNat_toString hgid]; rfl),
      show (if c8 then { o7 with gid? := some e.gid } else o7) = o8 by dsimp only [o8, o7, o6, o5, o4, o3, o2, o1, o0]; cases c8 <;> rfl]
    rfl
  have hgo := parsePaxPayload_go_records (bs := buildPaxPayload e wp) (offset := offset)
    (fuel := (buildPaxPayload e wp).size + 1) recs ByteArray.empty [] o0 o8
    hbs_eq hpax_lim (by rw [hbs_eq, ByteArray.empty_append]; omega)
    hkeys (hsub.nodup (by decide)) (fun _ _ h => by cases h) hfold
  simpa only [parsePaxPayload, ByteArray.size_empty, o8, o7, o6, o5, o4, o3, o2, o1, o0,
    c1, c2, c3, c4, c5, c6, c7, c8, decide_eq_true_eq] using hgo

private theorem mode_mask_idemp (m : UInt32) :
    (((m &&& 0o7777).toNat &&& 0o7777).toUInt32 &&& 0o7777) = (m &&& 0o7777) := by
  apply UInt32.toBitVec_inj.mp
  change (BitVec.ofNat 32 ((m.toBitVec &&& 4095#32).toNat &&& 4095)) &&& 4095#32 = m.toBitVec &&& 4095#32
  grind

private theorem ustarPathSplit_ok (wp : String) (hfit : pathFitsUstar wp = true) (hnul : !hasNulString wp = true) :
    let pair := if wp.toUTF8.size ≤ 100 then ("", wp) else match findUstarSplit wp with | some p => p | none => ("", wp)
    pair.2.toUTF8.size ≤ 100 ∧ pair.1.toUTF8.size ≤ 155 ∧ !hasNulString pair.2 = true ∧
      !hasNulString pair.1 = true ∧ (if pair.1.isEmpty then pair.2 else pair.1 ++ "/" ++ pair.2) = wp := by
  by_cases h100 : wp.toUTF8.size ≤ 100
  · simp only [h100, ↓reduceIte]; exact ⟨trivial, by decide, hnul, by decide, rfl⟩
  · simp only [h100, ↓reduceIte]; unfold pathFitsUstar at hfit; rw [Bool.and_eq_true] at hfit
    cases hf : findUstarSplit wp with
    | none => simp only [hf, Option.isSome_none, Bool.or_false, decide_eq_true_eq] at hfit; exact absurd hfit.2 h100
    | some pair =>
      rcases pair with ⟨pfx, nm⟩; have ⟨hjoin, hpfx_ne, _, hpfx_sz, hnm_sz⟩ := findUstarSplit_spec hf
      have hnul_all : (!hasNulString (pfx ++ ("/" ++ nm))) = true := by
        rw [← String.append_assoc, hjoin]; cases hc : hasNulString wp <;> simp_all
      rw [not_hasNulString_append, not_hasNulString_append, Bool.and_eq_true, Bool.and_eq_true] at hnul_all
      have hpfx_e : pfx.isEmpty = false := Bool.eq_false_iff.mpr (by simpa using hpfx_ne)
      exact ⟨hnm_sz, hpfx_sz, by simpa using hnul_all.2.2, by simpa using hnul_all.1, by simp [hpfx_e, hjoin]⟩

private theorem ascii_pax_or_fallback (s : String) (lim : Nat) :
    (if !isAsciiString s || s.toUTF8.size > lim then some s else none) = some s ∨
    ((if !isAsciiString s || s.toUTF8.size > lim then some s else none) = none ∧
      asciiFallback s lim = s ∧ s.toUTF8.size ≤ lim) := by
  by_cases h : (!isAsciiString s || s.toUTF8.size > lim) = true
  · left; simp only [h, ↓reduceIte]
  · right; simp only [Bool.not_eq_true] at h; have h' := h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at h'
    exact ⟨by simp only [h, Bool.false_eq_true, ↓reduceIte], isAsciiString_asciiFallback_eq h'.1 h'.2, h'.2⟩

private theorem unpackLoop_encodeEntryBlocks_step (opts : UnpackOptions)
    (pre post : ByteArray) (e : TarEntry) (normPath : String)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hnorm : normPath = normalizeTarPath e.kind e.path) (hpax_lim : fitsPaxLimit e = true)
    (hnot_seen : !seen.contains normPath = true) (hle_e : acc.length + 1 ≤ opts.maxEntries)
    (hle_b : totalBytes + e.data.size ≤ opts.maxTotalBytes) (hpost_sz : post.size ≥ 512) :
    ∃ entry' : TarEntry, entryEquivBool e entry' = true ∧ entry'.path = normPath ∧
      entry'.data.size = e.data.size ∧
      let bytes := pre ++ (encodeEntryBlocks e normPath ++ post)
      unpackLoop opts bytes pre.size none seen acc totalBytes =
        unpackLoop opts bytes (pre.size + (encodeEntryBlocks e normPath).size)
          none (normPath :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
  unfold validEntryBool at hve
  cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | error _ => rw [hv] at hve; cases hve
  | ok np =>
    rw [hv] at hve; dsimp only at hve
    have hnp_eq := validateEntryPath_normPath hv
    have hnp : np = normPath := hnp_eq.trans hnorm.symm; subst hnp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hve
    rcases hve with ⟨⟨hsym_ok, hdata_ok⟩, ⟨⟨⟨⟨⟨hnul_u0, hnul_g0⟩, huid⟩, hgid⟩, hmtime⟩, hsz⟩⟩
    have hnul_u : !hasNulString e.uname = true := by simpa using hnul_u0
    have hnul_g : !hasNulString e.gname = true := by simpa using hnul_g0
    have ⟨hv_wp, hnul_wp⟩ := validateEntryPath_wirePathOf hv
    have hnot_nul_e : !hasNulString e.linkTarget = true := by
      cases hk : e.kind <;> simp only [hk] at hsym_ok
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
        | error _ => rw [hvs] at hsym_ok; cases hsym_ok
        | ok _ =>
          unfold validateSymlinkTarget at hvs; dsimp only at hvs; iterate 2 (split at hvs; · cases hvs)
          rename_i hnn; cases hc : hasNulString e.linkTarget <;> first | rfl | exact absurd hc hnn
    let wp := wirePathOf e.kind np
    let typeByte : UInt8 := match e.kind with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
    have htype_beq : (typeByte == 0x78) = false := by dsimp only [typeByte]; cases e.kind <;> rfl
    let decEntry (bytes : ByteArray) (off : Nat) : TarEntry :=
      { path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
      , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
      , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
      , linkTarget := if e.kind == .symlink then e.linkTarget else "" }
    have decode_ustar_entry :
        ∀ (bytes hdrBlock : ByteArray) (off : Nat) (pendingPax : Option PaxOverrides)
          (fbName fbPrefix fbLink fbUname fbGname : String) (fbUid fbGid fbSize fbMtime : Nat),
          bytes.extract off (off + 512 + pad512 e.data.size) = hdrBlock ++ padBlock512 e.data →
          hdrBlock = buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix →
          off + 512 + pad512 e.data.size ≤ bytes.size →
          fbUid < ustarOctal7Limit → fbGid < ustarOctal7Limit →
          fbSize < ustarOctal11Limit → fbMtime < ustarOctal11Limit →
          (pendingPax.getD {}).size?.getD fbSize = e.data.size →
          (pendingPax.getD {}).uid?.getD fbUid = e.uid →
          (pendingPax.getD {}).gid?.getD fbGid = e.gid →
          (pendingPax.getD {}).mtime?.getD fbMtime = e.mtime →
          ((pendingPax.getD {}).path? = some wp ∨ ((pendingPax.getD {}).path? = none ∧
            fbName.toUTF8.size ≤ 100 ∧ fbPrefix.toUTF8.size ≤ 155 ∧ !hasNulString fbName = true ∧
            !hasNulString fbPrefix = true ∧ (if fbPrefix.isEmpty then fbName else fbPrefix ++ "/" ++ fbName) = wp)) →
          (e.kind = .symlink → (pendingPax.getD {}).linkpath? = some e.linkTarget ∨
            ((pendingPax.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100)) →
          ((pendingPax.getD {}).uname? = some e.uname ∨
            ((pendingPax.getD {}).uname? = none ∧ fbUname = e.uname ∧ e.uname.toUTF8.size ≤ 32)) →
          ((pendingPax.getD {}).gname? = some e.gname ∨
            ((pendingPax.getD {}).gname? = none ∧ fbGname = e.gname ∧ e.gname.toUTF8.size ≤ 32)) →
          entryEquivBool e (decEntry bytes off) = true ∧ (decEntry bytes off).data.size = e.data.size ∧
          unpackLoop opts bytes off pendingPax seen acc totalBytes =
            unpackLoop opts bytes (off + 512 + pad512 e.data.size) none (np :: seen) (decEntry bytes off :: acc) (totalBytes + e.data.size) := by
      intro bytes hdrBlock off pendingPax fbName fbPrefix fbLink fbUname fbGname
        fbUid fbGid fbSize fbMtime hbytes hhdr hbd_off hfuid hfgid hfsize hfmtime
        heff_size heff_uid heff_gid heff_mtime heff_path heff_link heff_uname heff_gname
      have hhdr_sz : hdrBlock.size = 512 := by rw [hhdr]; exact buildUstarHeader_size ..
      have hext_hdr : bytes.extract off (off + 512) =
          buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix := by
        have hsub : bytes.extract off (off + 512) = (bytes.extract off (off + 512 + pad512 e.data.size)).extract 0 512 := by
          rw [ByteArray.extract_extract]; congr 1; omega
        rw [hsub, hbytes, ← hhdr_sz]; exact (extract_append_exact_left hdrBlock (padBlock512 e.data)).trans hhdr
      have hnz : isZeroRange bytes off 512 = false := isZeroRange_buildUstarHeader_false (by omega) hext_hdr
      have hparse := parseUstarHeader_buildUstarHeader hfuid hfgid hfsize hfmtime (by omega) hext_hdr
      have ⟨hext_nm, hext_lk, hext_un, hext_gn, hext_pfx⟩ := buildUstarHeader_extract_strings hext_hdr
      have hkind_eq : (if typeByte == 0x30 || typeByte == 0x00 then some EntryKind.regular
          else if typeByte == 0x35 then some .directory else if typeByte == 0x32 then some .symlink else none) = some e.kind := by
        have : ∀ k : EntryKind, (let tb : UInt8 := match k with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
            if tb == 0x30 || tb == 0x00 then some EntryKind.regular
            else if tb == 0x35 then some .directory else if tb == 0x32 then some .symlink else none) = some k := fun k => by cases k <;> rfl
        exact this e.kind
      have hnonreg_f : (e.kind != .regular && e.data.size != 0) = false := by
        cases hk : e.kind <;> simp only [hk] at hdata_ok ⊢ <;>
          first | rfl | (change (true && !(e.data.size == 0)) = false; rw [hdata_ok]; rfl)
      have hseen_f : seen.contains np = false := Bool.eq_false_iff.mpr fun hc => by rw [hc] at hnot_seen; cases hnot_seen
      have hdec_un : (pendingPax.getD {}).uname? = none → decodeCStringUtf8 bytes (off + 265) (off + 297) off "uname" = .ok e.uname := by
        intro hn; rcases heff_uname with hu | ⟨_, rfl, hsz_u⟩
        · rw [hn] at hu; cases hu
        · rw [(by omega : off + 297 = (off + 265) + 32)]; exact decodeCStringUtf8_padRightBytes hnul_u hsz_u (by omega) hext_un
      have hdec_gn : (pendingPax.getD {}).gname? = none → decodeCStringUtf8 bytes (off + 297) (off + 329) off "gname" = .ok e.gname := by
        intro hn; rcases heff_gname with hg | ⟨_, rfl, hsz_g⟩
        · rw [hn] at hg; cases hg
        · rw [(by omega : off + 329 = (off + 297) + 32)]; exact decodeCStringUtf8_padRightBytes hnul_g hsz_g (by omega) hext_gn
      have hdec_lk : e.kind = .symlink → (pendingPax.getD {}).linkpath? = none →
          decodeCStringUtf8 bytes (off + 157) (off + 257) off "linkname" = .ok e.linkTarget := by
        intro hk hn; rcases heff_link hk with hl | ⟨_, rfl, hsz_l⟩
        · rw [hn] at hl; cases hl
        · rw [(by omega : off + 257 = (off + 157) + 100)]; exact decodeCStringUtf8_padRightBytes hnot_nul_e hsz_l (by omega) hext_lk
      have hdec_nm_pfx : (pendingPax.getD {}).path? = none →
          decodeCStringUtf8 bytes off (off + 100) off "name" = .ok fbName ∧
          decodeCStringUtf8 bytes (off + 345) (off + 500) off "prefix" = .ok fbPrefix ∧
          (if fbPrefix.isEmpty then fbName else fbPrefix ++ "/" ++ fbName) = wp := by
        intro hn; rcases heff_path with hp | ⟨_, hnm_sz, hpfx_sz, hnm_nul, hpfx_nul, hjoin⟩
        · rw [hn] at hp; cases hp
        · refine ⟨decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by omega) hext_nm, ?_, hjoin⟩
          rw [(by omega : off + 500 = (off + 345) + 155)]
          exact decodeCStringUtf8_padRightBytes hpfx_nul hpfx_sz (by omega) hext_pfx
      have hdec_step : decodeTarEntry opts bytes off
          { mode := (e.mode &&& 0o7777).toNat, uid := fbUid, gid := fbGid, size := fbSize, mtime := fbMtime, typeflag := typeByte }
          pendingPax seen acc.length totalBytes = .ok (decEntry bytes off, pad512 e.data.size) := by
        unfold decodeTarEntry; dsimp only [decEntry]; rw [hkind_eq]; dsimp only
        have hnot_maxe : ¬(acc.length + 1 > opts.maxEntries) := by omega
        have hnot_maxb : ¬(totalBytes + e.data.size > opts.maxTotalBytes) := by omega
        have hnot_trunc : ¬(off + 512 + pad512 e.data.size > bytes.size) := by omega
        simp only [heff_size, hnonreg_f, Bool.false_eq_true, ↓reduceIte, hnot_maxe, hnot_maxb, hnot_trunc]
        have hv_k : ∀ k, e.kind = k → validateEntryPath opts.allowAbsolute opts.allowParentTraversal k wp = .ok np :=
          fun _ hk => hk ▸ hv_wp
        rcases heff_path with hp | hp <;>
          (first | (rw [hp]; dsimp only) | (rcases hdec_nm_pfx hp.1 with ⟨h1, h2, hj⟩; rw [hp.1, h1, h2]; dsimp only; rw [hj])) <;>
          rcases heff_uname with hu | hu <;> (first | rw [hu] | rw [hu.1, hdec_un hu.1]) <;> dsimp only <;>
          rcases heff_gname with hg | hg <;> (first | rw [hg] | rw [hg.1, hdec_gn hg.1]) <;> dsimp only <;>
          (cases hk : e.kind <;> simp (config := { zeta := false }) only [hk] at hsym_ok ⊢
           · rw [hv_k _ hk]; dsimp only; simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]; rfl
           · rw [hv_k _ hk]; dsimp only; simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]; rfl
           · rcases heff_link hk with hl | hl <;> (first | rw [hl] | rw [hl.1, hdec_lk hk hl.1]) <;>
               (dsimp only; rw [hv_k _ hk]; dsimp only
                cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
                | error _ => simp [hvs] at hsym_ok
                | ok _ => simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]; rfl))
      have hdata_extract : (if e.data.size == 0 then ByteArray.empty
          else bytes.extract (off + 512) (off + 512 + e.data.size)) = e.data := by
        by_cases hz : e.data.size = 0
        · simp only [hz, beq_self_eq_true, ↓reduceIte]; exact ByteArray.ext (Array.eq_empty_of_size_eq_zero hz).symm
        · simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte]; have := le_pad512 e.data.size
          have hsub : bytes.extract (off + 512) (off + 512 + e.data.size) =
              (bytes.extract off (off + 512 + pad512 e.data.size)).extract 512 (512 + e.data.size) := by
            rw [ByteArray.extract_extract, Nat.add_assoc off 512 e.data.size, Nat.min_eq_left (by omega)]
          rw [hsub, hbytes, ← hhdr_sz, extract_append_right hdrBlock (padBlock512 e.data) e.data.size, padBlock512_extract_prefix e.data]
      have ⟨_, hnorm_id, _⟩ := validateEntryPath_idemp hv
      refine ⟨?_, by dsimp only [decEntry]; rw [hdata_extract], ?_⟩
      · unfold entryEquivBool; dsimp only [decEntry]; rw [hnorm_id, ← hnp_eq, hdata_extract, mode_mask_idemp]
        have hl : ((if e.kind == .symlink then e.linkTarget else "") ==
            (if e.kind == .symlink then (if e.kind == .symlink then e.linkTarget else "") else "")) = true := by
          cases e.kind <;> first | rfl | exact beq_self_eq_true _
        have hkeq : (e.kind == e.kind) = true := by cases e.kind <;> rfl
        simp [hl, hkeq]
      · have hnot_ge : ¬(off ≥ bytes.size) := by omega
        have hnot_gt : ¬(off + 512 > bytes.size) := by omega
        have hstep_ok : unpackStep opts bytes off pendingPax seen acc totalBytes =
            .ok (.cont (off + 512 + pad512 e.data.size) none ((decEntry bytes off).path :: seen)
              (decEntry bytes off :: acc) (totalBytes + (decEntry bytes off).data.size)) := by
          unfold unpackStep; simp only [hnot_ge, ↓reduceIte, hnz, Bool.false_eq_true, hnot_gt, hparse, htype_beq, hdec_step]
        rw [unpackLoop_step_continue opts bytes off pendingPax seen acc totalBytes _ _ _ _ _ (by omega) hstep_ok (by omega)]
        dsimp only [decEntry]; rw [hdata_extract]
    by_cases hneed : needsPax e wp
    · have hpax_lim' : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes := by
        unfold fitsPaxLimit at hpax_lim; dsimp only at hpax_lim; rw [← hnp_eq] at hpax_lim; simpa [wp, hneed] using hpax_lim
      let fbPair := if !pathFitsUstar wp then ("", asciiFallback wp 100)
        else if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with | some pair => pair | none => ("", asciiFallback wp 100)
      let fbLink := if e.kind == .symlink then asciiFallback e.linkTarget 100 else ""
      let fbUname := asciiFallback e.uname 32; let fbGname := asciiFallback e.gname 32
      let fbUid := if e.uid < ustarOctal7Limit then e.uid else 0
      let fbGid := if e.gid < ustarOctal7Limit then e.gid else 0
      let fbSize := if e.data.size < ustarOctal11Limit then e.data.size else 0
      let fbMtime := if e.mtime < ustarOctal11Limit then e.mtime else 0
      refine (fun (paxPayload paxHdr hdr : ByteArray)
          (hpaxPayload_eq : paxPayload = buildPaxPayload e wp)
          (hpaxHdr_eq : paxHdr = buildUstarHeader "././@PaxHeader" (0o644 : UInt32) 0 0 paxPayload.size 0 0x78 "" "" "" "")
          (hhdr_eq : hdr = buildUstarHeader fbPair.2 e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPair.1) => ?_)
        (buildPaxPayload e wp)
        (buildUstarHeader "././@PaxHeader" (0o644 : UInt32) 0 0 (buildPaxPayload e wp).size 0 0x78 "" "" "" "")
        (buildUstarHeader fbPair.2 e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPair.1) rfl rfl rfl
      have henc : encodeEntryBlocks e np = paxHdr ++ padBlock512 paxPayload ++ hdr ++ padBlock512 e.data := by
        have hneed' : needsPax e (wirePathOf e.kind np) = true := hneed
        unfold encodeEntryBlocks; dsimp only; simp only [hneed', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        dsimp only [wp] at hpaxPayload_eq hpaxHdr_eq hhdr_eq; rw [← hpaxPayload_eq, ← hpaxHdr_eq]
        exact congrArg (fun x => paxHdr ++ padBlock512 paxPayload ++ x ++ padBlock512 e.data) hhdr_eq.symm
      have hpaxHdr_sz : paxHdr.size = 512 := by rw [hpaxHdr_eq]; exact buildUstarHeader_size ..
      have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
      have hpadPax_sz : (padBlock512 paxPayload).size = pad512 paxPayload.size := padBlock512_size _
      have hpadData_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
      have henc_sz : (encodeEntryBlocks e np).size = (512 + pad512 paxPayload.size) + (512 + pad512 e.data.size) := by
        rw [henc]; simp only [ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, hhdr_sz, hpadData_sz]; omega
      let bytes := pre ++ (encodeEntryBlocks e np ++ post)
      have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by
        simp only [bytes, ByteArray.size_append, Nat.add_assoc]
      have hext_paxHdr : bytes.extract pre.size (pre.size + 512) =
          buildUstarHeader "././@PaxHeader" (0o644 : UInt32) 0 0 paxPayload.size 0 0x78 "" "" "" "" := by
        have hsplit : encodeEntryBlocks e np ++ post = paxHdr ++ (padBlock512 paxPayload ++ hdr ++ padBlock512 e.data ++ post) := by
          rw [henc]; simp only [ByteArray.append_assoc]
        dsimp only [bytes]; rw [hsplit, ← ByteArray.append_assoc, ← hpaxHdr_sz]
        exact (extract_append_mid pre paxHdr _).trans hpaxHdr_eq
      have hnz0 : isZeroRange bytes pre.size 512 = false := isZeroRange_buildUstarHeader_false (by omega) hext_paxHdr
      have h0_o7 : 0 < ustarOctal7Limit := by decide
      have h0_o11 : 0 < ustarOctal11Limit := by decide
      have hpax_o11 : paxPayload.size < ustarOctal11Limit := by
        have : maxPaxHeaderBytes < ustarOctal11Limit := by decide
        rw [hpaxPayload_eq]; omega
      have hparse0 := parseUstarHeader_buildUstarHeader h0_o7 h0_o7 hpax_o11 h0_o11 (by omega) hext_paxHdr
      have hext_paxPayload : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) = paxPayload := by
        have hsub : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) =
            (bytes.extract (pre.size + 512) (pre.size + 512 + (padBlock512 paxPayload).size)).extract 0 paxPayload.size := by
          have := le_pad512 paxPayload.size; rw [ByteArray.extract_extract, hpadPax_sz, Nat.add_zero, Nat.min_eq_left (by omega)]
        have hpre_hdr_sz : (pre ++ paxHdr).size = pre.size + 512 := by rw [ByteArray.size_append, hpaxHdr_sz]
        have hbytes_eq : bytes = (pre ++ paxHdr) ++ padBlock512 paxPayload ++ (hdr ++ padBlock512 e.data ++ post) := by
          dsimp only [bytes]; rw [henc]; simp only [ByteArray.append_assoc]
        rw [hsub, hbytes_eq, ← hpre_hdr_sz, extract_append_mid (pre ++ paxHdr) (padBlock512 paxPayload) _,
          padBlock512_extract_prefix paxPayload]
      have hparsePax := hpaxPayload_eq ▸ buildPaxPayload_parse e wp pre.size hnul_u hnul_g huid hgid hsz hmtime hpax_lim'
      let paxOv : PaxOverrides :=
        { path? := if !pathFitsUstar wp then some wp else none
        , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
        , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
        , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
        , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
        , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
        , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
        , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none }
      have hstep0 : unpackLoop opts bytes pre.size none seen acc totalBytes =
          unpackLoop opts bytes (pre.size + 512 + pad512 paxPayload.size) (some paxOv) seen acc totalBytes := by
        have hnot_ge0 : ¬(pre.size ≥ bytes.size) := by omega
        have hnot_gt0 : ¬(pre.size + 512 > bytes.size) := by omega
        have hnot_maxPax : ¬(paxPayload.size > maxPaxHeaderBytes) := by rw [hpaxPayload_eq]; omega
        have hnot_truncPax : ¬(pre.size + 512 + pad512 paxPayload.size > bytes.size) := by omega
        have hstep_ok0 : unpackStep opts bytes pre.size none seen acc totalBytes =
            .ok (.cont (pre.size + 512 + pad512 paxPayload.size) (some paxOv) seen acc totalBytes) := by
          unfold unpackStep
          simp only [hnot_ge0, ↓reduceIte, hnz0, Bool.false_eq_true, hnot_gt0, hparse0, beq_self_eq_true,
            Option.isSome_none, hnot_maxPax, hnot_truncPax, hext_paxPayload, hparsePax]; rfl
        exact unpackLoop_step_continue opts bytes pre.size none seen acc totalBytes _ _ _ _ _ (by omega) hstep_ok0 (by omega)
      let off1 := pre.size + 512 + pad512 paxPayload.size
      have hext1 : bytes.extract off1 (off1 + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
        have hpre1 : (pre ++ (paxHdr ++ padBlock512 paxPayload)).size = off1 := by
          simp only [off1, ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, Nat.add_assoc]
        have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by rw [ByteArray.size_append, hhdr_sz, hpadData_sz]
        have hbytes_eq : bytes = (pre ++ (paxHdr ++ padBlock512 paxPayload)) ++ (hdr ++ padBlock512 e.data) ++ post := by
          dsimp only [bytes]; rw [henc]; simp only [ByteArray.append_assoc]
        rw [hbytes_eq, Nat.add_assoc off1 512 (pad512 e.data.size), ← hpre1, ← hmid_sz]
        exact extract_append_mid (pre ++ (paxHdr ++ padBlock512 paxPayload)) (hdr ++ padBlock512 e.data) post
      have heff_path : (some paxOv |>.getD {}).path? = some wp ∨
          ((some paxOv |>.getD {}).path? = none ∧ fbPair.2.toUTF8.size ≤ 100 ∧ fbPair.1.toUTF8.size ≤ 155 ∧
            !hasNulString fbPair.2 = true ∧ !hasNulString fbPair.1 = true ∧
            (if fbPair.1.isEmpty then fbPair.2 else fbPair.1 ++ "/" ++ fbPair.2) = wp) := by
        cases hp : !pathFitsUstar wp with
        | true => left; dsimp [paxOv]; simp [hp]
        | false =>
          right; have hfit : pathFitsUstar wp = true := by simpa using hp
          have hsplit := ustarPathSplit_ok wp hfit hnul_wp; dsimp only at hsplit
          refine ⟨by dsimp [paxOv]; simp [hp], ?_⟩
          dsimp only [fbPair]; simp only [hp, Bool.false_eq_true, ↓reduceIte]
          by_cases h100 : wp.toUTF8.size ≤ 100
          · simp only [h100, ↓reduceIte] at hsplit ⊢; exact hsplit
          · unfold pathFitsUstar at hfit; rw [Bool.and_eq_true] at hfit
            cases hf : findUstarSplit wp with
            | none => simp only [hf, Option.isSome_none, Bool.or_false, decide_eq_true_eq] at hfit; exact absurd hfit.2 h100
            | some p => simp only [h100, hf, ↓reduceIte] at hsplit ⊢; exact hsplit
      have heff_link : e.kind = .symlink → (some paxOv |>.getD {}).linkpath? = some e.linkTarget ∨
          ((some paxOv |>.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100) := by
        intro hk; dsimp only [paxOv, fbLink]; rw [hk]; exact ascii_pax_or_fallback e.linkTarget 100
      have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr off1 (some paxOv)
        fbPair.2 fbPair.1 fbLink fbUname fbGname fbUid fbGid fbSize fbMtime hext1 hhdr_eq (by omega)
        (by dsimp [fbUid]; split <;> first | assumption | exact h0_o7)
        (by dsimp [fbGid]; split <;> first | assumption | exact h0_o7)
        (by dsimp [fbSize]; split <;> first | assumption | exact h0_o11)
        (by dsimp [fbMtime]; split <;> first | assumption | exact h0_o11)
        (by dsimp [paxOv, fbSize]; by_cases h : e.data.size ≥ ustarOctal11Limit <;> simp [h])
        (by dsimp [paxOv, fbUid]; by_cases h : e.uid ≥ ustarOctal7Limit <;> simp [h])
        (by dsimp [paxOv, fbGid]; by_cases h : e.gid ≥ ustarOctal7Limit <;> simp [h])
        (by dsimp [paxOv, fbMtime]; by_cases h : e.mtime ≥ ustarOctal11Limit <;> simp [h])
        heff_path heff_link (ascii_pax_or_fallback e.uname 32) (ascii_pax_or_fallback e.gname 32)
      refine ⟨_, heqv1, rfl, hsz1, ?_⟩
      dsimp only; dsimp only [bytes] at hstep0 hloop1
      rw [hstep0, hloop1, show off1 + 512 + pad512 e.data.size = pre.size + (encodeEntryBlocks e np).size by
        simp only [off1, henc_sz, Nat.add_assoc]]
    · have hneed_false : needsPax e (wirePathOf e.kind np) = false := Bool.eq_false_iff.mpr hneed
      have hnot_need := hneed_false; unfold needsPax at hnot_need
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt, Nat.not_le] at hnot_need
      rcases hnot_need with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfit_wp, _⟩, hsz_lk⟩, _⟩, hsz_un⟩, _⟩, hsz_gn⟩, huid7⟩, hgid7⟩, hsz11⟩, hmtime11⟩
      let pair := if wp.toUTF8.size ≤ 100 then ("", wp) else match findUstarSplit wp with | some p => p | none => ("", wp)
      refine (fun (hdr : ByteArray)
          (hhdr_eq : hdr = buildUstarHeader pair.2 e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pair.1) => ?_)
        (buildUstarHeader pair.2 e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pair.1) rfl
      have henc : encodeEntryBlocks e np = hdr ++ padBlock512 e.data := by
        unfold encodeEntryBlocks; dsimp only; simp only [hneed_false, Bool.not_false, ↓reduceIte]
        exact congrArg (· ++ padBlock512 e.data) hhdr_eq.symm
      have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
      have hpad_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
      have henc_sz : (encodeEntryBlocks e np).size = 512 + pad512 e.data.size := by rw [henc, ByteArray.size_append, hhdr_sz, hpad_sz]
      let bytes := pre ++ (encodeEntryBlocks e np ++ post)
      have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by simp only [bytes, ByteArray.size_append, Nat.add_assoc]
      have hext1 : bytes.extract pre.size (pre.size + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
        have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by rw [ByteArray.size_append, hhdr_sz, hpad_sz]
        dsimp only [bytes]; rw [henc, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← hmid_sz, ← ByteArray.append_assoc]
        exact extract_append_mid pre (hdr ++ padBlock512 e.data) post
      have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr pre.size none
        pair.2 pair.1 e.linkTarget e.uname e.gname e.uid e.gid e.data.size e.mtime
        hext1 hhdr_eq (by omega) huid7 hgid7 hsz11 hmtime11 rfl rfl rfl rfl
        (Or.inr ⟨rfl, ustarPathSplit_ok wp hfit_wp hnul_wp⟩)
        (fun _ => Or.inr ⟨rfl, rfl, hsz_lk⟩) (Or.inr ⟨rfl, rfl, hsz_un⟩) (Or.inr ⟨rfl, rfl, hsz_gn⟩)
      refine ⟨_, heqv1, rfl, hsz1, ?_⟩
      dsimp only [bytes]; rw [hloop1, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← henc_sz]

private def encodeEntriesList (entries : List TarEntry) : ByteArray :=
  entries.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) ByteArray.empty

private theorem foldl_encodeEntryBlocks_init (init : ByteArray) (entries : List TarEntry) :
    entries.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init =
      init ++ encodeEntriesList entries := by
  unfold encodeEntriesList; induction entries generalizing init with
  | nil => simp only [List.foldl_nil, ByteArray.append_empty]
  | cons _ _ ih => simp only [List.foldl_cons, ByteArray.empty_append]; rw [ih (init ++ _), ih (encodeEntryBlocks _ _), ByteArray.append_assoc]

private theorem isZeroRange_zeroBlock_left (pre post : ByteArray) :
    isZeroRange (pre ++ (zeroBlock ++ post)) pre.size 512 = true := by
  apply (isZeroRange_eq_true_iff _ _ _ (by decide)).mpr
  refine ⟨by simp only [ByteArray.size_append, zeroBlock_size]; omega, fun i hi _ => ?_⟩
  rw [ByteArray.getElem_append_right (by omega), ByteArray.getElem_append_left (by rw [zeroBlock_size]; omega)]
  exact zeroBlock_getElem (by rw [zeroBlock_size]; omega)

private theorem totalDataBytes_cons_rt (e : TarEntry) (rest : List TarEntry) :
    totalDataBytes (e :: rest) = e.data.size + totalDataBytes rest := by
  have hfold : ∀ (init : Nat) (es : List TarEntry),
      es.foldl (fun acc x => acc + x.data.size) init = init + totalDataBytes es := by
    intro init es; induction es generalizing init with
    | nil => simp [totalDataBytes]
    | cons x _ ih => simp only [totalDataBytes, List.foldl_cons, Nat.zero_add] at ih ⊢; rw [ih (init + x.data.size), ih x.data.size, Nat.add_assoc]
  unfold totalDataBytes; rw [List.foldl_cons, Nat.zero_add]; exact hfold e.data.size rest

private theorem unpackLoop_encodeEntriesList_aux (opts : UnpackOptions)
    (pre : ByteArray) (entries : List TarEntry) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : entries.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) = true)
    (hnodup : noDupNormalizedPathsBool.go seen entries = true) (hpax : entries.all fitsPaxLimit = true)
    (hlen : acc.length + entries.length ≤ opts.maxEntries)
    (hbytes : totalBytes + totalDataBytes entries ≤ opts.maxTotalBytes) :
    ∃ suf : List TarEntry, TarEquiv entries suf ∧
      unpackLoop opts (pre ++ (encodeEntriesList entries ++ (zeroBlock ++ zeroBlock)))
        pre.size none seen acc totalBytes = .ok (acc.reverse ++ suf) := by
  induction entries generalizing pre seen acc totalBytes with
  | nil =>
    refine ⟨[], trivial, ?_⟩
    have henc_nil : encodeEntriesList [] = ByteArray.empty := rfl
    rw [henc_nil, ByteArray.empty_append, List.append_nil]
    let bytes := pre ++ (zeroBlock ++ zeroBlock)
    have hbytes_sz : bytes.size = pre.size + 1024 := by simp only [bytes, ByteArray.size_append, zeroBlock_size]
    have hnot_ge : ¬(pre.size ≥ bytes.size) := by omega
    have hz1 : isZeroRange bytes pre.size 512 = true := isZeroRange_zeroBlock_left pre zeroBlock
    have hnot_ge512 : ¬(pre.size + 512 ≥ bytes.size) := by omega
    have hz2 : isZeroRange bytes (pre.size + 512) 512 = true := by
      have hsh : bytes = (pre ++ zeroBlock) ++ (zeroBlock ++ ByteArray.empty) := by
        dsimp only [bytes]; rw [ByteArray.append_empty, ByteArray.append_assoc]
      have hpre_sz : (pre ++ zeroBlock).size = pre.size + 512 := by rw [ByteArray.size_append, zeroBlock_size]
      rw [hsh, ← hpre_sz]; exact isZeroRange_zeroBlock_left (pre ++ zeroBlock) ByteArray.empty
    have htrail : allZeroTrailer bytes (pre.size + 1024) = true := by
      unfold allZeroTrailer; rw [(by omega : bytes.size - (pre.size + 1024) = 0)]; simp [allZeroTrailer.go]
    refine unpackLoop_step_done opts bytes pre.size none seen acc totalBytes _ (by omega) ?_
    unfold unpackStep
    simp only [hnot_ge, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hnot_ge512, hz2, Bool.not_true, htrail]
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hve hpax
    unfold noDupNormalizedPathsBool.go at hnodup; simp only [Bool.and_eq_true] at hnodup
    let np := normalizeTarPath e.kind e.path
    have hnot_seen : !seen.contains np = true := by simpa using hnodup.1
    have htot_cons := totalDataBytes_cons_rt e rest
    let tailBytes := encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)
    have htail_sz : tailBytes.size ≥ 512 := by simp only [tailBytes, ByteArray.size_append, zeroBlock_size]; omega
    have ⟨entry', heqv_e, _, _, hstep⟩ := unpackLoop_encodeEntryBlocks_step opts pre tailBytes e np seen acc totalBytes
      hve.1 rfl hpax.1 hnot_seen (by simp only [List.length_cons] at hlen; omega) (by omega) htail_sz
    have henc_cons : encodeEntriesList (e :: rest) = encodeEntryBlocks e np ++ encodeEntriesList rest := by
      unfold encodeEntriesList; simp only [List.foldl_cons, ByteArray.empty_append]
      exact foldl_encodeEntryBlocks_init (encodeEntryBlocks e np) rest
    have ⟨suf, hteq_rest, hloop_rest⟩ := ih (pre ++ encodeEntryBlocks e np) (np :: seen) (entry' :: acc)
      (totalBytes + e.data.size) hve.2 hnodup.2 hpax.2 (by simp at hlen ⊢; omega) (by omega)
    refine ⟨entry' :: suf, ⟨heqv_e, hteq_rest⟩, ?_⟩
    have hbytes_eq : pre ++ (encodeEntriesList (e :: rest) ++ (zeroBlock ++ zeroBlock)) =
        pre ++ (encodeEntryBlocks e np ++ tailBytes) := by dsimp only [tailBytes]; rw [henc_cons, ByteArray.append_assoc]
    have hbytes_sh : pre ++ (encodeEntryBlocks e np ++ tailBytes) =
        (pre ++ encodeEntryBlocks e np) ++ (encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)) := by
      dsimp only [tailBytes]; rw [ByteArray.append_assoc]
    rw [hbytes_eq, hstep, hbytes_sh, ← ByteArray.size_append (a := pre), hloop_rest]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Constructive witness that `packWith` and `unpackWith` round-trip any valid archive within limits. -/
theorem packUnpack_roundTrip_witness (entries : List TarEntry)
    (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (hvalid : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (habs : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hpar : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hlen : entries.length ≤ unpackOpts.maxEntries)
    (hbytes : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hpax : entries.all fitsPaxLimit = true) :
    ∃ bytes decoded, Impl.packWith packOpts entries = .ok bytes ∧ Impl.unpackWith unpackOpts bytes = .ok decoded ∧
      TarEquiv (if packOpts.deterministic then entries.map zeroDeterministicMeta else entries) decoded := by
  have hvalid_b : validArchiveBool packOpts.allowAbsolute packOpts.allowParentTraversal entries = true := hvalid
  have ⟨bytes, hpack_ok⟩ := (packWith_go_spec packOpts entries [] ByteArray.empty).2 hvalid_b
  have hbytes_spec := ((packWith_go_spec packOpts entries [] ByteArray.empty).1 bytes hpack_ok).2
  let effEntries := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
  have hfold_det : entries.foldl (fun b e => b ++ encodeEntryBlocks
      (if packOpts.deterministic = true then zeroDeterministicMeta e else e)
      (normalizeTarPath e.kind e.path)) ByteArray.empty = encodeEntriesList effEntries := by
    dsimp only [effEntries]; cases packOpts.deterministic with
    | false => rfl
    | true =>
      simp only [↓reduceIte]; unfold encodeEntriesList
      suffices ∀ (init : ByteArray) (es : List TarEntry),
          es.foldl (fun b e => b ++ encodeEntryBlocks (zeroDeterministicMeta e) (normalizeTarPath e.kind e.path)) init =
          (es.map zeroDeterministicMeta).foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init from
        this ByteArray.empty entries
      intro init es; induction es generalizing init with | nil => rfl | cons _ _ ih => simp only [List.map_cons, List.foldl_cons]; exact ih _
  have hbytes_eq : bytes = encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock) := by
    rw [hbytes_spec, ByteArray.empty_append, hfold_det]
  have hvalid_eff : validArchiveBool packOpts.allowAbsolute packOpts.allowParentTraversal effEntries = true := by
    dsimp only [effEntries]; split
    · exact validArchiveBool_map_zeroDeterministicMeta hvalid_b
    · exact hvalid_b
  have hvalid_unpack := validArchiveBool_mono habs hpar effEntries hvalid_eff
  have hpax_eff : effEntries.all fitsPaxLimit = true := by
    dsimp only [effEntries]; split
    · rw [List.all_map, List.all_eq_true]; rw [List.all_eq_true] at hpax
      exact fun e he => fitsPaxLimit_zeroDeterministicMeta (hpax e he)
    · exact hpax
  have hlen_eff : effEntries.length ≤ unpackOpts.maxEntries := by dsimp only [effEntries]; split <;> simp [hlen]
  have hbytes_eff : totalDataBytes effEntries ≤ unpackOpts.maxTotalBytes := by
    dsimp only [effEntries]; split
    · suffices ∀ (init : Nat) (es : List TarEntry),
          (es.map zeroDeterministicMeta).foldl (fun a e => a + e.data.size) init = es.foldl (fun a e => a + e.data.size) init by
        unfold totalDataBytes at hbytes ⊢; rw [this 0 entries]; exact hbytes
      intro init es; induction es generalizing init with | nil => rfl | cons _ _ ih => simp only [List.map_cons, List.foldl_cons]; exact ih _
    · exact hbytes
  unfold validArchiveBool at hvalid_unpack; rw [Bool.and_eq_true] at hvalid_unpack
  have ⟨decoded, hteq, hloop_ok⟩ := unpackLoop_encodeEntriesList_aux unpackOpts ByteArray.empty effEntries [] [] 0
    hvalid_unpack.1 hvalid_unpack.2 hpax_eff (by simpa using hlen_eff) (by simpa using hbytes_eff)
  have hbytes_nz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by
    have hsz_mod : (encodeEntriesList effEntries).size % 512 = 0 := by
      suffices ∀ (es : List TarEntry) (init : ByteArray), init.size % 512 = 0 →
          (es.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init).size % 512 = 0 from
        this effEntries ByteArray.empty rfl
      intro es; induction es with
      | nil => exact fun _ h => h
      | cons e _ ih =>
        intro init hinit; simp only [List.foldl_cons]; apply ih; rw [ByteArray.size_append]
        have he_mod : (encodeEntryBlocks e (normalizeTarPath e.kind e.path)).size % 512 = 0 := by
          unfold encodeEntryBlocks; dsimp only; split
          · have := padBlock512_size_mod e.data; simp only [ByteArray.size_append, buildUstarHeader_size]; omega
          · have := padBlock512_size_mod (buildPaxPayload e (wirePathOf e.kind (normalizeTarPath e.kind e.path)))
            have := padBlock512_size_mod e.data; simp only [ByteArray.size_append, buildUstarHeader_size]; omega
        omega
    have hsz_full : bytes.size = (encodeEntriesList effEntries).size + 1024 := by
      rw [hbytes_eq, ByteArray.size_append, ByteArray.size_append, zeroBlock_size]
    simp [show bytes.size ≠ 0 by omega, show bytes.size % 512 = 0 by omega]
  refine ⟨bytes, decoded, hpack_ok, ?_, hteq⟩
  unfold Impl.unpackWith; simp only [hbytes_nz, Bool.false_eq_true, ↓reduceIte]
  simpa [show ByteArray.empty ++ (encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock)) = bytes by
    rw [ByteArray.empty_append, hbytes_eq]] using hloop_ok

/-- Prove `test_tar_packUnpack_roundTrip` for `defaultApi`. -/
theorem allPass_packUnpack_roundTrip : AllPass (test_tar_packUnpack_roundTrip defaultApi) := by
  intro entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  obtain ⟨bytes, decoded, hp, hu, hteq⟩ :=
    packUnpack_roundTrip_witness entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  have hp' : defaultApi.packWith packOpts entries = .ok bytes := hp
  have hu' : defaultApi.unpackWith unpackOpts bytes = .ok decoded := hu
  dsimp only [test_tar_packUnpack_roundTrip, Bind.bind, Pure.pure, NondetTest.assert]
  rw [hp']; dsimp only; rw [hu']; exact ⟨hteq, trivial⟩

/-- Witness `CanReach (test_tar_packUnpack_roundTrip defaultApi)` using an empty archive. -/
theorem canReach_packUnpack_roundTrip : CanReach (test_tar_packUnpack_roundTrip defaultApi) := by
  have hv : ValidArchive ({} : PackOptions).allowAbsolute ({} : PackOptions).allowParentTraversal [] := rfl
  have htot : totalDataBytes [] ≤ ({} : UnpackOptions).maxTotalBytes := Nat.zero_le _
  obtain ⟨bytes, decoded, hp, hu, hteq⟩ := packUnpack_roundTrip_witness [] {} {} hv rfl rfl (Nat.zero_le _) htot rfl
  have hp' : defaultApi.packWith {} [] = .ok bytes := hp
  have hu' : defaultApi.unpackWith {} bytes = .ok decoded := hu
  unfold CanReach CanReachRun test_tar_packUnpack_roundTrip
  simp only [Bind.bind, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  refine ⟨[], {}, {}, hv, rfl, rfl, Nat.zero_le _, htot, rfl, ?_⟩
  rw [hp']; dsimp only; rw [hu']; exact ⟨hteq, trivial⟩

/-- Certify `checkRoundTripCase defaultApi` directly from `allPass_packUnpack_roundTrip`. -/
theorem checkRoundTripCase_of_valid {entries : List TarEntry} {packOpts : PackOptions} {unpackOpts : UnpackOptions}
    (hv : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (ha : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hp : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hl : entries.length ≤ unpackOpts.maxEntries)
    (hb : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hx : entries.all fitsPaxLimit = true) :
    AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries) :=
  allPass_packUnpack_roundTrip entries packOpts unpackOpts hv ha hp hl hb hx

end LeanSwe.Tar.Proofs

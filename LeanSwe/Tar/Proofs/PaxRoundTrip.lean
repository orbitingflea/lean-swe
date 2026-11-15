import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.PackValid

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem isAsciiString_char_lt {s : String} (h : isAsciiString s = true) :
    ∀ c ∈ s.toList, c.toNat < 0x80 := by
  intro c hc
  unfold isAsciiString at h
  rw [toUTF8_toList, List.all_eq_true] at h
  have hmem : ∀ b ∈ String.utf8EncodeChar c, b < 0x80 := fun b hb => by
    simpa [decide_eq_true_eq] using h b (List.mem_flatMap.mpr ⟨c, hc, hb⟩)
  unfold String.utf8EncodeChar at hmem
  dsimp only at hmem
  by_cases h1 : c.toNat ≤ 127
  · exact Nat.lt_succ_of_le h1
  · exfalso
    by_cases h2 : c.toNat ≤ 2047
    · have hb := hmem (UInt8.ofNat (c.toNat / 64 % 32) + 192) (by simp [h1, h2])
      have hto : (UInt8.ofNat (c.toNat / 64 % 32) + 192).toNat < 0x80 := hb
      simp only [UInt8.toNat_add, UInt8.toNat_ofNat'] at hto
      have hm : (192 : UInt8).toNat = 192 := rfl
      rw [hm] at hto
      omega
    · by_cases h3 : c.toNat ≤ 65535
      · have hb := hmem (UInt8.ofNat (c.toNat / 4096 % 16) + 224) (by simp [h1, h2, h3])
        have hto : (UInt8.ofNat (c.toNat / 4096 % 16) + 224).toNat < 0x80 := hb
        simp only [UInt8.toNat_add, UInt8.toNat_ofNat'] at hto
        have hm : (224 : UInt8).toNat = 224 := rfl
        rw [hm] at hto
        omega
      · have hb := hmem (UInt8.ofNat (c.toNat / 262144 % 8) + 240) (by simp [h1, h2, h3])
        have hto : (UInt8.ofNat (c.toNat / 262144 % 8) + 240).toNat < 0x80 := hb
        simp only [UInt8.toNat_add, UInt8.toNat_ofNat'] at hto
        have hm : (240 : UInt8).toNat = 240 := rfl
        rw [hm] at hto
        omega

private theorem toList_length_eq_utf8_of_isAscii {s : String} (h : isAsciiString s = true) :
    s.toList.length = s.toUTF8.size := by
  have hchars := isAsciiString_char_lt h
  have hflat : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 0x80) →
      (cs.flatMap String.utf8EncodeChar).length = cs.length := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      have hc : c.toNat ≤ 127 := Nat.le_of_lt_succ (hcs c (by simp))
      have hlen1 : (String.utf8EncodeChar c).length = 1 := by
        unfold String.utf8EncodeChar
        simp [hc]
      simp only [List.flatMap_cons, List.length_append, hlen1, List.length_cons]
      rw [ih (fun x hx => hcs x (by simp [hx]))]
      omega
  rw [← hflat s.toList hchars, ← List.size_toByteArray, ← toUTF8_eq_toByteArray]

/-- `asciiFallback` is the identity on short ASCII strings. -/
theorem isAsciiString_asciiFallback_eq {s : String} {maxChars : Nat}
    (hasc : isAsciiString s = true) (hsz : s.toUTF8.size ≤ maxChars) :
    asciiFallback s maxChars = s := by
  have hlen : s.toList.length ≤ maxChars := by
    rw [toList_length_eq_utf8_of_isAscii hasc]; exact hsz
  have hchars := isAsciiString_char_lt hasc
  unfold asciiFallback
  rw [List.take_of_length_le hlen]
  have hmap : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 0x80) →
      cs.map (fun c => if c.toNat < 0x80 then c else '?') = cs := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      have hc : c.toNat < 0x80 := hcs c (by simp)
      simp only [List.map_cons, hc, ↓reduceIte]
      rw [ih (fun x hx => hcs x (by simp [hx]))]
  rw [hmap s.toList hchars, String.ofList_toList]

private theorem parsePax_opt_step {bs rest : ByteArray} {offset pos : Nat}
    {seenKeys : List String} {ov nextOv : PaxOverrides}
    (cond : Bool) (key value : String)
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hmax : cond = true → (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_ne : !key.isEmpty = true) (hkey_nul : !hasNulString key = true)
    (hkey_nl : !key.toList.contains '\n' = true)
    (hkey_eq : (0x3d : UInt8) ∉ key.toUTF8.toList)
    (hnot_seen : cond = true → !seenKeys.contains key = true)
    (hnot_sparse : !startsWithStr key "GNU.sparse." = true)
    (happly : cond = true → applyPaxKey ov key value offset = .ok nextOv)
    (hsuf : bs.extract pos bs.size = (if cond then encodePaxRecord key value else ByteArray.empty) ++ rest) :
    parsePaxPayload.go bs offset pos seenKeys ov =
      parsePaxPayload.go bs offset
        (pos + (if cond then encodePaxRecord key value else ByteArray.empty).size)
        (if cond then key :: seenKeys else seenKeys)
        (if cond then nextOv else ov) := by
  cases cond with
  | false => simp
  | true =>
    simp only [↓reduceIte] at hsuf ⊢
    exact parsePaxPayload_go_step hkvMin (hmax rfl) hkey_ne hkey_nul hkey_nl hkey_eq
      (hnot_seen rfl) hnot_sparse (happly rfl) hsuf

private theorem extract_append_suffix (a b : ByteArray) :
    (a ++ b).extract a.size (a ++ b).size = b := by
  rw [ByteArray.size_append]
  simpa [ByteArray.append_empty] using extract_append_mid a b ByteArray.empty

private theorem encodePaxRecord_suffix_le_size (key val : String) :
    (" " ++ key ++ "=" ++ val ++ "\n").toUTF8.size ≤ (encodePaxRecord key val).size := by
  unfold encodePaxRecord
  dsimp only
  have hsuf := toUTF8_size_append
    (toString (paxRecordTotalLen (" " ++ key ++ "=" ++ val ++ "\n").toUTF8.size))
    (" " ++ key ++ "=" ++ val ++ "\n")
  omega

/-- Round-trip parsing of `buildPaxPayload`. -/
theorem buildPaxPayload_parse (e : TarEntry) (wp : String) (offset : Nat)
    (hnul_u : !hasNulString e.uname = true) (hnul_g : !hasNulString e.gname = true)
    (huid : e.uid < u64Limit) (hgid : e.gid < u64Limit)
    (hsz : e.data.size < u64Limit) (hmtime : e.mtime < u64Limit)
    (hmax : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes) :
    parsePaxPayload (buildPaxPayload e wp) offset = .ok
      { path? := if !pathFitsUstar wp then some wp else none
      , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
      , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
      , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
      , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
      , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
      , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
      , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none } := by
  unfold parsePaxPayload
  let c1 := !pathFitsUstar wp
  let c2 := e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100)
  let c3 := !isAsciiString e.uname || e.uname.toUTF8.size > 32
  let c4 := !isAsciiString e.gname || e.gname.toUTF8.size > 32
  let c5 := decide (e.data.size ≥ ustarOctal11Limit)
  let c6 := decide (e.mtime ≥ ustarOctal11Limit)
  let c7 := decide (e.uid ≥ ustarOctal7Limit)
  let c8 := decide (e.gid ≥ ustarOctal7Limit)
  let r1 := if c1 then encodePaxRecord "path" wp else ByteArray.empty
  let r2 := if c2 then encodePaxRecord "linkpath" e.linkTarget else ByteArray.empty
  let r3 := if c3 then encodePaxRecord "uname" e.uname else ByteArray.empty
  let r4 := if c4 then encodePaxRecord "gname" e.gname else ByteArray.empty
  let r5 := if c5 then encodePaxRecord "size" (toString e.data.size) else ByteArray.empty
  let r6 := if c6 then encodePaxRecord "mtime" (toString e.mtime) else ByteArray.empty
  let r7 := if c7 then encodePaxRecord "uid" (toString e.uid) else ByteArray.empty
  let r8 := if c8 then encodePaxRecord "gid" (toString e.gid) else ByteArray.empty
  let pax := r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8
  have hpax_sz : pax.size = r1.size + r2.size + r3.size + r4.size + r5.size + r6.size + r7.size + r8.size := by
    simp [pax, ByteArray.size_append]
  have hpax_eq : pax = buildPaxPayload e wp := by
    unfold buildPaxPayload
    simp only [pax, r1, r2, r3, r4, r5, r6, r7, r8, c1, c2, c3, c4, c5, c6, c7, c8, decide_eq_true_eq]
  have hpax_le : pax.size ≤ maxPaxHeaderBytes := by
    rw [hpax_eq]
    exact hmax
  have hkv4 : ∀ (k v : String), 1 ≤ k.toUTF8.size →
      4 ≤ (" " ++ k ++ "=" ++ v ++ "\n").toUTF8.size := by
    intro k v hk
    have hsp1 : " ".toUTF8.size = 1 := rfl
    have heq1 : "=".toUTF8.size = 1 := rfl
    have hnl1 : "\n".toUTF8.size = 1 := rfl
    simp only [toUTF8_size_append, hsp1, heq1, hnl1]
    omega
  have hs1 : pax.extract 0 pax.size = r1 ++ (r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8) := by
    have h0 : (ByteArray.empty ++ pax).extract ByteArray.empty.size (ByteArray.empty ++ pax).size = pax :=
      extract_append_suffix ByteArray.empty pax
    simp only [ByteArray.empty_append, ByteArray.size_empty] at h0
    rw [h0]
    simp only [pax, ByteArray.append_assoc]
  have hp1 := parsePax_opt_step (offset := offset) c1 "path" wp (seenKeys := []) (ov := {})
    (nextOv := { ({} : PaxOverrides) with path? := some wp })
    (hkv4 "path" wp (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "path" wp
      have h2 : (encodePaxRecord "path" wp).size = r1.size := by simp [r1, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => by decide) (by decide) (fun _ => rfl) hs1
  have hs_ext : ∀ (a b c : ByteArray), pax = a ++ b ++ c →
      pax.extract a.size pax.size = b ++ c := by
    intro a b c h
    rw [h, ByteArray.append_assoc]
    exact extract_append_suffix a (b ++ c)
  have hs2 : pax.extract r1.size pax.size = r2 ++ (r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8) :=
    hs_ext r1 r2 _ (by simp only [pax, ByteArray.append_assoc])
  let sk1 := if c1 then ["path"] else []
  have hnot_if_cons : ∀ {k key : String} {c : Bool} {xs : List String},
      k ≠ key → !xs.contains key = true → !(if c then k :: xs else xs).contains key = true := by
    intro k key c xs hne hx
    cases c with
    | false => exact hx
    | true =>
      simp only [↓reduceIte, Bool.not_eq_true', decide_eq_false_iff_not, List.contains_iff_mem,
        List.mem_cons] at hx ⊢
      rintro (rfl | hm')
      · exact hne rfl
      · exact hx hm'
  have hnul_u' : hasNulString e.uname = false := by cases hc : hasNulString e.uname <;> simp_all
  have hnul_g' : hasNulString e.gname = false := by cases hc : hasNulString e.gname <;> simp_all
  have hsk0 : !([] : List String).contains "path" = true := rfl
  have hsk1_lp : !sk1.contains "linkpath" = true :=
    hnot_if_cons (by decide) (by decide)
  have hp2 := parsePax_opt_step (offset := offset) c2 "linkpath" e.linkTarget
    (seenKeys := sk1)
    (ov := if c1 then ({ path? := some wp } : PaxOverrides) else {})
    (nextOv := { (if c1 then ({ path? := some wp } : PaxOverrides) else {}) with linkpath? := some e.linkTarget })
    (hkv4 "linkpath" e.linkTarget (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "linkpath" e.linkTarget
      have h2 : (encodePaxRecord "linkpath" e.linkTarget).size = r2.size := by simp [r2, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk1_lp) (by decide)
    (fun _ => by rfl) hs2
  have hs3 : pax.extract (r1.size + r2.size) pax.size = r3 ++ (r4 ++ r5 ++ r6 ++ r7 ++ r8) := by
    rw [← ByteArray.size_append]
    exact hs_ext (r1 ++ r2) r3 _ (by simp only [pax, ByteArray.append_assoc])
  let sk2 := if c2 then "linkpath" :: sk1 else sk1
  have hsk2_un : !sk2.contains "uname" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide))
  let ov2 := if c2 then { (if c1 then ({ path? := some wp } : PaxOverrides) else {}) with linkpath? := some e.linkTarget }
    else (if c1 then ({ path? := some wp } : PaxOverrides) else {})
  have hp3 := parsePax_opt_step (offset := offset) c3 "uname" e.uname (seenKeys := sk2) (ov := ov2)
    (nextOv := { ov2 with uname? := some e.uname })
    (hkv4 "uname" e.uname (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "uname" e.uname
      have h2 : (encodePaxRecord "uname" e.uname).size = r3.size := by simp [r3, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk2_un) (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("uname" == "path") = false := rfl
      have hb2 : ("uname" == "linkpath") = false := rfl
      have hb3 : ("uname" == "uname") = true := rfl
      simp only [hb1, hb2, hb3, hnul_u', Bool.false_eq_true, ↓reduceIte]) hs3
  have hs4 : pax.extract (r1.size + r2.size + r3.size) pax.size = r4 ++ (r5 ++ r6 ++ r7 ++ r8) := by
    rw [← ByteArray.size_append, ← ByteArray.size_append]
    exact hs_ext (r1 ++ r2 ++ r3) r4 _ (by simp only [pax, ByteArray.append_assoc])
  let sk3 := if c3 then "uname" :: sk2 else sk2
  have hsk3_gn : !sk3.contains "gname" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide)))
  let ov3 := if c3 then { ov2 with uname? := some e.uname } else ov2
  have hp4 := parsePax_opt_step (offset := offset) c4 "gname" e.gname (seenKeys := sk3) (ov := ov3)
    (nextOv := { ov3 with gname? := some e.gname })
    (hkv4 "gname" e.gname (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "gname" e.gname
      have h2 : (encodePaxRecord "gname" e.gname).size = r4.size := by simp [r4, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk3_gn) (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("gname" == "path") = false := rfl
      have hb2 : ("gname" == "linkpath") = false := rfl
      have hb3 : ("gname" == "uname") = false := rfl
      have hb4 : ("gname" == "gname") = true := rfl
      simp only [hb1, hb2, hb3, hb4, hnul_g', Bool.false_eq_true, ↓reduceIte]) hs4
  have hs5 : pax.extract (r1.size + r2.size + r3.size + r4.size) pax.size = r5 ++ (r6 ++ r7 ++ r8) := by
    rw [← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append]
    exact hs_ext (r1 ++ r2 ++ r3 ++ r4) r5 _ (by simp only [pax, ByteArray.append_assoc])
  let sk4 := if c4 then "gname" :: sk3 else sk3
  have hsk4_sz : !sk4.contains "size" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide))))
  let ov4 := if c4 then { ov3 with gname? := some e.gname } else ov3
  have hp5 := parsePax_opt_step (offset := offset) c5 "size" (toString e.data.size) (seenKeys := sk4) (ov := ov4)
    (nextOv := { ov4 with size? := some e.data.size })
    (hkv4 "size" (toString e.data.size) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "size" (toString e.data.size)
      have h2 : (encodePaxRecord "size" (toString e.data.size)).size = r5.size := by simp [r5, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk4_sz) (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("size" == "path") = false := rfl
      have hb2 : ("size" == "linkpath") = false := rfl
      have hb3 : ("size" == "uname") = false := rfl
      have hb4 : ("size" == "gname") = false := rfl
      have hb5 : ("size" == "size") = true := rfl
      simp only [hb1, hb2, hb3, hb4, hb5, Bool.false_eq_true, ↓reduceIte,
        parsePaxNat_toString hsz, Except.map]) hs5
  have hs6 : pax.extract (r1.size + r2.size + r3.size + r4.size + r5.size) pax.size = r6 ++ (r7 ++ r8) := by
    rw [← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append]
    exact hs_ext (r1 ++ r2 ++ r3 ++ r4 ++ r5) r6 _ (by simp only [pax, ByteArray.append_assoc])
  let sk5 := if c5 then "size" :: sk4 else sk4
  have hsk5_mt : !sk5.contains "mtime" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide)
      (hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide)))))
  let ov5 := if c5 then { ov4 with size? := some e.data.size } else ov4
  have hp6 := parsePax_opt_step (offset := offset) c6 "mtime" (toString e.mtime) (seenKeys := sk5) (ov := ov5)
    (nextOv := { ov5 with mtime? := some e.mtime })
    (hkv4 "mtime" (toString e.mtime) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "mtime" (toString e.mtime)
      have h2 : (encodePaxRecord "mtime" (toString e.mtime)).size = r6.size := by simp [r6, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk5_mt) (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("mtime" == "path") = false := rfl
      have hb2 : ("mtime" == "linkpath") = false := rfl
      have hb3 : ("mtime" == "uname") = false := rfl
      have hb4 : ("mtime" == "gname") = false := rfl
      have hb5 : ("mtime" == "size") = false := rfl
      have hb6 : ("mtime" == "uid") = false := rfl
      have hb7 : ("mtime" == "gid") = false := rfl
      have hb8 : ("mtime" == "mtime") = true := rfl
      simp only [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, Bool.false_eq_true, ↓reduceIte,
        parsePaxMtime_toString hmtime, Except.map]) hs6
  have hs7 : pax.extract (r1.size + r2.size + r3.size + r4.size + r5.size + r6.size) pax.size = r7 ++ r8 := by
    rw [← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append,
      ← ByteArray.size_append, ← ByteArray.size_append]
    exact hs_ext (r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6) r7 r8 (by simp only [pax, ByteArray.append_assoc])
  let sk6 := if c6 then "mtime" :: sk5 else sk5
  have hsk6_uid : !sk6.contains "uid" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide)
      (hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide))))))
  let ov6 := if c6 then { ov5 with mtime? := some e.mtime } else ov5
  have hp7 := parsePax_opt_step (offset := offset) c7 "uid" (toString e.uid) (seenKeys := sk6) (ov := ov6)
    (nextOv := { ov6 with uid? := some e.uid })
    (hkv4 "uid" (toString e.uid) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "uid" (toString e.uid)
      have h2 : (encodePaxRecord "uid" (toString e.uid)).size = r7.size := by simp [r7, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk6_uid) (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("uid" == "path") = false := rfl
      have hb2 : ("uid" == "linkpath") = false := rfl
      have hb3 : ("uid" == "uname") = false := rfl
      have hb4 : ("uid" == "gname") = false := rfl
      have hb5 : ("uid" == "size") = false := rfl
      have hb6 : ("uid" == "uid") = true := rfl
      simp only [hb1, hb2, hb3, hb4, hb5, hb6, Bool.false_eq_true, ↓reduceIte,
        parsePaxNat_toString huid, Except.map]) hs7
  have hs8 : pax.extract (r1.size + r2.size + r3.size + r4.size + r5.size + r6.size + r7.size) pax.size =
      r8 ++ ByteArray.empty := by
    rw [← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append,
      ← ByteArray.size_append, ← ByteArray.size_append, ← ByteArray.size_append]
    exact hs_ext (r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7) r8 ByteArray.empty
      (by rw [ByteArray.append_empty])
  let sk7 := if c7 then "uid" :: sk6 else sk6
  have hsk7_gid : !sk7.contains "gid" = true :=
    hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide)
      (hnot_if_cons (by decide) (hnot_if_cons (by decide) (hnot_if_cons (by decide) (by decide)))))))
  let ov7 := if c7 then { ov6 with uid? := some e.uid } else ov6
  have hp8 := parsePax_opt_step (offset := offset) c8 "gid" (toString e.gid) (seenKeys := sk7) (ov := ov7)
    (nextOv := { ov7 with gid? := some e.gid })
    (hkv4 "gid" (toString e.gid) (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide))
    (fun hc => by
      have h1 := encodePaxRecord_suffix_le_size "gid" (toString e.gid)
      have h2 : (encodePaxRecord "gid" (toString e.gid)).size = r8.size := by simp [r8, hc]
      omega)
    (by decide) (by decide) (by decide) (by rw [toUTF8_toList]; decide)
    (fun _ => hsk7_gid)
    (by decide)
    (fun _ => by
      unfold applyPaxKey
      have hb1 : ("gid" == "path") = false := rfl
      have hb2 : ("gid" == "linkpath") = false := rfl
      have hb3 : ("gid" == "uname") = false := rfl
      have hb4 : ("gid" == "gname") = false := rfl
      have hb5 : ("gid" == "size") = false := rfl
      have hb6 : ("gid" == "uid") = false := rfl
      have hb7 : ("gid" == "gid") = true := rfl
      simp only [hb1, hb2, hb3, hb4, hb5, hb6, hb7, Bool.false_eq_true, ↓reduceIte,
        parsePaxNat_toString hgid, Except.map]) hs8
  let sk8 := if c8 then "gid" :: sk7 else sk7
  let ov8 := if c8 then { ov7 with gid? := some e.gid } else ov7
  have hdone : parsePaxPayload.go pax offset pax.size sk8 ov8 = .ok ov8 := by
    rw [parsePaxPayload.go.eq_1]
    simp
  have heq_pos : r1.size + r2.size + r3.size + r4.size + r5.size + r6.size + r7.size + r8.size = pax.size := by
    omega
  dsimp only [r1, r2, r3, r4, r5, r6, r7, r8] at hp2 hp3 hp4 hp5 hp6 hp7 hp8 heq_pos
  rw [← hpax_eq, hp1]
  simp only [Nat.zero_add]
  rw [hp2, hp3, hp4, hp5, hp6, hp7, hp8, heq_pos, hdone]
  congr 1
  have h_ite_same : ∀ {α : Type} (c : Bool) (x : α), (if c = true then x else x) = x :=
    fun c x => by cases c <;> rfl
  have hc1' : ov8.path? = if c1 then some wp else none := by
    rw [show ov8.path? = ov7.path? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    rw [show ov7.path? = ov6.path? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    rw [show ov6.path? = ov5.path? from by dsimp only [ov6]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    rw [show ov5.path? = ov4.path? from by dsimp only [ov5]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    rw [show ov4.path? = ov3.path? from by dsimp only [ov4]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    rw [show ov3.path? = ov2.path? from by dsimp only [ov3]; rw [apply_ite PaxOverrides.path?, h_ite_same]]
    dsimp only [ov2]; rw [apply_ite PaxOverrides.path?, h_ite_same]; cases c1 <;> rfl
  have hc2' : ov8.linkpath? = if c2 then some e.linkTarget else none := by
    rw [show ov8.linkpath? = ov7.linkpath? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    rw [show ov7.linkpath? = ov6.linkpath? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    rw [show ov6.linkpath? = ov5.linkpath? from by dsimp only [ov6]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    rw [show ov5.linkpath? = ov4.linkpath? from by dsimp only [ov5]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    rw [show ov4.linkpath? = ov3.linkpath? from by dsimp only [ov4]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    rw [show ov3.linkpath? = ov2.linkpath? from by dsimp only [ov3]; rw [apply_ite PaxOverrides.linkpath?, h_ite_same]]
    dsimp only [ov2]; rw [apply_ite PaxOverrides.linkpath?]
    have h1 : (if c1 = true then ({ path? := some wp } : PaxOverrides) else {}).linkpath? = none := by
      cases c1 <;> rfl
    rw [h1]
  have hc3' : ov8.uname? = if c3 then some e.uname else none := by
    rw [show ov8.uname? = ov7.uname? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.uname?, h_ite_same]]
    rw [show ov7.uname? = ov6.uname? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.uname?, h_ite_same]]
    rw [show ov6.uname? = ov5.uname? from by dsimp only [ov6]; rw [apply_ite PaxOverrides.uname?, h_ite_same]]
    rw [show ov5.uname? = ov4.uname? from by dsimp only [ov5]; rw [apply_ite PaxOverrides.uname?, h_ite_same]]
    rw [show ov4.uname? = ov3.uname? from by dsimp only [ov4]; rw [apply_ite PaxOverrides.uname?, h_ite_same]]
    have h2 : ov2.uname? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.uname?, h_ite_same]; cases c1 <;> rfl
    dsimp only [ov3]; rw [apply_ite PaxOverrides.uname?, h2]
  have hc4' : ov8.gname? = if c4 then some e.gname else none := by
    rw [show ov8.gname? = ov7.gname? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.gname?, h_ite_same]]
    rw [show ov7.gname? = ov6.gname? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.gname?, h_ite_same]]
    rw [show ov6.gname? = ov5.gname? from by dsimp only [ov6]; rw [apply_ite PaxOverrides.gname?, h_ite_same]]
    rw [show ov5.gname? = ov4.gname? from by dsimp only [ov5]; rw [apply_ite PaxOverrides.gname?, h_ite_same]]
    have h2 : ov2.gname? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.gname?, h_ite_same]; cases c1 <;> rfl
    have h3 : ov3.gname? = none := by
      dsimp only [ov3]; rw [apply_ite PaxOverrides.gname?, h_ite_same, h2]
    dsimp only [ov4]; rw [apply_ite PaxOverrides.gname?, h3]
  have hc5' : ov8.size? = if e.data.size ≥ ustarOctal11Limit then some e.data.size else none := by
    rw [show ov8.size? = ov7.size? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.size?, h_ite_same]]
    rw [show ov7.size? = ov6.size? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.size?, h_ite_same]]
    rw [show ov6.size? = ov5.size? from by dsimp only [ov6]; rw [apply_ite PaxOverrides.size?, h_ite_same]]
    have h2 : ov2.size? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.size?, h_ite_same]; cases c1 <;> rfl
    have h3 : ov3.size? = none := by
      dsimp only [ov3]; rw [apply_ite PaxOverrides.size?, h_ite_same, h2]
    have h4 : ov4.size? = none := by
      dsimp only [ov4]; rw [apply_ite PaxOverrides.size?, h_ite_same, h3]
    dsimp only [ov5]; rw [apply_ite PaxOverrides.size?, h4]
    by_cases h : e.data.size ≥ ustarOctal11Limit <;> simp [c5, h]
  have hc6' : ov8.mtime? = if e.mtime ≥ ustarOctal11Limit then some e.mtime else none := by
    rw [show ov8.mtime? = ov7.mtime? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.mtime?, h_ite_same]]
    rw [show ov7.mtime? = ov6.mtime? from by dsimp only [ov7]; rw [apply_ite PaxOverrides.mtime?, h_ite_same]]
    have h2 : ov2.mtime? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.mtime?, h_ite_same]; cases c1 <;> rfl
    have h3 : ov3.mtime? = none := by
      dsimp only [ov3]; rw [apply_ite PaxOverrides.mtime?, h_ite_same, h2]
    have h4 : ov4.mtime? = none := by
      dsimp only [ov4]; rw [apply_ite PaxOverrides.mtime?, h_ite_same, h3]
    have h5 : ov5.mtime? = none := by
      dsimp only [ov5]; rw [apply_ite PaxOverrides.mtime?, h_ite_same, h4]
    dsimp only [ov6]; rw [apply_ite PaxOverrides.mtime?, h5]
    by_cases h : e.mtime ≥ ustarOctal11Limit <;> simp [c6, h]
  have hc7' : ov8.uid? = if e.uid ≥ ustarOctal7Limit then some e.uid else none := by
    rw [show ov8.uid? = ov7.uid? from by dsimp only [ov8]; rw [apply_ite PaxOverrides.uid?, h_ite_same]]
    have h2 : ov2.uid? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.uid?, h_ite_same]; cases c1 <;> rfl
    have h3 : ov3.uid? = none := by
      dsimp only [ov3]; rw [apply_ite PaxOverrides.uid?, h_ite_same, h2]
    have h4 : ov4.uid? = none := by
      dsimp only [ov4]; rw [apply_ite PaxOverrides.uid?, h_ite_same, h3]
    have h5 : ov5.uid? = none := by
      dsimp only [ov5]; rw [apply_ite PaxOverrides.uid?, h_ite_same, h4]
    have h6 : ov6.uid? = none := by
      dsimp only [ov6]; rw [apply_ite PaxOverrides.uid?, h_ite_same, h5]
    dsimp only [ov7]; rw [apply_ite PaxOverrides.uid?, h6]
    by_cases h : e.uid ≥ ustarOctal7Limit <;> simp [c7, h]
  have hc8' : ov8.gid? = if e.gid ≥ ustarOctal7Limit then some e.gid else none := by
    have h2 : ov2.gid? = none := by
      dsimp only [ov2]; rw [apply_ite PaxOverrides.gid?, h_ite_same]; cases c1 <;> rfl
    have h3 : ov3.gid? = none := by
      dsimp only [ov3]; rw [apply_ite PaxOverrides.gid?, h_ite_same, h2]
    have h4 : ov4.gid? = none := by
      dsimp only [ov4]; rw [apply_ite PaxOverrides.gid?, h_ite_same, h3]
    have h5 : ov5.gid? = none := by
      dsimp only [ov5]; rw [apply_ite PaxOverrides.gid?, h_ite_same, h4]
    have h6 : ov6.gid? = none := by
      dsimp only [ov6]; rw [apply_ite PaxOverrides.gid?, h_ite_same, h5]
    have h7 : ov7.gid? = none := by
      dsimp only [ov7]; rw [apply_ite PaxOverrides.gid?, h_ite_same, h6]
    dsimp only [ov8]; rw [apply_ite PaxOverrides.gid?, h7]
    by_cases h : e.gid ≥ ustarOctal7Limit <;> simp [c8, h]
  have h_eta : ∀ a b : PaxOverrides,
      a.path? = b.path? → a.linkpath? = b.linkpath? → a.uname? = b.uname? → a.gname? = b.gname? →
      a.size? = b.size? → a.mtime? = b.mtime? → a.uid? = b.uid? → a.gid? = b.gid? → a = b := by
    rintro ⟨⟩ ⟨⟩ rfl rfl rfl rfl rfl rfl rfl rfl
    rfl
  exact h_eta ov8 _ hc1' hc2' hc3' hc4' hc5' hc6' hc7' hc8'


end LeanSwe.Tar.Proofs

import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid

/-!
# Round-Trip Proof for `LeanSwe.Tar`

Proves universal encode/decode round-trip correctness (`allPass_packUnpack_roundTrip`,
`canReach_packUnpack_roundTrip`, and `checkRoundTripCase_of_valid`), merging PAX payload
round-tripping, single-entry USTAR/PAX block stepping, and archive-level induction.
-/

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem utf8EncodeChar_all_lt128 {c : Char}
    (h : (String.utf8EncodeChar c).all (fun b => decide (b < 128)) = true) :
    c.toNat < 128 := by
  by_cases hc : c.val.toNat ≤ 127
  · exact Nat.lt_succ_of_le hc
  · exfalso
    dsimp only [String.utf8EncodeChar] at h
    simp only [hc, ↓reduceIte] at h
    by_cases hc2 : c.val.toNat ≤ 2047
    · simp only [hc2, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      have hmod : ((UInt8.ofNat (c.val.toNat / 64 % 32 + 192)).toNat) = (c.val.toNat / 64 % 32 + 192) % 256 := rfl
      have h0 : (UInt8.ofNat (c.val.toNat / 64 % 32 + 192)).toNat < 128 := h.1
      omega
    · simp only [hc2, ↓reduceIte] at h
      by_cases hc3 : c.val.toNat ≤ 65535
      · simp only [hc3, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
        have hmod : ((UInt8.ofNat (c.val.toNat / 4096 % 16 + 224)).toNat) = (c.val.toNat / 4096 % 16 + 224) % 256 := rfl
        have h0 : (UInt8.ofNat (c.val.toNat / 4096 % 16 + 224)).toNat < 128 := h.1
        omega
      · simp only [hc3, ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
        have hmod : ((UInt8.ofNat (c.val.toNat / 262144 % 8 + 240)).toNat) = (c.val.toNat / 262144 % 8 + 240) % 256 := rfl
        have h0 : (UInt8.ofNat (c.val.toNat / 262144 % 8 + 240)).toNat < 128 := h.1
        have hbd := c.valid
        omega

private theorem utf8EncodeChar_length_pos (c : Char) : 1 ≤ (String.utf8EncodeChar c).length := by
  unfold String.utf8EncodeChar
  dsimp only
  by_cases h1 : c.val.toNat ≤ 127
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, ↓reduceIte]
    by_cases h2 : c.val.toNat ≤ 2047
    · simp only [h2, ↓reduceIte]; simp
    · simp only [h2, ↓reduceIte]
      by_cases h3 : c.val.toNat ≤ 65535
      · simp only [h3, ↓reduceIte]; simp
      · simp only [h3, ↓reduceIte]; simp

private theorem flatMap_utf8Encode_ascii : ∀ (cs : List Char),
    (cs.flatMap String.utf8EncodeChar).all (fun b => decide (b < 128)) = true →
    (∀ c ∈ cs, c.toNat < 128) ∧ cs.length ≤ (cs.flatMap String.utf8EncodeChar).length
  | [], _ => ⟨fun _ hc => False.elim (List.not_mem_nil hc), Nat.le_refl 0⟩
  | c :: cs, h => by
    rw [List.flatMap_cons, List.all_append, Bool.and_eq_true] at h
    have hc := utf8EncodeChar_all_lt128 h.1
    have ih := flatMap_utf8Encode_ascii cs h.2
    have hpos := utf8EncodeChar_length_pos c
    refine ⟨?_, ?_⟩
    · intro x hx
      cases hx with
      | head => exact hc
      | tail _ hx => exact ih.1 x hx
    · rw [List.flatMap_cons, List.length_append]
      simp only [List.length_cons]
      omega

private theorem list_map_ascii (cs : List Char)
    (hchars : ∀ c ∈ cs, c.toNat < 128) :
    List.map (fun c => if c.toNat < 128 then c else '?') cs = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hchars c (List.Mem.head cs)
    simp only [List.map_cons, hc, ↓reduceIte]
    exact congrArg (c :: ·) (ih (fun x hx => hchars x (List.Mem.tail c hx)))

private theorem isAsciiString_asciiFallback_eq {s : String} {maxChars : Nat}
    (hasc : isAsciiString s = true) (hsz : s.toUTF8.size ≤ maxChars) :
    asciiFallback s maxChars = s := by
  unfold isAsciiString at hasc
  rw [toUTF8_toList] at hasc
  have ⟨hchars, hlen_le⟩ := flatMap_utf8Encode_ascii s.toList hasc
  have hs_sz : s.toUTF8.size = (s.toList.flatMap String.utf8EncodeChar).length := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]
  have hlen : s.toList.length ≤ maxChars := by omega
  unfold asciiFallback
  rw [List.take_of_length_le hlen, list_map_ascii s.toList hchars, String.ofList_toList]

private theorem parsePaxPayload_go_done (bs : ByteArray) (offset fuel : Nat)
    (seenKeys : List String) (ov : PaxOverrides) (hf : 0 < fuel) :
    parsePaxPayload.go bs offset fuel bs.size seenKeys ov = .ok ov := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp [parsePaxPayload.go]

private theorem paxRecord_size_bounds (key value : String) (hk : !key.isEmpty = true) :
    4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ∧
    (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ (encodePaxRecord key value).size := by
  let suffix := " " ++ key ++ "=" ++ value ++ "\n"
  have hne : key ≠ "" := by
    intro heq; subst heq; simp at hk
  have hk_pos : 1 ≤ key.toUTF8.size := by
    cases hcl : key.toList with
    | nil =>
      exfalso
      have : key = "" := by rw [← String.ofList_toList (s := key), hcl]
      exact hne this
    | cons c cs =>
      have hlen : key.toUTF8.size = (key.toList.flatMap String.utf8EncodeChar).length := by
        rw [toUTF8_eq_toByteArray, List.size_toByteArray]
      have hc_pos := utf8EncodeChar_length_pos c
      rw [hlen, hcl, List.flatMap_cons, List.length_append]
      omega
  have hsuf : suffix.toUTF8.size =
      (" ".toUTF8.size + key.toUTF8.size) + "=".toUTF8.size + value.toUTF8.size + "\n".toUTF8.size := by
    simp only [suffix, toUTF8_append, ByteArray.size_append]
  have hsp : " ".toUTF8.size = 1 := rfl
  have heq : "=".toUTF8.size = 1 := rfl
  have hnl : "\n".toUTF8.size = 1 := rfl
  have h4 : 4 ≤ suffix.toUTF8.size := by omega
  have hrec : (encodePaxRecord key value).size =
      (toString (paxRecordTotalLen suffix.toUTF8.size)).toUTF8.size + suffix.toUTF8.size := by
    simp only [encodePaxRecord, suffix, toUTF8_append, ByteArray.size_append]
  have hsuf_le : suffix.toUTF8.size ≤ (encodePaxRecord key value).size := by
    rw [hrec]; exact Nat.le_add_left _ _
  exact ⟨h4, hsuf_le⟩

private theorem extract_self_all (b : ByteArray) : b.extract 0 b.size = b := by
  have h := extract_append_exact_left b ByteArray.empty
  simp only [ByteArray.append_empty] at h
  exact h

private theorem parsePax_opt_step
    {bs pre post : ByteArray} {offset fuel : Nat} {seenKeys : List String}
    {ov nextOv : PaxOverrides} {cond : Bool} {key value : String}
    (hbs : bs = pre ++ ((if cond then encodePaxRecord key value else ByteArray.empty) ++ post))
    (hbs_max : bs.size ≤ maxPaxHeaderBytes)
    (hfuel : bs.size - pre.size < fuel)
    (hkey : !key.isEmpty = true ∧ !hasNulString key = true ∧ !(key.toList.contains '\n') = true ∧
      (61 : UInt8) ∉ key.toUTF8.toList ∧ !startsWithStr key "GNU.sparse." = true)
    (hseen : !seenKeys.contains key = true)
    (happly : cond = true → applyPaxKey ov key value offset = .ok nextOv) :
    let stepRec := if cond then encodePaxRecord key value else ByteArray.empty
    let stepOv := if cond then nextOv else ov
    let stepSeen := if cond then key :: seenKeys else seenKeys
    let stepFuel := if cond then fuel - 1 else fuel
    bs.size - (pre.size + stepRec.size) < stepFuel ∧
    parsePaxPayload.go bs offset fuel pre.size seenKeys ov =
      parsePaxPayload.go bs offset stepFuel (pre.size + stepRec.size) stepSeen stepOv := by
  dsimp only
  cases cond with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, ByteArray.size_empty, Nat.add_zero]
    exact ⟨hfuel, trivial⟩
  | true =>
    simp only [↓reduceIte]
    simp only [↓reduceIte] at hbs
    have ⟨h4, hsuf_le⟩ := paxRecord_size_bounds key value hkey.1
    have hbs_sz : bs.size = pre.size + (encodePaxRecord key value).size + post.size := by
      rw [hbs]; simp only [ByteArray.size_append, Nat.add_assoc]
    have hrec_max : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by omega
    have hext : bs.extract pre.size bs.size = encodePaxRecord key value ++ post := by
      rw [hbs, ByteArray.size_append, extract_append_right, extract_self_all]
    have hfuel' : bs.size - (pre.size + (encodePaxRecord key value).size) < fuel - 1 := by omega
    refine ⟨hfuel', ?_⟩
    exact parsePaxPayload_go_step hfuel h4 hrec_max
      (by simpa using hkey.1) (by simpa using hkey.2.1) (by simpa using hkey.2.2.1)
      hkey.2.2.2.1 (by simpa using hseen) (by simpa using hkey.2.2.2.2) (happly rfl) hext

private theorem not_contains_optCons (c : Bool) (x y : String) (xs : List String)
    (hne : x ≠ y) (hxs : !xs.contains x = true) :
    !(if c then y :: xs else xs).contains x = true := by
  cases c with
  | false => exact hxs
  | true =>
    change !((y :: xs).elem x) = true
    rw [List.elem_cons, beq_false_of_ne hne]
    exact hxs

private theorem paxKey_valid_of_dec {key : String}
    (h : (!key.isEmpty = true ∧ !hasNulString key = true ∧ !(key.toList.contains '\n') = true ∧
      !((key.toList.flatMap String.utf8EncodeChar).contains (61 : UInt8)) = true ∧
      !startsWithStr key "GNU.sparse." = true)) :
    !key.isEmpty = true ∧ !hasNulString key = true ∧ !(key.toList.contains '\n') = true ∧
      (61 : UInt8) ∉ key.toUTF8.toList ∧ !startsWithStr key "GNU.sparse." = true := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  rw [toUTF8_toList]
  intro hm
  have h1 := List.contains_iff_mem.mpr hm
  have h2 := h.2.2.2.1
  rw [h1] at h2
  contradiction

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
  let bs := buildPaxPayload e wp
  have hbs_def : bs = r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8 := by
    simp only [bs, buildPaxPayload, r1, r2, r3, r4, r5, r6, r7, r8,
      c1, c2, c3, c4, c5, c6, c7, c8, decide_eq_true_eq]
  have hf0 : bs.size - ByteArray.empty.size < bs.size + 1 := by simp
  have hs1 := parsePax_opt_step (bs := bs) (pre := ByteArray.empty)
      (post := r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8) (offset := offset) (fuel := bs.size + 1)
      (seenKeys := []) (ov := {}) (nextOv := { path? := some wp }) (cond := c1) (key := "path") (value := wp)
      (by simpa [ByteArray.empty_append, ByteArray.append_assoc] using hbs_def)
      hpax_lim hf0 (paxKey_valid_of_dec (by decide)) rfl (fun _ => rfl)
  let p1 := ByteArray.empty ++ r1
  let o1 := if c1 then { path? := some wp } else ({} : PaxOverrides)
  let k1 := if c1 then ["path"] else ([] : List String)
  let f1 := if c1 then bs.size + 1 - 1 else bs.size + 1
  have hk2_seen : !k1.contains "linkpath" = true :=
    not_contains_optCons c1 "linkpath" "path" [] (by decide) rfl
  have hs2 := parsePax_opt_step (bs := bs) (pre := p1)
      (post := r3 ++ r4 ++ r5 ++ r6 ++ r7 ++ r8) (offset := offset) (fuel := f1)
      (seenKeys := k1) (ov := o1) (nextOv := { o1 with linkpath? := some e.linkTarget }) (cond := c2) (key := "linkpath") (value := e.linkTarget)
      (by simpa [p1, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p1, r1, f1] using hs1.1) (paxKey_valid_of_dec (by decide)) hk2_seen (fun _ => rfl)
  let p2 := p1 ++ r2
  let o2 := if c2 then { o1 with linkpath? := some e.linkTarget } else o1
  let k2 := if c2 then "linkpath" :: k1 else k1
  let f2 := if c2 then f1 - 1 else f1
  have hap3 : c3 = true → applyPaxKey o2 "uname" e.uname offset = .ok { o2 with uname? := some e.uname } := by
    intro _; unfold applyPaxKey
    have hu_f : hasNulString e.uname = false := by cases hc : hasNulString e.uname <;> simp_all
    simp [hu_f]
  have hk3_seen : !k2.contains "uname" = true :=
    not_contains_optCons c2 "uname" "linkpath" k1 (by decide)
      (not_contains_optCons c1 "uname" "path" [] (by decide) rfl)
  have hs3 := parsePax_opt_step (bs := bs) (pre := p2)
      (post := r4 ++ r5 ++ r6 ++ r7 ++ r8) (offset := offset) (fuel := f2)
      (seenKeys := k2) (ov := o2) (nextOv := { o2 with uname? := some e.uname }) (cond := c3) (key := "uname") (value := e.uname)
      (by simpa [p2, p1, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p2, r2, ByteArray.size_append, Nat.add_assoc] using hs2.1) (paxKey_valid_of_dec (by decide)) hk3_seen hap3
  let p3 := p2 ++ r3
  let o3 := if c3 then { o2 with uname? := some e.uname } else o2
  let k3 := if c3 then "uname" :: k2 else k2
  let f3 := if c3 then f2 - 1 else f2
  have hap4 : c4 = true → applyPaxKey o3 "gname" e.gname offset = .ok { o3 with gname? := some e.gname } := by
    intro _; unfold applyPaxKey
    have hg_f : hasNulString e.gname = false := by cases hc : hasNulString e.gname <;> simp_all
    simp [hg_f]
  have hk4_seen : !k3.contains "gname" = true :=
    not_contains_optCons c3 "gname" "uname" k2 (by decide)
      (not_contains_optCons c2 "gname" "linkpath" k1 (by decide)
        (not_contains_optCons c1 "gname" "path" [] (by decide) rfl))
  have hs4 := parsePax_opt_step (bs := bs) (pre := p3)
      (post := r5 ++ r6 ++ r7 ++ r8) (offset := offset) (fuel := f3)
      (seenKeys := k3) (ov := o3) (nextOv := { o3 with gname? := some e.gname }) (cond := c4) (key := "gname") (value := e.gname)
      (by simpa [p3, p2, p1, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p3, r3, ByteArray.size_append, Nat.add_assoc] using hs3.1) (paxKey_valid_of_dec (by decide)) hk4_seen hap4
  let p4 := p3 ++ r4
  let o4 := if c4 then { o3 with gname? := some e.gname } else o3
  let k4 := if c4 then "gname" :: k3 else k3
  let f4 := if c4 then f3 - 1 else f3
  have hap5 : c5 = true → applyPaxKey o4 "size" (toString e.data.size) offset = .ok { o4 with size? := some e.data.size } := by
    intro _; unfold applyPaxKey
    have hp := parsePaxNat_toString (offset := offset) (key := "size") hsz
    dsimp only [toString] at hp
    simp [hp]; rfl
  have hk5_seen : !k4.contains "size" = true :=
    not_contains_optCons c4 "size" "gname" k3 (by decide)
      (not_contains_optCons c3 "size" "uname" k2 (by decide)
        (not_contains_optCons c2 "size" "linkpath" k1 (by decide)
          (not_contains_optCons c1 "size" "path" [] (by decide) rfl)))
  have hs5 := parsePax_opt_step (bs := bs) (pre := p4)
      (post := r6 ++ r7 ++ r8) (offset := offset) (fuel := f4)
      (seenKeys := k4) (ov := o4) (nextOv := { o4 with size? := some e.data.size }) (cond := c5) (key := "size") (value := toString e.data.size)
      (by simpa [p4, p3, p2, p1, r5, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p4, r4, ByteArray.size_append, Nat.add_assoc] using hs4.1) (paxKey_valid_of_dec (by decide))
      hk5_seen hap5
  let p5 := p4 ++ r5
  let o5 := if c5 then { o4 with size? := some e.data.size } else o4
  let k5 := if c5 then "size" :: k4 else k4
  let f5 := if c5 then f4 - 1 else f4
  have hap6 : c6 = true → applyPaxKey o5 "mtime" (toString e.mtime) offset = .ok { o5 with mtime? := some e.mtime } := by
    intro _; unfold applyPaxKey
    have hp := parsePaxMtime_toString (offset := offset) hmtime
    dsimp only [toString] at hp
    simp [hp]; rfl
  have hk6_seen : !k5.contains "mtime" = true :=
    not_contains_optCons c5 "mtime" "size" k4 (by decide)
      (not_contains_optCons c4 "mtime" "gname" k3 (by decide)
        (not_contains_optCons c3 "mtime" "uname" k2 (by decide)
          (not_contains_optCons c2 "mtime" "linkpath" k1 (by decide)
            (not_contains_optCons c1 "mtime" "path" [] (by decide) rfl))))
  have hs6 := parsePax_opt_step (bs := bs) (pre := p5)
      (post := r7 ++ r8) (offset := offset) (fuel := f5)
      (seenKeys := k5) (ov := o5) (nextOv := { o5 with mtime? := some e.mtime }) (cond := c6) (key := "mtime") (value := toString e.mtime)
      (by simpa [p5, p4, p3, p2, p1, r5, r6, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p5, r5, ByteArray.size_append, Nat.add_assoc] using hs5.1) (paxKey_valid_of_dec (by decide))
      hk6_seen hap6
  let p6 := p5 ++ r6
  let o6 := if c6 then { o5 with mtime? := some e.mtime } else o5
  let k6 := if c6 then "mtime" :: k5 else k5
  let f6 := if c6 then f5 - 1 else f5
  have hap7 : c7 = true → applyPaxKey o6 "uid" (toString e.uid) offset = .ok { o6 with uid? := some e.uid } := by
    intro _; unfold applyPaxKey
    have hp := parsePaxNat_toString (offset := offset) (key := "uid") huid
    dsimp only [toString] at hp
    simp [hp]; rfl
  have hk7_seen : !k6.contains "uid" = true :=
    not_contains_optCons c6 "uid" "mtime" k5 (by decide)
      (not_contains_optCons c5 "uid" "size" k4 (by decide)
        (not_contains_optCons c4 "uid" "gname" k3 (by decide)
          (not_contains_optCons c3 "uid" "uname" k2 (by decide)
            (not_contains_optCons c2 "uid" "linkpath" k1 (by decide)
              (not_contains_optCons c1 "uid" "path" [] (by decide) rfl)))))
  have hs7 := parsePax_opt_step (bs := bs) (pre := p6)
      (post := r8) (offset := offset) (fuel := f6)
      (seenKeys := k6) (ov := o6) (nextOv := { o6 with uid? := some e.uid }) (cond := c7) (key := "uid") (value := toString e.uid)
      (by simpa [p6, p5, p4, p3, p2, p1, r5, r6, r7, ByteArray.append_assoc] using hbs_def)
      hpax_lim (by simpa [p6, r6, ByteArray.size_append, Nat.add_assoc] using hs6.1) (paxKey_valid_of_dec (by decide))
      hk7_seen hap7
  let p7 := p6 ++ r7
  let o7 := if c7 then { o6 with uid? := some e.uid } else o6
  let k7 := if c7 then "uid" :: k6 else k6
  let f7 := if c7 then f6 - 1 else f6
  have hap8 : c8 = true → applyPaxKey o7 "gid" (toString e.gid) offset = .ok { o7 with gid? := some e.gid } := by
    intro _; unfold applyPaxKey
    have hp := parsePaxNat_toString (offset := offset) (key := "gid") hgid
    dsimp only [toString] at hp
    simp [hp]; rfl
  have hk8_seen : !k7.contains "gid" = true :=
    not_contains_optCons c7 "gid" "uid" k6 (by decide)
      (not_contains_optCons c6 "gid" "mtime" k5 (by decide)
        (not_contains_optCons c5 "gid" "size" k4 (by decide)
          (not_contains_optCons c4 "gid" "gname" k3 (by decide)
            (not_contains_optCons c3 "gid" "uname" k2 (by decide)
              (not_contains_optCons c2 "gid" "linkpath" k1 (by decide)
                (not_contains_optCons c1 "gid" "path" [] (by decide) rfl))))))
  have hs8 := parsePax_opt_step (bs := bs) (pre := p7)
      (post := ByteArray.empty) (offset := offset) (fuel := f7)
      (seenKeys := k7) (ov := o7) (nextOv := { o7 with gid? := some e.gid }) (cond := c8) (key := "gid") (value := toString e.gid)
      (by simpa [p7, p6, p5, p4, p3, p2, p1, r5, r6, r7, r8, ByteArray.append_assoc, ByteArray.append_empty] using hbs_def)
      hpax_lim (by simpa [p7, r7, ByteArray.size_append, Nat.add_assoc] using hs7.1) (paxKey_valid_of_dec (by decide))
      hk8_seen hap8
  let p8 := p7 ++ r8
  let o8 := if c8 then { o7 with gid? := some e.gid } else o7
  let k8 := if c8 then "gid" :: k7 else k7
  let f8 := if c8 then f7 - 1 else f7
  have hp8_eq : p8.size = bs.size := by
    rw [hbs_def]; simp only [p8, p7, p6, p5, p4, p3, p2, p1, ByteArray.empty_append, ByteArray.size_append]
  have hf8_pos : 0 < f8 := by
    have hlt := hs8.1
    simp only [p8, ByteArray.size_append] at hp8_eq
    have hp8_lt : bs.size - (p7.size + r8.size) < f8 := hlt
    omega
  have ho8_eq : o8 =
      { path? := if c1 then some wp else none
      , linkpath? := if c2 then some e.linkTarget else none
      , uname? := if c3 then some e.uname else none
      , gname? := if c4 then some e.gname else none
      , size? := if c5 then some e.data.size else none
      , mtime? := if c6 then some e.mtime else none
      , uid? := if c7 then some e.uid else none
      , gid? := if c8 then some e.gid else none } := by
    dsimp only [o8, o7, o6, o5, o4, o3, o2, o1]
    cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;> cases c6 <;> cases c7 <;> cases c8 <;> rfl
  change parsePaxPayload.go bs offset (bs.size + 1) ByteArray.empty.size [] {} = _
  rw [hs1.2, show ByteArray.empty.size + r1.size = p1.size by simp [p1], hs2.2,
    show p1.size + r2.size = p2.size by simp [p2, ByteArray.size_append], hs3.2,
    show p2.size + r3.size = p3.size by simp [p3, ByteArray.size_append], hs4.2,
    show p3.size + r4.size = p4.size by simp [p4, ByteArray.size_append], hs5.2,
    show p4.size + r5.size = p5.size by simp [p5, ByteArray.size_append], hs6.2,
    show p5.size + r6.size = p6.size by simp [p6, ByteArray.size_append], hs7.2,
    show p6.size + r7.size = p7.size by simp [p7, ByteArray.size_append], hs8.2]
  have hp7_r8 : p7.size + r8.size = bs.size := by
    simpa [p8, ByteArray.size_append] using hp8_eq
  rw [hp7_r8, parsePaxPayload_go_done bs offset f8 k8 o8 hf8_pos, ho8_eq]
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, decide_eq_true_eq]

private theorem mode_mask_idemp (m : UInt32) :
    (((m &&& 0o7777).toNat &&& 0o7777).toUInt32 &&& 0o7777) = (m &&& 0o7777) := by
  have h1 : (m &&& 0o7777).toNat = m.toNat &&& 4095 := rfl
  have hlt : m.toNat &&& 4095 < 2 ^ 12 := Nat.and_lt_two_pow m.toNat (by decide)
  have hlt32 : m.toNat &&& 4095 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  have h2 : (((m &&& 0o7777).toNat &&& 0o7777).toUInt32 &&& 0o7777).toNat =
      (((m.toNat &&& 4095) &&& 4095) % 2 ^ 32) &&& 4095 := rfl
  rw [h2, ← h1, h1, Nat.and_assoc, Nat.and_self, Nat.mod_eq_of_lt hlt32, Nat.and_assoc, Nat.and_self]

private theorem ustarPathSplit_ok (wp : String) (hfit : pathFitsUstar wp = true) (hnul : !hasNulString wp = true) :
    let pair := if wp.toUTF8.size ≤ 100 then ("", wp) else match findUstarSplit wp with | some p => p | none => ("", wp)
    pair.2.toUTF8.size ≤ 100 ∧
    pair.1.toUTF8.size ≤ 155 ∧
    !hasNulString pair.2 = true ∧
    !hasNulString pair.1 = true ∧
    (if pair.1.isEmpty then pair.2 else pair.1 ++ "/" ++ pair.2) = wp := by
  by_cases h100 : wp.toUTF8.size ≤ 100
  · simp only [h100, ↓reduceIte]
    have hemp : "".isEmpty = true := rfl
    have hnul_e : !hasNulString "" = true := by decide
    have hsz_e : "".toUTF8.size ≤ 155 := by decide
    exact ⟨trivial, hsz_e, hnul, hnul_e, by simp [hemp]⟩
  · simp only [h100, ↓reduceIte]
    unfold pathFitsUstar at hfit
    rw [Bool.and_eq_true] at hfit
    have hsome : (findUstarSplit wp).isSome = true := by
      rcases Bool.or_eq_true_iff.mp hfit.2 with hle | hsome
      · exact absurd (decide_eq_true_eq.mp hle) h100
      · exact hsome
    cases hf : findUstarSplit wp with
    | none => rw [hf] at hsome; cases hsome
    | some pair =>
      rcases pair with ⟨pfx, nm⟩
      have ⟨hjoin, hpfx_ne, _, hpfx_sz, hnm_sz⟩ := findUstarSplit_spec hf
      have hjoin_nul := not_hasNulString_append (a := pfx) (b := "/" ++ nm)
      have hnul_wp' : (!hasNulString wp) = true := by cases hc : hasNulString wp <;> simp_all
      have hnul_all : (!hasNulString (pfx ++ ("/" ++ nm))) = true := by
        rw [← String.append_assoc, hjoin]
        exact hnul_wp'
      rw [hjoin_nul, Bool.and_eq_true] at hnul_all
      have hnul_s := not_hasNulString_append (a := "/") (b := nm)
      rw [hnul_s, Bool.and_eq_true] at hnul_all
      have hnul_nm : !hasNulString nm = true := by
        have h2 := hnul_all.2.2
        cases hc : hasNulString nm <;> simp [hc] at h2 ⊢
      have hnul_pfx : !hasNulString pfx = true := by
        have h1 := hnul_all.1
        cases hc : hasNulString pfx <;> simp [hc] at h1 ⊢
      have hpfx_e : pfx.isEmpty = false := by cases hc : pfx.isEmpty <;> simp_all
      exact ⟨hnm_sz, hpfx_sz, hnul_nm, hnul_pfx, by simp [hpfx_e, hjoin]⟩

private theorem unpackLoop_encodeEntryBlocks_step (opts : UnpackOptions)
    (pre post : ByteArray) (e : TarEntry) (normPath : String)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hnorm : normPath = normalizeTarPath e.kind e.path)
    (hpax_lim : fitsPaxLimit e = true)
    (hnot_seen : !seen.contains normPath = true)
    (hle_e : acc.length + 1 ≤ opts.maxEntries)
    (hle_b : totalBytes + e.data.size ≤ opts.maxTotalBytes)
    (hpost_sz : post.size ≥ 512) :
    ∃ entry' : TarEntry,
      entryEquivBool e entry' = true ∧
      entry'.path = normPath ∧
      entry'.data.size = e.data.size ∧
      let bytes := pre ++ (encodeEntryBlocks e normPath ++ post)
      unpackLoop opts bytes pre.size none seen acc totalBytes =
        unpackLoop opts bytes (pre.size + (encodeEntryBlocks e normPath).size)
          none (normPath :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
  unfold validEntryBool at hve
  cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | error _ => rw [hv] at hve; cases hve
  | ok np =>
    rw [hv] at hve
    dsimp only at hve
    have hnp_eq : np = normalizeTarPath e.kind e.path := validateEntryPath_normPath hv
    have hnp : np = normPath := hnp_eq.trans hnorm.symm
    subst hnp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hve
    rcases hve with ⟨⟨hsym_ok, hdata_ok⟩, ⟨⟨⟨⟨⟨hnul_u, hnul_g⟩, huid⟩, hgid⟩, hmtime⟩, hsz⟩⟩
    have ⟨hv_wp, hnul_wp⟩ := validateEntryPath_wirePathOf hv
    have hnot_nul_e : !hasNulString e.linkTarget = true := by
      cases hk : e.kind <;> simp only [hk] at hsym_ok
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
        | error _ => rw [hvs] at hsym_ok; cases hsym_ok
        | ok _ =>
          unfold validateSymlinkTarget at hvs
          dsimp only at hvs
          split at hvs
          · cases hvs
          · split at hvs
            · cases hvs
            · rename_i _ hnn
              cases hc : hasNulString e.linkTarget
              · rfl
              · exfalso; exact hnn hc
    let wp := wirePathOf e.kind np
    let typeByte : UInt8 := match e.kind with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
    have htype_ne : typeByte ≠ 0x78 := by dsimp only [typeByte]; cases e.kind <;> decide
    have htype_beq : (typeByte == 0x78) = false := Bool.eq_false_iff.mpr (by simpa [beq_iff_eq] using htype_ne)
    have decode_ustar_entry :
        ∀ (bytes hdrBlock : ByteArray) (off : Nat) (pendingPax : Option PaxOverrides)
          (fbName fbPrefix fbLink fbUname fbGname : String)
          (fbUid fbGid fbSize fbMtime : Nat)
          (hbytes : bytes.extract off (off + 512 + pad512 e.data.size) = hdrBlock ++ padBlock512 e.data)
          (hhdr : hdrBlock = buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix)
          (hbd_off : off + 512 + pad512 e.data.size ≤ bytes.size)
          (hfuid : fbUid < ustarOctal7Limit) (hfgid : fbGid < ustarOctal7Limit)
          (hfsize : fbSize < ustarOctal11Limit) (hfmtime : fbMtime < ustarOctal11Limit)
          (heff_size : (pendingPax.getD {}).size?.getD fbSize = e.data.size)
          (heff_uid : (pendingPax.getD {}).uid?.getD fbUid = e.uid)
          (heff_gid : (pendingPax.getD {}).gid?.getD fbGid = e.gid)
          (heff_mtime : (pendingPax.getD {}).mtime?.getD fbMtime = e.mtime)
          (heff_path : (pendingPax.getD {}).path? = some wp ∨
            ((pendingPax.getD {}).path? = none ∧ fbName.toUTF8.size ≤ 100 ∧ fbPrefix.toUTF8.size ≤ 155 ∧
              !hasNulString fbName = true ∧ !hasNulString fbPrefix = true ∧
              (if fbPrefix.isEmpty then fbName else fbPrefix ++ "/" ++ fbName) = wp))
          (heff_link : e.kind = .symlink → (pendingPax.getD {}).linkpath? = some e.linkTarget ∨
            ((pendingPax.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100))
          (heff_uname : (pendingPax.getD {}).uname? = some e.uname ∨
            ((pendingPax.getD {}).uname? = none ∧ fbUname = e.uname ∧ e.uname.toUTF8.size ≤ 32))
          (heff_gname : (pendingPax.getD {}).gname? = some e.gname ∨
            ((pendingPax.getD {}).gname? = none ∧ fbGname = e.gname ∧ e.gname.toUTF8.size ≤ 32)),
          let entry' : TarEntry :=
            { path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
            , uid := e.uid, gid := e.gid, mtime := e.mtime
            , uname := e.uname, gname := e.gname
            , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
            , linkTarget := if e.kind == .symlink then e.linkTarget else "" }
          entryEquivBool e entry' = true ∧
          entry'.data.size = e.data.size ∧
          unpackLoop opts bytes off pendingPax seen acc totalBytes =
            unpackLoop opts bytes (off + 512 + pad512 e.data.size) none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
      intro bytes hdrBlock off pendingPax fbName fbPrefix fbLink fbUname fbGname
        fbUid fbGid fbSize fbMtime hbytes hhdr hbd_off hfuid hfgid hfsize hfmtime
        heff_size heff_uid heff_gid heff_mtime heff_path heff_link heff_uname heff_gname
      have hhdr_sz : hdrBlock.size = 512 := by rw [hhdr]; exact buildUstarHeader_size ..
      have hext_hdr : bytes.extract off (off + 512) =
          buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix := by
        have hsub : bytes.extract off (off + 512) =
            (bytes.extract off (off + 512 + pad512 e.data.size)).extract 0 512 := by
          rw [ByteArray.extract_extract]; congr 1; omega
        rw [hsub, hbytes, ← hhdr_sz]
        exact (extract_append_exact_left hdrBlock (padBlock512 e.data)).trans hhdr
      have hnot_ge : ¬(off ≥ bytes.size) := by omega
      have hnz : isZeroRange bytes off 512 = false := isZeroRange_buildUstarHeader_false (by omega) hext_hdr
      have hnot_gt : ¬(off + 512 > bytes.size) := by omega
      have hparse : parseUstarHeader bytes off = .ok
          { mode := (e.mode &&& 0o7777).toNat, uid := fbUid, gid := fbGid, size := fbSize, mtime := fbMtime, typeflag := typeByte } :=
        parseUstarHeader_buildUstarHeader hfuid hfgid hfsize hfmtime (by omega) hext_hdr
      have ⟨hext_nm, hext_lk, hext_un, hext_gn, hext_pfx⟩ := buildUstarHeader_extract_strings hext_hdr
      have hkind_eq : (if typeByte == 0x30 || typeByte == 0x00 then some EntryKind.regular
          else if typeByte == 0x35 then some .directory
          else if typeByte == 0x32 then some .symlink
          else none) = some e.kind := by
        have hk_fn : ∀ k : EntryKind, (let tb : UInt8 := match k with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
            if tb == 0x30 || tb == 0x00 then some EntryKind.regular
            else if tb == 0x35 then some .directory
            else if tb == 0x32 then some .symlink
            else none) = some k := fun k => by cases k <;> rfl
        exact hk_fn e.kind
      have hnonreg_f : (e.kind != .regular && e.data.size != 0) = false := by
        cases hk : e.kind with
        | regular => rfl
        | directory => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
        | symlink => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
      have hnot_maxe : ¬(acc.length + 1 > opts.maxEntries) := by omega
      have hnot_maxb : ¬(totalBytes + e.data.size > opts.maxTotalBytes) := by omega
      have hnot_trunc : ¬(off + 512 + pad512 e.data.size > bytes.size) := by omega
      have hseen_f : seen.contains np = false := by
        cases hc : seen.contains np <;> simp_all
      have huname_ok : (match (pendingPax.getD {}).uname? with
          | some u => Except.ok u
          | none => decodeCStringUtf8 bytes (off + 265) (off + 297) off "uname") = .ok e.uname := by
        rcases heff_uname with hu | ⟨hu, hfb_u, hsz_u⟩
        · rw [hu]
        · have hnul_fb : !hasNulString fbUname = true := by rw [hfb_u]; exact hnul_u
          have hsz_fb : fbUname.toUTF8.size ≤ 32 := by rw [hfb_u]; exact hsz_u
          have hdec_un : decodeCStringUtf8 bytes (off + 265) (off + 297) off "uname" = .ok e.uname := by
            rw [(by omega : off + 297 = (off + 265) + 32)]
            have h0 : decodeCStringUtf8 bytes (off + 265) ((off + 265) + 32) off "uname" = .ok fbUname :=
              decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_un
            rwa [hfb_u] at h0
          rw [hu, hdec_un]
      have hgname_ok : (match (pendingPax.getD {}).gname? with
          | some g => Except.ok g
          | none => decodeCStringUtf8 bytes (off + 297) (off + 329) off "gname") = .ok e.gname := by
        rcases heff_gname with hg | ⟨hg, hfb_g, hsz_g⟩
        · rw [hg]
        · have hnul_fb : !hasNulString fbGname = true := by rw [hfb_g]; exact hnul_g
          have hsz_fb : fbGname.toUTF8.size ≤ 32 := by rw [hfb_g]; exact hsz_g
          have hdec_gn : decodeCStringUtf8 bytes (off + 297) (off + 329) off "gname" = .ok e.gname := by
            rw [(by omega : off + 329 = (off + 297) + 32)]
            have h0 : decodeCStringUtf8 bytes (off + 297) ((off + 297) + 32) off "gname" = .ok fbGname :=
              decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_gn
            rwa [hfb_g] at h0
          rw [hg, hdec_gn]
      have hlink_ok : (match e.kind with
          | .symlink =>
            match (pendingPax.getD {}).linkpath? with
            | some p => Except.ok p
            | none => decodeCStringUtf8 bytes (off + 157) (off + 257) off "linkname"
          | .regular => Except.ok ""
          | .directory => Except.ok "") = .ok (if e.kind == .symlink then e.linkTarget else "") := by
        cases hk : e.kind
        · rfl
        · rfl
        · rcases heff_link hk with hl | ⟨hl, hfb_l, hsz_l⟩
          · rw [hl]; rfl
          · have hnul_fb : !hasNulString fbLink = true := by rw [hfb_l]; exact hnot_nul_e
            have hsz_fb : fbLink.toUTF8.size ≤ 100 := by rw [hfb_l]; exact hsz_l
            have hdec_lk : decodeCStringUtf8 bytes (off + 157) (off + 257) off "linkname" = .ok e.linkTarget := by
              rw [(by omega : off + 257 = (off + 157) + 100)]
              have h0 : decodeCStringUtf8 bytes (off + 157) ((off + 157) + 100) off "linkname" = .ok fbLink :=
                decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_lk
              rwa [hfb_l] at h0
            rw [hl, hdec_lk]; rfl
      have hdec_step : decodeTarEntry opts bytes off
          { mode := (e.mode &&& 0o7777).toNat, uid := fbUid, gid := fbGid, size := fbSize, mtime := fbMtime, typeflag := typeByte }
          pendingPax seen acc.length totalBytes =
          .ok ({ path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
               , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
               , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
               , linkTarget := if e.kind == .symlink then e.linkTarget else "" }, pad512 e.data.size) := by
        unfold decodeTarEntry
        dsimp only
        rw [hkind_eq]
        dsimp only
        simp only [heff_size, hnonreg_f, Bool.false_eq_true, ↓reduceIte, hnot_maxe, hnot_maxb, hnot_trunc]
        have hdec_tail : ∀ (unameRes gnameRes : Except TarError String) (linkRes : Except TarError String),
            unameRes = .ok e.uname → gnameRes = .ok e.gname →
            linkRes = .ok (if e.kind == .symlink then e.linkTarget else "") →
            ((match (@Except.ok TarError String wp), linkRes, unameRes, gnameRes with
            | Except.error e, _, _, _ | _, Except.error e, _, _ | _, _, Except.error e, _ | _, _, _, Except.error e =>
              Except.error e
            | Except.ok rawPath, Except.ok rawLink, Except.ok uname, Except.ok gname =>
              match validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind rawPath with
              | Except.error err => Except.error { err with offset := some off }
              | Except.ok normPath =>
                match (match e.kind with
                  | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink
                  | .regular | .directory => (@Except.ok TarError Unit ())) with
                | Except.error err => Except.error { err with offset := some off }
                | Except.ok () =>
                  if seen.contains normPath then
                    Except.error ({ kind := TarErrorKind.duplicatePath
                                  , message := s!"duplicate tar entry path: {normPath}"
                                  , entryPath := some normPath, offset := some off } : TarError)
                  else
                    Except.ok ({ path := normPath, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
                               , uid := (pendingPax.getD {}).uid?.getD fbUid, gid := (pendingPax.getD {}).gid?.getD fbGid
                               , mtime := (pendingPax.getD {}).mtime?.getD fbMtime, uname := uname, gname := gname
                               , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
                               , linkTarget := rawLink }, pad512 e.data.size)) : Except TarError (TarEntry × Nat)) =
            .ok ({ path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
                 , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
                 , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
                 , linkTarget := if e.kind == .symlink then e.linkTarget else "" }, pad512 e.data.size) := by
          intro unameRes gnameRes linkRes hu hg hl
          rw [hu, hg, hl]
          dsimp only
          rw [hv_wp]
          dsimp only
          cases hk : e.kind <;> simp only [hk] at hsym_ok ⊢
          · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
          · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
          · have h_sym_beq : (EntryKind.symlink == EntryKind.symlink) = true := rfl
            rw [h_sym_beq]; simp only [↓reduceIte]
            cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
            | error err => simp [hvs] at hsym_ok
            | ok _ => simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
        rcases heff_path with hp | ⟨hp, hnm_sz, hpfx_sz, hnm_nul, hpfx_nul, hjoin⟩
        · rw [hp]; dsimp only
          exact hdec_tail _ _ _ huname_ok hgname_ok hlink_ok
        · have hdec_nm : decodeCStringUtf8 bytes off (off + 100) off "name" = .ok fbName :=
            decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by omega) hext_nm
          have hdec_pfx : decodeCStringUtf8 bytes (off + 345) (off + 500) off "prefix" = .ok fbPrefix := by
            have heq500 : off + 500 = (off + 345) + 155 := by omega
            rw [heq500]
            exact decodeCStringUtf8_padRightBytes hpfx_nul hpfx_sz (by omega) hext_pfx
          rw [hp, hdec_nm, hdec_pfx]; dsimp only; rw [hjoin]
          exact hdec_tail _ _ _ huname_ok hgname_ok hlink_ok
      have hdata_extract : (if e.data.size == 0 then ByteArray.empty
          else bytes.extract (off + 512) (off + 512 + e.data.size)) = e.data := by
        by_cases hz : e.data.size = 0
        · simp only [hz, beq_self_eq_true, ↓reduceIte]
          have : e.data.data = #[] := Array.eq_empty_of_size_eq_zero hz
          exact ByteArray.ext this.symm
        · have hbeq : (e.data.size == 0) = false := Bool.eq_false_iff.mpr (by simpa using hz)
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          have hpad_le := le_pad512 e.data.size
          have hsub : bytes.extract (off + 512) (off + 512 + e.data.size) =
              (bytes.extract off (off + 512 + pad512 e.data.size)).extract 512 (512 + e.data.size) := by
            rw [ByteArray.extract_extract, Nat.add_assoc off 512 e.data.size,
              Nat.min_eq_left (by omega)]
          rw [hsub, hbytes, ← hhdr_sz, extract_append_right hdrBlock (padBlock512 e.data) e.data.size,
            padBlock512_extract_prefix e.data]
      have ⟨_, hnorm_id, _⟩ := validateEntryPath_idemp hv
      have heqv : entryEquivBool e
          { path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
          , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
          , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
          , linkTarget := if e.kind == .symlink then e.linkTarget else "" } = true := by
        unfold entryEquivBool
        dsimp only
        rw [hnorm_id, ← hnp_eq, hdata_extract, mode_mask_idemp]
        have hl : ((if e.kind == .symlink then e.linkTarget else "") ==
            (if e.kind == .symlink then (if e.kind == .symlink then e.linkTarget else "") else "")) = true := by
          cases e.kind
          · rfl
          · rfl
          · change (e.linkTarget == e.linkTarget) = true; exact beq_self_eq_true _
        have hkeq : (e.kind == e.kind) = true := by cases e.kind <;> rfl
        simp [hl, hkeq]
      have hdata_sz' : (if e.data.size == 0 then ByteArray.empty
          else bytes.extract (off + 512) (off + 512 + e.data.size)).size = e.data.size := by
        rw [hdata_extract]
      refine ⟨heqv, hdata_sz', ?_⟩
      have hstep_ok : unpackStep opts bytes off pendingPax seen acc totalBytes =
          .ok (.cont (off + 512 + pad512 e.data.size) none (np :: seen)
            ({ path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
             , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
             , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
             , linkTarget := if e.kind == .symlink then e.linkTarget else "" } :: acc)
            (totalBytes + (if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)).size)) := by
        unfold unpackStep
        simp only [hnot_ge, ↓reduceIte, hnz, Bool.false_eq_true, hnot_gt, hparse, htype_beq, hdec_step]
      rw [unpackLoop_step_continue opts bytes off pendingPax seen acc totalBytes _ _ _ _ _
        (by omega) hstep_ok (by omega), hdata_sz']
    by_cases hneed : needsPax e wp
    · have hpax_lim' : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes := by
        unfold fitsPaxLimit at hpax_lim
        dsimp only at hpax_lim
        rw [← hnp_eq] at hpax_lim
        simp [wp, hneed] at hpax_lim
        exact hpax_lim
      let fbPair := if !pathFitsUstar wp then ("", asciiFallback wp 100)
        else if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with | some pair => pair | none => ("", asciiFallback wp 100)
      let fbLink := if e.kind == .symlink then asciiFallback e.linkTarget 100 else ""
      let fbUname := asciiFallback e.uname 32
      let fbGname := asciiFallback e.gname 32
      let fbUid := if e.uid < ustarOctal7Limit then e.uid else 0
      let fbGid := if e.gid < ustarOctal7Limit then e.gid else 0
      let fbSize := if e.data.size < ustarOctal11Limit then e.data.size else 0
      let fbMtime := if e.mtime < ustarOctal11Limit then e.mtime else 0
      have hpax_step : ∀ (paxPayload paxHdr hdr : ByteArray),
          paxPayload = buildPaxPayload e wp →
          paxHdr = buildUstarHeader "././@PaxHeader" (0o644 : UInt32) 0 0 paxPayload.size 0 0x78 "" "" "" "" →
          hdr = buildUstarHeader fbPair.2 e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPair.1 →
          ∃ entry' : TarEntry,
            entryEquivBool e entry' = true ∧
            entry'.path = np ∧
            entry'.data.size = e.data.size ∧
            let bytes := pre ++ (encodeEntryBlocks e np ++ post)
            unpackLoop opts bytes pre.size none seen acc totalBytes =
              unpackLoop opts bytes (pre.size + (encodeEntryBlocks e np).size)
                none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
        intro paxPayload paxHdr hdr hpaxPayload_eq hpaxHdr_eq hhdr_eq
        have henc : encodeEntryBlocks e np = paxHdr ++ padBlock512 paxPayload ++ hdr ++ padBlock512 e.data := by
          have hneed' : needsPax e (wirePathOf e.kind np) = true := hneed
          unfold encodeEntryBlocks
          dsimp only
          simp only [hneed', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp] at hpaxPayload_eq hpaxHdr_eq hhdr_eq
          rw [← hpaxPayload_eq, ← hpaxHdr_eq]
          exact congrArg (fun x => paxHdr ++ padBlock512 paxPayload ++ x ++ padBlock512 e.data) hhdr_eq.symm
        have hpaxHdr_sz : paxHdr.size = 512 := by rw [hpaxHdr_eq]; exact buildUstarHeader_size ..
        have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
        have hpadPax_sz : (padBlock512 paxPayload).size = pad512 paxPayload.size := padBlock512_size _
        have hpadData_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
        have henc_sz : (encodeEntryBlocks e np).size = (512 + pad512 paxPayload.size) + (512 + pad512 e.data.size) := by
          rw [henc]
          simp only [ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, hhdr_sz, hpadData_sz]
          omega
        let bytes := pre ++ (encodeEntryBlocks e np ++ post)
        have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by
          simp only [bytes, ByteArray.size_append, Nat.add_assoc]
        have hext_paxHdr : bytes.extract pre.size (pre.size + 512) = paxHdr := by
          have hsplit : encodeEntryBlocks e np ++ post =
              paxHdr ++ (padBlock512 paxPayload ++ hdr ++ padBlock512 e.data ++ post) := by
            rw [henc]; simp only [ByteArray.append_assoc]
          dsimp only [bytes]
          rw [hsplit, ← ByteArray.append_assoc, ← hpaxHdr_sz]
          exact extract_append_mid pre paxHdr _
        have hnot_ge0 : ¬(pre.size ≥ bytes.size) := by omega
        have hnz0 : isZeroRange bytes pre.size 512 = false :=
          isZeroRange_buildUstarHeader_false (by omega) (hext_paxHdr.trans hpaxHdr_eq)
        have hnot_gt0 : ¬(pre.size + 512 > bytes.size) := by omega
        have hpax_lim'' : paxPayload.size ≤ maxPaxHeaderBytes := by rw [hpaxPayload_eq]; exact hpax_lim'
        have hpax_o11 : paxPayload.size < ustarOctal11Limit := by
          have h : maxPaxHeaderBytes < ustarOctal11Limit := by decide
          omega
        have h0_o7 : 0 < ustarOctal7Limit := by decide
        have h0_o11 : 0 < ustarOctal11Limit := by decide
        have hparse0 : parseUstarHeader bytes pre.size = .ok
            { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := paxPayload.size, mtime := 0, typeflag := 0x78 } :=
          parseUstarHeader_buildUstarHeader h0_o7 h0_o7 hpax_o11 h0_o11 (by omega) (hext_paxHdr.trans hpaxHdr_eq)
        have hnot_maxPax : ¬(paxPayload.size > maxPaxHeaderBytes) := by omega
        have hnot_truncPax : ¬(pre.size + 512 + pad512 paxPayload.size > bytes.size) := by omega
        have hext_paxPayload : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) = paxPayload := by
          have hsplit : encodeEntryBlocks e np ++ post =
              (paxHdr ++ padBlock512 paxPayload) ++ (hdr ++ padBlock512 e.data ++ post) := by
            rw [henc]; simp only [ByteArray.append_assoc]
          have hsub : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) =
              (bytes.extract (pre.size + 512) (pre.size + 512 + (padBlock512 paxPayload).size)).extract 0 paxPayload.size := by
            rw [ByteArray.extract_extract, hpadPax_sz, Nat.add_zero]
            have hle := le_pad512 paxPayload.size
            rw [Nat.min_eq_left (by omega)]
          have hpre_hdr_sz : (pre ++ paxHdr).size = pre.size + 512 := by
            rw [ByteArray.size_append, hpaxHdr_sz]
          have hbytes_eq : bytes = pre ++ paxHdr ++ padBlock512 paxPayload ++ (hdr ++ padBlock512 e.data ++ post) := by
            dsimp only [bytes]; rw [hsplit]; simp only [ByteArray.append_assoc]
          rw [hsub, hbytes_eq, ← hpre_hdr_sz]
          rw [extract_append_mid (pre ++ paxHdr) (padBlock512 paxPayload) (hdr ++ padBlock512 e.data ++ post),
            padBlock512_extract_prefix paxPayload]
        have hparsePax : parsePaxPayload paxPayload pre.size = .ok
            { path? := if !pathFitsUstar wp then some wp else none
            , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
            , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
            , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
            , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
            , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
            , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
            , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none } := by
          rw [hpaxPayload_eq]
          exact buildPaxPayload_parse e wp pre.size hnul_u hnul_g huid hgid hsz hmtime hpax_lim'
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
          have hstep_ok0 : unpackStep opts bytes pre.size none seen acc totalBytes =
              .ok (.cont (pre.size + 512 + pad512 paxPayload.size) (some paxOv) seen acc totalBytes) := by
            unfold unpackStep
            simp only [hnot_ge0, ↓reduceIte, hnz0, Bool.false_eq_true, hnot_gt0, hparse0, beq_self_eq_true,
              Option.isSome_none, hnot_maxPax, hnot_truncPax, hext_paxPayload, hparsePax]
            dsimp only
          exact unpackLoop_step_continue opts bytes pre.size none seen acc totalBytes _ _ _ _ _
            (by omega) hstep_ok0 (by omega)
        let off1 := pre.size + 512 + pad512 paxPayload.size
        have hext1 : bytes.extract off1 (off1 + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
          have hpre1 : (pre ++ (paxHdr ++ padBlock512 paxPayload)).size = off1 := by
            simp only [off1, ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, Nat.add_assoc]
          have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by
            rw [ByteArray.size_append, hhdr_sz, hpadData_sz]
          have hbytes_eq : bytes = (pre ++ (paxHdr ++ padBlock512 paxPayload)) ++ (hdr ++ padBlock512 e.data) ++ post := by
            dsimp only [bytes]; rw [henc]; simp only [ByteArray.append_assoc]
          rw [hbytes_eq, Nat.add_assoc off1 512 (pad512 e.data.size), ← hpre1, ← hmid_sz]
          exact extract_append_mid (pre ++ (paxHdr ++ padBlock512 paxPayload)) (hdr ++ padBlock512 e.data) post
        have hfuid : fbUid < ustarOctal7Limit := by dsimp [fbUid]; split <;> first | assumption | exact h0_o7
        have hfgid : fbGid < ustarOctal7Limit := by dsimp [fbGid]; split <;> first | assumption | exact h0_o7
        have hfsize : fbSize < ustarOctal11Limit := by dsimp [fbSize]; split <;> first | assumption | exact h0_o11
        have hfmtime : fbMtime < ustarOctal11Limit := by dsimp [fbMtime]; split <;> first | assumption | exact h0_o11
        have heff_size : (some paxOv |>.getD {}).size?.getD fbSize = e.data.size := by
          dsimp [paxOv, fbSize]; by_cases h : e.data.size ≥ ustarOctal11Limit <;> simp [h]
        have heff_uid : (some paxOv |>.getD {}).uid?.getD fbUid = e.uid := by
          dsimp [paxOv, fbUid]; by_cases h : e.uid ≥ ustarOctal7Limit <;> simp [h]
        have heff_gid : (some paxOv |>.getD {}).gid?.getD fbGid = e.gid := by
          dsimp [paxOv, fbGid]; by_cases h : e.gid ≥ ustarOctal7Limit <;> simp [h]
        have heff_mtime : (some paxOv |>.getD {}).mtime?.getD fbMtime = e.mtime := by
          dsimp [paxOv, fbMtime]; by_cases h : e.mtime ≥ ustarOctal11Limit <;> simp [h]
        have heff_path : (some paxOv |>.getD {}).path? = some wp ∨
            ((some paxOv |>.getD {}).path? = none ∧ fbPair.2.toUTF8.size ≤ 100 ∧ fbPair.1.toUTF8.size ≤ 155 ∧
              !hasNulString fbPair.2 = true ∧ !hasNulString fbPair.1 = true ∧
              (if fbPair.1.isEmpty then fbPair.2 else fbPair.1 ++ "/" ++ fbPair.2) = wp) := by
          cases hp : !pathFitsUstar wp with
          | true =>
            left; dsimp [paxOv]; simp [hp]
          | false =>
            right
            have hfit : pathFitsUstar wp = true := by simpa using hp
            have hsplit := ustarPathSplit_ok wp hfit hnul_wp
            have hpair : fbPair = (if wp.toUTF8.size ≤ 100 then ("", wp)
                else match findUstarSplit wp with | some p => p | none => ("", asciiFallback wp 100)) := by
              dsimp only [fbPair]; simp only [hp, Bool.false_eq_true, ↓reduceIte]
            refine ⟨by dsimp [paxOv]; simp [hp], ?_⟩
            by_cases h100 : wp.toUTF8.size ≤ 100
            · dsimp only at hsplit
              simp only [h100, ↓reduceIte] at hsplit
              rw [hpair]; simp only [h100, ↓reduceIte]; exact hsplit
            · have hsome : (findUstarSplit wp).isSome = true := by
                have hfit' := hfit
                unfold pathFitsUstar at hfit'
                rw [Bool.and_eq_true] at hfit'
                rcases Bool.or_eq_true_iff.mp hfit'.2 with hle | hs
                · exact absurd (decide_eq_true_eq.mp hle) h100
                · exact hs
              cases hf : findUstarSplit wp with
              | none => rw [hf] at hsome; cases hsome
              | some p =>
                dsimp only at hsplit
                simp only [h100, ↓reduceIte, hf] at hsplit
                rw [hpair]; simp only [h100, ↓reduceIte, hf]; exact hsplit
        have heff_link : e.kind = .symlink → (some paxOv |>.getD {}).linkpath? = some e.linkTarget ∨
            ((some paxOv |>.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100) := by
          intro hk
          cases hl : (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) with
          | true => left; dsimp only [paxOv]; rw [hk, hl]; rfl
          | false =>
            right
            have hl' := hl
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hl'
            refine ⟨by dsimp only [paxOv]; rw [hk, hl]; rfl, ?_, hl'.2⟩
            dsimp only [fbLink]; rw [hk]
            change asciiFallback e.linkTarget 100 = e.linkTarget
            exact isAsciiString_asciiFallback_eq hl'.1 hl'.2
        have heff_uname : (some paxOv |>.getD {}).uname? = some e.uname ∨
            ((some paxOv |>.getD {}).uname? = none ∧ fbUname = e.uname ∧ e.uname.toUTF8.size ≤ 32) := by
          cases hu : (!isAsciiString e.uname || e.uname.toUTF8.size > 32) with
          | true => left; dsimp only [paxOv]; rw [hu]; rfl
          | false =>
            right
            have hu' := hu
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hu'
            refine ⟨by dsimp only [paxOv]; rw [hu]; rfl, ?_, hu'.2⟩
            exact isAsciiString_asciiFallback_eq hu'.1 hu'.2
        have heff_gname : (some paxOv |>.getD {}).gname? = some e.gname ∨
            ((some paxOv |>.getD {}).gname? = none ∧ fbGname = e.gname ∧ e.gname.toUTF8.size ≤ 32) := by
          cases hg : (!isAsciiString e.gname || e.gname.toUTF8.size > 32) with
          | true => left; dsimp only [paxOv]; rw [hg]; rfl
          | false =>
            right
            have hg' := hg
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hg'
            refine ⟨by dsimp only [paxOv]; rw [hg]; rfl, ?_, hg'.2⟩
            exact isAsciiString_asciiFallback_eq hg'.1 hg'.2
        have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr off1 (some paxOv)
          fbPair.2 fbPair.1 fbLink fbUname fbGname fbUid fbGid fbSize fbMtime
          hext1 hhdr_eq (by omega) hfuid hfgid hfsize hfmtime heff_size heff_uid heff_gid heff_mtime
          heff_path heff_link heff_uname heff_gname
        refine ⟨_, heqv1, rfl, hsz1, ?_⟩
        dsimp only
        dsimp only [bytes] at hstep0 hloop1
        rw [hstep0, hloop1]
        have hoff_eq : off1 + 512 + pad512 e.data.size = pre.size + (encodeEntryBlocks e np).size := by
          simp only [off1, henc_sz, Nat.add_assoc]
        rw [hoff_eq]
      exact hpax_step _ _ _ rfl rfl rfl
    · have hneed_false : needsPax e (wirePathOf e.kind np) = false := Bool.eq_false_iff.mpr hneed
      have hnot_need := hneed_false
      unfold needsPax at hnot_need
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt, Nat.not_le] at hnot_need
      rcases hnot_need with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfit_wp, _⟩, hsz_lk⟩, _⟩, hsz_un⟩, _⟩, hsz_gn⟩, huid7⟩, hgid7⟩, hsz11⟩, hmtime11⟩
      let pair := if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with | some p => p | none => ("", wp)
      have hustar_step : ∀ (hdr : ByteArray),
          hdr = buildUstarHeader pair.2 e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pair.1 →
          ∃ entry' : TarEntry,
            entryEquivBool e entry' = true ∧
            entry'.path = np ∧
            entry'.data.size = e.data.size ∧
            let bytes := pre ++ (encodeEntryBlocks e np ++ post)
            unpackLoop opts bytes pre.size none seen acc totalBytes =
              unpackLoop opts bytes (pre.size + (encodeEntryBlocks e np).size)
                none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
        intro hdr hhdr_eq
        have henc : encodeEntryBlocks e np = hdr ++ padBlock512 e.data := by
          unfold encodeEntryBlocks
          dsimp only
          simp only [hneed_false, Bool.not_false, ↓reduceIte]
          exact congrArg (· ++ padBlock512 e.data) hhdr_eq.symm
        have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
        have hpad_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
        have henc_sz : (encodeEntryBlocks e np).size = 512 + pad512 e.data.size := by
          rw [henc, ByteArray.size_append, hhdr_sz, hpad_sz]
        let bytes := pre ++ (encodeEntryBlocks e np ++ post)
        have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by
          simp only [bytes, ByteArray.size_append, Nat.add_assoc]
        have hext1 : bytes.extract pre.size (pre.size + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
          have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by
            rw [ByteArray.size_append, hhdr_sz, hpad_sz]
          dsimp only [bytes]
          rw [henc, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← hmid_sz, ← ByteArray.append_assoc]
          exact extract_append_mid pre (hdr ++ padBlock512 e.data) post
        have hsplit_wp := ustarPathSplit_ok wp hfit_wp hnul_wp
        have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr pre.size none
          pair.2 pair.1 e.linkTarget e.uname e.gname e.uid e.gid e.data.size e.mtime
          hext1 hhdr_eq (by omega) huid7 hgid7 hsz11 hmtime11 rfl rfl rfl rfl
          (Or.inr ⟨rfl, hsplit_wp⟩)
          (fun _ => Or.inr ⟨rfl, rfl, hsz_lk⟩)
          (Or.inr ⟨rfl, rfl, hsz_un⟩)
          (Or.inr ⟨rfl, rfl, hsz_gn⟩)
        refine ⟨_, heqv1, rfl, hsz1, ?_⟩
        dsimp only [bytes]
        rw [hloop1, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← henc_sz]
      exact hustar_step _ rfl

private def encodeEntriesList (entries : List TarEntry) : ByteArray :=
  entries.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) ByteArray.empty

private theorem foldl_encodeEntryBlocks_init (init : ByteArray) (entries : List TarEntry) :
    entries.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init =
      init ++ encodeEntriesList entries := by
  unfold encodeEntriesList
  induction entries generalizing init with
  | nil => simp [ByteArray.append_empty]
  | cons e rest ih =>
    simp only [List.foldl_cons, ByteArray.empty_append]
    rw [ih (init ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)),
        ih (encodeEntryBlocks e (normalizeTarPath e.kind e.path)), ByteArray.append_assoc]

private theorem isZeroRange_zeroBlock_left (pre post : ByteArray) :
    isZeroRange (pre ++ (zeroBlock ++ post)) pre.size 512 = true := by
  apply (isZeroRange_eq_true_iff _ _ _ (by decide)).mpr
  have hz_sz : zeroBlock.size = 512 := zeroBlock_size
  have hle : pre.size + 512 ≤ (pre ++ (zeroBlock ++ post)).size := by
    simp only [ByteArray.size_append, hz_sz]; omega
  refine ⟨hle, fun i hi hbd => ?_⟩
  rw [ByteArray.getElem_append_right (by omega), ByteArray.getElem_append_left (by omega)]
  have hsub : pre.size + i - pre.size = i := by omega
  simp only [hsub]
  have hlt : i < (Array.replicate 512 (0 : UInt8)).size := by simp [hi]
  have : zeroBlock[i]'(by omega) = (Array.replicate 512 (0 : UInt8))[i]'hlt := rfl
  rw [this, Array.getElem_replicate]

private theorem allZeroTrailer_of_ge (bytes : ByteArray) (pos : Nat) (hge : pos ≥ bytes.size) :
    allZeroTrailer bytes pos = true := by
  unfold allZeroTrailer
  have hz : bytes.size - pos = 0 := by omega
  rw [hz]
  simp [allZeroTrailer.go]

private theorem totalDataBytes_cons (e : TarEntry) (rest : List TarEntry) :
    totalDataBytes (e :: rest) = e.data.size + totalDataBytes rest := by
  have hfold : ∀ (init : Nat) (es : List TarEntry),
      es.foldl (fun acc x => acc + x.data.size) init = init + totalDataBytes es := by
    intro init es
    induction es generalizing init with
    | nil => simp [totalDataBytes]
    | cons x xs ih =>
      simp only [totalDataBytes, List.foldl_cons, Nat.zero_add] at ih ⊢
      rw [ih (init + x.data.size), ih x.data.size, Nat.add_assoc]
  unfold totalDataBytes
  simp only [List.foldl_cons, Nat.zero_add]
  exact hfold e.data.size rest

private theorem unpackLoop_encodeEntriesList_aux (opts : UnpackOptions)
    (pre : ByteArray) (entries : List TarEntry)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : entries.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) = true)
    (hnodup : noDupNormalizedPathsBool.go seen entries = true)
    (hpax : entries.all fitsPaxLimit = true)
    (hlen : acc.length + entries.length ≤ opts.maxEntries)
    (hbytes : totalBytes + totalDataBytes entries ≤ opts.maxTotalBytes) :
    ∃ suf : List TarEntry,
      TarEquiv entries suf ∧
      unpackLoop opts (pre ++ (encodeEntriesList entries ++ (zeroBlock ++ zeroBlock)))
        pre.size none seen acc totalBytes = .ok (acc.reverse ++ suf) := by
  induction entries generalizing pre seen acc totalBytes with
  | nil =>
    refine ⟨[], trivial, ?_⟩
    have henc_nil : encodeEntriesList [] = ByteArray.empty := rfl
    rw [henc_nil, ByteArray.empty_append, List.append_nil]
    let bytes := pre ++ (zeroBlock ++ zeroBlock)
    have hz_sz : zeroBlock.size = 512 := zeroBlock_size
    have hbytes_sz : bytes.size = pre.size + 1024 := by
      simp only [bytes, ByteArray.size_append, hz_sz]
    have hnot_ge : ¬(pre.size ≥ bytes.size) := by omega
    have hz1 : isZeroRange bytes pre.size 512 = true := isZeroRange_zeroBlock_left pre zeroBlock
    have hnot_ge512 : ¬(pre.size + 512 ≥ bytes.size) := by omega
    have hz2 : isZeroRange bytes (pre.size + 512) 512 = true := by
      have hbytes_shift : bytes = (pre ++ zeroBlock) ++ (zeroBlock ++ ByteArray.empty) := by
        simp only [bytes, ByteArray.append_empty, ByteArray.append_assoc]
      have hpre_sz : (pre ++ zeroBlock).size = pre.size + 512 := by rw [ByteArray.size_append, hz_sz]
      rw [hbytes_shift, ← hpre_sz]
      exact isZeroRange_zeroBlock_left (pre ++ zeroBlock) ByteArray.empty
    have htrail : allZeroTrailer bytes (pre.size + 1024) = true := allZeroTrailer_of_ge bytes _ (by omega)
    have hstep : unpackStep opts bytes pre.size none seen acc totalBytes = .ok (.done acc.reverse) := by
      unfold unpackStep
      simp only [hnot_ge, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hnot_ge512, hz2,
        Bool.not_true, htrail]
    exact unpackLoop_step_done opts bytes pre.size none seen acc totalBytes _ (by omega) hstep
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hve hpax
    unfold noDupNormalizedPathsBool.go at hnodup
    simp only [Bool.and_eq_true] at hnodup
    let np := normalizeTarPath e.kind e.path
    have hnot_seen : !seen.contains np = true := hnodup.1
    have hve_e : validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true := hve.1
    have htot_cons := totalDataBytes_cons e rest
    have hle_e : acc.length + 1 ≤ opts.maxEntries := by simp only [List.length_cons] at hlen; omega
    have hle_b : totalBytes + e.data.size ≤ opts.maxTotalBytes := by omega
    let tailBytes := encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)
    have htail_sz : tailBytes.size ≥ 512 := by
      have hz_sz : zeroBlock.size = 512 := zeroBlock_size
      simp only [tailBytes, ByteArray.size_append, hz_sz]; omega
    have ⟨entry', heqv_e, hpath_e, hsz_e, hstep⟩ :=
      unpackLoop_encodeEntryBlocks_step opts pre tailBytes e np seen acc totalBytes
        hve_e rfl hpax.1 hnot_seen hle_e hle_b htail_sz
    have henc_cons : encodeEntriesList (e :: rest) = encodeEntryBlocks e np ++ encodeEntriesList rest := by
      unfold encodeEntriesList
      simp only [List.foldl_cons, ByteArray.empty_append]
      exact foldl_encodeEntryBlocks_init (encodeEntryBlocks e np) rest
    have hbytes_eq : pre ++ (encodeEntriesList (e :: rest) ++ (zeroBlock ++ zeroBlock)) =
        pre ++ (encodeEntryBlocks e np ++ tailBytes) := by
      rw [henc_cons]; simp only [tailBytes, ByteArray.append_assoc]
    have hbytes_shift : pre ++ (encodeEntryBlocks e np ++ tailBytes) =
        (pre ++ encodeEntryBlocks e np) ++ (encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)) := by
      simp only [tailBytes, ByteArray.append_assoc]
    have hpre_sz : (pre ++ encodeEntryBlocks e np).size = pre.size + (encodeEntryBlocks e np).size :=
      ByteArray.size_append
    have ⟨suf, hteq_rest, hloop_rest⟩ := ih (pre ++ encodeEntryBlocks e np) (np :: seen) (entry' :: acc)
      (totalBytes + e.data.size) hve.2 hnodup.2 hpax.2 (by simp at hlen ⊢; omega) (by omega)
    refine ⟨entry' :: suf, ⟨heqv_e, hteq_rest⟩, ?_⟩
    rw [hbytes_eq]
    rw [hstep, hbytes_shift, ← hpre_sz, hloop_rest]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem unpackLoop_encodeEntriesList (opts : UnpackOptions)
    (pre : ByteArray) (entries : List TarEntry)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : entries.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) = true)
    (hnodup : noDupNormalizedPathsBool.go seen entries = true)
    (hpax : entries.all fitsPaxLimit = true)
    (hlen : acc.length + entries.length ≤ opts.maxEntries)
    (hbytes : totalBytes + totalDataBytes entries ≤ opts.maxTotalBytes)
    (hacc : acc = []) :
    ∃ decoded : List TarEntry,
      TarEquiv entries decoded ∧
      unpackLoop opts (pre ++ (encodeEntriesList entries ++ (zeroBlock ++ zeroBlock)))
        pre.size none seen acc totalBytes = .ok decoded := by
  subst hacc
  have ⟨suf, hteq, hok⟩ := unpackLoop_encodeEntriesList_aux opts pre entries seen [] totalBytes
    hve hnodup hpax hlen hbytes
  exact ⟨suf, hteq, by simpa using hok⟩

private theorem zeroDeterministicMeta_fitsPaxLimit (e : TarEntry)
    (h : fitsPaxLimit e = true) : fitsPaxLimit (zeroDeterministicMeta e) = true := by
  let np := normalizeTarPath e.kind e.path
  let wp := wirePathOf e.kind np
  have hnp : normalizeTarPath (zeroDeterministicMeta e).kind (zeroDeterministicMeta e).path = np := rfl
  have hwp : wirePathOf (zeroDeterministicMeta e).kind np = wp := rfl
  unfold fitsPaxLimit at h ⊢
  dsimp only at h ⊢
  rw [hnp, hwp]
  have hasc_e : isAsciiString "" = true := by
    unfold isAsciiString
    rw [toUTF8_toList]
    rfl
  have hsz_e : ¬("".toUTF8.size > 32) := by
    have h0 : "".toUTF8.size = 0 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]
      decide
    rw [h0]
    decide
  have h0_7 : ¬((0 : Nat) ≥ ustarOctal7Limit) := by decide
  have h0_11 : ¬((0 : Nat) ≥ ustarOctal11Limit) := by decide
  by_cases hn_z : needsPax (zeroDeterministicMeta e) wp = true
  · simp only [hn_z, ↓reduceIte, decide_eq_true_eq]
    have hn_e : needsPax e wp = true := by
      unfold needsPax at hn_z ⊢
      simp only [zeroDeterministicMeta, hasc_e, Bool.not_true, Bool.or_eq_true, decide_eq_true_eq] at hn_z ⊢
      simp only [hsz_e, h0_7, h0_11, Bool.false_eq_true, or_false] at hn_z
      rcases hn_z with ((h1 | h2) | h3) <;> simp_all
    have h' : (if needsPax e wp = true then decide ((buildPaxPayload e wp).size ≤ maxPaxHeaderBytes) else true) = true := h
    simp only [hn_e, ↓reduceIte, decide_eq_true_eq] at h'
    have hsz_le : (buildPaxPayload (zeroDeterministicMeta e) wp).size ≤ (buildPaxPayload e wp).size := by
      unfold buildPaxPayload
      dsimp only [zeroDeterministicMeta]
      simp only [hasc_e, Bool.not_true, hsz_e, h0_7, h0_11, decide_false, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, ByteArray.size_append, ByteArray.size_empty, Nat.add_zero]
      exact Nat.le_trans
        (Nat.add_le_add_right (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    omega
  · simp [hn_z]

private theorem zeroDeterministicMeta_validArchiveBool (allowAbs allowPar : Bool) (entries : List TarEntry)
    (hv : validArchiveBool allowAbs allowPar entries = true) :
    validArchiveBool allowAbs allowPar (entries.map zeroDeterministicMeta) = true := by
  unfold validArchiveBool at hv ⊢
  rw [Bool.and_eq_true] at hv ⊢
  have hall : (entries.map zeroDeterministicMeta).all (validEntryBool allowAbs allowPar) = true := by
    rw [List.all_map]
    rw [List.all_eq_true] at hv ⊢
    intro e he
    have hve := hv.1 e he
    unfold validEntryBool at hve ⊢
    dsimp only [Function.comp_def, zeroDeterministicMeta] at hve ⊢
    cases hvp : validateEntryPath allowAbs allowPar e.kind e.path with
    | error _ => simp [hvp] at hve
    | ok np =>
      have hnul_e : !hasNulString "" = true := by decide
      have h0_64 : decide ((0 : Nat) < u64Limit) = true := by decide
      simp only [hvp, Bool.and_eq_true] at hve ⊢
      rcases hve with ⟨⟨h1, h2⟩, ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h3⟩⟩
      exact ⟨⟨h1, h2⟩, ⟨⟨⟨⟨⟨hnul_e, hnul_e⟩, h0_64⟩, h0_64⟩, h0_64⟩, h3⟩⟩
  have hnodup : noDupNormalizedPathsBool (entries.map zeroDeterministicMeta) = true := by
    have hgo : ∀ seen es, noDupNormalizedPathsBool.go seen (es.map zeroDeterministicMeta) =
        noDupNormalizedPathsBool.go seen es := by
      intro seen es
      induction es generalizing seen with
      | nil => rfl
      | cons e rest ih =>
        simp only [List.map_cons, noDupNormalizedPathsBool.go]
        exact congrArg (_ && ·) (ih _)
    exact (hgo [] entries).trans hv.2
  exact ⟨hall, hnodup⟩

private theorem totalDataBytes_map_zeroDet (entries : List TarEntry) :
    totalDataBytes (entries.map zeroDeterministicMeta) = totalDataBytes entries := by
  have hfold : ∀ (init : Nat) (es : List TarEntry),
      (es.map zeroDeterministicMeta).foldl (fun acc e => acc + e.data.size) init =
      es.foldl (fun acc e => acc + e.data.size) init := by
    intro init es
    induction es generalizing init with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih (init + e.data.size)
  exact hfold 0 entries

private theorem foldl_det_eq_encodeEntriesList (det : Bool) (entries : List TarEntry) :
    entries.foldl (fun b e => b ++ encodeEntryBlocks (if det = true then zeroDeterministicMeta e else e)
      (normalizeTarPath e.kind e.path)) ByteArray.empty =
    encodeEntriesList (if det = true then entries.map zeroDeterministicMeta else entries) := by
  cases det with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    unfold encodeEntriesList
    have hgen : ∀ (init : ByteArray) (es : List TarEntry),
        es.foldl (fun b e => b ++ encodeEntryBlocks (zeroDeterministicMeta e) (normalizeTarPath e.kind e.path)) init =
        (es.map zeroDeterministicMeta).foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init := by
      intro init es
      induction es generalizing init with
      | nil => rfl
      | cons e rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        exact ih _
    exact hgen ByteArray.empty entries

private theorem packUnpack_roundTrip_witness (entries : List TarEntry)
    (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (hvalid : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (habs : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hpar : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hlen : entries.length ≤ unpackOpts.maxEntries)
    (hbytes : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hpax : entries.all fitsPaxLimit = true) :
    ∃ bytes decoded,
      Impl.packWith packOpts entries = .ok bytes ∧
      Impl.unpackWith unpackOpts bytes = .ok decoded ∧
      TarEquiv (if packOpts.deterministic then entries.map zeroDeterministicMeta else entries) decoded := by
  have hvalid_b : validArchiveBool packOpts.allowAbsolute packOpts.allowParentTraversal entries = true := hvalid
  have hvalid_b' := hvalid_b
  unfold validArchiveBool at hvalid_b'
  have ⟨bytes, hpack_ok⟩ := (packWith_go_spec packOpts entries [] ByteArray.empty).2 hvalid_b'
  have hpack_def : Impl.packWith packOpts entries = .ok bytes := hpack_ok
  have hbytes_spec := ((packWith_go_spec packOpts entries [] ByteArray.empty).1 bytes hpack_ok).2
  let effEntries := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
  have hbytes_eq : bytes = encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock) := by
    rw [hbytes_spec, ByteArray.empty_append, foldl_det_eq_encodeEntriesList]
  have hvalid_eff : validArchiveBool packOpts.allowAbsolute packOpts.allowParentTraversal effEntries = true := by
    dsimp only [effEntries]
    split
    · exact zeroDeterministicMeta_validArchiveBool _ _ entries hvalid_b
    · exact hvalid_b
  have hvalid_unpack : validArchiveBool unpackOpts.allowAbsolute unpackOpts.allowParentTraversal effEntries = true :=
    validArchiveBool_mono habs hpar effEntries hvalid_eff
  have hpax_eff : effEntries.all fitsPaxLimit = true := by
    dsimp only [effEntries]
    split
    · rw [List.all_map, List.all_eq_true]
      rw [List.all_eq_true] at hpax
      exact fun e he => zeroDeterministicMeta_fitsPaxLimit e (hpax e he)
    · exact hpax
  have hlen_eff : effEntries.length ≤ unpackOpts.maxEntries := by
    dsimp only [effEntries]
    split <;> simp [hlen]
  have hbytes_eff : totalDataBytes effEntries ≤ unpackOpts.maxTotalBytes := by
    dsimp only [effEntries]
    split
    · rw [totalDataBytes_map_zeroDet]; exact hbytes
    · exact hbytes
  unfold validArchiveBool at hvalid_unpack
  rw [Bool.and_eq_true, List.all_eq_true] at hvalid_unpack
  have ⟨decoded, hteq, hloop_ok⟩ := unpackLoop_encodeEntriesList unpackOpts ByteArray.empty effEntries [] [] 0
    (List.all_eq_true.mpr hvalid_unpack.1) hvalid_unpack.2 hpax_eff (by simpa using hlen_eff) (by simpa using hbytes_eff) rfl
  have hbytes_nz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by
    have hbytes_form : bytes = encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock) := hbytes_eq
    have hsz_mod : ∀ es : List TarEntry, (encodeEntriesList es).size % 512 = 0 := by
      intro es
      have hgen : ∀ (init : ByteArray), init.size % 512 = 0 →
          (es.foldl (fun b e => b ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) init).size % 512 = 0 := by
        intro init hinit
        induction es generalizing init with
        | nil => exact hinit
        | cons e rest ih =>
          simp only [List.foldl_cons]
          apply ih
          rw [ByteArray.size_append]
          have he_mod : (encodeEntryBlocks e (normalizeTarPath e.kind e.path)).size % 512 = 0 := by
            unfold encodeEntryBlocks
            dsimp only
            split
            · have hmd := padBlock512_size_mod e.data
              simp only [ByteArray.size_append, buildUstarHeader_size]
              omega
            · have hmp := padBlock512_size_mod (buildPaxPayload e (wirePathOf e.kind (normalizeTarPath e.kind e.path)))
              have hmd := padBlock512_size_mod e.data
              simp only [ByteArray.size_append, buildUstarHeader_size]
              omega
          omega
      exact hgen ByteArray.empty rfl
    have hz2_sz : (zeroBlock ++ zeroBlock).size = 1024 := by rw [ByteArray.size_append, zeroBlock_size]
    have hsz_full : bytes.size = (encodeEntriesList effEntries).size + 1024 := by
      rw [hbytes_form, ByteArray.size_append, hz2_sz]
    have hmod : bytes.size % 512 = 0 := by have := hsz_mod effEntries; omega
    have hpos : bytes.size ≠ 0 := by omega
    simp [hpos, hmod]
  have hunpack_ok : Impl.unpackWith unpackOpts bytes = .ok decoded := by
    unfold Impl.unpackWith
    simp only [hbytes_nz, Bool.false_eq_true, ↓reduceIte]
    have hbytes_form : ByteArray.empty ++ (encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock)) = bytes := by
      simpa [ByteArray.empty_append] using hbytes_eq.symm
    simpa [hbytes_form] using hloop_ok
  exact ⟨bytes, decoded, hpack_def, hunpack_ok, hteq⟩

/-- Prove `test_tar_packUnpack_roundTrip` for `defaultApi`. -/
theorem allPass_packUnpack_roundTrip :
    AllPass (test_tar_packUnpack_roundTrip defaultApi) := by
  intro entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  have ⟨bytes, decoded, hpack_ok, hunpack_ok, hteq⟩ :=
    packUnpack_roundTrip_witness entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  have hpack_def : defaultApi.packWith packOpts entries = .ok bytes := hpack_ok
  have hunpack_def : defaultApi.unpackWith unpackOpts bytes = .ok decoded := hunpack_ok
  dsimp only [test_tar_packUnpack_roundTrip, Bind.bind, Pure.pure, NondetTest.assert]
  rw [hpack_def]
  dsimp only
  rw [hunpack_def]
  exact ⟨hteq, trivial⟩

/-- Witness `CanReach (test_tar_packUnpack_roundTrip defaultApi)` using an empty archive. -/
theorem canReach_packUnpack_roundTrip :
    CanReach (test_tar_packUnpack_roundTrip defaultApi) := by
  have hv : ValidArchive ({} : PackOptions).allowAbsolute ({} : PackOptions).allowParentTraversal [] := by
    unfold ValidArchive validArchiveBool; rfl
  have hlen : ([] : List TarEntry).length ≤ ({} : UnpackOptions).maxEntries := Nat.zero_le _
  have htot : totalDataBytes [] ≤ ({} : UnpackOptions).maxTotalBytes := by simp [totalDataBytes]
  have hpax : ([] : List TarEntry).all fitsPaxLimit = true := rfl
  have ⟨bytes, decoded, hpack_ok, hunpack_ok, hteq⟩ :=
    packUnpack_roundTrip_witness [] {} {} hv rfl rfl hlen htot hpax
  have hpack_def : defaultApi.packWith {} [] = .ok bytes := hpack_ok
  have hunpack_def : defaultApi.unpackWith {} bytes = .ok decoded := hunpack_ok
  unfold CanReach CanReachRun test_tar_packUnpack_roundTrip
  simp only [Bind.bind, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  refine ⟨[], {}, {}, hv, rfl, rfl, hlen, htot, hpax, ?_⟩
  rw [hpack_def]
  dsimp only
  rw [hunpack_def]
  exact ⟨hteq, trivial⟩

/-- Decidable `Bool` form of `TarEquiv` for concrete certificate proofs. -/
def tarEquivBool : List TarEntry → List TarEntry → Bool
  | [], [] => true
  | a :: xs, b :: ys => entryEquivBool a b && tarEquivBool xs ys
  | _, _ => false

/-- `tarEquivBool xs ys = true` implies `TarEquiv xs ys`. -/
theorem tarEquiv_of_tarEquivBool {xs ys : List TarEntry} (h : tarEquivBool xs ys = true) :
    TarEquiv xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => trivial
    | cons _ _ => cases h
  | cons a xs ih =>
    cases ys with
    | nil => cases h
    | cons b ys =>
      simp only [tarEquivBool, Bool.and_eq_true] at h
      exact ⟨h.1, ih h.2⟩

/-- Concrete helper certifying `checkRoundTripCase defaultApi` when concrete evaluation succeeds. -/
theorem checkRoundTripCase_of_eval {packOpts : PackOptions} {unpackOpts : UnpackOptions}
    {entries : List TarEntry}
    (h : (match defaultApi.packWith packOpts entries with
      | .error _ => false
      | .ok bytes =>
        match defaultApi.unpackWith unpackOpts bytes with
        | .error _ => false
        | .ok decoded =>
          let expected := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
          tarEquivBool expected decoded) = true) :
    AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries) := by
  cases hp : defaultApi.packWith packOpts entries with
  | error _ => simp [hp] at h
  | ok bytes =>
    cases hu : defaultApi.unpackWith unpackOpts bytes with
    | error _ => simp [hp, hu] at h
    | ok decoded =>
      simp only [hp, hu] at h
      dsimp [AllPass, checkRoundTripCase]
      rw [hp]
      dsimp only
      rw [hu]
      dsimp only [Bind.bind, Pure.pure, NondetTest.assert]
      exact ⟨tarEquiv_of_tarEquivBool h, trivial⟩

/-- Certify `checkRoundTripCase defaultApi` directly from `allPass_packUnpack_roundTrip`. -/
theorem checkRoundTripCase_of_valid {entries : List TarEntry} {packOpts : PackOptions}
    {unpackOpts : UnpackOptions}
    (hv : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (ha : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hp : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hl : entries.length ≤ unpackOpts.maxEntries)
    (hb : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hx : entries.all fitsPaxLimit = true) :
    AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries) :=
  allPass_packUnpack_roundTrip entries packOpts unpackOpts hv ha hp hl hb hx

end LeanSwe.Tar.Proofs

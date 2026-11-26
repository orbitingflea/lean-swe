import Core.Assumptions
import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.SpecTests

/-!
# UUIDv4 Bitwise, Hex Codec, and Hyphen Framing Lemmas

Pure algebraic layer for `LeanSwe.Uuid.Proofs`:
- Bitwise RFC 4122 version/variant invariants (`uint8_bv8`, zero 256-entry tables).
- Generic `List UInt8` hex encoding/decoding (`formatHexList`, `decodeHexPairs`).
- Canonical `8-4-4-4-12` hyphen framing (`frame5` slice decomposition).
- Opaque-witness `ValidV4` specifications preventing kernel unfolding of `ByteArray.set!`.
- Pure `NeverErrorKindPure` reductions for `fromRandomBytes`, `parseHexChars`, and `parse`.
-/

namespace LeanSwe.Uuid.Proofs.Codec

open Core LeanSwe.Uuid

/-- Sixteen zero bytes used as a concrete non-vacuity witness. -/
def zeros16 : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Concatenation with a non-empty left prefix is never the empty string. -/
theorem append_ne_empty {a b : String} (hl : 0 < a.length) : a ++ b ≠ "" := by
  intro h; have hs := congrArg String.length h; rw [String.length_append] at hs
  have h0 : ("" : String).length = 0 := rfl; omega

/-- Valid 16-byte RFC 4122 version 4 UUID invariant. -/
def ValidV4 (u : Uuid) : Prop :=
  u.bytes.size = 16 ∧ (u.bytes[6]! &&& 0xF0) = 0x40 ∧ (u.bytes[8]! &&& 0xC0) = 0x80

private theorem uint8_bv8 {a b : UInt8}
    (h : a.toBitVec[0] = b.toBitVec[0] ∧ a.toBitVec[1] = b.toBitVec[1] ∧ a.toBitVec[2] = b.toBitVec[2] ∧
         a.toBitVec[3] = b.toBitVec[3] ∧ a.toBitVec[4] = b.toBitVec[4] ∧ a.toBitVec[5] = b.toBitVec[5] ∧
         a.toBitVec[6] = b.toBitVec[6] ∧ a.toBitVec[7] = b.toBitVec[7]) : a = b := by
  apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_getElem_eq; intro i hi
  match i, hi with
  | 0, _ => exact h.1 | 1, _ => exact h.2.1 | 2, _ => exact h.2.2.1 | 3, _ => exact h.2.2.2.1
  | 4, _ => exact h.2.2.2.2.1 | 5, _ => exact h.2.2.2.2.2.1 | 6, _ => exact h.2.2.2.2.2.2.1 | 7, _ => exact h.2.2.2.2.2.2.2

private theorem uint8_div16_of_ver {b : UInt8} (h : (b &&& 0xF0) = 0x40) : b.toNat / 16 = 4 := by
  have hv := congrArg (fun x : UInt8 => (x >>> 4).toNat) h
  rw [show (b &&& 0xF0) >>> 4 = b >>> 4 from uint8_bv8 (by simp)] at hv
  simpa [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow] using hv
private theorem uint8_div64_of_var {b : UInt8} (h : (b &&& 0xC0) = 0x80) : b.toNat / 64 = 2 := by
  have hv := congrArg (fun x : UInt8 => (x >>> 6).toNat) h
  rw [show (b &&& 0xC0) >>> 6 = b >>> 6 from uint8_bv8 (by simp)] at hv
  simpa [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow] using hv

private theorem hex_lower_ok : ∀ i : Fin 16, Internal.hexCharToNibble (Internal.lowerHexDigit i.1) = some (UInt8.ofNat i.1) := by decide
private theorem hex_upper_ok : ∀ i : Fin 16, Internal.hexCharToNibble (Char.toUpper (Internal.lowerHexDigit i.1)) = some (UInt8.ofNat i.1) := by decide
private theorem lower_isLowerHex_ok : ∀ i : Fin 16, isLowerHexChar (Internal.lowerHexDigit i.1) = true := by decide

private theorem uint8_hex_roundtrip_with (f : Char → Char)
    (hf : ∀ i : Fin 16, Internal.hexCharToNibble (f (Internal.lowerHexDigit i.1)) = some (UInt8.ofNat i.1)) (b : UInt8) :
    Internal.hexCharsToByte (f (Internal.lowerHexDigit (b.toNat / 16))) (f (Internal.lowerHexDigit (b.toNat % 16))) = some b := by
  have hb := b.toNat_lt; unfold Internal.hexCharsToByte
  rw [hf ⟨b.toNat / 16, by omega⟩, hf ⟨b.toNat % 16, by omega⟩]
  simp only [Option.some.injEq, UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : b.toNat / 16 < 256), Nat.mod_eq_of_lt (by omega : b.toNat % 16 < 256)]
  rw [show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat by omega, UInt8.ofNat_toNat]

private def nibbleCheck (c : Char) : Bool :=
  match Internal.hexCharToNibble c with
  | none => !isHexChar c
  | some n =>
    isHexChar c && (n.toNat < 16) && (Internal.lowerHexDigit n.toNat == Char.toLower c) && (c == '4' || n.toNat != 4) &&
    (c == '8' || c == '9' || c == 'a' || c == 'b' || c == 'A' || c == 'B' || !(8 ≤ n.toNat && n.toNat ≤ 11))

private theorem ascii_nibbleCheck : ∀ hi : Fin 8, ∀ lo : Fin 16, nibbleCheck (Char.ofNat (hi.1 * 16 + lo.1)) = true := by decide

private theorem nibbleCheck_all (c : Char) : nibbleCheck c = true := by
  rcases Nat.lt_or_ge c.toNat 128 with hc | hc
  · have h := ascii_nibbleCheck ⟨c.toNat / 16, by omega⟩ ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
    rw [show (c.toNat / 16) * 16 + c.toNat % 16 = c.toNat by omega, Char.ofNat_toNat] at h; exact h
  · have hle : ∀ d : Char, d.toNat ≤ 102 → ¬(c ≤ d) := fun d hd h => by
      have := UInt32.le_iff_toNat_le.mp h; change c.toNat ≤ d.toNat at this; omega
    simp [nibbleCheck, Internal.hexCharToNibble, isHexChar, isLowerHexChar,
      hle '9' (by decide), hle 'f' (by decide), hle 'F' (by decide)]

private theorem hexCharToNibble_none_of_not_hex {c : Char} (hn : isHexChar c = false) : Internal.hexCharToNibble c = none := by
  have hp := nibbleCheck_all c; cases h : Internal.hexCharToNibble c with | none => rfl | some _ => simp [nibbleCheck, h, hn] at hp
private theorem hexCharToNibble_some_of_hex {c : Char} (h : isHexChar c = true) : ∃ n, Internal.hexCharToNibble c = some n := by
  have hp := nibbleCheck_all c; cases h1 : Internal.hexCharToNibble c with | none => simp [nibbleCheck, h1, h] at hp | some n => exact ⟨n, rfl⟩

private theorem hexCharToNibble_props {c : Char} {n : UInt8} (h : Internal.hexCharToNibble c = some n) :
    n.toNat < 16 ∧ Internal.lowerHexDigit n.toNat = Char.toLower c ∧ (c ≠ '4' → n.toNat ≠ 4) ∧
    (c ≠ '8' → c ≠ '9' → c ≠ 'a' → c ≠ 'b' → c ≠ 'A' → c ≠ 'B' → ¬(8 ≤ n.toNat ∧ n.toNat ≤ 11)) := by
  have hp := nibbleCheck_all c
  simp only [nibbleCheck, h, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hp
  refine ⟨hp.1.1.1.2, hp.1.1.2, fun hne => hp.1.2.elim (fun e => absurd e hne) id, fun h8 h9 ha hb hA hB => ?_⟩
  rcases hp.2 with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | hnot
  all_goals first | exact absurd rfl ‹_› | (simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hnot; omega)

private theorem hexCharsToByte_byteToHexChars {hi lo : Char} {b : UInt8} (h : Internal.hexCharsToByte hi lo = some b) :
    Internal.byteToHexChars b = [Char.toLower hi, Char.toLower lo] := by
  unfold Internal.hexCharsToByte at h
  cases h1 : Internal.hexCharToNibble hi <;> cases h2 : Internal.hexCharToNibble lo <;> simp_all
  rename_i nh nl; subst h
  obtain ⟨hh1, hh2, _, _⟩ := hexCharToNibble_props h1; obtain ⟨hl1, hl2, _, _⟩ := hexCharToNibble_props h2
  have hnat : (nh * 16 + nl).toNat = nh.toNat * 16 + nl.toNat := by
    simp [UInt8.toNat_add, UInt8.toNat_mul, Nat.mod_eq_of_lt (by omega : nh.toNat * 16 < 256),
      Nat.mod_eq_of_lt (by omega : nh.toNat * 16 + nl.toNat < 256)]
  simp only [Internal.byteToHexChars, hnat]
  rw [show (nh.toNat * 16 + nl.toNat) / 16 = nh.toNat by omega,
      show (nh.toNat * 16 + nl.toNat) % 16 = nl.toNat by omega, hh2, hl2]

private theorem ba_getElem!_set! {bs : ByteArray} {i j : Nat} {v : UInt8} (hi : i < bs.size) (hj : j < bs.size) :
    (bs.set! i v)[j]! = if i = j then v else bs[j]! := by
  rw [getElem!_pos _ j (by rw [ByteArray.size_set!]; exact hj), getElem!_pos _ j hj]; exact ByteArray.getElem_set! bs i j v hi hj
private theorem ba_getElem!_of_list (bs : List UInt8) (i : Nat) (hi : i < bs.length) :
    (ByteArray.mk bs.toArray)[i]! = bs[i] := by rw [getElem!_pos _ i (by simp [ByteArray.size, hi])]; rfl

private theorem formatHexList_cons (b : UInt8) (rest : List UInt8) :
    Internal.formatHexList (b :: rest) =
      Internal.lowerHexDigit (b.toNat / 16) :: Internal.lowerHexDigit (b.toNat % 16) :: Internal.formatHexList rest := rfl
private theorem formatHexList_length : ∀ bs : List UInt8, (Internal.formatHexList bs).length = 2 * bs.length
  | [] => rfl | _ :: rest => by rw [formatHexList_cons]; simp [formatHexList_length rest]; omega
private theorem formatHexList_all_lowerHexChar (bs : List UInt8) : (Internal.formatHexList bs).all isLowerHexChar = true := by
  rw [List.all_eq_true]; intro c hc
  simp only [Internal.formatHexList, List.mem_flatMap, Internal.byteToHexChars, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨b, _, rfl | rfl⟩ <;> exact lower_isLowerHex_ok ⟨_, by have := b.toNat_lt; omega⟩
private theorem formatHexList_no_dash (bs : List UInt8) : ∀ c ∈ Internal.formatHexList bs, c ≠ '-' := fun c hc he => by
  subst he; cases List.all_eq_true.mp (formatHexList_all_lowerHexChar bs) '-' hc
private theorem formatHexList_getElem? : ∀ (bs : List UInt8) (i : Nat) (hi : i < bs.length),
    (Internal.formatHexList bs)[2 * i]? = some (Internal.lowerHexDigit (bs[i].toNat / 16)) ∧
    (Internal.formatHexList bs)[2 * i + 1]? = some (Internal.lowerHexDigit (bs[i].toNat % 16))
  | [], _, hi => by simp at hi
  | _ :: _, 0, _ => ⟨rfl, rfl⟩
  | _ :: rest, k + 1, hi => by rw [formatHexList_cons, show 2 * (k + 1) = (2 * k) + 2 by omega]; exact formatHexList_getElem? rest k (by simp at hi; omega)

private theorem decodeHexPairs_cons (hi lo : Char) (rest : List Char) {b : UInt8} (hb : Internal.hexCharsToByte hi lo = some b) :
    Internal.decodeHexPairs (hi :: lo :: rest) = (Internal.decodeHexPairs rest).map (b :: ·) := by
  cases hd : Internal.decodeHexPairs rest <;> (unfold Internal.decodeHexPairs; rw [hb, hd]; rfl)

private theorem decodeHexPairs_formatHexList_map (f : Char → Char)
    (hf : ∀ i : Fin 16, Internal.hexCharToNibble (f (Internal.lowerHexDigit i.1)) = some (UInt8.ofNat i.1)) :
    ∀ bs : List UInt8, Internal.decodeHexPairs ((Internal.formatHexList bs).map f) = some bs
  | [] => rfl
  | b :: rest => by
    rw [formatHexList_cons, List.map_cons, List.map_cons, decodeHexPairs_cons _ _ _ (uint8_hex_roundtrip_with f hf b),
        decodeHexPairs_formatHexList_map f hf rest]; rfl

private theorem decodeHexPairs_formatHexList :
    ∀ (cs : List Char) (bs : List UInt8), Internal.decodeHexPairs cs = some bs → Internal.formatHexList bs = cs.map Char.toLower
  | [], _, h => by simp [Internal.decodeHexPairs] at h; subst h; rfl
  | [_], _, h => by simp [Internal.decodeHexPairs] at h
  | hi :: lo :: rest, _, h => by
    unfold Internal.decodeHexPairs at h
    cases hb : Internal.hexCharsToByte hi lo <;> cases hr : Internal.decodeHexPairs rest <;> simp_all
    rename_i b bs'; subst h
    have hh := hexCharsToByte_byteToHexChars hb; have ht := decodeHexPairs_formatHexList rest bs' hr
    unfold Internal.formatHexList at ht ⊢; simp [List.flatMap_cons, hh, ht]

/-- `decodeHexPairs` returns `none` if any character in `cs` is not an ASCII hex digit. -/
theorem decodeHexPairs_none_of_mem_bad :
    ∀ (cs : List Char) (c : Char), c ∈ cs → isHexChar c = false → Internal.decodeHexPairs cs = none
  | [], _, hc, _ => by cases hc
  | [_], _, _, _ => rfl
  | hi :: lo :: rest, c, hc, hbad => by
    unfold Internal.decodeHexPairs; rcases List.mem_cons.mp hc with rfl | hrest
    · simp [Internal.hexCharsToByte, hexCharToNibble_none_of_not_hex hbad]
    · rcases List.mem_cons.mp hrest with rfl | htail
      · cases Internal.hexCharToNibble hi <;> simp [Internal.hexCharsToByte, hexCharToNibble_none_of_not_hex hbad]
      · simp [decodeHexPairs_none_of_mem_bad rest c htail hbad]

private theorem decodeHexPairs_formatHexList_set_even :
    ∀ (bs : List UInt8) (k : Nat) (hk : k < bs.length) (ch : Char) {nh : UInt8},
      Internal.hexCharToNibble ch = some nh →
      Internal.decodeHexPairs ((Internal.formatHexList bs).set (2 * k) ch) =
        some (bs.set k (UInt8.ofNat (nh.toNat * 16 + bs[k].toNat % 16)))
  | [], _, hk, _, _, _ => by simp at hk
  | b :: rest, 0, _, ch, nh, hnh => by
    rw [Nat.mul_zero, formatHexList_cons, List.set_cons_zero]
    have hbyte : Internal.hexCharsToByte ch (Internal.lowerHexDigit (b.toNat % 16)) =
        some (UInt8.ofNat (nh.toNat * 16 + b.toNat % 16)) := by
      unfold Internal.hexCharsToByte; rw [hnh, hex_lower_ok ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩]
      simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := b.toNat_lt; omega : b.toNat % 16 < 256)]
    have hinv : Internal.decodeHexPairs (Internal.formatHexList rest) = some rest := by
      simpa using decodeHexPairs_formatHexList_map (fun c => c) hex_lower_ok rest
    rw [decodeHexPairs_cons _ _ _ hbyte, hinv]; rfl
  | b :: rest, k' + 1, hk, ch, nh, hnh => by
    rw [formatHexList_cons, show 2 * (k' + 1) = (2 * k' + 1) + 1 by omega, List.set_cons_succ,
        show 2 * k' + 1 = (2 * k') + 1 by omega, List.set_cons_succ,
        decodeHexPairs_cons _ _ _ (uint8_hex_roundtrip_with (fun c => c) hex_lower_ok b),
        decodeHexPairs_formatHexList_set_even rest k' (by simp at hk; omega) ch hnh]; rfl

private def frame5 (a b c d e : List Char) : List Char := a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e

private theorem split5_eq (l : List Char) :
    l.take 8 ++ (l.drop 8).take 4 ++ (l.drop 12).take 4 ++ (l.drop 16).take 4 ++ l.drop 20 = l := by
  simp only [List.append_assoc]
  rw [show l.drop 20 = (l.drop 16).drop 4 by simp [List.drop_drop], List.take_append_drop,
      show l.drop 16 = (l.drop 12).drop 4 by simp [List.drop_drop], List.take_append_drop,
      show l.drop 12 = (l.drop 8).drop 4 by simp [List.drop_drop], List.take_append_drop]; exact List.take_append_drop 8 l

private theorem frame5_get {a b c d e : List Char} (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) :
    (frame5 a b c d e)[8]? = some '-' ∧ (frame5 a b c d e)[13]? = some '-' ∧ (frame5 a b c d e)[18]? = some '-' ∧
    (frame5 a b c d e)[23]? = some '-' ∧ (frame5 a b c d e)[14]? = c[0]? ∧ (frame5 a b c d e)[19]? = d[0]? := by
  simp [frame5, List.getElem?_append, ha, hb, hc, hd]
private theorem frame5_strip {a b c d e : List Char} (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) (he : e.length = 12) :
    Internal.stripCanonicalHyphens (frame5 a b c d e) = some (a ++ b ++ c ++ d ++ e) := by
  unfold Internal.stripCanonicalHyphens; simp [frame5, List.drop_append, List.drop_of_length_le, ha, hb, hc, hd, he]
private theorem frame5_insert {a b c d e : List Char} (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) :
    Internal.insertHyphens (a ++ b ++ c ++ d ++ e) = frame5 a b c d e := by
  unfold Internal.insertHyphens frame5; simp [List.drop_append, List.drop_of_length_le, ha, hb, hc, hd]
private theorem frame5_set {a b c d e : List Char} (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) (ch : Char) :
    (frame5 a b c d e).set 14 ch = frame5 a b (c.set 0 ch) d e ∧ (frame5 a b c d e).set 19 ch = frame5 a b c (d.set 0 ch) e ∧
    (a ++ b ++ c ++ d ++ e).set 12 ch = a ++ b ++ c.set 0 ch ++ d ++ e ∧ (a ++ b ++ c ++ d ++ e).set 16 ch = a ++ b ++ c ++ d.set 0 ch ++ e := by
  simp [frame5, ha, hb, hc, hd]

private theorem insertHyphens_get {l : List Char} (hl : l.length = 32) :
    (Internal.insertHyphens l)[8]? = some '-' ∧ (Internal.insertHyphens l)[13]? = some '-' ∧
    (Internal.insertHyphens l)[18]? = some '-' ∧ (Internal.insertHyphens l)[23]? = some '-' ∧
    (Internal.insertHyphens l)[14]? = l[12]? ∧ (Internal.insertHyphens l)[19]? = l[16]? := by
  have h := frame5_get (a := l.take 8) (b := (l.drop 8).take 4) (c := (l.drop 12).take 4)
    (d := (l.drop 16).take 4) (e := l.drop 20) (by simp [hl]) (by simp [hl]) (by simp [hl]) (by simp [hl])
  simp only [List.getElem?_take_of_lt (by decide : 0 < 4), List.getElem?_drop, Nat.add_zero] at h; exact h

private theorem insertHyphens_filter_dash {l : List Char} (hnd : ∀ c ∈ l, c ≠ '-') :
    (Internal.insertHyphens l).filter (fun c => c != '-') = l := by
  have hf : ∀ {xs : List Char}, (∀ c ∈ xs, c ∈ l) → xs.filter (fun c => c != '-') = xs := fun h =>
    List.filter_eq_self.mpr fun c hc => bne_iff_ne.mpr (hnd c (h c hc))
  simp only [Internal.insertHyphens, List.filter_append, List.filter_cons, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
  rw [hf (fun _ => List.mem_of_mem_take), hf (fun _ h => List.mem_of_mem_drop (List.mem_of_mem_take h)),
      hf (fun _ h => List.mem_of_mem_drop (List.mem_of_mem_take h)),
      hf (fun _ h => List.mem_of_mem_drop (List.mem_of_mem_take h)), hf (fun _ => List.mem_of_mem_drop)]; exact split5_eq l

private theorem stripCanonicalHyphens_insertHyphens_len {l : List Char} (hl : l.length = 32) :
    Internal.stripCanonicalHyphens (Internal.insertHyphens l) = some l := by
  have h := frame5_strip (a := l.take 8) (b := (l.drop 8).take 4) (c := (l.drop 12).take 4)
    (d := (l.drop 16).take 4) (e := l.drop 20) (by simp [hl]) (by simp [hl]) (by simp [hl]) (by simp [hl]) (by simp [hl])
  rw [split5_eq] at h; exact h

private theorem strip_insertHyphens_set {l : List Char} (hl : l.length = 32) (ch : Char) :
    Internal.stripCanonicalHyphens ((Internal.insertHyphens l).set 14 ch) = some (l.set 12 ch) ∧
    Internal.stripCanonicalHyphens ((Internal.insertHyphens l).set 19 ch) = some (l.set 16 ch) := by
  let a := l.take 8; let b := (l.drop 8).take 4; let c := (l.drop 12).take 4; let d := (l.drop 16).take 4; let e := l.drop 20
  have ha : a.length = 8 := by simp [a, hl]
  have hb : b.length = 4 := by simp [b, hl]
  have hc : c.length = 4 := by simp [c, hl]
  have hd : d.length = 4 := by simp [d, hl]
  have he : e.length = 12 := by simp [e, hl]
  obtain ⟨hs14, hs19, hl12, hl16⟩ := frame5_set ha hb hc hd ch
  exact ⟨by change Internal.stripCanonicalHyphens ((frame5 a b c d e).set 14 ch) = _; rw [hs14, frame5_strip ha hb (by simp [hc]) hd he, ← hl12, split5_eq l],
         by change Internal.stripCanonicalHyphens ((frame5 a b c d e).set 19 ch) = _; rw [hs19, frame5_strip ha hb hc (by simp [hd]) he, ← hl16, split5_eq l]⟩

private theorem stripCanonicalHyphens_insertHyphens {cs hex : List Char}
    (h : Internal.stripCanonicalHyphens cs = some hex) : Internal.insertHyphens (hex.map Char.toLower) = cs.map Char.toLower := by
  unfold Internal.stripCanonicalHyphens at h; split at h; { cases h }; split at h; { cases h }
  rename_i hlen hhy
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, not_or, Decidable.not_not, Option.some.injEq] at hlen hhy h
  obtain ⟨⟨⟨h8, h13⟩, h18⟩, h23⟩ := hhy; subst h
  have sp : ∀ (l : List Char) k (hk : k < l.length), l[k]? = some '-' → l = l.take k ++ ['-'] ++ l.drop (k + 1) := fun l k hk heq => by
    have hg : l[k] = '-' := Option.some.inj (by rw [← List.getElem?_eq_getElem hk, heq])
    have := List.take_append_drop k l; rw [List.drop_eq_getElem_cons hk, hg] at this; simpa [List.append_assoc] using this.symm
  have s8 := sp cs 8 (by omega) h8
  have s13 := sp (cs.drop 9) 4 (by simp [hlen]) (by simpa [List.getElem?_drop] using h13)
  have s18 := sp (cs.drop 14) 4 (by simp [hlen]) (by simpa [List.getElem?_drop] using h18)
  have s23 := sp (cs.drop 19) 4 (by simp [hlen]) (by simpa [List.getElem?_drop] using h23)
  simp only [List.drop_drop] at s13 s18 s23; rw [s23] at s18; rw [s18] at s13; rw [s13] at s8
  simp only [List.map_append]; rw [frame5_insert (by simp [hlen]) (by simp [hlen]) (by simp [hlen]) (by simp [hlen])]
  conv => rhs; rw [s8]
  simp [frame5, show ('-' : Char).toLower = '-' from rfl, List.append_assoc]

/-- `stripCanonicalHyphens` returns a 32-char list containing every non-hyphen index `idx < 36`. -/
theorem stripCanonicalHyphens_props {cs hex : List Char} (hs : Internal.stripCanonicalHyphens cs = some hex)
    {idx : Nat} (hi : idx < 36) (h8 : idx ≠ 8) (h13 : idx ≠ 13) (h18 : idx ≠ 18) (h23 : idx ≠ 23) :
    hex.length = 32 ∧ cs[idx]! ∈ hex := by
  unfold Internal.stripCanonicalHyphens at hs; split at hs; { cases hs }; split at hs; { cases hs }
  rename_i hlen _; simp only [bne_iff_ne, ne_eq, Decidable.not_not, Option.some.injEq] at hlen hs; subst hs
  refine ⟨by simp [hlen], ?_⟩
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : idx < cs.length)]
  have hm : ∀ s k, s + k = idx → k < 4 → cs[idx]'(by omega) ∈ (cs.drop s).take 4 := fun s k hsk hk =>
    List.mem_take_iff_getElem.mpr ⟨k, by simp [hlen]; omega, by simp [List.getElem_drop, hsk]⟩
  simp only [Option.getD_some, List.mem_append]
  rcases (by omega : idx < 8 ∨ (9 ≤ idx ∧ idx < 13) ∨ (14 ≤ idx ∧ idx < 18) ∨ (19 ≤ idx ∧ idx < 23) ∨ (24 ≤ idx ∧ idx < 36))
    with _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · exact Or.inl <| Or.inl <| Or.inl <| Or.inl (List.mem_take_iff_getElem.mpr ⟨idx, by simp [hlen]; omega, rfl⟩)
  · exact Or.inl <| Or.inl <| Or.inl <| Or.inr (hm 9 (idx - 9) (by omega) (by omega))
  · exact Or.inl <| Or.inl <| Or.inr (hm 14 (idx - 14) (by omega) (by omega))
  · exact Or.inl <| Or.inr (hm 19 (idx - 19) (by omega) (by omega))
  · exact Or.inr (List.mem_drop_iff_getElem.mpr ⟨idx - 24, by simp [hlen]; omega, by congr 1; omega⟩)

private def stampV4 (bs : ByteArray) : Uuid := { bytes := (bs.set! 6 ((bs[6]! &&& 0x0F) ||| 0x40)).set! 8 ((bs[8]! &&& 0x3F) ||| 0x80) }
private theorem validV4_len {u : Uuid} (hv : ValidV4 u) : u.bytes.data.toList.length = 16 := by rw [Array.length_toList, ByteArray.size_data, hv.1]
private theorem validV4_hex_len {u : Uuid} (hv : ValidV4 u) : (Internal.formatHexList u.bytes.data.toList).length = 32 := by rw [formatHexList_length, validV4_len hv]
private theorem validV4_toString_toList {u : Uuid} (hv : ValidV4 u) :
    (Internal.toString u).toList = Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList) := by unfold Internal.toString; simp [hv.1, String.toList_ofList]
private theorem validV4_get_eq {u : Uuid} (hv : ValidV4 u) {i : Nat} (hi : i < 16) :
    u.bytes.data.toList[i]'(by rw [validV4_len hv]; exact hi) = u.bytes[i]! := by rw [getElem!_pos u.bytes i (by rw [hv.1]; exact hi)]; rfl

/-- Construct an opaque valid RFC 4122 v4 `Uuid` from any 16-byte `ByteArray`, preserving non-version/variant bits. -/
theorem fromRandomBytes_spec {bs : ByteArray} (hlen : bs.size = 16) :
    ∃ u : Uuid, Internal.fromRandomBytes bs = .ok u ∧ ValidV4 u ∧
      (u.bytes[6]! &&& (0x0F : UInt8)) = (bs[6]! &&& (0x0F : UInt8)) ∧
      (u.bytes[8]! &&& (0x3F : UInt8)) = (bs[8]! &&& (0x3F : UInt8)) ∧
      (∀ i, i < 16 → i ≠ 6 → i ≠ 8 → u.bytes[i]! = bs[i]!) := by
  have hsz6 : (bs.set! 6 ((bs[6]! &&& 0x0F) ||| 0x40)).size = 16 := by rw [ByteArray.size_set!, hlen]
  have hsz8 : (stampV4 bs).bytes.size = 16 := by unfold stampV4; rw [ByteArray.size_set!, hsz6]
  have h6 : (stampV4 bs).bytes[6]! = (bs[6]! &&& 0x0F) ||| 0x40 := by
    unfold stampV4; rw [ba_getElem!_set! (by omega) (by omega)]
    simp only [show (8 : Nat) ≠ 6 by decide, ↓reduceIte]; rw [ba_getElem!_set! (by omega) (by omega)]; simp
  have h8 : (stampV4 bs).bytes[8]! = (bs[8]! &&& 0x3F) ||| 0x80 := by unfold stampV4; rw [ba_getElem!_set! (by omega) (by omega)]; simp
  refine ⟨stampV4 bs, by unfold Internal.fromRandomBytes stampV4; simp [hlen],
    ⟨hsz8, h6 ▸ uint8_bv8 (by simp), h8 ▸ uint8_bv8 (by simp)⟩, h6 ▸ uint8_bv8 (by simp), h8 ▸ uint8_bv8 (by simp), fun i hi hi6 hi8 => ?_⟩
  unfold stampV4; rw [ba_getElem!_set! (by omega) (by omega)]; simp only [hi8.symm, ↓reduceIte]; rw [ba_getElem!_set! (by omega) (by omega)]; simp [hi6.symm]

private theorem parseHexChars_of_valid_map {u : Uuid} (hv : ValidV4 u) (f : Char → Char)
    (hf : ∀ i : Fin 16, Internal.hexCharToNibble (f (Internal.lowerHexDigit i.1)) = some (UInt8.ofNat i.1)) :
    Internal.parseHexChars ((Internal.formatHexList u.bytes.data.toList).map f) = .ok u := by
  have hl : ((Internal.formatHexList u.bytes.data.toList).map f).length = 32 := by rw [List.length_map, validV4_hex_len hv]
  rw [Internal.parseHexChars]; simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, decodeHexPairs_formatHexList_map f hf]
  unfold Internal.validateV4BytesList; dsimp only
  have hmk : ByteArray.mk u.bytes.data.toList.toArray = u.bytes := by cases u.bytes; simp
  rw [hmk, show (u.bytes.size != 16) = false by simp [hv.1], show ((u.bytes[6]! &&& 0xF0) != 0x40) = false by simp [hv.2.1],
      show ((u.bytes[8]! &&& 0xC0) != 0x80) = false by simp [hv.2.2]]; rfl

private theorem parse_insertHyphens_map {u : Uuid} (hv : ValidV4 u) (f : Char → Char) (hdash : f '-' = '-')
    (hf : ∀ i : Fin 16, Internal.hexCharToNibble (f (Internal.lowerHexDigit i.1)) = some (UInt8.ofNat i.1)) :
    Internal.parseCanonicalChars ((Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList)).map f) = .ok u := by
  have hmap : (Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList)).map f =
      Internal.insertHyphens ((Internal.formatHexList u.bytes.data.toList).map f) := by simp [Internal.insertHyphens, hdash, List.map_take, List.map_drop]
  have hlu : ((Internal.formatHexList u.bytes.data.toList).map f).length = 32 := by rw [List.length_map, validV4_hex_len hv]
  rw [hmap, Internal.parseCanonicalChars,
      show (Internal.insertHyphens ((Internal.formatHexList u.bytes.data.toList).map f)).length = 36 by simp [Internal.insertHyphens, hlu]]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, stripCanonicalHyphens_insertHyphens_len hlu]
  exact parseHexChars_of_valid_map hv f hf

/-- Canonical `Internal.toString` formatting, hyphen layout, v4 nibbles, and round-trip specs for any valid v4 `Uuid`. -/
theorem toString_spec {u : Uuid} (hv : ValidV4 u) :
    (Internal.toString u).length = 36 ∧
    (Internal.toString u).toList[8]? = some '-' ∧ (Internal.toString u).toList[13]? = some '-' ∧
    (Internal.toString u).toList[18]? = some '-' ∧ (Internal.toString u).toList[23]? = some '-' ∧
    (Internal.toString u).toList.all (fun c => c == '-' || isLowerHexChar c) = true ∧
    (Internal.toString u).toList[14]? = some '4' ∧
    ((Internal.toString u).toList[19]? = some '8' ∨ (Internal.toString u).toList[19]? = some '9' ∨
      (Internal.toString u).toList[19]? = some 'a' ∨ (Internal.toString u).toList[19]? = some 'b') ∧
    Internal.parse (Internal.toString u) = .ok u ∧
    Internal.parse (String.ofList ((Internal.toString u).toList.map Char.toUpper)) = .ok u := by
  have hblen := validV4_len hv; have hfl := validV4_hex_len hv; have hto := validV4_toString_toList hv
  obtain ⟨d8, d13, d18, d23, p14, p19⟩ := insertHyphens_get hfl
  have h19 : (Internal.toString u).toList[19]? = some '8' ∨ (Internal.toString u).toList[19]? = some '9' ∨
      (Internal.toString u).toList[19]? = some 'a' ∨ (Internal.toString u).toList[19]? = some 'b' := by
    rw [hto, p19, (formatHexList_getElem? u.bytes.data.toList 8 (by omega)).1, validV4_get_eq hv (by decide)]
    have h64 := uint8_div64_of_var hv.2.2
    rcases (by omega : u.bytes[8]!.toNat / 16 = 8 ∨ u.bytes[8]!.toNat / 16 = 9 ∨
      u.bytes[8]!.toNat / 16 = 10 ∨ u.bytes[8]!.toNat / 16 = 11) with hq | hq | hq | hq <;> (rw [hq]; decide)
  have hall : (Internal.toString u).toList.all (fun c => c == '-' || isLowerHexChar c) = true := by
    rw [hto, List.all_eq_true]; intro c hc; by_cases h : c = '-'
    · simp [h]
    · have hm : c ∈ (Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList)).filter (fun c => c != '-') :=
        List.mem_filter.mpr ⟨hc, bne_iff_ne.mpr h⟩
      rw [insertHyphens_filter_dash (formatHexList_no_dash _)] at hm
      simp [List.all_eq_true.mp (formatHexList_all_lowerHexChar u.bytes.data.toList) c hm]
  exact ⟨by rw [← String.length_toList, hto]; simp [Internal.insertHyphens, hfl],
    hto ▸ d8, hto ▸ d13, hto ▸ d18, hto ▸ d23, hall,
    by rw [hto, p14, (formatHexList_getElem? u.bytes.data.toList 6 (by omega)).1, validV4_get_eq hv (by decide), uint8_div16_of_ver hv.2.1]; rfl,
    h19,
    by unfold Internal.parse; rw [hto]; simpa using parse_insertHyphens_map hv (fun c => c) rfl hex_lower_ok,
    by unfold Internal.parse; rw [String.toList_ofList, hto]; exact parse_insertHyphens_map hv Char.toUpper rfl hex_upper_ok⟩

/-- Compact `Internal.toHex` formatting, dash filtering, round-trip, and strict rejection specs for any valid v4 `Uuid`. -/
theorem toHex_spec {u : Uuid} (hv : ValidV4 u) :
    (Internal.toHex u).length = 32 ∧ (Internal.toHex u).toList.all isLowerHexChar = true ∧
    (Internal.toHex u).toList = (Internal.toString u).toList.filter (fun c => c != '-') ∧
    Internal.parseHex (Internal.toHex u) = .ok u ∧
    Internal.parseHex (String.ofList ((Internal.toHex u).toList.map Char.toUpper)) = .ok u ∧
    Internal.parse (Internal.toHex u) =
      .error { kind := .invalidFormat, message := s!"expected 36 characters for canonical UUID, got {32}" } := by
  have hfl := validV4_hex_len hv; have hstr := validV4_toString_toList hv
  have hhex : (Internal.toHex u).toList = Internal.formatHexList u.bytes.data.toList := by unfold Internal.toHex; rw [String.toList_ofList]
  exact ⟨by rw [← String.length_toList, hhex, hfl], hhex ▸ formatHexList_all_lowerHexChar _,
    by rw [hhex, hstr, insertHyphens_filter_dash (formatHexList_no_dash _)],
    by unfold Internal.parseHex; rw [hhex]; simpa using parseHexChars_of_valid_map hv (fun c => c) hex_lower_ok,
    by unfold Internal.parseHex; rw [String.toList_ofList, hhex]; exact parseHexChars_of_valid_map hv Char.toUpper hex_upper_ok,
    by unfold Internal.parse Internal.parseCanonicalChars; simp [hhex, hfl]⟩

/-- Big-endian high/low nibble indexing for `Internal.toHex` on any valid v4 `Uuid`. -/
theorem toHex_bigEndian {u : Uuid} (hv : ValidV4 u) {i : Nat} (hi : i < 16) :
    (Internal.toHex u).toList[2 * i]? = some (lowerHexDigit (u.bytes[i]!.toNat / 16)) ∧
    (Internal.toHex u).toList[2 * i + 1]? = some (lowerHexDigit (u.bytes[i]!.toNat % 16)) := by
  have hg := formatHexList_getElem? u.bytes.data.toList i (by rw [validV4_len hv]; exact hi)
  rw [validV4_get_eq hv hi] at hg; unfold Internal.toHex; rw [String.toList_ofList]; exact hg

/-- Accepted `parseHexChars` implies `ValidV4` and lowercase round-trip. -/
theorem parseHexChars_ok_props {cs : List Char} {u : Uuid} (h : Internal.parseHexChars cs = .ok u) :
    ValidV4 u ∧ Internal.formatHexList u.bytes.data.toList = cs.map Char.toLower := by
  unfold Internal.parseHexChars at h; split at h; { cases h }
  cases hd : Internal.decodeHexPairs cs with
  | none => simp [hd] at h
  | some bs =>
    simp only [hd] at h; unfold Internal.validateV4BytesList at h; dsimp only at h
    split at h; { cases h }; split at h; { cases h }; split at h; { cases h }
    simp only [Except.ok.injEq] at h; subst h
    rename_i hsz hv6 hv8; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz hv6 hv8
    exact ⟨⟨hsz, hv6, hv8⟩, decodeHexPairs_formatHexList cs bs hd⟩

/-- Every error returned by `parseHexChars` carries a non-empty diagnostic message. -/
theorem parseHexChars_err_msg {cs : List Char} {e : UuidError} (h : Internal.parseHexChars cs = .error e) : e.message ≠ "" := by
  unfold Internal.parseHexChars at h
  split at h; { cases h; exact append_ne_empty (by decide) }; split at h; { cases h; decide }
  unfold Internal.validateV4BytesList at h; dsimp only at h
  split at h; { cases h; exact append_ne_empty (by decide) }; split at h; { cases h; decide }; split at h; { cases h; decide }; cases h

/-- Accepted `parseCanonicalChars` implies `ValidV4` and lowercase hyphenated round-trip. -/
theorem parseCanonicalChars_ok_props {cs : List Char} {u : Uuid} (h : Internal.parseCanonicalChars cs = .ok u) :
    ValidV4 u ∧ (Internal.toString u).toList = cs.map Char.toLower := by
  unfold Internal.parseCanonicalChars at h; split at h; { cases h }; split at h; { cases h }
  rename_i hex hs; obtain ⟨hv, hfmt⟩ := parseHexChars_ok_props h
  exact ⟨hv, by unfold Internal.toString; simp [hv.1, String.toList_ofList, hfmt, stripCanonicalHyphens_insertHyphens hs]⟩

/-- Every error returned by `parseCanonicalChars` carries a non-empty diagnostic message. -/
theorem parseCanonicalChars_err_msg {cs : List Char} {e : UuidError} (h : Internal.parseCanonicalChars cs = .error e) : e.message ≠ "" := by
  unfold Internal.parseCanonicalChars at h
  split at h; { cases h; exact append_ne_empty (by decide) }; split at h; { cases h; decide }; exact parseHexChars_err_msg h

private theorem parseHex_set_even {u : Uuid} (hv : ValidV4 u) {k : Nat} (hk : k < 16)
    {ch : Char} {nh : UInt8} (hnh : Internal.hexCharToNibble ch = some nh) :
    Internal.parseHex (String.ofList ((Internal.toHex u).toList.set (2 * k) ch)) =
      Internal.validateV4BytesList (u.bytes.data.toList.set k
        (UInt8.ofNat (nh.toNat * 16 + (u.bytes.data.toList[k]'(by rw [validV4_len hv]; exact hk)).toNat % 16))) := by
  unfold Internal.parseHex Internal.toHex; rw [String.toList_ofList, String.toList_ofList]
  have hlen : ((Internal.formatHexList u.bytes.data.toList).set (2 * k) ch).length = 32 := by rw [List.length_set, validV4_hex_len hv]
  have hdec := decodeHexPairs_formatHexList_set_even u.bytes.data.toList k (by rw [validV4_len hv]; exact hk) ch hnh
  rw [Internal.parseHexChars]; simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hdec]

private theorem parse_set_eq_parseHex_set {u : Uuid} (hv : ValidV4 u) {i j : Nat} {ch : Char}
    (hs : Internal.stripCanonicalHyphens ((Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList)).set i ch) =
      some ((Internal.formatHexList u.bytes.data.toList).set j ch)) :
    Internal.parse (String.ofList ((Internal.toString u).toList.set i ch)) =
      Internal.parseHex (String.ofList ((Internal.toHex u).toList.set j ch)) := by
  have hfl := validV4_hex_len hv; unfold Internal.parse Internal.parseHex Internal.toHex
  rw [String.toList_ofList, String.toList_ofList, validV4_toString_toList hv, Internal.parseCanonicalChars]
  simp only [List.length_set, show (Internal.insertHyphens (Internal.formatHexList u.bytes.data.toList)).length = 36 by
    simp [Internal.insertHyphens, hfl], bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hs, String.toList_ofList]

/-- Mutating version nibble (`12` in hex / `14` in canonical) to a non-`'4'` hex digit rejects with `.invalidVersion`. -/
theorem badVer_rejects {u : Uuid} (hv : ValidV4 u) {badVer : Char} (hver : isHexChar badVer = true) (hne : badVer ≠ '4') :
    Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 badVer)) =
      .error { kind := .invalidVersion, message := "UUID version nibble must be 4" } ∧
    Internal.parse (String.ofList ((Internal.toString u).toList.set 14 badVer)) =
      .error { kind := .invalidVersion, message := "UUID version nibble must be 4" } := by
  have hhex : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 badVer)) =
      .error { kind := .invalidVersion, message := "UUID version nibble must be 4" } := by
    obtain ⟨nh, hnh⟩ := hexCharToNibble_some_of_hex hver; obtain ⟨hnhLt, _, hnhNe4, _⟩ := hexCharToNibble_props hnh
    rw [show (12 : Nat) = 2 * 6 from rfl, parseHex_set_even hv (by decide) hnh]; unfold Internal.validateV4BytesList; dsimp only
    have hblen := validV4_len hv; let b6 := UInt8.ofNat (nh.toNat * 16 + (u.bytes.data.toList[6]'(by omega)).toNat % 16)
    have hne40 : ((b6 &&& 0xF0) != 0x40) = true := bne_iff_ne.mpr fun h => by
      have hd := uint8_div16_of_ver h; have hmod := Nat.mod_lt (u.bytes.data.toList[6]'(by omega)).toNat (by decide : 0 < 16)
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hd; exact hnhNe4 hne (by omega)
    rw [show ((ByteArray.mk (u.bytes.data.toList.set 6 b6).toArray).size != 16) = false by simp [ByteArray.size, hblen],
        ba_getElem!_of_list _ 6 (by simp [hblen]), List.getElem_set_self, hne40]; rfl
  exact ⟨hhex, by rw [parse_set_eq_parseHex_set hv (strip_insertHyphens_set (validV4_hex_len hv) badVer).1]; exact hhex⟩

/-- Mutating variant nibble (`16` in hex / `19` in canonical) to a non-RFC-4122 hex digit rejects with `.invalidVersion`. -/
theorem badVar_rejects {u : Uuid} (hv : ValidV4 u) {badVar : Char} (hvar : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a') (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 badVar)) =
      .error { kind := .invalidVersion, message := "UUID variant bits must be RFC 4122 (10xx)" } ∧
    Internal.parse (String.ofList ((Internal.toString u).toList.set 19 badVar)) =
      .error { kind := .invalidVersion, message := "UUID variant bits must be RFC 4122 (10xx)" } := by
  have hhex : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 badVar)) =
      .error { kind := .invalidVersion, message := "UUID variant bits must be RFC 4122 (10xx)" } := by
    obtain ⟨nh, hnh⟩ := hexCharToNibble_some_of_hex hvar; obtain ⟨hnhLt, _, _, hnhNot⟩ := hexCharToNibble_props hnh
    rw [show (16 : Nat) = 2 * 8 from rfl, parseHex_set_even hv (by decide) hnh]; unfold Internal.validateV4BytesList; dsimp only
    have hblen := validV4_len hv; let b8 := UInt8.ofNat (nh.toNat * 16 + (u.bytes.data.toList[8]'(by omega)).toNat % 16)
    have hne80 : ((b8 &&& 0xC0) != 0x80) = true := bne_iff_ne.mpr fun h => by
      have hd := uint8_div64_of_var h; have hmod := Nat.mod_lt (u.bytes.data.toList[8]'(by omega)).toNat (by decide : 0 < 16)
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hd; exact hnhNot h8 h9 ha hb hA hB (by omega)
    have h6 : (ByteArray.mk (u.bytes.data.toList.set 8 b8).toArray)[6]! = u.bytes[6]! := by
      rw [ba_getElem!_of_list _ 6 (by simp [hblen]), List.getElem_set_ne (by decide), validV4_get_eq hv (by decide)]
    rw [show ((ByteArray.mk (u.bytes.data.toList.set 8 b8).toArray).size != 16) = false by simp [ByteArray.size, hblen],
        h6, show ((u.bytes[6]! &&& 0xF0) != 0x40) = false by simp [hv.2.1],
        ba_getElem!_of_list _ 8 (by simp [hblen]), List.getElem_set_self, hne80]; rfl
  exact ⟨hhex, by rw [parse_set_eq_parseHex_set hv (strip_insertHyphens_set (validV4_hex_len hv) badVar).2]; exact hhex⟩

private theorem neverPure_ite {α : Type} {k : UuidErrorKind} {c : Bool} {e : UuidError} {t : Except UuidError α}
    (he : e.kind ≠ k) (ht : NeverErrorKindPure UuidError.kind k t) :
    NeverErrorKindPure UuidError.kind k (if c then .error e else t) := by cases c <;> assumption

/-- `fromRandomBytes` never returns any error kind other than `.invalidLength`. -/
theorem fromRandomBytes_never (k : UuidErrorKind) (hk : .invalidLength ≠ k) (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind k (LeanSwe.Uuid.fromRandomBytes bs) := neverPure_ite hk trivial

/-- `parseHexChars` never returns any error kind other than `.invalidFormat` or `.invalidVersion`. -/
theorem parseHexChars_never (k : UuidErrorKind) (h1 : .invalidFormat ≠ k) (h2 : .invalidVersion ≠ k) (cs : List Char) :
    NeverErrorKindPure UuidError.kind k (Internal.parseHexChars cs) := by
  unfold Internal.parseHexChars; apply neverPure_ite h1
  cases Internal.decodeHexPairs cs with | none => exact h1 | some _ => exact neverPure_ite h1 (neverPure_ite h2 (neverPure_ite h2 trivial))

/-- `parse` never returns any error kind other than `.invalidFormat` or `.invalidVersion`. -/
theorem parse_never (k : UuidErrorKind) (h1 : .invalidFormat ≠ k) (h2 : .invalidVersion ≠ k) (s : String) :
    NeverErrorKindPure UuidError.kind k (LeanSwe.Uuid.parse s) := by
  change NeverErrorKindPure UuidError.kind k (Internal.parseCanonicalChars s.toList)
  unfold Internal.parseCanonicalChars; apply neverPure_ite h1
  cases Internal.stripCanonicalHyphens s.toList with | none => exact h1 | some hex => exact parseHexChars_never k h1 h2 hex

end LeanSwe.Uuid.Proofs.Codec

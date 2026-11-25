import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.Utf8Ws
import LeanSwe.Json.Proofs.StringSound

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

private theorem decodeShortEscapeByte (esc : UInt8) :
    let simple? : Option UInt8 :=
      if esc == 0x22 then some 0x22
      else if esc == 0x5c then some 0x5c
      else if esc == 0x2f then some 0x2f
      else if esc == 0x62 then some 0x08
      else if esc == 0x66 then some 0x0c
      else if esc == 0x6e then some 0x0a
      else if esc == 0x72 then some 0x0d
      else if esc == 0x74 then some 0x09
      else none
    (simple? = none) ∨
      ∃ (outCh : Char) (chByte : UInt8),
        simple? = some chByte ∧
        esc < 0x80 ∧ outCh.toNat < 0x80 ∧ outCh.val.toUInt8 = chByte ∧
        renderCharWithStyle outCh .shortEscape = some ['\\', Char.ofNat esc.toNat] := by
  by_cases h1 : esc == 0x22
  · have hb := beq_iff_eq.mp h1; subst hb; exact Or.inr ⟨'"', 0x22, rfl, by decide, by decide, rfl, by decide⟩
  · by_cases h2 : esc == 0x5c
    · have hb := beq_iff_eq.mp h2; subst hb; exact Or.inr ⟨'\\', 0x5c, rfl, by decide, by decide, rfl, by decide⟩
    · by_cases h3 : esc == 0x2f
      · have hb := beq_iff_eq.mp h3; subst hb; exact Or.inr ⟨'/', 0x2f, rfl, by decide, by decide, rfl, by decide⟩
      · by_cases h4 : esc == 0x62
        · have hb := beq_iff_eq.mp h4; subst hb; exact Or.inr ⟨'\x08', 0x08, rfl, by decide, by decide, rfl, by decide⟩
        · by_cases h5 : esc == 0x66
          · have hb := beq_iff_eq.mp h5; subst hb; exact Or.inr ⟨'\x0c', 0x0c, rfl, by decide, by decide, rfl, by decide⟩
          · by_cases h6 : esc == 0x6e
            · have hb := beq_iff_eq.mp h6; subst hb; exact Or.inr ⟨'\n', 0x0a, rfl, by decide, by decide, rfl, by decide⟩
            · by_cases h7 : esc == 0x72
              · have hb := beq_iff_eq.mp h7; subst hb; exact Or.inr ⟨'\r', 0x0d, rfl, by decide, by decide, rfl, by decide⟩
              · by_cases h8 : esc == 0x74
                · have hb := beq_iff_eq.mp h8; subst hb; exact Or.inr ⟨'\t', 0x09, rfl, by decide, by decide, rfl, by decide⟩
                · exact Or.inl (by simp [h1, h2, h3, h4, h5, h6, h7, h8])

private theorem surrogatePair_char_spec {u1 u2 : Nat} {cas1 cas2 : HexCase4}
    {h4_1 h4_2 : List Char}
    (hhi : 0xD800 ≤ u1 ∧ u1 < 0xDC00) (hlo : 0xDC00 ≤ u2 ∧ u2 < 0xE000)
    (hren1 : renderHex4 cas1 u1 = h4_1) (hren2 : renderHex4 cas2 u2 = h4_2) :
    ∃ outC : Char,
      Char.ofNat (0x10000 + (u1 - 0xD800) * 1024 + (u2 - 0xDC00)) = outC ∧
      renderCharWithStyle outC (.surrogatePair cas1 cas2) = some (h4_1 ++ h4_2) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hhi.1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hlo.1
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  have haLt : a < 1024 :=
    Nat.lt_of_add_lt_add_left (Nat.lt_of_lt_of_eq hhi.2 (by decide : 0xDC00 = 0xD800 + 1024))
  have hbLt : b < 1024 :=
    Nat.lt_of_add_lt_add_left (Nat.lt_of_lt_of_eq hlo.2 (by decide : 0xE000 = 0xDC00 + 1024))
  have hGtDfff : 0xdfff < 0x10000 + a * 1024 + b := by
    rw [Nat.add_assoc]
    exact Nat.lt_of_lt_of_le (by decide : 0xdfff < 0x10000) (Nat.le_add_right _ _)
  have hLtMax : 0x10000 + a * 1024 + b < 0x110000 := by
    have haLe : a ≤ 1023 := Nat.le_of_lt_succ haLt
    have hMulLe : a * 1024 ≤ 1023 * 1024 := Nat.mul_le_mul_right 1024 haLe
    calc 0x10000 + a * 1024 + b
        ≤ 0x10000 + 1023 * 1024 + b := Nat.add_le_add_right (Nat.add_le_add_left hMulLe 0x10000) b
      _ < 0x10000 + 1023 * 1024 + 1024 := Nat.add_lt_add_left hbLt _
      _ = 0x110000 := by decide
  have hHelper : ∀ (outC : Char), outC.toNat = 0x10000 + a * 1024 + b →
      renderCharWithStyle outC (.surrogatePair cas1 cas2) = some (h4_1 ++ h4_2) := by
    intro outC hout
    have hge1 : 0x10000 ≤ outC.toNat := by
      rw [hout, Nat.add_assoc]; exact Nat.le_add_right _ _
    have hSub : outC.toNat - 0x10000 = 1024 * a + b := by
      rw [hout, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_comm]
    have hDiv : (outC.toNat - 0x10000) / 1024 = a := by
      rw [hSub, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hbLt, Nat.add_zero]
    have hMod : (outC.toNat - 0x10000) % 1024 = b := by
      rw [hSub, Nat.mul_add_mod, Nat.mod_eq_of_lt hbLt]
    unfold renderCharWithStyle; dsimp only
    rw [ite_eq_left hge1]
    rw [hDiv, hMod, hren1, hren2]
  exact ⟨Char.ofNat (0x10000 + a * 1024 + b), rfl,
    hHelper _ (char_toNat_ofNat_valid (Or.inr ⟨hGtDfff, hLtMax⟩))⟩

private theorem unicodeHex_char_spec {u1 : Nat} {cas1 : HexCase4} {h4_1 : List Char}
    (hu1Lt : u1 < 0x10000)
    (hhi : ¬(0xD800 ≤ u1 ∧ u1 < 0xDC00)) (hlo : ¬(0xDC00 ≤ u1 ∧ u1 < 0xE000))
    (hren1 : renderHex4 cas1 u1 = h4_1) :
    ∃ outC : Char,
      Char.ofNat u1 = outC ∧
      renderCharWithStyle outC (.unicodeHex cas1) = some h4_1 := by
  have hVal : u1 < 0xd800 ∨ (0xdfff < u1 ∧ u1 < 0x110000) := by
    by_cases h : u1 < 0xD800
    · exact Or.inl h
    · have hge1 : 0xD800 ≤ u1 := Nat.not_lt.mp h
      have hge2 : 0xDC00 ≤ u1 := Nat.not_lt.mp (fun hlt => hhi ⟨hge1, hlt⟩)
      have hge3 : 0xE000 ≤ u1 := Nat.not_lt.mp (fun hlt => hlo ⟨hge2, hlt⟩)
      exact Or.inr ⟨Nat.lt_of_lt_of_le (by decide : 0xdfff < 0xE000) hge3,
        Nat.lt_trans hu1Lt (by decide : 0x10000 < 0x110000)⟩
  have hHelper : ∀ (outC : Char), outC.toNat = u1 →
      renderCharWithStyle outC (.unicodeHex cas1) = some h4_1 := by
    intro outC hout
    unfold renderCharWithStyle; dsimp only
    rw [hout, ite_eq_left hu1Lt, hren1]
  exact ⟨Char.ofNat u1, rfl, hHelper _ (char_toNat_ofNat_valid hVal)⟩

private theorem parseUnicodeEscape_complete {bytes : ByteArray} {pos endPos : Nat}
    {rest : List Char} {pref : List Char} {s : String}
    (hlt1 : pos + 1 < bytes.size) (heU : (bytes[pos + 1]'hlt1 == 0x75) = true)
    (hs1 : ByteSliceAt bytes (pos + 1) rest)
    (ihStep : ∀ (r' : List Char) (outC : Char) (p' : Nat),
      r'.length < rest.length + 1 →
      ByteSliceAt bytes p' r' →
      parseStringBody bytes p' (pref ++ [outC]).utf8Encode = .ok (s, endPos) →
      ∃ parsed styles body after,
        s = String.ofList ((pref ++ [outC]) ++ parsed) ∧
        r' = body ++ '"' :: after ∧
        renderStringChars parsed styles = some body ∧
        ByteSliceAt bytes endPos after)
    (hParse :
      (match parseHex4? bytes (pos + 2) with
       | none => Except.error "invalid \\u escape sequence"
       | some u1 =>
         if 0xD800 ≤ u1 && u1 < 0xDC00 then
           let paired? : Option Nat :=
             if hPair : pos + 12 ≤ bytes.size then
               if bytes[pos + 6] == 0x5c && bytes[pos + 7] == 0x75 then
                 match parseHex4? bytes (pos + 8) with
                 | some u2 =>
                   if 0xDC00 ≤ u2 && u2 < 0xE000 then
                     some (0x10000 + (u1 - 0xD800) * 1024 + (u2 - 0xDC00))
                   else none
                 | none => none
               else none
             else none
           match paired? with
           | some cp => parseStringBody bytes (pos + 12) (pushUtf8Char pref.utf8Encode (Char.ofNat cp))
           | none => Except.error "unpaired high UTF-16 surrogate in string"
         else if 0xDC00 ≤ u1 && u1 < 0xE000 then
           Except.error "lone low UTF-16 surrogate in string"
         else parseStringBody bytes (pos + 6) (pushUtf8Char pref.utf8Encode (Char.ofNat u1))) =
      .ok (s, endPos)) :
    ∃ parsed styles body after,
      s = String.ofList (pref ++ parsed) ∧
      ('\\' :: rest) = body ++ '"' :: after ∧
      renderStringChars parsed styles = some body ∧
      ByteSliceAt bytes endPos after := by
  have hbUEq : bytes[pos + 1]'hlt1 = 0x75 := beq_iff_eq.mp heU
  obtain ⟨uCh, rAfterU, hrestU, huNat, _, hs2⟩ :=
    byteSliceAt_head_lt_128 hs1 hlt1 (by rw [hbUEq]; decide)
  have huEq : uCh = 'u' := by
    apply Char.ext; apply UInt32.toNat_inj.mp
    change uCh.toNat = ('u').toNat; rw [huNat, hbUEq]; rfl
  subst huEq
  have hs2' : ByteSliceAt bytes (pos + 2) rAfterU := by simpa [Nat.add_assoc] using hs2
  cases hhex1 : parseHex4? bytes (pos + 2) with
  | none => rw [hhex1] at hParse; cases hParse
  | some u1 =>
    rw [hhex1] at hParse; dsimp only at hParse
    obtain ⟨cas1, c0, c1, c2, c3, rAfter6, hu1Lt, hrU4, hren4_1, hs6⟩ :=
      parseHex4?_complete hs2' hhex1
    have hs6' : ByteSliceAt bytes (pos + 6) rAfter6 := by simpa [Nat.add_assoc] using hs6
    by_cases hhi : (0xD800 ≤ u1 && u1 < 0xDC00) = true
    · rw [ite_eq_left hhi] at hParse
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hhi
      by_cases hPairBnd : pos + 12 ≤ bytes.size
      · simp only [hPairBnd, ↓reduceDIte] at hParse
        by_cases hbu2 : (bytes[pos + 6] == 0x5c && bytes[pos + 7] == 0x75) = true
        · rw [ite_eq_left hbu2] at hParse
          simp only [Bool.and_eq_true, beq_iff_eq] at hbu2
          obtain ⟨bs2, rAfter7, hr6Eq, hbs2Nat, _, hs7⟩ :=
            byteSliceAt_head_lt_128 hs6' (by omega) (by rw [hbu2.1]; decide)
          have hbs2Eq : bs2 = '\\' := by
            apply Char.ext; apply UInt32.toNat_inj.mp; change bs2.toNat = ('\\').toNat; rw [hbs2Nat, hbu2.1]; rfl
          subst hbs2Eq
          have hs7' : ByteSliceAt bytes (pos + 7) rAfter7 := by simpa [Nat.add_assoc] using hs7
          obtain ⟨uch2, rAfter8, hr7Eq, huch2Nat, _, hs8⟩ :=
            byteSliceAt_head_lt_128 hs7' (by omega) (by rw [hbu2.2]; decide)
          have huch2Eq : uch2 = 'u' := by
            apply Char.ext; apply UInt32.toNat_inj.mp; change uch2.toNat = ('u').toNat; rw [huch2Nat, hbu2.2]; rfl
          subst huch2Eq
          have hs8' : ByteSliceAt bytes (pos + 8) rAfter8 := by simpa [Nat.add_assoc] using hs8
          cases hhex2 : parseHex4? bytes (pos + 8) with
          | none => rw [hhex2] at hParse; cases hParse
          | some u2 =>
            rw [hhex2] at hParse; dsimp only at hParse
            by_cases hlo : (0xDC00 ≤ u2 && u2 < 0xE000) = true
            · rw [ite_eq_left hlo] at hParse; dsimp only at hParse
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hlo
              obtain ⟨cas2, e0, e1, e2, e3, rAfter12, _, hr8Eq, hren4_2, hs12⟩ :=
                parseHex4?_complete hs8' hhex2
              have hs12' : ByteSliceAt bytes (pos + 12) rAfter12 := by simpa [Nat.add_assoc] using hs12
              obtain ⟨outC, houtC, hrenSt⟩ := surrogatePair_char_spec hhi hlo hren4_1 hren4_2
              rw [houtC, pushUtf8Char_eq_utf8Encode, ← List.utf8Encode_append] at hParse
              have hltLen : rAfter12.length < rest.length + 1 := by
                subst hrestU hrU4 hr6Eq hr7Eq hr8Eq; simp; omega
              obtain ⟨pTl, stTl, bTl, after, hsEq, hrEq, hrenTl, hEndSl⟩ :=
                ihStep rAfter12 outC (pos + 12) hltLen hs12' hParse
              refine ⟨outC :: pTl, .surrogatePair cas1 cas2 :: stTl,
                (['\\', 'u', c0, c1, c2, c3] ++ ['\\', 'u', e0, e1, e2, e3]) ++ bTl, after,
                by simpa [List.append_assoc] using hsEq, ?_, ?_, hEndSl⟩
              · subst hrestU hrU4 hr6Eq hr7Eq hr8Eq; simp [hrEq]
              · simp [renderStringChars, hrenSt, hrenTl, bind, Option.bind]
            · rw [ite_eq_right hlo] at hParse; cases hParse
        · rw [ite_eq_right hbu2] at hParse; cases hParse
      · simp only [hPairBnd, ↓reduceDIte] at hParse; cases hParse
    · rw [ite_eq_right hhi] at hParse
      by_cases hloLone : (0xDC00 ≤ u1 && u1 < 0xE000) = true
      · rw [ite_eq_left hloLone] at hParse; cases hParse
      · rw [ite_eq_right hloLone] at hParse
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hhi hloLone
        obtain ⟨outC, houtC, hrenSt⟩ := unicodeHex_char_spec hu1Lt hhi hloLone hren4_1
        rw [houtC, pushUtf8Char_eq_utf8Encode, ← List.utf8Encode_append] at hParse
        have hltLen : rAfter6.length < rest.length + 1 := by
          subst hrestU hrU4; simp; omega
        obtain ⟨pTl, stTl, bTl, after, hsEq, hrEq, hrenTl, hEndSl⟩ :=
          ihStep rAfter6 outC (pos + 6) hltLen hs6' hParse
        refine ⟨outC :: pTl, .unicodeHex cas1 :: stTl,
          ['\\', 'u', c0, c1, c2, c3] ++ bTl, after,
          by simpa [List.append_assoc] using hsEq, ?_, ?_, hEndSl⟩
        · subst hrestU hrU4; simp [hrEq]
        · simp [renderStringChars, hrenSt, hrenTl, bind, Option.bind]

/-- Completeness of `parseStringBody` over a valid UTF-8 slice `ByteSliceAt bytes pos cs`. -/
theorem parseStringBody_complete :
    ∀ (n : Nat) (cs : List Char) {bytes : ByteArray} {pos endPos : Nat} (pref : List Char) {s : String},
      cs.length ≤ n →
      ByteSliceAt bytes pos cs →
      parseStringBody bytes pos pref.utf8Encode = .ok (s, endPos) →
      ∃ (parsed : List Char) (styles : List CharEscapeStyle) (body after : List Char),
        s = String.ofList (pref ++ parsed) ∧
        cs = body ++ '"' :: after ∧
        renderStringChars parsed styles = some body ∧
        ByteSliceAt bytes endPos after := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cs bytes pos endPos pref s hlen hSlice hParse
    cases cs with
    | nil =>
      have heq := byteSliceAt_nil_eq_size hSlice
      unfold parseStringBody at hParse
      have hnot : ¬(pos < bytes.size) := by omega
      simp [hnot] at hParse
    | cons c rest =>
      have hlt0 := byteSliceAt_cons_lt_size hSlice
      by_cases hq : c = '"'
      · subst hq
        obtain ⟨_, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
        unfold parseStringBody at hParse
        have hb0 : ('"').val.toUInt8 = 0x22 := rfl
        simp only [hlt0, ↓reduceDIte, hg0, hb0, beq_self_eq_true, ↓reduceIte] at hParse
        cases hf : String.fromUTF8? pref.utf8Encode <;> simp [hf] at hParse
        rcases hParse with ⟨rfl, rfl⟩
        have hEq := String.toByteArray_inj.mp ((fromUTF8?_eq_some_iff.mp hf).symm.trans String.toByteArray_ofList.symm)
        exact ⟨[], [], [], rest, by simpa using hEq, rfl, rfl, hs1⟩
      · by_cases hctrl : c.toNat < 0x20
        · obtain ⟨_, hg0, _⟩ := byteSliceAt_ascii_cons hSlice (by omega)
          have hbLt : c.val.toUInt8 < 0x20 := by
            rw [UInt8.lt_iff_toNat_lt, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]
            exact hctrl
          have hne22 : (c.val.toUInt8 == 0x22) = false := by
            apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8,
              Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]
            change c.toNat ≠ 0x22; omega
          unfold parseStringBody at hParse
          simp only [hlt0, ↓reduceDIte, hg0, hne22, hbLt, Bool.false_eq_true, ↓reduceIte] at hParse
          cases hParse
        · by_cases hbs : c = '\\'
          · subst hbs
            obtain ⟨_, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
            unfold parseStringBody at hParse
            have hb0 : ('\\').val.toUInt8 = 0x5c := rfl
            simp only [hlt0, ↓reduceDIte, hg0, hb0,
              (by decide : ((0x5c : UInt8) == 0x22) = false),
              (by decide : ¬((0x5c : UInt8) < 0x20)),
              beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hParse
            split at hParse <;> try cases hParse
            rename_i hlt1
            let escByte := bytes[pos + 1]'hlt1
            rcases decodeShortEscapeByte escByte with hNone | ⟨outCh, chByte, hSome, hesc80, hout80, hchEq, hrc⟩
            · dsimp only [escByte] at hNone
              rw [hNone] at hParse
              dsimp only at hParse
              by_cases heU : (bytes[pos + 1]'hlt1 == 0x75) = true
              · simp only [heU, ↓reduceIte] at hParse
                exact parseUnicodeEscape_complete hlt1 heU hs1
                  (fun r' outC p' hltR hsR hpR =>
                    ih r'.length (by simp at hlen; omega) r' (pref ++ [outC]) (Nat.le_refl _) hsR hpR)
                  hParse
              · simp [heU] at hParse
            · dsimp only [escByte] at hSome
              rw [hSome] at hParse
              dsimp only at hParse
              obtain ⟨escC, rAfterEsc, hrestEq, hescNat, _, hs2⟩ := byteSliceAt_head_lt_128 hs1 hlt1 hesc80
              have hescEq : Char.ofNat escByte.toNat = escC := by
                apply Char.ext; apply UInt32.toNat_inj.mp
                change (Char.ofNat escByte.toNat).toNat = escC.toNat
                rw [char_toNat_ofNat_valid (Or.inl (by have : escByte.toNat < 128 := UInt8.lt_iff_toNat_lt.mp hesc80; omega)), hescNat]
              rw [hescEq] at hrc
              have hc1 : outCh.utf8Size = 1 := by
                simp only [Char.utf8Size]
                have hle : outCh.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change outCh.toNat ≤ 0x7f; omega
                simp [hle]
              have hpush : pref.utf8Encode.push chByte = (pref ++ [outCh]).utf8Encode := by
                rw [← hchEq, ← ByteArray.append_toByteArray_singleton, ← String.utf8EncodeChar_eq_singleton hc1,
                  ← List.utf8Encode_singleton, ← List.utf8Encode_append]
              rw [hpush] at hParse
              have hs2' : ByteSliceAt bytes (pos + 2) rAfterEsc := by simpa [Nat.add_assoc] using hs2
              have hltLen : rAfterEsc.length < n := by subst hrestEq; simp at hlen; omega
              obtain ⟨pTl, stTl, bTl, after, hsEq, hrEq, hrenTl, hEndSl⟩ :=
                ih rAfterEsc.length hltLen rAfterEsc (pref ++ [outCh]) (Nat.le_refl _) hs2' hParse
              refine ⟨outCh :: pTl, .shortEscape :: stTl, ['\\', escC] ++ bTl, after,
                by simpa [List.append_assoc] using hsEq, ?_, ?_, hEndSl⟩
              · subst hrestEq; simp [hrEq]
              · simp [renderStringChars, hrc, hrenTl, bind, Option.bind]
          · obtain ⟨hEqRaw, hsNext⟩ := parseStringBody_rawChar_step hSlice pref.utf8Encode (by omega) hq hbs
            rw [hEqRaw, ← List.utf8Encode_append] at hParse
            have hltLen : rest.length < n := by simp at hlen; omega
            obtain ⟨pTl, stTl, bTl, after, hsEq, hrEq, hrenTl, hEndSl⟩ :=
              ih rest.length hltLen rest (pref ++ [c]) (Nat.le_refl _) hsNext hParse
            have hrenSt : renderCharWithStyle c .raw = some [c] := by
              simp [renderCharWithStyle, show 0x20 ≤ c.toNat by omega, hq, hbs]
            refine ⟨c :: pTl, .raw :: stTl, [c] ++ bTl, after,
              by simpa [List.append_assoc] using hsEq, by simp [hrEq], ?_, hEndSl⟩
            simp [renderStringChars, hrenSt, hrenTl, bind, Option.bind]

/-- Completeness of `parseStringAt` on `ByteSliceAt`, producing `styles` and `lit` for `renderStringLiteral`. -/
theorem parseStringAt_complete {bytes : ByteArray} {pos : Nat} {cs : List Char}
    {s : String} {pSub : { p : Nat // pos < p ∧ p ≤ bytes.size }}
    (hSlice : ByteSliceAt bytes pos cs) (hParse : parseStringAt bytes pos = .ok (s, pSub)) :
    ∃ (styles : List CharEscapeStyle) (lit : String) (after : List Char),
      cs = lit.toList ++ after ∧
      renderStringLiteral s styles = some lit ∧
      ByteSliceAt bytes pSub.1 after := by
  unfold parseStringAt at hParse
  split at hParse <;> try cases hParse
  rename_i hlt0
  by_cases hq : (bytes[pos]'hlt0 == 0x22) = true
  · simp only [hq, ↓reduceIte] at hParse
    have hbEq := beq_iff_eq.mp hq
    obtain ⟨qCh, rest, rfl, hqNat, _, hs1⟩ :=
      byteSliceAt_head_lt_128 hSlice hlt0 (by rw [hbEq]; decide)
    have hqCh : qCh = '"' := by
      apply Char.ext; apply UInt32.toNat_inj.mp; change qCh.toNat = ('"').toNat; rw [hqNat, hbEq]; rfl
    subst hqCh
    match hbody : parseStringBody bytes (pos + 1) ByteArray.empty with
    | .error _ => simp [hbody] at hParse
    | .ok ⟨sOut, endPos⟩ =>
      rw [hbody] at hParse; dsimp only at hParse
      split at hParse <;> simp at hParse
      rcases hParse with ⟨rfl, rfl⟩
      rw [← List.utf8Encode_nil] at hbody
      obtain ⟨parsed, styles, body, after, hsEq, hrEq, hren, hAfterSl⟩ :=
        parseStringBody_complete rest.length rest [] (Nat.le_refl _) hs1 hbody
      simp only [List.nil_append] at hsEq
      refine ⟨styles, "\"" ++ String.ofList body ++ "\"", after, ?_, ?_, hAfterSl⟩
      · simp [hrEq, String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl]
      · simp [renderStringLiteral, hsEq, String.toList_ofList, hren, bind, Option.bind]
  · simp [hq] at hParse

end LeanSwe.Json.Proofs

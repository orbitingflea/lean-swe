import Lean.Data.Json.Basic
import LeanSwe.Json.Impl.Format
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `!s.contains ch = true` holds iff `ch ∉ s.toList`. -/
theorem not_contains_char_iff {s : String} {ch : Char} :
    !s.contains ch = true ↔ ch ∉ s.toList := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, String.contains_char_eq, decide_eq_true_eq]

/-- `!s.isEmpty = true` holds iff `s.toList ≠ []`. -/
theorem not_isEmpty_iff {s : String} :
    !s.isEmpty = true ↔ s.toList ≠ [] := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, String.isEmpty_iff, Ne]
  exact ⟨fun h heq => h (String.ext heq), fun h heq => h (congrArg String.toList heq)⟩

/-- `s.startsWith "{"` reduces to `c == '{'` whenever `s.toList = c :: tl`. -/
theorem startsWith_openBrace_of_toList_cons {s : String} {c : Char} {tl : List Char}
    (h : s.toList = c :: tl) : s.startsWith "{" = (c == '{') := by
  have hOpen : "{".toList = ['{'] := rfl
  by_cases hc : c = '{'
  · subst hc
    simp only [beq_self_eq_true, String.startsWith_string_iff, hOpen, h]
    exact ⟨tl, rfl⟩
  · rw [beq_false_of_ne hc, String.startsWith_string_eq_false_iff, hOpen, h]
    rintro ⟨t, ht⟩
    injection ht with heq _
    exact hc heq.symm

/-- `!s.contains ch = true` for any delimiter-wrapped string `s.toList = l :: (mid ++ [r])`. -/
theorem not_contains_of_toList_wrap {s : String} {l r ch : Char} {mid : List Char}
    (h : s.toList = l :: (mid ++ [r])) (hl : ch ≠ l) (hr : ch ≠ r)
    (hmid : ch ∉ mid) : !s.contains ch = true := by
  rw [not_contains_char_iff, h, List.mem_cons]
  rintro (heq | hrest)
  · exact hl heq
  · rcases List.mem_append.mp hrest with hm | hsing
    · exact hmid hm
    · simp only [List.mem_singleton] at hsing
      exact hr hsing

/-- Canonical escape style chosen by `escapeCharChars` for each `Char`. -/
def canonicalCharStyle (c : Char) : CharEscapeStyle :=
  if c == '"' || c == '\\' || c == '\n' || c == '\r' then .shortEscape
  else if 0x0020 ≤ c.toNat then .raw
  else .unicodeHex {}

/-- `hexDigitLower` agrees with `renderHexNibble false`. -/
theorem hexDigitLower_eq (n : Nat) : hexDigitLower n = renderHexNibble false n := rfl

/-- `escapeCharChars c` equals `canonicalEscapeChar c` for all `c`. -/
theorem escapeCharChars_eq_canonical (c : Char) :
    escapeCharChars c = canonicalEscapeChar c := rfl

/-- `renderString s ""` equals `canonicalStringLit s`. -/
theorem renderString_eq_canonicalStringLit (s : String) :
    renderString s "" = canonicalStringLit s := by
  have hfn : escapeCharChars = canonicalEscapeChar := funext escapeCharChars_eq_canonical
  simp [renderString, canonicalStringLit, hfn]

/-- `renderCharWithStyle c (canonicalCharStyle c)` emits `some (escapeCharChars c)` and contains no `\n` or `\r`. -/
theorem renderCharWithStyle_canonical (c : Char) :
    renderCharWithStyle c (canonicalCharStyle c) = some (escapeCharChars c) ∧
      ∀ ch ∈ escapeCharChars c, ch ≠ '\n' ∧ ch ≠ '\r' := by
  unfold canonicalCharStyle escapeCharChars
  by_cases hq : c == '"'
  · rw [beq_iff_eq.mp hq]; decide
  · by_cases hb : c == '\\'
    · rw [beq_iff_eq.mp hb]; decide
    · by_cases hn : c == '\n'
      · rw [beq_iff_eq.mp hn]; decide
      · by_cases hr : c == '\r'
        · rw [beq_iff_eq.mp hr]; decide
        · simp only [hq, hb, hn, hr, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
          by_cases hge : 0x0020 ≤ c.toNat
          · simp only [hge, ↓reduceIte, renderCharWithStyle]
            have hc1 : (c != '"') = true := bne_iff_ne.mpr (fun h => hq (beq_iff_eq.mpr h))
            have hc2 : (c != '\\') = true := bne_iff_ne.mpr (fun h => hb (beq_iff_eq.mpr h))
            simp only [decide_true, hc1, hc2, Bool.and_self, ↓reduceIte]
            refine ⟨trivial, fun ch hmem => ?_⟩
            simp only [List.mem_singleton] at hmem; subst hmem
            exact ⟨fun h => hn (beq_iff_eq.mpr h), fun h => hr (beq_iff_eq.mpr h)⟩
          · simp only [hge, ↓reduceIte, renderCharWithStyle]
            have hltBmp : c.toNat < 0x10000 := by omega
            have h0 : (c.toNat / 4096) % 16 = c.toNat / 4096 := by omega
            have h1 : (c.toNat / 256) % 16 = (c.toNat % 4096) / 256 := by omega
            have h2 : (c.toNat / 16) % 16 = (c.toNat % 256) / 16 := by omega
            simp only [hltBmp, ↓reduceIte, renderHex4, h0, h1, h2, hexDigitLower_eq, true_and]
            have hNibSafe : ∀ k, k < 16 → renderHexNibble false k ≠ '\n' ∧ renderHexNibble false k ≠ '\r' := by
              intro k hk
              match k with
              | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
              | _ + 16 => omega
            intro ch hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
            · decide
            · decide
            · exact hNibSafe _ (by omega)
            · exact hNibSafe _ (by omega)
            · exact hNibSafe _ (by omega)
            · exact hNibSafe _ (Nat.mod_lt _ (by decide))

/-- `renderString s ""` is witnessed by `renderStringLiteral` and is non-empty, single-line, and starts with `'"'`. -/
theorem renderString_spec (s : String) :
    let out := renderString s ""
    !out.isEmpty = true ∧ !out.contains '\n' = true ∧ !out.contains '\r' = true ∧
      out.startsWith "{" = false ∧
      ∃ styles, renderStringLiteral s styles = some out := by
  have hBody : ∀ cs : List Char,
      renderStringChars cs (cs.map canonicalCharStyle) = some (cs.flatMap escapeCharChars) ∧
        ∀ ch ∈ cs.flatMap escapeCharChars, ch ≠ '\n' ∧ ch ≠ '\r' := by
    intro cs
    induction cs with
    | nil => simp [renderStringChars]
    | cons c tl ih =>
      obtain ⟨hcRen, hcSafe⟩ := renderCharWithStyle_canonical c
      refine ⟨by simp [renderStringChars, hcRen, ih.1, bind, Option.bind], ?_⟩
      intro ch hmem
      simp only [List.flatMap_cons, List.mem_append] at hmem
      exact hmem.elim (hcSafe ch) (ih.2 ch)
  obtain ⟨hRenChars, hSafeChars⟩ := hBody s.toList
  let body := s.toList.flatMap escapeCharChars
  let out := "\"" ++ String.ofList body ++ "\""
  have houtEq : renderString s "" = out := by simp [renderString, out, body]
  have houtList : out.toList = '"' :: (body ++ ['"']) := by
    simp [out, String.toList_append, String.toList_ofList]
  rw [houtEq]
  refine ⟨not_isEmpty_iff.mpr (by rw [houtList]; simp),
    not_contains_of_toList_wrap houtList (by decide) (by decide) (fun h => (hSafeChars '\n' h).1 rfl),
    not_contains_of_toList_wrap houtList (by decide) (by decide) (fun h => (hSafeChars '\r' h).2 rfl),
    startsWith_openBrace_of_toList_cons houtList,
    s.toList.map canonicalCharStyle, ?_⟩
  simp [renderStringLiteral, hRenChars, out, body, bind, Option.bind]

/-- `countDigitsAux` equals `modelCountDigitsAux`. -/
theorem countDigitsAux_eq_model (n digits : Nat) :
    countDigitsAux n digits = modelCountDigitsAux n digits := by
  unfold countDigitsAux modelCountDigitsAux
  by_cases h : n ≤ 9
  · simp [h]
  · simp [h, countDigitsAux_eq_model (n / 10) (digits + 1)]
termination_by n

/-- `jsonNumberToString n` equals `canonicalNumString n`. -/
theorem jsonNumberToString_eq_canonical (n : Lean.JsonNumber) :
    jsonNumberToString n = canonicalNumString n := by
  rcases n with ⟨m, e⟩
  by_cases hm0 : m = 0
  · subst hm0; rfl
  · cases e with
    | zero => simp [jsonNumberToString, canonicalNumString]
    | succ e' =>
      simp only [jsonNumberToString, canonicalNumString,
        countDigits, countDigitsAux_eq_model, formatFracStr, dropTrailingZeroChars]

/-- Upper bound `n < 10 ^ (countDigitsAux n d - d + 1)` and monotonicity `d ≤ countDigitsAux n d`. -/
theorem countDigitsAux_bounds (n d : Nat) :
    d ≤ countDigitsAux n d ∧ n < 10 ^ (countDigitsAux n d - d + 1) := by
  unfold countDigitsAux
  by_cases h : n ≤ 9
  · simp only [h, ↓reduceDIte, Nat.sub_self, Nat.zero_add, Nat.pow_one]
    exact ⟨Nat.le_refl _, by omega⟩
  · simp only [h, ↓reduceDIte]
    obtain ⟨hle, hlt⟩ := countDigitsAux_bounds (n / 10) (d + 1)
    refine ⟨by omega, ?_⟩
    have hexp : countDigitsAux (n / 10) (d + 1) - d + 1 =
        (countDigitsAux (n / 10) (d + 1) - (d + 1) + 1) + 1 := by omega
    rw [hexp, Nat.pow_succ]
    omega
termination_by n

/-- `n < 10 ^ countDigits n` for every natural number `n`. -/
theorem lt_pow10_countDigits (n : Nat) : n < 10 ^ countDigits n := by
  obtain ⟨hle, hlt⟩ := countDigitsAux_bounds n 1
  unfold countDigits
  have hexp : countDigitsAux n 1 - 1 + 1 = countDigitsAux n 1 := by omega
  rwa [hexp] at hlt

private theorem toDigitsCore_step' (f n : Nat) (ds : List Char) :
    Nat.toDigitsCore 10 (f + 1) n ds =
      if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
      else Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: ds) := rfl

/-- Upper bound `(Nat.toDigits 10 rem).length ≤ k` for `0 < rem < 10 ^ k`. -/
theorem toDigits_length_le_of_lt_pow10 {rem k : Nat} (hrpos : 0 < rem) (hrem : rem < 10 ^ k) :
    (Nat.toDigits 10 rem).length ≤ k := by
  have hne : ∀ (f' m' : Nat) (a' : List Char),
      m' < f' → 1 + a'.length ≤ (Nat.toDigitsCore 10 f' m' a').length := by
    intro f'
    induction f' with
    | zero => intros; omega
    | succ f'' ih2 =>
      intro m' a' hm'
      rw [toDigitsCore_step']
      generalize Nat.digitChar (m' % 10) = dc
      by_cases hq' : m' / 10 = 0
      · rw [ite_eq_left hq']; simp; omega
      · rw [ite_eq_right hq']
        have := ih2 (m' / 10) (dc :: a') (by omega)
        simp at this; omega
  have hPow : ∀ (fuel m : Nat) (acc : List Char), 0 < m → m < fuel →
      10 ^ ((Nat.toDigitsCore 10 fuel m acc).length - acc.length - 1) ≤ m := by
    intro fuel
    induction fuel with
    | zero => intros; omega
    | succ f ih =>
      intro m acc hm0 hmf
      rw [toDigitsCore_step']
      generalize Nat.digitChar (m % 10) = dc
      by_cases hq : m / 10 = 0
      · rw [ite_eq_left hq, List.length_cons]
        have hsub : acc.length + 1 - acc.length - 1 = 0 := by omega
        rw [hsub, Nat.pow_zero]; omega
      · rw [ite_eq_right hq]
        have hih := ih (m / 10) (dc :: acc) (by omega) (by omega)
        simp only [List.length_cons] at hih
        have hlenGe := hne f (m / 10) (dc :: acc) (by omega)
        simp only [List.length_cons] at hlenGe
        have hexp : (Nat.toDigitsCore 10 f (m / 10) (dc :: acc)).length - acc.length - 1 =
            ((Nat.toDigitsCore 10 f (m / 10) (dc :: acc)).length - (acc.length + 1) - 1) + 1 := by omega
        rw [hexp, Nat.pow_succ]
        have := Nat.mul_le_mul_right 10 hih
        omega
  have h1 := hPow (rem + 1) rem [] hrpos (by omega)
  simp only [List.length_nil, Nat.sub_zero] at h1
  apply Decidable.byContradiction
  intro hgt
  have hkLe : k ≤ (Nat.toDigits 10 rem).length - 1 := by omega
  have hpowLe : 10 ^ k ≤ 10 ^ ((Nat.toDigits 10 rem).length - 1) := Nat.pow_le_pow_right (by decide) hkLe
  unfold Nat.toDigits at hpowLe
  omega

/-- Append decomposition for `parseDecDigitsLoop`. -/
theorem parseDecDigitsLoop_append (acc : Nat) (xs ys : List Char) :
    parseDecDigitsLoop acc (xs ++ ys) = parseDecDigitsLoop (parseDecDigitsLoop acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c tl ih => simp [ih]

/-- `parseDecDigitsLoop acc (List.replicate t '0')` equals `acc * (10 ^ t)`. -/
theorem parseDecDigitsLoop_replicate_zero (acc t : Nat) :
    parseDecDigitsLoop acc (List.replicate t '0') = acc * (10 ^ t) := by
  induction t generalizing acc with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, parseDecDigitsLoop_cons,
      show ('0').toNat - 0x30 = 0 from rfl, Nat.add_zero, ih, Nat.pow_succ]
    rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k), ← Nat.mul_assoc]

/-- Decomposition of `dropTrailingZeroChars` on a positive all-digit sequence. -/
theorem dropTrailingZeroChars_props {padded : List Char}
    (hall : padded.all isAsciiDigit = true) (hpos : 0 < parseDecDigitsLoop 0 padded) :
    let trimmed := dropTrailingZeroChars padded
    !trimmed.isEmpty = true ∧
      trimmed.all isAsciiDigit = true ∧
      ∃ t, padded = trimmed ++ List.replicate t '0' := by
  have hRev : ∀ rev : List Char, rev.all isAsciiDigit = true →
      ∃ t, rev = List.replicate t '0' ++ rev.dropWhile (· == '0') ∧
        (rev.dropWhile (· == '0')).all isAsciiDigit = true := by
    intro rev hrev
    induction rev with
    | nil => exact ⟨0, rfl, rfl⟩
    | cons c tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrev
      by_cases hc0 : (c == '0') = true
      · rw [beq_iff_eq.mp hc0]
        obtain ⟨t, hEq, hAllD⟩ := ih hrev.2
        refine ⟨t + 1, ?_, by simpa [List.dropWhile_cons] using hAllD⟩
        simp only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte, List.replicate_succ, List.cons_append]
        exact congrArg ('0' :: ·) hEq
      · simp only [List.dropWhile_cons, hc0, Bool.false_eq_true, ↓reduceIte]
        exact ⟨0, rfl, by simp [hrev.1, hrev.2]⟩
  have hRevAll : padded.reverse.all isAsciiDigit = true := by
    rw [List.all_eq_true] at hall ⊢
    intro x hx; exact hall x (List.mem_reverse.mp hx)
  obtain ⟨t, hRevEq, hDropAll⟩ := hRev padded.reverse hRevAll
  let trimmed := (padded.reverse.dropWhile (· == '0')).reverse
  have hpaddedEq : padded = trimmed ++ List.replicate t '0' := by
    have := congrArg List.reverse hRevEq
    simpa [trimmed, List.reverse_append, List.reverse_replicate] using this
  have hTrimAll : trimmed.all isAsciiDigit = true := by
    rw [List.all_eq_true] at hDropAll ⊢
    intro x hx; exact hDropAll x (List.mem_reverse.mp hx)
  have hTrimNe : !trimmed.isEmpty = true := by
    cases htr : trimmed with
    | nil =>
      exfalso
      rw [htr, List.nil_append] at hpaddedEq
      rw [hpaddedEq, parseDecDigitsLoop_replicate_zero, Nat.zero_mul] at hpos
      omega
    | cons _ _ => rfl
  exact ⟨hTrimNe, hTrimAll, t, hpaddedEq⟩

end LeanSwe.Json.Proofs

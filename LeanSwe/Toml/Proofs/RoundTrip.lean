import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem normalizeChars_clean (cs : List Char)
    (h : cs.all (fun c => !isDisallowedControl c && c != '\r') = true) (line col : Nat) :
    normalizeChars line col cs = .ok cs := by
  induction cs generalizing line col with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    rcases h with ⟨⟨hc_ctrl, hc_cr⟩, hrest⟩
    have hrest' := ih hrest
    by_cases hnl : c = '\n'
    · subst hnl
      simp only [normalizeChars, hrest' (line + 1) 1, bind, Except.bind]
    · unfold normalizeChars
      split <;> rename_i heq
      · simp at heq
      · simp [hc_cr] at heq
      · simp [hc_cr] at heq
      · simp [hnl] at heq
      · cases heq
        simp only [hc_ctrl, Bool.false_eq_true, ↓reduceIte, hrest' line (col + 1), bind, Except.bind]

private theorem isBareKeyChar_lt_128 (c : Char) (h : isBareKeyChar c = true) : c.toNat < 128 := by
  simp only [isBareKeyChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h1) | h1)
  · have : c.toNat ≤ 'Z'.toNat := h2; have : 'Z'.toNat = 90 := rfl; omega
  · have : c.toNat ≤ 'z'.toNat := h2; have : 'z'.toNat = 122 := rfl; omega
  · have : c.toNat ≤ '9'.toNat := h2; have : '9'.toNat = 57 := rfl; omega
  · simp only [beq_iff_eq] at h1; subst h1; decide
  · simp only [beq_iff_eq] at h1; subst h1; decide

private theorem isBareKeyChar_clean_table :
    (List.range 128).all (fun n =>
      let c := Char.ofNat n
      !isBareKeyChar c ||
        (!isDisallowedControl c && c != '\r' && c != '\n' && !isHorizWs c &&
         c != '.' && c != '"' && c != '\'' && c != '#' && c != ',' && c != ']' && c != '}' && c != '=')) = true := by
  decide

private theorem isBareKeyChar_clean (c : Char) (h : isBareKeyChar c = true) :
    (!isDisallowedControl c && c != '\r' && c != '\n' && !isHorizWs c &&
     c != '.' && c != '"' && c != '\'' && c != '#' && c != ',' && c != ']' && c != '}' && c != '=') = true := by
  have hlt := isBareKeyChar_lt_128 c h
  have hmem := List.all_eq_true.mp isBareKeyChar_clean_table c.toNat (List.mem_range.mpr hlt)
  simp only [Char.ofNat_toNat, h, Bool.not_true, Bool.false_or] at hmem
  exact hmem

private theorem isSingleLineClean_implies_clean (s : String) (h : isSingleLineClean s = true) :
    s.toList.all (fun c => !isDisallowedControl c && c != '\r') = true := by
  simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h ⊢
  intro c hc
  have h1 := h c hc
  exact ⟨by simpa [Bool.not_eq_true'] using h1.1.1, h1.2⟩

private theorem isSingleLineClean_no_nl (s : String) (h : isSingleLineClean s = true)
    (c : Char) (hc : c ∈ s.toList) : c ≠ '\n' ∧ c ≠ '\r' ∧ (!isDisallowedControl c) = true := by
  simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h
  have h1 := h c hc
  exact ⟨h1.1.2, h1.2, by simpa [Bool.not_eq_true'] using h1.1.1⟩

private theorem hexDigitUpper_val_table :
    (List.range 16).all (fun n => hexVal? (hexDigitUpper n) == some n) = true := by
  decide

private theorem hexDigitUpper_clean_table :
    (List.range 16).all (fun n =>
      let c := hexDigitUpper n
      !isDisallowedControl c && c != '\r' && c != '\n' && c != '\\' && c != '"') = true := by
  decide

private theorem hexDigitUpper_val (n : Nat) (hn : n < 16) :
    hexVal? (hexDigitUpper n) = some n := by
  have h := List.all_eq_true.mp hexDigitUpper_val_table n (List.mem_range.mpr hn)
  simpa using h

private theorem hexDigitUpper_clean (n : Nat) (hn : n < 16) :
    (!isDisallowedControl (hexDigitUpper n) && hexDigitUpper n != '\r' &&
      hexDigitUpper n != '\n' && hexDigitUpper n != '\\' && hexDigitUpper n != '"') = true := by
  exact List.all_eq_true.mp hexDigitUpper_clean_table n (List.mem_range.mpr hn)

private theorem twoDigits_padNatZero_table :
    (List.range 100).all (fun n =>
      match (padNatZero 2 n).toList with
      | [c1, c2] =>
        !isDisallowedControl c1 && c1 != '\r' && c1 != '\n' && !isUnquotedDelim c1 &&
        !isDisallowedControl c2 && c2 != '\r' && c2 != '\n' && !isUnquotedDelim c2 &&
        twoDigitsNat? c1 c2 == some n
      | _ => false) = true := by
  decide

private theorem twoDigits_padNatZero (n : Nat) (hn : n < 100) :
    ∃ c1 c2, (padNatZero 2 n).toList = [c1, c2] ∧ twoDigitsNat? c1 c2 = some n ∧
      (!isDisallowedControl c1 && c1 != '\r' && c1 != '\n' && !isUnquotedDelim c1) = true ∧
      (!isDisallowedControl c2 && c2 != '\r' && c2 != '\n' && !isUnquotedDelim c2) = true := by
  have h := List.all_eq_true.mp twoDigits_padNatZero_table n (List.mem_range.mpr hn)
  cases hcs : (padNatZero 2 n).toList with
  | nil => simp [hcs] at h
  | cons c1 r1 =>
    cases r1 with
    | nil => simp [hcs] at h
    | cons c2 r2 =>
      cases r2 with
      | nil =>
        simp only [hcs, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
        exact ⟨c1, c2, rfl, h9, by simp [h1, h2, h3, h4], by simp [h5, h6, h7, h8]⟩
      | cons _ _ => simp [hcs] at h

private theorem toString_lt10_char (r : Nat) (hr : r < 10) :
    (toString r).toList = [Nat.digitChar r] ∧ isAsciiDigit (Nat.digitChar r) = true ∧
      digitVal (Nat.digitChar r) = r ∧
      (!isDisallowedControl (Nat.digitChar r) && Nat.digitChar r != '\r' &&
        Nat.digitChar r != '\n' && !isUnquotedDelim (Nat.digitChar r)) = true := by
  match r with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | r + 10 => omega

private theorem nat_toDigitsCore_acc (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [Nat.toDigitsCore]
  | succ f' ih =>
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    by_cases hdiv : n / 10 = 0
    · simp only [hdiv, ↓reduceIte, List.singleton_append]
    · simp only [hdiv, ↓reduceIte]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc), ih (n / 10) [Nat.digitChar (n % 10)],
        List.append_assoc, List.cons_append, List.nil_append]

private theorem toDigitsCore_fuel_mono (f1 f2 n : Nat) (hf1 : n < f1) (hf2 : n < f2) :
    Nat.toDigitsCore 10 f1 n [] = Nat.toDigitsCore 10 f2 n [] := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      rw [Nat.toDigitsCore, Nat.toDigitsCore]
      by_cases hdiv : n / 10 = 0
      · simp only [hdiv, ↓reduceIte]
      · simp only [hdiv, ↓reduceIte]
        have hlt1 : n / 10 < f1' := by omega
        have hlt2 : n / 10 < f2' := by omega
        rw [nat_toDigitsCore_acc f1' (n / 10) [Nat.digitChar (n % 10)],
          nat_toDigitsCore_acc f2' (n / 10) [Nat.digitChar (n % 10)],
          ih f2' (n / 10) hlt1 hlt2]

private theorem toString_two_digits_split (q r : Nat) (hq : 0 < q) (hr : r < 10) :
    (toString (q * 10 + r)).toList = (toString q).toList ++ [Nat.digitChar r] := by
  change (Nat.repr (q * 10 + r)).toList = (Nat.repr q).toList ++ [Nat.digitChar r]
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits]
  rw [Nat.toDigitsCore]
  have hq0 : q ≠ 0 := by omega
  have hdiv : (q * 10 + r) / 10 = q := by omega
  have hmod : (q * 10 + r) % 10 = r := by omega
  simp only [hdiv, hmod, hq0, ↓reduceIte]
  rw [nat_toDigitsCore_acc _ q [Nat.digitChar r],
    toDigitsCore_fuel_mono (q * 10 + r) (q + 1) q (by omega) (by omega)]

private theorem toString_digits_all_clean (n : Nat) :
    (toString n).toList.all (fun c =>
      isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (toString n).length ≥ 1 := by
  suffices h : ∀ k : Nat, ∀ m : Nat, m ≤ k →
      (toString m).toList.all (fun c =>
        isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
      (toString m).length ≥ 1 from h n n (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    decide
  | succ k' ih =>
    intro m hm
    by_cases h10 : m < 10
    · obtain ⟨hch, hd, _, hcl⟩ := toString_lt10_char m h10
      constructor
      · simp only [hch, List.all_cons, List.all_nil, Bool.and_true, hd]
        simpa [Bool.and_assoc] using hcl
      · change (toString m).toList.length ≥ 1
        rw [hch]; simp
    · have hq : 0 < m / 10 := by omega
      have hqm : m / 10 ≤ k' := by omega
      have hsplit := toString_two_digits_split (m / 10) (m % 10) hq (Nat.mod_lt m (by decide))
      have heqm : m / 10 * 10 + m % 10 = m := by omega
      rw [heqm] at hsplit
      obtain ⟨ih1, ih2⟩ := ih (m / 10) hqm
      obtain ⟨_, hd, _, hcl⟩ := toString_lt10_char (m % 10) (Nat.mod_lt m (by decide))
      constructor
      · simp only [hsplit, List.all_append, List.all_cons, List.all_nil, Bool.and_true, ih1, Bool.true_and, hd]
        simpa [Bool.and_assoc] using hcl
      · change (toString m).toList.length ≥ 1
        rw [hsplit]; simp

private theorem padNatZero_clean (w n : Nat) :
    (padNatZero w n).toList.all (fun c =>
      isAsciiDigit c && !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte, (toString_digits_all_clean n).1]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.all_append,
      (toString_digits_all_clean n).1, Bool.and_true, List.all_replicate]
    split <;> decide

private theorem padNatZero_length_of_toString_le (w n : Nat) (h : (toString n).length ≤ w) :
    (padNatZero w n).toList.length = w := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte]
    change (toString n).toList.length = w
    have hlen : (toString n).length = w := by omega
    simpa [String.length] using hlen
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.length_append,
      List.length_replicate]
    change w - (toString n).length + (toString n).length = w
    omega

private theorem toString_lt_pow10_len4 (y : Nat) (hy : y < 10000) : (toString y).length ≤ 4 := by
  have hlen_eq : (toString y).length = (toString y).toList.length := by
    change (Nat.repr y).length = (Nat.repr y).toList.length
    simp [Nat.repr]
  rw [hlen_eq]
  by_cases h1 : y < 10
  · obtain ⟨hch, _⟩ := toString_lt10_char y h1
    rw [hch]; simp
  · by_cases h2 : y < 100
    · have := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
      have heq : y / 10 * 10 + y % 10 = y := by omega
      rw [heq] at this
      obtain ⟨hch, _⟩ := toString_lt10_char (y / 10) (by omega)
      rw [this, hch]; simp
    · by_cases h3 : y < 1000
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        obtain ⟨hch, _⟩ := toString_lt10_char (y / 100) (by omega)
        rw [hs1, hs2, hch]; simp
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        have hs3 := toString_two_digits_split (y / 1000) ((y / 100) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq3 : y / 1000 * 10 + (y / 100) % 10 = y / 100 := by omega
        rw [heq3] at hs3
        obtain ⟨hch, _⟩ := toString_lt10_char (y / 1000) (by omega)
        rw [hs1, hs2, hs3, hch]; simp

private theorem fourDigitsNat?_of_digits (d1 d2 d3 d4 : Nat)
    (h1 : d1 < 10) (h2 : d2 < 10) (h3 : d3 < 10) (h4 : d4 < 10) :
    fourDigitsNat? (Nat.digitChar d1) (Nat.digitChar d2) (Nat.digitChar d3) (Nat.digitChar d4) =
      some (d1 * 1000 + d2 * 100 + d3 * 10 + d4) := by
  obtain ⟨_, hd1, hv1, _⟩ := toString_lt10_char d1 h1
  obtain ⟨_, hd2, hv2, _⟩ := toString_lt10_char d2 h2
  obtain ⟨_, hd3, hv3, _⟩ := toString_lt10_char d3 h3
  obtain ⟨_, hd4, hv4, _⟩ := toString_lt10_char d4 h4
  simp [fourDigitsNat?, hd1, hd2, hd3, hd4, hv1, hv2, hv3, hv4]
  omega

private theorem padNatZero_eq_of_toList (w n : Nat) (cs : List Char)
    (hcs : (toString n).toList = cs) (hlen : cs.length ≤ w) :
    (padNatZero w n).toList = List.replicate (w - cs.length) '0' ++ cs := by
  unfold padNatZero
  have hlen_str : (toString n).length = cs.length := by
    have h1 : (toString n).length = (toString n).toList.length := by
      change (Nat.repr n).length = (Nat.repr n).toList.length
      simp [Nat.repr]
    rw [h1, hcs]
  change (if (toString n).length ≥ w then toString n
    else String.ofList (List.replicate (w - (toString n).length) '0') ++ toString n).toList = _
  rw [hlen_str]
  by_cases hge : cs.length ≥ w
  · have hw : cs.length = w := by omega
    simp only [hge, ↓reduceIte]
    rw [hw, Nat.sub_self, List.replicate_zero, List.nil_append, hcs]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, hcs]

private theorem padNatZero_4_digits (y : Nat) (hy : y < 10000) :
    ∃ c1 c2 c3 c4, (padNatZero 4 y).toList = [c1, c2, c3, c4] ∧
      fourDigitsNat? c1 c2 c3 c4 = some y := by
  have h0 : Nat.digitChar 0 = '0' := rfl
  by_cases h1 : y < 10
  · obtain ⟨hc, _⟩ := toString_lt10_char y h1
    refine ⟨Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar y, ?_, ?_⟩
    · rw [padNatZero_eq_of_toList 4 y _ hc (by simp), h0]; rfl
    · rw [fourDigitsNat?_of_digits 0 0 0 y (by decide) (by decide) (by decide) h1]
      simp
  · by_cases h2 : y < 100
    · have hstr := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
      have heq : y / 10 * 10 + y % 10 = y := by omega
      rw [heq] at hstr
      obtain ⟨hca, _⟩ := toString_lt10_char (y / 10) (by omega)
      have hlist : (toString y).toList = [Nat.digitChar (y / 10), Nat.digitChar (y % 10)] := by
        rw [hstr, hca]; rfl
      refine ⟨Nat.digitChar 0, Nat.digitChar 0, Nat.digitChar (y / 10), Nat.digitChar (y % 10), ?_, ?_⟩
      · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp), h0]; rfl
      · rw [fourDigitsNat?_of_digits 0 0 (y / 10) (y % 10) (by decide) (by decide) (by omega) (Nat.mod_lt y (by decide))]
        simp [heq]
    · by_cases h3 : y < 1000
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        obtain ⟨hca, _⟩ := toString_lt10_char (y / 100) (by omega)
        have hlist : (toString y).toList =
            [Nat.digitChar (y / 100), Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10)] := by
          rw [hs1, hs2, hca]; rfl
        refine ⟨Nat.digitChar 0, Nat.digitChar (y / 100), Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10), ?_, ?_⟩
        · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp), h0]; rfl
        · rw [fourDigitsNat?_of_digits 0 (y / 100) ((y / 10) % 10) (y % 10)
            (by decide) (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt y (by decide))]
          apply congrArg some
          calc
            0 * 1000 + y / 100 * 100 + (y / 10) % 10 * 10 + y % 10
              = (y / 100 * 10 + (y / 10) % 10) * 10 + y % 10 := by rw [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
            _ = y / 10 * 10 + y % 10 := by rw [heq2]
            _ = y := heq1
      · have hs1 := toString_two_digits_split (y / 10) (y % 10) (by omega) (Nat.mod_lt y (by decide))
        have heq1 : y / 10 * 10 + y % 10 = y := by omega
        rw [heq1] at hs1
        have hs2 := toString_two_digits_split (y / 100) ((y / 10) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq2 : y / 100 * 10 + (y / 10) % 10 = y / 10 := by omega
        rw [heq2] at hs2
        have hs3 := toString_two_digits_split (y / 1000) ((y / 100) % 10) (by omega) (Nat.mod_lt _ (by decide))
        have heq3 : y / 1000 * 10 + (y / 100) % 10 = y / 100 := by omega
        rw [heq3] at hs3
        obtain ⟨hca, _⟩ := toString_lt10_char (y / 1000) (by omega)
        have hlist : (toString y).toList =
            [Nat.digitChar (y / 1000), Nat.digitChar ((y / 100) % 10),
             Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10)] := by
          rw [hs1, hs2, hs3, hca]; rfl
        refine ⟨Nat.digitChar (y / 1000), Nat.digitChar ((y / 100) % 10),
            Nat.digitChar ((y / 10) % 10), Nat.digitChar (y % 10), ?_, ?_⟩
        · rw [padNatZero_eq_of_toList 4 y _ hlist (by simp)]; rfl
        · rw [fourDigitsNat?_of_digits (y / 1000) ((y / 100) % 10) ((y / 10) % 10) (y % 10)
            (by omega) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt y (by decide))]
          apply congrArg some
          calc
            y / 1000 * 1000 + (y / 100) % 10 * 100 + (y / 10) % 10 * 10 + y % 10
              = ((y / 1000 * 10 + (y / 100) % 10) * 10 + (y / 10) % 10) * 10 + y % 10 := by
                  simp only [Nat.add_mul, Nat.mul_assoc]
            _ = (y / 100 * 10 + (y / 10) % 10) * 10 + y % 10 := by rw [heq3]
            _ = y / 10 * 10 + y % 10 := by rw [heq2]
            _ = y := heq1

private def utf8Sum : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + utf8Sum cs

private theorem utf8Sum_append (a b : List Char) :
    utf8Sum (a ++ b) = utf8Sum a + utf8Sum b := by
  induction a with
  | nil => simp [utf8Sum]
  | cons c cs ih => simp [utf8Sum, ih, Nat.add_assoc]

private theorem utf8ByteSize_ofList (cs : List Char) :
    (String.ofList cs).utf8ByteSize = utf8Sum cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih, utf8Sum]

private theorem utf8ByteSize_eq_utf8Sum (s : String) :
    s.utf8ByteSize = utf8Sum s.toList := by
  have h := utf8ByteSize_ofList s.toList
  simpa [String.ofList_toList] using h

private theorem utf8GetAux_append_add (a b : List Char) (i₀ : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ b) i₀ ⟨i₀.byteIdx + utf8Sum a⟩ =
      String.Pos.Raw.utf8GetAux b ⟨i₀.byteIdx + utf8Sum a⟩ ⟨i₀.byteIdx + utf8Sum a⟩ := by
  induction a generalizing i₀ with
  | nil => simp [utf8Sum]
  | cons c cs ih =>
    simp only [List.cons_append, utf8Sum]
    rw [String.Pos.Raw.utf8GetAux.eq_def]
    have hpos := Char.utf8Size_pos c
    have hne : i₀ ≠ ⟨i₀.byteIdx + (c.utf8Size + utf8Sum cs)⟩ := by
      intro heq
      have hidx : i₀.byteIdx = i₀.byteIdx + (c.utf8Size + utf8Sum cs) := congrArg String.Pos.Raw.byteIdx heq
      omega
    simp only [hne, ↓reduceIte]
    have hnext : i₀ + c = ⟨i₀.byteIdx + c.utf8Size⟩ := by
      apply String.Pos.Raw.ext
      exact String.Pos.Raw.byteIdx_add_char
    rw [hnext]
    have hadd : i₀.byteIdx + (c.utf8Size + utf8Sum cs) = (i₀.byteIdx + c.utf8Size) + utf8Sum cs := by omega
    rw [hadd]
    exact ih ⟨i₀.byteIdx + c.utf8Size⟩

private theorem get_at_utf8Sum (s : String) (a : List Char) (c : Char) (b : List Char)
    (h : s.toList = a ++ c :: b) :
    String.Pos.Raw.get s ⟨utf8Sum a⟩ = c ∧
    String.Pos.Raw.next s ⟨utf8Sum a⟩ = ⟨utf8Sum a + c.utf8Size⟩ ∧
    String.Pos.Raw.atEnd s ⟨utf8Sum a⟩ = false := by
  have hget : String.Pos.Raw.get s ⟨utf8Sum a⟩ = c := by
    change String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8Sum a⟩ = c
    rw [h]
    have h0 : (⟨utf8Sum a⟩ : String.Pos.Raw) = ⟨(0 : String.Pos.Raw).byteIdx + utf8Sum a⟩ := by
      simp [String.Pos.Raw.byteIdx_zero]
    rw [h0, utf8GetAux_append_add a (c :: b) 0, String.Pos.Raw.utf8GetAux.eq_def]
    simp
  refine ⟨hget, ?_, ?_⟩
  · apply String.Pos.Raw.ext
    change ((⟨utf8Sum a⟩ : String.Pos.Raw) + String.Pos.Raw.get s ⟨utf8Sum a⟩).byteIdx = utf8Sum a + c.utf8Size
    rw [hget]
    exact String.Pos.Raw.byteIdx_add_char
  · rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not]
    have hsz : s.utf8ByteSize = utf8Sum a + (c.utf8Size + utf8Sum b) := by
      rw [utf8ByteSize_eq_utf8Sum, h, utf8Sum_append, utf8Sum]
    have hpos := Char.utf8Size_pos c
    dsimp only
    omega

private theorem splitOnAux_length_ge (s sep : String) (b i j : String.Pos.Raw) (r : List String)
    (hj : j.byteIdx ≤ sep.utf8ByteSize) (hji : j.byteIdx ≤ i.byteIdx) :
    r.length + 1 ≤ (s.splitOnAux sep b i j r).length := by
  induction r_len_fuel :
      (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) +
        (sep.utf8ByteSize - j.byteIdx) + 1
      using Nat.strongRecOn generalizing b i j r with
  | ind n ih =>
    rw [String.splitOnAux.eq_def]
    by_cases hati : String.Pos.Raw.atEnd s i = true
    · simp only [hati, ↓reduceIte]
      simp
    · simp only [Bool.not_eq_true] at hati
      simp only [hati, Bool.false_eq_true, ↓reduceIte]
      by_cases hmatch : (String.Pos.Raw.get s i == String.Pos.Raw.get sep j) = true
      · simp only [hmatch, ↓reduceIte]
        have heq_ch : String.Pos.Raw.get s i = String.Pos.Raw.get sep j := by simpa using hmatch
        by_cases hatj : String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true
        · simp only [hatj, ↓reduceIte]
          have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
          rw [String.Pos.Raw.atEnd.eq_1] at hati
          simp only [decide_eq_false_iff_not, Nat.not_le] at hati
          have hun_le : (i.unoffsetBy j).byteIdx ≤ i.byteIdx := by
            change i.byteIdx - j.byteIdx ≤ i.byteIdx; omega
          have h0 : ((String.Pos.Raw.next s i).unoffsetBy 0).byteIdx = (String.Pos.Raw.next s i).byteIdx := by
            change (String.Pos.Raw.next s i).byteIdx - 0 = _; omega
          have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s i).unoffsetBy 0).byteIdx) *
              (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (0 : String.Pos.Raw).byteIdx) + 1 < n := by
            rw [h0]
            have hdiff : s.utf8ByteSize - (String.Pos.Raw.next s i).byteIdx ≤
                s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1 := by omega
            have hmul := Nat.mul_le_mul_right (sep.utf8ByteSize + 2) hdiff
            have hge1 : 1 ≤ s.utf8ByteSize - (i.unoffsetBy j).byteIdx := by omega
            have hsub1 : (s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1) * (sep.utf8ByteSize + 2) +
                (sep.utf8ByteSize + 2) =
                (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) := by
              rw [← Nat.succ_mul]; congr 1; omega
            have hz : (0 : String.Pos.Raw).byteIdx = 0 := rfl
            rw [← r_len_fuel, hz]
            omega
          have hrec := ih _ hstep (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
            (String.Pos.Raw.extract s b ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)) :: r)
            (by change 0 ≤ sep.utf8ByteSize; omega)
            (by change 0 ≤ _; omega)
            rfl
          simp only [List.length_cons] at hrec
          omega
        · simp only [Bool.not_eq_true] at hatj
          simp only [hatj, Bool.false_eq_true, ↓reduceIte]
          have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s i
          have hltj := String.Pos.Raw.byteIdx_lt_byteIdx_next sep j
          rw [String.Pos.Raw.atEnd.eq_1] at hati hatj
          simp only [decide_eq_false_iff_not, Nat.not_le] at hati hatj
          have hnext_eq : ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)).byteIdx =
              (i.unoffsetBy j).byteIdx := by
            change (i + String.Pos.Raw.get s i).byteIdx - (j + String.Pos.Raw.get sep j).byteIdx =
              i.byteIdx - j.byteIdx
            rw [String.Pos.Raw.byteIdx_add_char, String.Pos.Raw.byteIdx_add_char, heq_ch]
            omega
          have hji' : (String.Pos.Raw.next sep j).byteIdx ≤ (String.Pos.Raw.next s i).byteIdx := by
            change (j + String.Pos.Raw.get sep j).byteIdx ≤ (i + String.Pos.Raw.get s i).byteIdx
            rw [String.Pos.Raw.byteIdx_add_char, String.Pos.Raw.byteIdx_add_char, heq_ch]
            omega
          have hj_lt : j.byteIdx < (String.Pos.Raw.next sep j).byteIdx := hltj
          have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)).byteIdx) *
              (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (String.Pos.Raw.next sep j).byteIdx) + 1 < n := by
            rw [hnext_eq, ← r_len_fuel]
            omega
          exact ih _ hstep b (String.Pos.Raw.next s i) (String.Pos.Raw.next sep j) r (by omega) hji' rfl
      · simp only [Bool.not_eq_true] at hmatch
        simp only [hmatch, Bool.false_eq_true, ↓reduceIte]
        have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next s (i.unoffsetBy j)
        rw [String.Pos.Raw.atEnd.eq_1] at hati
        simp only [decide_eq_false_iff_not, Nat.not_le] at hati
        have hun_le : (i.unoffsetBy j).byteIdx ≤ i.byteIdx := by
          change i.byteIdx - j.byteIdx ≤ i.byteIdx; omega
        have h0 : ((String.Pos.Raw.next s (i.unoffsetBy j)).unoffsetBy 0).byteIdx =
            (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx := by
          change (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx - 0 = _; omega
        have hstep : (s.utf8ByteSize - ((String.Pos.Raw.next s (i.unoffsetBy j)).unoffsetBy 0).byteIdx) *
            (sep.utf8ByteSize + 2) + (sep.utf8ByteSize - (0 : String.Pos.Raw).byteIdx) + 1 < n := by
          rw [h0]
          have hdiff : s.utf8ByteSize - (String.Pos.Raw.next s (i.unoffsetBy j)).byteIdx ≤
              s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1 := by omega
          have hmul := Nat.mul_le_mul_right (sep.utf8ByteSize + 2) hdiff
          have hge1 : 1 ≤ s.utf8ByteSize - (i.unoffsetBy j).byteIdx := by omega
          have hsub1 : (s.utf8ByteSize - (i.unoffsetBy j).byteIdx - 1) * (sep.utf8ByteSize + 2) +
              (sep.utf8ByteSize + 2) =
              (s.utf8ByteSize - (i.unoffsetBy j).byteIdx) * (sep.utf8ByteSize + 2) := by
            rw [← Nat.succ_mul]; congr 1; omega
          have hz : (0 : String.Pos.Raw).byteIdx = 0 := rfl
          rw [← r_len_fuel, hz]
          omega
        exact ih _ hstep b (String.Pos.Raw.next s (i.unoffsetBy j)) 0 r
          (by change 0 ≤ sep.utf8ByteSize; omega) (by change 0 ≤ _; omega) rfl

private theorem splitOnAux_tripleQuote (s : String) (b i j : String.Pos.Raw) (r : List String)
    (pref suf : List Char)
    (hs : s.toList = pref ++ suf)
    (hj : j.byteIdx < 3)
    (hstate :
      (j.byteIdx = 0 ∧ i = ⟨utf8Sum pref⟩) ∨
      (j.byteIdx = 1 ∧ ∃ suf1, suf = '\'' :: suf1 ∧ i = ⟨utf8Sum pref + 1⟩) ∨
      (j.byteIdx = 2 ∧ ∃ suf2, suf = '\'' :: '\'' :: suf2 ∧ i = ⟨utf8Sum pref + 2⟩))
    (hhas : ∃ a b, suf = a ++ ['\'', '\'', '\''] ++ b) :
    r.length + 2 ≤ (s.splitOnAux "'''" b i j r).length := by
  induction hmeasure : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - j.byteIdx)
      using Nat.strongRecOn generalizing b i j r pref suf with
  | ind m ih =>
    have hq_sz : ('\'' : Char).utf8Size = 1 := rfl
    have hget_sep : ∀ (p : String.Pos.Raw), p.byteIdx < 3 →
        String.Pos.Raw.get "'''" p = '\'' ∧
        String.Pos.Raw.next "'''" p = ⟨p.byteIdx + 1⟩ ∧
        String.Pos.Raw.atEnd "'''" ⟨p.byteIdx + 1⟩ = decide (p.byteIdx + 1 ≥ 3) := by
      intro p hp
      rcases p with ⟨idx⟩
      dsimp only at hp
      match idx with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | n + 3 => omega
    have hsuf_ne_nil : suf ≠ [] := by
      intro hnil
      rcases hhas with ⟨a, b', hab⟩
      rw [hnil] at hab
      cases a <;> simp at hab
    cases hsuf_eq : suf with
    | nil => exact absurd hsuf_eq hsuf_ne_nil
    | cons c0 suf_tail =>
      have hk_atEnd : String.Pos.Raw.atEnd s ⟨utf8Sum pref⟩ = false := by
        have h' := hs
        rw [hsuf_eq] at h'
        exact (get_at_utf8Sum s pref c0 suf_tail h').2.2
      have hk_lt : utf8Sum pref < s.utf8ByteSize := by
        rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not] at hk_atEnd
        dsimp only at hk_atEnd
        omega
      rcases hstate with ⟨hj0, hi⟩ | ⟨hj1, suf1, hsuf1, hi⟩ | ⟨hj2, suf2, hsuf2, hi⟩
      · have hj_eq : j = 0 := String.Pos.Raw.ext hj0
        subst hj_eq
        have hs' : s.toList = pref ++ c0 :: suf_tail := by rw [hs, hsuf_eq]
        obtain ⟨hgetc0, hnextc0, hatc0⟩ := get_at_utf8Sum s pref c0 suf_tail hs'
        have hsep0 : String.Pos.Raw.get "'''" 0 = '\'' := rfl
        have hnextsep0 : String.Pos.Raw.next "'''" 0 = ⟨1⟩ := rfl
        have hatsep0 : String.Pos.Raw.atEnd "'''" ⟨1⟩ = false := rfl
        rw [String.splitOnAux.eq_def, hi, hatc0]
        simp only [Bool.false_eq_true, ↓reduceIte, hgetc0, hsep0, beq_iff_eq]
        by_cases hq : c0 = '\''
        · subst hq
          simp only [↓reduceIte, hnextc0, hnextsep0, hatsep0, hq_sz]
          have hstep : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) < m := by
            change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 0) = m at hmeasure
            omega
          exact ih _ hstep b ⟨utf8Sum pref + 1⟩ ⟨1⟩ r pref suf hs
            (by decide) (Or.inr (Or.inl ⟨rfl, suf_tail, hsuf_eq, rfl⟩)) hhas rfl
        · simp only [hq, ↓reduceIte]
          have hun0 : (⟨utf8Sum pref⟩ : String.Pos.Raw).unoffsetBy 0 = ⟨utf8Sum pref⟩ :=
            String.Pos.Raw.ext (Nat.sub_zero _)
          rw [hun0, hnextc0]
          have hsuf_tail_has : ∃ a b', suf_tail = a ++ ['\'', '\'', '\''] ++ b' := by
            rcases hhas with ⟨a, b', hab⟩
            rw [hsuf_eq] at hab
            cases a with
            | nil => simp at hab; exact absurd hab.1 hq
            | cons _ as =>
              simp only [List.cons_append, List.cons.injEq] at hab
              exact ⟨as, b', hab.2⟩
          have hpos := Char.utf8Size_pos c0
          have hpref' : s.toList = (pref ++ [c0]) ++ suf_tail := by
            rw [hs, hsuf_eq, List.append_assoc]; rfl
          have hsum' : utf8Sum (pref ++ [c0]) = utf8Sum pref + c0.utf8Size := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, Nat.add_zero]
          have hstep : (s.utf8ByteSize - utf8Sum (pref ++ [c0])) * 4 + (3 - 0) < m := by
            change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 0) = m at hmeasure
            omega
          exact ih _ hstep b ⟨utf8Sum pref + c0.utf8Size⟩ 0 r (pref ++ [c0]) suf_tail hpref'
            (by decide) (Or.inl ⟨rfl, by rw [hsum']⟩) hsuf_tail_has rfl
      · have hj_eq : j = ⟨1⟩ := String.Pos.Raw.ext hj1
        subst hj_eq
        have hsuf_eq1 : c0 :: suf_tail = '\'' :: suf1 := by rw [← hsuf_eq, hsuf1]
        injection hsuf_eq1 with hc0 hsuf1_eq
        subst hc0
        have hsuf1_ne : suf1 ≠ [] := by
          intro hnil
          rcases hhas with ⟨a, b', hab⟩
          rw [hsuf1, hnil] at hab
          cases a with
          | nil => simp at hab
          | cons _ a' => cases a' <;> simp at hab
        cases hsuf1_cases : suf1 with
        | nil => exact absurd hsuf1_cases hsuf1_ne
        | cons c1 suf1_tail =>
          have hs' : s.toList = (pref ++ ['\'']) ++ c1 :: suf1_tail := by
            rw [hs, hsuf1, hsuf1_cases, List.append_assoc]; rfl
          have hsum_p1 : utf8Sum (pref ++ ['\'']) = utf8Sum pref + 1 := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, hq_sz]
          obtain ⟨hgetc1, hnextc1, hatc1⟩ := get_at_utf8Sum s (pref ++ ['\'']) c1 suf1_tail hs'
          rw [hsum_p1] at hgetc1 hnextc1 hatc1
          have hsep1 : String.Pos.Raw.get "'''" ⟨1⟩ = '\'' := rfl
          have hnextsep1 : String.Pos.Raw.next "'''" ⟨1⟩ = ⟨2⟩ := rfl
          have hatsep1 : String.Pos.Raw.atEnd "'''" ⟨2⟩ = false := rfl
          rw [String.splitOnAux.eq_def, hi, hatc1]
          simp only [Bool.false_eq_true, ↓reduceIte, hgetc1, hsep1, beq_iff_eq]
          by_cases hq : c1 = '\''
          · subst hq
            simp only [↓reduceIte, hnextc1, hnextsep1, hatsep1, hq_sz]
            have hstep : (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 2) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) = m at hmeasure
              omega
            have hsuf2 : suf = '\'' :: '\'' :: suf1_tail := by rw [hsuf1, hsuf1_cases]
            exact ih _ hstep b ⟨utf8Sum pref + 2⟩ ⟨2⟩ r pref suf hs
              (by decide) (Or.inr (Or.inr ⟨rfl, suf1_tail, hsuf2, rfl⟩)) hhas rfl
          · simp only [hq, ↓reduceIte]
            have hun1 : (⟨utf8Sum pref + 1⟩ : String.Pos.Raw).unoffsetBy ⟨1⟩ = ⟨utf8Sum pref⟩ :=
              String.Pos.Raw.ext (by change utf8Sum pref + 1 - 1 = utf8Sum pref; omega)
            have hs0 : s.toList = pref ++ '\'' :: suf1 := by rw [hs, hsuf1]
            obtain ⟨_, hnext_q0, _⟩ := get_at_utf8Sum s pref '\'' suf1 hs0
            rw [hun1, hnext_q0, hq_sz]
            have hsuf1_has : ∃ a b', suf1 = a ++ ['\'', '\'', '\''] ++ b' := by
              rcases hhas with ⟨a, b', hab⟩
              rw [hsuf1, hsuf1_cases] at hab
              cases a with
              | nil => simp at hab; exact absurd hab.1 hq
              | cons _ as =>
                simp only [List.cons_append, List.cons.injEq] at hab
                exact ⟨as, b', by rw [hsuf1_cases, hab.2]⟩
            have hpref' : s.toList = (pref ++ ['\'']) ++ suf1 := by rw [hs, hsuf1, List.append_assoc]; rfl
            have hstep : (s.utf8ByteSize - utf8Sum (pref ++ ['\''])) * 4 + (3 - 0) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 1) = m at hmeasure
              omega
            exact ih _ hstep b ⟨utf8Sum pref + 1⟩ 0 r (pref ++ ['\'']) suf1 hpref'
              (by decide) (Or.inl ⟨rfl, by rw [hsum_p1]⟩) hsuf1_has rfl
      · have hj_eq : j = ⟨2⟩ := String.Pos.Raw.ext hj2
        subst hj_eq
        have hsuf_eq2 : c0 :: suf_tail = '\'' :: '\'' :: suf2 := by rw [← hsuf_eq, hsuf2]
        injection hsuf_eq2 with hc0 hsuf2_tail_eq
        subst hc0
        have hsuf2_ne : suf2 ≠ [] := by
          intro hnil
          rcases hhas with ⟨a, b', hab⟩
          rw [hsuf2, hnil] at hab
          cases a with
          | nil => simp at hab
          | cons _ a' =>
            cases a' with
            | nil => simp at hab
            | cons _ a'' => cases a'' <;> simp at hab
        cases hsuf2_cases : suf2 with
        | nil => exact absurd hsuf2_cases hsuf2_ne
        | cons c2 suf2_tail =>
          have hs' : s.toList = (pref ++ ['\'', '\'']) ++ c2 :: suf2_tail := by
            rw [hs, hsuf2, hsuf2_cases, List.append_assoc]; rfl
          have hsum_p2 : utf8Sum (pref ++ ['\'', '\'']) = utf8Sum pref + 2 := by
            rw [utf8Sum_append, utf8Sum, utf8Sum, utf8Sum, hq_sz]
          obtain ⟨hgetc2, hnextc2, hatc2⟩ := get_at_utf8Sum s (pref ++ ['\'', '\'']) c2 suf2_tail hs'
          rw [hsum_p2] at hgetc2 hnextc2 hatc2
          have hsep2 : String.Pos.Raw.get "'''" ⟨2⟩ = '\'' := rfl
          have hnextsep2 : String.Pos.Raw.next "'''" ⟨2⟩ = ⟨3⟩ := rfl
          have hatsep2 : String.Pos.Raw.atEnd "'''" ⟨3⟩ = true := rfl
          rw [String.splitOnAux.eq_def, hi, hatc2]
          simp only [Bool.false_eq_true, ↓reduceIte, hgetc2, hsep2, beq_iff_eq]
          by_cases hq : c2 = '\''
          · subst hq
            simp only [↓reduceIte, hnextc2, hnextsep2, hatsep2]
            have hge := splitOnAux_length_ge s "'''"
              (⟨utf8Sum pref + 2 + '\''.utf8Size⟩)
              (⟨utf8Sum pref + 2 + '\''.utf8Size⟩) 0
              (String.Pos.Raw.extract s b
                ((⟨utf8Sum pref + 2 + '\''.utf8Size⟩ : String.Pos.Raw).unoffsetBy ⟨3⟩) :: r)
              (by decide) (by change 0 ≤ _; omega)
            simp only [List.length_cons] at hge
            omega
          · simp only [hq, ↓reduceIte]
            have hun2 : (⟨utf8Sum pref + 2⟩ : String.Pos.Raw).unoffsetBy ⟨2⟩ = ⟨utf8Sum pref⟩ :=
              String.Pos.Raw.ext (by change utf8Sum pref + 2 - 2 = utf8Sum pref; omega)
            have hs0 : s.toList = pref ++ '\'' :: ('\'' :: suf2) := by rw [hs, hsuf2]
            obtain ⟨_, hnext_q0, _⟩ := get_at_utf8Sum s pref '\'' ('\'' :: suf2) hs0
            rw [hun2, hnext_q0, hq_sz]
            have hsum_p1 : utf8Sum (pref ++ ['\'']) = utf8Sum pref + 1 := by
              rw [utf8Sum_append, utf8Sum, utf8Sum, hq_sz]
            have hsuf2_has : ∃ a b', ('\'' :: suf2) = a ++ ['\'', '\'', '\''] ++ b' := by
              rcases hhas with ⟨a, b', hab⟩
              rw [hsuf2, hsuf2_cases] at hab
              cases a with
              | nil => simp at hab; exact absurd hab.1 hq
              | cons _ as =>
                simp only [List.cons_append, List.cons.injEq] at hab
                exact ⟨as, b', by rw [hsuf2_cases, hab.2]⟩
            have hpref' : s.toList = (pref ++ ['\'']) ++ ('\'' :: suf2) := by
              rw [hs, hsuf2, List.append_assoc]; rfl
            have hstep : (s.utf8ByteSize - utf8Sum (pref ++ ['\''])) * 4 + (3 - 0) < m := by
              change (s.utf8ByteSize - utf8Sum pref) * 4 + (3 - 2) = m at hmeasure
              omega
            exact ih _ hstep b ⟨utf8Sum pref + 1⟩ 0 r (pref ++ ['\'']) ('\'' :: suf2) hpref'
              (by decide) (Or.inl ⟨rfl, by rw [hsum_p1]⟩) hsuf2_has rfl

private theorem no_triple_quote_of_not_containsSubstr (s : String) (h : containsSubstr s "'''" = false) :
    ∀ a b : List Char, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b := by
  intro a b hab
  simp only [containsSubstr, decide_eq_false_iff_not, Nat.not_lt] at h
  have hne : ("'''" == "") = false := rfl
  have hsplit : s.splitOn "'''" = s.splitOnAux "'''" 0 0 0 [] := by
    simp [String.splitOn, hne]
  rw [hsplit] at h
  have hge := splitOnAux_tripleQuote s 0 0 0 [] [] s.toList (by simp) (by decide)
    (Or.inl ⟨rfl, rfl⟩) ⟨a, b, hab⟩
  simp at hge
  omega

private theorem getLast_ne_quote_of_not_endsWith (s : String) (h : s.endsWith "'" = false) :
    ∀ a : List Char, s.toList ≠ a ++ ['\''] := by
  intro a ha
  rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_eq_false_iff] at h
  apply h
  have hcopy : s.toSlice.copy = s := String.copy_toSlice
  rw [hcopy, ha]
  exact ⟨a, rfl⟩

private theorem not_mem_of_contains_false (s : String) (c : Char) (h : s.contains c = false) :
    c ∉ s.toList := by
  rw [String.contains_char_eq, decide_eq_false_iff_not] at h
  exact h

private theorem takeHexDigits_hexDigitUpper_4 (n : Nat) (hn : n < 256) (rest : List Char) :
    takeHexDigits 4 0 ('0' :: '0' :: hexDigitUpper (n / 16) :: hexDigitUpper (n % 16) :: rest) =
      some (n, rest) := by
  have h0 : hexVal? '0' = some 0 := rfl
  have h1 := hexDigitUpper_val (n / 16) (by omega)
  have h2 := hexDigitUpper_val (n % 16) (Nat.mod_lt n (by decide))
  simp only [takeHexDigits, h0, h1, h2]
  congr 1; congr 1; omega

private theorem parseUnicodeHex_hexDigitUpper_4 (c : Char) (hc : isDisallowedControl c = true) (rest : List Char) :
    parseUnicodeHex 4 ('0' :: '0' :: hexDigitUpper (c.toNat / 16) :: hexDigitUpper (c.toNat % 16) :: rest) =
      .ok (c, rest) := by
  have hlt : c.toNat < 256 := by
    simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    omega
  simp only [parseUnicodeHex, takeHexDigits_hexDigitUpper_4 c.toNat hlt rest]
  have hrange : (c.toNat > 0x10FFFF || (0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF)) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨by omega, Or.inl (by omega)⟩
  simp [hrange, Char.ofNat_toNat]

private theorem escapeBasicChar_clean (allowNewline : Bool) (c : Char) :
    ((escapeBasicChar allowNewline c).toList.all fun ch =>
      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
  by_cases h1 : c = '\\'
  · subst h1; cases allowNewline <;> decide
  · by_cases h2 : c = '"'
    · subst h2; cases allowNewline <;> decide
    · by_cases h3 : c = '\x08'
      · subst h3; cases allowNewline <;> decide
      · by_cases h4 : c = '\t'
        · subst h4; cases allowNewline <;> decide
        · by_cases h5 : c = '\n'
          · subst h5; cases allowNewline <;> decide
          · by_cases h6 : c = '\x0c'
            · subst h6; cases allowNewline <;> decide
            · by_cases h7 : c = '\r'
              · subst h7; cases allowNewline <;> decide
              · by_cases hc : isDisallowedControl c = true
                · have hdef : escapeBasicChar allowNewline c =
                      "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]
                  have hlt : c.toNat < 256 := by
                    simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true,
                      decide_eq_true_eq, beq_iff_eq] at hc
                    omega
                  have hd1 := hexDigitUpper_clean (c.toNat / 16) (by omega)
                  have hd2 := hexDigitUpper_clean (c.toNat % 16) (Nat.mod_lt _ (by decide))
                  simp only [String.toList_append, String.toList_ofList, List.all_append,
                    List.all_cons, List.all_nil, Bool.and_true]
                  have hu : (("\\u00" : String).toList.all fun ch =>
                      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
                    cases allowNewline <;> decide
                  simp only [Bool.and_eq_true] at hd1 hd2 ⊢
                  refine ⟨hu, ⟨?_, ?_⟩⟩
                  · cases allowNewline <;> simp [hd1]
                  · cases allowNewline <;> simp [hd2]
                · have hdef : escapeBasicChar allowNewline c = String.singleton c := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]
                  simp only [String.toList_singleton, List.all_cons, List.all_nil, Bool.and_true,
                    Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
                  refine ⟨⟨by simp at hc; exact hc, h7⟩, ?_⟩
                  cases allowNewline <;> simp [h5]

private theorem escapeBasicBody_clean (allowNewline : Bool) (s : String) :
    ((escapeBasicBody allowNewline s).toList.all fun ch =>
      !isDisallowedControl ch && ch != '\r' && (allowNewline || ch != '\n')) = true := by
  simp only [escapeBasicBody, String.toList_join, List.all_flatMap, List.all_map, Function.comp_def]
  rw [List.all_eq_true]
  intro c _
  exact escapeBasicChar_clean allowNewline c

private theorem parseBasicStringBodyFuel_step_bs (f : Nat) (acc rest : List Char) :
    parseBasicStringBodyFuel (f + 1) acc ('\\' :: rest) =
      (parseBasicEscape rest >>= fun (ch, afterEsc) =>
        parseBasicStringBodyFuel f (ch :: acc) afterEsc) := rfl

private theorem parseBasicStringBodyFuel_step_char (f : Nat) (acc : List Char) (c : Char) (rest : List Char)
    (hnl : c ≠ '\n') (hq : c ≠ '"') (hbs : c ≠ '\\') :
    parseBasicStringBodyFuel (f + 1) acc (c :: rest) = parseBasicStringBodyFuel f (c :: acc) rest := by
  conv => lhs; unfold parseBasicStringBodyFuel
  split <;> simp_all

private theorem escapeBasicChar_length_pos (allowNl : Bool) (c : Char) :
    (escapeBasicChar allowNl c).toList.length ≥ 1 := by
  by_cases h1 : c = '\\'
  · subst h1; cases allowNl <;> decide
  · by_cases h2 : c = '"'
    · subst h2; cases allowNl <;> decide
    · by_cases h3 : c = '\x08'
      · subst h3; cases allowNl <;> decide
      · by_cases h4 : c = '\t'
        · subst h4; cases allowNl <;> decide
        · by_cases h5 : c = '\n'
          · subst h5; cases allowNl <;> decide
          · by_cases h6 : c = '\x0c'
            · subst h6; cases allowNl <;> decide
            · by_cases h7 : c = '\r'
              · subst h7; cases allowNl <;> decide
              · by_cases hc : isDisallowedControl c = true
                · have hdef : escapeBasicChar allowNl c =
                      "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]; simp
                · have hdef : escapeBasicChar allowNl c = String.singleton c := by
                    simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                  rw [hdef]; simp

private theorem parseBasicStringBodyFuel_escapeBasicBody_list (cs acc rest : List Char) (fuel : Nat)
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ fuel) :
    parseBasicStringBodyFuel fuel acc (cs.flatMap (fun c => (escapeBasicChar false c).toList) ++ '"' :: rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f => simp [parseBasicStringBodyFuel]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_cons, List.append_assoc]
      have hsub : (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ f := by
        simp only [List.flatMap_cons, List.length_append] at hfuel
        have hlen := escapeBasicChar_length_pos false c
        omega
      by_cases h1 : c = '\\'
      · subst h1
        have hstr : (escapeBasicChar false '\\').toList = ['\\', '\\'] := rfl
        rw [hstr]
        simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
          parseBasicEscape, bind, Except.bind, ih ('\\' :: acc) f hsub]
        simp
      · by_cases h2 : c = '"'
        · subst h2
          have hstr : (escapeBasicChar false '"').toList = ['\\', '"'] := rfl
          rw [hstr]
          simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
            parseBasicEscape, bind, Except.bind, ih ('"' :: acc) f hsub]
          simp
        · by_cases h3 : c = '\x08'
          · subst h3
            have hstr : (escapeBasicChar false '\x08').toList = ['\\', 'b'] := rfl
            rw [hstr]
            simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
              parseBasicEscape, bind, Except.bind, ih ('\x08' :: acc) f hsub]
            simp
          · by_cases h4 : c = '\t'
            · subst h4
              have hstr : (escapeBasicChar false '\t').toList = ['\\', 't'] := rfl
              rw [hstr]
              simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                parseBasicEscape, bind, Except.bind, ih ('\t' :: acc) f hsub]
              simp
            · by_cases h5 : c = '\n'
              · subst h5
                have hstr : (escapeBasicChar false '\n').toList = ['\\', 'n'] := rfl
                rw [hstr]
                simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                  parseBasicEscape, bind, Except.bind, ih ('\n' :: acc) f hsub]
                simp
              · by_cases h6 : c = '\x0c'
                · subst h6
                  have hstr : (escapeBasicChar false '\x0c').toList = ['\\', 'f'] := rfl
                  rw [hstr]
                  simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                    parseBasicEscape, bind, Except.bind, ih ('\x0c' :: acc) f hsub]
                  simp
                · by_cases h7 : c = '\r'
                  · subst h7
                    have hstr : (escapeBasicChar false '\r').toList = ['\\', 'r'] := rfl
                    rw [hstr]
                    simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                      parseBasicEscape, bind, Except.bind, ih ('\r' :: acc) f hsub]
                    simp
                  · by_cases hc : isDisallowedControl c = true
                    · have hstr : (escapeBasicChar false c).toList =
                          ['\\', 'u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                        have hdef : escapeBasicChar false c =
                            "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]
                        have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                        simp [hu]
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append, parseBasicStringBodyFuel_step_bs,
                        parseBasicEscape, parseUnicodeHex_hexDigitUpper_4 c hc, bind, Except.bind,
                        ih (c :: acc) f hsub]
                      simp
                    · have hstr : (escapeBasicChar false c).toList = [c] := by
                        have hdef : escapeBasicChar false c = String.singleton c := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]; simp
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append]
                      rw [parseBasicStringBodyFuel_step_char f acc c _ h5 h2 h1, ih (c :: acc) f hsub]
                      simp

private theorem parseBasicStringBody_escapeBasicBody (s : String) (rest : List Char) :
    parseBasicStringBody ((escapeBasicBody false s).toList ++ '"' :: rest) =
      .ok (s, rest) := by
  unfold parseBasicStringBody
  have heq : (escapeBasicBody false s).toList =
      s.toList.flatMap (fun c => (escapeBasicChar false c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  have hlen : ((escapeBasicBody false s).toList ++ '"' :: rest).length + 1 ≥
      (s.toList.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 := by
    rw [heq]
    simp only [List.length_append, List.length_cons]
    omega
  rw [heq] at hlen ⊢
  rw [parseBasicStringBodyFuel_escapeBasicBody_list s.toList [] rest _ hlen]
  simp [String.ofList_toList]

private theorem parseMultilineBasicBodyFuel_step_bs (f : Nat) (acc rest : List Char) :
    parseMultilineBasicBodyFuel (f + 1) acc ('\\' :: rest) =
      match parseBasicEscape rest with
      | .ok (ch, afterEsc) => parseMultilineBasicBodyFuel f (ch :: acc) afterEsc
      | .error err =>
        match skipHorizWs rest with
        | '\n' :: afterNl => parseMultilineBasicBodyFuel f acc (skipHorizAndNl afterNl)
        | _ =>
          match rest with
          | 'u' :: _ => .error err
          | 'U' :: _ => .error err
          | _ => .error (mkErr .parseError "invalid escape sequence in multiline basic string") := rfl

private theorem parseMultilineBasicBodyFuel_step_char (f : Nat) (acc : List Char) (c : Char) (rest : List Char)
    (hq : c ≠ '"') (hbs : c ≠ '\\') :
    parseMultilineBasicBodyFuel (f + 1) acc (c :: rest) =
      parseMultilineBasicBodyFuel f (c :: acc) rest := by
  conv => lhs; unfold parseMultilineBasicBodyFuel
  split <;> simp_all

private theorem parseMultilineBasicBodyFuel_escapeBasicBody_list (cs acc rest : List Char) (fuel : Nat)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"')
    (hfuel : (cs.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ fuel) :
    parseMultilineBasicBodyFuel fuel acc
      (cs.flatMap (fun c => (escapeBasicChar true c).toList) ++ ['"', '"', '"'] ++ rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append]
      cases rest with
      | nil => simp [parseMultilineBasicBodyFuel]
      | cons c r =>
        have hne : c ≠ '"' := hrest c r rfl
        conv => lhs; unfold parseMultilineBasicBodyFuel
        split
        all_goals try (simp_all; done)
        rename_i _ hq1 _ _ heq
        cases heq
        exact absurd rfl (hq1 (c :: r) rfl)
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_cons, List.append_assoc]
      have hsub : (cs.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 ≤ f := by
        simp only [List.flatMap_cons, List.length_append] at hfuel
        have hlen := escapeBasicChar_length_pos true c
        omega
      by_cases h1 : c = '\\'
      · subst h1
        have hstr : (escapeBasicChar true '\\').toList = ['\\', '\\'] := rfl
        rw [hstr]
        simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
          parseBasicEscape]
        have hih := ih ('\\' :: acc) f hsub
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
        rw [hih]; simp
      · by_cases h2 : c = '"'
        · subst h2
          have hstr : (escapeBasicChar true '"').toList = ['\\', '"'] := rfl
          rw [hstr]
          simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
            parseBasicEscape]
          have hih := ih ('"' :: acc) f hsub
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
          rw [hih]; simp
        · by_cases h3 : c = '\x08'
          · subst h3
            have hstr : (escapeBasicChar true '\x08').toList = ['\\', 'b'] := rfl
            rw [hstr]
            simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
              parseBasicEscape]
            have hih := ih ('\x08' :: acc) f hsub
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
            rw [hih]; simp
          · by_cases h4 : c = '\t'
            · subst h4
              have hstr : (escapeBasicChar true '\t').toList = ['\\', 't'] := rfl
              rw [hstr]
              simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                parseBasicEscape]
              have hih := ih ('\t' :: acc) f hsub
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
              rw [hih]; simp
            · by_cases h5 : c = '\n'
              · subst h5
                have hstr : (escapeBasicChar true '\n').toList = ['\n'] := rfl
                rw [hstr]
                simp only [List.cons_append, List.nil_append]
                rw [parseMultilineBasicBodyFuel_step_char f acc '\n' _ (by decide) (by decide)]
                have hih := ih ('\n' :: acc) f hsub
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                rw [hih]; simp
              · by_cases h6 : c = '\x0c'
                · subst h6
                  have hstr : (escapeBasicChar true '\x0c').toList = ['\\', 'f'] := rfl
                  rw [hstr]
                  simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                    parseBasicEscape]
                  have hih := ih ('\x0c' :: acc) f hsub
                  simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                  rw [hih]; simp
                · by_cases h7 : c = '\r'
                  · subst h7
                    have hstr : (escapeBasicChar true '\r').toList = ['\\', 'r'] := rfl
                    rw [hstr]
                    simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                      parseBasicEscape]
                    have hih := ih ('\r' :: acc) f hsub
                    simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                    rw [hih]; simp
                  · by_cases hc : isDisallowedControl c = true
                    · have hstr : (escapeBasicChar true c).toList =
                          ['\\', 'u', '0', '0', hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                        have hdef : escapeBasicChar true c =
                            "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]
                        have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                        simp [hu]
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append, parseMultilineBasicBodyFuel_step_bs,
                        parseBasicEscape, parseUnicodeHex_hexDigitUpper_4 c hc]
                      have hih := ih (c :: acc) f hsub
                      simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                      rw [hih]; simp
                    · have hstr : (escapeBasicChar true c).toList = [c] := by
                        have hdef : escapeBasicChar true c = String.singleton c := by
                          simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                        rw [hdef]; simp
                      rw [hstr]
                      simp only [List.cons_append, List.nil_append]
                      rw [parseMultilineBasicBodyFuel_step_char f acc c _ h2 h1]
                      have hih := ih (c :: acc) f hsub
                      simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
                      rw [hih]; simp

private theorem parseMultilineBasicString_escapeBasicBody (s : String) (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"') :
    parseMultilineBasicString ('\n' :: (escapeBasicBody true s).toList ++ ['"', '"', '"'] ++ rest) =
      .ok (s, rest) := by
  unfold parseMultilineBasicString
  have heq : (escapeBasicBody true s).toList =
      s.toList.flatMap (fun c => (escapeBasicChar true c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  rw [heq]
  simp only [List.cons_append]
  have hlen : (s.toList.flatMap (fun c => (escapeBasicChar true c).toList) ++ ['"', '"', '"'] ++ rest).length + 1 ≥
      (s.toList.flatMap (fun c => (escapeBasicChar true c).toList)).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  rw [parseMultilineBasicBodyFuel_escapeBasicBody_list s.toList [] rest _ hrest hlen]
  simp [String.ofList_toList]

private theorem parseLiteralStringBody_list (cs acc rest : List Char)
    (hnl : '\n' ∉ cs) (hq : '\'' ∉ cs) :
    parseLiteralStringBody acc (cs ++ '\'' :: rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc with
  | nil => simp [parseLiteralStringBody]
  | cons c cs ih =>
    have hc_nl : c ≠ '\n' := fun h => hnl (by simp [h])
    have hc_q : c ≠ '\'' := fun h => hq (by simp [h])
    have hnl' : '\n' ∉ cs := fun h => hnl (by simp [h])
    have hq' : '\'' ∉ cs := fun h => hq (by simp [h])
    simp only [List.cons_append]
    unfold parseLiteralStringBody
    split <;> rename_i heq
    · simp at heq
    · injection heq with hc; exact absurd hc hc_nl
    · injection heq with hc; exact absurd hc hc_q
    · injection heq with hc hr
      subst hc hr
      rw [ih (c :: acc) hnl' hq']
      simp

private theorem parseMultilineLiteralBodyFuel_step (f : Nat) (acc : List Char) (c : Char) (cs : List Char)
    (hnot3 : ¬ (c = '\'' ∧ ∃ t, cs = '\'' :: '\'' :: t)) :
    parseMultilineLiteralBodyFuel (f + 1) acc (c :: cs) =
      parseMultilineLiteralBodyFuel f (c :: acc) cs := by
  conv => lhs; unfold parseMultilineLiteralBodyFuel
  split <;> first | simp_all | (exfalso; apply hnot3; simp_all)

private theorem parseMultilineLiteralBodyFuel_list (cs acc rest : List Char) (fuel : Nat)
    (hno3 : ∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b)
    (hnoend : ∀ a, cs ≠ a ++ ['\''])
    (hrest : ∀ c r, rest = c :: r → c ≠ '\'')
    (hfuel : cs.length + 1 ≤ fuel) :
    parseMultilineLiteralBodyFuel fuel acc (cs ++ ['\'', '\'', '\''] ++ rest) =
      .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs generalizing acc fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.nil_append, List.cons_append]
      cases rest with
      | nil => simp [parseMultilineLiteralBodyFuel]
      | cons c r =>
        have hne : c ≠ '\'' := hrest c r rfl
        conv => lhs; unfold parseMultilineLiteralBodyFuel
        split
        all_goals try (simp_all; done)
        rename_i hq1 _ heq
        cases heq
        exact absurd rfl (hq1 (c :: r) rfl)
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hsub : cs.length + 1 ≤ f := by simp at hfuel; omega
      have hno3' : ∀ a b, cs ≠ a ++ ['\'', '\'', '\''] ++ b := by
        intro a b hab
        exact hno3 (c :: a) b (by simp [hab])
      have hnoend' : ∀ a, cs ≠ a ++ ['\''] := by
        intro a ha
        exact hnoend (c :: a) (by simp [ha])
      have hnot3 : ¬ (c = '\'' ∧ ∃ t, cs ++ ['\'', '\'', '\''] ++ rest = '\'' :: '\'' :: t) := by
        intro ⟨hc, t, ht⟩
        subst hc
        cases cs with
        | nil => exact hnoend [] rfl
        | cons c1 cs1 =>
          cases cs1 with
          | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
            exact hnoend ['\''] (by simp [ht.1])
          | cons c2 cs2 =>
            simp only [List.cons_append, List.cons.injEq] at ht
            exact hno3 [] cs2 (by simp [ht.1, ht.2.1])
      change parseMultilineLiteralBodyFuel (f + 1) acc (c :: (cs ++ ['\'', '\'', '\''] ++ rest)) = _
      rw [parseMultilineLiteralBodyFuel_step f acc c _ hnot3,
        ih (c :: acc) f hno3' hnoend' hsub]
      simp

private theorem takeBareKeyChars_append (acc ks rest : List Char)
    (hks : ks.all isBareKeyChar = true)
    (hrest : ∀ c tail, rest = c :: tail → isBareKeyChar c = false) :
    takeBareKeyChars acc (ks ++ rest) = (acc.reverse ++ ks, rest) := by
  induction ks generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeBareKeyChars]
    | cons c r =>
      simp only [List.nil_append, takeBareKeyChars, hrest c r rfl, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
  | cons k ks ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hks
    simp only [List.cons_append, takeBareKeyChars, hks.1, ↓reduceIte]
    rw [ih (k :: acc) hks.2]
    simp

private theorem parseKeySegment_basic (cs : List Char) (hno : ¬ ∃ r, cs = '"' :: '"' :: r) :
    parseKeySegment ('"' :: cs) = parseBasicStringBody cs := by
  unfold parseKeySegment
  split
  · exfalso; apply hno; simp_all
  · simp_all
  · rename_i heq; cases heq; rfl
  · simp_all
  · simp_all

private theorem parseKeySegment_literal (cs : List Char) (hno : ¬ ∃ r, cs = '\'' :: '\'' :: r) :
    parseKeySegment ('\'' :: cs) = parseLiteralStringBody [] cs := by
  unfold parseKeySegment
  split
  · simp_all
  · exfalso; apply hno; simp_all
  · simp_all
  · rename_i heq; cases heq; rfl
  · simp_all

private theorem parseKeySegment_bare (c0 : Char) (cs : List Char) (hq1 : c0 ≠ '"') (hq2 : c0 ≠ '\'') :
    parseKeySegment (c0 :: cs) =
      let (ks, rest) := takeBareKeyChars [] (c0 :: cs)
      if ks.isEmpty then .error (mkErr .parseError "expected key")
      else .ok (String.ofList ks, rest) := by
  unfold parseKeySegment
  split <;> first | simp_all | rfl

private theorem renderKey_parseKeySegment (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'') :
    parseKeySegment (rk.toList ++ rest) = .ok (k, rest) ∧
    (rk.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk
      subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      rcases hbare with ⟨hne, hall⟩
      have hne_list : k.toList ≠ [] := by
        intro h
        have hk0 : k = "" := by rw [← String.ofList_toList (s := k), h]
        subst hk0
        simp at hne
      have hrest_bare : ∀ c tail, rest = c :: tail → isBareKeyChar c = false := by
        intro c tail h
        simpa using (hrest c tail h).1
      have htake := takeBareKeyChars_append [] k.toList rest hall hrest_bare
      simp only [List.reverse_nil, List.nil_append] at htake
      have hparse : parseKeySegment (k.toList ++ rest) = .ok (k, rest) := by
        cases hlist : k.toList with
        | nil => exact absurd hlist hne_list
        | cons c0 cs0 =>
          have hc0' : isBareKeyChar c0 = true :=
            List.all_eq_true.mp hall c0 (by rw [hlist]; simp)
          have hcl' := isBareKeyChar_clean c0 hc0'
          simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl'
          have hq1 : c0 ≠ '"' := hcl'.1.1.1.1.1.1.2
          have hq2 : c0 ≠ '\'' := hcl'.1.1.1.1.1.2
          simp only [List.cons_append, parseKeySegment_bare c0 (cs0 ++ rest) hq1 hq2]
          rw [← List.cons_append, ← hlist, htake]
          have hne_ks : k.toList.isEmpty = false := by simp [hlist]
          have hk_of : String.ofList k.toList = k := String.ofList_toList
          simp only [hne_ks, Bool.false_eq_true, ↓reduceIte, hk_of]
      refine ⟨hparse, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      have hbc := List.all_eq_true.mp hall c hc
      have hcl := isBareKeyChar_clean c hbc
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl ⊢
      exact ⟨⟨hcl.1.1.1.1.1.1.1.1.1.1.1, hcl.1.1.1.1.1.1.1.1.1.1.2⟩, hcl.1.1.1.1.1.1.1.1.1.2⟩
    · simp at hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk
    subst hrk
    have hclean_esc := escapeBasicBody_clean false k
    have hno3 : ¬ ∃ r', ((escapeBasicBody false k).toList ++ '"' :: rest) = '"' :: '"' :: r' := by
      intro ⟨r', hr'⟩
      cases hk : k.toList with
      | nil =>
        have hbody : (escapeBasicBody false k).toList = [] := by
          simp [escapeBasicBody, hk]
        rw [hbody, List.nil_append] at hr'
        cases rest with
        | nil => simp at hr'
        | cons c _ =>
          simp only [List.cons.injEq] at hr'
          exact (hrest c _ rfl).2.1 hr'.2.1
      | cons c0 cs0 =>
        have hbody : (escapeBasicBody false k).toList =
            (escapeBasicChar false c0).toList ++ cs0.flatMap (fun c => (escapeBasicChar false c).toList) := by
          simp [escapeBasicBody, String.toList_join, hk, List.flatMap_map]
        rw [hbody, List.append_assoc] at hr'
        have hne : ((escapeBasicChar false c0).toList).head? ≠ some '"' := by
          by_cases h1 : c0 = '\\'
          · subst h1; decide
          · by_cases h2 : c0 = '"'
            · subst h2; decide
            · by_cases h3 : c0 = '\x08'
              · subst h3; decide
              · by_cases h4 : c0 = '\t'
                · subst h4; decide
                · by_cases h5 : c0 = '\n'
                  · subst h5; decide
                  · by_cases h6 : c0 = '\x0c'
                    · subst h6; decide
                    · by_cases h7 : c0 = '\r'
                      · subst h7; decide
                      · by_cases hc : isDisallowedControl c0 = true
                        · have hdef : escapeBasicChar false c0 =
                              "\\u00" ++ String.ofList [hexDigitUpper (c0.toNat / 16), hexDigitUpper (c0.toNat % 16)] := by
                            simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                          rw [hdef]
                          have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                          simp [hu]
                        · have hdef : escapeBasicChar false c0 = String.singleton c0 := by
                            simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                          rw [hdef]; simp [h2]
        cases h0 : (escapeBasicChar false c0).toList with
        | nil =>
          have hlen := escapeBasicChar_length_pos false c0
          rw [h0] at hlen; simp at hlen
        | cons d0 ds0 =>
          rw [h0] at hr' hne
          injection hr' with hd0
          exact hne (by simp [hd0])
    have hparse : parseKeySegment (("\"" ++ escapeBasicBody false k ++ "\"").toList ++ rest) = .ok (k, rest) := by
      have hstr : ("\"" : String).toList = ['"'] := rfl
      simp only [String.toList_append, hstr, List.cons_append, List.nil_append, List.append_assoc]
      rw [parseKeySegment_basic _ hno3]
      exact parseBasicStringBody_escapeBasicBody k rest
    refine ⟨hparse, ?_⟩
    simp only [String.toList_append]
    have hq_clean : (("\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
    simp only [List.all_append, hq_clean, Bool.true_and, Bool.and_true]
    simpa [Bool.and_assoc] using hclean_esc
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hcond
      injection hr with hrk
      subst hrk
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨hclean, hnoq⟩
      have hnq := not_mem_of_contains_false k '\'' hnoq
      have hnl : '\n' ∉ k.toList := fun h => (isSingleLineClean_no_nl k hclean '\n' h).1 rfl
      have hno3 : ¬ ∃ r', (k.toList ++ '\'' :: rest) = '\'' :: '\'' :: r' := by
        intro ⟨r', hr'⟩
        cases hk : k.toList with
        | nil =>
          rw [hk, List.nil_append] at hr'
          cases rest with
          | nil => simp at hr'
          | cons c _ =>
            simp only [List.cons.injEq] at hr'
            exact (hrest c _ rfl).2.2 hr'.2.1
        | cons c0 _ =>
          rw [hk, List.cons_append] at hr'
          injection hr' with hc0
          exact hnq (by rw [hk, hc0]; simp)
      have hparse : parseKeySegment (("'" ++ k ++ "'").toList ++ rest) = .ok (k, rest) := by
        have hstr : ("'" : String).toList = ['\''] := rfl
        simp only [String.toList_append, hstr, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseKeySegment_literal _ hno3, parseLiteralStringBody_list k.toList [] rest hnl hnq]
        simp [String.ofList_toList]
      refine ⟨hparse, ?_⟩
      simp only [String.toList_append, List.all_append]
      have hq_clean : (("'" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
      simp only [hq_clean, Bool.true_and, Bool.and_true]
      simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hclean ⊢
      intro c hc
      have h1 := hclean c hc
      exact ⟨⟨h1.1.1, h1.2⟩, h1.1.2⟩
    · simp at hr

private theorem renderKey_head_clean (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) :
    ∃ c cs, rk.toList = c :: cs ∧ isHorizWs c = false ∧ c ≠ '.' := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk
      subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      rcases hbare with ⟨hne, hall⟩
      cases hk : k.toList with
      | nil =>
        have hk0 : k = "" := by rw [← String.ofList_toList (s := k), hk]
        subst hk0; simp at hne
      | cons c cs =>
        have hbc := List.all_eq_true.mp hall c (by rw [hk]; simp)
        have hws : isHorizWs c = false := by
          by_cases h1 : c = ' '
          · subst h1; simp [isBareKeyChar] at hbc
          · by_cases h2 : c = '\t'
            · subst h2; simp [isBareKeyChar] at hbc
            · simp [isHorizWs, h1, h2]
        have hndot : c ≠ '.' := by
          intro h; subst h; simp [isBareKeyChar] at hbc
        exact ⟨c, cs, rfl, hws, hndot⟩
    · simp at hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk
    subst hrk
    have hq : ("\"" : String).toList = ['"'] := rfl
    refine ⟨'"', (escapeBasicBody false k ++ "\"").toList, ?_, by decide, by decide⟩
    simp [String.toList_append, hq]
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · injection hr with hrk
      subst hrk
      have hq : ("'" : String).toList = ['\''] := rfl
      refine ⟨'\'', (k ++ "'").toList, ?_, by decide, by decide⟩
      simp [String.toList_append, hq]
    · simp at hr

private theorem skipHorizWs_cons_false (c : Char) (cs : List Char) (hc : isHorizWs c = false) :
    skipHorizWs (c :: cs) = c :: cs := by
  simp [skipHorizWs, hc]

private theorem joinRenderedPath_head_clean (r : String) (rs : List String)
    (hhead : ∃ c cs, r.toList = c :: cs ∧ isHorizWs c = false) :
    ∃ c cs, (joinRenderedPath (r :: rs)).toList = c :: cs ∧ isHorizWs c = false := by
  rcases hhead with ⟨c, cs, hr, hc⟩
  cases rs with
  | nil => exact ⟨c, cs, by simp [joinRenderedPath, hr], hc⟩
  | cons r2 rs2 =>
    refine ⟨c, cs ++ '.' :: (joinRenderedPath (r2 :: rs2)).toList, ?_, hc⟩
    have hd : ("." : String).toList = ['.'] := rfl
    simp [joinRenderedPath, String.toList_append, hr, hd]

private theorem joinRenderedPath_clean (rks : List String)
    (hclean : ∀ r ∈ rks, (r.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) :
    ((joinRenderedPath rks).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  induction rks with
  | nil => simp [joinRenderedPath]
  | cons r rs ih =>
    cases rs with
    | nil => simpa [joinRenderedPath] using hclean r (by simp)
    | cons r2 rs2 =>
      have hr := hclean r (by simp)
      have hrs := ih (fun x hx => hclean x (by simp [hx]))
      have hd : ((".") : String).toList = ['.'] := rfl
      have hdc : (['.'].all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by decide
      simp only [joinRenderedPath, String.toList_append, hd, List.all_append, hr, hdc, hrs, Bool.and_true]

private theorem joinRenderedPath_parseDottedKeyFuel (ks : List (String × KeyStyle)) (rks : List String)
    (hne : ks ≠ []) (hr : ks.mapM (fun p => renderKey p.1 p.2) = some rks)
    (rest : List Char) (fuel : Nat) (hf : ks.length ≤ fuel)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hskip : ∀ c tail, skipHorizWs rest = c :: tail → c ≠ '.') :
    parseDottedKeyFuel fuel ((joinRenderedPath rks).toList ++ rest) =
      .ok (ks.map Prod.fst, skipHorizWs rest) := by
  induction ks generalizing rks fuel with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.mapM_cons, bind, Option.bind] at hr
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hr
      | some rk =>
        rw [hrp] at hr
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hr
        | some rps =>
          rw [hrps] at hr
          injection hr with hrks
          subst hrks
          cases ps with
          | nil =>
            simp only [List.mapM_nil] at hrps
            injection hrps with hrps0
            subst hrps0
            simp only [joinRenderedPath, List.map_cons, List.map_nil]
            have hseg := (renderKey_parseKeySegment p.1 p.2 rk hrp rest hrest).1
            simp only [parseDottedKeyFuel, hseg, bind, Except.bind]
            cases hsw : skipHorizWs rest with
            | nil => simp
            | cons c tail =>
              have hndot : c ≠ '.' := hskip c tail hsw
              simp [hndot]
          | cons q qs =>
            cases rps with
            | nil =>
              simp only [List.mapM_cons, bind, Option.bind] at hrps
              cases hq : renderKey q.1 q.2 with
              | none => simp [hq] at hrps
              | some _ =>
                simp only [hq] at hrps
                cases hqs : qs.mapM (fun p => renderKey p.1 p.2) <;> simp [hqs] at hrps
            | cons rk2 rks2 =>
              have hd : ("." : String).toList = ['.'] := rfl
              have hjoin : (joinRenderedPath (rk :: rk2 :: rks2)).toList ++ rest =
                  rk.toList ++ ('.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest)) := by
                simp [joinRenderedPath, String.toList_append, hd, List.append_assoc]
              have hdot : ∀ c tail, '.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest) = c :: tail →
                  !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'' := by
                intro c tail h; injection h with hc; subst hc; decide
              have hseg := (renderKey_parseKeySegment p.1 p.2 rk hrp
                ('.' :: ((joinRenderedPath (rk2 :: rks2)).toList ++ rest)) hdot).1
              have hq_render : renderKey q.1 q.2 = some rk2 := by
                simp only [List.mapM_cons, bind, Option.bind] at hrps
                cases hq : renderKey q.1 q.2 with
                | none => simp [hq] at hrps
                | some rk2' =>
                  simp only [hq] at hrps
                  cases hqs : qs.mapM (fun p => renderKey p.1 p.2) with
                  | none => simp [hqs] at hrps
                  | some rks2' =>
                    rw [hqs] at hrps
                    injection hrps with heq
                    injection heq with heq2
                    rw [heq2]
              obtain ⟨c2, cs2, hrk2, hws2, _⟩ := renderKey_head_clean q.1 q.2 rk2 hq_render
              obtain ⟨c', cs', hjoin_head, hws'⟩ :=
                joinRenderedPath_head_clean rk2 rks2 ⟨c2, cs2, hrk2, hws2⟩
              have hskip_tail : skipHorizWs ((joinRenderedPath (rk2 :: rks2)).toList ++ rest) =
                  (joinRenderedPath (rk2 :: rks2)).toList ++ rest := by
                rw [hjoin_head, List.cons_append, skipHorizWs_cons_false _ _ hws']
              have hsub : (q :: qs).length ≤ f := by simp at hf; omega
              rw [hjoin]
              simp only [parseDottedKeyFuel, hseg, bind, Except.bind, skipHorizWs,
                show isHorizWs '.' = false from rfl, Bool.false_eq_true, ↓reduceIte, hskip_tail]
              rw [ih (rk2 :: rks2) (by simp) hrps f hsub]
              simp

private theorem joinRenderedPath_parseDottedKey (ks : List (String × KeyStyle)) (rks : List String)
    (hne : ks ≠ []) (hr : ks.mapM (fun p => renderKey p.1 p.2) = some rks)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hskip : ∀ c tail, skipHorizWs rest = c :: tail → c ≠ '.') :
    parseDottedKey ((joinRenderedPath rks).toList ++ rest) =
      .ok (ks.map Prod.fst, skipHorizWs rest) ∧
    ((joinRenderedPath rks).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  have hlen_rks : ∀ (ls : List (String × KeyStyle)) (rs : List String),
      ls.mapM (fun p => renderKey p.1 p.2) = some rs → ls ≠ [] →
      ls.length ≤ (joinRenderedPath rs).toList.length := by
    intro ls
    induction ls with
    | nil => intro _ _ h; exact absurd rfl h
    | cons p ps ih =>
      intro rs hrs _
      simp only [List.mapM_cons, bind, Option.bind] at hrs
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hrs
      | some rk =>
        rw [hrp] at hrs
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hrs
        | some rps =>
          rw [hrps] at hrs
          injection hrs with hrs_eq
          subst hrs_eq
          obtain ⟨c, cs, hrk, _⟩ := renderKey_head_clean p.1 p.2 rk hrp
          cases ps with
          | nil =>
            simp only [List.mapM_nil] at hrps
            injection hrps with hrps0; subst hrps0
            simp [joinRenderedPath, hrk]
          | cons q qs =>
            cases rps with
            | nil =>
              simp only [List.mapM_cons, bind, Option.bind] at hrps
              cases hq : renderKey q.1 q.2 with
              | none => simp [hq] at hrps
              | some _ =>
                simp only [hq] at hrps
                cases hqs : qs.mapM (fun p => renderKey p.1 p.2) <;> simp [hqs] at hrps
            | cons rk2 rks2 =>
              have hsub := ih (rk2 :: rks2) hrps (by simp)
              have hd : ("." : String).toList = ['.'] := rfl
              simp only [joinRenderedPath, String.toList_append, hd, List.length_append, List.length_cons,
                hrk] at hsub ⊢
              omega
  have hf : ks.length ≤ ((joinRenderedPath rks).toList ++ rest).length + 1 := by
    have h1 := hlen_rks ks rks hr hne
    simp only [List.length_append]; omega
  refine ⟨joinRenderedPath_parseDottedKeyFuel ks rks hne hr rest _ hf hrest hskip, ?_⟩
  apply joinRenderedPath_clean
  intro r hr_mem
  have hex : ∃ p ∈ ks, renderKey p.1 p.2 = some r := by
    clear hlen_rks hf hrest hskip hne
    induction ks generalizing rks with
    | nil => simp at hr; subst hr; simp at hr_mem
    | cons p ps ih =>
      simp only [List.mapM_cons, bind, Option.bind] at hr
      cases hrp : renderKey p.1 p.2 with
      | none => simp [hrp] at hr
      | some rk =>
        rw [hrp] at hr
        cases hrps : ps.mapM (fun p => renderKey p.1 p.2) with
        | none => simp [hrps] at hr
        | some rps =>
          rw [hrps] at hr
          injection hr with hrs_eq; subst hrs_eq
          simp only [List.mem_cons] at hr_mem
          rcases hr_mem with rfl | hmem
          · exact ⟨p, by simp, hrp⟩
          · obtain ⟨q, hq_mem, hq_r⟩ := ih rps hrps hmem
            exact ⟨q, by simp [hq_mem], hq_r⟩
  rcases hex with ⟨⟨k, style⟩, _, hkr⟩
  exact (renderKey_parseKeySegment k style r hkr [] (by intro _ _ h; cases h)).2

private theorem parseValueFuel_basic (numApi : NumParseApi) (fuel : Nat) (cs : List Char)
    (hno3 : ¬ ∃ r, cs = '"' :: '"' :: r) :
    parseValueFuel numApi (fuel + 1) ('"' :: cs) =
      (parseBasicStringBody cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  split
  · exfalso; apply hno3; simp_all
  · rename_i heq; injection heq with _; subst_vars; rfl
  all_goals simp_all

private theorem parseValueFuel_multilineBasic (numApi : NumParseApi) (fuel : Nat) (cs : List Char) :
    parseValueFuel numApi (fuel + 1) ('"' :: '"' :: '"' :: cs) =
      (parseMultilineBasicString cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  rfl

private theorem parseValueFuel_literal (numApi : NumParseApi) (fuel : Nat) (cs : List Char)
    (hno3 : ¬ ∃ r, cs = '\'' :: '\'' :: r) :
    parseValueFuel numApi (fuel + 1) ('\'' :: cs) =
      (parseLiteralStringBody [] cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  split
  · simp_all
  · simp_all
  · exfalso; apply hno3; simp_all
  · rename_i heq; injection heq with _; subst_vars; rfl
  all_goals simp_all

private theorem parseValueFuel_multilineLiteral (numApi : NumParseApi) (fuel : Nat) (cs : List Char) :
    parseValueFuel numApi (fuel + 1) ('\'' :: '\'' :: '\'' :: cs) =
      (parseMultilineLiteralString cs >>= fun (s, after) => .ok (.string s, after)) := by
  conv => lhs; unfold parseValueFuel
  rfl

private theorem renderStringLiteral_parseValueFuel (numApi : NumParseApi) (s : String) (st : StringStyle)
    (rs : String) (hr : renderStringLiteral s st = some rs) (rest : List Char) (fuel : Nat) (hf : fuel ≥ 1)
    (hrest : ∀ c r, rest = c :: r → c ≠ '"' ∧ c ≠ '\'') :
    parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (.string s, rest) ∧
    (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
    ((st = .basic ∨ st = .literal) →
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) := by
  cases fuel with
  | zero => omega
  | succ f =>
    cases st with
    | basic =>
      simp only [renderStringLiteral] at hr
      injection hr with hrs; subst hrs
      have hno3 : ¬ ∃ r', ((escapeBasicBody false s).toList ++ '"' :: rest) = '"' :: '"' :: r' := by
        intro ⟨r', hr'⟩
        cases hs : s.toList with
        | nil =>
          have hbody : (escapeBasicBody false s).toList = [] := by simp [escapeBasicBody, hs]
          rw [hbody, List.nil_append] at hr'
          cases rest with
          | nil => simp at hr'
          | cons c t =>
            simp only [List.cons.injEq] at hr'
            exact (hrest c t rfl).1 hr'.2.1
        | cons c0 cs0 =>
          have hbody : (escapeBasicBody false s).toList =
              (escapeBasicChar false c0).toList ++ cs0.flatMap (fun c => (escapeBasicChar false c).toList) := by
            simp [escapeBasicBody, String.toList_join, hs, List.flatMap_map]
          rw [hbody, List.append_assoc] at hr'
          have hne : ((escapeBasicChar false c0).toList).head? ≠ some '"' := by
            by_cases h1 : c0 = '\\'
            · subst h1; decide
            · by_cases h2 : c0 = '"'
              · subst h2; decide
              · by_cases h3 : c0 = '\x08'
                · subst h3; decide
                · by_cases h4 : c0 = '\t'
                  · subst h4; decide
                  · by_cases h5 : c0 = '\n'
                    · subst h5; decide
                    · by_cases h6 : c0 = '\x0c'
                      · subst h6; decide
                      · by_cases h7 : c0 = '\r'
                        · subst h7; decide
                        · by_cases hc : isDisallowedControl c0 = true
                          · have hdef : escapeBasicChar false c0 =
                                "\\u00" ++ String.ofList [hexDigitUpper (c0.toNat / 16), hexDigitUpper (c0.toNat % 16)] := by
                              simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                            rw [hdef]
                            have hu : ("\\u00" : String).toList = ['\\', 'u', '0', '0'] := rfl
                            simp [hu]
                          · have hdef : escapeBasicChar false c0 = String.singleton c0 := by
                              simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, hc]
                            rw [hdef]; simp [h2]
          cases h0 : (escapeBasicChar false c0).toList with
          | nil =>
            have hlen := escapeBasicChar_length_pos false c0
            rw [h0] at hlen; simp at hlen
          | cons d0 _ =>
            rw [h0] at hr' hne
            injection hr' with hd0
            exact hne (by simp [hd0])
      have hq : ("\"" : String).toList = ['"'] := rfl
      have hparse : parseValueFuel numApi (f + 1) (("\"" ++ escapeBasicBody false s ++ "\"").toList ++ rest) =
          .ok (.string s, rest) := by
        simp only [String.toList_append, hq, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseValueFuel_basic numApi f _ hno3]
        simp [parseBasicStringBody_escapeBasicBody s rest, bind, Except.bind]
      have hcl := escapeBasicBody_clean false s
      have hq_cl : (("\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
        decide
      have hcl_inline : (("\"" ++ escapeBasicBody false s ++ "\"").toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n') = true := by
        simp only [String.toList_append, List.all_append, hq_cl, Bool.true_and, Bool.and_true]
        simpa [Bool.and_assoc] using hcl
      refine ⟨hparse, ?_, fun _ => hcl_inline⟩
      rw [List.all_eq_true]
      intro c hc
      have h1 := List.all_eq_true.mp hcl_inline c hc
      simp only [Bool.and_eq_true] at h1
      exact (Bool.and_eq_true _ _).mpr h1.1
    | multilineBasic =>
      simp only [renderStringLiteral] at hr
      injection hr with hrs; subst hrs
      have ho : ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] := rfl
      have hc : ("\"\"\"" : String).toList = ['"', '"', '"'] := rfl
      have hparse : parseValueFuel numApi (f + 1)
          (("\"\"\"\n" ++ escapeBasicBody true s ++ "\"\"\"").toList ++ rest) = .ok (.string s, rest) := by
        simp only [String.toList_append, ho, hc, List.cons_append, List.nil_append, List.append_assoc]
        rw [parseValueFuel_multilineBasic numApi f]
        have hrest_q : ∀ c r, rest = c :: r → c ≠ '"' := fun c r h => (hrest c r h).1
        have hm := parseMultilineBasicString_escapeBasicBody s rest hrest_q
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hm
        simp [hm, bind, Except.bind]
      have hcl := escapeBasicBody_clean true s
      have hoc : (("\"\"\"\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
      have hcc : (("\"\"\"" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
      refine ⟨hparse, ?_, fun h => by rcases h with h | h <;> cases h⟩
      simp only [String.toList_append, List.all_append, hoc, hcc, Bool.true_and, Bool.and_true]
      simpa using hcl
    | literal =>
      simp only [renderStringLiteral] at hr
      split at hr
      · rename_i hcond
        injection hr with hrs; subst hrs
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨hclean, hnoq⟩
        have hnq := not_mem_of_contains_false s '\'' hnoq
        have hnl : '\n' ∉ s.toList := fun h => (isSingleLineClean_no_nl s hclean '\n' h).1 rfl
        have hno3 : ¬ ∃ r', (s.toList ++ '\'' :: rest) = '\'' :: '\'' :: r' := by
          intro ⟨r', hr'⟩
          cases hs : s.toList with
          | nil =>
            rw [hs, List.nil_append] at hr'
            cases rest with
            | nil => simp at hr'
            | cons c t =>
              simp only [List.cons.injEq] at hr'
              exact (hrest c t rfl).2 hr'.2.1
          | cons c0 _ =>
            rw [hs, List.cons_append] at hr'
            injection hr' with hc0
            exact hnq (by rw [hs, hc0]; simp)
        have hq : ("'" : String).toList = ['\''] := rfl
        have hparse : parseValueFuel numApi (f + 1) (("'" ++ s ++ "'").toList ++ rest) = .ok (.string s, rest) := by
          simp only [String.toList_append, hq, List.cons_append, List.nil_append, List.append_assoc]
          rw [parseValueFuel_literal numApi f _ hno3]
          simp [parseLiteralStringBody_list s.toList [] rest hnl hnq, String.ofList_toList, bind, Except.bind]
        have hq_cl : (("'" : String).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
          decide
        have hcl_inline : (("'" ++ s ++ "'").toList.all fun c =>
            !isDisallowedControl c && c != '\r' && c != '\n') = true := by
          simp only [String.toList_append, List.all_append, hq_cl, Bool.true_and, Bool.and_true]
          simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hclean ⊢
          intro c hc
          have h1 := hclean c hc
          exact ⟨⟨h1.1.1, h1.2⟩, h1.1.2⟩
        refine ⟨hparse, ?_, fun _ => hcl_inline⟩
        rw [List.all_eq_true]
        intro c hc
        have h1 := List.all_eq_true.mp hcl_inline c hc
        simp only [Bool.and_eq_true] at h1
        exact (Bool.and_eq_true _ _).mpr h1.1
      · simp at hr
    | multilineLiteral =>
      simp only [renderStringLiteral] at hr
      split at hr
      · rename_i hcond
        injection hr with hrs; subst hrs
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨⟨hclean, hno_sub⟩, hno_end⟩
        have hno3 := no_triple_quote_of_not_containsSubstr s hno_sub
        have hnoend := getLast_ne_quote_of_not_endsWith s hno_end
        have ho : ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] := rfl
        have hc : ("'''" : String).toList = ['\'', '\'', '\''] := rfl
        have hrest_q : ∀ c r, rest = c :: r → c ≠ '\'' := fun c r h => (hrest c r h).2
        have hparse : parseValueFuel numApi (f + 1) (("'''\n" ++ s ++ "'''").toList ++ rest) =
            .ok (.string s, rest) := by
          simp only [String.toList_append, ho, hc, List.cons_append, List.nil_append, List.append_assoc]
          rw [parseValueFuel_multilineLiteral numApi f]
          unfold parseMultilineLiteralString
          dsimp only
          have hlen : (s.toList ++ ['\'', '\'', '\''] ++ rest).length + 1 ≥ s.toList.length + 1 := by
            simp only [List.length_append]; omega
          have hm := parseMultilineLiteralBodyFuel_list s.toList [] rest _ hno3 hnoend hrest_q hlen
          simp only [List.reverse_nil, List.nil_append, String.ofList_toList, List.append_assoc,
            List.cons_append, List.nil_append, List.length_append, List.length_cons] at hm ⊢
          rw [hm]
          simp [bind, Except.bind]
        have hoc : (("'''\n" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
        have hcc : (("'''" : String).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by decide
        refine ⟨hparse, ?_, fun h => by rcases h with h | h <;> cases h⟩
        simp only [String.toList_append, List.all_append, hoc, hcc, Bool.true_and, Bool.and_true]
        simpa using hclean
      · simp at hr

private theorem twoDigitsNat?_isAscii (c1 c2 : Char) (n : Nat) (h : twoDigitsNat? c1 c2 = some n) :
    isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true := by
  simp only [twoDigitsNat?] at h
  split at h
  · rename_i hc; exact (Bool.and_eq_true _ _).mp hc
  · simp at h

private theorem fourDigitsNat?_isAscii (c1 c2 c3 c4 : Char) (n : Nat)
    (h : fourDigitsNat? c1 c2 c3 c4 = some n) :
    isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true ∧ isAsciiDigit c3 = true ∧ isAsciiDigit c4 = true := by
  simp only [fourDigitsNat?] at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true] at hc; exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · simp at h

private theorem padNatZero_clean_val (w n : Nat) :
    ((padNatZero w n).toList.all fun c =>
      !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  rw [List.all_eq_true]
  intro c hc
  have h1 := List.all_eq_true.mp (padNatZero_clean w n) c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact ⟨⟨⟨h1.1.1.1.2, h1.1.1.2⟩, h1.1.2⟩, h1.2⟩

private theorem dite_true {α : Type} {P : Prop} [Decidable P] {f : P → α} {g : ¬ P → α} (h : P) :
    dite P f g = f h := by
  split
  · rfl
  · rename_i hneg; exact absurd h hneg

private theorem renderDate_parseDatePart (d : Std.Time.PlainDate) (ds : String) (rest : List Char)
    (hr : renderDate d = some ds) :
    parseDatePart (ds.toList ++ rest) = .ok (d, rest) ∧
    hasDatePrefix (ds.toList ++ rest) = true ∧
    (ds.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderDate] at hr
  split at hr
  · rename_i hvd
    injection hr with hds
    subst hds
    have hv : (0 : Int) ≤ d.year ∧ d.year ≤ 9999 := by simpa [validTomlDate] using hvd
    have hv_int : (0 : Int) ≤ (d.year : Int) ∧ (d.year : Int) ≤ 9999 := hv
    have h_eq : Int.ofNat (d.year : Int).toNat = (d.year : Int) := Int.toNat_of_nonneg hv_int.1
    have hy_nat : d.year.toNat < 10000 := by
      have hle : Int.ofNat (d.year : Int).toNat ≤ 9999 := by rw [h_eq]; exact hv_int.2
      exact Int.ofNat_lt.mp (by omega)
    have hm_prop := d.month.property
    have hm_nat : d.month.val.toNat < 100 := by omega
    have hd_prop := d.day.property
    have hd_nat : d.day.val.toNat < 100 := by omega
    obtain ⟨y1, y2, y3, y4, hy_list, hy_four⟩ :=
      padNatZero_4_digits d.year.toNat hy_nat
    obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ :=
      twoDigits_padNatZero d.month.val.toNat hm_nat
    obtain ⟨d1, d2, hd_list, hd_two, _, _⟩ :=
      twoDigits_padNatZero d.day.val.toNat hd_nat
    have hdash : ("-" : String).toList = ['-'] := rfl
    have hlist : (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] := by
      simp only [String.toList_append, hy_list, hdash, hm_list, hd_list]
      rfl
    have hy_eq : Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat) = d.year :=
      Int.toNat_of_nonneg hv.1
    have hm_ok : d.month.val.toNat ≥ 1 ∧ d.month.val.toNat ≤ 12 := ⟨by omega, by omega⟩
    have hm_eq : Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok = d.month := by
      apply Subtype.ext
      exact Int.toNat_of_nonneg (by omega)
    have hd_ok : d.day.val.toNat ≥ 1 ∧ d.day.val.toNat ≤ 31 := ⟨by omega, by omega⟩
    have hd_eq : Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok = d.day := by
      apply Subtype.ext
      exact Int.toNat_of_nonneg (by omega)
    have hcal : Std.Time.PlainDate.ofYearMonthDay?
        (Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat))
        (Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok)
        (Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok) = some d := by
      rw [hy_eq, hm_eq, hd_eq, Std.Time.PlainDate.ofYearMonthDay?]
      exact dite_true d.valid
    have hparse : parseDatePart ((padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList ++ rest) = .ok (d, rest) := by
      rw [hlist]
      simp only [List.cons_append, List.nil_append, parseDatePart, hy_four, hm_two, hd_two]
      rw [dite_true hm_ok, dite_true hd_ok, hcal]
      simp [hvd]
    have hpref : hasDatePrefix ((padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++
        padNatZero 2 d.day.val.toNat).toList ++ rest) = true := by
      rw [hlist]
      obtain ⟨ay1, ay2, ay3, ay4⟩ := fourDigitsNat?_isAscii y1 y2 y3 y4 d.year.toNat hy_four
      obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii m1 m2 d.month.val.toNat hm_two
      obtain ⟨ad1, ad2⟩ := twoDigitsNat?_isAscii d1 d2 d.day.val.toNat hd_two
      simp [hasDatePrefix, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2]
    refine ⟨hparse, hpref, ?_⟩
    have hdash_cl : ("-".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
      decide
    simp only [String.toList_append, List.all_append, padNatZero_clean_val, hdash_cl, Bool.and_self]
  · simp at hr

private theorem pow10Nat_pos (k : Nat) : 0 < pow10Nat k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [pow10Nat]; omega

private theorem pow10Nat_add (a b : Nat) : pow10Nat (a + b) = pow10Nat a * pow10Nat b := by
  induction a with
  | zero => simp [pow10Nat]
  | succ a ih =>
    rw [Nat.succ_add, pow10Nat, ih, pow10Nat, Nat.mul_assoc]

private theorem pow10Nat_9 : pow10Nat 9 = 1000000000 := rfl

private theorem toString_length_le_pow10 (w n : Nat) (hw : 1 ≤ w) (hn : n < pow10Nat w) :
    (toString n).length ≤ w := by
  induction w generalizing n with
  | zero => omega
  | succ w ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, _⟩ := toString_lt10_char n h10
      have hlen : (toString n).length = (toString n).toList.length := by
        change (Nat.repr n).length = (Nat.repr n).toList.length; simp [Nat.repr]
      rw [hlen, hch]; simp
    · have hw1 : 1 ≤ w := by
        cases w with
        | zero => simp [pow10Nat] at hn; omega
        | succ _ => omega
      have hdiv_lt : n / 10 < pow10Nat w := by
        simp only [pow10Nat] at hn
        omega
      have hsub := ih (n / 10) hw1 hdiv_lt
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      have hlen : ∀ m : Nat, (toString m).length = (toString m).toList.length := by
        intro m; change (Nat.repr m).length = (Nat.repr m).toList.length; simp [Nat.repr]
      rw [hlen n, hlen (n / 10)] at *
      rw [hsplit, List.length_append, List.length_singleton]
      omega

private theorem foldl_digits_add (ds : List Char) (init : Nat)
    (hds : ds.all isAsciiDigit = true) :
    ds.foldl (fun a c => a * 10 + digitVal c) init =
      init * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
  induction ds generalizing init with
  | nil => simp [pow10Nat]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (init * 10 + digitVal c) hds.2, ih (digitVal c) hds.2, pow10Nat]
    calc
      (init * 10 + digitVal c) * pow10Nat cs.length + List.foldl (fun a c => a * 10 + digitVal c) 0 cs
        = init * (10 * pow10Nat cs.length) +
            (digitVal c * pow10Nat cs.length + List.foldl (fun a c => a * 10 + digitVal c) 0 cs) := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem toString_foldl_digits (n : Nat) :
    (toString n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, _, hdv, _⟩ := toString_lt10_char n h10
      rw [hch]
      simp [hdv]
    · have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      obtain ⟨_, _, hdv, _⟩ := toString_lt10_char (n % 10) (Nat.mod_lt n (by decide))
      rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_nil, hdv, ih (n / 10) (by omega)]
      omega

private theorem padNatZero_foldl_digits (w n : Nat) :
    (padNatZero w n).toList.foldl (fun a c => a * 10 + digitVal c) 0 = n := by
  unfold padNatZero
  dsimp only
  by_cases hge : (toString n).length ≥ w
  · simp only [hge, ↓reduceIte, toString_foldl_digits]
  · simp only [hge, ↓reduceIte, String.toList_append, String.toList_ofList, List.foldl_append]
    have hzeros : ∀ k, (List.replicate k '0').foldl (fun a c => a * 10 + digitVal c) 0 = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ, List.foldl_cons]
        have hd0 : digitVal '0' = 0 := rfl
        rw [Nat.zero_mul, Nat.zero_add, hd0]
        exact ih
    rw [hzeros, toString_foldl_digits]

private theorem takeDigits_append (acc ds rest : List Char)
    (hds : ds.all isAsciiDigit = true)
    (hrest : ∀ c r, rest = c :: r → isAsciiDigit c = false) :
    takeDigits acc (ds ++ rest) = (acc.reverse ++ ds, rest) := by
  induction ds generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeDigits]
    | cons c r => simp [takeDigits, hrest c r rfl]
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp only [List.cons_append, takeDigits, hds.1, ↓reduceIte]
    rw [ih (d :: acc) hds.2]
    simp

private theorem fracDigitsToNanosAux_append (k acc : Nat) (ds1 ds2 : List Char)
    (hlen : ds1.length ≤ k) (hds1 : ds1.all isAsciiDigit = true) :
    fracDigitsToNanosAux k acc (ds1 ++ ds2) =
      fracDigitsToNanosAux (k - ds1.length)
        (acc * pow10Nat ds1.length + ds1.foldl (fun a c => a * 10 + digitVal c) 0) ds2 := by
  induction ds1 generalizing k acc with
  | nil => simp [pow10Nat]
  | cons d ds ih =>
    cases k with
    | zero => simp at hlen
    | succ k' =>
      simp only [List.length_cons, List.all_cons, Bool.and_eq_true] at hlen hds1
      simp only [List.cons_append, fracDigitsToNanosAux]
      rw [ih k' (acc * 10 + digitVal d) (by omega) hds1.2]
      have hfold : (d :: ds).foldl (fun a c => a * 10 + digitVal c) 0 =
          digitVal d * pow10Nat ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
        simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
        exact foldl_digits_add ds (digitVal d) hds1.2
      rw [hfold]
      simp only [List.length_cons, pow10Nat]
      congr 1
      · omega
      · rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem fracDigitsToNanosAux_nil (k acc : Nat) :
    fracDigitsToNanosAux k acc [] = acc * pow10Nat k := by
  induction k generalizing acc with
  | zero => simp [fracDigitsToNanosAux, pow10Nat]
  | succ k ih =>
    simp only [fracDigitsToNanosAux, pow10Nat, ih (acc * 10)]
    rw [Nat.mul_assoc, Nat.mul_comm 10 (pow10Nat k)]

private theorem parseTimePart_digits_nofrac (h1 h2 m1 m2 s1 s2 : Char) (hh mm ss : Nat)
    (hh_two : twoDigitsNat? h1 h2 = some hh)
    (hm_two : twoDigitsNat? m1 m2 = some mm)
    (hs_two : twoDigitsNat? s1 s2 = some ss)
    (hh_ok : hh ≤ 23) (mm_ok : mm ≤ 59) (ss_ok : ss ≤ 59)
    (rest : List Char) (hndot : ∀ r, rest ≠ '.' :: r) :
    parseTimePart ([h1, h2, ':', m1, m2, ':', s1, s2] ++ rest) =
      .ok (Std.Time.PlainTime.mk
        (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
        (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
        (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
        0, rest) := by
  simp only [List.cons_append, List.nil_append, parseTimePart, hh_two, hm_two, hs_two,
    hh_ok, mm_ok, ss_ok, ↓reduceDIte]

private theorem parseTimePart_digits_frac (h1 h2 m1 m2 s1 s2 : Char) (hh mm ss : Nat)
    (hh_two : twoDigitsNat? h1 h2 = some hh)
    (hm_two : twoDigitsNat? m1 m2 = some mm)
    (hs_two : twoDigitsNat? s1 s2 = some ss)
    (hh_ok : hh ≤ 23) (mm_ok : mm ≤ 59) (ss_ok : ss ≤ 59)
    (fracDs rest : List Char)
    (htake : takeDigits [] (fracDs ++ rest) = (fracDs, rest))
    (hne : fracDs.isEmpty = false) :
    parseTimePart ([h1, h2, ':', m1, m2, ':', s1, s2] ++ '.' :: (fracDs ++ rest)) =
      .ok (Std.Time.PlainTime.mk
        (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
        (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
        (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
        (Std.Time.Nanosecond.Ordinal.ofNat (fracDigitsToNanos fracDs) (Nat.min_le_left _ _)),
        rest) := by
  simp only [List.cons_append, List.nil_append, parseTimePart, hh_two, hm_two, hs_two,
    hh_ok, mm_ok, ss_ok, ↓reduceDIte, htake, hne, Bool.false_eq_true, ↓reduceIte]

private theorem renderTime_parseTimePart (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (rest : List Char)
    (hr : renderTime t fd = some ts)
    (hrest : ∀ c r, rest = c :: r → isAsciiDigit c = false ∧ (fd = 0 → c ≠ '.')) :
    parseTimePart (ts.toList ++ rest) = .ok (t, rest) ∧
    hasTimePrefix (ts.toList ++ rest) = true ∧
    (ts.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderTime] at hr
  split at hr
  · simp at hr
  · rename_i hvt
    simp only [Bool.not_eq_true] at hvt
    have hvt_sec : t.second.val ≤ 59 := by simpa [validTomlTime] using hvt
    cases hfrac : formatNanosExact t.nanosecond.val.toNat fd with
    | none => simp [hfrac] at hr
    | some frac =>
      rw [hfrac] at hr
      injection hr with hts
      subst hts
      have hh_prop := t.hour.property
      have hm_prop := t.minute.property
      have hs_prop := t.second.property
      have hn_prop := t.nanosecond.property
      have hh_nat : t.hour.val.toNat < 100 := by omega
      have hm_nat : t.minute.val.toNat < 100 := by omega
      have hs_nat : t.second.val.toNat < 100 := by omega
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat hm_nat
      obtain ⟨s1, s2, hs_list, hs_two, _, _⟩ := twoDigits_padNatZero t.second.val.toNat hs_nat
      have hh_ok : t.hour.val.toNat ≤ 23 := by omega
      have mm_ok : t.minute.val.toNat ≤ 59 := by omega
      have ss_ok : t.second.val.toNat ≤ 59 := by omega
      have hh_eq : Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok = t.hour := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have mm_eq : Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok = t.minute := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have ss_eq : Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)) =
          t.second := by
        apply Subtype.ext; exact Int.toNat_of_nonneg (by omega)
      have hcol : (":" : String).toList = [':'] := rfl
      have hbase : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat).toList = [h1, h2, ':', m1, m2, ':', s1, s2] := by
        simp only [String.toList_append, hh_list, hcol, hm_list, hs_list]; rfl
      have hcol_cl : (":".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        decide
      have hpref : hasTimePrefix ((padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat ++ frac).toList ++ rest) = true := by
        rw [String.toList_append, List.append_assoc, hbase]
        obtain ⟨ah1, ah2⟩ := twoDigitsNat?_isAscii h1 h2 t.hour.val.toNat hh_two
        obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii m1 m2 t.minute.val.toNat hm_two
        obtain ⟨as1, as2⟩ := twoDigitsNat?_isAscii s1 s2 t.second.val.toNat hs_two
        simp [hasTimePrefix, ah1, ah2, am1, am2, as1, as2]
      simp only [formatNanosExact] at hfrac
      by_cases hgt9 : fd > 9
      · simp [hgt9] at hfrac
      · simp only [hgt9, ↓reduceIte] at hfrac
        by_cases hfd0 : fd = 0
        · subst hfd0
          simp only [beq_self_eq_true, ↓reduceIte] at hfrac
          by_cases hn0 : t.nanosecond.val.toNat = 0
          · simp only [hn0, beq_self_eq_true, ↓reduceIte] at hfrac
            injection hfrac with hfr; subst hfr
            have hn_eq : (0 : Std.Time.Nanosecond.Ordinal) = t.nanosecond := by
              apply Subtype.ext
              change (0 : Int) = t.nanosecond.val
              omega
            have htm : Std.Time.PlainTime.mk
                (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok)
                (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
                (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)))
                0 = t := by
              apply Std.Time.PlainTime.ext
              · exact hh_eq
              · exact mm_eq
              · exact ss_eq
              · exact hn_eq
            have hparse : parseTimePart ((padNatZero 2 t.hour.val.toNat ++ ":" ++
                padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++ "").toList ++ rest) =
                .ok (t, rest) := by
              rw [String.append_empty, hbase]
              have hndot : ∀ r, rest ≠ '.' :: r := by
                intro r hr'
                exact (hrest '.' r hr').2 rfl rfl
              rw [parseTimePart_digits_nofrac h1 h2 m1 m2 s1 s2 _ _ _ hh_two hm_two hs_two hh_ok mm_ok ss_ok rest hndot, htm]
            refine ⟨hparse, hpref, ?_⟩
            simp only [String.append_empty, String.toList_append, List.all_append, padNatZero_clean_val,
              hcol_cl, Bool.and_self]
          · simp [hn0] at hfrac
        · have hfd_ne : (fd == 0) = false := beq_false_of_ne hfd0
          simp only [hfd_ne, Bool.false_eq_true, ↓reduceIte] at hfrac
          by_cases hmod : t.nanosecond.val.toNat % pow10Nat (9 - fd) = 0
          · simp only [hmod, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hfrac
            injection hfrac with hfr; subst hfr
            have hn_lt9 : t.nanosecond.val.toNat < pow10Nat 9 := by
              rw [pow10Nat_9]; omega
            have hfd_pos : 1 ≤ fd := by omega
            have hfd_le9 : fd ≤ 9 := by omega
            have hdiv_lt : t.nanosecond.val.toNat / pow10Nat (9 - fd) < pow10Nat fd := by
              have h9 : fd + (9 - fd) = 9 := by omega
              have hsplit_p : pow10Nat fd * pow10Nat (9 - fd) = pow10Nat 9 := by
                rw [← pow10Nat_add, h9]
              exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, hsplit_p]; exact hn_lt9)
            have hlen_str := toString_length_le_pow10 fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))
              hfd_pos hdiv_lt
            have hlen_pad := padNatZero_length_of_toString_le fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))
              hlen_str
            have hpad_digits : ((padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList).all
                isAsciiDigit = true := by
              rw [List.all_eq_true]
              intro c hc
              have h1 := List.all_eq_true.mp (padNatZero_clean fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))) c hc
              simp only [Bool.and_eq_true] at h1
              exact h1.1.1.1.1
            have htake := takeDigits_append []
              (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList rest
              hpad_digits (fun c r h => (hrest c r h).1)
            simp only [List.reverse_nil, List.nil_append] at htake
            have hne_empty : ((padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList).isEmpty = false := by
              cases hpl : (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList with
              | nil => rw [hpl] at hlen_pad; simp at hlen_pad; omega
              | cons _ _ => rfl
            have hnano_eq : fracDigitsToNanos
                (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList = t.nanosecond.val.toNat := by
              simp only [fracDigitsToNanos]
              rw [← List.append_nil (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList]
              rw [fracDigitsToNanosAux_append 9 0 _ [] (by rw [hlen_pad]; omega) hpad_digits]
              rw [Nat.zero_mul, Nat.zero_add, padNatZero_foldl_digits, fracDigitsToNanosAux_nil, hlen_pad]
              have hmul : (t.nanosecond.val.toNat / pow10Nat (9 - fd)) * pow10Nat (9 - fd) =
                  t.nanosecond.val.toNat := by
                have hd := Nat.div_add_mod t.nanosecond.val.toNat (pow10Nat (9 - fd))
                rw [hmod, Nat.add_zero, Nat.mul_comm] at hd
                exact hd
              rw [hmul]
              exact Nat.min_eq_right (by omega)
            have hn_eq : Std.Time.Nanosecond.Ordinal.ofNat
                (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)
                (Nat.min_le_left _ _) = t.nanosecond := by
              apply Subtype.ext
              change (Int.ofNat (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)) =
                t.nanosecond.val
              rw [hnano_eq]
              exact Int.toNat_of_nonneg (by omega)
            have htm : Std.Time.PlainTime.mk
                (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok)
                (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
                (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide)))
                (Std.Time.Nanosecond.Ordinal.ofNat
                  (fracDigitsToNanos (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList)
                  (Nat.min_le_left _ _)) = t := by
              apply Std.Time.PlainTime.ext
              · exact hh_eq
              · exact mm_eq
              · exact ss_eq
              · exact hn_eq
            have hdot : ("." : String).toList = ['.'] := rfl
            have hparse : parseTimePart ((padNatZero 2 t.hour.val.toNat ++ ":" ++
                padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++
                ("." ++ padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd)))).toList ++ rest) =
                .ok (t, rest) := by
              rw [String.toList_append, List.append_assoc, hbase, String.toList_append, hdot]
              have hfrac_call := parseTimePart_digits_frac h1 h2 m1 m2 s1 s2 _ _ _ hh_two hm_two hs_two
                hh_ok mm_ok ss_ok
                (padNatZero fd (t.nanosecond.val.toNat / pow10Nat (9 - fd))).toList rest htake hne_empty
              simp only [List.cons_append, List.nil_append] at hfrac_call ⊢
              rw [hfrac_call, htm]
            refine ⟨hparse, hpref, ?_⟩
            have hdot_cl : (".".toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
              decide
            simp only [String.toList_append, List.all_append, padNatZero_clean_val, hcol_cl, hdot_cl, Bool.and_self]
          · simp [hmod] at hfrac

private theorem renderOffset_parseOffsetPart (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String)
    (hr : renderOffset o style = some os) :
    parseOffsetPart os.toList = .ok o ∧
    (os.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [renderOffset] at hr
  split at hr
  · simp at hr
  · rename_i hvo
    simp only [Bool.not_eq_true] at hvo
    have hvo' : o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340 := by
      simpa [validTomlOffset] using hvo
    by_cases hz : o.second.val = 0
    · have ho_eq : Std.Time.TimeZone.Offset.ofSeconds 0 = o := by
        apply Std.Time.TimeZone.Offset.ext
        apply Std.Time.Internal.UnitVal.ext
        exact hz.symm
      simp only [hz, beq_self_eq_true, ↓reduceIte] at hr
      cases style with
      | upperZ =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("Z" : String).toList = ['Z'] := rfl
        rw [hlist, parseOffsetPart, ho_eq]
      | lowerZ =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("z" : String).toList = ['z'] := rfl
        rw [hlist, parseOffsetPart, ho_eq]
      | numeric =>
        injection hr with hos; subst hos
        refine ⟨?_, by decide⟩
        have hlist : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
        have h00 : twoDigitsNat? '0' '0' = some 0 := rfl
        have hstep : parseOffsetPart ['+', '0', '0', ':', '0', '0'] =
            .ok (Std.Time.TimeZone.Offset.ofSeconds 0) := by
          simp [parseOffsetPart, h00, validTomlOffset]
          rfl
        rw [hlist, hstep, ho_eq]
    · have hne : (o.second.val == 0) = false := beq_false_of_ne hz
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hr
      injection hr with hos; subst hos
      have habs_lt : o.second.val.natAbs / 60 ≤ 1439 := by omega
      have hdiv_lt : o.second.val.natAbs / 60 / 60 ≤ 23 := by omega
      have hmod_lt : (o.second.val.natAbs / 60) % 60 ≤ 59 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ :=
        twoDigits_padNatZero (o.second.val.natAbs / 60 / 60) (by omega)
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ :=
        twoDigits_padNatZero ((o.second.val.natAbs / 60) % 60) (by omega)
      have hdiv60 : (o.second.val.natAbs / 60) * 60 = o.second.val.natAbs := by
        have hm0 : o.second.val.natAbs % 60 = 0 := by omega
        have hd := Nat.div_add_mod o.second.val.natAbs 60
        rw [hm0, Nat.add_zero, Nat.mul_comm] at hd
        exact hd
      have htotal_nat : (o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60 =
          o.second.val.natAbs := by
        have hsub : (o.second.val.natAbs / 60 / 60) * 60 + (o.second.val.natAbs / 60) % 60 =
            o.second.val.natAbs / 60 := by
          omega
        calc
          (o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60
            = ((o.second.val.natAbs / 60 / 60) * 60 + (o.second.val.natAbs / 60) % 60) * 60 := by
              rw [Nat.add_mul, Nat.mul_assoc]
          _ = (o.second.val.natAbs / 60) * 60 := by rw [hsub]
          _ = o.second.val.natAbs := hdiv60
      have htotal_pos : 0 < o.second.val.natAbs := Int.natAbs_pos.mpr hz
      have hsec_eq : (if Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60) == 0 then (0 : Int)
          else if (if o.second.val < 0 then '-' else '+') == '-' then
            -Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60)
          else Int.ofNat ((o.second.val.natAbs / 60 / 60) * 3600 + ((o.second.val.natAbs / 60) % 60) * 60)) =
          o.second.val := by
        rw [htotal_nat]
        have hnz : (Int.ofNat o.second.val.natAbs == 0) = false :=
          beq_false_of_ne (by change (o.second.val.natAbs : Int) ≠ 0; omega)
        simp only [hnz, Bool.false_eq_true, ↓reduceIte]
        by_cases hneg : o.second.val < 0
        · simp only [hneg, ↓reduceIte, beq_self_eq_true]
          change -(o.second.val.natAbs : Int) = o.second.val
          omega
        · simp only [hneg, ↓reduceIte]
          have hne_sign : ('+' == '-') = false := rfl
          simp only [hne_sign, Bool.false_eq_true, ↓reduceIte]
          change (o.second.val.natAbs : Int) = o.second.val
          omega
      have ho_eq : Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt o.second.val) = o := by
        apply Std.Time.TimeZone.Offset.ext
        apply Std.Time.Internal.UnitVal.ext
        rfl
      have hcol : (":" : String).toList = [':'] := rfl
      have hsign_char : (if o.second.val < 0 then "-" else "+").toList = [if o.second.val < 0 then '-' else '+'] := by
        split <;> rfl
      have hlist : ((if o.second.val < 0 then "-" else "+") ++
          padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++
          padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList =
          [if o.second.val < 0 then '-' else '+', h1, h2, ':', m1, m2] := by
        simp only [String.toList_append, hsign_char, hh_list, hcol, hm_list]
        rfl
      have hparse : parseOffsetPart (((if o.second.val < 0 then "-" else "+") ++
          padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++
          padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList) = .ok o := by
        rw [hlist]
        simp only [parseOffsetPart, hh_two, hm_two]
        have hsign_ok : ((if o.second.val < 0 then '-' else '+') == '+' ||
            (if o.second.val < 0 then '-' else '+') == '-') = true := by
          split <;> decide
        have hbound_ok : (decide (o.second.val.natAbs / 60 / 60 ≤ 23) &&
            decide ((o.second.val.natAbs / 60) % 60 ≤ 59)) = true := by
          simp [hdiv_lt, hmod_lt]
        have hvo_t : validTomlOffset o = true := by simpa using hvo
        simp only [hsign_ok, ↓reduceIte, hbound_ok]
        rw [hsec_eq, ho_eq, hvo_t]
        simp only [↓reduceIte]
      refine ⟨hparse, ?_⟩
      have hsign_cl : ((if o.second.val < 0 then "-" else "+").toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        split <;> decide
      have hcol_cl : (":".toList.all fun c =>
          !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
        decide
      simp only [String.toList_append, List.all_append, hsign_cl, padNatZero_clean_val, hcol_cl, Bool.and_self]

private theorem isUnquotedDelim_asciiDigit (c : Char) (h : isAsciiDigit c = true) :
    isUnquotedDelim c = false := by
  have h1 : '0' ≤ c ∧ c ≤ '9' := by
    simpa [isAsciiDigit] using h
  have hne : c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;>
      exact absurd h1 (by decide)
  simp [isUnquotedDelim, isHorizWs, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1,
    hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2]

private theorem not_unquotedDelim_of_not_ws (c : Char)
    (hws : c.isWhitespace = false) (hn : c != '#') (hc : c != ',')
    (hb : c != ']') (hrb : c != '}') : isUnquotedDelim c = false := by
  have hsp : c ≠ ' ' := by
    intro h; subst h; exact absurd (by decide : (' ').isWhitespace = true) (by simp [hws])
  have htb : c ≠ '\t' := by
    intro h; subst h; exact absurd (by decide : ('\t').isWhitespace = true) (by simp [hws])
  have hnl : c ≠ '\n' := by
    intro h; subst h; exact absurd (by decide : ('\n').isWhitespace = true) (by simp [hws])
  simp only [bne_iff_ne, ne_eq] at hn hc hb hrb
  simp [isUnquotedDelim, isHorizWs, hsp, htb, hnl, hn, hc, hb, hrb]

private theorem takeNonDelim_append (acc tok rest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeNonDelim acc (tok ++ rest) = (acc.reverse ++ tok, rest) := by
  induction tok generalizing acc with
  | nil =>
    cases rest with
    | nil => simp [takeNonDelim]
    | cons c r => simp [takeNonDelim, hrest c r rfl]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at htok
    simp only [List.cons_append, takeNonDelim, htok.1, Bool.false_eq_true, ↓reduceIte]
    rw [ih (c :: acc) htok.2]
    simp

private theorem list_append_split_cases {α : Type} (l1 l2 a b : List α) (x : α)
    (h : l1 ++ l2 = a ++ x :: b) :
    (∃ c ∈ a, ∃ r, l2 = c :: r) ∨ (l1 = a ∧ l2 = x :: b) ∨ x ∈ l1 := by
  induction a generalizing l1 with
  | nil =>
    cases l1 with
    | nil => exact Or.inr (Or.inl ⟨rfl, h⟩)
    | cons y ys =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      rw [← h.1]
      exact Or.inr (Or.inr List.mem_cons_self)
  | cons d ds ih =>
    cases l1 with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      exact Or.inl ⟨d, List.mem_cons_self, ds ++ x :: b, h⟩
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases ih ys h.2 with ⟨c, hc, r, hr⟩ | ⟨h1, h2⟩ | hx
      · exact Or.inl ⟨c, List.mem_cons_of_mem d hc, r, hr⟩
      · exact Or.inr (Or.inl ⟨by rw [h.1, h1], h2⟩)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem y hx))

private theorem takeUnquotedToken_noSpace (tok rest : List Char)
    (htok : tok.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    takeUnquotedToken (tok ++ rest) = (String.ofList tok, rest) := by
  unfold takeUnquotedToken
  split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest' heq
    by_cases hcond : (isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
        isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
        isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
        isAsciiDigit s1 && isAsciiDigit s2) = true
    · exfalso
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hm1⟩, hm2⟩, hd1⟩, hd2⟩, hh1⟩, _⟩, _⟩, _⟩, _⟩, _⟩
      have hheq' : tok ++ rest =
          [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ++
            ' ' :: [h1, h2, ':', min1, min2, ':', s1, s2] ++ rest' := heq
      rw [List.append_assoc] at hheq'
      have hsp := list_append_split_cases tok rest [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2]
        ([h1, h2, ':', min1, min2, ':', s1, s2] ++ rest') ' ' hheq'
      rcases hsp with ⟨c, hc, r, hr⟩ | ⟨_, hrest_eq⟩ | hmem_sp
      · have hdelim_t : isUnquotedDelim c = true := (hrest c r hr).1
        have hnot_delim : isUnquotedDelim c = false := by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy1
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy2
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy3
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hy4
          rcases List.mem_cons.mp hc with rfl | hc
          · rfl
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hm1
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hm2
          rcases List.mem_cons.mp hc with rfl | hc
          · rfl
          rcases List.mem_cons.mp hc with rfl | hc
          · exact isUnquotedDelim_asciiDigit _ hd1
          rcases List.mem_singleton.mp hc with rfl
          exact isUnquotedDelim_asciiDigit _ hd2
        rw [hdelim_t] at hnot_delim
        contradiction
      · have hnd := (hrest ' ' _ hrest_eq).2 rfl h1 _ rfl
        rw [hh1] at hnd
        contradiction
      · have h1 := List.all_eq_true.mp htok ' ' hmem_sp
        have hsp_delim : isUnquotedDelim ' ' = true := rfl
        simp [hsp_delim] at h1
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      rw [takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)]
      simp
  · rw [takeNonDelim_append [] tok rest htok (fun c r h => (hrest c r h).1)]
    simp

private theorem takeUnquotedToken_spaceDateTime
    (y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 : Char)
    (tail rest : List Char)
    (hy1 : isAsciiDigit y1 = true) (hy2 : isAsciiDigit y2 = true)
    (hy3 : isAsciiDigit y3 = true) (hy4 : isAsciiDigit y4 = true)
    (hm1 : isAsciiDigit m1 = true) (hm2 : isAsciiDigit m2 = true)
    (hd1 : isAsciiDigit d1 = true) (hd2 : isAsciiDigit d2 = true)
    (hh1 : isAsciiDigit h1 = true) (hh2 : isAsciiDigit h2 = true)
    (hmin1 : isAsciiDigit min1 = true) (hmin2 : isAsciiDigit min2 = true)
    (hs1 : isAsciiDigit s1 = true) (hs2 : isAsciiDigit s2 = true)
    (htail : tail.all (fun c => !isUnquotedDelim c) = true)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeUnquotedToken
      (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ tail) ++ rest) =
      (String.ofList ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++ tail),
        rest) := by
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append, takeUnquotedToken,
    hy1, hy2, hy3, hy4, hm1, hm2, hd1, hd2, hh1, hh2, hmin1, hmin2, hs1, hs2,
    Bool.and_self, ↓reduceIte]
  rw [takeNonDelim_append [] tail rest htail hrest]
  simp

private theorem padNatZero_all_digit (w n : Nat) :
    (padNatZero w n).toList.all isAsciiDigit = true := by
  rw [List.all_eq_true]
  intro c hc
  have h := List.all_eq_true.mp (padNatZero_clean w n) c hc
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

private theorem renderDate_head_digit (d : Std.Time.PlainDate) (ds : String) (hr : renderDate d = some ds) :
    ∀ c r, ds.toList = c :: r → isAsciiDigit c = true := by
  simp only [renderDate] at hr
  split at hr
  · injection hr with hds; subst hds
    have h4 : (padNatZero 4 d.year.toNat).toList.all isAsciiDigit = true := padNatZero_all_digit 4 d.year.toNat
    cases hpl : (padNatZero 4 d.year.toNat).toList with
    | nil =>
      have hlen : (padNatZero 4 d.year.toNat).toList.length ≥ 4 := by
        have hlen_eq : (toString (Int.toNat d.year)).toList.length =
            (toString (Int.toNat d.year)).length := by
          change (Nat.repr (Int.toNat d.year)).toList.length =
            (Nat.repr (Int.toNat d.year)).length
          simp [Nat.repr]
        simp only [padNatZero]
        split
        · rename_i hge
          change 4 ≤ (toString (Int.toNat d.year)).toList.length
          rw [hlen_eq]; exact hge
        · simp only [String.toList_append, String.toList_ofList,
            List.length_append, List.length_replicate]
          change 4 ≤ (4 - (toString (Int.toNat d.year)).length) +
            (toString (Int.toNat d.year)).toList.length
          rw [hlen_eq]; omega
      rw [hpl] at hlen; simp at hlen
    | cons y1 ys =>
      simp only [hpl, List.all_cons, Bool.and_eq_true] at h4
      intro c r hcr
      simp only [String.toList_append, hpl, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      exact h4.1
  · simp at hr

private theorem renderTime_head_digit (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (hr : renderTime t fd = some ts) :
    ∀ c r, ts.toList = c :: r → isAsciiDigit c = true := by
  simp only [renderTime] at hr
  split at hr
  · simp at hr
  · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
    | none => simp [hfr] at hr
    | some frac =>
      rw [hfr] at hr
      injection hr with hts; subst hts
      have hh_prop := t.hour.property
      have hh_nat : t.hour.val.toNat < 100 := by omega
      obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
      obtain ⟨ah1, _⟩ := twoDigitsNat?_isAscii h1 h2 t.hour.val.toNat hh_two
      intro c r hcr
      simp only [String.toList_append, hh_list, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      exact ah1

private theorem renderDate_localDate (d : Std.Time.PlainDate) (ds : String)
    (hr : renderDate d = some ds) :
    parseDateTimeToken ds = some (.ok (.localDate d)) ∧
    (ds.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (∀ c r, ds.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨hp, hpref, hcl⟩ := renderDate_parseDatePart d ds [] hr
  simp only [List.append_nil] at hp hpref
  refine ⟨?_, hcl, renderDate_head_digit d ds hr⟩
  simp [parseDateTimeToken, hpref, hp]

private theorem renderTime_localTime (t : Std.Time.PlainTime) (fd : Nat) (ts : String)
    (hr : renderTime t fd = some ts) :
    parseDateTimeToken ts = some (.ok (.localTime t)) ∧
    (ts.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    (∀ c r, ts.toList = c :: r → isAsciiDigit c = true) := by
  obtain ⟨hp, hpref, hcl⟩ := renderTime_parseTimePart t fd ts [] hr (fun _ _ h => by cases h)
  simp only [List.append_nil] at hp hpref
  have hno_date : hasDatePrefix ts.toList = false := by
    simp only [renderTime] at hr
    split at hr
    · simp at hr
    · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
      | none => simp [hfr] at hr
      | some frac =>
        rw [hfr] at hr
        injection hr with hts; subst hts
        have hh_prop := t.hour.property
        have hh_nat : t.hour.val.toNat < 100 := by omega
        obtain ⟨h1, h2, hh_list, _, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat hh_nat
        have hm_prop := t.minute.property
        have hm_nat : t.minute.val.toNat < 100 := by omega
        obtain ⟨m1, m2, hm_list, _, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat hm_nat
        have hs_prop := t.second.property
        have hs_le : t.second.val ≤ 60 := by simpa using hs_prop.2
        have hs_nat : t.second.val.toNat < 100 := by omega
        obtain ⟨s1, s2, hs_list, _, _, _⟩ := twoDigits_padNatZero t.second.val.toNat hs_nat
        have hcol : (":" : String).toList = [':'] := rfl
        simp only [String.toList_append, hh_list, hm_list, hs_list, hcol, List.cons_append, List.nil_append]
        simp only [hasDatePrefix]
        split
        · rename_i heq
          have h3 : ':' = _ := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1
          rw [← h3]
          simp [show isAsciiDigit ':' = false from rfl]
        · rfl
  refine ⟨?_, hcl, renderTime_head_digit t fd ts hr⟩
  simp [parseDateTimeToken, hno_date, hpref, hp]

private theorem renderDateTime_localDateTime_char (dt : Std.Time.PlainDateTime)
    (sepStr : String) (sepChar : Char) (hsep_list : sepStr.toList = [sepChar])
    (hsep_ok : (sepChar == 'T' || sepChar == 't' || sepChar == ' ') = true)
    (fd : Nat) (ds ts : String)
    (hdr : renderDate dt.date = some ds) (htr : renderTime dt.time fd = some ts) :
    parseDateTimeToken (ds ++ sepStr ++ ts) = some (.ok (.localDateTime dt)) := by
  obtain ⟨hdp, hdpref, _⟩ := renderDate_parseDatePart dt.date ds (sepStr ++ ts).toList hdr
  obtain ⟨htp, _, _⟩ := renderTime_parseTimePart dt.time fd ts [] htr (fun _ _ h => by cases h)
  simp only [List.append_nil] at htp
  have hdpref' : hasDatePrefix (ds ++ sepStr ++ ts).toList = true := by
    simpa [String.toList_append, hsep_list] using hdpref
  have hdp' : parseDatePart (ds ++ sepStr ++ ts).toList = .ok (dt.date, sepChar :: ts.toList) := by
    simpa [String.toList_append, hsep_list] using hdp
  have htm_eq : Std.Time.PlainDateTime.mk dt.date dt.time = dt := by
    cases dt; rfl
  simp only [parseDateTimeToken, hdpref', ↓reduceIte, hdp', hsep_ok, htp, htm_eq]

private theorem renderDateTime_localDateTime (dt : Std.Time.PlainDateTime) (sep : DateTimeSep) (fd : Nat)
    (ds ts : String) (hdr : renderDate dt.date = some ds) (htr : renderTime dt.time fd = some ts) :
    parseDateTimeToken (ds ++ renderDateTimeSep sep ++ ts) = some (.ok (.localDateTime dt)) := by
  cases sep
  · exact renderDateTime_localDateTime_char dt "T" 'T' rfl rfl fd ds ts hdr htr
  · exact renderDateTime_localDateTime_char dt "t" 't' rfl rfl fd ds ts hdr htr
  · exact renderDateTime_localDateTime_char dt " " ' ' rfl rfl fd ds ts hdr htr

private theorem renderOffset_head_char (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) (os : String)
    (hr : renderOffset o style = some os) :
    ∀ c r, os.toList = c :: r → isAsciiDigit c = false ∧ c ≠ '.' := by
  simp only [renderOffset] at hr
  split at hr
  · simp at hr
  · by_cases hz : o.second.val = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte] at hr
      cases style with
      | upperZ =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("Z" : String).toList = ['Z'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
      | lowerZ =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("z" : String).toList = ['z'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
      | numeric =>
        injection hr with hos; subst hos
        intro c r hcr
        have h : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
        rw [h] at hcr; injection hcr with hc _; subst hc; exact ⟨rfl, by decide⟩
    · have hne : (o.second.val == 0) = false := beq_false_of_ne hz
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hr
      injection hr with hos; subst hos
      intro c r hcr
      have hsign : (if o.second.val < 0 then "-" else "+").toList =
          [if o.second.val < 0 then '-' else '+'] := by
        split <;> rfl
      simp only [String.toList_append, hsign, List.cons_append] at hcr
      injection hcr with hc _; subst hc
      split <;> exact ⟨rfl, by decide⟩

private theorem renderOffsetDateTime_offsetDateTime_char (odt : TomlOffsetDateTime)
    (sepStr : String) (sepChar : Char) (hsep_list : sepStr.toList = [sepChar])
    (hsep_ok : (sepChar == 'T' || sepChar == 't' || sepChar == ' ') = true)
    (oStyle : OffsetStyle) (fd : Nat) (ds ts os : String)
    (hdr : renderDate odt.dateTime.date = some ds)
    (htr : renderTime odt.dateTime.time fd = some ts)
    (hor : renderOffset odt.offset oStyle = some os) :
    parseDateTimeToken (ds ++ sepStr ++ ts ++ os) = some (.ok (.offsetDateTime odt)) := by
  obtain ⟨hdp, hdpref, _⟩ := renderDate_parseDatePart odt.dateTime.date ds
    ((sepStr ++ ts ++ os).toList) hdr
  obtain ⟨htp, _, _⟩ := renderTime_parseTimePart odt.dateTime.time fd ts os.toList htr
    (fun c r h => let h1 := renderOffset_head_char odt.offset oStyle os hor c r h; ⟨h1.1, fun _ => h1.2⟩)
  obtain ⟨hop, _⟩ := renderOffset_parseOffsetPart odt.offset oStyle os hor
  have hdpref' : hasDatePrefix (ds ++ sepStr ++ ts ++ os).toList = true := by
    simpa [String.toList_append, hsep_list, List.append_assoc] using hdpref
  have hdp' : parseDatePart (ds ++ sepStr ++ ts ++ os).toList =
      .ok (odt.dateTime.date, sepChar :: (ts.toList ++ os.toList)) := by
    simpa [String.toList_append, hsep_list, List.append_assoc] using hdp
  have hodt_eq : TomlOffsetDateTime.mk (Std.Time.PlainDateTime.mk odt.dateTime.date odt.dateTime.time) odt.offset = odt := by
    rcases odt with ⟨⟨dd, tt⟩, oo⟩; rfl
  cases hos : os.toList with
  | nil => rw [hos] at hop; cases hop
  | cons o0 os' =>
    have htp' : parseTimePart (ts.toList ++ o0 :: os') = Except.ok (odt.dateTime.time, o0 :: os') := by
      simpa [hos] using htp
    have hop' : parseOffsetPart (o0 :: os') = Except.ok odt.offset := by
      simpa [hos] using hop
    simp only [parseDateTimeToken, hdpref', ↓reduceIte, hdp', hsep_ok, hos, htp', hop', hodt_eq]

private theorem renderOffsetDateTime_offsetDateTime (odt : TomlOffsetDateTime)
    (sep : DateTimeSep) (oStyle : OffsetStyle) (fd : Nat) (ds ts os : String)
    (hdr : renderDate odt.dateTime.date = some ds)
    (htr : renderTime odt.dateTime.time fd = some ts)
    (hor : renderOffset odt.offset oStyle = some os) :
    parseDateTimeToken (ds ++ renderDateTimeSep sep ++ ts ++ os) = some (.ok (.offsetDateTime odt)) := by
  cases sep
  · exact renderOffsetDateTime_offsetDateTime_char odt "T" 'T' rfl rfl oStyle fd ds ts os hdr htr hor
  · exact renderOffsetDateTime_offsetDateTime_char odt "t" 't' rfl rfl oStyle fd ds ts os hdr htr hor
  · exact renderOffsetDateTime_offsetDateTime_char odt " " ' ' rfl rfl oStyle fd ds ts os hdr htr hor

private theorem clean_all_not_unquotedDelim (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) :
    cs.all (fun c => !isUnquotedDelim c) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1
  exact h1.2

private theorem dateTime_space_takeUnquotedToken
    (d : Std.Time.PlainDate) (t : Std.Time.PlainTime) (fd : Nat)
    (ds ts suffix : String)
    (hdr : renderDate d = some ds)
    (htr : renderTime t fd = some ts)
    (hsuf : suffix.toList.all (fun c => !isUnquotedDelim c) = true)
    (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → isUnquotedDelim c = true) :
    takeUnquotedToken ((ds ++ " " ++ ts ++ suffix).toList ++ rest) =
      (ds ++ " " ++ ts ++ suffix, rest) := by
  have hd_eq : ∃ y1 y2 y3 y4 m1 m2 d1 d2,
      ds.toList = [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] ∧
      isAsciiDigit y1 = true ∧ isAsciiDigit y2 = true ∧ isAsciiDigit y3 = true ∧ isAsciiDigit y4 = true ∧
      isAsciiDigit m1 = true ∧ isAsciiDigit m2 = true ∧ isAsciiDigit d1 = true ∧ isAsciiDigit d2 = true := by
    simp only [renderDate] at hdr
    split at hdr
    · rename_i hvd
      injection hdr with hds; subst hds
      have hv : (0 : Int) ≤ d.year ∧ d.year ≤ 9999 := by simpa [validTomlDate] using hvd
      have h_eq : Int.ofNat (d.year : Int).toNat = (d.year : Int) := Int.toNat_of_nonneg hv.1
      have hy_nat : d.year.toNat < 10000 := by
        have hle : Int.ofNat (d.year : Int).toNat ≤ 9999 := by rw [h_eq]; exact hv.2
        exact Int.ofNat_lt.mp (by omega)
      have hm_prop := d.month.property
      have hd_prop := d.day.property
      obtain ⟨y1, y2, y3, y4, hy_list, hy_four⟩ := padNatZero_4_digits d.year.toNat hy_nat
      obtain ⟨m1, m2, hm_list, hm_two, _, _⟩ := twoDigits_padNatZero d.month.val.toNat (by omega)
      obtain ⟨d1, d2, hd_list, hd_two, _, _⟩ := twoDigits_padNatZero d.day.val.toNat (by omega)
      obtain ⟨ay1, ay2, ay3, ay4⟩ := fourDigitsNat?_isAscii _ _ _ _ _ hy_four
      obtain ⟨am1, am2⟩ := twoDigitsNat?_isAscii _ _ _ hm_two
      obtain ⟨ad1, ad2⟩ := twoDigitsNat?_isAscii _ _ _ hd_two
      have hdash : ("-" : String).toList = ['-'] := rfl
      refine ⟨y1, y2, y3, y4, m1, m2, d1, d2, ?_, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2⟩
      simp only [String.toList_append, hy_list, hdash, hm_list, hd_list]
      rfl
    · simp at hdr
  have ht_eq : ∃ h1 h2 min1 min2 s1 s2 ttail,
      ts.toList = [h1, h2, ':', min1, min2, ':', s1, s2] ++ ttail ∧
      isAsciiDigit h1 = true ∧ isAsciiDigit h2 = true ∧
      isAsciiDigit min1 = true ∧ isAsciiDigit min2 = true ∧
      isAsciiDigit s1 = true ∧ isAsciiDigit s2 = true ∧
      ttail.all (fun c => !isUnquotedDelim c) = true := by
    obtain ⟨_, _, hts_cl⟩ := renderTime_parseTimePart t fd ts [] htr (fun _ _ h => by cases h)
    simp only [renderTime] at htr
    split at htr
    · simp at htr
    · cases hfr : formatNanosExact t.nanosecond.val.toNat fd with
      | none => simp [hfr] at htr
      | some frac =>
        rw [hfr] at htr
        injection htr with hts; subst hts
        have hh_prop := t.hour.property
        have hm_prop := t.minute.property
        have hs_prop := t.second.property
        have hs_le : t.second.val ≤ 60 := by simpa using hs_prop.2
        obtain ⟨h1, h2, hh_list, hh_two, _, _⟩ := twoDigits_padNatZero t.hour.val.toNat (by omega)
        obtain ⟨min1, min2, hmin_list, hmin_two, _, _⟩ := twoDigits_padNatZero t.minute.val.toNat (by omega)
        obtain ⟨s1, s2, hs_list, hs_two, _, _⟩ := twoDigits_padNatZero t.second.val.toNat (by omega)
        obtain ⟨ah1, ah2⟩ := twoDigitsNat?_isAscii _ _ _ hh_two
        obtain ⟨amin1, amin2⟩ := twoDigitsNat?_isAscii _ _ _ hmin_two
        obtain ⟨as1, as2⟩ := twoDigitsNat?_isAscii _ _ _ hs_two
        have hcol : (":" : String).toList = [':'] := rfl
        have hfull : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
            padNatZero 2 t.second.val.toNat ++ frac).toList =
            [h1, h2, ':', min1, min2, ':', s1, s2] ++ frac.toList := by
          simp only [String.toList_append, hh_list, hcol, hmin_list, hs_list]
          rfl
        have hfrac_cl : frac.toList.all (fun c => !isUnquotedDelim c) = true := by
          have h1 := clean_all_not_unquotedDelim _ hts_cl
          rw [hfull, List.all_append, Bool.and_eq_true] at h1
          exact h1.2
        exact ⟨h1, h2, min1, min2, s1, s2, frac.toList, hfull, ah1, ah2, amin1, amin2, as1, as2, hfrac_cl⟩
  rcases hd_eq with ⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hy1, hy2, hy3, hy4, hm1, hm2, hd1, hd2⟩
  rcases ht_eq with ⟨h1, h2, min1, min2, s1, s2, ttail, hts, hh1, hh2, hmin1, hmin2, hs1, hs2, httail⟩
  have hsp : (" " : String).toList = [' '] := rfl
  have hfull : (ds ++ " " ++ ts ++ suffix).toList =
      [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++
        (ttail ++ suffix.toList) := by
    simp only [String.toList_append, hds, hsp, hts, List.cons_append, List.nil_append]
  rw [hfull]
  have htail_all : (ttail ++ suffix.toList).all (fun c => !isUnquotedDelim c) = true := by
    simp [List.all_append, httail, hsuf]
  rw [takeUnquotedToken_spaceDateTime y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2
    (ttail ++ suffix.toList) rest hy1 hy2 hy3 hy4 hm1 hm2 hd1 hd2 hh1 hh2 hmin1 hmin2 hs1 hs2
    htail_all hrest]
  have hstr : String.ofList
      ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++
        (ttail ++ suffix.toList)) = ds ++ " " ++ ts ++ suffix := by
    rw [← hfull, String.ofList_toList]
  rw [hstr]

private theorem consumeIntDigits_props (b : NumBase) (acc : Nat) (cs : List Char) (n : Nat)
    (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) :
    ∀ c ∈ cs, c ≠ ':' ∧ (b ≠ .hex → c ≠ 'e' ∧ c ≠ 'E') := by
  induction hlen : cs.length using Nat.strongRecOn generalizing cs acc with
  | ind len ih =>
    intro c hc
    cases cs with
    | nil => cases hc
    | cons c0 cs0 =>
      by_cases hu : c0 = '_'
      · subst hu
        cases cs0 with
        | nil => simp [NumParse.Model.consumeIntDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeIntDigits] at h
          cases hc with
          | head => exact ⟨by decide, fun _ => ⟨by decide, by decide⟩⟩
          | tail _ hc' =>
            cases hdv : NumParse.Model.digitVal? b c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              have hc1 : c1 ≠ ':' ∧ (b ≠ .hex → c1 ≠ 'e' ∧ c1 ≠ 'E') := by
                constructor
                · intro heq1; subst heq1; cases b <;> simp [NumParse.Model.digitVal?] at hdv
                · intro hb
                  constructor <;> intro heq1 <;> subst heq1 <;> cases b <;>
                    simp [NumParse.Model.digitVal?] at hdv <;> exact absurd rfl hb
              rcases List.mem_cons.mp hc' with rfl | hc''
              · exact hc1
              · exact ih cs1.length (by simp [← hlen]; omega) (acc * b.radix + d) cs1 h rfl c hc''
      · unfold NumParse.Model.consumeIntDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' cs0' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          cases hdv : NumParse.Model.digitVal? b c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            rcases List.mem_cons.mp hc with rfl | hc'
            · constructor
              · intro heq1; subst heq1; cases b <;> simp [NumParse.Model.digitVal?] at hdv
              · intro hb
                constructor <;> intro heq1 <;> subst heq1 <;> cases b <;>
                  simp [NumParse.Model.digitVal?] at hdv <;> exact absurd rfl hb
            · exact ih cs0.length (by simp [← hlen]) (acc * b.radix + d) cs0 h rfl c hc'

private theorem parseDecAfterSign_props (neg : Bool) (cs : List Char) (m : Int)
    (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ isAsciiDigit c0 = true) ∧
    (∀ c ∈ cs, c ≠ ':' ∧ c ≠ 'e' ∧ c ≠ 'E') := by
  cases cs with
  | nil => simp [NumParse.Model.parseDecAfterSign] at h
  | cons c0 rest =>
    cases h0 : c0 == '_' with
    | true =>
      have hc0 : c0 = '_' := beq_iff_eq.mp h0
      subst hc0
      simp [NumParse.Model.parseDecAfterSign] at h
    | false =>
      cases hzero : c0 == '0' with
      | true =>
        have hc0 : c0 = '0' := beq_iff_eq.mp hzero
        subst hc0
        cases rest with
        | nil =>
          refine ⟨⟨'0', [], rfl, rfl⟩, fun c hc => ?_⟩
          rcases List.mem_singleton.mp hc with rfl
          exact ⟨by decide, by decide, by decide⟩
        | cons c1 r1 =>
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [NumParse.Model.parseDecAfterSign, hd1] at h
          · by_cases hu1 : c1 = '_'
            · subst hu1
              cases r1 with
              | nil => simp [NumParse.Model.parseDecAfterSign, hd1] at h
              | cons c2 tail =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;>
                  simp [NumParse.Model.parseDecAfterSign, hd1, hd2] at h
            · simp [NumParse.Model.parseDecAfterSign, hd1, hu1] at h
      | false =>
        have hne0 : c0 ≠ '0' := fun he => by rw [he] at hzero; contradiction
        have hne_u : c0 ≠ '_' := fun he => by rw [he] at h0; contradiction
        unfold NumParse.Model.parseDecAfterSign at h
        split at h
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_u
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · rename_i c0' rest' _ _ _ heq
          injection heq with h1 h2; subst h1; subst h2
          cases hdv : NumParse.Model.digitVal? .dec c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            cases hn : NumParse.Model.consumeIntDigits .dec d rest with
            | error => rw [hn] at h; cases h
            | ok n =>
              have hd_c : isAsciiDigit c0 = true := by
                simp only [NumParse.Model.digitVal?] at hdv
                split at hdv
                · rename_i hc; simpa [isAsciiDigit, Bool.and_eq_true] using hc
                · cases hdv
              refine ⟨⟨c0, rest, rfl, hd_c⟩, fun c hc => ?_⟩
              rcases List.mem_cons.mp hc with rfl | hc'
              · refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hd_c <;> decide
              · have hp := consumeIntDigits_props .dec d rest n hn c hc'
                exact ⟨hp.1, hp.2 (by decide)⟩

private theorem parseIntModelChars_props (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigit c0 = true) ∧
      (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigit c1 = true)) ∧
    (∀ c ∈ cs, c ≠ ':') := by
  unfold NumParse.Model.parseIntModelChars at h
  split at h
  · cases h
  · rename_i _ b rest
    split at h
    · cases h
    · rcases parseDecAfterSign_props false ('0' :: b :: rest) m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
      injection hdr with hc1 _; subst hc1
      refine ⟨⟨'+', '0' :: b :: rest, rfl, Or.inl rfl, fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
      · injection h1 with hc1 _; subst hc1; exact hd_dig
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hchars c hc').1
  · rename_i _ b rest
    split at h
    · cases h
    · rcases parseDecAfterSign_props true ('0' :: b :: rest) m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
      injection hdr with hc1 _; subst hc1
      refine ⟨⟨'-', '0' :: b :: rest, rfl, Or.inr (Or.inl rfl), fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
      · injection h1 with hc1 _; subst hc1; exact hd_dig
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hchars c hc').1
  · rename_i _ rest _
    rcases parseDecAfterSign_props false rest m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    refine ⟨⟨'+', rest, rfl, Or.inl rfl, fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
    · rw [h1] at hdr; injection hdr with hc1 _; subst hc1; exact hd_dig
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hchars c hc').1
  · rename_i _ rest _
    rcases parseDecAfterSign_props true rest m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    refine ⟨⟨'-', rest, rfl, Or.inr (Or.inl rfl), fun c1 r1 _ h1 => ?_⟩, fun c hc => ?_⟩
    · rw [h1] at hdr; injection hdr with hc1 _; subst hc1; exact hd_dig
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hchars c hc').1
  · rename_i _ b rest
    cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h
      dsimp only at h
      have hd := parseDecAfterSign_props false ('0' :: b :: rest) m h
      refine ⟨⟨'0', b :: rest, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
        fun c hc => (hd.2 c hc).1⟩
    | some base =>
      rw [hbp] at h
      dsimp only at h
      cases rest with
      | nil => cases h
      | cons c1 cs1 =>
        by_cases hu : c1 = '_'
        · subst hu; cases h
        · split at h
          · cases h
          · cases h
          · rename_i c1' cs1' _ _ heq
            injection heq with h1 h2; subst h1; subst h2
            cases hdv : NumParse.Model.digitVal? base c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              cases hn : NumParse.Model.consumeIntDigits base d cs1 with
              | error => rw [hn] at h; cases h
              | ok n =>
                refine ⟨⟨'0', b :: c1 :: cs1, rfl, Or.inr (Or.inr rfl),
                  fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩, fun c hc => ?_⟩
                rcases List.mem_cons.mp hc with rfl | hc
                · decide
                rcases List.mem_cons.mp hc with rfl | hc
                · intro heq; subst heq; cases hbp
                rcases List.mem_cons.mp hc with rfl | hc
                · cases base <;> simp [NumParse.Model.digitVal?] at hdv <;>
                    intro heq <;> subst heq <;> simp at hdv
                · exact (consumeIntDigits_props base d cs1 n hn c hc).1
  · rcases parseDecAfterSign_props false cs m h with ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩
    have hne_sign : d0 ≠ '+' ∧ d0 ≠ '-' := ⟨fun he => by subst he; revert hd_dig; decide, fun he => by subst he; revert hd_dig; decide⟩
    refine ⟨⟨d0, dr, hdr, Or.inr (Or.inr hd_dig), fun _ _ hs _ => by rcases hs with h1 | h1; exact absurd h1 hne_sign.1; exact absurd h1 hne_sign.2⟩,
      fun c hc => (hchars c hc).1⟩

private theorem toString_nat_head_nonzero (n : Nat) (hn : 0 < n) :
    ∃ d0 ds, (toString n).toList = d0 :: ds ∧ isAsciiDigit d0 = true ∧ d0 ≠ '0' ∧
      (d0 :: ds).all isAsciiDigit = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h10 : n < 10
    · obtain ⟨hch, had, _, _⟩ := toString_lt10_char n h10
      have hne0 : (n : Nat).digitChar ≠ '0' := by
        intro heq
        have hdv : digitVal n.digitChar = digitVal '0' := congrArg digitVal heq
        obtain ⟨_, _, hdv', _⟩ := toString_lt10_char n h10
        have hd0 : digitVal '0' = 0 := rfl
        omega
      refine ⟨n.digitChar, [], hch, had, hne0, ?_⟩
      simp [had]
    · have hdiv_pos : 0 < n / 10 := by omega
      have hdiv_lt : n / 10 < n := by omega
      obtain ⟨d0, ds, hd_list, hd_dig, hd_ne0, hd_all⟩ := ih (n / 10) hdiv_lt hdiv_pos
      have hsplit := toString_two_digits_split (n / 10) (n % 10) (by omega) (Nat.mod_lt n (by decide))
      have heq : n / 10 * 10 + n % 10 = n := by omega
      rw [heq] at hsplit
      obtain ⟨_, had_m, _, _⟩ := toString_lt10_char (n % 10) (Nat.mod_lt n (by decide))
      refine ⟨d0, ds ++ [(n % 10).digitChar], ?_, hd_dig, hd_ne0, ?_⟩
      · rw [hsplit, hd_list]; rfl
      · simp only [List.all_cons, Bool.and_eq_true] at hd_all
        simp [List.all_append, hd_all.1, hd_all.2, had_m]

private theorem consumeIntDigits_dec_foldl (acc : Nat) (ds : List Char)
    (hds : ds.all isAsciiDigit = true) :
    NumParse.Model.consumeIntDigits .dec acc ds =
      .ok (ds.foldl (fun a c => a * 10 + digitVal c) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    have hnot_u : c ≠ '_' := by intro heq; subst heq; exact absurd hds.1 (by decide)
    have hdig_val : NumParse.Model.digitVal? .dec c = some (digitVal c) := by
      have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hds.1
      simp [NumParse.Model.digitVal?, h1.1, h1.2, digitVal]
    unfold NumParse.Model.consumeIntDigits
    split
    · rename_i heq; cases heq
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i c1 cs1 _ _ heq
      injection heq with h1 h2
      rw [← h1, ← h2]
      simp only [hdig_val, NumParse.Model.NumBase.radix, List.foldl_cons]
      exact ih (acc * 10 + digitVal c) hds.2

private theorem parseDecAfterSign_toString_nat (neg : Bool) (n : Nat) :
    NumParse.Model.parseDecAfterSign neg (toString n).toList =
      .ok (if neg then -Int.ofNat n else Int.ofNat n) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : (toString (0 : Nat)).toList = ['0'] := rfl
    rw [h0]
    simp [NumParse.Model.parseDecAfterSign]
  · obtain ⟨d0, ds, hlist, hd0, hne0, hall⟩ := toString_nat_head_nonzero n (by omega)
    rw [hlist]
    have hnot_u : d0 ≠ '_' := by intro heq; subst heq; revert hd0; decide
    have hdig_val : NumParse.Model.digitVal? .dec d0 = some (digitVal d0) := by
      have h1 : '0' ≤ d0 ∧ d0 ≤ '9' := by simpa [isAsciiDigit] using hd0
      simp [NumParse.Model.digitVal?, h1.1, h1.2, digitVal]
    have hall_ds : ds.all isAsciiDigit = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
    have hfold : (d0 :: ds).foldl (fun a c => a * 10 + digitVal c) 0 = n := by
      rw [← hlist]; exact toString_foldl_digits n
    unfold NumParse.Model.parseDecAfterSign
    split
    · contradiction
    · rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u
    · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
    · rename_i c1 rest1 _ _ heq
      injection heq with h1 h2; subst h1; subst h2
      simp only [hdig_val, consumeIntDigits_dec_foldl (digitVal d0) ds hall_ds]
      have hfold' : List.foldl (fun a c => a * 10 + digitVal c) (digitVal d0) ds = n := by
        simpa [List.foldl_cons, Nat.zero_mul, Nat.zero_add] using hfold
      rw [hfold']

private theorem formatInt64Canonical_isValidIntLex (n : Int64) :
    isValidIntLex (formatInt64Canonical n) n = true := by
  have hparse_int : NumParse.Model.parseIntModel (formatInt64Canonical n) = .ok n.toInt := by
    simp only [formatInt64Canonical, NumParse.Model.parseIntModel]
    cases hni : n.toInt with
    | ofNat m =>
      have hstr : toString (Int.ofNat m) = toString m := rfl
      rw [hstr]
      cases hm : m with
      | zero =>
        have h0 : (toString (0 : Nat)).toList = ['0'] := rfl
        rw [h0]; rfl
      | succ k =>
        obtain ⟨d0, ds, hlist, hd0, hne0, hall⟩ := toString_nat_head_nonzero (k + 1) (by omega)
        have hd := parseDecAfterSign_toString_nat false (k + 1)
        rw [hlist] at hd ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at hd
        have hne_plus : d0 ≠ '+' := fun he => by subst he; revert hd0; decide
        have hne_minus : d0 ≠ '-' := fun he => by subst he; revert hd0; decide
        unfold NumParse.Model.parseIntModelChars
        split
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_plus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_minus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_plus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_minus
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · exact hd
    | negSucc k =>
      have hstr : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
        change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList
        simp [String.toList_append, toString]
      rw [hstr]
      obtain ⟨d0, ds, hlist, hd0, hne0, _⟩ := toString_nat_head_nonzero (k + 1) (by omega)
      have hd := parseDecAfterSign_toString_nat true (k + 1)
      rw [hlist] at hd ⊢
      simp only [↓reduceIte] at hd
      have hres : NumParse.Model.parseIntModelChars ('-' :: d0 :: ds) =
          .ok (-Int.ofNat (k + 1)) := by
        unfold NumParse.Model.parseIntModelChars
        split
        · contradiction
        · rename_i heq; cases heq
        · rename_i heq; injection heq with _ h2; injection h2 with h3 _; exact absurd h3 hne0
        · rename_i heq; cases heq
        · rename_i rest _ _ heq; injection heq with _ h2; subst h2; exact hd
        · rename_i heq; cases heq
        · rename_i _ _ _ _ hne _; exact False.elim (hne (d0 :: ds) rfl)
      rw [hres]
      rfl
  have hbounds : NumParse.Model.inInt64Range n.toInt = true := by
    have h1 : (-2 ^ 63 : Int) ≤ n.toInt := Int64.le_toInt n
    have h2 : n.toInt ≤ Int64.maxValue.toInt := Int64.toInt_le n
    have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
    rw [NumParse.Model.inInt64Range, decide_eq_true_eq]
    simp only [NumParse.Model.int64MinInt, NumParse.Model.int64MaxInt]
    omega
  have hof : Int64.ofInt n.toInt = n := Int64.ofInt_toInt n
  have hp64 : NumParse.Model.parseInt64Model (formatInt64Canonical n) = .ok n := by
    simp [NumParse.Model.parseInt64Model, hparse_int, hbounds, hof]
  have honly_dec_or_minus : ∀ c ∈ (formatInt64Canonical n).toList, c = '-' ∨ isAsciiDigit c = true := by
    intro c hc
    simp only [formatInt64Canonical] at hc
    cases hni : n.toInt with
    | ofNat m =>
      rw [hni] at hc
      have hstr : toString (Int.ofNat m) = toString m := rfl
      rw [hstr] at hc
      have hd := List.all_eq_true.mp (toString_digits_all_clean m).1 c hc
      simp only [Bool.and_eq_true] at hd
      exact Or.inr hd.1.1.1.1
    | negSucc k =>
      rw [hni] at hc
      have hstr : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
        change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList
        simp [String.toList_append, toString]
      rw [hstr] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inl rfl
      · have hd := List.all_eq_true.mp (toString_digits_all_clean (k + 1)).1 c hc'
        simp only [Bool.and_eq_true] at hd
        exact Or.inr hd.1.1.1.1
  have hclean_all : (formatInt64Canonical n).toList.all (fun c =>
      !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && !isDisallowedControl c) = true := by
    rw [List.all_eq_true]
    intro c hc
    rcases honly_dec_or_minus c hc with rfl | hcd
    · decide
    · have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hcd
      have hws : c.isWhitespace = false := by
        simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
      have hneq : c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '.' := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
      have hctrl : isDisallowedControl c = false := by
        have h1' : (48 : Nat) ≤ c.toNat ∧ c.toNat ≤ 57 :=
          ⟨UInt32.le_iff_toNat_le.mp h1.1, UInt32.le_iff_toNat_le.mp h1.2⟩
        simp [isDisallowedControl]
        omega
      simp [hws, hneq.1, hneq.2.1, hneq.2.2.1, hneq.2.2.2.1, hneq.2.2.2.2, hctrl]
  have hno_upper : hasUppercaseBasePrefix (formatInt64Canonical n) = false := by
    have hnot_sw : ∀ p : String, ∀ c : Char, c ∈ p.toList → (c = 'X' ∨ c = 'O' ∨ c = 'B') →
        (formatInt64Canonical n).startsWith p = false := by
      intro p c hc_mem hc_up
      rw [Bool.eq_false_iff]
      intro hsw
      rw [String.startsWith_string_iff] at hsw
      rcases hsw with ⟨t, ht⟩
      have hmem : c ∈ (formatInt64Canonical n).toList := by
        rw [← ht]
        exact List.mem_append_left t hc_mem
      rcases honly_dec_or_minus c hmem with rfl | hdig
      · rcases hc_up with h | h | h <;> contradiction
      · rcases hc_up with rfl | rfl | rfl <;> revert hdig <;> decide
    simp only [hasUppercaseBasePrefix, Bool.or_eq_false_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hnot_sw "0X" 'X' (by decide) (by decide),
      hnot_sw "0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "+0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "+0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "+0B" 'B' (by decide) (by decide)⟩,
      hnot_sw "-0X" 'X' (by decide) (by decide)⟩,
      hnot_sw "-0O" 'O' (by decide) (by decide)⟩,
      hnot_sw "-0B" 'B' (by decide) (by decide)⟩
  have hno_exp : (!(formatInt64Canonical n).contains 'e' && !(formatInt64Canonical n).contains 'E') = true := by
    have hnot_e : 'e' ∉ (formatInt64Canonical n).toList := by
      intro hmem
      rcases honly_dec_or_minus 'e' hmem with h1 | h2
      · cases h1
      · revert h2; decide
    have hnot_E : 'E' ∉ (formatInt64Canonical n).toList := by
      intro hmem
      rcases honly_dec_or_minus 'E' hmem with h1 | h2
      · cases h1
      · revert h2; decide
    have he1 : (formatInt64Canonical n).contains 'e' = false := by simp [String.contains, hnot_e]
    have he2 : (formatInt64Canonical n).contains 'E' = false := by simp [String.contains, hnot_E]
    simp [he1, he2]
  simp only [isValidIntLex, hp64, hclean_all, beq_self_eq_true, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simpa [hasUppercaseBasePrefix] using hno_upper
  · split
    · trivial
    · simpa [Bool.not_or] using hno_exp

private theorem asciiDigit_clean (c : Char) (hc : isAsciiDigit c = true) :
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && c != '\r' && c != '\n' && !isDisallowedControl c && !isUnquotedDelim c = true := by
  have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigit] using hc
  have h1' : (48 : Nat) ≤ c.toNat ∧ c.toNat ≤ 57 :=
    ⟨UInt32.le_iff_toNat_le.mp h1.1, UInt32.le_iff_toNat_le.mp h1.2⟩
  have hws : c.isWhitespace = false := by
    simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
  have hneq : c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '.' ∧ c ≠ '\r' ∧ c ≠ '\n' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> exact absurd h1 (by decide)
  have hctrl : isDisallowedControl c = false := by
    simp [isDisallowedControl]
    omega
  have hud : isUnquotedDelim c = false := isUnquotedDelim_asciiDigit c hc
  simp [hws, hneq.1, hneq.2.1, hneq.2.2.1, hneq.2.2.2.1, hneq.2.2.2.2.1,
    hneq.2.2.2.2.2.1, hneq.2.2.2.2.2.2, hctrl, hud]

private def isFloatModelChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '.' || c == 'e' || c == 'E' || c == '_' ||
    c == 'i' || c == 'n' || c == 'f' || c == 'a' || isAsciiDigit c

private theorem isFloatModelChar_props (c : Char) (h : isFloatModelChar c = true) :
    c ≠ ':' ∧ c ≠ 'x' ∧ c ≠ 'X' ∧
      (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true ∧
      (!isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true := by
  simp only [isFloatModelChar, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hc)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hcl := asciiDigit_clean c hc
    simp only [Bool.and_eq_true] at hcl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro heq; subst heq; revert hc; decide
    · intro heq; subst heq; revert hc; decide
    · intro heq; subst heq; revert hc; decide
    · simp [hcl.1.1.1.1.1.1.1.1.1, hcl.1.1.1.1.1.1.1.1.2, hcl.1.1.1.1.1.1.1.2,
        hcl.1.1.1.1.1.1.2, hcl.1.1.1.1.1.2, hcl.1.2]
    · have hud : isUnquotedDelim c = false := by simpa using hcl.2
      simp [hcl.1.2, hcl.1.1.1.2, hcl.1.1.2, hud]

private theorem consumeDecFloatDigits_props (acc cnt : Nat) (cs : List Char)
    (m c : Nat) (rest : List Char)
    (h : NumParse.Model.consumeDecFloatDigits acc cnt cs = .ok (m, c, rest)) :
    ∃ pfx, cs = pfx ++ rest ∧
      (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) ∧
      (∀ c0 r0, rest = c0 :: r0 → c0 ≠ '_' ∧ isAsciiDigit c0 = false) := by
  induction hlen : cs.length using Nat.strongRecOn generalizing cs acc cnt with
  | ind len ih =>
    cases cs with
    | nil =>
      simp only [NumParse.Model.consumeDecFloatDigits] at h
      injection h with h1
      have hrest : rest = [] := (Prod.mk.inj (Prod.mk.inj h1).2).2.symm
      exact ⟨[], by simp [hrest], by simp, fun _ _ hr => by rw [hrest] at hr; cases hr⟩
    | cons c0 cs0 =>
      by_cases hu : c0 = '_'
      · subst hu
        cases cs0 with
        | nil => simp [NumParse.Model.consumeDecFloatDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeDecFloatDigits] at h
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp only [hd1, ↓reduceIte] at h
            obtain ⟨pfx, hcs, hpfx, hrest⟩ :=
              ih cs1.length (by simp [← hlen]; omega) _ _ cs1 h rfl
            have had1 : isAsciiDigit c1 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
            refine ⟨'_' :: c1 :: pfx, by simp [hcs], fun ch hc => ?_, hrest⟩
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inl rfl
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr had1
            · exact hpfx ch hc
          · simp [hd1] at h
      · unfold NumParse.Model.consumeDecFloatDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' cs0' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0] at h
            obtain ⟨pfx, hcs, hpfx, hrest⟩ :=
              ih cs0.length (by simp [← hlen]) _ _ cs0 h rfl
            have had0 : isAsciiDigit c0 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
            refine ⟨c0 :: pfx, by simp [hcs], fun ch hc => ?_, hrest⟩
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr had0
            · exact hpfx ch hc
          · simp only [hd0] at h
            injection h with h1
            have hrest : rest = c0 :: cs0 := (Prod.mk.inj (Prod.mk.inj h1).2).2.symm
            have had0 : isAsciiDigit c0 = false := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
            refine ⟨[], by simp [hrest], by simp, fun x r hxr => ?_⟩
            rw [hrest] at hxr
            injection hxr with hx _
            subst hx
            exact ⟨hu, had0⟩

private theorem parseFloatIntPart_props (cs : List Char) (m : Nat) (rest : List Char)
    (h : NumParse.Model.parseFloatIntPart cs = .ok (m, rest)) :
    ∃ pfx d0 ptail, cs = pfx ++ rest ∧ pfx = d0 :: ptail ∧ isAsciiDigit d0 = true ∧
      (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigit ch = true) ∧
      (∀ c0 r0, rest = c0 :: r0 → c0 ≠ '_' ∧ isAsciiDigit c0 = false) := by
  cases cs with
  | nil => simp [NumParse.Model.parseFloatIntPart] at h
  | cons c0 cs0 =>
    by_cases hu : c0 = '_'
    · subst hu; simp [NumParse.Model.parseFloatIntPart] at h
    · by_cases hz : c0 = '0'
      · subst hz
        cases cs0 with
        | nil =>
          simp only [NumParse.Model.parseFloatIntPart] at h
          injection h with h1
          have hrest : rest = [] := (Prod.mk.inj h1).2.symm
          refine ⟨['0'], '0', [], by simp [hrest], rfl, rfl, fun ch hc => ?_, fun _ _ hr => by rw [hrest] at hr; cases hr⟩
          rcases List.mem_singleton.mp hc with rfl; exact Or.inr rfl
        | cons c1 r1 =>
          simp only [NumParse.Model.parseFloatIntPart] at h
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [hd1] at h
          · by_cases hc1u : c1 = '_'
            · subst hc1u
              cases r1 with
              | nil => simp [hd1] at h
              | cons c2 t2 =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;> simp [hd1, hd2] at h
            · have hbeq : (c1 == '_') = false := beq_false_of_ne hc1u
              simp only [hd1, Bool.false_eq_true, ↓reduceIte, hbeq] at h
              injection h with h1
              have hrest : rest = c1 :: r1 := (Prod.mk.inj h1).2.symm
              have had1 : isAsciiDigit c1 = false := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
              refine ⟨['0'], '0', [], by simp [hrest], rfl, rfl, fun ch hc => ?_, fun x r hxr => ?_⟩
              · rcases List.mem_singleton.mp hc with rfl; exact Or.inr rfl
              · rw [hrest] at hxr; injection hxr with hx _; subst hx; exact ⟨hc1u, had1⟩
      · unfold NumParse.Model.parseFloatIntPart at h
        split at h
        · rename_i heq; cases heq
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hz
        · rename_i c0' cs0' _ _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0] at h
            cases hc : NumParse.Model.consumeDecFloatDigits (c0.toNat - '0'.toNat) 1 cs0 with
            | error => rw [hc] at h; cases h
            | ok res =>
              rcases res with ⟨mv, fst, rem⟩
              rw [hc] at h
              injection h with h1
              have hrem : rem = rest := (Prod.mk.inj h1).2
              subst hrem
              obtain ⟨pfx, hcs0, hpfx, hrest⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc
              have had0 : isAsciiDigit c0 = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0
              refine ⟨c0 :: pfx, c0, pfx, by simp [hcs0], rfl, had0, fun ch hm => ?_, hrest⟩
              rcases List.mem_cons.mp hm with rfl | hm'
              · exact Or.inr had0
              · exact hpfx ch hm'
          · simp [hd0] at h

private theorem parseFloatExpPart_props (cs : List Char) (e : Int)
    (h : NumParse.Model.parseFloatExpPart cs = .ok (e, [])) :
    ∀ c ∈ cs, c = '+' ∨ c = '-' ∨ c = '_' ∨ isAsciiDigit c = true := by
  unfold NumParse.Model.parseFloatExpPart at h
  have hbody : ∀ (expNeg : Bool) (body : List Char),
      (match body with
        | [] => Except.error NumParseErrorKind.invalidSyntax
        | '_' :: tail => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest =>
          if NumParse.Model.isDecDigit c = true then
            match NumParse.Model.consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) =>
              .ok (if expNeg = true then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error k => .error k
          else .error .invalidSyntax) = .ok (e, []) →
      ∀ c ∈ body, c = '_' ∨ isAsciiDigit c = true := by
    intro expNeg body hb c hc
    cases body with
    | nil => cases hb
    | cons c0 r0 =>
      by_cases hu : c0 = '_'
      · subst hu; cases hb
      · split at hb
        · rename_i heq; cases heq
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' r0' _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at hb
          by_cases hd0 : NumParse.Model.isDecDigit c0 = true
          · simp only [hd0, ↓reduceIte] at hb
            cases hc2 : NumParse.Model.consumeDecFloatDigits (c0.toNat - '0'.toNat) 1 r0 with
            | error => rw [hc2] at hb; cases hb
            | ok res =>
              rcases res with ⟨em, fst, rem⟩
              rw [hc2] at hb
              injection hb with h1
              have hrem : rem = [] := (Prod.mk.inj h1).2
              subst hrem
              obtain ⟨pfx, hr0, hpfx, _⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hc2
              simp only [List.append_nil] at hr0
              subst hr0
              rcases List.mem_cons.mp hc with rfl | hc'
              · exact Or.inr (by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd0)
              · exact hpfx c hc'
          · simp [hd0] at hb
  cases cs with
  | nil => simp at h
  | cons c0 r0 =>
    by_cases hp : c0 = '+'
    · subst hp
      dsimp only at h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inl rfl
      · rcases hbody false r0 h c hc' with h1 | h2
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr h2))
    · by_cases hm : c0 = '-'
      · subst hm
        dsimp only at h
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr (Or.inl rfl)
        · rcases hbody true r0 h c hc' with h1 | h2
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr (Or.inr h2))
      · dsimp only at h
        split at h
        · cases h
        · cases h
        · rename_i c0' r0' _ heq
          split at heq
          · rename_i _ heq_c0
            injection heq_c0 with h1 _
            exact absurd h1 hp
          · rename_i _ heq_c0
            injection heq_c0 with h1 _
            exact absurd h1 hm
          · dsimp only at heq
            have hfst : (match c0 :: r0 with
                | '+' :: rest => (false, rest)
                | '-' :: rest => (true, rest)
                | _ => (false, c0 :: r0)).fst = false := by
              split
              · rename_i _ heq_c0
                injection heq_c0 with h1 _
                exact absurd h1 hp
              · rename_i _ heq_c0
                injection heq_c0 with h1 _
                exact absurd h1 hm
              · rfl
            erw [hfst] at h
            intro c hc
            have hc' : c ∈ c0' :: r0' := by rw [← heq]; exact hc
            have hcall := hbody false (c0' :: r0') (by
              split
              · rename_i h_nil
                cases h_nil
              · rename_i _ h_us
                injection h_us with h_us' _
                exact absurd h_us' ‹c0' = '_' → False›
              · rename_i heq_cr
                injection heq_cr with hc1 hr1
                rw [← hc1, ← hr1]
                exact h) c hc'
            rcases hcall with h1 | h2
            · exact Or.inr (Or.inr (Or.inl h1))
            · exact Or.inr (Or.inr (Or.inr h2))

private theorem hasDatePrefix_false_of_digit_or_us_before_sep
    (pfx : List Char) (sep : Char) (tail : List Char)
    (hpfx : ∀ c ∈ pfx, c = '_' ∨ isAsciiDigit c = true)
    (hsep : sep = '.' ∨ sep = 'e' ∨ sep = 'E') :
    hasDatePrefix (pfx ++ sep :: tail) = false := by
  have hsep_not_dig : isAsciiDigit sep = false := by
    rcases hsep with rfl | rfl | rfl <;> rfl
  have hsep_not_dash : sep ≠ '-' := by
    rcases hsep with rfl | rfl | rfl <;> decide
  rcases pfx with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · simp only [List.nil_append, hasDatePrefix]
    split
    · rename_i heq; injection heq with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj heq).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj (List.cons.inj heq).2).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq; have h2 := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2; injection h2 with h1 _; subst h1; simp [hsep_not_dig]
    · rfl
  · simp only [List.cons_append, List.nil_append, hasDatePrefix]
    split
    · rename_i heq
      have hdash : sep = '-' := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).1
      exact absurd hdash hsep_not_dash
    · rfl
  · have he := hpfx e (by simp)
    have hne : e ≠ '-' := by
      rcases he with rfl | hd
      · decide
      · intro h1; subst h1; revert hd; decide
    simp only [List.cons_append, hasDatePrefix]
    split
    · rename_i heq
      have hdash : e = '-' := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).1
      exact absurd hdash hne
    · rfl

private theorem parseFloatExpSuffix_props (afterE : List Char) (g : Int → Float) (f : Float)
    (h : (match NumParse.Model.parseFloatExpPart afterE with
      | Except.error k => Except.error k
      | Except.ok (expVal, afterExp) =>
        if afterExp.isEmpty = true then Except.ok (g expVal) else Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterE, isFloatModelChar c = true := by
  cases hexp : NumParse.Model.parseFloatExpPart afterE with
  | error => rw [hexp] at h; cases h
  | ok res =>
    rcases res with ⟨expVal, afterExp⟩
    rw [hexp] at h
    dsimp only at h
    cases hrem : afterExp.isEmpty with
    | false => simp [hrem] at h
    | true =>
      have hae : afterExp = [] := by cases afterExp <;> simp_all
      subst hae
      intro c hc
      rcases parseFloatExpPart_props afterE expVal hexp c hc with rfl | rfl | rfl | hd
      · rfl
      · rfl
      · rfl
      · simp [isFloatModelChar, hd]

private theorem parseFloatAfterFrac_props (afterFrac : List Char) (neg : Bool) (mant fracCount : Nat) (f : Float)
    (h : (match afterFrac with
      | 'e' :: afterE =>
        match NumParse.Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mant (expVal - Int.ofNat fracCount))
          else Except.error NumParseErrorKind.trailingChars
      | 'E' :: afterE =>
        match NumParse.Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mant (expVal - Int.ofNat fracCount))
          else Except.error NumParseErrorKind.trailingChars
      | [] => Except.ok (NumParse.Model.evalFloat neg mant (-Int.ofNat fracCount))
      | _ :: _ => Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterFrac, isFloatModelChar c = true := by
  split at h
  · rename_i afterE
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rfl
    · exact parseFloatExpSuffix_props afterE _ f h c hc'
  · rename_i afterE
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rfl
    · exact parseFloatExpSuffix_props afterE _ f h c hc'
  · simp
  · simp at h

private theorem parseFloatModelChars_props (cs : List Char) (f : Float)
    (h : NumParse.Model.parseFloatModelChars cs = .ok f) :
    (∃ c0 rest, cs = c0 :: rest ∧
      (c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true)) ∧
    (∀ c ∈ cs, isFloatModelChar c = true) ∧
    hasDatePrefix cs = false ∧
    hasTimePrefix cs = false ∧
    isFloatTokenCandidate (String.ofList cs) = true := by
  have hnot_time : ∀ l : List Char, (∀ c ∈ l, isFloatModelChar c = true) → hasTimePrefix l = false := by
    intro l hl
    unfold hasTimePrefix
    split
    · exact absurd rfl (isFloatModelChar_props ':' (hl ':' (by simp))).1
    · rfl
  have hcand_of_sep : ∀ l : List Char, (∀ c ∈ l, isFloatModelChar c = true) →
      (l.contains '.' || l.contains 'e' || l.contains 'E') = true →
      isFloatTokenCandidate (String.ofList l) = true := by
    intro l hl hsep
    have hno_x : ∀ p : String, ∀ c ∈ p.toList, c = 'x' ∨ c = 'X' →
        (String.ofList l).startsWith p = false := by
      intro p c hcm hcx
      rw [Bool.eq_false_iff]
      intro hsw
      rw [String.startsWith_string_iff] at hsw
      rcases hsw with ⟨t, ht⟩
      have hmem : c ∈ l := by
        have h1 : c ∈ (String.ofList l).toList := by rw [← ht]; exact List.mem_append_left t hcm
        simpa [String.toList_ofList] using h1
      have hnx := (isFloatModelChar_props c (hl c hmem)).2
      rcases hcx with rfl | rfl
      · exact absurd rfl hnx.1
      · exact absurd rfl hnx.2.1
    simp only [isFloatTokenCandidate, String.toList_ofList, hsep, Bool.and_true]
    rw [hno_x "0x" 'x' (by decide) (Or.inl rfl),
      hno_x "0X" 'X' (by decide) (Or.inr rfl),
      hno_x "+0x" 'x' (by decide) (Or.inl rfl),
      hno_x "-0x" 'x' (by decide) (Or.inl rfl),
      hno_x "+0X" 'X' (by decide) (Or.inr rfl),
      hno_x "-0X" 'X' (by decide) (Or.inr rfl)]
    simp
  have hbody : ∀ body : List Char, ∀ neg : Bool,
      (match body with
        | 'i' :: 'n' :: 'f' :: rest =>
          match rest with | [] => Except.ok (if neg = true then -Float.inf else Float.inf) | _ :: _ => Except.error NumParseErrorKind.trailingChars
        | 'n' :: 'a' :: 'n' :: rest =>
          match rest with | [] => Except.ok Float.nan | _ :: _ => Except.error NumParseErrorKind.trailingChars
        | _ =>
          match NumParse.Model.parseFloatIntPart body with
          | Except.error k => Except.error k
          | Except.ok (intVal, afterInt) =>
            match afterInt with
            | '.' :: afterDot =>
              match afterDot with
              | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
              | c :: rest =>
                if NumParse.Model.isDecDigit c = true then
                  match NumParse.Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
                  | Except.error k => Except.error k
                  | Except.ok (mantissa, fracCount, afterFrac) =>
                    match afterFrac with
                    | 'e' :: afterE =>
                      match NumParse.Model.parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | 'E' :: afterE =>
                      match NumParse.Model.parseFloatExpPart afterE with
                      | Except.error k => Except.error k
                      | Except.ok (expVal, afterExp) =>
                        if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                        else Except.error NumParseErrorKind.trailingChars
                    | [] => Except.ok (NumParse.Model.evalFloat neg mantissa (-Int.ofNat fracCount))
                    | _ :: _ => Except.error NumParseErrorKind.trailingChars
                else Except.error NumParseErrorKind.invalidSyntax
              | [] => Except.error NumParseErrorKind.invalidSyntax
            | 'e' :: afterE =>
              match NumParse.Model.parseFloatExpPart afterE with
              | Except.error k => Except.error k
              | Except.ok (expVal, afterExp) =>
                if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg intVal expVal)
                else Except.error NumParseErrorKind.trailingChars
            | 'E' :: afterE =>
              match NumParse.Model.parseFloatExpPart afterE with
              | Except.error k => Except.error k
              | Except.ok (expVal, afterExp) =>
                if afterExp.isEmpty = true then Except.ok (NumParse.Model.evalFloat neg intVal expVal)
                else Except.error NumParseErrorKind.trailingChars
            | _ => Except.error NumParseErrorKind.invalidSyntax) = Except.ok f →
      (∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true)) ∧
      (∀ c ∈ body, isFloatModelChar c = true) ∧
      hasDatePrefix body = false ∧
      (body = ['i', 'n', 'f'] ∨ body = ['n', 'a', 'n'] ∨
        (body.contains '.' || body.contains 'e' || body.contains 'E') = true) := by
    intro body neg hb
    split at hb
    · rename_i rest
      cases rest with
      | nil =>
        refine ⟨⟨'i', ['n', 'f'], rfl, Or.inl rfl⟩, fun c hc => ?_, ?_, Or.inl rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> rfl
        · decide
      | cons _ _ => simp at hb
    · rename_i rest
      cases rest with
      | nil =>
        refine ⟨⟨'n', ['a', 'n'], rfl, Or.inr (Or.inl rfl)⟩, fun c hc => ?_, ?_, Or.inr (Or.inl rfl)⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> rfl
        · decide
      | cons _ _ => simp at hb
    · cases hip : NumParse.Model.parseFloatIntPart body with
      | error => rw [hip] at hb; cases hb
      | ok res =>
        rcases res with ⟨intVal, afterInt⟩
        rw [hip] at hb
        dsimp only at hb
        obtain ⟨pfx, d0, ptail, hbody_eq, hpfx_eq, hd0, hpfx_ch, _h_after⟩ := parseFloatIntPart_props body intVal afterInt hip
        have hpfx_fmc : ∀ c ∈ pfx, isFloatModelChar c = true := by
          intro c hc
          rcases hpfx_ch c hc with rfl | hd
          · rfl
          · simp [isFloatModelChar, hd]
        have hhead : ∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigit b0 = true) := by
          refine ⟨d0, ptail ++ afterInt, ?_, Or.inr (Or.inr hd0)⟩
          rw [hbody_eq, hpfx_eq, List.cons_append]
        split at hb
        · rename_i afterDot
          refine ⟨hhead, fun ch hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc ch hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · cases afterDot with
                | nil => cases hb
                | cons c1 r1 =>
                  by_cases h_us : c1 = '_'
                  · subst h_us; cases hb
                  · split at hb
                    · cases hb
                    · rename_i c1' r1' hne heq_ad
                      injection heq_ad with hc_eq hr_eq
                      subst hc_eq; subst hr_eq
                      by_cases hd1 : NumParse.Model.isDecDigit c1 = true
                      · simp only [hd1, ↓reduceIte] at hb
                        cases hcf : NumParse.Model.consumeDecFloatDigits (intVal * 10 + (c1.toNat - '0'.toNat)) 1 r1 with
                        | error => rw [hcf] at hb; cases hb
                        | ok res2 =>
                          rcases res2 with ⟨mantissa, fracCount, afterFrac⟩
                          rw [hcf] at hb
                          dsimp only at hb
                          obtain ⟨fpfx, hr1, hfpfx, _⟩ := consumeDecFloatDigits_props _ _ _ _ _ _ hcf
                          rcases List.mem_cons.mp hc3 with rfl | hc4
                          · have : isAsciiDigit ch = true := by simpa [NumParse.Model.isDecDigit, isAsciiDigit] using hd1
                            simp [isFloatModelChar, this]
                          · rw [hr1] at hc4
                            rcases List.mem_append.mp hc4 with hfp | haf
                            · rcases hfpfx ch hfp with rfl | hd'
                              · rfl
                              · simp [isFloatModelChar, hd']
                            · exact parseFloatAfterFrac_props afterFrac neg mantissa fracCount f hb ch haf
                      · simp [hd1] at hb
                    · cases hb
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx '.' afterDot hpfx_ch (Or.inl rfl)
          · have hmem_dot : '.' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inl (Or.inl hmem_dot)
        · rename_i afterE
          refine ⟨hhead, fun c hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc c hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · exact parseFloatExpSuffix_props afterE _ f hb c hc3
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'e' afterE hpfx_ch (Or.inr (Or.inl rfl))
          · have hmem_e : 'e' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inl (Or.inr hmem_e)
        · rename_i afterE
          refine ⟨hhead, fun c hc => ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [hbody_eq] at hc
            rcases List.mem_append.mp hc with hc1 | hc2
            · exact hpfx_fmc c hc1
            · rcases List.mem_cons.mp hc2 with rfl | hc3
              · rfl
              · exact parseFloatExpSuffix_props afterE _ f hb c hc3
          · rw [hbody_eq]
            exact hasDatePrefix_false_of_digit_or_us_before_sep pfx 'E' afterE hpfx_ch (Or.inr (Or.inr rfl))
          · have hmem_E : 'E' ∈ body := by rw [hbody_eq]; simp
            simp only [List.contains_iff_mem, Bool.or_eq_true]
            exact Or.inr hmem_E
        · cases hb
  cases cs with
  | nil => simp [NumParse.Model.parseFloatModelChars] at h
  | cons c0 r0 =>
    by_cases hp : c0 = '+'
    · subst hp
      simp only [NumParse.Model.parseFloatModelChars] at h
      obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, _, hkind⟩ := hbody r0 false h
      have hfmc_all : ∀ c ∈ '+' :: r0, isFloatModelChar c = true := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · rfl
        · exact hfmc c hc'
      have hnd : hasDatePrefix ('+' :: r0) = false := by
        unfold hasDatePrefix
        split
        · rename_i heq; injection heq with h1 _; subst h1; rfl
        · rfl
      refine ⟨⟨'+', r0, rfl, Or.inl rfl⟩, hfmc_all, hnd, hnot_time _ hfmc_all, ?_⟩
      rcases hkind with rfl | rfl | hsep
      · decide
      · decide
      · apply hcand_of_sep _ hfmc_all
        simp only [List.contains_iff_mem, Bool.or_eq_true] at hsep ⊢
        rcases hsep with (h1 | h2) | h3
        · exact Or.inl (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inl (Or.inr (List.mem_cons_of_mem _ h2))
        · exact Or.inr (List.mem_cons_of_mem _ h3)
    · by_cases hm : c0 = '-'
      · subst hm
        simp only [NumParse.Model.parseFloatModelChars] at h
        obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, _, hkind⟩ := hbody r0 true h
        have hfmc_all : ∀ c ∈ '-' :: r0, isFloatModelChar c = true := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · rfl
          · exact hfmc c hc'
        have hnd : hasDatePrefix ('-' :: r0) = false := by
          unfold hasDatePrefix
          split
          · rename_i heq; injection heq with h1 _; subst h1; rfl
          · rfl
        refine ⟨⟨'-', r0, rfl, Or.inr (Or.inl rfl)⟩, hfmc_all, hnd, hnot_time _ hfmc_all, ?_⟩
        rcases hkind with rfl | rfl | hsep
        · decide
        · decide
        · apply hcand_of_sep _ hfmc_all
          simp only [List.contains_iff_mem, Bool.or_eq_true] at hsep ⊢
          rcases hsep with (h1 | h2) | h3
          · exact Or.inl (Or.inl (List.mem_cons_of_mem _ h1))
          · exact Or.inl (Or.inr (List.mem_cons_of_mem _ h2))
          · exact Or.inr (List.mem_cons_of_mem _ h3)
      · unfold NumParse.Model.parseFloatModelChars at h
        dsimp only at h
        have hfst : (match c0 :: r0 with
            | '+' :: rest => (false, rest)
            | '-' :: rest => (true, rest)
            | _ => (false, c0 :: r0)).fst = false := by
          split
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hp
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hm
          · rfl
        have hsnd : (match c0 :: r0 with
            | '+' :: rest => (false, rest)
            | '-' :: rest => (true, rest)
            | _ => (false, c0 :: r0)).snd = c0 :: r0 := by
          split
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hp
          · rename_i _ heq_c0; injection heq_c0 with h1 _; exact absurd h1 hm
          · rfl
        erw [hfst, hsnd] at h
        obtain ⟨⟨b0, br, hr0, hb0⟩, hfmc, hnd, hkind⟩ := hbody (c0 :: r0) false h
        have hhead : c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigit c0 = true := by
          injection hr0 with h1 _; subst h1
          rcases hb0 with rfl | rfl | hd
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
        refine ⟨⟨c0, r0, rfl, hhead⟩, hfmc, hnd, hnot_time _ hfmc, ?_⟩
        rcases hkind with h1 | h2 | hsep
        · rw [h1]; decide
        · rw [h2]; decide
        · exact hcand_of_sep _ hfmc hsep

private theorem consumeIntDigits_extra (b : NumParse.Model.NumBase) (acc : Nat)
    (cs : List Char) (n : Nat) (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) :
    ∀ c ∈ cs, c ≠ '.' ∧ c ≠ '-' := by
  induction n0 : cs.length using Nat.strongRecOn generalizing cs acc with
  | ind len ih =>
    intro c hc
    cases cs with
    | nil => cases hc
    | cons c0 rest =>
      by_cases hu : c0 = '_'
      · subst hu
        cases rest with
        | nil => simp [NumParse.Model.consumeIntDigits] at h
        | cons c1 cs1 =>
          simp only [NumParse.Model.consumeIntDigits] at h
          cases hc with
          | head => exact ⟨by decide, by decide⟩
          | tail _ hc' =>
            cases hdv : NumParse.Model.digitVal? b c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              have hc1 : c1 ≠ '.' ∧ c1 ≠ '-' := by
                cases b <;> simp [NumParse.Model.digitVal?] at hdv <;>
                  constructor <;> intro heq <;> subst heq <;> simp at hdv
              rcases List.mem_cons.mp hc' with rfl | hc''
              · exact hc1
              · exact ih cs1.length (by simp [← n0]; omega) (acc * b.radix + d) cs1 h rfl c hc''
      · unfold NumParse.Model.consumeIntDigits at h
        split at h
        · rename_i heq; cases heq
        · rename_i _ _ heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i heq; injection heq with h1 _; exact absurd h1 hu
        · rename_i c0' rest' _ _ heq
          injection heq with h1 h2
          rw [← h1, ← h2] at h
          cases hdv : NumParse.Model.digitVal? b c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            rcases List.mem_cons.mp hc with rfl | hc'
            · cases b <;> simp [NumParse.Model.digitVal?] at hdv <;>
                constructor <;> intro heq <;> subst heq <;> simp at hdv
            · exact ih rest.length (by simp [← n0]) (acc * b.radix + d) rest h rfl c hc'

private theorem parseDecAfterSign_extra (neg : Bool) (cs : List Char) (m : Int)
    (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    ∀ c ∈ cs, c ≠ '.' ∧ c ≠ '-' := by
  cases cs with
  | nil => simp [NumParse.Model.parseDecAfterSign] at h
  | cons c0 rest =>
    cases h0 : c0 == '_' with
    | true =>
      have hc0 : c0 = '_' := beq_iff_eq.mp h0
      subst hc0; simp [NumParse.Model.parseDecAfterSign] at h
    | false =>
      cases hzero : c0 == '0' with
      | true =>
        have hc0 : c0 = '0' := beq_iff_eq.mp hzero
        subst hc0
        cases rest with
        | nil =>
          intro c hc
          rcases List.mem_singleton.mp hc with rfl
          exact ⟨by decide, by decide⟩
        | cons c1 r1 =>
          by_cases hd1 : NumParse.Model.isDecDigit c1 = true
          · simp [NumParse.Model.parseDecAfterSign, hd1] at h
          · by_cases hu1 : c1 = '_'
            · subst hu1
              cases r1 with
              | nil => simp [NumParse.Model.parseDecAfterSign, hd1] at h
              | cons c2 tail =>
                by_cases hd2 : NumParse.Model.isDecDigit c2 = true <;>
                  simp [NumParse.Model.parseDecAfterSign, hd1, hd2] at h
            · simp [NumParse.Model.parseDecAfterSign, hd1, hu1] at h
      | false =>
        have hne0 : c0 ≠ '0' := fun he => by rw [he] at hzero; contradiction
        have hne_u : c0 ≠ '_' := fun he => by rw [he] at h0; contradiction
        unfold NumParse.Model.parseDecAfterSign at h
        split at h
        · contradiction
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_u
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne0
        · rename_i c0' rest' _ _ _ heq
          injection heq with h1 h2; subst h1; subst h2
          cases hdv : NumParse.Model.digitVal? .dec c0 with
          | none => rw [hdv] at h; cases h
          | some d =>
            rw [hdv] at h
            dsimp only at h
            cases hn : NumParse.Model.consumeIntDigits .dec d rest with
            | error => rw [hn] at h; cases h
            | ok n =>
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hc'
              · simp [NumParse.Model.digitVal?] at hdv
                constructor <;> intro heq <;> subst heq <;> simp at hdv
              · exact consumeIntDigits_extra .dec d rest n hn c hc'

private theorem parseIntModelChars_extra (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∀ c ∈ cs, c ≠ '.') ∧ (∀ c0 r0, cs = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
  unfold NumParse.Model.parseIntModelChars at h
  split at h
  · cases h
  · rename_i _ b rest
    split at h
    · cases h
    · have hd := parseDecAfterSign_extra false ('0' :: b :: rest) m h
      refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hd c hc').1
      · injection hcr with _ hr; subst hr
        exact (hd c hc).2
  · rename_i _ b rest
    split at h
    · cases h
    · have hd := parseDecAfterSign_extra true ('0' :: b :: rest) m h
      refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact (hd c hc').1
      · injection hcr with _ hr; subst hr
        exact (hd c hc).2
  · rename_i _ rest _
    have hd := parseDecAfterSign_extra false rest m h
    refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hd c hc').1
    · injection hcr with _ hr; subst hr
      exact (hd c hc).2
  · rename_i _ rest _
    have hd := parseDecAfterSign_extra true rest m h
    refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc'
      · decide
      · exact (hd c hc').1
    · injection hcr with _ hr; subst hr
      exact (hd c hc).2
  · rename_i _ b rest
    cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h
      dsimp only at h
      have hd := parseDecAfterSign_extra false ('0' :: b :: rest) m h
      refine ⟨fun c hc => (hd c hc).1, fun c0 r0 hcr c hc => ?_⟩
      injection hcr with _ hr; subst hr
      exact (hd c (List.mem_cons_of_mem _ hc)).2
    | some base =>
      rw [hbp] at h
      dsimp only at h
      cases rest with
      | nil => cases h
      | cons c1 cs1 =>
        by_cases hu : c1 = '_'
        · subst hu; cases h
        · split at h
          · cases h
          · cases h
          · rename_i c1' cs1' _ _ heq
            injection heq with h1 h2; subst h1; subst h2
            cases hdv : NumParse.Model.digitVal? base c1 with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              cases hn : NumParse.Model.consumeIntDigits base d cs1 with
              | error => rw [hn] at h; cases h
              | ok n =>
                have hex := consumeIntDigits_extra base d cs1 n hn
                have hc1_ne : c1 ≠ '.' ∧ c1 ≠ '-' := by
                  cases base <;> simp [NumParse.Model.digitVal?] at hdv <;>
                    constructor <;> intro heq <;> subst heq <;> simp at hdv
                have hb_ne : b ≠ '.' ∧ b ≠ '-' := by
                  constructor <;> intro heq <;> subst heq <;> cases hbp
                refine ⟨fun c hc => ?_, fun c0 r0 hcr c hc => ?_⟩
                · rcases List.mem_cons.mp hc with rfl | hc
                  · decide
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hb_ne.1
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hc1_ne.1
                  · exact (hex c hc).1
                · injection hcr with _ hr; subst hr
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hb_ne.2
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hc1_ne.2
                  · exact (hex c hc).2
  · have hd := parseDecAfterSign_extra false cs m h
    refine ⟨fun c hc => (hd c hc).1, fun c0 r0 hcr c hc => ?_⟩
    rw [hcr] at hd
    exact (hd c (List.mem_cons_of_mem _ hc)).2

private theorem hasDatePrefix_imp (cs : List Char) (h : hasDatePrefix cs = true) :
    ∃ y1 y2 y3 y4 m1 m2 d1 d2 rest,
      cs = y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: rest := by
  unfold hasDatePrefix at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

private theorem hasTimePrefix_imp (cs : List Char) (h : hasTimePrefix cs = true) :
    ':' ∈ cs := by
  unfold hasTimePrefix at h
  split at h
  · simp
  · cases h

private theorem parseIntModelChars_no_datePrefix (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    hasDatePrefix cs = false ∧ hasTimePrefix cs = false := by
  obtain ⟨⟨c0, rest, hcs, _, _⟩, hno_col⟩ := parseIntModelChars_props cs m h
  obtain ⟨_, hno_dash⟩ := parseIntModelChars_extra cs m h
  refine ⟨?_, ?_⟩
  · cases hdp : hasDatePrefix cs
    · rfl
    · obtain ⟨y1, y2, y3, y4, m1, m2, d1, d2, rest', heq⟩ := hasDatePrefix_imp cs hdp
      have hcs' : c0 :: rest = y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: rest' := by
        rw [← hcs, heq]
      injection hcs' with _ hrest
      have hdash : '-' ∈ rest := by rw [hrest]; simp
      exact absurd rfl (hno_dash c0 rest hcs '-' hdash)
  · cases htp : hasTimePrefix cs
    · rfl
    · exact absurd rfl (hno_col ':' (hasTimePrefix_imp cs htp))

private theorem isValidIntLex_classifyScalarToken (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (s : String) (n : Int64) (h : isValidIntLex s n = true) :
    classifyScalarToken numApi s = .ok (.int n) ∧
    (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
    ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidIntLex, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨hchars, hno_up⟩, hno_exp⟩, hbeq⟩
  have hn_eq : (match NumParse.Model.parseInt64Model s with | .ok m => m == n | .error _ => false) = true :=
    hbeq
  have hp_model : NumParse.Model.parseInt64Model s = .ok n := by
    cases hp : NumParse.Model.parseInt64Model s with
    | error => rw [hp] at hn_eq; cases hn_eq
    | ok m =>
      rw [hp] at hn_eq
      have hmn : m = n := by simpa using hn_eq
      subst hmn; rfl
  have hm_chars : ∃ m : Int, NumParse.Model.parseIntModelChars s.toList = .ok m := by
    unfold NumParse.Model.parseInt64Model NumParse.Model.parseIntModel at hp_model
    cases hc : NumParse.Model.parseIntModelChars s.toList with
    | error => rw [hc] at hp_model; cases hp_model
    | ok m => exact ⟨m, rfl⟩
  rcases hm_chars with ⟨m, hm⟩
  obtain ⟨⟨c0, rest, hlist, hc0, hc1⟩, hno_col⟩ := parseIntModelChars_props s.toList m hm
  obtain ⟨hno_dot, _⟩ := parseIntModelChars_extra s.toList m hm
  obtain ⟨hnd, hnt⟩ := parseIntModelChars_no_datePrefix s.toList m hm
  have hnot_empty : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have hnil : s.toList = [] := by
      have : s = "" := by simpa using he
      subst this; rfl
    rw [hnil] at hlist; cases hlist
  have hnot_true : s ≠ "true" := by
    intro heq; subst heq
    rcases hc0 with rfl | rfl | hdig
    · cases hlist
    · cases hlist
    · injection hlist with h0 _; subst h0; revert hdig; decide
  have hnot_false : s ≠ "false" := by
    intro heq; subst heq
    rcases hc0 with rfl | rfl | hdig
    · cases hlist
    · cases hlist
    · injection hlist with h0 _; subst h0; revert hdig; decide
  have hnot_colon : ¬(':' ∈ s.toList) := fun hc => hno_col ':' hc rfl
  have hnot_dt : parseDateTimeToken s = none := by
    simp [parseDateTimeToken, hnd, hnt, hnot_colon]
  have hnot_spec : (s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = false := by
    have hs_list : ∀ t : String, s = t → s.toList = t.toList := fun t ht => by subst ht; rfl
    have hc_head : ∀ (t : String) (d : Char) (td : List Char), t.toList = d :: td →
        (d ≠ '+' ∧ d ≠ '-' ∧ isAsciiDigit d = false) → s ≠ t := by
      intro t d td ht hd hs_eq
      have h' := hs_list t hs_eq
      rw [hlist, ht] at h'
      injection h' with hd0 _
      subst hd0
      rcases hc0 with rfl | rfl | hdig
      · exact hd.1 rfl
      · exact hd.2.1 rfl
      · rw [hdig] at hd; cases hd.2.2
    have hc_snd : ∀ (t : String) (s0 s1 : Char) (td : List Char), t.toList = s0 :: s1 :: td →
        (s0 = '+' ∨ s0 = '-') → isAsciiDigit s1 = false → s ≠ t := by
      intro t s0 s1 td ht hs0 hs1 hs_eq
      have h' := hs_list t hs_eq
      rw [hlist, ht] at h'
      injection h' with hc0_eq hr_eq
      rcases hc0 with rfl | rfl | hdig
      · have hd1 := hc1 s1 td (Or.inl rfl) hr_eq
        rw [hd1] at hs1; cases hs1
      · have hd1 := hc1 s1 td (Or.inr rfl) hr_eq
        rw [hd1] at hs1; cases hs1
      · rw [hc0_eq] at hdig
        rcases hs0 with rfl | rfl <;> cases hdig
    have hni : s ≠ "inf" := hc_head "inf" 'i' ['n', 'f'] rfl (by decide)
    have hnn : s ≠ "nan" := hc_head "nan" 'n' ['a', 'n'] rfl (by decide)
    have hnpi : s ≠ "+inf" := hc_snd "+inf" '+' 'i' ['n', 'f'] rfl (Or.inl rfl) (by decide)
    have hnmi : s ≠ "-inf" := hc_snd "-inf" '-' 'i' ['n', 'f'] rfl (Or.inr rfl) (by decide)
    have hnpn : s ≠ "+nan" := hc_snd "+nan" '+' 'n' ['a', 'n'] rfl (Or.inl rfl) (by decide)
    have hnmn : s ≠ "-nan" := hc_snd "-nan" '-' 'n' ['a', 'n'] rfl (Or.inr rfl) (by decide)
    simp [hni, hnpi, hnmi, hnn, hnpn, hnmn]
  have hndot : ¬('.' ∈ s.toList) := fun hmem => hno_dot '.' hmem rfl
  have hnot_float_cand : isFloatTokenCandidate s = false := by
    unfold isFloatTokenCandidate
    rw [hnot_spec, Bool.false_or]
    split at hno_exp
    · rename_i hhex
      simp [hhex]
    · simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at hno_exp
      have hne1 : ¬('e' ∈ s.toList) := by
        have h1 : s.contains 'e' = false := hno_exp.1
        simpa [String.contains_char_eq] using h1
      have hne2 : ¬('E' ∈ s.toList) := by
        have h2 : s.contains 'E' = false := hno_exp.2
        simpa [String.contains_char_eq] using h2
      simp [hndot, hne1, hne2]
  have hcls : classifyScalarToken numApi s = .ok (.int n) := by
    simp [classifyScalarToken, hasUppercaseBasePrefix, hnot_empty, hnot_true, hnot_false, hnot_dt,
      hnot_float_cand, hchars]
    rw [hInt s n hp_model]
  refine ⟨hcls, ?_, c0, rest, hlist, ?_⟩
  · rw [List.all_eq_true] at hno_up ⊢
    intro c hc
    have h1 := hno_up c hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h1
    have hws : c.isWhitespace = false := h1.1.1.1.1.1.1
    have hnl : c ≠ '\n' := by
      intro heq; subst heq
      exact absurd (by decide : ('\n').isWhitespace = true) (by simp [hws])
    have hcr : c ≠ '\r' := by
      intro heq; subst heq
      exact absurd (by decide : ('\r').isWhitespace = true) (by simp [hws])
    have hud : isUnquotedDelim c = false :=
      not_unquotedDelim_of_not_ws c hws
        (bne_iff_ne.mpr h1.1.1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.1.2)
        (bne_iff_ne.mpr h1.1.1.2)
    simp [h1.2, hcr, hnl, hud]
  · rcases hc0 with rfl | rfl | hdig
    · decide
    · decide
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide

/-- Two `Float` values with identical IEEE 754 bit patterns are equal. -/
theorem float_eq_of_toBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  cases a with | ofModel am =>
  cases b with | ofModel bm =>
  cases am with | mk ab _ =>
  cases bm with | mk bb _ =>
  cases h
  rfl

private theorem float_beq_props (a b : Float) (h : (a == b) = true) :
    (b == a) = true ∧ a.isNaN = false ∧ b.isNaN = false := by
  have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h
  change (b.toModel.unpack.compare a.toModel.unpack == some .eq) = true ∧
    a.toModel.unpack.isNaN = false ∧ b.toModel.unpack.isNaN = false
  cases hu1 : a.toModel.unpack with
  | notANumber => simp [hu1, Float.Model.UnpackedFloat.compare] at hbeq
  | infinity s1 =>
    cases s1 <;> cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp_all [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN]
    | zero _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | finite _ _ _ _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
  | zero s1 =>
    cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | zero _ => simp [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN]
    | finite s2 _ _ _ => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
  | finite s1 m1 e1 p1 =>
    cases s1 <;> cases hu2 : b.toModel.unpack with
    | notANumber => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | infinity s2 => cases s2 <;> simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | zero _ => simp [hu1, hu2, Float.Model.UnpackedFloat.compare] at hbeq
    | finite s2 m2 e2 p2 =>
      cases s2 <;> simp_all [Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] <;>
        exact ⟨by omega, by omega⟩

private theorem float_beq_refl_of_nonNaN (a : Float) (h : a.isNaN = false) : (a == a) = true := by
  exact (NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [h]) (by simp [h])).mp (NumParse.Model.floatEquiv_refl a)

/-- Any string satisfying `FloatFormatSpec f s` is a valid TOML float lexeme for `f`. -/
theorem floatFormatSpec_isValidFloatLex (f : Float) (s : String)
    (hs : NumParse.Model.FloatFormatSpec f s) :
    isValidFloatLex s f = true := by
  simp only [NumParse.Model.FloatFormatSpec] at hs
  by_cases hnan : f.isNaN = true
  · simp only [hnan, ite_true] at hs
    subst hs
    have hp : NumParse.Model.parseFloatModel "nan" = .ok Float.nan := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hnan_lit : Float.nan.isNaN = true := by decide
    simp [isValidFloatLex, hp, hnan, hnan_lit]
    decide
  · have hnan_f : f.isNaN = false := Bool.eq_false_iff.mpr hnan
    simp only [hnan] at hs
    by_cases hinf : (f == Float.inf) = true
    · simp only [hinf, ite_true] at hs
      subst hs
      have hp : NumParse.Model.parseFloatModel "inf" = .ok Float.inf := by
        simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
      have hsym : (Float.inf == f) = true := (float_beq_props f Float.inf hinf).1
      simp [isValidFloatLex, hp, hsym]
      decide
    · simp only [hinf] at hs
      by_cases hninf : (f == -Float.inf) = true
      · simp only [hninf, ite_true] at hs
        subst hs
        have hp : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf) := by
          simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
        have hsym : (-Float.inf == f) = true := (float_beq_props f (-Float.inf) hninf).1
        simp [isValidFloatLex, hp, hsym]
        decide
      · simp only [hninf] at hs
        rcases hs with ⟨_, hsep, hmatch⟩
        cases hp : NumParse.Model.parseFloatModel s with
        | error => rw [hp] at hmatch; cases hmatch
        | ok y =>
          rw [hp] at hmatch
          have hy_eq : y = f := float_eq_of_toBits_eq hmatch
          subst hy_eq
          have hp_chars : NumParse.Model.parseFloatModelChars s.toList = .ok y := by
            simpa [NumParse.Model.parseFloatModel] using hp
          obtain ⟨_, hfmc, _, _, _⟩ := parseFloatModelChars_props s.toList y hp_chars
          have hnoTerm : (s.toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true := by
            rw [List.all_eq_true]
            intro c hc
            exact (isFloatModelChar_props c (hfmc c hc)).2.2.2.1
          have hmark : (s.contains '.' || s.contains 'e' || s.contains 'E' ||
              s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = true := by
            rcases hsep with h1 | h1 | h1 <;>
              simp only [String.contains_char_eq, decide_eq_true_eq] at h1 <;>
              simp [h1]
          have hbeq : (y == y) = true := float_beq_refl_of_nonNaN y hnan_f
          simp only [isValidFloatLex]
          rw [hmark, hnoTerm, hp]
          simp [hbeq]

private theorem isValidFloatLex_classifyScalarToken (numApi : NumParseApi)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (s : String) (f : Float) (h : isValidFloatLex s f = true) :
    ∃ g, classifyScalarToken numApi s = .ok (.float g) ∧
      TomlEquiv (.float f) (.float g) ∧
      (s.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true ∧
      ∃ c0 cs0, s.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
  simp only [isValidFloatLex, Bool.and_eq_true] at h
  rcases h with ⟨⟨_, _⟩, hmatch⟩
  cases hp : NumParse.Model.parseFloatModel s with
  | error => rw [hp] at hmatch; cases hmatch
  | ok g =>
    rw [hp] at hmatch
    have hp_chars : NumParse.Model.parseFloatModelChars s.toList = .ok g := by
      simpa [NumParse.Model.parseFloatModel] using hp
    obtain ⟨⟨c0, rest, hlist, hc0⟩, hfmc, hnd, hnt, hcand⟩ :=
      parseFloatModelChars_props s.toList g hp_chars
    have hnot_empty : s.isEmpty = false := by
      rw [Bool.eq_false_iff]
      intro he
      have hnil : s.toList = [] := by
        have : s = "" := by simpa using he
        subst this; rfl
      rw [hnil] at hlist; cases hlist
    have hnot_true : s ≠ "true" := by
      intro heq; subst heq
      rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · cases hlist
      · cases hlist
      · cases hlist
      · cases hlist
      · injection hlist with h0 _; subst h0; revert hdig; decide
    have hnot_false : s ≠ "false" := by
      intro heq; subst heq
      rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · cases hlist
      · cases hlist
      · cases hlist
      · cases hlist
      · injection hlist with h0 _; subst h0; revert hdig; decide
    have hnot_colon : ¬(':' ∈ s.toList) := by
      intro hc
      have := hfmc ':' hc
      cases this
    have hnot_dt : parseDateTimeToken s = none := by
      simp [parseDateTimeToken, hnd, hnt, hnot_colon]
    obtain ⟨g', hg', hbit⟩ := hFloat s g hp
    have hcls : classifyScalarToken numApi s = .ok (.float g') := by
      rw [String.ofList_toList] at hcand
      simp [classifyScalarToken, hnot_empty, hnot_true, hnot_false, hnot_dt, hcand, hg']
    have heq_f : TomlEquiv (.float f) (.float g') := by
      simp only [TomlEquiv]
      have heq_fg : NumParse.Model.FloatEquiv f g := by
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hmatch
        rcases hmatch with ⟨hg_nan, hf_nan⟩ | hgf
        · exact Or.inl ⟨hf_nan, hg_nan⟩
        · obtain ⟨hfg, hna_g, hna_f⟩ := float_beq_props g f hgf
          exact (NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [hna_f]) (by simp [hna_g])).mpr hfg
      exact NumParse.Model.floatEquiv_trans heq_fg
        (NumParse.Model.floatEquiv_symm (NumParse.Model.floatBitMatch_implies_floatEquiv hbit))
    refine ⟨g', hcls, heq_f, ?_, c0, rest, hlist, ?_⟩
    · rw [List.all_eq_true]
      intro c hc
      exact (isFloatModelChar_props c (hfmc c hc)).2.2.2.2
    · rcases hc0 with rfl | rfl | rfl | rfl | hdig
      · decide
      · decide
      · decide
      · decide
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide

private theorem canonicalFloat_isValidFloatLex (f : Float) :
    (f.isNaN = true → isValidFloatLex "nan" f = true) ∧
    ((f == Float.inf) = true → isValidFloatLex "inf" f = true) ∧
    ((f == -Float.inf) = true → isValidFloatLex "-inf" f = true) ∧
    (f.toBits = (0.0 : Float).toBits → isValidFloatLex "0.0" f = true) ∧
    (f.toBits = (-0.0 : Float).toBits → isValidFloatLex "-0.0" f = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnan
    have hp : NumParse.Model.parseFloatModel "nan" = .ok Float.nan := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hnan_lit : Float.nan.isNaN = true := by decide
    simp [isValidFloatLex, hp, hnan, hnan_lit]
    decide
  · intro hinf
    have hp : NumParse.Model.parseFloatModel "inf" = .ok Float.inf := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hsym := (float_beq_props f Float.inf hinf).1
    simp [isValidFloatLex, hp, hsym]
    decide
  · intro hninf
    have hp : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    have hsym := (float_beq_props f (-Float.inf) hninf).1
    simp [isValidFloatLex, hp, hsym]
    decide
  · intro hbits
    have hfeq : f = (0.0 : Float) := float_eq_of_toBits_eq hbits
    subst hfeq
    have hp : NumParse.Model.parseFloatModel "0.0" = .ok (0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_zero]
    have h0_eq : ((0.0 : Float) == (0.0 : Float)) = true := by decide
    simp [isValidFloatLex, hp, h0_eq]
    decide
  · intro hbits
    have hfeq : f = (-0.0 : Float) := float_eq_of_toBits_eq hbits
    subst hfeq
    have hp : NumParse.Model.parseFloatModel "-0.0" = .ok (-0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_neg_zero]
    have h0_eq : ((-0.0 : Float) == (-0.0 : Float)) = true := by decide
    simp [isValidFloatLex, hp, h0_eq]
    decide

private theorem parseValueFuel_unquoted (numApi : NumParseApi) (fuel : Nat) (c0 : Char) (cs : List Char)
    (hq1 : c0 ≠ '"') (hq2 : c0 ≠ '\'') (hb : c0 ≠ '[') (hbr : c0 ≠ '{') :
    parseValueFuel numApi (fuel + 1) (c0 :: cs) =
      (let (tok, rest) := takeUnquotedToken (c0 :: cs)
       classifyScalarToken numApi tok >>= fun v => .ok (v, rest)) := by
  conv => lhs; unfold parseValueFuel
  split <;>
    first
    | exact absurd rfl hq1
    | exact absurd rfl hq2
    | exact absurd rfl hb
    | exact absurd rfl hbr
    | (rename_i heq; injection heq with h1 _; first
      | exact absurd h1 hq1
      | exact absurd h1 hq2
      | exact absurd h1 hb
      | exact absurd h1 hbr)
    | rfl

private theorem clean_no_nl_of_full (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) :
    (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact h1.1

private theorem clean_cr_of_no_nl (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) :
    (cs.all fun c => !isDisallowedControl c && c != '\r') = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact h1.1

private theorem renderValueInline_scalar_parseValueFuel (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (v : TomlValue) (tape : ValueTape)
    (rs : String) (hr : renderValueInline v tape = some rs)
    (rest : List Char) (fuel : Nat) (hf : fuel ≥ 1)
    (hscalar : match v with | .array _ => False | .table _ => False | _ => True)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
      TomlEquiv v v' ∧
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
      ((∀ s st, v = .string s → tape = .string st → st = .basic ∨ st = .literal) →
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) := by
  cases fuel with
  | zero => omega
  | succ f =>
    have hrest_q : ∀ c r, rest = c :: r → c ≠ '"' ∧ c ≠ '\'' := by
      intro c r h
      have hd := (hrest c r h).1
      exact ⟨fun hc => (by subst hc; cases hd), fun hc => (by subst hc; cases hd)⟩
    have hrest_delim : ∀ c r, rest = c :: r → isUnquotedDelim c = true :=
      fun c r h => (hrest c r h).1
    cases v with
    | array _ => cases hscalar
    | table _ => cases hscalar
    | string s =>
      cases tape with
      | string st =>
        simp only [renderValueInline] at hr
        obtain ⟨hp, hcl, hsl⟩ := renderStringLiteral_parseValueFuel numApi s st rs hr rest (f + 1) (by omega) hrest_q
        refine ⟨.string s, hp, tomlEquiv_refl _, hcl, fun h => ?_⟩
        exact hsl (h s st rfl rfl)
      | _ => simp [renderValueInline] at hr
    | int n =>
      cases tape with
      | int olex =>
        have hlex : isValidIntLex rs n = true := by
          cases olex with
          | none =>
            simp only [renderValueInline] at hr
            injection hr with hrs; subst hrs
            exact formatInt64Canonical_isValidIntLex n
          | some lex =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i hv
              injection hr with hrs; subst hrs; exact hv
            · cases hr
        obtain ⟨hcls, hcl, c0, cs0, hrs_list, hq1, hq2, hb, hbr⟩ :=
          isValidIntLex_classifyScalarToken numApi hInt rs n hlex
        have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
        rw [String.ofList_toList] at htok
        have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.int n, rest) := by
          rw [hrs_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hq1 hq2 hb hbr]
          rw [← List.cons_append, ← hrs_list, htok]
          simp [hcls, bind, Except.bind]
        have hnl := clean_no_nl_of_full _ hcl
        exact ⟨.int n, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | float fl =>
      cases tape with
      | float olex =>
        have hlex : isValidFloatLex rs fl = true := by
          cases olex with
          | none =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i h1; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).1 h1
            · split at hr
              · rename_i h2; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.1 h2
              · split at hr
                · rename_i h3; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.1 h3
                · split at hr
                  · rename_i h4; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.1 (by simpa using h4)
                  · split at hr
                    · rename_i h5; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.2 (by simpa using h5)
                    · cases hr
          | some lex =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i hv; injection hr with hrs; subst hrs; exact hv
            · cases hr
        obtain ⟨g, hcls, heq_f, hcl, c0, cs0, hrs_list, hq1, hq2, hb, hbr⟩ :=
          isValidFloatLex_classifyScalarToken numApi hFloat rs fl hlex
        have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
        rw [String.ofList_toList] at htok
        have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.float g, rest) := by
          rw [hrs_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hq1 hq2 hb hbr]
          rw [← List.cons_append, ← hrs_list, htok]
          simp [hcls, bind, Except.bind]
        have hnl := clean_no_nl_of_full _ hcl
        exact ⟨.float g, hpv, heq_f, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | bool b =>
      cases tape with
      | bool =>
        cases b
        · simp [renderValueInline] at hr
          subst hr
          have htok := takeUnquotedToken_noSpace ("false" : String).toList rest (by decide) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi "false" = .ok (.bool false) := rfl
          refine ⟨.bool false, ?_, tomlEquiv_refl _, by decide, fun _ => by decide⟩
          have hf_list : ("false" : String).toList = ['f', 'a', 'l', 's', 'e'] := rfl
          rw [hf_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f 'f' (['a', 'l', 's', 'e'] ++ rest) (by decide) (by decide) (by decide) (by decide)]
          rw [← List.cons_append, ← hf_list, htok]
          simp [hcls, bind, Except.bind]
        · simp [renderValueInline] at hr
          subst hr
          have htok := takeUnquotedToken_noSpace ("true" : String).toList rest (by decide) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi "true" = .ok (.bool true) := rfl
          refine ⟨.bool true, ?_, tomlEquiv_refl _, by decide, fun _ => by decide⟩
          have ht_list : ("true" : String).toList = ['t', 'r', 'u', 'e'] := rfl
          rw [ht_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f 't' (['r', 'u', 'e'] ++ rest) (by decide) (by decide) (by decide) (by decide)]
          rw [← List.cons_append, ← ht_list, htok]
          simp [hcls, bind, Except.bind]
      | _ => simp [renderValueInline] at hr
    | localDate d =>
      cases tape with
      | localDate =>
        simp only [renderValueInline] at hr
        obtain ⟨hdt, hcl, hhd⟩ := renderDate_localDate d rs hr
        cases hrs_list : rs.toList with
        | nil =>
          have hrs : rs = "" := by rw [← String.ofList_toList (s := rs), hrs_list]
          subst hrs; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
        | cons c0 cs0 =>
          have hdig := hhd c0 cs0 hrs_list
          have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
          have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi rs = .ok (.localDate d) := by
            have hne : rs.isEmpty = false := by
              rw [Bool.eq_false_iff]; intro he
              have : rs = "" := by simpa using he
              subst this; cases hrs_list
            have hnt : rs ≠ "true" := fun he => by subst he; cases hrs_list; revert hdig; decide
            have hnf : rs ≠ "false" := fun he => by subst he; cases hrs_list; revert hdig; decide
            simp [classifyScalarToken, hne, hnt, hnf, hdt]
          have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.localDate d, rest) := by
            rw [hrs_list, List.cons_append]
            rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
            rw [← List.cons_append, ← hrs_list, htok]
            simp [hcls, bind, Except.bind]
          have hnl := clean_no_nl_of_full _ hcl
          rw [← hrs_list]
          exact ⟨.localDate d, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | localTime t =>
      cases tape with
      | localTime fd =>
        simp only [renderValueInline] at hr
        obtain ⟨hdt, hcl, hhd⟩ := renderTime_localTime t fd rs hr
        cases hrs_list : rs.toList with
        | nil =>
          have hrs : rs = "" := by rw [← String.ofList_toList (s := rs), hrs_list]
          subst hrs; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
        | cons c0 cs0 =>
          have hdig := hhd c0 cs0 hrs_list
          have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
          have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi rs = .ok (.localTime t) := by
            have hne : rs.isEmpty = false := by
              rw [Bool.eq_false_iff]; intro he
              have : rs = "" := by simpa using he
              subst this; cases hrs_list
            have hnt : rs ≠ "true" := fun he => by subst he; cases hrs_list; revert hdig; decide
            have hnf : rs ≠ "false" := fun he => by subst he; cases hrs_list; revert hdig; decide
            simp [classifyScalarToken, hne, hnt, hnf, hdt]
          have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.localTime t, rest) := by
            rw [hrs_list, List.cons_append]
            rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
            rw [← List.cons_append, ← hrs_list, htok]
            simp [hcls, bind, Except.bind]
          have hnl := clean_no_nl_of_full _ hcl
          rw [← hrs_list]
          exact ⟨.localTime t, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | localDateTime dt =>
      cases tape with
      | localDateTime sep fd =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hdr : renderDate dt.date with
        | none => simp [hdr] at hr
        | some ds =>
          cases htr : renderTime dt.time fd with
          | none => simp [hdr, htr] at hr
          | some ts =>
            simp only [hdr, htr, Option.some.injEq] at hr
            subst hr
            obtain ⟨_, hds_cl, hds_hd⟩ := renderDate_localDate dt.date ds hdr
            obtain ⟨_, hts_cl, _⟩ := renderTime_localTime dt.time fd ts htr
            have hdt := renderDateTime_localDateTime dt sep fd ds ts hdr htr
            have hds_ne : ds.toList ≠ [] := by
              intro hnil
              have h1 : ds = "" := by rw [← String.ofList_toList (s := ds), hnil]
              subst h1; simp [renderDate] at hdr
            cases hds_list : ds.toList with
            | nil => exact absurd hds_list hds_ne
            | cons c0 cs0 =>
              have hdig := hds_hd c0 cs0 hds_list
              have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
                refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
              have htok : takeUnquotedToken ((ds ++ renderDateTimeSep sep ++ ts).toList ++ rest) =
                  (ds ++ renderDateTimeSep sep ++ ts, rest) := by
                cases sep
                · have hsep_cl : (("T" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                  have hfull_cl : (ds ++ renderDateTimeSep .upperT ++ ts).toList.all (fun c => !isUnquotedDelim c) = true := by
                    simp only [renderDateTimeSep, String.toList_append, List.all_append,
                      clean_all_not_unquotedDelim _ hds_cl, hsep_cl, clean_all_not_unquotedDelim _ hts_cl,
                      Bool.and_self]
                  have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .upperT ++ ts).toList rest hfull_cl hrest
                  simpa [String.ofList_toList, String.append_assoc] using ht
                · have hsep_cl : (("t" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                  have hfull_cl : (ds ++ renderDateTimeSep .lowerT ++ ts).toList.all (fun c => !isUnquotedDelim c) = true := by
                    simp only [renderDateTimeSep, String.toList_append, List.all_append,
                      clean_all_not_unquotedDelim _ hds_cl, hsep_cl, clean_all_not_unquotedDelim _ hts_cl,
                      Bool.and_self]
                  have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .lowerT ++ ts).toList rest hfull_cl hrest
                  simpa [String.ofList_toList, String.append_assoc] using ht
                · have ht := dateTime_space_takeUnquotedToken dt.date dt.time fd ds ts "" hdr htr (by decide) rest hrest_delim
                  simpa [renderDateTimeSep, String.append_empty] using ht
              have hcls : classifyScalarToken numApi (ds ++ renderDateTimeSep sep ++ ts) = .ok (.localDateTime dt) := by
                have hfull_list : (ds ++ renderDateTimeSep sep ++ ts).toList = c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList) := by
                  simp [String.toList_append, hds_list, List.cons_append]
                have hne : (ds ++ renderDateTimeSep sep ++ ts).isEmpty = false := by
                  rw [Bool.eq_false_iff]; intro he
                  have h1 : (ds ++ renderDateTimeSep sep ++ ts) = "" := by simpa using he
                  have h2 := congrArg String.toList h1
                  rw [hfull_list] at h2; cases h2
                have hnt : (ds ++ renderDateTimeSep sep ++ ts) ≠ "true" := by
                  intro he
                  have h2 := congrArg String.toList he
                  rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                have hnf : (ds ++ renderDateTimeSep sep ++ ts) ≠ "false" := by
                  intro he
                  have h2 := congrArg String.toList he
                  rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                simp [classifyScalarToken, hne, hnt, hnf, hdt]
              have hpv : parseValueFuel numApi (f + 1) ((ds ++ renderDateTimeSep sep ++ ts).toList ++ rest) =
                  .ok (.localDateTime dt, rest) := by
                have hfull_list : (ds ++ renderDateTimeSep sep ++ ts).toList = c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList) := by
                  simp [String.toList_append, hds_list, List.cons_append]
                rw [hfull_list, List.cons_append]
                rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ rest)
                  hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
                rw [← List.cons_append, ← hfull_list, htok]
                simp [hcls, bind, Except.bind]
              have hsep_cl : ((renderDateTimeSep sep).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                cases sep <;> decide
              have hcl : ((ds ++ renderDateTimeSep sep ++ ts).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                simp only [String.toList_append, List.all_append, hsep_cl, clean_no_nl_of_full _ hds_cl,
                  clean_no_nl_of_full _ hts_cl, Bool.and_self]
              exact ⟨.localDateTime dt, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hcl, fun _ => hcl⟩
      | _ => simp [renderValueInline] at hr
    | offsetDateTime odt =>
      cases tape with
      | offsetDateTime sep oStyle fd =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hdr : renderDate odt.dateTime.date with
        | none => simp [hdr] at hr
        | some ds =>
          cases htr : renderTime odt.dateTime.time fd with
          | none => simp [hdr, htr] at hr
          | some ts =>
            cases hor : renderOffset odt.offset oStyle with
            | none => simp [hdr, htr, hor] at hr
            | some os =>
              simp only [hdr, htr, hor, Option.some.injEq] at hr
              subst hr
              obtain ⟨_, hds_cl, hds_hd⟩ := renderDate_localDate odt.dateTime.date ds hdr
              obtain ⟨_, hts_cl, _⟩ := renderTime_localTime odt.dateTime.time fd ts htr
              obtain ⟨_, hos_cl⟩ := renderOffset_parseOffsetPart odt.offset oStyle os hor
              have hdt := renderOffsetDateTime_offsetDateTime odt sep oStyle fd ds ts os hdr htr hor
              have hds_ne : ds.toList ≠ [] := by
                intro hnil
                have h1 : ds = "" := by rw [← String.ofList_toList (s := ds), hnil]
                subst h1; simp [renderDate] at hdr
              cases hds_list : ds.toList with
              | nil => exact absurd hds_list hds_ne
              | cons c0 cs0 =>
                have hdig := hds_hd c0 cs0 hds_list
                have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
                have htok : takeUnquotedToken ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList ++ rest) =
                    (ds ++ renderDateTimeSep sep ++ ts ++ os, rest) := by
                  cases sep
                  · have hsep_cl : (("T" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                    have hfull_cl : (ds ++ renderDateTimeSep .upperT ++ ts ++ os).toList.all (fun c => !isUnquotedDelim c) = true := by
                      simp only [renderDateTimeSep, String.toList_append, List.all_append,
                        clean_all_not_unquotedDelim _ hds_cl, hsep_cl,
                        clean_all_not_unquotedDelim _ hts_cl, clean_all_not_unquotedDelim _ hos_cl,
                        Bool.and_self]
                    have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .upperT ++ ts ++ os).toList rest hfull_cl hrest
                    simpa [String.ofList_toList, String.append_assoc] using ht
                  · have hsep_cl : (("t" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                    have hfull_cl : (ds ++ renderDateTimeSep .lowerT ++ ts ++ os).toList.all (fun c => !isUnquotedDelim c) = true := by
                      simp only [renderDateTimeSep, String.toList_append, List.all_append,
                        clean_all_not_unquotedDelim _ hds_cl, hsep_cl,
                        clean_all_not_unquotedDelim _ hts_cl, clean_all_not_unquotedDelim _ hos_cl,
                        Bool.and_self]
                    have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .lowerT ++ ts ++ os).toList rest hfull_cl hrest
                    simpa [String.ofList_toList, String.append_assoc] using ht
                  · exact dateTime_space_takeUnquotedToken odt.dateTime.date odt.dateTime.time fd ds ts os hdr htr
                      (clean_all_not_unquotedDelim _ hos_cl) rest hrest_delim
                have hcls : classifyScalarToken numApi (ds ++ renderDateTimeSep sep ++ ts ++ os) = .ok (.offsetDateTime odt) := by
                  have hfull_list : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList =
                      c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList) := by
                    simp [String.toList_append, hds_list, List.cons_append, List.append_assoc]
                  have hne : (ds ++ renderDateTimeSep sep ++ ts ++ os).isEmpty = false := by
                    rw [Bool.eq_false_iff]; intro he
                    have h1 : (ds ++ renderDateTimeSep sep ++ ts ++ os) = "" := by simpa using he
                    have h2 := congrArg String.toList h1
                    rw [hfull_list] at h2; cases h2
                  have hnt : (ds ++ renderDateTimeSep sep ++ ts ++ os) ≠ "true" := by
                    intro he
                    have h2 := congrArg String.toList he
                    rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                  have hnf : (ds ++ renderDateTimeSep sep ++ ts ++ os) ≠ "false" := by
                    intro he
                    have h2 := congrArg String.toList he
                    rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                  simp [classifyScalarToken, hne, hnt, hnf, hdt]
                have hpv : parseValueFuel numApi (f + 1) ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList ++ rest) =
                    .ok (.offsetDateTime odt, rest) := by
                  have hfull_list : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList =
                      c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList) := by
                    simp [String.toList_append, hds_list, List.cons_append, List.append_assoc]
                  rw [hfull_list, List.cons_append]
                  rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList ++ rest)
                    hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
                  rw [← List.cons_append, ← hfull_list, htok]
                  simp [hcls, bind, Except.bind]
                have hsep_cl : ((renderDateTimeSep sep).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                  cases sep <;> decide
                have hcl : ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                  simp only [String.toList_append, List.all_append, hsep_cl, clean_no_nl_of_full _ hds_cl,
                    clean_no_nl_of_full _ hts_cl, clean_no_nl_of_full _ hos_cl, Bool.and_self]
                exact ⟨.offsetDateTime odt, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hcl, fun _ => hcl⟩
      | _ => simp [renderValueInline] at hr

private theorem skipHorizWs_cons_of_false (c : Char) (cs : List Char)
    (h : isHorizWs c = false) : skipHorizWs (c :: cs) = c :: cs := by
  simp [skipHorizWs, h]

private theorem skipHorizWs_space (cs : List Char) : skipHorizWs (' ' :: cs) = skipHorizWs cs := by
  simp [skipHorizWs, isHorizWs]

private theorem skipTriviaNewlines_cons_of_safe (c : Char) (cs : List Char)
    (hws : isHorizWs c = false) (hn : c ≠ '\n') (hc : c ≠ '#') :
    skipTriviaNewlines (c :: cs) = c :: cs := by
  unfold skipTriviaNewlines skipTriviaNewlinesAux
  split
  · rename_i heq; cases heq
  · rename_i heq; injection heq with h1; exact absurd h1 hn
  · rename_i head rest _ heq
    injection heq with h1 h2; subst h1; subst h2
    simp [hws, beq_iff_eq, hc]

private theorem parseArrayFuel_skip_space (numApi : NumParseApi) (fuel : Nat)
    (cs : List Char) (revAcc : List TomlValue) :
    parseArrayFuel numApi fuel (' ' :: cs) revAcc = parseArrayFuel numApi fuel cs revAcc := by
  cases fuel with
  | zero => rfl
  | succ f =>
    have hsp : skipTriviaNewlines (' ' :: cs) = skipTriviaNewlines cs := by
      simp [skipTriviaNewlines, skipTriviaNewlinesAux, isHorizWs]
    simp only [parseArrayFuel, hsp]

private theorem renderKey_headSafe (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) :
    ∃ c0 cs0, rk.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧
      c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '[' ∧ c0 ≠ '.' := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk; subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      cases hlist : k.toList with
      | nil =>
        have h0 : k = "" := by rw [← String.ofList_toList (s := k), hlist]
        subst h0; simp at hbare
      | cons c0 cs0 =>
        have hc0 : isBareKeyChar c0 = true :=
          List.all_eq_true.mp hbare.2 c0 (by rw [hlist]; simp)
        have hcl := isBareKeyChar_clean c0 hc0
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl
        have hnbr : c0 ≠ '[' := by
          intro heq; subst heq; cases hc0
        exact ⟨c0, cs0, rfl, hcl.1.1.1.1.1.1.1.1.2, hcl.1.1.1.1.1.1.1.1.1.2,
          hcl.1.1.1.1.2, hcl.1.1.2, hcl.1.2, hnbr, hcl.1.1.1.1.1.1.1.2⟩
    · cases hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk; subst hrk
    refine ⟨'"', (escapeBasicBody false k ++ "\"").toList, ?_, by decide⟩
    simp [String.toList_append]
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · injection hr with hrk; subst hrk
      refine ⟨'\'', (k ++ "'").toList, ?_, by decide⟩
      simp [String.toList_append]
    · cases hr

private theorem renderValueInline_headSafe (v : TomlValue) (tape : ValueTape) (rs : String)
    (hr : renderValueInline v tape = some rs) :
    ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧
      c0 ≠ '\n' ∧ c0 ≠ '\r' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ ',' := by
  have hdigit_safe : ∀ c0, isAsciiDigit c0 = true →
      isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '\r' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ ',' := by
    intro c0 hd
    have hws : isHorizWs c0 = false := by
      cases hc0_eq : isHorizWs c0 with
      | false => rfl
      | true =>
        simp [isHorizWs] at hc0_eq
        rcases hc0_eq with rfl | rfl <;> cases hd
    refine ⟨hws, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> cases hd
  cases v with
  | string s =>
    cases tape with
    | string st =>
      simp only [renderValueInline] at hr
      cases st
      · simp only [renderStringLiteral] at hr; injection hr with hrs; subst hrs
        refine ⟨'"', (escapeBasicBody false s ++ "\"").toList, ?_, by decide⟩
        simp [String.toList_append]
      · simp only [renderStringLiteral] at hr; injection hr with hrs; subst hrs
        refine ⟨'"', ('"' :: '"' :: '\n' :: (escapeBasicBody true s ++ "\"\"\"").toList), ?_, by decide⟩
        simp [String.toList_append]
      · simp only [renderStringLiteral] at hr
        split at hr
        · injection hr with hrs; subst hrs
          refine ⟨'\'', (s ++ "'").toList, ?_, by decide⟩
          simp [String.toList_append]
        · cases hr
      · simp only [renderStringLiteral] at hr
        split at hr
        · injection hr with hrs; subst hrs
          refine ⟨'\'', ('\'' :: '\'' :: '\n' :: (s ++ "'''").toList), ?_, by decide⟩
          simp [String.toList_append]
        · cases hr
    | _ => simp [renderValueInline] at hr
  | int n =>
    cases tape with
    | int olex =>
      have hlex : isValidIntLex rs n = true := by
        cases olex with
        | none =>
          simp only [renderValueInline] at hr; injection hr with hrs; subst hrs
          exact formatInt64Canonical_isValidIntLex n
        | some lex =>
          simp only [renderValueInline] at hr; split at hr
          · injection hr with hrs; subst hrs; assumption
          · cases hr
      simp only [isValidIntLex, Bool.and_eq_true] at hlex
      have hm : ∃ m : Int, NumParse.Model.parseIntModelChars rs.toList = .ok m := by
        cases hp : NumParse.Model.parseInt64Model rs with
        | error => rw [hp] at hlex; simp at hlex
        | ok parsed =>
          unfold NumParse.Model.parseInt64Model NumParse.Model.parseIntModel at hp
          cases hc : NumParse.Model.parseIntModelChars rs.toList with
          | error => rw [hc] at hp; cases hp
          | ok m => exact ⟨m, rfl⟩
      rcases hm with ⟨m, hm⟩
      obtain ⟨⟨c0, cs0, hlist, hc0, _⟩, _⟩ := parseIntModelChars_props rs.toList m hm
      refine ⟨c0, cs0, hlist, ?_⟩
      rcases hc0 with rfl | rfl | hd
      · decide
      · decide
      · exact hdigit_safe c0 hd
    | _ => simp [renderValueInline] at hr
  | float fl =>
    cases tape with
    | float olex =>
      have hlex : isValidFloatLex rs fl = true := by
        cases olex with
        | none =>
          simp only [renderValueInline] at hr
          split at hr
          · rename_i h1; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).1 h1
          · split at hr
            · rename_i h2; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.1 h2
            · split at hr
              · rename_i h3; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.1 h3
              · split at hr
                · rename_i h4; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.1 (by simpa using h4)
                · split at hr
                  · rename_i h5; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.2 (by simpa using h5)
                  · cases hr
        | some lex =>
          simp only [renderValueInline] at hr; split at hr
          · injection hr with hrs; subst hrs; assumption
          · cases hr
      simp only [isValidFloatLex, Bool.and_eq_true] at hlex
      have hm : ∃ g, NumParse.Model.parseFloatModelChars rs.toList = .ok g := by
        cases hp : NumParse.Model.parseFloatModel rs with
        | error => rw [hp] at hlex; simp at hlex
        | ok g => exact ⟨g, by simpa [NumParse.Model.parseFloatModel] using hp⟩
      rcases hm with ⟨g, hg⟩
      obtain ⟨⟨c0, cs0, hlist, hc0⟩, _, _, _, _⟩ := parseFloatModelChars_props rs.toList g hg
      refine ⟨c0, cs0, hlist, ?_⟩
      rcases hc0 with rfl | rfl | rfl | rfl | hd
      · decide
      · decide
      · decide
      · decide
      · exact hdigit_safe c0 hd
    | _ => simp [renderValueInline] at hr
  | bool b =>
    cases tape with
    | bool =>
      cases b <;> simp [renderValueInline] at hr <;> subst hr <;>
        first
        | exact ⟨'f', ['a', 'l', 's', 'e'], rfl, by decide⟩
        | exact ⟨'t', ['r', 'u', 'e'], rfl, by decide⟩
    | _ => simp [renderValueInline] at hr
  | localDate d =>
    cases tape with
    | localDate =>
      simp only [renderValueInline] at hr
      obtain ⟨hdt, _, hhd⟩ := renderDate_localDate d rs hr
      cases hlist : rs.toList with
      | nil =>
        have h0 : rs = "" := by rw [← String.ofList_toList (s := rs), hlist]
        subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
      | cons c0 cs0 =>
        exact ⟨c0, cs0, rfl, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
    | _ => simp [renderValueInline] at hr
  | localTime t =>
    cases tape with
    | localTime fd =>
      simp only [renderValueInline] at hr
      obtain ⟨hdt, _, hhd⟩ := renderTime_localTime t fd rs hr
      cases hlist : rs.toList with
      | nil =>
        have h0 : rs = "" := by rw [← String.ofList_toList (s := rs), hlist]
        subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
      | cons c0 cs0 =>
        exact ⟨c0, cs0, rfl, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
    | _ => simp [renderValueInline] at hr
  | localDateTime dt =>
    cases tape with
    | localDateTime sep fd =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hdr : renderDate dt.date with
      | none => simp [hdr] at hr
      | some ds =>
        cases htr : renderTime dt.time fd with
        | none => simp [hdr, htr] at hr
        | some ts =>
          simp only [hdr, htr, Option.some.injEq] at hr; subst hr
          obtain ⟨hdt, _, hhd⟩ := renderDate_localDate dt.date ds hdr
          cases hlist : ds.toList with
          | nil =>
            have h0 : ds = "" := by rw [← String.ofList_toList (s := ds), hlist]
            subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
          | cons c0 cs0 =>
            refine ⟨c0, cs0 ++ (renderDateTimeSep sep ++ ts).toList, ?_, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
            simp [String.toList_append, hlist, List.cons_append]
    | _ => simp [renderValueInline] at hr
  | offsetDateTime odt =>
    cases tape with
    | offsetDateTime sep oStyle fd =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hdr : renderDate odt.dateTime.date with
      | none => simp [hdr] at hr
      | some ds =>
        cases htr : renderTime odt.dateTime.time fd with
        | none => simp [hdr, htr] at hr
        | some ts =>
          cases hor : renderOffset odt.offset oStyle with
          | none => simp [hdr, htr, hor] at hr
          | some os =>
            simp only [hdr, htr, hor, Option.some.injEq] at hr; subst hr
            obtain ⟨hdt, _, hhd⟩ := renderDate_localDate odt.dateTime.date ds hdr
            cases hlist : ds.toList with
            | nil =>
              have h0 : ds = "" := by rw [← String.ofList_toList (s := ds), hlist]
              subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
            | cons c0 cs0 =>
              refine ⟨c0, cs0 ++ (renderDateTimeSep sep ++ ts ++ os).toList, ?_, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
              simp [String.toList_append, hlist, List.cons_append, List.append_assoc]
    | _ => simp [renderValueInline] at hr
  | array xs =>
    cases tape with
    | array elemTapes =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hre : renderValueInline.renderArrayElems xs.toList elemTapes with
      | none => simp [hre] at hr
      | some strs =>
        simp only [hre, Option.some.injEq] at hr; subst hr
        refine ⟨'[', (String.intercalate ", " strs ++ "]").toList, ?_, by decide⟩
        simp [String.toList_append]
    | _ => simp [renderValueInline] at hr
  | table t =>
    cases tape with
    | inlineTable entryTapes =>
      simp only [renderValueInline, bind, Option.bind] at hr
      split at hr
      · simp at hr
      · cases hre : renderValueInline.renderInlineTableEntries t.toList entryTapes with
        | none => simp [hre] at hr
        | some kvs =>
          simp only [hre, Option.some.injEq] at hr; subst hr
          refine ⟨'{', (String.intercalate ", " kvs ++ "}").toList, ?_, by decide⟩
          simp [String.toList_append]
    | _ => simp [renderValueInline] at hr

mutual
  private theorem nodeToTomlValue_valueToInlineNode (v : TomlValue) :
      nodeToTomlValue (valueToInlineNode v) = v := by
    match v with
    | .table ⟨entries⟩ =>
      have hel := entriesToTomlList_inlineListToNodes entries
      simp [valueToInlineNode, nodeToTomlValue, hel]
    | .string _ | .int _ | .float _ | .bool _
    | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ | .array _ => rfl
  termination_by sizeOf v

  private theorem entriesToTomlList_inlineListToNodes (entries : List (String × TomlValue)) :
      entriesToTomlList (inlineListToNodes entries) = entries := by
    match entries with
    | [] => rfl
    | (k, v) :: rest =>
      simp only [inlineListToNodes, entriesToTomlList]
      rw [nodeToTomlValue_valueToInlineNode v, entriesToTomlList_inlineListToNodes rest]
  termination_by sizeOf entries
end

private theorem lookupKeyList_filter_ne (k q : String) (l : List (String × TomlValue)) :
    lookupKeyList k (l.filter fun p => p.1 != k) = none ∧
    (q ≠ k → lookupKeyList q (l.filter fun p => p.1 != k) = lookupKeyList q l) := by
  induction l with
  | nil => simp [lookupKeyList]
  | cons p ps ih =>
    rcases p with ⟨pk, pv⟩
    refine ⟨?_, ?_⟩
    · by_cases hpk : pk == k
      · have hne : (pk != k) = false := by simp [bne, hpk]
        simp [List.filter, hne, ih.1]
      · have hne : (pk != k) = true := by simp [bne, hpk]
        have hkp : (k == pk) = false := by
          rw [Bool.eq_false_iff]; intro heq
          exact hpk (beq_iff_eq.mpr (beq_iff_eq.mp heq).symm)
        simp [List.filter, hne, lookupKeyList, hkp, ih.1]
    · intro hqk
      by_cases hpk : pk == k
      · have hpk' : pk = k := beq_iff_eq.mp hpk
        have hne : (pk != k) = false := by simp [bne, hpk]
        have hqp : (q == pk) = false := by
          rw [Bool.eq_false_iff]; intro heq
          exact hqk (by rw [beq_iff_eq.mp heq, hpk'])
        simp [List.filter, hne, lookupKeyList, hqp, ih.2 hqk]
      · have hne : (pk != k) = true := by simp [bne, hpk]
        simp only [List.filter, hne, lookupKeyList]
        split
        · rfl
        · exact ih.2 hqk

private theorem assocLookupNode_assocSetNode (k q : String) (n : Node) (acc : List (String × Node)) :
    assocLookupNode q (assocSetNode k n acc) = if q == k then some n else assocLookupNode q acc := by
  induction acc with
  | nil =>
    simp [assocSetNode, assocLookupNode]
  | cons p ps ih =>
    rcases p with ⟨pk, pn⟩
    simp only [assocSetNode]
    by_cases hkp : k == pk
    · have hpk : pk = k := (beq_iff_eq.mp hkp).symm
      subst hpk
      by_cases hqp : (q == pk) = true <;> simp [assocLookupNode, hqp]
    · have hqp : ∀ h : q == pk, (q == k) = false := by
        intro h
        rw [Bool.eq_false_iff]; intro hqk
        exact hkp (beq_iff_eq.mpr ((beq_iff_eq.mp hqk).symm.trans (beq_iff_eq.mp h)))
      simp only [hkp, Bool.false_eq_true, ↓reduceIte, assocLookupNode]
      by_cases hqp_b : q == pk
      · simp [hqp_b, hqp hqp_b]
      · simp [hqp_b, ih]

private theorem lookupKeyList_entriesToTomlList (q : String) (acc : List (String × Node)) :
    lookupKeyList q (entriesToTomlList acc) = (assocLookupNode q acc).map nodeToTomlValue := by
  induction acc with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨pk, pn⟩
    simp only [entriesToTomlList, lookupKeyList, assocLookupNode]
    by_cases h : (q == pk) = true <;> simp [h, ih]

private theorem lookupKeyList_mem {k : String} {v : TomlValue} {l : List (String × TomlValue)}
    (h : lookupKeyList k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p ps ih =>
    rcases p with ⟨pk, pv⟩
    simp only [lookupKeyList] at h
    split at h
    · rename_i heq
      have hkp : k = pk := beq_iff_eq.mp heq
      injection h with hv
      subst hkp; subst hv
      exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

private theorem sizeOf_lt_of_mem_array {x : TomlValue} {xs : Array TomlValue}
    (h : x ∈ xs.toList) : sizeOf x < sizeOf (TomlValue.array xs) := by
  cases xs with | mk l =>
  have hx : sizeOf x < sizeOf l := by
    have := List.sizeOf_lt_of_mem h
    omega
  have : sizeOf l < sizeOf (TomlValue.array ⟨l⟩) := by simp +arith
  omega

private theorem sizeOf_lt_of_mem_table {k : String} {v : TomlValue} {t : TomlTable}
    (h : (k, v) ∈ t.toList) : sizeOf v < sizeOf (TomlValue.table t) := by
  cases t with | mk l =>
  have hp : sizeOf (k, v) < sizeOf l := List.sizeOf_lt_of_mem h
  have hv : sizeOf v < sizeOf (k, v) := by simp +arith
  have ht : sizeOf l < sizeOf (TomlValue.table ⟨l⟩) := by simp +arith
  omega

private theorem tomlListEquiv_append_single {l1 l2 : List TomlValue} {x1 x2 : TomlValue}
    (hl : TomlListEquiv l1 l2) (hx : TomlEquiv x1 x2) :
    TomlListEquiv (l1 ++ [x1]) (l2 ++ [x2]) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [TomlListEquiv, hx]
    | cons _ _ => simp [TomlListEquiv] at hl
  | cons a xr ih =>
    cases l2 with
    | nil => simp [TomlListEquiv] at hl
    | cons b yr =>
      simp only [TomlListEquiv] at hl
      simp only [List.cons_append, TomlListEquiv]
      exact ⟨hl.1, ih hl.2⟩

private theorem renderKey_parseDottedKey_single (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.') :
    parseDottedKey (rk.toList ++ rest) = .ok ([k], skipHorizWs rest) := by
  unfold parseDottedKey
  have hlen : ∃ f, (rk.toList ++ rest).length + 1 = f + 1 := ⟨(rk.toList ++ rest).length, rfl⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf]
  unfold parseDottedKeyFuel
  rw [(renderKey_parseKeySegment k ks rk hr rest hrest).1]
  simp only [bind, Except.bind]
  rcases hsw with ⟨c2, t2, hsw_eq, hne_dot⟩
  rw [hsw_eq]
  split
  · rename_i heq; injection heq with h1 _; exact absurd h1 hne_dot
  · rfl

private theorem renderArrayElems_parseArrayFuel (numApi : NumParseApi)
    (xs : List TomlValue) (tps : List ValueTape) (strs : List String)
    (harr : renderValueInline.renderArrayElems xs tps = some strs)
    (hVal : ∀ x ∈ xs, ∀ tp rs, renderValueInline x tp = some rs →
      ∀ rest fuel, fuel ≥ rs.toList.length →
      (∀ c r, rest = c :: r →
        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
      ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
        TomlEquiv x v' ∧
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true)
    (origPrefix revAcc : List TomlValue)
    (hacc : TomlListEquiv origPrefix revAcc.reverse)
    (rest : List Char) (fuel : Nat)
    (hf : fuel ≥ (String.intercalate ", " strs ++ "]").toList.length) :
    ∃ ys, parseArrayFuel numApi fuel ((String.intercalate ", " strs ++ "]").toList ++ rest) revAcc =
        .ok (.array ys, rest) ∧
      TomlListEquiv (origPrefix ++ xs) ys.toList ∧
      ((String.intercalate ", " strs ++ "]").toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction xs generalizing tps strs origPrefix revAcc fuel with
  | nil =>
    cases tps with
    | nil =>
      simp only [renderValueInline.renderArrayElems, Option.some.injEq] at harr
      subst harr
      cases fuel with
      | zero => simp at hf
      | succ f =>
        have hst : skipTriviaNewlines (']' :: rest) = ']' :: rest :=
          skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)
        refine ⟨revAcc.reverse.toArray, ?_, ?_, by decide⟩
        · simp [String.intercalate_nil, parseArrayFuel, hst]
        · simpa using hacc
    | cons _ _ => simp [renderValueInline.renderArrayElems] at harr
  | cons x xr ih =>
    cases tps with
    | nil => simp [renderValueInline.renderArrayElems] at harr
    | cons tp tpr =>
      simp only [renderValueInline.renderArrayElems, bind, Option.bind] at harr
      cases hx : renderValueInline x tp with
      | none => simp [hx] at harr
      | some sx =>
        cases hxr : renderValueInline.renderArrayElems xr tpr with
        | none => simp [hx, hxr] at harr
        | some sr =>
          simp only [hx, hxr, Option.some.injEq] at harr
          subst harr
          obtain ⟨c0, cs0, hsx_list, hws0, hn0, _, hc0, hbr0, _, _⟩ := renderValueInline_headSafe x tp sx hx
          let tailStr := match sr with | [] => "]" | _ :: _ => ", " ++ String.intercalate ", " sr ++ "]"
          let tailRest := tailStr.toList ++ rest
          have hinterc : (String.intercalate ", " (sx :: sr) ++ "]").toList = sx.toList ++ tailStr.toList := by
            cases sr with
            | nil => simp [tailStr, String.intercalate_singleton, String.toList_append]
            | cons s2 sr2 =>
              simp [tailStr, String.intercalate_cons_cons, String.toList_append, String.append_assoc]
          have htail_delim : ∀ c r, tailRest = c :: r →
              isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false) := by
            intro c r hc
            cases hsr : sr with
            | nil =>
              have hc' : ']' :: rest = c :: r := by simpa [tailRest, tailStr, hsr] using hc
              injection hc' with hcb _
              subst hcb; exact ⟨by decide, fun h => by cases h⟩
            | cons s2 sr2 =>
              have hc' : ',' :: ' ' :: (String.intercalate ", " (s2 :: sr2) ++ "]").toList ++ rest = c :: r := by
                simpa [tailRest, tailStr, hsr, String.toList_append, List.cons_append, List.append_assoc] using hc
              injection hc' with hcb _
              subst hcb; exact ⟨by decide, fun h => by cases h⟩
          have htail_len : tailStr.toList.length ≥ 1 := by
            cases sr <;> simp [tailStr, String.toList_append] <;> omega
          have hf_pos : ∃ f, fuel = f + 1 ∧ f ≥ sx.toList.length := by
            cases fuel with
            | zero => rw [hinterc, List.length_append] at hf; omega
            | succ f =>
              refine ⟨f, rfl, ?_⟩
              rw [hinterc, List.length_append] at hf
              omega
          rcases hf_pos with ⟨f, rfl, hf_x⟩
          obtain ⟨v', hpv, heqv, hcl_x⟩ := hVal x (by simp) tp sx hx tailRest f hf_x htail_delim
          have hskip1 : skipTriviaNewlines (sx.toList ++ tailRest) = sx.toList ++ tailRest := by
            rw [hsx_list, List.cons_append]
            exact skipTriviaNewlines_cons_of_safe c0 (cs0 ++ tailRest) hws0 hn0 hc0
          have hnot_nil : sx.toList ++ tailRest ≠ [] := by
            rw [hsx_list]; simp
          have hnot_rbr : ∀ r, sx.toList ++ tailRest ≠ ']' :: r := by
            intro r heq; rw [hsx_list, List.cons_append] at heq
            injection heq with h1 _; exact hbr0 h1
          have hstep : parseArrayFuel numApi (f + 1) ((String.intercalate ", " (sx :: sr) ++ "]").toList ++ rest) revAcc =
              (match skipTriviaNewlines tailRest with
               | ',' :: afterComma => parseArrayFuel numApi f afterComma (v' :: revAcc)
               | ']' :: afterClose => .ok (.array (v' :: revAcc).reverse.toArray, afterClose)
               | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array")) := by
            rw [hinterc, List.append_assoc]
            conv => lhs; unfold parseArrayFuel
            rw [hskip1]
            split
            · rename_i heq; exact absurd heq (hnot_rbr _)
            · rename_i heq; exact absurd heq hnot_nil
            · simp only [hpv, bind, Except.bind]; rfl
          cases hsr : sr with
          | nil =>
            have hxr_nil : xr = [] := by
              cases xr with
              | nil => rfl
              | cons y yr =>
                cases tpr with
                | nil => simp [renderValueInline.renderArrayElems] at hxr
                | cons yt ytr =>
                  simp only [renderValueInline.renderArrayElems, bind, Option.bind] at hxr
                  cases hry : renderValueInline y yt with
                  | none => simp [hry] at hxr
                  | some sy =>
                    cases hrrest : renderValueInline.renderArrayElems yr ytr with
                    | none => simp [hry, hrrest] at hxr
                    | some syr => simp [hry, hrrest, hsr] at hxr
            subst hxr_nil
            have htail_eq : tailRest = ']' :: rest := by simp [tailRest, tailStr, hsr]
            have hskip2 : skipTriviaNewlines tailRest = ']' :: rest := by
              rw [htail_eq]
              exact skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)
            refine ⟨(v' :: revAcc).reverse.toArray, ?_, ?_, ?_⟩
            · rw [← hsr, hstep, hskip2]; rfl
            · simp only [List.reverse_cons]
              exact tomlListEquiv_append_single hacc heqv
            · rw [← hsr, hinterc, List.all_append]
              exact Bool.and_eq_true_iff.mpr ⟨hcl_x, by simp [tailStr, hsr]; decide⟩
          | cons s2 sr2 =>
            have htail_eq : tailRest = ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) := by
              simp [tailRest, tailStr, hsr, String.toList_append, List.cons_append, List.append_assoc]
            have hskip2 : skipTriviaNewlines tailRest = ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) := by
              rw [htail_eq]
              exact skipTriviaNewlines_cons_of_safe ',' _ (by decide) (by decide) (by decide)
            have hf_rec : f ≥ (String.intercalate ", " sr ++ "]").toList.length := by
              have hsx_len : sx.toList.length ≥ 1 := by rw [hsx_list]; simp
              rw [hinterc, List.length_append] at hf
              simp only [tailStr, hsr, String.toList_append, List.length_append] at hf ⊢
              have h2 : (", " : String).toList.length = 2 := rfl
              omega
            have hVal' : ∀ y ∈ xr, ∀ tp' rs', renderValueInline y tp' = some rs' →
                ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                (∀ c r, rest' = c :: r →
                  isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                  TomlEquiv y v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true :=
              fun y hy => hVal y (by simp [hy])
            have hxr_clean : renderValueInline.renderArrayElems xr tpr = some sr := by simpa [hsr] using hxr
            have hacc' : TomlListEquiv (origPrefix ++ [x]) (v' :: revAcc).reverse := by
              simp only [List.reverse_cons]
              exact tomlListEquiv_append_single hacc heqv
            obtain ⟨ys, hys_parse, hys_eqv, hys_cl⟩ :=
              ih tpr sr hxr_clean hVal' (origPrefix ++ [x]) (v' :: revAcc) hacc' f hf_rec
            refine ⟨ys, ?_, ?_, ?_⟩
            · rw [← hsr, hstep, hskip2]
              have hred : (match ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) with
                  | ',' :: afterComma => parseArrayFuel numApi f afterComma (v' :: revAcc)
                  | ']' :: afterClose => .ok (.array (v' :: revAcc).reverse.toArray, afterClose)
                  | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array")) =
                  parseArrayFuel numApi f (' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest)) (v' :: revAcc) := rfl
              rw [hred, parseArrayFuel_skip_space]
              exact hys_parse
            · simpa [List.append_assoc] using hys_eqv
            · rw [← hsr, hinterc, List.all_append]
              refine Bool.and_eq_true_iff.mpr ⟨hcl_x, ?_⟩
              simp only [tailStr, hsr]
              rw [String.append_assoc, String.toList_append, List.all_append]
              refine Bool.and_eq_true_iff.mpr ⟨by decide, ?_⟩
              simpa [hsr] using hys_cl

private theorem parseInlineTableFuel_step (numApi : NumParseApi) (f : Nat)
    (cs : List Char) (acc : List (String × Node))
    (k : String) (r1 r3 r5 : List Char) (v : TomlValue) (nextEntries : List (String × Node))
    (hdk : parseDottedKey (skipHorizWs cs) = .ok ([k], r1))
    (hr2 : skipHorizWs r1 = '=' :: r3)
    (hpv : parseValueFuel numApi f (skipHorizWs r3) = .ok (v, r5))
    (hins : insertDottedEntries [k] acc [k] (valueToInlineNode v) = .ok nextEntries) :
    parseInlineTableFuel numApi (f + 1) cs acc =
      (match skipHorizWs r5 with
       | ',' :: afterComma =>
         match skipHorizWs afterComma with
         | '}' :: _ => .error (mkErr .parseError "trailing comma is not allowed in inline table")
         | nextCs => parseInlineTableFuel numApi f nextCs nextEntries
       | '}' :: afterClose => .ok (.table (entriesToTomlList nextEntries).toArray, afterClose)
       | _ => .error (mkErr .parseError "expected ',' or '}' in inline table")) := by
  conv =>
    lhs
    unfold parseInlineTableFuel
    simp only [hdk, bind, Except.bind, hr2, hpv, hins]
  rfl

private theorem renderInlineTableEntries_parseInlineTableFuel (numApi : NumParseApi)
    (origEntries rem : List (String × TomlValue))
    (entryTapes : List (String × KeyStyle × ValueTape)) (kvs : List String)
    (hrem_sub : ∀ q v, lookupKeyList q rem = some v → lookupKeyList q origEntries = some v)
    (htab : renderValueInline.renderInlineTableEntries rem entryTapes = some kvs)
    (hne : entryTapes ≠ [])
    (hVal : ∀ q v, lookupKeyList q origEntries = some v → ∀ tp rs, renderValueInline v tp = some rs →
      ∀ rest fuel, fuel ≥ rs.toList.length →
      (∀ c r, rest = c :: r →
        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
      ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
        TomlEquiv v v' ∧
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true)
    (acc : List (String × Node))
    (h1 : ∀ q, lookupKeyList q origEntries = none → assocLookupNode q acc = none)
    (h2 : ∀ q v, lookupKeyList q rem = some v → assocLookupNode q acc = none)
    (h3 : ∀ q v1, lookupKeyList q origEntries = some v1 → lookupKeyList q rem = none →
      ∃ v2, lookupKeyList q (entriesToTomlList acc) = some v2 ∧ TomlEquiv v1 v2)
    (rest : List Char) (fuel : Nat)
    (hf : fuel ≥ (String.intercalate ", " kvs ++ "}").toList.length) :
    ∃ resT, parseInlineTableFuel numApi fuel ((String.intercalate ", " kvs ++ "}").toList ++ rest) acc =
        .ok (.table resT, rest) ∧
      TomlTableEquivList origEntries resT.toList ∧
      ((String.intercalate ", " kvs ++ "}").toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction entryTapes generalizing rem kvs acc fuel with
  | nil => exact absurd rfl hne
  | cons entry restTapes ih =>
    rcases entry with ⟨k, ks, vt⟩
    simp only [renderValueInline.renderInlineTableEntries] at htab
    cases hlk : lookupKeyList k rem with
    | none => simp [hlk] at htab
    | some v =>
      simp only [hlk, bind, Option.bind] at htab
      cases hrk : renderKey k ks with
      | none => simp [hrk] at htab
      | some rk =>
        cases hrv : renderValueInline v vt with
        | none => simp [hrk, hrv] at htab
        | some rv =>
          cases htail : renderValueInline.renderInlineTableEntries (rem.filter fun p => p.1 != k) restTapes with
          | none => simp [hrk, hrv, htail] at htab
          | some tailKvs =>
            simp only [hrk, hrv, htail, Option.some.injEq] at htab
            subst htab
            let rem' := rem.filter (fun p => p.1 != k)
            change renderValueInline.renderInlineTableEntries rem' restTapes = some tailKvs at htail
            obtain ⟨ck0, csk0, hrk_list, hkws0, _, _, _, _, _, _⟩ := renderKey_headSafe k ks rk hrk
            obtain ⟨cv0, csv0, hrv_list, hvws0, _, _, _, _, _, _⟩ := renderValueInline_headSafe v vt rv hrv
            let tailStr := match tailKvs with | [] => "}" | _ :: _ => ", " ++ String.intercalate ", " tailKvs ++ "}"
            let afterRv := tailStr.toList ++ rest
            have hinterc : (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ tailStr.toList)) := by
              cases tailKvs with
              | nil => simp [tailStr, String.intercalate_singleton, String.toList_append, List.append_assoc]
              | cons kv2 kvr2 =>
                simp [tailStr, String.intercalate_cons_cons, String.toList_append, List.append_assoc]
            have hinterc_rest : (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              rw [hinterc]
              simp only [afterRv, List.append_assoc, List.cons_append]
            have hafter_delim : ∀ c r, afterRv = c :: r →
                isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false) := by
              intro c r hc
              cases htk : tailKvs with
              | nil =>
                simp only [afterRv, tailStr, htk] at hc
                injection hc with hcb _
                subst hcb; exact ⟨by decide, fun h => by cases h⟩
              | cons kv2 kvr2 =>
                have hc_list : ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) = c :: r := by
                  simpa [afterRv, tailStr, htk, String.toList_append, List.cons_append, List.append_assoc] using hc
                injection hc_list with hcb _
                subst hcb; exact ⟨by decide, fun h => by cases h⟩
            have hf_pos : ∃ f, fuel = f + 1 ∧ f ≥ rv.toList.length := by
              cases fuel with
              | zero =>
                rw [hinterc] at hf
                simp at hf
              | succ f =>
                refine ⟨f, rfl, ?_⟩
                rw [hinterc, List.length_append] at hf
                simp only [List.length_cons, List.length_append] at hf
                omega
            rcases hf_pos with ⟨f, rfl, hf_v⟩
            have hv_orig : lookupKeyList k origEntries = some v := hrem_sub k v hlk
            obtain ⟨v', hpv, heqv, hcl_v⟩ := hVal k v hv_orig vt rv hrv afterRv f hf_v hafter_delim
            have hcl_k := (renderKey_parseKeySegment k ks rk hrk (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) (by
              intro c tail h; injection h with hc _; subst hc; decide)).2
            have hcl_k' : (rk.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl_k ⊢
              intro c hc
              exact ⟨(hcl_k c hc).1.1, (hcl_k c hc).1.2⟩
            have hcs1 : skipHorizWs ((String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest) =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              rw [hinterc_rest, hrk_list, List.cons_append]
              exact skipHorizWs_cons_of_false ck0 _ hkws0
            have hdk : parseDottedKey (rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))) =
                .ok ([k], '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              have hdk' := renderKey_parseDottedKey_single k ks rk hrk
                (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))
                (fun c tail h => by injection h with hc _; subst hc; decide)
                ⟨'=', ' ' :: (rv.toList ++ afterRv), by simp [skipHorizWs, isHorizWs], by decide⟩
              simpa [skipHorizWs, isHorizWs] using hdk'
            have hr2 : skipHorizWs ('=' :: ' ' :: (rv.toList ++ afterRv)) = '=' :: ' ' :: (rv.toList ++ afterRv) :=
              skipHorizWs_cons_of_false '=' _ (by decide)
            have hr4 : skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv := by
              rw [skipHorizWs_space, hrv_list]
              exact skipHorizWs_cons_of_false cv0 _ hvws0
            have hins : insertDottedEntries [k] acc [k] (valueToInlineNode v') =
                .ok (assocSetNode k (valueToInlineNode v') acc) := by
              simp [insertDottedEntries, h2 k v hlk]
            have hr6 : skipHorizWs afterRv = afterRv := by
              cases htk : tailKvs <;> simp only [afterRv, tailStr, htk, String.toList_append]
              · exact skipHorizWs_cons_of_false '}' _ (by decide)
              · exact skipHorizWs_cons_of_false ',' _ (by decide)
            have h1' : ∀ q, lookupKeyList q origEntries = none →
                assocLookupNode q (assocSetNode k (valueToInlineNode v') acc) = none := by
              intro q hq
              rw [assocLookupNode_assocSetNode]
              by_cases hqk : q == k
              · have : q = k := beq_iff_eq.mp hqk
                subst this; rw [hv_orig] at hq; cases hq
              · simp [hqk, h1 q hq]
            have h2' : ∀ q w, lookupKeyList q rem' = some w →
                assocLookupNode q (assocSetNode k (valueToInlineNode v') acc) = none := by
              intro q w hqw
              have hne_k : q ≠ k := by
                intro heq; subst heq
                rw [(lookupKeyList_filter_ne q q rem).1] at hqw; cases hqw
              have hqw_rem : lookupKeyList q rem = some w := by
                rwa [(lookupKeyList_filter_ne k q rem).2 hne_k] at hqw
              rw [assocLookupNode_assocSetNode]
              have hqb : (q == k) = false := beq_false_of_ne hne_k
              simp [hqb, h2 q w hqw_rem]
            have h3' : ∀ q v1, lookupKeyList q origEntries = some v1 → lookupKeyList q rem' = none →
                ∃ v2, lookupKeyList q (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)) = some v2 ∧
                  TomlEquiv v1 v2 := by
              intro q v1 hqo hqr
              by_cases hqk : q = k
              · subst hqk
                have hv1_eq : v1 = v := by
                  rw [hv_orig] at hqo
                  injection hqo with hveq
                  exact hveq.symm
                subst hv1_eq
                refine ⟨v', ?_, heqv⟩
                rw [lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode]
                simp [nodeToTomlValue_valueToInlineNode]
              · have hqr_rem : lookupKeyList q rem = none := by
                  rwa [(lookupKeyList_filter_ne k q rem).2 hqk] at hqr
                obtain ⟨v2, hv2, heqv2⟩ := h3 q v1 hqo hqr_rem
                refine ⟨v2, ?_, heqv2⟩
                rw [lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode]
                have hqb : (q == k) = false := beq_false_of_ne hqk
                simp only [hqb, Bool.false_eq_true, ↓reduceIte]
                rwa [lookupKeyList_entriesToTomlList] at hv2
            cases hrestT : restTapes with
            | nil =>
              have hrem'_nil : rem' = [] := by
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                split at htail
                · rename_i hempty; exact List.isEmpty_iff.mp hempty
                · cases htail
              have htailKvs_nil : tailKvs = [] := by
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                split at htail
                · injection htail with h; exact h.symm
                · cases htail
              have hafter_eq : afterRv = '}' :: rest := by simp [afterRv, tailStr, htailKvs_nil]
              have hteq : TomlTableEquivList origEntries (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)) := by
                unfold TomlTableEquivList
                refine ⟨?_, ?_⟩
                · intro q hq
                  rw [lookupKeyList_entriesToTomlList, h1' q hq]; rfl
                · intro q v1 hq
                  have hqr : lookupKeyList q rem' = none := by simp [hrem'_nil, lookupKeyList]
                  exact h3' q v1 hq hqr
              refine ⟨(entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)).toArray, ?_, ?_, ?_⟩
              · rw [parseInlineTableFuel_step numApi f _ acc k _ _ _ v' _ (by rw [hcs1]; exact hdk) hr2
                    (by rw [show skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv from hr4]; exact hpv) hins,
                  hr6, hafter_eq]
                rfl
              · simpa using hteq
              · rw [hinterc, List.all_append]
                refine Bool.and_eq_true_iff.mpr ⟨hcl_k', ?_⟩
                simp only [List.all_cons, Bool.and_eq_true, List.all_append, tailStr, htailKvs_nil]
                exact ⟨by decide, by decide, by decide, hcl_v, by decide⟩
            | cons e2 er2 =>
              have htailKvs_ne : tailKvs ≠ [] := by
                intro hnil; subst hnil
                rcases e2 with ⟨k2, ks2, vt2⟩
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                cases hlk2 : lookupKeyList k2 rem' with
                | none => simp [hlk2] at htail
                | some v2 =>
                  simp only [hlk2, bind, Option.bind] at htail
                  cases hrk2 : renderKey k2 ks2 with
                  | none => simp [hrk2] at htail
                  | some rk2 =>
                    cases hrv2 : renderValueInline v2 vt2 with
                    | none => simp [hrk2, hrv2] at htail
                    | some rv2 =>
                      cases htl2 : renderValueInline.renderInlineTableEntries (rem'.filter fun p => p.1 != k2) er2 <;>
                        simp [hrk2, hrv2, htl2] at htail
              cases htk_eq : tailKvs with
              | nil => exact absurd htk_eq htailKvs_ne
              | cons kv2 kvr2 =>
                have htail' : renderValueInline.renderInlineTableEntries rem' restTapes = some (kv2 :: kvr2) := by
                  simpa [htk_eq] using htail
                have hk2_head : ∃ c_hd cs_hd, (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList = c_hd :: cs_hd ∧
                    isHorizWs c_hd = false ∧ c_hd ≠ '}' := by
                  rcases e2 with ⟨k2, ks2, vt2⟩
                  simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail'
                  cases hlk2 : lookupKeyList k2 rem' with
                  | none => simp [hlk2] at htail'
                  | some v2 =>
                    simp only [hlk2, bind, Option.bind] at htail'
                    cases hrk2 : renderKey k2 ks2 with
                    | none => simp [hrk2] at htail'
                    | some rk2 =>
                      cases hrv2 : renderValueInline v2 vt2 with
                      | none => simp [hrk2, hrv2] at htail'
                      | some rv2 =>
                        cases htl2 : renderValueInline.renderInlineTableEntries (rem'.filter fun p => p.1 != k2) er2 with
                        | none => simp [hrk2, hrv2, htl2] at htail'
                        | some tail2 =>
                          simp only [hrk2, hrv2, htl2, Option.some.injEq] at htail'
                          have hkv2 : kv2 = rk2 ++ " = " ++ rv2 := by
                            injection htail' with h1 _
                            exact h1.symm
                          obtain ⟨ck2, csk2, hrk2_list, hkws2, _, _, _, hbr2, _, _⟩ := renderKey_headSafe k2 ks2 rk2 hrk2
                          cases kvr2 with
                          | nil =>
                            refine ⟨ck2, csk2 ++ (" = " ++ rv2 ++ "}").toList, ?_, hkws2, hbr2⟩
                            simp [hkv2, String.intercalate_singleton, String.toList_append, hrk2_list, List.cons_append, List.append_assoc]
                          | cons kv3 kvr3 =>
                            refine ⟨ck2, csk2 ++ (" = " ++ rv2 ++ ", " ++ String.intercalate ", " (kv3 :: kvr3) ++ "}").toList, ?_, hkws2, hbr2⟩
                            simp [hkv2, String.intercalate_cons_cons, String.toList_append, hrk2_list, List.cons_append, List.append_assoc]
                rcases hk2_head with ⟨c_hd, cs_hd, hhd_list, hhd_ws, hhd_br⟩
                have hafter_eq : afterRv = ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) := by
                  simp [afterRv, tailStr, htk_eq, String.toList_append, List.cons_append, List.append_assoc]
                have hskip_ac : skipHorizWs (' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest)) =
                    (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest := by
                  rw [skipHorizWs_space, hhd_list, List.cons_append]
                  exact skipHorizWs_cons_of_false c_hd _ hhd_ws
                have hrem'_sub : ∀ q w, lookupKeyList q rem' = some w → lookupKeyList q origEntries = some w := by
                  intro q w hqw
                  have hne_k : q ≠ k := by
                    intro heq; subst heq
                    rw [(lookupKeyList_filter_ne q q rem).1] at hqw; cases hqw
                  exact hrem_sub q w (by rwa [(lookupKeyList_filter_ne k q rem).2 hne_k] at hqw)
                have hf_rec : f ≥ (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList.length := by
                  rw [hinterc, List.length_append] at hf
                  simp only [tailStr, htk_eq, String.toList_append, List.length_cons, List.length_append] at hf ⊢
                  have hrk_len : rk.toList.length ≥ 1 := by rw [hrk_list]; simp
                  have hrv_len : rv.toList.length ≥ 1 := by rw [hrv_list]; simp
                  have h2 : (", " : String).toList.length = 2 := rfl
                  omega
                have hne' : restTapes ≠ [] := by rw [hrestT]; simp
                obtain ⟨resT, hres_parse, hres_eqv, hres_cl⟩ :=
                  ih rem' (kv2 :: kvr2) hrem'_sub htail' hne' (assocSetNode k (valueToInlineNode v') acc)
                    h1' h2' h3' f hf_rec
                refine ⟨resT, ?_, hres_eqv, ?_⟩
                · rw [← htk_eq, parseInlineTableFuel_step numApi f _ acc k _ _ _ v' _ (by rw [hcs1]; exact hdk) hr2
                      (by rw [show skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv from hr4]; exact hpv) hins,
                    hr6, hafter_eq]
                  have hred : (match ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) with
                      | ',' :: afterComma =>
                        match skipHorizWs afterComma with
                        | '}' :: _ => Except.error (mkErr .parseError "trailing comma is not allowed in inline table")
                        | nextCs => parseInlineTableFuel numApi f nextCs (assocSetNode k (valueToInlineNode v') acc)
                      | '}' :: afterClose => Except.ok (.table (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)).toArray, afterClose)
                      | _ => Except.error (mkErr .parseError "expected ',' or '}' in inline table")) =
                      (match skipHorizWs (' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest)) with
                       | '}' :: _ => Except.error (mkErr .parseError "trailing comma is not allowed in inline table")
                       | nextCs => parseInlineTableFuel numApi f nextCs (assocSetNode k (valueToInlineNode v') acc)) := rfl
                  rw [hred, hskip_ac, hhd_list, List.cons_append]
                  split
                  · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
                  · rw [← List.cons_append, ← hhd_list]
                    exact hres_parse
                · rw [← htk_eq, hinterc, List.all_append]
                  refine Bool.and_eq_true_iff.mpr ⟨hcl_k', ?_⟩
                  simp only [List.all_cons, Bool.and_eq_true, List.all_append]
                  refine ⟨by decide, by decide, by decide, hcl_v, ?_⟩
                  simp only [tailStr, htk_eq]
                  rw [String.append_assoc, String.toList_append, List.all_append]
                  refine Bool.and_eq_true_iff.mpr ⟨by decide, ?_⟩
                  exact hres_cl

private theorem renderValueInline_parseValueFuel (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (v : TomlValue) (tape : ValueTape) (rs : String) (hr : renderValueInline v tape = some rs)
    (rest : List Char) (fuel : Nat) (hf : fuel ≥ rs.toList.length)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
      TomlEquiv v v' ∧
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction n0 : sizeOf v using Nat.strongRecOn generalizing v tape rs rest fuel with
  | ind len ih =>
    cases v with
    | array xs =>
      cases tape with
      | array elemTapes =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hre : renderValueInline.renderArrayElems xs.toList elemTapes with
        | none => simp [hre] at hr
        | some strs =>
          simp only [hre, Option.some.injEq] at hr; subst hr
          have hrs_list : ("[" ++ String.intercalate ", " strs ++ "]").toList =
              '[' :: ((String.intercalate ", " strs ++ "]").toList) := by
            simp [String.toList_append]
          cases fuel with
          | zero => simp [hrs_list] at hf
          | succ f =>
            have hf_arr : f ≥ (String.intercalate ", " strs ++ "]").toList.length := by
              rw [hrs_list, List.length_cons] at hf; omega
            have hVal : ∀ x ∈ xs.toList, ∀ tp rs', renderValueInline x tp = some rs' →
                ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                (∀ c r, rest' = c :: r →
                  isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                  TomlEquiv x v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              intro x hx tp rs' hrx rest' fuel' hfx hrest'
              have hlt : sizeOf x < len := by
                rw [← n0]; exact sizeOf_lt_of_mem_array hx
              exact ih (sizeOf x) hlt x tp rs' hrx rest' fuel' hfx hrest' rfl
            obtain ⟨ys, hys_parse, hys_eqv, hys_cl⟩ :=
              renderArrayElems_parseArrayFuel numApi xs.toList elemTapes strs hre hVal [] []
                (by simp [TomlListEquiv]) rest f hf_arr
            refine ⟨.array ys, ?_, ?_, ?_⟩
            · rw [hrs_list, List.cons_append]
              conv => lhs; unfold parseValueFuel
              exact hys_parse
            · simpa [TomlEquiv] using hys_eqv
            · rw [hrs_list, List.all_cons]
              exact Bool.and_eq_true_iff.mpr ⟨by decide, hys_cl⟩
      | _ => simp [renderValueInline] at hr
    | table t =>
      cases tape with
      | inlineTable entryTapes =>
        simp only [renderValueInline, bind, Option.bind] at hr
        split at hr
        · simp at hr
        · rename_i hnd
          cases hre : renderValueInline.renderInlineTableEntries t.toList entryTapes with
          | none => simp [hre] at hr
          | some kvs =>
            simp only [hre, Option.some.injEq] at hr; subst hr
            have hrs_list : ("{" ++ String.intercalate ", " kvs ++ "}").toList =
                '{' :: ((String.intercalate ", " kvs ++ "}").toList) := by
              simp [String.toList_append]
            cases fuel with
            | zero => simp [hrs_list] at hf
            | succ f =>
              cases entryTapes with
              | nil =>
                have ht_empty : t.toList = [] := by
                  simp only [renderValueInline.renderInlineTableEntries] at hre
                  split at hre
                  · rename_i hempty; exact List.isEmpty_iff.mp hempty
                  · cases hre
                have hkvs_nil : kvs = [] := by
                  simp only [renderValueInline.renderInlineTableEntries, ht_empty] at hre
                  simpa using hre.symm
                have hparse : parseValueFuel numApi (f + 1) (("{" ++ String.intercalate ", " kvs ++ "}").toList ++ rest) =
                    .ok (.table #[], rest) := by
                  simp [hkvs_nil, String.intercalate_nil, parseValueFuel, skipHorizWs_cons_of_false '}' rest (by decide)]
                have heqv : TomlEquiv (.table t) (.table #[]) := by
                  simp [TomlEquiv, TomlTableEquivList, ht_empty, lookupKeyList]
                refine ⟨.table #[], hparse, heqv, by simp [hkvs_nil, String.intercalate_nil]; decide⟩
              | cons e0 er0 =>
                have hkvs_ne : kvs ≠ [] := by
                  intro hnil; subst hnil
                  rcases e0 with ⟨k0, ks0, vt0⟩
                  simp only [renderValueInline.renderInlineTableEntries] at hre
                  cases hlk0 : lookupKeyList k0 t.toList with
                  | none => simp [hlk0] at hre
                  | some v0 =>
                    simp only [hlk0, bind, Option.bind] at hre
                    cases hrk0 : renderKey k0 ks0 with
                    | none => simp [hrk0] at hre
                    | some rk0 =>
                      cases hrv0 : renderValueInline v0 vt0 with
                      | none => simp [hrk0, hrv0] at hre
                      | some rv0 =>
                        cases htl0 : renderValueInline.renderInlineTableEntries (t.toList.filter fun p => p.1 != k0) er0 <;>
                          simp [hrk0, hrv0, htl0] at hre
                cases hkvs_eq : kvs with
                | nil => exact absurd hkvs_eq hkvs_ne
                | cons kv0 kvr0 =>
                  have hre' : renderValueInline.renderInlineTableEntries t.toList (e0 :: er0) = some (kv0 :: kvr0) := by
                    simpa [hkvs_eq] using hre
                  have hhd : ∃ c_hd cs_hd, (String.intercalate ", " (kv0 :: kvr0) ++ "}").toList = c_hd :: cs_hd ∧
                      isHorizWs c_hd = false ∧ c_hd ≠ '}' := by
                    rcases e0 with ⟨k0, ks0, vt0⟩
                    simp only [renderValueInline.renderInlineTableEntries] at hre'
                    cases hlk0 : lookupKeyList k0 t.toList with
                    | none => simp [hlk0] at hre'
                    | some v0 =>
                      simp only [hlk0, bind, Option.bind] at hre'
                      cases hrk0 : renderKey k0 ks0 with
                      | none => simp [hrk0] at hre'
                      | some rk0 =>
                        cases hrv0 : renderValueInline v0 vt0 with
                        | none => simp [hrk0, hrv0] at hre'
                        | some rv0 =>
                          cases htl0 : renderValueInline.renderInlineTableEntries (t.toList.filter fun p => p.1 != k0) er0 with
                          | none => simp [hrk0, hrv0, htl0] at hre'
                          | some tail0 =>
                            simp only [hrk0, hrv0, htl0, Option.some.injEq] at hre'
                            have hkv0 : kv0 = rk0 ++ " = " ++ rv0 := by
                              injection hre' with h1 _
                              exact h1.symm
                            obtain ⟨ck0, csk0, hrk0_list, hkws0, _, _, _, hbr0, _, _⟩ := renderKey_headSafe k0 ks0 rk0 hrk0
                            cases kvr0 with
                            | nil =>
                              refine ⟨ck0, csk0 ++ (" = " ++ rv0 ++ "}").toList, ?_, hkws0, hbr0⟩
                              simp [hkv0, String.intercalate_singleton, String.toList_append, hrk0_list, List.cons_append, List.append_assoc]
                            | cons kv1 kvr1 =>
                              refine ⟨ck0, csk0 ++ (" = " ++ rv0 ++ ", " ++ String.intercalate ", " (kv1 :: kvr1) ++ "}").toList, ?_, hkws0, hbr0⟩
                              simp [hkv0, String.intercalate_cons_cons, String.toList_append, hrk0_list, List.cons_append, List.append_assoc]
                  rcases hhd with ⟨c_hd, cs_hd, hhd_list, hhd_ws, hhd_br⟩
                  have hf_tab : f ≥ (String.intercalate ", " (kv0 :: kvr0) ++ "}").toList.length := by
                    rw [hrs_list, hkvs_eq, List.length_cons] at hf; omega
                  have hVal : ∀ q v, lookupKeyList q t.toList = some v → ∀ tp rs', renderValueInline v tp = some rs' →
                      ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                      (∀ c r, rest' = c :: r →
                        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                      ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                        TomlEquiv v v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                    intro q v hqv tp rs' hrv' rest' fuel' hfv' hrest'
                    have hlt : sizeOf v < len := by
                      rw [← n0]; exact sizeOf_lt_of_mem_table (lookupKeyList_mem hqv)
                    exact ih (sizeOf v) hlt v tp rs' hrv' rest' fuel' hfv' hrest' rfl
                  obtain ⟨resT, hres_parse, hres_eqv, hres_cl⟩ :=
                    renderInlineTableEntries_parseInlineTableFuel numApi t.toList t.toList (e0 :: er0) (kv0 :: kvr0)
                      (fun _ _ h => h) hre' (by simp) hVal []
                      (fun _ _ => rfl) (fun _ _ _ => rfl)
                      (fun q v1 h1 h2 => by rw [h1] at h2; cases h2)
                      rest f hf_tab
                  refine ⟨.table resT, ?_, ?_, ?_⟩
                  · rw [← hkvs_eq, hrs_list, hkvs_eq, List.cons_append]
                    have hpv_step : parseValueFuel numApi (f + 1) ('{' :: ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest)) =
                        (match skipHorizWs ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest) with
                         | '}' :: afterClose => .ok (.table #[], afterClose)
                         | other => parseInlineTableFuel numApi f other []) := rfl
                    rw [hpv_step, hhd_list, List.cons_append, skipHorizWs_cons_of_false c_hd _ hhd_ws]
                    split
                    · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
                    · rw [← List.cons_append, ← hhd_list]
                      exact hres_parse
                  · simpa [TomlEquiv, TomlTableEquiv] using hres_eqv
                  · rw [← hkvs_eq, hrs_list, hkvs_eq, List.all_cons]
                    exact Bool.and_eq_true_iff.mpr ⟨by decide, hres_cl⟩
      | _ => simp [renderValueInline] at hr
    | string _ | int _ | float _ | bool _
    | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      have hf_ge1 : fuel ≥ 1 := by
        obtain ⟨_, _, hlist, _⟩ := renderValueInline_headSafe _ tape rs hr
        rw [hlist, List.length_cons] at hf
        omega
      obtain ⟨v', hpv, heqv, hcl, _⟩ :=
        renderValueInline_scalar_parseValueFuel numApi hInt hFloat _ tape rs hr rest fuel hf_ge1 (by trivial) hrest
      exact ⟨v', hpv, heqv, hcl⟩

private def joinLines : List String → String
  | [] => ""
  | l :: ls => l ++ "\n" ++ joinLines ls

private theorem joinLines_append (a b : List String) :
    joinLines (a ++ b) = joinLines a ++ joinLines b := by
  induction a with
  | nil => simp [joinLines]
  | cons l ls ih => simp [joinLines, ih, String.append_assoc]

private theorem intercalate_nl_append_nl (lines : List String) (hne : lines ≠ []) :
    String.intercalate "\n" lines ++ "\n" = joinLines lines := by
  induction lines with
  | nil => exact absurd rfl hne
  | cons l ls ih =>
    cases ls with
    | nil => simp [String.intercalate_singleton, joinLines]
    | cons l2 ls2 =>
      rw [String.intercalate_cons_cons, joinLines, String.append_assoc]
      congr 1
      exact ih (by simp)

private theorem joinLines_all_clean (lines : List String)
    (h : ∀ l ∈ lines, (l.toList.all fun c => !isDisallowedControl c && c != '\r') = true) :
    ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction lines with
  | nil => rfl
  | cons l ls ih =>
    simp [joinLines, List.all_append, h l (by simp), ih (fun x hx => h x (by simp [hx])),
      (by decide : isDisallowedControl '\n' = false)]

private theorem joinLines_singleton_clean (s : String)
    (h : (s.toList.all fun c => !isDisallowedControl c && c != '\r') = true) :
    ((joinLines [s]).toList.all fun c => !isDisallowedControl c && c != '\r') = true :=
  joinLines_all_clean [s] (fun _ hl => by simp only [List.mem_singleton] at hl; subst hl; exact h)

private theorem skipCommentBody_clean (cs rest : List Char)
    (h : (cs.all fun c => c != '\n') = true) :
    skipCommentBody (cs ++ '\n' :: rest) = '\n' :: rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold skipCommentBody
    simp [h.1]
    exact ih h.2

private theorem skipTriviaNewlinesAux_true_clean (cs rest : List Char)
    (h : (cs.all fun c => c != '\n') = true) :
    skipTriviaNewlinesAux true (cs ++ '\n' :: rest) = skipTriviaNewlines rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold skipTriviaNewlinesAux
    simp [h.1]
    exact ih h.2

private theorem skipTriviaNewlines_comment_line (c : String) (rest : List Char)
    (hc : isSingleLineClean c = true) :
    skipTriviaNewlines (("#" ++ c ++ "\n").toList ++ rest) = skipTriviaNewlines rest := by
  have hno : (c.toList.all fun ch => ch != '\n') = true := by
    simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc ⊢
    intro ch hch
    exact (hc ch hch).1.2
  have hlist : ("#" ++ c ++ "\n").toList ++ rest = '#' :: (c.toList ++ '\n' :: rest) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  rw [hlist]
  exact skipTriviaNewlinesAux_true_clean c.toList rest hno

private theorem renderCommentSuffix_props (comment : Option String) (rc : String)
    (h : renderCommentSuffix comment = some rc) :
    (rc.toList.all fun ch => !isDisallowedControl ch && ch != '\r' && ch != '\n') = true ∧
    (∀ rest : List Char, consumeStatementEnd (rc.toList ++ '\n' :: rest) = .ok rest) ∧
    (∀ rest : List Char, ∀ c r, rc.toList ++ '\n' :: rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) := by
  cases comment with
  | none =>
    simp only [renderCommentSuffix, Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun rest => ?_, fun rest c r hc => ?_⟩
    · simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs]
    · injection hc with hc' _; subst hc'; exact ⟨by decide, fun h => by cases h⟩
  | some s =>
    simp only [renderCommentSuffix] at h
    split at h
    · rename_i hclean
      injection h with hrc; subst hrc
      have hcl : (s.toList.all fun ch => !isDisallowedControl ch && ch != '\r' && ch != '\n') = true := by
        simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hclean ⊢
        intro ch hch
        exact ⟨⟨(hclean ch hch).1.1, (hclean ch hch).2⟩, (hclean ch hch).1.2⟩
      have hno_nl : (s.toList.all fun ch => ch != '\n') = true := by
        simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcl ⊢
        intro ch hch; exact (hcl ch hch).2
      refine ⟨?_, fun rest => ?_, fun rest c r hc => ?_⟩
      · simp [String.toList_append, hcl, (by decide : isDisallowedControl ' ' = false),
          (by decide : isDisallowedControl '#' = false)]
      · have hlist : (" #" ++ s).toList ++ '\n' :: rest = ' ' :: '#' :: (s.toList ++ '\n' :: rest) := by
          simp [String.toList_append, List.cons_append]
        rw [hlist]
        simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs, skipCommentBody_clean s.toList rest hno_nl]
      · have hlist : (" #" ++ s).toList ++ '\n' :: rest = ' ' :: '#' :: (s.toList ++ '\n' :: rest) := by
          simp [String.toList_append, List.cons_append]
        rw [hlist] at hc
        injection hc with hc1 hr1
        subst hc1
        refine ⟨by decide, fun _ c2 r2 hr2 => ?_⟩
        rw [← hr1] at hr2
        injection hr2 with hc2 _
        subst hc2; decide
    · cases h

private theorem joinRenderedPath_props (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2) :
    (∃ c0 cs0, (joinRenderedPath (pairs.map Prod.snd)).toList = c0 :: cs0 ∧
      isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '.') ∧
    ((joinRenderedPath (pairs.map Prod.snd)).toList.all fun c =>
      !isDisallowedControl c && c != '\r' && c != '\n') = true ∧
    pairs.length ≤ (joinRenderedPath (pairs.map Prod.snd)).toList.length := by
  induction pairs with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    rcases p with ⟨k, rk⟩
    obtain ⟨ks, hrk⟩ := hkeys (k, rk) (by simp)
    obtain ⟨c0, cs0, hrk_list, hws0, hn0, hc0, hbr0, hrb0, hl0, hdot0⟩ := renderKey_headSafe k ks rk hrk
    have hrk_clean := (renderKey_parseKeySegment k ks rk hrk [' '] (fun c _ h => by
      injection h with h1 _; subst h1; decide)).2
    have hrk_len : rk.toList.length ≥ 1 := by rw [hrk_list]; simp
    cases ps with
    | nil =>
      refine ⟨⟨c0, cs0, ?_, hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩, ?_, ?_⟩
      · simpa [joinRenderedPath] using hrk_list
      · simpa [joinRenderedPath] using hrk_clean
      · simpa [joinRenderedPath] using hrk_len
    | cons p2 ps2 =>
      obtain ⟨_, hclean_ps, hlen_ps⟩ := ih (by simp) (fun q hq => hkeys q (by simp [hq]))
      have hjoin : joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd) =
          rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd) := rfl
      refine ⟨⟨c0, cs0 ++ ('.' :: (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList), ?_,
          hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩, ?_, ?_⟩
      · rw [hjoin, String.toList_append, String.toList_append, hrk_list]
        simp [List.cons_append, List.append_assoc]
      · rw [hjoin, String.toList_append, String.toList_append, List.all_append, List.all_append]
        simpa [hrk_clean, (by decide : isDisallowedControl '.' = false)] using hclean_ps
      · rw [hjoin, String.toList_append, String.toList_append, List.length_append, List.length_append]
        simp only [List.length_cons] at hlen_ps ⊢
        omega

private theorem parseDottedKeyFuel_joinRenderedPath
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.')
    (fuel : Nat) (hf : fuel ≥ pairs.length) :
    parseDottedKeyFuel fuel ((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest) =
      .ok (pairs.map Prod.fst, skipHorizWs rest) := by
  induction pairs generalizing rest fuel with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    rcases p with ⟨k, rk⟩
    obtain ⟨ks, hrk⟩ := hkeys (k, rk) (by simp)
    cases fuel with
    | zero => simp at hf
    | succ f =>
      cases ps with
      | nil =>
        simp only [List.map_cons, List.map_nil, joinRenderedPath]
        unfold parseDottedKeyFuel
        rw [(renderKey_parseKeySegment k ks rk hrk rest hrest).1]
        simp only [bind, Except.bind]
        rcases hsw with ⟨c2, t2, hsw_eq, hne_dot⟩
        rw [hsw_eq]
        split
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_dot
        · rfl
      | cons p2 ps2 =>
        have hps_ne : p2 :: ps2 ≠ [] := by simp
        have hps_keys : ∀ q ∈ p2 :: ps2, ∃ ks, renderKey q.1 ks = some q.2 :=
          fun q hq => hkeys q (by simp [hq])
        obtain ⟨⟨c2, cs2, hps_list, hws2, _⟩, _, _⟩ := joinRenderedPath_props (p2 :: ps2) hps_ne hps_keys
        have hjoin : joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd) =
            rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd) := rfl
        have hsplit : (joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd)).toList ++ rest =
            rk.toList ++ ('.' :: ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest)) := by
          rw [hjoin, String.toList_append, String.toList_append, List.append_assoc]
          simp
        rw [hsplit]
        unfold parseDottedKeyFuel
        have hdot_rest : ∀ c tail,
            ('.' :: ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest)) = c :: tail →
            !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'' := by
          intro c tail h; injection h with h1 _; subst h1; decide
        rw [(renderKey_parseKeySegment k ks rk hrk _ hdot_rest).1]
        simp only [bind, Except.bind]
        rw [skipHorizWs_cons_of_false '.' _ (by decide)]
        split
        · rename_i r3 hdot_eq
          injection hdot_eq with _ hr3
          rw [← hr3]
          have hskip_ps : skipHorizWs ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest) =
              (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest := by
            rw [hps_list, List.cons_append]
            exact skipHorizWs_cons_of_false c2 _ hws2
          rw [hskip_ps]
          have hf' : f ≥ (p2 :: ps2).length := by simp at hf; omega
          rw [ih hps_ne hps_keys rest hrest hsw f hf']
          rfl
        · rename_i hnot
          exact absurd rfl (hnot _)

private theorem parseDottedKey_joinRenderedPath
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.') :
    parseDottedKey ((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest) =
      .ok (pairs.map Prod.fst, skipHorizWs rest) := by
  unfold parseDottedKey
  have hlen := (joinRenderedPath_props pairs hne hkeys).2.2
  refine parseDottedKeyFuel_joinRenderedPath pairs hne hkeys rest hrest hsw
    (((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest).length + 1) (by simp; omega)

private theorem assocSetNode_idem (k : String) (v1 v2 : Node) (l : List (String × Node)) :
    assocSetNode k v2 (assocSetNode k v1 l) = assocSetNode k v2 l := by
  induction l with
  | nil => simp [assocSetNode]
  | cons p rest ih =>
    rcases p with ⟨k', old⟩
    by_cases h : k == k'
    · simp [assocSetNode, h]
    · simp [assocSetNode, h, ih]

private theorem assocLookupNode_assocSetNode_ne (k q : String) (v : Node)
    (l : List (String × Node)) (hne : q ≠ k) :
    assocLookupNode q (assocSetNode k v l) = assocLookupNode q l := by
  rw [assocLookupNode_assocSetNode, beq_false_of_ne hne]
  rfl

private theorem dropLast_append_singleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).dropLast = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l2 => simp [List.dropLast]

private theorem getLast?_append_singleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).getLast? = some x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l2 => simpa [List.getLast?] using ih

private theorem mapLastAot_eq (f : List (String × Node) → Except TomlError (List (String × Node)))
    (elems : List (List (String × Node))) (lastElem newLast : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem) (hf : f lastElem = .ok newLast) :
    mapLastAot f elems = .ok (elems.dropLast ++ [newLast]) := by
  induction elems with
  | nil => exact absurd rfl hne
  | cons a bs ih =>
    cases bs with
    | nil =>
      have ha : a = lastElem := by simpa [List.getLast?] using hlast
      subst ha
      simp [mapLastAot, hf, bind, Except.bind]
    | cons b bs2 =>
      have hlast' : (b :: bs2).getLast? = some lastElem := by simpa [List.getLast?] using hlast
      have ih' := ih (by simp) hlast'
      simp [mapLastAot, ih', List.dropLast, bind, Except.bind]

private inductive AtLocalPath :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries : List (String × Node)) :
      AtLocalPath entries [] entries id
  | consTable {entries : List (String × Node)} {k : String} {kind : TableKind}
      {sub : List (String × Node)} {ps : List String}
      {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      kind ≠ .inline →
      assocLookupNode k entries = some (.table kind sub) →
      AtLocalPath sub ps loc rb →
      AtLocalPath entries (k :: ps) loc (fun newLoc => assocSetNode k (.table kind (rb newLoc)) entries)
  | consAot {entries : List (String × Node)} {k : String}
      {elems : List (List (String × Node))} {lastElem : List (String × Node)}
      {ps : List String} {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      elems ≠ [] →
      elems.getLast? = some lastElem →
      assocLookupNode k entries = some (.aot elems) →
      AtLocalPath lastElem ps loc rb →
      AtLocalPath entries (k :: ps) loc
        (fun newLoc => assocSetNode k (.aot (elems.dropLast ++ [rb newLoc])) entries)

private theorem atLocalPath_self {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) :
    rb loc = root := by
  induction h with
  | nil _ => rfl
  | @consTable entries k kind sub ps loc rb _ hlk _ ih =>
    dsimp only
    rw [ih]
    clear ih
    induction entries with
    | nil => cases hlk
    | cons p rest ihr =>
      rcases p with ⟨k', n'⟩
      simp only [assocLookupNode] at hlk
      by_cases heq : k == k'
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk
        subst hlk
        simp [assocSetNode, heq]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk
        simp only [assocSetNode, heq, Bool.false_eq_true, ↓reduceIte, ihr hlk]
  | @consAot entries k elems lastElem ps loc rb hne hlast hlk _ ih =>
    dsimp only
    rw [ih]
    clear ih
    have helems : elems.dropLast ++ [lastElem] = elems := by
      clear hlk
      induction elems with
      | nil => exact absurd rfl hne
      | cons a bs ihe =>
        cases bs with
        | nil =>
          simp only [List.getLast?, Option.some.injEq] at hlast
          subst hlast; rfl
        | cons b bs2 =>
          have hlast' : (b :: bs2).getLast? = some lastElem := by simpa [List.getLast?] using hlast
          simp only [List.dropLast, List.cons_append, ihe (by simp) hlast']
    rw [helems]
    induction entries with
    | nil => cases hlk
    | cons p rest ihr =>
      rcases p with ⟨k', n'⟩
      simp only [assocLookupNode] at hlk
      by_cases heq : k == k'
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk
        subst hlk
        simp [assocSetNode, heq]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk
        simp only [assocSetNode, heq, Bool.false_eq_true, ↓reduceIte, ihr hlk]

private theorem atLocalPath_rebuild {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (newLoc : List (String × Node)) :
    AtLocalPath (rb newLoc) path newLoc rb := by
  induction h with
  | nil _ => exact AtLocalPath.nil newLoc
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table kind (rbSub newLoc)) entries) =
        some (.table kind (rbSub newLoc)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table kind (rbSub nl))
        (assocSetNode k (.table kind (rbSub newLoc)) entries)) =
        (fun nl => assocSetNode k (.table kind (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using AtLocalPath.consTable hkind hlk' ih
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    let elems' := elems.dropLast ++ [rbSub newLoc]
    have hne' : elems' ≠ [] := by simp [elems']
    have hlast' : elems'.getLast? = some (rbSub newLoc) := getLast?_append_singleton _ _
    have hlk' : assocLookupNode k (assocSetNode k (.aot elems') entries) = some (.aot elems') := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.aot (elems'.dropLast ++ [rbSub nl]))
        (assocSetNode k (.aot elems') entries)) =
        (fun nl => assocSetNode k (.aot (elems.dropLast ++ [rbSub nl])) entries) := by
      funext nl
      rw [dropLast_append_singleton]
      exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using AtLocalPath.consAot hne' hlast' hlk' ih

private theorem atLocalPath_stepTable {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (k : String) (kind : TableKind) (sub : List (String × Node))
    (hkind : kind ≠ .inline) (hlk : assocLookupNode k loc = some (.table kind sub)) :
    AtLocalPath root (path ++ [k]) sub (fun newSub => rb (assocSetNode k (.table kind newSub) loc)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact AtLocalPath.consTable hkind hlk (AtLocalPath.nil sub)
  | consTable hkind0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consTable hkind0 hlk0 (ih hlk)
  | consAot hne0 hlast0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consAot hne0 hlast0 hlk0 (ih hlk)

private theorem atLocalPath_stepAot {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (k : String)
    (elems : List (List (String × Node))) (lastElem : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem)
    (hlk : assocLookupNode k loc = some (.aot elems)) :
    AtLocalPath root (path ++ [k]) lastElem
      (fun newLast => rb (assocSetNode k (.aot (elems.dropLast ++ [newLast])) loc)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact AtLocalPath.consAot hne hlast hlk (AtLocalPath.nil lastElem)
  | consTable hkind0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consTable hkind0 hlk0 (ih hlk)
  | consAot hne0 hlast0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consAot hne0 hlast0 hlk0 (ih hlk)

private theorem atLocalPath_insertAtActivePath {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath relPath : List String) (newNode : Node)
    (newLoc : List (String × Node))
    (hins : insertDottedEntries fullPath loc relPath newNode = .ok newLoc) :
    insertAtActivePath fullPath root path relPath newNode = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa [insertAtActivePath] using hins
  | @consTable entries k kind sub ps loc' rbSub _ hlk _ ih =>
    simp [insertAtActivePath, hlk, ih hins, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk _ ih =>
    have hmap := mapLastAot_eq (fun elem => insertAtActivePath fullPath elem ps relPath newNode)
      elems lastElem (rbSub newLoc) hne hlast (ih hins)
    simp [insertAtActivePath, hlk, hmap, bind, Except.bind]

private theorem atLocalPath_applyTableHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyTableHeader fullPath loc suffix = .ok newLoc) :
    applyTableHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa using happ
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyTableHeader, hlk]
      rw [← hps]
      cases kind with
      | inline => exact absurd rfl hkind
      | explicit | subtableImplicit | dotted => simp [ih happ, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyTableHeader, hlk]
      rw [← hps]
      have hmap := mapLastAot_eq (fun elem => applyTableHeader fullPath elem (ps ++ suffix))
        elems lastElem (rbSub newLoc) hne hlast (ih happ)
      simp [hmap, bind, Except.bind]

private theorem atLocalPath_applyAotHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyAotHeader fullPath loc suffix = .ok newLoc) :
    applyAotHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa using happ
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyAotHeader, hlk]
      rw [← hps]
      cases kind with
      | inline => exact absurd rfl hkind
      | explicit | subtableImplicit | dotted => simp [ih happ, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyAotHeader, hlk]
      rw [← hps]
      have hmap := mapLastAot_eq (fun elem => applyAotHeader fullPath elem (ps ++ suffix))
        elems lastElem (rbSub newLoc) hne hlast (ih happ)
      simp [hmap, bind, Except.bind]

private inductive AtHeaderFocus :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | exact {root : List (String × Node)} {path : List String}
      {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      AtLocalPath root path loc rb → AtHeaderFocus root path loc rb
  | implicitNone {root parentLoc : List (String × Node)} {parentPath : List String}
      {rbParent : List (String × Node) → List (String × Node)} {k : String} :
      AtHeaderFocus root parentPath parentLoc rbParent →
      assocLookupNode k parentLoc = none →
      AtHeaderFocus root (parentPath ++ [k]) []
        (fun newSub => rbParent (assocSetNode k (.table .subtableImplicit newSub) parentLoc))

private theorem atHeaderFocus_applyTableHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyTableHeader fullPath loc suffix = .ok newLoc) :
    applyTableHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h generalizing suffix newLoc with
  | exact hp => exact atLocalPath_applyTableHeader hp fullPath suffix hsuf newLoc happ
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    rw [List.append_assoc]
    apply ih (k :: suffix) (by simp) (assocSetNode k (.table .subtableImplicit newLoc) parentLoc)
    cases suffix with
    | nil => exact absurd rfl hsuf
    | cons s0 ss0 =>
      simp [applyTableHeader, hnone, happ, bind, Except.bind]

private theorem atHeaderFocus_applyAotHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyAotHeader fullPath loc suffix = .ok newLoc) :
    applyAotHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h generalizing suffix newLoc with
  | exact hp => exact atLocalPath_applyAotHeader hp fullPath suffix hsuf newLoc happ
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    rw [List.append_assoc]
    apply ih (k :: suffix) (by simp) (assocSetNode k (.table .subtableImplicit newLoc) parentLoc)
    cases suffix with
    | nil => exact absurd rfl hsuf
    | cons s0 ss0 =>
      simp [applyAotHeader, hnone, happ, bind, Except.bind]

private theorem atHeaderFocus_step {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (newLoc : List (String × Node)) :
    AtLocalPath (rb newLoc) path newLoc rb := by
  induction h generalizing newLoc with
  | exact hp => exact atLocalPath_rebuild hp newLoc
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    let newParent := assocSetNode k (.table .subtableImplicit newLoc) parentLoc
    have hp := ih newParent
    have hlk : assocLookupNode k newParent = some (.table .subtableImplicit newLoc) := by
      simp [newParent, assocLookupNode_assocSetNode]
    have hstep := atLocalPath_stepTable hp k .subtableImplicit newLoc (by decide) hlk
    have hrb_eq : (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) newParent)) =
        (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) parentLoc)) := by
      funext nl
      simp [newParent, assocSetNode_idem]
    rwa [hrb_eq] at hstep

private theorem joinLines_length_ge (lines : List String) :
    (joinLines lines).toList.length ≥ lines.length := by
  induction lines with
  | nil => simp
  | cons l ls ih =>
    simp only [joinLines, String.toList_append, List.length_append, List.length_cons]
    have hnl : ("\n" : String).toList.length = 1 := rfl
    omega

private theorem parseDocumentFuel_assign_step (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (v : TomlValue) (vt : ValueTape) (rv : String) (hrv : renderValueInline v vt = some rv)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root : List (String × Node))
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    ∃ v', TomlEquiv v v' ∧
      ((joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList.all fun c =>
        !isDisallowedControl c && c != '\r') = true ∧
      (∀ nextRoot, insertAtActivePath (activePath ++ pairs.map Prod.fst) root activePath
        (pairs.map Prod.fst) (valueToInlineNode v') = .ok nextRoot →
       parseDocumentFuel numApi fuel
         ((joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars)
         activePath root =
       parseDocumentFuel numApi (fuel - 1) restChars activePath nextRoot) := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, hn0, hc0, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, hrc_delim⟩ := renderCommentSuffix_props comment rc hrc
  obtain ⟨cv0, csv0, hrv_list, hvws0, _⟩ := renderValueInline_headSafe v vt rv hrv
  let valRest := rc.toList ++ '\n' :: restChars
  let valFuel := (rv.toList ++ valRest).length + 2
  obtain ⟨v', hpv, heqv, hrv_cl⟩ :=
    renderValueInline_parseValueFuel numApi hInt hFloat v vt rv hrv valRest valFuel
      (by dsimp only [valFuel]; rw [List.length_append]; omega) (hrc_delim restChars)
  have hline_cl : ((lhs ++ " = " ++ rv ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hlhs_cl', by decide⟩, hrv_cl⟩, hrc_cl'⟩
  refine ⟨v', heqv, hline_cl, fun nextRoot hins' => ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : (lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars =
      lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) := by
    simp [valRest, String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines ((lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars) =
      lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) := by
    rw [hline_list, hlhs_list, List.cons_append]
    exact skipTriviaNewlines_cons_of_safe c0 _ hws0 hn0 hc0
  have hdk : parseDottedKey (lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest))) =
      .ok (pairs.map Prod.fst, '=' :: ' ' :: (rv.toList ++ valRest)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (' ' :: '=' :: ' ' :: (rv.toList ++ valRest))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨'=', ' ' :: (rv.toList ++ valRest), by simp [skipHorizWs, isHorizWs], by decide⟩
    simpa [lhs, skipHorizWs, isHorizWs] using h
  have hr2 : skipHorizWs ('=' :: ' ' :: (rv.toList ++ valRest)) = '=' :: ' ' :: (rv.toList ++ valRest) :=
    skipHorizWs_cons_of_false '=' _ (by decide)
  have hval_in : skipHorizWs (' ' :: (rv.toList ++ valRest)) = rv.toList ++ valRest := by
    rw [skipHorizWs_space, hrv_list, List.cons_append]
    exact skipHorizWs_cons_of_false cv0 _ hvws0
  have hval_ok : parseValue numApi (rv.toList ++ valRest) = .ok (v', valRest) := by
    unfold parseValue; exact hpv
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; rw [hlhs_list] at heq; cases heq
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq
    injection heq with h1 _; exact absurd h1 hl0
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq
    injection heq with h1 _; exact absurd h1 hl0
  · rw [hdk]
    simp only [bind, Except.bind, hr2]
    rw [hval_in, hval_ok]
    dsimp only [valRest]
    rw [hrc_end restChars]
    dsimp only
    rw [hins']

private theorem parseDocumentFuel_table_step (numApi : NumParseApi)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root nextRoot : List (String × Node))
    (happ : applyTableHeader (pairs.map Prod.fst) root (pairs.map Prod.fst) = .ok nextRoot)
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    (("[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]" ++ rc).toList.all fun c =>
      !isDisallowedControl c && c != '\r') = true ∧
    parseDocumentFuel numApi fuel
      (("[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]" ++ rc).toList ++ '\n' :: restChars)
      activePath root =
    parseDocumentFuel numApi (fuel - 1) restChars (pairs.map Prod.fst) nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, _, _, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, _⟩ := renderCommentSuffix_props comment rc hrc
  have hline_cl : (("[" ++ lhs ++ "]" ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨by decide, hlhs_cl'⟩, by decide⟩, hrc_cl'⟩
  refine ⟨hline_cl, ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : ("[" ++ lhs ++ "]" ++ rc).toList ++ '\n' :: restChars =
      '[' :: (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines (("[" ++ lhs ++ "]" ++ rc).toList ++ '\n' :: restChars) =
      '[' :: (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) := by
    rw [hline_list]
    exact skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)
  have hrest_lhs : skipHorizWs (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) =
      lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars)) := by
    rw [hlhs_list, List.cons_append]
    exact skipHorizWs_cons_of_false c0 _ hws0
  have hdk : parseDottedKey (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) =
      .ok (pairs.map Prod.fst, ']' :: (rc.toList ++ '\n' :: restChars)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (']' :: (rc.toList ++ '\n' :: restChars))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨']', rc.toList ++ '\n' :: restChars, skipHorizWs_cons_of_false ']' _ (by decide), by decide⟩
    simpa [lhs, skipHorizWs_cons_of_false ']' _ (by decide)] using h
  have hr2 : skipHorizWs (']' :: (rc.toList ++ '\n' :: restChars)) = ']' :: (rc.toList ++ '\n' :: restChars) :=
    skipHorizWs_cons_of_false ']' _ (by decide)
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; cases heq
  · rename_i heq
    injection heq with _ h2
    rw [hlhs_list, List.cons_append] at h2
    injection h2 with h2' _
    exact absurd h2' hl0
  · rename_i restHdr _ heq
    injection heq with _ hrest_eq
    rw [← hrest_eq, hrest_lhs, hdk]
    simp only [bind, Except.bind, hr2]
    rw [hrc_end restChars]
    dsimp only
    rw [happ]
  · rename_i hnot
    exact absurd rfl (hnot _)

private theorem parseDocumentFuel_aot_step (numApi : NumParseApi)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root nextRoot : List (String × Node))
    (happ : applyAotHeader (pairs.map Prod.fst) root (pairs.map Prod.fst) = .ok nextRoot)
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    (("[[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]]" ++ rc).toList.all fun c =>
      !isDisallowedControl c && c != '\r') = true ∧
    parseDocumentFuel numApi fuel
      (("[[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]]" ++ rc).toList ++ '\n' :: restChars)
      activePath root =
    parseDocumentFuel numApi (fuel - 1) restChars (pairs.map Prod.fst) nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, _⟩ := renderCommentSuffix_props comment rc hrc
  have hline_cl : (("[[" ++ lhs ++ "]]" ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨by decide, hlhs_cl'⟩, by decide⟩, hrc_cl'⟩
  refine ⟨hline_cl, ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : ("[[" ++ lhs ++ "]]" ++ rc).toList ++ '\n' :: restChars =
      '[' :: '[' :: (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines (("[[" ++ lhs ++ "]]" ++ rc).toList ++ '\n' :: restChars) =
      '[' :: '[' :: (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) := by
    rw [hline_list]
    exact skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)
  have hrest_lhs : skipHorizWs (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) =
      lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars)) := by
    rw [hlhs_list, List.cons_append]
    exact skipHorizWs_cons_of_false c0 _ hws0
  have hdk : parseDottedKey (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) =
      .ok (pairs.map Prod.fst, ']' :: ']' :: (rc.toList ++ '\n' :: restChars)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (']' :: ']' :: (rc.toList ++ '\n' :: restChars))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨']', ']' :: (rc.toList ++ '\n' :: restChars), skipHorizWs_cons_of_false ']' _ (by decide), by decide⟩
    simpa [lhs, skipHorizWs_cons_of_false ']' _ (by decide)] using h
  have hr2 : skipHorizWs (']' :: ']' :: (rc.toList ++ '\n' :: restChars)) =
      ']' :: ']' :: (rc.toList ++ '\n' :: restChars) :=
    skipHorizWs_cons_of_false ']' _ (by decide)
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; cases heq
  · rename_i restHdr _ heq
    injection heq with _ h1
    injection h1 with _ hrest_eq
    rw [← hrest_eq, hrest_lhs, hdk]
    simp only [bind, Except.bind, hr2]
    rw [hrc_end restChars]
    dsimp only
    rw [happ]
  · rename_i hnot heq
    injection heq with _ htail
    exact absurd htail.symm (hnot _)
  · rename_i hnot _
    exact absurd rfl (hnot _)

private inductive DottedWriteFocus :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries : List (String × Node)) :
      DottedWriteFocus entries [] entries id
  | consNone {entries : List (String × Node)} {k : String} {ps : List String}
      {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      assocLookupNode k entries = none →
      DottedWriteFocus [] ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)
  | consDotted {entries : List (String × Node)} {k : String} {cur : List (String × Node)}
      {ps : List String} {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      assocLookupNode k entries = some (.table .dotted cur) →
      DottedWriteFocus cur ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)

private theorem dottedWriteFocus_insert {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (fullPath rel : List String) (hrel : rel ≠ [])
    (newNode : Node) (newSub : List (String × Node))
    (hins : insertDottedEntries fullPath sub rel newNode = .ok newSub) :
    insertDottedEntries fullPath entries (pref ++ rel) newNode = .ok (rb newSub) := by
  induction h with
  | nil entries => simpa using hins
  | @consNone entries k ps sub' rbSub hnone hsub ih =>
    have hne : ps ++ rel ≠ [] := by
      cases ps with
      | nil => simpa using hrel
      | cons _ _ => simp
    cases hps : ps ++ rel with
    | nil => exact absurd hps hne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [insertDottedEntries, hnone]
      rw [← hps]
      simp [ih hins, bind, Except.bind]
  | @consDotted entries k cur ps sub' rbSub hlk hsub ih =>
    have hne : ps ++ rel ≠ [] := by
      cases ps with
      | nil => simpa using hrel
      | cons _ _ => simp
    cases hps : ps ++ rel with
    | nil => exact absurd hps hne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [insertDottedEntries, hlk]
      rw [← hps]
      simp [ih hins, bind, Except.bind]

private theorem dottedWriteFocus_rebuild {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (newSub : List (String × Node)) :
    DottedWriteFocus (rb newSub) pref newSub rb := by
  induction h with
  | nil _ => exact DottedWriteFocus.nil newSub
  | @consNone entries k ps sub' rbSub hnone hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table .dotted (rbSub newSub)) entries) =
        some (.table .dotted (rbSub newSub)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table .dotted (rbSub nl))
        (assocSetNode k (.table .dotted (rbSub newSub)) entries)) =
        (fun nl => assocSetNode k (.table .dotted (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using DottedWriteFocus.consDotted hlk' ih
  | @consDotted entries k cur ps sub' rbSub hlk hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table .dotted (rbSub newSub)) entries) =
        some (.table .dotted (rbSub newSub)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table .dotted (rbSub nl))
        (assocSetNode k (.table .dotted (rbSub newSub)) entries)) =
        (fun nl => assocSetNode k (.table .dotted (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using DottedWriteFocus.consDotted hlk' ih

private theorem dottedWriteFocus_step {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (k : String) (hnone : assocLookupNode k sub = none) :
    DottedWriteFocus entries (pref ++ [k]) [] (fun newSub => rb (assocSetNode k (.table .dotted newSub) sub)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact DottedWriteFocus.consNone hnone (DottedWriteFocus.nil [])
  | consNone hn0 hsub ih =>
    simp only [List.cons_append]
    exact DottedWriteFocus.consNone hn0 (ih hnone)
  | consDotted hlk0 hsub ih =>
    simp only [List.cons_append]
    exact DottedWriteFocus.consDotted hlk0 (ih hnone)

private theorem noDupStringsBool_iff_nodup (l : List String) :
    noDupStringsBool l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [noDupStringsBool]
  | cons x xs ih =>
    simp only [noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons]
    rw [ih]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨fun hmem => ?_, hxs⟩
      have hc : xs.contains x = true := List.contains_iff_mem.mpr hmem
      rw [hc] at hx; cases hx
    · rintro ⟨hx, hxs⟩
      refine ⟨?_, hxs⟩
      rw [Bool.eq_false_iff]; intro hc
      exact hx (List.contains_iff_mem.mp hc)

private theorem nodup_subset_len_mem {l1 l2 : List String}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hlen : l1.length = l2.length)
    (hsub : ∀ x ∈ l1, x ∈ l2) : ∀ y ∈ l2, y ∈ l1 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => intro y hy; cases hy
    | cons _ _ => simp at hlen
  | cons a as ih =>
    rw [List.nodup_cons] at h1
    have ha2 : a ∈ l2 := hsub a (by simp)
    have h2_erase : (l2.erase a).Nodup := h2.erase a
    have hlen_erase : as.length = (l2.erase a).length := by
      have hl : (l2.erase a).length = l2.length - 1 := List.length_erase_of_mem ha2
      simp only [List.length_cons] at hlen
      have hpos : l2.length ≥ 1 := List.length_pos_of_mem ha2
      omega
    have hsub_erase : ∀ x ∈ as, x ∈ l2.erase a := by
      intro x hx
      have hne : x ≠ a := fun heq => h1.1 (heq ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (by simp [hx]))
    intro y hy
    by_cases hya : y = a
    · simp [hya]
    · have hy_er : y ∈ l2.erase a := (List.mem_erase_of_ne hya).mpr hy
      exact List.mem_cons_of_mem a (ih h1.2 h2_erase hlen_erase hsub_erase y hy_er)

private theorem isPlanPermutation_props {entries : List (String × TomlValue)}
    {plan : List (String × EntryPlacement)} (h : isPlanPermutation entries plan = true) :
    noDupKeysBool entries = true ∧
    noDupStringsBool (plan.map Prod.fst) = true ∧
    (∀ p ∈ plan, ∃ v, lookupKeyList p.1 entries = some v) ∧
    (∀ q v, lookupKeyList q entries = some v → ∃ ep, (q, ep) ∈ plan) := by
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨hnd_e, hnd_p⟩, hlen⟩, hall⟩
  have h1 : ∀ p ∈ plan, ∃ v, lookupKeyList p.1 entries = some v := by
    intro p hp
    have hhas : hasKeyList p.1 entries = true := hall p hp
    clear hall hp hnd_e hnd_p hlen
    induction entries with
    | nil => cases hhas
    | cons e es ih =>
      rcases e with ⟨ek, ev⟩
      simp only [lookupKeyList]
      simp only [hasKeyList] at hhas
      by_cases hpk : p.1 == ek
      · simp [hpk]
      · simp only [hpk, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at hhas ⊢
        exact ih hhas
  have hnodup_p : (plan.map Prod.fst).Nodup := (noDupStringsBool_iff_nodup _).mp hnd_p
  have hnodup_e : (entries.map Prod.fst).Nodup := (noDupKeys_iff_nodup entries).mp hnd_e
  have hsub : ∀ x ∈ plan.map Prod.fst, x ∈ entries.map Prod.fst := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    exact (hasKeyList_eq_true_iff p.1 entries).mp (hall p hp)
  have hlen' : (plan.map Prod.fst).length = (entries.map Prod.fst).length := by
    simpa using hlen
  have hcov : ∀ q v, lookupKeyList q entries = some v → ∃ ep, (q, ep) ∈ plan := by
    intro q v hqv
    have hq_mem_e : q ∈ entries.map Prod.fst := by
      have hp := lookupKeyList_mem hqv
      exact List.mem_map.mpr ⟨(q, v), hp, rfl⟩
    have hq_mem_p : q ∈ plan.map Prod.fst := nodup_subset_len_mem hnodup_p hnodup_e hlen' hsub q hq_mem_e
    rw [List.mem_map] at hq_mem_p
    rcases hq_mem_p with ⟨⟨k, ep⟩, hmem, hkq⟩
    dsimp only at hkq; subst hkq
    exact ⟨ep, hmem⟩
  exact ⟨hnd_e, hnd_p, h1, hcov⟩

private theorem entriesToTomlList_of_plan_match (entries : List (String × TomlValue))
    (plan : List (String × EntryPlacement)) (hperm : isPlanPermutation entries plan = true)
    (nodes : List (String × Node))
    (hmatch : ∀ p ∈ plan, ∃ v nd, lookupKeyList p.1 entries = some v ∧
      assocLookupNode p.1 nodes = some nd ∧ TomlEquiv v (nodeToTomlValue nd))
    (honly : ∀ q, q ∉ plan.map Prod.fst → assocLookupNode q nodes = none) :
    TomlTableEquivList entries (entriesToTomlList nodes) := by
  obtain ⟨_, _, _, hcov⟩ := isPlanPermutation_props hperm
  unfold TomlTableEquivList
  refine ⟨?_, ?_⟩
  · intro q hnone
    rw [lookupKeyList_entriesToTomlList]
    by_cases hmem : q ∈ plan.map Prod.fst
    · rw [List.mem_map] at hmem
      rcases hmem with ⟨p, hp, rfl⟩
      obtain ⟨v, _, hv, _⟩ := hmatch p hp
      rw [hv] at hnone; cases hnone
    · rw [honly q hmem]; rfl
  · intro q v1 hqv1
    obtain ⟨ep, hep⟩ := hcov q v1 hqv1
    obtain ⟨v, nd, hv, hnd, heqv⟩ := hmatch (q, ep) hep
    have hv_eq : v1 = v := by rw [hqv1] at hv; injection hv
    subst hv_eq
    refine ⟨nodeToTomlValue nd, ?_, heqv⟩
    rw [lookupKeyList_entriesToTomlList, hnd]; rfl

private theorem nodup_key_ne_of_scope (plan : List (String × EntryPlacement))
    (hnd : noDupStringsBool (plan.map Prod.fst) = true)
    (p p' : String × EntryPlacement) (hp : p ∈ plan) (hp' : p' ∈ plan)
    (hps : p.2.isInlineScope = true) (hps' : p'.2.isInlineScope = false) :
    p.1 ≠ p'.1 := by
  intro heq
  have hnd' := (noDupStringsBool_iff_nodup _).mp hnd
  clear hnd
  induction plan with
  | nil => cases hp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd'
    rcases List.mem_cons.mp hp with rfl | hpxs <;> rcases List.mem_cons.mp hp' with rfl | hp'xs
    · rw [hps] at hps'; cases hps'
    · exact hnd'.1 (heq ▸ List.mem_map.mpr ⟨p', hp'xs, rfl⟩)
    · exact hnd'.1 (heq.symm ▸ List.mem_map.mpr ⟨p, hpxs, rfl⟩)
    · exact ih hpxs hp'xs hnd'.2

private theorem renderPlan_props_strong (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g) :
    ∀ n : Nat,
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (revPairs : List (String × String)) (lines : List String),
          sizeOf remPlan ≤ n →
          revPairs ≠ [] →
          (∀ p ∈ revPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderDottedList (revPairs.map Prod.snd) origEntries remPlan = some lines →
          ∀ (startRoot : List (String × Node)) (parentPath : List String)
            (parentLoc : List (String × Node)) (rbParent : List (String × Node) → List (String × Node))
            (subLoc : List (String × Node)) (rbDotted : List (String × Node) → List (String × Node)),
            AtLocalPath startRoot parentPath parentLoc rbParent →
            DottedWriteFocus parentLoc (revPairs.reverse.map Prod.fst) subLoc rbDotted →
            (∀ p ∈ remPlan, assocLookupNode p.1 subLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalSubLoc,
                (∀ p ∈ remPlan, ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                  assocLookupNode p.1 finalSubLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalSubLoc = assocLookupNode q subLoc) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                (remPlan = [] → lines = [] ∧ finalSubLoc = subLoc ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                  parseDocumentFuel numApi (fuel - lines.length) restChars parentPath startRoot) ∧
                (remPlan ≠ [] →
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                  parseDocumentFuel numApi (fuel - lines.length) restChars
                    parentPath (rbParent (rbDotted finalSubLoc)))) ∧
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (revRen : List String) (lines : List String),
          sizeOf remPlan ≤ n →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderInlineEntries revRen origEntries remPlan = some lines →
          ∀ (root : List (String × Node)) (curPath : List String)
            (startLoc : List (String × Node)) (rb : List (String × Node) → List (String × Node)),
            AtLocalPath root curPath startLoc rb →
            (∀ p ∈ remPlan, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc,
                (∀ p ∈ remPlan, p.2.isInlineScope = true →
                  ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                    assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 finalLoc = assocLookupNode p.1 startLoc) ∧
                (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) curPath root =
                parseDocumentFuel numApi (fuel - lines.length) restChars curPath (rb finalLoc)) ∧
      (∀ (elemPlans : List (List (String × EntryPlacement))) (xs : List TomlValue)
          (pathPairs : List (String × String)) (k rk : String) (rc : String) (lines : List String),
          sizeOf elemPlans ≤ n →
          (∃ ks, renderKey k ks = some rk) →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          (∃ comment, renderCommentSuffix comment = some rc) →
          renderAotElems (rk :: pathPairs.reverse.map Prod.snd) rc xs elemPlans = some lines →
          ∀ (root : List (String × Node)) (parentLoc : List (String × Node))
            (rbParent : List (String × Node) → List (String × Node))
            (prevElems : List (List (String × Node))) (startActivePath : List String),
            AtHeaderFocus root (pathPairs.map Prod.fst) parentLoc rbParent →
            ((prevElems = [] ∧ assocLookupNode k parentLoc = none) ∨
             (prevElems ≠ [] ∧ assocLookupNode k parentLoc = some (.aot prevElems))) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalElems endActivePath,
                (xs = [] → finalElems = prevElems ∧ lines = [] ∧ endActivePath = startActivePath) ∧
                (xs ≠ [] → lines ≠ [] ∧
                  ∃ tailElems, finalElems = prevElems ++ tailElems ∧ tailElems ≠ [] ∧
                    TomlListEquiv xs (aotElemsToToml tailElems) ∧
                    AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                      (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                (xs ≠ [] →
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath
                    (rbParent (assocSetNode k (.aot finalElems) parentLoc)))) ∧
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (pathPairs : List (String × String)) (lines : List String),
          sizeOf remPlan ≤ n →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries remPlan = some lines →
          ∀ (root : List (String × Node)) (startLoc : List (String × Node))
            (rb : List (String × Node) → List (String × Node)) (startActivePath : List String),
            AtHeaderFocus root (pathPairs.map Prod.fst) startLoc rb →
            (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc endActivePath,
                (remPlan.any (fun p => !p.2.isInlineScope) = false →
                  lines = [] ∧ finalLoc = startLoc ∧ endActivePath = startActivePath ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath root) ∧
                (remPlan.any (fun p => !p.2.isInlineScope) = true →
                  lines ≠ [] ∧
                  (∀ p ∈ remPlan, p.2.isInlineScope = false →
                    ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                      assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                  (∀ q, (∀ p ∈ remPlan, p.2.isInlineScope = false → q ≠ p.1) →
                    assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
                  AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true) ∧
      (∀ (origEntries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
          (pathPairs : List (String × String)) (lines : List String),
          sizeOf plan + 1 ≤ n →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          renderTablePlan (pathPairs.reverse.map Prod.snd) origEntries plan = some lines →
          ∀ (root : List (String × Node)) (startLoc : List (String × Node))
            (rb : List (String × Node) → List (String × Node)),
            AtLocalPath root (pathPairs.map Prod.fst) startLoc rb →
            startLoc = [] →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc endActivePath,
                TomlTableEquivList origEntries (entriesToTomlList finalLoc) ∧
                AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars)
                  (pathPairs.map Prod.fst) root =
                parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hDot : ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
        (revPairs : List (String × String)) (lines : List String),
        sizeOf remPlan ≤ n →
        revPairs ≠ [] →
        (∀ p ∈ revPairs, ∃ ks, renderKey p.1 ks = some p.2) →
        noDupStringsBool (remPlan.map Prod.fst) = true →
        (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
        renderDottedList (revPairs.map Prod.snd) origEntries remPlan = some lines →
        ∀ (startRoot : List (String × Node)) (parentPath : List String)
          (parentLoc : List (String × Node)) (rbParent : List (String × Node) → List (String × Node))
          (subLoc : List (String × Node)) (rbDotted : List (String × Node) → List (String × Node)),
          AtLocalPath startRoot parentPath parentLoc rbParent →
          DottedWriteFocus parentLoc (revPairs.reverse.map Prod.fst) subLoc rbDotted →
          (∀ p ∈ remPlan, assocLookupNode p.1 subLoc = none) →
          ∀ (restChars : List Char) (fuel : Nat),
            fuel ≥ lines.length →
            ∃ finalSubLoc,
              (∀ p ∈ remPlan, ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                assocLookupNode p.1 finalSubLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
              (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalSubLoc = assocLookupNode q subLoc) ∧
              ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
              (remPlan = [] → lines = [] ∧ finalSubLoc = subLoc ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                parseDocumentFuel numApi (fuel - lines.length) restChars parentPath startRoot) ∧
              (remPlan ≠ [] →
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                parseDocumentFuel numApi (fuel - lines.length) restChars
                  parentPath (rbParent (rbDotted finalSubLoc))) := by
      intro origEntries remPlan revPairs lines hsz hrev_ne hrev_keys hnd_rem hmem_rem hdl
        startRoot parentPath parentLoc rbParent subLoc rbDotted hAt hDotFocus hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderDottedList, Option.some.injEq] at hdl
        subst hdl
        exact ⟨subLoc, (fun p hp => by cases hp), (fun _ _ => rfl), rfl,
          (fun _ => ⟨rfl, rfl, by simp [joinLines]⟩), (fun hne => absurd rfl hne)⟩
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderDottedList] at hdl
        cases hlk : lookupKeyList k origEntries with
        | none => simp [hlk] at hdl
        | some v =>
          simp only [hlk] at hdl
          have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
          have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
            simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
            exact hnd_rem.2
          have hnot_tl : k ∉ tl.map Prod.fst := by
            simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
            intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
            rw [hc] at hnd_rem; cases hnd_rem.1
          have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
            fun p hp => hmem_rem p (by simp [hp])
          cases htail_res : renderDottedList (revPairs.map Prod.snd) origEntries tl with
          | none =>
            cases ep <;> simp [htail_res] at hdl
            · cases v <;> cases hdl
          | some tailLines =>
            cases ep with
            | tableSection _ _ _ _ | aotSection _ _ _ => simp at hdl
            | direct ks vt comment =>
              simp only [bind, Option.bind] at hdl
              cases hrk : renderKey k ks with
              | none => simp [hrk] at hdl
              | some rk =>
                cases hrv : renderValueInline v vt with
                | none => simp [hrk, hrv] at hdl
                | some rv =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrv, hrc] at hdl
                  | some rc =>
                    simp only [hrk, hrv, hrc, htail_res, Option.some.injEq] at hdl
                    subst hdl
                    let pairs := ((k, rk) :: revPairs).reverse
                    have hpairs_ne : pairs ≠ [] := by simp [pairs]
                    have hpairs_keys : ∀ p ∈ pairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                      intro p hp
                      simp only [pairs, List.reverse_cons, List.mem_append, List.mem_reverse, List.mem_singleton] at hp
                      rcases hp with h | h
                      · exact hrev_keys p h
                      · rw [h]; exact ⟨ks, hrk⟩
                    have hpairs_fst : pairs.map Prod.fst = revPairs.reverse.map Prod.fst ++ [k] := by
                      simp [pairs, List.reverse_cons, List.map_append]
                    have hpairs_snd : pairs.map Prod.snd = (rk :: revPairs.map Prod.snd).reverse := by
                      simp [pairs, List.reverse_cons, List.map_append]
                    have hline_eq : joinRenderedPath (rk :: revPairs.map Prod.snd).reverse ++ " = " ++ rv ++ rc =
                        joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc := by
                      rw [hpairs_snd]
                    let line := joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc
                    have hf1 : fuel ≥ 1 := by simp at hf; omega
                    obtain ⟨v', heqv, hline_cl, hstep⟩ :=
                      parseDocumentFuel_assign_step numApi hInt hFloat pairs hpairs_ne hpairs_keys
                        v vt rv hrv comment rc hrc parentPath startRoot
                        ((joinLines tailLines).toList ++ restChars) fuel hf1
                    let midSubLoc := assocSetNode k (valueToInlineNode v') subLoc
                    have hnone_k : assocLookupNode k subLoc = none := hfresh (k, .direct ks vt comment) (by simp)
                    have hins_sub : insertDottedEntries (parentPath ++ pairs.map Prod.fst) subLoc [k] (valueToInlineNode v') =
                        .ok midSubLoc := by
                      simp [insertDottedEntries, hnone_k, midSubLoc]
                    have hins_parent : insertDottedEntries (parentPath ++ pairs.map Prod.fst) parentLoc
                        (pairs.map Prod.fst) (valueToInlineNode v') = .ok (rbDotted midSubLoc) := by
                      rw [hpairs_fst] at hins_sub ⊢
                      exact dottedWriteFocus_insert hDotFocus _ [k] (by simp) (valueToInlineNode v') midSubLoc hins_sub
                    have hins_root : insertAtActivePath (parentPath ++ pairs.map Prod.fst)
                        startRoot parentPath (pairs.map Prod.fst) (valueToInlineNode v') =
                        .ok (rbParent (rbDotted midSubLoc)) :=
                      atLocalPath_insertAtActivePath hAt _ _ _ _ hins_parent
                    have hAt_mid : AtLocalPath (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent :=
                      atLocalPath_rebuild hAt (rbDotted midSubLoc)
                    have hDot_mid : DottedWriteFocus (rbDotted midSubLoc) (revPairs.reverse.map Prod.fst) midSubLoc rbDotted :=
                      dottedWriteFocus_rebuild hDotFocus midSubLoc
                    have hfresh_tl : ∀ p ∈ tl, assocLookupNode p.1 midSubLoc = none := by
                      intro p hp
                      have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                      rw [assocLookupNode_assocSetNode_ne k p.1 _ subLoc hne]
                      exact hfresh p (by simp [hp])
                    have hih_tl := (ih (sizeOf tl) hsz_tl).1 origEntries tl revPairs tailLines (Nat.le_refl _)
                      hrev_ne hrev_keys hnd_tl hmem_tl htail_res
                      (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent midSubLoc rbDotted
                      hAt_mid hDot_mid hfresh_tl restChars (fuel - 1) (by simp at hf; omega)
                    rcases hih_tl with ⟨finalSubLoc, htl_match, htl_rest, htl_cl, htl_nil, htl_cons⟩
                    have hparse_fin : parseDocumentFuel numApi fuel ((joinLines ([line] ++ tailLines)).toList ++ restChars) parentPath startRoot =
                        parseDocumentFuel numApi (fuel - ([line] ++ tailLines).length) restChars
                          parentPath (rbParent (rbDotted finalSubLoc)) := by
                      have hjoin_eq : (joinLines ([line] ++ tailLines)).toList ++ restChars =
                          line.toList ++ ('\n' :: ((joinLines tailLines).toList ++ restChars)) := by
                        simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                      rw [hjoin_eq, hstep (rbParent (rbDotted midSubLoc)) hins_root]
                      cases tl with
                      | nil =>
                        obtain ⟨_, hfin_eq, hparse0⟩ := htl_nil rfl
                        rw [hfin_eq, hparse0]
                        simp [Nat.sub_sub, Nat.add_comm]
                      | cons _ _ =>
                        rw [htl_cons (by simp)]
                        simp [Nat.sub_sub, Nat.add_comm]
                    refine ⟨finalSubLoc, ?_, ?_, ?_, (fun hnil => by cases hnil), fun _ => ?_⟩
                    · intro p hp
                      simp only [List.mem_cons] at hp
                      rcases hp with rfl | hptl
                      · refine ⟨v, valueToInlineNode v', hlk, ?_, ?_⟩
                        · rw [htl_rest k hnot_tl]
                          simp [midSubLoc, assocLookupNode_assocSetNode]
                        · simpa [nodeToTomlValue_valueToInlineNode] using heqv
                      · exact htl_match p hptl
                    · intro q hq_not
                      have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                      have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                      rw [htl_rest q hnot_tl']
                      exact assocLookupNode_assocSetNode_ne k q _ subLoc hne_k
                    · rw [hline_eq, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append]
                      exact Bool.and_eq_true_iff.mpr ⟨joinLines_singleton_clean _ hline_cl, htl_cl⟩
                    · rw [hline_eq]
                      simpa using hparse_fin
            | dotted ks subPlan =>
              cases v with
              | table sub =>
                by_cases hemp : sub.isEmpty = true
                · simp [hemp] at hdl
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at hdl
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hdl
                  | some rk =>
                    simp only [hrk] at hdl
                    cases hsub_lines : renderDottedSub (rk :: revPairs.map Prod.snd) sub.toList subPlan with
                    | none => simp [hsub_lines] at hdl
                    | some subLines =>
                      simp [hsub_lines, htail_res] at hdl
                      subst hdl
                      simp only [renderDottedSub] at hsub_lines
                      split at hsub_lines
                      · cases hsub_lines
                      · rename_i hperm_neg
                        have hperm : isPlanPermutation sub.toList subPlan = true := by
                          cases h : isPlanPermutation sub.toList subPlan
                          · exfalso; exact hperm_neg (by simp [h])
                          · rfl
                        obtain ⟨_, hnd_sub, hmem_sub, hcov_sub⟩ := isPlanPermutation_props hperm
                        have hsub_ne_list : sub.toList ≠ [] := by
                          intro heq
                          have hnil : sub = #[] := Array.toList_eq_nil_iff.mp heq
                          subst hnil
                          exact absurd rfl hemp
                        have hsubPlan_ne : subPlan ≠ [] := by
                          intro hnil
                          cases hsub_ne_cons : sub.toList with
                          | nil => exact hsub_ne_list hsub_ne_cons
                          | cons hd_s _ =>
                            obtain ⟨ep0, hep0⟩ := hcov_sub hd_s.1 hd_s.2 (by simp [hsub_ne_cons, lookupKeyList])
                            rw [hnil] at hep0; cases hep0
                        have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                        have hrev_sub_ne : (k, rk) :: revPairs ≠ [] := by simp
                        have hrev_sub_keys : ∀ p ∈ (k, rk) :: revPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                          intro p hp
                          rcases List.mem_cons.mp hp with rfl | h
                          · exact ⟨ks, hrk⟩
                          · exact hrev_keys p h
                        have hnone_k : assocLookupNode k subLoc = none := hfresh (k, .dotted ks subPlan) (by simp)
                        let rbSubDot := fun newSub => rbDotted (assocSetNode k (.table .dotted newSub) subLoc)
                        have hDot_sub : DottedWriteFocus parentLoc (((k, rk) :: revPairs).reverse.map Prod.fst) [] rbSubDot := by
                          simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
                          exact dottedWriteFocus_step hDotFocus k hnone_k
                        have hf_sub : fuel - subLines.length ≥ tailLines.length := by
                          simp only [List.length_append] at hf; omega
                        have hih_sub := (ih (sizeOf subPlan) hsz_sub).1 sub.toList subPlan ((k, rk) :: revPairs) subLines
                          (Nat.le_refl _) hrev_sub_ne hrev_sub_keys hnd_sub hmem_sub hsub_lines
                          startRoot parentPath parentLoc rbParent [] rbSubDot
                          hAt hDot_sub (fun _ _ => rfl) ((joinLines tailLines).toList ++ restChars) fuel
                          (by simp only [List.length_append] at hf; omega)
                        rcases hih_sub with ⟨finalChildSub, hsub_match, hsub_rest, hsub_cl, _, hsub_parse⟩
                        let midSubLoc := assocSetNode k (.table .dotted finalChildSub) subLoc
                        have hAt_mid : AtLocalPath (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent :=
                          atLocalPath_rebuild hAt (rbDotted midSubLoc)
                        have hDot_mid : DottedWriteFocus (rbDotted midSubLoc) (revPairs.reverse.map Prod.fst) midSubLoc rbDotted :=
                          dottedWriteFocus_rebuild hDotFocus midSubLoc
                        have hfresh_tl : ∀ p ∈ tl, assocLookupNode p.1 midSubLoc = none := by
                          intro p hp
                          have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                          rw [assocLookupNode_assocSetNode_ne k p.1 _ subLoc hne]
                          exact hfresh p (by simp [hp])
                        have hih_tl := (ih (sizeOf tl) hsz_tl).1 origEntries tl revPairs tailLines (Nat.le_refl _)
                          hrev_ne hrev_keys hnd_tl hmem_tl htail_res
                          (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent midSubLoc rbDotted
                          hAt_mid hDot_mid hfresh_tl restChars (fuel - subLines.length) hf_sub
                        rcases hih_tl with ⟨finalSubLoc, htl_match, htl_rest, htl_cl, htl_nil, htl_cons⟩
                        refine ⟨finalSubLoc, ?_, ?_, ?_, (fun hnil => by cases hnil), fun _ => ?_⟩
                        · intro p hp
                          simp only [List.mem_cons] at hp
                          rcases hp with rfl | hptl
                          · refine ⟨.table sub, .table .dotted finalChildSub, hlk, ?_, ?_⟩
                            · rw [htl_rest k hnot_tl]
                              simp [midSubLoc, assocLookupNode_assocSetNode]
                            · have hsub_only : ∀ q, q ∉ subPlan.map Prod.fst → assocLookupNode q finalChildSub = none :=
                                fun q hq => hsub_rest q hq
                              have heqv_sub := entriesToTomlList_of_plan_match sub.toList subPlan hperm finalChildSub hsub_match hsub_only
                              simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                          · exact htl_match p hptl
                        · intro q hq_not
                          have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                          have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                          rw [htl_rest q hnot_tl']
                          exact assocLookupNode_assocSetNode_ne k q _ subLoc hne_k
                        · rw [joinLines_append, String.toList_append, List.all_append]
                          exact Bool.and_eq_true_iff.mpr ⟨hsub_cl, htl_cl⟩
                        · rw [joinLines_append, String.toList_append, List.append_assoc, hsub_parse hsubPlan_ne]
                          change parseDocumentFuel numApi (fuel - subLines.length)
                              ((joinLines tailLines).toList ++ restChars) parentPath (rbParent (rbDotted midSubLoc)) =
                            parseDocumentFuel numApi (fuel - (subLines ++ tailLines).length) restChars
                              parentPath (rbParent (rbDotted finalSubLoc))
                          cases tl with
                          | nil =>
                            obtain ⟨_, hfin_eq, hparse0⟩ := htl_nil rfl
                            rw [hfin_eq, hparse0]
                            simp [List.length_append, Nat.sub_sub]
                          | cons _ _ =>
                            rw [htl_cons (by simp)]
                            simp [List.length_append, Nat.sub_sub]
              | _ => simp at hdl
    have hInl : ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
        (revRen : List String) (lines : List String),
        sizeOf remPlan ≤ n →
        noDupStringsBool (remPlan.map Prod.fst) = true →
        (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
        renderInlineEntries revRen origEntries remPlan = some lines →
        ∀ (root : List (String × Node)) (curPath : List String)
          (startLoc : List (String × Node)) (rb : List (String × Node) → List (String × Node)),
          AtLocalPath root curPath startLoc rb →
          (∀ p ∈ remPlan, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none) →
          ∀ (restChars : List Char) (fuel : Nat),
            fuel ≥ lines.length →
            ∃ finalLoc,
              (∀ p ∈ remPlan, p.2.isInlineScope = true →
                ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                  assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
              (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 finalLoc = assocLookupNode p.1 startLoc) ∧
              (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
              ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) curPath root =
              parseDocumentFuel numApi (fuel - lines.length) restChars curPath (rb finalLoc) := by
      intro origEntries remPlan revRen lines hsz hnd_rem hmem_rem hrie
        root curPath startLoc rb hAt hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderInlineEntries, Option.some.injEq] at hrie
        subst hrie
        refine ⟨startLoc, (fun p hp => by cases hp), (fun p hp => by cases hp), (fun _ _ => rfl), rfl, ?_⟩
        rw [atLocalPath_self hAt]
        simp [joinLines]
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderInlineEntries, bind, Option.bind] at hrie
        have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
        have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
          exact hnd_rem.2
        have hnot_tl : k ∉ tl.map Prod.fst := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
          intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
          rw [hc] at hnd_rem; cases hnd_rem.1
        have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
          fun p hp => hmem_rem p (by simp [hp])
        by_cases hsc : ep.isInlineScope = true
        · simp only [hsc, Bool.not_true] at hrie
          cases hlk : lookupKeyList k origEntries with
          | none => simp [hlk] at hrie
          | some v =>
            simp only [hlk] at hrie
            cases ep with
            | tableSection _ _ _ _ | aotSection _ _ _ => simp [EntryPlacement.isInlineScope] at hsc
            | direct ks vt comment =>
              cases hrk : renderKey k ks with
              | none => simp [hrk] at hrie
              | some rk =>
                cases hrv : renderValueInline v vt with
                | none => simp [hrk, hrv] at hrie
                | some rv =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrv, hrc] at hrie
                  | some rc =>
                    simp only [hrk, hrv, hrc] at hrie
                    cases htail_res : renderInlineEntries revRen origEntries tl with
                    | none => simp [htail_res] at hrie
                    | some tailLines =>
                      simp [htail_res] at hrie
                      subst hrie
                      let pairs := [(k, rk)]
                      have hpairs_ne : pairs ≠ [] := by simp [pairs]
                      have hpairs_keys : ∀ p ∈ pairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                        intro p hp; simp only [pairs, List.mem_singleton] at hp; rw [hp]; exact ⟨ks, hrk⟩
                      have hf1 : fuel ≥ 1 := by simp at hf; omega
                      obtain ⟨v', heqv, hline_cl, hstep⟩ :=
                        parseDocumentFuel_assign_step numApi hInt hFloat pairs hpairs_ne hpairs_keys
                          v vt rv hrv comment rc hrc curPath root
                          ((joinLines tailLines).toList ++ restChars) fuel hf1
                      let midLoc := assocSetNode k (valueToInlineNode v') startLoc
                      have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .direct ks vt comment) (by simp) hsc
                      have hins_loc : insertDottedEntries (curPath ++ [k]) startLoc [k] (valueToInlineNode v') = .ok midLoc := by
                        simp [insertDottedEntries, hnone_k, midLoc]
                      have hins_root : insertAtActivePath (curPath ++ pairs.map Prod.fst) root curPath (pairs.map Prod.fst)
                          (valueToInlineNode v') = .ok (rb midLoc) :=
                        atLocalPath_insertAtActivePath hAt (curPath ++ [k]) [k] (valueToInlineNode v') midLoc hins_loc
                      have hAt_mid : AtLocalPath (rb midLoc) curPath midLoc rb := atLocalPath_rebuild hAt midLoc
                      have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 midLoc = none := by
                        intro p hp hps
                        have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                        rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                        exact hfresh p (by simp [hp]) hps
                      have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
                        hnd_tl hmem_tl htail_res (rb midLoc) curPath midLoc rb hAt_mid hfresh_tl
                        restChars (fuel - 1) (by simp at hf; omega)
                      rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
                      refine ⟨finalLoc, ?_, ?_, ?_, ?_, ?_⟩
                      · intro p hp hps
                        simp only [List.mem_cons] at hp
                        rcases hp with rfl | hptl
                        · refine ⟨v, valueToInlineNode v', hlk, ?_, ?_⟩
                          · rw [htl_rest k hnot_tl]
                            simp [midLoc, assocLookupNode_assocSetNode]
                          · simpa [nodeToTomlValue_valueToInlineNode] using heqv
                        · exact htl_inl p hptl hps
                      · intro p hp hps
                        simp only [List.mem_cons] at hp
                        rcases hp with rfl | hptl
                        · rw [hsc] at hps; cases hps
                        · have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hptl, rfl⟩)
                          rw [htl_sec p hptl hps]
                          exact assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne
                      · intro q hq_not
                        have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                        have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                        rw [htl_rest q hnot_tl']
                        exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                      · have hline_eq2 : rk ++ " = " ++ rv ++ rc =
                            joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc := rfl
                        rw [hline_eq2, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append]
                        exact Bool.and_eq_true_iff.mpr ⟨joinLines_singleton_clean _ hline_cl, htl_cl⟩
                      · have hjoin_eq : (joinLines ((rk ++ " = " ++ rv ++ rc) :: tailLines)).toList ++ restChars =
                            (joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList ++
                              ('\n' :: ((joinLines tailLines).toList ++ restChars)) := by
                          simp [pairs, joinRenderedPath, joinLines, String.toList_append, List.cons_append, List.append_assoc]
                        rw [hjoin_eq, hstep (rb midLoc) hins_root, htl_parse]
                        simp [Nat.sub_sub, Nat.add_comm]
            | dotted ks subPlan =>
              cases v with
              | table sub =>
                by_cases hemp : sub.isEmpty = true
                · simp [hemp] at hrie
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrie
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hrie
                  | some rk =>
                    cases hsub_lines : renderDottedSub [rk] sub.toList subPlan with
                    | none => simp [hrk, hsub_lines] at hrie
                    | some subLines =>
                      simp only [hrk, hsub_lines] at hrie
                      cases htail_res : renderInlineEntries revRen origEntries tl with
                      | none => simp [htail_res] at hrie
                      | some tailLines =>
                        simp [htail_res] at hrie
                        subst hrie
                        simp only [renderDottedSub] at hsub_lines
                        split at hsub_lines
                        · cases hsub_lines
                        · rename_i hperm_neg
                          have hperm : isPlanPermutation sub.toList subPlan = true := by
                            cases h : isPlanPermutation sub.toList subPlan
                            · exfalso; exact hperm_neg (by simp [h])
                            · rfl
                          obtain ⟨_, hnd_sub, hmem_sub, hcov_sub⟩ := isPlanPermutation_props hperm
                          have hsub_ne_list : sub.toList ≠ [] := by
                            intro heq
                            have hnil : sub = #[] := Array.toList_eq_nil_iff.mp heq
                            subst hnil
                            exact absurd rfl hemp
                          have hsubPlan_ne : subPlan ≠ [] := by
                            intro hnil
                            cases hsub_ne_cons : sub.toList with
                            | nil => exact hsub_ne_list hsub_ne_cons
                            | cons hd_s _ =>
                              obtain ⟨ep0, hep0⟩ := hcov_sub hd_s.1 hd_s.2 (by simp [hsub_ne_cons, lookupKeyList])
                              rw [hnil] at hep0; cases hep0
                          have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                          have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .dotted ks subPlan) (by simp) hsc
                          let rbSubDot := fun newSub => assocSetNode k (.table .dotted newSub) startLoc
                          have hDot_sub : DottedWriteFocus startLoc ([(k, rk)].reverse.map Prod.fst) [] rbSubDot := by
                            simp only [List.reverse_singleton, List.map_cons, List.map_nil]
                            exact dottedWriteFocus_step (DottedWriteFocus.nil startLoc) k hnone_k
                          have hf_sub : fuel - subLines.length ≥ tailLines.length := by
                            simp only [List.length_append] at hf; omega
                          have hih_sub := hDot sub.toList subPlan [(k, rk)] subLines (by omega) (by simp)
                            (fun p hp => by simp only [List.mem_singleton] at hp; rw [hp]; exact ⟨ks, hrk⟩)
                            hnd_sub hmem_sub hsub_lines
                            root curPath startLoc rb [] rbSubDot hAt hDot_sub (fun _ _ => rfl)
                            ((joinLines tailLines).toList ++ restChars) fuel
                            (by simp only [List.length_append] at hf; omega)
                          rcases hih_sub with ⟨finalChildSub, hsub_match, hsub_rest, hsub_cl, _, hsub_parse⟩
                          let midLoc := assocSetNode k (.table .dotted finalChildSub) startLoc
                          have hAt_mid : AtLocalPath (rb midLoc) curPath midLoc rb := atLocalPath_rebuild hAt midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
                            hnd_tl hmem_tl htail_res (rb midLoc) curPath midLoc rb hAt_mid hfresh_tl
                            restChars (fuel - subLines.length) hf_sub
                          rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
                          refine ⟨finalLoc, ?_, ?_, ?_, ?_, ?_⟩
                          · intro p hp hps
                            simp only [List.mem_cons] at hp
                            rcases hp with rfl | hptl
                            · refine ⟨.table sub, .table .dotted finalChildSub, hlk, ?_, ?_⟩
                              · rw [htl_rest k hnot_tl]
                                simp [midLoc, assocLookupNode_assocSetNode]
                              · have heqv_sub := entriesToTomlList_of_plan_match sub.toList subPlan hperm finalChildSub hsub_match hsub_rest
                                simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                            · exact htl_inl p hptl hps
                          · intro p hp hps
                            simp only [List.mem_cons] at hp
                            rcases hp with rfl | hptl
                            · rw [hsc] at hps; cases hps
                            · have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hptl, rfl⟩)
                              rw [htl_sec p hptl hps]
                              exact assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne
                          · intro q hq_not
                            have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                            have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                            rw [htl_rest q hnot_tl']
                            exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                          · rw [joinLines_append, String.toList_append, List.all_append]
                            exact Bool.and_eq_true_iff.mpr ⟨hsub_cl, htl_cl⟩
                          · rw [joinLines_append, String.toList_append, List.append_assoc, hsub_parse hsubPlan_ne]
                            change parseDocumentFuel numApi (fuel - subLines.length)
                                ((joinLines tailLines).toList ++ restChars) curPath (rb midLoc) = _
                            rw [htl_parse]
                            simp [List.length_append, Nat.sub_sub]
              | _ => cases hrie
        · have hsc_false : ep.isInlineScope = false := by
            cases h : ep.isInlineScope
            · rfl
            · exact absurd h hsc
          simp only [hsc_false, Bool.not_false, ↓reduceIte] at hrie
          cases htail_res : renderInlineEntries revRen origEntries tl with
          | none => simp [htail_res] at hrie
          | some tailLines =>
            simp only [htail_res, Option.some.injEq, List.nil_append] at hrie
            subst hrie
            have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none :=
              fun p hp hps => hfresh p (by simp [hp]) hps
            have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
              hnd_tl hmem_tl htail_res root curPath startLoc rb hAt hfresh_tl restChars fuel hf
            rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
            refine ⟨finalLoc, ?_, ?_, ?_, htl_cl, htl_parse⟩
            · intro p hp hps
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hptl
              · rw [hsc_false] at hps; cases hps
              · exact htl_inl p hptl hps
            · intro p hp hps
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hptl
              · exact htl_rest k hnot_tl
              · exact htl_sec p hptl hps
            · intro q hq_not
              have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
              exact htl_rest q hnot_tl'
    have hAot : ∀ (elemPlans : List (List (String × EntryPlacement))) (xs : List TomlValue)
        (pathPairs : List (String × String)) (k rk : String) (rc : String) (lines : List String),
        sizeOf elemPlans ≤ n →
        (∃ ks, renderKey k ks = some rk) →
        (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
        (∃ comment, renderCommentSuffix comment = some rc) →
        renderAotElems (rk :: pathPairs.reverse.map Prod.snd) rc xs elemPlans = some lines →
        ∀ (root : List (String × Node)) (parentLoc : List (String × Node))
          (rbParent : List (String × Node) → List (String × Node))
          (prevElems : List (List (String × Node))) (startActivePath : List String),
          AtHeaderFocus root (pathPairs.map Prod.fst) parentLoc rbParent →
          ((prevElems = [] ∧ assocLookupNode k parentLoc = none) ∨
           (prevElems ≠ [] ∧ assocLookupNode k parentLoc = some (.aot prevElems))) →
          ∀ (restChars : List Char) (fuel : Nat),
            fuel ≥ lines.length →
            ∃ finalElems endActivePath,
              (xs = [] → finalElems = prevElems ∧ lines = [] ∧ endActivePath = startActivePath) ∧
              (xs ≠ [] → lines ≠ [] ∧
                ∃ tailElems, finalElems = prevElems ++ tailElems ∧ tailElems ≠ [] ∧
                  TomlListEquiv xs (aotElemsToToml tailElems) ∧
                  AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                    (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent) ∧
              ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
              (xs ≠ [] →
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath
                  (rbParent (assocSetNode k (.aot finalElems) parentLoc))) := by
      intro elemPlans xs pathPairs k rk rc lines hsz hk hpath hrc_ex hrae
        root parentLoc rbParent prevElems startActivePath hFocus hprev restChars fuel hf
      rcases hrc_ex with ⟨comment, hrc⟩
      cases xs with
      | nil =>
        cases elemPlans with
        | cons _ _ => simp [renderAotElems] at hrae
        | nil =>
          simp only [renderAotElems, Option.some.injEq] at hrae
          subst hrae
          refine ⟨prevElems, startActivePath, fun _ => ⟨rfl, rfl, rfl⟩, fun hne => absurd rfl hne, rfl, fun hne => absurd rfl hne⟩
      | cons elemVal xs' =>
        cases elemPlans with
        | nil => simp [renderAotElems] at hrae
        | cons ep eps =>
          cases elemVal with
          | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
            simp [renderAotElems] at hrae
          | table elem =>
            simp only [renderAotElems, bind, Option.bind] at hrae
            cases hbody : renderTablePlan (rk :: (pathPairs.map Prod.snd).reverse) elem.toList ep with
            | none =>
              rw [← List.map_reverse] at hbody
              simp only [List.map_reverse] at hrae
              rw [← List.map_reverse] at hrae
              simp only [hbody] at hrae; cases hrae
            | some bodyLines =>
              cases htail : renderAotElems (rk :: (pathPairs.map Prod.snd).reverse) rc xs' eps with
              | none =>
                rw [← List.map_reverse] at hbody htail
                simp only [List.map_reverse] at hrae
                rw [← List.map_reverse] at hrae
                simp only [hbody, htail] at hrae; cases hrae
              | some tailLines =>
                rw [← List.map_reverse] at hbody htail
                simp only [List.map_reverse] at hrae
                rw [← List.map_reverse] at hrae
                simp only [hbody, htail, Option.some.injEq] at hrae
                subst hrae
                let nextPairs := pathPairs ++ [(k, rk)]
                have hnext_ne : nextPairs ≠ [] := by simp [nextPairs]
                have hnext_keys : ∀ p ∈ nextPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                  intro p hp
                  simp only [nextPairs, List.mem_append, List.mem_singleton] at hp
                  rcases hp with h | h
                  · exact hpath p h
                  · rw [h]; exact hk
                have hnext_fst : nextPairs.map Prod.fst = pathPairs.map Prod.fst ++ [k] := by
                  simp [nextPairs, List.map_append]
                have hnext_rev : nextPairs.reverse.map Prod.snd = rk :: pathPairs.reverse.map Prod.snd := by
                  simp [nextPairs]
                let elemsMid := prevElems ++ [[]]
                let midParentLoc := assocSetNode k (.aot elemsMid) parentLoc
                have happ_loc : applyAotHeader (nextPairs.map Prod.fst) parentLoc [k] = .ok midParentLoc := by
                  rcases hprev with ⟨rfl, hnone_k⟩ | ⟨_, hsome_k⟩
                  · simp [applyAotHeader, hnone_k, midParentLoc, elemsMid]
                  · simp [applyAotHeader, hsome_k, midParentLoc, elemsMid]
                have happ_root : applyAotHeader (nextPairs.map Prod.fst) root (nextPairs.map Prod.fst) = .ok (rbParent midParentLoc) := by
                  have h := atHeaderFocus_applyAotHeader hFocus (nextPairs.map Prod.fst) [k] (by simp) midParentLoc happ_loc
                  rwa [← hnext_fst] at h
                have hf1 : fuel ≥ 1 := by simp at hf; omega
                obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                  parseDocumentFuel_aot_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                    startActivePath root (rbParent midParentLoc) happ_root
                    ((joinLines (bodyLines ++ tailLines)).toList ++ restChars) fuel hf1
                have hhdr_eq : "[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc =
                    "[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc := by
                  rw [← hnext_rev]; simp
                let rbElem := fun newElem => rbParent (assocSetNode k (.aot (prevElems ++ [newElem])) parentLoc)
                have hAt_midParent : AtLocalPath (rbParent midParentLoc) (pathPairs.map Prod.fst) midParentLoc rbParent :=
                  atHeaderFocus_step hFocus midParentLoc
                have hlk_mid : assocLookupNode k midParentLoc = some (.aot elemsMid) := by
                  simp [midParentLoc, assocLookupNode_assocSetNode]
                have hAt_elem0 : AtLocalPath (rbParent midParentLoc) (nextPairs.map Prod.fst) [] rbElem := by
                  rw [hnext_fst]
                  have hstep := atLocalPath_stepAot hAt_midParent k elemsMid [] (by simp [elemsMid]) (getLast?_append_singleton prevElems []) hlk_mid
                  have hrb_eq : (fun nl => rbParent (assocSetNode k (.aot (elemsMid.dropLast ++ [nl])) midParentLoc)) = rbElem := by
                    funext nl
                    simp only [elemsMid, dropLast_append_singleton, midParentLoc, assocSetNode_idem, rbElem]
                  rwa [hrb_eq] at hstep
                have hsz_ep : sizeOf ep + 1 < n := by
                  cases eps <;> simp +arith at hsz <;> omega
                have hsz_eps : sizeOf eps < n := by simp +arith at hsz; omega
                have hih_ep := (ih (sizeOf ep + 1) hsz_ep).2.2.2.2 elem.toList ep nextPairs bodyLines (Nat.le_refl _) hnext_keys
                  (by rw [hnext_rev]; exact hbody) (rbParent midParentLoc) [] rbElem hAt_elem0 rfl
                  ((joinLines tailLines).toList ++ restChars) (fuel - 1) (by simp only [List.length_cons, List.length_append] at hf; omega)
                rcases hih_ep with ⟨finalElem, midActivePath, heqv_elem, hAt_finalElem, hbody_cl, hbody_parse⟩
                let parentLoc' := assocSetNode k (.aot (prevElems ++ [finalElem])) parentLoc
                have hAt_parent' : AtLocalPath (rbParent parentLoc') (pathPairs.map Prod.fst) parentLoc' rbParent :=
                  atHeaderFocus_step hFocus parentLoc'
                have hlk_parent' : assocLookupNode k parentLoc' = some (.aot (prevElems ++ [finalElem])) := by
                  simp [parentLoc', assocLookupNode_assocSetNode]
                have hih_tail := (ih (sizeOf eps) hsz_eps).2.2.1 eps xs' pathPairs k rk rc tailLines (Nat.le_refl _)
                  hk hpath ⟨comment, hrc⟩ htail (rbParent parentLoc') parentLoc' rbParent (prevElems ++ [finalElem])
                  midActivePath (AtHeaderFocus.exact hAt_parent') (Or.inr ⟨by simp, hlk_parent'⟩)
                  restChars (fuel - 1 - bodyLines.length) (by simp only [List.length_cons, List.length_append] at hf; omega)
                rcases hih_tail with ⟨finalElems, endActivePath, hxs_nil, hxs_cons, htail_cl, htail_parse⟩
                have hcl_all : ((joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                    bodyLines ++ tailLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                  rw [List.cons_append, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append,
                    joinLines_append, String.toList_append, List.all_append]
                  have h1 : ((joinLines ["[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc]).toList.all
                      fun c => !isDisallowedControl c && c != '\r') = true := by
                    rw [hhdr_eq]
                    exact joinLines_singleton_clean _ hhdr_cl
                  exact Bool.and_eq_true_iff.mpr ⟨h1, Bool.and_eq_true_iff.mpr ⟨hbody_cl, htail_cl⟩⟩
                cases xs' with
                | nil =>
                  obtain ⟨rfl, rfl, hact_eq⟩ := hxs_nil rfl
                  refine ⟨prevElems ++ [finalElem], endActivePath, (fun hne => by cases hne), ?_, hcl_all, ?_⟩
                  · intro _
                    refine ⟨by simp, [finalElem], rfl, by simp, ?_, hAt_parent'⟩
                    simpa [aotElemsToToml, TomlListEquiv, TomlEquiv] using heqv_elem
                  · intro _
                    have hjoin_eq : (joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                        bodyLines ++ [])).toList ++ restChars =
                        ("[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc).toList ++
                          ('\n' :: ((joinLines (bodyLines ++ [])).toList ++ restChars)) := by
                      rw [hhdr_eq]; simp [List.cons_append, joinLines, String.toList_append, List.append_assoc]
                    rw [hjoin_eq, hhdr_parse]
                    simp only [List.append_nil, hact_eq]
                    simpa [joinLines, List.append_nil, rbElem, parentLoc', Nat.sub_sub, Nat.add_comm] using hbody_parse
                | cons _ _ =>
                  obtain ⟨_, tailElems2, hfin_eq, _, heqv_tail, _⟩ := hxs_cons (by simp)
                  have htail_eq2 : finalElems = prevElems ++ (finalElem :: tailElems2) := by
                    rw [hfin_eq, List.append_assoc]; rfl
                  have hAt_final : AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                      (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent :=
                    atHeaderFocus_step hFocus (assocSetNode k (.aot finalElems) parentLoc)
                  have hrb_idem : rbParent (assocSetNode k (.aot finalElems) parentLoc') =
                      rbParent (assocSetNode k (.aot finalElems) parentLoc) := by
                    simp only [parentLoc', assocSetNode_idem]
                  refine ⟨finalElems, endActivePath, (fun hne => by cases hne), ?_, hcl_all, ?_⟩
                  · intro _
                    refine ⟨by simp, finalElem :: tailElems2, htail_eq2, by simp, ?_, hAt_final⟩
                    simp only [aotElemsToToml, TomlListEquiv, TomlEquiv]
                    exact ⟨heqv_elem, heqv_tail⟩
                  · intro _
                    have hjoin_eq : (joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                        bodyLines ++ tailLines)).toList ++ restChars =
                        ("[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc).toList ++
                          ('\n' :: ((joinLines (bodyLines ++ tailLines)).toList ++ restChars)) := by
                      rw [hhdr_eq]; simp [List.cons_append, joinLines, String.toList_append, List.append_assoc]
                    rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse]
                    rw [htail_parse (by simp), hrb_idem]
                    rw [show fuel - 1 - bodyLines.length - tailLines.length =
                        fuel - (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) :: bodyLines ++ tailLines).length by
                      simp only [List.length_cons, List.length_append]; omega]
    have hSec : ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
        (pathPairs : List (String × String)) (lines : List String),
        sizeOf remPlan ≤ n →
        (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
        noDupStringsBool (remPlan.map Prod.fst) = true →
        (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
        renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries remPlan = some lines →
        ∀ (root : List (String × Node)) (startLoc : List (String × Node))
          (rb : List (String × Node) → List (String × Node)) (startActivePath : List String),
          AtHeaderFocus root (pathPairs.map Prod.fst) startLoc rb →
          (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none) →
          ∀ (restChars : List Char) (fuel : Nat),
            fuel ≥ lines.length →
            ∃ finalLoc endActivePath,
              (remPlan.any (fun p => !p.2.isInlineScope) = false →
                lines = [] ∧ finalLoc = startLoc ∧ endActivePath = startActivePath ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath root) ∧
              (remPlan.any (fun p => !p.2.isInlineScope) = true →
                lines ≠ [] ∧
                (∀ p ∈ remPlan, p.2.isInlineScope = false →
                  ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                    assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                (∀ q, (∀ p ∈ remPlan, p.2.isInlineScope = false → q ≠ p.1) →
                  assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
                AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) ∧
              ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      intro origEntries remPlan pathPairs lines hsz hpath hnd_rem hmem_rem hrse
        root startLoc rb startActivePath hFocus hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderSectionEntries, Option.some.injEq] at hrse
        subst hrse
        exact ⟨startLoc, startActivePath, fun _ => ⟨rfl, rfl, rfl, by simp [joinLines]⟩, fun h => by simp at h, rfl⟩
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderSectionEntries, bind, Option.bind] at hrse
        have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
        have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
          exact hnd_rem.2
        have hnot_tl : k ∉ tl.map Prod.fst := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
          intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
          rw [hc] at hnd_rem; cases hnd_rem.1
        have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
          fun p hp => hmem_rem p (by simp [hp])
        by_cases hsc : ep.isInlineScope = true
        · simp only [hsc, ↓reduceIte] at hrse
          cases htail_res : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
          | none =>
            rw [← List.map_reverse] at htail_res
            simp only [List.map_reverse] at hrse
            rw [← List.map_reverse] at hrse
            simp only [htail_res] at hrse
            cases hrse
          | some tailLines =>
            rw [← List.map_reverse] at htail_res
            simp only [List.map_reverse] at hrse
            rw [← List.map_reverse] at hrse
            simp only [htail_res, Option.some.injEq] at hrse
            subst hrse
            have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none :=
              fun p hp hps => hfresh p (by simp [hp]) hps
            have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
              hpath hnd_tl hmem_tl htail_res root startLoc rb startActivePath hFocus hfresh_tl restChars fuel hf
            rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
            refine ⟨finalLoc, endActivePath, ?_, ?_, htl_cl⟩
            · intro hnone
              have hnone_tl : tl.any (fun p => !p.2.isInlineScope) = false := by
                simpa [hsc] using hnone
              exact htl_false hnone_tl
            · intro hsome
              have hsome_tl : tl.any (fun p => !p.2.isInlineScope) = true := by
                simpa [hsc] using hsome
              obtain ⟨htl_ne, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true hsome_tl
              refine ⟨htl_ne, ?_, ?_, htl_At, htl_parse⟩
              · intro p hp hps
                simp only [List.mem_cons] at hp
                rcases hp with rfl | hptl
                · rw [hsc] at hps; cases hps
                · exact htl_match p hptl hps
              · intro q hq
                exact htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)
        · have hsc_false : ep.isInlineScope = false := by
            cases h : ep.isInlineScope
            · rfl
            · exact absurd h hsc
          simp only [hsc_false, Bool.false_eq_true, ↓reduceIte] at hrse
          cases hlk : lookupKeyList k origEntries with
          | none => simp [hlk] at hrse
          | some v =>
            simp only [hlk] at hrse
            cases ep with
            | direct _ _ _ | dotted _ _ => simp [EntryPlacement.isInlineScope] at hsc_false
            | tableSection ks subtableFirst subPlan comment =>
              cases v with
              | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
                simp at hrse
              | table sub =>
                cases hrk : renderKey k ks with
                | none => simp [hrk] at hrse
                | some rk =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrc] at hrse
                  | some rc =>
                    simp only [hrk, hrc] at hrse
                    let nextPairs := pathPairs ++ [(k, rk)]
                    have hnext_ne : nextPairs ≠ [] := by simp [nextPairs]
                    have hnext_keys : ∀ p ∈ nextPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                      intro p hp
                      simp only [nextPairs, List.mem_append, List.mem_singleton] at hp
                      rcases hp with h | h
                      · exact hpath p h
                      · rw [h]; exact ⟨ks, hrk⟩
                    have hnext_fst : nextPairs.map Prod.fst = pathPairs.map Prod.fst ++ [k] := by
                      simp [nextPairs, List.map_append]
                    have hnext_rev : nextPairs.reverse.map Prod.snd = rk :: pathPairs.reverse.map Prod.snd := by
                      simp [nextPairs]
                    have hhdr_eq : "[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc =
                        "[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc := by
                      rw [← hnext_rev]; simp
                    have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .tableSection ks subtableFirst subPlan comment) (by simp) hsc_false
                    cases subtableFirst with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte] at hrse
                      cases hbody : renderTablePlan (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                      | none =>
                        rw [← List.map_reverse] at hbody
                        simp only [List.map_reverse] at hrse
                        rw [← List.map_reverse] at hrse
                        simp only [hbody] at hrse
                        cases hrse
                      | some bodyLines =>
                        cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                        | none =>
                          rw [← List.map_reverse] at hbody htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hbody, htail] at hrse
                          cases hrse
                        | some tailLines =>
                          rw [← List.map_reverse] at hbody htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hbody, htail, Option.some.injEq] at hrse
                          subst hrse
                          let midParentLoc := assocSetNode k (.table .explicit []) startLoc
                          have happ_loc : applyTableHeader (nextPairs.map Prod.fst) startLoc [k] = .ok midParentLoc := by
                            simp [applyTableHeader, hnone_k, midParentLoc]
                          have happ_root : applyTableHeader (nextPairs.map Prod.fst) root (nextPairs.map Prod.fst) = .ok (rb midParentLoc) := by
                            have h := atHeaderFocus_applyTableHeader hFocus (nextPairs.map Prod.fst) [k] (by simp) midParentLoc happ_loc
                            rwa [← hnext_fst] at h
                          have hf1 : fuel ≥ 1 := by simp at hf; omega
                          obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                            parseDocumentFuel_table_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                              startActivePath root (rb midParentLoc) happ_root
                              ((joinLines (bodyLines ++ tailLines)).toList ++ restChars) fuel hf1
                          let rbSub := fun newSub => rb (assocSetNode k (.table .explicit newSub) startLoc)
                          have hAt_midParent : AtLocalPath (rb midParentLoc) (pathPairs.map Prod.fst) midParentLoc rb :=
                            atHeaderFocus_step hFocus midParentLoc
                          have hlk_mid : assocLookupNode k midParentLoc = some (.table .explicit []) := by
                            simp [midParentLoc, assocLookupNode_assocSetNode]
                          have hAt_sub0 : AtLocalPath (rb midParentLoc) (nextPairs.map Prod.fst) [] rbSub := by
                            have hrb_eq : (fun newSub => rb (assocSetNode k (.table .explicit newSub) midParentLoc)) = rbSub := by
                              funext newSub; simp [rbSub, midParentLoc, assocSetNode_idem]
                            rw [hnext_fst, ← hrb_eq]
                            exact atLocalPath_stepTable hAt_midParent k .explicit [] (by decide) hlk_mid
                          have hsz_sub : sizeOf subPlan + 1 < n := by simp +arith at hsz; omega
                          have hih_sub := (ih (sizeOf subPlan + 1) hsz_sub).2.2.2.2 sub.toList subPlan nextPairs bodyLines (Nat.le_refl _)
                            hnext_keys (by rw [hnext_rev]; exact hbody) (rb midParentLoc) [] rbSub hAt_sub0 rfl
                            ((joinLines tailLines).toList ++ restChars) (fuel - 1) (by simp only [List.length_cons, List.length_append] at hf; omega)
                          rcases hih_sub with ⟨finalSubLoc, midActivePath, heqv_sub, _, hbody_cl, hbody_parse⟩
                          let midLoc := assocSetNode k (.table .explicit finalSubLoc) startLoc
                          have hAt_midLoc : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
                            atHeaderFocus_step hFocus midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                            hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb midActivePath (AtHeaderFocus.exact hAt_midLoc) hfresh_tl
                            restChars (fuel - 1 - bodyLines.length) (by simp only [List.length_cons, List.length_append] at hf; omega)
                          rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                          have hcl_all : ((joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines)).toList.all
                              fun c => !isDisallowedControl c && c != '\r') = true := by
                            rw [List.cons_append, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append,
                              joinLines_append, String.toList_append, List.all_append]
                            have h1 : ((joinLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]).toList.all
                                fun c => !isDisallowedControl c && c != '\r') = true := by
                              rw [hhdr_eq]
                              exact joinLines_singleton_clean _ hhdr_cl
                            exact Bool.and_eq_true_iff.mpr ⟨h1, Bool.and_eq_true_iff.mpr ⟨hbody_cl, htl_cl⟩⟩
                          by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                          · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                            have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                              htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                            refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp, ?_, ?_, htl_At, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                              · exact htl_match p hptl hps
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .tableSection ks false subPlan comment) (by simp) hsc_false
                              rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · have hjoin_eq : (joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines)).toList ++ restChars =
                                  ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                    ('\n' :: ((joinLines (bodyLines ++ tailLines)).toList ++ restChars)) := by
                                rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                              rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse, htl_parse]
                              rw [show fuel - 1 - bodyLines.length - tailLines.length =
                                  fuel - ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines).length by
                                simp only [List.length_cons, List.length_append]; omega]
                          · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                              cases h : tl.any (fun p => !p.2.isInlineScope)
                              · rfl
                              · exact absurd h htl_any
                            obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                            refine ⟨midLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp, ?_, ?_, hAt_midLoc, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                · simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                              · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                rw [htl_any_f] at this; cases this
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .tableSection ks false subPlan comment) (by simp) hsc_false
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · have hjoin_eq : (joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ [])).toList ++ restChars =
                                  ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                    ('\n' :: ((joinLines (bodyLines ++ [])).toList ++ restChars)) := by
                                rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                              rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse, htl_parse0]
                              rw [show fuel - 1 - bodyLines.length - ([] : List String).length =
                                  fuel - ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ []).length by
                                simp only [List.length_cons, List.length_append, List.length_nil]; omega]
                    | true =>
                      simp only [↓reduceIte] at hrse
                      split at hrse
                      · cases hrse
                      · split at hrse
                        · cases hrse
                        · rename_i hperm_neg hall_neg
                          have hperm : isPlanPermutation sub.toList subPlan = true := by
                            cases h : isPlanPermutation sub.toList subPlan with
                            | true => rfl
                            | false => exfalso; exact hperm_neg (by simp [h])
                          have hany_sub : subPlan.any (fun p => !p.2.isInlineScope) = true := by
                            cases h : subPlan.any (fun p => !p.2.isInlineScope) with
                            | true => rfl
                            | false =>
                              exfalso; apply hall_neg
                              rw [List.any_eq_false] at h
                              simp only [List.all_eq_true]
                              intro p hp
                              have hnp := h p hp
                              cases hpi : p.2.isInlineScope with
                              | true => rfl
                              | false => exfalso; exact hnp (by simp [hpi])
                          obtain ⟨_, hnd_sub, hmem_sub, _⟩ := isPlanPermutation_props hperm
                          cases hsec_sub : renderSectionEntries (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                          | none =>
                            rw [← List.map_reverse] at hsec_sub
                            simp only [List.map_reverse] at hrse
                            rw [← List.map_reverse] at hrse
                            simp only [hsec_sub] at hrse
                            cases hrse
                          | some secLines =>
                            cases hinl_sub : renderInlineEntries (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                            | none =>
                              rw [← List.map_reverse] at hsec_sub hinl_sub
                              simp only [List.map_reverse] at hrse
                              rw [← List.map_reverse] at hrse
                              simp only [hsec_sub, hinl_sub] at hrse
                              cases hrse
                            | some inlLines =>
                              cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                              | none =>
                                rw [← List.map_reverse] at hsec_sub hinl_sub htail
                                simp only [List.map_reverse] at hrse
                                rw [← List.map_reverse] at hrse
                                simp only [hsec_sub, hinl_sub, htail] at hrse
                                cases hrse
                              | some tailLines =>
                                rw [← List.map_reverse] at hsec_sub hinl_sub htail
                                simp only [List.map_reverse] at hrse
                                rw [← List.map_reverse] at hrse
                                simp only [hsec_sub, hinl_sub, htail, Option.some.injEq] at hrse
                                subst hrse
                                let rbImp := fun newSub => rb (assocSetNode k (.table .subtableImplicit newSub) startLoc)
                                have hFocus_sub : AtHeaderFocus root (nextPairs.map Prod.fst) [] rbImp := by
                                  rw [hnext_fst]
                                  exact AtHeaderFocus.implicitNone hFocus hnone_k
                                have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                                have hf_sec : fuel ≥ secLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_sec := (ih (sizeOf subPlan) hsz_sub).2.2.2.1 sub.toList subPlan nextPairs secLines
                                  (Nat.le_refl _) hnext_keys hnd_sub hmem_sub (by rw [hnext_rev]; exact hsec_sub)
                                  root [] rbImp startActivePath hFocus_sub (fun _ _ _ => rfl)
                                  ((joinLines (["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++
                                    inlLines ++ tailLines)).toList ++ restChars) fuel hf_sec
                                rcases hih_sec with ⟨midSubLoc, midActivePath1, _, hsec_true, hsec_cl⟩
                                obtain ⟨hsec_ne, hsec_match, hsec_pres, hAt_midSub, hsec_parse⟩ := hsec_true hany_sub
                                let midParentImp := assocSetNode k (.table .subtableImplicit midSubLoc) startLoc
                                let midParentExp := assocSetNode k (.table .explicit midSubLoc) startLoc
                                have happ_loc : applyTableHeader (nextPairs.map Prod.fst) midParentImp [k] = .ok midParentExp := by
                                  have hlk_imp : assocLookupNode k midParentImp = some (.table .subtableImplicit midSubLoc) := by
                                    simp [midParentImp, assocLookupNode_assocSetNode]
                                  simp [applyTableHeader, hlk_imp, midParentExp, midParentImp, assocSetNode_idem]
                                have hAt_imp : AtLocalPath (rbImp midSubLoc) (pathPairs.map Prod.fst) midParentImp rb :=
                                  atHeaderFocus_step hFocus midParentImp
                                have happ_root : applyTableHeader (nextPairs.map Prod.fst) (rbImp midSubLoc) (nextPairs.map Prod.fst) = .ok (rb midParentExp) := by
                                  have h := atLocalPath_applyTableHeader hAt_imp (nextPairs.map Prod.fst) [k] (by simp) midParentExp happ_loc
                                  rwa [← hnext_fst] at h
                                have hf_hdr : fuel - secLines.length ≥ 1 := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                                  parseDocumentFuel_table_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                                    midActivePath1 (rbImp midSubLoc) (rb midParentExp) happ_root
                                    ((joinLines (inlLines ++ tailLines)).toList ++ restChars) (fuel - secLines.length) hf_hdr
                                let rbExp := fun newSub => rb (assocSetNode k (.table .explicit newSub) startLoc)
                                have hAt_exp0 : AtLocalPath (rb midParentExp) (nextPairs.map Prod.fst) midSubLoc rbExp := by
                                  have hAt_exp_p : AtLocalPath (rb midParentExp) (pathPairs.map Prod.fst) midParentExp rb :=
                                    atHeaderFocus_step hFocus midParentExp
                                  have hlk_exp : assocLookupNode k midParentExp = some (.table .explicit midSubLoc) := by
                                    simp [midParentExp, assocLookupNode_assocSetNode]
                                  have hrb_eq : (fun newSub => rb (assocSetNode k (.table .explicit newSub) midParentExp)) = rbExp := by
                                    funext newSub; simp [rbExp, midParentExp, assocSetNode_idem]
                                  rw [hnext_fst, ← hrb_eq]
                                  exact atLocalPath_stepTable hAt_exp_p k .explicit midSubLoc (by decide) hlk_exp
                                have hfresh_inl : ∀ p ∈ subPlan, p.2.isInlineScope = true → assocLookupNode p.1 midSubLoc = none := by
                                  intro p hp hps
                                  have hq : ∀ p' ∈ subPlan, p'.2.isInlineScope = false → p.1 ≠ p'.1 :=
                                    fun p' hp' hps' => nodup_key_ne_of_scope subPlan hnd_sub p p' hp hp' hps hps'
                                  rw [hsec_pres p.1 hq]
                                  rfl
                                have hf_inl : fuel - secLines.length - 1 ≥ inlLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_inl := (ih (sizeOf subPlan) hsz_sub).2.1 sub.toList subPlan (rk :: pathPairs.reverse.map Prod.snd) inlLines
                                  (Nat.le_refl _) hnd_sub hmem_sub hinl_sub (rb midParentExp) (nextPairs.map Prod.fst) midSubLoc rbExp
                                  hAt_exp0 hfresh_inl ((joinLines tailLines).toList ++ restChars) (fuel - secLines.length - 1) hf_inl
                                rcases hih_inl with ⟨finalSubLoc, hinl_match, hinl_sec, hinl_rest, hinl_cl, hinl_parse⟩
                                have heqv_sub : TomlTableEquivList sub.toList (entriesToTomlList finalSubLoc) := by
                                  apply entriesToTomlList_of_plan_match sub.toList subPlan hperm finalSubLoc
                                  · intro p hp
                                    by_cases hp_in : p.2.isInlineScope = true
                                    · exact hinl_match p hp hp_in
                                    · have hp_f : p.2.isInlineScope = false := by
                                        cases h : p.2.isInlineScope with
                                        | false => rfl
                                        | true => exact absurd h hp_in
                                      obtain ⟨v_s, nd_s, hv_s, hnd_s, heqv_s⟩ := hsec_match p hp hp_f
                                      refine ⟨v_s, nd_s, hv_s, ?_, heqv_s⟩
                                      rw [hinl_sec p hp hp_f]
                                      exact hnd_s
                                  · intro q hq_not
                                    rw [hinl_rest q hq_not]
                                    rw [hsec_pres q (fun p hp _ => fun heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
                                    rfl
                                let midLoc := assocSetNode k (.table .explicit finalSubLoc) startLoc
                                have hAt_midLoc : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
                                  atHeaderFocus_step hFocus midLoc
                                have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                                  intro p hp hps
                                  have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                                  rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                                  exact hfresh p (by simp [hp]) hps
                                have hf_tail : fuel - secLines.length - 1 - inlLines.length ≥ tailLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                                  hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb (nextPairs.map Prod.fst)
                                  (AtHeaderFocus.exact hAt_midLoc) hfresh_tl restChars (fuel - secLines.length - 1 - inlLines.length) hf_tail
                                rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                                have hcl_all : ((joinLines ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ tailLines)).toList.all
                                    fun c => !isDisallowedControl c && c != '\r') = true := by
                                  rw [joinLines_append, joinLines_append, joinLines_append, String.toList_append, String.toList_append, String.toList_append,
                                    List.all_append, List.all_append, List.all_append]
                                  have h1hdr : ((joinLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]).toList.all
                                      fun c => !isDisallowedControl c && c != '\r') = true := by
                                    rw [hhdr_eq]
                                    exact joinLines_singleton_clean _ hhdr_cl
                                  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hsec_cl, h1hdr⟩, hinl_cl⟩, htl_cl⟩
                                have hparse_sub : parseDocumentFuel numApi fuel
                                    ((joinLines (((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]) ++ inlLines) ++ tailLines)).toList ++ restChars)
                                    startActivePath root =
                                    parseDocumentFuel numApi (fuel - secLines.length - 1 - inlLines.length)
                                      ((joinLines tailLines).toList ++ restChars) (nextPairs.map Prod.fst) (rb midLoc) := by
                                  rw [List.append_assoc secLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] inlLines,
                                    List.append_assoc secLines _ tailLines, joinLines_append, String.toList_append, List.append_assoc, hsec_parse]
                                  simp only [List.singleton_append]
                                  rw [List.cons_append]
                                  have hmid2 : (joinLines (("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: (inlLines ++ tailLines))).toList ++ restChars =
                                      ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                        ('\n' :: ((joinLines (inlLines ++ tailLines)).toList ++ restChars)) := by
                                    rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                                  rw [hmid2, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hinl_parse]
                                by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                                · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                                  have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                                    htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                                  refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                                  intro _
                                  refine ⟨by simp [hsec_ne], ?_, ?_, htl_At, ?_⟩
                                  · intro p hp hps
                                    simp only [List.mem_cons] at hp
                                    rcases hp with rfl | hptl
                                    · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                      · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                      · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                                    · exact htl_match p hptl hps
                                  · intro q hq
                                    have hne_k : q ≠ k := hq (k, .tableSection ks true subPlan comment) (by simp) hsc_false
                                    rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                                    exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                                  · rw [hparse_sub, htl_parse]
                                    rw [show fuel - secLines.length - 1 - inlLines.length - tailLines.length =
                                        fuel - ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ tailLines).length by
                                      simp only [List.length_append, List.length_singleton]; omega]
                                · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                                    cases h : tl.any (fun p => !p.2.isInlineScope)
                                    · rfl
                                    · exact absurd h htl_any
                                  obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                                  refine ⟨midLoc, nextPairs.map Prod.fst, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                                  intro _
                                  refine ⟨by simp [hsec_ne], ?_, ?_, hAt_midLoc, ?_⟩
                                  · intro p hp hps
                                    simp only [List.mem_cons] at hp
                                    rcases hp with rfl | hptl
                                    · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                      · simp [midLoc, assocLookupNode_assocSetNode]
                                      · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                                    · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                      rw [htl_any_f] at this; cases this
                                  · intro q hq
                                    have hne_k : q ≠ k := hq (k, .tableSection ks true subPlan comment) (by simp) hsc_false
                                    exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                                  · rw [hparse_sub, htl_parse0]
                                    rw [show fuel - secLines.length - 1 - inlLines.length - ([] : List String).length =
                                        fuel - ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ []).length by
                                      simp only [List.length_append, List.length_singleton, List.length_nil]; omega]
            | aotSection ks elemPlans comment =>
              cases v with
              | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | table _ =>
                simp at hrse
              | array xs =>
                by_cases hemp : xs.isEmpty = true
                · simp [hemp] at hrse
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrse
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hrse
                  | some rk =>
                    cases hrc : renderCommentSuffix comment with
                    | none => simp [hrk, hrc] at hrse
                    | some rc =>
                      cases haot : renderAotElems (rk :: (pathPairs.map Prod.snd).reverse) rc xs.toList elemPlans with
                      | none =>
                        rw [← List.map_reverse] at haot
                        simp only [List.map_reverse] at hrse
                        rw [← List.map_reverse] at hrse
                        simp only [hrk, hrc, haot] at hrse
                        cases hrse
                      | some aotLines =>
                        cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                        | none =>
                          rw [← List.map_reverse] at haot htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hrk, hrc, haot, htail] at hrse
                          cases hrse
                        | some tailLines =>
                          rw [← List.map_reverse] at haot htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hrk, hrc, haot, htail, Option.some.injEq] at hrse
                          subst hrse
                          have hxs_ne : xs.toList ≠ [] := by
                            intro heq
                            have hnil : xs = #[] := Array.toList_eq_nil_iff.mp heq
                            subst hnil
                            exact absurd rfl hemp
                          have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                          have hsz_ep : sizeOf elemPlans < n := by simp +arith at hsz; omega
                          have hf_aot : fuel ≥ aotLines.length := by simp only [List.length_append] at hf; omega
                          have hih_aot := (ih (sizeOf elemPlans) hsz_ep).2.2.1 elemPlans xs.toList pathPairs k rk rc aotLines
                            (Nat.le_refl _) ⟨ks, hrk⟩ hpath ⟨comment, hrc⟩ haot root startLoc rb [] startActivePath
                            hFocus (Or.inl ⟨rfl, hnone_k⟩) ((joinLines tailLines).toList ++ restChars) fuel hf_aot
                          rcases hih_aot with ⟨finalElems, midActivePath, _, haot_cons, haot_cl, haot_parse⟩
                          obtain ⟨haot_ne, tailElems, hfin_eq, htail_ne, heqv_aot, hAt_midLoc⟩ := haot_cons hxs_ne
                          rw [List.nil_append] at hfin_eq
                          let midLoc := assocSetNode k (.aot tailElems) startLoc
                          have hAt_midLoc' : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb := by
                            simpa [midLoc, ← hfin_eq] using hAt_midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hf_tail : fuel - aotLines.length ≥ tailLines.length := by
                            simp only [List.length_append] at hf; omega
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                            hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb midActivePath (AtHeaderFocus.exact hAt_midLoc')
                            hfresh_tl restChars (fuel - aotLines.length) hf_tail
                          rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                          have hcl_all : ((joinLines (aotLines ++ tailLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                            rw [joinLines_append, String.toList_append, List.all_append]
                            exact Bool.and_eq_true_iff.mpr ⟨haot_cl, htl_cl⟩
                          by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                          · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                            have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                              htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                            refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp [haot_ne], ?_, ?_, htl_At, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.array xs, .aot tailElems, hlk, ?_, ?_⟩
                                · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_aot
                              · exact htl_match p hptl hps
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                              rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · rw [joinLines_append, String.toList_append, List.append_assoc, haot_parse hxs_ne]
                              rw [show rb (assocSetNode k (.aot finalElems) startLoc) = rb midLoc by simp [midLoc, hfin_eq]]
                              rw [htl_parse]
                              simp [List.length_append, Nat.sub_sub]
                          · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                              cases h : tl.any (fun p => !p.2.isInlineScope)
                              · rfl
                              · exact absurd h htl_any
                            obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                            refine ⟨midLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp [haot_ne], ?_, ?_, hAt_midLoc', ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.array xs, .aot tailElems, hlk, ?_, ?_⟩
                                · simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_aot
                              · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                rw [htl_any_f] at this; cases this
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · rw [joinLines_append, String.toList_append, List.append_assoc, haot_parse hxs_ne]
                              rw [show rb (assocSetNode k (.aot finalElems) startLoc) = rb midLoc by simp [midLoc, hfin_eq]]
                              rw [htl_parse0]
                              rw [show fuel - aotLines.length - ([] : List String).length = fuel - (aotLines ++ []).length by
                                simp only [List.length_append, List.length_nil, Nat.add_zero, Nat.sub_zero]]
    have hPlan : ∀ (origEntries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
        (pathPairs : List (String × String)) (lines : List String),
        sizeOf plan + 1 ≤ n →
        (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
        renderTablePlan (pathPairs.reverse.map Prod.snd) origEntries plan = some lines →
        ∀ (root : List (String × Node)) (startLoc : List (String × Node))
          (rb : List (String × Node) → List (String × Node)),
          AtLocalPath root (pathPairs.map Prod.fst) startLoc rb →
          startLoc = [] →
          ∀ (restChars : List Char) (fuel : Nat),
            fuel ≥ lines.length →
            ∃ finalLoc endActivePath,
              TomlTableEquivList origEntries (entriesToTomlList finalLoc) ∧
              AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
              ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars)
                (pathPairs.map Prod.fst) root =
              parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc) := by
      intro origEntries plan pathPairs lines hsz hpath hrtp root startLoc rb hAt hstart restChars fuel hf
      subst hstart
      simp only [renderTablePlan] at hrtp
      split at hrtp
      · cases hrtp
      · rename_i hperm_neg
        have hperm : isPlanPermutation origEntries plan = true := by
          cases h : isPlanPermutation origEntries plan
          · exfalso; exact hperm_neg (by simp [h])
          · rfl
        obtain ⟨_, hnd_p, hmem_p, _⟩ := isPlanPermutation_props hperm
        simp only [bind, Option.bind] at hrtp
        cases hinl : renderInlineEntries (pathPairs.reverse.map Prod.snd) origEntries plan with
        | none =>
          simp only [hinl] at hrtp
          cases hrtp
        | some inlLines =>
          cases hsec : renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries plan with
          | none =>
            simp only [hinl, hsec] at hrtp
            cases hrtp
          | some secLines =>
            simp only [hinl, hsec, Option.some.injEq] at hrtp
            subst hrtp
            have hsz_lt : sizeOf plan < n := by omega
            have hf_inl : fuel ≥ inlLines.length := by simp only [List.length_append] at hf; omega
            have hih_inl := hInl origEntries plan (pathPairs.reverse.map Prod.snd) inlLines (Nat.le_of_lt hsz_lt)
              hnd_p hmem_p hinl root (pathPairs.map Prod.fst) [] rb hAt (fun _ _ _ => rfl)
              ((joinLines secLines).toList ++ restChars) fuel hf_inl
            rcases hih_inl with ⟨midLoc, hinl_match, hinl_sec, hinl_rest, hinl_cl, hinl_parse⟩
            have hAt_mid : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
              atLocalPath_rebuild hAt midLoc
            have hfresh_sec : ∀ p ∈ plan, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none :=
              fun p hp hps => by rw [hinl_sec p hp hps]; rfl
            have hf_sec : fuel - inlLines.length ≥ secLines.length := by
              simp only [List.length_append] at hf; omega
            have hih_sec := hSec origEntries plan pathPairs secLines (Nat.le_of_lt hsz_lt) hpath hnd_p hmem_p hsec
              (rb midLoc) midLoc rb (pathPairs.map Prod.fst) (AtHeaderFocus.exact hAt_mid) hfresh_sec
              restChars (fuel - inlLines.length) hf_sec
            rcases hih_sec with ⟨finalLoc, endActivePath, hsec_false, hsec_true, hsec_cl⟩
            have hcl_all : ((joinLines (inlLines ++ secLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              rw [joinLines_append, String.toList_append, List.all_append]
              exact Bool.and_eq_true_iff.mpr ⟨hinl_cl, hsec_cl⟩
            by_cases hany : plan.any (fun p => !p.2.isInlineScope) = true
            · obtain ⟨_, hsec_match, hsec_pres, hAt_fin, hsec_parse⟩ := hsec_true hany
              have heqv : TomlTableEquivList origEntries (entriesToTomlList finalLoc) := by
                apply entriesToTomlList_of_plan_match origEntries plan hperm finalLoc
                · intro p hp
                  by_cases hp_in : p.2.isInlineScope = true
                  · obtain ⟨v, nd, hv, hnd, heqv⟩ := hinl_match p hp hp_in
                    refine ⟨v, nd, hv, ?_, heqv⟩
                    have hq : ∀ p' ∈ plan, p'.2.isInlineScope = false → p.1 ≠ p'.1 :=
                      fun p' hp' hps' => nodup_key_ne_of_scope plan hnd_p p p' hp hp' hp_in hps'
                    rw [hsec_pres p.1 hq]
                    exact hnd
                  · exact hsec_match p hp (by
                      cases h : p.2.isInlineScope
                      · rfl
                      · exact absurd h hp_in)
                · intro q hq_not
                  rw [hsec_pres q (fun p hp _ heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
                  exact hinl_rest q hq_not
              refine ⟨finalLoc, endActivePath, heqv, hAt_fin, hcl_all, ?_⟩
              rw [joinLines_append, String.toList_append, List.append_assoc, hinl_parse, hsec_parse]
              simp [List.length_append, Nat.sub_sub]
            · have hany_f : plan.any (fun p => !p.2.isInlineScope) = false := by
                cases h : plan.any (fun p => !p.2.isInlineScope)
                · rfl
                · exact absurd h hany
              obtain ⟨_, rfl, rfl, hsec_parse0⟩ := hsec_false hany_f
              have heqv : TomlTableEquivList origEntries (entriesToTomlList finalLoc) := by
                apply entriesToTomlList_of_plan_match origEntries plan hperm finalLoc
                · intro p hp
                  have hp_in : p.2.isInlineScope = true := by
                    by_cases h : p.2.isInlineScope = true
                    · exact h
                    · have : plan.any (fun p => !p.2.isInlineScope) = true := List.any_eq_true.mpr ⟨p, hp, by simp [h]⟩
                      rw [hany_f] at this; cases this
                  exact hinl_match p hp hp_in
                · exact hinl_rest
              refine ⟨finalLoc, pathPairs.map Prod.fst, heqv, hAt_mid, hcl_all, ?_⟩
              rw [joinLines_append, String.toList_append, List.append_assoc, hinl_parse, hsec_parse0]
              simp [List.length_append, Nat.sub_sub]
    exact ⟨hDot, hInl, hAot, hSec, hPlan⟩

private theorem parseDocumentFuel_skipTrivia (numApi : NumParseApi) (f : Nat)
    (cs1 cs2 : List Char) (activePath : List String) (root : List (String × Node))
    (h : skipTriviaNewlines cs1 = skipTriviaNewlines cs2) :
    parseDocumentFuel numApi (f + 1) cs1 activePath root =
    parseDocumentFuel numApi (f + 1) cs2 activePath root := by
  unfold parseDocumentFuel
  rw [h]

/-- Any output accepted by `Model.render` parses back under `parseWithNum` to an equivalent `TomlTable` whenever integer and float models match. -/
theorem render_parse_roundTrip_model (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (doc : TomlTable) (tape : RenderTape) (out : String)
    (hrender : render doc tape = some out) :
    ∃ parsed, parseWithNum numApi out = .ok parsed ∧ TomlTableEquiv doc parsed := by
  simp only [render] at hrender
  split at hrender
  · cases hrender
  · rename_i hwf_neg
    simp only [bind, Option.bind] at hrender
    have hhdr_body : ∃ hdrLines bodyLines,
        ((hdrLines = [] ∧ tape.headerComment = none) ∨
         (∃ c, isSingleLineClean c = true ∧ tape.headerComment = some c ∧ hdrLines = ["#" ++ c])) ∧
        renderTablePlan [] doc.toList tape.entries = some bodyLines ∧
        out = String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n" := by
      cases hc : tape.headerComment with
      | none =>
        simp only [hc] at hrender
        cases hbody : renderTablePlan [] doc.toList tape.entries with
        | none => simp [hbody] at hrender
        | some bodyLines =>
          simp only [hbody, Option.some.injEq] at hrender
          exact ⟨[], bodyLines, Or.inl ⟨rfl, rfl⟩, rfl, hrender.symm⟩
      | some c =>
        simp only [hc] at hrender
        split at hrender
        · rename_i hc_clean
          cases hbody : renderTablePlan [] doc.toList tape.entries with
          | none => simp [hbody] at hrender
          | some bodyLines =>
            simp only [hbody, Option.some.injEq] at hrender
            exact ⟨["#" ++ c], bodyLines, Or.inr ⟨c, hc_clean, rfl, rfl⟩, rfl, hrender.symm⟩
        · cases hrender
    rcases hhdr_body with ⟨hdrLines, bodyLines, hhdr_cases, hbody, rfl⟩
    by_cases hall_empty : hdrLines ++ bodyLines = []
    · have hbody_e : bodyLines = [] := (List.append_eq_nil_iff.mp hall_empty).2
      have hplan := (renderPlan_props_strong numApi hInt hFloat (sizeOf tape.entries + 1)).2.2.2.2
        doc.toList tape.entries [] bodyLines (Nat.le_refl _) (fun _ h => by cases h)
        hbody [] [] id (AtLocalPath.nil []) rfl [] 1 (by simp [hbody_e])
      rcases hplan with ⟨finalLoc, _, heqv_list, _, _, hbody_parse⟩
      have hroot_eq : finalLoc = [] := by
        simp [hbody_e, joinLines, parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux] at hbody_parse
        exact hbody_parse
      have hnorm : normalizeChars 1 1 (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n").toList = .ok ['\n'] := by
        have hstr : (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n").toList = ['\n'] := by
          simp [hall_empty]
        rw [hstr]
        apply normalizeChars_clean
        decide
      have hp_doc : parseDocumentFuel numApi 2 ['\n'] [] [] = .ok [] := by
        simp [parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux]
      have hlen1 : (['\n'] : List Char).length + 1 = 2 := rfl
      refine ⟨(entriesToTomlList []).toArray, ?_, ?_⟩
      · simp only [parseWithNum, hnorm, bind, Except.bind]
        rw [hlen1, hp_doc]
      · rw [hroot_eq] at heqv_list
        simpa [TomlTableEquiv] using heqv_list
    · have hinter : String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n" = joinLines (hdrLines ++ bodyLines) :=
        intercalate_nl_append_nl (hdrLines ++ bodyLines) hall_empty
      let fullFuel := (joinLines (hdrLines ++ bodyLines)).toList.length + 1
      have hge_len : (joinLines (hdrLines ++ bodyLines)).toList.length ≥ bodyLines.length := by
        have h1 := joinLines_length_ge (hdrLines ++ bodyLines)
        simp only [List.length_append] at h1
        omega
      have hplan := (renderPlan_props_strong numApi hInt hFloat (sizeOf tape.entries + 1)).2.2.2.2
        doc.toList tape.entries [] bodyLines (Nat.le_refl _) (fun _ h => by cases h)
        hbody [] [] id (AtLocalPath.nil []) rfl [] fullFuel (by omega)
      rcases hplan with ⟨finalLoc, _, heqv_list, _, hbody_cl, hbody_parse⟩
      have hnorm_eq : normalizeChars 1 1 (joinLines (hdrLines ++ bodyLines)).toList =
          .ok (joinLines (hdrLines ++ bodyLines)).toList := by
        apply normalizeChars_clean
        rw [joinLines_append, String.toList_append, List.all_append]
        have hhdr_cl : ((joinLines hdrLines).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
          rcases hhdr_cases with ⟨rfl, _⟩ | ⟨c, hc_clean, _, rfl⟩
          · rfl
          · have hc' : (c.toList.all fun ch => !isDisallowedControl ch && ch != '\r') = true := by
              simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc_clean ⊢
              intro ch hch; exact ⟨(hc_clean ch hch).1.1, (hc_clean ch hch).2⟩
            simp [joinLines, List.all_append, hc', (by decide : isDisallowedControl '#' = false),
              (by decide : isDisallowedControl '\n' = false)]
        exact Bool.and_eq_true_iff.mpr ⟨hhdr_cl, hbody_cl⟩
      have hskip : skipTriviaNewlines (joinLines (hdrLines ++ bodyLines)).toList =
          skipTriviaNewlines (joinLines bodyLines).toList := by
        rcases hhdr_cases with ⟨rfl, _⟩ | ⟨c, hc_clean, _, rfl⟩
        · simp
        · simp only [List.cons_append, List.nil_append, joinLines]
          rw [String.toList_append]
          exact skipTriviaNewlines_comment_line c (joinLines bodyLines).toList hc_clean
      have hparse_body : parseDocumentFuel numApi fullFuel (joinLines bodyLines).toList [] [] = .ok finalLoc := by
        simpa [id, List.append_nil] using hbody_parse.trans (by
          have hpos : fullFuel - bodyLines.length ≥ 1 := by omega
          cases hd : fullFuel - bodyLines.length with
          | zero => omega
          | succ _ => simp [parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux])
      have hp_full : parseDocumentFuel numApi fullFuel (joinLines (hdrLines ++ bodyLines)).toList [] [] = .ok finalLoc := by
        rw [parseDocumentFuel_skipTrivia numApi (joinLines (hdrLines ++ bodyLines)).toList.length _ _ [] [] hskip]
        exact hparse_body
      refine ⟨(entriesToTomlList finalLoc).toArray, ?_, ?_⟩
      · simp only [parseWithNum, hinter, hnorm_eq, bind, Except.bind]
        rw [show (joinLines (hdrLines ++ bodyLines)).toList.length + 1 = fullFuel from rfl, hp_full]
      · simpa [TomlTableEquiv] using heqv_list

private theorem joinRenderedPath_eq_intercalate (xs : List String) :
    joinRenderedPath xs = String.intercalate "." xs := by
  match xs with
  | [] => simp [joinRenderedPath, String.intercalate_nil]
  | [k] => simp [joinRenderedPath, String.intercalate_singleton]
  | k :: a :: rest =>
    simp [joinRenderedPath, joinRenderedPath_eq_intercalate (a :: rest), String.intercalate_cons_cons]

private theorem toString_mul_pow10 (q k : Nat) (hq : 0 < q) :
    (toString (q * pow10Nat k)).toList = (toString q).toList ++ List.replicate k '0' := by
  induction k with
  | zero => simp [pow10Nat]
  | succ k' ih =>
    have hmul : q * pow10Nat (k' + 1) = (q * pow10Nat k') * 10 + 0 := by
      change q * (10 * pow10Nat k') = q * pow10Nat k' * 10 + 0
      rw [Nat.add_zero, Nat.mul_left_comm, Nat.mul_comm 10]
    have hq' : 0 < q * pow10Nat k' := Nat.mul_pos hq (pow10Nat_pos k')
    rw [hmul, toString_two_digits_split (q * pow10Nat k') 0 hq' (by decide), ih]
    have hd0 : Nat.digitChar 0 = '0' := by decide
    rw [hd0, List.append_assoc, ← List.replicate_succ']

private theorem digitChar_ne_zero (d : Nat) (hd0 : d ≠ 0) (hd10 : d < 10) :
    Nat.digitChar d ≠ '0' := by
  match d with
  | 0 => exact absurd rfl hd0
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | _ + 10 => omega

private theorem toString_last_ne_zero (q : Nat) (hq : 0 < q) (hmod : q % 10 ≠ 0) :
    ∃ pref c, (toString q).toList = pref ++ [c] ∧ c ≠ '0' := by
  by_cases h10 : q < 10
  · obtain ⟨hch, _, _⟩ := toString_lt10_char q h10
    exact ⟨[], Nat.digitChar q, by rw [hch]; rfl, digitChar_ne_zero q (by omega) h10⟩
  · have hq10 : 0 < q / 10 := by omega
    have heq : q = (q / 10) * 10 + q % 10 := by omega
    have hsp := toString_two_digits_split (q / 10) (q % 10) hq10 (Nat.mod_lt q (by decide))
    rw [← heq] at hsp
    exact ⟨(toString (q / 10)).toList, Nat.digitChar (q % 10), hsp,
      digitChar_ne_zero (q % 10) hmod (Nat.mod_lt q (by decide))⟩

private theorem padNatZero_last_ne_zero (w q : Nat) (hq : 0 < q) (hmod : q % 10 ≠ 0)
    (hw : (toString q).toList.length ≤ w) :
    ∃ pref c, (padNatZero w q).toList = pref ++ [c] ∧ c ≠ '0' := by
  rw [padNatZero_eq_of_toList w q (toString q).toList rfl hw]
  obtain ⟨pref, c, hq_eq, hne⟩ := toString_last_ne_zero q hq hmod
  exact ⟨List.replicate (w - (toString q).toList.length) '0' ++ pref, c,
    by rw [hq_eq, List.append_assoc], hne⟩

private theorem dropWhile_replicate_zero_cons (k : Nat) (c : Char) (tl : List Char) (hc : c ≠ '0') :
    (List.replicate k '0' ++ c :: tl).dropWhile (· == '0') = c :: tl := by
  induction k with
  | zero =>
    have hbeq : (c == '0') = false := beq_false_of_ne hc
    simp [hbeq]
  | succ k' ih =>
    simp [List.replicate_succ, ih]

private def stripTrailingZerosNat (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else if n % 10 = 0 then
    let p := stripTrailingZerosNat (n / 10)
    (p.1 + 1, p.2)
  else (0, n)
termination_by n

private theorem stripTrailingZerosNat_spec (n : Nat) (hn : 0 < n) :
    let p := stripTrailingZerosNat n
    n = p.2 * pow10Nat p.1 ∧ 0 < p.2 ∧ p.2 % 10 ≠ 0 := by
  unfold stripTrailingZerosNat
  have hne0 : n ≠ 0 := by omega
  simp only [hne0, ↓reduceIte]
  by_cases hmod : n % 10 = 0
  · simp only [hmod, ↓reduceIte]
    have hdiv_pos : 0 < n / 10 := by omega
    have ih := stripTrailingZerosNat_spec (n / 10) hdiv_pos
    rcases ih with ⟨heq, hq_pos, hq_mod⟩
    refine ⟨?_, hq_pos, hq_mod⟩
    calc
      n = (n / 10) * 10 := by omega
      _ = ((stripTrailingZerosNat (n / 10)).2 * pow10Nat (stripTrailingZerosNat (n / 10)).1) * 10 := by rw [← heq]
      _ = (stripTrailingZerosNat (n / 10)).2 * pow10Nat ((stripTrailingZerosNat (n / 10)).1 + 1) := by
        change _ = _ * (10 * pow10Nat (stripTrailingZerosNat (n / 10)).1)
        rw [Nat.mul_assoc, Nat.mul_comm (pow10Nat _) 10]
  · simp only [hmod, ↓reduceIte, pow10Nat, Nat.mul_one]
    exact ⟨trivial, hn, hmod⟩
termination_by n

private theorem pow10Nat_mono {a b : Nat} (hab : a ≤ b) : pow10Nat a ≤ pow10Nat b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    simp only [pow10Nat]
    omega

private theorem formatNanosTrimmed_exists_exact (nano : Nat) (hn : nano < pow10Nat 9) :
    ∃ fd : Nat, formatNanosExact nano fd = some (formatNanosTrimmed nano) := by
  by_cases hn0 : nano = 0
  · subst hn0
    exact ⟨0, by simp [formatNanosExact, formatNanosTrimmed]⟩
  · have hn_pos : 0 < nano := by omega
    have hsp := stripTrailingZerosNat_spec nano hn_pos
    dsimp only at hsp
    let k := (stripTrailingZerosNat nano).1
    let q := (stripTrailingZerosNat nano).2
    rcases hsp with ⟨heq, hq_pos, hq_mod⟩
    have hk_lt9 : k < 9 := by
      by_cases hk : k < 9
      · exact hk
      · have hge9 : 9 ≤ k := by omega
        have hp9 : pow10Nat 9 ≤ pow10Nat k := pow10Nat_mono hge9
        have h1 : pow10Nat k ≤ q * pow10Nat k := Nat.le_mul_of_pos_left _ hq_pos
        have hle : pow10Nat 9 ≤ nano := by rw [heq]; exact Nat.le_trans hp9 h1
        exact False.elim (by omega)
    let fd := 9 - k
    have hfd_pos : 1 ≤ fd := by omega
    have h9_eq : fd + k = 9 := by omega
    have hq_lt : q < pow10Nat fd := by
      have hmul_pow : pow10Nat fd * pow10Nat k = pow10Nat 9 := by
        rw [← pow10Nat_add, h9_eq]
      by_cases hlt : q < pow10Nat fd
      · exact hlt
      · have h1 : pow10Nat fd ≤ q := by omega
        have h2 := Nat.mul_le_mul_right (pow10Nat k) h1
        rw [hmul_pow] at h2
        have hle : pow10Nat 9 ≤ nano := by rw [heq]; exact h2
        exact False.elim (by omega)
    have hq_len_str : (toString q).length ≤ fd := toString_length_le_pow10 fd q hfd_pos hq_lt
    have hq_len_list : (toString q).toList.length ≤ fd := by
      simpa [String.length] using hq_len_str
    have hn_str_len : (toString nano).length ≤ 9 := toString_length_le_pow10 9 nano (by omega) hn
    have hn_list_len : (toString nano).toList.length ≤ 9 := by
      simpa [String.length] using hn_str_len
    have hpad9 : (padNatZero 9 nano).toList = (padNatZero fd q).toList ++ List.replicate k '0' := by
      have hnano_list : (toString nano).toList = (toString q).toList ++ List.replicate k '0' := by
        rw [heq]; exact toString_mul_pow10 q k hq_pos
      have hlen_sum : (toString nano).toList.length = (toString q).toList.length + k := by
        rw [hnano_list, List.length_append, List.length_replicate]
      rw [padNatZero_eq_of_toList 9 nano _ hnano_list (by rw [← hnano_list]; exact hn_list_len),
        padNatZero_eq_of_toList fd q (toString q).toList rfl hq_len_list]
      have hsub : 9 - ((toString q).toList.length + k) = fd - (toString q).toList.length := by omega
      rw [List.length_append, List.length_replicate, hsub, List.append_assoc]
    obtain ⟨pref, c, hpad_fd, hc_ne⟩ := padNatZero_last_ne_zero fd q hq_pos hq_mod hq_len_list
    have htrim_eq : ((padNatZero 9 nano).toList.reverse.dropWhile (· == '0')).reverse =
        (padNatZero fd q).toList := by
      rw [hpad9, hpad_fd, List.reverse_append, List.reverse_replicate, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [dropWhile_replicate_zero_cons k c pref.reverse hc_ne, List.reverse_cons, List.reverse_reverse]
    have hfmt_trim : formatNanosTrimmed nano = "." ++ padNatZero fd q := by
      have hnb : (nano == 0) = false := beq_false_of_ne hn0
      simp only [formatNanosTrimmed, hnb, Bool.false_eq_true, ↓reduceIte]
      rw [htrim_eq, String.ofList_toList]
    have h9_fd : 9 - fd = k := by omega
    have hmod_div : nano % pow10Nat k = 0 := by
      rw [heq]; exact Nat.mul_mod_left q (pow10Nat k)
    have hdiv_val : nano / pow10Nat k = q := by
      rw [heq]; exact Nat.mul_div_cancel q (pow10Nat_pos k)
    have hfd_gt9 : ¬(fd > 9) := by omega
    have hfd_ne0 : (fd == 0) = false := beq_false_of_ne (by omega)
    refine ⟨fd, ?_⟩
    simp only [formatNanosExact, hfd_gt9, ↓reduceIte, hfd_ne0, Bool.false_eq_true,
      h9_fd, hmod_div, bne_self_eq_false, hdiv_val, hfmt_trim]

private def chooseKeyStyle (k : String) : KeyStyle :=
  if isValidBareKey k then .bare else .basic

private theorem renderKey_chooseKeyStyle (k : String) :
    renderKey k (chooseKeyStyle k) = some (formatKey k) := by
  by_cases hk : isValidBareKey k = true
  · simp [chooseKeyStyle, renderKey, formatKey, hk]
  · simp [chooseKeyStyle, renderKey, formatKey, hk]

private theorem renderDate_formatDate (d : Std.Time.PlainDate) (h : validTomlDate d = true) :
    renderDate d = some (formatDate d) := by
  simp [renderDate, formatDate, h]

private theorem renderTime_formatTime (t : Std.Time.PlainTime) (h : validTomlTime t = true) :
    ∃ fd : Nat, renderTime t fd = some (formatTime t) := by
  have hn_prop := t.nanosecond.property
  have hn_lt : t.nanosecond.val.toNat < pow10Nat 9 := by
    rw [pow10Nat_9]; omega
  obtain ⟨fd, hfd⟩ := formatNanosTrimmed_exists_exact t.nanosecond.val.toNat hn_lt
  exact ⟨fd, by simp [renderTime, formatTime, h, hfd]⟩

private theorem renderOffset_formatOffset (o : Std.Time.TimeZone.Offset)
    (h : validTomlOffset o = true) :
    renderOffset o .upperZ = some (formatOffset o) := by
  simp only [renderOffset, formatOffset, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

private theorem lookupKeyList_mem_of_noDupKeys (entries : List (String × TomlValue))
    (hnd : noDupKeysBool entries = true) :
    ∀ k v, (k, v) ∈ entries → lookupKeyList k entries = some v := by
  induction entries with
  | nil => intro k v hmem; cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    intro k v hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hhead | htail
    · cases hhead
      simp [lookupKeyList]
    · have hmem_map : k ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k, v), htail, rfl⟩
      have hhas : hasKeyList k tl = true := (hasKeyList_eq_true_iff k tl).mpr hmem_map
      have hne : k ≠ k' := by
        intro heq
        subst heq
        rw [hnd.1] at hhas
        cases hhas
      have hbeq : (k == k') = false := beq_false_of_ne hne
      simp only [lookupKeyList, hbeq, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2 k v htail

private theorem filter_ne_head_of_not_hasKey (k : String) (entries : List (String × TomlValue))
    (hnot : hasKeyList k entries = false) :
    entries.filter (fun p => p.1 != k) = entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [hasKeyList, Bool.or_eq_false_iff] at hnot
    have hne : (k' != k) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact fun h => by subst h; simp at hnot
    simp only [List.filter_cons, hne, ↓reduceIte, ih hnot.2]

private theorem renderValueInline_formatValueInline_aux (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (sz : Nat) :
    (∀ v : TomlValue, sizeOf v ≤ sz → WellFormedValue v →
      ∃ vt, renderValueInline v vt = some (formatValueInline numApi v)) ∧
    (∀ xs : List TomlValue, sizeOf xs ≤ sz → wellFormedValueBool.wellFormedListBool xs = true →
      ∃ elemTapes, renderValueInline.renderArrayElems xs elemTapes =
        some (formatArrayElems numApi xs)) ∧
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ entryTapes, renderValueInline.renderInlineTableEntries entries entryTapes =
        some (formatInlineEntries numApi entries)) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro v hsz _
      cases v <;> simp +arith at hsz
    · intro xs hsz _
      cases xs with
      | nil => exact ⟨[], rfl⟩
      | cons _ _ => simp +arith at hsz
    · intro entries hsz _ _
      cases entries with
      | nil => exact ⟨[], rfl⟩
      | cons _ _ => simp +arith at hsz
  | succ sz' ih =>
    have ihV := ih.1
    have ihA := ih.2.1
    have ihT := ih.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro v hsz hwf
      cases v with
      | string s => exact ⟨.string .basic, rfl⟩
      | int n =>
        exact ⟨.int (some (numApi.formatInt n.toInt)),
          by simp [renderValueInline, hFmtInt n, formatValueInline]⟩
      | float f =>
        exact ⟨.float (some (numApi.formatFloat f)),
          by simp [renderValueInline, hFmtFloat f, formatValueInline]⟩
      | bool b => exact ⟨.bool, rfl⟩
      | offsetDateTime odt =>
        have hvd : validTomlOffsetDateTime odt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        simp only [validTomlOffsetDateTime, validTomlDateTime, Bool.and_eq_true] at hvd
        have hd := renderDate_formatDate odt.dateTime.date hvd.1.1
        obtain ⟨fd, ht⟩ := renderTime_formatTime odt.dateTime.time hvd.1.2
        have ho := renderOffset_formatOffset odt.offset hvd.2
        exact ⟨.offsetDateTime .upperT .upperZ fd,
          by simp [renderValueInline, formatValueInline, renderDateTimeSep, hd, ht, ho]⟩
      | localDateTime dt =>
        have hvd : validTomlDateTime dt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        simp only [validTomlDateTime, Bool.and_eq_true] at hvd
        have hd := renderDate_formatDate dt.date hvd.1
        obtain ⟨fd, ht⟩ := renderTime_formatTime dt.time hvd.2
        exact ⟨.localDateTime .upperT fd,
          by simp [renderValueInline, formatValueInline, renderDateTimeSep, hd, ht]⟩
      | localDate d =>
        have hvd : validTomlDate d = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        exact ⟨.localDate, by simp [renderValueInline, formatValueInline, renderDate_formatDate d hvd]⟩
      | localTime t =>
        have hvt : validTomlTime t = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        obtain ⟨fd, ht⟩ := renderTime_formatTime t hvt
        exact ⟨.localTime fd, by simp [renderValueInline, formatValueInline, ht]⟩
      | array xs =>
        have hwf_l : wellFormedValueBool.wellFormedListBool xs.toList = true := by
          simpa [WellFormedValue, wellFormedValueBool] using hwf
        have hsz_l : sizeOf xs.toList ≤ sz' := by
          have := sizeOf_toList_lt_array xs
          have : sizeOf xs < sizeOf (TomlValue.array xs) := by simp +arith
          omega
        obtain ⟨elemTapes, he⟩ := ihA xs.toList hsz_l hwf_l
        exact ⟨.array elemTapes,
          by simp [renderValueInline, formatValueInline, he]⟩
      | table t =>
        have hwf_t : noDupKeysBool t.toList = true ∧
            wellFormedValueBool.wellFormedTableListBool t.toList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf
        have hsz_t : sizeOf t.toList ≤ sz' := by
          have := sizeOf_toList_lt_array t
          have : sizeOf t < sizeOf (TomlValue.table t) := by simp +arith
          omega
        obtain ⟨entryTapes, he⟩ := ihT t.toList hsz_t hwf_t.1 hwf_t.2
        exact ⟨.inlineTable entryTapes,
          by simp [renderValueInline, formatValueInline, hwf_t.1, he]⟩
    · intro xs hsz hwf
      cases xs with
      | nil => exact ⟨[], rfl⟩
      | cons x rest =>
        simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
        have hsz_x : sizeOf x ≤ sz' := by simp +arith at hsz ⊢; omega
        have hsz_r : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨vt, hvt⟩ := ihV x hsz_x hwf.1
        obtain ⟨elemTapes, he⟩ := ihA rest hsz_r hwf.2
        exact ⟨vt :: elemTapes,
          by simp [renderValueInline.renderArrayElems, formatArrayElems, hvt, he]⟩
    · intro entries hsz hnd hwf
      cases entries with
      | nil => exact ⟨[], rfl⟩
      | cons hd rest =>
        rcases hd with ⟨k, v⟩
        simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
        simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
        have hsz_v : sizeOf v ≤ sz' := by simp +arith at hsz ⊢; omega
        have hsz_r : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨vt, hvt⟩ := ihV v hsz_v hwf.1
        obtain ⟨restTapes, hr⟩ := ihT rest hsz_r hnd.2 hwf.2
        have hfilt : ((k, v) :: rest).filter (fun p => p.1 != k) = rest := by
          simp only [List.filter_cons, bne_self_eq_false]
          exact filter_ne_head_of_not_hasKey k rest hnd.1
        refine ⟨(k, chooseKeyStyle k, vt) :: restTapes, ?_⟩
        simp only [renderValueInline.renderInlineTableEntries, lookupKeyList, beq_self_eq_true,
          ↓reduceIte, renderKey_chooseKeyStyle k, hvt, hfilt, hr, formatInlineEntries,
          bind, Option.bind]

private theorem renderValueInline_formatValueInline (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (v : TomlValue) (hwf : WellFormedValue v) :
    ∃ vt, renderValueInline v vt = some (formatValueInline numApi v) :=
  (renderValueInline_formatValueInline_aux numApi hFmtInt hFmtFloat (sizeOf v)).1 v (Nat.le_refl _) hwf

private def PlacementMatches (numApi : NumParseApi) (k : String) (v : TomlValue)
    (ep : EntryPlacement) : Prop :=
  match v with
  | .table sub =>
    ∃ subPlan, ep = .tableSection (chooseKeyStyle k) false subPlan none ∧
      ∀ revPref, renderTablePlan revPref sub.toList subPlan =
        some (formatTableInlinePart numApi sub.toList ++ formatTableSectionPart numApi revPref sub.toList)
  | .array xs =>
    if isNonEmptyTableArray xs then
      ∃ elemPlans, ep = .aotSection (chooseKeyStyle k) elemPlans none ∧
        ∀ revTarget, renderAotElems revTarget "" xs.toList elemPlans =
          some (formatAotElemList numApi revTarget ("[[" ++ String.intercalate "." revTarget.reverse ++ "]]") xs.toList)
    else
      ∃ vt, ep = .direct (chooseKeyStyle k) vt none ∧
        renderValueInline v vt = some (formatValueInline numApi v)
  | _ =>
    ∃ vt, ep = .direct (chooseKeyStyle k) vt none ∧
      renderValueInline v vt = some (formatValueInline numApi v)

private theorem placementMatches_isInlineScope (numApi : NumParseApi) (k : String) (v : TomlValue)
    (ep : EntryPlacement) (hm : PlacementMatches numApi k v ep) :
    (match v with
     | .table _ => ep.isInlineScope = false
     | .array xs =>
       if isNonEmptyTableArray xs then ep.isInlineScope = false else ep.isInlineScope = true
     | _ => ep.isInlineScope = true) := by
  cases v with
  | table sub =>
    rcases hm with ⟨subPlan, rfl, _⟩; rfl
  | array xs =>
    by_cases haot : isNonEmptyTableArray xs = true
    · simp only [PlacementMatches, haot, ↓reduceIte] at hm ⊢
      rcases hm with ⟨elemPlans, rfl, _⟩; rfl
    · have haf : isNonEmptyTableArray xs = false := Bool.eq_false_iff.mpr haot
      simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      rcases hm with ⟨vt, rfl, _⟩; rfl
  | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
    rcases hm with ⟨vt, rfl, _⟩; rfl

private inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

private theorem ListRel.length_eq {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : ListRel R as bs) : bs.length = as.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem renderEntries_of_placementMatches (numApi : NumParseApi)
    (fullEntries : List (String × TomlValue))
    (subEntries : List (String × TomlValue)) (subPlan : List (String × EntryPlacement))
    (hsub : ∀ p ∈ subEntries, lookupKeyList p.1 fullEntries = some p.2)
    (hmatch : ListRel (fun p q => p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) subEntries subPlan)
    (revPref : List String) :
    renderInlineEntries revPref fullEntries subPlan = some (formatTableInlinePart numApi subEntries) ∧
    renderSectionEntries revPref fullEntries subPlan = some (formatTableSectionPart numApi revPref subEntries) := by
  induction hmatch with
  | nil =>
    exact ⟨by simp [renderInlineEntries, formatTableInlinePart],
      by simp [renderSectionEntries, formatTableSectionPart]⟩
  | @cons hd_e hd_p tl_e tl_p hhead htail ih =>
    rcases hd_e with ⟨k, v⟩
    rcases hd_p with ⟨kp, ep⟩
    rcases hhead with ⟨hk_eq, hm⟩
    dsimp only at hk_eq hm
    subst hk_eq
    have hlu : lookupKeyList k fullEntries = some v := hsub (k, v) List.mem_cons_self
    have hsub_tl : ∀ p ∈ tl_e, lookupKeyList p.1 fullEntries = some p.2 :=
      fun p hp => hsub p (List.mem_cons_of_mem _ hp)
    obtain ⟨ih_inl, ih_sec⟩ := ih hsub_tl
    cases v with
    | table sub =>
      rcases sub with ⟨subList⟩
      rcases hm with ⟨subPlan', rfl, htp⟩
      have hinl : renderInlineEntries revPref fullEntries ((k, .tableSection (chooseKeyStyle k) false subPlan' none) :: tl_p) =
          some (formatTableInlinePart numApi ((k, .table ⟨subList⟩) :: tl_e)) := by
        simp [renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart]
      have hsec : renderSectionEntries revPref fullEntries ((k, .tableSection (chooseKeyStyle k) false subPlan' none) :: tl_p) =
          some (formatTableSectionPart numApi revPref ((k, .table ⟨subList⟩) :: tl_e)) := by
        simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte,
          hlu, renderKey_chooseKeyStyle k, renderCommentSuffix, htp, ih_sec, formatTableSectionPart,
          bind, Option.bind, joinRenderedPath_eq_intercalate, String.append_empty]
        simp only [List.cons_append, List.append_assoc]
      exact ⟨hinl, hsec⟩
    | array xs =>
      rcases xs with ⟨xsList⟩
      by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
      · simp only [PlacementMatches, haot, ↓reduceIte] at hm
        rcases hm with ⟨elemPlans, rfl, ha⟩
        have hne : (⟨xsList⟩ : Array TomlValue).isEmpty = false := by
          simp only [isNonEmptyTableArray, Bool.and_eq_true, Bool.not_eq_true'] at haot
          exact haot.1
        have hinl : renderInlineEntries revPref fullEntries ((k, .aotSection (chooseKeyStyle k) elemPlans none) :: tl_p) =
            some (formatTableInlinePart numApi ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp [renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart, haot]
        have hsec : renderSectionEntries revPref fullEntries ((k, .aotSection (chooseKeyStyle k) elemPlans none) :: tl_p) =
            some (formatTableSectionPart numApi revPref ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte,
            hlu, hne, renderKey_chooseKeyStyle k, renderCommentSuffix, ha, ih_sec, formatTableSectionPart,
            haot, bind, Option.bind]
        exact ⟨hinl, hsec⟩
      · have haf : isNonEmptyTableArray ⟨xsList⟩ = false := Bool.eq_false_iff.mpr haot
        simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte] at hm
        rcases hm with ⟨vt, rfl, hrv⟩
        have hinl : renderInlineEntries revPref fullEntries ((k, .direct (chooseKeyStyle k) vt none) :: tl_p) =
            some (formatTableInlinePart numApi ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hlu, renderKey_chooseKeyStyle k, hrv, renderCommentSuffix, ih_inl,
            formatTableInlinePart, haf, bind, Option.bind, String.append_empty]
          rfl
        have hsec : renderSectionEntries revPref fullEntries ((k, .direct (chooseKeyStyle k) vt none) :: tl_p) =
            some (formatTableSectionPart numApi revPref ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp [renderSectionEntries, EntryPlacement.isInlineScope, ih_sec, formatTableSectionPart, haf]
        exact ⟨hinl, hsec⟩
    | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      rcases hm with ⟨vt, rfl, hrv⟩
      refine ⟨?_, ?_⟩
      · simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hlu, renderKey_chooseKeyStyle k, hrv, renderCommentSuffix, ih_inl,
          formatTableInlinePart, bind, Option.bind, String.append_empty]
        rfl
      · simp [renderSectionEntries, EntryPlacement.isInlineScope, ih_sec, formatTableSectionPart]

private theorem noDupStringsBool_map_fst (entries : List (String × TomlValue)) :
    noDupStringsBool (entries.map Prod.fst) = noDupKeysBool entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, noDupStringsBool, noDupKeysBool, ih]
    have hmem : (tl.map Prod.fst).contains k = hasKeyList k tl := by
      cases hc : (tl.map Prod.fst).contains k
      · symm
        cases hh : hasKeyList k tl
        · rfl
        · have h1 := (hasKeyList_eq_true_iff k tl).mp hh
          have h2 : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr h1
          rw [hc] at h2; cases h2
      · symm
        have h1 : k ∈ tl.map Prod.fst := List.contains_iff_mem.mp hc
        exact (hasKeyList_eq_true_iff k tl).mpr h1
    rw [hmem]

private theorem isPlanPermutation_of_match (numApi : NumParseApi)
    (entries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
    (hnd : noDupKeysBool entries = true)
    (hmatch : ListRel (fun p q => p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan) :
    isPlanPermutation entries plan = true := by
  have hmap : plan.map Prod.fst = entries.map Prod.fst := by
    clear hnd
    induction hmatch with
    | nil => rfl
    | cons hh _ ih => simp [hh.1, ih]
  have hlen : plan.length = entries.length := hmatch.length_eq
  have hall : plan.all (fun p => hasKeyList p.1 entries) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hmem : p.1 ∈ plan.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hmap] at hmem
    exact (hasKeyList_eq_true_iff p.1 entries).mpr hmem
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hnd, ?_⟩, hlen⟩, hall⟩
  rw [hmap, noDupStringsBool_map_fst, hnd]

private theorem choosePlan_exists_aux (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (sz : Nat) :
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ plan, (∀ revPref, renderTablePlan revPref entries plan =
        some (formatTableInlinePart numApi entries ++ formatTableSectionPart numApi revPref entries))) ∧
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ plan, ListRel (fun (p : String × TomlValue) (q : String × EntryPlacement) =>
        p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan) ∧
    (∀ xs : List TomlValue, sizeOf xs ≤ sz →
      wellFormedValueBool.wellFormedListBool xs = true →
      (xs.all fun v => match v with | .table _ => true | _ => false) = true →
      ∃ elemPlans, ∀ revTarget, renderAotElems revTarget "" xs elemPlans =
        some (formatAotElemList numApi revTarget ("[[" ++ String.intercalate "." revTarget.reverse ++ "]]") xs)) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro entries hsz _ _
      cases entries with
      | nil =>
        exact ⟨[], fun revPref => by
          simp [renderTablePlan, isPlanPermutation, noDupKeysBool, noDupStringsBool,
            renderInlineEntries, renderSectionEntries, formatTableInlinePart, formatTableSectionPart]⟩
      | cons _ _ => simp +arith at hsz
    · intro entries hsz _ _
      cases entries with
      | nil => exact ⟨[], .nil⟩
      | cons _ _ => simp +arith at hsz
    · intro xs hsz _ _
      cases xs with
      | nil => exact ⟨[], fun _ => by simp [renderAotElems, formatAotElemList]⟩
      | cons _ _ => simp +arith at hsz
  | succ sz' ih =>
    have ihMatch := ih.2.1
    have ihPlan := ih.1
    have ihAot := ih.2.2
    have hMatchStep : ∀ entries : List (String × TomlValue), sizeOf entries ≤ sz' + 1 →
        noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
        ∃ plan, ListRel (fun (p : String × TomlValue) (q : String × EntryPlacement) =>
          p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan := by
      intro entries hsz hnd hwf
      cases entries with
      | nil => exact ⟨[], .nil⟩
      | cons hd tl =>
        rcases hd with ⟨k, v⟩
        simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
        simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
        have hsz_tl : sizeOf tl ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨tlPlan, htl⟩ := ihMatch tl hsz_tl hnd.2 hwf.2
        cases v with
        | table sub =>
          have hwf_sub : noDupKeysBool sub.toList = true ∧
              wellFormedValueBool.wellFormedTableListBool sub.toList = true := by
            simpa [wellFormedValueBool, Bool.and_eq_true] using hwf.1
          have hsz_sub : sizeOf sub.toList ≤ sz' := by
            have := sizeOf_toList_lt_array sub
            simp +arith at hsz ⊢; omega
          obtain ⟨subPlan, hsub⟩ := ihPlan sub.toList hsz_sub hwf_sub.1 hwf_sub.2
          refine ⟨(k, .tableSection (chooseKeyStyle k) false subPlan none) :: tlPlan,
            .cons ⟨rfl, ⟨subPlan, rfl, hsub⟩⟩ htl⟩
        | array xs =>
          by_cases haot : isNonEmptyTableArray xs = true
          · have hwf_xs : wellFormedValueBool.wellFormedListBool xs.toList = true := by
              simpa [wellFormedValueBool] using hwf.1
            have hall_xs : (xs.toList.all fun v => match v with | .table _ => true | _ => false) = true := by
              simp only [isNonEmptyTableArray, Bool.and_eq_true] at haot
              exact haot.2
            have hsz_xs : sizeOf xs.toList ≤ sz' := by
              have := sizeOf_toList_lt_array xs
              simp +arith at hsz ⊢; omega
            obtain ⟨elemPlans, ha⟩ := ihAot xs.toList hsz_xs hwf_xs hall_xs
            refine ⟨(k, .aotSection (chooseKeyStyle k) elemPlans none) :: tlPlan,
              .cons ⟨rfl, ?_⟩ htl⟩
            simp only [PlacementMatches, haot, ↓reduceIte]
            exact ⟨elemPlans, rfl, ha⟩
          · have haf : isNonEmptyTableArray xs = false := Bool.eq_false_iff.mpr haot
            obtain ⟨vt, hvt⟩ := renderValueInline_formatValueInline numApi hFmtInt hFmtFloat (.array xs) hwf.1
            refine ⟨(k, .direct (chooseKeyStyle k) vt none) :: tlPlan,
              .cons ⟨rfl, ?_⟩ htl⟩
            simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte]
            exact ⟨vt, rfl, hvt⟩
        | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
          obtain ⟨vt, hvt⟩ := renderValueInline_formatValueInline numApi hFmtInt hFmtFloat _ hwf.1
          exact ⟨(k, .direct (chooseKeyStyle k) vt none) :: tlPlan,
            .cons ⟨rfl, ⟨vt, rfl, hvt⟩⟩ htl⟩
    have hPlanStep : ∀ entries : List (String × TomlValue), sizeOf entries ≤ sz' + 1 →
        noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
        ∃ plan, (∀ revPref, renderTablePlan revPref entries plan =
          some (formatTableInlinePart numApi entries ++ formatTableSectionPart numApi revPref entries)) := by
      intro entries hsz hnd hwf
      obtain ⟨plan, hmatch⟩ := hMatchStep entries hsz hnd hwf
      have hperm : isPlanPermutation entries plan = true :=
        isPlanPermutation_of_match numApi entries plan hnd hmatch
      have hmem : ∀ p ∈ entries, lookupKeyList p.1 entries = some p.2 :=
        fun p hp => lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp
      refine ⟨plan, fun revPref => ?_⟩
      obtain ⟨hinl, hsec⟩ := renderEntries_of_placementMatches numApi entries entries plan hmem hmatch revPref
      simp only [renderTablePlan, hperm, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hinl, hsec, bind, Option.bind]
    refine ⟨hPlanStep, hMatchStep, ?_⟩
    intro xs hsz hwf hall
    cases xs with
    | nil => exact ⟨[], fun _ => by simp [renderAotElems, formatAotElemList]⟩
    | cons x rest =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hsz_rest : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
      obtain ⟨tailPlans, htail⟩ := ihAot rest hsz_rest hwf.2 hall.2
      cases x with
      | table elem =>
        have hwf_e : noDupKeysBool elem.toList = true ∧
            wellFormedValueBool.wellFormedTableListBool elem.toList = true := by
          simpa [wellFormedValueBool, Bool.and_eq_true] using hwf.1
        have hsz_e : sizeOf elem.toList ≤ sz' := by
          have := sizeOf_toList_lt_array elem
          simp +arith at hsz ⊢; omega
        obtain ⟨ep, hep⟩ := ihPlan elem.toList hsz_e hwf_e.1 hwf_e.2
        refine ⟨ep :: tailPlans, fun revTarget => ?_⟩
        cases elem with
        | mk elemList =>
          simp only [renderAotElems, joinRenderedPath_eq_intercalate, String.append_empty,
            hep revTarget, htail revTarget, formatAotElemList, bind, Option.bind]
          simp only [List.cons_append, List.append_assoc]
      | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
        cases hall.1

private theorem formatSectionLines_nil_eq_nil (numApi : NumParseApi) (revPref : List String)
    (doc : TomlTable) (h : formatSectionLines numApi revPref doc = []) :
    doc.toList = [] := by
  cases hlist : doc.toList with
  | nil => rfl
  | cons hd tl =>
    rcases hd with ⟨k, v⟩
    simp only [formatSectionLines, hlist, List.append_eq_nil_iff] at h
    rcases h with ⟨hinl, hsec⟩
    cases v with
    | table sub =>
      cases sub
      simp [formatTableSectionPart] at hsec
    | array xs =>
      cases xs with
      | mk xsList =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · simp only [formatTableSectionPart, haot, ↓reduceIte] at hsec
          cases xsList with
          | nil =>
            simp [isNonEmptyTableArray] at haot
          | cons x0 rest =>
            simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
            cases x0 with
            | table elem =>
              cases elem
              simp [formatAotElemList] at hsec
            | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
              cases haot.2.1
        · have haf : isNonEmptyTableArray ⟨xsList⟩ = false := Bool.eq_false_iff.mpr haot
          simp [formatTableInlinePart, haf] at hinl
    | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      simp [formatTableInlinePart] at hinl

/-- Empty input string parses via `parseWithNum` to an empty `TomlTable`. -/
theorem parseWithNum_empty (numApi : NumParseApi) :
    parseWithNum numApi "" = .ok #[] := by
  simp [parseWithNum, normalizeChars, parseDocumentFuel, skipTriviaNewlines,
    skipTriviaNewlinesAux, entriesToTomlList, bind, Except.bind]

/-- Canonical `formatWithNum` output always parses via `parseWithNum` to an equivalent `TomlTable` for any `WellFormedTable`. -/
theorem formatWithNum_roundTrip_model (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (doc : TomlTable) (hwf : WellFormedTable doc) :
    ∃ parsed, parseWithNum numApi (formatWithNum numApi doc) = .ok parsed ∧
      TomlTableEquiv doc parsed := by
  unfold formatWithNum
  cases hlines : formatSectionLines numApi [] doc with
  | nil =>
    have hdoc_nil : doc.toList = [] := formatSectionLines_nil_eq_nil numApi [] doc hlines
    refine ⟨#[], parseWithNum_empty numApi, ?_⟩
    simp [TomlTableEquiv, hdoc_nil, TomlTableEquivList, lookupKeyList]
  | cons hd tl =>
    have hwf_b : wellFormedTableBool doc = true := hwf
    have hwf_parts : noDupKeysBool doc.toList = true ∧
        wellFormedValueBool.wellFormedTableListBool doc.toList = true := by
      simpa [wellFormedTableBool, Bool.and_eq_true] using hwf_b
    obtain ⟨plan, hplan⟩ := (choosePlan_exists_aux numApi hFmtInt hFmtFloat (sizeOf doc.toList)).1
      doc.toList (Nat.le_refl _) hwf_parts.1 hwf_parts.2
    have hrender : render doc ⟨plan, none⟩ = some (String.intercalate "\n" (hd :: tl) ++ "\n") := by
      have hbp : renderTablePlan [] doc.toList plan = some (hd :: tl) := by
        have hp := hplan []
        unfold formatSectionLines at hlines
        rw [hlines] at hp
        exact hp
      simp [render, hwf_b, hbp, bind, Option.bind]
    exact render_parse_roundTrip_model numApi hInt hFloat doc ⟨plan, none⟩
      (String.intercalate "\n" (hd :: tl) ++ "\n") hrender

end LeanSwe.Toml.Proofs

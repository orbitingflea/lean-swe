import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem char_ofNat_decDigit_props (d : Nat) (hd : d < 10) :
    Model.isDecDigit (Char.ofNat ('0'.toNat + d)) = true ∧
      Char.ofNat ('0'.toNat + d) ≠ '_' ∧
      (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d := by
  match d with
  | 0 => exact ⟨by decide, by decide, by decide⟩
  | 1 => exact ⟨by decide, by decide, by decide⟩
  | 2 => exact ⟨by decide, by decide, by decide⟩
  | 3 => exact ⟨by decide, by decide, by decide⟩
  | 4 => exact ⟨by decide, by decide, by decide⟩
  | 5 => exact ⟨by decide, by decide, by decide⟩
  | 6 => exact ⟨by decide, by decide, by decide⟩
  | 7 => exact ⟨by decide, by decide, by decide⟩
  | 8 => exact ⟨by decide, by decide, by decide⟩
  | 9 => exact ⟨by decide, by decide, by decide⟩
  | k + 10 => omega

private theorem decDigit_props {c : Char} (hc : Model.isDecDigit c = true) :
    c ≠ '_' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c.toNat - '0'.toNat < 10 := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hu : '_'.toNat = 95 := by decide
  have hd : '.'.toNat = 46 := by decide
  have he : 'e'.toNat = 101 := by decide
  have hE : 'E'.toNat = 69 := by decide
  have h1 : '0'.toNat ≤ c.toNat := hc.1
  have h2 : c.toNat ≤ '9'.toNat := hc.2
  refine ⟨?_, ?_, ?_, ?_, by omega⟩ <;> intro h <;> have hcn := congrArg Char.toNat h <;> omega

private theorem natToDecCharsPos_append (n : Nat) (acc : List Char) :
    Internal.natToDecCharsPos n acc = Internal.natToDecCharsPos n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, Internal.natToDecCharsPos.eq_2]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [ih ((m + 1) / 10) hlt (Char.ofNat ('0'.toNat + (m + 1) % 10) :: acc)]
      rw [ih ((m + 1) / 10) hlt [Char.ofNat ('0'.toNat + (m + 1) % 10)]]
      simp [List.append_assoc]

private def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

private theorem decFold_zeros (acc k : Nat) :
    (List.replicate k '0').foldl decStep acc = acc * 10 ^ k := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, decStep]
    have h0 : '0'.toNat - '0'.toNat = 0 := by decide
    rw [h0, Nat.add_zero, ih (acc * 10), Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]

private theorem decFold_zeros_zero (k : Nat) :
    (List.replicate k '0').foldl decStep 0 = 0 := by
  rw [decFold_zeros, Nat.zero_mul]

private theorem natToDecCharsPos_eval (n acc : Nat) :
    (Internal.natToDecCharsPos n []).foldl decStep acc =
      acc * 10 ^ (Internal.natToDecCharsPos n []).length + n := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [List.foldl_append, ih ((m + 1) / 10) hlt acc]
      simp only [List.foldl_cons, List.foldl_nil, decStep, List.length_append, List.length_singleton]
      have hd := (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2.2
      rw [hd, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]
      have hdiv : (m + 1) / 10 * 10 + (m + 1) % 10 = m + 1 := by omega
      omega

private theorem natToDecCharsPos_all_dec (n : Nat) :
    ∀ c ∈ Internal.natToDecCharsPos n [], Model.isDecDigit c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact ih ((m + 1) / 10) hlt c h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).1

private theorem natToDecCharsPos_nonempty {n : Nat} (hn : 0 < n) :
    Internal.natToDecCharsPos n [] ≠ [] := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
    simp

private theorem natToDecCharsPos_head_ne_zero {n : Nat} (hn : 0 < n) :
    (Internal.natToDecCharsPos n []).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      by_cases hq : (m + 1) / 10 = 0
      · rw [hq, Internal.natToDecCharsPos.eq_1, List.nil_append]
        simp only [List.head?_cons]
        intro heq
        have heq' : Char.ofNat ('0'.toNat + (m + 1) % 10) = '0' := Option.some.inj heq
        have hsub := congrArg (fun x : Char => x.toNat - '0'.toNat) heq'
        have hd := (char_ofNat_decDigit_props ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2.2
        rw [hd] at hsub
        have hz : '0'.toNat - '0'.toNat = 0 := by decide
        rw [hz] at hsub
        omega
      · have hqpos : 0 < (m + 1) / 10 := Nat.pos_of_ne_zero hq
        have hne := natToDecCharsPos_nonempty hqpos
        have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
        cases hql : Internal.natToDecCharsPos ((m + 1) / 10) [] with
        | nil => exact absurd hql hne
        | cons x xs =>
          simp only [List.cons_append, List.head?_cons]
          have hih := ih ((m + 1) / 10) hlt hqpos
          rw [hql, List.head?_cons] at hih
          exact hih

private theorem consumeDecFloatDigits_append_dec
    (ds : List Char) (hds : ∀ c ∈ ds, Model.isDecDigit c = true)
    (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ Model.isDecDigit r0 = false ∧ r0 ≠ '_')
    (acc count : Nat) :
    Model.consumeDecFloatDigits acc count (ds ++ rest) =
      Except.ok (ds.foldl decStep acc, count + ds.length, rest) := by
  induction ds generalizing acc count with
  | nil =>
    simp only [List.nil_append, List.foldl_nil, List.length_nil, Nat.add_zero]
    rcases hrest with rfl | ⟨r0, rem, rfl, hnd, hnu⟩
    · rw [Model.consumeDecFloatDigits.eq_1]
    · rw [Model.consumeDecFloatDigits.eq_4 acc count r0 rem (fun _ _ h => absurd h hnu) (fun h => absurd h hnu)]
      simp [hnd]
  | cons d ds ih =>
    have hd : Model.isDecDigit d = true := hds d (by simp)
    have hdnu : d ≠ '_' := (decDigit_props hd).1
    have hds' : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hds c (by simp [hc])
    rw [List.cons_append, Model.consumeDecFloatDigits.eq_4 acc count d (ds ++ rest) (fun _ _ h => absurd h hdnu) (fun h => absurd h hdnu)]
    simp only [hd, ↓reduceIte, List.foldl_cons, List.length_cons, decStep]
    rw [ih hds' (acc * 10 + (d.toNat - '0'.toNat)) (count + 1)]
    have hadd : count + 1 + ds.length = count + (ds.length + 1) := by omega
    rw [hadd]

private theorem parseFloatIntPart_append_dec
    (ds : List Char) (hne : ds ≠ [])
    (hds : ∀ c ∈ ds, Model.isDecDigit c = true)
    (hhd : ds.head? ≠ some '0')
    (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ Model.isDecDigit r0 = false ∧ r0 ≠ '_') :
    Model.parseFloatIntPart (ds ++ rest) = Except.ok (ds.foldl decStep 0, rest) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd : Model.isDecDigit d = true := hds d (by simp)
    have hdnu : d ≠ '_' := (decDigit_props hd).1
    have hdz : d ≠ '0' := by intro h; subst h; exact hhd rfl
    have hds' : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hds c (by simp [hc])
    rw [List.cons_append]
    unfold Model.parseFloatIntPart
    simp only []
    split
    · rw [consumeDecFloatDigits_append_dec ds hds' rest hrest (d.toNat - '0'.toNat) 1]
      simp [decStep]
    · rename_i hnd; exact absurd hd hnd

private theorem decDigit_cases {c : Char} (hc : Model.isDecDigit c = true) :
    c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨
    c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hlo : 48 ≤ c.toNat := h0 ▸ hc.1
  have hhi : c.toNat ≤ 57 := h9 ▸ hc.2
  have hsub : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
      c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  have hc_ofNat : Char.ofNat c.toNat = c := Char.ofNat_toNat c
  rcases hsub with h | h | h | h | h | h | h | h | h | h
  · left; exact hc_ofNat.symm.trans (by rw [h])
  · right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; right; left; exact hc_ofNat.symm.trans (by rw [h])
  · right; right; right; right; right; right; right; right; right; exact hc_ofNat.symm.trans (by rw [h])

private theorem parseFloatExpPart_cons_decDigit (d : Char) (ds : List Char)
    (hd : Model.isDecDigit d = true) :
    Model.parseFloatExpPart (d :: ds) =
      match Model.consumeDecFloatDigits (d.toNat - '0'.toNat) 1 ds with
      | Except.ok (eMag, _, rem) => Except.ok (Int.ofNat eMag, rem)
      | Except.error k => Except.error k := by
  rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem parseFloatExpPart_formatIntChars (e : Int) :
    Model.parseFloatExpPart (Internal.formatIntChars e) = Except.ok (e, []) := by
  cases e with
  | ofNat n =>
    cases n with
    | zero =>
      have hfmt : Internal.formatIntChars (Int.ofNat 0) = ['0'] := rfl
      rw [hfmt]
      have hz : Model.isDecDigit '0' = true := by decide
      rw [parseFloatExpPart_cons_decDigit '0' [] hz, Model.consumeDecFloatDigits.eq_1]
      rfl
    | succ m =>
      have hfmt : Internal.formatIntChars (Int.ofNat (Nat.succ m)) = Internal.natToDecCharsPos (m + 1) [] := rfl
      rw [hfmt]
      have hpos : 0 < m + 1 := Nat.succ_pos m
      have hne := natToDecCharsPos_nonempty hpos
      have hall := natToDecCharsPos_all_dec (m + 1)
      have hev := natToDecCharsPos_eval (m + 1) 0
      simp only [Nat.zero_mul, Nat.zero_add] at hev
      cases hcs : Internal.natToDecCharsPos (m + 1) [] with
      | nil => exact absurd hcs hne
      | cons d ds =>
        rw [hcs] at hall hev
        have hhd : Model.isDecDigit d = true := hall d (by simp)
        have hds : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hall c (by simp [hc])
        rw [parseFloatExpPart_cons_decDigit d ds hhd]
        have hcon := consumeDecFloatDigits_append_dec ds hds [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
        simp only [List.append_nil] at hcon
        rw [hcon]
        have hfold : ds.foldl decStep (d.toNat - '0'.toNat) = (d :: ds).foldl decStep 0 := by
          simp [decStep, List.foldl_cons]
        rw [hfold, hev]
  | negSucc n =>
    have hfmt : Internal.formatIntChars (Int.negSucc n) = '-' :: Internal.natToDecCharsPos (n + 1) [] := rfl
    rw [hfmt]
    have hpos : 0 < n + 1 := Nat.succ_pos n
    have hne := natToDecCharsPos_nonempty hpos
    have hall := natToDecCharsPos_all_dec (n + 1)
    have hev := natToDecCharsPos_eval (n + 1) 0
    simp only [Nat.zero_mul, Nat.zero_add] at hev
    cases hcs : Internal.natToDecCharsPos (n + 1) [] with
    | nil => exact absurd hcs hne
    | cons d ds =>
      rw [hcs] at hall hev
      have hhd : Model.isDecDigit d = true := hall d (by simp)
      have hdu : d ≠ '_' := (decDigit_props hhd).1
      have hds : ∀ c ∈ ds, Model.isDecDigit c = true := fun c hc => hall c (by simp [hc])
      unfold Model.parseFloatExpPart
      simp only []
      split
      · simp only [↓reduceIte]
        have hcon := consumeDecFloatDigits_append_dec ds hds [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
        simp only [List.append_nil] at hcon
        rw [hcon]
        have hfold : ds.foldl decStep (d.toNat - '0'.toNat) = (d :: ds).foldl decStep 0 := by
          simp [decStep, List.foldl_cons]
        rw [hfold, hev]
        rfl
      · rename_i hnd; exact absurd hhd hnd

private theorem formatIntChars_all_non_underscore (e : Int) :
    ∀ c ∈ Internal.formatIntChars e, c ≠ '_' := by
  unfold Internal.formatIntChars
  cases e with
  | ofNat n =>
    cases n with
    | zero =>
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      decide
    | succ m =>
      intro c hc
      exact (decDigit_props (natToDecCharsPos_all_dec (m + 1) c hc)).1
  | negSucc n =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact (decDigit_props (natToDecCharsPos_all_dec (n + 1) c hc)).1

private theorem list_contains_eq_false_of_forall {cs : List Char} {x : Char}
    (h : ∀ c ∈ cs, c ≠ x) : cs.contains x = false := by
  simp only [Bool.eq_false_iff]
  intro hc
  have hmem : x ∈ cs := List.contains_iff_mem.mp hc
  exact absurd rfl (h x hmem)
private theorem decDigit_not_special {c : Char} (hc : Model.isDecDigit c = true) :
    c ≠ '_' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ '+' ∧ c ≠ '-' ∧ c ≠ 'i' ∧ c ≠ 'n' := by
  simp only [Model.isDecDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h0 : '0'.toNat = 48 := by decide
  have h9 : '9'.toNat = 57 := by decide
  have hu : '_'.toNat = 95 := by decide
  have hd : '.'.toNat = 46 := by decide
  have he : 'e'.toNat = 101 := by decide
  have hE : 'E'.toNat = 69 := by decide
  have hp : '+'.toNat = 43 := by decide
  have hm : '-'.toNat = 45 := by decide
  have hi : 'i'.toNat = 105 := by decide
  have hn : 'n'.toNat = 110 := by decide
  have h1 : '0'.toNat ≤ c.toNat := hc.1
  have h2 : c.toNat ≤ '9'.toNat := hc.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have hcn := congrArg Char.toNat h <;> omega

private theorem parseFloatModelChars_cons_decDigit (neg : Bool) (d : Char) (rest : List Char)
    (hd : Model.isDecDigit d = true) :
    Model.parseFloatModelChars ((if neg then ['-'] else []) ++ d :: rest) =
      match Model.parseFloatIntPart (d :: rest) with
      | Except.error k => Except.error k
      | Except.ok (intVal, afterInt) =>
        match afterInt with
        | '.' :: afterDot =>
          match afterDot with
          | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
          | c :: rest2 =>
            if Model.isDecDigit c = true then
              match Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest2 with
              | Except.error k => Except.error k
              | Except.ok (mantissa, fracCount, afterFrac) =>
                match afterFrac with
                | 'e' :: afterE =>
                  match Model.parseFloatExpPart afterE with
                  | Except.error k => Except.error k
                  | Except.ok (expVal, afterExp) =>
                    if afterExp.isEmpty = true then
                      Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else Except.error NumParseErrorKind.trailingChars
                | 'E' :: afterE =>
                  match Model.parseFloatExpPart afterE with
                  | Except.error k => Except.error k
                  | Except.ok (expVal, afterExp) =>
                    if afterExp.isEmpty = true then
                      Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                    else Except.error NumParseErrorKind.trailingChars
                | [] => Except.ok (Model.evalFloat neg mantissa (-Int.ofNat fracCount))
                | _ :: _ => Except.error NumParseErrorKind.trailingChars
            else Except.error NumParseErrorKind.invalidSyntax
          | [] => Except.error NumParseErrorKind.invalidSyntax
        | 'e' :: afterE =>
          match Model.parseFloatExpPart afterE with
          | Except.error k => Except.error k
          | Except.ok (expVal, afterExp) =>
            if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
            else Except.error NumParseErrorKind.trailingChars
        | 'E' :: afterE =>
          match Model.parseFloatExpPart afterE with
          | Except.error k => Except.error k
          | Except.ok (expVal, afterExp) =>
            if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
            else Except.error NumParseErrorKind.trailingChars
        | _ => Except.error NumParseErrorKind.invalidSyntax := by
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    rcases decDigit_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Specification for scientific decimal float rendering and round-trip parsing. -/
theorem renderScientific_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let s := Internal.renderScientific neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg mant exp10) := by
  unfold Internal.renderScientific
  have hne := natToDecCharsPos_nonempty hm
  have hall := natToDecCharsPos_all_dec mant
  have hhd := natToDecCharsPos_head_ne_zero hm
  have hev := natToDecCharsPos_eval mant 0
  simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hds : Internal.natToDecCharsPos mant [] with
  | nil => exact absurd hds hne
  | cons d rest =>
    have hd : Model.isDecDigit d = true := hall d (by rw [hds]; simp)
    have hrest : ∀ c ∈ rest, Model.isDecDigit c = true := fun c hc => hall c (by rw [hds]; simp [hc])
    have hd0 : d ≠ '0' := by intro h; subst h; rw [hds] at hhd; exact hhd rfl
    cases rest with
    | nil =>
      simp only []
      have hfold : d.toNat - '0'.toNat = mant := by
        rw [← hev, hds]
        simp [decStep]
      have hnu : ∀ c ∈ (if neg = true then ['-'] else []) ++ [d, 'e'] ++ Internal.formatIntChars exp10, c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · cases neg <;> simp at h1a; subst h1a; decide
          · simp at h1b
            rcases h1b with rfl | rfl
            · exact (decDigit_props hd).1
            · decide
        · exact formatIntChars_all_non_underscore exp10 c h2
      have hhasE : ((if neg = true then ['-'] else []) ++ [d, 'e'] ++ Internal.formatIntChars exp10).contains 'e' = true := by
        simp
      refine ⟨?_, Or.inr (Or.inl ?_), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasE
      · unfold Model.parseFloatModel
        rw [String.toList_ofList, List.append_assoc]
        have hcons : [d, 'e'] ++ Internal.formatIntChars exp10 = d :: 'e' :: Internal.formatIntChars exp10 := rfl
        rw [hcons, parseFloatModelChars_cons_decDigit neg d ('e' :: Internal.formatIntChars exp10) hd]
        have he_nd : Model.isDecDigit 'e' = false := by decide
        have he_nu : 'e' ≠ '_' := by decide
        have hpint := parseFloatIntPart_append_dec [d] (by simp) (fun c hc => by simp at hc; subst hc; exact hd)
          (by simp [hd0]) ('e' :: Internal.formatIntChars exp10)
          (Or.inr ⟨'e', Internal.formatIntChars exp10, rfl, he_nd, he_nu⟩)
        simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStep, Nat.zero_mul,
          Nat.zero_add, hfold] at hpint
        rw [hpint]
        simp only [parseFloatExpPart_formatIntChars]
        rfl
    | cons r0 rs =>
      simp only []
      have hfold : (d :: r0 :: rs).foldl decStep 0 = mant := by
        rw [← hev, hds]
      have hallrest : ∀ c ∈ r0 :: rs, Model.isDecDigit c = true := hrest
      have hnu : ∀ c ∈ (if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
          Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length), c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · rcases List.mem_append.mp h1a with h1aa | h1ab
            · rcases List.mem_append.mp h1aa with h1aaa | h1aab
              · cases neg <;> simp at h1aaa; subst h1aaa; decide
              · simp at h1aab; rcases h1aab with rfl | rfl; exact (decDigit_props hd).1; decide
            · exact (decDigit_props (hallrest c h1ab)).1
          · simp at h1b; subst h1b; decide
        · exact formatIntChars_all_non_underscore _ c h2
      have hhasDot : ((if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
          Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length)).contains '.' = true := by
        simp
      refine ⟨?_, Or.inl ?_, ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasDot
      · unfold Model.parseFloatModel
        rw [String.toList_ofList]
        have hreassoc : (if neg = true then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
            Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length) =
            (if neg = true then ['-'] else []) ++
              d :: ('.' :: ((r0 :: rs) ++ 'e' ::
                Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length))) := by
          simp [List.append_assoc]
        rw [hreassoc, parseFloatModelChars_cons_decDigit neg d _ hd]
        have hdot_nd : Model.isDecDigit '.' = false := by decide
        have hdot_nu : '.' ≠ '_' := by decide
        have hpint := parseFloatIntPart_append_dec [d] (by simp) (fun c hc => by simp at hc; subst hc; exact hd)
          (by simp [hd0]) ('.' :: ((r0 :: rs) ++ 'e' :: Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length)))
          (Or.inr ⟨'.', _, rfl, hdot_nd, hdot_nu⟩)
        simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStep, Nat.zero_mul,
          Nat.zero_add] at hpint
        rw [hpint]
        have hr0 : Model.isDecDigit r0 = true := hallrest r0 (by simp)
        have hr0nu : r0 ≠ '_' := (decDigit_props hr0).1
        have hrs : ∀ c ∈ rs, Model.isDecDigit c = true := fun c hc => hallrest c (by simp [hc])
        have he_nd : Model.isDecDigit 'e' = false := by decide
        have he_nu : 'e' ≠ '_' := by decide
        rw [List.cons_append]
        simp only []
        have hcon := consumeDecFloatDigits_append_dec rs hrs ('e' :: Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length))
          (Or.inr ⟨'e', _, rfl, he_nd, he_nu⟩) ((d.toNat - '0'.toNat) * 10 + (r0.toNat - '0'.toNat)) 1
        have hmant : rs.foldl decStep ((d.toNat - '0'.toNat) * 10 + (r0.toNat - '0'.toNat)) = mant := by
          rw [← hfold]
          simp [List.foldl_cons, decStep]
        have hexp : exp10 + Int.ofNat (r0 :: rs).length - Int.ofNat (1 + rs.length) = exp10 := by
          simp only [List.length_cons, Nat.add_comm rs.length 1]
          omega
        split
        · simp only [hcon, parseFloatExpPart_formatIntChars, List.isEmpty_nil, hmant, hexp, ↓reduceIte]
        · rename_i hnd; exact absurd hr0 hnd

private theorem evalFloat_eq_evalScientificFloat (neg : Bool) (m : Nat) (e : Int) :
    (Model.evalFloat neg m e).toBits = (Internal.evalScientificFloat neg m e).toBits := rfl

private theorem decFold_append (acc : Nat) (xs ys : List Char) :
    (xs ++ ys).foldl decStep acc = ys.foldl decStep (xs.foldl decStep acc) :=
  List.foldl_append

private theorem afterDot_zero (neg : Bool) (intVal : Nat) :
    (match (['.', '0'] : List Char) with
      | '.' :: afterDot =>
        match afterDot with
        | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest2 =>
          if Model.isDecDigit c = true then
            match Model.consumeDecFloatDigits (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest2 with
            | Except.error k => Except.error k
            | Except.ok (mantissa, fracCount, afterFrac) =>
              match afterFrac with
              | 'e' :: afterE =>
                match Model.parseFloatExpPart afterE with
                | Except.error k => Except.error k
                | Except.ok (expVal, afterExp) =>
                  if afterExp.isEmpty = true then
                    Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                  else Except.error NumParseErrorKind.trailingChars
              | 'E' :: afterE =>
                match Model.parseFloatExpPart afterE with
                | Except.error k => Except.error k
                | Except.ok (expVal, afterExp) =>
                  if afterExp.isEmpty = true then
                    Except.ok (Model.evalFloat neg mantissa (expVal - Int.ofNat fracCount))
                  else Except.error NumParseErrorKind.trailingChars
              | [] => Except.ok (Model.evalFloat neg mantissa (-Int.ofNat fracCount))
              | _ :: _ => Except.error NumParseErrorKind.trailingChars
          else Except.error NumParseErrorKind.invalidSyntax
        | [] => Except.error NumParseErrorKind.invalidSyntax
      | 'e' :: afterE =>
        match Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
          else Except.error NumParseErrorKind.trailingChars
      | 'E' :: afterE =>
        match Model.parseFloatExpPart afterE with
        | Except.error k => Except.error k
        | Except.ok (expVal, afterExp) =>
          if afterExp.isEmpty = true then Except.ok (Model.evalFloat neg intVal expVal)
          else Except.error NumParseErrorKind.trailingChars
      | _ => Except.error NumParseErrorKind.invalidSyntax) =
      Except.ok (Model.evalFloat neg (intVal * 10) (-1)) := by
  have h0 : ('0'.toNat - '0'.toNat) = 0 := by decide
  change Except.ok (Model.evalFloat neg (intVal * 10 + ('0'.toNat - '0'.toNat)) (-1)) =
    Except.ok (Model.evalFloat neg (intVal * 10) (-1))
  rw [h0, Nat.add_zero]

private theorem renderFloatChoice_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let (effMant, effExp, s) := Internal.renderFloatChoice neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg effMant effExp) := by
  unfold Internal.renderFloatChoice
  dsimp only
  have hne := natToDecCharsPos_nonempty hm
  have hall := natToDecCharsPos_all_dec mant
  have hhd := natToDecCharsPos_head_ne_zero hm
  have hev := natToDecCharsPos_eval mant 0
  simp only [Nat.zero_mul, Nat.zero_add] at hev
  split
  · split
    · rename_i hexp
      let ds := Internal.natToDecCharsPos mant []
      let pad := exp10.toNat
      let pfx := if neg = true then ['-'] else []
      have hds_ne : ds ++ List.replicate pad '0' ≠ [] := by
        intro h; exact hne (List.append_eq_nil_iff.mp h).1
      have hds_all : ∀ c ∈ ds ++ List.replicate pad '0', Model.isDecDigit c = true := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hall c h1
        · rw [(List.mem_replicate.mp h2).2]; decide
      have hds_hd : (ds ++ List.replicate pad '0').head? ≠ some '0' := by
        cases hds : Internal.natToDecCharsPos mant [] with
        | nil => exact absurd hds hne
        | cons a as =>
          have hds' : ds = a :: as := hds
          rw [hds']
          simp only [List.cons_append, List.head?_cons]
          intro h; apply hhd; rw [hds]; exact h
      have hnu : ∀ c ∈ pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0'], c ≠ '_' := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · rcases List.mem_append.mp h1a with h1aa | h1ab
            · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
            · exact (decDigit_props (hall c h1ab)).1
          · rw [(List.mem_replicate.mp h1b).2]; decide
        · simp at h2; rcases h2 with rfl | rfl <;> decide
      have hhasDot : (pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0']).contains '.' = true := by
        simp
      refine ⟨?_, Or.inl ?_, ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_eq_false_of_forall hnu
      · simp only [String.contains_char_eq, String.toList_ofList]
        exact hhasDot
      · unfold Model.parseFloatModel
        rw [String.toList_ofList]
        change Model.parseFloatModelChars (pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0']) =
          Except.ok (Model.evalFloat neg (mant * 10 ^ (pad + 1)) (-1))
        cases hds' : Internal.natToDecCharsPos mant [] with
        | nil => exact absurd hds' hne
        | cons d0 ds0 =>
          have hd0 : Model.isDecDigit d0 = true := hall d0 (by rw [hds']; exact List.mem_cons_self)
          have hreassoc : pfx ++ ds ++ List.replicate pad '0' ++ ['.', '0'] =
              pfx ++ d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) := by
            change pfx ++ Internal.natToDecCharsPos mant [] ++ List.replicate pad '0' ++ ['.', '0'] = _
            rw [hds']; simp [List.append_assoc]
          rw [hreassoc, parseFloatModelChars_cons_decDigit neg d0 _ hd0]
          have hdot_nd : Model.isDecDigit '.' = false := by decide
          have hdot_nu : '.' ≠ '_' := by decide
          have hpint := parseFloatIntPart_append_dec (ds ++ List.replicate pad '0') hds_ne hds_all hds_hd
            ['.', '0'] (Or.inr ⟨'.', ['0'], rfl, hdot_nd, hdot_nu⟩)
          have hseq : d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) =
              (ds ++ List.replicate pad '0') ++ ['.', '0'] := by
            change d0 :: ((ds0 ++ List.replicate pad '0') ++ ['.', '0']) =
              (Internal.natToDecCharsPos mant [] ++ List.replicate pad '0') ++ ['.', '0']
            rw [hds']; simp [List.append_assoc]
          rw [hseq, hpint]
          dsimp only
          rw [afterDot_zero, decFold_append, hev, decFold_zeros, Nat.pow_succ, Nat.mul_assoc]
    · rename_i hexp
      let ds := Internal.natToDecCharsPos mant []
      let len := ds.length
      let k := (-exp10).toNat
      have hkpos : 0 < k := by
        dsimp only [k]
        cases exp10 with
        | ofNat n => exact absurd (Int.natCast_nonneg n) hexp
        | negSucc n => simp [Int.negSucc_eq]
      have hkeq : (-Int.ofNat k) = exp10 := by
        dsimp only [k]
        cases exp10 with
        | ofNat n => exact absurd (Int.natCast_nonneg n) hexp
        | negSucc n => simp [Int.negSucc_eq]
      split
      · rename_i hklt
        let splitIdx := len - k
        have hsp_pos : 0 < splitIdx := by dsimp only [splitIdx, len, ds, k]; omega
        have hsp_le : splitIdx ≤ len := by dsimp only [splitIdx, len, ds, k]; omega
        let ds1 := ds.take splitIdx
        let ds2 := ds.drop splitIdx
        have hds1_ne : ds1 ≠ [] := by
          intro h
          have hlen0 : ds1.length = 0 := by rw [h]; rfl
          change (ds.take splitIdx).length = 0 at hlen0
          rw [List.length_take, Nat.min_eq_left hsp_le] at hlen0
          omega
        have hds2_len : ds2.length = k := by
          simp [ds2, List.length_drop]
          dsimp only [splitIdx, len, ds, k] at *
          omega
        have hds2_ne : ds2 ≠ [] := by
          intro h; rw [h] at hds2_len; simp at hds2_len; omega
        have hds_split : ds1 ++ ds2 = ds := List.take_append_drop splitIdx ds
        have hds1_all : ∀ c ∈ ds1, Model.isDecDigit c = true := fun c hc => hall c (List.mem_of_mem_take hc)
        have hds2_all : ∀ c ∈ ds2, Model.isDecDigit c = true := fun c hc => hall c (List.mem_of_mem_drop hc)
        have hds1_hd : ds1.head? ≠ some '0' := by
          cases h1 : ds1 with
          | nil => exact absurd h1 hds1_ne
          | cons a as =>
            intro hh
            have hds_hd : ds.head? = some '0' := by
              rw [← hds_split, h1]; exact hh
            exact hhd hds_hd
        let pfx := if neg = true then ['-'] else []
        have hnu : ∀ c ∈ pfx ++ ds1 ++ ['.'] ++ ds2, c ≠ '_' := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · rcases List.mem_append.mp h1a with h1aa | h1ab
              · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
              · exact (decDigit_props (hds1_all c h1ab)).1
            · simp at h1b; subst h1b; decide
          · exact (decDigit_props (hds2_all c h2)).1
        have hhasDot : (pfx ++ ds1 ++ ['.'] ++ ds2).contains '.' = true := by
          simp
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
          exact list_contains_eq_false_of_forall hnu
        · simp only [String.contains_char_eq, String.toList_ofList]
          exact hhasDot
        · unfold Model.parseFloatModel
          rw [String.toList_ofList]
          cases h1 : ds1 with
          | nil => exact absurd h1 hds1_ne
          | cons d0 ds0 =>
            have hd0 : Model.isDecDigit d0 = true := hds1_all d0 (by rw [h1]; simp)
            have hreassoc : pfx ++ (d0 :: ds0) ++ ['.'] ++ ds2 = pfx ++ d0 :: (ds0 ++ '.' :: ds2) := by
              simp [List.append_assoc]
            have hreassoc2 : pfx ++ ds1 ++ ['.'] ++ ds2 = pfx ++ d0 :: (ds0 ++ '.' :: ds2) := by
              rw [h1]; exact hreassoc
            rw [hreassoc2, parseFloatModelChars_cons_decDigit neg d0 _ hd0]
            have hdot_nd : Model.isDecDigit '.' = false := by decide
            have hdot_nu : '.' ≠ '_' := by decide
            have hpint := parseFloatIntPart_append_dec ds1 hds1_ne hds1_all hds1_hd ('.' :: ds2)
              (Or.inr ⟨'.', ds2, rfl, hdot_nd, hdot_nu⟩)
            have hseq : d0 :: (ds0 ++ '.' :: ds2) = ds1 ++ '.' :: ds2 := by rw [h1]; simp
            rw [hseq, hpint]
            cases h2 : ds2 with
            | nil => exact absurd h2 hds2_ne
            | cons f0 frest =>
              have hf0 : Model.isDecDigit f0 = true := hds2_all f0 (by rw [h2]; simp)
              have hf0nu : f0 ≠ '_' := (decDigit_props hf0).1
              have hfrest : ∀ c ∈ frest, Model.isDecDigit c = true := fun c hc => hds2_all c (by rw [h2]; simp [hc])
              simp only []
              split
              · have hcon := consumeDecFloatDigits_append_dec frest hfrest [] (Or.inl rfl)
                  (ds1.foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) 1
                simp only [List.append_nil] at hcon
                rw [hcon]
                have hmant : frest.foldl decStep (ds1.foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) = mant := by
                  have h' : (ds1 ++ (f0 :: frest)).foldl decStep 0 = mant := by
                    rw [← h2, hds_split]; exact hev
                  rw [decFold_append, List.foldl_cons] at h'
                  exact h'
                have hexp' : -Int.ofNat (1 + frest.length) = exp10 := by
                  have hl : 1 + frest.length = k := by
                    rw [← hds2_len, h2]; simp [Nat.add_comm]
                  rw [hl, hkeq]
                simp only [hmant, hexp']
              · rename_i hnd; exact absurd hf0 hnd
      · rename_i hklt
        have hlen_eq : len = (Internal.natToDecCharsPos mant []).length := rfl
        rw [← hlen_eq] at hklt
        let zeros := List.replicate (k - len) '0'
        have hfrac_ne : zeros ++ ds ≠ [] := by
          intro h; exact hne (List.append_eq_nil_iff.mp h).2
        have hfrac_all : ∀ c ∈ zeros ++ ds, Model.isDecDigit c = true := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rw [(List.mem_replicate.mp h1).2]; decide
          · exact hall c h2
        have hfrac_len : (zeros ++ ds).length = k := by
          simp [zeros, len, ds]; omega
        let pfx := if neg = true then ['-'] else []
        have hnu : ∀ c ∈ pfx ++ ['0', '.'] ++ zeros ++ ds, c ≠ '_' := by
          intro c hc
          rcases List.mem_append.mp hc with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · rcases List.mem_append.mp h1a with h1aa | h1ab
              · cases neg <;> simp [pfx] at h1aa; subst h1aa; decide
              · simp at h1ab; rcases h1ab with rfl | rfl <;> decide
            · rw [(List.mem_replicate.mp h1b).2]; decide
          · exact (decDigit_props (hall c h2)).1
        have hhasDot : (pfx ++ ['0', '.'] ++ zeros ++ ds).contains '.' = true := by
          simp
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
          exact list_contains_eq_false_of_forall hnu
        · simp only [String.contains_char_eq, String.toList_ofList]
          exact hhasDot
        · unfold Model.parseFloatModel
          rw [String.toList_ofList]
          have hz_dec : Model.isDecDigit '0' = true := by decide
          have hreassoc : pfx ++ ['0', '.'] ++ zeros ++ ds = pfx ++ '0' :: ('.' :: (zeros ++ ds)) := by
            simp [List.append_assoc]
          rw [hreassoc, parseFloatModelChars_cons_decDigit neg '0' _ hz_dec]
          have hpint0 : Model.parseFloatIntPart ('0' :: '.' :: (zeros ++ ds)) =
              Except.ok (0, '.' :: (zeros ++ ds)) := by
            unfold Model.parseFloatIntPart
            have hd_nd : Model.isDecDigit '.' = false := by decide
            have hd_nu : ('.' == '_') = false := by decide
            simp [hd_nd, hd_nu]
          rw [hpint0]
          cases hf : zeros ++ ds with
          | nil => exact absurd hf hfrac_ne
          | cons f0 frest =>
            have hf0 : Model.isDecDigit f0 = true := hfrac_all f0 (by rw [hf]; simp)
            have hf0nu : f0 ≠ '_' := (decDigit_props hf0).1
            have hfrest : ∀ c ∈ frest, Model.isDecDigit c = true := fun c hc => hfrac_all c (by rw [hf]; simp [hc])
            simp only []
            split
            · have hcon := consumeDecFloatDigits_append_dec frest hfrest [] (Or.inl rfl)
                (0 * 10 + (f0.toNat - '0'.toNat)) 1
              simp only [List.append_nil] at hcon
              rw [hcon]
              have hmant : frest.foldl decStep (0 * 10 + (f0.toNat - '0'.toNat)) = mant := by
                have h' : (zeros ++ ds).foldl decStep 0 = mant := by
                  rw [decFold_append, decFold_zeros_zero]; exact hev
                rw [hf, List.foldl_cons] at h'
                exact h'
              have hexp' : -Int.ofNat (1 + frest.length) = exp10 := by
                have hl : 1 + frest.length = k := by
                  rw [← hfrac_len, hf]; simp [Nat.add_comm]
                rw [hl, hkeq]
              simp only [hmant, hexp']
            · rename_i hnd; exact absurd hf0 hnd
  · exact renderScientific_spec neg mant hm exp10

private theorem stripTrailingZeros_pos {mant : Nat} (hm : 0 < mant) (exp10 : Int) :
    0 < (Internal.stripTrailingZeros mant exp10).1 := by
  induction mant using Nat.strongRecOn generalizing exp10 with
  | ind mant ih =>
    rw [Internal.stripTrailingZeros.eq_def]
    have hnz : mant ≠ 0 := by omega
    simp only [hnz, ↓reduceDIte]
    by_cases hmod : mant % 10 = 0
    · have hbmod : (mant % 10 == 0) = true := beq_iff_eq.mpr hmod
      simp only [hbmod, ↓reduceIte]
      have hge10 : 10 ≤ mant := by omega
      have hdivpos : 0 < mant / 10 := by omega
      have hdivlt : mant / 10 < mant := Nat.div_lt_self hm (by decide)
      exact ih (mant / 10) hdivlt hdivpos (exp10 + 1)
    · have hbmod : (mant % 10 == 0) = false := beq_false_of_ne hmod
      simp only [hbmod, Bool.false_eq_true, ↓reduceIte]
      exact hm

private theorem checkFloatCandidate_spec {x : Float} {neg : Bool} {mant : Nat} {exp10 : Int} {s : String}
    (h : Internal.checkFloatCandidate x neg mant exp10 = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  unfold Internal.checkFloatCandidate at h
  by_cases hz : mant = 0
  · have hbz : (mant == 0) = true := beq_iff_eq.mpr hz
    simp [hbz] at h
  · have hbz : (mant == 0) = false := beq_false_of_ne hz
    simp only [hbz, Bool.false_eq_true, ↓reduceIte] at h
    have hmpos : 0 < mant := Nat.pos_of_ne_zero hz
    have hm'pos : 0 < (Internal.stripTrailingZeros mant exp10).1 := stripTrailingZeros_pos hmpos exp10
    cases hst : Internal.stripTrailingZeros mant exp10 with
    | mk m' e' =>
      rw [hst] at h hm'pos
      have hr := renderFloatChoice_spec neg m' hm'pos e'
      rcases hrc : Internal.renderFloatChoice neg m' e' with ⟨effMant, effExp, str⟩
      rw [hrc] at h hr
      simp only [] at h hr
      by_cases hbits : (Internal.evalScientificFloat neg effMant effExp).toBits = x.toBits
      · have hbbits : ((Internal.evalScientificFloat neg effMant effExp).toBits == x.toBits) = true :=
          beq_iff_eq.mpr hbits
        simp only [hbbits, ↓reduceIte] at h
        injection h with hs
        subst hs
        exact ⟨hr.1, hr.2.1, Model.evalFloat neg effMant effExp, hr.2.2, by
          rw [evalFloat_eq_evalScientificFloat]; exact hbits⟩
      · have hbbits : ((Internal.evalScientificFloat neg effMant effExp).toBits == x.toBits) = false :=
          beq_false_of_ne hbits
        simp [hbbits] at h

private theorem tryDigitsCount_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {d : Nat} {s : String}
    (h : Internal.tryDigitsCount x neg m e2 kEst d = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  have htryOne : ∀ e10 q0,
      (match Internal.checkFloatCandidate x neg q0 e10 with
        | some s => some s
        | none =>
          match Internal.checkFloatCandidate x neg (q0 + 1) e10 with
          | some s => some s
          | none => if 1 < q0 then Internal.checkFloatCandidate x neg (q0 - 1) e10 else none) = some s →
      (!s.contains '_') = true ∧
        (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
        ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
    intro e10 q0 h0
    split at h0
    · injection h0 with hs; subst hs; rename_i hc; exact checkFloatCandidate_spec hc
    · split at h0
      · injection h0 with hs; subst hs; rename_i _ hc; exact checkFloatCandidate_spec hc
      · split at h0
        · exact checkFloatCandidate_spec h0
        · simp at h0
  unfold Internal.tryDigitsCount at h
  simp only [] at h
  split at h
  · injection h with hs; subst hs; rename_i h1
    exact htryOne (kEst - Int.ofNat d + 1) _ h1
  · exact htryOne (kEst - Int.ofNat d + 1 - 1) _ h

/-- Specification for shortest-round-trip float candidate search. -/
theorem searchShortCandidate_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {rem : Nat} {s : String}
    (h : Internal.searchShortCandidate x neg m e2 kEst rem = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  induction rem with
  | zero =>
    rw [Internal.searchShortCandidate.eq_1] at h
    simp at h
  | succ k ih =>
    rw [Internal.searchShortCandidate.eq_2] at h
    split at h
    · injection h with hs; subst hs; rename_i ht
      exact tryDigitsCount_spec ht
    · exact ih h

end LeanSwe.NumParse.Proofs

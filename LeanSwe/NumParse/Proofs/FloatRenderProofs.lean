import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.IntProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem decFold_zeros (acc k : Nat) :
    (List.replicate k '0').foldl decStep acc = acc * 10 ^ k := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, decStep]
    rw [show '0'.toNat - '0'.toNat = 0 by decide, Nat.add_zero, ih (acc * 10),
        Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]

private theorem list_contains_false_of_forall {cs : List Char} {x : Char}
    (h : ∀ c ∈ cs, c ≠ x) : cs.contains x = false := by
  simp only [Bool.eq_false_iff]; intro hc; exact absurd rfl (h x (List.contains_iff_mem.mp hc))

private theorem consumeDecFloatDigits_append_dec
    (ds : List Char) (hds : ∀ c ∈ ds, isDecDigit c = true) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ isDecDigit r0 = false ∧ r0 ≠ '_')
    (acc count : Nat) :
    consumeDecFloatDigits acc count (ds ++ rest) = .ok (ds.foldl decStep acc, count + ds.length, rest) := by
  induction ds generalizing acc count with
  | nil =>
    simp only [List.nil_append, List.foldl_nil, List.length_nil, Nat.add_zero]
    rcases hrest with rfl | ⟨r0, rem, rfl, hnd, hnu⟩
    · rw [consumeDecFloatDigits.eq_1]
    · rw [consumeDecFloatDigits.eq_4 acc count r0 rem (fun _ _ h => absurd h hnu) (fun h => absurd h hnu)]; simp [hnd]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have hdnu : d ≠ '_' := decDigit_ne_of_false hd (by decide)
    rw [List.cons_append, consumeDecFloatDigits.eq_4 acc count d (ds ++ rest)
      (fun _ _ h => absurd h hdnu) (fun h => absurd h hdnu)]
    simp only [hd, ↓reduceIte, List.foldl_cons, List.length_cons, decStep]
    rw [ih (fun c hc => hds c (by simp [hc])) (acc * 10 + (d.toNat - '0'.toNat)) (count + 1),
        show count + 1 + ds.length = count + (ds.length + 1) by omega]

private theorem parseFloatIntPart_valid
    (ds : List Char) (hne : ds ≠ []) (hds : ∀ c ∈ ds, isDecDigit c = true)
    (hhead : ds = ['0'] ∨ ds.head? ≠ some '0')
    (r0 : Char) (rem : List Char) (hr0_nd : isDecDigit r0 = false) (hr0_nu : r0 ≠ '_') :
    parseFloatIntPart (ds ++ r0 :: rem) = .ok (ds.foldl decStep 0, r0 :: rem) := by
  rcases hhead with rfl | hhd
  · simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStep, Nat.zero_mul, Nat.zero_add,
      show '0'.toNat - '0'.toNat = 0 by decide]
    unfold parseFloatIntPart; simp [hr0_nd, beq_false_of_ne hr0_nu]
  · cases ds with
    | nil => exact absurd rfl hne
    | cons d ds =>
      have hd := hds d (by simp)
      have hdz : d ≠ '0' := fun h => hhd (by simp [h])
      have hdnu : d ≠ '_' := decDigit_ne_of_false hd (by decide)
      rw [List.cons_append, parseFloatIntPart.eq_5 d (ds ++ r0 :: rem) hdnu hdz]
      simp only [hd, ↓reduceIte]
      rw [consumeDecFloatDigits_append_dec ds (fun c hc => hds c (by simp [hc])) (r0 :: rem)
        (Or.inr ⟨r0, rem, rfl, hr0_nd, hr0_nu⟩) (d.toNat - '0'.toNat) 1]
      simp [decStep]

private theorem parseFloatExpPart_digit_list (ds : List Char) (hne : ds ≠ [])
    (hds : ∀ c ∈ ds, isDecDigit c = true) :
    parseFloatExpPart ds = .ok (Int.ofNat (ds.foldl decStep 0), []) ∧
      parseFloatExpPart ('-' :: ds) = .ok (-Int.ofNat (ds.foldl decStep 0), []) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd := hds d (by simp)
    have hp : d ≠ '+' := decDigit_ne_of_false hd (by decide)
    have hm : d ≠ '-' := decDigit_ne_of_false hd (by decide)
    have hu : d ≠ '_' := decDigit_ne_of_false hd (by decide)
    have hcon := consumeDecFloatDigits_append_dec ds (fun c hc => hds c (by simp [hc])) [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
    simp only [List.append_nil] at hcon
    have hfold : ds.foldl decStep (d.toNat - '0'.toNat) = (d :: ds).foldl decStep 0 := by simp [decStep]
    have hmatch : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (d :: ds)
        (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, d :: ds))) = (false, d :: ds) := by
      split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
    have hstep : ∀ (neg : Bool),
        parseFloatExpPart ((if neg then '-' else '+') :: d :: ds) =
          .ok (if neg then -Int.ofNat ((d :: ds).foldl decStep 0) else Int.ofNat ((d :: ds).foldl decStep 0), []) := by
      intro neg
      have hs : parseFloatExpPart.match_1 (fun _ => Bool × List Char) ((if neg then '-' else '+') :: d :: ds)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, (if neg then '-' else '+') :: d :: ds)) = (neg, d :: ds) := by
        cases neg <;> rfl
      unfold parseFloatExpPart; dsimp only; rw [hs]; dsimp only
      split
      · contradiction
      · rename_i h; exact absurd (List.cons.inj h).1 hu
      · rename_i c rest _ h; rcases List.cons.inj h with ⟨rfl, rfl⟩
        simp only [hd, ↓reduceIte]; rw [hcon, hfold]
    have hpos : parseFloatExpPart (d :: ds) = parseFloatExpPart ('+' :: d :: ds) := by
      unfold parseFloatExpPart; dsimp only; rw [hmatch]; rfl
    exact ⟨by rw [hpos]; simpa using hstep false, by simpa using hstep true⟩

private theorem parseFloatExpPart_formatIntChars (e : Int) :
    parseFloatExpPart (Internal.formatIntChars e) = .ok (e, []) := by
  cases e with
  | ofNat n =>
    cases n with
    | zero => exact (parseFloatExpPart_digit_list ['0'] (by simp) (by simp; decide)).1
    | succ m =>
      have h := (parseFloatExpPart_digit_list (Internal.natToDecCharsPos (m + 1) [])
        (natToDecCharsPos_nonempty (Nat.succ_pos m)) (natToDecCharsPos_all_dec (m + 1))).1
      have hev := natToDecCharsPos_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
      rw [hev] at h; exact h
  | negSucc m =>
    have h := (parseFloatExpPart_digit_list (Internal.natToDecCharsPos (m + 1) [])
      (natToDecCharsPos_nonempty (Nat.succ_pos m)) (natToDecCharsPos_all_dec (m + 1))).2
    have hev := natToDecCharsPos_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
    rw [hev] at h; exact h

private theorem formatIntChars_ne_underscore (e : Int) :
    ∀ c ∈ Internal.formatIntChars e, c ≠ '_' := by
  unfold Internal.formatIntChars
  cases e with
  | ofNat n =>
    cases n with
    | zero => intro c hc; simp at hc; subst hc; decide
    | succ m => intro c hc; exact decDigit_ne_of_false (natToDecCharsPos_all_dec (m + 1) c hc) (by decide)
  | negSucc n =>
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact decDigit_ne_of_false (natToDecCharsPos_all_dec (n + 1) c hc) (by decide)

private theorem parseFloatModelChars_pfx_eq (neg : Bool) (d : Char) (rest : List Char)
    (hd : isDecDigit d = true) :
    parseFloatModelChars ((if neg then ['-'] else []) ++ d :: rest) =
      parseFloatModelChars ((if neg then '-' else '+') :: d :: rest) := by
  cases neg with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    have hp : d ≠ '+' := decDigit_ne_of_false hd (by decide)
    have hm : d ≠ '-' := decDigit_ne_of_false hd (by decide)
    have hmatch : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (d :: rest)
        (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, d :: rest))) = (false, d :: rest) := by
      split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
    unfold parseFloatModelChars; dsimp only; rw [hmatch]; rfl

private theorem parseFloatModel_withDot (neg : Bool) (intDs fracDs : List Char) (exp? : Option Int)
    (hint_ne : intDs ≠ []) (hint_dec : ∀ c ∈ intDs, isDecDigit c = true)
    (hint_hd : intDs = ['0'] ∨ intDs.head? ≠ some '0')
    (hfrac_ne : fracDs ≠ []) (hfrac_dec : ∀ c ∈ fracDs, isDecDigit c = true) :
    let pfx := if neg then ['-'] else []
    let expTail := match exp? with | none => [] | some e => 'e' :: Internal.formatIntChars e
    let s := String.ofList (pfx ++ intDs ++ '.' :: fracDs ++ expTail)
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      parseFloatModel s = .ok (evalFloat neg ((intDs ++ fracDs).foldl decStep 0)
        (match exp? with | none => -Int.ofNat fracDs.length | some e => e - Int.ofNat fracDs.length)) := by
  cases intDs with
  | nil => exact absurd rfl hint_ne
  | cons d0 ds0 =>
    cases fracDs with
    | nil => exact absurd rfl hfrac_ne
    | cons f0 frest =>
      dsimp only
      let pfx := if neg then ['-'] else []
      let expTail := match exp? with | none => [] | some e => 'e' :: Internal.formatIntChars e
      have hnu : ∀ c ∈ pfx ++ (d0 :: ds0) ++ '.' :: (f0 :: frest) ++ expTail, c ≠ '_' := by
        intro c hc; simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with ((h1 | (rfl | h1)) | (rfl | rfl | h1)) | h1
        · cases neg <;> simp [pfx] at h1; subst h1; decide
        · exact decDigit_ne_of_false (hint_dec c (by simp)) (by decide)
        · exact decDigit_ne_of_false (hint_dec c (by simp [h1])) (by decide)
        · decide
        · exact decDigit_ne_of_false (hfrac_dec c (by simp)) (by decide)
        · exact decDigit_ne_of_false (hfrac_dec c (by simp [h1])) (by decide)
        · cases exp? with
          | none => simp [expTail] at h1
          | some e => rcases List.mem_cons.mp h1 with rfl | h1'; decide; exact formatIntChars_ne_underscore e c h1'
      refine ⟨?_, Or.inl (by simp [String.contains_char_eq, String.toList_ofList]), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_false_of_forall hnu
      · unfold parseFloatModel; rw [String.toList_ofList]
        have hd0 := hint_dec d0 (by simp)
        have hre : pfx ++ (d0 :: ds0) ++ '.' :: (f0 :: frest) ++ expTail =
            pfx ++ d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)) := by simp [List.append_assoc]
        rw [hre, parseFloatModelChars_pfx_eq neg d0 _ hd0]
        have hsign : parseFloatExpPart.match_1 (fun _ => Bool × List Char)
            ((if neg then '-' else '+') :: d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)))
            (fun r => (false, r)) (fun r => (true, r))
            (fun _ => (false, (if neg then '-' else '+') :: d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)))) =
            (neg, d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail))) := by
          cases neg <;> rfl
        unfold parseFloatModelChars; dsimp only; rw [hsign]; dsimp only
        have hi : d0 ≠ 'i' := decDigit_ne_of_false hd0 (by decide)
        have hn : d0 ≠ 'n' := decDigit_ne_of_false hd0 (by decide)
        split
        · rename_i h; exact absurd (List.cons.inj h).1 hi
        · rename_i h; exact absurd (List.cons.inj h).1 hn
        · have hpint := parseFloatIntPart_valid (d0 :: ds0) hint_ne hint_dec hint_hd '.' ((f0 :: frest) ++ expTail) (by decide) (by decide)
          rw [show d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)) = (d0 :: ds0) ++ '.' :: ((f0 :: frest) ++ expTail) by simp, hpint]
          have hf0 := hfrac_dec f0 (by simp)
          have htail : expTail = [] ∨ ∃ r0 rem, expTail = r0 :: rem ∧ isDecDigit r0 = false ∧ r0 ≠ '_' := by
            cases exp? with | none => exact Or.inl rfl | some e => exact Or.inr ⟨'e', Internal.formatIntChars e, rfl, by decide, by decide⟩
          have hcon := consumeDecFloatDigits_append_dec frest (fun c hc => hfrac_dec c (by simp [hc])) expTail
            htail ((d0 :: ds0).foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) 1
          have hmant : frest.foldl decStep ((d0 :: ds0).foldl decStep 0 * 10 + (f0.toNat - '0'.toNat)) =
              ((d0 :: ds0) ++ f0 :: frest).foldl decStep 0 := by rw [List.foldl_append, List.foldl_cons]; rfl
          have hlen : 1 + frest.length = (f0 :: frest).length := by simp [Nat.add_comm]
          rw [List.cons_append]; simp only []
          have hf0u : f0 ≠ '_' := decDigit_ne_of_false hf0 (by decide)
          split
          · rename_i h; exact absurd (List.cons.inj h).1 hf0u
          · rename_i c rest2 _ h; rcases List.cons.inj h with ⟨rfl, rfl⟩
            simp only [hf0, ↓reduceIte, hcon, hmant, hlen]
            cases exp? with
            | none => rfl
            | some e => simp only [expTail, parseFloatExpPart_formatIntChars, List.isEmpty_nil, ↓reduceIte]
          · rename_i h; cases h

/-- Specification for scientific decimal float rendering and round-trip parsing. -/
theorem renderScientific_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let s := Internal.renderScientific neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg mant exp10) := by
  unfold Internal.renderScientific
  have hall := natToDecCharsPos_all_dec mant
  have hhd := natToDecCharsPos_head_ne_zero hm
  have hev := natToDecCharsPos_eval mant 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hds : Internal.natToDecCharsPos mant [] with
  | nil => exact absurd hds (natToDecCharsPos_nonempty hm)
  | cons d rest =>
    rw [hds] at hall hhd hev
    have hd : isDecDigit d = true := hall d (by simp)
    have hd0 : d ≠ '0' := fun h => hhd (by simp [h])
    cases rest with
    | nil =>
      let pfx := if neg then ['-'] else []
      have hnu : ∀ c ∈ pfx ++ [d, 'e'] ++ Internal.formatIntChars exp10, c ≠ '_' := by
        intro c hc; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with (h1 | rfl | rfl) | h2
        · cases neg <;> simp [pfx] at h1; subst h1; decide
        · exact decDigit_ne_of_false hd (by decide)
        · decide
        · exact formatIntChars_ne_underscore exp10 c h2
      refine ⟨?_, Or.inr (Or.inl (by simp [String.contains_char_eq, String.toList_ofList])), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_false_of_forall hnu
      · unfold parseFloatModel; rw [String.toList_ofList, List.append_assoc]
        change parseFloatModelChars (pfx ++ d :: 'e' :: Internal.formatIntChars exp10) = _
        rw [parseFloatModelChars_pfx_eq neg d _ hd]
        have hsign : parseFloatExpPart.match_1 (fun _ => Bool × List Char)
            ((if neg then '-' else '+') :: d :: 'e' :: Internal.formatIntChars exp10)
            (fun r => (false, r)) (fun r => (true, r))
            (fun _ => (false, (if neg then '-' else '+') :: d :: 'e' :: Internal.formatIntChars exp10)) =
            (neg, d :: 'e' :: Internal.formatIntChars exp10) := by
          cases neg <;> rfl
        unfold parseFloatModelChars; dsimp only; rw [hsign]; dsimp only
        split
        · rename_i h; exact absurd (List.cons.inj h).1 (decDigit_ne_of_false hd (by decide))
        · rename_i h; exact absurd (List.cons.inj h).1 (decDigit_ne_of_false hd (by decide))
        · have hpint := parseFloatIntPart_valid [d] (by simp) (by simpa using hd) (Or.inr (by simp [hd0]))
            'e' (Internal.formatIntChars exp10) (by decide) (by decide)
          rw [show d :: 'e' :: Internal.formatIntChars exp10 = [d] ++ 'e' :: Internal.formatIntChars exp10 from rfl, hpint, hev]
          simp [parseFloatExpPart_formatIntChars]
    | cons r0 rs =>
      have hspec := parseFloatModel_withDot neg [d] (r0 :: rs) (some (exp10 + Int.ofNat (r0 :: rs).length))
        (by simp) (by simpa using hd) (Or.inr (by simp [hd0])) (by simp) (fun c hc => hall c (by simp [hc]))
      have hre : (if neg then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
            Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length) =
          (if neg then ['-'] else []) ++ [d] ++ '.' :: (r0 :: rs) ++ 'e' ::
            Internal.formatIntChars (exp10 + Int.ofNat (r0 :: rs).length) := by simp [List.append_assoc]
      have hfold : ([d] ++ (r0 :: rs)).foldl decStep 0 = mant := hev
      have hexp : exp10 + Int.ofNat (r0 :: rs).length - Int.ofNat (r0 :: rs).length = exp10 := by omega
      dsimp only at hspec ⊢; rw [hre]; rw [hfold, hexp] at hspec; exact hspec

private theorem renderFloatChoice_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let (effMant, effExp, s) := Internal.renderFloatChoice neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      Model.parseFloatModel s = Except.ok (Model.evalFloat neg effMant effExp) := by
  unfold Internal.renderFloatChoice; dsimp only
  let ds := Internal.natToDecCharsPos mant []
  have hne : ds ≠ [] := natToDecCharsPos_nonempty hm
  have hall : ∀ c ∈ ds, isDecDigit c = true := natToDecCharsPos_all_dec mant
  have hhd : ds.head? ≠ some '0' := natToDecCharsPos_head_ne_zero hm
  have hev : ds.foldl decStep 0 = mant := by simpa using natToDecCharsPos_eval mant 0
  split
  · split
    · let pad := exp10.toNat
      have hhead : (ds ++ List.replicate pad '0').head? ≠ some '0' := by
        cases h : ds with | nil => exact absurd h hne | cons a as => simpa [h] using hhd
      have hspec := parseFloatModel_withDot neg (ds ++ List.replicate pad '0') ['0'] none
        (fun h => hne (List.append_eq_nil_iff.mp h).1)
        (fun c hc => by rcases List.mem_append.mp hc with h | h; exact hall c h; rw [(List.mem_replicate.mp h).2]; decide)
        (Or.inr hhead) (by simp) (by simp; decide)
      have hfold : ((ds ++ List.replicate pad '0') ++ ['0']).foldl decStep 0 = mant * 10 ^ (pad + 1) := by
        rw [List.foldl_append, List.foldl_append, hev, decFold_zeros]
        simp only [List.foldl_cons, List.foldl_nil, decStep, show '0'.toNat - '0'.toNat = 0 by decide,
          Nat.add_zero, Nat.pow_succ, Nat.mul_assoc]
      have hre : (if neg then ['-'] else []) ++ ds ++ List.replicate pad '0' ++ ['.', '0'] =
          (if neg then ['-'] else []) ++ (ds ++ List.replicate pad '0') ++ '.' :: ['0'] ++ [] := by simp [List.append_assoc]
      dsimp only at hspec ⊢; rw [hre]; rw [hfold] at hspec; exact hspec
    · rename_i hexp
      let k := (-exp10).toNat
      have hkpos : 0 < k := by dsimp only [k]; cases exp10 with | ofNat n => exact absurd (Int.natCast_nonneg n) hexp | negSucc n => simp [Int.negSucc_eq]
      have hkeq : -Int.ofNat k = exp10 := by dsimp only [k]; cases exp10 with | ofNat n => exact absurd (Int.natCast_nonneg n) hexp | negSucc n => simp [Int.negSucc_eq]
      split
      · rename_i hklt
        let ds1 := ds.take (ds.length - k); let ds2 := ds.drop (ds.length - k)
        have hsplit : ds1 ++ ds2 = ds := List.take_append_drop _ ds
        have hds1_ne : ds1 ≠ [] := by
          intro h; have hl := congrArg List.length h; simp only [ds1, List.length_take, List.length_nil] at hl
          have : k < ds.length := hklt; omega
        have hds2_len : ds2.length = k := by simp only [ds2, List.length_drop]; have : k < ds.length := hklt; omega
        have hds2_ne : ds2 ≠ [] := by intro h; rw [h] at hds2_len; simp at hds2_len; omega
        have hds1_hd : ds1.head? ≠ some '0' := by
          cases h1 : ds1 with | nil => exact absurd h1 hds1_ne | cons a as => intro hh; apply hhd; rw [← hsplit, h1]; exact hh
        have hspec := parseFloatModel_withDot neg ds1 ds2 none hds1_ne
          (fun c hc => hall c (List.mem_of_mem_take hc)) (Or.inr hds1_hd) hds2_ne
          (fun c hc => hall c (List.mem_of_mem_drop hc))
        have hre : (if neg then ['-'] else []) ++ ds1 ++ ['.'] ++ ds2 =
            (if neg then ['-'] else []) ++ ds1 ++ '.' :: ds2 ++ [] := by simp [List.append_assoc]
        dsimp only at hspec ⊢; rw [hre]; rw [hsplit, hev, hds2_len, hkeq] at hspec; exact hspec
      · rename_i hklt
        let zeros := List.replicate (k - ds.length) '0'
        have hspec := parseFloatModel_withDot neg ['0'] (zeros ++ ds) none (by simp) (by simp; decide)
          (Or.inl rfl) (fun h => hne (List.append_eq_nil_iff.mp h).2)
          (fun c hc => by rcases List.mem_append.mp hc with h | h; rw [(List.mem_replicate.mp h).2]; decide; exact hall c h)
        have hfold : (['0'] ++ (zeros ++ ds)).foldl decStep 0 = mant := by
          rw [List.foldl_append, List.foldl_append]
          rw [show (['0']).foldl decStep 0 = 0 by decide, decFold_zeros, Nat.zero_mul, hev]
        have hlen : (zeros ++ ds).length = k := by
          simp only [zeros, List.length_append, List.length_replicate]
          have : ds.length ≤ k := Nat.le_of_not_lt hklt; omega
        have hre : (if neg then ['-'] else []) ++ ['0', '.'] ++ zeros ++ ds =
            (if neg then ['-'] else []) ++ ['0'] ++ '.' :: (zeros ++ ds) ++ [] := by simp [List.append_assoc]
        dsimp only at hspec ⊢; rw [hre]; rw [hfold, hlen, hkeq] at hspec; exact hspec
  · exact renderScientific_spec neg mant hm exp10

private theorem stripTrailingZeros_pos {mant : Nat} (hm : 0 < mant) (exp10 : Int) :
    0 < (Internal.stripTrailingZeros mant exp10).1 := by
  induction mant using Nat.strongRecOn generalizing exp10 with
  | ind mant ih =>
    rw [Internal.stripTrailingZeros.eq_def]
    simp only [show mant ≠ 0 by omega, ↓reduceDIte]
    by_cases hmod : mant % 10 = 0
    · simp only [beq_iff_eq.mpr hmod, ↓reduceIte]
      exact ih (mant / 10) (Nat.div_lt_self hm (by decide)) (by omega) (exp10 + 1)
    · simp only [beq_false_of_ne hmod, Bool.false_eq_true, ↓reduceIte]; exact hm

private theorem checkFloatCandidate_spec {x : Float} {neg : Bool} {mant : Nat} {exp10 : Int} {s : String}
    (h : Internal.checkFloatCandidate x neg mant exp10 = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  unfold Internal.checkFloatCandidate at h
  by_cases hz : mant = 0
  · simp [hz] at h
  · simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte] at h
    have hm'pos := stripTrailingZeros_pos (Nat.pos_of_ne_zero hz) exp10
    rcases hst : Internal.stripTrailingZeros mant exp10 with ⟨m', e'⟩
    rw [hst] at h hm'pos
    have hr := renderFloatChoice_spec neg m' hm'pos e'
    rcases hrc : Internal.renderFloatChoice neg m' e' with ⟨effMant, effExp, str⟩
    rw [hrc] at h hr; simp only [] at h hr
    by_cases hbits : (Internal.evalModelFloat neg effMant effExp).toBits = x.toBits
    · simp only [beq_iff_eq.mpr hbits, ↓reduceIte] at h
      injection h with hs; subst hs
      exact ⟨hr.1, hr.2.1, evalFloat neg effMant effExp, hr.2.2, hbits⟩
    · simp [beq_false_of_ne hbits] at h

private theorem tryDigitsCount_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {d : Nat} {s : String}
    (h : Internal.tryDigitsCount x neg m e2 kEst d = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  have htry : ∀ e10 q0,
      (match Internal.checkFloatCandidate x neg q0 e10 with
        | some s => some s
        | none => match Internal.checkFloatCandidate x neg (q0 + 1) e10 with
          | some s => some s
          | none => if 1 < q0 then Internal.checkFloatCandidate x neg (q0 - 1) e10 else none) = some s →
      (!s.contains '_') = true ∧ (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
        ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
    intro e10 q0 h0
    split at h0
    · injection h0 with hs; subst hs; exact checkFloatCandidate_spec ‹_›
    · split at h0
      · injection h0 with hs; subst hs; exact checkFloatCandidate_spec ‹_›
      · split at h0
        · exact checkFloatCandidate_spec h0
        · cases h0
  unfold Internal.tryDigitsCount at h; simp only [] at h
  split at h
  · injection h with hs; subst hs; exact htry _ _ ‹_›
  · exact htry _ _ h

/-- Specification for shortest-round-trip float candidate search. -/
theorem searchShortCandidate_spec {x : Float} {neg : Bool} {m : Nat} {e2 kEst : Int} {rem : Nat} {s : String}
    (h : Internal.searchShortCandidate x neg m e2 kEst rem = some s) :
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      ∃ y : Float, Model.parseFloatModel s = Except.ok y ∧ y.toBits = x.toBits := by
  induction rem with
  | zero => rw [Internal.searchShortCandidate.eq_1] at h; cases h
  | succ k ih =>
    rw [Internal.searchShortCandidate.eq_2] at h
    split at h
    · injection h with hs; subst hs; exact tryDigitsCount_spec ‹_›
    · exact ih h

end LeanSwe.NumParse.Proofs

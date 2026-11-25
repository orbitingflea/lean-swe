import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- `Internal.makeError` always produces a non-empty message. -/
theorem makeError_msg_ne_empty (k : NumParseErrorKind) (detail : String) :
    (Internal.makeError k detail).message ≠ "" := by
  unfold Internal.makeError; intro heq
  have hlen := congrArg String.length heq; simp only [String.length_append] at hlen
  have : (": " : String).length = 2 := rfl; have : ("" : String).length = 0 := rfl; omega

/-- Mapping `.kind` over `Internal.makeError` yields `Except.error k`. -/
theorem mapError_makeError {α : Type} (k : NumParseErrorKind) (detail : String) :
    (Except.error (Internal.makeError k detail) : Except NumParseError α).mapError (·.kind) = .error k := rfl

/-- `Internal.isDecDigit` agrees with `Model.isDecDigit`. -/
theorem isDecDigit_eq (c : Char) : Internal.isDecDigit c = isDecDigit c := rfl

/-- Extract an implementation `ok` result from a mapped model `ok` result. -/
theorem impl_eq_ok_of_mapError {α : Type} {impl : Except NumParseError α}
    {model : Except NumParseErrorKind α} {v : α}
    (hm : impl.mapError (·.kind) = model) (hv : model = .ok v) : impl = .ok v := by
  cases h : impl <;> simp [h, Except.mapError, hv] at hm ⊢; exact hm

/-- Extract an implementation `error` witness from a mapped model `error` result. -/
theorem impl_eq_error_of_mapError {α : Type} {impl : Except NumParseError α}
    {model : Except NumParseErrorKind α} {k : NumParseErrorKind}
    (hm : impl.mapError (·.kind) = model) (hk : model = .error k) :
    ∃ e, impl = .error e ∧ e.kind = k := by
  cases h : impl <;> simp [h, Except.mapError, hk] at hm ⊢; exact hm

/-- Any decimal digit differs from any non-decimal character. -/
theorem decDigit_ne_of_false {c x : Char} (hc : isDecDigit c = true) (hx : isDecDigit x = false) : c ≠ x := by
  intro h; subst h; rw [hx] at hc; cases hc

/-- Single decimal accumulation step over ASCII digit characters. -/
def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

private theorem char_ofNat_decDigit (d : Nat) (hd : d < 10) :
    isDecDigit (Char.ofNat ('0'.toNat + d)) = true ∧
      (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d :=
  (by decide : ∀ x : Fin 10,
    isDecDigit (Char.ofNat ('0'.toNat + x.1)) = true ∧
      (Char.ofNat ('0'.toNat + x.1)).toNat - '0'.toNat = x.1) ⟨d, hd⟩

private theorem natToDecCharsPos_append (n : Nat) (acc : List Char) :
    Internal.natToDecCharsPos n acc = Internal.natToDecCharsPos n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, Internal.natToDecCharsPos.eq_2]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [ih _ hlt (Char.ofNat ('0'.toNat + (m + 1) % 10) :: acc),
          ih _ hlt [Char.ofNat ('0'.toNat + (m + 1) % 10)]]
      simp [List.append_assoc]

/-- Folding `decStep` over `natToDecCharsPos n []` shifts `acc` and adds `n`. -/
theorem natToDecCharsPos_eval (n acc : Nat) :
    (Internal.natToDecCharsPos n []).foldl decStep acc =
      acc * 10 ^ (Internal.natToDecCharsPos n []).length + n := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append, List.foldl_append,
          ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) acc]
      have hd := (char_ofNat_decDigit ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2
      simp only [List.foldl_cons, List.foldl_nil, decStep, List.length_append, List.length_singleton, hd]
      rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]; omega

/-- Every character emitted by `Internal.natToDecCharsPos` is a decimal digit. -/
theorem natToDecCharsPos_all_dec (n : Nat) :
    ∀ c ∈ Internal.natToDecCharsPos n [], isDecDigit c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [Internal.natToDecCharsPos.eq_1]
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) c h1
      · simp only [List.mem_singleton] at h2; subst h2
        exact (char_ofNat_decDigit _ (Nat.mod_lt _ (by decide))).1

/-- `Internal.natToDecCharsPos` is non-empty for positive `n`. -/
theorem natToDecCharsPos_nonempty {n : Nat} (hn : 0 < n) :
    Internal.natToDecCharsPos n [] ≠ [] := by
  cases n with | zero => omega | succ m => rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]; simp

/-- `Internal.natToDecCharsPos` never emits a leading `'0'` for positive `n`. -/
theorem natToDecCharsPos_head_ne_zero {n : Nat} (hn : 0 < n) :
    (Internal.natToDecCharsPos n []).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [Internal.natToDecCharsPos.eq_2, natToDecCharsPos_append]
      by_cases hq : (m + 1) / 10 = 0
      · rw [hq, Internal.natToDecCharsPos.eq_1, List.nil_append]
        intro heq
        have hsub := congrArg (fun x : Char => x.toNat - '0'.toNat) (Option.some.inj heq)
        rw [(char_ofNat_decDigit ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2,
            show '0'.toNat - '0'.toNat = 0 from rfl] at hsub
        omega
      · have hqpos : 0 < (m + 1) / 10 := Nat.pos_of_ne_zero hq
        cases hql : Internal.natToDecCharsPos ((m + 1) / 10) [] with
        | nil => exact absurd hql (natToDecCharsPos_nonempty hqpos)
        | cons x xs =>
          simpa [hql] using ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) hqpos

private theorem digitValue_eq_digitVal (b : NumBase) (c : Char) :
    Internal.digitValue? b.radix c = digitVal? b c := by
  cases b <;> rfl

private theorem parseBasePrefix_eq_basePrefix (c : Char) :
    Internal.parseBasePrefix? c = Option.map NumBase.radix (basePrefix? c) := by
  unfold Internal.parseBasePrefix? basePrefix?; split <;> simp [NumBase.radix]

private theorem err_spec (k : NumParseErrorKind) (raw : String) {α : Type} :
    (Except.error (Internal.makeError k raw) : Except NumParseError α).mapError (·.kind) = .error k ∧
      ∀ e, (Except.error (Internal.makeError k raw) : Except NumParseError α) = .error e → e.message ≠ "" :=
  ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩

private theorem evalPairsLinear_append (acc : Nat) (xs ys : List (Nat × Nat)) :
    Internal.evalPairsLinear acc (xs ++ ys) = Internal.evalPairsLinear (Internal.evalPairsLinear acc xs) ys := by
  induction xs generalizing acc with | nil => rfl | cons x xs ih => exact ih (acc * x.2 + x.1)

private theorem mergePairsRev_eval (a : Nat) (acc xs : List (Nat × Nat)) :
    Internal.evalPairsLinear a (Internal.mergePairsRev acc xs) =
      Internal.evalPairsLinear (Internal.evalPairsLinear a acc.reverse) xs := by
  fun_induction Internal.mergePairsRev acc xs with
  | case1 _ _ _ _ _ _ ih =>
    rw [ih, List.reverse_cons, evalPairsLinear_append]; dsimp [Internal.evalPairsLinear]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | case2 => rw [List.reverse_cons, evalPairsLinear_append]
  | case3 => rfl

private theorem evalWeightedPairsFuel_eq (fuel : Nat) (xs : List (Nat × Nat)) :
    Internal.evalWeightedPairsFuel fuel xs = Internal.evalPairsLinear 0 xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    rcases xs with _ | ⟨⟨v, p⟩, _ | ⟨b, rest⟩⟩
    · rfl
    · simp [Internal.evalWeightedPairsFuel, Internal.evalPairsLinear]
    · simp only [Internal.evalWeightedPairsFuel, ih, mergePairsRev_eval]; rfl

private def chunkVal (radix : Nat) (chunksRev : List (Nat × Nat)) (chunkAcc chunkLen : Nat) : Nat :=
  Internal.evalPairsLinear 0 chunksRev.reverse * radix ^ chunkLen + chunkAcc

private theorem chunkVal_flush (radix : Nat) (chunksRev : List (Nat × Nat)) (chunkAcc k d : Nat) :
    chunkVal radix ((chunkAcc, radix ^ k) :: chunksRev) d 1 = chunkVal radix chunksRev chunkAcc k * radix + d := by
  simp [chunkVal, evalPairsLinear_append, Internal.evalPairsLinear]

private theorem chunkVal_step (radix : Nat) (chunksRev : List (Nat × Nat)) (chunkAcc chunkLen d : Nat) :
    chunkVal radix chunksRev (chunkAcc * radix + d) (chunkLen + 1) = chunkVal radix chunksRev chunkAcc chunkLen * radix + d := by
  simp only [chunkVal, Nat.pow_succ]; rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem intChunkBase_eq (b : NumBase) : Internal.intChunkBase b.radix = b.radix ^ 15 := by cases b <;> rfl

private theorem scanIntDigitsLoop_spec (raw : String) (b : NumBase)
    (chunksRev : List (Nat × Nat)) (chunkAcc chunkLen : Nat) (cs : List Char) :
    (Internal.scanIntDigitsLoop raw b.radix (b.radix ^ 15) chunksRev chunkAcc chunkLen cs).mapError (·.kind) =
        consumeIntDigits b (chunkVal b.radix chunksRev chunkAcc chunkLen) cs ∧
      ∀ e, Internal.scanIntDigitsLoop raw b.radix (b.radix ^ 15) chunksRev chunkAcc chunkLen cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanIntDigitsLoop raw b.radix (b.radix ^ 15) chunksRev chunkAcc chunkLen cs with
  | case1 chunksRev chunkAcc chunkLen =>
    rw [Internal.evalWeightedPairs, evalWeightedPairsFuel_eq, List.reverse_cons, evalPairsLinear_append]
    exact ⟨rfl, fun _ h => nomatch h⟩
  | case2 _ _ c cs d hd ih => rw [digitValue_eq_digitVal] at hd; rw [chunkVal_flush] at ih; simpa [consumeIntDigits, hd] using ih
  | case3 _ _ _ c cs d hd _ ih => rw [digitValue_eq_digitVal] at hd; rw [chunkVal_step] at ih; simpa [consumeIntDigits, hd] using ih
  | case4 _ _ _ c cs hnone => rw [digitValue_eq_digitVal] at hnone; simpa [consumeIntDigits, hnone] using err_spec .invalidUnderscore raw
  | case5 => exact err_spec .invalidUnderscore raw
  | case6 _ _ c cs hc1 hc2 d hd ih =>
    rw [digitValue_eq_digitVal] at hd; rw [chunkVal_flush] at ih; rw [consumeIntDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hd] using ih
  | case7 _ _ _ c cs hc1 hc2 d hd _ ih =>
    rw [digitValue_eq_digitVal] at hd; rw [chunkVal_step] at ih; rw [consumeIntDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hd] using ih
  | case8 _ _ _ c cs hc1 hc2 hnone =>
    rw [digitValue_eq_digitVal] at hnone; rw [consumeIntDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hnone] using err_spec .trailingChars raw

private theorem scanIntDigits_spec (raw : String) (b : NumBase) (acc : Nat) (cs : List Char) :
    (Internal.scanIntDigits raw b.radix acc cs).mapError (·.kind) = consumeIntDigits b acc cs ∧
      ∀ e, Internal.scanIntDigits raw b.radix acc cs = .error e → e.message ≠ "" := by
  unfold Internal.scanIntDigits; rw [intChunkBase_eq]
  simpa [chunkVal, Internal.evalPairsLinear] using scanIntDigitsLoop_spec raw b [(acc, 1)] 0 0 cs

private theorem lift_scanInt {raw : String} {b : NumBase} {d : Nat} {cs : List Char} (f : Nat → Int) :
    Except.mapError NumParseError.kind
      (match Internal.scanIntDigits raw b.radix d cs with | .ok n => Except.ok (f n) | .error e => Except.error e) =
      (match consumeIntDigits b d cs with | .ok n => Except.ok (f n) | .error k => Except.error k) ∧
    ∀ e : NumParseError,
      (match Internal.scanIntDigits raw b.radix d cs with | .ok n => Except.ok (f n) | .error err => Except.error err) = .error e →
        e.message ≠ "" := by
  have hs := scanIntDigits_spec raw b d cs
  cases hsc : Internal.scanIntDigits raw b.radix d cs with
  | error e =>
    have hsc' : consumeIntDigits b d cs = .error e.kind := by rw [← hs.1, hsc]; rfl
    exact ⟨by rw [hsc']; rfl, fun _ h => by cases h; exact hs.2 e hsc⟩
  | ok n =>
    have hsc' : consumeIntDigits b d cs = .ok n := by rw [← hs.1, hsc]; rfl
    exact ⟨by rw [hsc']; rfl, fun _ h => nomatch h⟩

private theorem parseDecSigned_spec (raw : String) (neg : Bool) (cs : List Char) :
    (Internal.parseDecSigned raw neg cs).mapError (·.kind) = parseDecAfterSign neg cs ∧
      ∀ e, Internal.parseDecSigned raw neg cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨c, cs⟩
  · exact err_spec .invalidSyntax raw
  · by_cases hcU : c = '_'
    · subst hcU; exact err_spec .invalidUnderscore raw
    · by_cases hc0 : c = '0'
      · subst hc0; unfold Internal.parseDecSigned parseDecAfterSign
        rcases cs with _ | ⟨c1, cs1⟩
        · exact ⟨rfl, fun _ h => nomatch h⟩
        · by_cases hdec : isDecDigit c1
          · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
          · by_cases hc1u : c1 = '_'
            · subst hc1u; rcases cs1 with _ | ⟨c2, cs2⟩
              · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
              · by_cases hdec2 : isDecDigit c2 <;>
                  simp [isDecDigit_eq, hdec, hdec2, mapError_makeError, makeError_msg_ne_empty]
            · simp [isDecDigit_eq, hdec, hc1u, mapError_makeError, makeError_msg_ne_empty]
      · rw [Internal.parseDecSigned.eq_5 raw neg c cs hcU hc0,
            parseDecAfterSign.eq_5 neg c cs hcU hc0,
            show Internal.digitValue? 10 c = digitVal? .dec c from digitValue_eq_digitVal .dec c]
        cases digitVal? .dec c with
        | none => exact err_spec .invalidSyntax raw
        | some d => exact lift_scanInt (b := .dec) (fun n => if neg then -Int.ofNat n else Int.ofNat n)

private theorem parseIntChars_spec (raw : String) (cs : List Char) :
    (Internal.parseIntChars raw cs).mapError (·.kind) = parseIntModelChars cs ∧
      ∀ e, Internal.parseIntChars raw cs = .error e → e.message ≠ "" := by
  unfold Internal.parseIntChars
  split
  · exact err_spec .emptyInput "input string is empty"
  · rename_i b rest
    rw [parseIntModelChars.eq_2, parseBasePrefix_eq_basePrefix]
    cases hbp : basePrefix? b with
    | some _ => simp [mapError_makeError, makeError_msg_ne_empty]
    | none => simpa [hbp] using parseDecSigned_spec raw false ('0' :: b :: rest)
  · rename_i b rest
    rw [parseIntModelChars.eq_3, parseBasePrefix_eq_basePrefix]
    cases hbp : basePrefix? b with
    | some _ => simp [mapError_makeError, makeError_msg_ne_empty]
    | none => simpa [hbp] using parseDecSigned_spec raw true ('0' :: b :: rest)
  · rename_i rest hne
    rw [parseIntModelChars.eq_4 rest (fun b r heq => hne b r (by simpa using heq))]
    exact parseDecSigned_spec raw false rest
  · rename_i rest hne
    rw [parseIntModelChars.eq_5 rest (fun b r heq => hne b r (by simpa using heq))]
    exact parseDecSigned_spec raw true rest
  · rename_i b rest
    rw [parseIntModelChars.eq_6, parseBasePrefix_eq_basePrefix]
    cases hbp : basePrefix? b with
    | none => simpa [hbp] using parseDecSigned_spec raw false ('0' :: b :: rest)
    | some base =>
      simp only [Option.map_some]
      split
      · exact err_spec .invalidSyntax raw
      · exact err_spec .invalidUnderscore raw
      · rename_i c cs' hcU
        rw [digitValue_eq_digitVal base]
        constructor
        · symm; split
          · contradiction
          · rename_i h; exact absurd (List.cons.inj h).1 hcU
          · rename_i heq; cases heq; symm
            cases digitVal? base c with
            | none => rfl
            | some d => exact (lift_scanInt (b := base) Int.ofNat).1
        · intro e he
          cases hdv : digitVal? base c with
          | none => simp [hdv] at he; subst he; exact makeError_msg_ne_empty _ _
          | some d => simp only [hdv] at he; exact (lift_scanInt (b := base) Int.ofNat).2 e he
  · rename_i h1 h2 h3 h4 h5 h6
    rw [parseIntModelChars.eq_7 cs h1 h2 h3 h4 h5 h6]
    exact parseDecSigned_spec raw false cs

/-- Specification connecting `Internal.parseInt` to `parseIntModel` and non-empty error messages. -/
theorem parseInt_spec (s : String) :
    (Internal.parseInt s).mapError (·.kind) = parseIntModel s ∧
      ∀ e, Internal.parseInt s = .error e → e.message ≠ "" :=
  parseIntChars_spec s s.toList

/-- Specification connecting `Internal.parseInt64` to `parseInt64Model` and non-empty error messages. -/
theorem parseInt64_spec (s : String) :
    (Internal.parseInt64 s).mapError (·.kind) = parseInt64Model s ∧
      ∀ e, Internal.parseInt64 s = .error e → e.message ≠ "" := by
  unfold Internal.parseInt64; rw [parseInt64Model_eq_parseIntModel]
  rcases parseInt_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt s with
  | error e =>
    have hpm : parseIntModel s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, Except.mapError, hmsg e hpi]
  | ok n =>
    have hpm : parseIntModel s = .ok n := by rw [← hm, hpi]; rfl
    rw [hpm]
    by_cases hr : int64MinInt ≤ n ∧ n ≤ int64MaxInt
    · have h1 : inInt64Range n = true := (inInt64Range_iff n).mpr hr
      have h2 : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hr
      simp [h1, h2, Except.mapError]
    · have h1 : inInt64Range n = false := Bool.eq_false_iff.mpr (mt (inInt64Range_iff n).mp hr)
      have h2 : (Internal.minInt64Bound ≤ n && n ≤ Internal.maxInt64Bound) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        exact if hlo : Internal.minInt64Bound ≤ n then Or.inr fun hhi => hr ⟨hlo, hhi⟩ else Or.inl hlo
      simp [h1, h2, mapError_makeError, makeError_msg_ne_empty]

private theorem consumeIntDigits_dec_digits (cs : List Char)
    (hdigits : ∀ c ∈ cs, isDecDigit c = true) (acc : Nat) :
    consumeIntDigits .dec acc cs = .ok (cs.foldl decStep acc) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    have hc := hdigits c (by simp)
    have hne : c ≠ '_' := decDigit_ne_of_false hc (by decide)
    have hdv : digitVal? .dec c = some (c.toNat - '0'.toNat) := by simp only [digitVal?, isDecDigit] at hc ⊢; simp [hc]
    rw [consumeIntDigits.eq_4 _ _ _ _ (fun _ _ h _ => hne h) (fun h _ => hne h)]
    simpa [NumBase.radix, hdv, decStep] using ih (fun x hx => hdigits x (by simp [hx])) _

private theorem parseIntModel_formatPos (neg : Bool) (m : Nat) :
    let cs := (if neg then ['-'] else []) ++ Internal.natToDecCharsPos (m + 1) []
    !(String.ofList cs).contains '_' ∧
      parseIntModel (String.ofList cs) = .ok (if neg then Int.negSucc m else Int.ofNat (m + 1)) := by
  have hall := natToDecCharsPos_all_dec (m + 1)
  have hhd := natToDecCharsPos_head_ne_zero (Nat.succ_pos m)
  have hev := natToDecCharsPos_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hcs : Internal.natToDecCharsPos (m + 1) [] with
  | nil => exact absurd hcs (natToDecCharsPos_nonempty (Nat.succ_pos m))
  | cons c rest =>
    rw [hcs] at hall hhd hev
    have hc := hall c (by simp)
    have hne0 : c ≠ '0' := fun h => hhd (by simp [h])
    have hcU : c ≠ '_' := decDigit_ne_of_false hc (by decide)
    have hdv : digitVal? .dec c = some (c.toNat - '0'.toNat) := by simp only [digitVal?, isDecDigit] at hc ⊢; simp [hc]
    have hpd : parseDecAfterSign neg (c :: rest) = .ok (if neg then Int.negSucc m else Int.ofNat (m + 1)) := by
      rw [parseDecAfterSign.eq_5 _ _ _ hcU hne0]
      simp only [hdv, consumeIntDigits_dec_digits rest (fun r hr => hall r (by simp [hr])),
        show rest.foldl decStep (c.toNat - '0'.toNat) = (c :: rest).foldl decStep 0 by simp [decStep], hev]
      cases neg <;> rfl
    cases neg with
    | false =>
      refine ⟨?_, ?_⟩
      · have hnu : '_' ∉ c :: rest := fun hm => decDigit_ne_of_false (hall '_' hm) (by decide) rfl
        simp [String.contains_char_eq, String.toList_ofList, hnu]
      · simp only [parseIntModel, String.toList_ofList, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        rw [parseIntModelChars.eq_7]
        · exact hpd
        · intro h; cases h
        · intro _ _ h; cases h; exact decDigit_ne_of_false hc (by decide) rfl
        · intro _ _ h; cases h; exact decDigit_ne_of_false hc (by decide) rfl
        · intro _ h; cases h; exact decDigit_ne_of_false hc (by decide) rfl
        · intro _ h; cases h; exact decDigit_ne_of_false hc (by decide) rfl
        · intro _ _ h; cases h; exact hne0 rfl
    | true =>
      refine ⟨?_, ?_⟩
      · have hnu : '_' ∉ '-' :: c :: rest := fun hm =>
          (List.mem_cons.mp hm).elim (fun h => absurd h (by decide)) (fun h => decDigit_ne_of_false (hall '_' h) (by decide) rfl)
        simp [String.contains_char_eq, String.toList_ofList, hnu]
      · simp only [parseIntModel, String.toList_ofList, ↓reduceIte, List.singleton_append]
        rw [parseIntModelChars.eq_5 _ (fun _ _ h => by cases h; exact hne0 rfl)]; exact hpd

/-- `parseIntModel` round-trips `Internal.formatInt` without underscores. -/
theorem parseIntModel_formatInt (n : Int) :
    !(Internal.formatInt n).contains '_' ∧ parseIntModel (Internal.formatInt n) = .ok n := by
  cases n with
  | ofNat k =>
    cases k with
    | zero => refine ⟨by simp only [Internal.formatInt, Internal.formatIntChars, String.contains_char_eq, String.toList_ofList]; decide, rfl⟩
    | succ m => exact parseIntModel_formatPos false m
  | negSucc m => exact parseIntModel_formatPos true m

private theorem formatIntChars_all_dec_or_minus (n : Int) :
    (Internal.formatInt n).toList.all (fun c => isDecDigit c || c == '-') = true := by
  unfold Internal.formatInt Internal.formatIntChars
  cases n with
  | ofNat k =>
    cases k with
    | zero => decide
    | succ m =>
      rw [String.toList_ofList]
      exact List.all_eq_true.mpr fun c hc => Bool.or_eq_true_iff.mpr (Or.inl (natToDecCharsPos_all_dec (m + 1) c hc))
  | negSucc m =>
    rw [String.toList_ofList, List.all_cons]
    refine Bool.and_eq_true_iff.mpr ⟨by decide, List.all_eq_true.mpr fun c hc => ?_⟩
    exact Bool.or_eq_true_iff.mpr (Or.inl (natToDecCharsPos_all_dec (m + 1) c hc))

/-- `Internal.formatInt` satisfies the strengthened `allowedFormatInt` relation. -/
theorem allowedFormatInt_formatInt (n : Int) :
    allowedFormatInt n (Internal.formatInt n) :=
  ⟨(parseIntModel_formatInt n).1, formatIntChars_all_dec_or_minus n, (parseIntModel_formatInt n).2⟩

end LeanSwe.NumParse.Proofs

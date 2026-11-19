import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.IntProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem decPairsLinear_append (acc : Nat) (xs ys : List (Nat × Nat)) :
    Internal.evalPairsLinear acc (xs ++ ys) = Internal.evalPairsLinear (Internal.evalPairsLinear acc xs) ys := by
  induction xs generalizing acc with | nil => rfl | cons x xs ih => exact ih (acc * x.2 + x.1)

private theorem decMergePairsRev_eval (a : Nat) (acc xs : List (Nat × Nat)) :
    Internal.evalPairsLinear a (Internal.mergePairsRev acc xs) =
      Internal.evalPairsLinear (Internal.evalPairsLinear a acc.reverse) xs := by
  fun_induction Internal.mergePairsRev acc xs with
  | case1 _ _ _ _ _ _ ih =>
    rw [ih, List.reverse_cons, decPairsLinear_append]; dsimp [Internal.evalPairsLinear]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | case2 => rw [List.reverse_cons, decPairsLinear_append]
  | case3 => rfl

private theorem decEvalWeightedPairsFuel_eq (fuel : Nat) (xs : List (Nat × Nat)) :
    Internal.evalWeightedPairsFuel fuel xs = Internal.evalPairsLinear 0 xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    rcases xs with _ | ⟨⟨v, p⟩, _ | ⟨b, rest⟩⟩
    · rfl
    · simp [Internal.evalWeightedPairsFuel, Internal.evalPairsLinear]
    · simp only [Internal.evalWeightedPairsFuel, ih, decMergePairsRev_eval]; rfl

private def decChunkVal (chunksRev : List (Nat × Nat)) (chunkAcc chunkLen : Nat) : Nat :=
  Internal.evalPairsLinear 0 chunksRev.reverse * 10 ^ chunkLen + chunkAcc

private theorem decChunkVal_flush (chunksRev : List (Nat × Nat)) (chunkAcc d : Nat) :
    decChunkVal ((chunkAcc, 1000000000000000000) :: chunksRev) d 1 = decChunkVal chunksRev chunkAcc 18 * 10 + d := by
  simp [decChunkVal, decPairsLinear_append, Internal.evalPairsLinear]

private theorem decChunkVal_step (chunksRev : List (Nat × Nat)) (chunkAcc chunkLen d : Nat) :
    decChunkVal chunksRev (chunkAcc * 10 + d) (chunkLen + 1) = decChunkVal chunksRev chunkAcc chunkLen * 10 + d := by
  simp only [decChunkVal, Nat.pow_succ]; rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem scanDecFloatDigitsLoop_spec (raw : String) (chunksRev : List (Nat × Nat))
    (chunkAcc chunkLen count : Nat) (cs : List Char) :
    (Internal.scanDecFloatDigitsLoop raw chunksRev chunkAcc chunkLen count cs).mapError (·.kind) =
        consumeDecFloatDigits (decChunkVal chunksRev chunkAcc chunkLen) count cs ∧
      ∀ e, Internal.scanDecFloatDigitsLoop raw chunksRev chunkAcc chunkLen count cs = .error e → e.message ≠ "" := by
  fun_induction Internal.scanDecFloatDigitsLoop raw chunksRev chunkAcc chunkLen count cs with
  | case1 chunksRev chunkAcc chunkLen count =>
    rw [Internal.evalWeightedPairs, decEvalWeightedPairsFuel_eq, List.reverse_cons, decPairsLinear_append]
    exact ⟨rfl, fun _ h => nomatch h⟩
  | case2 _ _ _ c _ hd d ih => have hd' : isDecDigit c = true := hd; rw [decChunkVal_flush] at ih; simpa [consumeDecFloatDigits, hd', d] using ih
  | case3 _ _ _ _ c _ hd d _ ih => have hd' : isDecDigit c = true := hd; rw [decChunkVal_step] at ih; simpa [consumeDecFloatDigits, hd', d] using ih
  | case4 _ _ _ _ c _ hd =>
    have hd' : isDecDigit c = false := by simpa [isDecDigit_eq] using hd
    exact ⟨by simp [consumeDecFloatDigits, hd', mapError_makeError], fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  | case5 => exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  | case6 _ _ _ c _ hc1 hc2 hd d ih =>
    have hd' : isDecDigit c = true := hd; rw [decChunkVal_flush] at ih; rw [consumeDecFloatDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hd', d] using ih
  | case7 _ _ _ _ c _ hc1 hc2 hd d _ ih =>
    have hd' : isDecDigit c = true := hd; rw [decChunkVal_step] at ih; rw [consumeDecFloatDigits.eq_4 _ _ _ _ hc1 hc2]; simpa [hd', d] using ih
  | case8 _ _ _ _ c _ hc1 hc2 hd =>
    have hd' : isDecDigit c = false := by simpa [isDecDigit_eq] using hd
    rw [Internal.evalWeightedPairs, decEvalWeightedPairsFuel_eq, List.reverse_cons, decPairsLinear_append,
        consumeDecFloatDigits.eq_4 _ _ _ _ hc1 hc2]
    exact ⟨by simp [hd', Except.mapError]; rfl, fun _ h => nomatch h⟩

/-- Mapping `.kind` over `Internal.scanDecFloatDigits` matches `consumeDecFloatDigits`. -/
theorem scanDecFloatDigits_mapError (raw : String) (acc count : Nat) (cs : List Char) :
    (Internal.scanDecFloatDigits raw acc count cs).mapError (·.kind) = consumeDecFloatDigits acc count cs := by
  simpa [Internal.scanDecFloatDigits, decChunkVal, Internal.evalPairsLinear] using (scanDecFloatDigitsLoop_spec raw [(acc, 1)] 0 0 count cs).1

/-- `Internal.scanDecFloatDigits` produces non-empty error messages. -/
theorem scanDecFloatDigits_msg (raw : String) (acc count : Nat) (cs : List Char) (e : NumParseError) :
    Internal.scanDecFloatDigits raw acc count cs = .error e → e.message ≠ "" :=
  (scanDecFloatDigitsLoop_spec raw [(acc, 1)] 0 0 count cs).2 e

/-- Specification connecting `Internal.parseFloatIntPart` to `Model.parseFloatIntPart`. -/
theorem parseFloatIntPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatIntPart raw cs).mapError (·.kind) = parseFloatIntPart cs ∧
      ∀ e, Internal.parseFloatIntPart raw cs = .error e → e.message ≠ "" := by
  rcases cs with _ | ⟨c, cs⟩
  · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hcU : c = '_'
    · subst hcU; exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
    · by_cases hc0 : c = '0'
      · subst hc0; unfold Internal.parseFloatIntPart parseFloatIntPart
        rcases cs with _ | ⟨c1, cs1⟩
        · exact ⟨rfl, fun _ h => nomatch h⟩
        · by_cases hdec : isDecDigit c1
          · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
          · by_cases hc1u : c1 = '_'
            · subst hc1u; rcases cs1 with _ | ⟨c2, cs2⟩
              · simp [isDecDigit_eq, hdec, mapError_makeError, makeError_msg_ne_empty]
              · by_cases hdec2 : isDecDigit c2 <;>
                  simp [isDecDigit_eq, hdec, hdec2, mapError_makeError, makeError_msg_ne_empty]
            · simp [isDecDigit_eq, hdec, hc1u, Except.mapError]
      · rw [Internal.parseFloatIntPart.eq_5 raw c cs hcU hc0,
            parseFloatIntPart.eq_5 c cs hcU hc0, isDecDigit_eq]
        by_cases hdec : isDecDigit c
        · simp only [hdec, ↓reduceIte]
          have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 cs
          cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 cs with
          | error e =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .error e.kind := by rw [← hm, hsc]; rfl
            exact ⟨by rw [hsc']; rfl, fun _ h => by cases h; exact scanDecFloatDigits_msg _ _ _ _ e hsc⟩
          | ok r =>
            have hsc' : consumeDecFloatDigits (c.toNat - '0'.toNat) 1 cs = .ok r := by rw [← hm, hsc]; rfl
            exact ⟨by rw [hsc']; rfl, fun _ h => nomatch h⟩
        · simp [hdec, mapError_makeError, makeError_msg_ne_empty]

/-- Specification connecting `Internal.parseFloatExpPart` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpPart_spec_aux (raw : String) (expNeg : Bool) (afterSign : List Char) :
    Except.mapError NumParseError.kind
      (match afterSign with
        | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
        | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
        | c :: rest => if Internal.isDecDigit c then
            match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) => Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error e => Except.error e
          else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) =
      (match afterSign with
        | [] => Except.error NumParseErrorKind.invalidSyntax
        | '_' :: _ => Except.error NumParseErrorKind.invalidUnderscore
        | c :: rest => if isDecDigit c then
            match consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest with
            | .ok (eMag, _, rem) => Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
            | .error k => Except.error k
          else Except.error NumParseErrorKind.invalidSyntax) ∧
      ∀ e, (match afterSign with
          | [] => Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)
          | '_' :: _ => Except.error (Internal.makeError NumParseErrorKind.invalidUnderscore raw)
          | c :: rest => if Internal.isDecDigit c then
              match Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
              | .ok (eMag, _, rem) => Except.ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
              | .error e => Except.error e
            else Except.error (Internal.makeError NumParseErrorKind.invalidSyntax raw)) = Except.error e →
          e.message ≠ "" := by
  constructor
  · split
    · rfl
    · rfl
    · rename_i c rest _; rw [isDecDigit_eq]; by_cases hdec : isDecDigit c
      · simp only [hdec, ↓reduceIte]; have hm := scanDecFloatDigits_mapError raw (c.toNat - '0'.toNat) 1 rest
        cases hsc : Internal.scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
        | error e => rw [show consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .error e.kind by rw [← hm, hsc]; rfl]; rfl
        | ok r => rw [show consumeDecFloatDigits (c.toNat - '0'.toNat) 1 rest = .ok r by rw [← hm, hsc]; rfl]; rfl
      · simp [hdec, mapError_makeError]
  · intro e he
    repeat' (first
      | (cases he; exact makeError_msg_ne_empty _ _; done)
      | (cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›; done)
      | (cases he; done)
      | split at he)

/-- Specification connecting `Internal.parseFloatExpPart` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpPart_spec (raw : String) (cs : List Char) :
    (Internal.parseFloatExpPart raw cs).mapError (·.kind) = parseFloatExpPart cs ∧
      ∀ e, Internal.parseFloatExpPart raw cs = .error e → e.message ≠ "" := by
  have hstrip : ∀ (c : Char) (rest : List Char), c ≠ '+' → c ≠ '-' →
      Internal.parseFloatExpPart raw (c :: rest) = Internal.parseFloatExpPart raw ('+' :: c :: rest) ∧
      parseFloatExpPart (c :: rest) = parseFloatExpPart ('+' :: c :: rest) := by
    intro c rest hp hm
    constructor
    · have h : (Internal.parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c :: rest)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c :: rest))) = (false, c :: rest) := by
        split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
      unfold Internal.parseFloatExpPart; dsimp only; rw [h]; rfl
    · have h : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (c :: rest)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, c :: rest))) = (false, c :: rest) := by
        split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
      unfold parseFloatExpPart; dsimp only; rw [h]; rfl
  have hbase : ∀ (s : Char) (rest : List Char), (s = '+' ∨ s = '-') →
      (Internal.parseFloatExpPart raw (s :: rest)).mapError (·.kind) = parseFloatExpPart (s :: rest) ∧
        ∀ e, Internal.parseFloatExpPart raw (s :: rest) = .error e → e.message ≠ "" := by
    rintro _ rest (rfl | rfl) <;>
      exact ⟨(parseFloatExpPart_spec_aux raw _ rest).1, fun e he => by
        unfold Internal.parseFloatExpPart at he; dsimp only at he
        repeat' (first
          | (cases he; exact makeError_msg_ne_empty _ _; done)
          | (cases he; exact scanDecFloatDigits_msg _ _ _ _ _ ‹_›; done)
          | (cases he; done)
          | split at he)⟩
  rcases cs with _ | ⟨c, rest⟩
  · exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _⟩
  · by_cases hp : c = '+'
    · subst hp; exact hbase '+' rest (Or.inl rfl)
    · by_cases hm : c = '-'
      · subst hm; exact hbase '-' rest (Or.inr rfl)
      · rw [(hstrip c rest hp hm).1, (hstrip c rest hp hm).2]
        exact hbase '+' (c :: rest) (Or.inl rfl)

section FloatFastBounds
open Float.Model Float.Model.UnpackedFloat

private theorem pow2_3n_le_pow10 (n : Nat) : 2 ^ (3 * n) ≤ 10 ^ n := by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) n
private theorem pow10_le_pow2_4n (n : Nat) : 10 ^ n ≤ 2 ^ (4 * n) := by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) n
private theorem two_mul_mul_pow2 (m n : Nat) : 2 * (m * 2 ^ n) = m * 2 ^ (n + 1) := by
  rw [Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm 2 m, Nat.mul_assoc]

private theorem shiftLeft_two_mul_lt_pow10 {m b k : Nat} (hm : m ≠ 0) (hb : m.log2 + b + 2 < 3 * k) :
    2 * (m <<< b) < 10 ^ k ∧ m <<< b < 10 ^ k ∧ m <<< b ≠ 0 := by
  have hsh : m <<< b = m * 2 ^ b := Nat.shiftLeft_eq m b
  have hmul : 2 * (m <<< b) < 2 ^ (m.log2 + b + 2) := by
    rw [hsh, two_mul_mul_pow2, show m.log2 + b + 2 = (m.log2 + 1) + (b + 1) by omega,
        Nat.pow_add 2 (m.log2 + 1) (b + 1)]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.pow_pos (a := 2) (by decide))
  have h2lt : 2 * (m <<< b) < 10 ^ k :=
    Nat.lt_of_lt_of_le (Nat.lt_trans hmul (Nat.pow_lt_pow_right (by decide) hb)) (pow2_3n_le_pow10 k)
  refine ⟨h2lt, by omega, ?_⟩
  rw [hsh]; exact Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pow_pos (by decide)))

private theorem shiftLeft_pow10_bounds {m b k : Nat} (hov : ((10 ^ k) <<< b) ≤ m) :
    m ≠ 0 ∧ 3 * k + b ≤ m.log2 ∧ (10 ^ k).log2 + b ≤ m.log2 ∧ 2 ^ b ≤ m / 10 ^ k ∧ m / 10 ^ k ≠ 0 := by
  have hp10 : 0 < 10 ^ k := Nat.pow_pos (by decide)
  have hov' : 10 ^ k * 2 ^ b ≤ m := by rwa [Nat.shiftLeft_eq] at hov
  have hm_ge : 2 ^ (3 * k + b) ≤ m := by
    rw [Nat.pow_add]; exact Nat.le_trans (Nat.mul_le_mul_right _ (pow2_3n_le_pow10 k)) hov'
  have hm : m ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hm_ge)
  have hq_ge : 2 ^ b ≤ m / 10 ^ k := (Nat.le_div_iff_mul_le hp10).2 (by rw [Nat.mul_comm]; exact hov')
  have hq_ne : m / 10 ^ k ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hq_ge)
  refine ⟨hm, (Nat.le_log2 hm).2 hm_ge, (Nat.le_log2 hm).2 ?_, hq_ge, hq_ne⟩
  rw [Nat.pow_add]; exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.log2_self_le (by omega))) hov'

private theorem pow10_shiftLeft_le_of_log2 {m b k : Nat} (hm : m ≠ 0) (h : b + 4 * k ≤ m.log2) :
    ((10 ^ k) <<< b) ≤ m := by
  rw [Nat.shiftLeft_eq]
  exact Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_right _ (pow10_le_pow2_4n k))
    (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega))) (Nat.log2_self_le hm)

private theorem shiftRight_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  change (Nat.repeat ExtendedMantissa.shiftRightOne k em).mantissa = em.mantissa / 2 ^ k
  induction k generalizing em with
  | zero => simp [Nat.repeat]
  | succ k ih => simp only [Nat.repeat, ExtendedMantissa.shiftRightOne]; rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem ofMantissaAndAccuracy_mantissa (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  cases acc with | exact => rfl | inexact c => cases c <;> rfl

private theorem shiftToTarget_pos (m : Nat) (e : Int) (acc : Accuracy) (hm : m ≠ 0)
    (hle : (Format.binary64.targetExponent (totalExponent m e) - e).toNat ≤ m.log2) :
    0 < (shiftToTargetExponent Format.binary64 m e acc).1.mantissa := by
  unfold shiftToTargetExponent shiftToExponent; dsimp only []
  rw [shiftRight_mantissa, ofMantissaAndAccuracy_mantissa]
  exact Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by decide) hle) (Nat.log2_self_le hm)) (Nat.pow_pos (by decide))

private theorem roundedMantissa_ge (em : ExtendedMantissa) : em.mantissa ≤ em.roundedMantissa := by
  rcases em with ⟨m, r, s⟩; cases r <;> cases s <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]

private theorem pack_roundWithAccuracy_overflow (m : Nat) (e : Int) (acc : Accuracy)
    (hm : m ≠ 0) (hov : 1024 ≤ (m.log2 : Int) + e) (hle : e ≤ 972) :
    Float.ofModel (Float.Model.pack (roundWithAccuracy Format.binary64 .positive m e acc)) = Float.inf := by
  have hmb : Format.binary64.mantissaBits = 53 := rfl
  have hmin : Format.binary64.minExponent = -1074 := rfl
  unfold roundWithAccuracy; dsimp only []
  let st1 := shiftToTargetExponent Format.binary64 m e acc
  have hm1 : 0 < st1.1.mantissa := shiftToTarget_pos m e acc hm (by unfold Format.targetExponent totalExponent; omega)
  have hrem : 0 < st1.1.roundedMantissa := Nat.lt_of_lt_of_le hm1 (roundedMantissa_ge _)
  have he1 : (972 : Int) ≤ st1.2 := by
    unfold st1 shiftToTargetExponent shiftToExponent Format.targetExponent totalExponent; dsimp only []; omega
  let st2 := shiftToTargetExponent Format.binary64 st1.1.roundedMantissa st1.2 .exact
  have hm2 : st2.1.mantissa ≠ 0 := Nat.ne_of_gt
    (shiftToTarget_pos st1.1.roundedMantissa st1.2 .exact (Nat.ne_of_gt hrem)
      (by unfold Format.targetExponent totalExponent; omega))
  have he2 : (972 : Int) ≤ st2.2 := by unfold st2 shiftToTargetExponent shiftToExponent; dsimp only []; omega
  change Float.ofModel (Float.Model.pack (if h : st2.1.mantissa = 0 then _ else _)) = Float.inf
  simp only [hm2, ↓reduceDIte]
  show Float.ofModel (Float.Model.pack (.finite .positive st2.1.mantissa st2.2 _)) =
    Float.ofModel (Float.Model.pack (.infinity .positive))
  have hge : 2 ^ Format.binary64.exponentBits ≤
      (st2.2 + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    have : 2 ^ Format.binary64.exponentBits = 2048 := rfl
    have : Format.binary64.exponentBias = 1023 := rfl
    have : Format.binary64.mantissaBitsWithoutImplicit = 52 := rfl
    omega
  congr 1; unfold Float.Model.pack; congr 1; unfold UnpackedFloat.pack; simp only [hge, ↓reduceIte]

private theorem evalFloat_pos_overflow {m p : Nat} (hm : m ≠ 0) (hov : 1024 ≤ m.log2 + 3 * p) :
    evalFloat false m (p : Int) = Float.inf := by
  by_cases hp : p > 2048
  · exact evalFloat_overflow_pos hm (by omega)
  · have hmb : Format.binary64.mantissaBits = 53 := rfl
    let mant := (m <<< Format.binary64.mantissaBits) * 10 ^ p
    have hmsh : m <<< Format.binary64.mantissaBits = m * 2 ^ 53 := by rw [hmb, Nat.shiftLeft_eq]
    have hmul_pos : mant ≠ 0 := by
      rw [show mant = (m * 2 ^ 53) * 10 ^ p by dsimp [mant]; rw [hmsh]]
      exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm) (by decide)) (Nat.pow_pos (by decide)))
    have hlog : m.log2 + 53 + 3 * p ≤ mant.log2 := (Nat.le_log2 hmul_pos).2 <| by
      rw [show mant = (m * 2 ^ 53) * 10 ^ p by dsimp [mant]; rw [hmsh], Nat.pow_add, Nat.pow_add]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.log2_self_le hm)) (pow2_3n_le_pow10 p)
    unfold evalFloat evalFloatModel Float.Model.ofScientific UnpackedFloat.ofScientific
    have hpow2_11 : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
    have h1 : ¬((p : Int) > 2 ^ Format.binary64.exponentBits) := by omega
    have h2 : ¬((p : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (m.log2 : Int))) := by omega
    have hp_toNat : (p : Int).toNat = p := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hm, ↓reduceDIte, h1, h2, Int.natCast_nonneg p, hp_toNat]
    change Float.ofModel (Float.Model.pack (UnpackedFloat.mul Format.binary64
      (.finite .positive (m <<< Format.binary64.mantissaBits) (-Format.binary64.mantissaBits) _)
      (.finite .positive (10 ^ p) 0 _))) = Float.inf
    unfold UnpackedFloat.mul
    exact pack_roundWithAccuracy_overflow mant (-(Format.binary64.mantissaBits : Int) + 0) .exact hmul_pos (by omega) (by omega)

private theorem evalFloat_neg_underflow {m k : Nat} (hm : m ≠ 0) (hk : 0 < k) (hund : m.log2 + 1080 ≤ 3 * k) :
    evalFloat false m (-(k : Int)) = (0.0 : Float) := by
  by_cases hfar : (-(k : Int)) < -(2048 + (m.log2 : Int))
  · exact evalFloat_underflow_pos hfar
  · have h10 := pow2_3n_le_pow10 k
    have hlog10 : 3 * k ≤ (10 ^ k).log2 := (Nat.le_log2 (Nat.ne_of_gt (Nat.pow_pos (by decide)))).2 h10
    unfold evalFloat evalFloatModel Float.Model.ofScientific UnpackedFloat.ofScientific
    have hpow2_11 : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
    have h1 : ¬(-(k : Int) > 2 ^ Format.binary64.exponentBits) := by omega
    have h2 : ¬(-(k : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (m.log2 : Int))) := by omega
    have h3 : ¬((0 : Int) ≤ -(k : Int)) := by omega
    have htoNat : (-(-(k : Int))).toNat = k := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hm, ↓reduceDIte, h1, h2, h3, htoNat]
    change Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64
      (.finite .positive m 0 _) (.finite .positive (10 ^ k) 0 _))) = 0.0
    unfold UnpackedFloat.div divCore
    have hte : min ((0 : Int) - 0) (Format.binary64.targetExponent
        (totalExponent m 0 - totalExponent (10 ^ k) 0)) = -1074 := by
      have : Format.binary64.minExponent = -1074 := rfl
      have : Format.binary64.mantissaBits = 53 := rfl
      unfold Format.targetExponent totalExponent; omega
    have ⟨h2lt, hlt, hne⟩ := shiftLeft_two_mul_lt_pow10 (m := m) (b := 1074) (k := k) hm (by omega)
    have hacc : accuracyOfFraction ((m <<< 1074) % 10 ^ k) (10 ^ k) = .inexact .lt := by
      rw [Nat.mod_eq_of_lt hlt]; unfold accuracyOfFraction; simp only [hne, ↓reduceIte, compare, compareOfLessAndEq, h2lt]
    dsimp only []; rw [hte, show ((0 : Int) - 0 - (-1074 : Int)).toNat = 1074 from rfl, Nat.div_eq_of_lt hlt, hacc]; decide

private theorem evalFloat_neg_overflow {m k : Nat} (hk : 0 < k) (hov : ((10 ^ k) <<< 1024) ≤ m) :
    evalFloat false m (-(k : Int)) = Float.inf := by
  have ⟨hm, hlog_3k, hlog_10k, hq_ge, hq_ne⟩ := shiftLeft_pow10_bounds hov
  unfold evalFloat evalFloatModel Float.Model.ofScientific UnpackedFloat.ofScientific
  have hpow2_11 : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
  have h1 : ¬(-(k : Int) > 2 ^ Format.binary64.exponentBits) := by omega
  have h2 : ¬(-(k : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (m.log2 : Int))) := by omega
  have h3 : ¬((0 : Int) ≤ -(k : Int)) := by omega
  have htoNat : (-(-(k : Int))).toNat = k := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, hm, ↓reduceDIte, h1, h2, h3, htoNat]
  change Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64
    (.finite .positive m 0 _) (.finite .positive (10 ^ k) 0 _))) = Float.inf
  unfold UnpackedFloat.div divCore
  have hte : min ((0 : Int) - 0) (Format.binary64.targetExponent
      (totalExponent m 0 - totalExponent (10 ^ k) 0)) = 0 := by
    have : Format.binary64.minExponent = -1074 := rfl
    have : Format.binary64.mantissaBits = 53 := rfl
    unfold Format.targetExponent totalExponent; omega
  dsimp only []; rw [hte, show ((0 : Int) - 0 - (0 : Int)).toNat = 0 from rfl, Nat.shiftLeft_zero]
  have hq_log : 1024 ≤ (m / 10 ^ k).log2 := (Nat.le_log2 hq_ne).2 hq_ge
  exact pack_roundWithAccuracy_overflow (m / 10 ^ k) 0 _ hq_ne (by omega) (by omega)

private theorem lift_inf (neg : Bool) {m : Nat} {e : Int} (h : evalFloat false m e = Float.inf) :
    (match neg with | true => -Float.inf | false => Float.inf) = evalFloat neg m e := by
  cases neg with | false => exact h.symm | true => rw [evalFloat_neg, h]

private theorem lift_zero (neg : Bool) {m : Nat} {e : Int} (h : evalFloat false m e = (0.0 : Float)) :
    (match neg with | true => -0.0 | false => 0.0) = evalFloat neg m e := by
  cases neg with | false => exact h.symm | true => rw [evalFloat_neg, h]

private theorem evalScientificFloat_eq_evalFloat (neg : Bool) (mantissa : Nat) (exp10 : Int) :
    Internal.evalScientificFloat neg mantissa exp10 = evalFloat neg mantissa exp10 := by
  unfold Internal.evalScientificFloat
  cases mantissa with
  | zero => exact lift_zero neg (evalFloat_zero exp10)
  | succ m1 =>
    dsimp only []; have hm : m1 + 1 ≠ 0 := Nat.succ_ne_zero m1
    by_cases hexp : 0 ≤ exp10
    · simp only [decide_eq_true hexp]
      by_cases hov : 1024 ≤ (m1 + 1).log2 + 3 * exp10.toNat
      · simp only [decide_eq_true hov]; exact lift_inf neg ((by omega : ((exp10.toNat : Nat) : Int) = exp10) ▸ evalFloat_pos_overflow hm hov)
      · simp only [decide_eq_false hov]; rfl
    · simp only [decide_eq_false hexp]
      have hk_pos : 0 < (-exp10).toNat := by omega
      have hk_eq : -(((-exp10).toNat : Nat) : Int) = exp10 := by omega
      by_cases hund : (m1 + 1).log2 + 1080 ≤ 3 * (-exp10).toNat
      · simp only [decide_eq_true hund]; exact lift_zero neg (hk_eq ▸ evalFloat_neg_underflow hm hk_pos hund)
      · simp only [decide_eq_false hund]
        by_cases hov1 : 1024 + 4 * (-exp10).toNat ≤ (m1 + 1).log2
        · simp only [decide_eq_true hov1]; exact lift_inf neg (hk_eq ▸ evalFloat_neg_overflow hk_pos (pow10_shiftLeft_le_of_log2 hm hov1))
        · simp only [decide_eq_false hov1]
          by_cases hov2 : ((10 ^ (-exp10).toNat) <<< 1024) ≤ m1 + 1
          · simp only [decide_eq_true hov2]; exact lift_inf neg (hk_eq ▸ evalFloat_neg_overflow hk_pos hov2)
          · simp only [decide_eq_false hov2]; rfl

end FloatFastBounds

/-- Specification connecting `Internal.parseFloatExpTail` to `Model.parseFloatExpPart`. -/
theorem parseFloatExpTail_spec (raw : String) (neg : Bool) (mantissa : Nat) (fracAdj : Int) (afterE : List Char) :
    Except.mapError NumParseError.kind (Internal.parseFloatExpTail raw neg mantissa fracAdj afterE) =
      (match parseFloatExpPart afterE with
        | .error k => .error k
        | .ok (expVal, afterExp) => if afterExp.isEmpty then .ok (evalFloat neg mantissa (expVal + fracAdj)) else .error .trailingChars) ∧
      ∀ e, Internal.parseFloatExpTail raw neg mantissa fracAdj afterE = .error e → e.message ≠ "" := by
  unfold Internal.parseFloatExpTail; rcases parseFloatExpPart_spec raw afterE with ⟨hm, hmsg⟩
  cases hpe : Internal.parseFloatExpPart raw afterE with
  | error e => simp [show parseFloatExpPart afterE = .error e.kind by rw [← hm, hpe]; rfl, Except.mapError, hmsg e hpe]
  | ok r =>
    rcases r with ⟨expVal, afterExp⟩; rw [show parseFloatExpPart afterE = .ok (expVal, afterExp) by rw [← hm, hpe]; rfl]
    by_cases hemp : afterExp.isEmpty
    · simp [hemp, Except.mapError, evalScientificFloat_eq_evalFloat]
    · simp [hemp, mapError_makeError, makeError_msg_ne_empty]

end LeanSwe.NumParse.Proofs

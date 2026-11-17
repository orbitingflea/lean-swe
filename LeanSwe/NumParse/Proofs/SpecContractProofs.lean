import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.IntProofs
import LeanSwe.NumParse.Proofs.FloatParseProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Proof of `test_numparse_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_numparse_onError_returnsNonEmptyMessage :
    AllPass (test_numparse_onError_returnsNonEmptyMessage defaultApi) := by
  intro s
  dsimp [test_numparse_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  have p1 : ∀ e, Internal.parseInt s = .error e → e.message ≠ "" := (parseInt_spec s).2
  have p2 : ∀ e, Internal.parseInt64 s = .error e → e.message ≠ "" := (parseInt64_spec s).2
  have p3 : ∀ e, Internal.parseFloat s = .error e → e.message ≠ "" := (parseFloat_spec s).2
  cases h1 : Internal.parseInt s <;>
    cases h2 : Internal.parseInt64 s <;>
    cases h3 : Internal.parseFloat s <;>
    dsimp only <;>
    refine ⟨?_, ?_, ?_, trivial⟩
  all_goals first | trivial | exact p1 _ h1 | exact p2 _ h2 | exact p3 _ h3

/-- Non-vacuity `CanReach` witness for `test_numparse_onError_returnsNonEmptyMessage`. -/
theorem reach_numparse_onError_returnsNonEmptyMessage :
    CanReach (test_numparse_onError_returnsNonEmptyMessage defaultApi) :=
  ⟨"", proof_numparse_onError_returnsNonEmptyMessage ""⟩

/-- Proof of `test_numparse_parseInt_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt_matchesModel :
    AllPass (test_numparse_parseInt_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseInt_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseInt_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt s with
  | error e =>
    have hpm : parseIntModel s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, hmsg e hpi]
  | ok v =>
    have hpm : parseIntModel s = .ok v := by rw [← hm, hpi]; rfl
    simp [hpm]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt_matchesModel`. -/
theorem reach_numparse_parseInt_matchesModel :
    CanReach (test_numparse_parseInt_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt_matchesModel "0"⟩

/-- Proof of `test_numparse_parseInt64_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt64_matchesModel :
    AllPass (test_numparse_parseInt64_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseInt64_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseInt64_spec s with ⟨hm, hmsg⟩
  cases hpi : Internal.parseInt64 s with
  | error e =>
    have hpm : parseInt64Model s = .error e.kind := by rw [← hm, hpi]; rfl
    simp [hpm, hmsg e hpi]
  | ok v =>
    have hpm : parseInt64Model s = .ok v := by rw [← hm, hpi]; rfl
    simp [hpm]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt64_matchesModel`. -/
theorem reach_numparse_parseInt64_matchesModel :
    CanReach (test_numparse_parseInt64_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt64_matchesModel "0"⟩

/-- Proof of `test_numparse_formatInt_roundTrip` for `defaultApi`. -/
theorem proof_numparse_formatInt_roundTrip :
    AllPass (test_numparse_formatInt_roundTrip defaultApi) := by
  intro n
  rcases parseIntModel_formatInt n with ⟨hnoU, hmodel⟩
  rcases parseInt_spec (Internal.formatInt n) with ⟨hpi_m, _⟩
  have hpi_ok : Internal.parseInt (Internal.formatInt n) = .ok n := by
    cases h1 : Internal.parseInt (Internal.formatInt n) with
    | error e => have : parseIntModel (Internal.formatInt n) = .error e.kind := by rw [← hpi_m, h1]; rfl
                 rw [hmodel] at this; cases this
    | ok v => have : parseIntModel (Internal.formatInt n) = .ok v := by rw [← hpi_m, h1]; rfl
              rw [hmodel] at this; cases this; rfl
  rcases parseInt64_spec (Internal.formatInt n) with ⟨h64_m, h64_msg⟩
  dsimp [test_numparse_formatInt_roundTrip, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  refine ⟨hnoU, hmodel, hpi_ok, ?_⟩
  by_cases hr : inInt64Range n = true
  · simp only [hr, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .ok (Int64.ofInt n) := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr]
    cases h1 : Internal.parseInt64 (Internal.formatInt n) with
    | error e =>
      have : parseInt64Model (Internal.formatInt n) = .error e.kind := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this
    | ok v =>
      have : parseInt64Model (Internal.formatInt n) = .ok v := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this; exact ⟨rfl, trivial⟩
  · have hr' : inInt64Range n = false := Bool.eq_false_iff.mpr hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .error .overflow := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr']
    cases h1 : Internal.parseInt64 (Internal.formatInt n) with
    | error e =>
      have heq : parseInt64Model (Internal.formatInt n) = .error e.kind := by rw [← h64_m, h1]; rfl
      rw [hm64] at heq
      injection heq with hk
      exact ⟨⟨hk.symm, h64_msg e h1⟩, trivial⟩
    | ok v =>
      have : parseInt64Model (Internal.formatInt n) = .ok v := by rw [← h64_m, h1]; rfl
      rw [hm64] at this; cases this

/-- Non-vacuity `CanReach` witness for `test_numparse_formatInt_roundTrip`. -/
theorem reach_numparse_formatInt_roundTrip :
    CanReach (test_numparse_formatInt_roundTrip defaultApi) :=
  ⟨0, proof_numparse_formatInt_roundTrip 0⟩

/-- Proof of `test_numparse_parseFloat_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseFloat_matchesModel :
    AllPass (test_numparse_parseFloat_matchesModel defaultApi) := by
  intro s
  dsimp [test_numparse_parseFloat_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  rcases parseFloat_spec s with ⟨hm, hmsg⟩
  cases hpf : Internal.parseFloat s with
  | error e =>
    have hpm : parseFloatModel s = .error e.kind := by rw [← hm, hpf]; rfl
    simp [hpm, hmsg e hpf]
  | ok v =>
    have hpm : parseFloatModel s = .ok v := by rw [← hm, hpf]; rfl
    simp [hpm, floatBitMatch_refl]

/-- Non-vacuity `CanReach` witness for `test_numparse_parseFloat_matchesModel`. -/
theorem reach_numparse_parseFloat_matchesModel :
    CanReach (test_numparse_parseFloat_matchesModel defaultApi) :=
  ⟨"0.0", proof_numparse_parseFloat_matchesModel "0.0"⟩

private theorem defaultApi_parseInt_of_model {s : String} {expected : Int}
    (hm : parseIntModel s = .ok expected) :
    match defaultApi.parseInt s with
    | .ok v => v = expected
    | .error _ => False := by
  have hs := (parseInt_spec s).1
  change (Internal.parseInt s).mapError (·.kind) = parseIntModel s at hs
  change match Internal.parseInt s with | .ok v => v = expected | .error _ => False
  cases h : Internal.parseInt s with
  | error e => have : parseIntModel s = .error e.kind := by rw [← hs, h]; rfl
               rw [hm] at this; cases this
  | ok v => have : parseIntModel s = .ok v := by rw [← hs, h]; rfl
            rw [hm] at this; exact (Except.ok.inj this).symm

private theorem defaultApi_parseInt_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseIntModel s = .error expected) :
    match defaultApi.parseInt s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseInt_spec s
  change match Internal.parseInt s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseInt s with
  | error e =>
    have heq : parseIntModel s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseIntModel s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem defaultApi_parseInt64_of_model {s : String} {expected : Int64}
    (hm : parseInt64Model s = .ok expected) :
    match defaultApi.parseInt64 s with
    | .ok v => v = expected
    | .error _ => False := by
  have hs := (parseInt64_spec s).1
  change match Internal.parseInt64 s with | .ok v => v = expected | .error _ => False
  cases h : Internal.parseInt64 s with
  | error e => have : parseInt64Model s = .error e.kind := by rw [← hs, h]; rfl
               rw [hm] at this; cases this
  | ok v => have : parseInt64Model s = .ok v := by rw [← hs, h]; rfl
            rw [hm] at this; exact (Except.ok.inj this).symm

private theorem defaultApi_parseInt64_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseInt64Model s = .error expected) :
    match defaultApi.parseInt64 s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseInt64_spec s
  change match Internal.parseInt64 s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseInt64 s with
  | error e =>
    have heq : parseInt64Model s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseInt64Model s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem defaultApi_parseFloat_bits_of_model {s : String} {expected : Float}
    (hm : ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch expected y) :
    match defaultApi.parseFloat s with
    | .ok actual => FloatBitMatch expected actual
    | .error _ => False := by
  rcases hm with ⟨y, hmy, hbit⟩
  have hs := (parseFloat_spec s).1
  change match Internal.parseFloat s with | .ok actual => FloatBitMatch expected actual | .error _ => False
  cases h : Internal.parseFloat s with
  | error e => have : parseFloatModel s = .error e.kind := by rw [← hs, h]; rfl
               rw [hmy] at this; cases this
  | ok v => have : parseFloatModel s = .ok v := by rw [← hs, h]; rfl
            rw [hmy] at this
            cases Except.ok.inj this
            exact hbit

private theorem defaultApi_parseFloat_err_of_model {s : String} {expected : NumParseErrorKind}
    (hm : parseFloatModel s = .error expected) :
    match defaultApi.parseFloat s with
    | .ok _ => False
    | .error e => e.kind = expected ∧ e.message ≠ "" := by
  have hs := parseFloat_spec s
  change match Internal.parseFloat s with | .ok _ => False | .error e => e.kind = expected ∧ e.message ≠ ""
  cases h : Internal.parseFloat s with
  | error e =>
    have heq : parseFloatModel s = .error e.kind := by rw [← hs.1, h]; rfl
    rw [hm] at heq
    exact ⟨(Except.error.inj heq).symm, hs.2 e h⟩
  | ok v =>
    have heq : parseFloatModel s = .ok v := by rw [← hs.1, h]; rfl
    rw [hm] at heq; cases heq

private theorem pow2_3n_le_pow10 (n : Nat) : 2 ^ (3 * n) ≤ 10 ^ n := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left (by decide) n

private theorem shiftRight_mantissa (em : Float.Model.UnpackedFloat.ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  change (Nat.repeat Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne k em).mantissa = em.mantissa / 2 ^ k
  induction k generalizing em with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    simp only [Nat.repeat, Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]
    rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem roundedMantissa_ge (em : Float.Model.UnpackedFloat.ExtendedMantissa) :
    em.mantissa ≤ em.roundedMantissa := by
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;> simp [Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]

private theorem div_pow2_pos {x k : Nat} (hx : x ≠ 0) (hk : k ≤ x.log2) :
    0 < x / 2 ^ k :=
  Nat.div_pos
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) ((Nat.le_log2 hx).1 (Nat.le_refl _)))
    (Nat.pow_pos (by decide))

private theorem pack_finite_pos_ge972 {m : Nat} {e : Int} (hm : 0 < m) (he : 972 ≤ e) :
    Float.ofModel (Float.Model.pack (.finite .positive m e hm)) = Float.inf := by
  have hpow : 2 ^ Float.Model.Format.binary64.exponentBits = 2048 := by decide
  have hbias : Float.Model.Format.binary64.exponentBias = 1023 := by decide
  have hmbi : Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 52 := by decide
  have hge : 2 ^ Float.Model.Format.binary64.exponentBits ≤
      (e + Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    omega
  show Float.ofModel (Float.Model.pack (.finite .positive m e hm)) =
    Float.ofModel (Float.Model.pack (.infinity .positive))
  congr 1
  unfold Float.Model.pack
  congr 1
  unfold Float.Model.UnpackedFloat.pack
  simp only [hge, ↓reduceIte]

private theorem evalFloat_overflow_ge360 (e : Int) (he : 360 ≤ e) (he2 : e ≤ 2048) :
    evalFloat false 1 e = Float.inf := by
  have he_nonneg : 0 ≤ e := by omega
  have h10 := pow2_3n_le_pow10 e.toNat
  have hmb : Float.Model.Format.binary64.mantissaBits = 53 := by decide
  have hmin : Float.Model.Format.binary64.minExponent = -1074 := by decide
  have hpow2_11 : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := by decide
  have hlog1 : Nat.log2 1 = 0 := by decide
  let mant := (1 <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ e.toNat
  have hmul_pos : mant ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  have h2pow : 2 ^ (3 * e.toNat) ≤ mant := Nat.le_trans h10 (Nat.le_mul_of_pos_left _ (by decide))
  have hlog : 3 * e.toNat ≤ mant.log2 := (Nat.le_log2 hmul_pos).2 h2pow
  have hlog1080 : 1080 ≤ mant.log2 := by omega
  unfold evalFloat evalFloatModel Float.Model.ofScientific Float.Model.UnpackedFloat.ofScientific
  have hnot1 : ¬(e > 2 ^ Float.Model.Format.binary64.exponentBits) := by omega
  have hnot2 : ¬(e < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, hnot1, hnot2, he_nonneg]
  change Float.ofModel (Float.Model.pack (Float.Model.UnpackedFloat.mul Float.Model.Format.binary64
    (.finite .positive (1 <<< Float.Model.Format.binary64.mantissaBits)
      (-Float.Model.Format.binary64.mantissaBits) _)
    (.finite .positive (10 ^ e.toNat) 0 _))) = Float.inf
  unfold Float.Model.UnpackedFloat.mul Float.Model.UnpackedFloat.roundWithAccuracy
  dsimp only []
  let st1 := Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
    (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact
  have hsh1_le : (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent mant (-(Float.Model.Format.binary64.mantissaBits : Int) + 0)) -
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0)).toNat ≤ mant.log2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hm1_pos : 0 < st1.1.mantissa := by
    change 0 < (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact).1.mantissa
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]
    rw [shiftRight_mantissa]
    exact div_pow2_pos hmul_pos hsh1_le
  have hrem_pos : 0 < st1.1.roundedMantissa := Nat.lt_of_lt_of_le hm1_pos (roundedMantissa_ge _)
  have he1_ge : (972 : Int) ≤ st1.2 := by
    change (972 : Int) ≤ (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 mant
      (-(Float.Model.Format.binary64.mantissaBits : Int) + 0) .exact).2
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
      Float.Model.Format.targetExponent Float.Model.totalExponent
    dsimp only []; omega
  let st2 := Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
    st1.1.roundedMantissa st1.2 .exact
  have hsh2_le : (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent st1.1.roundedMantissa st1.2) - st1.2).toNat ≤
      st1.1.roundedMantissa.log2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hm2_pos : st2.1.mantissa ≠ 0 := by
    change (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
      st1.1.roundedMantissa st1.2 .exact).1.mantissa ≠ 0
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy]
    rw [shiftRight_mantissa]
    exact Nat.ne_of_gt (div_pow2_pos (Nat.ne_of_gt hrem_pos) hsh2_le)
  change Float.ofModel (Float.Model.pack (if h : st2.1.mantissa = 0 then _ else _)) = Float.inf
  simp only [hm2_pos, ↓reduceDIte]
  have he2_ge : (972 : Int) ≤ st2.2 := by
    change (972 : Int) ≤ (Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
      st1.1.roundedMantissa st1.2 .exact).2
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    dsimp only []; omega
  exact pack_finite_pos_ge972 (Nat.pos_of_ne_zero hm2_pos) he2_ge

private theorem round_zero_lt_neg1074 :
    Float.ofModel (Float.Model.pack
      (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive 0 (-1074)
        (.inexact .lt))) = (0.0 : Float) := by
  decide

private theorem accuracy_one_shiftLeft_lt {k d : Nat} (hk : 2 ^ (k + 1) < d) :
    (1 <<< k) / d = 0 ∧
    Float.Model.UnpackedFloat.accuracyOfFraction ((1 <<< k) % d) d = .inexact .lt := by
  have hpow : 1 <<< k = 2 ^ k := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2mul : 2 * (1 <<< k) = 2 ^ (k + 1) := by
    rw [hpow, Nat.mul_comm, Nat.pow_succ]
  have h1lt2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)
  have hlt : 1 <<< k < d := hpow ▸ Nat.lt_trans h1lt2 hk
  have hne : (1 <<< k) ≠ 0 := hpow ▸ Nat.ne_of_gt (Nat.pow_pos (by decide))
  refine ⟨Nat.div_eq_of_lt hlt, ?_⟩
  rw [Nat.mod_eq_of_lt hlt]
  unfold Float.Model.UnpackedFloat.accuracyOfFraction
  simp only [hne, ↓reduceIte, h2mul]
  have hcmp : compare (2 ^ (k + 1)) d = .lt := by
    simp [compare, compareOfLessAndEq, hk]
  rw [hcmp]

private theorem evalFloat_underflow_le_neg360 (e : Int) (he : e ≤ -360) (he2 : -(2048 : Int) ≤ e) :
    evalFloat false 1 e = (0.0 : Float) := by
  have he_neg : ¬(0 ≤ e) := by omega
  let p := (-e).toNat
  have hp_ge : 360 ≤ p := by omega
  have h10 := pow2_3n_le_pow10 p
  have h10_pos : 10 ^ p ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have hlog : 3 * p ≤ (10 ^ p).log2 := (Nat.le_log2 h10_pos).2 h10
  have hlog1080 : 1080 ≤ (10 ^ p).log2 := by omega
  unfold evalFloat evalFloatModel Float.Model.ofScientific Float.Model.UnpackedFloat.ofScientific
  have hpow2_11 : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := by decide
  have hlog1 : Nat.log2 1 = 0 := by decide
  have hnot1 : ¬(e > 2 ^ Float.Model.Format.binary64.exponentBits) := by omega
  have hnot2 : ¬(e < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, hnot1, hnot2, he_neg]
  change Float.ofModel (Float.Model.pack
    (Float.Model.UnpackedFloat.div Float.Model.Format.binary64
      (.finite .positive 1 0 _) (.finite .positive (10 ^ p) 0 _))) = 0.0
  unfold Float.Model.UnpackedFloat.div Float.Model.UnpackedFloat.divCore
  have hmin : Float.Model.Format.binary64.minExponent = -1074 := by decide
  have hmb : Float.Model.Format.binary64.mantissaBits = 53 := by decide
  have hte : min ((0 : Int) - 0) (Float.Model.Format.binary64.targetExponent
      (Float.Model.totalExponent 1 0 - Float.Model.totalExponent (10 ^ p) 0)) = -1074 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent; omega
  have hsh : ((0 : Int) - 0 - (-1074 : Int)).toNat = 1074 := rfl
  have hk_lt : 2 ^ (1074 + 1) < 10 ^ p := by
    calc 2 ^ (1074 + 1) < 2 ^ (3 * p) := Nat.pow_lt_pow_right (by decide) (by omega)
      _ ≤ 10 ^ p := h10
  have ⟨hdiv, hacc⟩ := accuracy_one_shiftLeft_lt (k := 1074) hk_lt
  dsimp only []
  rw [hte, hsh, hdiv, hacc]
  exact round_zero_lt_neg1074

private theorem float_zero_neg_zero_checks :
    match defaultApi.parseFloat "0.0", defaultApi.parseFloat "-0.0" with
    | .ok p, .ok n =>
      p.toBits = (0.0 : Float).toBits ∧
      (n.toBits = (-0.0 : Float).toBits ∧
        (n.toBits ≠ p.toBits ∧ (FloatEquiv p n ∧ True)))
    | _, _ => False := by
  have hp_spec := (parseFloat_spec "0.0").1
  have hn_spec := (parseFloat_spec "-0.0").1
  change match Internal.parseFloat "0.0", Internal.parseFloat "-0.0" with
    | .ok p, .ok n => _ | _, _ => False
  cases hp : Internal.parseFloat "0.0" with
  | error e =>
    have : parseFloatModel "0.0" = .error e.kind := by rw [← hp_spec, hp]; rfl
    cases this
  | ok p =>
    cases hn : Internal.parseFloat "-0.0" with
    | error e =>
      have : parseFloatModel "-0.0" = .error e.kind := by rw [← hn_spec, hn]; rfl
      cases this
    | ok n =>
      have hp_m : parseFloatModel "0.0" = .ok p := by rw [← hp_spec, hp]; rfl
      have hn_m : parseFloatModel "-0.0" = .ok n := by rw [← hn_spec, hn]; rfl
      have hp_eq : p = evalFloat false 0 (-1) := (Except.ok.inj hp_m).symm
      have hn_eq : n = evalFloat true 0 (-1) := (Except.ok.inj hn_m).symm
      subst hp_eq; subst hn_eq
      refine ⟨by decide, by decide, by decide, by unfold FloatEquiv; decide, trivial⟩

private def pubCheckFloatOkBits (cases : List (String × Float)) : AllPassRun Unit :=
  cases.forM fun (s, expected) =>
    match defaultApi.parseFloat s with
    | .ok actual => NondetTest.assert (FloatBitMatch expected actual)
    | .error _ => NondetTest.assert False

private theorem pubCheckFloatOkBits_bind (cases : List (String × Float))
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hcases : ∀ p ∈ cases, ∃ y, parseFloatModel p.1 = .ok y ∧ FloatBitMatch p.2 y)
    (hk : k () post) :
    (pubCheckFloatOkBits cases >>= k) post := by
  induction cases with
  | nil => exact hk
  | cons p ps ih =>
    change ((match defaultApi.parseFloat p.1 with
      | .ok actual => NondetTest.assert (FloatBitMatch p.2 actual)
      | .error _ => NondetTest.assert False) : AllPassRun Unit)
      (fun _ => (pubCheckFloatOkBits ps >>= k) post)
    have hp := defaultApi_parseFloat_bits_of_model (hcases p (by simp))
    have hps := ih (fun q hq => hcases q (by simp [hq]))
    cases hd : defaultApi.parseFloat p.1 with
    | error e => rw [hd] at hp; exact False.elim hp
    | ok actual =>
      rw [hd] at hp
      exact ⟨hp, hps⟩

private def pubCheckFloatErr (cases : List (String × NumParseErrorKind)) : AllPassRun Unit :=
  cases.forM fun (s, expected) =>
    match defaultApi.parseFloat s with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "")

private theorem pubCheckFloatErr_bind (cases : List (String × NumParseErrorKind))
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hcases : ∀ p ∈ cases, parseFloatModel p.1 = .error p.2)
    (hk : k () post) :
    (pubCheckFloatErr cases >>= k) post := by
  induction cases with
  | nil => exact hk
  | cons p ps ih =>
    change ((match defaultApi.parseFloat p.1 with
      | .ok _ => NondetTest.assert False
      | .error e => NondetTest.assert (e.kind = p.2 ∧ e.message ≠ "")) : AllPassRun Unit)
      (fun _ => (pubCheckFloatErr ps >>= k) post)
    have hp := defaultApi_parseFloat_err_of_model (hcases p (by simp))
    have hps := ih (fun q hq => hcases q (by simp [hq]))
    cases hd : defaultApi.parseFloat p.1 with
    | ok v => rw [hd] at hp; exact False.elim hp
    | error e =>
      rw [hd] at hp
      exact ⟨hp, hps⟩

private def pubZeroCheck : AllPassRun Unit :=
  match defaultApi.parseFloat "0.0", defaultApi.parseFloat "-0.0" with
  | .ok p, .ok n => do
    NondetTest.assert (p.toBits = (0.0 : Float).toBits)
    NondetTest.assert (n.toBits = (-0.0 : Float).toBits)
    NondetTest.assert (n.toBits ≠ p.toBits)
    NondetTest.assert (FloatEquiv p n)
  | _, _ => NondetTest.assert False

private def floatOkCases : List (String × Float) :=
  [ ("inf", Float.inf), ("+inf", Float.inf), ("-inf", -Float.inf)
  , ("nan", Float.nan), ("+nan", Float.nan), ("-nan", Float.nan)
  , ("0.0", 0.0), ("+0.0", 0.0), ("-0.0", -0.0)
  , ("1e05", evalFloat false 1 5), ("1e-00", 1.0), ("1e+01", 10.0)
  , ("1e400", Float.inf), ("-1e400", -Float.inf)
  , ("1e-400", 0.0), ("-1e-400", -0.0)
  , ("1e1000000000", Float.inf), ("-1e1000000000", -Float.inf)
  , ("1e-1000000000", 0.0), ("-1e-1000000000", -0.0)
  , ("5e-324", evalFloat false 5 (-324)), ("2.47e-324", evalFloat false 247 (-326))
  , ("2.5e-324", evalFloat false 25 (-325)), ("1e-323", evalFloat false 1 (-323)) ]

private def floatErrCases : List (String × NumParseErrorKind) :=
  [ ("", .emptyInput), ("Inf", .invalidSyntax), ("INF", .invalidSyntax)
  , ("Infinity", .invalidSyntax), ("-Infinity", .invalidSyntax)
  , ("NaN", .invalidSyntax), ("NAN", .invalidSyntax), ("42", .invalidSyntax)
  , ("-0", .invalidSyntax), ("1_000", .invalidSyntax), (".5", .invalidSyntax)
  , ("1.", .invalidSyntax), ("1.5e", .invalidSyntax), ("1.5e+", .invalidSyntax)
  , ("01.5", .leadingZero), ("-00e1", .leadingZero), ("0_1.5", .leadingZero)
  , ("1._5", .invalidUnderscore), ("1.5_", .invalidUnderscore)
  , ("1.5e_", .invalidUnderscore), ("1.5e_1", .invalidUnderscore)
  , ("1.5e1_", .invalidUnderscore), ("infx", .trailingChars)
  , ("nanx", .trailingChars), ("1.5x", .trailingChars), ("1.5 ", .trailingChars) ]

/-- Proof of `test_numparse_int_concreteBoundaries` for `defaultApi`. -/
theorem proof_numparse_int_concreteBoundaries :
    AllPass (test_numparse_int_concreteBoundaries defaultApi) := by
  have hrt : ∀ n : Int,
      parseIntModel (defaultApi.formatInt n) = .ok n ∧ defaultApi.parseInt (defaultApi.formatInt n) = .ok n := by
    intro n
    have hm := (parseIntModel_formatInt n).2
    have hok : defaultApi.parseInt (defaultApi.formatInt n) = .ok n := by
      have hs := (parseInt_spec (Internal.formatInt n)).1
      change Internal.parseInt (Internal.formatInt n) = .ok n
      cases h : Internal.parseInt (Internal.formatInt n) with
      | error e =>
        have : parseIntModel (Internal.formatInt n) = .error e.kind := by rw [← hs, h]; rfl
        rw [hm] at this; cases this
      | ok v =>
        have : parseIntModel (Internal.formatInt n) = .ok v := by rw [← hs, h]; rfl
        rw [hm] at this; cases this; rfl
    exact ⟨hm, hok⟩
  dsimp [AllPass, test_numparse_int_concreteBoundaries, Bind.bind, Pure.pure, List.forM, Core.NondetTest.assert]
  repeat'
    first
    | exact True.intro
    | exact rfl
    | exact makeError_msg_ne_empty _ _
    | exact hrt _
    | exact defaultApi_parseInt_of_model (by decide)
    | exact defaultApi_parseInt_err_of_model (by decide)
    | exact defaultApi_parseInt64_of_model (by decide)
    | exact defaultApi_parseInt64_err_of_model (by decide)
    | constructor

/-- Non-vacuity `CanReach` witness for `test_numparse_int_concreteBoundaries`. -/
theorem reach_numparse_int_concreteBoundaries :
    CanReach (test_numparse_int_concreteBoundaries defaultApi) :=
  proof_numparse_int_concreteBoundaries

private theorem exists_parseFloatModel_of_eq {s : String} {neg : Bool} {m : Nat} {e : Int}
    (h : parseFloatModel s = .ok (evalFloat neg m e)) :
    ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch (evalFloat neg m e) y :=
  ⟨evalFloat neg m e, h, floatBitMatch_refl _⟩

/-- Proof of `test_numparse_float_concreteSpecialsAndEdges` for `defaultApi`. -/
theorem proof_numparse_float_concreteSpecialsAndEdges :
    AllPass (test_numparse_float_concreteSpecialsAndEdges defaultApi) := by
  have h1e400 : evalFloat false 1 400 = Float.inf :=
    evalFloat_overflow_ge360 400 (by decide) (by decide)
  have hn1e400 : evalFloat true 1 400 = -Float.inf := by
    rw [evalFloat_neg, h1e400]
  have h1en400 : evalFloat false 1 (-400) = (0.0 : Float) :=
    evalFloat_underflow_le_neg360 (-400) (by decide) (by decide)
  have hn1en400 : evalFloat true 1 (-400) = (-0.0 : Float) := by
    rw [evalFloat_neg, h1en400]
  have h1eBig : evalFloat false 1 1000000000 = Float.inf :=
    evalFloat_overflow_pos (by decide) (by decide)
  have hn1eBig : evalFloat true 1 1000000000 = -Float.inf :=
    evalFloat_overflow_neg (by decide) (by decide)
  have h1enBig : evalFloat false 1 (-1000000000) = (0.0 : Float) :=
    evalFloat_underflow_pos (by decide)
  have hn1enBig : evalFloat true 1 (-1000000000) = (-0.0 : Float) :=
    evalFloat_underflow_neg (by decide)
  change (do pubCheckFloatOkBits floatOkCases; pubCheckFloatErr floatErrCases; pubZeroCheck) (fun _ => True)
  apply pubCheckFloatOkBits_bind
  · intro p hp
    simp only [floatOkCases, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e400" = .ok (evalFloat false 1 400) from rfl, h1e400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e400" = .ok (evalFloat true 1 400) from rfl, hn1e400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e-400" = .ok (evalFloat false 1 (-400)) from rfl, h1en400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e-400" = .ok (evalFloat true 1 (-400)) from rfl, hn1en400]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e1000000000" = .ok (evalFloat false 1 1000000000) from rfl, h1eBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e1000000000" = .ok (evalFloat true 1 1000000000) from rfl, hn1eBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "1e-1000000000" = .ok (evalFloat false 1 (-1000000000)) from rfl, h1enBig]), floatBitMatch_refl _⟩
    · exact ⟨_, (by rw [show parseFloatModel "-1e-1000000000" = .ok (evalFloat true 1 (-1000000000)) from rfl, hn1enBig]), floatBitMatch_refl _⟩
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
  · apply pubCheckFloatErr_bind
    · intro p hp
      simp only [floatErrCases, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · exact float_zero_neg_zero_checks

/-- Non-vacuity `CanReach` witness for `test_numparse_float_concreteSpecialsAndEdges`. -/
theorem reach_numparse_float_concreteSpecialsAndEdges :
    CanReach (test_numparse_float_concreteSpecialsAndEdges defaultApi) :=
  proof_numparse_float_concreteSpecialsAndEdges

end LeanSwe.NumParse.Proofs

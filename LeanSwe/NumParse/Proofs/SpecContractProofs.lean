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

private theorem match_ok_of_mapError {α : Type} {impl : Except NumParseError α}
    {model : Except NumParseErrorKind α} {P : α → Prop} {v : α}
    (hs : impl.mapError (·.kind) = model) (hm : model = .ok v) (hp : P v) :
    match impl with | .ok x => P x | .error _ => False := by
  have hi := impl_eq_ok_of_mapError hs hm
  cases impl with | error _ => cases hi | ok _ => cases hi; exact hp

private theorem match_err_of_mapError {α : Type} {impl : Except NumParseError α}
    {model : Except NumParseErrorKind α} {k : NumParseErrorKind}
    (hs : impl.mapError (·.kind) = model ∧ ∀ e, impl = .error e → e.message ≠ "")
    (hm : model = .error k) :
    match impl with | .ok _ => False | .error e => e.kind = k ∧ e.message ≠ "" := by
  rcases impl_eq_error_of_mapError hs.1 hm with ⟨e, he, hk⟩
  cases impl with | ok _ => cases he | error _ => cases he; exact ⟨hk, hs.2 e rfl⟩

/-- Proof of `test_numparse_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_numparse_onError_returnsNonEmptyMessage :
    AllPass (test_numparse_onError_returnsNonEmptyMessage defaultApi) := by
  intro s
  dsimp [test_numparse_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  cases h1 : Internal.parseInt s <;> cases h2 : Internal.parseInt64 s <;>
    cases h3 : Internal.parseFloat s <;> dsimp only <;>
    refine ⟨?_, ?_, ?_, trivial⟩ <;>
    first | trivial | exact (parseInt_spec s).2 _ h1 | exact (parseInt64_spec s).2 _ h2 | exact (parseFloat_spec s).2 _ h3

/-- Non-vacuity `CanReach` witness for `test_numparse_onError_returnsNonEmptyMessage`. -/
theorem reach_numparse_onError_returnsNonEmptyMessage :
    CanReach (test_numparse_onError_returnsNonEmptyMessage defaultApi) :=
  ⟨"", proof_numparse_onError_returnsNonEmptyMessage ""⟩

/-- Proof of `test_numparse_parseInt_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt_matchesModel :
    AllPass (test_numparse_parseInt_matchesModel defaultApi) := by
  intro s; have hs := parseInt_spec s
  dsimp [test_numparse_parseInt_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseInt s with
  | error e =>
    rw [show parseIntModel s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v =>
    rw [show parseIntModel s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt_matchesModel`. -/
theorem reach_numparse_parseInt_matchesModel :
    CanReach (test_numparse_parseInt_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt_matchesModel "0"⟩

/-- Proof of `test_numparse_parseInt64_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt64_matchesModel :
    AllPass (test_numparse_parseInt64_matchesModel defaultApi) := by
  intro s; have hs := parseInt64_spec s
  dsimp [test_numparse_parseInt64_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseInt64 s with
  | error e =>
    rw [show parseInt64Model s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v =>
    rw [show parseInt64Model s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt64_matchesModel`. -/
theorem reach_numparse_parseInt64_matchesModel :
    CanReach (test_numparse_parseInt64_matchesModel defaultApi) :=
  ⟨"0", proof_numparse_parseInt64_matchesModel "0"⟩

/-- Proof of `test_numparse_formatInt_roundTrip` for `defaultApi`. -/
theorem proof_numparse_formatInt_roundTrip :
    AllPass (test_numparse_formatInt_roundTrip defaultApi) := by
  intro n
  rcases parseIntModel_formatInt n with ⟨hnoU, hmodel⟩
  have hpi_ok := impl_eq_ok_of_mapError (parseInt_spec (Internal.formatInt n)).1 hmodel
  have h64 := parseInt64_spec (Internal.formatInt n)
  dsimp [test_numparse_formatInt_roundTrip, defaultApi, Internal.defaultApi,
    Bind.bind, Core.NondetTest.assert]
  refine ⟨hnoU, hmodel, hpi_ok, ?_⟩
  by_cases hr : inInt64Range n = true
  · simp only [hr, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .ok (Int64.ofInt n) := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr]
    exact ⟨impl_eq_ok_of_mapError h64.1 hm64, trivial⟩
  · have hr' : inInt64Range n = false := Bool.eq_false_iff.mpr hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .error .overflow := by
      rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr']
    rcases impl_eq_error_of_mapError h64.1 hm64 with ⟨e, he, hk⟩
    rw [he]; exact ⟨⟨hk, h64.2 e he⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_formatInt_roundTrip`. -/
theorem reach_numparse_formatInt_roundTrip :
    CanReach (test_numparse_formatInt_roundTrip defaultApi) :=
  ⟨0, proof_numparse_formatInt_roundTrip 0⟩

/-- Proof of `test_numparse_parseFloat_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseFloat_matchesModel :
    AllPass (test_numparse_parseFloat_matchesModel defaultApi) := by
  intro s; have hs := parseFloat_spec s
  dsimp [test_numparse_parseFloat_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseFloat s with
  | error e =>
    rw [show parseFloatModel s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v =>
    rw [show parseFloatModel s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨floatBitMatch_refl v, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseFloat_matchesModel`. -/
theorem reach_numparse_parseFloat_matchesModel :
    CanReach (test_numparse_parseFloat_matchesModel defaultApi) :=
  ⟨"0.0", proof_numparse_parseFloat_matchesModel "0.0"⟩

section FloatBoundaryProofs
open Float.Model Float.Model.UnpackedFloat

private theorem pow2_3n_le_pow10 (n : Nat) : 2 ^ (3 * n) ≤ 10 ^ n := by
  rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) n

private theorem shiftRight_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  change (Nat.repeat ExtendedMantissa.shiftRightOne k em).mantissa = em.mantissa / 2 ^ k
  induction k generalizing em with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    simp only [Nat.repeat, ExtendedMantissa.shiftRightOne]
    rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem shiftToTarget_pos (m : Nat) (e : Int) (hm : m ≠ 0)
    (hle : (Format.binary64.targetExponent (totalExponent m e) - e).toNat ≤ m.log2) :
    0 < (shiftToTargetExponent Format.binary64 m e .exact).1.mantissa := by
  unfold shiftToTargetExponent shiftToExponent
  dsimp only [ExtendedMantissa.ofMantissaAndAccuracy]
  rw [shiftRight_mantissa]
  exact Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by decide) hle) (Nat.log2_self_le hm))
    (Nat.pow_pos (by decide))

private theorem roundedMantissa_ge (em : ExtendedMantissa) : em.mantissa ≤ em.roundedMantissa := by
  rcases em with ⟨m, r, s⟩
  cases r <;> cases s <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]

private theorem evalFloat_overflow_ge360 (p : Nat) (hp : 360 ≤ p) (hp2 : p ≤ 2048) :
    evalFloat false 1 (p : Int) = Float.inf := by
  have h10 := pow2_3n_le_pow10 p
  have hmb : Format.binary64.mantissaBits = 53 := rfl
  have hmin : Format.binary64.minExponent = -1074 := rfl
  let mant := (1 <<< Format.binary64.mantissaBits) * 10 ^ p
  have hmul_pos : mant ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  have hlog : 3 * p ≤ mant.log2 :=
    (Nat.le_log2 hmul_pos).2 (Nat.le_trans h10 (Nat.le_mul_of_pos_left _ (by decide)))
  unfold evalFloat evalFloatModel Float.Model.ofScientific UnpackedFloat.ofScientific
  have hpow2_11 : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
  have hlog1 : Nat.log2 1 = 0 := rfl
  have h1 : ¬((p : Int) > 2 ^ Format.binary64.exponentBits) := by omega
  have h2 : ¬((p : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, h1, h2, Int.natCast_nonneg p]
  change Float.ofModel (Float.Model.pack (UnpackedFloat.mul Format.binary64
    (.finite .positive (1 <<< Format.binary64.mantissaBits) (-Format.binary64.mantissaBits) _)
    (.finite .positive (10 ^ p) 0 _))) = Float.inf
  unfold UnpackedFloat.mul roundWithAccuracy; dsimp only []
  let st1 := shiftToTargetExponent Format.binary64 mant (-(Format.binary64.mantissaBits : Int) + 0) .exact
  have hm1_pos : 0 < st1.1.mantissa :=
    shiftToTarget_pos mant _ hmul_pos (by unfold Format.targetExponent totalExponent; omega)
  have hrem_pos : 0 < st1.1.roundedMantissa := Nat.lt_of_lt_of_le hm1_pos (roundedMantissa_ge _)
  have he1_ge : (972 : Int) ≤ st1.2 := by
    unfold st1 shiftToTargetExponent shiftToExponent Format.targetExponent totalExponent; dsimp only []; omega
  let st2 := shiftToTargetExponent Format.binary64 st1.1.roundedMantissa st1.2 .exact
  have hm2_pos : st2.1.mantissa ≠ 0 := Nat.ne_of_gt
    (shiftToTarget_pos st1.1.roundedMantissa st1.2 (Nat.ne_of_gt hrem_pos)
      (by unfold Format.targetExponent totalExponent; omega))
  have he2_ge : (972 : Int) ≤ st2.2 := by
    unfold st2 shiftToTargetExponent shiftToExponent; dsimp only []; omega
  change Float.ofModel (Float.Model.pack (if h : st2.1.mantissa = 0 then _ else _)) = Float.inf
  simp only [hm2_pos, ↓reduceDIte]
  show Float.ofModel (Float.Model.pack (.finite .positive st2.1.mantissa st2.2 _)) =
    Float.ofModel (Float.Model.pack (.infinity .positive))
  have hge : 2 ^ Format.binary64.exponentBits ≤
      (st2.2 + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    have : 2 ^ Format.binary64.exponentBits = 2048 := rfl
    have : Format.binary64.exponentBias = 1023 := rfl
    have : Format.binary64.mantissaBitsWithoutImplicit = 52 := rfl
    omega
  congr 1; unfold Float.Model.pack; congr 1; unfold UnpackedFloat.pack; simp only [hge, ↓reduceIte]

private theorem accuracy_one_shiftLeft_lt {k d : Nat} (hk : 2 ^ (k + 1) < d) :
    (1 <<< k) / d = 0 ∧ accuracyOfFraction ((1 <<< k) % d) d = .inexact .lt := by
  have hpow : 1 <<< k = 2 ^ k := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2mul : 2 * (1 <<< k) = 2 ^ (k + 1) := by rw [hpow, Nat.mul_comm, Nat.pow_succ]
  have hlt : 1 <<< k < d := hpow ▸ Nat.lt_trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)) hk
  have hne : (1 <<< k) ≠ 0 := hpow ▸ Nat.ne_of_gt (Nat.pow_pos (by decide))
  refine ⟨Nat.div_eq_of_lt hlt, ?_⟩
  rw [Nat.mod_eq_of_lt hlt]; unfold accuracyOfFraction
  simp only [hne, ↓reduceIte, h2mul, compare, compareOfLessAndEq, hk]

private theorem evalFloat_underflow_le_neg360 (p : Nat) (hp : 360 ≤ p) (hp2 : p ≤ 2048) :
    evalFloat false 1 (-(p : Int)) = (0.0 : Float) := by
  have h10 := pow2_3n_le_pow10 p
  have hlog : 3 * p ≤ (10 ^ p).log2 := (Nat.le_log2 (Nat.ne_of_gt (Nat.pow_pos (by decide)))).2 h10
  unfold evalFloat evalFloatModel Float.Model.ofScientific UnpackedFloat.ofScientific
  have hpow2_11 : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
  have hlog1 : Nat.log2 1 = 0 := rfl
  have h1 : ¬(-(p : Int) > 2 ^ Format.binary64.exponentBits) := by omega
  have h2 : ¬(-(p : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (Nat.log2 1 : Int))) := by omega
  have h3 : ¬((0 : Int) ≤ -(p : Int)) := by omega
  have htoNat : (-(-(p : Int))).toNat = p := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, ↓reduceDIte, h1, h2, h3, htoNat]
  change Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64
    (.finite .positive 1 0 _) (.finite .positive (10 ^ p) 0 _))) = 0.0
  unfold UnpackedFloat.div divCore
  have hte : min ((0 : Int) - 0) (Format.binary64.targetExponent
      (totalExponent 1 0 - totalExponent (10 ^ p) 0)) = -1074 := by
    have : Format.binary64.minExponent = -1074 := rfl
    have : Format.binary64.mantissaBits = 53 := rfl
    unfold Format.targetExponent totalExponent; omega
  have hk_lt : 2 ^ (1074 + 1) < 10 ^ p :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (a := 2) (m := 1074 + 1) (n := 3 * p) (by decide) (by omega)) h10
  have ⟨hdiv, hacc⟩ := accuracy_one_shiftLeft_lt (k := 1074) hk_lt
  dsimp only []
  rw [hte, show ((0 : Int) - 0 - (-1074 : Int)).toNat = 1074 from rfl, hdiv, hacc]; decide

end FloatBoundaryProofs

private theorem list_forM_allPass_bind {α : Type} (xs : List α) (f : α → AllPassRun Unit)
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hxs : ∀ x ∈ xs, ∀ q : Unit → Prop, q () → f x q) (hk : k () post) :
    (xs.forM f >>= k) post := by
  induction xs with
  | nil => exact hk
  | cons x xs ih => exact hxs x (by simp) _ (ih (fun y hy => hxs y (by simp [hy])))

/-- Proof of `test_numparse_int_concreteBoundaries` for `defaultApi`. -/
theorem proof_numparse_int_concreteBoundaries :
    AllPass (test_numparse_int_concreteBoundaries defaultApi) := by
  have hrt : ∀ n : Int,
      parseIntModel (defaultApi.formatInt n) = .ok n ∧ defaultApi.parseInt (defaultApi.formatInt n) = .ok n :=
    fun n => ⟨(parseIntModel_formatInt n).2, impl_eq_ok_of_mapError (parseInt_spec _).1 (parseIntModel_formatInt n).2⟩
  dsimp [AllPass, test_numparse_int_concreteBoundaries, Bind.bind, Pure.pure, List.forM, Core.NondetTest.assert]
  repeat'
    first
    | exact True.intro | exact rfl | exact makeError_msg_ne_empty _ _ | exact hrt _
    | exact match_ok_of_mapError (parseInt_spec _).1 (by decide) rfl
    | exact match_err_of_mapError (parseInt_spec _) (by decide)
    | exact match_ok_of_mapError (parseInt64_spec _).1 (by decide) rfl
    | exact match_err_of_mapError (parseInt64_spec _) (by decide)
    | constructor

/-- Non-vacuity `CanReach` witness for `test_numparse_int_concreteBoundaries`. -/
theorem reach_numparse_int_concreteBoundaries :
    CanReach (test_numparse_int_concreteBoundaries defaultApi) :=
  proof_numparse_int_concreteBoundaries

private theorem float_ok_case {s : String} {expected : Float}
    (h : ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch expected y)
    {q : Unit → Prop} (hq : q ()) :
    (match defaultApi.parseFloat s with
      | .ok actual => NondetTest.assert (FloatBitMatch expected actual)
      | .error _ => NondetTest.assert False : AllPassRun Unit) q := by
  rcases h with ⟨y, hmy, hbit⟩
  rw [show defaultApi.parseFloat s = .ok y from impl_eq_ok_of_mapError (parseFloat_spec s).1 hmy]
  exact ⟨hbit, hq⟩

private theorem float_err_case {s : String} {expected : NumParseErrorKind}
    (hm : parseFloatModel s = .error expected) {q : Unit → Prop} (hq : q ()) :
    (match defaultApi.parseFloat s with
      | .ok _ => NondetTest.assert False
      | .error e => NondetTest.assert (e.kind = expected ∧ e.message ≠ "") : AllPassRun Unit) q := by
  rcases impl_eq_error_of_mapError (parseFloat_spec s).1 hm with ⟨e, he, hk⟩
  rw [show defaultApi.parseFloat s = .error e from he]
  exact ⟨⟨hk, (parseFloat_spec s).2 e he⟩, hq⟩

private theorem exists_parseFloatModel_of_eq {s : String} {neg : Bool} {m : Nat} {e : Int}
    (h : parseFloatModel s = .ok (evalFloat neg m e)) :
    ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch (evalFloat neg m e) y :=
  ⟨evalFloat neg m e, h, floatBitMatch_refl _⟩

/-- Proof of `test_numparse_float_concreteSpecialsAndEdges` for `defaultApi`. -/
theorem proof_numparse_float_concreteSpecialsAndEdges :
    AllPass (test_numparse_float_concreteSpecialsAndEdges defaultApi) := by
  have h1e400 : evalFloat false 1 400 = Float.inf := evalFloat_overflow_ge360 400 (by decide) (by decide)
  have hn1e400 : evalFloat true 1 400 = -Float.inf := (evalFloat_neg 1 400).trans (congrArg Neg.neg h1e400)
  have h1en400 : evalFloat false 1 (-400) = (0.0 : Float) := evalFloat_underflow_le_neg360 400 (by decide) (by decide)
  have hn1en400 : evalFloat true 1 (-400) = (-0.0 : Float) := (evalFloat_neg 1 (-400)).trans (congrArg Neg.neg h1en400)
  have h1eBig : evalFloat false 1 1000000000 = Float.inf := evalFloat_overflow_pos (by decide) (by decide)
  have hn1eBig : evalFloat true 1 1000000000 = -Float.inf := evalFloat_overflow_neg (by decide) (by decide)
  have h1enBig : evalFloat false 1 (-1000000000) = (0.0 : Float) := evalFloat_underflow_pos (by decide)
  have hn1enBig : evalFloat true 1 (-1000000000) = (-0.0 : Float) := evalFloat_underflow_neg (by decide)
  have hBig : ∀ {s : String} {neg : Bool} {m : Nat} {e : Int} {v : Float},
      evalFloat neg m e = v → parseFloatModel s = .ok (evalFloat neg m e) →
      ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch v y :=
    fun hv hp => ⟨_, hp.trans (congrArg Except.ok hv), floatBitMatch_refl _⟩
  unfold AllPass test_numparse_float_concreteSpecialsAndEdges
  apply list_forM_allPass_bind
  · intro p hp q hq
    apply float_ok_case _ hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
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
    · exact exists_parseFloatModel_of_eq rfl
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact hBig h1e400 rfl
    · exact hBig hn1e400 rfl
    · exact hBig h1en400 rfl
    · exact hBig hn1en400 rfl
    · exact hBig h1eBig rfl
    · exact hBig hn1eBig rfl
    · exact hBig h1enBig rfl
    · exact hBig hn1enBig rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
  · apply list_forM_allPass_bind
    · intro p hp q hq
      apply float_err_case _ hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have hp : defaultApi.parseFloat "0.0" = .ok (evalFloat false 0 (-1)) := impl_eq_ok_of_mapError (parseFloat_spec "0.0").1 rfl
      have hn : defaultApi.parseFloat "-0.0" = .ok (evalFloat true 0 (-1)) := impl_eq_ok_of_mapError (parseFloat_spec "-0.0").1 rfl
      rw [hp, hn]; exact ⟨by decide, by decide, by decide, by unfold FloatEquiv; decide, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_float_concreteSpecialsAndEdges`. -/
theorem reach_numparse_float_concreteSpecialsAndEdges :
    CanReach (test_numparse_float_concreteSpecialsAndEdges defaultApi) :=
  proof_numparse_float_concreteSpecialsAndEdges

end LeanSwe.NumParse.Proofs

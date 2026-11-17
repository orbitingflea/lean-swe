import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs.FloatParseProofs
import LeanSwe.NumParse.Proofs.FloatRenderProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem nat_log2_pow2_bounds (n : Nat) (hn : 0 < n) :
    2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.log2_def]
    by_cases h2 : 2 ≤ n
    · simp only [h2, ↓reduceIte]
      have hdpos : 0 < n / 2 := by omega
      have hdlt : n / 2 < n := Nat.div_lt_self hn (by decide)
      obtain ⟨hlo, hhi⟩ := ih (n / 2) hdlt hdpos
      constructor
      · rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ]; omega
    · simp only [h2, ↓reduceIte]
      omega

private theorem nat_log2_eq_of_bounds {n k : Nat} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    n.log2 = k := by
  have hkpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hkpos hlo
  obtain ⟨hl, hr⟩ := nat_log2_pow2_bounds n hnpos
  have h1 : 2 ^ n.log2 < 2 ^ (k + 1) := Nat.lt_of_le_of_lt hl hhi
  have h2 : 2 ^ k < 2 ^ (n.log2 + 1) := Nat.lt_of_le_of_lt hlo hr
  have hlt1 : n.log2 < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  have hlt2 : k < n.log2 + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

private theorem nat_log2_mul_pow2 (a s : Nat) (ha : 0 < a) :
    (a * 2 ^ s).log2 = a.log2 + s := by
  obtain ⟨hlo, hhi⟩ := nat_log2_pow2_bounds a ha
  apply nat_log2_eq_of_bounds
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul_right (2 ^ s) hlo
  · rw [Nat.add_right_comm, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hhi (Nat.pow_pos (by decide))

private theorem nat_log2_mul_bounds (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a.log2 + b.log2 ≤ (a * b).log2 ∧ (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  obtain ⟨halo, hahi⟩ := nat_log2_pow2_bounds a ha
  obtain ⟨hblo, hbhi⟩ := nat_log2_pow2_bounds b hb
  have hab : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨hlo, hhi⟩ := nat_log2_pow2_bounds (a * b) hab
  have hpow_lo : 2 ^ (a.log2 + b.log2) ≤ a * b := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul halo hblo
  have hpow_hi : a * b < 2 ^ (a.log2 + b.log2 + 2) := by
    have hmul : a * b < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt hahi))
        (Nat.mul_lt_mul_of_pos_left hbhi (Nat.pow_pos (by decide)))
    have hexp : 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) = 2 ^ (a.log2 + b.log2 + 2) := by
      rw [← Nat.pow_add]
      congr 1; omega
    exact hexp ▸ hmul
  have h1 : 2 ^ (a.log2 + b.log2) < 2 ^ ((a * b).log2 + 1) := Nat.lt_of_le_of_lt hpow_lo hhi
  have h2 : 2 ^ (a * b).log2 < 2 ^ (a.log2 + b.log2 + 2) := Nat.lt_of_le_of_lt hlo hpow_hi
  have hlt1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  have hlt2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

private theorem extendedMantissa_shift_exact_mul_pow2 (m s : Nat) :
    (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ s) .exact >>> s) =
      ⟨m, false, false⟩ := by
  induction s generalizing m with
  | zero =>
    simp [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    have hm2 : m * 2 ^ (k + 1) = (m * 2) * 2 ^ k := by
      rw [Nat.pow_succ', ← Nat.mul_assoc]
    have hrep : ∀ em : Float.Model.UnpackedFloat.ExtendedMantissa,
        (em >>> (k + 1)) = Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne (em >>> k) := by
      intro em; rfl
    rw [hrep, hm2]
    have ihk := ih (m * 2)
    change Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne
      (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy ((m * 2) * 2 ^ k) .exact >>> k) =
      ⟨m, false, false⟩
    rw [ihk]
    simp [Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]

private theorem shiftRightOne_two_mul (m : Nat) :
    Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne ⟨2 * m, false, false⟩ = ⟨m, false, false⟩ := by
  simp [Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne]

private theorem shiftToTargetExponent_exact (m : Nat) (e2 : Int)
    (htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2) :
    Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 m e2 .exact =
      (⟨m, false, false⟩, e2) := by
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
  rw [htarg]
  dsimp only
  have hsh0 : (e2 - e2).toNat = 0 := by omega
  rw [hsh0]
  simp [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
    HShiftRight.hShiftRight, Nat.repeat]

private theorem roundWithAccuracy_binary64_pos_exact (m : Nat) (e2 : Int)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    (Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive m e2 .exact) =
      .finite .positive m e2 (by rcases hvalid with ⟨_, hm, _⟩ | ⟨hm, _⟩ <;> omega) := by
  have hmpos : 0 < m := by rcases hvalid with ⟨_, hm, _⟩ | ⟨hm, _⟩ <;> omega
  have htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin]
    rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
    · have hloglt : m.log2 < 52 := by
        obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
        have hlt : 2 ^ m.log2 < 2 ^ 52 := Nat.lt_of_le_of_lt hlo hm52
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
      omega
    · have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      omega
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
  simp only [shiftToTargetExponent_exact m e2 htarg,
    Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  have hmne : m ≠ 0 := by omega
  simp only [hmne, ↓reduceDIte]

private theorem roundWithAccuracy_binary64_pos_double (m : Nat) (e2 : Int)
    (hm52 : 2 ^ 52 ≤ m) (hm53 : m < 2 ^ 53) (he_lo : -1073 ≤ e2) (he_hi : e2 ≤ 971) :
    Float.Model.UnpackedFloat.roundWithAccuracy Float.Model.Format.binary64 .positive (2 * m) (e2 - 1) .exact =
      .finite .positive m e2 (by omega) := by
  have hmpos : 0 < m := by omega
  have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
  have hlog2 : (2 * m).log2 = 53 := by
    have hpow : 2 * m = m * 2 ^ 1 := by omega
    rw [hpow, nat_log2_mul_pow2 m 1 hmpos, hlog]
  have htarg : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent (2 * m) (e2 - 1)) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin, hlog2]
    omega
  have htarg2 : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m e2) = e2 := by
    unfold Float.Model.Format.targetExponent Float.Model.totalExponent
    have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
    have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
    rw [hmb, hmin, hlog]
    omega
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
  have hsh1_step : Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64 (2 * m) (e2 - 1) .exact =
      (⟨m, false, false⟩, e2) := by
    unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
    rw [htarg]
    dsimp only
    have hsh1 : (e2 - (e2 - 1)).toNat = 1 := by omega
    rw [hsh1]
    simp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      HShiftRight.hShiftRight, Nat.repeat]
    rw [shiftRightOne_two_mul]
    exact Prod.ext rfl (by omega)
  rw [hsh1_step]
  dsimp only
  simp only [shiftToTargetExponent_exact m e2 htarg2,
    Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  have hmne : m ≠ 0 := by omega
  simp only [hmne, ↓reduceDIte]

private theorem packComponents_unpack_eq (b : BitVec 64) :
    Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.Sign.ofBitVec
        (Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b))
      (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b)
      (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b) = b := by
  let signVec := Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b
  have hsign : (Float.Model.UnpackedFloat.Sign.ofBitVec signVec).toBitVec = signVec := by
    unfold Float.Model.UnpackedFloat.Sign.ofBitVec
    split
    · rename_i h; rw [h]; rfl
    · rename_i h
      have h1 : signVec = 1#1 := by
        have hb : signVec.toNat < 2 ^ 1 := signVec.isLt
        have hb2 : signVec.toNat < 2 := Nat.lt_of_lt_of_eq hb (by decide)
        have hnz : signVec.toNat ≠ 0 := by
          intro hz; apply h; exact BitVec.eq_of_toNat_eq hz
        have hnat1 : signVec.toNat = (1#1 : BitVec 1).toNat := by
          change signVec.toNat = 1
          omega
        exact BitVec.eq_of_toNat_eq hnat1
      rw [h1]; rfl
  rw [Float.Model.UnpackedFloat.packComponents, hsign]
  ext i hi
  have hlen : 1 + Float.Model.Format.binary64.exponentBits + Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 64 := rfl
  rw [hlen] at hi
  have hget : ∀ j (hj : j < 64), b.getLsbD j = b[j] := fun j hj => BitVec.getLsbD_eq_getElem hj
  simp only [signVec, Float.Model.UnpackedFloat.unpackSign,
    Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
    Float.Model.Format.binary64]
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  by_cases h52 : i < 52
  · simp only [h52, ↓reduceDIte]
    rw [hget _ (by omega)]
    congr 1; omega
  · by_cases h63 : i < 63
    · have h11 : i - 52 < 11 := by omega
      simp only [h52, ↓reduceDIte, h11]
      rw [hget _ (by omega)]
      congr 1; omega
    · have h1 : i - 63 < 1 := by omega
      have hn11 : ¬(i - 52 < 11) := by omega
      simp only [h52, ↓reduceDIte, hn11]
      rw [hget _ (by omega)]
      congr 1; omega

private theorem unpackSign_packComponents
    {sign : Float.Model.UnpackedFloat.Sign}
    {exponent : BitVec 11}
    {mantissa : BitVec 52} :
    Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64)
        (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 sign exponent mantissa) =
      sign.toBitVec := by
  ext i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp only [Float.Model.UnpackedFloat.unpackSign, Float.Model.UnpackedFloat.packComponents,
    Float.Model.Format.binary64, BitVec.getElem_extractLsb']
  have hget : ∀ (v : BitVec (1 + 11 + 52)) j (hj : j < 64), v.getLsbD j = v[j] :=
    fun v j hj => BitVec.getLsbD_eq_getElem hj
  rw [hget _ 63 (by omega)]
  rw [BitVec.getElem_append]
  split
  · omega
  · rw [BitVec.getElem_append]
    split
    · omega
    · rfl

private theorem unpack_finite_props (x : Float) (sign : Float.Model.UnpackedFloat.Sign)
    (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) :
    ((e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) ∧
      (Float.Model.pack (.finite sign m e2 hm)).toBits = x.toModel.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  have hun_def : Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .finite sign m e2 hm := hun
  unfold Float.Model.UnpackedFloat.unpack at hun_def
  dsimp only at hun_def
  have hrepack : Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.Sign.ofBitVec (Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b))
      (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b)
      (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b) = b :=
    packComponents_unpack_eq b
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun_def
    split at hun_def <;> cases hun_def
  · simp only [hexp1, ↓reduceIte] at hun_def
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun_def
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp [hmant0] at hun_def
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.finite.injEq] at hun_def
        rcases hun_def with ⟨rfl, rfl, rfl⟩
        have hm52 : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 52 :=
          (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        have hmpos : 0 < (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
          have : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b ≠ 0#52 := hmant0
          exact Nat.pos_of_ne_zero (fun hz => this (BitVec.eq_of_toNat_eq hz))
        have heq : (↑(0#11 : BitVec 11).toNat -
            (↑Float.Model.Format.binary64.exponentBias + ↑Float.Model.Format.binary64.mantissaBitsWithoutImplicit) + 1 : Int) = -1074 := rfl
        rw [heq]
        refine ⟨Or.inl ⟨rfl, hmpos, hm52⟩, ?_⟩
        apply congrArg UInt64.ofBitVec
        simp only [Float.Model.UnpackedFloat.pack]
        have hloglt : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 < 52 := by
          obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds _ hmpos
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
        have hbiased : ((-1074 : Int) + Float.Model.Format.binary64.exponentBias +
            Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = 1 := rfl
        have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ 1 + 1) := by decide
        have hcond2 : ¬((Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 + 1 =
            Float.Model.Format.binary64.mantissaBits) := by
          change ¬(_ + 1 = 53); omega
        simp only [hbiased, hcond1, ↓reduceIte, hcond2]
        have hmbv : BitVec.ofNat 52 (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
            Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b :=
          BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt hm52)
        rw [← hexp0, hmbv]
        exact hrepack
    · simp only [hexp0, ↓reduceIte, Float.Model.UnpackedFloat.finite.injEq] at hun_def
      rcases hun_def with ⟨rfl, rfl, rfl⟩
      have hexp_lt : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat < 2047 := by
        have hle : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat < 2048 :=
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).isLt
        have hne : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat ≠ 2047 := by
          intro h; apply hexp1; exact BitVec.eq_of_toNat_eq h
        omega
      have hexp_pos : 0 < (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat := by
        have hne : (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat ≠ 0 := by
          intro h; apply hexp0; exact BitVec.eq_of_toNat_eq h
        omega
      have hm_val : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
          2 ^ 52 + (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
        rw [BitVec.toNat_append_eq_mul_add]; rfl
      have hm_lo : 2 ^ 52 ≤ (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat := by
        rw [hm_val]; omega
      have hm_hi : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 53 := by
        have h52 : (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 52 :=
          (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        rw [hm_val]; omega
      have he_val : (((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) -
          (Float.Model.Format.binary64.exponentBias + Float.Model.Format.binary64.mantissaBitsWithoutImplicit)) =
          ((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) - 1075 := rfl
      rw [he_val]
      refine ⟨Or.inr ⟨hm_lo, hm_hi, by omega, by omega⟩, ?_⟩
      apply congrArg UInt64.ofBitVec
      simp only [Float.Model.UnpackedFloat.pack]
      have hlog : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 = 52 :=
        nat_log2_eq_of_bounds hm_lo hm_hi
      have hbiased : ((((Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat : Int) -
          1075) +
          Float.Model.Format.binary64.exponentBias + Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat =
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat := by
        have hbm : (Float.Model.Format.binary64.exponentBias +
            Float.Model.Format.binary64.mantissaBitsWithoutImplicit : Int) = 1075 := rfl
        rw [Int.add_assoc, hbm]; omega
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤
          (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat + 1) := by
        change ¬(2048 ≤ _ + 1); omega
      have hcond2 : (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat.log2 + 1 =
          Float.Model.Format.binary64.mantissaBits := by
        rw [hlog]; rfl
      simp only [hbiased, hcond1, ↓reduceIte, hcond2]
      have hebv : BitVec.ofNat 11 (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat =
          Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b :=
        BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).isLt)
      have hmbv : BitVec.ofNat 52 (1#1 ++ Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat =
          Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b := by
        apply BitVec.eq_of_toNat_eq
        have h52 := (Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
        simp only [BitVec.toNat_ofNat, hm_val, Nat.add_mod_left, Nat.mod_eq_of_lt h52]
      rw [hebv, hmbv]
      exact hrepack

private theorem neg_pack_finite_pos (m : Nat) (e2 : Int) (hm : 0 < m)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    Float.Model.neg (Float.Model.pack (.finite .positive m e2 hm)) =
      Float.Model.pack (.finite .negative m e2 hm) := by
  have hunpack : (Float.Model.pack (.finite .positive m e2 hm)).unpack = .finite .positive m e2 hm := by
    unfold Float.Model.unpack Float.Model.pack Float.Model.UnpackedFloat.pack
    dsimp only
    have hbm : (Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit : Int) = 1075 := rfl
    have hbiased : (e2 + Float.Model.Format.binary64.exponentBias +
        Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = (e2 + 1075).toNat := by
      rw [Int.add_assoc, hbm]
    rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
    · have hloglt : m.log2 < 52 := by
        obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
      have hbiased1 : ((-1074 : Int) + Float.Model.Format.binary64.exponentBias +
          Float.Model.Format.binary64.mantissaBitsWithoutImplicit).toNat = 1 := rfl
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ 1 + 1) := by decide
      have hcond2 : ¬(m.log2 + 1 = Float.Model.Format.binary64.mantissaBits) := by
        change ¬(m.log2 + 1 = 53); omega
      simp only [hbiased1, hcond1, ↓reduceIte, hcond2]
      unfold Float.Model.UnpackedFloat.unpack
      simp only [Float.Model.UnpackedFloat.unpackExponent_packComponents,
        Float.Model.UnpackedFloat.unpackMantissa_packComponents]
      have hsign : Float.Model.UnpackedFloat.Sign.ofBitVec
          (Float.Model.UnpackedFloat.unpackSign
            (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 .positive 0#_ (BitVec.ofNat _ m))) =
          .positive := by
        rw [unpackSign_packComponents]; rfl
      have hexp1 : (0#11 : BitVec 11) ≠ -1#11 := by decide
      have hmant_ne : (BitVec.ofNat 52 m) ≠ 0#52 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hm52] at this; omega
      simp only [hsign, hexp1, ↓reduceIte, hmant_ne, ↓reduceDIte, Float.Model.UnpackedFloat.finite.injEq]
      refine ⟨trivial, Nat.mod_eq_of_lt hm52, rfl⟩
    · have hlog : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      have hcond1 : ¬(2 ^ Float.Model.Format.binary64.exponentBits ≤ (e2 + 1075).toNat + 1) := by
        change ¬(2048 ≤ (e2 + 1075).toNat + 1); omega
      have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
      have hcond2 : m.log2 + 1 = Float.Model.Format.binary64.mantissaBits := by
        rw [hmb, hlog]
      simp only [hbiased, hcond1, ↓reduceIte, hcond2]
      unfold Float.Model.UnpackedFloat.unpack
      simp only [Float.Model.UnpackedFloat.unpackExponent_packComponents,
        Float.Model.UnpackedFloat.unpackMantissa_packComponents]
      have hsign : Float.Model.UnpackedFloat.Sign.ofBitVec
          (Float.Model.UnpackedFloat.unpackSign
            (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 .positive
              (BitVec.ofNat _ (e2 + 1075).toNat) (BitVec.ofNat _ m))) = .positive := by
        rw [unpackSign_packComponents]; rfl
      have hlt2047 : (e2 + 1075).toNat < 2047 := by omega
      have hpos_e : 0 < (e2 + 1075).toNat := by omega
      have hexp_ne1 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ -1#11 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)] at this; omega
      have hexp_ne0 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ 0#11 := by
        intro h; have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)] at this; omega
      simp only [hsign, hexp_ne1, ↓reduceIte, hexp_ne0, Float.Model.UnpackedFloat.finite.injEq]
      refine ⟨trivial, ?_, ?_⟩
      · have hlt52 : m - 2 ^ 52 < 2 ^ 52 :=
          Nat.sub_lt_left_of_lt_add hm52 (by rw [← Nat.two_mul]; exact hm53)
        have hsub52 : 2 ^ 52 + (m - 2 ^ 52) = m := Nat.add_sub_cancel' hm52
        have hmod52 : (BitVec.ofNat 52 m).toNat = m - 2 ^ 52 := by
          simp only [BitVec.toNat_ofNat]
          have hmod := Nat.add_mod_left (2 ^ 52) (m - 2 ^ 52)
          rw [hsub52] at hmod
          rw [hmod, Nat.mod_eq_of_lt hlt52]
        rw [BitVec.toNat_append_eq_mul_add, hmod52]
        have h1_val : (1#1 : BitVec 1).toNat * 2 ^ Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 2 ^ 52 := rfl
        rw [h1_val]
        exact hsub52
      · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (e2 + 1075).toNat < 2048)]
        have hbm' : (Float.Model.Format.binary64.exponentBias : Int) + (52 : Nat) = 1075 := rfl
        rw [hbm']; omega
  unfold Float.Model.neg
  rw [hunpack]
  rfl

private theorem evalFloat_fallback_pos_bits (m : Nat) (e2 : Int) (hm : 0 < m)
    (hvalid : (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)) :
    Float.Model.ofScientific (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat) (if 0 ≤ e2 then 0 else e2) =
      Float.Model.pack (.finite .positive m e2 hm) := by
  unfold Float.Model.ofScientific
  congr 1
  by_cases he : 0 ≤ e2
  · cases e2 with
    | negSucc _ => exact absurd he (by omega)
    | ofNat n =>
      have hm52 : 2 ^ 52 ≤ m := by rcases hvalid with ⟨h0, _⟩ | ⟨h, _⟩; exact absurd h0 (by omega); exact h
      have hm53 : m < 2 ^ 53 := by rcases hvalid with ⟨h0, _⟩ | ⟨_, h, _⟩; exact absurd h0 (by omega); exact h
      have hehi : (Int.ofNat n) ≤ 971 := by rcases hvalid with ⟨h0, _⟩ | ⟨_, _, _, h⟩; exact absurd h0 (by omega); exact h
      have hnt : (Int.ofNat n).toNat = n := rfl
      simp only [he, ↓reduceIte, hnt]
      have hM : m <<< n = m * 2 ^ n := Nat.shiftLeft_eq m n
      have hMpos : 0 < m <<< n := by rw [hM]; exact Nat.mul_pos hm (Nat.pow_pos (by decide))
      have hMne : m <<< n ≠ 0 := by omega
      unfold Float.Model.UnpackedFloat.ofScientific
      dsimp only
      have hexpb : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := rfl
      have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
      have hno1 : ¬((0 : Int) > 2 ^ Float.Model.Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬((0 : Int) < -((2 ^ Float.Model.Format.binary64.exponentBits : Int) + (m <<< n).log2)) := by
        have hnn : (0 : Int) ≤ (m <<< n).log2 := Int.natCast_nonneg _
        rw [hexpb]; omega
      have hge0 : (0 : Int) ≤ 0 := Int.le_refl 0
      simp only [hMne, ↓reduceDIte, hno1, hno2, hge0, ↓reduceIte]
      unfold Float.Model.UnpackedFloat.mul
      dsimp only
      have hs_mul : (Float.Model.UnpackedFloat.Sign.positive * Float.Model.UnpackedFloat.Sign.positive) = .positive := rfl
      rw [hs_mul]
      have hz_nat : (0 : Int).toNat = 0 := rfl
      have hmul_val : ((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat =
          m * 2 ^ (n + 53) := by
        rw [hz_nat, Nat.pow_zero, Nat.mul_one, hmb, hM, Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add]
      have hlogm : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
      have hlog_mul : (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat).log2 =
          52 + (n + 53) := by
        rw [hmul_val, nat_log2_mul_pow2 m (n + 53) hm, hlogm]
      have htarg : Float.Model.Format.binary64.targetExponent
          (Float.Model.totalExponent (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat)
            (-↑Float.Model.Format.binary64.mantissaBits + 0)) = Int.ofNat n := by
        unfold Float.Model.Format.targetExponent Float.Model.totalExponent
        have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
        rw [hlog_mul, hmb, hmin, Int.add_zero]
        omega
      have hsh1_step : Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.Format.binary64
          (((m <<< n) <<< Float.Model.Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat)
          (-↑Float.Model.Format.binary64.mantissaBits + 0) .exact = (⟨m, false, false⟩, Int.ofNat n) := by
        unfold Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
        rw [htarg]
        dsimp only
        have hsh : (Int.ofNat n - (-↑Float.Model.Format.binary64.mantissaBits + 0)).toNat = n + 53 := by
          rw [hmb]; omega
        rw [hsh, hmul_val, extendedMantissa_shift_exact_mul_pow2 m (n + 53)]
        have hexp : (-↑Float.Model.Format.binary64.mantissaBits + 0 : Int) + ↑(n + 53) = Int.ofNat n := by
          rw [hmb]; push_cast; omega
        rw [hexp]
      have htarg2 : Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent m (Int.ofNat n)) = Int.ofNat n := by
        unfold Float.Model.Format.targetExponent Float.Model.totalExponent
        have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
        rw [hmb, hmin, hlogm]; omega
      unfold Float.Model.UnpackedFloat.roundWithAccuracy
      rw [hsh1_step]
      dsimp only
      simp only [shiftToTargetExponent_exact m (Int.ofNat n) htarg2,
        Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
        Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
        Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
      have hmne : m ≠ 0 := by omega
      simp only [hmne, ↓reduceDIte]
  · cases e2 with
    | ofNat n => exact absurd (Int.natCast_nonneg n) he
    | negSucc e' =>
      simp only [he, ↓reduceIte]
      let k := (-Int.negSucc e').toNat
      have hk_def : k = e' + 1 := rfl
      have hk_eq : Int.negSucc e' = -Int.ofNat k := rfl
      have hk_pos : 1 ≤ k := by rw [hk_def]; omega
      have hk_le : k ≤ 1074 := by
        rw [hk_def]
        rcases hvalid with ⟨h0, _⟩ | ⟨_, _, he_lo, _⟩ <;> omega
      let M := m * 5 ^ k
      have h5pos : 0 < 5 ^ k := Nat.pow_pos (by decide)
      have hMpos : 0 < M := Nat.mul_pos hm h5pos
      have hMne : m * 5 ^ (-Int.negSucc e').toNat ≠ 0 := Nat.ne_of_gt hMpos
      unfold Float.Model.UnpackedFloat.ofScientific
      dsimp only
      have hexpb : (2 ^ Float.Model.Format.binary64.exponentBits : Int) = 2048 := rfl
      have hno1 : ¬(Int.negSucc e' > 2 ^ Float.Model.Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬(Int.negSucc e' < -(2 ^ 11 + ↑(m * 5 ^ (-Int.negSucc e').toNat).log2)) := by
        have hnn : (0 : Int) ≤ (m * 5 ^ (-Int.negSucc e').toNat).log2 := Int.natCast_nonneg _
        omega
      have hnotge : ¬(0 ≤ Int.negSucc e') := he
      simp only [hMne, ↓reduceDIte, hno1, hno2, hnotge, ↓reduceIte]
      unfold Float.Model.UnpackedFloat.div Float.Model.UnpackedFloat.divCore
      dsimp only
      have hsdiv : (Float.Model.UnpackedFloat.Sign.positive / Float.Model.UnpackedFloat.Sign.positive) = .positive := rfl
      rw [hsdiv]
      have h00 : (0 : Int) - 0 = 0 := rfl
      have h10_eq : 10 ^ k = 5 ^ k * 2 ^ k := by rw [← Nat.mul_pow]
      have hlog10 : (10 ^ k).log2 = (5 ^ k).log2 + k := by
        rw [h10_eq, nat_log2_mul_pow2 (5 ^ k) k h5pos]
      obtain ⟨hM_lo, hM_hi⟩ := nat_log2_mul_bounds m (5 ^ k) hm h5pos
      have hM_lo_i : (m.log2 : Int) + ((5 ^ k).log2 : Int) ≤ (M.log2 : Int) := by
        have h := Int.ofNat_le.mpr hM_lo
        push_cast at h; exact h
      have hM_hi_i : (M.log2 : Int) ≤ (m.log2 : Int) + ((5 ^ k).log2 : Int) + 1 := by
        have h := Int.ofNat_le.mpr hM_hi
        push_cast at h; exact h
      have hlog10_i : ((10 ^ k).log2 : Int) = ((5 ^ k).log2 : Int) + (k : Int) := by
        have h := congrArg (Int.ofNat) hlog10
        push_cast at h; exact h
      have hdiv_exact : ∀ s : Nat, k ≤ s →
          (M <<< s) / 10 ^ k = m * 2 ^ (s - k) ∧ (M <<< s) % 10 ^ k = 0 := by
        intro s hs
        have hpow : 2 ^ s = 2 ^ k * 2 ^ (s - k) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hmul : M <<< s = (m * 2 ^ (s - k)) * 10 ^ k := by
          rw [Nat.shiftLeft_eq]
          dsimp only [M]
          rw [hpow, h10_eq]
          calc
            m * 5 ^ k * (2 ^ k * 2 ^ (s - k))
                = m * (5 ^ k * (2 ^ k * 2 ^ (s - k))) := Nat.mul_assoc _ _ _
            _ = m * ((5 ^ k * 2 ^ k) * 2 ^ (s - k)) := by rw [Nat.mul_assoc (5 ^ k)]
            _ = m * (2 ^ (s - k) * (5 ^ k * 2 ^ k)) := by rw [Nat.mul_comm (5 ^ k * 2 ^ k)]
            _ = m * 2 ^ (s - k) * (5 ^ k * 2 ^ k) := (Nat.mul_assoc _ _ _).symm
        rw [hmul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide : 0 < 10)), Nat.mul_mod_left]
        exact ⟨rfl, rfl⟩
      rcases hvalid with ⟨h1074, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
      · have hk1074 : k = 1074 := by rw [hk_def]; omega
        have hk_i : (k : Int) = 1074 := by rw [hk1074]; rfl
        have hloglt : m.log2 < 52 := by
          obtain ⟨hlo, _⟩ := nat_log2_pow2_bounds m hm0
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlo hm52)
        have hloglt_i : (m.log2 : Int) < 52 := Int.ofNat_lt.mpr hloglt
        have htarg : Float.Model.Format.binary64.targetExponent
            (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = -1074 := by
          unfold Float.Model.Format.targetExponent Float.Model.totalExponent
          have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
          have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
          rw [hmb, hmin]
          omega
        have hmin0 : min (0 : Int) (-1074) = -1074 := by omega
        rw [htarg, h00, hmin0]
        have hsh : ((0 : Int) - (-1074 : Int)).toNat = 1074 := rfl
        rw [hsh]
        obtain ⟨hq, hr⟩ := hdiv_exact 1074 (by omega)
        have hksub : 1074 - k = 0 := by omega
        rw [hq, hr, hksub, Nat.pow_zero, Nat.mul_one]
        have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
        rw [hacc]
        have he1074 : Int.negSucc e' = -1074 := h1074
        rw [he1074]
        exact roundWithAccuracy_binary64_pos_exact m (-1074) (Or.inl ⟨rfl, hm0, hm52⟩)
      · have hlogm : m.log2 = 52 := nat_log2_eq_of_bounds hm52 hm53
        have hlogm_i : (m.log2 : Int) = 52 := by rw [hlogm]; rfl
        have hdiff_bounds : (M.log2 : Int) - ((10 ^ k).log2 : Int) - 53 = Int.negSucc e' ∨
            (M.log2 : Int) - ((10 ^ k).log2 : Int) - 53 = Int.negSucc e' - 1 := by
          omega
        rcases hdiff_bounds with hdiff | hdiff
        · have htarg : Float.Model.Format.binary64.targetExponent
              (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = Int.negSucc e' := by
            unfold Float.Model.Format.targetExponent Float.Model.totalExponent
            have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
            have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
            rw [hmb, hmin]; omega
          have hmin0 : min (0 : Int) (Int.negSucc e') = Int.negSucc e' := by omega
          rw [htarg, h00, hmin0]
          have hsh : ((0 : Int) - Int.negSucc e').toNat = k := by rw [hk_eq]; omega
          rw [hsh]
          obtain ⟨hq, hr⟩ := hdiv_exact k (by omega)
          rw [hq, hr, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
          have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
          rw [hacc]
          exact roundWithAccuracy_binary64_pos_exact m (Int.negSucc e') (Or.inr ⟨hm52, hm53, he_lo, he_hi⟩)
        · by_cases he1074 : Int.negSucc e' = -1074
          · have hk1074 : k = 1074 := by rw [hk_def]; omega
            have htarg : Float.Model.Format.binary64.targetExponent
                (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = -1074 := by
              unfold Float.Model.Format.targetExponent Float.Model.totalExponent
              have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
              have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
              rw [hmb, hmin]; omega
            have hmin0 : min (0 : Int) (-1074) = -1074 := by omega
            rw [htarg, h00, hmin0]
            have hsh : ((0 : Int) - (-1074 : Int)).toNat = 1074 := rfl
            rw [hsh]
            obtain ⟨hq, hr⟩ := hdiv_exact 1074 (by omega)
            have hksub : 1074 - k = 0 := by omega
            rw [hq, hr, hksub, Nat.pow_zero, Nat.mul_one]
            have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
            rw [hacc]
            rw [he1074]
            exact roundWithAccuracy_binary64_pos_exact m (-1074)
              (Or.inr ⟨hm52, hm53, Int.le_refl (-1074), by decide⟩)
          · have he1073 : -1073 ≤ Int.negSucc e' := by omega
            have htarg : Float.Model.Format.binary64.targetExponent
                (Float.Model.totalExponent M 0 - Float.Model.totalExponent (10 ^ k) 0) = Int.negSucc e' - 1 := by
              unfold Float.Model.Format.targetExponent Float.Model.totalExponent
              have hmb : Float.Model.Format.binary64.mantissaBits = 53 := rfl
              have hmin : Float.Model.Format.binary64.minExponent = -1074 := rfl
              rw [hmb, hmin]; omega
            have hmin0 : min (0 : Int) (Int.negSucc e' - 1) = Int.negSucc e' - 1 := by omega
            rw [htarg, h00, hmin0]
            have hsh : ((0 : Int) - (Int.negSucc e' - 1)).toNat = k + 1 := by rw [hk_eq]; omega
            rw [hsh]
            obtain ⟨hq, hr⟩ := hdiv_exact (k + 1) (by omega)
            rw [hq, hr]
            have hpow1 : k + 1 - k = 1 := by omega
            rw [hpow1, Nat.pow_one, Nat.mul_comm m 2]
            have hacc : Float.Model.UnpackedFloat.accuracyOfFraction 0 (10 ^ k) = .exact := rfl
            rw [hacc]
            exact roundWithAccuracy_binary64_pos_double m (Int.negSucc e') hm52 hm53 he1073 he_hi

private theorem fallback_toBits_eq (x : Float) (sign : Float.Model.UnpackedFloat.Sign)
    (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) :
    (Model.evalFloat (match sign with | .positive => false | .negative => true)
      (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat)
      (if 0 ≤ e2 then 0 else e2)).toBits = x.toBits := by
  obtain ⟨hvalid, hpack_bits⟩ := unpack_finite_props x sign m e2 hm hun
  have hpos := evalFloat_fallback_pos_bits m e2 hm hvalid
  cases sign with
  | positive =>
    change (Float.ofModel (Float.Model.ofScientific _ _)).toBits = x.toBits
    rw [hpos]
    exact hpack_bits
  | negative =>
    change (Float.ofModel (Float.Model.neg (Float.Model.ofScientific _ _))).toBits = x.toBits
    rw [hpos, neg_pack_finite_pos m e2 hm hvalid]
    exact hpack_bits

private theorem zero_pos_toBits_eq (x : Float) (hun : x.toModel.unpack = .zero .positive) :
    (0.0 : Float).toBits = x.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .zero .positive at hun
  unfold Float.Model.UnpackedFloat.unpack at hun
  dsimp only at hun
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun
    split at hun <;> cases hun
  · simp only [hexp1, ↓reduceIte] at hun
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.zero.injEq] at hun
        have hsign0 : Float.Model.UnpackedFloat.unpackSign (spec := Float.Model.Format.binary64) b = 0#1 := by
          unfold Float.Model.UnpackedFloat.Sign.ofBitVec at hun
          split at hun
          · assumption
          · cases hun
        have hb0 : b = 0#64 := by
          ext i hi
          simp only [Float.Model.UnpackedFloat.unpackSign, Float.Model.UnpackedFloat.unpackExponent,
            Float.Model.UnpackedFloat.unpackMantissa, Float.Model.Format.binary64] at hsign0 hexp0 hmant0
          have h1 : b.getLsbD i = false := by
            by_cases hi52 : i < 52
            · have := congrArg (fun v : BitVec 52 => v.getLsbD i) hmant0
              simpa [BitVec.getLsbD_extractLsb', hi52] using this
            · by_cases hi63 : i < 63
              · have := congrArg (fun v : BitVec 11 => v.getLsbD (i - 52)) hexp0
                have hlt : i - 52 < 11 := by omega
                have hadd : 52 + (i - 52) = i := by omega
                simpa [BitVec.getLsbD_extractLsb', hlt, hadd] using this
              · have := congrArg (fun v : BitVec 1 => v.getLsbD (i - 63)) hsign0
                have hlt : i - 63 < 1 := by omega
                have hadd : 63 + (i - 63) = i := by omega
                simpa [BitVec.getLsbD_extractLsb', hlt, hadd] using this
          simpa [BitVec.getLsbD_eq_getElem, hi] using h1
        apply congrArg UInt64.ofBitVec
        exact hb0.symm
      · simp [hmant0] at hun
    · simp [hexp0] at hun

private theorem zero_neg_toBits_eq (x : Float) (hun : x.toModel.unpack = .zero .negative) :
    (-0.0 : Float).toBits = x.toBits := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .zero .negative at hun
  unfold Float.Model.UnpackedFloat.unpack at hun
  dsimp only at hun
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hun
    split at hun <;> cases hun
  · simp only [hexp1, ↓reduceIte] at hun
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hun
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp only [hmant0, ↓reduceDIte, Float.Model.UnpackedFloat.zero.injEq] at hun
        have hb0 : Float.Model.UnpackedFloat.packedZero Float.Model.Format.binary64 .negative = b := by
          unfold Float.Model.UnpackedFloat.packedZero
          have hz11 : (0 : BitVec Float.Model.Format.binary64.exponentBits) = 0#11 := rfl
          have hz52 : (0 : BitVec Float.Model.Format.binary64.mantissaBitsWithoutImplicit) = 0#52 := rfl
          rw [← hun, hz11, hz52, ← hexp0, ← hmant0]
          exact packComponents_unpack_eq b
        have hneg0 : (-0.0 : Float).toBits = UInt64.ofBitVec (Float.Model.UnpackedFloat.packedZero Float.Model.Format.binary64 .negative) := rfl
        rw [hneg0]
        exact congrArg UInt64.ofBitVec hb0
      · simp [hmant0] at hun
    · simp [hexp0] at hun

private theorem formatFloat_spec (x : Float) :
    Model.FloatFormatSpec x (Internal.formatFloat x) := by
  unfold Internal.formatFloat Model.FloatFormatSpec
  by_cases hnan : x.isNaN = true
  · simp only [hnan, ↓reduceIte]
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte]
    by_cases hinf : (x == Float.inf) = true
    · simp only [hinf, ↓reduceIte]
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte]
      by_cases hninf : (x == -Float.inf) = true
      · simp only [hninf, ↓reduceIte]
      · simp only [hninf, Bool.false_eq_true, ↓reduceIte]
        have hnotnan : x.toModel.unpack ≠ .notANumber := by
          intro h
          apply hnan
          change x.toModel.unpack.isNaN = true
          simp [h, Float.Model.UnpackedFloat.isNaN]
        have hnotinf : x.toModel.unpack ≠ .infinity .positive := by
          intro h
          apply hinf
          change (x.toModel.unpack.beq Float.inf.toModel.unpack) = true
          simp [h, Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare,
            show Float.inf.toModel.unpack = .infinity .positive from rfl, compare]
        have hnotninf : x.toModel.unpack ≠ .infinity .negative := by
          intro h
          apply hninf
          change (x.toModel.unpack.beq (-Float.inf).toModel.unpack) = true
          simp [h, Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare,
            show (-Float.inf).toModel.unpack = .infinity .negative from rfl, compare]
        split
        · rename_i hun; exact absurd hun hnotnan
        · rename_i hun; exact absurd hun hnotinf
        · rename_i hun; exact absurd hun hnotninf
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          have hp : Model.parseFloatModel "0.0" = Except.ok (0.0 : Float) := rfl
          rw [hp]
          exact zero_pos_toBits_eq x hun
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          have hp : Model.parseFloatModel "-0.0" = Except.ok (-0.0 : Float) := rfl
          rw [hp]
          exact zero_neg_toBits_eq x hun
        · rename_i sign m e2 hm hun
          cases sign <;>
          · split
            · rename_i s hsr
              obtain ⟨hnu, hsep, y, hy, hbits⟩ := searchShortCandidate_spec hsr
              refine ⟨hnu, hsep, ?_⟩
              rw [hy]
              exact hbits
            · by_cases he : 0 ≤ e2
              · simp only [he, ↓reduceIte]
                have hMpos : 0 < m <<< e2.toNat := by
                  rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.pow_pos (by decide))
                obtain ⟨hnu, hsep, hp⟩ := renderScientific_spec _ (m <<< e2.toNat) hMpos 0
                refine ⟨hnu, hsep, ?_⟩
                rw [hp]
                have hfb := fallback_toBits_eq x _ m e2 hm hun
                simp only [he, ↓reduceIte] at hfb
                exact hfb
              · simp only [he, ↓reduceIte]
                have hMpos : 0 < m * 5 ^ (-e2).toNat := Nat.mul_pos hm (Nat.pow_pos (by decide))
                obtain ⟨hnu, hsep, hp⟩ := renderScientific_spec _ (m * 5 ^ (-e2).toNat) hMpos e2
                refine ⟨hnu, hsep, ?_⟩
                rw [hp]
                have hfb := fallback_toBits_eq x _ m e2 hm hun
                simp only [he, ↓reduceIte] at hfb
                exact hfb

private theorem eq_inf_toBits {x : Float} (s : Float.Model.UnpackedFloat.Sign)
    (h : (x.toModel.unpack.beq (.infinity s)) = true) :
    (Float.ofModel (Float.Model.pack (.infinity s))).toBits = x.toBits := by
  have hu : x.toModel.unpack = .infinity s := by
    cases s <;> cases hu' : x.toModel.unpack with
    | infinity s' =>
      cases s' <;>
        simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h <;> rfl
    | notANumber =>
      simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
    | zero s' =>
      simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
    | finite s' _ _ _ =>
      cases s' <;>
        simp [hu', Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare] at h
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  change Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b = .infinity s at hu
  unfold Float.Model.UnpackedFloat.unpack at hu
  dsimp only at hu
  by_cases hexp1 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#11
  · simp only [hexp1, ↓reduceIte] at hu
    by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
    · simp only [hmant0, ↓reduceIte, Float.Model.UnpackedFloat.infinity.injEq] at hu
      have hpack : Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 s (-1#11) 0#52 = b := by
        rw [← hu, ← hexp1, ← hmant0]
        exact packComponents_unpack_eq b
      have hinf_bits : (Float.ofModel (Float.Model.pack (.infinity s))).toBits = UInt64.ofBitVec
          (Float.Model.UnpackedFloat.packComponents Float.Model.Format.binary64 s (-1#11) 0#52) := by
        cases s <;> rfl
      rw [hinf_bits]
      exact congrArg UInt64.ofBitVec hpack
    · simp [hmant0] at hu
  · simp only [hexp1, ↓reduceIte] at hu
    by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#11
    · simp only [hexp0, ↓reduceIte] at hu
      by_cases hmant0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#52
      · simp [hmant0] at hu
      · simp [hmant0] at hu
    · simp [hexp0] at hu

private theorem formatFloat_roundTrip_one (x : Float) :
    Model.FloatFormatSpec x (Internal.formatFloat x) ∧
      match Internal.parseFloat (Internal.formatFloat x) with
      | .ok y => Model.FloatBitMatch x y ∧ Model.FloatEquiv x y
      | .error _ => False := by
  have hfmt := formatFloat_spec x
  refine ⟨hfmt, ?_⟩
  have hpf := (parseFloat_spec (Internal.formatFloat x)).1
  have hfmt' := hfmt
  unfold Model.FloatFormatSpec at hfmt'
  by_cases hnan : x.isNaN = true
  · simp only [hnan, ↓reduceIte] at hfmt'
    rw [hfmt'] at hpf ⊢
    have hp : Model.parseFloatModel "nan" = .ok Float.nan := rfl
    cases hd : Internal.parseFloat "nan" with
    | error e =>
      have heq : Model.parseFloatModel "nan" = .error e.kind := by rw [← hpf, hd]; rfl
      rw [hp] at heq; cases heq
    | ok y =>
      have heq : Model.parseFloatModel "nan" = .ok y := by rw [← hpf, hd]; rfl
      rw [hp] at heq
      rcases Except.ok.inj heq with rfl
      have hnan_y : Float.nan.isNaN = true := by decide
      exact ⟨by simp [Model.FloatBitMatch, hnan, hnan_y], Or.inl ⟨hnan, hnan_y⟩⟩
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hfmt'
    by_cases hinf : (x == Float.inf) = true
    · simp only [hinf, ↓reduceIte] at hfmt'
      rw [hfmt'] at hpf ⊢
      have hp : Model.parseFloatModel "inf" = .ok Float.inf := rfl
      cases hd : Internal.parseFloat "inf" with
      | error e =>
        have heq : Model.parseFloatModel "inf" = .error e.kind := by rw [← hpf, hd]; rfl
        rw [hp] at heq; cases heq
      | ok y =>
        have heq : Model.parseFloatModel "inf" = .ok y := by rw [← hpf, hd]; rfl
        rw [hp] at heq
        rcases Except.ok.inj heq with rfl
        have hx : Float.inf.toBits = x.toBits := by
          have hb := eq_inf_toBits .positive hinf
          change (Float.ofModel (Float.Model.pack (.infinity .positive))).toBits = x.toBits at hb
          exact hb
        exact ⟨by simp [Model.FloatBitMatch, hnan, hx], Or.inr hinf⟩
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte] at hfmt'
      by_cases hninf : (x == -Float.inf) = true
      · simp only [hninf, ↓reduceIte] at hfmt'
        rw [hfmt'] at hpf ⊢
        have hp : Model.parseFloatModel "-inf" = .ok (-Float.inf) := rfl
        cases hd : Internal.parseFloat "-inf" with
        | error e =>
          have heq : Model.parseFloatModel "-inf" = .error e.kind := by rw [← hpf, hd]; rfl
          rw [hp] at heq; cases heq
        | ok y =>
          have heq : Model.parseFloatModel "-inf" = .ok y := by rw [← hpf, hd]; rfl
          rw [hp] at heq
          rcases Except.ok.inj heq with rfl
          have hx : (-Float.inf).toBits = x.toBits := by
            have hb := eq_inf_toBits .negative hninf
            change (Float.ofModel (Float.Model.pack (.infinity .negative))).toBits = x.toBits at hb
            exact hb
          exact ⟨by simp [Model.FloatBitMatch, hnan, hx], Or.inr hninf⟩
      · simp only [hninf, Bool.false_eq_true, ↓reduceIte] at hfmt'
        rcases hfmt' with ⟨_, _, hm⟩
        cases hd : Internal.parseFloat (Internal.formatFloat x) with
        | error e =>
          have heq : Model.parseFloatModel (Internal.formatFloat x) = .error e.kind := by
            rw [← hpf, hd]; rfl
          rw [heq] at hm
          exact False.elim hm
        | ok y =>
          have heq : Model.parseFloatModel (Internal.formatFloat x) = .ok y := by
            rw [← hpf, hd]; rfl
          rw [heq] at hm
          have hbm : Model.FloatBitMatch x y := by simp [Model.FloatBitMatch, hnan, hm]
          exact ⟨hbm, Model.floatEquiv_symm (Model.floatBitMatch_implies_floatEquiv hbm)⟩

/-- Proof of `test_numparse_formatFloat_specAndRoundTrip` for `defaultApi`. -/
theorem proof_numparse_formatFloat_specAndRoundTrip :
    AllPass (test_numparse_formatFloat_specAndRoundTrip defaultApi) := by
  intro x
  have h := formatFloat_roundTrip_one x
  dsimp [test_numparse_formatFloat_specAndRoundTrip, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  refine ⟨h.1, ?_⟩
  cases hpf : Internal.parseFloat (Internal.formatFloat x) with
  | error e =>
    have h2 := h.2
    rw [hpf] at h2
    exact False.elim h2
  | ok y =>
    have h2 := h.2
    rw [hpf] at h2
    exact ⟨h2, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_formatFloat_specAndRoundTrip`. -/
theorem reach_numparse_formatFloat_specAndRoundTrip :
    CanReach (test_numparse_formatFloat_specAndRoundTrip defaultApi) :=
  ⟨0.0, proof_numparse_formatFloat_specAndRoundTrip 0.0⟩

private def pubCheckFormatPreserves (xs : List Float) : AllPassRun Unit :=
  xs.forM fun x => do
    let s := defaultApi.formatFloat x
    NondetTest.assert (FloatFormatSpec x s)
    match defaultApi.parseFloat s with
    | .ok y => NondetTest.assert (FloatBitMatch x y)
    | .error _ => NondetTest.assert False

private theorem pubCheckFormatPreserves_all (xs : List Float) :
    pubCheckFormatPreserves xs (fun _ => True) := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    have h := formatFloat_roundTrip_one x
    change ((NondetTest.assert (FloatFormatSpec x (Internal.formatFloat x)) : AllPassRun Unit)
      (fun _ => (match Internal.parseFloat (Internal.formatFloat x) with
        | .ok y => NondetTest.assert (FloatBitMatch x y)
        | .error _ => NondetTest.assert False : AllPassRun Unit)
        (fun _ => pubCheckFormatPreserves xs (fun _ => True))))
    refine ⟨h.1, ?_⟩
    cases hpf : Internal.parseFloat (Internal.formatFloat x) with
    | error e =>
      have h2 := h.2
      rw [hpf] at h2
      exact False.elim h2
    | ok y =>
      have h2 := h.2
      rw [hpf] at h2
      exact ⟨h2.1, ih⟩

/-- Proof of `test_numparse_float_formatPreservesSpecialsAndExtremes` for `defaultApi`. -/
theorem proof_numparse_float_formatPreservesSpecialsAndExtremes :
    AllPass (test_numparse_float_formatPreservesSpecialsAndExtremes defaultApi) :=
  pubCheckFormatPreserves_all _

/-- Non-vacuity `CanReach` witness for `test_numparse_float_formatPreservesSpecialsAndExtremes`. -/
theorem reach_numparse_float_formatPreservesSpecialsAndExtremes :
    CanReach (test_numparse_float_formatPreservesSpecialsAndExtremes defaultApi) :=
  proof_numparse_float_formatPreservesSpecialsAndExtremes

end LeanSwe.NumParse.Proofs

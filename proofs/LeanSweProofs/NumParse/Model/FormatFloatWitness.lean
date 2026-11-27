import Init.Data.Float.Model
import LeanSweProofs.NumParse.Model
import LeanSweProofs.NumParse.Model.FormatSciWitness

namespace LeanSwe.NumParse.Model

open Float.Model Float.Model.UnpackedFloat

/-- Pure mathematical reference float formatter satisfying `FloatFormatSpec` on every `Float`. -/
def witnessFormatFloat (x : Float) : String :=
  if x.isNaN then "nan"
  else if x == Float.inf then "inf"
  else if x == -Float.inf then "-inf"
  else
    match x.toModel.unpack with
    | .notANumber => "nan"
    | .infinity .positive => "inf"
    | .infinity .negative => "-inf"
    | .zero .positive => "0.0"
    | .zero .negative => "-0.0"
    | .finite sign m e2 _ =>
      let neg := match sign with | .positive => false | .negative => true
      let mant := if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat
      let exp10 := if 0 ≤ e2 then 0 else e2
      renderScientificModel neg mant exp10

private abbrev FiniteBoundsModel (m : Nat) (e2 : Int) : Prop :=
  (e2 = -1074 ∧ 0 < m ∧ m < 2 ^ 52) ∨ (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e2 ∧ e2 ≤ 971)

private theorem nat_log2_mul_pow2_model (a s : Nat) (ha : 0 < a) : (a * 2 ^ s).log2 = a.log2 + s := by
  have hp : 0 < 2 ^ s := Nat.pow_pos (by decide)
  exact (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.mul_pos ha hp))).mpr
    ⟨by rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.log2_self_le (by omega)),
     by rw [Nat.add_right_comm, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self hp⟩

private theorem nat_log2_mul_bounds_model (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a.log2 + b.log2 ≤ (a * b).log2 ∧ (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  have hab : a * b ≠ 0 := Nat.ne_of_gt (Nat.mul_pos ha hb)
  have hlo : 2 ^ (a.log2 + b.log2) ≤ a * b := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul (Nat.log2_self_le (by omega)) (Nat.log2_self_le (by omega))
  have hhi : a * b < 2 ^ (a.log2 + b.log2 + 2) := by
    have h1 := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right b (Nat.le_of_lt (Nat.lt_log2_self (n := a))))
      (Nat.mul_lt_mul_of_pos_left (Nat.lt_log2_self (n := b)) (Nat.pow_pos (by decide)))
    simpa [← Nat.pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  exact ⟨(Nat.le_log2 hab).mpr hlo, by have := (Nat.log2_lt hab).mpr hhi; omega⟩

private theorem extendedMantissa_shift_exact_mul_pow2_model (m s : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ s) .exact >>> s) = ⟨m, false, false⟩ := by
  induction s generalizing m with
  | zero => simp [ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    have hm2 : m * 2 ^ (k + 1) = (m * 2) * 2 ^ k := by rw [Nat.pow_succ', ← Nat.mul_assoc]
    change ExtendedMantissa.shiftRightOne
      (ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ (k + 1)) .exact >>> k) = ⟨m, false, false⟩
    rw [hm2, ih (m * 2)]; simp [ExtendedMantissa.shiftRightOne]

private theorem shiftToTargetExponent_exact_model (m : Nat) (e2 : Int)
    (htarg : Format.binary64.targetExponent (totalExponent m e2) = e2) :
    shiftToTargetExponent Format.binary64 m e2 .exact = (⟨m, false, false⟩, e2) := by
  unfold shiftToTargetExponent shiftToExponent
  rw [htarg]; dsimp only; rw [show (e2 - e2).toNat = 0 by omega]
  simp [ExtendedMantissa.ofMantissaAndAccuracy, HShiftRight.hShiftRight, Nat.repeat]

private theorem roundWithAccuracy_binary64_shift_model (m : Nat) (e2 : Int) (s : Nat) (hm : 0 < m)
    (ht1 : Format.binary64.targetExponent (totalExponent (m * 2 ^ s) (e2 - s)) = e2)
    (ht2 : Format.binary64.targetExponent (totalExponent m e2) = e2) :
    roundWithAccuracy Format.binary64 .positive (m * 2 ^ s) (e2 - s) .exact =
      .finite .positive m e2 hm := by
  have hsh : shiftToTargetExponent Format.binary64 (m * 2 ^ s) (e2 - s) .exact = (⟨m, false, false⟩, e2) := by
    unfold shiftToTargetExponent shiftToExponent
    rw [ht1]; dsimp only
    rw [show (e2 - (e2 - s)).toNat = s by omega, extendedMantissa_shift_exact_mul_pow2_model]
    exact Prod.ext rfl (by omega)
  unfold roundWithAccuracy; rw [hsh]; dsimp only
  simp only [shiftToTargetExponent_exact_model m e2 ht2, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, show m ≠ 0 by omega, ↓reduceDIte]

private theorem packComponents_unpack_eq_model (b : BitVec 64) :
    packComponents Format.binary64
      (Sign.ofBitVec (unpackSign (spec := Format.binary64) b))
      (unpackExponent (spec := Format.binary64) b)
      (unpackMantissa (spec := Format.binary64) b) = b := by
  let sv := unpackSign (spec := Format.binary64) b
  have hsign : (Sign.ofBitVec sv).toBitVec = sv :=
    (by decide : ∀ x : BitVec 1, (Sign.ofBitVec x).toBitVec = x) sv
  rw [packComponents, hsign]
  ext i hi
  rw [show 1 + Format.binary64.exponentBits + Format.binary64.mantissaBitsWithoutImplicit = 64 from rfl] at hi
  simp only [sv, unpackSign, unpackExponent, unpackMantissa, Format.binary64,
    BitVec.getElem_append, BitVec.getElem_extractLsb']
  have hget : ∀ j (hj : j < 64), b.getLsbD j = b[j] := fun _ hj => BitVec.getLsbD_eq_getElem hj
  by_cases h52 : i < 52
  · simp only [h52, ↓reduceDIte]; rw [hget _ (by omega)]; congr 1; omega
  · by_cases h63 : i < 63
    · have h11 : i - 52 < 11 := by omega
      simp only [h52, ↓reduceDIte, h11]; rw [hget _ (by omega)]; congr 1; omega
    · have hn11 : ¬(i - 52 < 11) := by omega
      simp only [h52, ↓reduceDIte, hn11]; rw [hget _ (by omega)]; congr 1; omega

private theorem unpackSign_packComponents_model {sign : Sign} {exponent : BitVec 11} {mantissa : BitVec 52} :
    unpackSign (spec := Format.binary64) (packComponents Format.binary64 sign exponent mantissa) =
      sign.toBitVec := by
  ext i hi; have hi0 : i = 0 := by omega
  subst hi0
  simp only [unpackSign, packComponents, Format.binary64, BitVec.getElem_extractLsb']
  change (sign.toBitVec ++ exponent ++ mantissa).getLsbD 63 = sign.toBitVec[0]
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_append]
  split
  · omega
  · rw [BitVec.getElem_append]
    split
    · omega
    · rfl

private theorem pack_unpack_eq_self_model (b : BitVec 64)
    (hnn : UnpackedFloat.unpack Format.binary64 b ≠ .notANumber) :
    UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 b) = b := by
  have hre := packComponents_unpack_eq_model b
  unfold UnpackedFloat.unpack at hnn ⊢; dsimp only at hnn ⊢
  by_cases he1 : unpackExponent (spec := Format.binary64) b = -1#11
  · simp only [he1, ↓reduceIte] at hnn ⊢
    by_cases hm0 : unpackMantissa (spec := Format.binary64) b = 0#52
    · simp only [hm0, ↓reduceIte, UnpackedFloat.pack, packedInfinity]
      rw [show (0 : BitVec Format.binary64.mantissaBitsWithoutImplicit) = 0#52 from rfl, ← he1, ← hm0]; exact hre
    · simp [hm0] at hnn
  · simp only [he1, ↓reduceIte] at hnn ⊢
    by_cases he0 : unpackExponent (spec := Format.binary64) b = 0#11
    · simp only [he0, ↓reduceIte] at hnn ⊢
      by_cases hm0 : unpackMantissa (spec := Format.binary64) b = 0#52
      · simp only [hm0, ↓reduceDIte, UnpackedFloat.pack, packedZero]
        rw [show (0 : BitVec Format.binary64.exponentBits) = 0#11 from rfl,
            show (0 : BitVec Format.binary64.mantissaBitsWithoutImplicit) = 0#52 from rfl, ← he0, ← hm0]; exact hre
      · simp only [hm0, ↓reduceDIte, UnpackedFloat.pack]
        have hm52 : (unpackMantissa (spec := Format.binary64) b).toNat < 2 ^ 52 := (unpackMantissa _).isLt
        have hloglt : (unpackMantissa (spec := Format.binary64) b).toNat.log2 < 52 :=
          (Nat.log2_lt fun hz => hm0 (BitVec.eq_of_toNat_eq hz)).mpr hm52
        have hbiased : ((0#11 : BitVec 11).toNat -
            (Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit) + 1 +
            Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit : Int).toNat = 1 := rfl
        have hmbv : BitVec.ofNat 52 (unpackMantissa (spec := Format.binary64) b).toNat =
            unpackMantissa (spec := Format.binary64) b := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt hm52)
        have hc1 : ¬(2 ^ Format.binary64.exponentBits ≤ 1 + 1) := by decide
        have hc2 : ¬((unpackMantissa (spec := Format.binary64) b).toNat.log2 + 1 = Format.binary64.mantissaBits) := by
          change ¬(_ + 1 = 53); omega
        simp only [hbiased, hc1, ↓reduceIte, hc2, hmbv]; rw [← he0]; exact hre
    · simp only [he0, ↓reduceIte, UnpackedFloat.pack]
      have h52 : (unpackMantissa (spec := Format.binary64) b).toNat < 2 ^ 52 := (unpackMantissa _).isLt
      have hexp_lt : (unpackExponent (spec := Format.binary64) b).toNat < 2047 := by
        have : (unpackExponent (spec := Format.binary64) b).toNat < 2048 := (unpackExponent _).isLt
        have : (unpackExponent (spec := Format.binary64) b).toNat ≠ 2047 := fun h => he1 (BitVec.eq_of_toNat_eq h)
        omega
      have hm_val : (1#1 ++ unpackMantissa (spec := Format.binary64) b).toNat =
          2 ^ 52 + (unpackMantissa (spec := Format.binary64) b).toNat := by rw [BitVec.toNat_append_eq_mul_add]; rfl
      have hlog : (1#1 ++ unpackMantissa (spec := Format.binary64) b).toNat.log2 = 52 :=
        (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
      have hbiased : (((unpackExponent (spec := Format.binary64) b).toNat : Int) -
          (Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit) +
          Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat =
          (unpackExponent (spec := Format.binary64) b).toNat := by omega
      have hc1 : ¬(2 ^ Format.binary64.exponentBits ≤ (unpackExponent (spec := Format.binary64) b).toNat + 1) := by
        change ¬(2048 ≤ _ + 1); omega
      have hc2 : (1#1 ++ unpackMantissa (spec := Format.binary64) b).toNat.log2 + 1 = Format.binary64.mantissaBits := by
        rw [hlog]; rfl
      have hebv : BitVec.ofNat 11 (unpackExponent (spec := Format.binary64) b).toNat =
          unpackExponent (spec := Format.binary64) b :=
        BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (unpackExponent (spec := Format.binary64) b).isLt)
      have hmbv : BitVec.ofNat 52 (1#1 ++ unpackMantissa (spec := Format.binary64) b).toNat =
          unpackMantissa (spec := Format.binary64) b :=
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, hm_val, Nat.add_mod_left, Nat.mod_eq_of_lt h52])
      simp only [hbiased, hc1, ↓reduceIte, hc2, hebv, hmbv]; exact hre

private theorem pack_unpack_toBits_model {x : Float} {u : UnpackedFloat}
    (hun : x.toModel.unpack = u) (hnn : u ≠ .notANumber) : (Float.Model.pack u).toBits = x.toBits := by
  have hb := pack_unpack_eq_self_model x.toModel.toBits.toBitVec (by rw [← hun] at hnn; exact hnn)
  rw [show UnpackedFloat.unpack Format.binary64 x.toModel.toBits.toBitVec = u from hun] at hb
  exact congrArg UInt64.ofBitVec hb

private theorem unpack_finite_valid_model (x : Float) (sign : Sign) (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) : FiniteBoundsModel m e2 := by
  let b : BitVec 64 := x.toModel.toBits.toBitVec
  have hun_def : UnpackedFloat.unpack Format.binary64 b = .finite sign m e2 hm := hun
  unfold UnpackedFloat.unpack at hun_def; dsimp only at hun_def
  by_cases he1 : unpackExponent (spec := Format.binary64) b = -1#11
  · simp only [he1, ↓reduceIte] at hun_def; split at hun_def <;> cases hun_def
  · simp only [he1, ↓reduceIte] at hun_def
    by_cases he0 : unpackExponent (spec := Format.binary64) b = 0#11
    · simp only [he0, ↓reduceIte] at hun_def
      by_cases hm0 : unpackMantissa (spec := Format.binary64) b = 0#52
      · simp [hm0] at hun_def
      · simp only [hm0, ↓reduceDIte, UnpackedFloat.finite.injEq] at hun_def
        rcases hun_def with ⟨rfl, rfl, rfl⟩; exact Or.inl ⟨rfl, hm, (unpackMantissa _).isLt⟩
    · simp only [he0, ↓reduceIte, UnpackedFloat.finite.injEq] at hun_def
      rcases hun_def with ⟨rfl, rfl, rfl⟩
      have hexp_lt : (unpackExponent (spec := Format.binary64) b).toNat < 2047 := by
        have : (unpackExponent (spec := Format.binary64) b).toNat < 2048 := (unpackExponent _).isLt
        have : (unpackExponent (spec := Format.binary64) b).toNat ≠ 2047 := fun h => he1 (BitVec.eq_of_toNat_eq h)
        omega
      have hexp_pos : 0 < (unpackExponent (spec := Format.binary64) b).toNat :=
        Nat.pos_of_ne_zero fun h => he0 (BitVec.eq_of_toNat_eq h)
      have hm_val : (1#1 ++ unpackMantissa (spec := Format.binary64) b).toNat =
          2 ^ 52 + (unpackMantissa (spec := Format.binary64) b).toNat := by rw [BitVec.toNat_append_eq_mul_add]; rfl
      have h52 : (unpackMantissa (spec := Format.binary64) b).toNat < 2 ^ 52 := (unpackMantissa _).isLt
      change _ ∨ (2 ^ 52 ≤ _ ∧ _ < 2 ^ 53 ∧
        -1074 ≤ ((unpackExponent (spec := Format.binary64) b).toNat : Int) - 1075 ∧
        ((unpackExponent (spec := Format.binary64) b).toNat : Int) - 1075 ≤ 971)
      exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

private theorem neg_pack_finite_pos_model (m : Nat) (e2 : Int) (hm : 0 < m) (hvalid : FiniteBoundsModel m e2) :
    Float.Model.neg (Float.Model.pack (.finite .positive m e2 hm)) =
      Float.Model.pack (.finite .negative m e2 hm) := by
  have hunpack : (Float.Model.pack (.finite .positive m e2 hm)).unpack = .finite .positive m e2 hm := by
    unfold Float.Model.unpack Float.Model.pack UnpackedFloat.pack; dsimp only
    rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
    · have hloglt : m.log2 < 52 := (Nat.log2_lt (by omega)).mpr hm52
      have hc1 : ¬(2 ^ Format.binary64.exponentBits ≤ 1 + 1) := by decide
      have hc2 : ¬(m.log2 + 1 = Format.binary64.mantissaBits) := by change ¬(m.log2 + 1 = 53); omega
      simp only [show ((-1074 : Int) + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat = 1 from rfl, hc1, ↓reduceIte, hc2]
      unfold UnpackedFloat.unpack
      simp only [unpackExponent_packComponents, unpackMantissa_packComponents, unpackSign_packComponents_model]
      have hmne : (BitVec.ofNat 52 m) ≠ 0#52 := fun h => by
        have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt hm52] at this; omega
      simp only [show (0#11 : BitVec 11) ≠ -1#11 by decide, ↓reduceIte, hmne, ↓reduceDIte, UnpackedFloat.finite.injEq]
      exact ⟨rfl, Nat.mod_eq_of_lt hm52, rfl⟩
    · have hlog : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm52, hm53⟩
      have hbiased : (e2 + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat =
          (e2 + 1075).toNat := by rw [Int.add_assoc]; rfl
      have hc1 : ¬(2 ^ Format.binary64.exponentBits ≤ (e2 + 1075).toNat + 1) := by change ¬(2048 ≤ _ + 1); omega
      simp only [hbiased, hc1, ↓reduceIte, show m.log2 + 1 = Format.binary64.mantissaBits by rw [hlog]; rfl]
      unfold UnpackedFloat.unpack
      simp only [unpackExponent_packComponents, unpackMantissa_packComponents, unpackSign_packComponents_model]
      have hmodE : (BitVec.ofNat 11 (e2 + 1075).toNat).toNat = (e2 + 1075).toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hne1 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ -1#11 := fun h => by
        have := congrArg BitVec.toNat h; rw [hmodE] at this; change (e2 + 1075).toNat = 2047 at this; omega
      have hne0 : BitVec.ofNat 11 (e2 + 1075).toNat ≠ 0#11 := fun h => by
        have := congrArg BitVec.toNat h; rw [hmodE] at this; change (e2 + 1075).toNat = 0 at this; omega
      simp only [hne1, ↓reduceIte, hne0, UnpackedFloat.finite.injEq]
      refine ⟨rfl, ?_, by rw [hmodE]; change ((e2 + 1075).toNat : Int) - 1075 = e2; omega⟩
      have hmod52 : (BitVec.ofNat 52 m).toNat = m - 2 ^ 52 := by
        simp only [BitVec.toNat_ofNat]
        have hmod := Nat.add_mod_left (2 ^ 52) (m - 2 ^ 52)
        rw [Nat.add_sub_cancel' hm52] at hmod; rw [hmod, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_append_eq_mul_add, hmod52]; change 1 * 2 ^ 52 + (m - 2 ^ 52) = m; omega
  unfold Float.Model.neg; rw [hunpack]; rfl

private theorem valid_target_eq_model (m : Nat) (e2 : Int) (hvalid : FiniteBoundsModel m e2) :
    Format.binary64.targetExponent (totalExponent m e2) = e2 := by
  unfold Format.targetExponent totalExponent
  rw [show Format.binary64.mantissaBits = 53 from rfl, show Format.binary64.minExponent = -1074 from rfl]
  rcases hvalid with ⟨rfl, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
  · have : m.log2 < 52 := (Nat.log2_lt (by omega)).mpr hm52; omega
  · have : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm52, hm53⟩; omega

private theorem evalFloat_fallback_pos_bits_model (m : Nat) (e2 : Int) (hm : 0 < m)
    (hvalid : FiniteBoundsModel m e2) :
    Float.Model.ofScientific (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat) (if 0 ≤ e2 then 0 else e2) =
      Float.Model.pack (.finite .positive m e2 hm) := by
  unfold Float.Model.ofScientific; congr 1
  have ht2 := valid_target_eq_model m e2 hvalid
  have hmb : Format.binary64.mantissaBits = 53 := rfl
  have hmin : Format.binary64.minExponent = -1074 := rfl
  have hexpb : (2 ^ Format.binary64.exponentBits : Int) = 2048 := rfl
  by_cases he : 0 ≤ e2
  · cases e2 with
    | negSucc _ => exact absurd he (by omega)
    | ofNat n =>
      rcases hvalid with ⟨h0, _⟩ | ⟨hm52, hm53, _, hehi⟩
      · exact absurd h0 (by omega)
      simp only [he, ↓reduceIte, show (Int.ofNat n).toNat = n from rfl]
      have hM : m <<< n = m * 2 ^ n := Nat.shiftLeft_eq m n
      have hMne : m <<< n ≠ 0 := by rw [hM]; exact Nat.ne_of_gt (Nat.mul_pos hm (Nat.pow_pos (by decide)))
      unfold UnpackedFloat.ofScientific; dsimp only
      have hno1 : ¬((0 : Int) > 2 ^ Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬((0 : Int) < -((2 ^ Format.binary64.exponentBits : Int) + (m <<< n).log2)) := by
        have := Int.natCast_nonneg (m <<< n).log2; rw [hexpb]; omega
      simp only [hMne, ↓reduceDIte, hno1, hno2, Int.le_refl (0 : Int), ↓reduceIte]
      unfold UnpackedFloat.mul; dsimp only
      have hmul_val : ((m <<< n) <<< Format.binary64.mantissaBits) * 10 ^ (0 : Int).toNat = m * 2 ^ (n + 53) := by
        rw [show (0 : Int).toNat = 0 from rfl, Nat.pow_zero, Nat.mul_one, hmb, hM,
            Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add]
      have hexp : (-(Format.binary64.mantissaBits : Int) + 0) = Int.ofNat n - ((n + 53 : Nat) : Int) := by
        rw [hmb]; change (-53 : Int) = (n : Int) - ((n + 53 : Nat) : Int); omega
      have hlogm : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm52, hm53⟩
      rw [hmul_val, hexp]
      exact roundWithAccuracy_binary64_shift_model m (Int.ofNat n) (n + 53) hm
        (by unfold Format.targetExponent totalExponent; rw [nat_log2_mul_pow2_model m (n + 53) hm, hlogm, hmb, hmin]; omega) ht2
  · cases e2 with
    | ofNat n => exact absurd (Int.natCast_nonneg n) he
    | negSucc e' =>
      simp only [he, ↓reduceIte]
      let k := (-Int.negSucc e').toNat
      have hk_def : k = e' + 1 := rfl
      have hk_int : (k : Int) = -(Int.negSucc e') := by omega
      have hk_le : k ≤ 1074 := by rcases hvalid with ⟨h0, _⟩ | ⟨_, _, he_lo, _⟩ <;> omega
      let M := m * 5 ^ k
      have h5pos : 0 < 5 ^ k := Nat.pow_pos (by decide)
      have hMne : m * 5 ^ (-Int.negSucc e').toNat ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hm h5pos)
      unfold UnpackedFloat.ofScientific; dsimp only
      have hno1 : ¬(Int.negSucc e' > 2 ^ Format.binary64.exponentBits) := by rw [hexpb]; omega
      have hno2 : ¬(Int.negSucc e' < -(2 ^ 11 + ↑(m * 5 ^ (-Int.negSucc e').toNat).log2)) := by
        have := Int.natCast_nonneg (m * 5 ^ (-Int.negSucc e').toNat).log2; omega
      simp only [hMne, ↓reduceDIte, hno1, hno2, he, ↓reduceIte]
      unfold UnpackedFloat.div divCore; dsimp only
      have h10_eq : 10 ^ k = 5 ^ k * 2 ^ k := by rw [← Nat.mul_pow]
      have hlog10_i : ((10 ^ k).log2 : Int) = ((5 ^ k).log2 : Int) + (k : Int) := by
        have h := congrArg Int.ofNat (by rw [h10_eq, nat_log2_mul_pow2_model _ k h5pos] : (10 ^ k).log2 = (5 ^ k).log2 + k)
        push_cast at h; exact h
      obtain ⟨hM_lo, hM_hi⟩ := nat_log2_mul_bounds_model m (5 ^ k) hm h5pos
      have hM_lo_i : (m.log2 : Int) + ((5 ^ k).log2 : Int) ≤ (M.log2 : Int) := by
        have h := Int.ofNat_le.mpr hM_lo; push_cast at h; exact h
      have hM_hi_i : (M.log2 : Int) ≤ (m.log2 : Int) + ((5 ^ k).log2 : Int) + 1 := by
        have h := Int.ofNat_le.mpr hM_hi; push_cast at h; exact h
      have hstep : ∀ (t : Int) (s : Nat),
          Format.binary64.targetExponent (totalExponent M 0 - totalExponent (10 ^ k) 0) = t →
          t = Int.negSucc e' - s → t ≤ 0 →
          Format.binary64.targetExponent (totalExponent (m * 2 ^ s) (Int.negSucc e' - s)) = Int.negSucc e' →
          roundWithAccuracy Format.binary64 (Sign.positive / Sign.positive)
            ((M <<< ((0 : Int) - 0 - min ((0 : Int) - 0) (Format.binary64.targetExponent
              (totalExponent M 0 - totalExponent (10 ^ k) 0))).toNat) / 10 ^ k)
            (min ((0 : Int) - 0) (Format.binary64.targetExponent (totalExponent M 0 - totalExponent (10 ^ k) 0)))
            (accuracyOfFraction ((M <<< ((0 : Int) - 0 - min ((0 : Int) - 0) (Format.binary64.targetExponent
              (totalExponent M 0 - totalExponent (10 ^ k) 0))).toNat) % 10 ^ k) (10 ^ k)) =
            .finite .positive m (Int.negSucc e') hm := by
        intro t s ht hte htle ht1
        rw [ht, show min ((0 : Int) - 0) t = t by omega, show ((0 : Int) - 0 - t).toNat = k + s by omega]
        have hmul : M <<< (k + s) = (m * 2 ^ s) * 10 ^ k := by
          rw [Nat.shiftLeft_eq]; dsimp only [M]; rw [Nat.pow_add, h10_eq]
          rw [Nat.mul_assoc m (5 ^ k), ← Nat.mul_assoc (5 ^ k) (2 ^ k), Nat.mul_comm (5 ^ k * 2 ^ k), ← Nat.mul_assoc]
        rw [hmul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide : 0 < 10)), Nat.mul_mod_left, hte]
        exact roundWithAccuracy_binary64_shift_model m (Int.negSucc e') s hm ht1 ht2
      rcases hvalid with ⟨h1074, hm0, hm52⟩ | ⟨hm52, hm53, he_lo, he_hi⟩
      · have hmlt : (m.log2 : Int) < 52 := Int.ofNat_lt.mpr ((Nat.log2_lt (by omega)).mpr hm52)
        refine hstep (-1074) 0 ?_ (by omega) (by omega) (by simpa using ht2)
        unfold Format.targetExponent totalExponent; rw [hmb, hmin]; omega
      · have hlogm : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨hm52, hm53⟩
        have hlogm_i : (m.log2 : Int) = 52 := by rw [hlogm]; rfl
        by_cases hd : (M.log2 : Int) - ((10 ^ k).log2 : Int) - 53 = Int.negSucc e'
        · refine hstep (Int.negSucc e') 0 ?_ (by omega) (by omega) (by simpa using ht2)
          unfold Format.targetExponent totalExponent; rw [hmb, hmin]; omega
        · by_cases he1074 : Int.negSucc e' = -1074
          · refine hstep (-1074) 0 ?_ (by omega) (by omega) (by simpa using ht2)
            unfold Format.targetExponent totalExponent; rw [hmb, hmin]; omega
          · refine hstep (Int.negSucc e' - 1) 1 ?_ (by omega) (by omega) ?_
            · unfold Format.targetExponent totalExponent; rw [hmb, hmin]; omega
            · unfold Format.targetExponent totalExponent; rw [hmb, hmin, nat_log2_mul_pow2_model m 1 hm, hlogm]; omega

private theorem fallback_toBits_eq_model (x : Float) (sign : Sign) (m : Nat) (e2 : Int) (hm : 0 < m)
    (hun : x.toModel.unpack = .finite sign m e2 hm) :
    (evalFloat (match sign with | .positive => false | .negative => true)
      (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat)
      (if 0 ≤ e2 then 0 else e2)).toBits = x.toBits := by
  have hvalid := unpack_finite_valid_model x sign m e2 hm hun
  have hpack := pack_unpack_toBits_model hun (by simp)
  have hpos := evalFloat_fallback_pos_bits_model m e2 hm hvalid
  cases sign with
  | positive => change (Float.ofModel (Float.Model.ofScientific _ _)).toBits = x.toBits; rw [hpos]; exact hpack
  | negative =>
    change (Float.ofModel (Float.Model.neg (Float.Model.ofScientific _ _))).toBits = x.toBits
    rw [hpos, neg_pack_finite_pos_model m e2 hm hvalid]; exact hpack

/-- `witnessFormatFloat` satisfies `FloatFormatSpec` on every `Float`. -/
theorem floatFormatSpec_witnessFormatFloat (x : Float) :
    FloatFormatSpec x (witnessFormatFloat x) := by
  unfold witnessFormatFloat FloatFormatSpec
  by_cases hnan : x.isNaN = true
  · simp only [hnan, ↓reduceIte]
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte]
    by_cases hinf : (x == Float.inf) = true
    · simp only [hinf, ↓reduceIte]
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte]
      by_cases hninf : (x == -Float.inf) = true
      · simp only [hninf, ↓reduceIte]
      · simp only [hninf, Bool.false_eq_true, ↓reduceIte]
        split
        · rename_i hun; exact absurd (by change x.toModel.unpack.isNaN = true; simp [hun, UnpackedFloat.isNaN]) hnan
        · rename_i hun
          exact absurd (by change x.toModel.unpack.beq Float.inf.toModel.unpack = true
                           simp [hun, UnpackedFloat.beq, UnpackedFloat.compare, show Float.inf.toModel.unpack = .infinity .positive from rfl, compare]) hinf
        · rename_i hun
          exact absurd (by change x.toModel.unpack.beq (-Float.inf).toModel.unpack = true
                           simp [hun, UnpackedFloat.beq, UnpackedFloat.compare, show (-Float.inf).toModel.unpack = .infinity .negative from rfl, compare]) hninf
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          rw [show parseFloatModel "0.0" = .ok (0.0 : Float) from rfl]
          exact show (Float.Model.pack (.zero .positive)).toBits = x.toBits from pack_unpack_toBits_model hun (by simp)
        · rename_i hun
          refine ⟨by simp [String.contains_char_eq], Or.inl (by simp [String.contains_char_eq]), ?_⟩
          rw [show parseFloatModel "-0.0" = .ok (-0.0 : Float) from rfl]
          exact show (Float.Model.pack (.zero .negative)).toBits = x.toBits from pack_unpack_toBits_model hun (by simp)
        · rename_i sign m e2 hm hun
          cases sign <;>
          · have hpos : 0 < (if 0 ≤ e2 then m <<< e2.toNat else m * 5 ^ (-e2).toNat) := by
              split
              · rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.pow_pos (by decide))
              · exact Nat.mul_pos hm (Nat.pow_pos (by decide))
            obtain ⟨hnu, hsep, hp⟩ := renderScientificModel_spec _ _ hpos (if 0 ≤ e2 then 0 else e2)
            have hfb := fallback_toBits_eq_model x _ m e2 hm hun
            by_cases he : 0 ≤ e2 <;> simp only [he, ↓reduceIte] at hnu hsep hp hfb ⊢ <;>
              exact ⟨hnu, hsep, by rw [hp]; exact hfb⟩

end LeanSwe.NumParse.Model

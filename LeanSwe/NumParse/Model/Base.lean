import Init.Data.Float.Model
import LeanSwe.NumParse.Types

namespace LeanSwe.NumParse.Model

open Float.Model

/-- IEEE-754 numeric equivalence extended to a true equivalence relation (`NaN ≈ NaN` and `+0.0 ≈ -0.0`). -/
def FloatEquiv (a b : Float) : Prop :=
  (a.isNaN = true ∧ b.isNaN = true) ∨ (a == b) = true

private theorem unpacked_isNaN_iff (u : UnpackedFloat) :
    u.isNaN = true ↔ u = .notANumber := by
  cases u <;> simp [UnpackedFloat.isNaN]

private theorem int_compare_eq_iff (a b : Int) : compare a b = .eq ↔ a = b := by
  simp only [compare, compareOfLessAndEq]
  split
  · simp_all; omega
  · split
    · simp_all
    · simp_all

private theorem nat_compare_eq_iff (a b : Nat) : compare a b = .eq ↔ a = b := by
  simp only [compare, compareOfLessAndEq]
  split
  · simp_all; omega
  · split
    · simp_all
    · simp_all

private theorem unpacked_compare_eq_some_eq_iff (u v : UnpackedFloat) :
    u.compare v = some .eq ↔
      (u ≠ .notANumber ∧ v ≠ .notANumber ∧
        ((∃ s₁ s₂, u = .zero s₁ ∧ v = .zero s₂) ∨ u = v)) := by
  cases u with
  | notANumber => simp [UnpackedFloat.compare]
  | infinity s₁ =>
    cases v with
    | notANumber => simp [UnpackedFloat.compare]
    | infinity s₂ =>
      cases s₁ <;> cases s₂ <;> simp [UnpackedFloat.compare, compare]
    | zero s₂ => cases s₁ <;> simp [UnpackedFloat.compare]
    | finite s₂ m₂ e₂ hm₂ => cases s₁ <;> simp [UnpackedFloat.compare]
  | zero s₁ =>
    cases v with
    | notANumber => simp [UnpackedFloat.compare]
    | infinity s₂ => cases s₂ <;> simp [UnpackedFloat.compare]
    | zero s₂ => simp [UnpackedFloat.compare]
    | finite s₂ m₂ e₂ hm₂ => cases s₂ <;> simp [UnpackedFloat.compare]
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | notANumber => simp [UnpackedFloat.compare]
    | infinity s₂ => cases s₁ <;> cases s₂ <;> simp [UnpackedFloat.compare]
    | zero s₂ => cases s₁ <;> simp [UnpackedFloat.compare]
    | finite s₂ m₂ e₂ hm₂ =>
      cases s₁ <;> cases s₂
      · simp only [UnpackedFloat.compare, Option.some.injEq, ne_eq, reduceCtorEq, not_false_eq_true,
          true_and, UnpackedFloat.finite.injEq]
        constructor
        · intro h
          cases hc : compare e₁ e₂ <;> cases hm : compare m₁ m₂ <;>
            simp [hc, hm, Ordering.then, Ordering.swap] at h
          exact Or.inr ⟨(nat_compare_eq_iff m₁ m₂).mp hm, (int_compare_eq_iff e₁ e₂).mp hc⟩
        · rintro (⟨_, _, ⟨⟩, _⟩ | ⟨rfl, rfl⟩)
          simp [Ordering.then, Ordering.swap]
      · simp [UnpackedFloat.compare]
      · simp [UnpackedFloat.compare]
      · simp only [UnpackedFloat.compare, Option.some.injEq, ne_eq, reduceCtorEq, not_false_eq_true,
          true_and, UnpackedFloat.finite.injEq]
        constructor
        · intro h
          cases hc : compare e₁ e₂ <;> cases hm : compare m₁ m₂ <;>
            simp [hc, hm, Ordering.then] at h
          exact Or.inr ⟨(nat_compare_eq_iff m₁ m₂).mp hm, (int_compare_eq_iff e₁ e₂).mp hc⟩
        · rintro (⟨_, _, ⟨⟩, _⟩ | ⟨rfl, rfl⟩)
          simp [Ordering.then]

/-- Reflexivity of `FloatEquiv`. -/
theorem floatEquiv_refl (a : Float) : FloatEquiv a a := by
  unfold FloatEquiv
  change (a.toModel.unpack.isNaN = true ∧ a.toModel.unpack.isNaN = true) ∨
    (a.toModel.unpack.beq a.toModel.unpack) = true
  by_cases h : a.toModel.unpack = .notANumber
  · left; simp [h, UnpackedFloat.isNaN]
  · right
    simp only [UnpackedFloat.beq, beq_iff_eq]
    exact (unpacked_compare_eq_some_eq_iff _ _).mpr ⟨h, h, Or.inr rfl⟩

/-- Symmetry of `FloatEquiv`. -/
theorem floatEquiv_symm {a b : Float} (hab : FloatEquiv a b) : FloatEquiv b a := by
  rcases hab with ⟨ha, hb⟩ | hbeq
  · exact Or.inl ⟨hb, ha⟩
  · right
    change (b.toModel.unpack.beq a.toModel.unpack) = true
    change (a.toModel.unpack.beq b.toModel.unpack) = true at hbeq
    simp only [UnpackedFloat.beq, beq_iff_eq] at hbeq ⊢
    obtain ⟨ha, hb, hrel⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hbeq
    refine (unpacked_compare_eq_some_eq_iff _ _).mpr ⟨hb, ha, ?_⟩
    rcases hrel with ⟨s₁, s₂, h1, h2⟩ | heq
    · exact Or.inl ⟨s₂, s₁, h2, h1⟩
    · exact Or.inr heq.symm

/-- Transitivity of `FloatEquiv`. -/
theorem floatEquiv_trans {a b c : Float} (hab : FloatEquiv a b) (hbc : FloatEquiv b c) :
    FloatEquiv a c := by
  rcases hab with ⟨ha, hb⟩ | hab
  · rcases hbc with ⟨_, hc⟩ | hbc
    · exact Or.inl ⟨ha, hc⟩
    · change (b.toModel.unpack.beq c.toModel.unpack) = true at hbc
      simp only [UnpackedFloat.beq, beq_iff_eq] at hbc
      obtain ⟨hb', _⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hbc
      exact False.elim (hb' ((unpacked_isNaN_iff _).mp hb))
  · rcases hbc with ⟨hb, _⟩ | hbc
    · change (a.toModel.unpack.beq b.toModel.unpack) = true at hab
      simp only [UnpackedFloat.beq, beq_iff_eq] at hab
      obtain ⟨_, hb', _⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hab
      exact False.elim (hb' ((unpacked_isNaN_iff _).mp hb))
    · right
      change (a.toModel.unpack.beq c.toModel.unpack) = true
      change (a.toModel.unpack.beq b.toModel.unpack) = true at hab
      change (b.toModel.unpack.beq c.toModel.unpack) = true at hbc
      simp only [UnpackedFloat.beq, beq_iff_eq] at hab hbc ⊢
      obtain ⟨ha, _, r1⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hab
      obtain ⟨_, hc, r2⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hbc
      refine (unpacked_compare_eq_some_eq_iff _ _).mpr ⟨ha, hc, ?_⟩
      rcases r1 with ⟨s₁, s₂, ha0, hb0⟩ | heqab
      · rcases r2 with ⟨_, s₄, _, hc0⟩ | heqbc
        · exact Or.inl ⟨s₁, s₄, ha0, hc0⟩
        · exact Or.inl ⟨s₁, s₂, ha0, by rw [← heqbc]; exact hb0⟩
      · rcases r2 with ⟨s₃, s₄, hb0, hc0⟩ | heqbc
        · exact Or.inl ⟨s₃, s₄, by rw [heqab]; exact hb0, hc0⟩
        · exact Or.inr (heqab.trans heqbc)

/-- `FloatEquiv` is an equivalence relation on `Float`. -/
theorem floatEquiv_equivalence : Equivalence FloatEquiv :=
  ⟨floatEquiv_refl, @floatEquiv_symm, @floatEquiv_trans⟩

/-- Positive zero and negative zero are `FloatEquiv`. -/
theorem floatEquiv_posZero_negZero : FloatEquiv (0.0 : Float) (-0.0) := by
  right
  decide

/-- Canonical `NaN` values are `FloatEquiv`. -/
theorem floatEquiv_nan_nan : FloatEquiv Float.nan Float.nan := by
  left
  constructor <;> decide

/-- For non-NaN floats, `FloatEquiv` coincides with IEEE-754 `==`. -/
theorem floatEquiv_nonNaN_iff_beq {a b : Float}
    (ha : ¬(a.isNaN = true)) (_hb : ¬(b.isNaN = true)) :
    FloatEquiv a b ↔ (a == b) = true := by
  unfold FloatEquiv
  constructor
  · rintro (⟨ha', _⟩ | h)
    · exact False.elim (ha ha')
    · exact h
  · intro h
    exact Or.inr h

private theorem unpack_not_nan_ne_allOnes_or_zero {b : BitVec 64}
    (hn : UnpackedFloat.unpack Format.binary64 b ≠ .notANumber) :
    @UnpackedFloat.unpackExponent Format.binary64 b = (-1#_) →
      @UnpackedFloat.unpackMantissa Format.binary64 b = 0#_ := by
  unfold UnpackedFloat.unpack at hn
  intro hexp
  simp only [hexp, ↓reduceIte] at hn
  by_cases hm : @UnpackedFloat.unpackMantissa Format.binary64 b = 0#_
  · exact hm
  · simp [hm] at hn

private theorem unpackSign_inj_aux {b₁ b₂ : BitVec 64}
    (hs : UnpackedFloat.Sign.ofBitVec (@UnpackedFloat.unpackSign Format.binary64 b₁) =
      UnpackedFloat.Sign.ofBitVec (@UnpackedFloat.unpackSign Format.binary64 b₂)) :
    @UnpackedFloat.unpackSign Format.binary64 b₁ = @UnpackedFloat.unpackSign Format.binary64 b₂ :=
  (by decide : ∀ x y : BitVec 1, UnpackedFloat.Sign.ofBitVec x = UnpackedFloat.Sign.ofBitVec y → x = y)
    _ _ hs

private theorem bitVec64_ext_components {b₁ b₂ : BitVec 64}
    (hs : UnpackedFloat.Sign.ofBitVec (@UnpackedFloat.unpackSign Format.binary64 b₁) =
      UnpackedFloat.Sign.ofBitVec (@UnpackedFloat.unpackSign Format.binary64 b₂))
    (he : @UnpackedFloat.unpackExponent Format.binary64 b₁ = @UnpackedFloat.unpackExponent Format.binary64 b₂)
    (hm : @UnpackedFloat.unpackMantissa Format.binary64 b₁ = @UnpackedFloat.unpackMantissa Format.binary64 b₂) :
    b₁ = b₂ := by
  have hs' := unpackSign_inj_aux hs
  ext i hi
  by_cases h63 : i = 63
  · subst h63
    have hbit := congrArg (fun x : BitVec 1 => x[0]) hs'
    simp only [UnpackedFloat.unpackSign, BitVec.getElem_extractLsb'] at hbit
    exact hbit
  · by_cases h52 : i < 52
    · have hbit := congrArg (fun x : BitVec 52 => x[i]) hm
      simp only [UnpackedFloat.unpackMantissa, BitVec.getElem_extractLsb', Nat.zero_add] at hbit
      exact hbit
    · have hlt : i - 52 < 11 := by omega
      have hbit := congrArg (fun x : BitVec 11 => x[i - 52]) he
      simp only [UnpackedFloat.unpackExponent, BitVec.getElem_extractLsb',
        Nat.add_sub_cancel' (by omega : 52 ≤ i)] at hbit
      exact hbit

private theorem unpackExponent_inj_aux {b₁ b₂ : BitVec 64}
    (h1 : UnpackedFloat.unpack Format.binary64 b₁ = UnpackedFloat.unpack Format.binary64 b₂)
    (hn1 : UnpackedFloat.unpack Format.binary64 b₁ ≠ .notANumber) :
    b₁ = b₂ := by
  have hn2 : UnpackedFloat.unpack Format.binary64 b₂ ≠ .notANumber := by rw [← h1]; exact hn1
  unfold UnpackedFloat.unpack at h1
  dsimp only at h1
  by_cases he1 : @UnpackedFloat.unpackExponent Format.binary64 b₁ = (-1#_) <;>
    by_cases he2 : @UnpackedFloat.unpackExponent Format.binary64 b₂ = (-1#_)
  · have hm1 := unpack_not_nan_ne_allOnes_or_zero hn1 he1
    have hm2 := unpack_not_nan_ne_allOnes_or_zero hn2 he2
    simp only [he1, hm1, ↓reduceIte, he2, hm2, UnpackedFloat.infinity.injEq] at h1
    exact bitVec64_ext_components h1 (he1.trans he2.symm) (hm1.trans hm2.symm)
  · have hm1 := unpack_not_nan_ne_allOnes_or_zero hn1 he1
    simp only [he1, hm1, ↓reduceIte, he2] at h1
    by_cases hz2 : @UnpackedFloat.unpackExponent Format.binary64 b₂ = 0#_
    · by_cases hm2 : @UnpackedFloat.unpackMantissa Format.binary64 b₂ = 0#_ <;>
        simp [hz2, hm2] at h1
    · simp [hz2] at h1
  · have hm2 := unpack_not_nan_ne_allOnes_or_zero hn2 he2
    simp only [he1, he2, hm2, ↓reduceIte] at h1
    by_cases hz1 : @UnpackedFloat.unpackExponent Format.binary64 b₁ = 0#_
    · by_cases hm1 : @UnpackedFloat.unpackMantissa Format.binary64 b₁ = 0#_ <;>
        simp [hz1, hm1] at h1
    · simp [hz1] at h1
  · simp only [he1, ↓reduceIte, he2] at h1
    by_cases hz1 : @UnpackedFloat.unpackExponent Format.binary64 b₁ = 0#_ <;>
      by_cases hz2 : @UnpackedFloat.unpackExponent Format.binary64 b₂ = 0#_
    · by_cases hm1 : @UnpackedFloat.unpackMantissa Format.binary64 b₁ = 0#_ <;>
        by_cases hm2 : @UnpackedFloat.unpackMantissa Format.binary64 b₂ = 0#_
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2, hm2, UnpackedFloat.zero.injEq] at h1
        exact bitVec64_ext_components h1 (hz1.trans hz2.symm) (hm1.trans hm2.symm)
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2, hm2] at h1
        cases h1
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2, hm2] at h1
        cases h1
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2, hm2, UnpackedFloat.finite.injEq] at h1
        rcases h1 with ⟨hs, hm, _⟩
        exact bitVec64_ext_components hs (hz1.trans hz2.symm) (BitVec.eq_of_toNat_eq hm)
    · by_cases hm1 : @UnpackedFloat.unpackMantissa Format.binary64 b₁ = 0#_
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2] at h1
        cases h1
      · simp only [hz1, hm1, ↓reduceDIte, ↓reduceIte, hz2, UnpackedFloat.finite.injEq] at h1
        rcases h1 with ⟨_, hm, _⟩
        have hlt1 : (@UnpackedFloat.unpackMantissa Format.binary64 b₁).toNat < 2 ^ 52 := BitVec.isLt _
        have hEqW : BitVec.setWidth 53 (@UnpackedFloat.unpackMantissa Format.binary64 b₁) =
            1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₂ := by
          apply BitVec.eq_of_toNat_eq
          have hlt2 : (1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₂).toNat < 2 ^ 53 := BitVec.isLt _
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          exact hm
        have h52a : (BitVec.setWidth 53 (@UnpackedFloat.unpackMantissa Format.binary64 b₁))[52] = false := by
          simp
        have h52b : (1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₂)[52] = true := by
          rw [BitVec.getElem_append]
          simp
        rw [hEqW, h52b] at h52a
        contradiction
    · by_cases hm2 : @UnpackedFloat.unpackMantissa Format.binary64 b₂ = 0#_
      · simp only [hz1, ↓reduceIte, hz2, hm2, ↓reduceDIte] at h1
        cases h1
      · simp only [hz1, ↓reduceIte, hz2, hm2, ↓reduceDIte, UnpackedFloat.finite.injEq] at h1
        rcases h1 with ⟨_, hm, _⟩
        have hlt2 : (@UnpackedFloat.unpackMantissa Format.binary64 b₂).toNat < 2 ^ 52 := BitVec.isLt _
        have hEqW : BitVec.setWidth 53 (@UnpackedFloat.unpackMantissa Format.binary64 b₂) =
            1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₁ := by
          apply BitVec.eq_of_toNat_eq
          have hlt1 : (1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₁).toNat < 2 ^ 53 := BitVec.isLt _
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          exact hm.symm
        have h52a : (BitVec.setWidth 53 (@UnpackedFloat.unpackMantissa Format.binary64 b₂))[52] = false := by
          simp
        have h52b : (1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₁)[52] = true := by
          rw [BitVec.getElem_append]
          simp
        rw [hEqW, h52b] at h52a
        contradiction
    · simp only [hz1, ↓reduceIte, hz2, UnpackedFloat.finite.injEq] at h1
      rcases h1 with ⟨hs, hm, hexp⟩
      have hexpEq : @UnpackedFloat.unpackExponent Format.binary64 b₁ =
          @UnpackedFloat.unpackExponent Format.binary64 b₂ :=
        BitVec.eq_of_toNat_eq (by omega)
      have hcat : 1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₁ =
          1#1 ++ @UnpackedFloat.unpackMantissa Format.binary64 b₂ :=
        BitVec.eq_of_toNat_eq hm
      have hmEq : @UnpackedFloat.unpackMantissa Format.binary64 b₁ =
          @UnpackedFloat.unpackMantissa Format.binary64 b₂ := by
        ext i hi
        have hbit := congrArg (fun x : BitVec 53 => x[i]) hcat
        rw [BitVec.getElem_append, BitVec.getElem_append] at hbit
        simp [hi] at hbit
        exact hbit
      exact bitVec64_ext_components hs hexpEq hmEq

private theorem float_eq_of_unpack_eq {a b : Float}
    (ha : ¬(a.isNaN = true))
    (h : a.toModel.unpack = b.toModel.unpack) : a = b := by
  have hna : a.toModel.unpack ≠ .notANumber := fun hnan =>
    ha ((unpacked_isNaN_iff _).mpr hnan)
  have hbv : a.toModel.toBits.toBitVec = b.toModel.toBits.toBitVec :=
    unpackExponent_inj_aux h hna
  have hu : a.toModel.toBits = b.toModel.toBits := UInt64.toBitVec_inj.mp hbv
  cases a with | ofModel ma =>
  cases b with | ofModel mb =>
  cases ma with | mk ba va =>
  cases mb with | mk bb vb =>
  simp only at hu
  subst hu
  rfl

/-- For non-NaN, non-zero floats, `FloatEquiv` coincides with propositional equality `a = b`. -/
theorem floatEquiv_nonZero_eq {a b : Float}
    (ha : ¬(a.isNaN = true)) (hb : ¬(b.isNaN = true))
    (hnz : (a == (0.0 : Float)) = false) :
    FloatEquiv a b ↔ a = b := by
  rw [floatEquiv_nonNaN_iff_beq ha hb]
  constructor
  · intro hbeq
    change (a.toModel.unpack.beq b.toModel.unpack) = true at hbeq
    simp only [UnpackedFloat.beq, beq_iff_eq] at hbeq
    obtain ⟨_, _, hrel⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hbeq
    rcases hrel with ⟨_, _, ha0, _⟩ | hunpack
    · exfalso
      have h0 : (a == (0.0 : Float)) = true := by
        change (a.toModel.unpack.beq (0.0 : Float).toModel.unpack) = true
        simp only [UnpackedFloat.beq, beq_iff_eq]
        have hz : (0.0 : Float).toModel.unpack = .zero .positive := by
          have hz0 : (0.0 : Float) = Float.ofBits 0 := by decide
          rw [hz0]
          rfl
        rw [ha0, hz]
        simp [UnpackedFloat.compare]
      rw [h0] at hnz
      contradiction
    · exact float_eq_of_unpack_eq ha hunpack
  · intro heq
    subst heq
    exact (floatEquiv_nonNaN_iff_beq ha hb).mp (floatEquiv_refl a)

/-- Negation preserves `FloatEquiv`. -/
theorem floatEquiv_neg {a b : Float} (hab : FloatEquiv a b) : FloatEquiv (-a) (-b) := by
  rcases hab with ⟨ha, hb⟩ | hbeq
  · left
    have hna : a.toModel.unpack = .notANumber := (unpacked_isNaN_iff _).mp ha
    have hnb : b.toModel.unpack = .notANumber := (unpacked_isNaN_iff _).mp hb
    have hnegNaN : ∀ x : Float, x.toModel.unpack = .notANumber → (-x).isNaN = true := by
      intro x hx
      have hneg : (-x.toModel) = .nan := by
        change Float.Model.pack x.toModel.unpack.neg = Float.Model.nan
        rw [hx]
        rfl
      change ((-x.toModel).unpack.isNaN) = true
      rw [hneg]
      decide
    exact ⟨hnegNaN a hna, hnegNaN b hnb⟩
  · change (a.toModel.unpack.beq b.toModel.unpack) = true at hbeq
    simp only [UnpackedFloat.beq, beq_iff_eq] at hbeq
    obtain ⟨ha, _, hrel⟩ := (unpacked_compare_eq_some_eq_iff _ _).mp hbeq
    rcases hrel with ⟨s₁, s₂, ha0, hb0⟩ | hunpack
    · have haNotNaN : ¬(a.isNaN = true) := fun h => ha ((unpacked_isNaN_iff _).mp h)
      have hbNotNaN : ¬(b.isNaN = true) := by
        intro h
        have hnb := (unpacked_isNaN_iff _).mp h
        rw [hb0] at hnb
        cases hnb
      have haZero : a = Float.ofBits 0 ∨ a = Float.ofBits 0x8000000000000000 := by
        cases s₁ with
        | positive =>
          left
          apply float_eq_of_unpack_eq haNotNaN
          rw [ha0]
          rfl
        | negative =>
          right
          apply float_eq_of_unpack_eq haNotNaN
          rw [ha0]
          rfl
      have hbZero : b = Float.ofBits 0 ∨ b = Float.ofBits 0x8000000000000000 := by
        cases s₂ with
        | positive =>
          left
          apply float_eq_of_unpack_eq hbNotNaN
          rw [hb0]
          rfl
        | negative =>
          right
          apply float_eq_of_unpack_eq hbNotNaN
          rw [hb0]
          rfl
      rcases haZero with rfl | rfl <;> rcases hbZero with rfl | rfl <;> right <;> decide
    · have haNotNaN : ¬(a.isNaN = true) := fun h => ha ((unpacked_isNaN_iff _).mp h)
      have heq : a = b := float_eq_of_unpack_eq haNotNaN hunpack
      subst heq
      exact floatEquiv_refl (-a)

/-- Integer base supported by `LeanSwe.NumParse`. -/
inductive NumBase where
  /-- Base 2 (`0b` / `0B`). -/
  | bin
  /-- Base 8 (`0o` / `0O`). -/
  | oct
  /-- Base 10 (unprefixed decimal). -/
  | dec
  /-- Base 16 (`0x` / `0X`). -/
  | hex
  deriving Repr, BEq, DecidableEq

/-- Numerical radix of a `NumBase`. -/
def NumBase.radix : NumBase → Nat
  | .bin => 2
  | .oct => 8
  | .dec => 10
  | .hex => 16

/-- Digit value in the given `NumBase`, or `none` if `c` is not a valid digit in that base. -/
def digitVal? (b : NumBase) (c : Char) : Option Nat :=
  match b with
  | .bin =>
    if c == '0' then some 0
    else if c == '1' then some 1
    else none
  | .oct =>
    if '0' ≤ c && c ≤ '7' then some (c.toNat - '0'.toNat) else none
  | .dec =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
  | .hex =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none

/-- Predicate checking whether `c` is an ASCII decimal digit `'0'..'9'`. -/
def isDecDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Accumulator helper evaluating a big-endian list of digit values in `base`. -/
def evalDigitsAux (base : Nat) (acc : Nat) : List Nat → Nat
  | [] => acc
  | d :: ds => evalDigitsAux base (acc * base + d) ds

/-- Evaluate a big-endian list of digit values in `base`. -/
def evalDigits (base : Nat) (ds : List Nat) : Nat :=
  evalDigitsAux base 0 ds

/-- `evalDigits` on an empty list is `0`. -/
theorem evalDigits_nil (base : Nat) : evalDigits base [] = 0 := rfl

/-- `evalDigitsAux` distributes over list concatenation. -/
theorem evalDigitsAux_append (base acc : Nat) (ds₁ ds₂ : List Nat) :
    evalDigitsAux base acc (ds₁ ++ ds₂) = evalDigitsAux base (evalDigitsAux base acc ds₁) ds₂ := by
  induction ds₁ generalizing acc with
  | nil => rfl
  | cons d ds ih => exact ih (acc * base + d)

/-- `evalDigits` over a singleton list returns the digit itself. -/
theorem evalDigits_singleton (base d : Nat) : evalDigits base [d] = d := by
  simp [evalDigits, evalDigitsAux]

/-- Minimum `Int64` value as an unbounded `Int` (`-2^63`). -/
def int64MinInt : Int := -9223372036854775808

/-- Maximum `Int64` value as an unbounded `Int` (`2^63 - 1`). -/
def int64MaxInt : Int := 9223372036854775807

/-- Check whether `n : Int` lies within signed 64-bit bounds `[-2^63, 2^63 - 1]`. -/
def inInt64Range (n : Int) : Bool :=
  decide (int64MinInt ≤ n ∧ n ≤ int64MaxInt)

/-- Characterization of `inInt64Range`. -/
theorem inInt64Range_iff (n : Int) :
    inInt64Range n = true ↔ int64MinInt ≤ n ∧ n ≤ int64MaxInt := by
  simp [inInt64Range]

/-- Map base prefix character (`x`/`X`, `o`/`O`, `b`/`B`) to its `NumBase`. -/
def basePrefix? : Char → Option NumBase
  | 'x' | 'X' => some .hex
  | 'o' | 'O' => some .oct
  | 'b' | 'B' => some .bin
  | _ => none

/-- Scan remaining digits and underscore separators for an integer literal in `NumBase`. -/
def consumeIntDigits (b : NumBase) (acc : Nat) : List Char → Except NumParseErrorKind Nat
  | [] => .ok acc
  | '_' :: c :: cs =>
    match digitVal? b c with
    | some d => consumeIntDigits b (acc * b.radix + d) cs
    | none => .error .invalidUnderscore
  | '_' :: [] => .error .invalidUnderscore
  | c :: cs =>
    match digitVal? b c with
    | some d => consumeIntDigits b (acc * b.radix + d) cs
    | none => .error .trailingChars

/-- Parse an unprefixed signed decimal integer literal body in the model grammar. -/
def parseDecAfterSign (neg : Bool) : List Char → Except NumParseErrorKind Int
  | [] => .error .invalidSyntax
  | '_' :: _ => .error .invalidUnderscore
  | '0' :: rest =>
    match rest with
    | [] => .ok 0
    | c :: _ =>
      if isDecDigit c then .error .leadingZero
      else if c == '_' then
        match rest with
        | '_' :: c2 :: _ =>
          if isDecDigit c2 then .error .leadingZero else .error .invalidUnderscore
        | _ => .error .invalidUnderscore
      else .error .trailingChars
  | c :: rest =>
    match digitVal? .dec c with
    | some d =>
      match consumeIntDigits .dec d rest with
      | .ok n => .ok (if neg then -Int.ofNat n else Int.ofNat n)
      | .error k => .error k
    | none => .error .invalidSyntax

/-- Pure mathematical integer grammar and value specification over `List Char`. -/
def parseIntModelChars : List Char → Except NumParseErrorKind Int
  | [] => .error .emptyInput
  | '+' :: '0' :: b :: rest =>
    if (basePrefix? b).isSome then .error .invalidSignForBase
    else parseDecAfterSign false ('0' :: b :: rest)
  | '-' :: '0' :: b :: rest =>
    if (basePrefix? b).isSome then .error .invalidSignForBase
    else parseDecAfterSign true ('0' :: b :: rest)
  | '+' :: rest => parseDecAfterSign false rest
  | '-' :: rest => parseDecAfterSign true rest
  | '0' :: b :: rest =>
    match basePrefix? b with
    | some base =>
      match rest with
      | [] => .error .invalidSyntax
      | '_' :: _ => .error .invalidUnderscore
      | c :: cs =>
        match digitVal? base c with
        | some d =>
          match consumeIntDigits base d cs with
          | .ok n => .ok (Int.ofNat n)
          | .error k => .error k
        | none => .error .invalidSyntax
    | none => parseDecAfterSign false ('0' :: b :: rest)
  | cs => parseDecAfterSign false cs

/-- Pure mathematical integer grammar and value specification over `String`. -/
def parseIntModel (s : String) : Except NumParseErrorKind Int :=
  parseIntModelChars s.toList

/-- Pure mathematical signed 64-bit integer specification over `String`. -/
def parseInt64Model (s : String) : Except NumParseErrorKind Int64 :=
  match parseIntModel s with
  | .error k => .error k
  | .ok n =>
    if inInt64Range n then .ok (Int64.ofInt n)
    else .error .overflow

/-- `parseInt64Model` agrees with `parseIntModel` on syntax and enforces `inInt64Range` with `.overflow`. -/
theorem parseInt64Model_eq_parseIntModel (s : String) :
    parseInt64Model s =
      match parseIntModel s with
      | .error k => .error k
      | .ok n => if inInt64Range n then .ok (Int64.ofInt n) else .error .overflow := rfl

end LeanSwe.NumParse.Model

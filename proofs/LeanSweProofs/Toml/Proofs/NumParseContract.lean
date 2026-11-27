import LeanSweProofs.Toml.Proofs.Core
import LeanSweProofs.NumParse.Model.Obeys

/-!
# Compositional `ObeysApi` to `ValidNumApi` Bridge (`NumParseContract`)

Derives `ValidNumApi num` solely from `LeanSwe.NumParse.Model.ObeysApi num` without
importing `LeanSwe.NumParse.Proofs`, `LeanSwe.NumParse.Impl`, or `LeanSwe.NumParse.Interface`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Any `NumParseApi` satisfying `LeanSwe.NumParse.Model.ObeysApi` satisfies `ValidNumApi`. -/
theorem validNumApi_of_obeysApi {num : NumParseApi} (h : ObeysApi num) : ValidNumApi num := by
  rcases h with ⟨hInt, hInt64, hFmtInt, hFlt, hFmtFlt⟩
  refine
    { onError := fun s => ⟨(hInt s).2, (hInt64 s).2, (hFlt s).2⟩
    , parseInt64 := hInt64
    , parseFloat := fun s => ?_
    , formatInt := fun n => ?_
    , formatFloat := fun x => ?_
    , formatIntChars := fun n => (hFmtInt n).2.1 }
  · rcases hFlt s with ⟨hm, hmsg⟩
    cases hp : num.parseFloat s with
    | error e =>
      rw [hp] at hm
      cases hpm : parseFloatModel s with
      | error k =>
        rw [hpm] at hm
        injection hm with hk
        exact ⟨hk, hmsg e hp⟩
      | ok v =>
        rw [hpm] at hm
        cases hm
    | ok y =>
      rw [hp] at hm
      cases hpm : parseFloatModel s with
      | error k =>
        rw [hpm] at hm
        cases hm
      | ok v =>
        rw [hpm] at hm
        injection hm with hy
        subst hy
        exact floatBitMatch_refl _
  · rcases hFmtInt n with ⟨hnoU, _, hmodel⟩
    have hpi_map := (hInt (num.formatInt n)).1
    have hpi : num.parseInt (num.formatInt n) = .ok n := by
      cases hp : num.parseInt (num.formatInt n) <;> simp [hp, hmodel, Except.mapError] at hpi_map ⊢
      exact hpi_map
    rcases hInt64 (num.formatInt n) with ⟨h64_map, h64_msg⟩
    refine ⟨hnoU, hmodel, hpi, ?_⟩
    by_cases hr : inInt64Range n = true
    · simp only [hr, ↓reduceIte]
      have hm64 : parseInt64Model (num.formatInt n) = .ok (Int64.ofInt n) := by
        rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr]
      cases hp64 : num.parseInt64 (num.formatInt n) <;> simp [hp64, hm64, Except.mapError] at h64_map ⊢
      exact h64_map
    · have hrF : inInt64Range n = false := Bool.eq_false_iff.mpr hr
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have hm64 : parseInt64Model (num.formatInt n) = .error .overflow := by
        rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hrF]
      cases hp64 : num.parseInt64 (num.formatInt n) <;> simp [hp64, hm64, Except.mapError] at h64_map ⊢
      exact ⟨h64_map, h64_msg _ hp64⟩
  · have hfmt := hFmtFlt x
    refine ⟨hfmt, ?_⟩
    have hpf := (hFlt (num.formatFloat x)).1
    have hfmt' := hfmt
    unfold allowedFormatFloat FloatFormatSpec at hfmt'
    by_cases hnan : x.isNaN = true
    · simp only [hnan, ↓reduceIte] at hfmt'
      rw [hfmt', show parseFloatModel "nan" = .ok Float.nan from rfl] at hpf
      rw [hfmt']
      cases hd : num.parseFloat "nan" with
      | error _ => rw [hd] at hpf; cases hpf
      | ok y =>
        rw [hd] at hpf
        injection hpf with hy
        subst hy
        have hn : Float.nan.isNaN = true := by decide
        exact ⟨by simp [FloatBitMatch, hnan, hn], Or.inl ⟨hnan, hn⟩⟩
    · simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hfmt'
      by_cases hinf : (x == Float.inf) = true
      · simp only [hinf, ↓reduceIte] at hfmt'
        rw [hfmt', show parseFloatModel "inf" = .ok Float.inf from rfl] at hpf
        rw [hfmt']
        cases hd : num.parseFloat "inf" with
        | error _ => rw [hd] at hpf; cases hpf
        | ok y =>
          rw [hd] at hpf
          injection hpf with hy
          subst hy
          have hxEq : Float.inf = x :=
            (floatEquiv_nonZero_eq (by decide) hnan (by decide)).mp (floatEquiv_symm (Or.inr hinf))
          subst hxEq
          exact ⟨floatBitMatch_refl _, floatEquiv_refl _⟩
      · simp only [hinf, Bool.false_eq_true, ↓reduceIte] at hfmt'
        by_cases hninf : (x == -Float.inf) = true
        · simp only [hninf, ↓reduceIte] at hfmt'
          rw [hfmt', show parseFloatModel "-inf" = .ok (-Float.inf) from rfl] at hpf
          rw [hfmt']
          cases hd : num.parseFloat "-inf" with
          | error _ => rw [hd] at hpf; cases hpf
          | ok y =>
            rw [hd] at hpf
            injection hpf with hy
            subst hy
            have hxEq : -Float.inf = x :=
              (floatEquiv_nonZero_eq (by decide) hnan (by decide)).mp (floatEquiv_symm (Or.inr hninf))
            subst hxEq
            exact ⟨floatBitMatch_refl _, floatEquiv_refl _⟩
        · simp only [hninf, Bool.false_eq_true, ↓reduceIte] at hfmt'
          rcases hfmt' with ⟨_, _, hm⟩
          cases hd : num.parseFloat (num.formatFloat x) with
          | error e =>
            have hpm : parseFloatModel (num.formatFloat x) = .error e.kind := by
              rw [← hpf, hd]; rfl
            rw [hpm] at hm
            exact False.elim hm
          | ok y =>
            have hpm : parseFloatModel (num.formatFloat x) = .ok y := by
              rw [← hpf, hd]; rfl
            rw [hpm] at hm
            have hbm : FloatBitMatch x y := by simp [FloatBitMatch, hnan, hm]
            exact ⟨hbm, floatEquiv_symm (floatBitMatch_implies_floatEquiv hbm)⟩

end LeanSwe.Toml.Proofs

import LeanSwe.Time.Interface
import LeanSwe.Time.EpochBaseProofs
import LeanSwe.Time.HinnantProofs

namespace LeanSwe.Time.Proofs

open Std.Time

private theorem year_range_core (z era doe yoe doy mp m : Int)
    (hz_b : -60 ≤ z ∧ z ≤ 3652364)
    (hera : era = (if z ≥ 0 then z else z - 146096).tdiv 146097)
    (hdoe : doe = z - era * 146097)
    (hyoe : yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365)
    (hdoy : doy = doe - (365 * yoe + yoe / 4 - yoe / 100))
    (hmp : mp = (5 * doy + 2) / 153)
    (hm : m = mp + if mp < 10 then 3 else -9) :
    0 ≤ yoe + era * 400 + (if m ≤ 2 then 1 else 0) ∧
      yoe + era * 400 + (if m ≤ 2 then 1 else 0) ≤ 9999 := by
  by_cases hneg : z ≥ 0
  · have hera_e : era = z / 146097 := by
      rw [hera]; simp only [hneg, ↓reduceIte, Int.tdiv_eq_ediv_of_nonneg hneg]
    have hdoe0 : 0 ≤ doe := by omega
    have hdoe1 : doe ≤ 146096 := by omega
    have hmax := hinnantF_mono hdoe0 hdoe1 (by omega)
    have hmin := hinnantF_mono (by omega : 0 ≤ (0 : Int)) hdoe0 hdoe1
    have hv146 : hinnantF 146096 / 365 = 399 := rfl
    have hv0 : hinnantF 0 / 365 = 0 := rfl
    have hyoe_f : yoe = hinnantF doe / 365 := hyoe
    have hyoe_b : 0 ≤ yoe ∧ yoe ≤ 399 := by
      rw [hyoe_f]
      have hd1 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmin
      have hd2 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmax
      omega
    by_cases hera24 : era = 24
    · subst hera24
      have hdoe24 : doe ≤ 146036 := by omega
      have hmax24 := hinnantF_mono hdoe0 hdoe24 (by omega)
      have hv24 : hinnantF 146036 / 365 = 399 := rfl
      have hmgt : yoe = 399 → m > 2 := by
        intro hy399
        have hdoy_l : doy ≤ 305 := by rw [hdoy, hy399]; omega
        omega
      by_cases hy399 : yoe = 399
      · have hnot : ¬ (m ≤ 2) := by have := hmgt hy399; omega
        simp only [hnot, ↓reduceIte]
        omega
      · split <;> omega
    · have hera_lt : era ≤ 24 := by omega
      split <;> omega
  · have hera_n : era = -1 := by
      rw [hera]; simp only [hneg, ↓reduceIte]
      have hmul := Int.mul_tdiv_add_tmod (z - 146096) 146097
      have hb := tmod_bounds_neg (z - 146096) 146097 (by omega) (by decide)
      omega
    have hdoe_b : 146037 ≤ doe ∧ doe ≤ 146096 := by omega
    have hmin := hinnantF_mono (by omega : 0 ≤ (146037 : Int)) hdoe_b.1 (by omega)
    have hmax := hinnantF_mono (by omega : 0 ≤ doe) hdoe_b.2 (by omega)
    have hv1 : hinnantF 146037 / 365 = 399 := rfl
    have hv2 : hinnantF 146096 / 365 = 399 := rfl
    have hyoe399 : yoe = 399 := by
      rw [hyoe]
      change hinnantF doe / 365 = 399
      have hd1 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmin
      have hd2 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmax
      omega
    have hdoy_ge : doy ≥ 306 := by rw [hdoy, hyoe399]; omega
    have hm_le : m ≤ 2 := by omega
    simp [hm_le, hyoe399, hera_n]

/-- Calendar/formatting proof helper `ofEpochDay_year_range`. -/
theorem ofEpochDay_year_range (day : Day.Offset)
    (hlo : -719528 ≤ day.val) (hhi : day.val ≤ 2932896) :
    0 ≤ (PlainDate.ofEpochDay day).year.toInt ∧ (PlainDate.ofEpochDay day).year.toInt ≤ 9999 := by
  have hev := hinnant_ofEpochDay_eval day
  rw [hev.1]
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let m := mp + if mp < 10 then 3 else -9
  have hz_b : -60 ≤ z ∧ z ≤ 3652364 := by
    change -60 ≤ day.val + 719468 ∧ day.val + 719468 ≤ 3652364
    omega
  exact year_range_core z era doe yoe doy mp m hz_b rfl rfl rfl rfl rfl rfl

end LeanSwe.Time.Proofs

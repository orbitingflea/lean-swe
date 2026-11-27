import LeanSwe.Time.Interface
import LeanSweProofs.Time.Proofs.EpochBaseProofs
import LeanSweProofs.Time.Proofs.HinnantProofs

namespace LeanSwe.Time.Proofs

open Std.Time

private theorem toEpochDay_arith_core (dint z era doe yoe doy d m y : Int)
    (hz : z = dint + 719468)
    (hdoe : doe = z - era * 146097)
    (hdoe_b : 0 ≤ doe ∧ doe ≤ 146096)
    (hyoe : yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365)
    (hdoe_eq : doe = 365 * yoe + yoe / 4 - yoe / 100 + doy)
    (hdoy_back : doy = (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1)
    (hm_b : 1 ≤ m ∧ m ≤ 12)
    (hym1 : m ≤ 2 → y - 1 = yoe + era * 400)
    (hym2 : m > 2 → y = yoe + era * 400) :
    (let y' := if m > 2 then y else y - 1
     let era' := (if y' ≥ 0 then y' else y' - 399).tdiv 400
     let yoe' := y' - era' * 400
     let doy' := (153 * (m + if m > 2 then -3 else 9) + 2).tdiv 5 + d - 1
     era' * 146097 + (yoe' * 365 + yoe'.tdiv 4 - yoe'.tdiv 100 + doy') - 719468) = dint := by
  have hyoe_b : 0 ≤ yoe ∧ yoe ≤ 399 := by
    have hmax := hinnantF_mono hdoe_b.1 hdoe_b.2 (by omega)
    have hmin := hinnantF_mono (by omega : 0 ≤ (0 : Int)) hdoe_b.1 hdoe_b.2
    have hv146 : hinnantF 146096 / 365 = 399 := rfl
    have hv0 : hinnantF 0 / 365 = 0 := rfl
    have hd1 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmin
    have hd2 := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmax
    have hy_f : yoe = hinnantF doe / 365 := hyoe
    omega
  have hy_adj : (if m > 2 then y else y - 1) = yoe + era * 400 := by
    by_cases hmgt : m > 2
    · simp only [hmgt, ↓reduceIte]; exact hym2 hmgt
    · simp only [hmgt, ↓reduceIte]; exact hym1 (by omega)
  have hera_rec : (if yoe + era * 400 ≥ 0 then yoe + era * 400 else yoe + era * 400 - 399).tdiv 400 = era := by
    by_cases hnon : yoe + era * 400 ≥ 0
    · simp only [hnon, ↓reduceIte, Int.tdiv_eq_ediv_of_nonneg hnon]; omega
    · simp only [hnon, ↓reduceIte]
      have hneg : yoe + era * 400 - 399 ≤ 0 := by omega
      have hmul := Int.mul_tdiv_add_tmod (yoe + era * 400 - 399) 400
      have hb := tmod_bounds_neg (yoe + era * 400 - 399) 400 hneg (by decide)
      omega
  have hdoy_tdiv : (153 * (m + if m > 2 then -3 else 9) + 2).tdiv 5 =
      (153 * (m + if m > 2 then -3 else 9) + 2) / 5 :=
    Int.tdiv_eq_ediv_of_nonneg (by by_cases h : m > 2 <;> simp [h] <;> omega)
  dsimp only
  rw [hy_adj, hera_rec]
  have hyoe_rec : yoe + era * 400 - era * 400 = yoe := by omega
  rw [hyoe_rec, Int.tdiv_eq_ediv_of_nonneg hyoe_b.1, Int.tdiv_eq_ediv_of_nonneg hyoe_b.1, hdoy_tdiv]
  omega

/-- Calendar/formatting proof helper `toEpochDay_ofEpochDay`. -/
theorem toEpochDay_ofEpochDay (day : Day.Offset) :
    (PlainDate.ofEpochDay day).toEpochDay = day := by
  have hev := hinnant_ofEpochDay_eval day
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := mp + if mp < 10 then 3 else -9
  let y := yoe + era * 400 + if m ≤ 2 then 1 else 0
  have hdoe_b : 0 ≤ doe ∧ doe ≤ 146096 := by
    dsimp [doe, era]
    split
    · next h =>
      have hmul := Int.mul_tdiv_add_tmod z 146097
      have h1 := Int.tmod_nonneg 146097 h
      have h2 := Int.tmod_lt_of_pos z (by decide : 0 < (146097 : Int))
      omega
    · next h =>
      have hmul := Int.mul_tdiv_add_tmod (z - 146096) 146097
      have hb := tmod_bounds_neg (z - 146096) 146097 (by omega) (by decide)
      omega
  have harith := toEpochDay_arith_core day.toInt z era doe yoe doy d m y
    rfl rfl hdoe_b rfl hev.2.2.2.1 hev.2.2.2.2.1
    ⟨hev.2.2.2.2.2.1, hev.2.2.2.2.2.2.1⟩
    hev.2.2.2.2.2.2.2.2.2.1 hev.2.2.2.2.2.2.2.2.2.2
  have hm_eq : (PlainDate.ofEpochDay day).month.toInt = m := hev.2.1
  have hd_eq : (PlainDate.ofEpochDay day).day.toInt = d := hev.2.2.1
  have hy_eq : (PlainDate.ofEpochDay day).year = Year.Offset.ofInt y := hev.1
  unfold PlainDate.toEpochDay
  rw [hm_eq, hd_eq, hy_eq]
  have hday_eq : Day.Offset.ofInt day.toInt = day := by apply Internal.UnitVal.ext; rfl
  rw [← hday_eq]
  apply congrArg Day.Offset.ofInt
  dsimp only [Year.Offset.ofInt, Year.Offset.toInt]
  exact harith

end LeanSwe.Time.Proofs

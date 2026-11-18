import LeanSwe.Time.Interface
import LeanSwe.Time.EpochBaseProofs

namespace LeanSwe.Time.Proofs

open Std.Time

/-- Hinnant evaluation lemma `hinnant_ofEpochDay_eval`. -/
theorem hinnant_ofEpochDay_eval (day : Day.Offset) :
    let z := day.toInt + 719468
    let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
    let doe := z - era * 146097
    let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
    let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := mp + if mp < 10 then 3 else -9
    let y := yoe + era * 400 + if m ≤ 2 then 1 else 0
    (PlainDate.ofEpochDay day).year.toInt = y ∧
    (PlainDate.ofEpochDay day).month.val = m ∧
    (PlainDate.ofEpochDay day).day.val = d ∧
    doe = 365 * yoe + yoe / 4 - yoe / 100 + doy ∧
    doy = (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 ∧
    1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧
    (d ≤ if m = 2 then (if (Year.Offset.ofInt y).isLeap then 29 else 28)
      else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31) ∧
    (m ≤ 2 → y - 1 = yoe + era * 400) ∧
    (m > 2 → y = yoe + era * 400) := by
  intro z era doe yoe doy mp d m y
  have hdoe : 0 ≤ doe ∧ doe ≤ 146096 := by
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
  have hyoe_b : 0 ≤ yoe ∧ yoe ≤ 399 := by
    have hmax := hinnantF_mono hdoe.1 hdoe.2 (by omega)
    have hmin := hinnantF_mono (by omega : 0 ≤ (0 : Int)) hdoe.1 hdoe.2
    have hv146 : hinnantF 146096 / 365 = 399 := rfl
    have hv0 : hinnantF 0 / 365 = 0 := rfl
    change 0 ≤ hinnantF doe / 365 ∧ hinnantF doe / 365 ≤ 399
    omega
  have hdoy_b : 0 ≤ doy ∧ doy ≤ 365 ∧
      (doy = 365 → (yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0))) := by
    have hfin := hinnant_yoe_bounds yoe hyoe_b.1 hyoe_b.2
    dsimp at hfin
    have hnot_next : yoe < 399 → doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 := by
      intro hlt
      exact Classical.byContradiction fun hge => by
        have hge' : 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100 ≤ doe := by omega
        have hfn := hinnant_yoe_bounds (yoe + 1) (by omega) (by omega)
        dsimp at hfn
        have hm := hinnantF_mono hfn.1 hge' hdoe.2
        have hdiv : hinnantF (365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100) / 365 ≤ hinnantF doe / 365 :=
          Int.ediv_le_ediv (by decide) hm
        have hy_eq : hinnantF doe / 365 = yoe := rfl
        omega
    have hnot_prev : 365 * yoe + yoe / 4 - yoe / 100 ≤ doe := by
      exact Classical.byContradiction fun hlt => by
        have hypos : 1 ≤ yoe := Classical.byContradiction fun h0 => by
          have hy0 : yoe = 0 := by omega
          rw [hy0] at hlt; simp at hlt; exact absurd hdoe.1 (by omega)
        have hle := hinnant_prev_dmax yoe doe hypos hyoe_b.2 hdoe.1 (by omega)
        have hy_eq : hinnantF doe / 365 = yoe := rfl
        omega
    have hdoy_le : doy ≤ if yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0) then 365 else 364 := by
      by_cases h399 : yoe = 399
      · simp [h399]; omega
      · exact doy_upper_of_lt yoe doe hyoe_b.1 (by omega) (hnot_next (by omega))
    refine ⟨by omega, ?_, ?_⟩
    · split at hdoy_le <;> omega
    · intro h365
      exact Classical.byContradiction fun hneg => by
        simp [hneg] at hdoy_le
        omega
  have hmp_b : 0 ≤ mp ∧ mp ≤ 11 := by omega
  have hm_b : 1 ≤ m ∧ m ≤ 12 := by omega
  have hd_b : 1 ≤ d ∧ d ≤ 31 := by omega
  have hdoy_back : doy = (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 :=
    doy_mp_back doy hdoy_b.1 hdoy_b.2.1
  have hday_valid : d ≤ if m = 2 then (if (Year.Offset.ofInt y).isLeap then 29 else 28)
      else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31 := by
    refine doy_day_valid doy (Year.Offset.ofInt y).isLeap hdoy_b.1 hdoy_b.2.1 ?_
    intro h365
    have hc := hdoy_b.2.2 h365
    have hmp11 : mp = 11 := by dsimp [mp]; rw [h365]; rfl
    have hm2 : m = 2 := by dsimp [m]; rw [hmp11]; rfl
    have hy_e : y = yoe + 1 + era * 400 := by dsimp [y]; simp [hm2]; omega
    rw [hy_e, isLeap_yoe_plus1 era yoe hyoe_b.1 hyoe_b.2]
    simp [hc]
  have hyoe_t : doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096 =
      doe - doe / 1460 + doe / 36524 - doe / 146096 := by
    rw [Int.tdiv_eq_ediv_of_nonneg hdoe.1, Int.tdiv_eq_ediv_of_nonneg hdoe.1,
      Int.tdiv_eq_ediv_of_nonneg hdoe.1]
  have hfn : PlainDate.ofEpochDay day =
      PlainDate.ofYearMonthDayClip (Year.Offset.ofInt y)
        (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal)
        (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal) := by
    unfold PlainDate.ofEpochDay
    have h1 : (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365 = yoe := by
      rw [hyoe_t]
      exact Int.tdiv_eq_ediv_of_nonneg (by omega)
    have h2 : (doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100)) = doy := by
      rw [Int.tdiv_eq_ediv_of_nonneg hyoe_b.1, Int.tdiv_eq_ediv_of_nonneg hyoe_b.1]
    have h3 : (5 * doy + 2).tdiv 153 = mp := Int.tdiv_eq_ediv_of_nonneg (by omega)
    have h4 : (153 * mp + 2).tdiv 5 = (153 * mp + 2) / 5 := Int.tdiv_eq_ediv_of_nonneg (by omega)
    dsimp only
    rw [h1, h2, h3, h4]
    rfl
  have hval : (Year.Offset.ofInt y).Valid
      (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal)
      (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal) := by
    have hdval := day_clip_eq hd_b
    have hmval := month_clip_eq hm_b
    have hdv := days_val_eq (Year.Offset.ofInt y).isLeap
      (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal)
    show (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal).val ≤
      (Month.Ordinal.days (Year.Offset.ofInt y).isLeap
        (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal)).val
    rw [hdval, hdv, hmval]
    exact hday_valid
  have hclip : Month.Ordinal.clipDay (Year.Offset.ofInt y).isLeap
      (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal)
      (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal) =
      (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal) := clipDay_of_le hval
  have heval : PlainDate.ofEpochDay day =
      ⟨Year.Offset.ofInt y, Internal.Bounded.LE.clip m (by decide),
        Internal.Bounded.LE.clip d (by decide), hval⟩ := by
    rw [hfn]
    apply plainDate_ext
    · rfl
    · rfl
    · dsimp [PlainDate.ofYearMonthDayClip]
      exact hclip
  rw [heval]
  refine ⟨rfl, month_clip_eq hm_b, day_clip_eq hd_b, by omega, hdoy_back, hm_b.1, hm_b.2, hd_b.1,
    hday_valid, ?_, ?_⟩
  · intro hmle; dsimp [y]; simp [hmle]
  · intro hmgt; dsimp [y]; simp [show ¬ (m ≤ 2) by omega]

end LeanSwe.Time.Proofs

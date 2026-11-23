import LeanSwe.Time.Interface

namespace LeanSwe.Time.Proofs

open Std.Time

/-- Calendar/Hinnant proof helper `tmod_bounds_neg`. -/
theorem tmod_bounds_neg (n d : Int) (hn : n ≤ 0) (hd : 0 < d) :
    -d < n.tmod d ∧ n.tmod d ≤ 0 := by
  have h1 : 0 ≤ (-n).tmod d := Int.tmod_nonneg d (by omega)
  have h2 : (-n).tmod d < d := Int.tmod_lt_of_pos (-n) hd
  rw [show n.tmod d = -((-n).tmod d) by rw [← Int.neg_tmod, Int.neg_neg]]
  omega

private theorem tmod_eq_zero_iff (x d : Int) (_hd : 0 < d) :
    x.tmod d = 0 ↔ x % d = 0 := by
  by_cases hx : 0 ≤ x
  · rw [Int.tmod_eq_emod_of_nonneg hx]
  · rw [show x = -(-x) from (Int.neg_neg x).symm, Int.neg_tmod,
      Int.tmod_eq_emod_of_nonneg (by omega), Int.neg_neg, Int.neg_eq_zero]
    constructor <;> intro h
    · rw [← Int.dvd_iff_emod_eq_zero, ← Int.dvd_neg, Int.dvd_iff_emod_eq_zero]; exact h
    · rw [← Int.dvd_iff_emod_eq_zero, Int.dvd_neg, Int.dvd_iff_emod_eq_zero]; exact h

/-- Calendar/Hinnant proof helper `era_yoe_bounds`. -/
theorem era_yoe_bounds (y : Int) :
    let era := (if y ≥ 0 then y else y - 399).tdiv 400
    let yoe := y - era * 400
    0 ≤ yoe ∧ yoe ≤ 399 := by
  dsimp
  split
  · next h =>
    have hmul := Int.mul_tdiv_add_tmod y 400
    have h1 := Int.tmod_nonneg 400 h
    have h2 : y.tmod 400 < 400 := Int.tmod_lt_of_pos y (by decide)
    omega
  · next h =>
    have hmul := Int.mul_tdiv_add_tmod (y - 399) 400
    have hb := tmod_bounds_neg (y - 399) 400 (by omega) (by decide)
    omega

/-- Calendar/Hinnant proof helper `isLeap_yoe_plus1`. -/
theorem isLeap_yoe_plus1 (era yoe : Int) (hy0 : 0 ≤ yoe) (hy1 : yoe ≤ 399) :
    (Year.Offset.ofInt (yoe + 1 + era * 400)).isLeap =
      decide ((yoe = 399) ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0)) := by
  simp only [Year.Offset.isLeap]
  have hv : (Year.Offset.ofInt (yoe + 1 + era * 400)).toInt = yoe + 1 + era * 400 := rfl
  rw [hv]
  apply decide_eq_decide.mpr
  simp only [ne_eq, tmod_eq_zero_iff _ 4 (by decide), tmod_eq_zero_iff _ 100 (by decide),
    tmod_eq_zero_iff _ 400 (by decide)]
  omega

/-- Calendar/Hinnant proof helper `days_val_eq`. -/
theorem days_val_eq (leap : Bool) (m : Month.Ordinal) :
    (Month.Ordinal.days leap m).val =
      if m.val = 2 then (if leap then 29 else 28)
      else if m.val = 4 ∨ m.val = 6 ∨ m.val = 9 ∨ m.val = 11 then 30 else 31 := by
  have hfin : ∀ (lp : Bool) (k : Fin 13), (hk : 1 ≤ (k.val : Int) ∧ (k.val : Int) ≤ 12) →
      (Month.Ordinal.days lp ⟨k.val, hk⟩).val =
        if (k.val : Int) = 2 then (if lp then 29 else 28)
        else if (k.val : Int) = 4 ∨ (k.val : Int) = 6 ∨ (k.val : Int) = 9 ∨ (k.val : Int) = 11 then 30 else 31 := by
    decide
  rcases m with ⟨mv, hm⟩
  have hk : (mv.toNat : Int) = mv := by omega
  have hres := hfin leap ⟨mv.toNat, by omega⟩ (by simpa [hk] using hm)
  simpa [hk] using hres

/-- Hinnant helper. -/
def hinnantF (x : Int) : Int :=
  x - x / 1460 + x / 36524 - x / 146096

/-- Epoch base proof helper `hinnantF`. -/
theorem hinnantF_step (x : Int) (hx0 : 0 ≤ x) (hx1 : x < 146096) :
    hinnantF x ≤ hinnantF (x + 1) := by
  dsimp [hinnantF]
  by_cases hlast : x = 146095
  · subst hlast; decide
  · omega

/-- Epoch base proof helper `hinnantF`. -/
theorem hinnantF_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 146096) :
    hinnantF a ≤ hinnantF b := by
  have hk : ∃ k : Nat, b = a + k := ⟨(b - a).toNat, by omega⟩
  rcases hk with ⟨k, rfl⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : a + (k : Int) ≤ 146096 := by omega
    have h2 : a + (k : Int) < 146096 := by omega
    have hstep := hinnantF_step (a + k) (by omega) h2
    rw [show a + ((k + 1 : Nat) : Int) = a + (k : Int) + 1 by omega]
    exact Int.le_trans (ih (by omega) h1) hstep

/-- Epoch base proof helper `hinnant_yoe_bounds`. -/
theorem hinnant_yoe_bounds_alg (yv : Int) (hy0 : 0 ≤ yv) (hy1 : yv ≤ 399) :
    let dmin := 365 * yv + yv / 4 - yv / 100
    let maxDoy : Int := if yv = 399 ∨ ((yv + 1) % 4 = 0 ∧ (yv + 1) % 100 ≠ 0) then 365 else 364
    let dmax := dmin + maxDoy
    0 ≤ dmin ∧ dmax ≤ 146096 ∧ hinnantF dmin / 365 = yv ∧ hinnantF dmax / 365 = yv := by
  dsimp [hinnantF]
  let c := yv / 100
  let k := (yv % 100) / 4
  let r := yv % 4
  have hdec : yv = 100 * c + 4 * k + r ∧ 0 ≤ c ∧ c ≤ 3 ∧ 0 ≤ k ∧ k ≤ 24 ∧ 0 ≤ r ∧ r ≤ 3 := by
    dsimp [c, k, r]; omega
  have hy4 : yv / 4 = 25 * c + k := by dsimp [c, k]; omega
  have hy100 : yv / 100 = c := rfl
  have hdmin_e : 365 * yv + yv / 4 - yv / 100 = 36524 * c + 1461 * k + 365 * r := by
    rw [hy4, hy100]; omega
  by_cases h399 : yv = 399
  · subst h399; decide
  · have hm_lt : 365 * yv + yv / 4 - yv / 100 < 146096 := by rw [hdmin_e]; omega
    have hr3 : r = 3 ↔ (yv + 1) % 4 = 0 := by dsimp [r]; omega
    have hk24 : c < 3 → (k = 24 ∧ r = 3 ↔ (yv + 1) % 100 = 0) := by
      intro _; dsimp [c, k, r]; omega
    have hmax_le : (if yv = 399 ∨ ((yv + 1) % 4 = 0 ∧ (yv + 1) % 100 ≠ 0) then 365 else 364) ≤ 365 := by
      split <;> omega
    have hdmin_1460 : (365 * yv + yv / 4 - yv / 100) / 1460 = 25 * c + k := by
      rw [hdmin_e]; omega
    have hdmin_36524 : (365 * yv + yv / 4 - yv / 100) / 36524 = c := by
      rw [hdmin_e]; omega
    have hdmin_146096 : (365 * yv + yv / 4 - yv / 100) / 146096 = 0 := by
      rw [hdmin_e]; omega
    rw [hdmin_1460, hdmin_36524, hdmin_146096]
    have hleft : (365 * yv + yv / 4 - yv / 100 - (25 * c + k) + c - 0) / 365 = yv := by
      rw [hdmin_e]; omega
    refine ⟨by rw [hdmin_e]; omega, ?_, hleft, ?_⟩
    · split <;> rw [hdmin_e] <;> omega
    · split
      · next hleap =>
        have hrr : r = 3 := hr3.mpr (hleap.elim (fun h => absurd h h399) (fun h => h.1))
        have hnot99 : ¬ (c < 3 ∧ k = 24) := by
          intro ⟨hc, hk⟩; have h100 := (hk24 hc).mp ⟨hk, hrr⟩; exact hleap.elim (fun h => absurd h h399) (fun h => absurd h100 h.2)
        have hdmax_1460 : (365 * yv + yv / 4 - yv / 100 + 365) / 1460 = 25 * c + k + 1 := by
          rw [hdmin_e, hrr]; omega
        have hdmax_36524 : (365 * yv + yv / 4 - yv / 100 + 365) / 36524 = c := by
          rw [hdmin_e, hrr]; omega
        have hdmax_146096 : (365 * yv + yv / 4 - yv / 100 + 365) / 146096 = 0 := by
          rw [hdmin_e, hrr]; omega
        rw [hdmax_1460, hdmax_36524, hdmax_146096, hdmin_e]; omega
      · next hnoleap =>
        have hdmax_36524 : (365 * yv + yv / 4 - yv / 100 + 364) / 36524 = c := by
          rw [hdmin_e]; omega
        have hdmax_146096 : (365 * yv + yv / 4 - yv / 100 + 364) / 146096 = 0 := by
          rw [hdmin_e]; omega
        rw [hdmax_36524, hdmax_146096]
        by_cases hd1460 : 24 * c + k + 365 * r + 364 ≥ 1460
        · have hdmax_1460 : (365 * yv + yv / 4 - yv / 100 + 364) / 1460 = 25 * c + k + 1 := by
            rw [hdmin_e]; omega
          rw [hdmax_1460, hdmin_e]; omega
        · have hdmax_1460 : (365 * yv + yv / 4 - yv / 100 + 364) / 1460 = 25 * c + k := by
            rw [hdmin_e]; omega
          rw [hdmax_1460, hdmin_e]; omega

/-- Calendar/Hinnant proof helper `hinnant_doe_bounds`. -/
theorem hinnant_doe_bounds (yoe doy : Int) (hy0 : 0 ≤ yoe) (hy1 : yoe ≤ 399)
    (hd0 : 0 ≤ doy) (hd1 : doy ≤ 365)
    (hleap : doy = 365 → (yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0))) :
    let doe := 365 * yoe + yoe / 4 - yoe / 100 + doy
    0 ≤ doe ∧ doe ≤ 146096 ∧
      (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 = yoe := by
  dsimp
  have hfin := hinnant_yoe_bounds_alg yoe hy0 hy1
  dsimp at hfin
  have hdoyMax : doy ≤ if yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0) then 365 else 364 := by
    by_cases hcond : yoe = 399 ∨ (yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0
    · simp [hcond, hd1]
    · simp only [hcond, ↓reduceIte]
      by_cases hgt : doy = 365
      · exact absurd (hleap hgt) hcond
      · omega
  have hmono1 := hinnantF_mono hfin.1
    (by omega : 365 * yoe + yoe / 4 - yoe / 100 ≤ 365 * yoe + yoe / 4 - yoe / 100 + doy)
    (by omega)
  have hmono2 := hinnantF_mono (by omega : 0 ≤ 365 * yoe + yoe / 4 - yoe / 100 + doy)
    (by omega) hfin.2.1
  change _ ∧ _ ∧ hinnantF (365 * yoe + yoe / 4 - yoe / 100 + doy) / 365 = yoe
  omega

/-- Calendar/Hinnant proof helper `plainDate_ext`. -/
theorem plainDate_ext {a b : PlainDate}
    (hy : a.year = b.year) (hm : a.month = b.month) (hd : a.day = b.day) : a = b := by
  cases a; cases b; simp only at hy hm hd; subst hy; subst hm; subst hd; rfl

/-- Calendar/Hinnant proof helper `month_clip_eq`. -/
theorem month_clip_eq {m : Int} (hm : 1 ≤ m ∧ m ≤ 12) :
    (Internal.Bounded.LE.clip m (by decide) : Month.Ordinal).val = m := by
  simp [Internal.Bounded.LE.clip, hm.1, hm.2]

/-- Calendar/Hinnant proof helper `day_clip_eq`. -/
theorem day_clip_eq {d : Int} (hd : 1 ≤ d ∧ d ≤ 31) :
    (Internal.Bounded.LE.clip d (by decide) : Day.Ordinal).val = d := by
  simp [Internal.Bounded.LE.clip, hd.1, hd.2]

/-- Calendar/Hinnant proof helper `clipDay_of_le`. -/
theorem clipDay_of_le {leap : Bool} {m : Month.Ordinal} {d : Day.Ordinal}
    (h : d ≤ Month.Ordinal.days leap m) :
    m.clipDay leap d = d := by
  change d.val ≤ (Month.Ordinal.days leap m).val at h
  simp only [Month.Ordinal.clipDay]
  split
  · next hgt => exact absurd h (by omega)
  · rfl

/-- Calendar/Hinnant proof helper `month_day_doy_roundtrip`. -/
theorem month_day_doy_roundtrip (m d : Int) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hdMax : d ≤ if m = 2 then 29 else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31) :
    let doy := (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1
    let mp := (5 * doy + 2) / 153
    let d' := doy - (153 * mp + 2) / 5 + 1
    let m' := mp + if mp < 10 then 3 else -9
    0 ≤ doy ∧ doy ≤ 365 ∧ (doy = 365 → m = 2 ∧ d = 29) ∧ m' = m ∧ d' = d := by
  dsimp
  have h12 : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨
      m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases h12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Calendar/formatting proof helper `ofEpochDay_toEpochDay`. -/
theorem ofEpochDay_toEpochDay (date : PlainDate) :
    PlainDate.ofEpochDay date.toEpochDay = date := by
  have hm := date.month.property
  have hvalid := date.valid
  have hd_prop := date.day.property
  have hdays := days_val_eq date.year.isLeap date.month
  have hdMax : date.day.val ≤ if date.month.val = 2 then 29
      else if date.month.val = 4 ∨ date.month.val = 6 ∨ date.month.val = 9 ∨ date.month.val = 11 then 30 else 31 := by
    change date.day.val ≤ (Month.Ordinal.days date.year.isLeap date.month).val at hvalid
    rw [hdays] at hvalid
    by_cases hm2 : date.month.val = 2 <;> simp_all <;> cases date.year.isLeap <;> omega
  dsimp [PlainDate.ofEpochDay, PlainDate.toEpochDay]
  change let y : Int := if date.month.val > 2 then date.year.toInt else date.year.toInt - 1
    let era := (if y ≥ 0 then y else y - 399).tdiv 400
    let yoe := y - era * 400
    let m := date.month.val
    let d := date.day.val
    let doy := (153 * (m + if m > 2 then -3 else 9) + 2).tdiv 5 + d - 1
    let doe := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
    let z := (Day.Offset.ofInt (era * 146097 + doe - 719468)).toInt + 719468
    let era' := (if z ≥ 0 then z else z - 146096).tdiv 146097
    let doe' := z - era' * 146097
    let yoe' := (doe' - doe'.tdiv 1460 + doe'.tdiv 36524 - doe'.tdiv 146096).tdiv 365
    let y' := yoe' + era' * 400
    let doy' := doe' - (365 * yoe' + yoe'.tdiv 4 - yoe'.tdiv 100)
    let mp := (5 * doy' + 2).tdiv 153
    let d' := doy' - (153 * mp + 2).tdiv 5 + 1
    let m' := mp + if mp < 10 then 3 else -9
    let y'' := y' + if m' ≤ 2 then 1 else 0
    PlainDate.ofYearMonthDayClip y'' (Internal.Bounded.LE.clip m' (by decide) : Month.Ordinal)
      (Internal.Bounded.LE.clip d' (by decide) : Day.Ordinal) = date
  intro y era yoe m d doy doe z era' doe' yoe' y' doy' mp d' m' y''
  have hyb := era_yoe_bounds y
  have hyoe0 : 0 ≤ yoe := hyb.1
  have hyoe1 : yoe ≤ 399 := hyb.2
  have hdoy_tdiv : (153 * (m + if m > 2 then -3 else 9) + 2).tdiv 5 =
      (153 * (m + if m > 2 then -3 else 9) + 2) / 5 :=
    Int.tdiv_eq_ediv_of_nonneg (by by_cases h : m > 2 <;> simp [h] <;> omega)
  have hmd := month_day_doy_roundtrip m d hm.1 hm.2 hd_prop.1 hdMax
  have hdoy_eq : doy = (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 := by
    dsimp [doy]; rw [hdoy_tdiv]
  have hdoy0 : 0 ≤ doy := by omega
  have hdoy1 : doy ≤ 365 := by omega
  have hyoe_t4 : yoe.tdiv 4 = yoe / 4 := Int.tdiv_eq_ediv_of_nonneg hyoe0
  have hyoe_t100 : yoe.tdiv 100 = yoe / 100 := Int.tdiv_eq_ediv_of_nonneg hyoe0
  have hdoe_eq : doe = 365 * yoe + yoe / 4 - yoe / 100 + doy := by
    dsimp [doe]; rw [hyoe_t4, hyoe_t100]; omega
  have hleap_doy : doy = 365 → yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0) := by
    intro h365
    have ⟨hm2, hd29⟩ := hmd.2.2.1 (by omega)
    have hm_val : date.month.val = 2 := hm2
    have hle : date.year.isLeap = true := by
      change date.day.val ≤ (Month.Ordinal.days date.year.isLeap date.month).val at hvalid
      rw [hdays] at hvalid
      simp [hm_val] at hvalid
      dsimp [d] at hd29
      cases hlp : date.year.isLeap
      · simp [hlp] at hvalid; omega
      · rfl
    have hy_sub : y = date.year.toInt - 1 := by simp [y, hm_val]
    have hyear_eq : date.year = Year.Offset.ofInt (yoe + 1 + era * 400) := by
      change date.year.toInt = yoe + 1 + era * 400
      dsimp [yoe]; omega
    rw [hyear_eq, isLeap_yoe_plus1 era yoe hyoe0 hyoe1] at hle
    exact decide_eq_true_iff.mp hle
  have hhb := hinnant_doe_bounds yoe doy hyoe0 hyoe1 hdoy0 hdoy1 hleap_doy
  dsimp only at hhb
  rw [← hdoe_eq] at hhb
  have hdoe0 : 0 ≤ doe := by omega
  have hdoe1 : doe ≤ 146096 := by omega
  have hz_eq : z = era * 146097 + doe := by
    change (era * 146097 + doe - 719468) + 719468 = era * 146097 + doe
    omega
  have hera' : era' = era := by
    dsimp [era']
    rw [hz_eq]
    by_cases hz : era * 146097 + doe ≥ 0
    · have ht : (era * 146097 + doe).tdiv 146097 = (era * 146097 + doe) / 146097 :=
        Int.tdiv_eq_ediv_of_nonneg (by omega)
      simp only [hz, ↓reduceIte, ht]
      omega
    · have hneg : era * 146097 + doe - 146096 ≤ 0 := by omega
      have ht := tmod_bounds_neg (era * 146097 + doe - 146096) 146097 hneg (by decide)
      have hmul := Int.mul_tdiv_add_tmod (era * 146097 + doe - 146096) 146097
      simp only [hz, ↓reduceIte]
      omega
  have hdoe' : doe' = doe := by dsimp [doe']; rw [hz_eq, hera']; omega
  have hyoe' : yoe' = yoe := by
    dsimp [yoe']
    rw [hdoe']
    rw [Int.tdiv_eq_ediv_of_nonneg hdoe0, Int.tdiv_eq_ediv_of_nonneg hdoe0,
      Int.tdiv_eq_ediv_of_nonneg hdoe0]
    have hnum_nonneg : 0 ≤ doe - doe / 1460 + doe / 36524 - doe / 146096 := by omega
    rw [Int.tdiv_eq_ediv_of_nonneg hnum_nonneg]
    exact hhb.2.2
  have hdoy' : doy' = doy := by
    dsimp [doy']
    rw [hdoe', hyoe', Int.tdiv_eq_ediv_of_nonneg hyoe0, Int.tdiv_eq_ediv_of_nonneg hyoe0]
    omega
  have hmp_nonneg : 0 ≤ 5 * doy' + 2 := by omega
  have hdoy'_t153 : (5 * doy' + 2).tdiv 153 = (5 * doy' + 2) / 153 :=
    Int.tdiv_eq_ediv_of_nonneg hmp_nonneg
  have hmp_eq : mp = (5 * doy + 2) / 153 := by dsimp [mp]; rw [hdoy'_t153, hdoy']
  have hmp_nonneg2 : 0 ≤ 153 * mp + 2 := by omega
  dsimp only at hmd
  rw [← hdoy_eq] at hmd
  have hd'_eq : d' = d := by
    dsimp [d']
    rw [Int.tdiv_eq_ediv_of_nonneg hmp_nonneg2, hmp_eq, hdoy']
    exact hmd.2.2.2.2
  have hm'_eq : m' = m := by
    dsimp [m']
    rw [hmp_eq]
    exact hmd.2.2.2.1
  have hy''_eq : y'' = date.year.toInt := by
    dsimp [y'', y', yoe]
    rw [hyoe', hera', hm'_eq]
    by_cases hmgt : date.month.val > 2
    · have hle : ¬ (m ≤ 2) := by dsimp [m]; omega
      simp [hle]; omega
    · have hle : m ≤ 2 := by dsimp [m]; omega
      simp [hle]; omega
  apply plainDate_ext
  · exact hy''_eq
  · apply Subtype.ext
    change (Internal.Bounded.LE.clip m' (by decide) : Month.Ordinal).val = date.month.val
    rw [hm'_eq, month_clip_eq hm]
  · dsimp [PlainDate.ofYearMonthDayClip]
    have hyear_match : (Year.Offset.ofInt y'') = date.year := hy''_eq
    have hmonth_match : (Internal.Bounded.LE.clip m' (by decide) : Month.Ordinal) = date.month := by
      apply Subtype.ext; rw [hm'_eq]; exact month_clip_eq hm
    have hday_match : (Internal.Bounded.LE.clip d' (by decide) : Day.Ordinal) = date.day := by
      apply Subtype.ext; rw [hd'_eq]; exact day_clip_eq hd_prop
    change Month.Ordinal.clipDay (Year.Offset.ofInt y'').isLeap
      (Internal.Bounded.LE.clip m' (by decide) : Month.Ordinal)
      (Internal.Bounded.LE.clip d' (by decide) : Day.Ordinal) = date.day
    rw [hyear_match, hmonth_match, hday_match]
    exact clipDay_of_le date.valid

/-- Epoch base proof helper `hinnant_yoe_bounds`. -/
theorem hinnant_yoe_bounds (yv : Int) (hy0 : 0 ≤ yv) (hy1 : yv ≤ 399) :
    let dmin := 365 * yv + yv / 4 - yv / 100
    let maxDoy : Int := if yv = 399 ∨ ((yv + 1) % 4 = 0 ∧ (yv + 1) % 100 ≠ 0) then 365 else 364
    let dmax := dmin + maxDoy
    0 ≤ dmin ∧ dmax ≤ 146096 ∧ hinnantF dmin / 365 = yv ∧ hinnantF dmax / 365 = yv :=
  hinnant_yoe_bounds_alg yv hy0 hy1

/-- Epoch base proof helper `hinnant_prev_dmax`. -/
theorem hinnant_prev_dmax (yoe doe : Int) (hy1 : 1 ≤ yoe) (hy2 : yoe ≤ 399)
    (hdoe0 : 0 ≤ doe) (hdlt : doe < 365 * yoe + yoe / 4 - yoe / 100) :
    hinnantF doe / 365 ≤ yoe - 1 := by
  have hfn := hinnant_yoe_bounds_alg (yoe - 1) (by omega) (by omega)
  dsimp only at hfn
  have hneq : ¬ (yoe - 1 = 399) := by omega
  have hdm : doe ≤ 365 * (yoe - 1) + (yoe - 1) / 4 - (yoe - 1) / 100 +
      if yoe - 1 = 399 ∨ ((yoe - 1 + 1) % 4 = 0 ∧ (yoe - 1 + 1) % 100 ≠ 0) then 365 else 364 := by
    simp only [hneq, false_or]
    split <;> omega
  have hmono := hinnantF_mono hdoe0 hdm (by omega)
  have hdiv := Int.ediv_le_ediv (by decide : (0 : Int) < 365) hmono
  omega

/-- Epoch base proof helper `doy_upper_of_lt`. -/
theorem doy_upper_of_lt (yoe doe : Int) (hy0 : 0 ≤ yoe) (hy1 : yoe < 399)
    (hlt : doe < 365 * (yoe + 1) + (yoe + 1) / 4 - (yoe + 1) / 100) :
    doe - (365 * yoe + yoe / 4 - yoe / 100) ≤
      if yoe = 399 ∨ ((yoe + 1) % 4 = 0 ∧ (yoe + 1) % 100 ≠ 0) then 365 else 364 := by
  have hneq : ¬ (yoe = 399) := by omega
  simp only [hneq, false_or]
  split <;> omega

/-- Epoch base proof helper `doy_mp_back`. -/
theorem doy_mp_back (doy : Int) (h0 : 0 ≤ doy) (h1 : doy ≤ 365) :
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := mp + if mp < 10 then 3 else -9
    doy = (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 := by
  intro mp d m
  have h12 : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨
      mp = 6 ∨ mp = 7 ∨ mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [m, d, h] <;> omega

/-- Epoch base proof helper `doy_day_valid`. -/
theorem doy_day_valid (doy : Int) (leapFeb29 : Bool) (h0 : 0 ≤ doy) (h1 : doy ≤ 365)
    (hfeb : doy = 365 → leapFeb29 = true) :
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := mp + if mp < 10 then 3 else -9
    d ≤ if m = 2 then (if leapFeb29 then 29 else 28)
      else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31 := by
  intro mp d m
  have h12 : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨
      mp = 6 ∨ mp = 7 ∨ mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · simp [m, d, h]; omega
  · have hm2 : m = 2 := by dsimp [m]; omega
    rw [hm2]
    simp only [↓reduceIte]
    cases hlb : leapFeb29 with
    | true => simp; omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hlt : doy < 365 := Classical.byContradiction fun hge => by
        have htr := hfeb (by omega)
        rw [hlb] at htr
        cases htr
      omega

end LeanSwe.Time.Proofs

import LeanSwe.Time.Interface
import LeanSweProofs.Time.Proofs.EpochBaseProofs

namespace LeanSwe.Time.Proofs

open Std.Time

private theorem doy_of_month_le2 (m d : Int) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) (_hd1 : 1 ≤ d) (_hd2 : d ≤ 31) :
    (m = 1 → (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 = 305 + d) ∧
    (m = 2 → (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 = 336 + d) := by
  constructor <;> intro hm <;> subst hm <;> simp <;> omega

private theorem doy_gt2_bounds (m d : Int) (hm1 : 3 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d) (hd2 : d ≤ 31) :
    (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1 ≤ 305 := by
  have hm_eq : (if m > 2 then (-3 : Int) else 9) = -3 := by simp [show m > 2 by omega]
  rw [hm_eq]
  have h10 : m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases h10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem doy_gt2_lt (m1 d1 m2 d2 : Int) (hm1 : 3 ≤ m1) (hlt : m1 < m2) (hm2 : m2 ≤ 12)
    (hd1 : d1 ≤ if m1 = 4 ∨ m1 = 6 ∨ m1 = 9 ∨ m1 = 11 then 30 else 31) (hd2 : 1 ≤ d2) :
    (153 * (m1 + if m1 > 2 then -3 else 9) + 2) / 5 + d1 - 1 <
      (153 * (m2 + if m2 > 2 then -3 else 9) + 2) / 5 + d2 - 1 := by
  simp only [show m1 > 2 by omega, show m2 > 2 by omega, ↓reduceIte]
  have hstep : ∀ k : Int, (3 ≤ k ∧ k ≤ 11) →
      (153 * (k - 3) + 2) / 5 + (if k = 4 ∨ k = 6 ∨ k = 9 ∨ k = 11 then 30 else 31) - 1 <
        (153 * (k + 1 - 3) + 2) / 5 + 1 - 1 := by
    intro k hk
    rcases (by omega : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hmono : ∀ a b : Int, 3 ≤ a → a ≤ b → b ≤ 12 →
      (153 * (a - 3) + 2) / 5 ≤ (153 * (b - 3) + 2) / 5 := by
    intro a b ha hab hb
    omega
  have hs := hstep m1 (by omega)
  have hm := hmono (m1 + 1) m2 (by omega) (by omega) hm2
  omega

private theorem doy_of_month_valid_bounds (m d : Int) (leap : Bool)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hvalid : d ≤ if m = 2 then (if leap then 29 else 28)
      else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31) :
    let doy := (153 * (m + if m > 2 then -3 else 9) + 2) / 5 + d - 1
    0 ≤ doy ∧ doy ≤ 365 ∧ (doy = 365 → m = 2 ∧ leap = true) := by
  have hdMax : d ≤ if m = 2 then 29 else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31 := by
    by_cases hm2' : m = 2
    · subst hm2'; cases leap <;> simp at hvalid <;> simp <;> omega
    · simp [hm2'] at hvalid ⊢; exact hvalid
  have hmd := month_day_doy_roundtrip m d hm1 hm2 hd1 hdMax
  dsimp at hmd ⊢
  refine ⟨hmd.1, hmd.2.1, ?_⟩
  intro h365
  have ⟨hm2', _hd29⟩ := hmd.2.2.1 h365
  refine ⟨hm2', ?_⟩
  subst hm2'
  cases leap
  · simp at hvalid; omega
  · rfl

private theorem ordering_then_eq_lt (a b : Ordering) (h : a.then b = .lt) :
    a = .lt ∨ (a = .eq ∧ b = .lt) := by
  cases a <;> cases b <;> simp [Ordering.then] at h ⊢

private theorem plainDate_epoch_lt_core
    (ay am ad by_ bm bd ya era_a yoe_a doya yb era_b yoe_b doyb : Int)
    (h_cmp_split : ay < by_ ∨ (ay = by_ ∧ (am < bm ∨ (am = bm ∧ ad < bd))))
    (hm_a : 1 ≤ am ∧ am ≤ 12) (hd_a : 1 ≤ ad ∧ ad ≤ 31)
    (hm_b : 1 ≤ bm ∧ bm ≤ 12) (hd_b : 1 ≤ bd ∧ bd ≤ 31)
    (ha_val' : ad ≤ if am = 2 then 29 else if am = 4 ∨ am = 6 ∨ am = 9 ∨ am = 11 then 30 else 31)
    (hya : ya = if am > 2 then ay else ay - 1)
    (hyb : yb = if bm > 2 then by_ else by_ - 1)
    (hera_a : era_a = (if ya ≥ 0 then ya else ya - 399).tdiv 400)
    (hyoe_a : yoe_a = ya - era_a * 400)
    (hera_b : era_b = (if yb ≥ 0 then yb else yb - 399).tdiv 400)
    (hyoe_b : yoe_b = yb - era_b * 400)
    (ha_y_b : 0 ≤ yoe_a ∧ yoe_a ≤ 399)
    (hb_y_b : 0 ≤ yoe_b ∧ yoe_b ≤ 399)
    (hdoya : doya = (153 * (am + if am > 2 then -3 else 9) + 2) / 5 + ad - 1)
    (hdoyb : doyb = (153 * (bm + if bm > 2 then -3 else 9) + 2) / 5 + bd - 1)
    (hdo_a : 0 ≤ doya ∧ doya ≤ 365)
    (hdo_b : 0 ≤ doyb ∧ doyb ≤ 365)
    (h_no_leap_a : doya = 365 → (yoe_a = 399 ∨ ((yoe_a + 1) % 4 = 0 ∧ (yoe_a + 1) % 100 ≠ 0))) :
    era_a * 146097 + (365 * yoe_a + yoe_a / 4 - yoe_a / 100 + doya) - 719468 <
      era_b * 146097 + (365 * yoe_b + yoe_b / 4 - yoe_b / 100 + doyb) - 719468 := by
  rcases h_cmp_split with hy_lt | ⟨hy_eq', hmd_lt⟩
  · by_cases hsame : ya = yb
    · have ha3 : am > 2 := by
        rw [hya, hyb] at hsame
        by_cases h1 : am > 2 <;> by_cases h2 : bm > 2 <;> simp [h1, h2] at hsame <;> omega
      have hb2 : bm ≤ 2 := by
        rw [hya, hyb] at hsame
        by_cases h1 : am > 2 <;> by_cases h2 : bm > 2 <;> simp [h1, h2] at hsame <;> omega
      have ha_d := doy_gt2_bounds am ad (by omega) hm_a.2 hd_a.1 hd_a.2
      have hb_d := doy_of_month_le2 bm bd hm_b.1 hb2 hd_b.1 hd_b.2
      have hdoy_lt : doya < doyb := by
        have : 306 ≤ doyb := by
          rw [hdoyb]
          by_cases h1 : bm = 1
          · rw [hb_d.1 h1]; omega
          · rw [hb_d.2 (by omega)]; omega
        omega
      have hera_eq : era_a = era_b := by rw [hera_a, hera_b, hsame]
      have hyoe_eq : yoe_a = yoe_b := by rw [hyoe_a, hyoe_b, hsame, hera_eq]
      rw [hera_eq, hyoe_eq]; omega
    · have hy_le : ya < yb := Classical.byContradiction fun hge => by
        have hge' : yb < ya := by omega
        rw [hya, hyb] at hge'
        by_cases h1 : am > 2 <;> by_cases h2 : bm > 2 <;> simp [h1, h2] at hge' <;> omega
      by_cases hera_lt : era_a < era_b
      · have hmin_a : 0 ≤ 365 * yoe_a + yoe_a / 4 - yoe_a / 100 + doya := by omega
        have hmax_a : 365 * yoe_a + yoe_a / 4 - yoe_a / 100 + doya ≤ 146096 := by
          by_cases h365 : doya = 365
          · have := h_no_leap_a h365
            have hfn := hinnant_yoe_bounds yoe_a ha_y_b.1 ha_y_b.2
            dsimp at hfn; omega
          · have hfn := hinnant_yoe_bounds yoe_a ha_y_b.1 ha_y_b.2
            dsimp at hfn; split at hfn <;> omega
        have hmin_b : 0 ≤ 365 * yoe_b + yoe_b / 4 - yoe_b / 100 + doyb := by omega
        omega
      · have hera_eq : era_a = era_b := by omega
        have hyoe_lt : yoe_a < yoe_b := by omega
        by_cases h365 : doya = 365
        · have _hlp := h_no_leap_a h365
          rw [hera_eq]; omega
        · rw [hera_eq]; omega
  · rcases hmd_lt with hm_lt | ⟨hmv_eq, hdv_lt⟩
    · by_cases hsame : ya = yb
      · have hdoy_lt : doya < doyb := by
          by_cases ha2 : am ≤ 2
          · have hb2 : bm ≤ 2 := by
              rw [hya, hyb, hy_eq'] at hsame; split at hsame <;> split at hsame <;> omega
            have ha1 : am = 1 := by omega
            have hb2' : bm = 2 := by omega
            have ha_d := doy_of_month_le2 am ad hm_a.1 ha2 hd_a.1 hd_a.2
            have hb_d := doy_of_month_le2 bm bd hm_b.1 hb2 hd_b.1 hd_b.2
            rw [hdoya, hdoyb, ha_d.1 ha1, hb_d.2 hb2']
            omega
          · have ha_nd : ad ≤ if am = 4 ∨ am = 6 ∨ am = 9 ∨ am = 11 then 30 else 31 := by
              have hne2 : am ≠ 2 := by omega
              simp [hne2] at ha_val'; exact ha_val'
            rw [hdoya, hdoyb]
            exact doy_gt2_lt am ad bm bd (by omega) hm_lt hm_b.2 ha_nd hd_b.1
        have hera_eq : era_a = era_b := by rw [hera_a, hera_b, hsame]
        have hyoe_eq : yoe_a = yoe_b := by rw [hyoe_a, hyoe_b, hsame, hera_eq]
        rw [hera_eq, hyoe_eq]; omega
      · have ha2 : am ≤ 2 := by rw [hya, hyb, hy_eq'] at hsame; split at hsame <;> split at hsame <;> omega
        have hb3 : bm > 2 := by rw [hya, hyb, hy_eq'] at hsame; split at hsame <;> split at hsame <;> omega
        have hyb_eq : yb = ya + 1 := by
          rw [hya, hyb, hy_eq']
          simp [show ¬ am > 2 by omega, hb3]
        by_cases h399 : yoe_a = 399
        · have hera_b' : era_b = era_a + 1 := by
            have hyb2 : yb = (era_a + 1) * 400 := by omega
            rw [hera_b, hyb2]
            split
            · next hge => rw [Int.tdiv_eq_ediv_of_nonneg hge]; omega
            · next hlt =>
              have hb := tmod_bounds_neg ((era_a + 1) * 400 - 399) 400 (by omega) (by decide)
              have hm := Int.mul_tdiv_add_tmod ((era_a + 1) * 400 - 399) 400
              omega
          have hyoe_b' : yoe_b = 0 := by omega
          rw [hera_b', hyoe_b', h399]; omega
        · have hera_eq : era_a = era_b := by omega
          have hyoe_b' : yoe_b = yoe_a + 1 := by omega
          rw [hera_eq, hyoe_b']
          by_cases h365 : doya = 365
          · have _hlp := h_no_leap_a h365
            omega
          · omega
    · have hsame : ya = yb := by rw [hya, hyb, hy_eq', hmv_eq]
      have hera_eq : era_a = era_b := by rw [hera_a, hera_b, hsame]
      have hyoe_eq : yoe_a = yoe_b := by rw [hyoe_a, hyoe_b, hsame, hera_eq]
      have hdoy_lt : doya < doyb := by rw [hdoya, hdoyb, hmv_eq]; omega
      rw [hera_eq, hyoe_eq]; omega

/-- Calendar/formatting proof helper `plainDate_toEpochDay_lt_of_compare_lt`. -/
theorem plainDate_toEpochDay_lt_of_compare_lt {a b : PlainDate}
    (hlt : compare a b = .lt) : a.toEpochDay.val < b.toEpochDay.val := by
  rw [PlainDate.compare_def] at hlt
  dsimp [compareLex, compareOn] at hlt
  have hy_or := ordering_then_eq_lt _ _ hlt
  have h_cmp_split : a.year.toInt < b.year.toInt ∨
      (a.year.toInt = b.year.toInt ∧
        (a.month.val < b.month.val ∨ (a.month.val = b.month.val ∧ a.day.val < b.day.val))) := by
    rcases hy_or with hy | ⟨hy, hmd⟩
    · left; change compare (a.year : Int) (b.year : Int) = .lt at hy
      exact Int.compare_eq_lt.mp hy
    · right
      have hy_eq : a.year.toInt = b.year.toInt := by
        change compare (a.year : Int) (b.year : Int) = .eq at hy
        exact Int.compare_eq_eq.mp hy
      have hmd_or := ordering_then_eq_lt _ _ hmd
      refine ⟨hy_eq, ?_⟩
      rcases hmd_or with hm | ⟨hm, hd⟩
      · left; change compare a.month.val b.month.val = .lt at hm
        exact Int.compare_eq_lt.mp hm
      · right
        have hm_eq : a.month.val = b.month.val := by
          change compare a.month.val b.month.val = .eq at hm
          exact Int.compare_eq_eq.mp hm
        change compare a.day.val b.day.val = .lt at hd
        exact ⟨hm_eq, Int.compare_eq_lt.mp hd⟩
  have ha_y_b := era_yoe_bounds (if a.month.val > 2 then a.year.toInt else a.year.toInt - 1)
  let ya := (if a.month.val > 2 then a.year.toInt else a.year.toInt - 1)
  let era_a := (if ya ≥ 0 then ya else ya - 399).tdiv 400
  let yoe_a := ya - era_a * 400
  let yb := (if b.month.val > 2 then b.year.toInt else b.year.toInt - 1)
  let era_b := (if yb ≥ 0 then yb else yb - 399).tdiv 400
  let yoe_b := yb - era_b * 400
  have hb_y_b := era_yoe_bounds yb
  have h_epoch : ∀ d : PlainDate,
      let yd := if d.month.val > 2 then d.year.toInt else d.year.toInt - 1
      let erad := (if yd ≥ 0 then yd else yd - 399).tdiv 400
      let yoed := yd - erad * 400
      let doyd := (153 * (d.month.val + if d.month.val > 2 then -3 else 9) + 2) / 5 + d.day.val - 1
      d.toEpochDay.val = erad * 146097 + (365 * yoed + yoed / 4 - yoed / 100 + doyd) - 719468 := by
    intro d yd erad yoed doyd
    dsimp [PlainDate.toEpochDay]
    have _hm := d.month.property
    have hm_v : d.month.toInt = d.month.val := rfl
    have hd_v : d.day.toInt = d.day.val := rfl
    rw [hm_v, hd_v]
    have hb_d := era_yoe_bounds yd
    have ht5 : (153 * (d.month.val + if d.month.val > 2 then -3 else 9) + 2).tdiv 5 =
        (153 * (d.month.val + if d.month.val > 2 then -3 else 9) + 2) / 5 :=
      Int.tdiv_eq_ediv_of_nonneg (by by_cases h : d.month.val > 2 <;> simp [h] <;> omega)
    change (Day.Offset.ofInt ((erad * 146097 + (yoed * 365 + yoed.tdiv 4 - yoed.tdiv 100 + _)) - 719468)).val = _
    have ho : ∀ x : Int, (Day.Offset.ofInt x).val = x := fun _ => rfl
    rw [ho, Int.tdiv_eq_ediv_of_nonneg hb_d.1, Int.tdiv_eq_ediv_of_nonneg hb_d.1, ht5]
    omega
  have ha_ep := h_epoch a
  have hb_ep := h_epoch b
  dsimp at ha_ep hb_ep
  let doya := (153 * (a.month.val + if a.month.val > 2 then -3 else 9) + 2) / 5 + a.day.val - 1
  let doyb := (153 * (b.month.val + if b.month.val > 2 then -3 else 9) + 2) / 5 + b.day.val - 1
  have hm_a := a.month.property
  have hd_a := a.day.property
  have hm_b := b.month.property
  have hd_b := b.day.property
  have ha_val' : a.day.val ≤ if a.month.val = 2 then (if a.year.isLeap then 29 else 28)
      else if a.month.val = 4 ∨ a.month.val = 6 ∨ a.month.val = 9 ∨ a.month.val = 11 then 30 else 31 := by
    have hv := a.valid
    change a.day.val ≤ (Month.Ordinal.days a.year.isLeap a.month).val at hv
    rwa [days_val_eq] at hv
  have hb_val' : b.day.val ≤ if b.month.val = 2 then (if b.year.isLeap then 29 else 28)
      else if b.month.val = 4 ∨ b.month.val = 6 ∨ b.month.val = 9 ∨ b.month.val = 11 then 30 else 31 := by
    have hv := b.valid
    change b.day.val ≤ (Month.Ordinal.days b.year.isLeap b.month).val at hv
    rwa [days_val_eq] at hv
  have ha_val_max : a.day.val ≤ if a.month.val = 2 then 29
      else if a.month.val = 4 ∨ a.month.val = 6 ∨ a.month.val = 9 ∨ a.month.val = 11 then 30 else 31 := by
    by_cases hm2 : a.month.val = 2
    · simp only [hm2, ↓reduceIte] at ha_val' ⊢
      cases hl : a.year.isLeap <;> simp only [hl, ↓reduceIte] at ha_val' <;> omega
    · simp only [hm2, ↓reduceIte] at ha_val' ⊢; exact ha_val'
  have hda := doy_of_month_valid_bounds a.month.val a.day.val a.year.isLeap hm_a.1 hm_a.2 hd_a.1 ha_val'
  have hdb := doy_of_month_valid_bounds b.month.val b.day.val b.year.isLeap hm_b.1 hm_b.2 hd_b.1 hb_val'
  have h_no_leap_a : doya = 365 → (yoe_a = 399 ∨ ((yoe_a + 1) % 4 = 0 ∧ (yoe_a + 1) % 100 ≠ 0)) := by
    intro h365
    have ⟨hm2, hlp⟩ := hda.2.2 h365
    have hy_e : a.year = Year.Offset.ofInt (yoe_a + 1 + era_a * 400) := by
      change a.year.toInt = yoe_a + 1 + era_a * 400
      dsimp [yoe_a, ya]; simp [hm2]; omega
    rw [hy_e, isLeap_yoe_plus1 era_a yoe_a ha_y_b.1 ha_y_b.2] at hlp
    exact decide_eq_true_iff.mp hlp
  rw [ha_ep, hb_ep]
  exact plainDate_epoch_lt_core a.year.toInt a.month.val a.day.val b.year.toInt b.month.val b.day.val
    ya era_a yoe_a doya yb era_b yoe_b doyb
    h_cmp_split hm_a hd_a hm_b hd_b ha_val_max rfl rfl rfl rfl rfl rfl
    ha_y_b hb_y_b rfl rfl ⟨hda.1, hda.2.1⟩ ⟨hdb.1, hdb.2.1⟩ h_no_leap_a

end LeanSwe.Time.Proofs

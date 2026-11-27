import Core.Obeys
import LeanSwe.Time.Interface
import LeanSweProofs.Time.Model
import LeanSweProofs.Time.Model.Refines
import LeanSweProofs.Time.Proofs.EpochBaseProofs
import LeanSweProofs.Time.Proofs.HinnantProofs
import LeanSweProofs.Time.Proofs.HinnantRoundTripProofs
import LeanSweProofs.Time.Proofs.HinnantRangeProofs
import LeanSweProofs.Time.Proofs.CalendarProofs
import LeanSweProofs.Time.Proofs.FormatParseProofs
import LeanSweProofs.Time.Proofs.RefinesModel
import LeanSweProofs.Time.Proofs.RefinesWitness

/-!
# Verified Time & Calendar Specification Proofs

Top-level verification entry point exporting pure duration, timestamp, calendar,
and UTC ISO 8601 / `YYYY-MM-DD` round-trip theorems alongside `obeys_model` and
`obeys_model_nonvacuous`.
-/

namespace LeanSwe.Time.Proofs

open Core
open Std.Time
open LeanSwe.Time.Proofs.RefinesModel (toNanoseconds_ofNanoseconds toNanoseconds_inj)

private theorem toNanoseconds_neg (d : Duration) :
    d.neg.toNanoseconds.val = -d.toNanoseconds.val := by
  rcases d with ⟨⟨s⟩, ⟨n, _⟩, _⟩
  change (-s) * 1000000000 + (-n) = -(s * 1000000000 + n)
  omega

private theorem toNanoseconds_add (a b : Duration) :
    (a + b).toNanoseconds.val = a.toNanoseconds.val + b.toNanoseconds.val := by
  change (Duration.ofNanoseconds (a.toNanoseconds + b.toNanoseconds)).toNanoseconds.val = _
  rw [toNanoseconds_ofNanoseconds]
  rfl

private theorem toNanoseconds_sub (a b : Duration) :
    (a - b).toNanoseconds.val = a.toNanoseconds.val - b.toNanoseconds.val := by
  change (Duration.ofNanoseconds (a.toNanoseconds + b.neg.toNanoseconds)).toNanoseconds.val = _
  rw [toNanoseconds_ofNanoseconds]
  have h := toNanoseconds_neg b
  change a.toNanoseconds.val + b.neg.toNanoseconds.val = a.toNanoseconds.val - b.toNanoseconds.val
  omega

private theorem bounded_ediv_val {lo hi : Int} (b : Internal.Bounded.LE lo hi)
    (num : Int) (h : num > 0) :
    (b.ediv num h).val = b.val.ediv num := by
  rcases b with ⟨v, ⟨hl, hr⟩⟩
  simp [Internal.Bounded.LE.ediv]

/-- Adding and subtracting a `Duration` recovers the original `Duration`. -/
theorem duration_add_sub_inverse (d1 d2 : Duration) : (d1 + d2) - d2 = d1 := by
  apply toNanoseconds_inj
  apply Internal.UnitVal.ext
  rw [toNanoseconds_sub, toNanoseconds_add]
  omega

/-- Shifting a `Timestamp` by `d` and subtracting `d` recovers `t`, and taking the difference recovers `d`. -/
theorem timestamp_add_sub_inverse (t : Timestamp) (d : Duration) :
    (t + d) - d = t ∧ (t + d) - t = d := by
  constructor
  · apply Timestamp.ext
    apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    change ((t.val + d) - d).toNanoseconds.val = t.val.toNanoseconds.val
    rw [toNanoseconds_sub, toNanoseconds_add]
    omega
  · apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    change ((t.val + d) - t.val).toNanoseconds.val = d.toNanoseconds.val
    rw [toNanoseconds_sub, toNanoseconds_add]
    omega

/-- `Millisecond.Offset` round-trips through `Duration.ofMillisecond` and `Duration.toMilliseconds`. -/
theorem toMilliseconds_ofMillisecond (ms : Millisecond.Offset) :
    (Duration.ofMillisecond ms).toMilliseconds = ms := by
  apply Internal.UnitVal.ext
  have hval : (Duration.ofMillisecond ms).toNanoseconds.val = ms.val * 1000000 := by
    change (Duration.ofNanoseconds ms.toNanoseconds).toNanoseconds.val = ms.val * 1000000
    rw [toNanoseconds_ofNanoseconds]
    rfl
  generalize Duration.ofMillisecond ms = d at hval ⊢
  rcases d with ⟨sec, nsec, hsign⟩
  change sec.val * 1000000000 + nsec.val = ms.val * 1000000 at hval
  have hed_val : (nsec.ediv 1000000 (by decide)).val = nsec.val.ediv 1000000 :=
    bounded_ediv_val nsec 1000000 (by decide)
  have hmsec : (Duration.mk sec nsec hsign).toMilliseconds.val =
      sec.val * 1000 + nsec.val.ediv 1000000 :=
    Eq.trans
      (rfl : (Duration.mk sec nsec hsign).toMilliseconds.val =
        sec.val * 1000 + (nsec.ediv 1000000 (by decide)).val)
      (congrArg (sec.val * 1000 + ·) hed_val)
  refine Eq.trans hmsec ?_
  have hdiv : nsec.val.ediv 1000000 = nsec.val / 1000000 := rfl
  have hed : 1000000 * (nsec.val / 1000000) + nsec.val % 1000000 = nsec.val :=
    Int.mul_ediv_add_emod nsec.val 1000000
  have hn' := nsec.property
  omega

/-- Every UTC timestamp in years `0000..9999` round-trips through `formatUtcIso8601` and `parseUtcIso8601`. -/
theorem utcIso8601_roundTrip (ts : Timestamp)
    (hbound : -62167219200000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
      ts.toNanosecondsSinceUnixEpoch.val ≤ 253402300799999999999) :
    LeanSwe.Time.parseUtcIso8601 (LeanSwe.Time.formatUtcIso8601 ts) = .ok ts := by
  change Internal.parseUtcIso8601 (Internal.formatUtcIso8601 ts) = .ok ts
  dsimp [Internal.formatUtcIso8601, Internal.utcSplitTimestamp]
  let ns := ts.toNanosecondsSinceUnixEpoch.val
  let sec := ns.ediv 1000000000
  let nano := (ns.emod 1000000000).toNat
  let day := sec.ediv 86400
  let sod := (sec.emod 86400).toNat
  have hns_b : -62167219200000000000 ≤ ns ∧ ns ≤ 253402300799999999999 := hbound
  have hday_e : day = (ns / 1000000000) / 86400 := rfl
  have hday_lo : -719528 ≤ day := by rw [hday_e]; omega
  have hday_hi : day ≤ 2932896 := by rw [hday_e]; omega
  have hy_range := ofEpochDay_year_range (Day.Offset.ofInt day) hday_lo hday_hi
  dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind]
  rw [String.toList_ofList]
  simp only [List.append_assoc, List.cons_append]
  rw [parseDateHead_formatUtcDateChars _ hy_range.1 hy_range.2]
  dsimp [Internal.pop1?]
  have hsod_e : sod = ((ns / 1000000000) % 86400).toNat := rfl
  have hsod_b : sod < 86400 := by rw [hsod_e]; omega
  rw [popTwoDigitsNat?_twoDigitsChars (sod / 3600) (by omega)]
  dsimp [Internal.pop1?]
  rw [popTwoDigitsNat?_twoDigitsChars ((sod % 3600) / 60) (by omega)]
  dsimp [Internal.pop1?]
  rw [popTwoDigitsNat?_twoDigitsChars (sod % 60) (by omega)]
  dsimp
  have hrange_ok : (sod / 3600 ≤ 23 && (sod % 3600) / 60 ≤ 59 && sod % 60 ≤ 59) = true := by
    simp [show sod / 3600 ≤ 23 by omega, show (sod % 3600) / 60 ≤ 59 by omega, show sod % 60 ≤ 59 by omega]
  simp only [hrange_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [splitLeadingDigits_nineDigitsChars nano ['Z'] (by decide)]
  dsimp
  have hlen : (Internal.nineDigitsChars nano).isEmpty = false ∧ (Internal.nineDigitsChars nano).length ≤ 9 := by
    simp [Internal.nineDigitsChars]
  have hflag : ((Internal.nineDigitsChars nano).isEmpty || decide ((Internal.nineDigitsChars nano).length > 9)) = false := by
    simp [hlen.1, hlen.2]
  simp only [hflag, Bool.false_eq_true, ↓reduceIte]
  have hnano_e : nano = (ns % 1000000000).toNat := rfl
  have hnano_b : nano < 1000000000 := by rw [hnano_e]; omega
  rw [fracDigitsToNanos9_nineDigitsChars nano hnano_b]
  have hoff : Internal.parseOffsetSeconds ['Z'] = .ok 0 := by
    dsimp [Internal.parseOffsetSeconds, Internal.pop1?, List.isEmpty]
  rw [hoff]
  dsimp
  rw [toEpochDay_ofEpochDay (Day.Offset.ofInt day)]
  congr 1
  apply Timestamp.ext
  apply toNanoseconds_inj
  apply Internal.UnitVal.ext
  change (Duration.ofNanoseconds (Nanosecond.Offset.ofInt (((Day.Offset.ofInt day).val * 86400 +
      Int.ofNat (sod / 3600 * 3600 + (sod % 3600) / 60 * 60 + sod % 60) - 0) * 1000000000 +
      Int.ofNat nano))).toNanoseconds.val = ts.toNanosecondsSinceUnixEpoch.val
  rw [toNanoseconds_ofNanoseconds]
  change ((Day.Offset.ofInt day).val * 86400 +
      Int.ofNat (sod / 3600 * 3600 + (sod % 3600) / 60 * 60 + sod % 60) - 0) * 1000000000 +
      Int.ofNat nano = ts.toNanosecondsSinceUnixEpoch.val
  have hday_v : (Day.Offset.ofInt day).val = day := rfl
  rw [hday_v, hday_e, hsod_e, hnano_e]
  dsimp [ns]
  omega

/-- Every `PlainDate` in years `0000..9999` round-trips through `formatUtcDate` and `parseUtcDate`. -/
theorem utcDate_roundTrip (d : PlainDate)
    (hbound : 0 ≤ d.year.toInt ∧ d.year.toInt ≤ 9999) :
    LeanSwe.Time.parseUtcDate (LeanSwe.Time.formatUtcDate d) = .ok d := by
  change Internal.parseUtcDate (Internal.formatUtcDate d) = .ok d
  dsimp [Internal.formatUtcDate, Internal.parseUtcDate, Bind.bind, Except.bind]
  rw [String.toList_ofList]
  have h1 := parseDateHead_formatUtcDateChars d hbound.1 hbound.2 []
  rw [List.append_nil] at h1
  rw [h1]

/-- Every `PlainDate` round-trips through UTC midnight `timestampOfUtcDate` / `utcDateOfTimestamp`,
    and subtracting 1 nanosecond crosses into the strictly earlier calendar day. -/
theorem utcDate_timestamp_roundTrip (d : PlainDate) :
    LeanSwe.Time.utcDateOfTimestamp (LeanSwe.Time.timestampOfUtcDate d) = d ∧
    compare (LeanSwe.Time.utcDateOfTimestamp (LeanSwe.Time.timestampOfUtcDate d - Duration.ofNanoseconds 1)) d = .lt := by
  constructor
  · change Internal.utcDateOfTimestamp (Internal.timestampOfUtcDate d) = d
    dsimp [Internal.timestampOfUtcDate, Internal.utcDateOfTimestamp, Internal.utcSplitTimestamp]
    have hdiv : ((d.toEpochDay.val * 86400000000000).ediv 1000000000).ediv 86400 = d.toEpochDay.val := by
      change ((d.toEpochDay.val * 86400000000000) / 1000000000) / 86400 = d.toEpochDay.val
      omega
    have hts : (Timestamp.ofNanosecondsSinceUnixEpoch
        (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).toNanosecondsSinceUnixEpoch.val =
        d.toEpochDay.val * 86400000000000 :=
      congrArg Internal.UnitVal.val
        (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)))
    rw [hts, hdiv]
    exact ofEpochDay_toEpochDay d
  · let x := PlainDate.ofEpochDay (Day.Offset.ofInt (d.toEpochDay.val - 1))
    have hprev : LeanSwe.Time.utcDateOfTimestamp
        (LeanSwe.Time.timestampOfUtcDate d - Duration.ofNanoseconds 1) = x := by
      change Internal.utcDateOfTimestamp (Internal.timestampOfUtcDate d - Duration.ofNanoseconds 1) = x
      dsimp [Internal.utcDateOfTimestamp, Internal.utcSplitTimestamp, Internal.timestampOfUtcDate]
      have hsub : (Timestamp.ofNanosecondsSinceUnixEpoch
          (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)) -
          Duration.ofNanoseconds 1).toNanosecondsSinceUnixEpoch.val =
          d.toEpochDay.val * 86400000000000 - 1 := by
        have h1 : (Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val.toNanoseconds.val =
            d.toEpochDay.val * 86400000000000 :=
          congrArg Internal.UnitVal.val
            (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)))
        have h2 : (Duration.ofNanoseconds 1).toNanoseconds.val = 1 := by decide
        have h3 := toNanoseconds_sub
          (Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val
          (Duration.ofNanoseconds 1)
        change ((Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val -
            Duration.ofNanoseconds 1).toNanoseconds.val = _
        rw [h3, h1, h2]
      rw [hsub]
      have hdiv : ((d.toEpochDay.val * 86400000000000 - 1).ediv 1000000000).ediv 86400 = d.toEpochDay.val - 1 := by
        change ((d.toEpochDay.val * 86400000000000 - 1) / 1000000000) / 86400 = d.toEpochDay.val - 1
        omega
      rw [hdiv]
    rw [hprev]
    have hx_ep : x.toEpochDay.val = d.toEpochDay.val - 1 := by
      dsimp [x]
      rw [toEpochDay_ofEpochDay]
      rfl
    cases hcmp : compare x d with
    | lt => rfl
    | eq =>
      have heq := Std.LawfulEqOrd.eq_of_compare hcmp
      rw [heq] at hx_ep
      omega
    | gt =>
      have hsw : compare d x = (compare x d).swap := Std.OrientedCmp.eq_swap
      have hlt : compare d x = .lt := by rw [hsw, hcmp]; rfl
      have hlt_ep := plainDate_toEpochDay_lt_of_compare_lt hlt
      omega

/-- Every error returned by `parseUtcIso8601` has kind `.invalidFormat` and non-empty message. -/
theorem parseUtcIso8601_err_nonEmpty (raw : String) {e : TimeError}
    (h : LeanSwe.Time.parseUtcIso8601 raw = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" :=
  parseUtcIso8601_err raw h

/-- Every error returned by `parseUtcDate` has kind `.invalidFormat` and non-empty message. -/
theorem parseUtcDate_err_nonEmpty (raw : String) {e : TimeError}
    (h : LeanSwe.Time.parseUtcDate raw = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" :=
  parseUtcDate_err raw h

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.Time` against `LeanSwe.Time.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq2 LeanSwe.Time.elapsedDuration Model.elapsedDuration ∧
    Core.ObeysPureEq2 LeanSwe.Time.deadlineNanos Model.deadlineNanos ∧
    Core.ObeysPureEq2 LeanSwe.Time.isMonoExpired Model.isMonoExpired ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcIso8601 Model.formatUtcIso8601 ∧
    Core.ObeysPureEq LeanSwe.Time.parseUtcIso8601 Model.parseUtcIso8601 ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcCompact Model.formatUtcCompact ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcDate Model.formatUtcDate ∧
    Core.ObeysPureEq LeanSwe.Time.parseUtcDate Model.parseUtcDate ∧
    Core.ObeysPureEq LeanSwe.Time.utcDateOfTimestamp Model.utcDateOfTimestamp ∧
    Core.ObeysPureEq LeanSwe.Time.timestampOfUtcDate Model.timestampOfUtcDate ∧
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkTimeOps Model.execTimeOpsStep Model.allowedTimeOpsStep ∧
    Core.ObeysStepFromFinally id Model.pkgWf Model.execTimeOpsStep Model.allowedTimeOpsStep
      Model.pkgWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  LeanSwe.Time.Proofs.RefinesModel.refines_model_impl

/-- Concrete non-vacuity witness instantiating `obeys_model` over `RefinesModel.refRawOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStep Model.toModelState Model.pkgWf
      (Model.execPkgStep (Internal.mkApiM (Internal.mkTimeOps RefinesModel.refRawOps)))
      Model.allowedPkgStep :=
  obeys_model.2.2.2.2.2.2.2.2.2.2.2 Model.toModelState (Internal.mkTimeOps RefinesModel.refRawOps)
    (obeys_model.2.2.2.2.2.2.2.2.2.2.1 id RefinesModel.refRawOps RefinesModel.refRawOps_obeys_model)

end LeanSwe.Time.Proofs

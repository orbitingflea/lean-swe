import Core.Obeys
import LeanSwe.Time.Model
import LeanSwe.Time.Model.Refines
import LeanSwe.Time.Interface

/-!
# `TimeRand` Raw-Step Helpers for `LeanSwe.Time`

Helper lemmas extracting `TimeModelState` postconditions for `clock_gettime` and
`clock_nanosleep` under `LeanSwe.Time.Model.allowedRawStep`, plus `Timespec`
and `Duration` nanosecond conversion lemmas.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.LinuxSyscall.TimeRand
  (Timespec TimeRandOpsM NSEC_PER_SEC MIN_TIMESPEC_SEC_INT MAX_TIMESPEC_SEC
   MAX_TIMESPEC_NANOS execTimeRandReq)
open LeanSwe.Time

/-- Conversion of `Nanosecond.Offset` round-trips through `Duration.ofNanoseconds`. -/
theorem toNanoseconds_ofNanoseconds (n : Nanosecond.Offset) :
    (Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

/-- `Duration.toNanoseconds` is injective. -/
theorem toNanoseconds_inj {a b : Duration} (h : a.toNanoseconds = b.toNanoseconds) : a = b := by
  have hv : a.toNanoseconds.val = b.toNanoseconds.val := congrArg Internal.UnitVal.val h
  rcases a with ⟨⟨sa⟩, ⟨na, hna⟩, hsa⟩
  rcases b with ⟨⟨sb⟩, ⟨nb, hnb⟩, hsb⟩
  dsimp only at hna hnb hsa hsb
  change sa * 1000000000 + na = sb * 1000000000 + nb at hv
  have hs : sa = sb := by omega
  have hn : na = nb := by omega
  subst hs hn
  rfl

/-- Small `Nat` values round-trip through `Int64.ofInt` without wraparound. -/
theorem int64_toInt_ofNat (n : Nat) (hn : n < 2 ^ 63) :
    (Int64.ofInt (n : Int)).toInt = (n : Int) := by
  rw [Int64.toInt_ofInt]
  have hn' : n < 9223372036854775808 := hn
  have h1 : (n : Int) < (9223372036854775808 : Int) := Int.ofNat_lt.mpr hn'
  change (if (n : Int) % (18446744073709551616 : Int) < (9223372036854775808 : Int) then
      (n : Int) % (18446744073709551616 : Int)
    else (n : Int) % (18446744073709551616 : Int) - (18446744073709551616 : Int)) = (n : Int)
  have hm : (n : Int) % (18446744073709551616 : Int) = (n : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega)
  rw [hm]
  simp [h1]

/-- Signed `Int` values in `[-2^63, 2^63 - 1]` round-trip through `Int64.ofInt`. -/
theorem int64_toInt_ofInt_range (z : Int)
    (hlo : (-9223372036854775808 : Int) ≤ z) (hhi : z ≤ 9223372036854775807) :
    (Int64.ofInt z).toInt = z := by
  rw [Int64.toInt_ofInt, Int.bmod_eq_of_le] <;> simp only [Int64.size] <;> omega

/-- Signed `Int64.toInt` bounds matching `MIN_TIMESPEC_SEC_INT` and `MAX_TIMESPEC_SEC`. -/
theorem int64_toInt_bounds (x : Int64) :
    MIN_TIMESPEC_SEC_INT ≤ x.toInt ∧ x.toInt ≤ Int.ofNat MAX_TIMESPEC_SEC := by
  have hge : -(2 ^ 63 : Int) ≤ x.toBitVec.toInt := BitVec.le_toInt x.toBitVec
  have hlt : x.toBitVec.toInt < (2 ^ 63 : Int) := @BitVec.toInt_lt 64 x.toBitVec
  change -9223372036854775808 ≤ x.toBitVec.toInt ∧ x.toBitVec.toInt ≤ 9223372036854775807
  omega

/-- Valid `Timespec` values satisfy `toNanosNat ≤ MAX_TIMESPEC_NANOS`. -/
theorem timespec_valid_toNanosNat_le {ts : Timespec} (hv : ts.isValid = true) :
    0 ≤ ts.sec.toInt ∧ ts.nsec.toNat < NSEC_PER_SEC ∧ ts.toNanosNat ≤ MAX_TIMESPEC_NANOS := by
  simp only [Timespec.isValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hsec0 : 0 ≤ ts.sec.toInt := hv.1
  have hnsec : ts.nsec.toNat < NSEC_PER_SEC := hv.2
  have hhi := (int64_toInt_bounds ts.sec).2
  change ts.sec.toInt ≤ 9223372036854775807 at hhi
  have hsecNat : ts.sec.toInt.toNat ≤ MAX_TIMESPEC_SEC := by
    change ts.sec.toInt.toNat ≤ 9223372036854775807
    omega
  dsimp only [Timespec.toNanosNat, MAX_TIMESPEC_NANOS]
  refine ⟨hsec0, hnsec, ?_⟩
  have hmul : ts.sec.toInt.toNat * NSEC_PER_SEC ≤ MAX_TIMESPEC_SEC * NSEC_PER_SEC :=
    Nat.mul_le_mul_right NSEC_PER_SEC hsecNat
  have hns : ts.nsec.toNat ≤ NSEC_PER_SEC - 1 := Nat.le_sub_one_of_lt hnsec
  exact Nat.add_le_add hmul hns

/-- Successful `Timespec.ofNanosNat?` yields a valid `Timespec` with exact nanoseconds. -/
theorem ofNanosNat?_some_props {ns : Nat} {ts : Timespec}
    (h : Timespec.ofNanosNat? ns = some ts) :
    ts.isValid = true ∧ ts.toNanosNat = ns := by
  dsimp only [Timespec.ofNanosNat?] at h
  by_cases hle : ns.ble MAX_TIMESPEC_NANOS = true
  · simp only [hle, ↓reduceIte, Option.some.injEq] at h
    subst h
    have hleNat : ns ≤ 9223372036854775807999999999 := Nat.ble_eq.mp hle
    have hnsLt : ns / NSEC_PER_SEC < 2 ^ 63 := by
      change ns / 1000000000 < 9223372036854775808
      omega
    have hsec : (Int64.ofInt (Int.ofNat (ns / NSEC_PER_SEC))).toInt =
        Int.ofNat (ns / NSEC_PER_SEC) :=
      int64_toInt_ofNat _ hnsLt
    have hrem : ns % NSEC_PER_SEC < NSEC_PER_SEC := Nat.mod_lt ns (by decide)
    have hnsec : (UInt32.ofNat (ns % NSEC_PER_SEC)).toNat = ns % NSEC_PER_SEC := by
      rw [UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_trans hrem (by decide))
    refine ⟨?_, ?_⟩
    · simp only [Timespec.isValid, hsec, hnsec, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg _, hrem⟩
    · dsimp only [Timespec.toNanosNat]
      rw [hsec, hnsec]
      change (ns / NSEC_PER_SEC) * NSEC_PER_SEC + ns % NSEC_PER_SEC = ns
      exact Nat.div_add_mod' ns NSEC_PER_SEC
  · simp [hle] at h

/-- `Internal.relativeTimespecOfMs ms` is valid and equals `ms.toNat * 1_000_000` ns. -/
theorem relativeTimespecOfMs_valid (ms : UInt32) :
    (Internal.relativeTimespecOfMs ms).isValid = true ∧
      (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000 := by
  have hms_lt : ms.toNat < 4294967296 := ms.toBitVec.isLt
  have hsecLt : ms.toNat / 1000 < 2 ^ 63 := by
    change ms.toNat / 1000 < 9223372036854775808
    omega
  have hsec0 : (Int64.ofInt (Int.ofNat (ms.toNat / 1000))).toInt = ((ms.toNat / 1000 : Nat) : Int) :=
    int64_toInt_ofNat _ hsecLt
  have hrem : ms.toNat % 1000 * 1000000 < 1000000000 := by omega
  have hnsec0 : (UInt32.ofNat (ms.toNat % 1000 * 1000000)).toNat = ms.toNat % 1000 * 1000000 := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans hrem (by decide))
  simp only [Timespec.isValid, Timespec.toNanosNat, NSEC_PER_SEC,
    Internal.relativeTimespecOfMs, hsec0, hnsec0]
  constructor
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, hrem⟩
  · rw [Int.toNat_natCast]
    calc ms.toNat / 1000 * 1000000000 + ms.toNat % 1000 * 1000000
      _ = (ms.toNat / 1000 * 1000 + ms.toNat % 1000) * 1000000 := by
        rw [Nat.add_mul, Nat.mul_assoc]
      _ = ms.toNat * 1000000 := by
        rw [Nat.div_add_mod']

/-- Extract wall-clock validity from `Model.pkgWf`. -/
theorem pkgWf_wall {s : Model.TimeModelState} (hwf : Model.pkgWf s = true) :
    Model.isValidTimestampNanos s.wallNanos = true :=
  (Bool.and_eq_true_iff.mp hwf).1

/-- Extract monotonic-clock validity from `Model.pkgWf`. -/
theorem pkgWf_mono {s : Model.TimeModelState} (hwf : Model.pkgWf s = true) :
    Model.isValidMonoNanos s.monoNanos = true :=
  (Bool.and_eq_true_iff.mp hwf).2

/-- Combine wall-clock and monotonic-clock validity into `Model.pkgWf`. -/
theorem pkgWf_mk {s : Model.TimeModelState}
    (hw : Model.isValidTimestampNanos s.wallNanos = true)
    (hm : Model.isValidMonoNanos s.monoNanos = true) :
    Model.pkgWf s = true :=
  Bool.and_eq_true_iff.mpr ⟨hw, hm⟩

private theorem stateM_bind_run {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

/-- Raw `clock_gettime .realtime` step postcondition under `Model.allowedRawStep`. -/
theorem clock_gettime_realtime_raw {W : Type}
    (proj : W → Model.TimeRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep)
    (w : W) (hw : Model.rawWf (proj w) = true) :
    ∃ ts : Timespec,
      (sys.clock_gettime .realtime).run w = (.ok ts, ((sys.clock_gettime .realtime).run w).2) ∧
      (proj w).wallNanos ≤ (proj ((sys.clock_gettime .realtime).run w).2).wallNanos ∧
      Model.isValidTimestampNanos (proj ((sys.clock_gettime .realtime).run w).2).wallNanos = true ∧
      ts.toEpochNanos = (proj ((sys.clock_gettime .realtime).run w).2).wallNanos ∧
      (proj w).monoNanos ≤ (proj ((sys.clock_gettime .realtime).run w).2).monoNanos ∧
      Model.isValidMonoNanos (proj ((sys.clock_gettime .realtime).run w).2).monoNanos = true := by
  have hStep := hRaw w (.clock_gettime .realtime) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
  rw [stateM_bind_run] at hStep
  cases hcg : (sys.clock_gettime .realtime).run w with
  | mk res w' =>
    rw [hcg] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
    cases res with
    | error _ => exact False.elim hStep
    | ok ts =>
      rcases hStep with ⟨_, hwLe, hwVal, hEq, hmLe, hmVal⟩
      exact ⟨ts, rfl, hwLe, hwVal, hEq, hmLe, hmVal⟩

/-- Raw `clock_gettime .monotonic` step postcondition under `Model.allowedRawStep`. -/
theorem clock_gettime_monotonic_raw {W : Type}
    (proj : W → Model.TimeRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep)
    (w : W) (hw : Model.rawWf (proj w) = true) :
    ∃ ts : Timespec,
      (sys.clock_gettime .monotonic).run w = (.ok ts, ((sys.clock_gettime .monotonic).run w).2) ∧
      ts.isValid = true ∧
      (proj w).monoNanos ≤ (proj ((sys.clock_gettime .monotonic).run w).2).monoNanos ∧
      Model.isValidMonoNanos (proj ((sys.clock_gettime .monotonic).run w).2).monoNanos = true ∧
      ts.toNanosNat = (proj ((sys.clock_gettime .monotonic).run w).2).monoNanos ∧
      (proj w).wallNanos ≤ (proj ((sys.clock_gettime .monotonic).run w).2).wallNanos ∧
      Model.isValidTimestampNanos (proj ((sys.clock_gettime .monotonic).run w).2).wallNanos = true := by
  have hStep := hRaw w (.clock_gettime .monotonic) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
  rw [stateM_bind_run] at hStep
  cases hcg : (sys.clock_gettime .monotonic).run w with
  | mk res w' =>
    rw [hcg] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
    cases res with
    | error _ => exact False.elim hStep
    | ok ts =>
      rcases hStep with ⟨hval, hmLe, hmVal, hEq, hwLe, hwVal⟩
      exact ⟨ts, rfl, hval, hmLe, hmVal, hEq, hwLe, hwVal⟩

/-- Raw valid relative `clock_nanosleep .monotonic` step postcondition under `Model.allowedRawStep`. -/
theorem clock_nanosleep_monotonic_rel_raw {W : Type}
    (proj : W → Model.TimeRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep)
    (reqTs : Timespec) (hvalid : reqTs.isValid = true)
    (w : W) (hw : Model.rawWf (proj w) = true) :
    (sys.clock_nanosleep .monotonic false reqTs).run w =
      (.ok (), ((sys.clock_nanosleep .monotonic false reqTs).run w).2) ∧
    min Model.maxMonoNanos ((proj w).monoNanos + reqTs.toNanosNat) ≤
      (proj ((sys.clock_nanosleep .monotonic false reqTs).run w).2).monoNanos ∧
    Model.isValidMonoNanos (proj ((sys.clock_nanosleep .monotonic false reqTs).run w).2).monoNanos = true ∧
    (proj w).wallNanos ≤ (proj ((sys.clock_nanosleep .monotonic false reqTs).run w).2).wallNanos ∧
    Model.isValidTimestampNanos (proj ((sys.clock_nanosleep .monotonic false reqTs).run w).2).wallNanos = true := by
  have hStep := hRaw w (.clock_nanosleep .monotonic false reqTs) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
  rw [stateM_bind_run] at hStep
  cases hcn : (sys.clock_nanosleep .monotonic false reqTs).run w with
  | mk res w' =>
    rw [hcn] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
    cases res with
    | error _ =>
      rcases hStep with ⟨hinv, _, _⟩
      rw [hvalid] at hinv
      cases hinv
    | ok u =>
      cases u
      rcases hStep with ⟨_, hmLe, hmVal, hwLe, hwVal⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hmLe
      exact ⟨rfl, hmLe, hmVal, hwLe, hwVal⟩

/-- Raw valid `TIMER_ABSTIME` `clock_nanosleep .monotonic` step outcome under `Model.allowedRawStep`:
    either succeeds reaching `max monoNanos reqTs.toNanosNat`, or returns `Errno.EINTR` while strictly
    decrementing `eintrBudget` and preserving clock monotonicity and validity. -/
theorem clock_nanosleep_monotonic_abs_raw {W : Type}
    (proj : W → Model.TimeRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep)
    (reqTs : Timespec) (hvalid : reqTs.isValid = true)
    (w : W) (hw : Model.rawWf (proj w) = true) :
    let r := (sys.clock_nanosleep .monotonic true reqTs).run w
    (r.1 = .ok () ∧
      max (proj w).monoNanos reqTs.toNanosNat ≤ (proj r.2).monoNanos ∧
      Model.isValidMonoNanos (proj r.2).monoNanos = true ∧
      (proj w).wallNanos ≤ (proj r.2).wallNanos ∧
      Model.isValidTimestampNanos (proj r.2).wallNanos = true) ∨
    (r.1 = .error LeanSwe.LinuxSyscall.Errno.EINTR ∧
      (proj r.2).eintrBudget.val < (proj w).eintrBudget.val ∧
      (proj w).monoNanos ≤ (proj r.2).monoNanos ∧
      Model.isValidMonoNanos (proj r.2).monoNanos = true ∧
      (proj w).wallNanos ≤ (proj r.2).wallNanos ∧
      Model.isValidTimestampNanos (proj r.2).wallNanos = true) := by
  have hStep := hRaw w (.clock_nanosleep .monotonic true reqTs) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
  rw [stateM_bind_run] at hStep
  cases hcn : (sys.clock_nanosleep .monotonic true reqTs).run w with
  | mk res w' =>
    rw [hcn] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
    cases res with
    | error e =>
      rcases hStep with ⟨hinv, _, _⟩ | ⟨_, he, hbud, hmLe, hmVal, hwLe, hwVal⟩
      · rw [hvalid] at hinv; cases hinv
      · subst he; exact Or.inr ⟨rfl, hbud, hmLe, hmVal, hwLe, hwVal⟩
    | ok u =>
      cases u
      rcases hStep with ⟨_, hmLe, hmVal, hwLe, hwVal⟩
      simp only [↓reduceIte] at hmLe
      exact Or.inl ⟨rfl, hmLe, hmVal, hwLe, hwVal⟩

end LeanSwe.Time.Proofs.RefinesModel

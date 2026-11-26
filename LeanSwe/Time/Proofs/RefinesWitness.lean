import Core.Obeys
import LeanSwe.Time.Model
import LeanSwe.Time.Model.Refines
import LeanSwe.Time.Proofs.RefinesTimeRandHelpers

/-!
# Constructive Raw Witness for `LeanSwe.Time`

Defines `refRawOps : TimeRandOpsM (StateM TimeRawState)` and proves
`refRawOps_obeys_model`, witnessing non-vacuity of `Model.allowedRawStep`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (Timespec TimeRandOpsM NSEC_PER_SEC)
open LeanSwe.Time

/-- Constructive `TimeRandOpsM (StateM TimeRawState)` witnessing satisfiability of `Model.allowedRawStep`. -/
def refRawOps : TimeRandOpsM (StateM Model.TimeRawState) :=
  { clock_gettime := fun clk => do
      let s ← get
      match clk with
      | .realtime =>
        let sec := Int64.ofInt (s.wallNanos.ediv 1000000000)
        let nsec := UInt32.ofNat (s.wallNanos.emod 1000000000).toNat
        pure (.ok { sec, nsec })
      | .monotonic =>
        let sec := Int64.ofInt (Int.ofNat (s.monoNanos / 1000000000))
        let nsec := UInt32.ofNat (s.monoNanos % 1000000000)
        pure (.ok { sec, nsec })
    clock_nanosleep := fun clk abstime reqTs => do
      if !reqTs.isValid then
        pure (.error Errno.EINVAL)
      else
        match clk with
        | .realtime => pure (.ok ())
        | .monotonic =>
          let s ← get
          set { s with
            monoNanos :=
              if abstime then max s.monoNanos reqTs.toNanosNat
              else min Model.maxMonoNanos (s.monoNanos + reqTs.toNanosNat) }
          pure (.ok ())
    getrandom := fun _ _ => pure (.ok ByteArray.empty) }

private theorem nsec_lt_uint32_size {n : Nat} (h : n < 1000000000) : n < UInt32.size := by
  have hbound : 1000000000 < UInt32.size := by simp [UInt32.size]
  exact Nat.lt_trans h hbound

private theorem refRawOps_realtime (s : Model.TimeRawState) (hwf : Model.rawWf s = true) :
    let res := (Model.execRawStep refRawOps (.clock_gettime .realtime)).run s
    Model.allowedRawStep s (.clock_gettime .realtime) res.1 res.2 := by
  have hwVal := pkgWf_wall hwf
  have hmVal := pkgWf_mono hwf
  have hwBounds : Model.minTimestampNanos ≤ s.wallNanos ∧ s.wallNanos ≤ Model.maxTimestampNanos :=
    of_decide_eq_true hwVal
  let q : Int := s.wallNanos / 1000000000
  let r : Int := s.wallNanos % 1000000000
  have hqLo : (-9223372036854775808 : Int) ≤ q := by
    have h1 := hwBounds.1
    change -9223372036854775808000000000 ≤ s.wallNanos at h1
    omega
  have hqHi : q ≤ 9223372036854775807 := by
    have h2 := hwBounds.2
    change s.wallNanos ≤ 9223372036854775807999999999 at h2
    omega
  have hrNonneg : (0 : Int) ≤ r := Int.emod_nonneg s.wallNanos (by omega)
  have hrLt : r.toNat < 1000000000 := by omega
  have hsecEq : (Int64.ofInt q).toInt = q := int64_toInt_ofInt_range q hqLo hqHi
  have hnsecEq : (UInt32.ofNat r.toNat).toNat = r.toNat := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (nsec_lt_uint32_size hrLt)
  let ts : Timespec := { sec := Int64.ofInt q, nsec := UInt32.ofNat r.toNat }
  change Timespec.hasValidNsec ts = true ∧
    s.wallNanos ≤ s.wallNanos ∧ Model.isValidTimestampNanos s.wallNanos = true ∧
    ts.toEpochNanos = s.wallNanos ∧
    s.monoNanos ≤ s.monoNanos ∧ Model.isValidMonoNanos s.monoNanos = true
  refine ⟨?_, Int.le_refl _, hwVal, ?_, Nat.le_refl _, hmVal⟩
  · simp only [Timespec.hasValidNsec, ts, NSEC_PER_SEC, hnsecEq, decide_eq_true_eq]
    exact hrLt
  · change (Int64.ofInt q).toInt * 1000000000 + ((UInt32.ofNat r.toNat).toNat : Int) = s.wallNanos
    rw [hsecEq, hnsecEq, Int.toNat_of_nonneg hrNonneg]
    have h := Int.mul_ediv_add_emod s.wallNanos 1000000000
    rw [Int.mul_comm] at h
    exact h

private theorem refRawOps_monotonic (s : Model.TimeRawState) (hwf : Model.rawWf s = true) :
    let res := (Model.execRawStep refRawOps (.clock_gettime .monotonic)).run s
    Model.allowedRawStep s (.clock_gettime .monotonic) res.1 res.2 := by
  have hwVal := pkgWf_wall hwf
  have hmVal := pkgWf_mono hwf
  have hmBound : s.monoNanos ≤ Model.maxMonoNanos := of_decide_eq_true hmVal
  let q : Nat := s.monoNanos / 1000000000
  let r : Nat := s.monoNanos % 1000000000
  have hqLt : q < 2 ^ 63 := by
    change s.monoNanos ≤ 9223372036854775807999999999 at hmBound
    omega
  have hrLt : r < 1000000000 := Nat.mod_lt _ (by omega)
  have hsecEq : (Int64.ofInt (Int.ofNat q)).toInt = Int.ofNat q := int64_toInt_ofNat q hqLt
  have hnsecEq : (UInt32.ofNat r).toNat = r := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (nsec_lt_uint32_size hrLt)
  let ts : Timespec := { sec := Int64.ofInt (Int.ofNat q), nsec := UInt32.ofNat r }
  change Timespec.isValid ts = true ∧
    s.monoNanos ≤ s.monoNanos ∧ Model.isValidMonoNanos s.monoNanos = true ∧
    ts.toNanosNat = s.monoNanos ∧
    s.wallNanos ≤ s.wallNanos ∧ Model.isValidTimestampNanos s.wallNanos = true
  refine ⟨?_, Nat.le_refl _, hmVal, ?_, Int.le_refl _, hwVal⟩
  · simp only [Timespec.isValid, ts, NSEC_PER_SEC, hsecEq, hnsecEq, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg q, hrLt⟩
  · change (Int64.ofInt (Int.ofNat q)).toInt.toNat * 1000000000 + (UInt32.ofNat r).toNat = s.monoNanos
    rw [hsecEq, hnsecEq]
    exact Nat.div_add_mod' s.monoNanos 1000000000

private theorem refRawOps_nanosleep_invalid (s : Model.TimeRawState)
    (clk : LeanSwe.LinuxSyscall.TimeRand.ClockId) (abstime : Bool) (reqTs : Timespec)
    (hv : reqTs.isValid = false) :
    let res := (Model.execRawStep refRawOps (.clock_nanosleep clk abstime reqTs)).run s
    Model.allowedRawStep s (.clock_nanosleep clk abstime reqTs) res.1 res.2 := by
  have hrun : (Model.execRawStep refRawOps (.clock_nanosleep clk abstime reqTs)).run s =
      (.err Errno.EINVAL, s) := by
    dsimp only [Model.execRawStep, LeanSwe.LinuxSyscall.TimeRand.execTimeRandReq,
      LeanSwe.LinuxSyscall.TimeRand.outcomeOfUnit, refRawOps]
    rw [hv]
    rfl
  rw [hrun]
  cases clk with
  | realtime => exact ⟨hv, rfl, rfl⟩
  | monotonic =>
    cases abstime with
    | false => exact ⟨hv, rfl, rfl⟩
    | true => exact Or.inl ⟨hv, rfl, rfl⟩

private theorem refRawOps_nanosleep_realtime (s : Model.TimeRawState)
    (abstime : Bool) (reqTs : Timespec) (hv : reqTs.isValid = true) :
    let res := (Model.execRawStep refRawOps (.clock_nanosleep .realtime abstime reqTs)).run s
    Model.allowedRawStep s (.clock_nanosleep .realtime abstime reqTs) res.1 res.2 := by
  have hrun : (Model.execRawStep refRawOps (.clock_nanosleep .realtime abstime reqTs)).run s =
      (.unit, s) := by
    dsimp only [Model.execRawStep, LeanSwe.LinuxSyscall.TimeRand.execTimeRandReq,
      LeanSwe.LinuxSyscall.TimeRand.outcomeOfUnit, refRawOps]
    rw [hv]
    rfl
  rw [hrun]
  exact ⟨hv, rfl⟩

private theorem allowed_monotonic_of_eq (s : Model.TimeRawState) (abstime : Bool) (reqTs : Timespec)
    (m : Nat) (hv : reqTs.isValid = true)
    (hm : (if abstime then max s.monoNanos reqTs.toNanosNat
           else min Model.maxMonoNanos (s.monoNanos + reqTs.toNanosNat)) ≤ m)
    (hvalid : m ≤ Model.maxMonoNanos)
    (hw : Model.isValidTimestampNanos s.wallNanos = true) :
    Model.allowedRawStep s (.clock_nanosleep .monotonic abstime reqTs)
      .unit { s with monoNanos := m } :=
  ⟨hv, hm, decide_eq_true hvalid, Int.le_refl _, hw⟩

private theorem nextMono_le_max (a b : Nat) (abstime : Bool)
    (ha : a ≤ Model.maxMonoNanos) (hb : b ≤ Model.maxMonoNanos) :
    (if abstime then max a b else min Model.maxMonoNanos (a + b)) ≤ Model.maxMonoNanos := by
  cases abstime
  · exact Nat.min_le_left _ _
  · exact Nat.max_le.mpr ⟨ha, hb⟩

private theorem refRawOps_nanosleep_monotonic_run (s : Model.TimeRawState)
    (abstime : Bool) (reqTs : Timespec) (hv : reqTs.isValid = true) :
    (Model.execRawStep refRawOps (.clock_nanosleep .monotonic abstime reqTs)).run s =
      (.unit, { s with
        monoNanos :=
          if abstime then max s.monoNanos reqTs.toNanosNat
          else min Model.maxMonoNanos (s.monoNanos + reqTs.toNanosNat) }) := by
  dsimp only [Model.execRawStep, LeanSwe.LinuxSyscall.TimeRand.execTimeRandReq,
    LeanSwe.LinuxSyscall.TimeRand.outcomeOfUnit, refRawOps]
  rw [hv]
  rfl

private theorem refRawOps_nanosleep_monotonic (s : Model.TimeRawState)
    (abstime : Bool) (reqTs : Timespec)
    (hwf : Model.rawWf s = true) (hv : reqTs.isValid = true) :
    let res := (Model.execRawStep refRawOps (.clock_nanosleep .monotonic abstime reqTs)).run s
    Model.allowedRawStep s (.clock_nanosleep .monotonic abstime reqTs) res.1 res.2 :=
  @Eq.ndrec _ _
    (fun res => Model.allowedRawStep s (.clock_nanosleep .monotonic abstime reqTs) res.1 res.2)
    (allowed_monotonic_of_eq s abstime reqTs _ hv (Nat.le_refl _)
      (nextMono_le_max s.monoNanos reqTs.toNanosNat abstime
        (of_decide_eq_true (pkgWf_mono hwf)) (timespec_valid_toNanosNat_le hv).2.2)
      (pkgWf_wall hwf))
    _ (refRawOps_nanosleep_monotonic_run s abstime reqTs hv).symm

/-- `refRawOps` satisfies `Model.allowedRawStep` under `Core.ObeysStepId`. -/
theorem refRawOps_obeys_model :
    Core.ObeysStepId Model.rawWf (Model.execRawStep refRawOps) Model.allowedRawStep := by
  intro s req hwf
  cases req with
  | clock_gettime clk =>
    cases clk with
    | realtime => exact refRawOps_realtime s hwf
    | monotonic => exact refRawOps_monotonic s hwf
  | clock_nanosleep clk abstime reqTs =>
    cases hv : reqTs.isValid with
    | false => exact refRawOps_nanosleep_invalid s clk abstime reqTs hv
    | true =>
      cases clk with
      | realtime => exact refRawOps_nanosleep_realtime s abstime reqTs hv
      | monotonic => exact refRawOps_nanosleep_monotonic s abstime reqTs hwf hv
  | getrandom _ _ => rfl

end LeanSwe.Time.Proofs.RefinesModel

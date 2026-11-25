import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.TimeRand.SpecTests

namespace LeanSwe.LinuxSyscall.TimeRand.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

private theorem int64_toInt_ofInt {x : Int}
    (hlo : MIN_TIMESPEC_SEC_INT ≤ x) (hhi : x ≤ Int.ofNat MAX_TIMESPEC_SEC) :
    (Int64.ofInt x).toInt = x := by
  rw [Int64.toInt_ofInt]
  change -9223372036854775808 ≤ x at hlo
  change x ≤ 9223372036854775807 at hhi
  change (if x % (18446744073709551616 : Int) < (9223372036854775808 : Int) then
      x % (18446744073709551616 : Int)
    else x % (18446744073709551616 : Int) - (18446744073709551616 : Int)) = x
  by_cases hx : 0 ≤ x
  · have hm : x % (18446744073709551616 : Int) = x := Int.emod_eq_of_lt hx (by omega)
    rw [hm]
    have hlt : x < (9223372036854775808 : Int) := by omega
    simp [hlt]
  · have hm : x % (18446744073709551616 : Int) = x + (18446744073709551616 : Int) := by omega
    rw [hm]
    have hge : ¬ x + (18446744073709551616 : Int) < (9223372036854775808 : Int) := by omega
    simp [hge]

private theorem u32_toNat_ofNat_lt {n : Nat} (h : n < 4294967296) :
    (UInt32.ofNat n).toNat = n := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- `Timespec.ofNanosNat?` returns `none` whenever `MAX_TIMESPEC_NANOS < ns`. -/
theorem ofNanosNat?_none {ns : Nat} (h : MAX_TIMESPEC_NANOS < ns) :
    Timespec.ofNanosNat? ns = none := by
  unfold Timespec.ofNanosNat?
  have hble : ns.ble MAX_TIMESPEC_NANOS = false := by
    cases hb : ns.ble MAX_TIMESPEC_NANOS
    · rfl
    · have := Nat.ble_eq.mp hb
      omega
  simp [hble]

/-- `Timespec.ofNanosNat?` returns a valid `Timespec` round-tripping `ns` whenever `ns ≤ MAX_TIMESPEC_NANOS`. -/
theorem ofNanosNat?_some {ns : Nat} (h : ns ≤ MAX_TIMESPEC_NANOS) :
    ∃ out, Timespec.ofNanosNat? ns = some out ∧
      Timespec.isValid out = true ∧ out.toNanosNat = ns := by
  unfold Timespec.ofNanosNat?
  have hble : ns.ble MAX_TIMESPEC_NANOS = true := Nat.ble_eq.mpr h
  simp only [hble, ↓reduceIte]
  have hbound : ns ≤ 9223372036854775807999999999 := h
  have hdiv : ns / 1000000000 ≤ 9223372036854775807 := by omega
  have hrem : ns % 1000000000 < 1000000000 := Nat.mod_lt ns (by decide)
  have hsec : (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt =
      Int.ofNat (ns / 1000000000) := by
    refine int64_toInt_ofInt ?_ ?_
    · exact Int.le_trans (by decide) (Int.natCast_nonneg (ns / 1000000000))
    · change ((ns / 1000000000 : Nat) : Int) ≤ 9223372036854775807
      omega
  have hnsec : (UInt32.ofNat (ns % 1000000000)).toNat = ns % 1000000000 :=
    u32_toNat_ofNat_lt (by omega)
  refine ⟨_, rfl, ?_, ?_⟩
  · unfold Timespec.isValid NSEC_PER_SEC
    change decide (0 ≤ (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt) &&
        decide ((UInt32.ofNat (ns % 1000000000)).toNat < 1000000000) = true
    rw [hsec, hnsec]
    have hnonneg : decide ((0 : Int) ≤ Int.ofNat (ns / 1000000000)) = true :=
      decide_eq_true (Int.natCast_nonneg _)
    rw [hnonneg, decide_eq_true hrem]
    rfl
  · unfold Timespec.toNanosNat NSEC_PER_SEC
    change (Int64.ofInt (Int.ofNat (ns / 1000000000))).toInt.toNat * 1000000000 +
        (UInt32.ofNat (ns % 1000000000)).toNat = ns
    rw [hsec, hnsec]
    change (ns / 1000000000) * 1000000000 + ns % 1000000000 = ns
    exact Nat.div_add_mod' ns 1000000000

/-- Exact characterization of `Timespec.ofEpochNanos?` across signed `Int64` bounds. -/
theorem ofEpochNanos?_spec (ns : Int) :
    let secInt := ns.ediv (Int.ofNat NSEC_PER_SEC)
    if MIN_TIMESPEC_SEC_INT ≤ secInt ∧ secInt ≤ Int.ofNat MAX_TIMESPEC_SEC then
      ∃ out, Timespec.ofEpochNanos? ns = some out ∧
        out.hasValidNsec = true ∧ out.toEpochNanos = ns
    else
      Timespec.ofEpochNanos? ns = none := by
  by_cases h : MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat NSEC_PER_SEC) ∧
      ns.ediv (Int.ofNat NSEC_PER_SEC) ≤ Int.ofNat MAX_TIMESPEC_SEC
  · simp only [h]
    unfold Timespec.ofEpochNanos? NSEC_PER_SEC
    dsimp only
    have h' : MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat 1000000000) ∧
        ns.ediv (Int.ofNat 1000000000) ≤ Int.ofNat MAX_TIMESPEC_SEC := h
    rw [decide_eq_true h']
    simp only [↓reduceIte]
    have hpos : (0 : Int) < (1000000000 : Int) := by decide
    have hmod0 : 0 ≤ ns.emod (1000000000 : Int) := Int.emod_nonneg ns (by decide)
    have hmod1 : ns.emod (1000000000 : Int) < (1000000000 : Int) := Int.emod_lt_of_pos ns hpos
    have htoNat : (ns.emod (1000000000 : Int)).toNat < 1000000000 := by omega
    have hnsec : (UInt32.ofNat (ns.emod (1000000000 : Int)).toNat).toNat =
        (ns.emod (1000000000 : Int)).toNat :=
      u32_toNat_ofNat_lt (by omega)
    have hsec : (Int64.ofInt (ns.ediv (1000000000 : Int))).toInt =
        ns.ediv (1000000000 : Int) := int64_toInt_ofInt h'.1 h'.2
    refine ⟨_, rfl, ?_, ?_⟩
    · unfold Timespec.hasValidNsec
    
      change decide ((UInt32.ofNat (ns.emod (1000000000 : Int)).toNat).toNat < 1000000000) = true
      rw [hnsec]
      simp [htoNat]
    · unfold Timespec.toEpochNanos
      change (Int64.ofInt (ns.ediv (1000000000 : Int))).toInt * (1000000000 : Int) +
          Int.ofNat (UInt32.ofNat (ns.emod (1000000000 : Int)).toNat).toNat = ns
      rw [hsec, hnsec]
      have hrem : Int.ofNat (ns.emod (1000000000 : Int)).toNat =
          ns.emod (1000000000 : Int) := Int.toNat_of_nonneg hmod0
      rw [hrem]
      have hdivmod := Int.mul_ediv_add_emod ns (1000000000 : Int)
      rw [Int.mul_comm] at hdivmod
      exact hdivmod
  · simp only [h]
    unfold Timespec.ofEpochNanos? NSEC_PER_SEC
    dsimp only
    have h' : ¬(MIN_TIMESPEC_SEC_INT ≤ ns.ediv (Int.ofNat 1000000000) ∧
        ns.ediv (Int.ofNat 1000000000) ≤ Int.ofNat MAX_TIMESPEC_SEC) := h
    rw [decide_eq_false h']
    rfl

private theorem deterministicEntropyListAux_length (drawIdx rem pos : Nat) (acc : List UInt8) :
    (deterministicEntropyListAux drawIdx rem pos acc).length = acc.length + rem := by
  induction rem generalizing pos acc with
  | zero => simp [deterministicEntropyListAux]
  | succ rem ih =>
    simp only [deterministicEntropyListAux]
    rw [ih]
    simp [List.length_cons]
    omega

private theorem deterministicEntropyList_length (drawIdx rem pos : Nat) :
    (deterministicEntropyList drawIdx rem pos).length = rem := by
  rw [deterministicEntropyList, deterministicEntropyListAux_length]
  simp

private theorem deterministicEntropyBytesAux_size (drawIdx rem pos : Nat) (acc : ByteArray) :
    (deterministicEntropyBytesAux drawIdx rem pos acc).size = acc.size + rem := by
  induction rem generalizing pos acc with
  | zero => simp [deterministicEntropyBytesAux]
  | succ rem ih =>
    simp only [deterministicEntropyBytesAux]
    rw [ih, ByteArray.size_push]
    omega

/-- `deterministicEntropyBytes drawIdx len` produces a `ByteArray` of exact length `len`. -/
theorem deterministicEntropyBytes_size (drawIdx len : Nat) :
    (deterministicEntropyBytes drawIdx len).size = len := by
  unfold deterministicEntropyBytes
  by_cases h : len ≤ 256
  · simp [h, ByteArray.size, deterministicEntropyList_length]
  · simp only [h, ↓reduceIte]
    rw [deterministicEntropyBytesAux_size]
    have h0 : (ByteArray.emptyWithCapacity len).size = 0 := rfl
    omega

private theorem deterministicEntropyBytes_succ_ne (drawIdx : Nat) :
    deterministicEntropyBytes drawIdx 16 ≠ deterministicEntropyBytes (drawIdx + 1) 16 := by
  intro heq
  have h0 : (deterministicEntropyBytes drawIdx 16).data.toList.head? =
      (deterministicEntropyBytes (drawIdx + 1) 16).data.toList.head? :=
    congrArg (fun ba => ba.data.toList.head?) heq
  have hL : (deterministicEntropyBytes drawIdx 16).data.toList.head? =
      some (UInt8.ofNat ((drawIdx / 1) % 256)) := rfl
  have hR : (deterministicEntropyBytes (drawIdx + 1) 16).data.toList.head? =
      some (UInt8.ofNat (((drawIdx + 1) / 1) % 256)) := rfl
  rw [hL, hR] at h0
  injection h0 with hbyte
  have hval := congrArg UInt8.toNat hbyte
  change ((drawIdx / 1) % 256) % 256 = (((drawIdx + 1) / 1) % 256) % 256 at hval
  omega

/-- `min len.toNat MAX_READ_BYTES.toNat` is always accepted by `validGetrandomResultLen len`. -/
theorem validGetrandomResultLen_eq (len : UInt32) :
    validGetrandomResultLen len (min len.toNat MAX_READ_BYTES.toNat) = true := by
  unfold validGetrandomResultLen
  by_cases h0 : min len.toNat MAX_READ_BYTES.toNat = 0
  · simp [h0]
  · have hgt : 1 ≤ min len.toNat MAX_READ_BYTES.toNat := by omega
    by_cases hle : min len.toNat MAX_READ_BYTES.toNat ≤ GETRANDOM_EXACT_MAX
    · simp [h0, hle]
    · simp [h0, hle, hgt]

/-- State transition of `modelOps.clock_gettime .realtime`. -/
theorem modelOps_clock_gettime_realtime (s : TimeRandState) :
    modelOps.clock_gettime .realtime s =
      match Timespec.ofEpochNanos? s.realtimeNs with
      | some ts => (Except.ok ts, s)
      | none =>
        let clampedSec : Int64 :=
          if s.realtimeNs < 0 then Int64.minValue else Int64.maxValue
        let clampedNsec : UInt32 :=
          if s.realtimeNs < 0 then 0 else UInt32.ofNat (NSEC_PER_SEC - 1)
        (Except.ok { sec := clampedSec, nsec := clampedNsec }, s) := by
  dsimp only [modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get]
  cases Timespec.ofEpochNanos? s.realtimeNs <;> simp [StateT.pure] <;> rfl

/-- State transition of `modelOps.clock_gettime .monotonic`. -/
theorem modelOps_clock_gettime_monotonic (s : TimeRandState) :
    modelOps.clock_gettime .monotonic s =
      match Timespec.ofNanosNat? s.monoLowerBoundNs with
      | some ts => (Except.ok ts, { s with monoLowerBoundNs := ts.toNanosNat })
      | none =>
        (Except.ok { sec := Int64.ofInt (Int.ofNat MAX_TIMESPEC_SEC), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) }, s) := by
  dsimp only [modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set]
  cases Timespec.ofNanosNat? s.monoLowerBoundNs <;> simp [StateT.pure, StateT.set, StateT.bind] <;> rfl

/-- State transition of `modelOps.clock_nanosleep`. -/
theorem modelOps_clock_nanosleep (clk : ClockId) (abs : Bool) (req : Timespec)
    (s : TimeRandState) :
    modelOps.clock_nanosleep clk abs req s =
      if !req.isValid then
        (Except.error Errno.EINVAL, s)
      else
        match clk with
        | .realtime => (Except.ok (), s)
        | .monotonic =>
          let nextMono :=
            if abs then max s.monoLowerBoundNs req.toNanosNat
            else max s.monoLowerBoundNs (min MAX_TIMESPEC_NANOS (s.monoLowerBoundNs + req.toNanosNat))
          (Except.ok (), { s with monoLowerBoundNs := nextMono }) := by
  dsimp only [modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set]
  cases hr : req.isValid <;> cases clk <;> simp [StateT.pure, StateT.set, StateT.bind] <;> rfl

/-- State transition of `modelOps.getrandom`. -/
theorem modelOps_getrandom (len : UInt32) (flags : GrndFlags) (s : TimeRandState) :
    modelOps.getrandom len flags s =
      if flags.isInvalid then
        (Except.error Errno.EINVAL, s)
      else if !s.crngReady && flags.nonblock && !flags.insecure then
        (Except.error Errno.EAGAIN, s)
      else
        let cap := min len.toNat MAX_READ_BYTES.toNat
        let bs := deterministicEntropyBytes s.entropyDraws cap
        (Except.ok bs, { s with
          crngReady := s.crngReady || !flags.insecure
          entropyDraws := s.entropyDraws + 1 }) := by
  dsimp only [modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set]
  by_cases h1 : flags.isInvalid = true
  · simp [h1, StateT.pure]; rfl
  · by_cases h2 : (!s.crngReady && flags.nonblock && !flags.insecure) = true
    · simp [h1, h2, StateT.pure]; rfl
    · simp [h1, h2, StateT.pure, StateT.set, StateT.bind]; rfl

/-- Proof of `test_timerand_errno_classificationAndTransient`. -/
theorem proof_timerand_errno_classificationAndTransient :
    AllPass (test_timerand_errno_classificationAndTransient) := by
  intro e
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  cases e <;> rfl

private theorem grnd_toBits_inj (g1 g2 : GrndFlags) :
    (g1.toBits == g2.toBits) = (g1 == g2) := by
  rcases g1 with ⟨a1, a2, a3⟩
  rcases g2 with ⟨b1, b2, b3⟩
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-- Proof of `test_timerand_encoders_injectiveAndGrndInvalid`. -/
theorem proof_timerand_encoders_injectiveAndGrndInvalid :
    AllPass (test_timerand_encoders_injectiveAndGrndInvalid) := by
  intro c1 c2 g1 g2
  refine ⟨?_, ?_, grnd_toBits_inj g1 g2, ?_, rfl, rfl, rfl, trivial⟩
  · cases c1 <;> cases c2 <;> rfl
  · exact ⟨rfl, rfl⟩
  · rcases g1 with ⟨_, r, i⟩
    cases r <;> cases i <;> rfl

/-- Proof of `test_timerand_timespec_validAndNanosRoundTrip`. -/
theorem proof_timerand_timespec_validAndNanosRoundTrip :
    AllPass (test_timerand_timespec_validAndNanosRoundTrip) := by
  intro ts ns epochNs
  refine ⟨?_, ?_, ?_, trivial⟩
  · unfold Timespec.isValid
    rfl
  · by_cases h : ns ≤ MAX_TIMESPEC_NANOS
    · simp only [h]
      exact ofNanosNat?_some h
    · simp only [h]
      exact ofNanosNat?_none (Nat.lt_of_not_le h)
  · exact ofEpochNanos?_spec epochNs

/-- Proof of `test_timerand_mkTimeRandOps_encodesAndDelegates` for `Internal.mkTimeRandOpsM`. -/
theorem proof_timerand_mkTimeRandOps_encodesAndDelegates :
    AllPass (test_timerand_mkTimeRandOps_encodesAndDelegates Internal.mkTimeRandOpsM) := by
  intro rawGet rawSleep rawRand clk abstime req len flags
  simp only [Internal.mkTimeRandOpsM, NondetTest.assert, Bind.bind, Pure.pure]
  cases rawGet clk.toRaw <;> simp

/-- Proof of `test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes` for `modelOps`. -/
theorem proof_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes :
    AllPass (test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes (S := TimeRandState) modelOps) := by
  intro s₀ clk abstime badReq hbad
  dsimp only [test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes, NondetTest.assert]
  change (modelOps.clock_nanosleep clk abstime badReq s₀ = (.error Errno.EINVAL, s₀)) ∧ True
  rw [modelOps_clock_nanosleep]
  simp [hbad]

/-- Non-vacuity `CanReach` witness for `test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes`. -/
theorem reach_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes :
    CanReach (test_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes (S := TimeRandState) modelOps) := by
  refine ⟨default, .realtime, false, { sec := -1, nsec := 0 }, by decide, ?_⟩
  exact proof_timerand_ops_invalidTimespecRejectedOnAllClocksAndModes default .realtime false
    { sec := -1, nsec := 0 } (by decide)

private theorem monotonic_of_witnesses
    (ops : TimeRandOpsM (StateM TimeRandState))
    (hwit : ∀ (s₀ : TimeRandState) (relTs absTs : Timespec),
      relTs.isValid = true → absTs.isValid = true →
      s₀.monoLowerBoundNs + relTs.toNanosNat + absTs.toNanosNat ≤ MAX_TIMESPEC_NANOS →
      ∃ t0 t2 t3 : Timespec, ∃ s₁ s₃ s₄ s₅ s₆ : TimeRandState,
        ops.clock_gettime .monotonic s₀ = (.ok t0, s₁) ∧
        ops.clock_gettime .monotonic s₁ = (.ok t0, s₁) ∧
        ops.clock_nanosleep .monotonic false relTs s₁ = (.ok (), s₃) ∧
        ops.clock_gettime .monotonic s₃ = (.ok t2, s₄) ∧
        ops.clock_nanosleep .monotonic true absTs s₄ = (.ok (), s₅) ∧
        ops.clock_gettime .monotonic s₅ = (.ok t3, s₆) ∧
        ops.clock_nanosleep .realtime false relTs s₆ = (.ok (), s₆) ∧
        ops.clock_gettime .monotonic s₆ = (.ok t3, s₆) ∧
        t0.isValid = true ∧ t2.isValid = true ∧ t3.isValid = true ∧
        s₀.monoLowerBoundNs ≤ t0.toNanosNat ∧
        t0.toNanosNat + relTs.toNanosNat ≤ t2.toNanosNat ∧
        max t2.toNanosNat absTs.toNanosNat ≤ t3.toNanosNat) :
    AllPass (test_timerand_ops_monotonicMultiCallAndNanosleepBounds ops) := by
  intro s₀ relTs absTs hrel habs hbound
  rcases hwit s₀ relTs absTs hrel habs hbound with
    ⟨t0, t2, t3, s₁, s₃, s₄, s₅, s₆, hcg0, hcg1, hsnRel, hcg2, hsnAbs, hcg3, hsnReal, hcg4,
      ht0v, ht2v, ht3v, hle0, hle1, hle2⟩
  dsimp only [NondetTest.assert, Bind.bind, Pure.pure, StateT.run]
  rw [hcg0]
  dsimp only
  rw [hcg1]
  dsimp only
  refine ⟨⟨ht0v, ht0v⟩, ⟨hle0, Nat.le_refl _⟩, ?_⟩
  rw [hsnRel]
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [hcg2]
  dsimp only
  refine ⟨⟨ht2v, hle1⟩, ?_⟩
  rw [hsnAbs]
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [hcg3]
  dsimp only
  refine ⟨⟨ht3v, hle2⟩, ?_⟩
  rw [hsnReal]
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [hcg4]
  dsimp only
  exact ⟨⟨t3, rfl, Nat.le_refl _⟩, trivial⟩

/-- Proof of `test_timerand_ops_monotonicMultiCallAndNanosleepBounds` for `modelOps`. -/
theorem proof_timerand_ops_monotonicMultiCallAndNanosleepBounds :
    AllPass (test_timerand_ops_monotonicMultiCallAndNanosleepBounds modelOps) := by
  refine monotonic_of_witnesses modelOps ?_
  intro s₀ relTs absTs hrel habs hbound
  have hm0 : s₀.monoLowerBoundNs ≤ MAX_TIMESPEC_NANOS :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hbound
  obtain ⟨t0, ht0Eq, ht0Valid, ht0Ns⟩ := ofNanosNat?_some hm0
  have hstep1Mono : s₀.monoLowerBoundNs + relTs.toNanosNat ≤ MAX_TIMESPEC_NANOS :=
    Nat.le_trans (Nat.le_add_right _ _) hbound
  obtain ⟨t2, ht2Eq, ht2Valid, ht2Ns⟩ := ofNanosNat?_some hstep1Mono
  have hstep2Mono : max (s₀.monoLowerBoundNs + relTs.toNanosNat) absTs.toNanosNat ≤ MAX_TIMESPEC_NANOS :=
    Nat.max_le.mpr ⟨hstep1Mono, Nat.le_trans (Nat.le_add_left _ _) hbound⟩
  obtain ⟨t3, ht3Eq, ht3Valid, ht3Ns⟩ := ofNanosNat?_some hstep2Mono
  let s₁ : TimeRandState := { s₀ with monoLowerBoundNs := t0.toNanosNat }
  let s₃ : TimeRandState := { s₀ with monoLowerBoundNs := s₀.monoLowerBoundNs + relTs.toNanosNat }
  let s₄ : TimeRandState := { s₀ with monoLowerBoundNs := t2.toNanosNat }
  let s₅ : TimeRandState := { s₀ with monoLowerBoundNs := max t2.toNanosNat absTs.toNanosNat }
  let s₆ : TimeRandState := { s₀ with monoLowerBoundNs := t3.toNanosNat }
  have hcg0 : modelOps.clock_gettime .monotonic s₀ = (.ok t0, s₁) := by
    rw [modelOps_clock_gettime_monotonic, ht0Eq]
  have hcg1 : modelOps.clock_gettime .monotonic s₁ = (.ok t0, s₁) := by
    rw [modelOps_clock_gettime_monotonic]
    have hm1 : s₁.monoLowerBoundNs = s₀.monoLowerBoundNs := ht0Ns
    rw [hm1, ht0Eq]
  have hsnRel : modelOps.clock_nanosleep .monotonic false relTs s₁ = (.ok (), s₃) := by
    rw [modelOps_clock_nanosleep]
    simp only [hrel, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hmin : min MAX_TIMESPEC_NANOS (s₀.monoLowerBoundNs + relTs.toNanosNat) =
        s₀.monoLowerBoundNs + relTs.toNanosNat := Nat.min_eq_right hstep1Mono
    have hmax : max s₀.monoLowerBoundNs (s₀.monoLowerBoundNs + relTs.toNanosNat) =
        s₀.monoLowerBoundNs + relTs.toNanosNat := Nat.max_eq_right (Nat.le_add_right _ _)
    change (Except.ok (), { s₁ with
        monoLowerBoundNs := max s₁.monoLowerBoundNs (min MAX_TIMESPEC_NANOS (s₁.monoLowerBoundNs + relTs.toNanosNat)) }) =
      (Except.ok (), s₃)
    simp only [s₁, s₃, ht0Ns, hmin, hmax]
  have hcg2 : modelOps.clock_gettime .monotonic s₃ = (.ok t2, s₄) := by
    rw [modelOps_clock_gettime_monotonic]
    have hm3 : s₃.monoLowerBoundNs = s₀.monoLowerBoundNs + relTs.toNanosNat := rfl
    rw [hm3, ht2Eq]
  have hsnAbs : modelOps.clock_nanosleep .monotonic true absTs s₄ = (.ok (), s₅) := by
    rw [modelOps_clock_nanosleep]
    simp [habs, s₄, s₅]
  have hcg3 : modelOps.clock_gettime .monotonic s₅ = (.ok t3, s₆) := by
    rw [modelOps_clock_gettime_monotonic]
    have hm5 : s₅.monoLowerBoundNs = max (s₀.monoLowerBoundNs + relTs.toNanosNat) absTs.toNanosNat := by
      dsimp only [s₅]
      rw [ht2Ns]
    rw [hm5, ht3Eq]
  have hsnReal : modelOps.clock_nanosleep .realtime false relTs s₆ = (.ok (), s₆) := by
    rw [modelOps_clock_nanosleep]
    simp [hrel]
  have hcg4 : modelOps.clock_gettime .monotonic s₆ = (.ok t3, s₆) := by
    rw [modelOps_clock_gettime_monotonic]
    have hm6 : s₆.monoLowerBoundNs = max (s₀.monoLowerBoundNs + relTs.toNanosNat) absTs.toNanosNat := ht3Ns
    rw [hm6, ht3Eq]
  exact ⟨t0, t2, t3, s₁, s₃, s₄, s₅, s₆, hcg0, hcg1, hsnRel, hcg2, hsnAbs, hcg3, hsnReal, hcg4,
    ht0Valid, ht2Valid, ht3Valid, by rw [ht0Ns]; exact Nat.le_refl _,
    by rw [ht0Ns, ht2Ns]; exact Nat.le_refl _, by rw [ht2Ns, ht3Ns]; exact Nat.le_refl _⟩

/-- Non-vacuity `CanReach` witness for `test_timerand_ops_monotonicMultiCallAndNanosleepBounds`. -/
theorem reach_timerand_ops_monotonicMultiCallAndNanosleepBounds :
    CanReach (test_timerand_ops_monotonicMultiCallAndNanosleepBounds modelOps) := by
  refine ⟨default, { sec := 0, nsec := 0 }, { sec := 0, nsec := 0 }, by decide, by decide,
    by decide, ?_⟩
  exact proof_timerand_ops_monotonicMultiCallAndNanosleepBounds default { sec := 0, nsec := 0 }
    { sec := 0, nsec := 0 } (by decide) (by decide) (by decide)

/-- Proof of `test_timerand_ops_getrandom_flagsLengthsAndCrngState` for `modelOps`. -/
theorem proof_timerand_ops_getrandom_flagsLengthsAndCrngState :
    AllPass (test_timerand_ops_getrandom_flagsLengthsAndCrngState modelOps) := by
  intro s₀ len nb
  have hInv : ∀ l : UInt32,
      modelOps.getrandom l { nonblock := nb, random := true, insecure := true } s₀ =
        (.error Errno.EINVAL, s₀) := by
    intro l
    rw [modelOps_getrandom]
    rfl
  let sUnseeded : TimeRandState := { s₀ with crngReady := false }
  have hEa : modelOps.getrandom 16 { nonblock := true, insecure := false } sUnseeded =
      (.error Errno.EAGAIN, sUnseeded) := by
    rw [modelOps_getrandom]
    rfl
  let sAfterInsec : TimeRandState := { sUnseeded with crngReady := false, entropyDraws := sUnseeded.entropyDraws + 1 }
  have hInsec : modelOps.getrandom 16 { nonblock := true, insecure := true } sUnseeded =
      (.ok (deterministicEntropyBytes sUnseeded.entropyDraws 16), sAfterInsec) := by
    rw [modelOps_getrandom]
    rfl
  let sSeeded : TimeRandState := { sUnseeded with crngReady := true, entropyDraws := sUnseeded.entropyDraws + 1 }
  have hZero : modelOps.getrandom 0 {} sUnseeded = (.ok ByteArray.empty, sSeeded) := by
    rw [modelOps_getrandom]
    simp only [GrndFlags.isInvalid, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.and_false]
    have hb : deterministicEntropyBytes sUnseeded.entropyDraws 0 = ByteArray.empty := rfl
    simp [hb, sSeeded]
  let sDraw1 : TimeRandState := { sSeeded with crngReady := true, entropyDraws := sSeeded.entropyDraws + 1 }
  let sDraw2 : TimeRandState := { sDraw1 with crngReady := true, entropyDraws := sDraw1.entropyDraws + 1 }
  have hNb1 : modelOps.getrandom 16 { nonblock := true } sSeeded =
      (.ok (deterministicEntropyBytes sSeeded.entropyDraws 16), sDraw1) := by
    rw [modelOps_getrandom]
    rfl
  have hNb2 : modelOps.getrandom 16 { nonblock := true } sDraw1 =
      (.ok (deterministicEntropyBytes sDraw1.entropyDraws 16), sDraw2) := by
    rw [modelOps_getrandom]
    rfl
  dsimp (config := { zeta := false }) only [NondetTest.assert, Bind.bind, Pure.pure, StateT.run]
  refine ⟨hInv len, hInv 0, hEa, ?_⟩
  rw [hInsec]
  dsimp (config := { zeta := false }) only
  refine ⟨⟨⟨deterministicEntropyBytes sUnseeded.entropyDraws 16, rfl,
    deterministicEntropyBytes_size sUnseeded.entropyDraws 16⟩, rfl⟩, ?_⟩
  rw [hZero]
  dsimp (config := { zeta := false }) only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rw [hNb1]
  dsimp (config := { zeta := false, zetaDelta := false }) only
  rw [hNb2]
  dsimp (config := { zeta := false, zetaDelta := false }) only
  refine ⟨⟨deterministicEntropyBytes_size sSeeded.entropyDraws 16,
    deterministicEntropyBytes_size sDraw1.entropyDraws 16,
    deterministicEntropyBytes_succ_ne sSeeded.entropyDraws, rfl⟩, ?_⟩
  rw [modelOps_getrandom]
  simp only [GrndFlags.isInvalid, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, Bool.and_false]
  exact ⟨⟨deterministicEntropyBytes s₀.entropyDraws (min len.toNat MAX_READ_BYTES.toNat), rfl,
    deterministicEntropyBytes_size s₀.entropyDraws (min len.toNat MAX_READ_BYTES.toNat),
    by rw [deterministicEntropyBytes_size]; exact validGetrandomResultLen_eq len⟩, trivial⟩

end LeanSwe.LinuxSyscall.TimeRand.Proofs

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

private theorem ofNanosNat?_none {ns : Nat} (h : MAX_TIMESPEC_NANOS < ns) :
    Timespec.ofNanosNat? ns = none := by
  unfold Timespec.ofNanosNat?
  have hble : ns.ble MAX_TIMESPEC_NANOS = false := by
    cases hb : ns.ble MAX_TIMESPEC_NANOS
    · rfl
    · have := Nat.ble_eq.mp hb
      omega
  simp [hble]

private theorem ofNanosNat?_some {ns : Nat} (h : ns ≤ MAX_TIMESPEC_NANOS) :
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

private theorem ofEpochNanos?_spec (ns : Int) :
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

private theorem deterministicEntropyBytes_size (drawIdx len : Nat) :
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

private theorem validGetrandomResultLen_eq (len : UInt32) :
    validGetrandomResultLen len (min len.toNat MAX_READ_BYTES.toNat) = true := by
  unfold validGetrandomResultLen
  by_cases h0 : min len.toNat MAX_READ_BYTES.toNat = 0
  · simp [h0]
  · have hgt : 1 ≤ min len.toNat MAX_READ_BYTES.toNat := by omega
    by_cases hle : min len.toNat MAX_READ_BYTES.toNat ≤ GETRANDOM_EXACT_MAX
    · simp [h0, hle]
    · simp [h0, hle, hgt]

private theorem modelOps_clock_gettime_realtime (s : TimeRandState) :
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

private theorem modelOps_clock_gettime_monotonic (s : TimeRandState) :
    modelOps.clock_gettime .monotonic s =
      match Timespec.ofNanosNat? s.monoLowerBoundNs with
      | some ts => (Except.ok ts, { s with monoLowerBoundNs := ts.toNanosNat })
      | none =>
        (Except.ok { sec := Int64.ofInt (Int.ofNat MAX_TIMESPEC_SEC), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) }, s) := by
  dsimp only [modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set]
  cases Timespec.ofNanosNat? s.monoLowerBoundNs <;> simp [StateT.pure, StateT.set, StateT.bind] <;> rfl

private theorem modelOps_clock_nanosleep (clk : ClockId) (abs : Bool) (req : Timespec)
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

private theorem modelOps_getrandom (len : UInt32) (flags : GrndFlags) (s : TimeRandState) :
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

private theorem allowedStep_clock_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let negReal : Timespec := { sec := -1, nsec := 999999999 }
    let badNsec : Timespec := { sec := 0, nsec := 1000000000 }
    let sPos : TimeRandState := { s with monoLowerBoundNs := 5000 }
    let sZero : TimeRandState := { s with monoLowerBoundNs := 0, realtimeNs := 0 }
    allowedStep s (.clock_gettime .realtime) (.timespec negReal) = some s ∧
    allowedStep s (.clock_gettime .realtime) (.timespec badNsec) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.timespec negReal) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.timespec badNsec) = none ∧
    allowedStep sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 4999 }) = none ∧
    allowedStep sPos (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 5000 }) =
      some { sPos with monoLowerBoundNs := 5000 } ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.EINTR) = none ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.ENOMEM) = none ∧
    allowedStep sZero (.clock_gettime .realtime) (.err Errno.EIO) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.EINTR) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.ENOMEM) = none ∧
    allowedStep sZero (.clock_gettime .monotonic) (.err Errno.EIO) = none := by
  have hzero : decide (-9223372036854775808 ≤ Int.ediv 0 1000000000 ∧ Int.ediv 0 1000000000 ≤ 9223372036854775807) = true := by decide
  simp [allowedStep, allowedStepCore, hs, Timespec.hasValidNsec, Timespec.isValid,
    Timespec.toNanosNat, MAX_TIMESPEC_SEC, MAX_TIMESPEC_NANOS,
    NSEC_PER_SEC] <;>
  exact hzero

private theorem allowedStep_sleep_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let negReal : Timespec := { sec := -1, nsec := 999999999 }
    let badNsec : Timespec := { sec := 0, nsec := 1000000000 }
    let sPos : TimeRandState := { s with monoLowerBoundNs := 5000 }
    let reqValid : Timespec := { sec := 0, nsec := 2000 }
    allowedStep s (.clock_nanosleep .realtime true negReal) .unit = none ∧
    allowedStep s (.clock_nanosleep .realtime true negReal) (.err Errno.EINVAL) = some s ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) .unit = none ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINTR) = none ∧
    allowedStep s (.clock_nanosleep .monotonic false badNsec) (.err Errno.EINVAL) = some s ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) .unit =
      some { sPos with monoLowerBoundNs := 7000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic true reqValid) .unit =
      some { sPos with monoLowerBoundNs := 5000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic true { sec := 0, nsec := 9000 }) .unit =
      some { sPos with monoLowerBoundNs := 9000 } ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINTR) = some sPos ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EINVAL) = none ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOMEM) = none ∧
    allowedStep sPos (.clock_nanosleep .monotonic false reqValid) (.err Errno.EIO) = none := by
  simp [allowedStep, allowedStepCore, hs, Timespec.isValid, Timespec.toNanosNat,
    MAX_TIMESPEC_NANOS, MAX_TIMESPEC_SEC, NSEC_PER_SEC,
    Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO]

private theorem allowedStep_rand_cases (s : TimeRandState) (hs : s.ambientSeccomp = false) :
    let sUnready : TimeRandState := { s with crngReady := false }
    let sReady : TimeRandState := { s with crngReady := true }
    let reqValid : Timespec := { sec := 0, nsec := 2000 }
    allowedStep s (.getrandom 0 { random := true, insecure := true }) (.bytes ByteArray.empty) = none ∧
    allowedStep s (.getrandom 0 { random := true, insecure := true }) (.err Errno.EINVAL) = some s ∧
    (allowedStep s (.getrandom 0 {}) (.bytes ByteArray.empty)).isSome = true ∧
    allowedStep s (.getrandom 0 {}) (.bytes (ByteArray.mk #[1])) = none ∧
    allowedStep s (.getrandom 16 {}) (.bytes (ByteArray.mk #[1, 2, 3])) = none ∧
    (allowedStep s (.getrandom 300 {}) (.bytes (ByteArray.mk #[1, 2, 3]))).isSome = true ∧
    allowedStep s (.getrandom 300 {}) (.bytes ByteArray.empty) = none ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = some sUnready ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true, insecure := true }) (.err Errno.EAGAIN) = none ∧
    allowedStep sUnready (.getrandom 16 { nonblock := false }) (.err Errno.EAGAIN) = none ∧
    allowedStep sReady (.getrandom 16 { nonblock := true }) (.err Errno.EAGAIN) = none ∧
    allowedStep s (.getrandom 16 {}) (.err Errno.EMFILE) = none ∧
    allowedStep s (.getrandom 16 {}) (.err Errno.ENFILE) = none ∧
    allowedStep s (.clock_gettime .monotonic) (.err Errno.EMFILE) = none ∧
    allowedStep s (.clock_nanosleep .monotonic false reqValid) (.err Errno.ENOSPC) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.EINTR) = some sUnready ∧
    allowedStep sUnready (.getrandom 16 { nonblock := true }) (.err Errno.EINTR) = none ∧
    allowedStep sUnready (.getrandom 16 { insecure := true }) (.err Errno.EINTR) = none ∧
    allowedStep sReady (.getrandom 16 {}) (.err Errno.EINTR) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.ENOMEM) = none ∧
    allowedStep sUnready (.getrandom 16 {}) (.err Errno.EIO) = none := by
  cases hc : s.crngReady <;>
    simp [allowedStep, allowedStepCore, hs, Timespec.isValid, GrndFlags.isInvalid,
      validGetrandomResultLen, NSEC_PER_SEC, GETRANDOM_EXACT_MAX,
      MAX_READ_BYTES, Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.EAGAIN,
      Errno.EMFILE, Errno.ENFILE, Errno.ENOSPC, hc]

/-- Proof of `test_timerand_allowedStep_exactKernelSemantics` for `allowedStep`. -/
theorem proof_timerand_allowedStep_exactKernelSemantics :
    AllPass (test_timerand_allowedStep_exactKernelSemantics) := by
  intro sRaw
  let s : TimeRandState := { sRaw with ambientSeccomp := false }
  have hs : s.ambientSeccomp = false := rfl
  have hc := allowedStep_clock_cases s hs
  have hs' := allowedStep_sleep_cases s hs
  have hr := allowedStep_rand_cases s hs
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
    hs'.1, hs'.2.1, hs'.2.2.1, hs'.2.2.2.1, hs'.2.2.2.2.1, hs'.2.2.2.2.2.1,
    hs'.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.2.1,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2,
    hs'.2.2.2.2.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2.2.2.2.2,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    trivial⟩

/-- Proof of `test_timerand_allowedStep_withOuterSeccomp` for `allowedStep`. -/
theorem proof_timerand_allowedStep_withOuterSeccomp :
    AllPass (test_timerand_allowedStep_withOuterSeccomp) := by
  intro sBase
  dsimp only [test_timerand_allowedStep_withOuterSeccomp, Core.NondetTest.assert, Bind.bind]
  simp [TimeRandState.initial, TimeRandState.withOuterSeccomp, allowedStep, allowedStepCore,
    Timespec.isValid, Timespec.toNanosNat, GrndFlags.isInvalid,
    MAX_TIMESPEC_NANOS, MAX_TIMESPEC_SEC,
    NSEC_PER_SEC, Errno.EPERM, Errno.EACCES, Errno.ENOSYS, Errno.EAGAIN, Errno.EINVAL,
    Errno.EFAULT, Errno.EINTR]

/-- Proof of `test_timerand_modelOps_soundAgainstAllowedStep` for `modelOps` and `allowedStep`. -/
theorem proof_timerand_modelOps_soundAgainstAllowedStep :
    AllPass (test_timerand_modelOps_soundAgainstAllowedStep modelOps) := by
  intro s clk abstime req len flags
  dsimp (config := { zeta := false }) only [NondetTest.assert, Bind.bind, StateT.run]
  change (allowedStep s (.clock_gettime clk) (outcomeOfTimespec (modelOps.clock_gettime clk s).1) =
      some (modelOps.clock_gettime clk s).2) ∧
    (allowedStep s (.clock_nanosleep clk abstime req) (outcomeOfUnit (modelOps.clock_nanosleep clk abstime req s).1) =
      some (modelOps.clock_nanosleep clk abstime req s).2) ∧
    (allowedStep s (.getrandom len flags) (outcomeOfBytes (modelOps.getrandom len flags s).1) =
      some (modelOps.getrandom len flags s).2) ∧ True
  refine ⟨?_, ?_, ?_, trivial⟩
  · cases clk
    · have hspec := ofEpochNanos?_spec s.realtimeNs
      dsimp only at hspec
      rw [modelOps_clock_gettime_realtime]
      split at hspec
      · rcases hspec with ⟨ts, htsEq, htsValid, _⟩
        rw [htsEq]
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, htsValid]
      · rw [hspec]
        let clampedSec : Int64 :=
          if s.realtimeNs < 0 then Int64.minValue else Int64.maxValue
        let clampedNsec : UInt32 :=
          if s.realtimeNs < 0 then 0 else UInt32.ofNat (NSEC_PER_SEC - 1)
        let clampedTs : Timespec := { sec := clampedSec, nsec := clampedNsec }
        have hval : clampedTs.hasValidNsec = true := by
          dsimp only [clampedTs, clampedNsec, Timespec.hasValidNsec, NSEC_PER_SEC]
          by_cases hneg : s.realtimeNs < 0 <;> simp [hneg] <;> decide
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hval, clampedTs, clampedSec, clampedNsec]
    · rw [modelOps_clock_gettime_monotonic]
      by_cases hm : s.monoLowerBoundNs ≤ MAX_TIMESPEC_NANOS
      · obtain ⟨ts, htsEq, htsValid, htsNs⟩ := ofNanosNat?_some hm
        rw [htsEq]
        have hmin : min s.monoLowerBoundNs MAX_TIMESPEC_NANOS = s.monoLowerBoundNs := Nat.min_eq_left hm
        cases hsec : s.ambientSeccomp <;>
          simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, htsValid, htsNs, hmin]
      · have hgt : MAX_TIMESPEC_NANOS < s.monoLowerBoundNs := Nat.lt_of_not_le hm
        have hnone := ofNanosNat?_none hgt
        rw [hnone]
        have hmin : min s.monoLowerBoundNs MAX_TIMESPEC_NANOS = MAX_TIMESPEC_NANOS :=
          Nat.min_eq_right (Nat.le_of_lt hgt)
        have hmax : max s.monoLowerBoundNs MAX_TIMESPEC_NANOS = s.monoLowerBoundNs :=
          Nat.max_eq_left (Nat.le_of_lt hgt)
        have hval : Timespec.isValid { sec := Int64.ofInt (MAX_TIMESPEC_SEC : Int), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) } = true := by decide
        have hns : Timespec.toNanosNat { sec := Int64.ofInt (MAX_TIMESPEC_SEC : Int), nsec := UInt32.ofNat (NSEC_PER_SEC - 1) } = MAX_TIMESPEC_NANOS := by decide
        cases hsec : s.ambientSeccomp
        · simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hmin]
          rw [hval, hns]
          cases s; simp_all
        · simp [outcomeOfTimespec, allowedStep, allowedStepCore, hsec, hmin]
          rw [hval, hns]
          cases s; simp_all
  · rw [modelOps_clock_nanosleep]
    by_cases hv : req.isValid = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hsec : s.ambientSeccomp <;> cases clk <;>
        simp [outcomeOfUnit, allowedStep, allowedStepCore, hsec, hv]
    · have hfalse : req.isValid = false := by
        cases hb : req.isValid <;> simp_all
      cases hsec : s.ambientSeccomp <;>
        simp [hfalse, outcomeOfUnit, allowedStep, allowedStepCore, hsec, Errno.EINVAL, Errno.EFAULT]
  · rw [modelOps_getrandom]
    by_cases hinv : flags.isInvalid = true
    · cases hsec : s.ambientSeccomp <;>
        simp [hinv, outcomeOfBytes, allowedStep, allowedStepCore, hsec, Errno.EINVAL, Errno.EFAULT]
    · have hinvFalse : flags.isInvalid = false := by
        cases hb : flags.isInvalid <;> simp_all
      simp only [hinvFalse, Bool.false_eq_true, ↓reduceIte]
      by_cases hea : (!s.crngReady && flags.nonblock && !flags.insecure) = true
      · simp only [hea, ↓reduceIte, outcomeOfBytes]
        cases hsec : s.ambientSeccomp
        · simp only [allowedStep, allowedStepCore, hsec, Bool.false_eq_true, ↓reduceIte, hinvFalse, hea]
          rfl
        · simp [allowedStep, hsec, Errno.EAGAIN, Errno.EFAULT]
      · have heaFalse : (!s.crngReady && flags.nonblock && !flags.insecure) = false := by
          cases hb : (!s.crngReady && flags.nonblock && !flags.insecure) <;> simp_all
        simp only [heaFalse, Bool.false_eq_true, ↓reduceIte, outcomeOfBytes]
        have hlen : validGetrandomResultLen len
            (deterministicEntropyBytes s.entropyDraws (min len.toNat MAX_READ_BYTES.toNat)).size = true := by
          rw [deterministicEntropyBytes_size]
          exact validGetrandomResultLen_eq len
        cases hsec : s.ambientSeccomp <;>
          simp [allowedStep, allowedStepCore, hsec, hinvFalse, hlen]

/-- Exact disjoint partition of `Errno.isTransientOsErrno` into `EINTR`, `Errno.isCriticalOsErrno`, and `Errno.isResourceLimitErrno`. -/
theorem errno_transient_partition (e : Errno) :
    Errno.isTransientOsErrno e =
      (e == Errno.EINTR || Errno.isCriticalOsErrno e || Errno.isResourceLimitErrno e) ∧
    (Errno.isCriticalOsErrno e && Errno.isResourceLimitErrno e) = false := by
  refine ⟨?_, ?_⟩
  · unfold Errno.isTransientOsErrno Errno.isCriticalOsErrno Errno.isResourceLimitErrno
    cases e == Errno.EINTR <;> cases e == Errno.EIO <;> cases e == Errno.ENOMEM <;>
      cases e == Errno.ENFILE <;> cases e == Errno.EMFILE <;> cases e == Errno.ENOSPC <;> rfl
  · by_cases h1 : e == Errno.ENOMEM
    · have : e = Errno.ENOMEM := eq_of_beq h1
      subst this; decide
    · by_cases h2 : e == Errno.EIO
      · have : e = Errno.EIO := eq_of_beq h2
        subst this; decide
      · by_cases h3 : e == Errno.ENFILE
        · have : e = Errno.ENFILE := eq_of_beq h3
          subst this; decide
        · simp [Errno.isCriticalOsErrno, h1, h2, h3]

private theorem allowedStepCore_preserves_ambientSeccomp
    (s s' : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : allowedStepCore s req out = some s') :
    s'.ambientSeccomp = s.ambientSeccomp := by
  cases req with
  | clock_gettime clk =>
    cases out with
    | timespec ts =>
      cases clk <;> simp only [allowedStepCore] at h <;> split at h <;>
        first | contradiction | (injection h with hEq; rw [← hEq])
    | _ => simp [allowedStepCore] at h
  | clock_nanosleep clk abstime reqTs =>
    simp only [allowedStepCore] at h
    split at h
    · cases out with
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
    · cases out with
      | unit =>
        cases clk <;> simp only at h <;> injection h with hEq <;> rw [← hEq]
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
  | getrandom len flags =>
    simp only [allowedStepCore] at h
    split at h
    · cases out with
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h
    · cases out with
      | bytes got =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | err e =>
        simp only at h
        split at h <;> first | contradiction | (injection h with hEq; rw [← hEq])
      | _ => simp at h

private theorem allowedStepCore_not_critical
    (s s' : TimeRandState) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : allowedStepCore s req out = some s') :
    isCriticalFault out = false := by
  cases out with
  | unit | timespec _ | bytes _ => rfl
  | err e =>
    cases req with
    | clock_gettime clk => simp [allowedStepCore] at h
    | clock_nanosleep clk abstime reqTs =>
      simp only [allowedStepCore] at h
      split at h
      · split at h
        · rename_i heq
          have : e = Errno.EINVAL := eq_of_beq heq
          subst this; decide
        · contradiction
      · split at h
        · rename_i heq
          have : e = Errno.EINTR := eq_of_beq heq
          subst this; decide
        · contradiction
    | getrandom len flags =>
      simp only [allowedStepCore] at h
      split at h
      · split at h
        · rename_i heq
          have : e = Errno.EINVAL := eq_of_beq heq
          subst this; decide
        · contradiction
      · split at h
        · rename_i hcond
          rcases Bool.or_eq_true_iff.mp hcond with h1 | h2
          · simp only [Bool.and_eq_true] at h1
            have : e = Errno.EAGAIN := eq_of_beq h1.2
            subst this; decide
          · simp only [Bool.and_eq_true] at h2
            have : e = Errno.EINTR := eq_of_beq h2.2
            subst this; decide
        · contradiction

/-- Initial healthy `TimeRand` environments satisfy `HealthyEnv.wf`. -/
theorem healthyEnv_initial_wf (budget : Nat) (realtimeNs : Int) (crngReady : Bool) :
    (HealthyEnv.initial budget realtimeNs crngReady).wf = true :=
  rfl

/-- Tightness by construction: every `allowedStep` transition from a healthy `TimeRand` environment without curated critical faults (and with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    (env : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome) (s' : TimeRandState)
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget)
    (hNoCrit : isCriticalFault out = false) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hb : env.eintrBudget > 0 := hBudget hEi
    simp [hb]

/-- Soundness of `healthyStep` with respect to `allowedStep`: every `healthyStep` transition is a valid `allowedStep` transition, preserves `HealthyEnv.wf`, excludes curated critical OS faults, and strictly decreases `eintrBudget` on `EINTR`. -/
theorem healthyStep_implies_allowedStep
    (env env' : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    env.wf = true ∧
    env'.wf = true ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env'.eintrBudget < env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by
      cases hw : env.wf <;> simp_all
    have hNoCrit : isCriticalFault out = false := by
      cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => rw [hAl] at h; contradiction
    | some s' =>
      rw [hAl] at h
      dsimp only at h
      have hSecF : env.state.ambientSeccomp = false := by
        unfold HealthyEnv.wf at hWf
        cases hb : env.state.ambientSeccomp <;> simp_all
      have hCore : allowedStepCore env.state req out = some s' := by
        simpa [allowedStep, hSecF] using hAl
      have hSec' : s'.ambientSeccomp = false := by
        rw [allowedStepCore_preserves_ambientSeccomp _ _ _ _ hCore, hSecF]
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        dsimp only
        exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec'], hNoCrit, Nat.le_refl _, fun hc => by cases hc⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hb : env.eintrBudget > 0
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          subst h
          dsimp only
          exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec'], hNoCrit, Nat.sub_le _ _, fun _ => by omega⟩
        · simp [hb] at h

/-- Reference `healthyModelOps` refines `healthyStep` universally across all requests. -/
theorem healthyModelOps_refinesHealthyTimeRand :
    RefinesHealthyTimeRand healthyModelOps := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  have hSound := proof_timerand_modelOps_soundAgainstAllowedStep env.state
  have hSecF : env.state.ambientSeccomp = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  cases req with
  | clock_gettime clk =>
    have h1 := (hSound clk false default 0 {}).1
    have hCore : allowedStepCore env.state (.clock_gettime clk)
        (outcomeOfTimespec (modelOps.clock_gettime clk env.state).1) =
        some (modelOps.clock_gettime clk env.state).2 := by
      simpa [allowedStep, hSecF] using h1
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfTimespec (modelOps.clock_gettime clk env.state).1) = false := by
      cases clk
      · rw [modelOps_clock_gettime_realtime]
        cases Timespec.ofEpochNanos? env.state.realtimeNs <;> rfl
      · rw [modelOps_clock_gettime_monotonic]
        cases Timespec.ofNanosNat? env.state.monoLowerBoundNs <;> rfl
    have hTight := allowedStep_healthy_tight env (.clock_gettime clk) _ _ h1 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.clock_gettime, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight
  | clock_nanosleep clk abstime reqTs =>
    have h2 := (hSound clk abstime reqTs 0 {}).2.1
    have hCore : allowedStepCore env.state (.clock_nanosleep clk abstime reqTs)
        (outcomeOfUnit (modelOps.clock_nanosleep clk abstime reqTs env.state).1) =
        some (modelOps.clock_nanosleep clk abstime reqTs env.state).2 := by
      simpa [allowedStep, hSecF] using h2
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfUnit (modelOps.clock_nanosleep clk abstime reqTs env.state).1) = false := by
      rw [modelOps_clock_nanosleep]
      split
      · dsimp only; decide
      · cases clk <;> rfl
    have hTight := allowedStep_healthy_tight env (.clock_nanosleep clk abstime reqTs) _ _ h2 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.clock_nanosleep, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight
  | getrandom len flags =>
    have h3 := (hSound .realtime false default len flags).2.2.1
    have hCore : allowedStepCore env.state (.getrandom len flags)
        (outcomeOfBytes (modelOps.getrandom len flags env.state).1) =
        some (modelOps.getrandom len flags env.state).2 := by
      simpa [allowedStep, hSecF] using h3
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfBytes (modelOps.getrandom len flags env.state).1) = false := by
      rw [modelOps_getrandom]
      by_cases h1 : flags.isInvalid = true
      · simp [h1]; decide
      · by_cases h2 : (!env.state.crngReady && flags.nonblock && !flags.insecure) = true
        · simp [h1, h2]; decide
        · simp [h1, h2, outcomeOfBytes, isEintrOutcome]
    have hTight := allowedStep_healthy_tight env (.getrandom len flags) _ _ h3 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.getrandom, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight

/-- Over any `ops` satisfying `RefinesHealthyTimeRandAt proj ops`, `clock_gettime` succeeds unconditionally without consuming `eintrBudget`. -/
theorem refinesHealthy_clock_gettime_ok
    {W : Type} {proj : W → HealthyEnv} {ops : TimeRandOpsM (StateM W)}
    (hRef : RefinesHealthyTimeRandAt proj ops)
    (w : W) (clk : ClockId) (hWf : (proj w).wf = true) :
    ∃ ts w', (ops.clock_gettime clk).run w = (.ok ts, w') ∧
      (proj w').wf = true ∧
      (proj w').eintrBudget = (proj w).eintrBudget ∧
      allowedStepCore (proj w).state (.clock_gettime clk) (.timespec ts) = some (proj w').state := by
  have hStep := hRef w (.clock_gettime clk) hWf
  dsimp only [execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
  cases hRun : (ops.clock_gettime clk).run w with
  | mk res w' =>
    change (ops.clock_gettime clk) w = (res, w') at hRun
    rw [hRun] at hStep
    dsimp only at hStep
    rcases healthyStep_implies_allowedStep (proj w) (proj w') (.clock_gettime clk)
      (outcomeOfTimespec res) hStep with ⟨hAl, _, hWf', _, _, _⟩
    have hSecF : (proj w).state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf
      cases hb : (proj w).state.ambientSeccomp <;> simp_all
    have hCore : allowedStepCore (proj w).state (.clock_gettime clk) (outcomeOfTimespec res) =
        some (proj w').state := by
      simpa [allowedStep, hSecF] using hAl
    cases res with
    | error e =>
      simp [outcomeOfTimespec, allowedStepCore] at hCore
    | ok ts =>
      have hBud : (proj w').eintrBudget = (proj w).eintrBudget := by
        unfold healthyStep at hStep
        rw [hAl] at hStep
        simp only [hWf, Bool.not_true, isCriticalFault, outcomeOfTimespec, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte, isEintrOutcome, Option.some.injEq] at hStep
        exact (congrArg HealthyEnv.eintrBudget hStep).symm
      exact ⟨ts, w', rfl, hWf', hBud, hCore⟩

/-- Lens-lifting composition theorem: lifting any `ops` satisfying `RefinesHealthyTimeRand` along `(getEnv, setEnv)` with `∀ w e, getEnv (setEnv w e) = e` satisfies `RefinesHealthyTimeRandAt getEnv`. -/
theorem refinesHealthyTimeRandAt_of_lens
    {W : Type} (getEnv : W → HealthyEnv) (setEnv : W → HealthyEnv → W)
    (hGetSet : ∀ (w : W) (e : HealthyEnv), getEnv (setEnv w e) = e)
    {ops : TimeRandOpsM (StateM HealthyEnv)} (hRef : RefinesHealthyTimeRand ops) :
    RefinesHealthyTimeRandAt getEnv
      { clock_gettime := fun clk w =>
          let (res, e') := (ops.clock_gettime clk).run (getEnv w); (res, setEnv w e')
        clock_nanosleep := fun clk abstime reqTs w =>
          let (res, e') := (ops.clock_nanosleep clk abstime reqTs).run (getEnv w); (res, setEnv w e')
        getrandom := fun len flags w =>
          let (res, e') := (ops.getrandom len flags).run (getEnv w); (res, setEnv w e') } := by
  intro w req hWf
  have hStep := hRef (getEnv w) req hWf
  cases req with
  | clock_gettime clk =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.clock_gettime clk (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep
  | clock_nanosleep clk abstime reqTs =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.clock_nanosleep clk abstime reqTs (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep
  | getrandom len flags =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.getrandom len flags (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep

/-- Proof of `test_timerand_healthyStep_and_healthyModelOps`. -/
theorem proof_timerand_healthyStep_and_healthyModelOps :
    AllPass test_timerand_healthyStep_and_healthyModelOps := by
  dsimp only [test_timerand_healthyStep_and_healthyModelOps, NondetTest.assert, Bind.bind, Pure.pure]
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro env hWf clk abstime sleepTs len flags
    obtain ⟨ts, envGet, hRunGet, hWfGet, hBudGet, _⟩ :=
      refinesHealthy_clock_gettime_ok healthyModelOps_refinesHealthyTimeRand env clk hWf
    have hStepGet := healthyModelOps_refinesHealthyTimeRand env (.clock_gettime clk) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepGet
    have hStepSleep := healthyModelOps_refinesHealthyTimeRand env (.clock_nanosleep clk abstime sleepTs) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepSleep
    have hStepRand := healthyModelOps_refinesHealthyTimeRand env (.getrandom len flags) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepRand
    refine ⟨?_, ?_, ?_, fun _ _ _ => ⟨rfl, trivial⟩⟩
    · have hLiftG : (healthyModelOps.clock_gettime clk).run env =
          (let (mGet, sGet) := (modelOps.clock_gettime clk).run env.state; (mGet, { env with state := sGet })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.clock_gettime clk).run env.state <;> rfl
      show (healthyModelOps.clock_gettime clk).run env =
          (let (mGet, sGet) := (modelOps.clock_gettime clk).run env.state; (mGet, { env with state := sGet })) ∧
        (∃ ts, (healthyModelOps.clock_gettime clk env).1 = .ok ts) ∧
        healthyStep env (.clock_gettime clk) (outcomeOfTimespec (healthyModelOps.clock_gettime clk env).1) =
          some (healthyModelOps.clock_gettime clk env).2 ∧
        (healthyModelOps.clock_gettime clk env).2.wf = true ∧
        (healthyModelOps.clock_gettime clk env).2.eintrBudget = env.eintrBudget
      change healthyModelOps.clock_gettime clk env = (.ok ts, envGet) at hRunGet
      refine ⟨hLiftG, ?_⟩
      rw [hRunGet] at hStepGet ⊢
      dsimp only at hStepGet ⊢
      exact ⟨⟨ts, rfl⟩, hStepGet, hWfGet, hBudGet⟩
    · have hLiftS : (healthyModelOps.clock_nanosleep clk abstime sleepTs).run env =
          (let (mSleep, sSleep) := (modelOps.clock_nanosleep clk abstime sleepTs).run env.state; (mSleep, { env with state := sSleep })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.clock_nanosleep clk abstime sleepTs).run env.state <;> rfl
      show (healthyModelOps.clock_nanosleep clk abstime sleepTs).run env =
          (let (mSleep, sSleep) := (modelOps.clock_nanosleep clk abstime sleepTs).run env.state; (mSleep, { env with state := sSleep })) ∧
        healthyStep env (.clock_nanosleep clk abstime sleepTs)
          (outcomeOfUnit (healthyModelOps.clock_nanosleep clk abstime sleepTs env).1) =
          some (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2 ∧
        (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2.wf = true ∧
        (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftS, ?_⟩
      cases hS : healthyModelOps.clock_nanosleep clk abstime sleepTs env with
      | mk rSleep envSleep =>
        rw [hS] at hStepSleep
        dsimp only at hStepSleep ⊢
        have hWfS := (healthyStep_implies_allowedStep env envSleep _ _ hStepSleep).2.2.1
        have hBudS : envSleep.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hS
          cases modelOps.clock_nanosleep clk abstime sleepTs env.state with
          | mk r0 s0 =>
            injection hS with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepSleep, hWfS, hBudS⟩
    · have hLiftR : (healthyModelOps.getrandom len flags).run env =
          (let (mRand, sRand) := (modelOps.getrandom len flags).run env.state; (mRand, { env with state := sRand })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.getrandom len flags).run env.state <;> rfl
      show (healthyModelOps.getrandom len flags).run env =
          (let (mRand, sRand) := (modelOps.getrandom len flags).run env.state; (mRand, { env with state := sRand })) ∧
        healthyStep env (.getrandom len flags)
          (outcomeOfBytes (healthyModelOps.getrandom len flags env).1) =
          some (healthyModelOps.getrandom len flags env).2 ∧
        (healthyModelOps.getrandom len flags env).2.wf = true ∧
        (healthyModelOps.getrandom len flags env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftR, ?_⟩
      cases hR : healthyModelOps.getrandom len flags env with
      | mk rRand envRand =>
        rw [hR] at hStepRand
        dsimp only at hStepRand ⊢
        have hWfR := (healthyStep_implies_allowedStep env envRand _ _ hStepRand).2.2.1
        have hBudR : envRand.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hR
          cases modelOps.getrandom len flags env.state with
          | mk r0 s0 =>
            injection hR with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepRand, hWfR, hBudR⟩

/-- Reachability witness for `test_timerand_healthyStep_and_healthyModelOps`. -/
theorem reach_timerand_healthyStep_and_healthyModelOps :
    CanReach test_timerand_healthyStep_and_healthyModelOps := by
  have hAll := proof_timerand_healthyStep_and_healthyModelOps
  have hRest := hAll.2.2.2.2.2 (HealthyEnv.initial 1 0 false) rfl .monotonic false { sec := 0, nsec := 0 } 0 {}
  refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    HealthyEnv.initial 1 0 false, rfl, .monotonic, false, { sec := 0, nsec := 0 }, 0, {},
    hRest.1, hRest.2.1, hRest.2.2.1,
    HealthyEnv.initial 1 0 false, .clock_gettime .monotonic, .timespec { sec := 0, nsec := 0 }, ?_⟩
  exact hRest.2.2.2 (HealthyEnv.initial 1 0 false) (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 0 })

end LeanSwe.LinuxSyscall.TimeRand.Proofs

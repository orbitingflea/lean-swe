import Core.Assumptions
import Core.Obeys
import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.Model
import LeanSwe.Uuid.SpecTests
import LeanSwe.Uuid.Proofs.Codec
import LeanSwe.Uuid.Proofs.Entropy
import LeanSwe.Uuid.Proofs.RefinesModel

/-!
# Verified RFC 4122 UUIDv4 Specification Proofs

Top-level entry point exporting all `52` specification proofs (`proof_uuid_*`),
non-vacuity witnesses (`reach_uuid_*`), and error-kind impossibility theorems
(`uuid_*_never_*`). Reusable theory lives in `Proofs/Codec.lean` and `Proofs/Entropy.lean`.
-/

namespace LeanSwe.Uuid.Proofs

open Core Core.NondetTest LeanSwe.Uuid LeanSwe.Uuid.Proofs.Codec LeanSwe.Uuid.Proofs.Entropy
open LeanSwe.LinuxSyscall (Errno)

/-- Proof of `test_uuid_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_uuid_mapRawError_returnsNonEmptyMessage :
    AllPass (test_uuid_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw; cases raw <;> exact ⟨⟨rfl, mapRawError_msg_ne _⟩, rfl, trivial⟩

/-- Proof of `test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload` for `defaultApi`. -/
theorem proof_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload :
    AllPass (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload defaultApi) := by
  intro bs hlen; obtain ⟨u, hfr, ⟨hsz, hv6, hv8⟩, hlo6, hlo8, hoth⟩ := fromRandomBytes_spec hlen
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
  rw [hfr]; exact ⟨hsz, hv6, hv8, hlo6, hlo8, fun i ⟨hi, hi6, hi8⟩ => ⟨hoth i hi hi6 hi8, trivial⟩⟩
/-- Non-vacuity witness for `test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload`. -/
theorem reach_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload :
    CanReach (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload defaultApi) := by
  have h := proof_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload zeros16 rfl
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert] at h ⊢
  exact ⟨zeros16, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, 0, by decide, h.2.2.2.2.2 0 (by decide)⟩

/-- Proof of `test_uuid_fromRandomBytes_invalidLen_returnsError` for `defaultApi`. -/
theorem proof_uuid_fromRandomBytes_invalidLen_returnsError :
    AllPass (test_uuid_fromRandomBytes_invalidLen_returnsError defaultApi) := by
  intro bs hne
  dsimp [test_uuid_fromRandomBytes_invalidLen_returnsError, defaultApi, Internal.mkApi, Internal.fromRandomBytes, Bind.bind, Core.NondetTest.assert]
  rw [bne_iff_ne.mpr hne]; exact ⟨⟨rfl, append_ne_empty (by decide)⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_fromRandomBytes_invalidLen_returnsError`. -/
theorem reach_uuid_fromRandomBytes_invalidLen_returnsError :
    CanReach (test_uuid_fromRandomBytes_invalidLen_returnsError defaultApi) :=
  ⟨ByteArray.empty, by decide, proof_uuid_fromRandomBytes_invalidLen_returnsError ByteArray.empty (by decide)⟩

/-- Proof of `test_uuid_toString_formatAndRoundTrip` for `defaultApi`. -/
theorem proof_uuid_toString_formatAndRoundTrip :
    AllPass (test_uuid_toString_formatAndRoundTrip defaultApi) := by
  intro bs hlen; obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  obtain ⟨hlen36, d8, d13, d18, d23, hall, h14, h19, hparse, _⟩ := toString_spec hv
  dsimp [test_uuid_toString_formatAndRoundTrip, defaultApi, Internal.mkApi, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [hfr]; exact ⟨hlen36, ⟨d8, d13, d18, d23⟩, hall, h14, h19, hparse, by rw [hparse]; rfl, trivial⟩
/-- Non-vacuity witness for `test_uuid_toString_formatAndRoundTrip`. -/
theorem reach_uuid_toString_formatAndRoundTrip :
    CanReach (test_uuid_toString_formatAndRoundTrip defaultApi) :=
  ⟨zeros16, rfl, proof_uuid_toString_formatAndRoundTrip zeros16 rfl⟩

/-- Proof of `test_uuid_toHex_formatAndRoundTrip` for `defaultApi`. -/
theorem proof_uuid_toHex_formatAndRoundTrip :
    AllPass (test_uuid_toHex_formatAndRoundTrip defaultApi) := by
  intro bs hlen; obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  obtain ⟨hlen32, hall, hfilt, hpHex, _, hpBad⟩ := toHex_spec hv
  dsimp [test_uuid_toHex_formatAndRoundTrip, defaultApi, Internal.mkApi, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [hfr]; refine ⟨hlen32, hall, hfilt, hpHex, by rw [hpBad]; rfl, ?_⟩
  rw [hpBad]; exact ⟨⟨rfl, append_ne_empty (by decide)⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_toHex_formatAndRoundTrip`. -/
theorem reach_uuid_toHex_formatAndRoundTrip :
    CanReach (test_uuid_toHex_formatAndRoundTrip defaultApi) :=
  ⟨zeros16, rfl, proof_uuid_toHex_formatAndRoundTrip zeros16 rfl⟩

/-- Proof of `test_uuid_toHex_bigEndianNibbleOrder` for `defaultApi`. -/
theorem proof_uuid_toHex_bigEndianNibbleOrder :
    AllPass (test_uuid_toHex_bigEndianNibbleOrder defaultApi) := by
  intro bs hlen; obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  dsimp [test_uuid_toHex_bigEndianNibbleOrder, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
  rw [hfr]; intro i hi; obtain ⟨h1, h2⟩ := toHex_bigEndian hv hi; exact ⟨h1, h2, trivial⟩
/-- Non-vacuity witness for `test_uuid_toHex_bigEndianNibbleOrder`. -/
theorem reach_uuid_toHex_bigEndianNibbleOrder :
    CanReach (test_uuid_toHex_bigEndianNibbleOrder defaultApi) := by
  have h := proof_uuid_toHex_bigEndianNibbleOrder zeros16 rfl 0 (by decide)
  dsimp [test_uuid_toHex_bigEndianNibbleOrder, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert] at h ⊢
  exact ⟨zeros16, rfl, 0, by decide, h⟩

/-- Proof of `test_uuid_parse_acceptsUppercaseHex` for `defaultApi`. -/
theorem proof_uuid_parse_acceptsUppercaseHex :
    AllPass (test_uuid_parse_acceptsUppercaseHex defaultApi) := by
  intro bs hlen; obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  have hstrUp := (toString_spec hv).2.2.2.2.2.2.2.2.2; have hhexUp := (toHex_spec hv).2.2.2.2.1
  dsimp [test_uuid_parse_acceptsUppercaseHex, defaultApi, Internal.mkApi, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [hfr]; exact ⟨hstrUp, by rw [hstrUp]; rfl, hhexUp, trivial⟩
/-- Non-vacuity witness for `test_uuid_parse_acceptsUppercaseHex`. -/
theorem reach_uuid_parse_acceptsUppercaseHex :
    CanReach (test_uuid_parse_acceptsUppercaseHex defaultApi) :=
  ⟨zeros16, rfl, proof_uuid_parse_acceptsUppercaseHex zeros16 rfl⟩

/-- Proof of `test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip` for `defaultApi`. -/
theorem proof_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip :
    AllPass (test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip defaultApi) := by
  intro s; dsimp [test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip, defaultApi, Internal.mkApi, Internal.parse, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  cases hp : Internal.parseCanonicalChars s.toList with
  | error _ => exact ⟨⟨parseCanonicalChars_err_msg hp, rfl⟩, trivial⟩
  | ok _ => obtain ⟨⟨hsz, hv6, hv8⟩, hstr⟩ := parseCanonicalChars_ok_props hp; exact ⟨rfl, hsz, hv6, hv8, hstr, trivial⟩

/-- Proof of `test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip` for `defaultApi`. -/
theorem proof_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip :
    AllPass (test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip defaultApi) := by
  intro s; dsimp [test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip, defaultApi, Internal.mkApi, Internal.parseHex, Internal.toHex, Bind.bind, Core.NondetTest.assert]
  cases hp : Internal.parseHexChars s.toList with
  | error _ => exact ⟨parseHexChars_err_msg hp, trivial⟩
  | ok _ => obtain ⟨⟨hsz, hv6, hv8⟩, hfmt⟩ := parseHexChars_ok_props hp; exact ⟨hsz, hv6, hv8, by rw [String.toList_ofList, hfmt], trivial⟩

/-- Proof of `test_uuid_parse_rejectsInvalidLength` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsInvalidLength :
    AllPass (test_uuid_parse_rejectsInvalidLength defaultApi) := by
  intro s hne
  dsimp [test_uuid_parse_rejectsInvalidLength, defaultApi, Internal.mkApi, Internal.parse, Internal.isValid, Internal.parseCanonicalChars, Bind.bind, Core.NondetTest.assert]
  have hbne : (s.toList.length != 36) = true := bne_iff_ne.mpr (by rw [String.length_toList]; exact hne)
  simp only [hbne, ↓reduceIte, Except.isOk, Except.toBool]; exact ⟨⟨trivial, append_ne_empty (by decide), trivial⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_parse_rejectsInvalidLength`. -/
theorem reach_uuid_parse_rejectsInvalidLength :
    CanReach (test_uuid_parse_rejectsInvalidLength defaultApi) :=
  ⟨"", by decide, proof_uuid_parse_rejectsInvalidLength "" (by decide)⟩

/-- Proof of `test_uuid_parse_rejectsNonHexChar` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsNonHexChar :
    AllPass (test_uuid_parse_rejectsNonHexChar defaultApi) := by
  intro s hlen idx ⟨hi, h8, h13, h18, h23⟩ hbad
  dsimp [test_uuid_parse_rejectsNonHexChar, defaultApi, Internal.mkApi, Internal.parse, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 36 := by rw [String.length_toList]; exact hlen
  cases hs : Internal.stripCanonicalHyphens s.toList with
  | none => simp [Internal.parseCanonicalChars, hclen, hs, Except.isOk, Except.toBool]
  | some hex =>
    obtain ⟨hhl, hmem⟩ := stripCanonicalHyphens_props hs hi h8 h13 h18 h23
    have hdec := decodeHexPairs_none_of_mem_bad hex s.toList[idx]! hmem hbad
    simp [Internal.parseCanonicalChars, hclen, hs, Internal.parseHexChars, hhl, hdec, Except.isOk, Except.toBool]
/-- Non-vacuity witness for `test_uuid_parse_rejectsNonHexChar`. -/
theorem reach_uuid_parse_rejectsNonHexChar :
    CanReach (test_uuid_parse_rejectsNonHexChar defaultApi) :=
  ⟨"g0000000-0000-4000-8000-000000000000", by decide, 0, by decide, by decide,
    proof_uuid_parse_rejectsNonHexChar "g0000000-0000-4000-8000-000000000000" (by decide) 0 (by decide) (by decide)⟩

/-- Proof of `test_uuid_parse_rejectsMissingHyphen` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsMissingHyphen :
    AllPass (test_uuid_parse_rejectsMissingHyphen defaultApi) := by
  intro s hlen hmiss
  dsimp [test_uuid_parse_rejectsMissingHyphen, defaultApi, Internal.mkApi, Internal.parse, Internal.isValid, Internal.parseCanonicalChars, Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 36 := by rw [String.length_toList]; exact hlen
  have hs : Internal.stripCanonicalHyphens s.toList = none := by
    have hhy : (s.toList[8]? != some '-' || s.toList[13]? != some '-' || s.toList[18]? != some '-' || s.toList[23]? != some '-') = true := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]; rcases hmiss with h | h | h | h <;> simp [h]
    unfold Internal.stripCanonicalHyphens; simp only [hclen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hhy]
  simp [hclen, hs, Except.isOk, Except.toBool]
/-- Non-vacuity witness for `test_uuid_parse_rejectsMissingHyphen`. -/
theorem reach_uuid_parse_rejectsMissingHyphen :
    CanReach (test_uuid_parse_rejectsMissingHyphen defaultApi) :=
  ⟨"000000000000040008000000000000000000", by decide, by decide,
    proof_uuid_parse_rejectsMissingHyphen "000000000000040008000000000000000000" (by decide) (by decide)⟩

/-- Proof of `test_uuid_parse_rejectsNonV4VersionOrVariant` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsNonV4VersionOrVariant :
    AllPass (test_uuid_parse_rejectsNonV4VersionOrVariant defaultApi) := by
  intro bs hlen badVer ⟨hverHex, hverNe⟩ badVar ⟨hvarHex, h8, h9, ha, hb, hA, hB⟩
  obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  dsimp [test_uuid_parse_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
  have hp1 := (badVer_rejects hv hverHex hverNe).2; have hp2 := (badVar_rejects hv hvarHex h8 h9 ha hb hA hB).2
  rw [hfr]; dsimp only; rw [hp1]; dsimp only; rw [hp2]; dsimp only
  exact ⟨⟨rfl, by decide, by unfold Internal.isValid; rw [hp1]; rfl⟩, ⟨rfl, by decide, by unfold Internal.isValid; rw [hp2]; rfl⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_parse_rejectsNonV4VersionOrVariant`. -/
theorem reach_uuid_parse_rejectsNonV4VersionOrVariant :
    CanReach (test_uuid_parse_rejectsNonV4VersionOrVariant defaultApi) :=
  (fun (bs : ByteArray) (hlen : bs.size = 16) => by
    obtain ⟨_, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
    have hp1 := (badVer_rejects hv (by decide) (by decide : '5' ≠ '4')).2
    have hp2 := (badVar_rejects hv (badVar := '0') (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    dsimp [test_uuid_parse_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
    refine ⟨bs, hlen, '5', by decide, '0', by decide, ?_⟩
    rw [hfr]; dsimp only; rw [hp1]; dsimp only; rw [hp2]; dsimp only
    exact ⟨⟨rfl, by decide, by unfold Internal.isValid; rw [hp1]; rfl⟩, ⟨rfl, by decide, by unfold Internal.isValid; rw [hp2]; rfl⟩, trivial⟩) zeros16 rfl

/-- Proof of `test_uuid_parseHex_rejectsInvalidLength` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsInvalidLength :
    AllPass (test_uuid_parseHex_rejectsInvalidLength defaultApi) := by
  intro s hne
  dsimp [test_uuid_parseHex_rejectsInvalidLength, defaultApi, Internal.mkApi, Internal.parseHex, Internal.parseHexChars, Bind.bind, Core.NondetTest.assert]
  have hbne : (s.toList.length != 32) = true := bne_iff_ne.mpr (by rw [String.length_toList]; exact hne)
  simp only [hbne, ↓reduceIte]; exact ⟨⟨trivial, append_ne_empty (by decide)⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_parseHex_rejectsInvalidLength`. -/
theorem reach_uuid_parseHex_rejectsInvalidLength :
    CanReach (test_uuid_parseHex_rejectsInvalidLength defaultApi) :=
  ⟨"", by decide, proof_uuid_parseHex_rejectsInvalidLength "" (by decide)⟩

/-- Proof of `test_uuid_parseHex_rejectsNonHexChar` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsNonHexChar :
    AllPass (test_uuid_parseHex_rejectsNonHexChar defaultApi) := by
  intro s hlen idx ⟨hidx, hbad⟩
  dsimp [test_uuid_parseHex_rejectsNonHexChar, defaultApi, Internal.mkApi, Internal.parseHex, Internal.parseHexChars, Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 32 := by rw [String.length_toList]; exact hlen
  have hmem : s.toList[idx]! ∈ s.toList := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (hclen ▸ hidx)]; exact List.getElem_mem _
  simp only [hclen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, decodeHexPairs_none_of_mem_bad s.toList s.toList[idx]! hmem hbad]; decide
/-- Non-vacuity witness for `test_uuid_parseHex_rejectsNonHexChar`. -/
theorem reach_uuid_parseHex_rejectsNonHexChar :
    CanReach (test_uuid_parseHex_rejectsNonHexChar defaultApi) :=
  ⟨"g0000000000040008000000000000000", by decide, 0, by decide,
    proof_uuid_parseHex_rejectsNonHexChar "g0000000000040008000000000000000" (by decide) 0 (by decide)⟩

/-- Proof of `test_uuid_parseHex_rejectsNonV4VersionOrVariant` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsNonV4VersionOrVariant :
    AllPass (test_uuid_parseHex_rejectsNonV4VersionOrVariant defaultApi) := by
  intro bs hlen badVer ⟨hverHex, hverNe⟩ badVar ⟨hvarHex, h8, h9, ha, hb, hA, hB⟩
  obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
  dsimp [test_uuid_parseHex_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
  have hp1 := (badVer_rejects hv hverHex hverNe).1; have hp2 := (badVar_rejects hv hvarHex h8 h9 ha hb hA hB).1
  rw [hfr]; dsimp only; rw [hp1]; dsimp only; rw [hp2]; dsimp only
  exact ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_parseHex_rejectsNonV4VersionOrVariant`. -/
theorem reach_uuid_parseHex_rejectsNonV4VersionOrVariant :
    CanReach (test_uuid_parseHex_rejectsNonV4VersionOrVariant defaultApi) :=
  (fun (bs : ByteArray) (hlen : bs.size = 16) => by
    obtain ⟨_, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hlen
    have hp1 := (badVer_rejects hv (by decide) (by decide : '5' ≠ '4')).1
    have hp2 := (badVar_rejects hv (badVar := '0') (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    dsimp [test_uuid_parseHex_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Bind.bind, Core.NondetTest.assert]
    refine ⟨bs, hlen, '5', by decide, '0', by decide, ?_⟩
    rw [hfr]; dsimp only; rw [hp1]; dsimp only; rw [hp2]; dsimp only
    exact ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, trivial⟩) zeros16 rfl

/-- Proof of `test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid` for `mkApiM`. -/
theorem proof_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid :
    AllPass (test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid Internal.mkApiM) := by
  intro s₀
  dsimp [test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  rw [mkApiM_modelOps_getUuid_run s₀]; dsimp only
  rw [mkApiM_modelOps_getUuid_run { s₀ with crngReady := true, entropyDraws := s₀.entropyDraws + 1 }]
  dsimp only [Internal.mkApiM, Internal.mkApi]
  obtain ⟨u1, hfr1, hv1, _, _, hoth1⟩ := fromRandomBytes_spec (deterministicEntropyBytes_size s₀.entropyDraws 16)
  obtain ⟨u2, hfr2, hv2, _, _, hoth2⟩ := fromRandomBytes_spec (deterministicEntropyBytes_size (s₀.entropyDraws + 1) 16)
  rw [hfr1, hfr2]; dsimp only
  have hne : u1 ≠ u2 := fun h => by
    have hb0 := congrArg (fun u : Uuid => u.bytes[0]!.toNat) h
    rw [hoth1 0 (by omega) (by decide) (by decide), hoth2 0 (by omega) (by decide) (by decide),
        deterministicEntropyBytes_16_get0, deterministicEntropyBytes_16_get0] at hb0
    simp only [UInt8.toNat_ofNat', Nat.mod_mod] at hb0; omega
  have hp1 := (toString_spec hv1).2.2.2.2.2.2.2.2.1; have hp2 := (toString_spec hv2).2.2.2.2.2.2.2.2.1
  have hh1 := (toHex_spec hv1).2.2.2.1; have hh2 := (toHex_spec hv2).2.2.2.1
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, hne,
    fun h => hne (Except.ok.inj (by have := congrArg Internal.parse h; rwa [hp1, hp2] at this)),
    fun h => hne (Except.ok.inj (by have := congrArg Internal.parseHex h; rwa [hh1, hh2] at this)),
    hv1, hv2, ⟨by rw [Internal.isValid, hp1]; rfl, by rw [Internal.isValid, hp2]; rfl⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid`. -/
theorem reach_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid :
    CanReach (test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid Internal.mkApiM) :=
  ⟨{}, proof_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid {}⟩

/-- Proof of `test_uuid_getUuid_usesExact16BytesFromGetrandom` for `mkApiM`. -/
theorem proof_uuid_getUuid_usesExact16BytesFromGetrandom :
    AllPass (test_uuid_getUuid_usesExact16BytesFromGetrandom Internal.mkApiM) := by
  intro bs hlen
  dsimp [test_uuid_getUuid_usesExact16BytesFromGetrandom, Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Core.NondetTest.assert]
  rw [gather_first_step]; dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.modifyGet, Internal.stepRandomBytes16]
  have hcond : (bs.size == 0 || decide (bs.size > 16)) = false := by rw [beq_false_of_ne (by omega), decide_eq_false (by omega)]; rfl
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, show Internal.appendBytes ByteArray.empty bs = bs from rfl, beq_iff_eq.mpr hlen]
  exact ⟨⟨rfl, rfl⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_getUuid_usesExact16BytesFromGetrandom`. -/
theorem reach_uuid_getUuid_usesExact16BytesFromGetrandom :
    CanReach (test_uuid_getUuid_usesExact16BytesFromGetrandom Internal.mkApiM) :=
  ⟨zeros16, rfl, proof_uuid_getUuid_usesExact16BytesFromGetrandom zeros16 rfl⟩

/-- Proof of `test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr` for `mkApiM`. -/
theorem proof_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr :
    AllPass (test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr Internal.mkApiM) := by
  intro b1 b2 eintrCount ⟨hb1, hb2, hsum⟩ heintr
  dsimp [test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr, Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  rw [gather_first_step]; dsimp only [Bind.bind, StateT.bind, List.cons_append]; rw [scripted_cons]
  have hcond : (b1.size == 0 || decide (b1.size > 16)) = false := by rw [beq_false_of_ne (by omega), decide_eq_false (by omega)]; rfl
  dsimp only [Internal.stepRandomBytes16]; rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, show Internal.appendBytes ByteArray.empty b1 = b1 from rfl, beq_false_of_ne (by omega : b1.size ≠ 16)]
  rw [gather_script_eintr_loop eintrCount 31 (by omega) b1 b2 hb1 hb2 hsum none]; exact ⟨⟨rfl, rfl⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr`. -/
theorem reach_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr :
    CanReach (test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr Internal.mkApiM) :=
  ⟨ByteArray.mk #[1, 2, 3, 4], ByteArray.mk #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], 1, by decide, by decide,
    proof_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr (ByteArray.mk #[1, 2, 3, 4]) (ByteArray.mk #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) 1 (by decide) (by decide)⟩

/-- Proof of `test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry` for `mkApiM`. -/
theorem proof_uuid_getUuid_mapsNonEintrErrnoWithoutRetry :
    AllPass (test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry Internal.mkApiM) := by
  intro e hne
  dsimp [test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry, Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  rw [gather_first_step]; dsimp only [Bind.bind, StateT.bind]; rw [counting_run]
  dsimp only [Internal.stepRandomBytes16]; rw [beq_false_of_ne hne]; simp only [Bool.false_eq_true, ↓reduceIte]
  dsimp only [Pure.pure, StateT.pure]; exact ⟨rfl, ⟨Internal.mapErrnoToUuidError e, rfl, rfl, rfl, mapRawError_msg_ne _⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry`. -/
theorem reach_uuid_getUuid_mapsNonEintrErrnoWithoutRetry :
    CanReach (test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry Internal.mkApiM) :=
  ⟨Errno.EIO, by decide, proof_uuid_getUuid_mapsNonEintrErrnoWithoutRetry Errno.EIO (by decide)⟩

/-- Proof of `test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed` for `mkApiM`. -/
theorem proof_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed :
    AllPass (test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed Internal.mkApiM) := by
  intro bigChunk hbig
  dsimp [test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed, Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  obtain ⟨heintr, hempty, errBig, hbigEq, hbigKind, hbigErrno, hbigMsg⟩ := gather_fixed_failures hbig
  rw [heintr, hempty, hbigEq]
  exact ⟨⟨rfl, _, rfl, rfl, rfl, mapRawError_msg_ne _⟩, ⟨rfl, _, rfl, rfl, rfl, mapRawError_msg_ne _⟩,
    ⟨rfl, errBig, rfl, hbigKind, hbigErrno, hbigMsg⟩, trivial⟩
/-- Non-vacuity witness for `test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed`. -/
theorem reach_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed :
    CanReach (test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed Internal.mkApiM) :=
  ⟨ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], by decide,
    proof_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) (by decide)⟩

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.entropyFailed`. -/
theorem uuid_fromRandomBytes_never_entropyFailed (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.fromRandomBytes bs) := fromRandomBytes_never .entropyFailed (by decide) bs
/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidFormat`. -/
theorem uuid_fromRandomBytes_never_invalidFormat (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidFormat (LeanSwe.Uuid.fromRandomBytes bs) := fromRandomBytes_never .invalidFormat (by decide) bs
/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidVersion`. -/
theorem uuid_fromRandomBytes_never_invalidVersion (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidVersion (LeanSwe.Uuid.fromRandomBytes bs) := fromRandomBytes_never .invalidVersion (by decide) bs

/-- Proof that `LeanSwe.Uuid.parse` never returns `.entropyFailed`. -/
theorem uuid_parse_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parse s) := parse_never .entropyFailed (by decide) (by decide) s
/-- Proof that `LeanSwe.Uuid.parse` never returns `.invalidLength`. -/
theorem uuid_parse_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parse s) := parse_never .invalidLength (by decide) (by decide) s

/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.entropyFailed`. -/
theorem uuid_parseHex_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parseHex s) := parseHexChars_never .entropyFailed (by decide) (by decide) s.toList
/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.invalidLength`. -/
theorem uuid_parseHex_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parseHex s) := parseHexChars_never .invalidLength (by decide) (by decide) s.toList

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidLength`. -/
theorem uuid_getUuid_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.getUuid w := getUuid_never .invalidLength (by decide) w
/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidFormat`. -/
theorem uuid_getUuid_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.getUuid w := getUuid_never .invalidFormat (by decide) w
/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidVersion`. -/
theorem uuid_getUuid_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.getUuid w := getUuid_never .invalidVersion (by decide) w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidLength`. -/
theorem uuid_v4_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.v4 w := uuid_getUuid_never_invalidLength w
/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidFormat`. -/
theorem uuid_v4_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.v4 w := uuid_getUuid_never_invalidFormat w
/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidVersion`. -/
theorem uuid_v4_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.v4 w := uuid_getUuid_never_invalidVersion w

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.Uuid` against `LeanSwe.Uuid.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Uuid.mapRawError Model.mapRawError ∧
    Core.ObeysPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes ∧
    Core.ObeysPureEq LeanSwe.Uuid.toString Model.toString ∧
    Core.ObeysPureEq LeanSwe.Uuid.toHex Model.toHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.parse Model.parse ∧
    Core.ObeysPureEq LeanSwe.Uuid.parseHex Model.parseHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.isValid Model.isValid ∧
    Core.ObeysStepFrom id Model.healthyWf Model.execRawStep Model.allowedRawStep
      Model.healthyWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep :=
  LeanSwe.Uuid.Proofs.RefinesModel.refines_model_impl

end LeanSwe.Uuid.Proofs

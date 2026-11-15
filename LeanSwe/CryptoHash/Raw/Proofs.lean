import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Impl
import LeanSwe.CryptoHash.Raw.Interface
import LeanSwe.CryptoHash.Raw.SpecTests

namespace LeanSwe.CryptoHash.Raw.Proofs

open Core (AllPass CanReach)
open LeanSwe.CryptoHash.Raw

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hfb
  · rename_i hne
    intro hemp
    apply hne
    simp [hemp]

/-- `defaultOps.mapRawError` satisfies `test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage`. -/
theorem raw_mapRawError_mapsKindsAndNonEmptyMessage :
    AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage defaultOps) := by
  intro raw
  cases raw with
  | invalidArgument detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | invalidHexInput detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid hex input" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | lengthError expected got detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail (by
        intro h
        have hlen := congrArg String.length h
        simp [String.length] at hlen)
    · exact ⟨rfl, rfl⟩
    · trivial
  | opensslError code detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | userError detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "cryptohash error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial

private def pureModelRawOps : RawCryptoHashOpsM (StateM Unit) :=
  { mapRawError := Internal.mapRawError
    digestRaw := fun alg _ => pure (.ok (ByteArray.mk (Array.replicate (digestLen alg) 0)))
    hmacSha256Raw := fun _ _ => pure (.ok (ByteArray.mk (Array.replicate 32 0)))
    ctEqualRaw := fun a b =>
      if a.size != b.size then
        pure (.error (Internal.mapRawError (.lengthError a.size b.size "length mismatch")))
      else
        pure (.ok (a == b)) }

/-- `pureModelRawOps` satisfies `test_cryptohashraw_digestRaw_returnsExpectedLengthOrError`. -/
theorem raw_digestRaw_returnsExpectedLengthOrError :
    AllPass (test_cryptohashraw_digestRaw_returnsExpectedLengthOrError pureModelRawOps) := by
  intro _ alg _
  dsimp [test_cryptohashraw_digestRaw_returnsExpectedLengthOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_hmacSha256Raw_returns32BytesOrError`. -/
theorem raw_hmacSha256Raw_returns32BytesOrError :
    AllPass (test_cryptohashraw_hmacSha256Raw_returns32BytesOrError pureModelRawOps) := by
  intro _ _ _
  dsimp [test_cryptohashraw_hmacSha256Raw_returns32BytesOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_returnsLengthMismatch :
    AllPass (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch pureModelRawOps) := by
  intro _ a b hne
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind, Core.NondetTest.assume]
  have hneB : (a.size != b.size) = true := bne_iff_ne.mpr hne
  simp [hneB, StateT.pure, pure, Internal.mapRawError, Internal.nonEmptyMsg]

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch pureModelRawOps) := by
  refine ⟨(), ByteArray.empty, ByteArray.mk #[1], by decide, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size, Internal.mapRawError, Internal.nonEmptyMsg, StateT.pure, pure]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_returnsBoolOrError :
    AllPass (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError pureModelRawOps) := by
  intro _ a b heq
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  have hfalse : (a.size != b.size) = false := by simp [heq]
  simp [hfalse, StateT.pure, pure]

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError pureModelRawOps) := by
  refine ⟨(), ByteArray.empty, ByteArray.empty, rfl, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp

end LeanSwe.CryptoHash.Raw.Proofs

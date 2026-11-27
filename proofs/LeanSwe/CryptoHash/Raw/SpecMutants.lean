import Core.NondetTest
import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.CryptoHash.Raw`. -/

namespace LeanSwe.CryptoHash.Raw

open Core (NondetTest)
open Core.NondetTest

private def stubRawOps : RawCryptoHashOps :=
  { mapRawError := fun
      | .invalidArgument _ => { kind := .invalidInput, message := "invalid argument" }
      | .invalidHexInput _ => { kind := .invalidHex, message := "invalid hex" }
      | .lengthError _ _ _ => { kind := .lengthMismatch, message := "length mismatch" }
      | .opensslError code _ => { kind := .cryptoError, opensslCode := code, message := "openssl error" }
      | .userError _ => { kind := .cryptoError, message := "cryptohash error" }
    digestRaw := fun alg _ => pure (.ok (ByteArray.mk (Array.replicate (digestLen alg) 0)))
    hmacSha256Raw := fun _ _ => pure (.ok (ByteArray.mk (Array.replicate 32 0)))
    ctEqualRaw := fun a b =>
      if a.size != b.size then
        pure (.error { kind := .lengthMismatch, message := "length mismatch" })
      else
        pure (.ok (a == b)) }

private def stubStateRawOps : RawCryptoHashOpsM (StateM Unit) :=
  { mapRawError := stubRawOps.mapRawError
    digestRaw := fun alg _ => pure (.ok (ByteArray.mk (Array.replicate (digestLen alg) 0)))
    hmacSha256Raw := fun _ _ => pure (.ok (ByteArray.mk (Array.replicate 32 0)))
    ctEqualRaw := fun a b =>
      if a.size != b.size then
        pure (.error { kind := .lengthMismatch, message := "length mismatch" })
      else
        pure (.ok (a == b)) }

private def buggyEmptyErrRaw (base : RawCryptoHashOps) : RawCryptoHashOps :=
  { base with mapRawError := fun _ => { kind := .cryptoError, message := "" } }

private def buggyWrongKindRaw (base : RawCryptoHashOps) : RawCryptoHashOps :=
  { base with mapRawError := fun _ => { kind := .cryptoError, message := "bad" } }

private def buggyDropCodeRaw (base : RawCryptoHashOps) : RawCryptoHashOps :=
  { base with mapRawError := fun _ => { kind := .cryptoError, opensslCode := none, message := "bad" } }

private def buggyWrongDigestLenRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with digestRaw := fun _ _ => pure (.ok (ByteArray.mk #[1, 2, 3])) }

private def buggyEmptyDigestErrRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with digestRaw := fun _ _ => pure (.error { kind := .cryptoError, message := "" }) }

private def buggyWrongHmacLenRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with hmacSha256Raw := fun _ _ => pure (.ok (ByteArray.mk #[1, 2, 3])) }

private def buggyEmptyHmacErrRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with hmacSha256Raw := fun _ _ => pure (.error { kind := .cryptoError, message := "" }) }

private def buggyCtEqAcceptsMismatchRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with ctEqualRaw := fun _ _ => pure (.ok false) }

private def buggyCtEqWrongErrKindRaw : RawCryptoHashOpsM (StateM Unit) :=
  { stubStateRawOps with ctEqualRaw := fun _ _ => pure (.error { kind := .invalidInput, message := "wrong kind" }) }

example : ¬ Core.AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, buggyEmptyErrRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage (buggyWrongKindRaw stubRawOps)) := by
  intro h
  have h0 := h (.invalidArgument "bad")
  dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, buggyWrongKindRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage (buggyDropCodeRaw stubRawOps)) := by
  intro h
  have h0 := h (.opensslError (some 42) "ossl")
  dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, buggyDropCodeRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_cryptohashraw_digestRaw_returnsExpectedLengthOrError buggyWrongDigestLenRaw) := by
  intro h
  have h0 := h () .sha256 ByteArray.empty
  simp [buggyWrongDigestLenRaw, StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_cryptohashraw_digestRaw_returnsExpectedLengthOrError buggyEmptyDigestErrRaw) := by
  intro h
  have h0 := h () .sha256 ByteArray.empty
  simp [buggyEmptyDigestErrRaw, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_cryptohashraw_hmacSha256Raw_returns32BytesOrError buggyWrongHmacLenRaw) := by
  intro h
  have h0 := h () ByteArray.empty ByteArray.empty
  simp [buggyWrongHmacLenRaw, StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_cryptohashraw_hmacSha256Raw_returns32BytesOrError buggyEmptyHmacErrRaw) := by
  intro h
  have h0 := h () ByteArray.empty ByteArray.empty
  simp [buggyEmptyHmacErrRaw, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch buggyCtEqAcceptsMismatchRaw) := by
  intro h
  have h0 := h () ByteArray.empty (ByteArray.mk #[1]) (by decide)
  simp [buggyCtEqAcceptsMismatchRaw, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch buggyCtEqWrongErrKindRaw) := by
  intro h
  have h0 := h () ByteArray.empty (ByteArray.mk #[1]) (by decide)
  simp [buggyCtEqWrongErrKindRaw, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError
    { stubStateRawOps with ctEqualRaw := fun _ _ => pure (.error { kind := .cryptoError, message := "" }) }) := by
  intro h
  have h0 := h () ByteArray.empty ByteArray.empty rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_cryptohashraw_modelDigestsValidLengthsAndVectors
    { Model.modelRawOps with digestRaw := fun _ _ => .ok ByteArray.empty }) := by
  intro h
  have h0 := h .sha256 ByteArray.empty ByteArray.empty
  dsimp [test_cryptohashraw_modelDigestsValidLengthsAndVectors, Core.NondetTest.assert, Bind.bind] at h0
  have hsz := congrArg (fun r : Except CryptoHashError ByteArray =>
    match r with | .ok bs => bs.size | .error _ => 0) h0.1
  change 0 = 32 at hsz
  omega

end LeanSwe.CryptoHash.Raw

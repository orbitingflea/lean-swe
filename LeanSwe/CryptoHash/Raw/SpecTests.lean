import Core.NondetTest
import LeanSwe.CryptoHash.Raw.Types

namespace LeanSwe.CryptoHash.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every `CryptoHashRawError` maps to its expected `CryptoHashErrorKind`, preserves `opensslCode` on `.opensslError`, and carries a non-empty message. -/
def test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawCryptoHashOps) : runner Unit := do
  let raw ← nondet CryptoHashRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")
  match raw with
  | .invalidArgument _ => NondetTest.assert (err.kind = .invalidInput ∧ err.opensslCode = none)
  | .invalidHexInput _ => NondetTest.assert (err.kind = .invalidHex ∧ err.opensslCode = none)
  | .lengthError _ _ _ => NondetTest.assert (err.kind = .lengthMismatch ∧ err.opensslCode = none)
  | .opensslError code _ => NondetTest.assert (err.kind = .cryptoError ∧ err.opensslCode = code)
  | .userError _ => NondetTest.assert (err.kind = .cryptoError ∧ err.opensslCode = none)

/-- Successful `ops.digestRaw` calls return exactly `digestLen alg` bytes, and failures carry a non-empty message. -/
def test_cryptohashraw_digestRaw_returnsExpectedLengthOrError
    {S : Type} {runner} [NondetTest runner] (ops : RawCryptoHashOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let alg ← nondet HashAlg
  let msg ← nondet ByteArray
  match (ops.digestRaw alg msg).run s₀ with
  | (.ok bs, _) => NondetTest.assert (bs.size = digestLen alg)
  | (.error e, _) => NondetTest.assert (e.message ≠ "")

/-- Successful `ops.hmacSha256Raw` calls return exactly 32 bytes, and failures carry a non-empty message. -/
def test_cryptohashraw_hmacSha256Raw_returns32BytesOrError
    {S : Type} {runner} [NondetTest runner] (ops : RawCryptoHashOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  match (ops.hmacSha256Raw key msg).run s₀ with
  | (.ok bs, _) => NondetTest.assert (bs.size = 32)
  | (.error e, _) => NondetTest.assert (e.message ≠ "")

/-- `ops.ctEqualRaw` rejects unequal-length inputs with `.lengthMismatch` and a non-empty message. -/
def test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch
    {S : Type} {runner} [NondetTest runner] (ops : RawCryptoHashOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  assume (a.size ≠ b.size)
  match (ops.ctEqualRaw a b).run s₀ with
  | (.ok _, _) => NondetTest.assert False
  | (.error e, _) => NondetTest.assert (e.kind = .lengthMismatch ∧ e.message ≠ "")

/-- `ops.ctEqualRaw` on equal-length inputs returns a boolean result or a non-empty error. -/
def test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError
    {S : Type} {runner} [NondetTest runner] (ops : RawCryptoHashOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  assume (a.size = b.size)
  match (ops.ctEqualRaw a b).run s₀ with
  | (.ok _, _) => NondetTest.assert True
  | (.error e, _) => NondetTest.assert (e.message ≠ "")

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

end LeanSwe.CryptoHash.Raw

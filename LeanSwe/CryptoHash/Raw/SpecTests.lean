import Core.NondetTest
import Core.Assumptions
import LeanSwe.CryptoHash.Raw.Types

namespace LeanSwe.CryptoHash.Raw

open Core (NondetTest AssumptionObligation ErrorObligation)
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

/-- Checkable external-boundary assumptions for `LeanSwe.CryptoHash.Raw` over OpenSSL 3 `libcrypto` (`c/cryptohash_shim.c`). -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestRaw_sha256MatchesFips180Vectors"
      subject := "LeanSwe.CryptoHash.Raw.digestRaw"
      formalPred? := none }
  , { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestRaw_sha512MatchesFips180Vectors"
      subject := "LeanSwe.CryptoHash.Raw.digestRaw"
      formalPred? := none }
  , { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_hmacSha256Raw_matchesRfc4231AndEmptyKey"
      subject := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      formalPred? := none }
  , { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestAndHmac_preserveEmbeddedNulBytes"
      subject := "LeanSwe.CryptoHash.Raw.digestRaw"
      formalPred? := none }
  , { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_ctEqualRaw_matchesByteEquality"
      subject := "LeanSwe.CryptoHash.Raw.ctEqualRaw"
      formalPred? := none }
  , { name := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_differentialMatchesPythonHashlibAndHmac"
      subject := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      formalPred? := none } ]

/-- Declared error-coverage matrix for `LeanSwe.CryptoHash.Raw` fallible requests (`CryptoHashErrorKind`). -/
def errorCoverage : List (ErrorObligation CryptoHashErrorKind) :=
  [ { request := "LeanSwe.CryptoHash.Raw.digestRaw"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_digestRaw_never_invalidInput" }
  , { request := "LeanSwe.CryptoHash.Raw.digestRaw"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_digestRaw_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.Raw.digestRaw"
      errorKind := .lengthMismatch
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_digestRaw_never_lengthMismatch" }
  , { request := "LeanSwe.CryptoHash.Raw.digestRaw"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_digestRaw_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_hmacSha256Raw_never_invalidInput" }
  , { request := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_hmacSha256Raw_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      errorKind := .lengthMismatch
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_hmacSha256Raw_never_lengthMismatch" }
  , { request := "LeanSwe.CryptoHash.Raw.hmacSha256Raw"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_hmacSha256Raw_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.Raw.ctEqualRaw"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_ctEqualRaw_never_invalidInput" }
  , { request := "LeanSwe.CryptoHash.Raw.ctEqualRaw"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_ctEqualRaw_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.Raw.ctEqualRaw"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_ctEqualRaw_lengthMismatch" .real }
  , { request := "LeanSwe.CryptoHash.Raw.ctEqualRaw"
      errorKind := .cryptoError
      justification := .provedImpossible "LeanSwe.CryptoHash.Raw.Proofs.raw_ctEqualRaw_never_cryptoError" } ]

end LeanSwe.CryptoHash.Raw

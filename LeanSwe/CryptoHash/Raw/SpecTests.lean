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

end LeanSwe.CryptoHash.Raw

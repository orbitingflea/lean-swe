import Core.NondetTest
import LeanSwe.CryptoHash.Raw.Types
import LeanSweProofs.CryptoHash.Raw.Model

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

/-- Pure `ops` (`Model.modelRawOps`) produces `digestLen alg`-byte digests, 32-byte HMAC tags, and matches NIST FIPS 180-4 / RFC 4231 vectors. -/
def test_cryptohashraw_modelDigestsValidLengthsAndVectors
    {runner} [NondetTest runner] (ops : RawCryptoHashOpsM Id) : runner Unit := do
  let alg ← nondet HashAlg
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  NondetTest.assert (ops.digestRaw alg msg = .ok (Model.digestBytesModel alg msg))
  NondetTest.assert ((Model.digestBytesModel alg msg).size = digestLen alg)
  NondetTest.assert (ops.hmacSha256Raw key msg = .ok (Model.hmacSha256Bytes key msg))
  NondetTest.assert ((Model.hmacSha256Bytes key msg).size = 32)
  NondetTest.assert (Model.sha256Bytes ByteArray.empty = ByteArray.mk #[
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
    0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
    0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55])
  NondetTest.assert (Model.sha256Bytes "abc".toUTF8 = ByteArray.mk #[
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
    0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
    0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad])
  NondetTest.assert (Model.sha512Bytes ByteArray.empty = ByteArray.mk #[
    0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd,
    0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07,
    0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc,
    0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce,
    0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0,
    0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f,
    0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81,
    0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e])
  NondetTest.assert (Model.sha512Bytes "abc".toUTF8 = ByteArray.mk #[
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
    0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
    0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
    0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
    0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
    0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
    0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
    0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f])
  NondetTest.assert (Model.hmacSha256Bytes (ByteArray.mk (Array.replicate 20 0x0b)) "Hi There".toUTF8 = ByteArray.mk #[
    0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
    0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
    0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
    0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7])
  NondetTest.assert (Model.hmacSha256Bytes "Jefe".toUTF8 "what do ya want for nothing?".toUTF8 = ByteArray.mk #[
    0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e,
    0x6a, 0x04, 0x24, 0x26, 0x08, 0x95, 0x75, 0xc7,
    0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83,
    0x9d, 0xec, 0x58, 0xb9, 0x64, 0xec, 0x38, 0x43])
  NondetTest.assert (Model.hmacSha256Bytes (ByteArray.mk (Array.replicate 131 0xaa)) "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8 = ByteArray.mk #[
    0x60, 0xe4, 0x31, 0x59, 0x1e, 0xe0, 0xb6, 0x7f,
    0x0d, 0x8a, 0x26, 0xaa, 0xcb, 0xf5, 0xb7, 0x7f,
    0x8e, 0x0b, 0xc6, 0x21, 0x37, 0x28, 0xc5, 0x14,
    0x05, 0x46, 0x04, 0x0f, 0x0e, 0xe3, 0x7f, 0x54])
  NondetTest.assert (Model.hmacSha256Bytes ByteArray.empty ByteArray.empty = ByteArray.mk #[
    0xb6, 0x13, 0x67, 0x9a, 0x08, 0x14, 0xd9, 0xec,
    0x77, 0x2f, 0x95, 0xd7, 0x78, 0xc3, 0x5f, 0xc5,
    0xff, 0x16, 0x97, 0xc4, 0x93, 0x71, 0x56, 0x53,
    0xc6, 0xc7, 0x12, 0x14, 0x42, 0x92, 0xc5, 0xad])

end LeanSwe.CryptoHash.Raw

import LeanSwe.CryptoHash.Types
import LeanSwe.CryptoHash.Impl
import LeanSwe.CryptoHash.Raw.Interface

namespace LeanSwe.CryptoHash

/-- Default `IO` cryptographic hash and HMAC API backed by OpenSSL 3 `libcrypto`. -/
def defaultApi : CryptoHashApi :=
  Internal.mkApiM Raw.defaultOps

/-- Convert a raw error record into a normalized `CryptoHashError` with a non-empty message. -/
@[inline] def mapRawError (err : CryptoHashRawError) : CryptoHashError :=
  defaultApi.mapRawError err

/-- Compute a digest for `HashAlg` over arbitrary input bytes. -/
@[inline] def hash (alg : HashAlg) (msg : ByteArray) : IO (Except CryptoHashError Digest) :=
  defaultApi.hash alg msg

/-- Compute a SHA-256 digest over arbitrary input bytes. -/
@[inline] def sha256 (msg : ByteArray) : IO (Except CryptoHashError Digest) :=
  defaultApi.sha256 msg

/-- Compute a SHA-512 digest over arbitrary input bytes. -/
@[inline] def sha512 (msg : ByteArray) : IO (Except CryptoHashError Digest) :=
  defaultApi.sha512 msg

/-- Compute an RFC 2104 HMAC-SHA256 digest over arbitrary `key` and `msg`. -/
@[inline] def hmacSha256 (key msg : ByteArray) : IO (Except CryptoHashError Digest) :=
  defaultApi.hmacSha256 key msg

/-- Verify an expected HMAC-SHA256 `Digest` in constant time. -/
@[inline] def verifyHmacSha256 (key msg : ByteArray) (expected : Digest) :
    IO (Except CryptoHashError Bool) :=
  defaultApi.verifyHmacSha256 key msg expected

/-- Encode `Digest` bytes as lowercase ASCII hexadecimal characters. -/
@[inline] def toHex (d : Digest) : String :=
  defaultApi.toHex d

/-- Decode case-insensitive ASCII hexadecimal characters into a length-checked `Digest`. -/
@[inline] def fromHex (alg : HashAlg) (s : String) : Except CryptoHashError Digest :=
  defaultApi.fromHex alg s

/-- Compare two byte slices in constant time, returning `false` on unequal lengths. -/
@[inline] def ctEq (a b : ByteArray) : IO (Except CryptoHashError Bool) :=
  defaultApi.ctEq a b

end LeanSwe.CryptoHash

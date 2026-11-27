import LeanSwe.CryptoHash.Types
import LeanSwe.CryptoHash.Impl

namespace LeanSwe.CryptoHash

@[extern "leanswe_cryptohash_digest"]
private opaque rawDigest : UInt8 → @& ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray)

@[extern "leanswe_cryptohash_hmac_sha256"]
private opaque rawHmacSha256 : @& ByteArray → @& ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray)

@[extern "leanswe_cryptohash_ct_equal"]
private opaque rawCtEqual : @& ByteArray → @& ByteArray → BaseIO Bool

/-- Default `IO` cryptographic hash and HMAC API backed by OpenSSL 3 `libcrypto` via `c/cryptohash_shim.c`. -/
def defaultApi : CryptoHashApi :=
  Internal.mkApiFromFfiM
    { digestRaw := fun tag data => liftM (rawDigest tag data)
      hmacSha256Raw := fun key msg => liftM (rawHmacSha256 key msg)
      ctEqualRaw := fun a b => liftM (rawCtEqual a b) }

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

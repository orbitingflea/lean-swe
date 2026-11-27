namespace LeanSwe.CryptoHash

/-- Supported cryptographic hash algorithms in `LeanSwe.CryptoHash`. -/
inductive HashAlg where
  /-- SHA-256 (32-byte digest). -/
  | sha256
  /-- SHA-512 (64-byte digest). -/
  | sha512
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Expected digest byte length for a `HashAlg`. -/
def digestLen : HashAlg → Nat
  | .sha256 => 32
  | .sha512 => 64

/-- Classification of failures in `LeanSwe.CryptoHash`. -/
inductive CryptoHashErrorKind where
  /-- Caller passed an invalid argument or mismatched algorithm tag. -/
  | invalidInput
  /-- Hex string contained non-hex characters or had odd character length. -/
  | invalidHex
  /-- Digest, byte slice, or hex length did not match the expected size. -/
  | lengthMismatch
  /-- Underlying OpenSSL `libcrypto` or backend cryptographic failure. -/
  | cryptoError
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.CryptoHash` operations. -/
structure CryptoHashError where
  /-- Machine-checkable error category. -/
  kind : CryptoHashErrorKind
  /-- First OpenSSL `ERR_get_error()` code captured on failure, when non-zero. -/
  opensslCode : Option UInt64 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw C-shim error inputs for total error-mapping specs. -/
inductive CryptoHashRawError where
  /-- Caller passed an invalid argument or unrecognized algorithm tag. -/
  | invalidArgument (detail : String)
  /-- Invalid hexadecimal input representation. -/
  | invalidHexInput (detail : String)
  /-- Byte count did not match expected digest or slice length. -/
  | lengthError (expected got : Nat) (detail : String)
  /-- OpenSSL `libcrypto` failure with optional non-zero `ERR_get_error()` code. -/
  | opensslError (code : Option UInt64) (detail : String)
  /-- Generic runtime error message. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Minimal OpenSSL `libcrypto` cryptographic primitives parameterized over effect monad `m`. -/
structure RawCryptoHashOpsM (m : Type → Type) where
  /-- Convert a raw error record into a normalized `CryptoHashError` with a non-empty message. -/
  mapRawError : CryptoHashRawError → CryptoHashError
  /-- Compute the raw digest bytes for `HashAlg` over arbitrary input bytes. -/
  digestRaw : HashAlg → ByteArray → m (Except CryptoHashError ByteArray)
  /-- Compute the raw 32-byte RFC 2104 HMAC-SHA256 tag over arbitrary `key` and `msg`. -/
  hmacSha256Raw : ByteArray → ByteArray → m (Except CryptoHashError ByteArray)
  /-- Constant-time byte-slice comparison over equal-length `ByteArray` values. -/
  ctEqualRaw : ByteArray → ByteArray → m (Except CryptoHashError Bool)

/-- Concrete `IO` primitive bundle for `LeanSwe.CryptoHash`. -/
abbrev RawCryptoHashOps := RawCryptoHashOpsM IO

/-- OpenSSL `libcrypto` C-ABI operations parameterized over effect monad `m`. -/
structure CryptoHashFfiOpsM (m : Type → Type) where
  /-- Compute raw digest bytes for algorithm tag (`0 = SHA256`, `1 = SHA512`). -/
  digestRaw : UInt8 → ByteArray → m (UInt32 × UInt64 × String × ByteArray)
  /-- Compute raw 32-byte HMAC-SHA256 tag over `key` and `msg`. -/
  hmacSha256Raw : ByteArray → ByteArray → m (UInt32 × UInt64 × String × ByteArray)
  /-- Constant-time byte-slice comparison via OpenSSL `CRYPTO_memcmp`. -/
  ctEqualRaw : ByteArray → ByteArray → m Bool

/-- Cryptographic digest tagged by its `HashAlg`. -/
structure Digest where
  /-- Hash algorithm that produced or owns this digest. -/
  alg : HashAlg
  /-- Raw digest bytes (expected length `digestLen alg`). -/
  bytes : ByteArray
  deriving BEq, DecidableEq, Inhabited

instance : Repr Digest where
  reprPrec d prec :=
    Repr.addAppParen ("Digest.mk " ++ repr d.alg ++ " " ++ repr d.bytes.data) prec

/-- Proposition asserting `d.bytes` has the exact length required by `d.alg`. -/
def ValidDigest (d : Digest) : Prop :=
  d.bytes.size = digestLen d.alg

/-- Boolean check that `d.bytes` has the exact length required by `d.alg`. -/
def Digest.isValid (d : Digest) : Bool :=
  d.bytes.size == digestLen d.alg

/-- Public cryptographic hash and HMAC API exported by `LeanSwe.CryptoHash`, parameterized over `m`. -/
structure CryptoHashApiM (m : Type → Type) where
  /-- Convert a raw error record into a normalized `CryptoHashError` with a non-empty message. -/
  mapRawError : CryptoHashRawError → CryptoHashError
  /-- Compute a digest for `HashAlg` over arbitrary input bytes. -/
  hash : HashAlg → ByteArray → m (Except CryptoHashError Digest)
  /-- Compute a SHA-256 digest over arbitrary input bytes. -/
  sha256 : ByteArray → m (Except CryptoHashError Digest)
  /-- Compute a SHA-512 digest over arbitrary input bytes. -/
  sha512 : ByteArray → m (Except CryptoHashError Digest)
  /-- Compute an RFC 2104 HMAC-SHA256 digest over arbitrary `key` and `msg`. -/
  hmacSha256 : ByteArray → ByteArray → m (Except CryptoHashError Digest)
  /-- Verify an expected HMAC-SHA256 `Digest` in constant time. -/
  verifyHmacSha256 : ByteArray → ByteArray → Digest → m (Except CryptoHashError Bool)
  /-- Encode `Digest` bytes as lowercase ASCII hexadecimal characters. -/
  toHex : Digest → String
  /-- Decode case-insensitive ASCII hexadecimal characters into a length-checked `Digest`. -/
  fromHex : HashAlg → String → Except CryptoHashError Digest
  /-- Compare two byte slices in constant time, returning `false` on unequal lengths. -/
  ctEq : ByteArray → ByteArray → m (Except CryptoHashError Bool)

/-- Concrete `IO` cryptographic hash API bundle exported by `LeanSwe.CryptoHash`. -/
abbrev CryptoHashApi := CryptoHashApiM IO

end LeanSwe.CryptoHash

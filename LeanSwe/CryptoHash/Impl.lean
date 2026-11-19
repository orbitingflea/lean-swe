import LeanSwe.CryptoHash.Types

namespace LeanSwe.CryptoHash.Internal

open LeanSwe.CryptoHash
  (HashAlg digestLen CryptoHashErrorKind CryptoHashError CryptoHashRawError
   RawCryptoHashOpsM Digest CryptoHashApiM)

/-- Convert a nibble `0..15` to its lowercase ASCII hexadecimal character. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Parse an ASCII hexadecimal character (`0-9`, `a-f`, `A-F`) into a nibble `0..15`. -/
def hexCharToNibble (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else none

/-- Encode a single byte into big-endian high and low lowercase hexadecimal characters. -/
def byteToHexChars (b : UInt8) : List Char :=
  [lowerHexDigit (b.toNat / 16), lowerHexDigit (b.toNat % 16)]

/-- Decode two ASCII hexadecimal characters (high nibble, low nibble) into a byte. -/
def hexCharsToByte (hi lo : Char) : Option UInt8 :=
  match hexCharToNibble hi, hexCharToNibble lo with
  | some h, some l => some (UInt8.ofNat (h.toNat * 16 + l.toNat))
  | _, _ => none

/-- Format a list of bytes as compact lowercase hexadecimal characters. -/
def formatHexList (bs : List UInt8) : List Char :=
  bs.flatMap byteToHexChars

/-- Encode `Digest` bytes as lowercase ASCII hexadecimal characters. -/
def toHex (d : Digest) : String :=
  String.ofList (formatHexList d.bytes.data.toList)

/-- Tail-recursive accumulator decoding an even-length list of ASCII hexadecimal characters into bytes. -/
def decodeHexPairsAcc (accRev : List UInt8) : List Char → Option (List UInt8)
  | [] => some accRev.reverse
  | hi :: lo :: rest =>
    match hexCharsToByte hi lo with
    | some b => decodeHexPairsAcc (b :: accRev) rest
    | none => none
  | _ => none

/-- Decode a hexadecimal `Digest` string for `alg`, validating format and byte length. -/
def fromHex (alg : HashAlg) (s : String) : Except CryptoHashError Digest :=
  match decodeHexPairsAcc [] s.toList with
  | none =>
    .error { kind := .invalidHex, message := "hex string must have even length and contain only ASCII hex digits" }
  | some bs =>
    let ba := ByteArray.mk bs.toArray
    if ba.size != digestLen alg then
      .error { kind := .lengthMismatch, message := s!"expected {digestLen alg} digest bytes, got {ba.size}" }
    else
      .ok { alg, bytes := ba }

/-- Compute a length-validated `Digest` for `alg` via `raw.digestRaw`. -/
def hashM {m : Type → Type} [Monad m] (raw : RawCryptoHashOpsM m)
    (alg : HashAlg) (msg : ByteArray) : m (Except CryptoHashError Digest) := do
  match ← raw.digestRaw alg msg with
  | .error e => return .error e
  | .ok bs =>
    if bs.size != digestLen alg then
      return .error { kind := .lengthMismatch, message := s!"digest length mismatch: expected {digestLen alg} bytes, got {bs.size}" }
    else
      return .ok { alg, bytes := bs }

/-- Compute an RFC 2104 HMAC-SHA256 `Digest` via `raw.hmacSha256Raw`. -/
def hmacSha256M {m : Type → Type} [Monad m] (raw : RawCryptoHashOpsM m)
    (key msg : ByteArray) : m (Except CryptoHashError Digest) := do
  match ← raw.hmacSha256Raw key msg with
  | .error e => return .error e
  | .ok bs =>
    if bs.size != 32 then
      return .error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {bs.size}" }
    else
      return .ok { alg := .sha256, bytes := bs }

/-- Compare two byte slices in constant time, returning `false` on unequal lengths without invoking `raw.ctEqualRaw`. -/
def ctEqM {m : Type → Type} [Monad m] (raw : RawCryptoHashOpsM m)
    (a b : ByteArray) : m (Except CryptoHashError Bool) :=
  if a.size != b.size then
    pure (.ok false)
  else
    raw.ctEqualRaw a b

/-- Verify an expected HMAC-SHA256 `Digest` in constant time. -/
def verifyHmacSha256M {m : Type → Type} [Monad m] (raw : RawCryptoHashOpsM m)
    (key msg : ByteArray) (expected : Digest) : m (Except CryptoHashError Bool) := do
  if expected.alg != .sha256 then
    return .error { kind := .invalidInput, message := "expected HMAC-SHA256 digest algorithm" }
  if expected.bytes.size != 32 then
    return .error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {expected.bytes.size}" }
  match ← hmacSha256M raw key msg with
  | .error e => return .error e
  | .ok tag => ctEqM raw tag.bytes expected.bytes

/-- Build the generic `CryptoHashApiM m` bundle over an injected `RawCryptoHashOpsM m`. -/
def mkApiM {m : Type → Type} [Monad m] (rawOps : RawCryptoHashOpsM m) : CryptoHashApiM m :=
  { mapRawError := rawOps.mapRawError
    hash := hashM rawOps
    sha256 := hashM rawOps .sha256
    sha512 := hashM rawOps .sha512
    hmacSha256 := hmacSha256M rawOps
    verifyHmacSha256 := verifyHmacSha256M rawOps
    toHex := toHex
    fromHex := fromHex
    ctEq := ctEqM rawOps }

end LeanSwe.CryptoHash.Internal

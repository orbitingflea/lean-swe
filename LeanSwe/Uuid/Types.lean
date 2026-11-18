namespace LeanSwe.Uuid

/-- Maximum `getrandom(2)` attempts (covering up to 16 single-byte partial reads plus 16 `EINTR` retries) when gathering 16 UUIDv4 entropy bytes. -/
def MAX_GETRANDOM_ATTEMPTS : Nat := 32

/-- Classification of failures in `LeanSwe.Uuid`. -/
inductive UuidErrorKind where
  /-- OS entropy source (`TimeRand.getrandom`) failed, exhausted retries, or returned an invalid chunk length. -/
  | entropyFailed
  /-- Input byte array passed to `fromRandomBytes` did not have length 16. -/
  | invalidLength
  /-- Input string had invalid length, characters, or hyphen layout. -/
  | invalidFormat
  /-- Parsed UUID did not have RFC 4122 version 4 and variant `10xx` bits. -/
  | invalidVersion
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.Uuid` operations. -/
structure UuidError where
  /-- Machine-checkable error category. -/
  kind : UuidErrorKind
  /-- Underlying OS `errno` code from `getrandom`, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure representation of raw OS entropy error inputs for total error-mapping specs. -/
inductive UuidRawError where
  /-- OS entropy read failed with `errno` and detail message. -/
  | osError (errno : UInt32) (detail : String)
  /-- Entropy source returned an unexpected byte count or exhausted bounded retries before reaching 16 bytes. -/
  | shortRead (gotBytes : Nat) (detail : String)
  /-- Generic runtime error message. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Wrapper around a 16-byte RFC 4122 UUID value. -/
structure Uuid where
  /-- Raw 16-byte big-endian UUID bytes. -/
  bytes : ByteArray
  deriving BEq, DecidableEq, Inhabited

instance : Repr Uuid where
  reprPrec u prec := Repr.addAppParen ("Uuid.mk " ++ repr u.bytes.data) prec

/-- Public UUIDv4 operations exported by `LeanSwe.Uuid`, parameterized over effect monad `m`. -/
structure UuidApiM (m : Type → Type) where
  /-- Convert a raw OS entropy error record into a normalized `UuidError` with non-empty message. -/
  mapRawError : UuidRawError → UuidError
  /-- Construct a v4 `Uuid` from 16 raw random bytes, setting RFC 4122 version (`0x40`) and variant (`0x80`) bits. -/
  fromRandomBytes : ByteArray → Except UuidError Uuid
  /-- Format `Uuid` as canonical lowercase `8-4-4-4-12` (36 characters). -/
  toString : Uuid → String
  /-- Format `Uuid` as compact lowercase 32-character hex. -/
  toHex : Uuid → String
  /-- Parse a strict canonical `8-4-4-4-12` UUIDv4 string (case-insensitive hex, RFC 4122 v4 version and variant bits). -/
  parse : String → Except UuidError Uuid
  /-- Parse a compact 32-character hex UUIDv4 string (case-insensitive hex, RFC 4122 v4 version and variant bits). -/
  parseHex : String → Except UuidError Uuid
  /-- Return `true` iff `s` is a valid strict canonical `8-4-4-4-12` UUIDv4 string. -/
  isValid : String → Bool
  /-- Generate a fresh UUIDv4 via the underlying entropy source. -/
  getUuid : m (Except UuidError Uuid)

/-- Concrete `IO` UUIDv4 API bundle exported by `LeanSwe.Uuid`. -/
abbrev UuidApi := UuidApiM IO

end LeanSwe.Uuid

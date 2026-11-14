import LeanSwe.Uuid.Raw.Types

namespace LeanSwe.Uuid

export LeanSwe.Uuid.Raw
  (UuidErrorKind UuidError UuidRawError RawUuidOpsM RawUuidOps)

/-- Wrapper around a 16-byte RFC 4122 UUID value. -/
structure Uuid where
  /-- Raw 16-byte big-endian UUID bytes. -/
  bytes : ByteArray
  deriving BEq, DecidableEq, Inhabited

instance : Repr Uuid where
  reprPrec u prec := Repr.addAppParen ("Uuid.mk " ++ repr u.bytes.data) prec

/-- Deterministic mock entropy state for testing and proofs over `RawUuidOpsM (StateM MockRngState)`. -/
structure MockRngState where
  /-- Monotonic counter mixed into generated 16-byte blocks so consecutive draws differ. -/
  counter : Nat := 0
  /-- Optional injected failure returned instead of generating entropy bytes. -/
  failWith : Option UuidError := none
  /-- Number of `randomBytes16` calls observed on this state. -/
  draws : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

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

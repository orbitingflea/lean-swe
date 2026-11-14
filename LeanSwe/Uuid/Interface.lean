import LeanSwe.Uuid.Raw.Interface
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.Impl

namespace LeanSwe.Uuid

/-- Default concrete `IO` UUIDv4 API bundle backed by `LeanSwe.Uuid.Raw.defaultOps`. -/
def defaultApi : UuidApi :=
  Internal.mkApiM Raw.defaultOps

/-- Convert a raw OS entropy error record into a normalized `UuidError` with non-empty message. -/
@[inline] def mapRawError (err : UuidRawError) : UuidError :=
  defaultApi.mapRawError err

/-- Construct a v4 `Uuid` from 16 raw random bytes, setting RFC 4122 version (`0x40`) and variant (`0x80`) bits. -/
@[inline] def fromRandomBytes (bs : ByteArray) : Except UuidError Uuid :=
  defaultApi.fromRandomBytes bs

/-- Format `Uuid` as canonical lowercase `8-4-4-4-12` (36 characters). -/
@[inline] def toString (u : Uuid) : String :=
  defaultApi.toString u

/-- Format `Uuid` as compact lowercase 32-character hex. -/
@[inline] def toHex (u : Uuid) : String :=
  defaultApi.toHex u

/-- Parse a strict canonical `8-4-4-4-12` UUIDv4 string. -/
@[inline] def parse (s : String) : Except UuidError Uuid :=
  defaultApi.parse s

/-- Parse a compact 32-character hex UUIDv4 string. -/
@[inline] def parseHex (s : String) : Except UuidError Uuid :=
  defaultApi.parseHex s

/-- Return `true` iff `s` is a valid strict canonical `8-4-4-4-12` UUIDv4 string. -/
@[inline] def isValid (s : String) : Bool :=
  defaultApi.isValid s

/-- Generate a fresh UUIDv4 using OS entropy. -/
@[inline] def getUuid : IO (Except UuidError Uuid) :=
  defaultApi.getUuid

end LeanSwe.Uuid

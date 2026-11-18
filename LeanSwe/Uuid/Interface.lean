import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.Impl

namespace LeanSwe.Uuid

/-- Construct a `UuidApiM m` purely over an injected `LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m` capability bundle. -/
@[inline] def mkApi {m : Type → Type} [Monad m]
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m) : UuidApiM m :=
  Internal.mkApi sys

/-- Default concrete `IO` UUIDv4 API bundle backed by `LeanSwe.LinuxSyscall.TimeRand.defaultOps`. -/
def defaultApi : UuidApi :=
  Internal.mkApi LeanSwe.LinuxSyscall.TimeRand.defaultOps

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

/-- Generate a fresh UUIDv4 using Linux `getrandom(2)` via `LeanSwe.LinuxSyscall.TimeRand`. -/
@[inline] def getUuid : IO (Except UuidError Uuid) :=
  defaultApi.getUuid

/-- Alias of `getUuid` generating a fresh RFC 4122 v4 `Uuid` via `LeanSwe.LinuxSyscall.TimeRand`. -/
@[inline] def v4 : IO (Except UuidError Uuid) :=
  defaultApi.getUuid

end LeanSwe.Uuid

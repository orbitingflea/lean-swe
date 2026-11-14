import LeanSwe.Uuid.Raw.Types
import LeanSwe.Uuid.Raw.Impl

namespace LeanSwe.Uuid.Raw

@[extern "leanswe_uuid_random_bytes16"]
private opaque rawRandomBytes16 : IO ByteArray

/-- Default OS entropy primitive bundle backed by `c/uuid_shim.c`. -/
def defaultOps : RawUuidOps :=
  Internal.mkRawOps { randomBytes16 := rawRandomBytes16 }

/-- Convert a raw OS entropy error record into a normalized `UuidError` with non-empty message. -/
@[inline] def mapRawError (err : UuidRawError) : UuidError :=
  defaultOps.mapRawError err

/-- Read 16 cryptographically random bytes from OS entropy. -/
@[inline] def randomBytes16 : IO (Except UuidError ByteArray) :=
  defaultOps.randomBytes16

end LeanSwe.Uuid.Raw

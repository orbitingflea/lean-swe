import LeanSwe.Env.Raw.Types
import LeanSwe.Env.Raw.Impl

namespace LeanSwe.Env.Raw

@[extern "leanswe_env_list"]
private opaque rawListEnv : IO (Array (String × String))

private def posixRawOps : Internal.PosixRawOps :=
  { listEnv := rawListEnv }

/-- Default minimal OS environment primitives backed by `IO.getEnv` and `c/env_shim.c`. -/
def defaultOps : RawEnvOps :=
  Internal.mkRawOps posixRawOps

/-- Convert a raw OS error record into a normalized `EnvError` with non-empty message. -/
@[inline] def mapRawError (err : EnvRawError) : EnvError :=
  defaultOps.mapRawError err

/-- Look up a single environment variable via `IO.getEnv` without upper-layer key validation. -/
@[inline] def getEnv (key : String) : IO (Except EnvRawError (Option String)) :=
  defaultOps.getEnv key

/-- List all `(key, value)` environment entries in process `environ` order. -/
@[inline] def listEnv : IO (Except EnvRawError (Array (String × String))) :=
  defaultOps.listEnv

end LeanSwe.Env.Raw

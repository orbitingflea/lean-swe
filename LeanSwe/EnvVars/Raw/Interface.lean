import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Impl

namespace LeanSwe.EnvVars.Raw

@[extern "leanswe_envvars_list"]
private opaque rawListEnv : IO (Array (String × String))

private def posixRawOps : Internal.PosixRawOps :=
  { listEnv := rawListEnv }

/-- Default minimal OS environment primitives backed by `IO.getEnv` and `c/envvars_shim.c`. -/
def defaultOps : RawEnvVarsOps :=
  Internal.mkRawOps posixRawOps

/-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
@[inline] def mapRawError (err : EnvVarsRawError) : EnvVarsError :=
  defaultOps.mapRawError err

/-- Look up a single environment variable via `IO.getEnv` without upper-layer key validation. -/
@[inline] def getEnv (key : String) : IO (Except EnvVarsRawError (Option String)) :=
  defaultOps.getEnv key

/-- List all `(key, value)` environment entries in process `environ` order. -/
@[inline] def listEnv : IO (Except EnvVarsRawError (Array (String × String))) :=
  defaultOps.listEnv

end LeanSwe.EnvVars.Raw

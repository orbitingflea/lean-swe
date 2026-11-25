import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Impl

namespace LeanSwe.EnvVars.Raw

@[extern "leanswe_envvars_getenv"]
private opaque rawGetEnvBytes (key : @& String) : BaseIO (Option ByteArray)

@[extern "leanswe_envvars_environ"]
private opaque rawListEnvironBytes : BaseIO (Array ByteArray)

private def posixRawOps : PosixRawOps :=
  { getEnvBytes := fun key => rawGetEnvBytes key
    listEnvironBytes := rawListEnvironBytes }

/-- Full OS environment primitive bundle including raw `listEnvironBytes`, backed by `c/envvars_shim.c`. -/
abbrev defaultOpsBase : RawEnvVarsBundle :=
  Internal.mkRawBundle posixRawOps

/-- Default minimal OS environment primitives backed by `c/envvars_shim.c` (`getenv(3)` and `environ(7)`). -/
def defaultOps : RawEnvVarsOps :=
  defaultOpsBase.toRawEnvVarsOpsM

/-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
@[inline] def mapRawError (err : EnvVarsRawError) : EnvVarsError :=
  defaultOps.mapRawError err

/-- Look up a single environment variable via `getenv(3)` and Lean UTF-8 decoding without upper-layer `.invalidKey` errors. -/
@[inline] def getEnv (key : String) : IO (Except EnvVarsRawError (Option String)) :=
  defaultOps.getEnv key

/-- List all `(key, value)` environment entries from `environ(7)` in order via Lean `'='` splitting and UTF-8 decoding. -/
@[inline] def listEnv : IO (Except EnvVarsRawError (Array (String × String))) :=
  defaultOps.listEnv

/-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order without UTF-8 decoding. -/
@[inline] def listEnvironBytes : IO (Array ByteArray) :=
  defaultOpsBase.listEnvironBytes

end LeanSwe.EnvVars.Raw

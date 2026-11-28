import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Impl

namespace LeanSwe.EnvVars

@[extern "leanswe_envvars_getenv"]
private opaque rawGetEnvBytes (key : @& String) : BaseIO (Option ByteArray)

@[extern "leanswe_envvars_environ"]
private opaque rawListEnvironBytes : BaseIO (Array ByteArray)

private def posixRawOps : PosixRawOps :=
  { getEnvBytes := fun key => rawGetEnvBytes key
    listEnvironBytes := rawListEnvironBytes }

/-- Default `EnvVarsApi` backed directly by `c/envvars_shim.c` (`getenv(3)` and `environ(7)`). -/
def defaultApi : EnvVarsApi :=
  Internal.mkApiM posixRawOps

/-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
@[inline] def mapRawError (err : EnvVarsRawError) : EnvVarsError :=
  defaultApi.mapRawError err

/-- Validate `key` and look up its value in the process environment. -/
@[inline] def getEnv (key : String) : IO (Except EnvVarsError (Option String)) :=
  defaultApi.getEnv key

/-- Return all `(key, value)` entries from the process environment. -/
@[inline] def listEnv : IO (Except EnvVarsError (Array (String × String))) :=
  defaultApi.listEnv

/-- Return the non-empty `HOME` directory string, or `.notFound` if unset or empty. -/
@[inline] def homeDir : IO (Except EnvVarsError String) :=
  defaultApi.homeDir

/-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order without UTF-8 decoding. -/
@[inline] def listEnvironBytes : IO (Array ByteArray) :=
  defaultApi.listEnvironBytes

/-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
@[inline] def splitSearchPath (path : String) : Array String :=
  defaultApi.splitSearchPath path

end LeanSwe.EnvVars

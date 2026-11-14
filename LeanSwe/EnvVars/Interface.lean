import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Impl
import LeanSwe.EnvVars.Raw.Interface

namespace LeanSwe.EnvVars

/-- Default `EnvVarsApi` backed by `LeanSwe.EnvVars.Raw.defaultOps`. -/
def defaultApi : EnvVarsApi :=
  Internal.mkApiM Raw.defaultOps

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

/-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
@[inline] def splitSearchPath (path : String) : Array String :=
  defaultApi.splitSearchPath path

end LeanSwe.EnvVars

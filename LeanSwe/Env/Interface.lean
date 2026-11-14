import LeanSwe.Env.Types
import LeanSwe.Env.Impl
import LeanSwe.Env.Raw.Interface

namespace LeanSwe.Env

/-- Default `EnvApi` backed by `LeanSwe.Env.Raw.defaultOps`. -/
def defaultApi : EnvApi :=
  Internal.mkApiM Raw.defaultOps

/-- Convert a raw OS error record into a normalized `EnvError` with non-empty message. -/
@[inline] def mapRawError (err : EnvRawError) : EnvError :=
  defaultApi.mapRawError err

/-- Validate `key` and look up its value in the process environment. -/
@[inline] def getEnv (key : String) : IO (Except EnvError (Option String)) :=
  defaultApi.getEnv key

/-- Return all `(key, value)` entries from the process environment. -/
@[inline] def listEnv : IO (Except EnvError (Array (String × String))) :=
  defaultApi.listEnv

/-- Return the non-empty `HOME` directory string, or `.notFound` if unset or empty. -/
@[inline] def homeDir : IO (Except EnvError String) :=
  defaultApi.homeDir

/-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
@[inline] def splitSearchPath (path : String) : Array String :=
  defaultApi.splitSearchPath path

end LeanSwe.Env

import LeanSwe.EnvVars.Raw.Types

namespace LeanSwe.EnvVars

export LeanSwe.EnvVars.Raw
  (EnvVarsErrorKind EnvVarsError EnvVarsRawError RawEnvVarsOpsM RawEnvVarsOps)

/-- Public read-only environment operations exported by `LeanSwe.EnvVars`, parameterized over `m`. -/
structure EnvVarsApiM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
  mapRawError : EnvVarsRawError → EnvVarsError
  /-- Validate `key` and look up its value in the process environment. -/
  getEnv : String → m (Except EnvVarsError (Option String))
  /-- Return all `(key, value)` entries from the process environment. -/
  listEnv : m (Except EnvVarsError (Array (String × String)))
  /-- Return the non-empty `HOME` directory string, or `.notFound` if unset or empty. -/
  homeDir : m (Except EnvVarsError String)
  /-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
  splitSearchPath : String → Array String

/-- Concrete `IO` environment API bundle exported by `LeanSwe.EnvVars`. -/
abbrev EnvVarsApi := EnvVarsApiM IO

end LeanSwe.EnvVars

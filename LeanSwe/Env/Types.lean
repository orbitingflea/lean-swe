import LeanSwe.Env.Raw.Types

namespace LeanSwe.Env

export LeanSwe.Env.Raw
  (EnvErrorKind EnvError EnvRawError RawEnvOpsM RawEnvOps)

/-- Public read-only environment operations exported by `LeanSwe.Env`, parameterized over `m`. -/
structure EnvApiM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `EnvError` with non-empty message. -/
  mapRawError : EnvRawError → EnvError
  /-- Validate `key` and look up its value in the process environment. -/
  getEnv : String → m (Except EnvError (Option String))
  /-- Return all `(key, value)` entries from the process environment. -/
  listEnv : m (Except EnvError (Array (String × String)))
  /-- Return the non-empty `HOME` directory string, or `.notFound` if unset or empty. -/
  homeDir : m (Except EnvError String)
  /-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
  splitSearchPath : String → Array String

/-- Concrete `IO` environment API bundle exported by `LeanSwe.Env`. -/
abbrev EnvApi := EnvApiM IO

end LeanSwe.Env

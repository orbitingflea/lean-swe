namespace LeanSwe.EnvVars

/-- Classification of environment variable errors. -/
inductive EnvVarsErrorKind where
  /-- Invalid environment variable name (empty, contains `=`, or contains NUL). -/
  | invalidKey
  /-- Invalid UTF-8 encoding in an environment variable entry or value. -/
  | invalidEncoding
  /-- Required environment variable (`HOME` in `homeDir`) is unset or empty. -/
  | notFound
  /-- Other OS-level failure reading the process environment. -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed environment error returned by `LeanSwe.EnvVars` operations. -/
structure EnvVarsError where
  /-- Machine-checkable error category. -/
  kind : EnvVarsErrorKind
  /-- Environment variable name associated with the error, when available. -/
  key : Option String := none
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw OS environment error inputs for total error-mapping specs. -/
inductive EnvVarsRawError where
  /-- Invalid UTF-8 sequence encountered while decoding an environment key or value. -/
  | invalidEncoding (key? : Option String) (detail : String)
  /-- Invalid argument or key rejected by the OS boundary (`EINVAL`). -/
  | invalidArgument (key? : Option String) (errno : UInt32) (detail : String)
  /-- Numeric OS error (such as `ENOMEM`). -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic user-constructed error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Thin byte-level POSIX data-passing hooks parameterized over effect monad `m`,
    wrapping `getenv(3)` and `environ(7)` with zero UTF-8 decoding or `'='` parsing in C. -/
structure PosixRawOpsM (m : Type → Type) where
  /-- Look up raw NUL-free value bytes for a valid POSIX environment variable name via `getenv(3)`,
      returning `none` when unset. -/
  getEnvBytes : String → m (Option ByteArray)
  /-- Copy all raw NUL-free entry byte slices from POSIX `environ(7)` in order
      (`#[]` when `environ == NULL`). -/
  listEnvironBytes : m (Array ByteArray)

/-- Concrete `IO` thin-call POSIX byte hooks backed by `c/envvars_shim.c`. -/
abbrev PosixRawOps := PosixRawOpsM IO

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
  /-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order without UTF-8 decoding. -/
  listEnvironBytes : m (Array ByteArray)
  /-- Split a POSIX `:`-delimited search path, dropping empty segments (`""` yields `#[]`). -/
  splitSearchPath : String → Array String

/-- Concrete `IO` environment API bundle exported by `LeanSwe.EnvVars`. -/
abbrev EnvVarsApi := EnvVarsApiM IO

end LeanSwe.EnvVars

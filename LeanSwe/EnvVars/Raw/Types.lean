namespace LeanSwe.EnvVars.Raw

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

/-- Typed environment error returned by `LeanSwe.EnvVars.Raw` and `LeanSwe.EnvVars` operations. -/
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

/-- Minimal read-only environment primitives parameterized over effect monad `m`. -/
structure RawEnvVarsOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
  mapRawError : EnvVarsRawError → EnvVarsError
  /-- Look up a single environment variable without upper-layer key validation. -/
  getEnv : String → m (Except EnvVarsRawError (Option String))
  /-- List all `(key, value)` environment entries in process `environ` order. -/
  listEnv : m (Except EnvVarsRawError (Array (String × String)))

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.EnvVars.Raw`. -/
abbrev RawEnvVarsOps := RawEnvVarsOpsM IO

end LeanSwe.EnvVars.Raw

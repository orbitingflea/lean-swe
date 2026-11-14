namespace LeanSwe.Env.Raw

/-- Classification of environment variable errors. -/
inductive EnvErrorKind where
  /-- Invalid environment variable name (empty, contains `=`, or contains NUL). -/
  | invalidKey
  /-- Invalid UTF-8 encoding in an environment variable entry or value. -/
  | invalidEncoding
  /-- Required environment variable (`HOME` in `homeDir`) is unset or empty. -/
  | notFound
  /-- Other OS-level failure reading the process environment. -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed environment error returned by `LeanSwe.Env.Raw` and `LeanSwe.Env` operations. -/
structure EnvError where
  /-- Machine-checkable error category. -/
  kind : EnvErrorKind
  /-- Environment variable name associated with the error, when available. -/
  key : Option String := none
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw OS environment error inputs for total error-mapping specs. -/
inductive EnvRawError where
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
structure RawEnvOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `EnvError` with non-empty message. -/
  mapRawError : EnvRawError → EnvError
  /-- Look up a single environment variable without upper-layer key validation. -/
  getEnv : String → m (Except EnvRawError (Option String))
  /-- List all `(key, value)` environment entries in process `environ` order. -/
  listEnv : m (Except EnvRawError (Array (String × String)))

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.Env.Raw`. -/
abbrev RawEnvOps := RawEnvOpsM IO

end LeanSwe.Env.Raw

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

/-- Constructor tag enum for `EnvVarsRawError` used in exhaustive error-coverage declarations. -/
inductive EnvVarsRawErrorKind where
  /-- Corresponds to `EnvVarsRawError.invalidEncoding`. -/
  | invalidEncoding
  /-- Corresponds to `EnvVarsRawError.invalidArgument`. -/
  | invalidArgument
  /-- Corresponds to `EnvVarsRawError.otherError`. -/
  | otherError
  /-- Corresponds to `EnvVarsRawError.userError`. -/
  | userError
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

/-- Return the closed constructor tag of an `EnvVarsRawError`. -/
def EnvVarsRawError.kind : EnvVarsRawError → EnvVarsRawErrorKind
  | .invalidEncoding _ _ => .invalidEncoding
  | .invalidArgument _ _ _ => .invalidArgument
  | .otherError _ _ => .otherError
  | .userError _ => .userError

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

/-- Minimal read-only environment primitives parameterized over effect monad `m`. -/
structure RawEnvVarsOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `EnvVarsError` with non-empty message. -/
  mapRawError : EnvVarsRawError → EnvVarsError
  /-- Look up a single environment variable via `getenv(3)` without upper-layer `.invalidKey` errors,
      returning `.ok none` when unset (or when `key` cannot name a POSIX environment variable) and
      `.error (.invalidEncoding (some key) ...)` when the raw value bytes are not valid UTF-8. -/
  getEnv : String → m (Except EnvVarsRawError (Option String))
  /-- List all `(key, value)` environment entries from `environ(7)` in order, skipping entries
      lacking `'='` or starting with `'='`, and failing with `.error (.invalidEncoding ...)` on
      invalid UTF-8 in any key (`key? = none`) or value (`key? = some key`). -/
  listEnv : m (Except EnvVarsRawError (Array (String × String)))

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.EnvVars.Raw`. -/
abbrev RawEnvVarsOps := RawEnvVarsOpsM IO

/-- Full capability bundle for `LeanSwe.EnvVars.Raw`, extending `RawEnvVarsOpsM m` with raw `listEnvironBytes`. -/
structure RawEnvVarsBundleM (m : Type → Type) extends RawEnvVarsOpsM m where
  /-- Snapshot raw NUL-free byte entries directly from `environ(7)` in order. -/
  listEnvironBytes : m (Array ByteArray)

/-- Concrete `IO` full capability bundle exported by `LeanSwe.EnvVars.Raw`. -/
abbrev RawEnvVarsBundle := RawEnvVarsBundleM IO

end LeanSwe.EnvVars.Raw

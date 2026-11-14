import LeanSwe.Env.Raw.Types

namespace LeanSwe.Env.Raw.Internal

open LeanSwe.Env.Raw (EnvErrorKind EnvError EnvRawError RawEnvOps)

/-- POSIX FFI operations injected by `LeanSwe.Env.Raw.Interface`. -/
structure PosixRawOps where
  /-- Read all `(key, value)` entries from POSIX `environ`. -/
  listEnv : IO (Array (String × String))

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `EnvRawError` record into a normalized `EnvError` with non-empty message. -/
def mapRawError : EnvRawError → EnvError
  | .invalidEncoding key? detail =>
    { kind := .invalidEncoding
      key := key?
      errnoCode := none
      message := nonEmptyMsg "invalid UTF-8 in environment" detail }
  | .invalidArgument key? code detail =>
    { kind := .invalidKey
      key := key?
      errnoCode := some code
      message := nonEmptyMsg "invalid environment variable name" detail }
  | .otherError code detail =>
    { kind := .ioError
      key := none
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      key := none
      errnoCode := none
      message := nonEmptyMsg "environment error" detail }

/-- Convert a Lean `IO.Error` into `EnvRawError`. -/
def ioErrorToRaw : IO.Error → EnvRawError
  | .invalidArgument key? code detail =>
    if detail == "invalid UTF-8 in environment entry" then
      .invalidEncoding key? detail
    else
      .invalidArgument key? code detail
  | .otherError code detail => .otherError code detail
  | .userError detail =>
    if detail == "invalid UTF-8 in environment entry" then
      .invalidEncoding none detail
    else
      .userError detail
  | .noFileOrDirectory _ code detail => .otherError code detail
  | .alreadyExists _ code detail => .otherError code detail
  | .permissionDenied _ code detail => .otherError code detail
  | .inappropriateType _ code detail => .otherError code detail
  | .unsupportedOperation code detail => .otherError code detail
  | .unsatisfiedConstraints code detail => .otherError code detail
  | .illegalOperation code detail => .otherError code detail
  | .resourceBusy code detail => .otherError code detail
  | .resourceVanished code detail => .otherError code detail
  | .hardwareFault code detail => .otherError code detail
  | .protocolError code detail => .otherError code detail
  | .timeExpired code detail => .otherError code detail
  | .interrupted p code detail => .otherError code s!"{p}: {detail}"
  | .resourceExhausted _ code detail => .otherError code detail
  | .noSuchThing _ code detail => .otherError code detail
  | .unexpectedEof => .userError "unexpected end of file"

/-- Build the concrete `RawEnvOps` bundle from injected POSIX C-ABI hooks. -/
def mkRawOps (posix : PosixRawOps) : RawEnvOps :=
  { mapRawError := mapRawError
    getEnv := fun key => do
      let val ← IO.getEnv key
      return .ok val
    listEnv := do
      try
        return .ok (← posix.listEnv)
      catch err =>
        return .error (ioErrorToRaw err) }

end LeanSwe.Env.Raw.Internal

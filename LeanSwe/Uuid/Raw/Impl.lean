import LeanSwe.Uuid.Raw.Types

namespace LeanSwe.Uuid.Raw.Internal

open LeanSwe.Uuid.Raw (UuidErrorKind UuidError UuidRawError RawUuidOpsM RawUuidOps)

/-- Native OS entropy hook injected by `LeanSwe.Uuid.Raw.Interface`. -/
structure PosixRandomOps where
  /-- Read 16 random bytes from OS entropy. -/
  randomBytes16 : IO ByteArray

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `UuidRawError` record into a normalized `UuidError` with kind `.entropyFailed` and a non-empty message. -/
def mapRawError : UuidRawError → UuidError
  | .osError code detail =>
    { kind := .entropyFailed
      errnoCode := some code
      message := nonEmptyMsg s!"os entropy error {code}" detail }
  | .shortRead gotBytes detail =>
    { kind := .entropyFailed
      errnoCode := none
      message := nonEmptyMsg s!"entropy short read: expected 16 bytes, got {gotBytes}" detail }
  | .userError detail =>
    { kind := .entropyFailed
      errnoCode := none
      message := nonEmptyMsg "os entropy error" detail }

/-- Convert a Lean `IO.Error` into `UuidRawError`. -/
def ioErrorToRaw : IO.Error → UuidRawError
  | .noFileOrDirectory _ code detail => .osError code detail
  | .alreadyExists _ code detail => .osError code detail
  | .permissionDenied _ code detail => .osError code detail
  | .inappropriateType _ code detail => .osError code detail
  | .invalidArgument _ code detail => .osError code detail
  | .unsupportedOperation code detail => .osError code detail
  | .unsatisfiedConstraints code detail => .osError code detail
  | .illegalOperation code detail => .osError code detail
  | .resourceBusy code detail => .osError code detail
  | .resourceVanished code detail => .osError code detail
  | .hardwareFault code detail => .osError code detail
  | .protocolError code detail => .osError code detail
  | .timeExpired code detail => .osError code detail
  | .interrupted _ code detail => .osError code detail
  | .resourceExhausted _ code detail => .osError code detail
  | .noSuchThing _ code detail => .osError code detail
  | .unexpectedEof => .userError "unexpected end of entropy stream"
  | .otherError code detail => .osError code detail
  | .userError detail => .userError detail

/-- Build the concrete `RawUuidOps` bundle from the injected C-ABI entropy hook. -/
def mkRawOps (posix : PosixRandomOps) : RawUuidOps :=
  { mapRawError := mapRawError
    randomBytes16 := do
      try
        let bs ← posix.randomBytes16
        if bs.size != 16 then
          return .error (mapRawError (.shortRead bs.size s!"expected 16 bytes, got {bs.size}"))
        return .ok bs
      catch err =>
        return .error (mapRawError (ioErrorToRaw err)) }

end LeanSwe.Uuid.Raw.Internal

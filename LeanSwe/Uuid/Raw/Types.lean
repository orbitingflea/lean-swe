namespace LeanSwe.Uuid.Raw

/-- Classification of failures in `LeanSwe.Uuid.Raw` and `LeanSwe.Uuid`. -/
inductive UuidErrorKind where
  /-- OS entropy source failed (`getrandom` / `/dev/urandom` failure or short read). -/
  | entropyFailed
  /-- Input byte array did not have length 16. -/
  | invalidLength
  /-- Input string had invalid length, characters, or hyphen layout. -/
  | invalidFormat
  /-- Parsed UUID did not have RFC 4122 version 4 and variant `10xx` bits. -/
  | invalidVersion
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Uuid.Raw` and `LeanSwe.Uuid` operations. -/
structure UuidError where
  /-- Machine-checkable error category. -/
  kind : UuidErrorKind
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw OS entropy error inputs for total error-mapping specs. -/
inductive UuidRawError where
  /-- OS entropy read failed with `errno` and detail message. -/
  | osError (errno : UInt32) (detail : String)
  /-- Entropy source returned a byte count other than 16. -/
  | shortRead (gotBytes : Nat) (detail : String)
  /-- Generic runtime error message. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Minimal OS entropy primitive bundle parameterized over effect monad `m`. -/
structure RawUuidOpsM (m : Type → Type) where
  /-- Convert a raw OS entropy error record into a normalized `UuidError` with non-empty message. -/
  mapRawError : UuidRawError → UuidError
  /-- Read 16 cryptographically random bytes from OS entropy. -/
  randomBytes16 : m (Except UuidError ByteArray)

/-- Concrete `IO` OS entropy bundle exported by `LeanSwe.Uuid.Raw`. -/
abbrev RawUuidOps := RawUuidOpsM IO

end LeanSwe.Uuid.Raw

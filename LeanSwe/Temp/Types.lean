namespace LeanSwe.Temp

/-- Classification of failures in `LeanSwe.Temp`. -/
inductive TempErrorKind where
  /-- Invalid root path, directory prefix, or unexpected non-file lock entry. -/
  | invalidInput
  /-- Target path or temporary root does not exist. -/
  | notFound
  /-- Exclusive directory creation collided with an existing path. -/
  | alreadyExists
  /-- Insufficient filesystem permissions for temp directory operations. -/
  | permissionDenied
  /-- Expected a directory (for temp root or child), found a non-directory. -/
  | notADirectory
  /-- Underlying OS, environment, entropy, or lock I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Temp` operations. -/
structure TempError where
  /-- Machine-checkable error category. -/
  kind : TempErrorKind
  /-- Path associated with the failure, when applicable. -/
  path : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Summary returned by `cleanupStaleTempDirs`. -/
structure CleanupReport where
  /-- Full paths (`fs.join root name`) of removed directories in `listDir` sorted order. -/
  removed : Array String := #[]
  /-- Full paths of actively locked directories kept regardless of age. -/
  keptLocked : Array String := #[]
  /-- Full paths of unlocked directories without `.lock` kept within `maxAgeSec`. -/
  keptFresh : Array String := #[]
  /-- Full paths of non-matching names or non-directory/symlink entries skipped. -/
  skipped : Array String := #[]
  /-- Per-entry errors recorded without aborting the rest of the sweep. -/
  failed : Array TempError := #[]
  deriving Repr, BEq, DecidableEq

/-- Public temporary-directory operations exported by `LeanSwe.Temp`, parameterized over `m`. -/
structure TempApiM (m : Type → Type) where
  /-- Exclusively create `<root>/<dirPrefix><uuid>`, run `action dir`, and recursively remove `dir` on exit. -/
  withTempDir :
    {α : Type} → Option String → String → (String → m (Except TempError α)) → m (Except TempError α)
  /-- Like `withTempDir`, while holding a `.shared` advisory `flock` on `<dir>/.lock` during `action dir`. -/
  withLockedTempDir :
    {α : Type} → Option String → String → (String → m (Except TempError α)) → m (Except TempError α)
  /-- Sweep immediate subdirectories of `root` matching `dirPrefix`, respecting live locks and `maxAgeSec`. -/
  cleanupStaleTempDirs : Option String → String → Nat → m (Except TempError CleanupReport)

/-- Concrete `IO` temporary-directory API bundle exported by `LeanSwe.Temp`. -/
abbrev TempApi := TempApiM IO

end LeanSwe.Temp

import LeanSwe.EnvVars.Interface
import LeanSwe.Fs.Interface
import LeanSwe.Temp.Impl
import LeanSwe.Temp.Types
import LeanSwe.Time.Interface
import LeanSwe.Uuid.Interface

namespace LeanSwe.Temp

/-- Construct a `TempApiM m` over custom capability interfaces. -/
@[inline] def mkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : LeanSwe.Fs.FsApiM m)
    (time : LeanSwe.Time.TimeOpsM m)
    (uuid : LeanSwe.Uuid.UuidApiM m)
    (env : LeanSwe.EnvVars.EnvVarsApiM m) : TempApiM m :=
  Internal.mkApiM fs time uuid env

/-- Default concrete `IO` temporary-directory API bundle. -/
def defaultApi : TempApi :=
  Internal.mkApiM
    LeanSwe.Fs.defaultApi
    LeanSwe.Time.defaultOps
    LeanSwe.Uuid.defaultApi
    LeanSwe.EnvVars.defaultApi

/-- Create an exclusive `0o700` temporary directory, execute `action dir`, and remove it on exit. -/
@[inline] def withTempDir {α : Type}
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (action : String → IO (Except TempError α)) : IO (Except TempError α) :=
  defaultApi.withTempDir root? dirPrefix action

/-- Create an exclusive `0o700` temporary directory locked `.shared` via `<dir>/.lock`, execute `action dir`, and remove it on exit. -/
@[inline] def withLockedTempDir {α : Type}
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (action : String → IO (Except TempError α)) : IO (Except TempError α) :=
  defaultApi.withLockedTempDir root? dirPrefix action

/-- Sweep immediate subdirectories under `root` matching `dirPrefix`, preserving active `.lock` dirs and unlocked dirs within `maxAgeSec`. -/
@[inline] def cleanupStaleTempDirs
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (maxAgeSec : Nat := 86400) : IO (Except TempError CleanupReport) :=
  defaultApi.cleanupStaleTempDirs root? dirPrefix maxAgeSec

end LeanSwe.Temp

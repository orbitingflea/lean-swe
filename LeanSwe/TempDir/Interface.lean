import LeanSwe.EnvVars.Interface
import LeanSwe.Fs.Interface
import LeanSwe.TempDir.Impl
import LeanSwe.TempDir.Model
import LeanSwe.TempDir.Types
import LeanSwe.Time.Interface
import LeanSwe.Uuid.Interface

namespace LeanSwe.TempDir

/-- Construct a `TempDirApiM m` over custom capability interfaces. -/
@[inline] def mkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : LeanSwe.Fs.FsApiM m)
    (time : LeanSwe.Time.TimeOpsM m)
    (uuid : LeanSwe.Uuid.UuidApiM m)
    (env : LeanSwe.EnvVars.EnvVarsApiM m) : TempDirApiM m :=
  Internal.mkApiFromCapsM { fs := fs, time := time, uuid := uuid, env := env }

/-- Default concrete `IO` temporary-directory API bundle. -/
def defaultApi : TempDirApi :=
  Internal.mkApiFromCapsM
    { fs := LeanSwe.Fs.defaultApi
      time := LeanSwe.Time.defaultOps
      uuid := LeanSwe.Uuid.defaultApi
      env := LeanSwe.EnvVars.defaultApi }

/-- Create an exclusive `0o700` temporary directory, execute `action dir`, and remove it on exit. -/
@[inline] def withTempDir {α : Type}
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (action : String → IO (Except TempDirError α)) : IO (Except TempDirError α) :=
  defaultApi.withTempDir root? dirPrefix action

/-- Create an exclusive `0o700` temporary directory locked `.shared` via `<dir>/.lock`, execute `action dir`, and remove it on exit. -/
@[inline] def withLockedTempDir {α : Type}
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (action : String → IO (Except TempDirError α)) : IO (Except TempDirError α) :=
  defaultApi.withLockedTempDir root? dirPrefix action

/-- Sweep immediate subdirectories under `root` matching `dirPrefix`, preserving active `.lock` dirs and unlocked dirs within `maxAgeSec`. -/
@[inline] def cleanupStaleTempDirs
    (root? : Option String := none)
    (dirPrefix : String := "tmp-")
    (maxAgeSec : Nat := 86400) : IO (Except TempDirError CleanupReport) :=
  defaultApi.cleanupStaleTempDirs root? dirPrefix maxAgeSec

end LeanSwe.TempDir

import Core.NondetTest
import Core.Assumptions
import LeanSwe.EnvVars.Types
import LeanSwe.Fs.Types
import LeanSwe.TempDir.Types
import LeanSwe.Time.Types
import LeanSwe.Uuid.Types

namespace LeanSwe.TempDir

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)

/-- Builder function assembling a `TempDirApiM m` from injected `Fs`, `Time`, `Uuid`, and `Env` interfaces. -/
abbrev TempDirBuilder (m : Type → Type) :=
  FsApiM m → TimeOpsM m → UuidApiM m → EnvVarsApiM m → TempDirApiM m

private def validPrefix (p : String) : Bool :=
  !p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)

private def validRoot (r : String) : Bool :=
  !r.isEmpty && !(Char.ofNat 0 ∈ r.toList)

private def validEntryName (n : String) : Bool :=
  !n.isEmpty && n != "." && n != ".." && !('/' ∈ n.toList) && !(Char.ofNat 0 ∈ n.toList)

private def hasRwx (st : FileStat) : Prop :=
  st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1

private def hasPath (xs : Array String) (p : String) : Bool :=
  xs.toList.contains p

private def isSorted (xs : Array String) : Bool :=
  xs.toList.Pairwise (· ≤ ·)

/-- `withTempDir` creates `<root>/<dirPrefix><uuid>` with mode `0o700`, executes `action dir`, returns `.ok val`, and removes `dir` on exit. -/
def test_tempdir_withTempDir_okCleansUpAndSetsMode
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let val ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let api := mkApi fs time uuid env
    let (res, s₁) := (api.withTempDir (some root) dirPrefix fun d => do
      let st ← fs.lstat d
      match st with
      | .error _ => return .error { kind := .ioError, path := some d, message := "lstat inside action failed" }
      | .ok info =>
        if info.kind != .dir || info.mode != 0o700 || d != dir then
          return .error { kind := .invalidInput, path := some d, message := "unexpected dir mode or path" }
        else
          match ← fs.writeText (fs.join d "payload.txt") "hello" with
          | .error _ => return .error { kind := .ioError, path := some d, message := "writeText inside action failed" }
          | .ok () => return .ok val).run s₀
    NondetTest.assert (res = .ok val)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)

/-- `withTempDir` cleans up `dir` and returns `action`'s `.error` with precedence over cleanup errors. -/
def test_tempdir_withTempDir_errorCleansUpAndPreservesError
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let actionErr ← nondet TempDirError
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let api := mkApi fs time uuid env
    let (res, s₁) := (api.withTempDir (some root) dirPrefix fun d => do
      let _ ← fs.writeText (fs.join d "tmp.txt") "data"
      return (Except.error actionErr : Except TempDirError Nat)).run s₀
    NondetTest.assert (res = .error actionErr)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)
    let fsFailClean : FsApiM (StateM S) :=
      { fs with rmtree := fun _ _ => pure (.error { kind := .permissionDenied, message := "cleanup failed" }) }
    let (resFail, _) := ((mkApi fsFailClean time uuid env).withTempDir (some root) dirPrefix fun _ =>
      pure (Except.error actionErr : Except TempDirError Nat)).run s₀
    NondetTest.assert (resFail = .error actionErr)

/-- When `action` returns `.ok` and `fs.rmtree` fails, `withTempDir` propagates the cleanup error rather than swallowing it. -/
def test_tempdir_withTempDir_cleanupErrorReturnedOnOk
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let val ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let fsFailClean : FsApiM (StateM S) :=
      { fs with rmtree := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "rm failed" }) }
    let (res, _) := ((mkApi fsFailClean time uuid env).withTempDir (some root) dirPrefix fun _ =>
      pure (.ok val)).run s₀
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .permissionDenied ∧ e.message ≠ "")

/-- Exclusive creation rejects pre-existing directories or symlinks at `<root>/<dirPrefix><uuid>` with `.alreadyExists` without running `action` or deleting the existing entry. -/
def test_tempdir_withTempDir_collisionRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let markerPath ← nondet String
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  assume (((fs.lstat markerPath).run s₀).1.isOk = false)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (∃ stExist, ((fs.lstat dir).run sAfterUuid).1 = .ok stExist ∧
      (stExist.kind = .dir ∨ stExist.kind = .symlink))
    let api := mkApi fs time uuid env
    let (res, s₁) := (api.withTempDir (some root) dirPrefix fun _ => do
      let _ ← fs.writeText markerPath "ran"
      return (.ok () : Except TempDirError Unit)).run s₀
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .alreadyExists)
    NondetTest.assert (((fs.lstat markerPath).run s₁).1.isOk = false)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = true)

/-- If `fs.chmod dir 0o700` fails right after `fs.mkdir`, `withTempDir` rolls back `dir` without running `action`. -/
def test_tempdir_withTempDir_chmodFailureRollsBack
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let markerPath ← nondet String
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  assume (((fs.lstat markerPath).run s₀).1.isOk = false)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let fsBadChmod : FsApiM (StateM S) :=
      { fs with chmod := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "chmod denied" }) }
    let (res, s₁) := ((mkApi fsBadChmod time uuid env).withTempDir (some root) dirPrefix fun _ => do
      let _ ← fs.writeText markerPath "ran"
      return (.ok () : Except TempDirError Unit)).run s₀
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .permissionDenied)
    NondetTest.assert (((fs.lstat markerPath).run s₁).1.isOk = false)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)

/-- All three operations reject invalid `dirPrefix` (`""`, `"."`, `".."`, leading `'.'`, `'/'`, NUL) and invalid explicit `root?` (`""`, NUL) with `.invalidInput` without modifying state. -/
def test_tempdir_validation_rejectsInvalidInputs
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  assume (¬ validPrefix dirPrefix ∨ ¬ validRoot root)
  let api := mkApi fs time uuid env
  let (r1, s1) := (api.withTempDir (some root) dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
  let (r2, s2) := (api.withLockedTempDir (some root) dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
  let (r3, s3) := (api.cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀
  NondetTest.assert (∃ e, r1 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (∃ e, r2 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (∃ e, r3 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (s1 = s₀ ∧ s2 = s₀ ∧ s3 = s₀)

/-- With `root? = none`, all three operations resolve non-empty `TMPDIR`, reject NUL `TMPDIR` with `.invalidInput`, reject missing/non-dir `TMPDIR` strictly, and fall back to `"/tmp"` when `TMPDIR` is unset or empty. -/
def test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dirPrefix ← nondet String
  assume (validPrefix dirPrefix)
  let (envRes, sAfterEnv) := (env.getEnv "TMPDIR").run s₀
  let (uRes, sAfterUuid) := uuid.getUuid.run sAfterEnv
  let api := mkApi fs time uuid env
  match envRes, uRes with
  | .ok (some tmpdir), .ok u =>
    if !tmpdir.isEmpty then
      if Char.ofNat 0 ∈ tmpdir.toList then
        let (r1, s1) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
        let (r2, s2) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
        let (r3, s3) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
        NondetTest.assert ((∃ e, r1 = .error e ∧ e.kind = .invalidInput) ∧ s1 = sAfterEnv)
        NondetTest.assert ((∃ e, r2 = .error e ∧ e.kind = .invalidInput) ∧ s2 = sAfterEnv)
        NondetTest.assert ((∃ e, r3 = .error e ∧ e.kind = .invalidInput) ∧ s3 = sAfterEnv)
      else
        match ((fs.stat tmpdir).run sAfterUuid).1 with
        | .error fe =>
          let (r1, _) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
          let (r2, _) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
          let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
          NondetTest.assert (∃ te, r1 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
          NondetTest.assert (∃ te, r2 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
          NondetTest.assert (∃ te, r3 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
        | .ok st =>
          if st.kind != .dir then
            let (r1, _) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
            let (r2, _) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempDirError Unit)).run s₀
            let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
            NondetTest.assert (∃ te, r1 = .error te ∧ te.kind = .notADirectory)
            NondetTest.assert (∃ te, r2 = .error te ∧ te.kind = .notADirectory)
            NondetTest.assert (∃ te, r3 = .error te ∧ te.kind = .notADirectory)
          else
            assume (hasRwx st)
            let expectedDir := fs.join tmpdir (dirPrefix ++ uuid.toString u)
            assume (((fs.lstat expectedDir).run sAfterUuid).1.isOk = false)
            let (r1, _) := (api.withTempDir none dirPrefix fun d => pure (.ok d)).run s₀
            let (r2, _) := (api.withLockedTempDir none dirPrefix fun d => pure (.ok d)).run s₀
            let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
            NondetTest.assert (r1 = .ok expectedDir)
            NondetTest.assert (r2 = .ok expectedDir)
            NondetTest.assert (r3.isOk = true)
    else
      assume (∃ stTmp, ((fs.stat "/tmp").run sAfterUuid).1 = .ok stTmp ∧ hasRwx stTmp)
      let expectedDir := fs.join "/tmp" (dirPrefix ++ uuid.toString u)
      assume (((fs.lstat expectedDir).run sAfterUuid).1.isOk = false)
      let (r1, _) := (api.withTempDir none dirPrefix fun d => pure (.ok d)).run s₀
      let (r2, _) := (api.withLockedTempDir none dirPrefix fun d => pure (.ok d)).run s₀
      let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
      NondetTest.assert (r1 = .ok expectedDir)
      NondetTest.assert (r2 = .ok expectedDir)
      NondetTest.assert (r3.isOk = true)
  | .ok none, .ok u =>
    assume (∃ stTmp, ((fs.stat "/tmp").run sAfterUuid).1 = .ok stTmp ∧ hasRwx stTmp)
    let expectedDir := fs.join "/tmp" (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat expectedDir).run sAfterUuid).1.isOk = false)
    let (r1, _) := (api.withTempDir none dirPrefix fun d => pure (.ok d)).run s₀
    let (r2, _) := (api.withLockedTempDir none dirPrefix fun d => pure (.ok d)).run s₀
    let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
    NondetTest.assert (r1 = .ok expectedDir)
    NondetTest.assert (r2 = .ok expectedDir)
    NondetTest.assert (r3.isOk = true)
  | _, _ => assume False

/-- `withLockedTempDir` sets mode `0o700`, holds a `.shared` lock on `<dir>/.lock` while `action` runs, cleans up `dir` and releases all locks on `.ok` and `.error`, and propagates lock errors with precedence over cleanup errors. -/
def test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let val ← nondet Nat
  let err ← nondet TempDirError
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    let lockPath := fs.join dir ".lock"
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let api := mkApi fs time uuid env
    let (resOk, sOk) := (api.withLockedTempDir (some root) dirPrefix fun d => do
      let stDir ← fs.lstat d
      let lst ← fs.lstat (fs.join d ".lock")
      let sharedProbe ← fs.tryWithFileLock (fs.join d ".lock") .shared false (pure (.ok ()))
      let exProbe ← fs.tryWithFileLock (fs.join d ".lock") .exclusive false (pure (.ok ()))
      match stDir, lst, sharedProbe, exProbe with
      | .ok info, .ok st, .ok (some ()), .ok none =>
        if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
          return .ok val
        else
          return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
      | .error _, _, _, _ =>
        return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
      | _, .error _, _, _ =>
        return .error { kind := .notFound, path := some d, message := "missing lock file" }
      | _, _, _, _ =>
        return .error { kind := .ioError, path := some d, message := "lock invariant failed" }).run s₀
    NondetTest.assert (resOk = .ok val)
    NondetTest.assert (((fs.lstat dir).run sOk).1.isOk = false)
    NondetTest.assert (∃ e, ((fs.lstat lockPath).run sOk).1 = .error e ∧ e.kind = .notFound)
    let probeOk := (do
      let _ ← fs.mkdir dir false false
      fs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sOk
    NondetTest.assert (probeOk.1 = .ok (some ()))
    let (resErr, sErr) := (api.withLockedTempDir (some root) dirPrefix fun _ =>
      pure (Except.error err : Except TempDirError Nat)).run s₀
    NondetTest.assert (resErr = .error err)
    NondetTest.assert (((fs.lstat dir).run sErr).1.isOk = false)
    let probeErr := (do
      let _ ← fs.mkdir dir false false
      fs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sErr
    NondetTest.assert (probeErr.1 = .ok (some ()))
    let fsLockAndRmFail : FsApiM (StateM S) :=
      { fs with
        withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
        rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
    let (resLockRm, _) := ((mkApi fsLockAndRmFail time uuid env).withLockedTempDir (some root) dirPrefix fun _ =>
      pure (.ok val)).run s₀
    NondetTest.assert (∃ e, resLockRm = .error e ∧ e.kind = .permissionDenied)
    let fsLockFailCleanOk : FsApiM (StateM S) :=
      { fs with
        withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
    let (resLockClean, sLockClean) := ((mkApi fsLockFailCleanOk time uuid env).withLockedTempDir (some root) dirPrefix fun _ =>
      pure (.ok val)).run s₀
    NondetTest.assert (∃ e, resLockClean = .error e ∧ e.kind = .permissionDenied)
    NondetTest.assert (((fs.lstat dir).run sLockClean).1.isOk = false)

/-- `withLockedTempDir` ignores `.notFound` from `fs.rmtree` in its finalizer so a concurrent sweep removing `dir` after `.lock` release does not discard `action`'s `.ok` result. -/
def test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let val ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let fsConcurrentSweep : FsApiM (StateM S) :=
      { fs with
        rmtree := fun p ign => do
          let _ ← fs.rmtree p ign
          pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
    let (res, s₁) := ((mkApi fsConcurrentSweep time uuid env).withLockedTempDir (some root) dirPrefix fun _ =>
      pure (.ok val)).run s₀
    NondetTest.assert (res = .ok val)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)

/-- Over `ExceptT String (StateM S)`, an uncaught exception thrown inside `withTempDir` or `withLockedTempDir` triggers cleanup (and lock release) while propagating the exception. -/
def test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock
    {S : Type} {runner} [NondetTest runner]
    (mkExApi : TempDirBuilder (ExceptT String (StateM S)))
    (fsEx : FsApiM (ExceptT String (StateM S))) (timeEx : TimeOpsM (ExceptT String (StateM S)))
    (uuidEx : UuidApiM (ExceptT String (StateM S))) (envEx : EnvVarsApiM (ExceptT String (StateM S)))
    (fs : FsApiM (StateM S)) (uuid : UuidApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let (uRes, sAfterUuid) := uuid.getUuid.run s₀
  match uRes with
  | .error _ => assume False
  | .ok u =>
    let dir := fs.join root (dirPrefix ++ uuid.toString u)
    assume (((fs.lstat dir).run sAfterUuid).1.isOk = false)
    let apiEx := mkExApi fsEx timeEx uuidEx envEx
    let (r1, s1) := (ExceptT.run (apiEx.withTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM S) (Except TempDirError Unit)))).run s₀
    NondetTest.assert (r1 = .error "boom")
    NondetTest.assert (((fs.lstat dir).run s1).1.isOk = false)
    let (r2, s2) := (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM S) (Except TempDirError Unit)))).run s₀
    NondetTest.assert (r2 = .error "boom")
    NondetTest.assert (((fs.lstat dir).run s2).1.isOk = false)
    let probeS2 := (do
      let _ ← fs.mkdir dir false false
      fs.tryWithFileLock (fs.join dir ".lock") .exclusive true (pure (.ok ()))).run s2
    NondetTest.assert (probeS2.1 = .ok (some ()))

/-- `cleanupStaleTempDirs` keeps any matching directory whose `<dir>/.lock` is actively locked (`.shared` or `.exclusive`), even when `age > maxAgeSec` (including `maxAgeSec = 0`). -/
def test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let childName ← nondet String
  let maxAgeSec ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (validEntryName childName)
  assume (dirPrefix.toList.isPrefixOf childName.toList)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let child := fs.join root childName
  let lockPath := fs.join child ".lock"
  assume (∃ stChild, ((fs.lstat child).run s₀).1 = .ok stChild ∧ stChild.kind = .dir)
  assume (∃ stLock, ((fs.lstat lockPath).run s₀).1 = .ok stLock ∧ stLock.kind = .file)
  let (nowTs, _) := time.nowTimestamp.run s₀
  let (stChildRes, _) := (fs.lstat child).run s₀
  match stChildRes with
  | .error _ => assume False
  | .ok stChild =>
    assume (nowTs.toSecondsSinceUnixEpoch.val - stChild.modifiedSec > (maxAgeSec : Int))
    let api := mkApi fs time uuid env
    let (res, _) := (fs.withFileLock lockPath .shared false do
      let rep ← api.cleanupStaleTempDirs (some root) dirPrefix maxAgeSec
      let innerProbe ← fs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))
      let stillExists ← fs.lstat child
      return .ok (rep, innerProbe, stillExists.isOk)).run s₀
    match res with
    | .error _ => assume False
    | .ok (repRes, innerProbe, stillExists) =>
      match repRes with
      | .error _ => NondetTest.assert False
      | .ok rep =>
        NondetTest.assert (hasPath rep.keptLocked child ∧ ¬ hasPath rep.removed child)
        NondetTest.assert (innerProbe = .ok none ∧ stillExists = true)

/-- `cleanupStaleTempDirs` immediately removes a matching directory whose `<dir>/.lock` exists and is unlocked, even when `age = 0 ≤ maxAgeSec`, leaving zero locks held. -/
def test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let childName ← nondet String
  let maxAgeSec ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix ∧ maxAgeSec > 0)
  assume (validEntryName childName)
  assume (dirPrefix.toList.isPrefixOf childName.toList)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let child := fs.join root childName
  let lockPath := fs.join child ".lock"
  assume (∃ stChild, ((fs.lstat child).run s₀).1 = .ok stChild ∧ hasRwx stChild)
  assume (∃ stLock, ((fs.lstat lockPath).run s₀).1 = .ok stLock ∧ stLock.kind = .file)
  assume (((fs.listDir child).run s₀).1 = .ok #[".lock"])
  assume (((fs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₀).1 = .ok (some ()))
  let (nowTs, _) := time.nowTimestamp.run s₀
  let (stChildRes, _) := (fs.lstat child).run s₀
  match stChildRes with
  | .error _ => assume False
  | .ok stChild =>
    assume (nowTs.toSecondsSinceUnixEpoch.val - stChild.modifiedSec ≤ (maxAgeSec : Int))
    let (res, s₁) := ((mkApi fs time uuid env).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀
    match res with
    | .error _ => NondetTest.assert False
    | .ok rep =>
      NondetTest.assert (hasPath rep.removed child ∧ ¬ hasPath rep.keptLocked child ∧ ¬ hasPath rep.keptFresh child)
      NondetTest.assert (((fs.lstat child).run s₁).1.isOk = false)
      let probeAfter := (do
        let _ ← fs.mkdir child false false
        fs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run s₁
      NondetTest.assert (probeAfter.1 = .ok (some ()))

/-- For matching directories without `.lock`, `cleanupStaleTempDirs` keeps directories with `nowSec - modifiedSec ≤ maxAgeSec` (including equality and negative clock skew) and removes those with `nowSec - modifiedSec > maxAgeSec`. -/
def test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let childName ← nondet String
  let maxAgeSec ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (validEntryName childName)
  assume (dirPrefix.toList.isPrefixOf childName.toList)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let child := fs.join root childName
  let lockPath := fs.join child ".lock"
  assume (∃ stChild, ((fs.lstat child).run s₀).1 = .ok stChild ∧ hasRwx stChild)
  assume (∃ e, ((fs.lstat lockPath).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (nowTs, _) := time.nowTimestamp.run s₀
  let (stChildRes, _) := (fs.lstat child).run s₀
  match stChildRes with
  | .error _ => assume False
  | .ok stChild =>
    let ageSec := nowTs.toSecondsSinceUnixEpoch.val - stChild.modifiedSec
    let (res, s₁) := ((mkApi fs time uuid env).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀
    match res with
    | .error _ => NondetTest.assert False
    | .ok rep =>
      if ageSec ≤ (maxAgeSec : Int) then
        NondetTest.assert (hasPath rep.keptFresh child ∧ ¬ hasPath rep.removed child)
        NondetTest.assert (((fs.lstat child).run s₁).1.isOk = true)
      else
        assume (((fs.listDir child).run s₀).1 = .ok #[])
        NondetTest.assert (hasPath rep.removed child ∧ ¬ hasPath rep.keptFresh child)
        NondetTest.assert (((fs.lstat child).run s₁).1.isOk = false)

/-- `cleanupStaleTempDirs` skips non-matching names, regular files, and symlinks under `root` without modifying them, and emits sorted paths in `CleanupReport`. -/
def test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let entryName ← nondet String
  let maxAgeSec ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (validEntryName entryName)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let child := fs.join root entryName
  assume (∃ stChild, ((fs.lstat child).run s₀).1 = .ok stChild ∧
    (¬ dirPrefix.toList.isPrefixOf entryName.toList ∨ stChild.kind ≠ .dir))
  let (res, s₁) := ((mkApi fs time uuid env).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀
  match res with
  | .error _ => NondetTest.assert False
  | .ok rep =>
    NondetTest.assert (hasPath rep.skipped child ∧ ¬ hasPath rep.removed child)
    NondetTest.assert (((fs.lstat child).run s₁).1.isOk = true)
    NondetTest.assert (isSorted rep.removed ∧ isSorted rep.keptLocked ∧ isSorted rep.keptFresh ∧ isSorted rep.skipped)

/-- `cleanupStaleTempDirs` rejects non-regular `.lock` entries (symlinks, directories, other) into `failed` without removing `child`, and keeps `.lock` intact and unlocked when deleting a non-`.lock` child fails. -/
def test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempDirBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let childName ← nondet String
  let maxAgeSec ← nondet Nat
  assume (validRoot root ∧ validPrefix dirPrefix)
  assume (validEntryName childName)
  assume (dirPrefix.toList.isPrefixOf childName.toList)
  assume (∃ stRoot, ((fs.stat root).run s₀).1 = .ok stRoot ∧ hasRwx stRoot)
  let child := fs.join root childName
  let lockPath := fs.join child ".lock"
  assume (∃ stChild, ((fs.lstat child).run s₀).1 = .ok stChild ∧ hasRwx stChild)
  let (lockStatRes, _) := (fs.lstat lockPath).run s₀
  match lockStatRes with
  | .ok stLock =>
    if stLock.kind != .file then
      let (res, s₁) := ((mkApi fs time uuid env).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀
      match res with
      | .error _ => NondetTest.assert False
      | .ok rep =>
        NondetTest.assert (¬ hasPath rep.removed child ∧ ¬ hasPath rep.keptFresh child)
        NondetTest.assert (rep.failed.any (fun e => e.kind == .invalidInput && e.path == some lockPath))
        NondetTest.assert (((fs.lstat child).run s₁).1.isOk = true)
    else
      let payload := fs.join child "locked_child.txt"
      assume (∃ stP, ((fs.lstat payload).run s₀).1 = .ok stP ∧ stP.kind = .file)
      assume (((fs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₀).1 = .ok (some ()))
      let fsFailChild : FsApiM (StateM S) :=
        { fs with
          unlink := fun p miss =>
            if p == payload then pure (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" })
            else fs.unlink p miss }
      let (res, s₁) := ((mkApi fsFailChild time uuid env).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀
      match res with
      | .error _ => NondetTest.assert False
      | .ok rep =>
        NondetTest.assert (¬ hasPath rep.removed child ∧ ¬ hasPath rep.keptFresh child)
        NondetTest.assert (!rep.failed.isEmpty)
        NondetTest.assert (((fs.lstat lockPath).run s₁).1.isOk = true)
        NondetTest.assert (((fs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()))
  | .error _ => assume False

private def stubRemovePrefix (p : String) (xs : List String) : Bool :=
  let pref := if p == "/" then "/" else p ++ "/"
  xs.any fun k => k == p || pref.toList.isPrefixOf k.toList

/-- Complete `3 × 6` `(request, errorKind)` coverage matrix for pure orchestration package `LeanSwe.TempDir` (`TempDirErrorKind`). -/
def errorCoverage : List (ErrorObligation TempDirErrorKind) :=
  [ { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_invalidInput" .real }
  , { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .notFound
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_notFound" .real }
  , { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_alreadyExists" .mocked }
  , { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_permissionDenied" .real }
  , { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .notADirectory
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_notADirectory" .real }
  , { request := "LeanSwe.TempDir.withTempDir"
      errorKind := .ioError
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_ioError" .real }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_invalidInput" .real }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .notFound
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_notFound" .real }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_alreadyExists" .mocked }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_permissionDenied" .real }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .notADirectory
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_notADirectory" .real }
  , { request := "LeanSwe.TempDir.withLockedTempDir"
      errorKind := .ioError
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_ioError" .real }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_invalidInput" .real }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .notFound
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_notFound" .real }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_alreadyExists" .mocked }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_permissionDenied" .real }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .notADirectory
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_notADirectory" .real }
  , { request := "LeanSwe.TempDir.cleanupStaleTempDirs"
      errorKind := .ioError
      justification := .tested "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_ioError" .real } ]

end LeanSwe.TempDir

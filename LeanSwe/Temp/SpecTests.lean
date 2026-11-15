import Core.NondetTest
import LeanSwe.EnvVars.Types
import LeanSwe.Fs.Types
import LeanSwe.Temp.Types
import LeanSwe.Time.Types
import LeanSwe.Uuid.Types

namespace LeanSwe.Temp

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)

/-- Builder function assembling a `TempApiM m` from injected `Fs`, `Time`, `Uuid`, and `Env` interfaces. -/
abbrev TempBuilder (m : Type → Type) :=
  FsApiM m → TimeOpsM m → UuidApiM m → EnvVarsApiM m → TempApiM m

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
def test_temp_withTempDir_okCleansUpAndSetsMode
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_withTempDir_errorCleansUpAndPreservesError
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let actionErr ← nondet TempError
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
      return (Except.error actionErr : Except TempError Nat)).run s₀
    NondetTest.assert (res = .error actionErr)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)
    let fsFailClean : FsApiM (StateM S) :=
      { fs with rmtree := fun _ _ => pure (.error { kind := .permissionDenied, message := "cleanup failed" }) }
    let (resFail, _) := ((mkApi fsFailClean time uuid env).withTempDir (some root) dirPrefix fun _ =>
      pure (Except.error actionErr : Except TempError Nat)).run s₀
    NondetTest.assert (resFail = .error actionErr)

/-- When `action` returns `.ok` and `fs.rmtree` fails, `withTempDir` propagates the cleanup error rather than swallowing it. -/
def test_temp_withTempDir_cleanupErrorReturnedOnOk
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_withTempDir_collisionRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
      return (.ok () : Except TempError Unit)).run s₀
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .alreadyExists)
    NondetTest.assert (((fs.lstat markerPath).run s₁).1.isOk = false)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = true)

/-- If `fs.chmod dir 0o700` fails right after `fs.mkdir`, `withTempDir` rolls back `dir` without running `action`. -/
def test_temp_withTempDir_chmodFailureRollsBack
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
      return (.ok () : Except TempError Unit)).run s₀
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .permissionDenied)
    NondetTest.assert (((fs.lstat markerPath).run s₁).1.isOk = false)
    NondetTest.assert (((fs.lstat dir).run s₁).1.isOk = false)

/-- All three operations reject invalid `dirPrefix` (`""`, `"."`, `".."`, leading `'.'`, `'/'`, NUL) and invalid explicit `root?` (`""`, NUL) with `.invalidInput` without modifying state. -/
def test_temp_validation_rejectsInvalidInputs
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  assume (¬ validPrefix dirPrefix ∨ ¬ validRoot root)
  let api := mkApi fs time uuid env
  let (r1, s1) := (api.withTempDir (some root) dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
  let (r2, s2) := (api.withLockedTempDir (some root) dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
  let (r3, s3) := (api.cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀
  NondetTest.assert (∃ e, r1 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (∃ e, r2 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (∃ e, r3 = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "")
  NondetTest.assert (s1 = s₀ ∧ s2 = s₀ ∧ s3 = s₀)

/-- With `root? = none`, all three operations resolve non-empty `TMPDIR`, reject NUL `TMPDIR` with `.invalidInput`, reject missing/non-dir `TMPDIR` strictly, and fall back to `"/tmp"` when `TMPDIR` is unset or empty. -/
def test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
        let (r1, s1) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
        let (r2, s2) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
        let (r3, s3) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
        NondetTest.assert ((∃ e, r1 = .error e ∧ e.kind = .invalidInput) ∧ s1 = sAfterEnv)
        NondetTest.assert ((∃ e, r2 = .error e ∧ e.kind = .invalidInput) ∧ s2 = sAfterEnv)
        NondetTest.assert ((∃ e, r3 = .error e ∧ e.kind = .invalidInput) ∧ s3 = sAfterEnv)
      else
        match ((fs.stat tmpdir).run sAfterUuid).1 with
        | .error fe =>
          let (r1, _) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
          let (r2, _) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
          let (r3, _) := (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀
          NondetTest.assert (∃ te, r1 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
          NondetTest.assert (∃ te, r2 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
          NondetTest.assert (∃ te, r3 = .error te ∧ (fe.kind ≠ .notFound ∨ te.kind = .notFound))
        | .ok st =>
          if st.kind != .dir then
            let (r1, _) := (api.withTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
            let (r2, _) := (api.withLockedTempDir none dirPrefix fun _ => pure (.ok () : Except TempError Unit)).run s₀
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
def test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let dirPrefix ← nondet String
  let val ← nondet Nat
  let err ← nondet TempError
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
      pure (Except.error err : Except TempError Nat)).run s₀
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
def test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_tryFinally_exceptionCleansUpAndReleasesLock
    {S : Type} {runner} [NondetTest runner]
    (mkExApi : TempBuilder (ExceptT String (StateM S)))
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
      (throw "boom" : ExceptT String (StateM S) (Except TempError Unit)))).run s₀
    NondetTest.assert (r1 = .error "boom")
    NondetTest.assert (((fs.lstat dir).run s1).1.isOk = false)
    let (r2, s2) := (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM S) (Except TempError Unit)))).run s₀
    NondetTest.assert (r2 = .error "boom")
    NondetTest.assert (((fs.lstat dir).run s2).1.isOk = false)
    let probeS2 := (do
      let _ ← fs.mkdir dir false false
      fs.tryWithFileLock (fs.join dir ".lock") .exclusive true (pure (.ok ()))).run s2
    NondetTest.assert (probeS2.1 = .ok (some ()))

/-- `cleanupStaleTempDirs` keeps any matching directory whose `<dir>/.lock` is actively locked (`.shared` or `.exclusive`), even when `age > maxAgeSec` (including `maxAgeSec = 0`). -/
def test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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
def test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
    {S : Type} {runner} [NondetTest runner]
    (mkApi : TempBuilder (StateM S))
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

private structure TempStubState where
  dirs : List (String × Int × Nat) := [("/tmp", 0, 0o755)]
  files : List (String × String × Int) := []
  symlinks : List (String × String × Int) := []
  locks : List (String × LockMode) := []
  tmpdir : Option String := none
  nowSec : Int := 1000
  deriving Repr, BEq, DecidableEq

private def stubUuidVal : Uuid :=
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, 0, 1] }

private def stubJoin (a b : String) : String :=
  if a.isEmpty then b
  else if a == "/" then "/" ++ b
  else a ++ "/" ++ b

private def stubParentChild (dir full : String) : Option String :=
  let pref := if dir == "/" then "/" else dir ++ "/"
  if pref.toList.isPrefixOf full.toList then
    let rest := String.ofList (full.toList.drop pref.length)
    if rest.isEmpty || '/' ∈ rest.toList then none else some rest
  else none

private def stubLstatPure (s : TempStubState) (p : String) : Except FsError FileStat :=
  match s.dirs.find? (fun d => d.1 == p) with
  | some (_, mtime, mode) =>
    .ok { kind := .dir, byteSize := 0, mode := mode, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | none =>
    match s.files.find? (fun f => f.1 == p) with
    | some (_, content, mtime) =>
      .ok { kind := .file, byteSize := content.length, mode := 0o644, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
    | none =>
      match s.symlinks.find? (fun l => l.1 == p) with
      | some (_, _, mtime) =>
        .ok { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
      | none => .error { kind := .notFound, path := some p, message := "not found" }

private def stubStatPure (s : TempStubState) (p : String) : Except FsError FileStat :=
  match s.symlinks.find? (fun l => l.1 == p) with
  | some (_, tgt, _) => stubLstatPure s tgt
  | none => stubLstatPure s p

private def stubRemovePrefix (p : String) (xs : List String) : Bool :=
  let pref := if p == "/" then "/" else p ++ "/"
  xs.any fun k => k == p || pref.toList.isPrefixOf k.toList

private def stubRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempStubState (Except FsError Unit) := do
  let s ← get
  match stubLstatPure s p with
  | .error e =>
    if ignoreMissing && e.kind == .notFound then return .ok ()
    else return .error e
  | .ok st =>
    if st.kind != .dir then return .error { kind := .notADirectory, path := some p, message := "not a dir" }
    let pref := if p == "/" then "/" else p ++ "/"
    let keep (k : String) : Bool := !(k == p || pref.toList.isPrefixOf k.toList)
    set { s with
      dirs := s.dirs.filter (fun d => keep d.1)
      files := s.files.filter (fun f => keep f.1)
      symlinks := s.symlinks.filter (fun l => keep l.1) }
    return .ok ()

private def stubHasConflict (locks : List (String × LockMode)) (p : String) (m : LockMode) : Bool :=
  locks.any fun (lp, lm) => lp == p && (m == .exclusive || lm == .exclusive)

private def stubRemoveFirstLock (p : String) (m : LockMode) : List (String × LockMode) → List (String × LockMode)
  | [] => []
  | x :: xs => if x == (p, m) then xs else x :: stubRemoveFirstLock p m xs

private def stubFs : FsApiM (StateM TempStubState) :=
  { join := stubJoin
    joinMany := fun parts => parts.foldl stubJoin ""
    normPath := fun p => p
    parent := fun _ => none
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun p _ => .ok p
    withSuffix := fun p _ => .ok p
    isAbsolute := fun p => p.startsWith "/"
    relativeTo := fun p _ => .ok p
    mapRawError := fun _ => { kind := .ioError, message := "raw" }
    readText := fun p => do
      let s ← get
      match s.files.find? (fun f => f.1 == p) with
      | some (_, c, _) => return .ok c
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
    writeText := fun p c => do
      let s ← get
      set { s with files := (p, c, s.nowSec) :: s.files.filter (fun f => f.1 != p) }
      return .ok ()
    appendText := fun p c => do
      let s ← get
      set { s with files := (p, c, s.nowSec) :: s.files.filter (fun f => f.1 != p) }
      return .ok ()
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun p _ => do
      let s ← get
      set { s with files := (p, "", s.nowSec) :: s.files.filter (fun f => f.1 != p) }
      return .ok ()
    mkdir := fun p _ existOk => do
      let s ← get
      match stubLstatPure s p with
      | .ok st =>
        if existOk && st.kind == .dir then return .ok ()
        else return .error { kind := .alreadyExists, path := some p, message := "exists" }
      | .error _ =>
        set { s with dirs := (p, s.nowSec, 0o755) :: s.dirs }
        return .ok ()
    unlink := fun p miss => do
      let s ← get
      match stubLstatPure s p with
      | .error e => if miss && e.kind == .notFound then return .ok () else return .error e
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is a dir" }
        set { s with
          files := s.files.filter (fun f => f.1 != p)
          symlinks := s.symlinks.filter (fun l => l.1 != p) }
        return .ok ()
    rmdir := fun p => do
      let s ← get
      match stubLstatPure s p with
      | .error e => return .error e
      | .ok st =>
        if st.kind != .dir then return .error { kind := .notADirectory, path := some p, message := "not a dir" }
        set { s with dirs := s.dirs.filter (fun d => d.1 != p) }
        return .ok ()
    rmtree := stubRmtreePure
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun p => do return .ok ((stubStatPure (← get) p).isOk)
    isFile := fun p => do
      match stubStatPure (← get) p with
      | .ok st => return .ok (st.kind == .file)
      | .error _ => return .ok false
    isDir := fun p => do
      match stubStatPure (← get) p with
      | .ok st => return .ok (st.kind == .dir)
      | .error _ => return .ok false
    isSymlink := fun p => do
      match stubLstatPure (← get) p with
      | .ok st => return .ok (st.kind == .symlink)
      | .error _ => return .ok false
    stat := fun p => do return stubStatPure (← get) p
    lstat := fun p => do return stubLstatPure (← get) p
    chmod := fun p m => do
      let s ← get
      if s.dirs.any (fun d => d.1 == p) then
        set { s with dirs := s.dirs.map (fun (k, t, old) => if k == p then (k, t, m) else (k, t, old)) }
        return .ok ()
      else
        return .error { kind := .notFound, path := some p, message := "not found" }
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "no link" })
    resolve := fun p => pure (.ok p)
    cwd := pure (.ok "/")
    listDir := fun p => do
      let s ← get
      let ds := s.dirs.filterMap (fun d => stubParentChild p d.1)
      let fs := s.files.filterMap (fun f => stubParentChild p f.1)
      let ls := s.symlinks.filterMap (fun l => stubParentChild p l.1)
      let all := ds ++ fs ++ ls
      return .ok (match all with | [] => #[] | [x] => #[x] | _ => (all.mergeSort (· ≤ ·)).toArray)
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun p mode createIfMissing action => do
      let s ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
        set { s with locks := (p, mode) :: s.locks }
        let r ← action
        modify fun s' => { s' with locks := stubRemoveFirstLock p mode s'.locks }
        return r
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          set { s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks }
          let r ← action
          modify fun s' => { s' with locks := stubRemoveFirstLock p mode s'.locks }
          return r
        else
          return .error e
    tryWithFileLock := fun p mode createIfMissing action => do
      let s ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .ok none
        set { s with locks := (p, mode) :: s.locks }
        let r ← action
        modify fun s' => { s' with locks := stubRemoveFirstLock p mode s'.locks }
        return r.map some
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .ok none
          set { s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks }
          let r ← action
          modify fun s' => { s' with locks := stubRemoveFirstLock p mode s'.locks }
          return r.map some
        else
          return .error e }

private def stubTime : TimeOpsM (StateM TempStubState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec)
    monoNanosNow := pure 0
    sleep := fun _ => pure () }

private def stubUuid : UuidApiM (StateM TempStubState) :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "entropy" }
    fromRandomBytes := fun _ => .ok stubUuidVal
    toString := fun _ => "00000000-0000-4000-8000-000000000001"
    toHex := fun _ => "00000000000040008000000000000001"
    parse := fun _ => .ok stubUuidVal
    parseHex := fun _ => .ok stubUuidVal
    isValid := fun _ => true
    getUuid := pure (.ok stubUuidVal) }

private def stubEnv : EnvVarsApiM (StateM TempStubState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }
    getEnv := fun k => do
      if k == "TMPDIR" then return .ok (← get).tmpdir
      else return .ok none
    listEnv := pure (.ok #[])
    homeDir := pure (.ok "/home/user")
    splitSearchPath := fun _ => #[] }

private def stubFsEx : FsApiM (ExceptT String (StateM TempStubState)) :=
  { join := stubFs.join
    joinMany := stubFs.joinMany
    normPath := stubFs.normPath
    parent := stubFs.parent
    name := stubFs.name
    stem := stubFs.stem
    suffix := stubFs.suffix
    suffixes := stubFs.suffixes
    withName := stubFs.withName
    withSuffix := stubFs.withSuffix
    isAbsolute := stubFs.isAbsolute
    relativeTo := stubFs.relativeTo
    mapRawError := stubFs.mapRawError
    readText := fun p => liftM (stubFs.readText p)
    writeText := fun p c => liftM (stubFs.writeText p c)
    appendText := fun p c => liftM (stubFs.appendText p c)
    readBytes := fun p => liftM (stubFs.readBytes p)
    writeBytes := fun p bs => liftM (stubFs.writeBytes p bs)
    atomicWriteText := fun p c => liftM (stubFs.atomicWriteText p c)
    touch := fun p ex => liftM (stubFs.touch p ex)
    mkdir := fun p par ex => liftM (stubFs.mkdir p par ex)
    unlink := fun p m => liftM (stubFs.unlink p m)
    rmdir := fun p => liftM (stubFs.rmdir p)
    rmtree := fun p ign => liftM (stubFs.rmtree p ign)
    rename := fun a b => liftM (stubFs.rename a b)
    copyFile := fun a b => liftM (stubFs.copyFile a b)
    copyTree := fun a b c => liftM (stubFs.copyTree a b c)
    pathExists := fun p => liftM (stubFs.pathExists p)
    isFile := fun p => liftM (stubFs.isFile p)
    isDir := fun p => liftM (stubFs.isDir p)
    isSymlink := fun p => liftM (stubFs.isSymlink p)
    stat := fun p => liftM (stubFs.stat p)
    lstat := fun p => liftM (stubFs.lstat p)
    chmod := fun p m => liftM (stubFs.chmod p m)
    symlink := fun a b => liftM (stubFs.symlink a b)
    readLink := fun p => liftM (stubFs.readLink p)
    resolve := fun p => liftM (stubFs.resolve p)
    cwd := liftM stubFs.cwd
    listDir := fun p => liftM (stubFs.listDir p)
    walk := fun p => liftM (stubFs.walk p)
    glob := fun a b => liftM (stubFs.glob a b)
    rglob := fun a b => liftM (stubFs.rglob a b)
    withFileLock := fun p mode createIfMissing action => do
      let s : TempStubState ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
        liftM (set ({ s with locks := (p, mode) :: s.locks } : TempStubState) : StateM TempStubState Unit)
        let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempStubState Unit))
        return r
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          liftM (set ({ s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks } : TempStubState) : StateM TempStubState Unit)
          let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempStubState Unit))
          return r
        else
          return .error e
    tryWithFileLock := fun p mode createIfMissing action => do
      let s : TempStubState ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .ok none
        liftM (set ({ s with locks := (p, mode) :: s.locks } : TempStubState) : StateM TempStubState Unit)
        let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempStubState Unit))
        return r.map some
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .ok none
          liftM (set ({ s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks } : TempStubState) : StateM TempStubState Unit)
          let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempStubState Unit))
          return r.map some
        else
          return .error e }

private def stubTimeEx : TimeOpsM (ExceptT String (StateM TempStubState)) :=
  { nowTimestamp := liftM stubTime.nowTimestamp
    monoNanosNow := liftM stubTime.monoNanosNow
    sleep := fun ms => liftM (stubTime.sleep ms) }

private def stubUuidEx : UuidApiM (ExceptT String (StateM TempStubState)) :=
  { mapRawError := stubUuid.mapRawError
    fromRandomBytes := stubUuid.fromRandomBytes
    toString := stubUuid.toString
    toHex := stubUuid.toHex
    parse := stubUuid.parse
    parseHex := stubUuid.parseHex
    isValid := stubUuid.isValid
    getUuid := liftM stubUuid.getUuid }

private def stubEnvEx : EnvVarsApiM (ExceptT String (StateM TempStubState)) :=
  { mapRawError := stubEnv.mapRawError
    getEnv := fun k => liftM (stubEnv.getEnv k)
    listEnv := liftM stubEnv.listEnv
    homeDir := liftM stubEnv.homeDir
    splitSearchPath := stubEnv.splitSearchPath }

private def noopTempBuilder {m : Type → Type} [Monad m] : TempBuilder m :=
  fun _ _ _ _ =>
    { withTempDir := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      withLockedTempDir := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      cleanupStaleTempDirs := fun _ _ _ => pure (.ok {}) }

private def buggyWithTempDirNoCleanup : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let _ ← fs.chmod dir 0o700
            action dir }

private def buggyWithTempDirSwallowsCleanupErr : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let r ← action dir
            let _ ← fs.rmtree dir true
            return r }

private def buggyWithTempDirExistOk : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false true with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let r ← action dir
            let _ ← fs.rmtree dir true
            return r }

private def buggyWithTempDirNoChmodRollback : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            match ← fs.chmod dir 0o700 with
            | .error _ => return .error { kind := .permissionDenied, message := "chmod" }
            | .ok () =>
              let r ← action dir
              let _ ← fs.rmtree dir true
              return r }

private def buggyWithTempDirIgnoresTmpdir : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let _ ← fs.chmod dir 0o700
            let r ← action dir
            let _ ← fs.rmtree dir true
            return r }

private def buggyWithLockedTempDirPropagatesNotFound : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withLockedTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let lockPath := fs.join dir ".lock"
            let lr ← fs.withFileLock lockPath .shared true (do return .ok (← action dir))
            match ← fs.rmtree dir true with
            | .error re => return .error { kind := .notFound, path := re.path, message := "rm failed" }
            | .ok () =>
              match lr with
              | .error _ => return .error { kind := .ioError, message := "lock" }
              | .ok r => return r }

private def buggyExNoTryFinally : TempBuilder (ExceptT String (StateM TempStubState)) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTimeEx uuid stubEnvEx) with
      withTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let r ← action dir
            let _ ← fs.rmtree dir true
            return r }

private def buggyCleanupDeletesLocked : TempBuilder (StateM TempStubState) :=
  fun fs _ _ _ =>
    { (noopTempBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        match ← fs.listDir root with
        | .error _ => return .error { kind := .ioError, message := "listdir" }
        | .ok names =>
          let mut removed := #[]
          for n in names do
            let child := fs.join root n
            let _ ← fs.rmtree child true
            removed := removed.push child
          return .ok { removed } }

private def buggyCleanupKeepsDeadLock : TempBuilder (StateM TempStubState) :=
  fun _ _ _ _ =>
    { (noopTempBuilder stubFs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        return .ok { keptFresh := #[stubJoin root "tmp-dead"] } }

private def buggyCleanupDeletesYoungUnlocked : TempBuilder (StateM TempStubState) :=
  fun fs _ _ _ =>
    { (noopTempBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-young"
        let _ ← fs.rmtree child true
        return .ok { removed := #[child] } }

private def buggyCleanupDeletesNonMatching : TempBuilder (StateM TempStubState) :=
  fun fs _ _ _ =>
    { (noopTempBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "other-dir"
        let _ ← fs.rmtree child true
        return .ok { removed := #[child] } }

private def buggyCleanupDeletesLockFirst : TempBuilder (StateM TempStubState) :=
  fun fs _ _ _ =>
    { (noopTempBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-dead"
        let _ ← fs.rmtree child true
        return .ok { failed := #[{ kind := .permissionDenied, path := some child, message := "partial" }] } }

private def buggyWithLockedTempDirNoChmod : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withLockedTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let lockPath := fs.join dir ".lock"
            let lr ← fs.withFileLock lockPath .shared true (do return .ok (← action dir))
            let _ ← fs.rmtree dir true
            match lr with
            | .error _ => return .error { kind := .ioError, message := "lock" }
            | .ok r => return r }

private def buggyWithLockedTempDirSwallowsLockErr : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid _ =>
    { (noopTempBuilder fs stubTime uuid stubEnv) with
      withLockedTempDir := fun root? dirPrefix action => do
        let root := root?.getD "/tmp"
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join root (dirPrefix ++ uuid.toString u)
          match ← fs.mkdir dir false false with
          | .error _ => return .error { kind := .alreadyExists, message := "exists" }
          | .ok () =>
            let _ ← fs.chmod dir 0o700
            let lockPath := fs.join dir ".lock"
            let lr ← fs.withFileLock lockPath .shared true (do return .ok (← action dir))
            match ← fs.rmtree dir true with
            | .error _ => return .error { kind := .ioError, message := "rm wins over lock err" }
            | .ok () =>
              match lr with
              | .error _ => return .error { kind := .permissionDenied, message := "lock" }
              | .ok r => return r }

private def buggyLockedTempDirIgnoresTmpdir : TempBuilder (StateM TempStubState) :=
  fun fs _ uuid env =>
    { (noopTempBuilder fs stubTime uuid env) with
      withTempDir := fun _ dirPrefix action => do
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          match ← env.getEnv "TMPDIR" with
          | .ok (some t) =>
            let root := if t.isEmpty then "/tmp" else t
            let dir := fs.join root (dirPrefix ++ uuid.toString u)
            let _ ← fs.mkdir dir false false
            let _ ← fs.chmod dir 0o700
            let r ← action dir
            let _ ← fs.rmtree dir true
            return r
          | _ => return .error { kind := .ioError, message := "env" }
      withLockedTempDir := fun _ dirPrefix action => do
        match ← uuid.getUuid with
        | .error _ => return .error { kind := .ioError, message := "uuid" }
        | .ok u =>
          let dir := fs.join "/tmp" (dirPrefix ++ uuid.toString u)
          let _ ← fs.mkdir dir false false
          let _ ← fs.chmod dir 0o700
          let lockPath := fs.join dir ".lock"
          let lr ← fs.withFileLock lockPath .shared true (do return .ok (← action dir))
          let _ ← fs.rmtree dir true
          match lr with
          | .error _ => return .error { kind := .ioError, message := "lock" }
          | .ok r => return r }

private def buggyCleanupLeaksLockOnPartialFail : TempBuilder (StateM TempStubState) :=
  fun fs _ _ _ =>
    { (noopTempBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-dead"
        let lockPath := fs.join child ".lock"
        modify fun s => { s with locks := (lockPath, .exclusive) :: s.locks }
        return .ok { failed := #[{ kind := .permissionDenied, path := some child, message := "leaked lock" }] } }

example : ¬ Core.AllPass (test_temp_withTempDir_okCleansUpAndSetsMode buggyWithTempDirNoCleanup stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 7 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_temp_withTempDir_okCleansUpAndSetsMode, Core.NondetTest.assert, Bind.bind, stubFs, stubTime, stubUuid, stubEnv, buggyWithTempDirNoCleanup] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_temp_withTempDir_errorCleansUpAndPreservesError noopTempBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" { kind := .invalidInput, message := "err" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_temp_withTempDir_errorCleansUpAndPreservesError, Core.NondetTest.assert, Bind.bind, noopTempBuilder] at h0
  cases h0.1

example : ¬ Core.AllPass (test_temp_withTempDir_cleanupErrorReturnedOnOk buggyWithTempDirSwallowsCleanupErr stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 1 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_temp_withTempDir_cleanupErrorReturnedOnOk, Core.NondetTest.assert, Bind.bind, buggyWithTempDirSwallowsCleanupErr] at h0
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_temp_withTempDir_collisionRejected buggyWithTempDirExistOk stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState := { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-00000000-0000-4000-8000-000000000001", 0, 0o755)] }
  have h0 := h s "/tmp" "tmp-" "/marker" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, Or.inl rfl⟩
  dsimp [test_temp_withTempDir_collisionRejected, Core.NondetTest.assert, Bind.bind, buggyWithTempDirExistOk] at h0
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_temp_withTempDir_chmodFailureRollsBack buggyWithTempDirNoChmodRollback stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" "/marker" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide) (by decide)
  dsimp [test_temp_withTempDir_chmodFailureRollsBack, Core.NondetTest.assert, Bind.bind, buggyWithTempDirNoChmodRollback] at h0
  exact absurd h0.2.2 (by decide)

example : ¬ Core.AllPass (test_temp_validation_rejectsInvalidInputs noopTempBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" ".bad" (Or.inl (by decide))
  dsimp [test_temp_validation_rejectsInvalidInputs, Core.NondetTest.assert, Bind.bind, noopTempBuilder] at h0
  rcases h0.1 with ⟨e, he, hk, _⟩
  cases he
  cases hk

example : ¬ Core.AllPass (test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing buggyWithTempDirIgnoresTmpdir stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState := { dirs := [("/tmp", 0, 0o755), ("/custom", 0, 0o755)], tmpdir := some "/custom" }
  have h0 := h s "tmp-" (by decide) ⟨rfl, rfl, rfl, rfl⟩ (by decide)
  have hEq : (Except.ok "/tmp/tmp-00000000-0000-4000-8000-000000000001" : Except TempError String) = Except.ok "/custom/tmp-00000000-0000-4000-8000-000000000001" := h0.1
  simp at hEq

example : ¬ Core.AllPass (test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing buggyLockedTempDirIgnoresTmpdir stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState := { dirs := [("/tmp", 0, 0o755), ("/custom", 0, 0o755)], tmpdir := some "/custom" }
  have h0 := h s "tmp-" (by decide) ⟨rfl, rfl, rfl, rfl⟩ (by decide)
  have hEq : (Except.ok "/tmp/tmp-00000000-0000-4000-8000-000000000001" : Except TempError String) = Except.ok "/custom/tmp-00000000-0000-4000-8000-000000000001" := h0.2.1
  simp at hEq

example : ¬ Core.AllPass (test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit noopTempBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, Core.NondetTest.assert, Bind.bind, noopTempBuilder] at h0
  cases h0.1

example : ¬ Core.AllPass (test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit buggyWithLockedTempDirNoChmod stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  have hEq : Except.error { kind := TempErrorKind.ioError, path := some "/tmp/tmp-00000000-0000-4000-8000-000000000001", message := "dir mode or lock invariant failed" } = (Except.ok 5 : Except TempError Nat) := h0.1
  cases hEq

example : ¬ Core.AllPass (test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit buggyWithLockedTempDirSwallowsLockErr stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  rcases h0.2.2.2.2.2.2.2.1 with ⟨e, he, hk⟩
  have hErr : Except.error { kind := TempErrorKind.ioError, message := "rm wins over lock err" } = (Except.error e : Except TempError Nat) := he
  cases hErr
  cases hk

example : ¬ Core.AllPass (test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup buggyWithLockedTempDirPropagatesNotFound stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 9 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  have hEq : Except.error { kind := TempErrorKind.notFound, path := some "/tmp/tmp-00000000-0000-4000-8000-000000000001", message := "rm failed" } = (Except.ok 9 : Except TempError Nat) := h0.1
  cases hEq

example : ¬ Core.AllPass (test_temp_tryFinally_exceptionCleansUpAndReleasesLock buggyExNoTryFinally stubFsEx stubTimeEx stubUuidEx stubEnvEx stubFs stubUuid) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_temp_tryFinally_exceptionCleansUpAndReleasesLock, Core.NondetTest.assert, Bind.bind, buggyExNoTryFinally, stubFsEx, stubTimeEx, stubUuidEx, stubEnvEx, stubFs, stubUuid] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge buggyCleanupDeletesLocked stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-live", 0, 0o700)]
      files := [("/tmp/tmp-live/.lock", "", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-live" 10 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ ⟨{ kind := .file, byteSize := 0, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ (by decide)
  dsimp [test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesLocked, stubFs, stubTime, stubUuid, stubEnv] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately buggyCleanupKeepsDeadLock stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 1000, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 1000)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 1000, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 0, mode := 0o644, modifiedSec := 1000, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ (congrArg Except.ok (by decide)) rfl (by decide)
  dsimp [test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately, Core.NondetTest.assert, Bind.bind, buggyCleanupKeepsDeadLock] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked buggyCleanupDeletesYoungUnlocked stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-young", 950, 0o700)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-young" 100 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 950, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .notFound, path := some "/tmp/tmp-young/.lock", message := "not found" }, rfl, rfl⟩
  have hBad : (false = true ∧ ¬ true = true) ∧ false = true ∧ True := h0
  exact absurd hBad (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety buggyCleanupDeletesNonMatching stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/other-dir", 0, 0o755)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "other-dir" 10 (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, Or.inl (by decide)⟩
  dsimp [test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesNonMatching] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety buggyCleanupDeletesLockFirst stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 0, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 0), ("/tmp/tmp-dead/locked_child.txt", "x", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 1, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ rfl
  dsimp [test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesLockFirst] at h0
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety buggyCleanupLeaksLockOnPartialFail stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 0, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 0), ("/tmp/tmp-dead/locked_child.txt", "x", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 1, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ rfl
  have hBad : (Except.ok (none : Option Unit) : Except FsError (Option Unit)) = Except.ok (some ()) := h0.2.2.2.1
  cases hBad

end LeanSwe.Temp

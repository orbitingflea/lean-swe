import LeanSwe.EnvVars.Types
import LeanSwe.Fs.Types
import LeanSwe.TempDir.Types
import LeanSwe.Time.Types
import LeanSwe.Uuid.Types

namespace LeanSwe.TempDir.Internal

open LeanSwe.Fs (FsApiM FsError EntryKind)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)

/-- Check whether `dirPrefix` is non-empty, does not start with `'.'`, and contains no `'/'` or NUL byte. -/
def validPrefix (dirPrefix : String) : Bool :=
  !dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' &&
    !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)

/-- Check whether `root` is non-empty and contains no NUL byte. -/
def validRoot (root : String) : Bool :=
  !root.isEmpty && !(Char.ofNat 0 ∈ root.toList)

/-- Insert a path string into a sorted list using lexicographical `String` order. -/
def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Sort a list of path strings into ascending lexicographical order. -/
def sortStrings : List String → List String
  | [] => []
  | x :: xs => insertSorted x (sortStrings xs)

/-- Map an `FsError` into a `TempDirError` with non-empty diagnostic message. -/
def mapFsError (err : FsError) : TempDirError :=
  let kind :=
    match err.kind with
    | .invalidInput => TempDirErrorKind.invalidInput
    | .notFound => TempDirErrorKind.notFound
    | .alreadyExists => TempDirErrorKind.alreadyExists
    | .permissionDenied => TempDirErrorKind.permissionDenied
    | .notADirectory => TempDirErrorKind.notADirectory
    | _ => TempDirErrorKind.ioError
  { kind := kind
    path := err.path
    message := if err.message.isEmpty then "filesystem error" else err.message }

/-- Map a `UuidError` into a `TempDirError` with non-empty diagnostic message. -/
def mapUuidError (err : UuidError) : TempDirError :=
  { kind := .ioError
    path := none
    message := if err.message.isEmpty then "uuid generation failed" else err.message }

/-- Map an `EnvError` into a `TempDirError` with non-empty diagnostic message. -/
def mapEnvError (err : EnvVarsError) : TempDirError :=
  { kind := .ioError
    path := none
    message := if err.message.isEmpty then "environment lookup failed" else err.message }

/-- Resolve and validate the base temporary directory from `root?` or `TMPDIR` (falling back to `"/tmp"`). -/
def resolveRoot {m : Type → Type} [Monad m]
    (fs : FsApiM m) (env : EnvVarsApiM m) (root? : Option String) :
    m (Except TempDirError String) := do
  let rawRoot? ←
    match root? with
    | some r => pure (Except.ok r)
    | none =>
      match ← env.getEnv "TMPDIR" with
      | .error e => pure (Except.error (mapEnvError e))
      | .ok (some v) => pure (Except.ok (if v.isEmpty then "/tmp" else v))
      | .ok none => pure (Except.ok "/tmp")
  match rawRoot? with
  | .error te => return .error te
  | .ok root =>
    if !validRoot root then
      return .error { kind := .invalidInput, path := some root, message := "invalid temporary root path" }
    match ← fs.stat root with
    | .error fe => return .error (mapFsError fe)
    | .ok st =>
      if st.kind != .dir then
        return .error { kind := .notADirectory, path := some root, message := "temporary root is not a directory" }
      return .ok root

/-- Remove `dir` recursively, treating `.notFound` as already removed. -/
def cleanupDirIgnoringNotFound {m : Type → Type} [Monad m]
    (fs : FsApiM m) (dir : String) : m (Except TempDirError Unit) := do
  match ← fs.rmtree dir true with
  | .ok () => return .ok ()
  | .error fe =>
    if fe.kind == .notFound then return .ok ()
    else return .error (mapFsError fe)

/-- Create an exclusive `0o700` temporary subdirectory `<root>/<dirPrefix><uuid>`. -/
def createTempDir {m : Type → Type} [Monad m]
    (fs : FsApiM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) :
    m (Except TempDirError String) := do
  if !validPrefix dirPrefix then
    return .error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }
  match ← resolveRoot fs env root? with
  | .error te => return .error te
  | .ok root =>
    match ← uuid.getUuid with
    | .error ue => return .error (mapUuidError ue)
    | .ok u =>
      let dir := fs.join root (dirPrefix ++ uuid.toString u)
      match ← fs.mkdir dir false false with
      | .error fe => return .error (mapFsError fe)
      | .ok () =>
        match ← fs.chmod dir 0o700 with
        | .ok () => return .ok dir
        | .error fe =>
          let _ ← cleanupDirIgnoringNotFound fs dir
          return .error (mapFsError fe)

/-- Combine `action` and finalizer cleanup results, giving `action`'s error precedence. -/
def combineCleanup {α : Type} (actionRes : Except TempDirError α)
    (cleanRes : Except TempDirError Unit) : Except TempDirError α :=
  match actionRes, cleanRes with
  | .error te, _ => .error te
  | .ok a, .ok () => .ok a
  | .ok _, .error ce => .error ce

/-- Generic `withTempDir` implementation over injected capability interfaces. -/
def withTempDirM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String)
    (action : String → m (Except TempDirError α)) :
    m (Except TempDirError α) := do
  match ← createTempDir fs uuid env root? dirPrefix with
  | .error te => return .error te
  | .ok dir =>
    let (actionRes, cleanRes) ← tryFinally' (action dir) (fun _ => cleanupDirIgnoringNotFound fs dir)
    return combineCleanup actionRes cleanRes

/-- Generic `withLockedTempDir` implementation holding a `.shared` lock on `<dir>/.lock`. -/
def withLockedTempDirM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String)
    (action : String → m (Except TempDirError α)) :
    m (Except TempDirError α) :=
  withTempDirM fs uuid env root? dirPrefix fun dir => do
    match ← fs.withFileLock (fs.join dir ".lock") .shared true (do return .ok (← action dir)) with
    | .error fe => return .error (mapFsError fe)
    | .ok r => return r

/-- Delete all non-`.lock` entries inside `child`, failing fast before removing `.lock`. -/
def removeNonLockChildren {m : Type → Type} [Monad m]
    (fs : FsApiM m) (child : String) : List String → m (Except TempDirError Unit)
  | [] => return .ok ()
  | name :: rest => do
    if name == ".lock" then
      removeNonLockChildren fs child rest
    else
      let entry := fs.join child name
      match ← fs.lstat entry with
      | .error fe =>
        if fe.kind == .notFound then removeNonLockChildren fs child rest
        else return .error (mapFsError fe)
      | .ok st =>
        let delRes ←
          if st.kind == .dir then cleanupDirIgnoringNotFound fs entry
          else
            match ← fs.unlink entry true with
            | .ok () => pure (.ok ())
            | .error fe => pure (.error (mapFsError fe))
        match delRes with
        | .error te => return .error te
        | .ok () => removeNonLockChildren fs child rest

/-- Remove a locked temp directory under an active `.exclusive` lock, deleting `.lock` last. -/
def removeLockedTempDir {m : Type → Type} [Monad m]
    (fs : FsApiM m) (child lockPath : String) : m (Except FsError (Except TempDirError Unit)) := do
  match ← fs.listDir child with
  | .error fe =>
    if fe.kind == .notFound then return .ok (.ok ())
    else return .ok (.error (mapFsError fe))
  | .ok names =>
    match ← removeNonLockChildren fs child names.toList with
    | .error te => return .ok (.error te)
    | .ok () =>
      match ← fs.unlink lockPath true with
      | .error fe => return .ok (.error (mapFsError fe))
      | .ok () =>
        match ← fs.rmdir child with
        | .ok () => return .ok (.ok ())
        | .error fe =>
          if fe.kind == .notFound then return .ok (.ok ())
          else return .ok (.error (mapFsError fe))

/-- Process one immediate entry under `root` during a stale-temp sweep. -/
def sweepEntry {m : Type → Type} [Monad m]
    (fs : FsApiM m) (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) (entryName : String) : m CleanupReport := do
  let child := fs.join root entryName
  if !dirPrefix.toList.isPrefixOf entryName.toList then
    return { rep with skipped := rep.skipped.push child }
  match ← fs.lstat child with
  | .error fe =>
    if fe.kind == .notFound then return rep
    else return { rep with failed := rep.failed.push (mapFsError fe) }
  | .ok stChild =>
    if stChild.kind != .dir then
      return { rep with skipped := rep.skipped.push child }
    let lockPath := fs.join child ".lock"
    match ← fs.lstat lockPath with
    | .ok stLock =>
      if stLock.kind != .file then
        return { rep with
          failed := rep.failed.push
            { kind := .invalidInput, path := some lockPath, message := "lock entry is not a regular file" } }
      match ← fs.tryWithFileLock lockPath .exclusive false (removeLockedTempDir fs child lockPath) with
      | .ok none => return { rep with keptLocked := rep.keptLocked.push child }
      | .ok (some (.ok ())) => return { rep with removed := rep.removed.push child }
      | .ok (some (.error te)) => return { rep with failed := rep.failed.push te }
      | .error fe =>
        if fe.kind == .notFound then return rep
        else return { rep with failed := rep.failed.push (mapFsError fe) }
    | .error fe =>
      if fe.kind != .notFound then
        return { rep with failed := rep.failed.push (mapFsError fe) }
      let ageSec : Int := nowSec - stChild.modifiedSec
      if ageSec ≤ (maxAgeSec : Int) then
        return { rep with keptFresh := rep.keptFresh.push child }
      match ← cleanupDirIgnoringNotFound fs child with
      | .ok () => return { rep with removed := rep.removed.push child }
      | .error te => return { rep with failed := rep.failed.push te }

/-- Fold `sweepEntry` across a list of child entry names. -/
def sweepEntries {m : Type → Type} [Monad m]
    (fs : FsApiM m) (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) : List String → m CleanupReport
  | [] => return rep
  | name :: rest => do
    let rep' ← sweepEntry fs root dirPrefix maxAgeSec nowSec rep name
    sweepEntries fs root dirPrefix maxAgeSec nowSec rep' rest

/-- Generic `cleanupStaleTempDirs` implementation over injected capability interfaces. -/
def cleanupStaleTempDirsM {m : Type → Type} [Monad m]
    (fs : FsApiM m) (time : TimeOpsM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat) :
    m (Except TempDirError CleanupReport) := do
  if !validPrefix dirPrefix then
    return .error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }
  match ← resolveRoot fs env root? with
  | .error te => return .error te
  | .ok root =>
    let nowTs ← time.nowTimestamp
    let nowSec := nowTs.toSecondsSinceUnixEpoch.val
    match ← fs.listDir root with
    | .error fe => return .error (mapFsError fe)
    | .ok names =>
      let rep ← sweepEntries fs root dirPrefix maxAgeSec nowSec {} names.toList
      return .ok
        { removed := (sortStrings rep.removed.toList).toArray
          keptLocked := (sortStrings rep.keptLocked.toList).toArray
          keptFresh := (sortStrings rep.keptFresh.toList).toArray
          skipped := (sortStrings rep.skipped.toList).toArray
          failed := rep.failed }

/-- Assemble a `TempDirApiM m` from injected `Fs`, `Time`, `Uuid`, and `Env` interfaces. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m) :
    TempDirApiM m :=
  { withTempDir := fun root? dirPrefix action => withTempDirM fs uuid env root? dirPrefix action
    withLockedTempDir := fun root? dirPrefix action => withLockedTempDirM fs uuid env root? dirPrefix action
    cleanupStaleTempDirs := fun root? dirPrefix maxAgeSec =>
      cleanupStaleTempDirsM fs time env root? dirPrefix maxAgeSec }

end LeanSwe.TempDir.Internal

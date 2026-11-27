import Core.NondetTest
import LeanSwe.EnvVars.Types
import LeanSwe.Fs.Types
import LeanSwe.TempDir.Types
import LeanSwe.Time.Types
import LeanSwe.Uuid.Types
import LeanSwe.TempDir.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.TempDir`. -/

namespace LeanSwe.TempDir

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)

private structure TempDirStubState where
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

private def stubLstatPure (s : TempDirStubState) (p : String) : Except FsError FileStat :=
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

private def stubStatPure (s : TempDirStubState) (p : String) : Except FsError FileStat :=
  match s.symlinks.find? (fun l => l.1 == p) with
  | some (_, tgt, _) => stubLstatPure s tgt
  | none => stubLstatPure s p

private def stubRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempDirStubState (Except FsError Unit) := do
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

private def stubFs : FsApiM (StateM TempDirStubState) :=
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
    atomicWriteBytes := fun _ _ => pure (.ok ())
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

private def stubTime : TimeOpsM (StateM TempDirStubState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec)
    monoNanosNow := pure 0
    sleep := fun _ => pure () }

private def stubUuid : UuidApiM (StateM TempDirStubState) :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "entropy" }
    fromRandomBytes := fun _ => .ok stubUuidVal
    toString := fun _ => "00000000-0000-4000-8000-000000000001"
    toHex := fun _ => "00000000000040008000000000000001"
    parse := fun _ => .ok stubUuidVal
    parseHex := fun _ => .ok stubUuidVal
    isValid := fun _ => true
    getUuid := pure (.ok stubUuidVal) }

private def stubEnv : EnvVarsApiM (StateM TempDirStubState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }
    getEnv := fun k => do
      if k == "TMPDIR" then return .ok (← get).tmpdir
      else return .ok none
    listEnv := pure (.ok #[])
    homeDir := pure (.ok "/var/user")
    splitSearchPath := fun _ => #[] }

private def stubFsEx : FsApiM (ExceptT String (StateM TempDirStubState)) :=
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
    atomicWriteBytes := fun p bs => liftM (stubFs.atomicWriteBytes p bs)
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
      let s : TempDirStubState ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
        liftM (set ({ s with locks := (p, mode) :: s.locks } : TempDirStubState) : StateM TempDirStubState Unit)
        let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempDirStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempDirStubState Unit))
        return r
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          liftM (set ({ s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks } : TempDirStubState) : StateM TempDirStubState Unit)
          let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempDirStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempDirStubState Unit))
          return r
        else
          return .error e
    tryWithFileLock := fun p mode createIfMissing action => do
      let s : TempDirStubState ← get
      match stubLstatPure s p with
      | .ok st =>
        if st.kind == .dir then return .error { kind := .isADirectory, path := some p, message := "is dir" }
        if st.kind == .symlink then return .error { kind := .invalidInput, path := some p, message := "symlink" }
        if stubHasConflict s.locks p mode then return .ok none
        liftM (set ({ s with locks := (p, mode) :: s.locks } : TempDirStubState) : StateM TempDirStubState Unit)
        let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempDirStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempDirStubState Unit))
        return r.map some
      | .error e =>
        if e.kind == .notFound && createIfMissing then
          if stubHasConflict s.locks p mode then return .ok none
          liftM (set ({ s with files := (p, "", s.nowSec) :: s.files, locks := (p, mode) :: s.locks } : TempDirStubState) : StateM TempDirStubState Unit)
          let (r, _) ← tryFinally' action (fun _ => liftM (modify (fun (s' : TempDirStubState) => { s' with locks := stubRemoveFirstLock p mode s'.locks }) : StateM TempDirStubState Unit))
          return r.map some
        else
          return .error e }

private def stubTimeEx : TimeOpsM (ExceptT String (StateM TempDirStubState)) :=
  { nowTimestamp := liftM stubTime.nowTimestamp
    monoNanosNow := liftM stubTime.monoNanosNow
    sleep := fun ms => liftM (stubTime.sleep ms) }

private def stubUuidEx : UuidApiM (ExceptT String (StateM TempDirStubState)) :=
  { mapRawError := stubUuid.mapRawError
    fromRandomBytes := stubUuid.fromRandomBytes
    toString := stubUuid.toString
    toHex := stubUuid.toHex
    parse := stubUuid.parse
    parseHex := stubUuid.parseHex
    isValid := stubUuid.isValid
    getUuid := liftM stubUuid.getUuid }

private def stubEnvEx : EnvVarsApiM (ExceptT String (StateM TempDirStubState)) :=
  { mapRawError := stubEnv.mapRawError
    getEnv := fun k => liftM (stubEnv.getEnv k)
    listEnv := liftM stubEnv.listEnv
    homeDir := liftM stubEnv.homeDir
    splitSearchPath := stubEnv.splitSearchPath }

private def noopTempDirBuilder {m : Type → Type} [Monad m] : TempDirBuilder m :=
  fun _ _ _ _ =>
    { withTempDir := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      withLockedTempDir := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      cleanupStaleTempDirs := fun _ _ _ => pure (.ok {}) }

private def buggyWithTempDirNoCleanup : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithTempDirSwallowsCleanupErr : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithTempDirExistOk : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithTempDirNoChmodRollback : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithTempDirIgnoresTmpdir : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithLockedTempDirPropagatesNotFound : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyExNoTryFinally : TempDirBuilder (ExceptT String (StateM TempDirStubState)) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTimeEx uuid stubEnvEx) with
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

private def buggyCleanupDeletesLocked : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ _ _ =>
    { (noopTempDirBuilder fs stubTime stubUuid stubEnv) with
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

private def buggyCleanupKeepsDeadLock : TempDirBuilder (StateM TempDirStubState) :=
  fun _ _ _ _ =>
    { (noopTempDirBuilder stubFs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        return .ok { keptFresh := #[stubJoin root "tmp-dead"] } }

private def buggyCleanupDeletesYoungUnlocked : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ _ _ =>
    { (noopTempDirBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-young"
        let _ ← fs.rmtree child true
        return .ok { removed := #[child] } }

private def buggyCleanupDeletesNonMatching : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ _ _ =>
    { (noopTempDirBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "other-dir"
        let _ ← fs.rmtree child true
        return .ok { removed := #[child] } }

private def buggyCleanupDeletesLockFirst : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ _ _ =>
    { (noopTempDirBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-dead"
        let _ ← fs.rmtree child true
        return .ok { failed := #[{ kind := .permissionDenied, path := some child, message := "partial" }] } }

private def buggyWithLockedTempDirNoChmod : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyWithLockedTempDirSwallowsLockErr : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid _ =>
    { (noopTempDirBuilder fs stubTime uuid stubEnv) with
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

private def buggyLockedTempDirIgnoresTmpdir : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ uuid env =>
    { (noopTempDirBuilder fs stubTime uuid env) with
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

private def buggyCleanupLeaksLockOnPartialFail : TempDirBuilder (StateM TempDirStubState) :=
  fun fs _ _ _ =>
    { (noopTempDirBuilder fs stubTime stubUuid stubEnv) with
      cleanupStaleTempDirs := fun root? _ _ => do
        let root := root?.getD "/tmp"
        let child := fs.join root "tmp-dead"
        let lockPath := fs.join child ".lock"
        modify fun s => { s with locks := (lockPath, .exclusive) :: s.locks }
        return .ok { failed := #[{ kind := .permissionDenied, path := some child, message := "leaked lock" }] } }

example : ¬ Core.AllPass (test_tempdir_withTempDir_okCleansUpAndSetsMode buggyWithTempDirNoCleanup stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 7 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_tempdir_withTempDir_okCleansUpAndSetsMode, Core.NondetTest.assert, Bind.bind, stubFs, stubTime, stubUuid, stubEnv, buggyWithTempDirNoCleanup] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_tempdir_withTempDir_errorCleansUpAndPreservesError noopTempDirBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" { kind := .invalidInput, message := "err" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_tempdir_withTempDir_errorCleansUpAndPreservesError, Core.NondetTest.assert, Bind.bind, noopTempDirBuilder] at h0
  cases h0.1

example : ¬ Core.AllPass (test_tempdir_withTempDir_cleanupErrorReturnedOnOk buggyWithTempDirSwallowsCleanupErr stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 1 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, Core.NondetTest.assert, Bind.bind, buggyWithTempDirSwallowsCleanupErr] at h0
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_tempdir_withTempDir_collisionRejected buggyWithTempDirExistOk stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState := { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-00000000-0000-4000-8000-000000000001", 0, 0o755)] }
  have h0 := h s "/tmp" "tmp-" "/marker" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, Or.inl rfl⟩
  dsimp [test_tempdir_withTempDir_collisionRejected, Core.NondetTest.assert, Bind.bind, buggyWithTempDirExistOk] at h0
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_tempdir_withTempDir_chmodFailureRollsBack buggyWithTempDirNoChmodRollback stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" "/marker" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide) (by decide)
  dsimp [test_tempdir_withTempDir_chmodFailureRollsBack, Core.NondetTest.assert, Bind.bind, buggyWithTempDirNoChmodRollback] at h0
  exact absurd h0.2.2 (by decide)

example : ¬ Core.AllPass (test_tempdir_validation_rejectsInvalidInputs noopTempDirBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" ".bad" (Or.inl (by decide))
  dsimp [test_tempdir_validation_rejectsInvalidInputs, Core.NondetTest.assert, Bind.bind, noopTempDirBuilder] at h0
  rcases h0.1 with ⟨e, he, hk, _⟩
  cases he
  cases hk

example : ¬ Core.AllPass (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing buggyWithTempDirIgnoresTmpdir stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState := { dirs := [("/tmp", 0, 0o755), ("/custom", 0, 0o755)], tmpdir := some "/custom" }
  have h0 := h s "tmp-" (by decide) ⟨rfl, rfl, rfl, rfl⟩ (by decide)
  have hEq : (Except.ok "/tmp/tmp-00000000-0000-4000-8000-000000000001" : Except TempDirError String) = Except.ok "/custom/tmp-00000000-0000-4000-8000-000000000001" := h0.1
  simp at hEq

example : ¬ Core.AllPass (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing buggyLockedTempDirIgnoresTmpdir stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState := { dirs := [("/tmp", 0, 0o755), ("/custom", 0, 0o755)], tmpdir := some "/custom" }
  have h0 := h s "tmp-" (by decide) ⟨rfl, rfl, rfl, rfl⟩ (by decide)
  have hEq : (Except.ok "/tmp/tmp-00000000-0000-4000-8000-000000000001" : Except TempDirError String) = Except.ok "/custom/tmp-00000000-0000-4000-8000-000000000001" := h0.2.1
  simp at hEq

example : ¬ Core.AllPass (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit noopTempDirBuilder stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, Core.NondetTest.assert, Bind.bind, noopTempDirBuilder] at h0
  cases h0.1

example : ¬ Core.AllPass (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit buggyWithLockedTempDirNoChmod stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  have hEq : Except.error { kind := TempDirErrorKind.ioError, path := some "/tmp/tmp-00000000-0000-4000-8000-000000000001", message := "dir mode or lock invariant failed" } = (Except.ok 5 : Except TempDirError Nat) := h0.1
  cases hEq

example : ¬ Core.AllPass (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit buggyWithLockedTempDirSwallowsLockErr stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 5 { kind := .ioError, message := "e" } (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  rcases h0.2.2.2.2.2.2.2.1 with ⟨e, he, hk⟩
  have hErr : Except.error { kind := TempDirErrorKind.ioError, message := "rm wins over lock err" } = (Except.error e : Except TempDirError Nat) := he
  cases hErr
  cases hk

example : ¬ Core.AllPass (test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup buggyWithLockedTempDirPropagatesNotFound stubFs stubTime stubUuid stubEnv) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" 9 (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  have hEq : Except.error { kind := TempDirErrorKind.notFound, path := some "/tmp/tmp-00000000-0000-4000-8000-000000000001", message := "rm failed" } = (Except.ok 9 : Except TempDirError Nat) := h0.1
  cases hEq

example : ¬ Core.AllPass (test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock buggyExNoTryFinally stubFsEx stubTimeEx stubUuidEx stubEnvEx stubFs stubUuid) := by
  intro h
  have h0 := h {} "/tmp" "tmp-" (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ (by decide)
  dsimp [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, Core.NondetTest.assert, Bind.bind, buggyExNoTryFinally, stubFsEx, stubTimeEx, stubUuidEx, stubEnvEx, stubFs, stubUuid] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge buggyCleanupDeletesLocked stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-live", 0, 0o700)]
      files := [("/tmp/tmp-live/.lock", "", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-live" 10 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ ⟨{ kind := .file, byteSize := 0, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ (by decide)
  dsimp [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesLocked, stubFs, stubTime, stubUuid, stubEnv] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately buggyCleanupKeepsDeadLock stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 1000, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 1000)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 1000, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 0, mode := 0o644, modifiedSec := 1000, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ (congrArg Except.ok (by decide)) rfl (by decide)
  dsimp [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, Core.NondetTest.assert, Bind.bind, buggyCleanupKeepsDeadLock] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked buggyCleanupDeletesYoungUnlocked stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-young", 950, 0o700)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-young" 100 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 950, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .notFound, path := some "/tmp/tmp-young/.lock", message := "not found" }, rfl, rfl⟩
  have hBad : (false = true ∧ ¬ true = true) ∧ false = true ∧ True := h0
  exact absurd hBad (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety buggyCleanupDeletesNonMatching stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/other-dir", 0, 0o755)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "other-dir" 10 (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, Or.inl (by decide)⟩
  dsimp [test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesNonMatching] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety buggyCleanupDeletesLockFirst stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 0, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 0), ("/tmp/tmp-dead/locked_child.txt", "x", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 1, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ rfl
  dsimp [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, Core.NondetTest.assert, Bind.bind, buggyCleanupDeletesLockFirst] at h0
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety buggyCleanupLeaksLockOnPartialFail stubFs stubTime stubUuid stubEnv) := by
  intro h
  let s : TempDirStubState :=
    { dirs := [("/tmp", 0, 0o755), ("/tmp/tmp-dead", 0, 0o700)]
      files := [("/tmp/tmp-dead/.lock", "", 0), ("/tmp/tmp-dead/locked_child.txt", "x", 0)]
      nowSec := 1000 }
  have h0 := h s "/tmp" "tmp-" "tmp-dead" 86400 (by decide) (by decide) (by decide) ⟨{ kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .dir, byteSize := 0, mode := 0o700, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .file, byteSize := 1, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }, rfl, rfl⟩ rfl
  have hBad : (Except.ok (none : Option Unit) : Except FsError (Option Unit)) = Except.ok (some ()) := h0.2.2.2.1
  cases hBad

end LeanSwe.TempDir

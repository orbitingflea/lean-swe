import LeanSwe.Fs.Types
import LeanSwe.Fs.Model
import LeanSwe.Glob.Interface

namespace LeanSwe.Fs.Internal

open LeanSwe.Fs
  (FsErrorKind FsError EntryKind FileStat WalkEntry FsRawError LockMode FsApi FsApiM
   EntryName RelPath SubtreeM SubtreeOpenerM)
open LeanSwe.Fs.Model (NonLockFsOpsM RawFsOpsM RawDirOpsM ScopedRawFsOpsM nonEmptyMsg isValidRawPath)

export LeanSwe.Fs.Model
  (isAbsChars isAbsolute join joinMany splitCharList joinSlashChars collapseChars normPath
   cleanCharSegments splitLastAux splitParentName parent name splitRevAtDot splitNameSuffix
   stem suffix suffixes validFileName validSuffix joinParentName withName withSuffix relativeTo)

/-- Construct a `GlobError` mapped into `FsError`. -/
def mapGlobError (pattern : String) (err : LeanSwe.Glob.GlobError) : FsError :=
  { kind := .invalidInput
    path := some pattern
    errnoCode := none
    message := nonEmptyMsg "invalid glob pattern" err.message }

/-- Read and sort immediate child entry names in `path`. -/
def listDirSortedM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m) (path : String) :
    m (Except FsError (Array String)) := do
  match ← ops.readDir path with
  | .error e => return .error e
  | .ok names => return .ok (names.toList.mergeSort (· ≤ ·)).toArray

/-- Build ancestor directory chain from outermost to immediate parent (excluding `/`). -/
def ancestorChain (p : String) : Nat → List String
  | 0 => []
  | n + 1 =>
    match parent p with
    | none => []
    | some "/" => []
    | some par => ancestorChain par n ++ [par]

/-- Ensure ancestor directory `anc` exists as a directory. -/
def ensureDirM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m) (anc : String) :
    m (Except FsError Unit) := do
  match ← ops.stat true anc with
  | .ok st =>
    if st.kind == .dir then
      return .ok ()
    else
      return .error { kind := .notADirectory, path := some anc, message := s!"not a directory: {anc}" }
  | .error e =>
    if e.kind != .notFound then
      return .error e
    else
      match ← ops.createDir anc with
      | .ok () => return .ok ()
      | .error ce =>
        if ce.kind == .alreadyExists then
          match ← ops.stat true anc with
          | .ok st2 =>
            if st2.kind == .dir then return .ok ()
            else return .error { kind := .notADirectory, path := some anc, message := s!"not a directory: {anc}" }
          | .error _ => return .error { kind := .notADirectory, path := some anc, message := s!"not a directory: {anc}" }
        else
          return .error ce

/-- Ensure a top-down list of ancestor directories exist. -/
def ensureAncestorsM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m) :
    List String → m (Except FsError Unit)
  | [] => return .ok ()
  | anc :: rest => do
    match ← ensureDirM ops anc with
    | .error e => return .error e
    | .ok () => ensureAncestorsM ops rest

/-- Create leaf directory `path`, tolerating concurrent `.alreadyExists` when `path` resolves to a directory. -/
def createDirExistOkM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) : m (Except FsError Unit) := do
  match ← ops.createDir path with
  | .ok () => return .ok ()
  | .error ce =>
    if ce.kind != .alreadyExists then
      return .error ce
    else
      match ← ops.stat true path with
      | .ok st =>
        if st.kind == .dir then
          return .ok ()
        else
          return .error ce
      | .error _ =>
        return .error ce

/-- Generic `mkdir` implementation over `NonLockFsOpsM m`. -/
def mkdirImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (parents existOk : Bool) : m (Except FsError Unit) := do
  match ← ops.stat false path with
  | .ok st =>
    if existOk && st.kind == .dir then
      return .ok ()
    else if existOk && st.kind == .symlink then
      match ← ops.stat true path with
      | .ok tgtSt =>
        if tgtSt.kind == .dir then
          return .ok ()
        else
          return .error { kind := .alreadyExists, path := some path, message := s!"path already exists: {path}" }
      | .error _ =>
        return .error { kind := .alreadyExists, path := some path, message := s!"path already exists: {path}" }
    else
      return .error { kind := .alreadyExists, path := some path, message := s!"path already exists: {path}" }
  | .error e =>
    if e.kind != .notFound then
      return .error e
    else if !parents then
      if existOk then createDirExistOkM ops path else ops.createDir path
    else
      let ancs := ancestorChain path path.toList.length
      match ← ensureAncestorsM ops ancs with
      | .error ae => return .error ae
      | .ok () => if existOk then createDirExistOkM ops path else ops.createDir path

/-- Generic `unlink` implementation over `NonLockFsOpsM m`. -/
def unlinkImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (missingOk : Bool) : m (Except FsError Unit) := do
  match ← ops.stat false path with
  | .error e =>
    if e.kind == .notFound && missingOk then
      return .ok ()
    else
      return .error e
  | .ok st =>
    if st.kind == .dir then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else
      ops.unlinkFile path

/-- Sequence a monadic action `f` across `List String`, short-circuiting on first error. -/
def forEachChildM {m : Type → Type} [Monad m]
    (f : String → m (Except FsError Unit)) : List String → m (Except FsError Unit)
  | [] => return .ok ()
  | n :: rest => do
    match ← f n with
    | .error e => return .error e
    | .ok () => forEachChildM f rest

/-- Bounded recursive worker for `rmtreeImplM`. -/
def rmtreeGoM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (dir : String) : Nat → m (Except FsError Unit)
  | 0 => return .error { kind := .ioError, path := some dir, message := s!"maximum directory depth exceeded: {dir}" }
  | fuel + 1 => do
    match ← listDirSortedM ops dir with
    | .error e => return .error e
    | .ok names =>
      match ← forEachChildM (fun n => do
        let child := join dir n
        match ← ops.stat false child with
        | .error e => return .error e
        | .ok st =>
          if st.kind == .dir then rmtreeGoM ops child fuel
          else ops.unlinkFile child) names.toList with
      | .error e => return .error e
      | .ok () => ops.removeDir dir

/-- Generic `rmtree` implementation over `NonLockFsOpsM m`. -/
def rmtreeImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (ignoreMissing : Bool) : m (Except FsError Unit) := do
  match ← ops.stat false path with
  | .error e =>
    if e.kind == .notFound && ignoreMissing then
      return .ok ()
    else
      return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }
    else
      rmtreeGoM ops path 4096

/-- Generic `copyFile` implementation over `NonLockFsOpsM m`. -/
def copyFileImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (src dst : String) : m (Except FsError Unit) := do
  match ← ops.stat true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind == .dir then
      return .error { kind := .isADirectory, path := some src, message := s!"source is a directory: {src}" }
    match ← ops.readBytes src with
    | .error e => return .error e
    | .ok bytes => ops.writeBytes dst bytes

/-- Resolve the deepest existing ancestor of `cur` and append uncreated suffix segments. -/
def resolveApproxGoM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (cur : String) (tail : List String) : Nat → m String
  | 0 => return tail.foldl join cur
  | fuel + 1 => do
    match ← ops.realPath cur with
    | .ok rp => return tail.foldl join rp
    | .error _ =>
      match parent cur, name cur with
      | some par, some seg => resolveApproxGoM ops par (seg :: tail) fuel
      | _, _ => return tail.foldl join cur

/-- Bounded recursive worker for `copyTreeImplM`. -/
def copyTreeGoM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (src dst : String) (dirsExistOk : Bool) (visited : List String) : Nat → m (Except FsError Unit)
  | 0 => return .error { kind := .ioError, path := some src, message := s!"maximum directory depth exceeded: {src}" }
  | fuel + 1 => do
    match ← ops.stat true src with
    | .error e => return .error e
    | .ok st =>
      if st.kind != .dir then
        return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
      match ← ops.realPath src with
      | .error e => return .error e
      | .ok canon =>
        if canon ∈ visited then
          return .error { kind := .invalidInput, path := some src, message := s!"symlink directory loop: {src}" }
        let visited' := canon :: visited
        match ← listDirSortedM ops src with
        | .error e => return .error e
        | .ok names =>
          match ← mkdirImplM ops dst true dirsExistOk with
          | .error e => return .error e
          | .ok () =>
            forEachChildM (fun n => do
              let sChild := join src n
              let dChild := join dst n
              match ← ops.stat true sChild with
              | .error e => return .error e
              | .ok childSt =>
                if childSt.kind == .dir then
                  copyTreeGoM ops sChild dChild dirsExistOk visited' fuel
                else
                  copyFileImplM ops sChild dChild) names.toList

/-- Generic `copyTree` implementation over `NonLockFsOpsM m` with cycle and self-copy guards. -/
def copyTreeImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (src dst : String) (dirsExistOk : Bool) : m (Except FsError Unit) := do
  match ← ops.stat true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
    match ← ops.realPath src with
    | .error e => return .error e
    | .ok srcCanon =>
      let dstAbs ←
        if isAbsolute dst then
          pure (normPath dst)
        else do
          match ← ops.cwd with
          | .error _ => pure (normPath dst)
          | .ok d => pure (normPath (join d dst))
      let dstCanon ← resolveApproxGoM ops dstAbs [] (dstAbs.toList.length + 1)
      if dstCanon == srcCanon || srcCanon == "/" || (srcCanon.toList ++ ['/']).isPrefixOf dstCanon.toList then
        return .error { kind := .invalidInput, path := some dst, message := s!"cannot copy directory into itself: {dst}" }
      copyTreeGoM ops src dst dirsExistOk [] 4096

/-- Generic `touch` implementation over `NonLockFsOpsM m`. -/
def touchImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (existOk : Bool) : m (Except FsError Unit) := do
  match ← ops.stat false path with
  | .ok st =>
    if !existOk then
      return .error { kind := .alreadyExists, path := some path, message := s!"file already exists: {path}" }
    else if st.kind == .dir then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else if st.kind == .symlink then
      match ← ops.stat true path with
      | .ok tgtSt =>
        if tgtSt.kind == .dir then
          return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
        else
          ops.appendText path ""
      | .error _ =>
        ops.appendText path ""
    else
      ops.appendText path ""
  | .error e =>
    if e.kind == .notFound then
      ops.writeBytes path ByteArray.empty
    else
      return .error e

/-- Checks whether `path` ends with a raw `.` or `..` final segment before normalization. -/
def hasDotFinalSegment (path : String) : Bool :=
  match path.toList.reverse with
  | ['.'] | '.' :: '/' :: _ => true
  | ['.', '.'] | '.' :: '.' :: '/' :: _ => true
  | _ => false

/-- Checks raw path validity and rejects raw `.` or `..` final path segments. -/
def isValidAtomicTargetPath (path : String) : Bool :=
  isValidRawPath path && !hasDotFinalSegment path

/-- Writes `bytes` to a sibling temp file with a fresh nonce and renames it atomically to `path`. -/
def atomicWriteSiblingM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (bytes : ByteArray) : m (Except FsError Unit) := do
  let parentDir := (parent path).getD "."
  let baseName := (name path).getD "tmp"
  let nonce ← ops.monotonicNonce
  let tmpPath := join parentDir s!".{baseName}.tmp.{nonce}"
  match ← ops.createFileNew tmpPath bytes with
  | .error e => return .error e
  | .ok () =>
    match ← ops.rename tmpPath path with
    | .error e =>
      let _ ← ops.unlinkFile tmpPath
      return .error e
    | .ok () => return .ok ()

/-- Implements `FsApiM.atomicWriteBytes` cleanly over non-lock raw filesystem ops. -/
def atomicWriteBytesImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (bytes : ByteArray) : m (Except FsError Unit) := do
  if !isValidAtomicTargetPath path then
    return .error { kind := .invalidInput, path := some path, message := s!"invalid target path: {path}" }
  else if path == "/" then
    return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
  else
    match ← ops.stat false path with
    | .error e =>
      if e.kind != .notFound then
        return .error e
      else
        atomicWriteSiblingM ops path bytes
    | .ok st =>
      if st.kind == .dir then
        return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
      else
        atomicWriteSiblingM ops path bytes

/-- Generic `atomicWriteText` implementation over `NonLockFsOpsM m`. -/
def atomicWriteTextImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path content : String) : m (Except FsError Unit) :=
  atomicWriteBytesImplM ops path content.toUTF8

/-- Retry exclusive sibling temporary creation up to `attempts` times on `.alreadyExists`, then rename onto `path`. -/
def atomicWriteSiblingRetryM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (bytes : ByteArray) : Nat → m (Except FsError Unit)
  | 0 =>
    pure (.error { kind := .alreadyExists, path := some path, message := "temporary file name collision limit exceeded" })
  | attempts + 1 => do
    let parentDir := (parent path).getD "."
    let baseName := (name path).getD "tmp"
    let nonce ← ops.monotonicNonce
    let tmpPath := join parentDir s!".{baseName}.tmp.{nonce}"
    match ← ops.createFileNew tmpPath bytes with
    | .ok () =>
      match ← ops.rename tmpPath path with
      | .ok () => pure (.ok ())
      | .error e =>
        let _ ← ops.unlinkFile tmpPath
        pure (.error e)
    | .error e =>
      if e.kind == .alreadyExists && attempts > 0 then
        atomicWriteSiblingRetryM ops path bytes attempts
      else
        pure (.error e)

/-- Implements `FsApiM.atomicWriteBytes` with bounded sibling temp-collision retry. -/
def atomicWriteBytesRetryM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) (bytes : ByteArray) (attempts : Nat := 16) : m (Except FsError Unit) := do
  if !isValidAtomicTargetPath path then
    return .error { kind := .invalidInput, path := some path, message := s!"invalid target path: {path}" }
  else if path == "/" then
    return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
  else
    match ← ops.stat false path with
    | .error e =>
      if e.kind != .notFound then
        return .error e
      else
        atomicWriteSiblingRetryM ops path bytes attempts
    | .ok st =>
      if st.kind == .dir then
        return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
      else
        atomicWriteSiblingRetryM ops path bytes attempts

/-- Bounded recursive worker for `walkImplM`. -/
def walkGoM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (root relRoot : String) (acc : Array WalkEntry) : Nat → m (Except FsError (Array WalkEntry))
  | 0 => return .error { kind := .ioError, path := some root, message := s!"maximum directory depth exceeded: {root}" }
  | fuel + 1 => do
    let fullDir := if relRoot == "." then root else join root relRoot
    match ← listDirSortedM ops fullDir with
    | .error e => return .error e
    | .ok names =>
      let mut dirs : Array String := #[]
      let mut files : Array String := #[]
      for n in names do
        let childFull := join fullDir n
        let isSubDir ←
          match ← ops.stat false childFull with
          | .ok st => pure (st.kind == .dir)
          | .error _ => pure false
        if isSubDir then
          dirs := dirs.push n
        else
          files := files.push n
      let mut out := acc.push { root := relRoot, dirs, files }
      for d in dirs do
        let nextRel := if relRoot == "." then d else join relRoot d
        match ← walkGoM ops root nextRel out fuel with
        | .error e => return .error e
        | .ok out' => out := out'
      return .ok out

/-- Generic `walk` implementation over `NonLockFsOpsM m`. -/
def walkImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (root : String) : m (Except FsError (Array WalkEntry)) := do
  match ← ops.stat true root with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }
    walkGoM ops root "." #[] 4096

/-- Generic `glob` implementation over `NonLockFsOpsM m`. -/
def globImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (root pattern : String) : m (Except FsError (Array String)) := do
  match LeanSwe.Glob.validate pattern with
  | .error e => return .error (mapGlobError pattern e)
  | .ok () =>
    match ← walkImplM ops root with
    | .error e => return .error e
    | .ok entries =>
      let mut candidates : Array String := #[]
      for entry in entries do
        for d in entry.dirs do
          let rel := if entry.root == "." then d else join entry.root d
          candidates := candidates.push rel
        for f in entry.files do
          let rel := if entry.root == "." then f else join entry.root f
          candidates := candidates.push rel
      match LeanSwe.Glob.filter pattern candidates with
      | .error e => return .error (mapGlobError pattern e)
      | .ok matched => return .ok (matched.toList.mergeSort (· ≤ ·)).toArray

/-- Generic `rglob` implementation over `NonLockFsOpsM m`. -/
def rglobImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (root pattern : String) : m (Except FsError (Array String)) :=
  let fullPat := if pattern == "**" || pattern.startsWith "**/" then pattern else "**/" ++ pattern
  globImplM ops root fullPat

/-- Generic `readText` implementation over `NonLockFsOpsM m`. -/
def readTextImplM {m : Type → Type} [Monad m] (ops : NonLockFsOpsM m)
    (path : String) : m (Except FsError String) := do
  match ← ops.readBytes path with
  | .error e => return .error e
  | .ok bs =>
    match String.fromUTF8? bs with
    | some s => return .ok s
    | none => return .error { kind := .invalidInput, path := some path, message := s!"invalid UTF-8 in file: {path}" }

/-- Run `action` under `handle`, always calling `ops.releaseLock handle` afterward. -/
def bracketLockM {m : Type → Type} [Monad m] [MonadFinally m]
    {lockH : Type} (ops : RawFsOpsM m lockH) {α : Type} (handle : lockH)
    (action : m (Except FsError α)) : m (Except FsError α) := do
  let (actRes, relRes) ← tryFinally' action (fun _ => ops.releaseLock handle)
  match actRes with
  | .error e => return .error e
  | .ok a =>
    match relRes with
    | .ok () => return .ok a
    | .error re => return .error re

/-- Acquire `mode` advisory lock on `path`, run `action`, and unlock/close afterward. -/
def withFileLockImplM {m : Type → Type} [Monad m] [MonadFinally m]
    {lockH : Type} (ops : RawFsOpsM m lockH) {α : Type} (path : String) (mode : LockMode)
    (createIfMissing : Bool) (action : m (Except FsError α)) : m (Except FsError α) := do
  match ← ops.acquireLock path mode createIfMissing false with
  | .error e => return .error e
  | .ok handle => bracketLockM ops handle action

/-- Try non-blocking `mode` lock on `path`; return `.ok none` on `.wouldBlock`, else run `action`. -/
def tryWithFileLockImplM {m : Type → Type} [Monad m] [MonadFinally m]
    {lockH : Type} (ops : RawFsOpsM m lockH) {α : Type} (path : String) (mode : LockMode)
    (createIfMissing : Bool) (action : m (Except FsError α)) : m (Except FsError (Option α)) := do
  match ← ops.acquireLock path mode createIfMissing true with
  | .error e =>
    if e.kind == .wouldBlock then
      return .ok none
    else
      return .error e
  | .ok handle =>
    match ← bracketLockM ops handle action with
    | .ok a => return .ok (some a)
    | .error e => return .error e

/-- Project `RawFsOpsM m lockH` into `ScopedRawFsOpsM m` by bracketing `acquireLock`/`releaseLock`. -/
def toScopedRawFsOpsM {m : Type → Type} [Monad m] [MonadFinally m] {lockH : Type}
    (ops : RawFsOpsM m lockH) : ScopedRawFsOpsM m :=
  { toNonLockFsOpsM := ops.toNonLockFsOpsM
    withFileLock := withFileLockImplM ops
    tryWithFileLock := tryWithFileLockImplM ops }

end LeanSwe.Fs.Internal

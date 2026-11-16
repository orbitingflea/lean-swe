import LeanSwe.Fs.Types
import LeanSwe.Fs.Raw.Types
import LeanSwe.Glob.Interface

namespace LeanSwe.Fs.Internal

open LeanSwe.Fs
  (FsErrorKind FsError EntryKind FileStat WalkEntry FsRawError LockMode LockHandle RawFsOpsM FsApi FsApiM
   DirHandle EntryName RelPath RawDirOpsM SubtreeM SubtreeOpenerM)

private def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Construct a `GlobError` mapped into `FsError`. -/
def mapGlobError (pattern : String) (err : LeanSwe.Glob.GlobError) : FsError :=
  { kind := .invalidInput
    path := some pattern
    errnoCode := none
    message := nonEmptyMsg "invalid glob pattern" err.message }

/-- Return `true` iff character list starts with `/`. -/
def isAbsChars : List Char → Bool
  | '/' :: _ => true
  | _ => false

/-- Return `true` iff `path` begins with `/`. -/
def isAbsolute (path : String) : Bool :=
  isAbsChars path.toList

/-- Join two path strings using `/` (`Path.joinpath`). -/
def join (base sub : String) : String :=
  if isAbsolute sub then sub
  else if base.isEmpty then sub
  else if base.toList.getLast? == some '/' then base ++ sub
  else base ++ "/" ++ sub

/-- Join an array of path strings left-to-right. -/
def joinMany (parts : Array String) : String :=
  parts.foldl join ""

/-- Split `cs` on `sep`, always producing a non-empty list of segments. -/
def splitCharList (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then
      [] :: splitCharList sep cs
    else
      match splitCharList sep cs with
      | [] => [[c]]
      | seg :: rest => (c :: seg) :: rest

/-- Join path segments using `/` separators. -/
def joinSlashChars : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: rest => s ++ '/' :: joinSlashChars rest

/-- Collapse slash-separated path character segments lexically. -/
def collapseChars (abs : Bool) : List (List Char) → List (List Char) → List (List Char)
  | [], acc => acc.reverse
  | seg :: rest, acc =>
    if seg.isEmpty || seg == ['.'] then
      collapseChars abs rest acc
    else if seg == ['.', '.'] then
      match acc with
      | top :: tail =>
        if top != ['.', '.'] then collapseChars abs rest tail
        else collapseChars abs rest (if abs then acc else ['.', '.'] :: acc)
      | [] =>
        collapseChars abs rest (if abs then [] else [['.', '.']])
    else
      collapseChars abs rest (seg :: acc)

/-- Lexically normalize `.` and `..` segments and redundant `/` (`os.path.normpath`). -/
def normPath (path : String) : String :=
  let cs := path.toList
  let abs := isAbsChars cs
  let parts := collapseChars abs (splitCharList '/' cs) []
  if abs then
    String.ofList ('/' :: joinSlashChars parts)
  else if parts.isEmpty then
    "."
  else
    String.ofList (joinSlashChars parts)

/-- Split `path` into non-empty `/` character segments (excluding `.`), tracking `abs`. -/
def cleanCharSegments (path : String) : Bool × List (List Char) :=
  let cs := path.toList
  (isAbsChars cs, (splitCharList '/' cs).filter fun s => !s.isEmpty && s != ['.'])

/-- Split a non-empty list into `(init, last)`. -/
def splitLastAux {α : Type} : List α → List α → Option (List α × α)
  | [], _ => none
  | [x], acc => some (acc.reverse, x)
  | x :: rest, acc => splitLastAux rest (x :: acc)

/-- Split `path` into optional parent string and final component name. -/
def splitParentName (path : String) : Option (Option String × String) :=
  let (abs, parts) := cleanCharSegments path
  match splitLastAux parts [] with
  | none => none
  | some ([], last) =>
    some (if abs then some "/" else none, String.ofList last)
  | some (front, last) =>
    let joined := joinSlashChars front
    let prefixStr := String.ofList (if abs then '/' :: joined else joined)
    some (some prefixStr, String.ofList last)

/-- Return parent directory path, or `none` when at root or single bare component. -/
def parent (path : String) : Option String :=
  match splitParentName path with
  | none => none
  | some (p?, _) => p?

/-- Return the final path component name, if any. -/
def name (path : String) : Option String :=
  match splitParentName path with
  | none => none
  | some (_, last) => some last

/-- Split reversed character list at the first `.` separator. -/
def splitRevAtDot : List Char → Option (List Char × List Char)
  | [] => none
  | '.' :: rest => some (rest, [])
  | c :: rest =>
    match splitRevAtDot rest with
    | none => none
    | some (pref, suf) => some (pref, c :: suf)

/-- Split a single filename into `(stem, suffix)` using Python `Path` conventions. -/
def splitNameSuffix (fileName : String) : String × String :=
  match splitRevAtDot fileName.toList.reverse with
  | none => (fileName, "")
  | some (revPref, revSuf) =>
    if revPref.isEmpty || revSuf.isEmpty || revPref.all (· == '.') then
      (fileName, "")
    else
      (String.ofList revPref.reverse, "." ++ String.ofList revSuf.reverse)

/-- Return the final path component without its last suffix (`Path.stem`). -/
def stem (path : String) : Option String :=
  (name path).map fun n => (splitNameSuffix n).1

/-- Return the last `.ext` suffix of filename, or `""` when none (`Path.suffix`). -/
def suffix (path : String) : String :=
  match name path with
  | none => ""
  | some n => (splitNameSuffix n).2

/-- Return all `.ext` suffixes of filename (`Path.suffixes`). -/
def suffixes (path : String) : Array String :=
  match name path with
  | none => #[]
  | some n =>
    match n.toList.reverse with
    | '.' :: _ => #[]
    | _ =>
      let stripped := n.toList.dropWhile (· == '.')
      match splitCharList '.' stripped with
      | [] | [_] => #[]
      | _ :: exts => (exts.map fun cs => "." ++ String.ofList cs).toArray

/-- Return `true` iff `s` is a valid non-empty single path segment name. -/
def validFileName (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && !('/' ∈ cs) && cs != ['.'] && cs != ['.', '.']

/-- Return `true` iff `s` is empty or a valid non-empty suffix starting with `.`. -/
def validSuffix (s : String) : Bool :=
  match s.toList with
  | [] => true
  | '.' :: rest => !rest.isEmpty && !('/' ∈ rest) && rest != ['.']
  | _ => false

/-- Join optional normalized parent prefix with a valid filename `newName`. -/
def joinParentName : Option String → String → String
  | none, newName => newName
  | some "/", newName => "/" ++ newName
  | some par, newName => par ++ "/" ++ newName

/-- Replace the final path component (`Path.with_name`). -/
def withName (path newName : String) : Except FsError String :=
  if !validFileName newName then
    .error { kind := .invalidInput, path := some path, message := s!"invalid filename: '{newName}'" }
  else
    match splitParentName path with
    | none =>
      .error { kind := .invalidInput, path := some path, message := "path has an empty name" }
    | some (par?, _) => .ok (joinParentName par? newName)

/-- Replace or strip the last suffix (`Path.with_suffix`). -/
def withSuffix (path newSuffix : String) : Except FsError String :=
  if !validSuffix newSuffix then
    .error { kind := .invalidInput, path := some path, message := s!"invalid suffix: '{newSuffix}'" }
  else
    match splitParentName path with
    | none =>
      .error { kind := .invalidInput, path := some path, message := "path has an empty name" }
    | some (_, oldName) =>
      let (stemPart, _) := splitNameSuffix oldName
      if stemPart.isEmpty || stemPart.toList.all (· == '.') then
        .error { kind := .invalidInput, path := some path, message := "cannot change suffix of dot-only name" }
      else
        withName path (stemPart ++ newSuffix)

private def stripPrefixParts : List (List Char) → List (List Char) → Option (List (List Char))
  | [], rest => some rest
  | b :: bs, p :: ps =>
    if b == p then stripPrefixParts bs ps else none
  | _ :: _, [] => none

/-- Compute lexical path of `path` relative to `base` (`Path.relative_to`). -/
def relativeTo (path base : String) : Except FsError String :=
  let (absP, pParts) := cleanCharSegments (normPath path)
  let (absB, bParts) := cleanCharSegments (normPath base)
  if absP != absB then
    .error { kind := .invalidInput, path := some path, message := s!"'{path}' is not in the subpath of '{base}'" }
  else
    match stripPrefixParts bParts pParts with
    | none =>
      .error { kind := .invalidInput, path := some path, message := s!"'{path}' is not in the subpath of '{base}'" }
    | some [] => .ok "."
    | some rel => .ok (String.ofList (joinSlashChars rel))

/-- Read and sort immediate child entry names in `path`. -/
def listDirSortedM {m : Type → Type} [Monad m] (ops : RawFsOpsM m) (path : String) :
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
def ensureDirM {m : Type → Type} [Monad m] (ops : RawFsOpsM m) (anc : String) :
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
def ensureAncestorsM {m : Type → Type} [Monad m] (ops : RawFsOpsM m) :
    List String → m (Except FsError Unit)
  | [] => return .ok ()
  | anc :: rest => do
    match ← ensureDirM ops anc with
    | .error e => return .error e
    | .ok () => ensureAncestorsM ops rest

/-- Generic `mkdir` implementation over `RawFsOpsM m`. -/
def mkdirImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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
      ops.createDir path
    else
      let ancs := ancestorChain path path.toList.length
      match ← ensureAncestorsM ops ancs with
      | .error ae => return .error ae
      | .ok () => ops.createDir path

private def unlinkImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

private def rmtreeGoM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

private def rmtreeImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

private def copyFileImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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
def resolveApproxGoM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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
def copyTreeGoM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

/-- Generic `copyTree` implementation over `RawFsOpsM m` with cycle and self-copy guards. -/
def copyTreeImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

/-- Generic `touch` implementation over `RawFsOpsM m`. -/
def touchImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

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
def atomicWriteSiblingM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

/-- Implements `FsApiM.atomicWriteBytes` cleanly over raw filesystem ops. -/
def atomicWriteBytesImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

private def atomicWriteTextImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
    (path content : String) : m (Except FsError Unit) :=
  atomicWriteBytesImplM ops path content.toUTF8

private def walkGoM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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

/-- Generic `walk` implementation over `RawFsOpsM m`. -/
def walkImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
    (root : String) : m (Except FsError (Array WalkEntry)) := do
  match ← ops.stat true root with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }
    walkGoM ops root "." #[] 4096

private def globImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
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
      | .ok matched => return .ok (matched.qsort (· < ·))

private def rglobImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
    (root pattern : String) : m (Except FsError (Array String)) :=
  let fullPat := if pattern == "**" || pattern.startsWith "**/" then pattern else "**/" ++ pattern
  globImplM ops root fullPat

/-- Generic `readText` implementation over `RawFsOpsM m`. -/
def readTextImplM {m : Type → Type} [Monad m] (ops : RawFsOpsM m)
    (path : String) : m (Except FsError String) := do
  match ← ops.readBytes path with
  | .error e => return .error e
  | .ok bs =>
    match String.fromUTF8? bs with
    | some s => return .ok s
    | none => return .error { kind := .invalidInput, path := some path, message := s!"invalid UTF-8 in file: {path}" }

/-- Run `action` under `handle`, always calling `ops.releaseLock handle` afterward. -/
def bracketLockM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawFsOpsM m) {α : Type} (handle : LockHandle)
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
    (ops : RawFsOpsM m) {α : Type} (path : String) (mode : LockMode)
    (createIfMissing : Bool) (action : m (Except FsError α)) : m (Except FsError α) := do
  match ← ops.acquireLock path mode createIfMissing false with
  | .error e => return .error e
  | .ok handle => bracketLockM ops handle action

/-- Try non-blocking `mode` lock on `path`; return `.ok none` on `.wouldBlock`, else run `action`. -/
def tryWithFileLockImplM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawFsOpsM m) {α : Type} (path : String) (mode : LockMode)
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

/-- Build a generic `FsApiM m` from injected single-step `RawFsOpsM m` primitives. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] (ops : RawFsOpsM m) : FsApiM m :=
  { join := join
    joinMany := joinMany
    normPath := normPath
    parent := parent
    name := name
    stem := stem
    suffix := suffix
    suffixes := suffixes
    withName := withName
    withSuffix := withSuffix
    isAbsolute := isAbsolute
    relativeTo := relativeTo
    mapRawError := ops.mapRawError
    readText := readTextImplM ops
    writeText := fun p c => ops.writeBytes p c.toUTF8
    appendText := ops.appendText
    readBytes := ops.readBytes
    writeBytes := ops.writeBytes
    atomicWriteBytes := atomicWriteBytesImplM ops
    atomicWriteText := atomicWriteTextImplM ops
    touch := touchImplM ops
    mkdir := mkdirImplM ops
    unlink := unlinkImplM ops
    rmdir := ops.removeDir
    rmtree := rmtreeImplM ops
    rename := ops.rename
    copyFile := copyFileImplM ops
    copyTree := copyTreeImplM ops
    pathExists := fun p => do
      match ← ops.stat true p with
      | .ok _ => return .ok true
      | .error _ => return .ok false
    isFile := fun p => do
      match ← ops.stat true p with
      | .ok st => return .ok (st.kind == .file)
      | .error _ => return .ok false
    isDir := fun p => do
      match ← ops.stat true p with
      | .ok st => return .ok (st.kind == .dir)
      | .error _ => return .ok false
    isSymlink := fun p => do
      match ← ops.stat false p with
      | .ok st => return .ok (st.kind == .symlink)
      | .error _ => return .ok false
    stat := ops.stat true
    lstat := ops.stat false
    chmod := ops.chmod
    symlink := ops.symlink
    readLink := ops.readLink
    resolve := ops.realPath
    cwd := ops.cwd
    listDir := listDirSortedM ops
    walk := walkImplM ops
    glob := globImplM ops
    rglob := rglobImplM ops
    withFileLock := withFileLockImplM ops
    tryWithFileLock := tryWithFileLockImplM ops }

/-- Execute `action` and unconditionally close `dh`, preserving `action`'s return value. -/
def bracketCloseDirM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (dh : DirHandle) (action : m α) : m α := do
  let (res, _) ← tryFinally' action (fun _ => ops.closeDir dh)
  pure res

/-- Execute `action` while holding `lockHandle`, always releasing `lockHandle` afterward. -/
def bracketDirLockM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (lockHandle : LockHandle) (action : m (Except FsError α)) :
    m (Except FsError α) := do
  let (actRes, relRes) ← tryFinally' action (fun _ => ops.releaseLock lockHandle)
  match actRes with
  | .error e => pure (.error e)
  | .ok a =>
    match relRes with
    | .ok () => pure (.ok a)
    | .error re => pure (.error re)

/-- Descend from open handle `cur` through `segs`, passing the reached handle to `act` and always closing every non-root intermediate handle (`isRoot = false`). -/
def walkDescendAuxM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (isRoot : Bool) (cur : DirHandle) :
    List EntryName → (DirHandle → m (Except FsError α)) → m (Except FsError α)
  | [], act =>
    if isRoot then
      act cur
    else
      bracketCloseDirM ops cur (act cur)
  | seg :: rest, act => do
    let rNext ←
      if isRoot then
        ops.openDirAt cur seg
      else
        bracketCloseDirM ops cur (ops.openDirAt cur seg)
    match rNext with
    | .error e => pure (.error e)
    | .ok nextDh => walkDescendAuxM ops false nextDh rest act

/-- Descend through `segs` from root directory handle `dh` using `O(1)` open handles and closing every handle opened during descent. -/
def walkDescendM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (dh : DirHandle) (segs : List EntryName)
    (act : DirHandle → m (Except FsError α)) : m (Except FsError α) :=
  walkDescendAuxM ops true dh segs act

/-- Ensure intermediate parent directories exist (`0o755`) along `segs` without following symlinks, then run `leafAct` on the final parent handle. -/
def mkdirWalkM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (isRoot : Bool) (cur : DirHandle) :
    List EntryName → (DirHandle → m (Except FsError Unit)) → m (Except FsError Unit)
  | [], leafAct =>
    if isRoot then
      leafAct cur
    else
      bracketCloseDirM ops cur (leafAct cur)
  | seg :: rest, leafAct => do
    let step : m (Except FsError DirHandle) := do
      match ← ops.openDirAt cur seg with
      | .ok nextDh => pure (.ok nextDh)
      | .error e =>
        if e.kind == .notFound then
          match ← ops.createDirAt cur seg with
          | .ok () => ops.openDirAt cur seg
          | .error ce =>
            if ce.kind == .alreadyExists then ops.openDirAt cur seg
            else pure (.error ce)
        else
          pure (.error e)
    let rNext ←
      if isRoot then
        step
      else
        bracketCloseDirM ops cur step
    match rNext with
    | .error e => pure (.error e)
    | .ok nextDh => mkdirWalkM ops false nextDh rest leafAct

/-- Retry temporary sibling creation up to `attempts` times on `.alreadyExists`, atomically rename onto `leaf`, and clean up the temporary file on rename failure. -/
def atomicWriteAtAuxM {m : Type → Type} [Monad m] (ops : RawDirOpsM m)
    (parDh : DirHandle) (leaf : EntryName) (bytes : ByteArray) : Nat → m (Except FsError Unit)
  | 0 =>
    pure (.error { kind := .alreadyExists, path := some leaf.val, message := "temporary file name collision limit exceeded" })
  | attempts + 1 => do
    let tmp ← ops.freshTempName
    match ← ops.createFileAt parDh tmp bytes with
    | .ok () =>
      match ← ops.renameAt parDh tmp parDh leaf with
      | .ok () => pure (.ok ())
      | .error e =>
        let _ ← ops.unlinkAt parDh tmp false
        pure (.error e)
    | .error e =>
      if e.kind == .alreadyExists && attempts > 0 then
        atomicWriteAtAuxM ops parDh leaf bytes attempts
      else
        pure (.error e)

/-- Sort immediate `EntryName` entries lexicographically ascending. -/
@[reducible] def sortEntryNames (names : Array EntryName) : List EntryName :=
  names.toList.mergeSort (fun a b => a.val ≤ b.val)

/-- Classify sorted child names under `dirDh` via `lstatAt` into directory names and non-directory filenames without descending into symlinks. -/
def classifyChildrenM {m : Type → Type} [Monad m] (ops : RawDirOpsM m) (dirDh : DirHandle) :
    List EntryName → List EntryName → List String → m (Except FsError (List EntryName × List String))
  | [], dirsAcc, filesAcc => pure (.ok (dirsAcc.reverse, filesAcc.reverse))
  | n :: rest, dirsAcc, filesAcc => do
    match ← ops.lstatAt dirDh n with
    | .error e => pure (.error e)
    | .ok info =>
      if info.kind == .dir then
        classifyChildrenM ops dirDh rest (n :: dirsAcc) filesAcc
      else
        classifyChildrenM ops dirDh rest dirsAcc (n.val :: filesAcc)

mutual
  /-- Traverse sorted subdirectories in pre-order DFS starting from `(relSegs, relLabel)`. -/
  def walkChildrenM {m : Type → Type} [Monad m] [MonadFinally m]
      (ops : RawDirOpsM m) (rootDh : DirHandle) (relSegs : List EntryName)
      (relLabel : String) (fuel : Nat) (acc : Array WalkEntry) :
      List EntryName → m (Except FsError (Array WalkEntry))
    | [] => pure (.ok acc)
    | d :: rest => do
      let nextLabel := if relLabel == "." then d.val else relLabel ++ "/" ++ d.val
      match ← walkRecM ops rootDh (relSegs ++ [d]) nextLabel acc fuel with
      | .error e => pure (.error e)
      | .ok acc' => walkChildrenM ops rootDh relSegs relLabel fuel acc' rest

  /-- Bounded pre-order directory walk using `O(1)` open handles and `fuel` depth limit. -/
  def walkRecM {m : Type → Type} [Monad m] [MonadFinally m]
      (ops : RawDirOpsM m) (rootDh : DirHandle)
      (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) :
      Nat → m (Except FsError (Array WalkEntry))
    | 0 =>
      pure (.error { kind := .ioError, path := some relLabel, message := s!"maximum directory depth exceeded: {relLabel}" })
    | fuel + 1 => do
      let rRead ← walkDescendM ops rootDh relSegs fun dirDh => do
        match ← ops.readDirAt dirDh with
        | .error e => pure (.error e)
        | .ok rawNames => classifyChildrenM ops dirDh (sortEntryNames rawNames) [] []
      match rRead with
      | .error e => pure (.error e)
      | .ok (dirs, files) =>
        let entry : WalkEntry := {
          root := relLabel
          dirs := (dirs.map (·.val)).toArray
          files := files.toArray }
        walkChildrenM ops rootDh relSegs relLabel fuel (acc.push entry) dirs
end

/-- Unlink leading non-directory entries in `items` while holding one open directory handle, stopping before the first directory child `d` and returning remaining items so `dirDh` is closed before recursing. -/
def rmtreeNonDirPrefixM {m : Type → Type} [Monad m] (ops : RawDirOpsM m) (dirDh : DirHandle) :
    List EntryName → m (Except FsError (Option (EntryName × List EntryName)))
  | [] => pure (.ok none)
  | c :: rest => do
    match ← ops.lstatAt dirDh c with
    | .error e =>
      if e.kind == .notFound then rmtreeNonDirPrefixM ops dirDh rest
      else pure (.error e)
    | .ok info =>
      if info.kind == .dir then
        pure (.ok (some (c, rest)))
      else
        match ← ops.unlinkAt dirDh c false with
        | .ok () => rmtreeNonDirPrefixM ops dirDh rest
        | .error e =>
          if e.kind == .notFound then rmtreeNonDirPrefixM ops dirDh rest
          else pure (.error e)

/-- Process remaining entries inside directory `dirSegs` in bounded batches, closing open directory handles before calling `subDirFn` on any child directory. -/
def rmtreeProcessM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (rootDh : DirHandle) (dirSegs : List EntryName)
    (subDirFn : EntryName → m (Except FsError Unit)) :
    Nat → List EntryName → m (Except FsError Unit)
  | _, [] => pure (.ok ())
  | 0, _ => pure (.ok ())
  | steps + 1, items => do
    let rBatch ← walkDescendM ops rootDh dirSegs fun dirDh =>
      rmtreeNonDirPrefixM ops dirDh items
    match rBatch with
    | .error e => pure (.error e)
    | .ok none => pure (.ok ())
    | .ok (some (subDir, rest)) => do
      match ← subDirFn subDir with
      | .error e => pure (.error e)
      | .ok () => rmtreeProcessM ops rootDh dirSegs subDirFn steps rest

/-- Recursively delete child directory `leaf` under `parSegs` with bounded recursion depth `fuel` and `O(1)` open handles. -/
def rmtreeDirAtM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (rootDh : DirHandle) (parSegs : List EntryName) (leaf : EntryName) :
    Nat → m (Except FsError Unit)
  | 0 =>
    pure (.error { kind := .ioError, path := some leaf.val, message := s!"maximum directory recursion depth exceeded: {leaf.val}" })
  | fuel + 1 => do
    let dirSegs := parSegs ++ [leaf]
    let rRead ← walkDescendM ops rootDh dirSegs fun dirDh => ops.readDirAt dirDh
    match rRead with
    | .error e => pure (.error e)
    | .ok rawNames =>
      let sorted := sortEntryNames rawNames
      match ← rmtreeProcessM ops rootDh dirSegs (fun subDir => rmtreeDirAtM ops rootDh dirSegs subDir fuel) sorted.length sorted with
      | .error e => pure (.error e)
      | .ok () => walkDescendM ops rootDh parSegs fun parDh => ops.unlinkAt parDh leaf true

/-- Implement `SubtreeM m` operations confined to open root directory handle `dh`. -/
def subtreeOpsM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (dh : DirHandle) : SubtreeM m :=
  { lstat := fun rel =>
      match splitLastAux rel.segments [] with
      | none => ops.fstatDir dh
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.lstatAt parDh leaf
    readRegular := fun rel =>
      match splitLastAux rel.segments [] with
      | none => do
        match ← ops.fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind == .dir then
            pure (.error { kind := .isADirectory, path := some ".", message := "is a directory: ." })
          else
            pure (.error { kind := .notADirectory, path := some ".", message := "not a directory: ." })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.readRegularAt parDh leaf
    atomicWriteBytes := fun rel bytes =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot atomically write subtree root" })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => atomicWriteAtAuxM ops parDh leaf bytes 16
    mkdir := fun rel parents existOk =>
      match splitLastAux rel.segments [] with
      | none => do
        match ← ops.fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind != .dir then
            pure (.error { kind := .notADirectory, path := some ".", message := "not a directory: ." })
          else if existOk then
            pure (.ok ())
          else
            pure (.error { kind := .alreadyExists, path := some ".", message := "directory already exists: ." })
      | some (pre, leaf) =>
        let leafAct : DirHandle → m (Except FsError Unit) := fun parDh => do
          match ← ops.createDirAt parDh leaf with
          | .ok () => pure (.ok ())
          | .error e =>
            if existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
              match ← ops.lstatAt parDh leaf with
              | .error _ => pure (.error e)
              | .ok info =>
                if info.kind == .dir then pure (.ok ())
                else if e.kind == .alreadyExists then pure (.error e)
                else pure (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" })
            else
              pure (.error e)
        if parents then
          mkdirWalkM ops true dh pre leafAct
        else
          walkDescendM ops dh pre leafAct
    unlink := fun rel missingOk =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot unlink subtree root" })
      | some (pre, leaf) => do
        match ← walkDescendM ops dh pre fun parDh => ops.unlinkAt parDh leaf false with
        | .ok () => pure (.ok ())
        | .error e =>
          if e.kind == .notFound && missingOk then pure (.ok ())
          else pure (.error e)
    rmdir := fun rel =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot remove subtree root" })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.unlinkAt parDh leaf true
    rmtree := fun rel ignoreMissing =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot recursively remove subtree root" })
      | some (pre, leaf) => do
        let rLeaf ← walkDescendM ops dh pre fun parDh => ops.lstatAt parDh leaf
        match rLeaf with
        | .error e =>
          if e.kind == .notFound && ignoreMissing then pure (.ok ())
          else pure (.error e)
        | .ok info =>
          if info.kind != .dir then
            pure (.error { kind := .notADirectory, path := some leaf.val, message := s!"not a directory: {leaf.val}" })
          else
            rmtreeDirAtM ops dh pre leaf 4096
    symlink := fun target rel =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot replace subtree root with symlink" })
      | some (pre, leaf) =>
        if target.isEmpty || Char.ofNat 0 ∈ target.toList then
          pure (.error { kind := .invalidInput, path := some target, message := "invalid symlink target" })
        else
          walkDescendM ops dh pre fun parDh => ops.symlinkAt target parDh leaf
    listDir := fun rel =>
      walkDescendM ops dh rel.segments fun dirDh => do
        match ← ops.readDirAt dirDh with
        | .error e => pure (.error e)
        | .ok names => pure (.ok (sortEntryNames names).toArray)
    walk := fun rel =>
      walkRecM ops dh rel.segments "." #[] 4096
    withFileLock := fun {_α} rel mode createIfMissing action =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot lock subtree root" })
      | some (pre, leaf) => do
        let rLock ← walkDescendM ops dh pre fun parDh =>
          ops.acquireLockAt parDh leaf mode createIfMissing false
        match rLock with
        | .error e => pure (.error e)
        | .ok lockHandle =>
          bracketDirLockM ops lockHandle action
    tryWithFileLock := fun {_α} rel mode createIfMissing action =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot lock subtree root" })
      | some (pre, leaf) => do
        let rLock ← walkDescendM ops dh pre fun parDh =>
          ops.acquireLockAt parDh leaf mode createIfMissing true
        match rLock with
        | .error e =>
          if e.kind == .wouldBlock then pure (.ok none)
          else pure (.error e)
        | .ok lockHandle =>
          bracketDirLockM ops lockHandle do
            match ← action with
            | .ok a => pure (.ok (some a))
            | .error e => pure (.error e) }

/-- Open `rootPath` once via `ops.openDir`, validate it is a directory with owner read+search (`0o500`), execute `action`, and always close the handle on exit. -/
def withSubtreeM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) (rootPath : String)
    (action : SubtreeM m → m (Except FsError α)) : m (Except FsError α) := do
  match ← ops.openDir rootPath with
  | .error e => pure (.error e)
  | .ok dh =>
    bracketCloseDirM ops dh do
      match ← ops.fstatDir dh with
      | .error e => pure (.error e)
      | .ok info =>
        if info.kind != .dir then
          pure (.error { kind := .notADirectory, path := some rootPath, message := s!"not a directory: {rootPath}" })
        else if (info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0 then
          pure (.error { kind := .permissionDenied, path := some rootPath, message := s!"permission denied: {rootPath}" })
        else
          action (subtreeOpsM ops dh)

/-- Build a `SubtreeOpenerM m` backed by `ops`. -/
def mkSubtreeOpenerM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawDirOpsM m) : SubtreeOpenerM m :=
  { withSubtree := withSubtreeM ops }

end LeanSwe.Fs.Internal

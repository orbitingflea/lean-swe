import LeanSwe.Fs.Types
import LeanSwe.Glob.Interface

/-!
# Fs Package Internal Implementation

Implements `LeanSwe.Fs.FsApi` with Python-parity path manipulation, error
normalization, `IO.FS` wrappers, `LeanSwe.Glob`-powered tree walks, and an
injected `PosixRawOps` bridge for POSIX calls implemented in `c/fs_shim.c`.
Placed under `namespace LeanSwe.Fs.Internal` with zero `@[extern]` declarations.
-/

namespace LeanSwe.Fs.Internal

open LeanSwe.Fs (FsErrorKind FsError EntryKind FileStat WalkEntry FsRawError FsApi)

/-- Audited POSIX FFI operations injected by `LeanSwe.Fs.Interface`. -/
structure PosixRawOps where
  /-- Set file mode bits (`chmod`). -/
  chmod : String → UInt32 → IO Unit
  /-- Create symbolic link `(target, linkPath)`. -/
  symlink : String → String → IO Unit
  /-- Read symbolic link target path. -/
  readLink : String → IO String
  /-- Read POSIX mode bits (`st_mode & 0o7777`), optionally following symlinks. -/
  statMode : String → Bool → IO UInt32

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Classify common Linux/macOS `errno` codes used across `otherError` and `inappropriateType`. -/
def classifyErrno (code : UInt32) (defaultKind : FsErrorKind) : FsErrorKind :=
  match code.toNat with
  | 1 | 13 => .permissionDenied
  | 2 => .notFound
  | 17 => .alreadyExists
  | 20 => .notADirectory
  | 21 => .isADirectory
  | 22 | 36 => .invalidInput
  | 39 | 66 => .notEmpty
  | _ => defaultKind

/-- Convert a pure `FsRawError` record into a normalized `FsError` with non-empty message. -/
def mapRawError : FsRawError → FsError
  | .noFileOrDirectory path code detail =>
    { kind := .notFound
      path := some path
      errnoCode := some code
      message := nonEmptyMsg s!"no such file or directory: {path}" detail }
  | .alreadyExists path? code detail =>
    { kind := .alreadyExists
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "file or directory already exists" detail }
  | .permissionDenied path? code detail =>
    { kind := .permissionDenied
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "permission denied" detail }
  | .inappropriateType path? code detail =>
    { kind := classifyErrno code .ioError
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "inappropriate file type" detail }
  | .invalidArgument path? code detail =>
    { kind := .invalidInput
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "invalid argument" detail }
  | .unsupportedOperation code detail =>
    { kind := .unsupported
      path := none
      errnoCode := some code
      message := nonEmptyMsg "unsupported filesystem operation" detail }
  | .otherError code detail =>
    { kind := classifyErrno code .ioError
      path := none
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      path := none
      errnoCode := none
      message := nonEmptyMsg "filesystem error" detail }

/-- Convert a Lean `IO.Error` into `FsRawError`. -/
def ioErrorToRaw (fallbackPath : Option String) : IO.Error → FsRawError
  | .noFileOrDirectory p code detail => .noFileOrDirectory p code detail
  | .alreadyExists p? code detail => .alreadyExists (p? <|> fallbackPath) code detail
  | .permissionDenied p? code detail => .permissionDenied (p? <|> fallbackPath) code detail
  | .inappropriateType p? code detail => .inappropriateType (p? <|> fallbackPath) code detail
  | .invalidArgument p? code detail => .invalidArgument (p? <|> fallbackPath) code detail
  | .unsupportedOperation code detail => .unsupportedOperation code detail
  | .unsatisfiedConstraints code detail => .otherError code detail
  | .illegalOperation code detail => .otherError code detail
  | .resourceBusy code detail => .otherError code detail
  | .resourceVanished code detail => .otherError code detail
  | .hardwareFault code detail => .otherError code detail
  | .protocolError code detail => .otherError code detail
  | .timeExpired code detail => .otherError code detail
  | .interrupted p code detail => .otherError code s!"{p}: {detail}"
  | .resourceExhausted p? code detail => .invalidArgument (p? <|> fallbackPath) code detail
  | .noSuchThing p? _ _ => .noFileOrDirectory (p?.or fallbackPath |>.getD "") 2 "no such file or directory"
  | .unexpectedEof => .userError "unexpected end of file"
  | .otherError code detail => .otherError code detail
  | .userError detail => .userError detail

/-- Normalize an `IO.Error` into an `FsError`, preserving `fallbackPath` if missing. -/
def mapIoError (fallbackPath : Option String) (err : IO.Error) : FsError :=
  let mapped := mapRawError (ioErrorToRaw fallbackPath err)
  { mapped with path := mapped.path <|> fallbackPath }

/-- Run an `IO α` action, capturing exceptions into `Except FsError α`. -/
def catchFs {α : Type} (path? : Option String) (act : IO α) : IO (Except FsError α) := do
  try
    return .ok (← act)
  catch err =>
    return .error (mapIoError path? err)

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
  else if base.endsWith "/" then base ++ sub
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
    if n.endsWith "." then
      #[]
    else
      let stripped := String.ofList (n.toList.dropWhile (· == '.'))
      match stripped.splitOn "." with
      | [] | [_] => #[]
      | _ :: exts => (exts.map ("." ++ ·)).toArray

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

private def toEntryKind : IO.FS.FileType → EntryKind
  | .file => .file
  | .dir => .dir
  | .symlink => .symlink
  | .other => .other

private def statImpl (posix : PosixRawOps) (follow : Bool) (path : String) :
    IO (Except FsError FileStat) :=
  catchFs (some path) do
    let fp := System.FilePath.mk path
    let md ← if follow then fp.metadata else fp.symlinkMetadata
    let mode ← posix.statMode path follow
    return {
      kind := toEntryKind md.type
      byteSize := md.byteSize.toNat
      mode := mode.toNat
      modifiedSec := md.modified.sec
      modifiedNsec := md.modified.nsec.toNat
      accessedSec := md.accessed.sec
      accessedNsec := md.accessed.nsec.toNat }

private def listDirSorted (path : String) : IO (Except FsError (Array String)) :=
  catchFs (some path) do
    let entries ← (System.FilePath.mk path).readDir
    let names := entries.map (·.fileName)
    return names.qsort (· < ·)

private def mkdirImpl (posix : PosixRawOps) (path : String) (parents existOk : Bool) :
    IO (Except FsError Unit) := do
  let fp := System.FilePath.mk path
  match ← statImpl posix false path with
  | .ok st =>
    if existOk && st.kind == .dir then
      return .ok ()
    else if existOk && st.kind == .symlink && (← fp.isDir) then
      return .ok ()
    else
      return .error { kind := .alreadyExists, path := some path, message := s!"path already exists: {path}" }
  | .error e =>
    if e.kind != .notFound then
      return .error e
    else if parents then
      catchFs (some path) (IO.FS.createDirAll fp)
    else
      catchFs (some path) (IO.FS.createDir fp)

private def unlinkImpl (posix : PosixRawOps) (path : String) (missingOk : Bool) :
    IO (Except FsError Unit) := do
  match ← statImpl posix false path with
  | .error e =>
    if e.kind == .notFound && missingOk then
      return .ok ()
    else
      return .error e
  | .ok st =>
    if st.kind == .dir then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else
      catchFs (some path) (IO.FS.removeFile (System.FilePath.mk path))

private def rmdirImpl (path : String) : IO (Except FsError Unit) :=
  catchFs (some path) (IO.FS.removeDir (System.FilePath.mk path))

private def rmtreeImpl (posix : PosixRawOps) (path : String) (ignoreMissing : Bool) :
    IO (Except FsError Unit) := do
  match ← statImpl posix false path with
  | .error e =>
    if e.kind == .notFound && ignoreMissing then
      return .ok ()
    else
      return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }
    else
      catchFs (some path) (IO.FS.removeDirAll (System.FilePath.mk path))

private def copyFileImpl (posix : PosixRawOps) (src dst : String) : IO (Except FsError Unit) := do
  match ← statImpl posix true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind == .dir then
      return .error { kind := .isADirectory, path := some src, message := s!"source is a directory: {src}" }
    let bytesRes ← catchFs (some src) (IO.FS.readBinFile (System.FilePath.mk src))
    match bytesRes with
    | .error e => return .error e
    | .ok bytes => catchFs (some dst) (IO.FS.writeBinFile (System.FilePath.mk dst) bytes)

private partial def resolveApproxGo (cur : String) (tail : List String) : IO String := do
  try
    let rp ← IO.FS.realPath (System.FilePath.mk cur)
    return tail.foldl join rp.toString
  catch _ =>
    match parent cur, name cur with
    | some par, some seg => resolveApproxGo par (seg :: tail)
    | _, _ => return tail.foldl join cur

private partial def copyTreeGo (posix : PosixRawOps) (src dst : String) (dirsExistOk : Bool)
    (visited : List String) : IO (Except FsError Unit) := do
  match ← statImpl posix true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
    let canonRes ← catchFs (some src) (IO.FS.realPath (System.FilePath.mk src))
    let canon ← match canonRes with
      | .error e => return .error e
      | .ok rp => pure rp.toString
    if canon ∈ visited then
      return .error { kind := .invalidInput, path := some src, message := s!"symlink directory loop: {src}" }
    let visited' := canon :: visited
    match ← listDirSorted src with
    | .error e => return .error e
    | .ok names =>
      match ← mkdirImpl posix dst true dirsExistOk with
      | .error e => return .error e
      | .ok () =>
        for n in names do
          let sChild := join src n
          let dChild := join dst n
          match ← statImpl posix true sChild with
          | .error e => return .error e
          | .ok childSt =>
            if childSt.kind == .dir then
              match ← copyTreeGo posix sChild dChild dirsExistOk visited' with
              | .error e => return .error e
              | .ok () => pure ()
            else
              match ← copyFileImpl posix sChild dChild with
              | .error e => return .error e
              | .ok () => pure ()
        return .ok ()

private def copyTreeImpl (posix : PosixRawOps) (src dst : String) (dirsExistOk : Bool) :
    IO (Except FsError Unit) := do
  match ← statImpl posix true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
    match ← catchFs (some src) (IO.FS.realPath (System.FilePath.mk src)) with
    | .error e => return .error e
    | .ok srcRp =>
      let srcCanon := srcRp.toString
      let dstAbs ←
        if isAbsolute dst then
          pure (normPath dst)
        else do
          let cwdDir ← catchFs none IO.currentDir
          match cwdDir with
          | .error _ => pure (normPath dst)
          | .ok d => pure (normPath (join d.toString dst))
      let dstCanon ← resolveApproxGo dstAbs []
      if dstCanon == srcCanon || srcCanon == "/" || dstCanon.startsWith (srcCanon ++ "/") then
        return .error { kind := .invalidInput, path := some dst, message := s!"cannot copy directory into itself: {dst}" }
      copyTreeGo posix src dst dirsExistOk []

private def touchImpl (posix : PosixRawOps) (path : String) (existOk : Bool) :
    IO (Except FsError Unit) := do
  let fp := System.FilePath.mk path
  match ← statImpl posix false path with
  | .ok st =>
    if !existOk then
      return .error { kind := .alreadyExists, path := some path, message := s!"file already exists: {path}" }
    else if st.kind == .dir || (st.kind == .symlink && (← fp.isDir)) then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else
      catchFs (some path) do
        let h ← IO.FS.Handle.mk fp .append
        h.flush
  | .error e =>
    if e.kind == .notFound then
      catchFs (some path) (IO.FS.writeFile fp "")
    else
      return .error e

private def atomicWriteTextImpl (path content : String) : IO (Except FsError Unit) := do
  let parentDir := (parent path).getD "."
  let baseName := (name path).getD "tmp"
  let nonce ← IO.monoNanosNow
  let tmpPath := join parentDir s!".{baseName}.tmp.{nonce}"
  match ← catchFs (some tmpPath) (IO.FS.writeFile (System.FilePath.mk tmpPath) content) with
  | .error e => return .error e
  | .ok () =>
    match ← catchFs (some path) (IO.FS.rename (System.FilePath.mk tmpPath) (System.FilePath.mk path)) with
    | .error e =>
      try IO.FS.removeFile (System.FilePath.mk tmpPath) catch _ => pure ()
      return .error e
    | .ok () => return .ok ()

private partial def walkGo (root relRoot : String) (acc : Array WalkEntry) :
    IO (Except FsError (Array WalkEntry)) := do
  let fullDir := if relRoot == "." then root else join root relRoot
  match ← listDirSorted fullDir with
  | .error e => return .error e
  | .ok names =>
    let mut dirs : Array String := #[]
    let mut files : Array String := #[]
    for n in names do
      let childFull := join fullDir n
      let isSubDir ←
        try
          let md ← (System.FilePath.mk childFull).symlinkMetadata
          pure (md.type == .dir)
        catch _ =>
          pure false
      if isSubDir then
        dirs := dirs.push n
      else
        files := files.push n
    let mut out := acc.push { root := relRoot, dirs, files }
    for d in dirs do
      let nextRel := if relRoot == "." then d else join relRoot d
      match ← walkGo root nextRel out with
      | .error e => return .error e
      | .ok out' => out := out'
    return .ok out

private def walkImpl (root : String) : IO (Except FsError (Array WalkEntry)) := do
  match ← catchFs (some root) ((System.FilePath.mk root).metadata) with
  | .error e => return .error e
  | .ok md =>
    if md.type != .dir then
      return .error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }
    walkGo root "." #[]

private def globImpl (root pattern : String) : IO (Except FsError (Array String)) := do
  match LeanSwe.Glob.validate pattern with
  | .error e => return .error (mapGlobError pattern e)
  | .ok () =>
    match ← walkImpl root with
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

private def rglobImpl (root pattern : String) : IO (Except FsError (Array String)) :=
  let fullPat := if pattern == "**" || pattern.startsWith "**/" then pattern else "**/" ++ pattern
  globImpl root fullPat

/-- Build the concrete `FsApi` from injected POSIX C-ABI hooks. -/
def mkApi (posix : PosixRawOps) : FsApi :=
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
    mapRawError := mapRawError
    readText := fun p => catchFs (some p) (IO.FS.readFile (System.FilePath.mk p))
    writeText := fun p c => catchFs (some p) (IO.FS.writeFile (System.FilePath.mk p) c)
    appendText := fun p c => catchFs (some p) do
      let h ← IO.FS.Handle.mk (System.FilePath.mk p) .append
      h.putStr c
      h.flush
    readBytes := fun p => catchFs (some p) (IO.FS.readBinFile (System.FilePath.mk p))
    writeBytes := fun p b => catchFs (some p) (IO.FS.writeBinFile (System.FilePath.mk p) b)
    atomicWriteText := atomicWriteTextImpl
    touch := touchImpl posix
    mkdir := mkdirImpl posix
    unlink := unlinkImpl posix
    rmdir := rmdirImpl
    rmtree := rmtreeImpl posix
    rename := fun s d => catchFs (some s) (IO.FS.rename (System.FilePath.mk s) (System.FilePath.mk d))
    copyFile := copyFileImpl posix
    copyTree := copyTreeImpl posix
    pathExists := fun p => catchFs (some p) ((System.FilePath.mk p).pathExists)
    isFile := fun p => catchFs (some p) do
      match ← catchFs (some p) ((System.FilePath.mk p).metadata) with
      | .error _ => return false
      | .ok md => return md.type == .file
    isDir := fun p => catchFs (some p) ((System.FilePath.mk p).isDir)
    isSymlink := fun p => catchFs (some p) do
      match ← catchFs (some p) ((System.FilePath.mk p).symlinkMetadata) with
      | .error _ => return false
      | .ok md => return md.type == .symlink
    stat := statImpl posix true
    lstat := statImpl posix false
    chmod := fun p mode => catchFs (some p) (posix.chmod p (UInt32.ofNat mode))
    symlink := fun t l => catchFs (some l) (posix.symlink t l)
    readLink := fun p => catchFs (some p) (posix.readLink p)
    resolve := fun p => catchFs (some p) do
      let rp ← IO.FS.realPath (System.FilePath.mk p)
      return rp.toString
    cwd := catchFs none do
      let d ← IO.currentDir
      return d.toString
    listDir := listDirSorted
    walk := walkImpl
    glob := globImpl
    rglob := rglobImpl }

/-- Temporary directory bracket modeled after Python `tempfile.TemporaryDirectory`. -/
def withTempDir {α : Type} (f : String → IO (Except FsError α)) : IO (Except FsError α) := do
  match ← catchFs none (IO.FS.withTempDir fun dir => f dir.toString) with
  | .error e => return .error e
  | .ok inner => return inner

end LeanSwe.Fs.Internal

namespace LeanSwe.Fs

/-- Classification of filesystem and path errors modeled after Python `OSError` subclasses. -/
inductive FsErrorKind where
  /-- Target path or parent directory does not exist (`FileNotFoundError`). -/
  | notFound
  /-- Target path already exists (`FileExistsError`). -/
  | alreadyExists
  /-- Insufficient permissions or disallowed operation (`PermissionError`). -/
  | permissionDenied
  /-- Expected a regular file or non-directory, found a directory (`IsADirectoryError`). -/
  | isADirectory
  /-- Expected a directory, found a non-directory (`NotADirectoryError`). -/
  | notADirectory
  /-- Directory is not empty on `rmdir` (`ENOTEMPTY`). -/
  | notEmpty
  /-- Invalid path, suffix, filename, glob pattern, or encoding (`ValueError` / `EINVAL`). -/
  | invalidInput
  /-- Operation not supported on the current platform or filesystem. -/
  | unsupported
  /-- Non-blocking `flock` would block because a conflicting lock is held (`EWOULDBLOCK` / `EAGAIN`). -/
  | wouldBlock
  /-- Other OS-level I/O failure (`OSError`). -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Advisory `flock(2)` lock mode. -/
inductive LockMode where
  /-- Shared (read) advisory lock (`LOCK_SH`). -/
  | shared
  /-- Exclusive (write) advisory lock (`LOCK_EX`). -/
  | exclusive
  deriving Repr, BEq, DecidableEq

/-- Typed filesystem error returned by `LeanSwe.Fs` operations. -/
structure FsError where
  /-- Machine-checkable error category. -/
  kind : FsErrorKind
  /-- Path associated with the error, when available. -/
  path : Option String := none
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Directory entry file type returned by `stat` and `lstat`. -/
inductive EntryKind where
  /-- Regular file. -/
  | file
  /-- Directory. -/
  | dir
  /-- Symbolic link (visible under `lstat`). -/
  | symlink
  /-- Socket, FIFO, device, or other special entry. -/
  | other
  deriving Repr, BEq, DecidableEq

/-- File status metadata modeled after Python `os.stat_result`. -/
structure FileStat where
  /-- Kind of filesystem entry. -/
  kind : EntryKind
  /-- Size in bytes. -/
  byteSize : Nat
  /-- POSIX permission bits (`st_mode & 0o7777`). -/
  mode : Nat
  /-- Last modification timestamp (seconds). -/
  modifiedSec : Int
  /-- Last modification timestamp (nanoseconds). -/
  modifiedNsec : Nat
  /-- Last access timestamp (seconds). -/
  accessedSec : Int
  /-- Last access timestamp (nanoseconds). -/
  accessedNsec : Nat
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw OS error inputs for total error-mapping specs. -/
inductive FsRawError where
  /-- Path or parent directory missing (`ENOENT`). -/
  | noFileOrDirectory (path : String) (errno : UInt32) (detail : String)
  /-- Destination already exists (`EEXIST`). -/
  | alreadyExists (path? : Option String) (errno : UInt32) (detail : String)
  /-- Permission denied (`EACCES` / `EPERM`). -/
  | permissionDenied (path? : Option String) (errno : UInt32) (detail : String)
  /-- Inappropriate file type (`EISDIR` / `ENOTDIR` / `ENOTEMPTY`). -/
  | inappropriateType (path? : Option String) (errno : UInt32) (detail : String)
  /-- Invalid argument (`EINVAL` / `ENAMETOOLONG`). -/
  | invalidArgument (path? : Option String) (errno : UInt32) (detail : String)
  /-- Unsupported platform operation. -/
  | unsupportedOperation (errno : UInt32) (detail : String)
  /-- Non-blocking `flock` contended (`EWOULDBLOCK` / `EAGAIN`). -/
  | wouldBlock (path? : Option String) (errno : UInt32) (detail : String)
  /-- Generic numeric OS error. -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic user-constructed error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Reducible `List Char` predicate checking whether `s` is a valid single entry name (non-empty, no `'/'` or NUL, not `"."` or `".."`). -/
@[reducible] def validSeg (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && !cs.contains '/' && !cs.contains (Char.ofNat 0) && cs != ['.'] && cs != ['.', '.']

/-- Validated single directory entry name (never empty, `"."`, `".."`, `'/'`, or NUL). -/
structure EntryName where
  /-- Underlying single-segment filename string. -/
  val : String
  /-- Kernel-checkable proof that `val` satisfies `validSeg`. -/
  valid : validSeg val = true

instance : BEq EntryName where
  beq a b := a.val == b.val

instance : DecidableEq EntryName
  | ⟨v1, _⟩, ⟨v2, _⟩ =>
    if h : v1 = v2 then isTrue (by subst h; rfl)
    else isFalse (fun he => h (congrArg EntryName.val he))

instance : Repr EntryName where
  reprPrec n p := Repr.addAppParen ("EntryName.lit " ++ repr n.val) p

instance : ToString EntryName where
  toString n := n.val

/-- Parse a runtime `String` into a validated `EntryName`, failing with `.invalidInput` if invalid. -/
def EntryName.parse (s : String) : Except FsError EntryName :=
  if h : validSeg s = true then
    .ok { val := s, valid := h }
  else
    .error { kind := .invalidInput, path := some s, message := s!"invalid entry name: '{s}'" }

/-- Construct a compile-time `EntryName` literal validated in the Lean kernel (`by decide +kernel`). -/
def EntryName.lit (s : String) (h : validSeg s = true := by decide +kernel) : EntryName :=
  { val := s, valid := h }

/-- Split a `List Char` on `'/'`, preserving empty segments so leading, trailing, and repeated slashes are rejected. -/
@[reducible] def splitSlashRaw : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == '/' then [] :: splitSlashRaw cs
    else
      match splitSlashRaw cs with
      | [] => [[c]]
      | seg :: rest => (c :: seg) :: rest

/-- Parse slash-split character segments into validated `EntryName` values. -/
@[reducible] def parseRelSegments (rawPath : String) : List (List Char) → Except FsError (List EntryName)
  | [] => .ok []
  | segChars :: rest =>
    let seg := String.ofList segChars
    if h : validSeg seg = true then
      match parseRelSegments rawPath rest with
      | .ok tail => .ok ({ val := seg, valid := h } :: tail)
      | .error e => .error e
    else
      .error { kind := .invalidInput, path := some rawPath, message := s!"invalid relative path segment '{seg}' in '{rawPath}'" }

/-- Validated subtree-relative path composed of zero or more `EntryName` segments (never escaping via `..` or `/`). -/
structure RelPath where
  /-- Ordered path segments relative to the opened subtree root. -/
  segments : List EntryName
  deriving Repr, BEq, DecidableEq

/-- Empty relative path referring to the opened subtree root itself. -/
def RelPath.root : RelPath :=
  { segments := [] }

/-- Return `true` iff `p` is the empty `RelPath.root`. -/
def RelPath.isEmpty (p : RelPath) : Bool :=
  p.segments.isEmpty

/-- Concatenate two `RelPath` values left-to-right. -/
def RelPath.join (a b : RelPath) : RelPath :=
  { segments := a.segments ++ b.segments }

/-- Append a single validated `EntryName` segment to `p`. -/
def RelPath.push (p : RelPath) (seg : EntryName) : RelPath :=
  { segments := p.segments ++ [seg] }

/-- Render `p` as a slash-separated relative string (`"."` for `RelPath.root`). -/
def RelPath.render (p : RelPath) : String :=
  if p.segments.isEmpty then "." else String.intercalate "/" (p.segments.map (·.val))

instance : ToString RelPath where
  toString := RelPath.render

/-- Parse a non-empty relative path string, rejecting `""`, leading `/`, trailing `/`, `//`, `.`, `..`, and NUL. -/
def RelPath.parse (s : String) : Except FsError RelPath :=
  match parseRelSegments s (splitSlashRaw s.toList) with
  | .ok segs => .ok { segments := segs }
  | .error e => .error e

/-- Parse a relative path string, mapping `"."` to `RelPath.root` (compatible with `Fs.relativeTo`). -/
def RelPath.parseRoot (s : String) : Except FsError RelPath :=
  if s == "." then .ok RelPath.root else RelPath.parse s

/-- Construct a compile-time `RelPath` literal validated in the Lean kernel (`by decide +kernel`). -/
def RelPath.lit (s : String) (h : (RelPath.parse s).isOk = true := by decide +kernel) : RelPath :=
  match hp : RelPath.parse s with
  | .ok p => p
  | .error _ => False.elim (by rw [hp] at h; cases h)

/-- Single yielded directory node from `walk` (analogous to Python `os.walk` triples). -/
structure WalkEntry where
  /-- Directory path relative to walk root (`"."` for the walk root itself). -/
  root : String
  /-- Sorted immediate child directory names. -/
  dirs : Array String
  /-- Sorted immediate child non-directory entry names. -/
  files : Array String
  deriving Repr, BEq, DecidableEq

/-- Public operations exported by `LeanSwe.Fs`, parameterized over effect monad `m`. -/
structure FsApiM (m : Type → Type) where
  /-- Join two paths using `/` (`Path.joinpath`). -/
  join : String → String → String
  /-- Join an array of path segments left-to-right. -/
  joinMany : Array String → String
  /-- Lexically normalize `.` and `..` segments and redundant `/` separators (`os.path.normpath`). -/
  normPath : String → String
  /-- Return parent directory path, or `none` when at root or single component. -/
  parent : String → Option String
  /-- Return final path component name, if present. -/
  name : String → Option String
  /-- Return final path component without its last suffix (`Path.stem`). -/
  stem : String → Option String
  /-- Return final `.ext` suffix of filename (`Path.suffix`), or `""` when none. -/
  suffix : String → String
  /-- Return all `.ext` suffixes of filename (`Path.suffixes`). -/
  suffixes : String → Array String
  /-- Replace the final path component (`Path.with_name`). -/
  withName : String → String → Except FsError String
  /-- Replace or strip the last suffix (`Path.with_suffix`). -/
  withSuffix : String → String → Except FsError String
  /-- Return `true` iff `path` begins with `/`. -/
  isAbsolute : String → Bool
  /-- Compute lexical path of `path` relative to `base` (`Path.relative_to`). -/
  relativeTo : String → String → Except FsError String
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Read entire UTF-8 text file (`Path.read_text`). -/
  readText : String → m (Except FsError String)
  /-- Write or overwrite UTF-8 text file (`Path.write_text`). -/
  writeText : String → String → m (Except FsError Unit)
  /-- Append UTF-8 text to file, creating it if absent. -/
  appendText : String → String → m (Except FsError Unit)
  /-- Read entire binary file (`Path.read_bytes`). -/
  readBytes : String → m (Except FsError ByteArray)
  /-- Write or overwrite binary file (`Path.write_bytes`). -/
  writeBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically write binary bytes via a sibling exclusive temporary file and `rename`. -/
  atomicWriteBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically write text via a sibling exclusive temporary file and `rename`. -/
  atomicWriteText : String → String → m (Except FsError Unit)
  /-- Create empty file if missing (`Path.touch`). -/
  touch : String → Bool → m (Except FsError Unit)
  /-- Create directory, optionally creating parents or succeeding if present (`Path.mkdir`). -/
  mkdir : String → Bool → Bool → m (Except FsError Unit)
  /-- Remove file or symlink (`Path.unlink`). -/
  unlink : String → Bool → m (Except FsError Unit)
  /-- Remove empty directory (`Path.rmdir`). -/
  rmdir : String → m (Except FsError Unit)
  /-- Recursively delete directory tree (`shutil.rmtree`). -/
  rmtree : String → Bool → m (Except FsError Unit)
  /-- Rename or replace file/directory (`os.replace`). -/
  rename : String → String → m (Except FsError Unit)
  /-- Copy file contents (`shutil.copyfile`). -/
  copyFile : String → String → m (Except FsError Unit)
  /-- Recursively copy directory tree (`shutil.copytree`). -/
  copyTree : String → String → Bool → m (Except FsError Unit)
  /-- Check whether `path` exists, following symlinks (`Path.exists`). -/
  pathExists : String → m (Except FsError Bool)
  /-- Check whether `path` refers to a regular file, following symlinks (`Path.is_file`). -/
  isFile : String → m (Except FsError Bool)
  /-- Check whether `path` refers to a directory, following symlinks (`Path.is_dir`). -/
  isDir : String → m (Except FsError Bool)
  /-- Check whether `path` itself is a symbolic link (`Path.is_symlink`). -/
  isSymlink : String → m (Except FsError Bool)
  /-- Inspect metadata following symlinks (`os.stat`). -/
  stat : String → m (Except FsError FileStat)
  /-- Inspect metadata without following symlinks (`os.lstat`). -/
  lstat : String → m (Except FsError FileStat)
  /-- Set POSIX permission mode bits (`os.chmod`). -/
  chmod : String → Nat → m (Except FsError Unit)
  /-- Create symbolic link at `linkPath` pointing to `target` (`os.symlink`). -/
  symlink : String → String → m (Except FsError Unit)
  /-- Read symbolic link target (`os.readlink`). -/
  readLink : String → m (Except FsError String)
  /-- Resolve symlinks and return canonical absolute path (`Path.resolve`). -/
  resolve : String → m (Except FsError String)
  /-- Return current working directory (`os.getcwd`). -/
  cwd : m (Except FsError String)
  /-- Return sorted immediate child names in directory (`os.listdir`). -/
  listDir : String → m (Except FsError (Array String))
  /-- Top-down directory walk yielding sorted children (`os.walk`). -/
  walk : String → m (Except FsError (Array WalkEntry))
  /-- Find sorted relative paths under `root` matching glob `pattern` (`Path.glob`). -/
  glob : String → String → m (Except FsError (Array String))
  /-- Recursively match glob `pattern` under `root` (`Path.rglob`). -/
  rglob : String → String → m (Except FsError (Array String))
  /-- Acquire an advisory `flock`, execute `action`, and release the lock on exit. -/
  withFileLock : {α : Type} → String → LockMode → Bool → m (Except FsError α) → m (Except FsError α)
  /-- Non-blocking `withFileLock`, returning `.ok none` without running `action` when blocked. -/
  tryWithFileLock :
    {α : Type} → String → LockMode → Bool → m (Except FsError α) → m (Except FsError (Option α))

/-- Concrete `IO` filesystem API bundle for `LeanSwe.Fs`. -/
abbrev FsApi := FsApiM IO

/-- Directory-anchored, symlink-refusing filesystem capability scoped to an open subtree root. -/
structure SubtreeM (m : Type → Type) : Type 1 where
  /-- Inspect metadata at `rel` without following symlinks (`fstatDir` for `.root`). -/
  lstat : RelPath → m (Except FsError FileStat)
  /-- Read entire regular file at `rel` without following symlinks or blocking on special files. -/
  readRegular : RelPath → m (Except FsError ByteArray)
  /-- Atomically write `bytes` at `rel` (`0o644` subject to process `umask`). -/
  atomicWriteBytes : RelPath → ByteArray → m (Except FsError Unit)
  /-- Create directory at `rel` with `parents` and `existOk` (`0o755` subject to process `umask`). -/
  mkdir : RelPath → Bool → Bool → m (Except FsError Unit)
  /-- Remove non-directory or symbolic link at `rel` (with `missingOk`). -/
  unlink : RelPath → Bool → m (Except FsError Unit)
  /-- Remove empty directory at `rel`. -/
  rmdir : RelPath → m (Except FsError Unit)
  /-- Recursively remove directory tree at `rel` (with `ignoreMissing`). -/
  rmtree : RelPath → Bool → m (Except FsError Unit)
  /-- Create symbolic link at `linkRel` pointing to `target`. -/
  symlink : String → RelPath → m (Except FsError Unit)
  /-- Return sorted immediate child entry names inside directory `rel`. -/
  listDir : RelPath → m (Except FsError (Array EntryName))
  /-- Bounded top-down directory walk yielding sorted children inside `rel` without descending into symlinks. -/
  walk : RelPath → m (Except FsError (Array WalkEntry))
  /-- Acquire an advisory `flock` at `rel`, run `action`, and release the lock on exit. -/
  withFileLock : {α : Type} → RelPath → LockMode → Bool → m (Except FsError α) → m (Except FsError α)
  /-- Non-blocking `withFileLock`, returning `.ok none` without running `action` when contended. -/
  tryWithFileLock :
    {α : Type} → RelPath → LockMode → Bool → m (Except FsError α) → m (Except FsError (Option α))

/-- Concrete `IO` confined subtree capability exported by `LeanSwe.Fs`. -/
abbrev Subtree := SubtreeM IO

/-- Capability opener providing a confined `SubtreeM m` scoped to an opened directory descriptor. -/
structure SubtreeOpenerM (m : Type → Type) : Type 1 where
  /-- Open `rootPath` once as a pinned directory handle, run `action`, and close the handle on exit. -/
  withSubtree : {α : Type} → String → (SubtreeM m → m (Except FsError α)) → m (Except FsError α)

/-- Concrete `IO` subtree opener bundle exported by `LeanSwe.Fs`. -/
abbrev SubtreeOpener := SubtreeOpenerM IO

end LeanSwe.Fs

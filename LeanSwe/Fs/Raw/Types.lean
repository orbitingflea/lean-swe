namespace LeanSwe.Fs.Raw

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

/-- Opaque handle to an open file descriptor holding an advisory `flock(2)` lock. -/
structure LockHandle where
  /-- Opaque C slot-table or VFS lock identifier managed by `RawFsOpsM`. -/
  handleId : Nat
  /-- Target lock file path passed to `acquireLock`. -/
  path : String
  /-- Advisory lock mode held by this handle. -/
  mode : LockMode
  deriving Repr, BEq, DecidableEq

/-- Typed filesystem error returned by `LeanSwe.Fs.Raw` and `LeanSwe.Fs` operations. -/
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

/-- Minimal single-step filesystem primitives parameterized over effect monad `m`. -/
structure RawFsOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Inspect metadata (`follow = true` follows symlinks; `false` inspects links). -/
  stat : Bool → String → m (Except FsError FileStat)
  /-- List immediate entry names inside a directory. -/
  readDir : String → m (Except FsError (Array String))
  /-- Create a single directory, failing if parent is absent or path exists. -/
  createDir : String → m (Except FsError Unit)
  /-- Remove an empty directory. -/
  removeDir : String → m (Except FsError Unit)
  /-- Remove a file or symbolic link. -/
  unlinkFile : String → m (Except FsError Unit)
  /-- Read entire binary file (regular files only; rejects directories, FIFOs, and special files). -/
  readBytes : String → m (Except FsError ByteArray)
  /-- Write or overwrite binary file. -/
  writeBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically create a new regular file without following symlinks (`O_CREAT | O_EXCL | O_NOFOLLOW`), failing with `.alreadyExists` if any entry exists. -/
  createFileNew : String → ByteArray → m (Except FsError Unit)
  /-- Append UTF-8 text to a file, creating it if absent. -/
  appendText : String → String → m (Except FsError Unit)
  /-- Rename or replace a file or directory. -/
  rename : String → String → m (Except FsError Unit)
  /-- Set POSIX permission mode bits (`chmod`). -/
  chmod : String → Nat → m (Except FsError Unit)
  /-- Create symbolic link `(target, linkPath)`. -/
  symlink : String → String → m (Except FsError Unit)
  /-- Read symbolic link target path. -/
  readLink : String → m (Except FsError String)
  /-- Resolve canonical absolute path. -/
  realPath : String → m (Except FsError String)
  /-- Return current working directory. -/
  cwd : m (Except FsError String)
  /-- Return a monotonic nonce for temporary sibling filenames. -/
  monotonicNonce : m Nat
  /-- Open `path` and acquire an advisory `flock(2)` lock (`shared` or `exclusive`). -/
  acquireLock : String → LockMode → Bool → Bool → m (Except FsError LockHandle)
  /-- Unlock and close an acquired `LockHandle`. -/
  releaseLock : LockHandle → m (Except FsError Unit)

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.Fs.Raw`. -/
abbrev RawFsOps := RawFsOpsM IO

/-- Opaque handle to an open directory descriptor managed by `RawDirOpsM`. -/
structure DirHandle where
  /-- Opaque C slot-table or VFS handle identifier. -/
  handleId : Nat
  /-- Root directory path passed when opening the base handle. -/
  rootPath : String
  deriving Repr, BEq, DecidableEq

/-- Check whether directory handle identifier `id` lies strictly within `(0, UInt64.size)`. -/
def isValidDirHandleId (id : Nat) : Bool :=
  decide (0 < id ∧ id < UInt64.size)

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

/-- Single-step directory-descriptor (`*at`) primitives refusing symlinks, parameterized over effect monad `m`. -/
structure RawDirOpsM (m : Type → Type) where
  /-- Open `root` directory (`O_RDONLY | O_DIRECTORY | O_CLOEXEC`) returning a pinned `DirHandle`. -/
  openDir : String → m (Except FsError DirHandle)
  /-- Open immediate child directory `name` under `dh` without following symlinks (`O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC`). -/
  openDirAt : DirHandle → EntryName → m (Except FsError DirHandle)
  /-- Close an open `DirHandle`. -/
  closeDir : DirHandle → m (Except FsError Unit)
  /-- Inspect metadata of the open directory referenced by `dh` (`fstat`). -/
  fstatDir : DirHandle → m (Except FsError FileStat)
  /-- Inspect metadata of immediate child `name` under `dh` without following symlinks (`fstatat(..., AT_SYMLINK_NOFOLLOW)`). -/
  lstatAt : DirHandle → EntryName → m (Except FsError FileStat)
  /-- List unsorted immediate entry names inside `dh` (excluding `.` and `..`). -/
  readDirAt : DirHandle → m (Except FsError (Array EntryName))
  /-- Create immediate child directory `name` under `dh` (`0o755` subject to process `umask`). -/
  createDirAt : DirHandle → EntryName → m (Except FsError Unit)
  /-- Read entire regular file `name` under `dh` without following symlinks or blocking on special files. -/
  readRegularAt : DirHandle → EntryName → m (Except FsError ByteArray)
  /-- Atomically create a new regular file `name` under `dh` (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644` subject to process `umask`). -/
  createFileAt : DirHandle → EntryName → ByteArray → m (Except FsError Unit)
  /-- Atomically rename `(srcDh, srcName)` to `(dstDh, dstName)` (`renameat`). -/
  renameAt : DirHandle → EntryName → DirHandle → EntryName → m (Except FsError Unit)
  /-- Remove child entry (`isDir = false`) or empty child directory (`isDir = true` via `AT_REMOVEDIR`) under `dh`. -/
  unlinkAt : DirHandle → EntryName → Bool → m (Except FsError Unit)
  /-- Create symbolic link `(target, linkDh, linkName)` (`symlinkat`). -/
  symlinkAt : String → DirHandle → EntryName → m (Except FsError Unit)
  /-- Open child `name` under `dh` without following symlinks and acquire an advisory `flock(2)` lock (`0o644` if created). -/
  acquireLockAt : DirHandle → EntryName → LockMode → Bool → Bool → m (Except FsError LockHandle)
  /-- Unlock and close an acquired `LockHandle`. -/
  releaseLock : LockHandle → m (Except FsError Unit)
  /-- Generate a short target-independent temporary sibling `EntryName` (such as `.t.<nonce>`). -/
  freshTempName : m EntryName

/-- Concrete `IO` single-step directory-descriptor API bundle exported by `LeanSwe.Fs.Raw`. -/
abbrev RawDirOps := RawDirOpsM IO

end LeanSwe.Fs.Raw

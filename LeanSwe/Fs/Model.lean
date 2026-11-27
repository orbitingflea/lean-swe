import LeanSwe.Fs.Types
import LeanSwe.Fs.Types.Internal

namespace LeanSwe.Fs.Model

open LeanSwe.Fs

/-- Virtual advisory lock handle used by the pure in-memory `VfsState` model. -/
structure LockHandle where
  /-- Model-local lock identifier in `VfsState.locks`. -/
  handleId : Nat
  /-- Target lock file path passed to `acquireLock`. -/
  path : String
  /-- Advisory lock mode held by this handle. -/
  mode : LockMode
  deriving Repr, BEq, DecidableEq

/-- Virtual open directory handle used by the pure in-memory `VfsState` model. -/
structure DirHandle where
  /-- Model-local directory handle identifier in `VfsState.openDirs`. -/
  handleId : Nat
  /-- Root directory path passed when opening the handle. -/
  rootPath : String
  deriving Repr, BEq, DecidableEq

/-- Minimal single-step non-lock filesystem primitives parameterized over effect monad `m`. -/
abbrev NonLockFsOpsM := LeanSwe.Fs.Internal.NonLockFsOpsM

/-- Minimal single-step filesystem primitives parameterized over effect monad `m` and lock handle type `lockH`. -/
abbrev RawFsOpsM (m : Type → Type) (lockH : Type := LockHandle) :=
  LeanSwe.Fs.Internal.RawFsOpsM m lockH

/-- Concrete `IO` single-step filesystem primitive bundle. -/
abbrev RawFsOps (lockH : Type := LockHandle) := LeanSwe.Fs.Internal.RawFsOpsM IO lockH

/-- Scoped single-step filesystem primitive bundle replacing raw `acquireLock`/`releaseLock` with bracketed lock operations (no exposed handle parameter). -/
abbrev ScopedRawFsOpsM := LeanSwe.Fs.Internal.ScopedRawFsOpsM

/-- Single-step directory-descriptor (`*at`) primitives refusing symlinks, parameterized over effect monad `m` and handle types `dirH`, `lockH`. -/
abbrev RawDirOpsM (m : Type → Type) (dirH : Type := DirHandle) (lockH : Type := LockHandle) :=
  LeanSwe.Fs.Internal.RawDirOpsM m dirH lockH

/-- Concrete `IO` single-step directory-descriptor primitive bundle. -/
abbrev RawDirOps (dirH : Type := DirHandle) (lockH : Type := LockHandle) :=
  LeanSwe.Fs.Internal.RawDirOpsM IO dirH lockH

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Classify common Linux `errno` codes used across `otherError` and `inappropriateType`. -/
def classifyErrno (code : UInt32) (defaultKind : FsErrorKind) : FsErrorKind :=
  match code.toNat with
  | 1 | 13 | 30 => .permissionDenied
  | 2 => .notFound
  | 17 => .alreadyExists
  | 20 => .notADirectory
  | 21 => .isADirectory
  | 22 | 36 => .invalidInput
  | 38 | 95 => .unsupported
  | 39 | 66 => .notEmpty
  | _ => defaultKind

/-- Pure specification of `mapRawError`, converting raw OS error records into normalized `FsError` values. -/
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
  | .wouldBlock path? code detail =>
    { kind := .wouldBlock
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "resource temporarily unavailable" detail }
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

/-- Strip matching leading segment prefix from `pParts`. -/
def stripPrefixParts : List (List Char) → List (List Char) → Option (List (List Char))
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

/-- Builder function constructing a `SubtreeM m` from `RawDirOpsM m` and an open root handle. -/
abbrev SubtreeBuilder (m : Type → Type) :=
  RawDirOpsM m → DirHandle → SubtreeM m

/-- Builder function constructing a `SubtreeOpenerM m` from `RawDirOpsM m`. -/
abbrev SubtreeOpenerBuilder (m : Type → Type) :=
  RawDirOpsM m → SubtreeOpenerM m

/-- Node stored in the pure in-memory VFS model. -/
inductive VfsNode where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits. -/
  | dir (mode : Nat)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)
  deriving BEq, DecidableEq

/-- Structural directory tree backing `VfsState` (makes orphan paths unrepresentable). -/
inductive VfsTree where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits and child lookup. -/
  | dir (mode : Nat) (children : String → Option VfsTree)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)

/-- Extract the top-level `VfsNode` summary of a `VfsTree`. -/
def vfsTreeTopNode : VfsTree → VfsNode
  | .file bs m => .file bs m
  | .dir m _ => .dir m
  | .symlink t m => .symlink t m

/-- Construct an empty directory `VfsTree` with POSIX mode `mode`. -/
def vfsEmptyDir (mode : Nat) : VfsTree :=
  .dir mode (fun _ => none)

/-- Look up the subtree at segment path `segs` inside `t`. -/
def vfsTreeGet (t : VfsTree) : List String → Option VfsTree
  | [] => some t
  | seg :: rest =>
    match t with
    | .dir _ ch =>
      match ch seg with
      | none => none
      | some sub => vfsTreeGet sub rest
    | _ => none

/-- Look up the `VfsNode` at segment path `segs` inside `t`. -/
def nodeAt (t : VfsTree) (segs : List String) : Option VfsNode :=
  (vfsTreeGet t segs).map vfsTreeTopNode

/-- Update or delete the subtree at segment path `segs` inside `t`. -/
def vfsTreeSet (t : VfsTree) (segs : List String) (v : Option VfsTree) : VfsTree :=
  match segs with
  | [] => v.getD t
  | [last] =>
    match t with
    | .dir m ch => .dir m (fun s => if s == last then v else ch s)
    | _ => t
  | seg :: rest =>
    match t with
    | .dir m ch =>
      .dir m (fun s =>
        if s == seg then
          match ch seg with
          | some sub => some (vfsTreeSet sub rest v)
          | none => none
        else ch s)
    | _ => t

/-- Pure in-memory VFS state backing both ambient `vfsOps` and handle-anchored `vfsDirOps`. -/
structure VfsState where
  /-- Root directory tree of the VFS. -/
  tree : VfsTree
  /-- Canonical paths tracked for directory listing. -/
  keys : List String
  /-- Current working directory (normalized absolute path). -/
  cwd : String
  /-- Monotonic counter for temporary sibling filenames. -/
  nonce : Nat
  /-- Active advisory locks `(handleId, canonicalPath, mode)`. -/
  locks : List (Nat × String × LockMode) := []
  /-- Monotonic counter for allocated lock handle IDs. -/
  nextLockId : Nat := 1
  /-- Active open directory handles mapping `handleId` to physical tree position from `"/"`. -/
  openDirs : List (Nat × List String) := []
  /-- Monotonic counter for allocated directory handle IDs. -/
  nextDirId : Nat := 1

/-- Normalize `path` against `cwd` into a canonical absolute path string. -/
def vfsAbsNorm (cwd path : String) : String :=
  normPath (if isAbsolute path then path else join cwd path)

/-- Split an absolute normalized path into non-empty path segments. -/
def vfsSplitSegs (absNorm : String) : List String :=
  match absNorm.toList with
  | '/' :: rest =>
    (splitCharList '/' rest).filterMap fun cs =>
      if cs.isEmpty then none else some (String.ofList cs)
  | _ => []

/-- Return `true` iff `k` is a normalized absolute path string. -/
def isCanonPath (k : String) : Bool :=
  isAbsolute k && (normPath k == k)

/-- Look up a canonical path in `VfsTree`. -/
def vfsTreeNodes (t : VfsTree) (k : String) : Option VfsNode :=
  if isCanonPath k then nodeAt t (vfsSplitSegs k) else none

/-- Canonical path lookup view derived from `VfsState.tree`. -/
def VfsState.nodes (st : VfsState) : String → Option VfsNode :=
  vfsTreeNodes st.tree

/-- Append child segment `seg` to canonical directory path `cur`. -/
def vfsChildPath (cur seg : String) : String :=
  if cur == "/" then "/" ++ seg else cur ++ "/" ++ seg

/-- Reconstruct canonical absolute path string from physical segment list `segs`. -/
def pathOfSegs (segs : List String) : String :=
  match segs with
  | [] => "/"
  | _ => "/" ++ String.intercalate "/" segs

/-- Resolve `segs` from `cur` following symlinks up to `fuel` steps (`followLast` controls final link). -/
def vfsResolveSegs (nodes : String → Option VfsNode) (cur : String)
    (segs : List String) (followLast : Bool) : Nat → Except FsError (String × VfsNode)
  | 0 => .error { kind := .ioError, path := some cur, message := "too many levels of symbolic links" }
  | fuel + 1 =>
    match segs with
    | [] =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.symlink target m) =>
        if followLast then
          let par := (parent cur).getD "/"
          let nextAbs := normPath (if isAbsolute target then target else join par target)
          vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs) true fuel
        else
          .ok (cur, .symlink target m)
      | some node => .ok (cur, node)
    | seg :: rest =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.dir mode) =>
        if (mode / 64) % 2 == 0 then
          .error { kind := .permissionDenied, path := some cur, message := s!"permission denied: {cur}" }
        else
          vfsResolveSegs nodes (vfsChildPath cur seg) rest followLast fuel
      | some (.symlink target _) =>
        let par := (parent cur).getD "/"
        let nextAbs := normPath (if isAbsolute target then target else join par target)
        vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs ++ seg :: rest) followLast fuel
      | some (.file _ _) =>
        .error { kind := .notADirectory, path := some cur, message := s!"not a directory: {cur}" }

/-- Convert a `VfsNode` to `FileStat`. -/
def vfsToStat : VfsNode → FileStat
  | .file bs m =>
    { kind := .file, byteSize := bs.size, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .dir m =>
    { kind := .dir, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ m =>
    { kind := .symlink, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }

/-- Pure `stat` over `VfsState`. -/
def vfsStatPure (st : VfsState) (follow : Bool) (path : String) : Except FsError FileStat :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) follow 1024 with
  | .error e => .error e
  | .ok (_, node) => .ok (vfsToStat node)

/-- Pure `realPath` over `VfsState`. -/
def vfsRealPathPure (st : VfsState) (path : String) : Except FsError String :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, _) => .ok canon

/-- Pure `createDir` over `VfsState`. -/
def vfsCreateDirPure (st : VfsState) (path : String) : Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
  | .ok _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
  | .error e =>
    if e.kind != .notFound then
      (.error e, st)
    else
      match splitLastAux (vfsSplitSegs abs) [] with
      | none =>
        (.error { kind := .notFound, path := some path, message := s!"invalid path: {path}" }, st)
      | some (parSegs, lastSeg) =>
        match vfsResolveSegs st.nodes "/" parSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (parCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
          else
            let newKey := vfsChildPath parCanon lastSeg
            match st.nodes newKey with
            | some _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
            | none =>
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (vfsEmptyDir 0o755))
                keys := newKey :: st.keys })
        | .ok (parCanon, _) =>
          (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

/-- Pure `readDir` over `VfsState`. -/
def vfsReadDirPure (st : VfsState) (path : String) : Except FsError (Array String) :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, .dir mode) =>
    if (mode / 256) % 2 == 0 then
      .error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }
    else
      let prefixChars := (if canon == "/" then "/" else canon ++ "/").toList
      let children := st.keys.eraseDups.filterMap fun k =>
        if (st.nodes k).isSome then
          if k != canon && prefixChars.isPrefixOf k.toList then
            let restChars := k.toList.drop prefixChars.length
            if !restChars.isEmpty && !('/' ∈ restChars) then some (String.ofList restChars) else none
          else none
        else none
      .ok children.toArray
  | .ok (_, _) => .error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }

/-- Pure `writeBytes` over `VfsState`. -/
def vfsWriteBytesPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match splitLastAux (vfsSplitSegs abs) [] with
  | none => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
  | some (parSegs, lastSeg) =>
    match vfsResolveSegs st.nodes "/" parSegs true 512 with
    | .error pe => (.error pe, st)
    | .ok (parCanon, .dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
      else
        let targetKey := vfsChildPath parCanon lastSeg
        match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
        | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | _ =>
          let finalKey := match st.nodes targetKey with
            | some (.symlink tgt _) => vfsAbsNorm parCanon tgt
            | _ => targetKey
          (.ok (), { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs finalKey) (some (.file bs 0o644))
            keys := finalKey :: st.keys })
    | .ok (parCanon, _) =>
      (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

private def maxLockId : List (Nat × String × LockMode) → Nat
  | [] => 0
  | (i, _, _) :: rest => max i (maxLockId rest)

private def freshLockId (st : VfsState) : Nat :=
  max (maxLockId st.locks) st.nextLockId + 1

/-- Return `true` iff `locks` contains a conflicting lock on `canon` for `mode`. -/
def hasLockConflict (locks : List (Nat × String × LockMode)) (canon : String)
    (mode : LockMode) : Bool :=
  locks.any fun (_, p, m) => p == canon && (mode == .exclusive || m == .exclusive)

private def isValidLockPath (path : String) : Bool :=
  let chars := path.toList
  !chars.isEmpty && !(chars.length > 1 && chars.getLast? == some '/')

/-- Pure `acquireLock` over `VfsState`. -/
def vfsAcquireLockPure (st : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (_nonBlocking : Bool) : Except FsError LockHandle × VfsState :=
  if !isValidLockPath path then
    (.error { kind := .invalidInput, path := some path, message := "invalid lock path" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok (canon, .file _ _) =>
      if hasLockConflict st.locks canon mode then
        (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
      else
        let id := freshLockId st
        (.ok { handleId := id, path := path, mode := mode },
          { st with locks := (id, canon, mode) :: st.locks, nextLockId := id })
    | .ok (_, .dir _) =>
      (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
    | .ok (_, .symlink _ _) =>
      (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else if !createIfMissing then
        (.error e, st)
      else
        match splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 512 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              if hasLockConflict st.locks newKey mode then
                (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
              else
                let id := freshLockId st
                (.ok { handleId := id, path := path, mode := mode },
                  { st with
                    tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file ByteArray.empty 0o644))
                    keys := newKey :: st.keys
                    locks := (id, newKey, mode) :: st.locks
                    nextLockId := id })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

/-- Pure `releaseLock` over `VfsState`. -/
def vfsReleaseLockPure (st : VfsState) (handle : LockHandle) :
    Except FsError Unit × VfsState :=
  if handle.handleId == 0 then
    (.error { kind := .invalidInput, path := some handle.path, message := "invalid lock handle" }, st)
  else if st.locks.any (fun (id, _, _) => id == handle.handleId) then
    (.ok (), { st with locks := st.locks.filter (fun (id, _, _) => id != handle.handleId) })
  else
    (.error { kind := .invalidInput, path := some handle.path, message := "unknown lock handle" }, st)

/-- Return `true` iff `path` is non-empty, NUL-free, and lacks a non-root trailing `'/'`. -/
def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

/-- Pure `readBytes` over `VfsState`. -/
def vfsReadBytesPure (st : VfsState) (path : String) : Except FsError ByteArray :=
  if !isValidRawPath path then
    .error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => .error e
    | .ok (_, .file bs _) => .ok bs
    | .ok (_, .dir _) => .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    | .ok (_, _) => .error { kind := .notFound, path := some path, message := s!"not found: {path}" }

/-- Pure `createFileNew` over `VfsState`. -/
def vfsCreateFileNewPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  if !isValidRawPath path then
    (.error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok _ =>
      (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else
        match splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 1024 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file bs 0o644))
                keys := newKey :: st.keys })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

/-- Pure `rename` over `VfsState`. -/
def vfsRenamePure (st : VfsState) (src dst : String) : Except FsError Unit × VfsState :=
  if !isValidRawPath src then
    (.error { kind := .invalidInput, path := some src, message := s!"invalid path: {src}" }, st)
  else if !isValidRawPath dst then
    (.error { kind := .invalidInput, path := some dst, message := s!"invalid path: {dst}" }, st)
  else
    let srcAbs := vfsAbsNorm st.cwd src
    let dstAbs := vfsAbsNorm st.cwd dst
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs srcAbs) false 1024 with
    | .error e => (.error e, st)
    | .ok (srcCanon, srcNode) =>
      match splitLastAux (vfsSplitSegs dstAbs) [] with
      | none => (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
      | some (dstParSegs, dstLastSeg) =>
        match vfsResolveSegs st.nodes "/" dstParSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (dstParCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some dst, message := s!"permission denied: {dst}" }, st)
          else
            let dstKey := vfsChildPath dstParCanon dstLastSeg
            let srcIsDir := match srcNode with | .dir _ => true | _ => false
            let dstIsDir := match st.nodes dstKey with | some (.dir _) => true | _ => false
            if dstIsDir && !srcIsDir then
              (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
            else if srcCanon == dstKey then
              (.ok (), st)
            else
              let moved := vfsTreeGet st.tree (vfsSplitSegs srcCanon)
              let tr₁ := vfsTreeSet st.tree (vfsSplitSegs srcCanon) none
              (.ok (), { st with
                tree := vfsTreeSet tr₁ (vfsSplitSegs dstKey) moved
                keys := dstKey :: st.keys })
        | .ok (dstParCanon, _) =>
          (.error { kind := .notADirectory, path := some dstParCanon, message := s!"not a directory: {dstParCanon}" }, st)

/-- Pure single-step `RawFsOpsM (StateM VfsState)` backed by `VfsState`. -/
def vfsOps : RawFsOpsM (StateM VfsState) :=
  { mapRawError := mapRawError
    stat := fun follow path st => (vfsStatPure st follow path, st)
    readDir := fun path st => (vfsReadDirPure st path, st)
    createDir := fun path st => vfsCreateDirPure st path
    removeDir := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (canon, .dir _) =>
        if canon == "/" then (.error { kind := .permissionDenied, path := some path, message := "cannot remove root" }, st)
        else (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
      | .ok (_, _) => (.error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }, st)
    unlinkFile := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | .ok (canon, _) => (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
    readBytes := fun path st => (vfsReadBytesPure st path, st)
    writeBytes := fun path bs st => vfsWriteBytesPure st path bs
    createFileNew := fun path bs st => vfsCreateFileNewPure st path bs
    appendText := fun path s st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .ok (canon, .file bs m) =>
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) (some (.file (bs ++ s.toUTF8) m)) })
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | _ => vfsWriteBytesPure st path s.toUTF8
    rename := fun src dst st => vfsRenamePure st src dst
    chmod := fun path mode st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .error e => (.error e, st)
      | .ok (canon, _) =>
        let updated := match vfsTreeGet st.tree (vfsSplitSegs canon) with
          | some (.file bs _) => some (.file bs mode)
          | some (.dir _ ch) => some (.dir mode ch)
          | some (.symlink t _) => some (.symlink t mode)
          | none => none
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) updated })
    symlink := fun target linkPath st =>
      let abs := vfsAbsNorm st.cwd linkPath
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .ok _ => (.error { kind := .alreadyExists, path := some linkPath, message := s!"already exists: {linkPath}" }, st)
      | .error e =>
        if e.kind != .notFound then (.error e, st)
        else (.ok (), { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs abs) (some (.symlink target 0o777))
          keys := abs :: st.keys })
    readLink := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .symlink target _) => (.ok target, st)
      | .ok (_, _) => (.error { kind := .invalidInput, path := some path, message := s!"not a symlink: {path}" }, st)
    realPath := fun path st => (vfsRealPathPure st path, st)
    cwd := fun st => (.ok st.cwd, st)
    monotonicNonce := fun st => (st.nonce, { st with nonce := st.nonce + 1 })
    acquireLock := fun path mode createIfMissing nonBlocking st =>
      vfsAcquireLockPure st path mode createIfMissing nonBlocking
    releaseLock := fun handle st => vfsReleaseLockPure st handle }

private def maxDirId : List (Nat × List String) → Nat
  | [] => 0
  | (i, _) :: rest => max i (maxDirId rest)

private def freshDirId (st : VfsState) : Nat :=
  max (maxDirId st.openDirs) st.nextDirId + 1

/-- Look up the physical segment path associated with an open `DirHandle` in `st`. -/
def lookupDir (st : VfsState) (dh : DirHandle) : Option (List String) :=
  if dh.handleId == 0 then none
  else (st.openDirs.find? (fun (id, _) => id == dh.handleId)).map (·.2)

private def allocDirHandle (st : VfsState) (rootPath : String) (pos : List String) :
    DirHandle × VfsState :=
  let id := freshDirId st
  ({ handleId := id, rootPath := rootPath },
    { st with openDirs := (id, pos) :: st.openDirs, nextDirId := id + 1 })

private def invalidDirHandleErr (dh : DirHandle) : FsError :=
  { kind := .invalidInput, path := some dh.rootPath, message := s!"invalid or closed directory handle: {dh.handleId}" }

private def vfsReadDirAtEntries (st : VfsState) (pos : List String) : Array EntryName :=
  let dirCanon := pathOfSegs pos
  let prefixChars := (if dirCanon == "/" then "/" else dirCanon ++ "/").toList
  let entries := st.keys.eraseDups.filterMap fun k =>
    if (st.nodes k).isSome then
      if k != dirCanon && prefixChars.isPrefixOf k.toList then
        let restChars := k.toList.drop prefixChars.length
        let restStr := String.ofList restChars
        if h : validSeg restStr = true then
          some { val := restStr, valid := h }
        else
          none
      else none
    else none
  entries.toArray

private def dirHasLiveChild (st : VfsState) (dirPos : List String) : Bool :=
  let dirCanon := pathOfSegs dirPos
  let prefixChars := (if dirCanon == "/" then "/" else dirCanon ++ "/").toList
  st.keys.any fun k =>
    (st.nodes k).isSome && k != dirCanon && prefixChars.isPrefixOf k.toList

private def remapKeysAfterRename (keys : List String) (srcPos dstPos : List String) : List String :=
  let srcPrefix := srcPos
  keys.map fun k =>
    let kSegs := vfsSplitSegs k
    if srcPrefix.isPrefixOf kSegs then
      pathOfSegs (dstPos ++ kSegs.drop srcPrefix.length)
    else
      k

private theorem toDigitsCore_mem_digit_or_acc (fuel base n : Nat) (acc : List Char) (c : Char)
    (hBase : base = 10) (hMem : c ∈ Nat.toDigitsCore base fuel n acc) :
    c ∈ acc ∨ ∃ d < 10, c = Nat.digitChar d := by
  induction fuel generalizing n acc with
  | zero =>
    simp [Nat.toDigitsCore] at hMem
    exact Or.inl hMem
  | succ f ih =>
    unfold Nat.toDigitsCore at hMem
    dsimp only at hMem
    split at hMem
    · simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hAcc
      · exact Or.inr ⟨n % base, by subst hBase; exact Nat.mod_lt _ (by decide), rfl⟩
      · exact Or.inl hAcc
    · rcases ih (n / base) (Nat.digitChar (n % base) :: acc) hMem with hAcc | hDig
      · simp only [List.mem_cons] at hAcc
        rcases hAcc with rfl | hOld
        · exact Or.inr ⟨n % base, by subst hBase; exact Nat.mod_lt _ (by decide), rfl⟩
        · exact Or.inl hOld
      · exact Or.inr hDig

private theorem nat_toString_digits (n : Nat) (c : Char) (hMem : c ∈ (toString n).toList) :
    c ≠ '/' ∧ c ≠ Char.ofNat 0 := by
  have hDig : c ∈ Nat.toDigits 10 n := by simpa [toString, Nat.repr] using hMem
  unfold Nat.toDigits at hDig
  rcases toDigitsCore_mem_digit_or_acc (n + 1) 10 n [] c rfl hDig with hc | ⟨d, hd, rfl⟩
  · simp at hc
  · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
    all_goals first | decide | omega

/-- Every decimal-suffixed `.t.<n>` temporary filename satisfies `validSeg`. -/
theorem validSeg_dotT (n : Nat) : validSeg (".t." ++ toString n) = true := by
  have hNoSlash : (".t." ++ toString n).toList.contains '/' = false := by
    refine Bool.eq_false_iff.mpr ?_
    intro hm
    have hMem : '/' ∈ (".t." ++ toString n).toList := List.contains_iff_mem.mp hm
    rw [String.toList_append, show ".t.".toList = ['.', 't', '.'] by decide, List.mem_append] at hMem
    rcases hMem with hP | hN
    · simp at hP
    · exact (nat_toString_digits n '/' hN).1 rfl
  have hNoNul : (".t." ++ toString n).toList.contains (Char.ofNat 0) = false := by
    refine Bool.eq_false_iff.mpr ?_
    intro hm
    have hMem : Char.ofNat 0 ∈ (".t." ++ toString n).toList := List.contains_iff_mem.mp hm
    rw [String.toList_append, show ".t.".toList = ['.', 't', '.'] by decide, List.mem_append] at hMem
    rcases hMem with hP | hN
    · simp at hP
    · exact (nat_toString_digits n (Char.ofNat 0) hN).2 rfl
  have hNeEmpty : (!(".t." ++ toString n).toList.isEmpty) = true := by
    rw [String.toList_append, show ".t.".toList = ['.', 't', '.'] by decide]
    simp
  have hNeDot : ((".t." ++ toString n).toList != ['.']) = true := by
    rw [String.toList_append, show ".t.".toList = ['.', 't', '.'] by decide]
    simp
  have hNeDotDot : ((".t." ++ toString n).toList != ['.', '.']) = true := by
    rw [String.toList_append, show ".t.".toList = ['.', 't', '.'] by decide]
    simp
  change (!(".t." ++ toString n).toList.isEmpty && !(".t." ++ toString n).toList.contains '/' &&
    !(".t." ++ toString n).toList.contains (Char.ofNat 0) &&
    (".t." ++ toString n).toList != ['.'] && (".t." ++ toString n).toList != ['.', '.']) = true
  rw [hNeEmpty, hNoSlash, hNoNul, hNeDot, hNeDotDot]
  rfl

private def vfsOpenDirPure (st : VfsState) (root : String) :
    Except FsError DirHandle × VfsState :=
  if !isValidRawPath root then
    (.error { kind := .invalidInput, path := some root, message := s!"invalid path: {root}" }, st)
  else
    let abs := vfsAbsNorm st.cwd root
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => (.error e, st)
    | .ok (canon, .dir mode) =>
      if (mode / 256) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" }, st)
      else
        let (dh, st') := allocDirHandle st root (vfsSplitSegs canon)
        (.ok dh, st')
    | .ok (_, _) =>
      (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st)

private def vfsOpenDirAtPure (st : VfsState) (dh : DirHandle) (name : EntryName) :
    Except FsError DirHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (invalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | none => (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error { kind := .invalidInput, path := some name.val, message := s!"symlink refused in subtree traversal: {name.val}" }, st)
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let (childDh, st') := allocDirHandle st (pathOfSegs childPos) childPos
            (.ok childDh, st')
        | some _ =>
          (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
    | some _ =>
      (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private def vfsCloseDirPure (st : VfsState) (dh : DirHandle) :
    Except FsError Unit × VfsState :=
  if dh.handleId == 0 then
    (.error (invalidDirHandleErr dh), st)
  else if st.openDirs.any (fun (id, _) => id == dh.handleId) then
    (.ok (), { st with openDirs := st.openDirs.filter (fun (id, _) => id != dh.handleId) })
  else
    (.error (invalidDirHandleErr dh), st)

private def vfsFstatDirPure (st : VfsState) (dh : DirHandle) : Except FsError FileStat :=
  match lookupDir st dh with
  | none => .error (invalidDirHandleErr dh)
  | some pos =>
    match nodeAt st.tree pos with
    | some node => .ok (vfsToStat node)
    | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }

private def vfsLstatAtPure (st : VfsState) (dh : DirHandle) (name : EntryName) :
    Except FsError FileStat :=
  match lookupDir st dh with
  | none => .error (invalidDirHandleErr dh)
  | some pos =>
    match nodeAt st.tree pos with
    | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
      else
        match nodeAt st.tree (pos ++ [name.val]) with
        | some node => .ok (vfsToStat node)
        | none => .error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }
    | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }

private def vfsReadDirAtPure (st : VfsState) (dh : DirHandle) : Except FsError (Array EntryName) :=
  match lookupDir st dh with
  | none => .error (invalidDirHandleErr dh)
  | some pos =>
    match nodeAt st.tree pos with
    | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
    | some (.dir mode) =>
      if (mode / 256) % 2 == 0 then
        .error { kind := .permissionDenied, path := some dh.rootPath, message := s!"permission denied: {dh.rootPath}" }
      else
        .ok (vfsReadDirAtEntries st pos)
    | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }

private def vfsCreateDirAtPure (st : VfsState) (dh : DirHandle) (name : EntryName) :
    Except FsError Unit × VfsState :=
  match lookupDir st dh with
  | none => (.error (invalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | some _ => (.error { kind := .alreadyExists, path := some name.val, message := s!"already exists: {name.val}" }, st)
        | none =>
          (.ok (), { st with
            tree := vfsTreeSet st.tree childPos (some (vfsEmptyDir 0o755))
            keys := pathOfSegs childPos :: st.keys })
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private def vfsReadRegularAtPure (st : VfsState) (dh : DirHandle) (name : EntryName) :
    Except FsError ByteArray :=
  match lookupDir st dh with
  | none => .error (invalidDirHandleErr dh)
  | some pos =>
    match nodeAt st.tree pos with
    | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
      else
        match nodeAt st.tree (pos ++ [name.val]) with
        | none => .error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }
        | some (.file bs fMode) =>
          if (fMode / 256) % 2 == 0 then
            .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
          else
            .ok bs
        | some (.dir _) => .error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }
        | some (.symlink _ _) => .error { kind := .invalidInput, path := some name.val, message := s!"symlink refused: {name.val}" }
    | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }

private def vfsCreateFileAtPure (st : VfsState) (dh : DirHandle) (name : EntryName)
    (bytes : ByteArray) : Except FsError Unit × VfsState :=
  match lookupDir st dh with
  | none => (.error (invalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | some _ => (.error { kind := .alreadyExists, path := some name.val, message := s!"already exists: {name.val}" }, st)
        | none =>
          (.ok (), { st with
            tree := vfsTreeSet st.tree childPos (some (.file bytes 0o644))
            keys := pathOfSegs childPos :: st.keys })
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private def vfsRenameAtPure (st : VfsState) (srcDh : DirHandle) (srcName : EntryName)
    (dstDh : DirHandle) (dstName : EntryName) : Except FsError Unit × VfsState :=
  match lookupDir st srcDh, lookupDir st dstDh with
  | none, _ => (.error (invalidDirHandleErr srcDh), st)
  | _, none => (.error (invalidDirHandleErr dstDh), st)
  | some srcPos, some dstPos =>
    match nodeAt st.tree srcPos, nodeAt st.tree dstPos with
    | some (.dir srcMode), some (.dir dstMode) =>
      if (srcMode / 128) % 2 == 0 || (srcMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some srcName.val, message := s!"permission denied: {srcName.val}" }, st)
      else if (dstMode / 128) % 2 == 0 || (dstMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some dstName.val, message := s!"permission denied: {dstName.val}" }, st)
      else
        let srcFull := srcPos ++ [srcName.val]
        let dstFull := dstPos ++ [dstName.val]
        match vfsTreeGet st.tree srcFull with
        | none => (.error { kind := .notFound, path := some srcName.val, message := s!"no such file or directory: {srcName.val}" }, st)
        | some srcSub =>
          if srcFull == dstFull then
            (.ok (), st)
          else if srcFull.isPrefixOf dstPos then
            (.error { kind := .invalidInput, path := some dstName.val, message := "cannot rename directory into itself" }, st)
          else
            let srcIsDir := match srcSub with | .dir _ _ => true | _ => false
            let dstNode := nodeAt st.tree dstFull
            match srcIsDir, dstNode with
            | false, some (.dir _) =>
              (.error { kind := .isADirectory, path := some dstName.val, message := s!"is a directory: {dstName.val}" }, st)
            | true, some (.file _ _) | true, some (.symlink _ _) =>
              (.error { kind := .notADirectory, path := some dstName.val, message := s!"not a directory: {dstName.val}" }, st)
            | true, some (.dir _) =>
              if dirHasLiveChild st dstFull then
                (.error { kind := .notEmpty, path := some dstName.val, message := s!"directory not empty: {dstName.val}" }, st)
              else
                let tr₁ := vfsTreeSet st.tree srcFull none
                (.ok (), { st with
                  tree := vfsTreeSet tr₁ dstFull (some srcSub)
                  keys := pathOfSegs dstFull :: remapKeysAfterRename st.keys srcFull dstFull })
            | _, _ =>
              let tr₁ := vfsTreeSet st.tree srcFull none
              (.ok (), { st with
                tree := vfsTreeSet tr₁ dstFull (some srcSub)
                keys := pathOfSegs dstFull :: remapKeysAfterRename st.keys srcFull dstFull })
    | none, _ => (.error { kind := .notFound, path := some srcDh.rootPath, message := "source directory no longer exists" }, st)
    | _, none => (.error { kind := .notFound, path := some dstDh.rootPath, message := "destination directory no longer exists" }, st)
    | some _, _ => (.error { kind := .notADirectory, path := some srcDh.rootPath, message := s!"not a directory: {srcDh.rootPath}" }, st)

private def vfsUnlinkAtPure (st : VfsState) (dh : DirHandle) (name : EntryName) (isDir : Bool) :
    Except FsError Unit × VfsState :=
  match lookupDir st dh with
  | none => (.error (invalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | none => (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.dir _) =>
          if !isDir then
            (.error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }, st)
          else if dirHasLiveChild st childPos then
            (.error { kind := .notEmpty, path := some name.val, message := s!"directory not empty: {name.val}" }, st)
          else
            (.ok (), { st with tree := vfsTreeSet st.tree childPos none })
        | some _ =>
          if isDir then
            (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
          else
            (.ok (), { st with tree := vfsTreeSet st.tree childPos none })
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private def vfsSymlinkAtPure (st : VfsState) (target : String) (dh : DirHandle)
    (linkName : EntryName) : Except FsError Unit × VfsState :=
  if target.isEmpty || target.toList.contains (Char.ofNat 0) then
    (.error { kind := .invalidInput, path := some linkName.val, message := "invalid symlink target" }, st)
  else
    match lookupDir st dh with
    | none => (.error (invalidDirHandleErr dh), st)
    | some pos =>
      match nodeAt st.tree pos with
      | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
      | some (.dir parMode) =>
        if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
          (.error { kind := .permissionDenied, path := some linkName.val, message := s!"permission denied: {linkName.val}" }, st)
        else
          let childPos := pos ++ [linkName.val]
          match nodeAt st.tree childPos with
          | some _ => (.error { kind := .alreadyExists, path := some linkName.val, message := s!"already exists: {linkName.val}" }, st)
          | none =>
            (.ok (), { st with
              tree := vfsTreeSet st.tree childPos (some (.symlink target 0o777))
              keys := pathOfSegs childPos :: st.keys })
      | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private def vfsAcquireLockAtPure (st : VfsState) (dh : DirHandle) (name : EntryName)
    (mode : LockMode) (createIfMissing : Bool) (_nonBlocking : Bool) :
    Except FsError LockHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (invalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        let childCanon := pathOfSegs childPos
        match nodeAt st.tree childPos with
        | some (.file _ _) =>
          if hasLockConflict st.locks childCanon mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            let id := freshLockId st
            (.ok { handleId := id, path := childCanon, mode := mode },
              { st with locks := (id, childCanon, mode) :: st.locks, nextLockId := id })
        | some (.dir _) =>
          (.error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error { kind := .invalidInput, path := some name.val, message := s!"symlink rejected for lock: {name.val}" }, st)
        | none =>
          if !createIfMissing then
            (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
          else if (parMode / 128) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else if hasLockConflict st.locks childCanon mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            let id := freshLockId st
            (.ok { handleId := id, path := childCanon, mode := mode },
              { st with
                tree := vfsTreeSet st.tree childPos (some (.file ByteArray.empty 0o644))
                keys := childCanon :: st.keys
                locks := (id, childCanon, mode) :: st.locks
                nextLockId := id })
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- Pure physical-position `RawDirOpsM (StateM VfsState)` backed by `VfsState` without resolving symlinks on `*at` steps. -/
def vfsDirOps : RawDirOpsM (StateM VfsState) :=
  { openDir := fun root st => vfsOpenDirPure st root
    openDirAt := fun dh name st => vfsOpenDirAtPure st dh name
    closeDir := fun dh st => vfsCloseDirPure st dh
    fstatDir := fun dh st => (vfsFstatDirPure st dh, st)
    lstatAt := fun dh name st => (vfsLstatAtPure st dh name, st)
    readDirAt := fun dh st => (vfsReadDirAtPure st dh, st)
    createDirAt := fun dh name st => vfsCreateDirAtPure st dh name
    readRegularAt := fun dh name st => (vfsReadRegularAtPure st dh name, st)
    createFileAt := fun dh name bytes st => vfsCreateFileAtPure st dh name bytes
    renameAt := fun srcDh srcName dstDh dstName st => vfsRenameAtPure st srcDh srcName dstDh dstName
    unlinkAt := fun dh name isDir st => vfsUnlinkAtPure st dh name isDir
    symlinkAt := fun target dh linkName st => vfsSymlinkAtPure st target dh linkName
    acquireLockAt := fun dh name mode createIfMissing nonBlocking st =>
      vfsAcquireLockAtPure st dh name mode createIfMissing nonBlocking
    releaseLock := fun handle st => vfsReleaseLockPure st handle
    freshTempName := fun st =>
      ({ val := ".t." ++ toString st.nonce, valid := validSeg_dotT st.nonce },
        { st with nonce := st.nonce + 1 }) }

/-- Two VFS states agree on all nodes strictly outside the subtree rooted at physical segments `root`. -/
def SameOutside (root : List String) (st st' : VfsState) : Prop :=
  ∀ p : String, ¬ root <+: vfsSplitSegs p → st'.nodes p = st.nodes p

/-- External concurrent environment step `env` that preserves `cwd`, `root` itself, `openDirs`, `locks`, and everything strictly outside `root`. -/
def EnvInside (root : List String) (env : VfsState → VfsState) : Prop :=
  ∀ st : VfsState,
    SameOutside root st (env st) ∧
    nodeAt (env st).tree root = nodeAt st.tree root ∧
    (env st).cwd = st.cwd ∧
    (env st).openDirs = st.openDirs ∧
    (env st).locks = st.locks

/-- Apply external concurrent environment step `env` before each single `RawDirOpsM` primitive step. -/
def interleave (env : VfsState → VfsState) (ops : RawDirOpsM (StateM VfsState)) :
    RawDirOpsM (StateM VfsState) :=
  { openDir := fun root st => ops.openDir root (env st)
    openDirAt := fun dh name st => ops.openDirAt dh name (env st)
    closeDir := fun dh st => ops.closeDir dh (env st)
    fstatDir := fun dh st => ops.fstatDir dh (env st)
    lstatAt := fun dh name st => ops.lstatAt dh name (env st)
    readDirAt := fun dh st => ops.readDirAt dh (env st)
    createDirAt := fun dh name st => ops.createDirAt dh name (env st)
    readRegularAt := fun dh name st => ops.readRegularAt dh name (env st)
    createFileAt := fun dh name bytes st => ops.createFileAt dh name bytes (env st)
    renameAt := fun srcDh srcName dstDh dstName st => ops.renameAt srcDh srcName dstDh dstName (env st)
    unlinkAt := fun dh name isDir st => ops.unlinkAt dh name isDir (env st)
    symlinkAt := fun target dh linkName st => ops.symlinkAt target dh linkName (env st)
    acquireLockAt := fun dh name mode createIfMissing nonBlocking st =>
      ops.acquireLockAt dh name mode createIfMissing nonBlocking (env st)
    releaseLock := fun handle st => ops.releaseLock handle (env st)
    freshTempName := fun st => ops.freshTempName (env st) }

/-- Free inductive program AST covering all 12 `SubtreeM` calls, lock brackets, and continuations. -/
inductive SubtreeProg : Type → Type 1 where
  /-- Pure return value. -/
  | pure {α : Type} (a : α) : SubtreeProg α
  /-- Invoke `sub.lstat rel` and pass the result to continuation `k`. -/
  | lstat {α : Type} (rel : RelPath) (k : Except FsError FileStat → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.readRegular rel` and pass the result to continuation `k`. -/
  | readRegular {α : Type} (rel : RelPath) (k : Except FsError ByteArray → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.atomicWriteBytes` and pass the result to continuation `k`. -/
  | atomicWriteBytes {α : Type} (rel : RelPath) (bytes : ByteArray)
      (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.mkdir` and pass the result to continuation `k`. -/
  | mkdir {α : Type} (rel : RelPath) (parents existOk : Bool)
      (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.unlink` and pass the result to continuation `k`. -/
  | unlink {α : Type} (rel : RelPath) (missingOk : Bool)
      (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.rmdir` and pass the result to continuation `k`. -/
  | rmdir {α : Type} (rel : RelPath) (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.rmtree` and pass the result to continuation `k`. -/
  | rmtree {α : Type} (rel : RelPath) (ignoreMissing : Bool)
      (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.symlink` and pass the result to continuation `k`. -/
  | symlink {α : Type} (target : String) (rel : RelPath)
      (k : Except FsError Unit → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.listDir` and pass the result to continuation `k`. -/
  | listDir {α : Type} (rel : RelPath)
      (k : Except FsError (Array EntryName) → SubtreeProg α) : SubtreeProg α
  /-- Invoke `sub.walk` and pass the result to continuation `k`. -/
  | walk {α : Type} (rel : RelPath)
      (k : Except FsError (Array WalkEntry) → SubtreeProg α) : SubtreeProg α
  /-- Execute bracketed `sub.withFileLock` over `body` and pass its result to `k`. -/
  | withFileLock {α β : Type} (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
      (body : SubtreeProg (Except FsError β))
      (k : Except FsError β → SubtreeProg α) : SubtreeProg α
  /-- Execute bracketed `sub.tryWithFileLock` over `body` and pass its result to `k`. -/
  | tryWithFileLock {α β : Type} (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
      (body : SubtreeProg (Except FsError β))
      (k : Except FsError (Option β) → SubtreeProg α) : SubtreeProg α

/-- Interpret a `SubtreeProg α` against a `SubtreeM m` capability. -/
def evalSubtreeProg {m : Type → Type} [Monad m] (sub : SubtreeM m) :
    {α : Type} → SubtreeProg α → m α
  | _, .pure a => pure a
  | _, .lstat rel k => sub.lstat rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .readRegular rel k => sub.readRegular rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .atomicWriteBytes rel bytes k =>
    sub.atomicWriteBytes rel bytes >>= fun r => evalSubtreeProg sub (k r)
  | _, .mkdir rel p e k => sub.mkdir rel p e >>= fun r => evalSubtreeProg sub (k r)
  | _, .unlink rel m k => sub.unlink rel m >>= fun r => evalSubtreeProg sub (k r)
  | _, .rmdir rel k => sub.rmdir rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .rmtree rel ig k => sub.rmtree rel ig >>= fun r => evalSubtreeProg sub (k r)
  | _, .symlink tgt rel k => sub.symlink tgt rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .listDir rel k => sub.listDir rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .walk rel k => sub.walk rel >>= fun r => evalSubtreeProg sub (k r)
  | _, .withFileLock rel mode c body k =>
    sub.withFileLock rel mode c (evalSubtreeProg sub body) >>= fun r => evalSubtreeProg sub (k r)
  | _, .tryWithFileLock rel mode c body k =>
    sub.tryWithFileLock rel mode c (evalSubtreeProg sub body) >>= fun r => evalSubtreeProg sub (k r)

/-- Every live node in `st.tree` has its canonical path recorded in `st.keys`. -/
def VfsKeysComplete (st : VfsState) : Prop :=
  ∀ segs : List String, nodeAt st.tree segs ≠ none → pathOfSegs segs ∈ st.keys

/-- All open directory handles in `st.openDirs` have positive IDs strictly below `st.nextDirId`. -/
def DirHandleInvariant (st : VfsState) : Prop :=
  ∀ id pos, (id, pos) ∈ st.openDirs → 0 < id ∧ id < st.nextDirId

/-- Every live node inside `t` is reachable solely via valid `EntryName` segments (`validSeg`). -/
def VfsTreeValidSegs (t : VfsTree) : Prop :=
  ∀ segs : List String, nodeAt t segs ≠ none → ∀ s ∈ segs, validSeg s = true

/-- Every directory inside `t` has owner read+search (`0o500`) permissions and nesting depth strictly below `fuel`. -/
def VfsTreeWalkable : Nat → VfsTree → Prop
  | _, .file _ _ => True
  | _, .symlink _ _ => True
  | 0, .dir _ _ => False
  | fuel + 1, .dir m ch =>
    (m / 256) % 2 = 1 ∧ (m / 64) % 2 = 1 ∧
    ∀ name sub, ch name = some sub → VfsTreeWalkable fuel sub

/-- Every directory inside `t` has owner `rwx` (`0o700`) permissions and nesting depth strictly below `fuel`. -/
def VfsTreeRemovable : Nat → VfsTree → Prop
  | _, .file _ _ => True
  | _, .symlink _ _ => True
  | 0, .dir _ _ => False
  | fuel + 1, .dir m ch =>
    (m / 256) % 2 = 1 ∧ (m / 128) % 2 = 1 ∧ (m / 64) % 2 = 1 ∧
    ∀ name sub, ch name = some sub → VfsTreeRemovable fuel sub

/-- Frozen theorem specification: every `SubtreeM` operation from valid handle `dh` at `pos` preserves `SameOutside pos`, and `rmtree` preserves tighter `SameOutside (pos ++ rel)`. -/
def SpecSubtreeSameOutside (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  ∀ (st : VfsState) (dh : DirHandle) (pos : List String) (rel : RelPath)
    (bytes : ByteArray) (b1 b2 : Bool) (target : String)
    (lockMode : LockMode) (α : Type) (pureRes : Except FsError α),
    lookupDir st dh = some pos →
    (∃ m, nodeAt st.tree pos = some (.dir m)) →
    let sub := mkSubtree vfsDirOps dh
    SameOutside pos st (sub.lstat rel |>.run st).2 ∧
    SameOutside pos st (sub.readRegular rel |>.run st).2 ∧
    SameOutside pos st (sub.atomicWriteBytes rel bytes |>.run st).2 ∧
    SameOutside pos st (sub.mkdir rel b1 b2 |>.run st).2 ∧
    SameOutside pos st (sub.unlink rel b1 |>.run st).2 ∧
    SameOutside pos st (sub.rmdir rel |>.run st).2 ∧
    SameOutside (pos ++ rel.segments.map (·.val)) st (sub.rmtree rel b1 |>.run st).2 ∧
    SameOutside pos st (sub.symlink target rel |>.run st).2 ∧
    SameOutside pos st (sub.listDir rel |>.run st).2 ∧
    SameOutside pos st (sub.walk rel |>.run st).2 ∧
    SameOutside pos st (sub.withFileLock rel lockMode b1 (pure pureRes) |>.run st).2 ∧
    SameOutside pos st (sub.tryWithFileLock rel lockMode b1 (pure pureRes) |>.run st).2

/-- Frozen theorem specification: any strict prefix of `rel` resolving to a `.symlink` node causes all 12 `SubtreeM` operations to fail with `.invalidInput` without mutating `nodes`. -/
def SpecNoSymlinkFollowAncestors (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  ∀ (st : VfsState) (dh : DirHandle) (pos : List String) (pre : List EntryName) (rest : List EntryName)
    (t : String) (lm : Nat) (bytes : ByteArray) (b1 b2 : Bool)
    (target : String) (lockMode : LockMode) (α : Type) (pureRes : Except FsError α),
    let rel : RelPath := { segments := pre ++ rest }
    lookupDir st dh = some pos →
    rest ≠ [] →
    (∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧ (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1) →
    (∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1) →
    nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm) →
    let sub := mkSubtree vfsDirOps dh
    let check {β : Type} (act : StateM VfsState (Except FsError β)) : Prop :=
      let (r, st') := act.run st
      (∃ e, r = .error e ∧ e.kind = .invalidInput) ∧ st'.nodes = st.nodes
    check (sub.lstat rel) ∧
    check (sub.readRegular rel) ∧
    check (sub.atomicWriteBytes rel bytes) ∧
    check (sub.mkdir rel b1 b2) ∧
    check (sub.unlink rel b1) ∧
    check (sub.rmdir rel) ∧
    check (sub.rmtree rel b1) ∧
    check (sub.symlink target rel) ∧
    check (sub.listDir rel) ∧
    check (sub.walk rel) ∧
    check (sub.withFileLock rel lockMode b1 (pure pureRes)) ∧
    check (sub.tryWithFileLock rel lockMode b1 (pure pureRes))

/-- Frozen theorem specification: `atomicWriteBytes` on a leaf symlink replaces the link itself with `.file` (`0o644`) and leaves its target untouched. -/
def SpecAtomicWriteLeafSymlink (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  ∀ (st : VfsState) (dh : DirHandle) (pos : List String) (pre : List EntryName) (leaf : EntryName)
    (t : String) (lm : Nat) (bytes : ByteArray),
    let rel : RelPath := { segments := pre ++ [leaf] }
    let parentPos := pos ++ pre.map (·.val)
    let leafPos := parentPos ++ [leaf.val]
    lookupDir st dh = some pos →
    DirHandleInvariant st →
    (∀ k ≤ pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧ (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1) →
    (∃ pm, nodeAt st.tree parentPos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1) →
    nodeAt st.tree leafPos = some (.symlink t lm) →
    nodeAt st.tree (parentPos ++ [".t." ++ toString st.nonce]) = none →
    let (res, st') := ((mkSubtree vfsDirOps dh).atomicWriteBytes rel bytes).run st
    res = .ok () ∧
    nodeAt st'.tree leafPos = some (.file bytes 0o644) ∧
    SameOutside leafPos st st' ∧
    st'.openDirs = st.openDirs

/-- Frozen theorem specification: any `SubtreeProg` inside `withSubtree root` under `interleave env vfsDirOps` with `EnvInside pos env` preserves `SameOutside pos`, `openDirs`, and `locks`. -/
def SpecSubtreeProgramSameOutsideInterleaved
    (mkOpener : SubtreeOpenerBuilder (StateM VfsState)) : Prop :=
  ∀ (α : Type) (env : VfsState → VfsState) (root : String) (st : VfsState)
    (pos : List String) (m : Nat) (prog : SubtreeProg (Except FsError α)),
    (∀ s ∈ pos, validSeg s = true) →
    EnvInside pos env →
    DirHandleInvariant st →
    isValidRawPath root = true →
    vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd root)) true 1024 =
      .ok (pathOfSegs pos, .dir m) →
    (∀ s : VfsState, SameOutside pos st s → s.cwd = st.cwd → nodeAt s.tree pos = nodeAt st.tree pos →
      ∀ r, vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd root)) true 1024 = .ok r → r.1 = pathOfSegs pos) →
    let (_, st') :=
      ((mkOpener (interleave env vfsDirOps)).withSubtree root
        (fun sub => evalSubtreeProg sub prog)).run st
    SameOutside pos st st' ∧ st'.openDirs = st.openDirs ∧ st'.locks = st.locks

/-- Frozen theorem specification: every `SubtreeM` operation and `withSubtree` preserves `openDirs` under `DirHandleInvariant`. -/
def SpecDescriptorConservation
    (mkOpener : SubtreeOpenerBuilder (StateM VfsState))
    (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  (∀ (st : VfsState) (dh : DirHandle) (rel : RelPath)
    (bytes : ByteArray) (b1 b2 : Bool) (target : String)
    (lockMode : LockMode) (α : Type) (pureRes : Except FsError α),
    DirHandleInvariant st →
    let sub := mkSubtree vfsDirOps dh
    (sub.lstat rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.readRegular rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.atomicWriteBytes rel bytes |>.run st).2.openDirs = st.openDirs ∧
    (sub.mkdir rel b1 b2 |>.run st).2.openDirs = st.openDirs ∧
    (sub.unlink rel b1 |>.run st).2.openDirs = st.openDirs ∧
    (sub.rmdir rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.rmtree rel b1 |>.run st).2.openDirs = st.openDirs ∧
    (sub.symlink target rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.listDir rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.walk rel |>.run st).2.openDirs = st.openDirs ∧
    (sub.withFileLock rel lockMode b1 (pure pureRes) |>.run st).2.openDirs = st.openDirs ∧
    (sub.tryWithFileLock rel lockMode b1 (pure pureRes) |>.run st).2.openDirs = st.openDirs) ∧
  (∀ (α : Type) (root : String) (st : VfsState) (pureRes : Except FsError α),
    DirHandleInvariant st →
    ((mkOpener vfsDirOps).withSubtree root (fun _ => pure pureRes) |>.run st).2.openDirs = st.openDirs)

/-- Frozen theorem specification: every `DirHandle`-taking `vfsDirOps` primitive refuses closed or forged handles with `.invalidInput` without mutating `nodes`. -/
def SpecInvalidHandleRefused : Prop :=
  ∀ (st : VfsState) (dh otherDh : DirHandle) (name otherName : EntryName)
    (bytes : ByteArray) (b1 b2 : Bool) (target : String) (lockMode : LockMode),
    lookupDir st dh = none →
    let check {β : Type} (act : StateM VfsState (Except FsError β)) : Prop :=
      let (r, st') := act.run st
      (∃ e, r = .error e ∧ e.kind = .invalidInput) ∧ st'.nodes = st.nodes
    check (vfsDirOps.openDirAt dh name) ∧
    check (vfsDirOps.closeDir dh) ∧
    check (vfsDirOps.fstatDir dh) ∧
    check (vfsDirOps.lstatAt dh name) ∧
    check (vfsDirOps.readDirAt dh) ∧
    check (vfsDirOps.createDirAt dh name) ∧
    check (vfsDirOps.readRegularAt dh name) ∧
    check (vfsDirOps.createFileAt dh name bytes) ∧
    check (vfsDirOps.renameAt dh name otherDh otherName) ∧
    check (vfsDirOps.renameAt otherDh otherName dh name) ∧
    check (vfsDirOps.unlinkAt dh name b1) ∧
    check (vfsDirOps.symlinkAt target dh name) ∧
    check (vfsDirOps.acquireLockAt dh name lockMode b1 b2)

/-- Frozen theorem specification: `atomicWriteBytes` followed by `readRegular` and `lstat` returns exact written bytes and `.file` metadata with mode `0o644`. -/
def SpecAtomicWriteReadRegularRoundTrip (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  ∀ (st : VfsState) (dh : DirHandle) (pos : List String) (leaf : EntryName)
    (bytes : ByteArray),
    let rel : RelPath := { segments := [leaf] }
    lookupDir st dh = some pos →
    DirHandleInvariant st →
    (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1) →
    nodeAt st.tree (pos ++ [".t." ++ toString st.nonce]) = none →
    (match nodeAt st.tree (pos ++ [leaf.val]) with | some (.dir _) => False | _ => True) →
    let sub := mkSubtree vfsDirOps dh
    let (wRes, st₁) := (sub.atomicWriteBytes rel bytes).run st
    wRes = .ok () ∧
    (sub.readRegular rel |>.run st₁).1 = .ok bytes ∧
    (∃ lst, (sub.lstat rel |>.run st₁).1 = .ok lst ∧
      lst.kind = .file ∧ lst.byteSize = bytes.size ∧ lst.mode = 0o644)

/-- Frozen theorem specification: `mkdir` makes the created directory visible to `listDir` and `rmtree` leaves `lstat` as `.notFound` under `VfsKeysComplete` and `VfsTreeRemovable`. -/
def SpecMkdirVisibleAndRmtreeNotFound (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  (∀ (st : VfsState) (dh : DirHandle) (pos : List String) (child : EntryName),
    lookupDir st dh = some pos →
    DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    pos.length + 1 < 1024 →
    (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1) →
    nodeAt st.tree (pos ++ [child.val]) = none →
    let sub := mkSubtree vfsDirOps dh
    let (mRes, st₁) := (sub.mkdir { segments := [child] } false false).run st
    mRes = .ok () ∧
    (∃ names, (sub.listDir RelPath.root |>.run st₁).1 = .ok names ∧ child ∈ names.toList)) ∧
  (∀ (st : VfsState) (dh : DirHandle) (pos : List String) (child : EntryName),
    VfsKeysComplete st →
    lookupDir st dh = some pos →
    DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    pos.length + 1 < 1024 →
    (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1) →
    (∃ cm, nodeAt st.tree (pos ++ [child.val]) = some (.dir cm) ∧ (cm / 256) % 2 = 1 ∧ (cm / 128) % 2 = 1 ∧ (cm / 64) % 2 = 1) →
    (∀ tsub, vfsTreeGet st.tree (pos ++ [child.val]) = some tsub →
      VfsTreeValidSegs tsub ∧ VfsTreeRemovable 4095 tsub) →
    let sub := mkSubtree vfsDirOps dh
    let (rRes, st₁) := (sub.rmtree { segments := [child] } false).run st
    rRes = .ok () ∧
    (∃ e, (sub.lstat { segments := [child] } |>.run st₁).1 = .error e ∧ e.kind = .notFound))

/-- Frozen theorem specification: on symlink-free traversable subpaths under `pos`, `SubtreeM.readRegular` and `SubtreeM.lstat` agree with ambient `vfsOps.readBytes` and `vfsOps.stat false`. -/
def SpecSubtreeAgreesWithAmbientOnSymlinkFree (mkSubtree : SubtreeBuilder (StateM VfsState)) : Prop :=
  ∀ (st : VfsState) (dh : DirHandle) (pos : List String) (rel : RelPath) (bs : ByteArray) (fm : Nat),
    lookupDir st dh = some pos →
    DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    rel ≠ RelPath.root →
    pos.length + rel.segments.length < 1024 →
    (∀ k ≤ rel.segments.length,
      k < rel.segments.length →
      ∃ dm, nodeAt st.tree (pos ++ (rel.segments.take k).map (·.val)) = some (.dir dm) ∧
        (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1) →
    (∀ k < pos.length,
      ∃ dm, nodeAt st.tree (pos.take k) = some (.dir dm) ∧ (dm / 64) % 2 = 1) →
    nodeAt st.tree (pos ++ rel.segments.map (·.val)) = some (.file bs fm) →
    (fm / 256) % 2 = 1 →
    let fullPath := pathOfSegs (pos ++ rel.segments.map (·.val))
    let sub := mkSubtree vfsDirOps dh
    (sub.readRegular rel |>.run st).1 = (vfsOps.readBytes fullPath |>.run st).1 ∧
    (sub.lstat rel |>.run st).1 = (vfsOps.stat false fullPath |>.run st).1

end LeanSwe.Fs.Model

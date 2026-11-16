import LeanSwe.Fs.Raw.Types

namespace LeanSwe.Fs.Raw.Internal

open LeanSwe.Fs.Raw
  (FsErrorKind FsError EntryKind FileStat FsRawError LockMode LockHandle RawFsOpsM RawFsOps
   DirHandle EntryName RawDirOps validSeg isValidDirHandleId)

/-- POSIX FFI operations injected by `LeanSwe.Fs.Raw.Interface`. -/
structure PosixRawOps where
  /-- Set file mode bits (`chmod`). -/
  chmod : String → UInt32 → IO Unit
  /-- Create symbolic link `(target, linkPath)`. -/
  symlink : String → String → IO Unit
  /-- Read symbolic link target path. -/
  readLink : String → IO String
  /-- Read POSIX mode bits (`st_mode & 0o7777`), optionally following symlinks. -/
  statMode : String → Bool → IO UInt32
  /-- Acquire an advisory lock on `path` (`mode`, `createIfMissing`, `nonBlocking`), returning `(status, handleId, errno)`. -/
  acquireLock : String → UInt8 → Bool → Bool → IO (UInt8 × UInt64 × UInt32)
  /-- Release an advisory file lock handle `(handleId, path)`. -/
  releaseLock : UInt64 → String → IO Unit
  /-- Read entire regular file bytes without blocking on non-regular files. -/
  readRegularBytes : String → IO ByteArray
  /-- Exclusively create a new regular file without following final symlinks. -/
  createFileNew : String → ByteArray → IO Unit

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

/-- Map Lean's `IO.FS.FileType` to `EntryKind`. -/
def toEntryKind : IO.FS.FileType → EntryKind
  | .file => .file
  | .dir => .dir
  | .symlink => .symlink
  | .other => .other

/-- Build the concrete `RawFsOps` bundle from injected POSIX C-ABI hooks. -/
def mkRawOps (posix : PosixRawOps) : RawFsOps :=
  { mapRawError := mapRawError
    stat := fun follow path => catchFs (some path) do
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
    readDir := fun path => catchFs (some path) do
      let entries ← (System.FilePath.mk path).readDir
      return entries.map (·.fileName)
    createDir := fun path => catchFs (some path) (IO.FS.createDir (System.FilePath.mk path))
    removeDir := fun path => catchFs (some path) (IO.FS.removeDir (System.FilePath.mk path))
    unlinkFile := fun path => catchFs (some path) (IO.FS.removeFile (System.FilePath.mk path))
    readBytes := fun path => catchFs (some path) (posix.readRegularBytes path)
    writeBytes := fun path b => catchFs (some path) (IO.FS.writeBinFile (System.FilePath.mk path) b)
    createFileNew := fun path b => catchFs (some path) (posix.createFileNew path b)
    appendText := fun path content => catchFs (some path) do
      let h ← IO.FS.Handle.mk (System.FilePath.mk path) .append
      h.putStr content
      h.flush
    rename := fun s d => catchFs (some s) (IO.FS.rename (System.FilePath.mk s) (System.FilePath.mk d))
    chmod := fun path mode => catchFs (some path) (posix.chmod path (UInt32.ofNat mode))
    symlink := fun target linkPath => catchFs (some linkPath) (posix.symlink target linkPath)
    readLink := fun path => catchFs (some path) (posix.readLink path)
    realPath := fun path => catchFs (some path) do
      let rp ← IO.FS.realPath (System.FilePath.mk path)
      return rp.toString
    cwd := catchFs none do
      let d ← IO.currentDir
      return d.toString
    monotonicNonce := IO.monoNanosNow
    acquireLock := fun path mode createIfMissing nonBlocking => do
      let modeByte : UInt8 := match mode with
        | .shared => 0
        | .exclusive => 1
      match ← catchFs (some path) (posix.acquireLock path modeByte createIfMissing nonBlocking) with
      | .error e => return .error e
      | .ok (0, handleId, _) =>
        return .ok { handleId := handleId.toNat, path := path, mode := mode }
      | .ok (1, _, errCode) =>
        return .error (mapRawError (.wouldBlock (some path) errCode "resource temporarily unavailable"))
      | .ok (_, _, errCode) =>
        return .error (mapRawError (.invalidArgument (some path) errCode "invalid lock path"))
    releaseLock := fun handle => do
      if handle.handleId == 0 || handle.handleId ≥ UInt64.size then
        return .error (mapRawError (.invalidArgument (some handle.path) 22 "invalid lock handle"))
      catchFs (some handle.path) (posix.releaseLock (UInt64.ofNat handle.handleId) handle.path) }

/-- POSIX directory-descriptor FFI hooks injected by `LeanSwe.Fs.Raw.Interface`. -/
structure PosixDirOps where
  /-- Open `root` directory descriptor returning an opaque slot ID. -/
  openDir : String → IO UInt64
  /-- Open child directory `name` under `dirId` without following symlinks. -/
  openDirAt : UInt64 → String → IO UInt64
  /-- Close open directory descriptor `dirId`. -/
  closeDir : UInt64 → String → IO Unit
  /-- Inspect metadata of open directory descriptor `dirId` (`fstat`). -/
  fstatDir : UInt64 → String → IO (UInt8 × UInt64 × UInt32 × Int × UInt32 × Int × UInt32)
  /-- Inspect metadata of child `name` under `dirId` without following symlinks (`fstatat`). -/
  lstatAt : UInt64 → String → IO (UInt8 × UInt64 × UInt32 × Int × UInt32 × Int × UInt32)
  /-- Read raw child entry names under `dirId`. -/
  readDirAt : UInt64 → String → IO (Array String)
  /-- Create child directory `name` under `dirId` (`0o755`). -/
  createDirAt : UInt64 → String → IO Unit
  /-- Read regular file `name` under `dirId` without following symlinks or blocking. -/
  readRegularAt : UInt64 → String → IO ByteArray
  /-- Create new regular file `name` under `dirId` (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644`). -/
  createFileAt : UInt64 → String → ByteArray → IO Unit
  /-- Rename `(srcId, srcName)` to `(dstId, dstName)`. -/
  renameAt : UInt64 → String → UInt64 → String → IO Unit
  /-- Unlink child (`isDir = false`) or remove empty child directory (`isDir = true`). -/
  unlinkAt : UInt64 → String → Bool → IO Unit
  /-- Create symbolic link `(target, dirId, name)`. -/
  symlinkAt : String → UInt64 → String → IO Unit
  /-- Acquire advisory lock on child `name` under `dirId`, returning `(status, handleId, errno)`. -/
  acquireLockAt : UInt64 → String → UInt8 → Bool → Bool → IO (UInt8 × UInt64 × UInt32)
  /-- Release an advisory file lock handle `(handleId, path)`. -/
  releaseLock : UInt64 → String → IO Unit
  /-- Return a strictly monotonic non-zero process-local counter value. -/
  freshTempNonce : IO UInt64

/-- Convert a packed C `stat` tuple into `FileStat`. -/
def toFileStat (raw : UInt8 × UInt64 × UInt32 × Int × UInt32 × Int × UInt32) : FileStat :=
  let (kindByte, sz, mode, mSec, mNsec, aSec, aNsec) := raw
  let kind : EntryKind :=
    match kindByte.toNat with
    | 0 => .file
    | 1 => .dir
    | 2 => .symlink
    | _ => .other
  { kind := kind
    byteSize := sz.toNat
    mode := mode.toNat
    modifiedSec := mSec
    modifiedNsec := mNsec.toNat
    accessedSec := aSec
    accessedNsec := aNsec.toNat }

/-- Validate `DirHandle.handleId` before casting to `UInt64`, returning `.invalidInput` when out of range. -/
def checkDirHandle (dh : DirHandle) (fallbackPath : String) : Except FsError UInt64 :=
  if !isValidDirHandleId dh.handleId then
    .error (mapRawError (.invalidArgument (some fallbackPath) 22 "invalid directory handle"))
  else
    .ok (UInt64.ofNat dh.handleId)

/-- Parse and deduplicate raw OS directory entry names into `EntryName` values. -/
def parseUniqueEntryNames (raw : Array String) : Except FsError (Array EntryName) := do
  let mut out : Array EntryName := #[]
  for s in raw do
    let name ← EntryName.parse s
    if !out.contains name then
      out := out.push name
  return out

/-- Build the concrete `RawDirOps` bundle from injected POSIX directory-descriptor hooks. -/
def mkRawDirOps (posix : PosixDirOps) : RawDirOps :=
  { openDir := fun rootPath => catchFs (some rootPath) do
      let hid ← posix.openDir rootPath
      return { handleId := hid.toNat, rootPath := rootPath }
    openDirAt := fun dh name =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) do
        let hid ← posix.openDirAt dirId name.val
        return { handleId := hid.toNat, rootPath := dh.rootPath }
    closeDir := fun dh =>
      match checkDirHandle dh dh.rootPath with
      | .error e => return .error e
      | .ok dirId => catchFs (some dh.rootPath) (posix.closeDir dirId dh.rootPath)
    fstatDir := fun dh =>
      match checkDirHandle dh dh.rootPath with
      | .error e => return .error e
      | .ok dirId => catchFs (some dh.rootPath) do
        return toFileStat (← posix.fstatDir dirId dh.rootPath)
    lstatAt := fun dh name =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) do
        return toFileStat (← posix.lstatAt dirId name.val)
    readDirAt := fun dh =>
      match checkDirHandle dh dh.rootPath with
      | .error e => return .error e
      | .ok dirId => do
        match ← catchFs (some dh.rootPath) (posix.readDirAt dirId dh.rootPath) with
        | .error e => return .error e
        | .ok raw => return parseUniqueEntryNames raw
    createDirAt := fun dh name =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) (posix.createDirAt dirId name.val)
    readRegularAt := fun dh name =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) (posix.readRegularAt dirId name.val)
    createFileAt := fun dh name bytes =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) (posix.createFileAt dirId name.val bytes)
    renameAt := fun srcDh srcName dstDh dstName =>
      match checkDirHandle srcDh srcName.val, checkDirHandle dstDh dstName.val with
      | .error e, _ => return .error e
      | _, .error e => return .error e
      | .ok srcId, .ok dstId =>
        catchFs (some srcName.val) (posix.renameAt srcId srcName.val dstId dstName.val)
    unlinkAt := fun dh name isDir =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) (posix.unlinkAt dirId name.val isDir)
    symlinkAt := fun target dh name =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => catchFs (some name.val) (posix.symlinkAt target dirId name.val)
    acquireLockAt := fun dh name mode createIfMissing nonBlocking =>
      match checkDirHandle dh name.val with
      | .error e => return .error e
      | .ok dirId => do
        let modeByte : UInt8 := match mode with
          | .shared => 0
          | .exclusive => 1
        match ← catchFs (some name.val) (posix.acquireLockAt dirId name.val modeByte createIfMissing nonBlocking) with
        | .error e => return .error e
        | .ok (0, handleId, _) =>
          return .ok { handleId := handleId.toNat, path := name.val, mode := mode }
        | .ok (1, _, errCode) =>
          return .error (mapRawError (.wouldBlock (some name.val) errCode "resource temporarily unavailable"))
        | .ok (_, _, errCode) =>
          return .error (mapRawError (.invalidArgument (some name.val) errCode "invalid lock path"))
    releaseLock := fun handle => do
      if handle.handleId == 0 || handle.handleId ≥ UInt64.size then
        return .error (mapRawError (.invalidArgument (some handle.path) 22 "invalid lock handle"))
      catchFs (some handle.path) (posix.releaseLock (UInt64.ofNat handle.handleId) handle.path)
    freshTempName := do
      let n ← posix.freshTempNonce
      let candidate := ".t." ++ toString n.toNat
      if h : validSeg candidate = true then
        return { val := candidate, valid := h }
      else
        return EntryName.lit ".t" }

end LeanSwe.Fs.Raw.Internal

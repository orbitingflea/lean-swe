import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model
import LeanSwe.Fs.SysBridge.Common

namespace LeanSwe.Fs.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model (RawFsOpsM RawFsOps RawDirOpsM RawDirOps mapRawError isValidRawPath validSeg_dotT)

/-- Build a parametric `RawFsOpsM m fd` bundle purely over `FilesOpsM m fd` and nonce source `nextNonce` (`createDir` uses `0o777` and `writeBytes`/`appendText` use `0o666` masked by process `umask`, while `createFileNew`/`acquireLock` preserve historical `0o644`). -/
def mkRawFsOpsM {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (nextNonce : m Nat)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    RawFsOpsM m fd :=
  { mapRawError := mapRawError
    stat := fun follow path => do
      match ← retryEintr (files.fstatat none path.toUTF8 { symlinkNofollow := !follow }) eintrFuel with
      | .ok st => return .ok (statInfoToFileStat st)
      | .error e => return .error (mapErrno (some path) "stat" e)
    readDir := fun path => readDirPure files path eintrFuel streamFuel
    createDir := fun path => do
      match ← retryEintr (files.mkdirat none path.toUTF8 0o777) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some path) "mkdir" e)
    removeDir := fun path => removeDirAtOpt files none path eintrFuel
    unlinkFile := fun path => do
      match ← retryEintr (files.unlinkat none path.toUTF8 false) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some path) "unlink" e)
    readBytes := fun path => readBytesPure files path eintrFuel streamFuel
    writeBytes := fun path bytes => do
      let flags : OpenFlags :=
        { access := .wronly, creat := true, trunc := true, cloexec := true }
      match ← retryEintr (files.openat none path.toUTF8 flags 0o666) eintrFuel with
      | .error e => return .error (mapErrno (some path) "open" e)
      | .ok h => writeAllAndClose files h path bytes eintrFuel
    createFileNew := fun path bytes => createFileNewPure files path bytes eintrFuel
    appendText := fun path content => do
      let flags : OpenFlags :=
        { access := .wronly, creat := true, append := true, cloexec := true }
      match ← retryEintr (files.openat none path.toUTF8 flags 0o666) eintrFuel with
      | .error e => return .error (mapErrno (some path) "open" e)
      | .ok h => writeAllAndClose files h path content.toUTF8 eintrFuel
    rename := fun src dst => do
      match ← retryEintr (files.renameat2 none src.toUTF8 none dst.toUTF8 {}) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some src) "rename" e)
    chmod := fun path mode => do
      match ← retryEintr (files.fchmodat none path.toUTF8 (UInt32.ofNat mode)) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some path) "chmod" e)
    symlink := fun target linkPath => do
      match ← retryEintr (files.symlinkat target.toUTF8 none linkPath.toUTF8) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some linkPath) "symlink" e)
    readLink := fun path => readLinkLoop files path 256 eintrFuel 13
    realPath := fun path => realPathPure files path eintrFuel
    cwd := getcwdLoop files 4096 eintrFuel 9
    monotonicNonce := nextNonce
    acquireLock := fun path mode createIfMissing nonBlocking =>
      acquireLockPure files path mode createIfMissing nonBlocking eintrFuel
    releaseLock := fun handle => releaseLockPure files handle eintrFuel }

/-- Open `rootPath` as a pinned directory descriptor (`O_RDONLY | O_DIRECTORY | O_CLOEXEC`). -/
def openDirPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (rootPath : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError fd) := do
  if !isValidRawPath rootPath then
    return .error (mapErrno (some rootPath) "openDir" Errno.EINVAL)
  let flags : OpenFlags := { access := .rdonly, directory := true, cloexec := true }
  match ← retryEintr (files.openat none rootPath.toUTF8 flags 0) eintrFuel with
  | .error e => return .error (mapErrno (some rootPath) "openDir" e)
  | .ok h => return .ok h

/-- Open immediate child directory `name` under `dirFd` without following symlinks (`O_NOFOLLOW | O_DIRECTORY`). -/
def openDirAtPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dirFd : fd) (name : EntryName)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError fd) := do
  let flags : OpenFlags :=
    { access := .rdonly, directory := true, nofollow := true, cloexec := true }
  match ← retryEintr (files.openat (some dirFd) name.val.toUTF8 flags 0) eintrFuel with
  | .ok h => return .ok h
  | .error e =>
    if e == Errno.ELOOP then
      return .error (mapErrno (some name.val) "openDirAt" Errno.EINVAL)
    else if e == Errno.ENOTDIR then
      match ← retryEintr (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) eintrFuel with
      | .ok st =>
        if st.kind == .symlink then
          return .error (mapErrno (some name.val) "openDirAt" Errno.EINVAL)
        else
          return .error (mapErrno (some name.val) "openDirAt" Errno.ENOTDIR)
      | .error _ => return .error (mapErrno (some name.val) "openDirAt" Errno.ENOTDIR)
    else
      return .error (mapErrno (some name.val) "openDirAt" e)

/-- List unique child `EntryName` entries inside open directory `dirFd` via `reopenReadOnly` (independent cursor) with `lseek(0)` fallback. -/
def readDirAtPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dirFd : fd)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    m (Except FsError (Array EntryName)) := do
  let rawRes ← match ← retryEintr (files.reopenReadOnly dirFd) eintrFuel with
    | .ok dupFd =>
      let r ← readDirStreamLoop files dupFd "." #[] streamFuel
      match r with
      | .error err =>
        closeQuiet files dupFd
        pure (.error err)
      | .ok entries =>
        match ← closeCheck files dupFd (some ".") with
        | .error ce => pure (.error ce)
        | .ok () => pure (.ok entries)
    | .error _ =>
      match ← retryEintr (files.lseek dirFd 0 .seekSet) eintrFuel with
      | .error se => pure (.error (mapErrno (some ".") "lseek" se))
      | .ok _ => readDirStreamLoop files dirFd "." #[] streamFuel
  match rawRes with
  | .error err => return .error err
  | .ok raw => return parseUniqueEntryNames raw

/-- Read entire regular child file `name` under `dirFd` without following symlinks or blocking on special files. -/
def readRegularAtPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dirFd : fd) (name : EntryName)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    m (Except FsError ByteArray) := do
  let flags : OpenFlags :=
    { access := .rdonly, nofollow := true, nonblock := true, cloexec := true, noctty := true }
  match ← retryEintr (files.openat (some dirFd) name.val.toUTF8 flags 0) eintrFuel with
  | .ok h => readRegularFd files h name.val streamFuel
  | .error e =>
    if e == Errno.ELOOP then
      return .error (mapErrno (some name.val) "openat" Errno.EINVAL)
    else if e == Errno.ENXIO then
      match ← retryEintr (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) eintrFuel with
      | .ok st =>
        if st.kind == .dir then return .error (mapErrno (some name.val) "openat" Errno.EISDIR)
        else return .error (mapErrno (some name.val) "openat" Errno.EINVAL)
      | .error _ => return .error (mapErrno (some name.val) "openat" Errno.EINVAL)
    else
      return .error (mapErrno (some name.val) "openat" e)

/-- Atomically create a new regular file `name` under `dirFd` (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644` masked by `umask` matching `RawDirOpsM.createFileAt`), unlinking on write failure. -/
def createFileAtPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dirFd : fd) (name : EntryName)
    (bytes : ByteArray) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError Unit) := do
  let flags : OpenFlags :=
    { access := .wronly, creat := true, excl := true, nofollow := true, cloexec := true }
  match ← retryEintr (files.openat (some dirFd) name.val.toUTF8 flags 0o644) eintrFuel with
  | .error e => return .error (mapErrno (some name.val) "openat" e)
  | .ok h =>
    match ← writeAllAndClose files h name.val bytes eintrFuel with
    | .ok () => return .ok ()
    | .error err =>
      let _ ← files.unlinkat (some dirFd) name.val.toUTF8 false
      return .error err

/-- Open child `name` under `dirFd` without following symlinks and acquire an advisory `flock(2)` lock returning `fd` directly (`0o644` masked by `umask` when `createIfMissing = true`, matching `RawDirOpsM.acquireLockAt`). -/
def acquireLockAtPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dirFd : fd) (name : EntryName)
    (mode : LockMode) (createIfMissing nonBlocking : Bool)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError fd) := do
  let baseFlags : OpenFlags :=
    { access := .rdonly, nofollow := true, cloexec := true, nonblock := true }
  let r0 ← retryEintr (files.openat (some dirFd) name.val.toUTF8 baseFlags 0) eintrFuel
  let r1 ← match r0 with
    | .ok h => pure (.ok h)
    | .error e =>
      if e == Errno.ENOENT && createIfMissing then
        retryEintr (files.openat (some dirFd) name.val.toUTF8 { baseFlags with creat := true } 0o644) eintrFuel
      else
        pure (.error e)
  match r1 with
  | .error e =>
    if e == Errno.ELOOP || e == Errno.ENXIO then
      return .error (mapErrno (some name.val) "openat" Errno.EINVAL)
    else
      return .error (mapErrno (some name.val) "openat" e)
  | .ok h => finishLockFd files h name.val mode nonBlocking eintrFuel

/-- Build a parametric `RawDirOpsM m fd fd` bundle purely over `FilesOpsM m fd` and temporary sequence source `nextTempSeq` (`createDirAt` preserves historical `0o755` and `createFileAt`/`acquireLockAt` preserve `0o644`, all masked by process `umask`). -/
def mkRawDirOpsM {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (nextTempSeq : m Nat)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    RawDirOpsM m fd fd :=
  { openDir := fun rootPath => openDirPure files rootPath eintrFuel
    openDirAt := fun dirFd name => openDirAtPure files dirFd name eintrFuel
    closeDir := fun dirFd => closeCheck files dirFd none
    fstatDir := fun dirFd => do
      match ← files.fstat dirFd with
      | .ok st => return .ok (statInfoToFileStat st)
      | .error e => return .error (mapErrno none "fstat" e)
    lstatAt := fun dirFd name => do
      match ← retryEintr (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) eintrFuel with
      | .ok st => return .ok (statInfoToFileStat st)
      | .error e => return .error (mapErrno (some name.val) "fstatat" e)
    readDirAt := fun dirFd => readDirAtPure files dirFd eintrFuel streamFuel
    createDirAt := fun dirFd name => do
      match ← retryEintr (files.mkdirat (some dirFd) name.val.toUTF8 0o755) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some name.val) "mkdirat" e)
    readRegularAt := fun dirFd name => readRegularAtPure files dirFd name eintrFuel streamFuel
    createFileAt := fun dirFd name bytes => createFileAtPure files dirFd name bytes eintrFuel
    renameAt := fun srcFd srcName dstFd dstName => do
      match ← retryEintr (files.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some srcName.val) "renameat2" e)
    unlinkAt := fun dirFd name isDir =>
      if isDir then removeDirAtOpt files (some dirFd) name.val eintrFuel
      else do
        match ← retryEintr (files.unlinkat (some dirFd) name.val.toUTF8 false) eintrFuel with
        | .ok () => return .ok ()
        | .error e => return .error (mapErrno (some name.val) "unlinkat" e)
    symlinkAt := fun target dirFd name => do
      if target.isEmpty || target.toList.contains (Char.ofNat 0) then
        return .error (mapErrno (some name.val) "symlinkat" Errno.EINVAL)
      match ← retryEintr (files.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8) eintrFuel with
      | .ok () => return .ok ()
      | .error e => return .error (mapErrno (some name.val) "symlinkat" e)
    acquireLockAt := fun dirFd name mode createIfMissing nonBlocking =>
      acquireLockAtPure files dirFd name mode createIfMissing nonBlocking eintrFuel
    releaseLock := fun handle => releaseLockPure files handle eintrFuel
    freshTempName := do
      let n ← nextTempSeq
      return { val := ".t." ++ toString n, valid := validSeg_dotT n } }

/-- Default Linux `RawFsOpsM` backed directly by `LinuxSyscall.Files.defaultOps` and `LinuxSyscall.TimeRand.defaultOps`. -/
def defaultOps : RawFsOpsM IO LinuxSyscall.RawFd :=
  mkRawFsOpsM LinuxSyscall.Files.defaultOps (nextTimeRandNonce LinuxSyscall.TimeRand.defaultOps)

/-- Default Linux `RawDirOpsM` backed directly by `LinuxSyscall.Files.defaultOps` and `LinuxSyscall.TimeRand.defaultOps`. -/
def defaultDirOps : RawDirOpsM IO LinuxSyscall.RawFd LinuxSyscall.RawFd :=
  mkRawDirOpsM LinuxSyscall.Files.defaultOps (nextTimeRandNonce LinuxSyscall.TimeRand.defaultOps)

end LeanSwe.Fs.SysBridge

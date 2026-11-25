import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model

namespace LeanSwe.Fs.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model (mapRawError isValidRawPath)

/-- Map a Linux `Errno` honestly into `FsError` (`EMFILE`/`ENFILE` map to `.ioError`; never returns `.wouldBlock`). -/
def mapErrno (path? : Option String) (ctx : String) (e : Errno) : FsError :=
  let kind :=
    if e == Errno.ENOENT then .notFound
    else if e == Errno.EEXIST then .alreadyExists
    else if e == Errno.EACCES || e == Errno.EPERM || e == Errno.EROFS then .permissionDenied
    else if e == Errno.EISDIR then .isADirectory
    else if e == Errno.ENOTDIR then .notADirectory
    else if e == Errno.ENOTEMPTY then .notEmpty
    else if e == Errno.EINVAL || e == Errno.ENAMETOOLONG then .invalidInput
    else if e == Errno.ENOSYS || e == Errno.EOPNOTSUPP then .unsupported
    else .ioError
  { kind := kind
    path := path?
    errnoCode := some e
    message := s!"{ctx}: {Errno.name e}" }

/-- Convert Linux `StatInfo` into `FileStat`. -/
def statInfoToFileStat (st : StatInfo) : FileStat :=
  let kind : EntryKind :=
    match st.kind with
    | .reg => .file
    | .dir => .dir
    | .symlink => .symlink
    | _ => .other
  { kind := kind
    byteSize := st.size
    mode := st.mode.toNat
    modifiedSec := st.mtimeSec
    modifiedNsec := st.mtimeNsec.toNat
    accessedSec := st.atimeSec
    accessedNsec := st.atimeNsec.toNat }

/-- Parse and deduplicate raw OS directory entry names into `EntryName` values. -/
def parseUniqueEntryNames (raw : Array String) : Except FsError (Array EntryName) := do
  let mut out : Array EntryName := #[]
  for s in raw do
    let name ← EntryName.parse s
    if !out.contains name then
      out := out.push name
  return out

/-- Default bounded chunk count for reading regular files and directory streams (`64 GiB` at `64 KiB`/chunk). -/
def DEFAULT_STREAM_FUEL : Nat := 1048576

/-- Default read chunk size (`64 KiB`). -/
def READ_CHUNK_SIZE : UInt32 := 65536

/-- Default write chunk size (`64 KiB`). -/
def WRITE_CHUNK_SIZE : Nat := 65536

/-- Default `getdents64` buffer size (`8 KiB`). -/
def GETDENTS_BUF_SIZE : UInt32 := 8192

/-- Maximum `readlink` / `getcwd` buffer cap (`1 MiB`). -/
def MAX_PATH_BUF_CAP : UInt32 := 1048576

/-- Maximum Linux symlink expansion depth (`MAXSYMLINKS = 40`). -/
def MAX_SYMLINK_DEPTH : Nat := 40

/-- Close `h`, ignoring Linux `EINTR` per `close(2)` semantics and reporting any other error. -/
def closeCheck {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path? : Option String) : m (Except FsError Unit) := do
  match ← files.close h with
  | .ok () => return .ok ()
  | .error e =>
    if e == Errno.EINTR then return .ok ()
    else return .error (mapErrno path? "close" e)

/-- Best-effort close of `h` on error cleanup paths. -/
def closeQuiet {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) : m Unit := do
  let _ ← files.close h
  return ()

/-- Loop reading chunks from regular file `h` until EOF, retrying `EINTR`/`EAGAIN`, and always closing `h`. -/
def readAllChunksLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String)
    (chunks : Array ByteArray) (total : Nat) : Nat → m (Except FsError ByteArray)
  | 0 => do
    closeQuiet files h
    return .error (mapErrno (some path) "read" Errno.EIO)
  | fuel + 1 => do
    match ← files.read h READ_CHUNK_SIZE with
    | .error e =>
      if e == Errno.EINTR || e == Errno.EAGAIN then
        readAllChunksLoop files h path chunks total fuel
      else
        closeQuiet files h
        return .error (mapErrno (some path) "read" e)
    | .ok chunk =>
      if chunk.size == 0 then
        match ← closeCheck files h (some path) with
        | .error ce => return .error ce
        | .ok () => return .ok (concatChunks chunks total)
      else
        readAllChunksLoop files h path (chunks.push chunk) (total + chunk.size) fuel

/-- Validate regular file via `fstat`, clear `O_NONBLOCK` if set, read to EOF, and close `h`. -/
def readRegularFd {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String)
    (streamFuel : Nat := DEFAULT_STREAM_FUEL) : m (Except FsError ByteArray) := do
  match ← files.fstat h with
  | .error e =>
    closeQuiet files h
    return .error (mapErrno (some path) "fstat" e)
  | .ok st =>
    if st.kind == .dir then
      closeQuiet files h
      return .error (mapErrno (some path) "read" Errno.EISDIR)
    else if st.kind != .reg then
      closeQuiet files h
      return .error (mapErrno (some path) "read" Errno.EINVAL)
    else
      match ← files.fcntl h .getFl with
      | .error e =>
        closeQuiet files h
        return .error (mapErrno (some path) "fcntl" e)
      | .ok fl =>
        if (fl &&& ((1 : UInt32) <<< 8)) != 0 then
          let appendBit := (fl &&& ((1 : UInt32) <<< 5)) != 0
          match ← files.fcntl h (.setFl false appendBit) with
          | .error e =>
            closeQuiet files h
            return .error (mapErrno (some path) "fcntl" e)
          | .ok _ => readAllChunksLoop files h path #[] 0 streamFuel
        else
          readAllChunksLoop files h path #[] 0 streamFuel

/-- Loop writing all bytes of `data` from `off` to `h`, retrying `EINTR`, and always closing `h`. -/
def writeAllLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String) (data : ByteArray)
    (off : Nat) : Nat → m (Except FsError Unit)
  | 0 => do
    closeQuiet files h
    return .error (mapErrno (some path) "write" Errno.EIO)
  | fuel + 1 => do
    if off >= data.size then
      closeCheck files h (some path)
    else
      let sliceEnd := min data.size (off + WRITE_CHUNK_SIZE)
      let chunk := data.extract off sliceEnd
      match ← files.write h chunk with
      | .error e =>
        if e == Errno.EINTR then
          writeAllLoop files h path data off fuel
        else
          closeQuiet files h
          return .error (mapErrno (some path) "write" e)
      | .ok n =>
        if n == 0 then
          closeQuiet files h
          return .error (mapErrno (some path) "write" Errno.EIO)
        else
          writeAllLoop files h path data (off + n.toNat) fuel

/-- Write all of `data` to `h` and close `h`, reporting the first write or close error. -/
def writeAllAndClose {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String) (data : ByteArray)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError Unit) :=
  writeAllLoop files h path data 0 (data.size + eintrFuel + 1)

/-- Locate the first NUL byte in `bs` within `[pos, stop)`. -/
def findNulByteAux (bs : ByteArray) (pos stop : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if _ : pos < stop then
      if h2 : pos < bs.size then
        let b := bs[pos]
        if b == 0 then some pos
        else findNulByteAux bs (pos + 1) stop fuel
      else none
    else none

/-- Decode one `linux_dirent64` entry at `pos`, returning `(nameBytes, nextPos)`. -/
def parseDirent64One (bs : ByteArray) (pos : Nat) : Option (ByteArray × Nat) :=
  if pos + 20 > bs.size then none
  else
    let lo := (bs.get! (pos + 16)).toNat
    let hi := (bs.get! (pos + 17)).toNat
    let reclen := lo + hi * 256
    if reclen < 24 || reclen % 8 != 0 || pos + reclen > bs.size then none
    else
      match findNulByteAux bs (pos + 19) (pos + reclen) (reclen - 18) with
      | none => none
      | some nulPos =>
        if nulPos == pos + 19 then none
        else some (bs.extract (pos + 19) nulPos, pos + reclen)

/-- Decode a raw `getdents64` buffer into non-`.`/non-`..` UTF-8 entry names. -/
def parseDirents64Aux (bs : ByteArray) (pos : Nat) (acc : Array String) (path : String) :
    Nat → Except FsError (Array String)
  | 0 => .error (mapErrno (some path) "getdents64" Errno.EIO)
  | fuel + 1 =>
    if pos == bs.size then .ok acc
    else
      match parseDirent64One bs pos with
      | none => .error (mapErrno (some path) "getdents64" Errno.EIO)
      | some (nameBytes, nextPos) =>
        match String.fromUTF8? nameBytes with
        | none =>
          .error { kind := .invalidInput, path := some path, errnoCode := some Errno.EINVAL,
                   message := s!"invalid UTF-8 directory entry in '{path}'" }
        | some nm =>
          let acc' := if nm == "." || nm == ".." then acc else acc.push nm
          parseDirents64Aux bs nextPos acc' path fuel

/-- Decode an entire raw `getdents64` buffer into entry names (excluding `.` and `..`). -/
def parseDirents64 (bs : ByteArray) (path : String) : Except FsError (Array String) :=
  parseDirents64Aux bs 0 #[] path (bs.size + 1)

/-- Loop reading `getdents64` batches from `h` until EOF, accumulating entry names. -/
def readDirStreamLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String)
    (acc : Array String) : Nat → m (Except FsError (Array String))
  | 0 => return .error (mapErrno (some path) "getdents64" Errno.EIO)
  | fuel + 1 => do
    match ← files.getdents64 h GETDENTS_BUF_SIZE with
    | .error e =>
      if e == Errno.EINTR then
        readDirStreamLoop files h path acc fuel
      else
        return .error (mapErrno (some path) "getdents64" e)
    | .ok buf =>
      if buf.size == 0 then
        return .ok acc
      else
        match parseDirents64Aux buf 0 acc path (buf.size + 1) with
        | .error pe => return .error pe
        | .ok acc' => readDirStreamLoop files h path acc' fuel

/-- Read a symlink target via `readlinkat`, doubling buffer capacity up to `MAX_PATH_BUF_CAP`. -/
def readLinkLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String) (cap : UInt32) (eintrFuel : Nat) :
    Nat → m (Except FsError String)
  | 0 => return .error (mapErrno (some path) "readlink" Errno.ENAMETOOLONG)
  | fuel + 1 => do
    match ← retryEintr (files.readlinkat none path.toUTF8 cap) eintrFuel with
    | .error e => return .error (mapErrno (some path) "readlink" e)
    | .ok bs =>
      if bs.size < cap.toNat then
        match String.fromUTF8? bs with
        | some s => return .ok s
        | none =>
          return .error { kind := .invalidInput, path := some path, errnoCode := some Errno.EINVAL,
                          message := s!"invalid UTF-8 symlink target at '{path}'" }
      else if cap >= MAX_PATH_BUF_CAP then
        return .error (mapErrno (some path) "readlink" Errno.ENAMETOOLONG)
      else
        readLinkLoop files path (min (cap * 2) MAX_PATH_BUF_CAP) eintrFuel fuel

/-- Query the current working directory via `getcwd`, doubling buffer capacity on `ERANGE` up to `MAX_PATH_BUF_CAP`. -/
def getcwdLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (cap : UInt32) (eintrFuel : Nat) :
    Nat → m (Except FsError String)
  | 0 => return .error (mapErrno none "getcwd" Errno.ENAMETOOLONG)
  | fuel + 1 => do
    match ← retryEintr (files.getcwd cap) eintrFuel with
    | .error e =>
      if e == Errno.ERANGE && cap < MAX_PATH_BUF_CAP then
        getcwdLoop files (min (cap * 2) MAX_PATH_BUF_CAP) eintrFuel fuel
      else
        return .error (mapErrno none "getcwd" e)
    | .ok bs =>
      match String.fromUTF8? bs with
      | some s => return .ok s
      | none =>
        return .error { kind := .invalidInput, path := none, errnoCode := some Errno.EINVAL,
                        message := "invalid UTF-8 current working directory" }

/-- Render reversed canonical path segments as an absolute POSIX path string. -/
def renderAbsRev (rev : List String) : String :=
  if rev.isEmpty then "/" else "/" ++ String.intercalate "/" rev.reverse

/-- Split a path string into non-empty slash-delimited segments. -/
def splitNonEmptySegs (p : String) : List String :=
  (p.splitOn "/").filter (!·.isEmpty)

/-- Iterative POSIX `realpath` resolution loop over `fstatat(AT_SYMLINK_NOFOLLOW)` and `readlinkat`. -/
def realPathLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (origPath : String) (eintrFuel : Nat)
    (resolvedRev : List String) (queue : List String) (trailingSlash : Bool) (symLeft : Nat) :
    Nat → m (Except FsError String)
  | 0 => return .error (mapErrno (some origPath) "realpath" Errno.ELOOP)
  | fuel + 1 => do
    match queue with
    | [] =>
      let cur := renderAbsRev resolvedRev
      match ← retryEintr (files.fstatat none cur.toUTF8 { symlinkNofollow := true }) eintrFuel with
      | .error e => return .error (mapErrno (some origPath) "realpath" e)
      | .ok st =>
        if trailingSlash && st.kind != .dir then
          return .error (mapErrno (some origPath) "realpath" Errno.ENOTDIR)
        else
          return .ok cur
    | seg :: rest =>
      if seg == "." then
        realPathLoop files origPath eintrFuel resolvedRev rest trailingSlash symLeft fuel
      else if seg == ".." then
        let cur := renderAbsRev resolvedRev
        match ← retryEintr (files.fstatat none cur.toUTF8 { symlinkNofollow := true }) eintrFuel with
        | .error e => return .error (mapErrno (some origPath) "realpath" e)
        | .ok st =>
          if st.kind != .dir then
            return .error (mapErrno (some origPath) "realpath" Errno.ENOTDIR)
          else
            let popped := match resolvedRev with | [] => [] | _ :: tl => tl
            realPathLoop files origPath eintrFuel popped rest trailingSlash symLeft fuel
      else
        let nextRev := seg :: resolvedRev
        let cand := renderAbsRev nextRev
        match ← retryEintr (files.fstatat none cand.toUTF8 { symlinkNofollow := true }) eintrFuel with
        | .error e => return .error (mapErrno (some origPath) "realpath" e)
        | .ok st =>
          if st.kind == .symlink then
            if symLeft == 0 then
              return .error (mapErrno (some origPath) "realpath" Errno.ELOOP)
            else
              match ← readLinkLoop files cand 256 eintrFuel 13 with
              | .error e => return .error { e with path := some origPath }
              | .ok target =>
                let tgtAbs := target.startsWith "/"
                let tgtSegs := splitNonEmptySegs target
                let tgtTrail := target.length > 1 && target.endsWith "/"
                let nextResolved := if tgtAbs then [] else resolvedRev
                let nextTrail := if rest.isEmpty then (trailingSlash || tgtTrail) else trailingSlash
                realPathLoop files origPath eintrFuel nextResolved (tgtSegs ++ rest) nextTrail (symLeft - 1) fuel
          else if st.kind == .dir then
            realPathLoop files origPath eintrFuel nextRev rest trailingSlash symLeft fuel
          else if !rest.isEmpty || trailingSlash then
            return .error (mapErrno (some origPath) "realpath" Errno.ENOTDIR)
          else
            return .ok cand

/-- Resolve `path` to a canonical absolute POSIX path via `getcwd`, `fstatat`, and `readlinkat`. -/
def realPathPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except FsError String) := do
  if path.isEmpty then
    return .error (mapErrno (some path) "realpath" Errno.ENOENT)
  else if path.toList.contains (Char.ofNat 0) then
    return .error (mapErrno (some path) "realpath" Errno.EINVAL)
  else
    let isAbs := path.startsWith "/"
    let trailingSlash := path.length > 1 && path.endsWith "/"
    let segs := splitNonEmptySegs path
    let startRev? : Except FsError (List String) ←
      if isAbs then
        pure (.ok [])
      else do
        match ← getcwdLoop files 4096 eintrFuel 9 with
        | .error e => pure (.error { e with path := some path })
        | .ok cwdStr => pure (.ok (splitNonEmptySegs cwdStr).reverse)
    match startRev? with
    | .error e => return .error e
    | .ok startRev =>
      realPathLoop files path eintrFuel startRev segs trailingSlash MAX_SYMLINK_DEPTH (segs.length + 4096)

/-- Validate an opened lock descriptor (`S_ISREG`), apply `flock(2)`, and return `h` directly. -/
def finishLockFd {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (path : String) (mode : LockMode) (nonBlocking : Bool)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError fd) := do
  match ← files.fstat h with
  | .error e =>
    closeQuiet files h
    return .error (mapErrno (some path) "fstat" e)
  | .ok st =>
    if st.kind == .dir then
      closeQuiet files h
      return .error (mapErrno (some path) "flock" Errno.EISDIR)
    else if st.kind != .reg then
      closeQuiet files h
      return .error (mapErrno (some path) "flock" Errno.EINVAL)
    else
      let op : FlockOp := match mode with
        | .shared => .shared nonBlocking
        | .exclusive => .exclusive nonBlocking
      match ← retryEintr (files.flock h op) eintrFuel with
      | .error e =>
        closeQuiet files h
        if nonBlocking && e == Errno.EAGAIN then
          return .error (mapRawError (.wouldBlock (some path) e "resource temporarily unavailable"))
        else
          return .error (mapErrno (some path) "flock" e)
      | .ok () => return .ok h

/-- Release an advisory lock descriptor (`flock(LOCK_UN)` followed by `close`). -/
def releaseLockPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (h : fd) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except FsError Unit) := do
  let unlockRes ← retryEintr (files.flock h .unlock) eintrFuel
  let closeRes ← closeCheck files h none
  match unlockRes with
  | .error e => return .error (mapErrno none "flock" e)
  | .ok () => return closeRes

/-- Open a regular file for reading without blocking on FIFOs/sockets, validate `S_ISREG`, and read all bytes. -/
def readBytesPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    m (Except FsError ByteArray) := do
  if !isValidRawPath path then
    return .error (mapErrno (some path) "open" Errno.EINVAL)
  let flags : OpenFlags :=
    { access := .rdonly, nonblock := true, cloexec := true, noctty := true }
  match ← retryEintr (files.openat none path.toUTF8 flags 0) eintrFuel with
  | .ok h => readRegularFd files h path streamFuel
  | .error e =>
    if e == Errno.ENXIO then
      match ← retryEintr (files.fstatat none path.toUTF8 {}) eintrFuel with
      | .ok st =>
        if st.kind == .dir then return .error (mapErrno (some path) "open" Errno.EISDIR)
        else return .error (mapErrno (some path) "open" Errno.EINVAL)
      | .error _ =>
        match ← retryEintr (files.fstatat none path.toUTF8 { symlinkNofollow := true }) eintrFuel with
        | .ok st =>
          if st.kind == .dir then return .error (mapErrno (some path) "open" Errno.EISDIR)
          else return .error (mapErrno (some path) "open" Errno.EINVAL)
        | .error _ => return .error (mapErrno (some path) "open" Errno.EINVAL)
    else
      return .error (mapErrno (some path) "open" e)

/-- Exclusively create a new regular file without following symlinks (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644` masked by `umask` matching historical `createFileNew`), unlinking on write failure. -/
def createFileNewPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String) (bytes : ByteArray)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError Unit) := do
  if !isValidRawPath path then
    return .error (mapErrno (some path) "open" Errno.EINVAL)
  let flags : OpenFlags :=
    { access := .wronly, creat := true, excl := true, nofollow := true, cloexec := true }
  match ← retryEintr (files.openat none path.toUTF8 flags 0o644) eintrFuel with
  | .error e => return .error (mapErrno (some path) "open" e)
  | .ok h =>
    match ← writeAllAndClose files h path bytes eintrFuel with
    | .ok () => return .ok ()
    | .error err =>
      let _ ← files.unlinkat none path.toUTF8 false
      return .error err

/-- Open `path` without following symlinks and acquire an advisory `flock(2)` lock returning `fd` directly (`0o644` masked by `umask` when `createIfMissing = true`, matching historical `acquireLock`). -/
def acquireLockPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String) (mode : LockMode) (createIfMissing nonBlocking : Bool)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except FsError fd) := do
  if !isValidRawPath path then
    return .error (mapErrno (some path) "open" Errno.EINVAL)
  let baseFlags : OpenFlags :=
    { access := .rdonly, nofollow := true, cloexec := true, nonblock := true }
  let openRes ← retryEintr (files.openat none path.toUTF8 baseFlags 0) eintrFuel
  let fdRes ← match openRes with
    | .ok h => pure (.ok h)
    | .error e =>
      if e == Errno.ENOENT && createIfMissing then
        retryEintr (files.openat none path.toUTF8 { baseFlags with creat := true } 0o644) eintrFuel
      else
        pure (.error e)
  match fdRes with
  | .error e =>
    if e == Errno.ELOOP || e == Errno.ENXIO then
      return .error (mapErrno (some path) "open" Errno.EINVAL)
    else
      return .error (mapErrno (some path) "open" e)
  | .ok h => finishLockFd files h path mode nonBlocking eintrFuel

/-- List immediate entry names inside directory `path` via `openat` + `getdents64` + `close`. -/
def readDirPure {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (path : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) (streamFuel : Nat := DEFAULT_STREAM_FUEL) :
    m (Except FsError (Array String)) := do
  let flags : OpenFlags := { access := .rdonly, directory := true, cloexec := true }
  match ← retryEintr (files.openat none path.toUTF8 flags 0) eintrFuel with
  | .error e => return .error (mapErrno (some path) "open" e)
  | .ok h =>
    let res ← readDirStreamLoop files h path #[] streamFuel
    match res with
    | .error err =>
      closeQuiet files h
      return .error err
    | .ok entries =>
      match ← closeCheck files h (some path) with
      | .error ce => return .error ce
      | .ok () => return .ok entries

/-- Remove an empty directory via `unlinkat(..., true)`, mapping `EEXIST` honestly to `.notEmpty`. -/
def removeDirAtOpt {m : Type → Type} [Monad m] {fd : Type}
    (files : FilesOpsM m fd) (dir : Option fd) (path : String) (eintrFuel : Nat) :
    m (Except FsError Unit) := do
  match ← retryEintr (files.unlinkat dir path.toUTF8 true) eintrFuel with
  | .ok () => return .ok ()
  | .error e =>
    if e == Errno.EEXIST then
      return .error (mapErrno (some path) "rmdir" Errno.ENOTEMPTY)
    else
      return .error (mapErrno (some path) "rmdir" e)

/-- Decode a `ByteArray` in little-endian byte order into `Nat`. -/
def decodeNatLE (bs : ByteArray) : Nat :=
  bs.data.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- Sample a fresh temporary-filename nonce statelessly from `CLOCK_MONOTONIC` and `getrandom(8)`. -/
def nextTimeRandNonce {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) : m Nat := do
  let ns : Nat ← match ← timeRand.clock_gettime .monotonic with
    | .ok ts => pure (ts.sec.toInt.toNat * 1000000000 + ts.nsec.toNat)
    | .error _ => pure 0
  let rand : Nat ← match ← timeRand.getrandom 8 {} with
    | .ok bs => pure (decodeNatLE bs)
    | .error _ => pure 0
  return ns * 18446744073709551616 + rand

end LeanSwe.Fs.SysBridge

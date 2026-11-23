import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model

namespace LeanSwe.Fs.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs

/-- Filesystem syscall and monotonic temporary-sequence capability parameterized over handle type `fd`. -/
structure FsFilesCapM (fd : Type) (m : Type → Type) where
  /-- Verified `LinuxSyscall.Files` syscall bundle. -/
  files : FilesOpsM m fd
  /-- Monotonic sequence source for sibling temporary filenames. -/
  nextTempSeq : m Nat

/-- Concrete healthy-model `FsFilesCapM` specialized to `LinuxSyscall.Files.HandleId`. -/
abbrev HealthyFilesCapM (m : Type → Type) := FsFilesCapM HandleId m

/-- Abstract healthy-OS world state for `LeanSwe.Fs`, pairing `LinuxSyscall.Files.HealthyEnv` with the monotonic temp-name counter. -/
structure FsWorld where
  /-- Underlying healthy Linux filesystem environment. -/
  env : HealthyEnv := HealthyEnv.initial
  /-- Monotonic temporary-name sequence counter. -/
  tempSeq : Nat := 0
  deriving BEq, Inhabited

/-- Well-formedness invariant on `FsWorld`: underlying healthy Linux environment is well-formed (no ambient seccomp interception). -/
def fsWorldWf (w : FsWorld) : Bool :=
  w.env.wf

/-- One executed Linux filesystem syscall and its observed outcome. -/
abbrev KernelStep := FilesReq × FilesOutcome

/-- Convert Linux `StatInfo` into public `FileStat`. -/
def toFileStat (st : StatInfo) : FileStat :=
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

/-- Model path validity predicate matching `SysBridge.isValidRawPath`. -/
def isValidRawPathModel (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

/-- Canonical open flags for non-blocking regular-file reads (`O_RDONLY | O_NONBLOCK | O_CLOEXEC | O_NOCTTY`). -/
def readOpenFlags : OpenFlags :=
  { access := .rdonly, nonblock := true, cloexec := true, noctty := true }

/-- Canonical open flags for symlink-refusing confined regular-file reads (`O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC | O_NOCTTY`). -/
def readAtOpenFlags : OpenFlags :=
  { access := .rdonly, nofollow := true, nonblock := true, cloexec := true, noctty := true }

/-- Canonical open flags for truncating writes (`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`). -/
def writeOpenFlags : OpenFlags :=
  { access := .wronly, creat := true, trunc := true, cloexec := true }

/-- Canonical open flags for exclusive symlink-refusing file creation (`O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC`). -/
def createNewOpenFlags : OpenFlags :=
  { access := .wronly, creat := true, excl := true, nofollow := true, cloexec := true }

/-- Canonical open flags for appending writes (`O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC`). -/
def appendOpenFlags : OpenFlags :=
  { access := .wronly, creat := true, append := true, cloexec := true }

/-- Canonical open flags for opening directories (`O_RDONLY | O_DIRECTORY | O_CLOEXEC`). -/
def dirOpenFlags : OpenFlags :=
  { access := .rdonly, directory := true, cloexec := true }

/-- Translate `LockMode` and `nonBlocking` into the corresponding `FlockOp`. -/
def lockModeToFlockOp (mode : LockMode) (nonBlocking : Bool) : FlockOp :=
  match mode with
  | .shared => .shared nonBlocking
  | .exclusive => .exclusive nonBlocking

/-- Explicit-trace reflexive-transitive closure of verified `LinuxSyscall.Files.healthyStep` transitions. -/
inductive HealthyFilesSteps : HealthyEnv → List KernelStep → HealthyEnv → Prop where
  /-- Zero kernel syscall steps. -/
  | nil (e : HealthyEnv) : HealthyFilesSteps e [] e
  /-- One verified `healthyStep` prepended to a healthy step trace. -/
  | cons {e1 e2 e3 : HealthyEnv} (req : FilesReq) (out : FilesOutcome) (rest : List KernelStep)
      (hStep : healthyStep e1 req out = some e2)
      (hRest : HealthyFilesSteps e2 rest e3) :
      HealthyFilesSteps e1 ((req, out) :: rest) e3

/-- Return the newly allocated `HandleId` when a kernel step opens a file descriptor. -/
def stepOpenedFd : KernelStep → Option HandleId
  | (.openat _ _ _ _, .opened hid) => some hid
  | (.openat2 _ _ _, .opened hid) => some hid
  | (.reopenReadOnly _, .opened hid) => some hid
  | _ => none

/-- Return the closed `HandleId` when a kernel step invokes `close`. -/
def stepClosedFd : KernelStep → Option HandleId
  | (.close hid, _) => some hid
  | _ => none

/-- Descriptor ownership discipline across a kernel trace: every opened handle is tracked and only held handles may be closed. -/
inductive TraceFds : List HandleId → List KernelStep → List HandleId → Prop where
  /-- Empty trace preserves held descriptors. -/
  | nil (held : List HandleId) : TraceFds held [] held
  /-- Single kernel step pushes opened handle or pops closed held handle. -/
  | step {held held' held'' : List HandleId} {s : KernelStep} {rest : List KernelStep}
      (hOne :
        match stepOpenedFd s, stepClosedFd s with
        | some h, none => held' = h :: held
        | none, some h => h ∈ held ∧ held' = held.erase h
        | none, none => held' = held
        | some _, some _ => False)
      (hRest : TraceFds held' rest held'') :
      TraceFds held (s :: rest) held''

/-- Sound closed-operation kernel trace transition: preserves `fsWorldWf`, executes verified `healthyStep`s in `tr`, leaks zero FDs and closes zero foreign FDs (`TraceFds [] tr []`), and advances `tempSeq` monotonically. -/
def FsWorldTrace (w : FsWorld) (tr : List KernelStep) (w' : FsWorld) : Prop :=
  fsWorldWf w' = true ∧
  HealthyFilesSteps w.env tr w'.env ∧
  TraceFds [] tr [] ∧
  w.tempSeq ≤ w'.tempSeq

/-- Contiguous subtrace relation `sub` inside `tr`. -/
def Subtrace (sub tr : List KernelStep) : Prop :=
  ∃ pre post, tr = pre ++ sub ++ post

/-- Concatenate all bytes actually written to descriptor `h` across `tr`. -/
def writtenBytesOn (h : HandleId) (tr : List KernelStep) : ByteArray :=
  tr.foldl (fun acc step =>
    match step with
    | (.write hid chunk, .u32 n) =>
      if hid == h then acc ++ chunk.extract 0 n.toNat else acc
    | _ => acc) ByteArray.empty

/-- Concatenate all bytes read from descriptor `h` across `tr`. -/
def readBytesOn (h : HandleId) (tr : List KernelStep) : ByteArray :=
  tr.foldl (fun acc step =>
    match step with
    | (.read hid _, .bytes chunk) =>
      if hid == h then acc ++ chunk else acc
    | _ => acc) ByteArray.empty

/-- Trace witness that `fstatat` succeeded on `(dir, path, follow)` and yielded `st = toFileStat rawSt`. -/
def StatTrace (dir : Option HandleId) (path : ByteArray) (follow : Bool)
    (st : FileStat) (tr : List KernelStep) : Prop :=
  ∃ rawSt, (.fstatat dir path { symlinkNofollow := !follow }, .statted rawSt) ∈ tr ∧
    st = toFileStat rawSt

/-- Trace witness that `fstat h` succeeded and yielded `st = toFileStat rawSt`. -/
def FstatTrace (h : HandleId) (st : FileStat) (tr : List KernelStep) : Prop :=
  ∃ rawSt, (.fstat h, .statted rawSt) ∈ tr ∧ st = toFileStat rawSt

/-- Trace witness that `mkdirat` succeeded on `(dir, path)` with mode `0o755`. -/
def MkdirTrace (dir : Option HandleId) (path : ByteArray) (tr : List KernelStep) : Prop :=
  (.mkdirat dir path 0o755, .unit) ∈ tr

/-- Trace witness that `unlinkat` succeeded on `(dir, path, removeDir)`. -/
def UnlinkTrace (dir : Option HandleId) (path : ByteArray) (removeDir : Bool)
    (tr : List KernelStep) : Prop :=
  (.unlinkat dir path removeDir, .unit) ∈ tr

/-- Trace witness that `renameat2` succeeded from `(srcDir, src)` to `(dstDir, dst)`. -/
def RenameTrace (srcDir : Option HandleId) (src : ByteArray)
    (dstDir : Option HandleId) (dst : ByteArray) (tr : List KernelStep) : Prop :=
  (.renameat2 srcDir src dstDir dst {}, .unit) ∈ tr

/-- Trace witness that `fchmodat` succeeded on `(dir, path, mode)`. -/
def ChmodTrace (dir : Option HandleId) (path : ByteArray) (mode : Nat)
    (tr : List KernelStep) : Prop :=
  (.fchmodat dir path (UInt32.ofNat mode), .unit) ∈ tr

/-- Trace witness that `symlinkat` succeeded for `target` at `(dir, linkPath)`. -/
def SymlinkTrace (target : ByteArray) (dir : Option HandleId) (linkPath : ByteArray)
    (tr : List KernelStep) : Prop :=
  (.symlinkat target dir linkPath, .unit) ∈ tr

/-- Trace witness that `readlinkat` returned a non-truncated UTF-8 buffer decoding to `s`. -/
def ReadLinkTrace (path : ByteArray) (s : String) (tr : List KernelStep) : Prop :=
  ∃ cap bs, (.readlinkat none path cap, .bytes bs) ∈ tr ∧
    bs.size < cap.toNat ∧ String.fromUTF8? bs = some s

/-- Trace witness that `getcwd` returned a UTF-8 buffer decoding to `s`. -/
def GetcwdTrace (s : String) (tr : List KernelStep) : Prop :=
  ∃ cap bs, (.getcwd cap, .bytes bs) ∈ tr ∧ String.fromUTF8? bs = some s

/-- Trace witness that canonical path `s` is absolute (begins with `/`) and passed final `fstatat(AT_SYMLINK_NOFOLLOW)`. -/
def RealPathTrace (s : String) (tr : List KernelStep) : Prop :=
  isAbsolute s = true ∧
  ∃ rawSt, (.fstatat none s.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr

/-- Trace witness that `(dir, path)` was opened with `flags`, verified regular via `fstat`, read to 0-byte EOF with exact concatenated payload `bs`, and closed. -/
def ReadRegularTrace (dir : Option HandleId) (path : ByteArray) (flags : OpenFlags)
    (bs : ByteArray) (tr : List KernelStep) : Prop :=
  ∃ h rawSt eof trOpen trBody trClose,
    tr = trOpen ++ trBody ++ trClose ∧
    (.openat dir path flags 0, .opened h) ∈ trOpen ∧
    (.fstat h, .statted rawSt) ∈ trBody ∧
    rawSt.kind = .reg ∧
    (.read h 65536, .bytes eof) ∈ trBody ∧
    eof.size = 0 ∧
    readBytesOn h trBody = bs ∧
    (∃ co, (.close h, co) ∈ trClose)

/-- Trace witness that `(dir, path)` was opened with `(flags, mode)`, written with slices concatenating to exact `data`, and closed. -/
def WriteFileTrace (dir : Option HandleId) (path : ByteArray) (flags : OpenFlags)
    (mode : UInt32) (data : ByteArray) (tr : List KernelStep) : Prop :=
  ∃ h trOpen trBody trClose,
    tr = trOpen ++ trBody ++ trClose ∧
    (.openat dir path flags mode, .opened h) ∈ trOpen ∧
    writtenBytesOn h trBody = data ∧
    (∃ co, (.close h, co) ∈ trClose)

/-- Trace witness that `path` was opened with `O_DIRECTORY`, scanned via `getdents64` to 0-byte EOF excluding `.`/`..`, and closed. -/
def ReadDirTrace (path : ByteArray) (xs : Array String) (tr : List KernelStep) : Prop :=
  (∀ nm ∈ xs.toList, nm ≠ "." ∧ nm ≠ "..") ∧
  ∃ h eof trOpen trBody trClose,
    tr = trOpen ++ trBody ++ trClose ∧
    (.openat none path dirOpenFlags 0, .opened h) ∈ trOpen ∧
    (.getdents64 h 8192, .bytes eof) ∈ trBody ∧
    eof.size = 0 ∧
    (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ trBody ∧ buf.size > 0) ∧
    (∃ co, (.close h, co) ∈ trClose)

/-- Trace witness that an advisory `flock` was acquired on regular file `(dir, path)` without following symlinks, unlocked, and closed. -/
def FileLockTrace (dir : Option HandleId) (path : ByteArray) (mode : LockMode)
    (nonBlocking unlockOk : Bool) (tr : List KernelStep) : Prop :=
  ∃ h rawSt fl modeArg trOpen trLock trRel,
    tr = trOpen ++ trLock ++ trRel ∧
    fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
    (.openat dir path fl modeArg, .opened h) ∈ trOpen ∧
    (.fstat h, .statted rawSt) ∈ trLock ∧
    rawSt.kind = .reg ∧
    (.flock h (lockModeToFlockOp mode nonBlocking), .unit) ∈ trLock ∧
    (∃ uo, (.flock h .unlock, uo) ∈ trRel ∧ (unlockOk = true → uo = .unit)) ∧
    (∃ co, (.close h, co) ∈ trRel)

/-- Trace witness that a non-blocking advisory `flock` on regular file `(dir, path)` observed `EAGAIN` and closed the descriptor. -/
def TryLockContendedTrace (dir : Option HandleId) (path : ByteArray) (mode : LockMode)
    (tr : List KernelStep) : Prop :=
  ∃ h rawSt fl modeArg trOpen trLock trClose,
    tr = trOpen ++ trLock ++ trClose ∧
    fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
    (.openat dir path fl modeArg, .opened h) ∈ trOpen ∧
    (.fstat h, .statted rawSt) ∈ trLock ∧
    rawSt.kind = .reg ∧
    (.flock h (lockModeToFlockOp mode true), .err Errno.EAGAIN) ∈ trLock ∧
    (∃ co, (.close h, co) ∈ trClose)

/-- Witness that `p` is the UTF-8 encoding of a single-segment `EntryName` (no `/`, NUL, `.`, or `..`). -/
def isSingleEntryBytes (p : ByteArray) : Prop :=
  ∃ nm : EntryName, p = nm.val.toUTF8

/-- Real descriptor confinement predicate for every kernel request inside an open `Subtree`: forbids ambient `dir = none`, enforces `O_NOFOLLOW`/`AT_SYMLINK_NOFOLLOW`, and restricts path arguments to single-segment `EntryName`s. -/
def SubtreeConfinedReq : FilesReq → Prop
  | .openat (some _) p fl _ => fl.nofollow = true ∧ isSingleEntryBytes p
  | .fstatat (some _) p fl => fl.symlinkNofollow = true ∧ isSingleEntryBytes p
  | .mkdirat (some _) p _ => isSingleEntryBytes p
  | .unlinkat (some _) p _ => isSingleEntryBytes p
  | .renameat2 (some _) src (some _) dst _ => isSingleEntryBytes src ∧ isSingleEntryBytes dst
  | .symlinkat _ (some _) linkPath => isSingleEntryBytes linkPath
  | .fstat _ | .fcntl _ _ | .read _ _ | .write _ _ | .close _
  | .getdents64 _ _ | .reopenReadOnly _ | .lseek _ _ _ | .flock _ _ => True
  | _ => False

/-- Non-lock filesystem error invariant: diagnostic message is non-empty and kind is never `.wouldBlock`. -/
def nonLockErrOk (e : FsError) : Prop :=
  e.message ≠ "" ∧ e.kind ≠ .wouldBlock

/-- Single-step request sum for `HealthyFilesCapM` inside `Core.RefinesStepFromFinally`. -/
inductive FilesCapStepReq where
  /-- Execute one curated `LinuxSyscall.Files.FilesReq` syscall. -/
  | fileReq (req : FilesReq)
  /-- Allocate the next monotonic temporary-name sequence number. -/
  | nextTempSeq

/-- Single-step output sum for `HealthyFilesCapM` inside `Core.RefinesStepFromFinally`. -/
inductive FilesCapStepOut where
  /-- Decoded `LinuxSyscall.Files.FilesOutcome`. -/
  | fileOut (out : FilesOutcome)
  /-- Allocated temporary sequence number. -/
  | tempSeq (n : Nat)

/-- Execute one `FilesCapStepReq` against a `HealthyFilesCapM (StateM W)` capability bundle. -/
def execFilesCapStep {W : Type} (cap : HealthyFilesCapM (StateM W)) :
    FilesCapStepReq → StateM W FilesCapStepOut
  | .fileReq req => FilesCapStepOut.fileOut <$> execFilesReq cap.files req
  | .nextTempSeq => FilesCapStepOut.tempSeq <$> cap.nextTempSeq

/-- Relational healthy-OS step specification for `HealthyFilesCapM` directly over `LinuxSyscall.Files.healthyStep`. -/
def allowedFilesCapStep (w : FsWorld) (req : FilesCapStepReq) (out : FilesCapStepOut) (w' : FsWorld) : Prop :=
  match out, req with
  | .fileOut o, .fileReq r =>
    fsWorldWf w = true ∧
    healthyStep w.env r o = some w'.env ∧
    w'.tempSeq = w.tempSeq ∧
    fsWorldWf w' = true
  | .tempSeq n, .nextTempSeq =>
    fsWorldWf w = true ∧
    w'.env = w.env ∧
    n = w.tempSeq ∧
    w'.tempSeq = w.tempSeq + 1
  | _, _ => False

/-- Single-step request sum covering all 19 operations of `ScopedRawFsOpsM`. -/
inductive ScopedRawFsStepReq where
  /-- Pure `mapRawError` normalization. -/
  | mapRawError (raw : FsRawError)
  /-- `stat` (`follow = true`) or `lstat` (`follow = false`). -/
  | stat (follow : Bool) (path : String)
  /-- Unsorted `readDir` excluding `.` and `..`. -/
  | readDir (path : String)
  /-- Single-level `createDir`. -/
  | createDir (path : String)
  /-- `removeDir`. -/
  | removeDir (path : String)
  /-- `unlinkFile`. -/
  | unlinkFile (path : String)
  /-- `readBytes`. -/
  | readBytes (path : String)
  /-- `writeBytes`. -/
  | writeBytes (path : String) (data : ByteArray)
  /-- Exclusive symlink-refusing `createFileNew`. -/
  | createFileNew (path : String) (data : ByteArray)
  /-- `appendText`. -/
  | appendText (path content : String)
  /-- `rename`. -/
  | rename (src dst : String)
  /-- `chmod`. -/
  | chmod (path : String) (mode : Nat)
  /-- `symlink`. -/
  | symlink (target linkPath : String)
  /-- `readLink`. -/
  | readLink (path : String)
  /-- `realPath`. -/
  | realPath (path : String)
  /-- `cwd`. -/
  | cwd
  /-- `monotonicNonce`. -/
  | monotonicNonce
  /-- Bracketed blocking `withFileLock` exercised with pure action outcome `actRes`. -/
  | withFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- Bracketed non-blocking `tryWithFileLock` exercised with pure action outcome `actRes`. -/
  | tryWithFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step output sum for `ScopedRawFsOpsM`. -/
inductive ScopedRawFsStepOut where
  /-- Output of `mapRawError`. -/
  | mapped (err : FsError)
  /-- Output of `stat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `readDir`. -/
  | names (res : Except FsError (Array String))
  /-- Output of `Unit`-returning primitives. -/
  | unit (res : Except FsError Unit)
  /-- Output of `readBytes`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `readLink`, `realPath`, and `cwd`. -/
  | str (res : Except FsError String)
  /-- Output of `monotonicNonce`. -/
  | nonce (n : Nat)
  /-- Output of `withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `ScopedRawFsStepReq` against a `ScopedRawFsOpsM (StateM W)` bundle. -/
def execScopedRawFsStep {W : Type} (ops : ScopedRawFsOpsM (StateM W)) :
    ScopedRawFsStepReq → StateM W ScopedRawFsStepOut
  | .mapRawError raw => pure (.mapped (ops.mapRawError raw))
  | .stat follow path => ScopedRawFsStepOut.stat <$> ops.stat follow path
  | .readDir path => ScopedRawFsStepOut.names <$> ops.readDir path
  | .createDir path => ScopedRawFsStepOut.unit <$> ops.createDir path
  | .removeDir path => ScopedRawFsStepOut.unit <$> ops.removeDir path
  | .unlinkFile path => ScopedRawFsStepOut.unit <$> ops.unlinkFile path
  | .readBytes path => ScopedRawFsStepOut.bytes <$> ops.readBytes path
  | .writeBytes path data => ScopedRawFsStepOut.unit <$> ops.writeBytes path data
  | .createFileNew path data => ScopedRawFsStepOut.unit <$> ops.createFileNew path data
  | .appendText path content => ScopedRawFsStepOut.unit <$> ops.appendText path content
  | .rename src dst => ScopedRawFsStepOut.unit <$> ops.rename src dst
  | .chmod path mode => ScopedRawFsStepOut.unit <$> ops.chmod path mode
  | .symlink target linkPath => ScopedRawFsStepOut.unit <$> ops.symlink target linkPath
  | .readLink path => ScopedRawFsStepOut.str <$> ops.readLink path
  | .realPath path => ScopedRawFsStepOut.str <$> ops.realPath path
  | .cwd => ScopedRawFsStepOut.str <$> ops.cwd
  | .monotonicNonce => ScopedRawFsStepOut.nonce <$> ops.monotonicNonce
  | .withFileLock path mode createIfMissing actRes =>
    ScopedRawFsStepOut.lockVal <$> ops.withFileLock path mode createIfMissing (pure actRes)
  | .tryWithFileLock path mode createIfMissing actRes =>
    ScopedRawFsStepOut.tryLockVal <$> ops.tryWithFileLock path mode createIfMissing (pure actRes)

/-- Behavioral trace-based relational step specification for `ScopedRawFsOpsM`. -/
def allowedScopedRawFsStep (w : FsWorld) (req : ScopedRawFsStepReq)
    (out : ScopedRawFsStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .mapped err =>
    match req with
    | .mapRawError raw => FsWorldTrace w [] w' ∧ w' = w ∧ err = mapRawError raw
    | _ => False
  | .stat res =>
    match req with
    | .stat follow path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok st => StatTrace none path.toUTF8 follow st tr
        | .error e =>
          nonLockErrOk e ∧
          (∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := !follow }, .err err) ∈ tr ∧
            (e.kind = .notFound → err = Errno.ENOENT))
    | _ => False
  | .names res =>
    match req with
    | .readDir path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok xs => ReadDirTrace path.toUTF8 xs tr
        | .error e => nonLockErrOk e ∧ tr ≠ []
    | _ => False
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
      match req, res with
      | .createDir path, .ok () => MkdirTrace none path.toUTF8 tr
      | .removeDir path, .ok () => UnlinkTrace none path.toUTF8 true tr
      | .unlinkFile path, .ok () => UnlinkTrace none path.toUTF8 false tr
      | .writeBytes path data, .ok () => WriteFileTrace none path.toUTF8 writeOpenFlags 0o644 data tr
      | .createFileNew path data, .ok () => WriteFileTrace none path.toUTF8 createNewOpenFlags 0o644 data tr
      | .appendText path content, .ok () => WriteFileTrace none path.toUTF8 appendOpenFlags 0o644 content.toUTF8 tr
      | .rename src dst, .ok () => RenameTrace none src.toUTF8 none dst.toUTF8 tr
      | .chmod path mode, .ok () => ChmodTrace none path.toUTF8 mode tr
      | .symlink target linkPath, .ok () => SymlinkTrace target.toUTF8 none linkPath.toUTF8 tr
      | .createFileNew path _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))
      | .createDir _, .error e | .removeDir _, .error e | .unlinkFile _, .error e
      | .writeBytes _ _, .error e | .appendText _ _, .error e | .rename _ _, .error e
      | .chmod _ _, .error e | .symlink _ _, .error e =>
        nonLockErrOk e ∧ tr ≠ []
      | _, _ => False
  | .bytes res =>
    match req with
    | .readBytes path =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
        | .error e =>
          nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))
    | _ => False
  | .str res =>
    ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
      match req, res with
      | .readLink path, .ok s => ReadLinkTrace path.toUTF8 s tr
      | .realPath _, .ok s => RealPathTrace s tr
      | .cwd, .ok s => GetcwdTrace s tr
      | .readLink _, .error e | .cwd, .error e => nonLockErrOk e ∧ tr ≠ []
      | .realPath path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput)
      | _, _ => False
  | .nonce n =>
    match req with
    | .monotonicNonce =>
      FsWorldTrace w [] w' ∧ w'.env = w.env ∧ n = w.tempSeq ∧ w'.tempSeq = w.tempSeq + 1
    | _ => False
  | .lockVal res =>
    match req with
    | .withFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok v => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode false true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode false false tr)
    | _ => False
  | .tryLockVal res =>
    match req with
    | .tryWithFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧ w'.tempSeq = w.tempSeq ∧
        match res with
        | .ok none => TryLockContendedTrace none path.toUTF8 mode tr
        | .ok (some v) => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode true true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode true false tr)
    | _ => False

/-- Single-step request sum covering all 32 effectful operations of `FsApiM`. -/
inductive FsStepReq where
  /-- `api.readText`. -/
  | readText (path : String)
  /-- `api.writeText`. -/
  | writeText (path content : String)
  /-- `api.appendText`. -/
  | appendText (path content : String)
  /-- `api.readBytes`. -/
  | readBytes (path : String)
  /-- `api.writeBytes`. -/
  | writeBytes (path : String) (data : ByteArray)
  /-- `api.atomicWriteBytes`. -/
  | atomicWriteBytes (path : String) (data : ByteArray)
  /-- `api.atomicWriteText`. -/
  | atomicWriteText (path content : String)
  /-- `api.touch`. -/
  | touch (path : String) (existOk : Bool)
  /-- `api.mkdir`. -/
  | mkdir (path : String) (parents existOk : Bool)
  /-- `api.unlink`. -/
  | unlink (path : String) (missingOk : Bool)
  /-- `api.rmdir`. -/
  | rmdir (path : String)
  /-- `api.rmtree`. -/
  | rmtree (path : String) (ignoreMissing : Bool)
  /-- `api.rename`. -/
  | rename (src dst : String)
  /-- `api.copyFile`. -/
  | copyFile (src dst : String)
  /-- `api.copyTree`. -/
  | copyTree (src dst : String) (dirsExistOk : Bool)
  /-- `api.pathExists`. -/
  | pathExists (path : String)
  /-- `api.isFile`. -/
  | isFile (path : String)
  /-- `api.isDir`. -/
  | isDir (path : String)
  /-- `api.isSymlink`. -/
  | isSymlink (path : String)
  /-- `api.stat`. -/
  | stat (path : String)
  /-- `api.lstat`. -/
  | lstat (path : String)
  /-- `api.chmod`. -/
  | chmod (path : String) (mode : Nat)
  /-- `api.symlink`. -/
  | symlink (target linkPath : String)
  /-- `api.readLink`. -/
  | readLink (path : String)
  /-- `api.resolve`. -/
  | resolve (path : String)
  /-- `api.cwd`. -/
  | cwd
  /-- `api.listDir`. -/
  | listDir (path : String)
  /-- `api.walk`. -/
  | walk (root : String)
  /-- `api.glob`. -/
  | glob (root pattern : String)
  /-- `api.rglob`. -/
  | rglob (root pattern : String)
  /-- `api.withFileLock` exercised with pure action outcome `actRes`. -/
  | withFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- `api.tryWithFileLock` exercised with pure action outcome `actRes`. -/
  | tryWithFileLock (path : String) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step output sum for `FsApiM`. -/
inductive FsStepOut where
  /-- Output of `Unit`-returning operations. -/
  | unit (res : Except FsError Unit)
  /-- Output of boolean predicate queries (`pathExists`, `isFile`, `isDir`, `isSymlink`). -/
  | flag (res : Except FsError Bool)
  /-- Output of `stat` and `lstat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `readBytes`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `readText`, `readLink`, `resolve`, and `cwd`. -/
  | str (res : Except FsError String)
  /-- Output of sorted string-array queries (`listDir`, `glob`, `rglob`). -/
  | names (res : Except FsError (Array String))
  /-- Output of `walk`. -/
  | walkEntries (res : Except FsError (Array WalkEntry))
  /-- Output of `withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `FsStepReq` against an `FsApiM (StateM W)` bundle. -/
def execFsStep {W : Type} (api : FsApiM (StateM W)) : FsStepReq → StateM W FsStepOut
  | .readText path => FsStepOut.str <$> api.readText path
  | .writeText path content => FsStepOut.unit <$> api.writeText path content
  | .appendText path content => FsStepOut.unit <$> api.appendText path content
  | .readBytes path => FsStepOut.bytes <$> api.readBytes path
  | .writeBytes path data => FsStepOut.unit <$> api.writeBytes path data
  | .atomicWriteBytes path data => FsStepOut.unit <$> api.atomicWriteBytes path data
  | .atomicWriteText path content => FsStepOut.unit <$> api.atomicWriteText path content
  | .touch path existOk => FsStepOut.unit <$> api.touch path existOk
  | .mkdir path parents existOk => FsStepOut.unit <$> api.mkdir path parents existOk
  | .unlink path missingOk => FsStepOut.unit <$> api.unlink path missingOk
  | .rmdir path => FsStepOut.unit <$> api.rmdir path
  | .rmtree path ignoreMissing => FsStepOut.unit <$> api.rmtree path ignoreMissing
  | .rename src dst => FsStepOut.unit <$> api.rename src dst
  | .copyFile src dst => FsStepOut.unit <$> api.copyFile src dst
  | .copyTree src dst dirsExistOk => FsStepOut.unit <$> api.copyTree src dst dirsExistOk
  | .pathExists path => FsStepOut.flag <$> api.pathExists path
  | .isFile path => FsStepOut.flag <$> api.isFile path
  | .isDir path => FsStepOut.flag <$> api.isDir path
  | .isSymlink path => FsStepOut.flag <$> api.isSymlink path
  | .stat path => FsStepOut.stat <$> api.stat path
  | .lstat path => FsStepOut.stat <$> api.lstat path
  | .chmod path mode => FsStepOut.unit <$> api.chmod path mode
  | .symlink target linkPath => FsStepOut.unit <$> api.symlink target linkPath
  | .readLink path => FsStepOut.str <$> api.readLink path
  | .resolve path => FsStepOut.str <$> api.resolve path
  | .cwd => FsStepOut.str <$> api.cwd
  | .listDir path => FsStepOut.names <$> api.listDir path
  | .walk root => FsStepOut.walkEntries <$> api.walk root
  | .glob root pattern => FsStepOut.names <$> api.glob root pattern
  | .rglob root pattern => FsStepOut.names <$> api.rglob root pattern
  | .withFileLock path mode createIfMissing actRes =>
    FsStepOut.lockVal <$> api.withFileLock path mode createIfMissing (pure actRes)
  | .tryWithFileLock path mode createIfMissing actRes =>
    FsStepOut.tryLockVal <$> api.tryWithFileLock path mode createIfMissing (pure actRes)

/-- Behavioral trace witness for `atomicWriteBytes path data`: creates an exclusive `nofollow` sibling temp file with exact `data` using `w.tempSeq`, then atomically renames it onto `path`. -/
def AtomicWriteTrace (w w' : FsWorld) (path : String) (data : ByteArray) (tr : List KernelStep) : Prop :=
  let tmpPath := join ((parent path).getD ".") s!".{(name path).getD "tmp"}.tmp.{w.tempSeq}"
  w'.tempSeq = w.tempSeq + 1 ∧
  ∃ tr1 tr2 tr3,
    tr = tr1 ++ tr2 ++ tr3 ∧
    WriteFileTrace none tmpPath.toUTF8 createNewOpenFlags 0o644 data tr2 ∧
    RenameTrace none tmpPath.toUTF8 none path.toUTF8 tr3

/-- Behavioral trace witness for `mkdir path _ existOk`: either `mkdirat` created `path`, or `existOk = true` and `fstatat` confirmed an existing directory. -/
def MkdirOkTrace (path : String) (existOk : Bool) (tr : List KernelStep) : Prop :=
  MkdirTrace none path.toUTF8 tr ∨
  (existOk = true ∧ ∃ rawSt nf, (.fstatat none path.toUTF8 { symlinkNofollow := nf }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir)

/-- Behavioral trace witness that `root` was verified as a directory and scanned via `openat(O_DIRECTORY)` + `getdents64` EOF. -/
def WalkRootTrace (root : String) (tr : List KernelStep) : Prop :=
  (∃ rawSt, (.fstatat none root.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir) ∧
  (∃ h eof, (.openat none root.toUTF8 dirOpenFlags 0, .opened h) ∈ tr ∧ (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0)

/-- Behavioral trace-based relational step specification for all 32 effectful `FsApiM` operations over healthy Linux `FsWorld`. -/
def allowedFsStep (w : FsWorld) (req : FsStepReq) (out : FsStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .writeText path content, .ok () =>
        WriteFileTrace none path.toUTF8 writeOpenFlags 0o644 content.toUTF8 tr
      | .appendText path content, .ok () =>
        WriteFileTrace none path.toUTF8 appendOpenFlags 0o644 content.toUTF8 tr
      | .writeBytes path data, .ok () =>
        WriteFileTrace none path.toUTF8 writeOpenFlags 0o644 data tr
      | .atomicWriteBytes path data, .ok () =>
        AtomicWriteTrace w w' path data tr
      | .atomicWriteText path content, .ok () =>
        AtomicWriteTrace w w' path content.toUTF8 tr
      | .touch path existOk, .ok () =>
        (existOk = true ∧ ∃ tr1 tr2, tr = tr1 ++ tr2 ∧
          WriteFileTrace none path.toUTF8 appendOpenFlags 0o644 ByteArray.empty tr2) ∨
        (∃ tr1 tr2, tr = tr1 ++ tr2 ∧
          (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr1 ∧
          WriteFileTrace none path.toUTF8 writeOpenFlags 0o644 ByteArray.empty tr2)
      | .mkdir path _ existOk, .ok () =>
        MkdirOkTrace path existOk tr
      | .unlink path missingOk, .ok () =>
        UnlinkTrace none path.toUTF8 false tr ∨
        (missingOk = true ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr)
      | .rmdir path, .ok () =>
        UnlinkTrace none path.toUTF8 true tr
      | .rmtree path ignoreMissing, .ok () =>
        UnlinkTrace none path.toUTF8 true tr ∨
        (ignoreMissing = true ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr)
      | .rename src dst, .ok () =>
        RenameTrace none src.toUTF8 none dst.toUTF8 tr
      | .copyFile src dst, .ok () =>
        ∃ bs tr1 tr2 tr3,
          tr = tr1 ++ tr2 ++ tr3 ∧
          ReadRegularTrace none src.toUTF8 readOpenFlags bs tr2 ∧
          WriteFileTrace none dst.toUTF8 writeOpenFlags 0o644 bs tr3
      | .copyTree src dst dirsExistOk, .ok () =>
        (∃ rawSt, (.fstatat none src.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir) ∧
        MkdirOkTrace dst dirsExistOk tr
      | .chmod path mode, .ok () =>
        ChmodTrace none path.toUTF8 mode tr
      | .symlink target linkPath, .ok () =>
        SymlinkTrace target.toUTF8 none linkPath.toUTF8 tr
      | .atomicWriteBytes path _, .error e | .atomicWriteText path _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/"))
      | .writeText _ _, .error e | .appendText _ _, .error e | .writeBytes _ _, .error e
      | .touch _ _, .error e | .mkdir _ _ _, .error e | .unlink _ _, .error e
      | .rmdir _, .error e | .rmtree _ _, .error e | .rename _ _, .error e
      | .copyFile _ _, .error e | .copyTree _ _ _, .error e | .chmod _ _, .error e
      | .symlink _ _, .error e =>
        nonLockErrOk e ∧ tr ≠ []
      | _, _ => False
  | .flag res =>
    match res with
    | .ok b =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match req with
        | .pathExists path =>
          (b = true ∧ ∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isFile path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .reg)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isDir path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .dir)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr)
        | .isSymlink path =>
          (∃ rawSt, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ b = (rawSt.kind == .symlink)) ∨
          (b = false ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err err) ∈ tr)
        | _ => False
    | .error _ => False
  | .stat res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .stat path, .ok st => StatTrace none path.toUTF8 true st tr
      | .lstat path, .ok st => StatTrace none path.toUTF8 false st tr
      | .stat path, .error e =>
        nonLockErrOk e ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := false }, .err err) ∈ tr
      | .lstat path, .error e =>
        nonLockErrOk e ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err err) ∈ tr
      | _, _ => False
  | .bytes res =>
    match req with
    | .readBytes path =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
        | .error e =>
          nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))
    | _ => False
  | .str res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .readText path, .ok s =>
        ∃ bs, String.fromUTF8? bs = some s ∧ ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
      | .readLink path, .ok s => ReadLinkTrace path.toUTF8 s tr
      | .resolve _, .ok s => RealPathTrace s tr
      | .cwd, .ok s => GetcwdTrace s tr
      | .readText path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))
      | .readLink _, .error e | .cwd, .error e => nonLockErrOk e ∧ tr ≠ []
      | .resolve path, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput)
      | _, _ => False
  | .names res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req, res with
      | .listDir path, .ok xs =>
        List.Pairwise (· ≤ ·) xs.toList ∧ ReadDirTrace path.toUTF8 xs tr
      | .glob root _, .ok xs | .rglob root _, .ok xs =>
        List.Pairwise (· ≤ ·) xs.toList ∧ WalkRootTrace root tr
      | .listDir _, .error e => nonLockErrOk e ∧ tr ≠ []
      | .glob _ _, .error e | .rglob _ _, .error e =>
        nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput)
      | _, _ => False
  | .walkEntries res =>
    match req with
    | .walk root =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok entries =>
          (∀ e ∈ entries.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
          entries.size > 0 ∧
          WalkRootTrace root tr
        | .error e => nonLockErrOk e ∧ tr ≠ []
    | _ => False
  | .lockVal res =>
    match req with
    | .withFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok v => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode false true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode false false tr)
    | _ => False
  | .tryLockVal res =>
    match req with
    | .tryWithFileLock path mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok none => TryLockContendedTrace none path.toUTF8 mode tr
        | .ok (some v) => actRes = .ok v ∧ FileLockTrace none path.toUTF8 mode true true tr
        | .error e =>
          (nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput))) ∨
          (actRes = .error e ∧ FileLockTrace none path.toUTF8 mode true false tr)
    | _ => False

/-- Finite single-operation request inside an open `SubtreeM` capability. -/
inductive SubtreeOpReq where
  /-- `sub.lstat`. -/
  | lstat (rel : RelPath)
  /-- `sub.readRegular`. -/
  | readRegular (rel : RelPath)
  /-- `sub.atomicWriteBytes`. -/
  | atomicWriteBytes (rel : RelPath) (data : ByteArray)
  /-- `sub.mkdir`. -/
  | mkdir (rel : RelPath) (parents existOk : Bool)
  /-- `sub.unlink`. -/
  | unlink (rel : RelPath) (missingOk : Bool)
  /-- `sub.rmdir`. -/
  | rmdir (rel : RelPath)
  /-- `sub.rmtree`. -/
  | rmtree (rel : RelPath) (ignoreMissing : Bool)
  /-- `sub.symlink`. -/
  | symlink (target : String) (rel : RelPath)
  /-- `sub.listDir`. -/
  | listDir (rel : RelPath)
  /-- `sub.walk`. -/
  | walk (rel : RelPath)
  /-- `sub.withFileLock` with pure action outcome `actRes`. -/
  | withFileLock (rel : RelPath) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)
  /-- `sub.tryWithFileLock` with pure action outcome `actRes`. -/
  | tryWithFileLock (rel : RelPath) (mode : LockMode) (createIfMissing : Bool) (actRes : Except FsError Nat)

/-- Single-step request opening `rootPath` via `withSubtree` and running `op`. -/
structure SubtreeStepReq where
  /-- Host path to open as the confined subtree root. -/
  rootPath : String
  /-- Operation to execute inside `withSubtree`. -/
  op : SubtreeOpReq

/-- Single-step output sum for `SubtreeOpenerM.withSubtree`. -/
inductive SubtreeStepOut where
  /-- Output of `sub.lstat`. -/
  | stat (res : Except FsError FileStat)
  /-- Output of `sub.readRegular`. -/
  | bytes (res : Except FsError ByteArray)
  /-- Output of `Unit`-returning subtree operations. -/
  | unit (res : Except FsError Unit)
  /-- Output of `sub.listDir`. -/
  | entryNames (res : Except FsError (Array EntryName))
  /-- Output of `sub.walk`. -/
  | walkEntries (res : Except FsError (Array WalkEntry))
  /-- Output of `sub.withFileLock`. -/
  | lockVal (res : Except FsError Nat)
  /-- Output of `sub.tryWithFileLock`. -/
  | tryLockVal (res : Except FsError (Option Nat))

/-- Execute one `SubtreeStepReq` against a `SubtreeOpenerM (StateM W)` capability bundle. -/
def execSubtreeStep {W : Type} (opener : SubtreeOpenerM (StateM W)) (req : SubtreeStepReq) :
    StateM W SubtreeStepOut :=
  match req.op with
  | .lstat rel => SubtreeStepOut.stat <$> opener.withSubtree req.rootPath (·.lstat rel)
  | .readRegular rel => SubtreeStepOut.bytes <$> opener.withSubtree req.rootPath (·.readRegular rel)
  | .atomicWriteBytes rel data =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.atomicWriteBytes rel data)
  | .mkdir rel parents existOk =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.mkdir rel parents existOk)
  | .unlink rel missingOk =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.unlink rel missingOk)
  | .rmdir rel => SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.rmdir rel)
  | .rmtree rel ignoreMissing =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.rmtree rel ignoreMissing)
  | .symlink target rel =>
    SubtreeStepOut.unit <$> opener.withSubtree req.rootPath (·.symlink target rel)
  | .listDir rel => SubtreeStepOut.entryNames <$> opener.withSubtree req.rootPath (·.listDir rel)
  | .walk rel => SubtreeStepOut.walkEntries <$> opener.withSubtree req.rootPath (·.walk rel)
  | .withFileLock rel mode createIfMissing actRes =>
    SubtreeStepOut.lockVal <$>
      opener.withSubtree req.rootPath (·.withFileLock rel mode createIfMissing (pure actRes))
  | .tryWithFileLock rel mode createIfMissing actRes =>
    SubtreeStepOut.tryLockVal <$>
      opener.withSubtree req.rootPath (·.tryWithFileLock rel mode createIfMissing (pure actRes))

/-- Descriptor-confined trace decomposition for an entered `withSubtree rootPath` execution: opens `rootPath` once with `O_DIRECTORY`, runs only `SubtreeConfinedReq` steps inside `trInner` preserving `[rootDh]`, and closes `rootDh` on exit. -/
def SubtreeConfinedTrace (rootPath : String) (tr : List KernelStep)
    (bodyProp : HandleId → List KernelStep → Prop) : Prop :=
  ∃ rootDh trOpen trInner trClose,
    tr = trOpen ++ trInner ++ trClose ∧
    (.openat none rootPath.toUTF8 dirOpenFlags 0, .opened rootDh) ∈ trOpen ∧
    (∀ s ∈ trOpen, ∃ o, s = (.openat none rootPath.toUTF8 dirOpenFlags 0, o)) ∧
    TraceFds [rootDh] trInner [rootDh] ∧
    (∀ s ∈ trInner, SubtreeConfinedReq s.1) ∧
    (∃ co, trClose = [(.close rootDh, co)]) ∧
    bodyProp rootDh trInner

/-- Confined trace witness for any `withSubtree` error: either invalid root path before opening, failed `openat(O_DIRECTORY)` of `rootPath`, or a confined execution that closed `rootDh`. -/
def SubtreeErrTrace (rootPath : String) (e : FsError) (tr : List KernelStep) : Prop :=
  nonLockErrOk e ∧
  ((tr = [] ∧ isValidRawPathModel rootPath = false ∧ e.kind = .invalidInput) ∨
   (tr ≠ [] ∧ ∀ s ∈ tr, ∃ o, s = (.openat none rootPath.toUTF8 dirOpenFlags 0, o)) ∨
   SubtreeConfinedTrace rootPath tr (fun _ _ => True))

/-- Behavioral and descriptor-confinement relational step specification for `SubtreeOpenerM.withSubtree` and all 12 `SubtreeM` methods over healthy Linux `FsWorld`. -/
def allowedSubtreeStep (w : FsWorld) (req : SubtreeStepReq)
    (out : SubtreeStepOut) (w' : FsWorld) : Prop :=
  match out with
  | .stat res =>
    match req.op with
    | .lstat rel =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok st =>
          SubtreeConfinedTrace req.rootPath tr fun rootDh trInner =>
            match splitLastAux rel.segments [] with
            | none => FstatTrace rootDh st trInner
            | some (_, leaf) => ∃ d, StatTrace (some d) leaf.val.toUTF8 false st trInner
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .bytes res =>
    match req.op with
    | .readRegular rel =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok bs =>
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              ReadRegularTrace (some d) leaf.val.toUTF8 readAtOpenFlags bs sub
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .unit res =>
    ∃ tr, FsWorldTrace w tr w' ∧
      match req.op, res with
      | .atomicWriteBytes rel data, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d, ∃ tmp : EntryName, ∃ sub1 sub2,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            Subtrace (sub1 ++ sub2) trInner ∧
            WriteFileTrace (some d) tmp.val.toUTF8 createNewOpenFlags 0o644 data sub1 ∧
            RenameTrace (some d) tmp.val.toUTF8 (some d) leaf.val.toUTF8 sub2
      | .mkdir rel _ existOk, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun rootDh trInner =>
          match splitLastAux rel.segments [] with
          | none => existOk = true ∧ ∃ rawSt, (.fstat rootDh, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir
          | some (_, leaf) =>
            ∃ d, MkdirTrace (some d) leaf.val.toUTF8 trInner ∨
              (existOk = true ∧ ∃ rawSt, (.fstatat (some d) leaf.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir)
      | .unlink rel missingOk, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 false trInner) ∨
             (missingOk = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner))
      | .rmdir rel, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            UnlinkTrace (some d) leaf.val.toUTF8 true trInner
      | .rmtree rel ignoreMissing, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 true trInner) ∨
             (ignoreMissing = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner))
      | .symlink target rel, .ok () =>
        SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
          ∃ pre leaf d,
            splitLastAux rel.segments [] = some (pre, leaf) ∧
            SymlinkTrace target.toUTF8 (some d) leaf.val.toUTF8 trInner
      | .atomicWriteBytes _ _, .error e | .mkdir _ _ _, .error e | .unlink _ _, .error e
      | .rmdir _, .error e | .rmtree _ _, .error e | .symlink _ _, .error e =>
        SubtreeErrTrace req.rootPath e tr
      | _, _ => False
  | .entryNames res =>
    match req.op with
    | .listDir _ =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok xs =>
          List.Pairwise (fun a b => a.val ≤ b.val) xs.toList ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ h eof,
              (.getdents64 h 8192, .bytes eof) ∈ trInner ∧
              eof.size = 0 ∧
              (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ trInner ∧ buf.size > 0)
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .walkEntries res =>
    match req.op with
    | .walk _ =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok entries =>
          (∀ e ∈ entries.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
          entries.size > 0 ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ trInner ∧ eof.size = 0
        | .error e => SubtreeErrTrace req.rootPath e tr
    | _ => False
  | .lockVal res =>
    match req.op with
    | .withFileLock rel mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok v =>
          actRes = .ok v ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              FileLockTrace (some d) leaf.val.toUTF8 mode false true sub
        | .error e =>
          SubtreeErrTrace req.rootPath e tr ∨
          (actRes = .error e ∧
            SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
              ∃ pre leaf d sub,
                splitLastAux rel.segments [] = some (pre, leaf) ∧
                Subtrace sub trInner ∧
                FileLockTrace (some d) leaf.val.toUTF8 mode false false sub)
    | _ => False
  | .tryLockVal res =>
    match req.op with
    | .tryWithFileLock rel mode _ actRes =>
      ∃ tr, FsWorldTrace w tr w' ∧
        match res with
        | .ok none =>
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              TryLockContendedTrace (some d) leaf.val.toUTF8 mode sub
        | .ok (some v) =>
          actRes = .ok v ∧
          SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
            ∃ pre leaf d sub,
              splitLastAux rel.segments [] = some (pre, leaf) ∧
              Subtrace sub trInner ∧
              FileLockTrace (some d) leaf.val.toUTF8 mode true true sub
        | .error e =>
          SubtreeErrTrace req.rootPath e tr ∨
          (actRes = .error e ∧
            SubtreeConfinedTrace req.rootPath tr fun _ trInner =>
              ∃ pre leaf d sub,
                splitLastAux rel.segments [] = some (pre, leaf) ∧
                Subtrace sub trInner ∧
                FileLockTrace (some d) leaf.val.toUTF8 mode true false sub)
    | _ => False

end LeanSwe.Fs.Model

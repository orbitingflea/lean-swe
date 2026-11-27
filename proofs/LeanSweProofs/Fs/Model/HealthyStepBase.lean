import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSweProofs.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import LeanSwe.Fs.Types
import LeanSweProofs.Fs.Model

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

/-- Canonical lower-layer syscall capability bundle for `LeanSwe.Fs` over `LinuxSyscall.Files` and `LinuxSyscall.TimeRand`. -/
abbrev FsSysCapsM := LeanSwe.Fs.Internal.FsSysCapsM

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

/-- Combined healthy-OS dependency world state pairing `FsWorld`, `TimeRand.HealthyEnv`, and `RawFd` descriptor projection. -/
structure FsDepsWorld where
  /-- Underlying `FsWorld` state. -/
  fs : FsWorld := {}
  /-- Underlying healthy `TimeRand` environment. -/
  time : TimeRand.HealthyEnv := TimeRand.HealthyEnv.initial
  /-- Logical descriptor-table identity of each `RawFd` box. -/
  toHid : RawFd → HandleId := fun _ => 0

instance : Inhabited FsDepsWorld := ⟨{}⟩

/-- Well-formedness invariant on `FsDepsWorld`. -/
def fsDepsWorldWf (w : FsDepsWorld) : Bool :=
  fsWorldWf w.fs && w.time.wf

/-- Project `FsDepsWorld` onto `FsWorld` for `Core.ObeysStepFromFinally` (mapping ill-formed `time` worlds to an ill-formed `FsWorld`). -/
def fsDepsWorldToFsWorld (w : FsDepsWorld) : FsWorld :=
  if w.time.wf then w.fs
  else { env := { state := { FilesState.initial with ambientSeccomp := true }, eintrBudget := 0 }, tempSeq := 0 }

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

/-- Trace witness that `mkdirat` succeeded on `(dir, path)` with `mode`. -/
def MkdirTrace (dir : Option HandleId) (path : ByteArray) (mode : UInt32) (tr : List KernelStep) : Prop :=
  (.mkdirat dir path mode, .unit) ∈ tr

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

/-- Single-step request sum for `HealthyFilesCapM` inside `Core.ObeysStepFromFinally`. -/
inductive FilesCapStepReq where
  /-- Execute one curated `LinuxSyscall.Files.FilesReq` syscall. -/
  | fileReq (req : FilesReq)
  /-- Allocate the next monotonic temporary-name sequence number. -/
  | nextTempSeq

/-- Single-step output sum for `HealthyFilesCapM` inside `Core.ObeysStepFromFinally`. -/
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

/-- Parametric `Files` syscall request sum over descriptor type `fd`. -/
inductive RawFilesReq (fd : Type) where
  /-- `openat(dir, path, flags, mode)`. -/
  | openat (dir : Option fd) (path : ByteArray) (flags : OpenFlags) (mode : Mode)
  /-- `openat2(dir, path, how)`. -/
  | openat2 (dir : Option fd) (path : ByteArray) (how : OpenHow)
  /-- `close(h)`. -/
  | close (h : fd)
  /-- `read(h, maxBytes)`. -/
  | read (h : fd) (maxBytes : UInt32)
  /-- `write(h, data)`. -/
  | write (h : fd) (data : ByteArray)
  /-- `fstat(h)`. -/
  | fstat (h : fd)
  /-- `fstatat(dir, path, flags)`. -/
  | fstatat (dir : Option fd) (path : ByteArray) (flags : AtFlags)
  /-- `faccessat(dir, path, mask, flags)`. -/
  | faccessat (dir : Option fd) (path : ByteArray) (mask : AccessModeMask) (flags : AtFlags)
  /-- `mkdirat(dir, path, mode)`. -/
  | mkdirat (dir : Option fd) (path : ByteArray) (mode : Mode)
  /-- `unlinkat(dir, path, removeDir)`. -/
  | unlinkat (dir : Option fd) (path : ByteArray) (removeDir : Bool)
  /-- `renameat2(oldDir, oldPath, newDir, newPath, flags)`. -/
  | renameat2 (oldDir : Option fd) (oldPath : ByteArray) (newDir : Option fd) (newPath : ByteArray) (flags : RenameFlags)
  /-- `symlinkat(target, dir, linkPath)`. -/
  | symlinkat (target : ByteArray) (dir : Option fd) (linkPath : ByteArray)
  /-- `readlinkat(dir, path, cap)`. -/
  | readlinkat (dir : Option fd) (path : ByteArray) (cap : UInt32)
  /-- `getdents64(h, bufBytes)`. -/
  | getdents64 (h : fd) (bufBytes : UInt32)
  /-- `fchmodat(dir, path, mode)`. -/
  | fchmodat (dir : Option fd) (path : ByteArray) (mode : Mode)
  /-- `fchmod(h, mode)`. -/
  | fchmod (h : fd) (mode : Mode)
  /-- `flock(h, op)`. -/
  | flock (h : fd) (op : FlockOp)
  /-- `fcntl(h, cmd)`. -/
  | fcntl (h : fd) (cmd : FcntlCmd)
  /-- `fsync(h)`. -/
  | fsync (h : fd)
  /-- `getcwd(cap)`. -/
  | getcwd (cap : UInt32)
  /-- `lseek(h, offset, whence)`. -/
  | lseek (h : fd) (offset : Int64) (whence : SeekWhence)
  /-- `reopenReadOnly(h)`. -/
  | reopenReadOnly (h : fd)
  /-- `dupStdio(slot)`. -/
  | dupStdio (slot : StdioFd)

/-- Parametric `Files` syscall outcome sum over descriptor type `fd`. -/
inductive RawFilesOut (fd : Type) where
  /-- Succeeded returning `Unit`. -/
  | unit
  /-- Succeeded returning opened descriptor `h`. -/
  | opened (h : fd)
  /-- Succeeded returning `ByteArray`. -/
  | bytes (data : ByteArray)
  /-- Succeeded returning `UInt32`. -/
  | u32 (val : UInt32)
  /-- Succeeded returning `UInt64`. -/
  | u64 (val : UInt64)
  /-- Succeeded returning `StatInfo`. -/
  | statted (st : StatInfo)
  /-- Failed with `Errno`. -/
  | err (errno : Errno)

/-- Project `Option fd` to `Option HandleId` via `hidOf` (reducible for definitional unfolding). -/
@[simp, reducible] def mapOptHid {fd : Type} (hidOf : fd → HandleId) : Option fd → Option HandleId
  | none => none
  | some h => some (hidOf h)

/-- Project `RawFilesReq fd` to `FilesReq` via `hidOf`. -/
@[simp, reducible] def RawFilesReq.toFilesReq {fd : Type} (hidOf : fd → HandleId) : RawFilesReq fd → FilesReq
  | .openat d p fl md => .openat (mapOptHid hidOf d) p fl md
  | .openat2 d p how => .openat2 (mapOptHid hidOf d) p how
  | .close h => .close (hidOf h)
  | .read h n => .read (hidOf h) n
  | .write h bs => .write (hidOf h) bs
  | .fstat h => .fstat (hidOf h)
  | .fstatat d p fl => .fstatat (mapOptHid hidOf d) p fl
  | .faccessat d p mk fl => .faccessat (mapOptHid hidOf d) p mk fl
  | .mkdirat d p md => .mkdirat (mapOptHid hidOf d) p md
  | .unlinkat d p rd => .unlinkat (mapOptHid hidOf d) p rd
  | .renameat2 od op nd np fl => .renameat2 (mapOptHid hidOf od) op (mapOptHid hidOf nd) np fl
  | .symlinkat t d lp => .symlinkat t (mapOptHid hidOf d) lp
  | .readlinkat d p c => .readlinkat (mapOptHid hidOf d) p c
  | .getdents64 h c => .getdents64 (hidOf h) c
  | .fchmodat d p md => .fchmodat (mapOptHid hidOf d) p md
  | .fchmod h md => .fchmod (hidOf h) md
  | .flock h op => .flock (hidOf h) op
  | .fcntl h cmd => .fcntl (hidOf h) cmd
  | .fsync h => .fsync (hidOf h)
  | .getcwd c => .getcwd c
  | .lseek h off wh => .lseek (hidOf h) off wh
  | .reopenReadOnly h => .reopenReadOnly (hidOf h)
  | .dupStdio sl => .dupStdio sl

/-- Project `RawFilesOut fd` to `FilesOutcome` via `hidOf`. -/
@[simp, reducible] def RawFilesOut.toFilesOutcome {fd : Type} (hidOf : fd → HandleId) : RawFilesOut fd → FilesOutcome
  | .unit => .unit
  | .opened h => .opened (hidOf h)
  | .bytes b => .bytes b
  | .u32 v => .u32 v
  | .u64 v => .u64 v
  | .statted st => .statted st
  | .err e => .err e

/-- Convert `Except Errno Unit` into `RawFilesOut fd`. -/
def rawOutcomeOfUnit {fd : Type} : Except Errno Unit → RawFilesOut fd
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno fd` into `RawFilesOut fd`. -/
def rawOutcomeOfOpened {fd : Type} : Except Errno fd → RawFilesOut fd
  | .ok h => .opened h
  | .error e => .err e

/-- Convert `Except Errno ByteArray` into `RawFilesOut fd`. -/
def rawOutcomeOfBytes {fd : Type} : Except Errno ByteArray → RawFilesOut fd
  | .ok b => .bytes b
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `RawFilesOut fd`. -/
def rawOutcomeOfU32 {fd : Type} : Except Errno UInt32 → RawFilesOut fd
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert `Except Errno UInt64` into `RawFilesOut fd`. -/
def rawOutcomeOfU64 {fd : Type} : Except Errno UInt64 → RawFilesOut fd
  | .ok v => .u64 v
  | .error e => .err e

/-- Convert `Except Errno StatInfo` into `RawFilesOut fd`. -/
def rawOutcomeOfStatted {fd : Type} : Except Errno StatInfo → RawFilesOut fd
  | .ok st => .statted st
  | .error e => .err e

/-- Execute one `RawFilesReq fd` against a `FilesOpsM m fd` bundle. -/
def execRawFilesReq {m : Type → Type} [Monad m] {fd : Type}
    (ops : FilesOpsM m fd) : RawFilesReq fd → m (RawFilesOut fd)
  | .openat d p fl md => rawOutcomeOfOpened <$> ops.openat d p fl md
  | .openat2 d p how => rawOutcomeOfOpened <$> ops.openat2 d p how
  | .close h => rawOutcomeOfUnit <$> ops.close h
  | .read h n => rawOutcomeOfBytes <$> ops.read h n
  | .write h bs => rawOutcomeOfU32 <$> ops.write h bs
  | .fstat h => rawOutcomeOfStatted <$> ops.fstat h
  | .fstatat d p fl => rawOutcomeOfStatted <$> ops.fstatat d p fl
  | .faccessat d p mk fl => rawOutcomeOfUnit <$> ops.faccessat d p mk fl
  | .mkdirat d p md => rawOutcomeOfUnit <$> ops.mkdirat d p md
  | .unlinkat d p rd => rawOutcomeOfUnit <$> ops.unlinkat d p rd
  | .renameat2 od op nd np fl => rawOutcomeOfUnit <$> ops.renameat2 od op nd np fl
  | .symlinkat t d lp => rawOutcomeOfUnit <$> ops.symlinkat t d lp
  | .readlinkat d p c => rawOutcomeOfBytes <$> ops.readlinkat d p c
  | .getdents64 h c => rawOutcomeOfBytes <$> ops.getdents64 h c
  | .fchmodat d p md => rawOutcomeOfUnit <$> ops.fchmodat d p md
  | .fchmod h md => rawOutcomeOfUnit <$> ops.fchmod h md
  | .flock h op => rawOutcomeOfUnit <$> ops.flock h op
  | .fcntl h cmd => rawOutcomeOfU32 <$> ops.fcntl h cmd
  | .fsync h => rawOutcomeOfUnit <$> ops.fsync h
  | .getcwd c => rawOutcomeOfBytes <$> ops.getcwd c
  | .lseek h off wh => rawOutcomeOfU64 <$> ops.lseek h off wh
  | .reopenReadOnly h => rawOutcomeOfOpened <$> ops.reopenReadOnly h
  | .dupStdio sl => rawOutcomeOfOpened <$> ops.dupStdio sl

/-- Single-step request sum for `FsSysCapsM` inside `Core.ObeysStepFromFinally`. -/
inductive FsSysCapReq where
  /-- Execute one `LinuxSyscall.Files` syscall over `RawFd`. -/
  | files (req : RawFilesReq RawFd)
  /-- Execute one `LinuxSyscall.TimeRand` syscall. -/
  | timeRand (req : TimeRand.TimeRandReq)

/-- Single-step output sum for `FsSysCapsM` inside `Core.ObeysStepFromFinally`. -/
inductive FsSysCapOut where
  /-- Decoded `RawFilesOut RawFd`. -/
  | files (out : RawFilesOut RawFd)
  /-- Decoded `TimeRand.TimeRandOutcome`. -/
  | timeRand (out : TimeRand.TimeRandOutcome)

/-- Execute one `FsSysCapReq` against a `FsSysCapsM (StateM W)` capability bundle. -/
def execFsSysCapStep {W : Type} (caps : FsSysCapsM (StateM W)) :
    FsSysCapReq → StateM W FsSysCapOut
  | .files req => FsSysCapOut.files <$> execRawFilesReq caps.files req
  | .timeRand req => FsSysCapOut.timeRand <$> TimeRand.execTimeRandReq caps.timeRand req

/-- Relational healthy-OS step specification for `FsSysCapsM` directly over `LinuxSyscall.Files.healthyStep` and `LinuxSyscall.TimeRand.healthyStep`. -/
def allowedFsSysCapStep (w : FsDepsWorld) (req : FsSysCapReq) (out : FsSysCapOut) (w' : FsDepsWorld) : Prop :=
  fsDepsWorldWf w = true ∧
  fsDepsWorldWf w' = true ∧
  w'.toHid = w.toHid ∧
  w'.fs.tempSeq = w.fs.tempSeq ∧
  match req, out with
  | .files r, .files o =>
    healthyStep w.fs.env (r.toFilesReq w.toHid) (o.toFilesOutcome w.toHid) = some w'.fs.env ∧
    w'.time = w.time
  | .timeRand r, .timeRand o =>
    TimeRand.healthyStep w.time r o = some w'.time ∧
    w'.fs.env = w.fs.env
  | _, _ => False

end LeanSwe.Fs.Model

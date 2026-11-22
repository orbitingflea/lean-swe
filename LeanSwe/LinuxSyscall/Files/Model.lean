import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

/-- Return `true` iff `e` is a valid safe outer `seccomp(SECCOMP_RET_ERRNO)` error (`1..4095 \ {EFAULT}`). -/
def Errno.isSafeSeccompErrno (e : Errno) : Bool :=
  e.toNat >= 1 && e.toNat <= 4095 && e != Errno.EFAULT

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Logical inode identifier in the `Files` world model (`0` is the scratch root directory). -/
abbrev InodeId := Nat

/-- Advisory lock state held by an open file description (`flock(2)`). -/
inductive LockKind where
  /-- Shared lock (`LOCK_SH`). -/
  | shared
  /-- Exclusive lock (`LOCK_EX`). -/
  | exclusive
  deriving Repr, DecidableEq, BEq

/-- Special character-device behavior kinds. -/
inductive CharDevKind where
  /-- Null device (`/dev/null`): reads return EOF, writes succeed discarding bytes. -/
  | nullDev
  /-- Zero device (`/dev/zero`): reads return NUL bytes, writes succeed discarding bytes. -/
  | zeroDev
  /-- Full device (`/dev/full`): reads return NUL bytes, all writes fail with `ENOSPC`. -/
  | fullDev
  /-- Whiteout character device (`0:0`) created by `RENAME_WHITEOUT`. -/
  | whiteout
  /-- Other host special character device. -/
  | generic
  deriving Repr, DecidableEq, BEq

/-- Compatibility alias for character-device specialization. -/
abbrev SpecialDevKind := CharDevKind

/-- Kernel `memfd` seal state (only meaningful on regular files). -/
inductive SealState where
  /-- Not sealable (`ext4`, normal files, or non-regular files). -/
  | unsealable
  /-- Sealable `memfd` inode carrying accumulated `F_SEAL_*` bits. -/
  | sealable (mask : UInt32 := 0)
  deriving Repr, DecidableEq, BEq

/-- Regular-file inode payload with sparse extent storage supporting `2^63 - 1` seeks without hole materialization. -/
structure RegData where
  /-- Logical byte length of the regular file. -/
  size : Nat := 0
  /-- Sorted non-overlapping non-empty `(offset, bytes)` written extents. -/
  extents : List (Nat × ByteArray) := []
  /-- `memfd` seal state. -/
  seals : SealState := .unsealable
  /-- Whether opening for write/truncation rejects with `ETXTBSY`. -/
  exeProtected : Bool := false
  deriving Repr, BEq

/-- Unboxed `O(1)` byte lookup returning `0` when `i ≥ b.size`. -/
@[inline] def byteGetD (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- Tail-recursive helper building an `n`-byte zero-filled `ByteArray` without boxed `Array UInt8` allocation. -/
def replicateZeroBytesLoop : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | n + 1, acc => replicateZeroBytesLoop n (acc.push 0)

/-- Allocate an unboxed `ByteArray` of `n` zero bytes. -/
def replicateZeroBytes (n : Nat) : ByteArray :=
  replicateZeroBytesLoop n (ByteArray.emptyWithCapacity n)

/-- Construct a `RegData` from an initial contiguous `ByteArray`. -/
def RegData.ofBytes (b : ByteArray) (seals : SealState := .unsealable) (exeProtected : Bool := false) : RegData :=
  { size := b.size
    extents := if b.size == 0 then [] else [(0, b)]
    seals := seals
    exeProtected := exeProtected }

/-- Copy `rem` overlapping bytes from extent `eData` (`eStart`) into unboxed `ByteArray` `buf` starting at `i`. -/
def paintExtentLoop (pos eStart : Nat) (eData : ByteArray) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, buf => buf
  | rem + 1, i, buf =>
    let buf' := buf.set! (i - pos) (byteGetD eData (i - eStart))
    paintExtentLoop pos eStart eData rem (i + 1) buf'

/-- Materialize `len` bytes starting at `pos` from sparse `RegData` extents (`O(#extents + actualLen)`). -/
def RegData.readSlice (rd : RegData) (pos len : Nat) : ByteArray :=
  let avail := if pos < rd.size then rd.size - pos else 0
  let actualLen := min len avail
  if actualLen == 0 then ByteArray.empty
  else
    let rEnd := pos + actualLen
    let init := replicateZeroBytes actualLen
    rd.extents.foldl (fun buf (eStart, eData) =>
      let eEnd := eStart + eData.size
      let ovStart := max pos eStart
      let ovEnd := min rEnd eEnd
      if ovStart < ovEnd then paintExtentLoop pos eStart eData (ovEnd - ovStart) ovStart buf
      else buf) init

/-- Materialize the full byte content of `RegData` (for small test fixtures). -/
def RegData.bytes (rd : RegData) : ByteArray :=
  rd.readSlice 0 rd.size

/-- Directory lifecycle state. -/
inductive DirLifecycle where
  /-- Live native or upper directory. -/
  | live
  /-- Unlinked native or upper directory (`nlink = 0`). -/
  | unlinked
  /-- Merged `overlayfs` directory reporting `st_nlink = 1`. -/
  | overlayMerged
  /-- Removed uncopied `overlayfs` lower directory (`nlink` preserved, lookups/readdir/getcwd `ENOENT`, `fchmod` `ENOTDIR`). -/
  | overlayDeadLower
  /-- Removed copied-up `overlayfs` merged directory (`st_nlink = 1`, lookups/readdir/getcwd `ENOENT`, `fchmod` succeeds). -/
  | overlayDeadMerged
  deriving Repr, DecidableEq, BEq

/-- Return `true` iff directory lifecycle state `l` represents a removed directory. -/
def DirLifecycle.isDead : DirLifecycle → Bool
  | .unlinked | .overlayDeadLower | .overlayDeadMerged => true
  | .live | .overlayMerged => false

/-- Directory inode payload. -/
structure DirData where
  /-- Directory entries `(name, childIno)`. -/
  children : List (ByteArray × InodeId) := []
  /-- Parent directory inode (`0` for root). -/
  parentIno : InodeId := 0
  /-- Directory lifecycle state. -/
  lifecycle : DirLifecycle := .live
  deriving Repr, BEq

/-- Symlink target separating regular symlinks from procfs magic links. -/
inductive SymlinkTarget where
  /-- Standard symlink target path bytes. -/
  | path (bytes : ByteArray)
  /-- Procfs magic link resolving directly to `targetIno` (optionally tied to open descriptor `fdHid?`). -/
  | procMagic (targetIno : InodeId) (fdHid? : Option HandleId := none)
  deriving Repr, BEq

/-- Pipe ring capacity in 4 KiB pages (`PIPE_MIN_DEF_BUFFERS = 2`, `PIPE_DEF_BUFFERS = 16`). -/
inductive PipeCapacity where
  /-- Known exact capacity in 4 KiB pages. -/
  | exact (pages : Nat)
  /-- Uncalibrated kernel pipe capacity bounded in `[minPages, maxPages]`. -/
  | uncalibrated (minPages : Nat := 2) (maxPages : Nat := 16)
  deriving Repr, DecidableEq, BEq

/-- Lower bound in pages on `PipeCapacity`. -/
def PipeCapacity.minPages : PipeCapacity → Nat
  | .exact p => max 1 p
  | .uncalibrated lo _ => max 1 lo

/-- Upper bound in pages on `PipeCapacity`. -/
def PipeCapacity.maxPages : PipeCapacity → Nat
  | .exact p => max 1 p
  | .uncalibrated lo hi => max 1 (max lo hi)

/-- Named FIFO (`S_IFIFO`) pipe ring state. -/
structure PipeRing where
  /-- Pending unread bytes queued in the pipe buffer. -/
  buf : ByteArray := ByteArray.mk #[]
  /-- Occupied 4 KiB pipe ring slots `(tailOffset, unreadBytes)`. -/
  slots : List (Nat × Nat) := []
  /-- Number of open read-capable handles (`rdonly` or `rdwr`). -/
  readers : Nat := 0
  /-- Number of open write-capable handles (`wronly` or `rdwr`). -/
  writers : Nat := 0
  /-- Pipe ring page capacity. -/
  capacity : PipeCapacity := .uncalibrated 2 16
  deriving Repr, BEq

/-- Per-kind inode payload guaranteeing `kind` and payload agree by construction. -/
inductive InodeData where
  /-- Regular file payload. -/
  | reg (d : RegData := {})
  /-- Directory payload. -/
  | dir (d : DirData := {})
  /-- Symlink payload. -/
  | symlink (t : SymlinkTarget)
  /-- Named FIFO payload. -/
  | fifo (p : PipeRing := {})
  /-- Character device payload. -/
  | charDev (k : CharDevKind := .generic)
  /-- Unix domain socket. -/
  | socket
  /-- Block device. -/
  | blockDev
  /-- Unclassified special file. -/
  | other
  deriving Repr, BEq

/-- Inode ownership and active user-namespace mapping (`kuid_has_mapping` / `kgid_has_mapping`). -/
structure InodeOwner where
  /-- Whether the effective process UID owns this inode. -/
  ownedByUid : Bool := true
  /-- Whether the effective process is in the inode's owning GID (`in_group_p`). -/
  inGroup : Bool := true
  /-- Optional numeric UID for sticky-directory checks. -/
  uid? : Option UInt32 := none
  /-- Whether the inode UID is mapped in the active user namespace. -/
  uidMapped : Bool := true
  /-- Whether the inode GID is mapped in the active user namespace. -/
  gidMapped : Bool := true
  /-- Optional opaque tag distinguishing unmapped host UIDs sharing `overflowuid`. -/
  uidTag? : Option UInt32 := none
  deriving Repr, DecidableEq, BEq

/-- Observed kernel `(st_dev, st_ino)` identity and cross-mount aliasing policy. -/
structure KernelIdentity where
  /-- Real kernel `st_dev` bound on first `fstat` / `fstatat` observation. -/
  dev? : Option UInt64 := none
  /-- Real kernel `st_ino` bound on first `fstat` / `fstatat` observation. -/
  ino? : Option UInt64 := none
  /-- Whether bind-mounted / lower hardlinked nodes may share `(st_dev, st_ino)` with another mount or dentry. -/
  allowAlias : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Backing filesystem nature of an inode. -/
inductive InodeOrigin where
  /-- Normal scratch or overlayfs inode (`lowerUncopied = true` iff copy-up pending). -/
  | managed (lowerUncopied : Bool := false)
  /-- External host inode whose metadata (`st_size`, `st_nlink`, dynamic reads) is kernel-generated. -/
  | hostDynamic
  /-- Virtual pseudo-filesystem inode (`/proc`, `/sys`). -/
  | pseudoFs
  deriving Repr, DecidableEq, BEq

/-- Structured logical inode record tracked by `FilesState`. -/
structure VNode where
  /-- Kind-specific payload. -/
  data : InodeData
  /-- Lower 12 permission mode bits (`0o7777`). -/
  mode : Mode
  /-- Whether lower 12 mode bits were explicitly set (`0o7777`) vs umask-masked. -/
  modeExact : Bool := false
  /-- Hard-link count. -/
  nlink : Nat := 1
  /-- Logical mount identifier. -/
  mountId : Nat := 0
  /-- Ownership and user-namespace mapping. -/
  owner : InodeOwner := {}
  /-- Kernel `(st_dev, st_ino)` binding. -/
  kernelId : KernelIdentity := {}
  /-- Backing filesystem origin. -/
  origin : InodeOrigin := .managed false
  deriving Repr, BEq

/-- Project `FileKind` from `VNode.data`. -/
def VNode.kind (vn : VNode) : FileKind :=
  match vn.data with
  | .reg _ => .reg
  | .dir _ => .dir
  | .symlink _ => .symlink
  | .fifo _ => .fifo
  | .charDev _ => .charDev
  | .socket => .socket
  | .blockDev => .blockDev
  | .other => .other

/-- Project regular-file bytes (`empty` for non-regular files). -/
def VNode.bytes (vn : VNode) : ByteArray :=
  match vn.data with
  | .reg rd => rd.bytes
  | _ => ByteArray.mk #[]

/-- Project directory children (`[]` for non-directories). -/
def VNode.children (vn : VNode) : List (ByteArray × InodeId) :=
  match vn.data with
  | .dir dd => dd.children
  | _ => []

/-- Project parent directory inode (`0` for non-directories). -/
def VNode.parentIno (vn : VNode) : InodeId :=
  match vn.data with
  | .dir dd => dd.parentIno
  | _ => 0

/-- Return `true` iff `vn` is a dead directory (`.unlinked` or `.overlayDeadLower`). -/
def VNode.isDeadDir (vn : VNode) : Bool :=
  match vn.data with
  | .dir dd => dd.lifecycle.isDead
  | _ => false

/-- Return `true` iff `vn` is a merged (live or removed) `overlayfs` directory. -/
def VNode.overlayMergedDir (vn : VNode) : Bool :=
  match vn.data with
  | .dir dd => dd.lifecycle == .overlayMerged || dd.lifecycle == .overlayDeadMerged
  | _ => false

/-- Project regular symlink target bytes (`empty` for magic links and non-symlinks). -/
def VNode.symlinkTarget (vn : VNode) : ByteArray :=
  match vn.data with
  | .symlink (.path b) => b
  | _ => ByteArray.mk #[]

/-- Return `true` iff `vn` is a procfs magic link. -/
def VNode.isMagicLink (vn : VNode) : Bool :=
  match vn.data with
  | .symlink (.procMagic _ _) => true
  | _ => false

/-- Return `true` iff `vn` belongs to a virtual pseudo-filesystem (`/proc`, `/sys`). -/
def VNode.isPseudo (vn : VNode) : Bool :=
  vn.origin == .pseudoFs

/-- Return `true` iff `vn` has kernel-generated metadata or dynamic reads. -/
def VNode.isDynamic (vn : VNode) : Bool :=
  vn.origin != .managed false && vn.origin != .managed true

/-- Return `true` iff `vn` resides on an uncopied `overlayfs` lower layer. -/
def VNode.mayCopyUp (vn : VNode) : Bool :=
  vn.origin == .managed true

/-- Mutually exclusive file position for regular descriptors vs directory streams. -/
inductive FilePos where
  /-- Byte offset for `read` / `write`. -/
  | byteOffset (off : Nat := 0)
  /-- Entry cursor and EOF latch for `getdents64`. -/
  | dirStream (cursor : Nat := 0) (atEof : Bool := false)
  deriving Repr, DecidableEq, BEq

/-- Extract byte offset (`0` if directory stream). -/
def FilePos.offset : FilePos → Nat
  | .byteOffset o => o
  | .dirStream _ _ => 0

/-- Extract directory cursor (`0` if byte offset). -/
def FilePos.dirCursor : FilePos → Nat
  | .byteOffset _ => 0
  | .dirStream c _ => c

/-- Extract directory EOF latch (`false` if byte offset). -/
def FilePos.dirAtEof : FilePos → Bool
  | .byteOffset _ => false
  | .dirStream _ eof => eof

/-- Descriptor lifecycle under `LeanFdBox` and optional outer `ambientSeccomp`. -/
inductive FdCloseState where
  /-- Box and kernel descriptor are open. -/
  | open
  /-- Prior `close` under `ambientSeccomp` returned a `filp_close`-overlapping errno. -/
  | closeUncertain
  deriving Repr, DecidableEq, BEq

/-- Open file description entry tracked by `FilesState`. -/
structure OpenDesc where
  /-- Target logical inode ID. -/
  ino : InodeId
  /-- Access mode (`rdonly`, `wronly`, `rdwr`). -/
  access : AccessMode
  /-- Whether `O_APPEND` is set. -/
  append : Bool := false
  /-- Whether `O_NONBLOCK` is set. -/
  nonblock : Bool := false
  /-- Whether `FD_CLOEXEC` is set. -/
  cloexec : Bool := true
  /-- Current byte offset or directory stream cursor. -/
  pos : FilePos := .byteOffset 0
  /-- Advisory `flock` lock currently held by this open file description. -/
  lock? : Option LockKind := none
  /-- Close certainty state. -/
  closeState : FdCloseState := .open
  /-- Resolved directory entry `(parentIno, leaf)` backing this descriptor, if linked/known. -/
  dentry? : Option (InodeId × ByteArray) := none
  /-- Most recent `(parentIno, leaf)` observed for this descriptor (retained across unlink). -/
  lastDentry? : Option (InodeId × ByteArray) := none
  /-- Maximum `linux_dirent64` record size observed in the directory during prior `getdents64` calls on this descriptor. -/
  dirCachedMaxReclen : Nat := 0
  /-- Whether this descriptor was opened with `O_PATH` (path-only reference FD). -/
  isPathFd : Bool := false
  /-- Whether this descriptor was created via `dupStdio` wrapping an external stdio FD. -/
  isExternalStdio : Bool := false
  /-- Directory entries observed during prior `getdents64` calls (preserving `ext4` `private_data` unlinked cache). -/
  dirCachedEntries : List (ByteArray × Option FileKind) := []
  /-- Kernel open file description identity when aliasing a closed stdio slot `0/1/2`. -/
  ofdId? : Option Nat := none
  deriving Repr, DecidableEq, BEq

/-- Per-logical-mount VFS capability profile. -/
structure MountProfile where
  /-- Read-only mount (`ST_RDONLY`), returning `EROFS` on mutations. -/
  readOnly : Bool := false
  /-- Whether symbolic links are supported (`false` on `vfat`). -/
  supportsSymlinks : Bool := true
  /-- Whether POSIX per-inode mode/permission updates persist (`false` on `vfat`). -/
  posixModes : Bool := true
  /-- Whether overlayfs semantics apply. -/
  isOverlay : Bool := false
  /-- Whether `memfd`/`tmpfs` file seals are supported. -/
  supportsSeals : Bool := true
  deriving Repr, DecidableEq, BEq

/-- Effective Linux process capabilities with exact kernel VFS credential helpers. -/
structure ProcessCred where
  /-- `CAP_DAC_OVERRIDE`. -/
  capDacOverride : Bool := false
  /-- `CAP_DAC_READ_SEARCH`. -/
  capDacReadSearch : Bool := false
  /-- `CAP_FOWNER`. -/
  capFowner : Bool := false
  /-- `CAP_FSETID`. -/
  capFsetid : Bool := false
  /-- Whether running in `init_user_ns` (`capable(CAP_FSETID)` in `should_remove_suid`). -/
  initUserNs : Bool := true
  /-- Whether the process's effective/filesystem UID is mapped in `current_user_ns()`. -/
  uidMapped : Bool := true
  /-- Whether the process's effective/filesystem GID is mapped in `current_user_ns()`. -/
  gidMapped : Bool := true
  deriving Repr, DecidableEq, BEq

/-- Exact `capable_wrt_inode_uidgid(idmap, inode, cap)` (`kernel/capability.c`). -/
def ProcessCred.capableWrtInode (c : ProcessCred) (o : InodeOwner) (cap : ProcessCred → Bool) : Bool :=
  cap c && o.uidMapped && o.gidMapped

/-- Exact `capable(CAP_FSETID)` for `should_remove_suid()` (`fs/inode.c`, requires `init_user_ns`). -/
def ProcessCred.capableGlobalFsetid (c : ProcessCred) : Bool :=
  c.capFsetid && c.initUserNs

/-- Exact `inode_owner_or_capable(idmap, inode)` (`fs/inode.c`). -/
def ProcessCred.ownerOrCapFowner (c : ProcessCred) (o : InodeOwner) : Bool :=
  o.ownedByUid || (c.capFowner && o.uidMapped)

/-- Exact `in_group_or_capable(idmap, inode, vfsgid)` (`fs/attr.c` `setattr_prepare`). -/
def ProcessCred.inGroupOrCapFsetid (c : ProcessCred) (o : InodeOwner) : Bool :=
  o.inGroup || c.capableWrtInode o (·.capFsetid)

/-- Kernel `fs.protected_*` sysctls. -/
structure FsSysctls where
  /-- `fs.protected_regular` (`0`, `1`, or `2`). -/
  protectedRegular : UInt32 := 2
  /-- `fs.protected_fifos` (`0`, `1`, or `2`). -/
  protectedFifos : UInt32 := 1
  /-- `fs.protected_symlinks` (`false` = 0, `true` = 1). -/
  protectedSymlinks : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Current working directory state (`bound` exact path vs `unbound` default). -/
inductive CwdPath where
  /-- Exact host CWD path observed by `getcwd`. -/
  | bound (path : ByteArray)
  /-- Unbound initial CWD path prior to the first succeeding `getcwd`. -/
  | unbound (defaultPath : ByteArray)
  deriving Repr, BEq

/-- Extract byte path from `CwdPath`. -/
def CwdPath.bytes : CwdPath → ByteArray
  | .bound p | .unbound p => p

/-- Return `true` iff `CwdPath` has been bound to the real host CWD. -/
def CwdPath.isBound : CwdPath → Bool
  | .bound _ => true
  | .unbound _ => false

/-- Executable stateful world model for all 23 curated Linux `Files` syscalls. -/
structure FilesState where
  /-- Logical inode table (`0` is the filesystem root `/`). -/
  inodes : List (InodeId × VNode)
  /-- Open descriptor table mapping `HandleId` to `OpenDesc`. -/
  fds : List (HandleId × OpenDesc)
  /-- Logical current working directory path state. -/
  cwdPath : CwdPath
  /-- Logical inode ID of filesystem root `/`. -/
  rootIno : InodeId := 0
  /-- Logical inode ID of current working directory (`AT_FDCWD`). -/
  cwdIno : InodeId := 0
  /-- Process file mode creation mask (`umask`, lower 9 bits `0o0777`). -/
  umask : Mode := 0o022
  /-- Per-mount VFS capability profiles keyed by `mountId`. -/
  mountProfiles : List (Nat × MountProfile) := []
  /-- Effective Linux process capabilities. -/
  cred : ProcessCred := {}
  /-- Kernel `fs.protected_*` sysctl configuration. -/
  sysctls : FsSysctls := {}
  /-- Whether an inherited outer `seccomp(SECCOMP_RET_ERRNO)` filter is active. -/
  ambientSeccomp : Bool := false
  /-- Initially closed host stdio slots (`0/1/2`) available for lowest-FD allocation and `dupStdio` aliasing. -/
  freeStdioSlots : List StdioFd := []
  /-- Mapping from OS stdio slot `0/1/2` to managed `HandleId` when an open occupied a closed stdio slot. -/
  managedStdioMap : List (StdioFd × HandleId) := []
  /-- Next handle-ID watermarks recorded when closing handles still pinned by `O_PATH` `/proc/self/fd` links. -/
  procClosedAfter : List (HandleId × Nat) := []
  /-- Next synthetic open file description ID for `dupStdio` aliasing. -/
  nextOfdId : Nat := 0
  /-- Next logical inode ID to allocate. -/
  nextIno : InodeId
  /-- Next logical handle ID to allocate. -/
  nextHid : HandleId
  deriving Repr, BEq

/-- Initial `FilesState` containing an empty root/CWD directory (inode `0`, mode `0o755`). -/
def FilesState.initial (cwd : ByteArray := ByteArray.mk #[47]) : FilesState :=
  { inodes := [(0, { data := .dir { parentIno := 0, lifecycle := .live }, mode := 0o755, nlink := 2 })]
    fds := []
    cwdPath := if cwd.size > 1 then .bound cwd else .unbound cwd
    rootIno := 0
    cwdIno := 0
    umask := 0o022
    nextIno := 1
    nextHid := 0 }

instance : Inhabited FilesState := ⟨FilesState.initial⟩

/-- Configure `ambientSeccomp` on `s` for pre-installed safe outer `seccomp(SECCOMP_RET_ERRNO)` filters. -/
def FilesState.withOuterSeccomp (s : FilesState) (enabled : Bool := true) : FilesState :=
  { s with ambientSeccomp := enabled }

/-- Unboxed index loop comparing `rem` bytes of `a` and `b` starting at `i`. -/
def bytesEqLoop (a b : ByteArray) (i rem : Nat) : Bool :=
  match rem with
  | 0 => true
  | rem' + 1 =>
    if byteGetD a i == byteGetD b i then bytesEqLoop a b (i + 1) rem' else false

/-- Kernel-reducible unboxed `ByteArray` equality. -/
def bytesEq (a b : ByteArray) : Bool :=
  a.size == b.size && bytesEqLoop a b 0 a.size

/-- Look up a `ByteArray` key in a directory children list. -/
def bytesAssocGet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) : Option β :=
  match xs with
  | [] => none
  | (k', v) :: rest => if bytesEq k' k then some v else bytesAssocGet rest k

private def bytesAssocSetAux {β : Type} (k : ByteArray) (v : β) :
    List (ByteArray × β) → List (ByteArray × β) → List (ByteArray × β)
  | [], acc => acc.reverseAux [(k, v)]
  | (k', v') :: rest, acc =>
    if bytesEq k' k then acc.reverseAux ((k, v) :: rest)
    else bytesAssocSetAux k v rest ((k', v') :: acc)

/-- Insert or replace a `ByteArray` key in a directory children list (tail-recursive). -/
def bytesAssocSet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) (v : β) : List (ByteArray × β) :=
  bytesAssocSetAux k v xs []

private def bytesAssocEraseAux {β : Type} (k : ByteArray) :
    List (ByteArray × β) → List (ByteArray × β) → List (ByteArray × β)
  | [], acc => acc.reverse
  | (k', v') :: rest, acc =>
    if bytesEq k' k then acc.reverseAux rest
    else bytesAssocEraseAux k rest ((k', v') :: acc)

/-- Remove a `ByteArray` key from a directory children list (tail-recursive). -/
def bytesAssocErase {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) : List (ByteArray × β) :=
  bytesAssocEraseAux k xs []

/-- Look up a key in an association list. -/
def assocGet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  match xs with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else assocGet rest k

private def assocSetAux {α β : Type} [BEq α] (k : α) (v : β) :
    List (α × β) → List (α × β) → List (α × β)
  | [], acc => acc.reverseAux [(k, v)]
  | (k', v') :: rest, acc =>
    if k' == k then acc.reverseAux ((k, v) :: rest)
    else assocSetAux k v rest ((k', v') :: acc)

/-- Insert or replace a key in an association list (tail-recursive). -/
def assocSet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) (v : β) : List (α × β) :=
  assocSetAux k v xs []

private def assocEraseAux {α β : Type} [BEq α] (k : α) :
    List (α × β) → List (α × β) → List (α × β)
  | [], acc => acc.reverse
  | (k', v') :: rest, acc =>
    if k' == k then acc.reverseAux rest
    else assocEraseAux k rest ((k', v') :: acc)

/-- Remove a key from an association list (tail-recursive). -/
def assocErase {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : List (α × β) :=
  assocEraseAux k xs []

/-- Extract `bytes[start .. start + len)` without boxed `Array UInt8` materialization. -/
def sliceBytes (b : ByteArray) (start len : Nat) : ByteArray :=
  if start == 0 && len >= b.size then b
  else b.extract start (min b.size (start + len))

private def coalesceExtentsAux :
    Option (Nat × ByteArray) → List (Nat × ByteArray) → List (Nat × ByteArray) → List (Nat × ByteArray)
  | none, [], acc => acc.reverse
  | some cur, [], acc => (cur :: acc).reverse
  | none, hd :: tl, acc => coalesceExtentsAux (some hd) tl acc
  | some (s1, d1), (s2, d2) :: tl, acc =>
    if s1 + d1.size == s2 && d1.size + d2.size <= 4096 then
      coalesceExtentsAux (some (s1, d1 ++ d2)) tl acc
    else
      coalesceExtentsAux (some (s2, d2)) tl ((s1, d1) :: acc)

private def insertExtentAux (pos wEnd : Nat) (chunk : ByteArray) :
    List (Nat × ByteArray) → Bool → List (Nat × ByteArray) → List (Nat × ByteArray)
  | [], inserted, acc =>
    let finalAcc := if inserted then acc else (pos, chunk) :: acc
    coalesceExtentsAux none finalAcc.reverse []
  | (eStart, eData) :: rest, inserted, acc =>
    let eEnd := eStart + eData.size
    if eEnd <= pos then
      insertExtentAux pos wEnd chunk rest inserted ((eStart, eData) :: acc)
    else if eStart >= wEnd then
      let acc' := if inserted then acc else (pos, chunk) :: acc
      insertExtentAux pos wEnd chunk rest true ((eStart, eData) :: acc')
    else
      let acc1 := if eStart < pos then (eStart, sliceBytes eData 0 (pos - eStart)) :: acc else acc
      let acc2 := if inserted then acc1 else (pos, chunk) :: acc1
      let acc3 := if eEnd > wEnd then (wEnd, sliceBytes eData (wEnd - eStart) (eEnd - wEnd)) :: acc2 else acc2
      insertExtentAux pos wEnd chunk rest true acc3

/-- Overwrite sparse `RegData` at `offset` with `chunk` in `O(#extents + chunk.size)` memory/time. -/
def RegData.writeAt (rd : RegData) (offset : Nat) (chunk : ByteArray) : RegData :=
  if chunk.size == 0 then rd
  else
    let wEnd := offset + chunk.size
    { rd with
      size := max rd.size wEnd
      extents := insertExtentAux offset wEnd chunk rd.extents false [] }

/-- ASCII path separator byte (`'/'`, `47`). -/
def slashByte : UInt8 := 47

/-- Single-dot path segment (`"."`). -/
def dotBytes : ByteArray := ByteArray.mk #[46]

/-- Double-dot parent path segment (`".."`). -/
def dotDotBytes : ByteArray := ByteArray.mk #[46, 46]

/-- Root-slash sentinel leaf returned by `resolveParentAndLeaf` for `"/"`. -/
def slashBytes : ByteArray := ByteArray.mk #[47]

/-- ASCII `"(unreachable)"` prefix returned by Linux `getcwd` for paths outside the root mount. -/
def unreachablePrefix : ByteArray := ByteArray.mk #[40, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 41]

/-- Return `true` iff `b` begins with `pfx` byte-for-byte. -/
def startsWithBytes (b pfx : ByteArray) : Bool :=
  b.size >= pfx.size && bytesEq (sliceBytes b 0 pfx.size) pfx

/-- Index-scanning helper for `splitPathBytes` avoiding intermediate `List UInt8` materialization. -/
def splitPathBytesLoop (path : ByteArray) (i segStart : Nat) (acc : List ByteArray) : Nat → List ByteArray
  | 0 =>
    let acc' :=
      if segStart < i then
        (if segStart == 0 && acc.isEmpty then [path] else path.extract segStart i :: acc)
      else acc
    acc'.reverse
  | rem + 1 =>
    if h : i < path.size then
      let b := path[i]
      if b == slashByte then
        let acc' := if segStart < i then path.extract segStart i :: acc else acc
        splitPathBytesLoop path (i + 1) (i + 1) acc' rem
      else
        splitPathBytesLoop path (i + 1) segStart acc rem
    else
      let acc' :=
        if segStart < i then
          (if segStart == 0 && acc.isEmpty then [path] else path.extract segStart i :: acc)
        else acc
      acc'.reverse

private theorem splitPathBytesLoop_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    ∀ k i, i + k = path.size →
      splitPathBytesLoop path i 0 [] k = [path]
  | 0, i, hk => by
    have hEq : i = path.size := by omega
    subst hEq
    unfold splitPathBytesLoop
    simp [hPos]
  | k + 1, i, hk => by
    have hi : i < path.size := by omega
    unfold splitPathBytesLoop
    simp only [hi, ↓reduceDIte]
    have hNe : (path[i] == slashByte) = false := by
      have h1 := hNo i hi
      simpa [bne] using h1
    rw [hNe]
    exact splitPathBytesLoop_noSlash path hPos hNo k (i + 1) (by omega)

/-- Split a byte path into `(isAbs, nonEmptySegments, hasTrailingSlash)`. -/
def splitPathBytes (path : ByteArray) : Bool × List ByteArray × Bool :=
  let sz := path.size
  let isAbs := if h : 0 < sz then path[0] == slashByte else false
  let trailingSlash := if h : 0 < sz then path[sz - 1] == slashByte else false
  (isAbs, splitPathBytesLoop path 0 0 [] sz, trailingSlash)

/-- Any non-empty path without `'/'` splits to `[path]`. -/
theorem splitPathBytes_of_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    splitPathBytes path = (false, [path], false) := by
  unfold splitPathBytes
  have h0 : (path[0] == slashByte) = false := by
    have := hNo 0 hPos
    simpa [bne] using this
  have hLast : (path[path.size - 1] == slashByte) = false := by
    have := hNo (path.size - 1) (Nat.sub_lt hPos Nat.zero_lt_one)
    simpa [bne] using this
  simp only [hPos, ↓reduceDIte, h0, hLast]
  exact congrArg (fun x => (false, x, false))
    (splitPathBytesLoop_noSlash path hPos hNo path.size 0 (Nat.zero_add _))

/-- Look up the `mountId` of `ino` in `s` (`0` if absent). -/
def inodeMountId (s : FilesState) (ino : InodeId) : Nat :=
  match assocGet s.inodes ino with
  | some vn => vn.mountId
  | none => 0

/-- Look up the `MountProfile` for `mntId` in `s`. -/
def mountProfileOf (s : FilesState) (mntId : Nat) : MountProfile :=
  match assocGet s.mountProfiles mntId with
  | some mp => mp
  | none => {}

/-- Return `true` iff `mntId` is a read-only mount (`EROFS`). -/
def isReadOnlyMount (s : FilesState) (mntId : Nat) : Bool :=
  (mountProfileOf s mntId).readOnly

/-- Return `true` iff `mntId` supports symbolic links (`false` on `vfat`). -/
def mountSupportsSymlinks (s : FilesState) (mntId : Nat) : Bool :=
  (mountProfileOf s mntId).supportsSymlinks

/-- Return `true` iff `mntId` supports POSIX per-inode mode/permission updates. -/
def mountPosixModes (s : FilesState) (mntId : Nat) : Bool :=
  (mountProfileOf s mntId).posixModes

/-- Check owner permission bits (`0o400` read, `0o200` write, `0o100` exec). -/
def hasOwnerPerm (mode : Mode) (needR needW needX : Bool) : Bool :=
  (!needR || (mode &&& 0o400) != 0) &&
  (!needW || (mode &&& 0o200) != 0) &&
  (!needX || (mode &&& 0o100) != 0)

/-- Check group permission bits (`0o040` read, `0o020` write, `0o010` exec). -/
def hasGroupPerm (mode : Mode) (needR needW needX : Bool) : Bool :=
  (!needR || (mode &&& 0o040) != 0) &&
  (!needW || (mode &&& 0o020) != 0) &&
  (!needX || (mode &&& 0o010) != 0)

/-- Check world permission bits (`0o004` read, `0o002` write, `0o001` exec). -/
def hasOtherPerm (mode : Mode) (needR needW needX : Bool) : Bool :=
  (!needR || (mode &&& 0o004) != 0) &&
  (!needW || (mode &&& 0o002) != 0) &&
  (!needX || (mode &&& 0o001) != 0)

/-- Check VFS permissions on `vn` for the active process UID/GID (`ownedByUid` -> `inGroup` -> world bits). -/
def hasVNodePerm (vn : VNode) (needR needW needX : Bool) : Bool :=
  if vn.owner.ownedByUid then hasOwnerPerm vn.mode needR needW needX
  else if vn.owner.inGroup then hasGroupPerm vn.mode needR needW needX
  else hasOtherPerm vn.mode needR needW needX

private def sameKnownOwner (a b : VNode) : Bool :=
  if a.owner.uidMapped && b.owner.uidMapped then
    match a.owner.uid?, b.owner.uid? with
    | some u1, some u2 => u1 == u2
    | _, _ => false
  else if !a.owner.uidMapped && !b.owner.uidMapped then
    match a.owner.uidTag?, b.owner.uidTag? with
    | some t1, some t2 => t1 == t2
    | _, _ => false
  else
    false

/-- Check permission bits under `CAP_DAC_OVERRIDE` and `CAP_DAC_READ_SEARCH`, falling back to `hasVNodePerm`. -/
def hasVNodePermIn (s : FilesState) (vn : VNode) (needR needW needX : Bool) : Bool :=
  if s.cred.capableWrtInode vn.owner (·.capDacOverride) &&
      (vn.kind == .dir || !needX || (vn.mode &&& 0o111) != 0) then true
  else if s.cred.capableWrtInode vn.owner (·.capDacReadSearch) &&
      (if vn.kind == .dir then !needW else !needW && !needX) then true
  else hasVNodePerm vn needR needW needX

/-- Resolve the starting directory inode for an `*at` syscall (`none` = `s.cwdIno`). -/
def resolveStartDir (s : FilesState) (dir : Option HandleId) : Except Errno InodeId :=
  match dir with
  | none => .ok s.cwdIno
  | some hid =>
    match assocGet s.fds hid with
    | none => .error Errno.EBADF
    | some desc =>
      match assocGet s.inodes desc.ino with
      | none => .error Errno.EBADF
      | some vn =>
        if vn.kind == .dir then .ok desc.ino
        else .error Errno.ENOTDIR

/-- Validate path bytes for embedded NUL (`EINVAL`) and Linux `getname_flags` total length limit (`>= PATH_MAX` -> `ENAMETOOLONG`). -/
def validatePathBytes (path : ByteArray) : Except Errno (Bool × List ByteArray × Bool) :=
  if hasEmbeddedNul path then .error Errno.EINVAL
  else if path.size >= PATH_MAX then .error Errno.ENAMETOOLONG
  else .ok (splitPathBytes path)

/-- Maximum symbolic link dereference depth (`MAXSYMLINKS`). -/
def MAX_SYMLINKS : Nat := 40

/-- Check whether `anc` is an ancestor directory of `desc` (or equal to `desc`). -/
def isAncestorInode (s : FilesState) (anc desc : InodeId) (fuel : Nat := 64) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if anc == desc then true
    else
      match assocGet s.inodes desc with
      | none => false
      | some vn =>
        if vn.parentIno == desc then false
        else isAncestorInode s anc vn.parentIno fuel'

/-- Outcome of `openat` / `openat2` / lookup path traversal. -/
inductive OpenTarget where
  /-- Resolved to an existing inode `ino` (with trailing-`/` and special-`.`/`..`/root flags, optional parent/leaf, and proc-magic flag). -/
  | existing (ino : InodeId) (trailing : Bool) (isSpecialDotRoot : Bool := false)
      (parentIno? : Option InodeId := none) (leaf? : Option ByteArray := none)
      (viaProcMagic : Bool := false) (procMagicHid? : Option HandleId := none)
  /-- Final segment `leaf` was absent inside directory `parentIno`. -/
  | missingInParent (parentIno : InodeId) (leaf : ByteArray) (trailing : Bool)
  /-- Traversal passed through or ended with trailing `'/'` on an external opaque handle. -/
  | externalOpaque (procMagicHid? : Option HandleId := none)
  deriving Repr, DecidableEq, BEq

/-- Mode parameterizing unified `walkPath`. -/
inductive WalkMode where
  /-- Normal path lookup (`resolvePath` / `resolveLookupOrExt`). -/
  | lookup (followFinal : Bool)
  /-- Parent-directory lookup (`resolveParentAndLeaf` / Linux `path_parentat` / `link_path_walk`), where every component precedes a leaf and never takes the `WALK_TRAILING` `may_follow_link` check. -/
  | parent
  /-- `openat` / `openat2` lookup tracking missing leaf in parent and `O_CREAT | O_EXCL` symlink stop. -/
  | openTarget (followFinal exclCreate hasCreat : Bool)
  deriving Repr, DecidableEq, BEq

/-- Result returned by `walkPath` recording whether traversal touched any `..` segment. -/
structure WalkResult where
  /-- Resolved target or missing-leaf parent. -/
  target : OpenTarget
  /-- True iff the walk processed a `..` component (directly or inside a followed symlink). -/
  touchedDotDot : Bool
  deriving Repr, DecidableEq, BEq

private def findDirDentry (inodes : List (InodeId × VNode)) (targetIno : InodeId) : Option (InodeId × ByteArray) :=
  inodes.findSome? fun (pIno, pvn) =>
    match pvn.data with
    | .dir dd =>
      dd.children.findSome? fun (leaf, cIno) =>
        if cIno == targetIno && !bytesEq leaf dotBytes && !bytesEq leaf dotDotBytes then some (pIno, leaf)
        else none
    | _ => none

private def resolveProcMagicTarget (s : FilesState) (tgtIno : InodeId)
    (fdHid? : Option HandleId) : Except Errno (InodeId × Option (InodeId × ByteArray)) :=
  match fdHid? with
  | some hid =>
    match assocGet s.fds hid with
    | some desc => .ok (desc.ino, desc.dentry?)
    | none => .error Errno.ENOENT
  | none => .ok (tgtIno, none)

private def isDentryLinked (s : FilesState) (targetIno : InodeId) : Option (InodeId × ByteArray) → Bool
  | none => false
  | some (pIno, leaf) =>
    match assocGet s.inodes pIno with
    | some pvn =>
      match pvn.data with
      | .dir dd => !pvn.isDeadDir && pvn.nlink > 0 && bytesAssocGet dd.children leaf == some targetIno
      | _ => false
    | none => false

private def rebindDentryFds (fds : List (HandleId × OpenDesc)) (oldIno : InodeId)
    (parentLeaf : InodeId × ByteArray) (newIno : InodeId) : List (HandleId × OpenDesc) :=
  fds.map fun (hid, d) =>
    if d.ino == oldIno && d.dentry? == some parentLeaf then (hid, { d with ino := newIno })
    else (hid, d)

private def clearDentryOnFds (fds : List (HandleId × OpenDesc)) (parentLeaf : InodeId × ByteArray) :
    List (HandleId × OpenDesc) :=
  fds.map fun (hid, d) =>
    if d.dentry? == some parentLeaf then (hid, { d with dentry? := none })
    else (hid, d)

private def moveDentryOnFds (fds : List (HandleId × OpenDesc))
    (oldPL newPL : InodeId × ByteArray) (exchange : Bool) : List (HandleId × OpenDesc) :=
  fds.map fun (hid, d) =>
    if d.dentry? == some oldPL then (hid, { d with dentry? := some newPL, lastDentry? := some newPL })
    else if d.dentry? == some newPL then
      let next? := if exchange then some oldPL else none
      (hid, { d with dentry? := next?, lastDentry? := if exchange then some oldPL else d.lastDentry? })
    else (hid, d)

private def resolveStartDirDentry (s : FilesState) (dir : Option HandleId) (isAbs : Bool)
    (resolve : ResolveFlags) : Option (InodeId × ByteArray) :=
  if isAbs && !resolve.beneath && !resolve.inRoot then none
  else
    match dir with
    | some hid => (assocGet s.fds hid).bind (·.dentry?)
    | none => if s.cwdIno == s.rootIno then none else findDirDentry s.inodes s.cwdIno

/-- Unified structurally-recursive path segment walker for lookups and `openat`/`openat2`. -/
def walkPath (s : FilesState) (rootIno : InodeId) (anchorMount : Nat) (resolve : ResolveFlags)
    (mode : WalkMode) (rootSet : Bool := true) (touchedDotDot : Bool := false)
    (curDentry? : Option (InodeId × ByteArray) := none) :
    Nat → Nat → InodeId → Nat → List ByteArray → Bool → (Except Errno OpenTarget × Bool)
  | 0, _, _, _, _, _ => (.error Errno.ELOOP, touchedDotDot)
  | stepFuel + 1, symFuel, curIno, depth, segs, trailing =>
    match segs with
    | [] =>
      let pIno? := curDentry?.map (·.1)
      let lf? := curDentry?.map (·.2)
      match mode with
      | .openTarget _ _ _ => (.ok (.existing curIno trailing true pIno? lf?), touchedDotDot)
      | .lookup _ | .parent =>
        match assocGet s.inodes curIno with
        | none => (.error Errno.ENOENT, touchedDotDot)
        | some vn =>
          if trailing && vn.kind != .dir then
            if vn.isDynamic && vn.kind == .other then (.ok (.externalOpaque none), touchedDotDot)
            else (.error Errno.ENOTDIR, touchedDotDot)
          else (.ok (.existing curIno trailing true pIno? lf?), touchedDotDot)
    | seg :: rest =>
      match assocGet s.inodes curIno with
      | none => (.error Errno.ENOENT, touchedDotDot)
      | some dirVn =>
        match dirVn.data with
        | .dir dd =>
          if !hasVNodePermIn s dirVn false false true then (.error Errno.EACCES, touchedDotDot)
          else if bytesEq seg dotBytes then
            walkPath s rootIno anchorMount resolve mode rootSet touchedDotDot curDentry? stepFuel symFuel curIno depth rest trailing
          else if bytesEq seg dotDotBytes then
            let td' := true
            if resolve.beneath && depth == 0 then (.error Errno.EXDEV, td')
            else if resolve.inRoot && depth == 0 then
              walkPath s rootIno anchorMount resolve mode rootSet td' (findDirDentry s.inodes rootIno) stepFuel symFuel rootIno 0 rest trailing
            else if resolve.noXdev && inodeMountId s dd.parentIno != anchorMount then (.error Errno.EXDEV, td')
            else
              let nextDepth := if depth > 0 then depth - 1 else 0
              walkPath s rootIno anchorMount resolve mode true td' (findDirDentry s.inodes dd.parentIno) stepFuel symFuel dd.parentIno nextDepth rest trailing
          else
            let isCreatTrail := match mode with
              | .openTarget _ _ hasCreat => rest.isEmpty && hasCreat && trailing
              | .lookup _ | .parent => false
            if isCreatTrail then
              (.ok (.existing curIno true false (curDentry?.map (·.1)) (curDentry?.map (·.2))), touchedDotDot)
            else if dirVn.nlink == 0 || dd.lifecycle.isDead then (.error Errno.ENOENT, touchedDotDot)
            else if seg.size > NAME_MAX then (.error Errno.ENAMETOOLONG, touchedDotDot)
            else
              let isFinal := rest.isEmpty
              match bytesAssocGet dd.children seg with
              | none =>
                match mode with
                | .openTarget _ _ _ =>
                  if isFinal then (.ok (.missingInParent curIno seg trailing), touchedDotDot)
                  else (.error Errno.ENOENT, touchedDotDot)
                | .lookup _ | .parent => (.error Errno.ENOENT, touchedDotDot)
              | some childIno =>
                match assocGet s.inodes childIno with
                | none => (.error Errno.ENOENT, touchedDotDot)
                | some childVn =>
                  if resolve.noXdev && childVn.mountId != anchorMount then (.error Errno.EXDEV, touchedDotDot)
                  else
                    match childVn.data with
                    | .symlink symTgt =>
                      let procDead := match symTgt with
                        | .procMagic _ (some hid) => (assocGet s.fds hid).isNone
                        | _ => false
                      if procDead then (.error Errno.ENOENT, touchedDotDot)
                      else
                      let (stopHere, exclStop) := match mode with
                        | .lookup followFinal => (isFinal && !followFinal && !trailing, false)
                        | .parent => (false, false)
                        | .openTarget followFinal exclCreate _ =>
                          (isFinal && (exclCreate || (!followFinal && !trailing)), isFinal && exclCreate)
                      let isTrailingWalk := isFinal && match mode with
                        | .parent => false
                        | .lookup _ | .openTarget _ _ _ => true
                      if exclStop then
                        (.ok (.existing childIno trailing false (some curIno) (some seg)), touchedDotDot)
                      else if stopHere then
                        (.ok (.existing childIno false false (some curIno) (some seg)), touchedDotDot)
                      else if symFuel == 0 then (.error Errno.ELOOP, touchedDotDot)
                      else if isTrailingWalk && s.sysctls.protectedSymlinks &&
                          (dirVn.mode &&& 0o1002) == 0o1002 && !childVn.owner.ownedByUid &&
                          !sameKnownOwner childVn dirVn then
                        (.error Errno.EACCES, touchedDotDot)
                      else if resolve.noSymlinks then (.error Errno.ELOOP, touchedDotDot)
                      else
                        match symTgt with
                        | .procMagic tgtIno fdHid? =>
                          if !childVn.owner.ownedByUid then (.error Errno.EACCES, touchedDotDot)
                          else if resolve.noMagiclinks then (.error Errno.ELOOP, touchedDotDot)
                          else
                            match resolveProcMagicTarget s tgtIno fdHid? with
                            | .error re =>
                              let maybeRebound := match fdHid? with
                                | some h => match assocGet s.procClosedAfter h with
                                  | some minH => s.fds.any (fun (k, _) => k >= minH)
                                  | none => false
                                | none => false
                              if maybeRebound then (.ok (.externalOpaque fdHid?), touchedDotDot)
                              else (.error re, touchedDotDot)
                            | .ok (effTgtIno, effDentry?) =>
                              match assocGet s.inodes effTgtIno with
                              | none => (.error Errno.ENOENT, touchedDotDot)
                              | some tgtVn =>
                                if resolve.noXdev && tgtVn.mountId != anchorMount then (.error Errno.EXDEV, touchedDotDot)
                                else if resolve.beneath || resolve.inRoot then (.error Errno.EXDEV, touchedDotDot)
                                else
                                  let isExtTarget :=
                                    (match fdHid? with
                                      | some hid => match assocGet s.fds hid with | some d => d.isExternalStdio | none => false
                                      | none => false) ||
                                    (tgtVn.isDynamic && tgtVn.kind == .other)
                                  if isExtTarget && (!isFinal || trailing) then
                                    (.ok (.externalOpaque fdHid?), touchedDotDot)
                                  else if isFinal then
                                    let pIno? := effDentry?.map (·.1)
                                    let lf? := effDentry?.map (·.2)
                                    match mode with
                                    | .lookup _ | .parent =>
                                      if trailing && tgtVn.kind != .dir then (.error Errno.ENOTDIR, touchedDotDot)
                                      else (.ok (.existing effTgtIno trailing false pIno? lf? true fdHid?), touchedDotDot)
                                    | .openTarget _ _ _ => (.ok (.existing effTgtIno trailing false pIno? lf? true fdHid?), touchedDotDot)
                                  else
                                    let nextDepth := if effTgtIno == rootIno then 0 else depth
                                    walkPath s rootIno anchorMount resolve mode rootSet touchedDotDot effDentry? stepFuel (symFuel - 1)
                                      effTgtIno nextDepth rest trailing
                        | .path targetBytes =>
                          if targetBytes.size == 0 then (.error Errno.ENOENT, touchedDotDot)
                          else
                            match validatePathBytes targetBytes with
                            | .error e => (.error e, touchedDotDot)
                            | .ok (tAbs, tSegs, tTrail) =>
                              if tAbs && resolve.beneath then (.error Errno.EXDEV, touchedDotDot)
                              else if tAbs && resolve.noXdev && !resolve.inRoot && !rootSet then (.error Errno.EXDEV, touchedDotDot)
                              else
                                let nextIno := if tAbs then (if resolve.inRoot then rootIno else s.rootIno) else curIno
                                if resolve.noXdev && inodeMountId s nextIno != anchorMount then (.error Errno.EXDEV, touchedDotDot)
                                else
                                  let nextDepth := if tAbs then 0 else depth
                                  let nextDentry? := if tAbs then none else curDentry?
                                  let combinedSegs := tSegs ++ rest
                                  let combinedTrail := if isFinal then (tTrail || trailing) else trailing
                                  if combinedSegs.isEmpty then
                                    match assocGet s.inodes nextIno with
                                    | none => (.error Errno.ENOENT, touchedDotDot)
                                    | some nvn =>
                                      let pIno? := nextDentry?.map (·.1)
                                      let lf? := nextDentry?.map (·.2)
                                      match mode with
                                      | .lookup _ | .parent =>
                                        if combinedTrail && nvn.kind != .dir then (.error Errno.ENOTDIR, touchedDotDot)
                                        else (.ok (.existing nextIno combinedTrail false pIno? lf?), touchedDotDot)
                                      | .openTarget _ _ _ => (.ok (.existing nextIno combinedTrail false pIno? lf?), touchedDotDot)
                                  else
                                    walkPath s rootIno anchorMount resolve mode rootSet touchedDotDot nextDentry? stepFuel (symFuel - 1)
                                      nextIno nextDepth combinedSegs combinedTrail
                    | _ =>
                      if isFinal then
                        match mode with
                        | .lookup _ | .parent =>
                          if trailing && childVn.kind != .dir then (.error Errno.ENOTDIR, touchedDotDot)
                          else (.ok (.existing childIno trailing false (some curIno) (some seg)), touchedDotDot)
                        | .openTarget _ _ _ =>
                          (.ok (.existing childIno trailing false (some curIno) (some seg)), touchedDotDot)
                      else if childVn.kind != .dir then (.error Errno.ENOTDIR, touchedDotDot)
                      else
                        walkPath s rootIno anchorMount resolve mode rootSet touchedDotDot (some (curIno, seg)) stepFuel symFuel
                          childIno (depth + 1) rest trailing
        | _ =>
          if dirVn.isDynamic && dirVn.kind == .other then (.ok (.externalOpaque none), touchedDotDot)
          else (.error Errno.ENOTDIR, touchedDotDot)

/-- Pre-open validation matching Linux `do_sys_openat2` / `path_init` (`EBADF`/`ENOENT`/`EXDEV`/`ENOTDIR`). -/
def validateOpenStart (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (resolve : ResolveFlags := {}) : Except Errno Unit := do
  let (isAbs, _, _) ← validatePathBytes path
  if path.size == 0 then .error Errno.ENOENT
  else if isAbs && resolve.beneath then .error Errno.EXDEV
  else
    let _ ←
      if isAbs && !resolve.beneath && !resolve.inRoot then .ok s.rootIno
      else resolveStartDir s dir
    .ok ()

/-- Check that an optional explicit `dirfd` handle is still open in `s.fds`. -/
private def checkDirHandleOpen (s : FilesState) (dir : Option HandleId) : Except Errno Unit :=
  match dir with
  | none => .ok ()
  | some hid =>
    match assocGet s.fds hid with
    | none => .error Errno.EBADF
    | some _ => .ok ()

/-- Resolve an `openat`/`openat2` path together with a `..`-traversal flag (`touchedDotDot`). -/
def resolveOpenTargetWalk (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal exclCreate : Bool) (resolve : ResolveFlags := {}) (hasCreat : Bool := false) :
    Except Errno OpenTarget × Bool :=
  if hasEmbeddedNul path then (.error Errno.EINVAL, false)
  else
    match checkDirHandleOpen s dir with
    | .error e => (.error e, false)
    | .ok () =>
      match validatePathBytes path with
      | .error e => (.error e, false)
      | .ok (isAbs, segs, trailing) =>
        if path.size == 0 then (.error Errno.ENOENT, false)
        else if isAbs && resolve.beneath then (.error Errno.EXDEV, false)
        else
          let startRes :=
            if isAbs && !resolve.beneath && !resolve.inRoot then .ok s.rootIno
            else resolveStartDir s dir
          match startRes with
          | .error e => (.error e, false)
          | .ok startIno =>
            let baseIno := if isAbs then (if resolve.inRoot then startIno else s.rootIno) else startIno
            let anchorMount := inodeMountId s baseIno
            let initDentry? := resolveStartDirDentry s dir isAbs resolve
            walkPath s startIno anchorMount resolve (.openTarget followFinal exclCreate hasCreat)
              (isAbs || resolve.inRoot) false initDentry? (segs.length + (MAX_SYMLINKS + 1) * PATH_MAX + 32)
              MAX_SYMLINKS baseIno 0 segs trailing

/-- Resolve an `openat` / `openat2` path into either an existing inode or a missing leaf in its parent directory. -/
def resolveOpenTarget (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal exclCreate : Bool) (resolve : ResolveFlags := {}) (hasCreat : Bool := false) : Except Errno OpenTarget :=
  (resolveOpenTargetWalk s dir path followFinal exclCreate resolve hasCreat).1

/-- Resolve a path relative to `dir` into its target node or `none` if traversal hits an external opaque descriptor. -/
def resolveLookupOrExt (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal : Bool) (resolve : ResolveFlags := {}) :
    Except Errno (Option (InodeId × Option (InodeId × ByteArray) × Option (HandleId × OpenDesc))) := do
  if hasEmbeddedNul path then .error Errno.EINVAL
  else
    checkDirHandleOpen s dir
    let (isAbs, segs, trailing) ← validatePathBytes path
    if path.size == 0 then .error Errno.ENOENT
    else if isAbs && resolve.beneath then .error Errno.EXDEV
    else
      let startIno ←
        if isAbs && !resolve.beneath && !resolve.inRoot then .ok s.rootIno
        else resolveStartDir s dir
      let baseIno := if isAbs then (if resolve.inRoot then startIno else s.rootIno) else startIno
      let anchorMount := inodeMountId s baseIno
      let initDentry? := resolveStartDirDentry s dir isAbs resolve
      let res ← (walkPath s startIno anchorMount resolve (.lookup followFinal) (isAbs || resolve.inRoot) false
        initDentry? (segs.length + (MAX_SYMLINKS + 1) * PATH_MAX + 32) MAX_SYMLINKS baseIno 0 segs trailing).1
      match res with
      | .existing ino _ _ pIno? lf? _ procHid? =>
        let dentry? := match pIno?, lf? with
          | some p, some l => some (p, l)
          | _, _ => none
        let procDesc? := procHid?.bind fun hid => (assocGet s.fds hid).map fun d => (hid, d)
        .ok (some (ino, dentry?, procDesc?))
      | .externalOpaque _ => .ok none
      | .missingInParent _ _ _ => .error Errno.ENOENT

/-- Resolve a path relative to `dir` into its target `InodeId` and resolved `(parentIno, leaf)` dentry. -/
def resolvePathWithDentry (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal : Bool) (resolve : ResolveFlags := {}) :
    Except Errno (InodeId × Option (InodeId × ByteArray)) := do
  match ← resolveLookupOrExt s dir path followFinal resolve with
  | some (ino, dentry?, _) => .ok (ino, dentry?)
  | none => .error Errno.ENOTDIR

private def resolvePathWithDentryAndProc (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal : Bool) (resolve : ResolveFlags := {}) :
    Except Errno (InodeId × Option (InodeId × ByteArray) × Option (HandleId × OpenDesc)) := do
  match ← resolveLookupOrExt s dir path followFinal resolve with
  | some res => .ok res
  | none => .error Errno.ENOTDIR

/-- Resolve a path relative to `dir` into its target `InodeId`. -/
def resolvePath (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (followFinal : Bool) (resolve : ResolveFlags := {}) : Except Errno InodeId := do
  let (ino, _) ← resolvePathWithDentry s dir path followFinal resolve
  .ok ino

private def resolveParentOrExt (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (resolve : ResolveFlags := {}) (checkLeafNameMax : Bool := true) (checkDeadParent : Bool := true) :
    Except Errno (Option (InodeId × ByteArray × Bool)) := do
  if hasEmbeddedNul path then .error Errno.EINVAL
  else
    checkDirHandleOpen s dir
    let (isAbs, segs, trailing) ← validatePathBytes path
    if path.size == 0 then .error Errno.ENOENT
    else if isAbs && resolve.beneath then .error Errno.EXDEV
    else
      let startIno ←
        if isAbs && !resolve.beneath && !resolve.inRoot then .ok s.rootIno
        else resolveStartDir s dir
      let baseIno := if isAbs then (if resolve.inRoot then startIno else s.rootIno) else startIno
      let anchorMount := inodeMountId s baseIno
      match segs.reverse with
      | [] => .ok (some (baseIno, slashBytes, true))
      | leaf :: revParent =>
        let parentSegs := revParent.reverse
        let res ← (walkPath s startIno anchorMount resolve .parent (isAbs || resolve.inRoot) false none
          (parentSegs.length + (MAX_SYMLINKS + 1) * PATH_MAX + 32) MAX_SYMLINKS baseIno 0 parentSegs false).1
        match res with
        | .missingInParent _ _ _ => .error Errno.ENOENT
        | .externalOpaque _ => .ok none
        | .existing parentIno _ _ _ _ _ _ =>
          match assocGet s.inodes parentIno with
          | none => .error Errno.ENOENT
          | some pvn =>
            match pvn.data with
            | .dir dd =>
              if !hasVNodePermIn s pvn false false true then .error Errno.EACCES
              else if checkDeadParent && !(bytesEq leaf dotBytes || bytesEq leaf dotDotBytes) &&
                  (pvn.nlink == 0 || dd.lifecycle.isDead) then .error Errno.ENOENT
              else if checkLeafNameMax && leaf.size > NAME_MAX then .error Errno.ENAMETOOLONG
              else .ok (some (parentIno, leaf, trailing))
            | _ =>
              if pvn.isDynamic && pvn.kind == .other then .ok none
              else .error Errno.ENOTDIR

/-- Resolve the parent directory `InodeId` and final entry name of `path`. -/
def resolveParentAndLeaf (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (resolve : ResolveFlags := {}) (checkLeafNameMax : Bool := true) (checkDeadParent : Bool := true) :
    Except Errno (InodeId × ByteArray × Bool) := do
  match ← resolveParentOrExt s dir path resolve checkLeafNameMax checkDeadParent with
  | some res => .ok res
  | none => .error Errno.ENOTDIR

/-- Return `true` iff `e` can be returned by Linux `ksys_close` / `filp_close`. -/
def isKernelCloseErr (e : Errno) : Bool :=
  e == Errno.EBADF || e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOSPC ||
  e.toNat == 122 || e == Errno.ENOMEM || e == Errno.ESTALE || e.toNat == 104

private def clearUncertain (s : FilesState) (hid : HandleId) : FilesState :=
  match assocGet s.fds hid with
  | none => s
  | some d =>
    if d.closeState == .closeUncertain then { s with fds := assocSet s.fds hid { d with closeState := .open } }
    else s

private def sameFlockTarget (s : FilesState) (selfDesc odesc : OpenDesc) : Bool :=
  (selfDesc.ofdId?.isNone || odesc.ofdId? != selfDesc.ofdId?) &&
  odesc.ino == selfDesc.ino &&
  let mayCopy := (assocGet s.inodes selfDesc.ino).map (·.mayCopyUp) |>.getD false
  (!mayCopy || (odesc.dentry? == selfDesc.dentry? && odesc.lastDentry? == selfDesc.lastDentry?))

private def hasCertainConflictingFlock (s : FilesState) (selfHid : HandleId) (selfDesc : OpenDesc)
    (exclusive : Bool) : Bool :=
  s.fds.any fun (hid, desc) =>
    hid != selfHid && sameFlockTarget s selfDesc desc && desc.closeState == .open &&
    match desc.lock? with
    | none => false
    | some .exclusive => true
    | some .shared => exclusive

private def uncertainConflictingFlocks (s : FilesState) (selfHid : HandleId) (selfDesc : OpenDesc)
    (exclusive : Bool) : List (HandleId × OpenDesc) :=
  s.fds.filter fun (hid, desc) =>
    hid != selfHid && sameFlockTarget s selfDesc desc && desc.closeState == .closeUncertain &&
    match desc.lock? with
    | none => false
    | some .exclusive => true
    | some .shared => exclusive

/-- Compute `(minReaders, maxReaders, minWriters, maxWriters)` accounting for uncertain-close FIFO handles. -/
def fifoCounts (s : FilesState) (ino : InodeId) (ring : PipeRing) : Nat × Nat × Nat × Nat :=
  let maybeR := s.fds.foldl (fun n (_, d) =>
    if !d.isPathFd && d.ino == ino && d.closeState == .closeUncertain && (d.access == .rdonly || d.access == .rdwr) then n + 1 else n) 0
  let maybeW := s.fds.foldl (fun n (_, d) =>
    if !d.isPathFd && d.ino == ino && d.closeState == .closeUncertain && (d.access == .wronly || d.access == .rdwr) then n + 1 else n) 0
  (ring.readers - maybeR, ring.readers, ring.writers - maybeW, ring.writers)

/-- Return `true` iff outcome `out` is `.err err`. -/
def isOutcomeErr (out : FilesOutcome) (err : Errno) : Bool :=
  match out with
  | .err e => e == err
  | _ => false

private def pipeConsumeSlots : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | slots, 0 => slots
  | (tail, len) :: rest, k =>
    if k < len then (tail, len - k) :: rest
    else pipeConsumeSlots rest (k - len)

/-- Reverse-accumulator helper for `pipePushSlots` avoiding quadratic list append. -/
def pipePushSlotsRev : List (Nat × Nat) → Nat → Nat → Nat → List (Nat × Nat) × Nat
  | revSlots, 0, _, written => (revSlots.reverse, written)
  | revSlots, _, 0, written => (revSlots.reverse, written)
  | revSlots, n + 1, rem, written =>
    let chunk := min rem 4096
    pipePushSlotsRev ((chunk, chunk) :: revSlots) n (rem - chunk) (written + chunk)

/-- Push up to `n` new 4 KiB pipe ring slots onto `slots` while `rem > 0`. -/
def pipePushSlots (slots : List (Nat × Nat)) (n rem written : Nat) : List (Nat × Nat) × Nat :=
  pipePushSlotsRev slots.reverse n rem written

/-- Simulate pipe ring-buffer slot allocation up to `capPages` (`PIPE_BUF` / page capacity). -/
def pipeWriteSlots (slots : List (Nat × Nat)) (capPages totalLen : Nat) :
    List (Nat × Nat) × Nat :=
  if totalLen == 0 then (slots, 0)
  else
    let maxSlots := max 1 capPages
    let chars := totalLen % 4096
    let (slots0, written0, rem0) :=
      if chars > 0 then
        match slots.reverse with
        | (tTail, tLen) :: revInit =>
          if tTail + chars <= 4096 then
            (revInit.reverse ++ [(tTail + chars, tLen + chars)], chars, totalLen - chars)
          else (slots, 0, totalLen)
        | [] => (slots, 0, totalLen)
      else (slots, 0, totalLen)
    pipePushSlots slots0 (maxSlots - slots0.length) rem0 written0

private def updateSharedDesc (fds : List (HandleId × OpenDesc)) (hid : HandleId)
    (f : OpenDesc → OpenDesc) : List (HandleId × OpenDesc) :=
  match assocGet fds hid with
  | none => fds
  | some target =>
    match target.ofdId? with
    | none => assocSet fds hid (f target)
    | some oid => fds.map fun (h, d) => if d.ofdId? == some oid then (h, f d) else (h, d)

private def sortStdioSlots (slots : List StdioFd) : List StdioFd :=
  ([.stdin, .stdout, .stderr] : List StdioFd).filter fun s => slots.contains s

/-- Bind the lowest free stdio slot (`0`/`1`/`2`), if any, to newly created `newHid`. -/
def bindFreeStdioSlot (s : FilesState) (newHid : HandleId) (desc : OpenDesc) : FilesState × OpenDesc :=
  match sortStdioSlots s.freeStdioSlots with
  | [] => (s, desc)
  | slot :: rest =>
    let oid := s.nextOfdId
    let desc' := { desc with ofdId? := some oid }
    let s' := { s with
      freeStdioSlots := rest
      managedStdioMap := assocSet s.managedStdioMap slot newHid
      nextOfdId := oid + 1 }
    (s', desc')

private def isInodeProcMagicTarget (inodes : List (InodeId × VNode)) (fds : List (HandleId × OpenDesc))
    (ino : InodeId) : Bool :=
  fds.any fun (_, d) =>
    match assocGet inodes d.ino with
    | some sv =>
      match sv.data with
      | .symlink (.procMagic tgt _) => tgt == ino
      | _ => false
    | none => false

private def pruneIfDeadInode (inodes : List (InodeId × VNode)) (fds : List (HandleId × OpenDesc))
    (cwdIno rootIno ino : InodeId) : List (InodeId × VNode) :=
  if ino == cwdIno || ino == rootIno then inodes
  else if fds.any (·.2.ino == ino) then inodes
  else if isInodeProcMagicTarget inodes fds ino then inodes
  else
    match assocGet inodes ino with
    | none => inodes
    | some vn =>
      let isDeadUnlinked :=
        match vn.data with
        | .dir dd => dd.lifecycle == .unlinked && vn.nlink == 0
        | _ => vn.nlink == 0 && !vn.mayCopyUp
      let isDeadExtStdio := vn.origin == .hostDynamic && vn.kind == .other
      if isDeadUnlinked || isDeadExtStdio then assocErase inodes ino
      else inodes

/-- Close descriptor `hid` (`desc`) in `s`, decrementing FIFO reader/writer counts and erasing `hid` from `s.fds`. -/
def closeDescInState (s : FilesState) (hid : HandleId) (desc : OpenDesc) : FilesState :=
  let fds' := assocErase s.fds hid
  let sharedStillOpen :=
    match desc.ofdId? with
    | some oid => fds'.any (·.2.ofdId? == some oid)
    | none => false
  let closeInodes :=
    if desc.isPathFd || sharedStillOpen then s.inodes
    else
    match assocGet s.inodes desc.ino with
    | some vn =>
      match vn.data with
      | .fifo ring =>
        let r' := if desc.access == .rdonly || desc.access == .rdwr then ring.readers - 1 else ring.readers
        let w' := if desc.access == .wronly || desc.access == .rdwr then ring.writers - 1 else ring.writers
        let clearBuf := r' == 0 && w' == 0
        let ring' :=
          { ring with
            readers := r'
            writers := w'
            buf := if clearBuf then ByteArray.mk #[] else ring.buf
            slots := if clearBuf then [] else ring.slots
            capacity := if clearBuf then .uncalibrated 2 16 else ring.capacity }
        assocSet s.inodes desc.ino { vn with data := .fifo ring' }
      | _ => s.inodes
    | none => s.inodes
  let prunedInodes := pruneIfDeadInode closeInodes fds' s.cwdIno s.rootIno desc.ino
  let (freeSlots', managedMap') :=
    match s.managedStdioMap.find? (·.2 == hid) with
    | some (slot, _) => (sortStdioSlots (slot :: s.freeStdioSlots), assocErase s.managedStdioMap slot)
    | none => (s.freeStdioSlots, s.managedStdioMap)
  let procClosedAfter' :=
    if prunedInodes.any (fun (_, vn) =>
        match vn.data with
        | .symlink (.procMagic _ (some h)) => h == hid
        | _ => false) then
      assocSet s.procClosedAfter hid s.nextHid
    else s.procClosedAfter
  { s with
    inodes := prunedInodes
    fds := fds'
    freeStdioSlots := freeSlots'
    managedStdioMap := managedMap'
    procClosedAfter := procClosedAfter' }

/-- Resolve uncertain-close FIFO descriptors as closed or still-open upon observing pipe I/O. -/
def resolveUncertainFifo (s : FilesState) (ino : InodeId) (wantReaders closeThem : Bool) : FilesState :=
  let matchesRole := fun (d : OpenDesc) =>
    !d.isPathFd && d.ino == ino && d.closeState == .closeUncertain &&
    if wantReaders then (d.access == .rdonly || d.access == .rdwr)
    else (d.access == .wronly || d.access == .rdwr)
  let targets := s.fds.filter fun (_, d) => matchesRole d
  if closeThem then
    targets.foldl (fun st (ohid, odesc) => closeDescInState st ohid odesc) s
  else
    match targets with
    | [(ohid, _)] => clearUncertain s ohid
    | _ => s

/-- Check if another open file description on `ino` holds a conflicting `flock` lock. -/
def hasConflictingFlock (s : FilesState) (selfHid : HandleId) (ino : InodeId) (exclusive : Bool) : Bool :=
  s.fds.any fun (hid, desc) =>
    hid != selfHid && desc.ino == ino &&
    match desc.lock? with
    | none => false
    | some .exclusive => true
    | some .shared => exclusive

/-- Encode `OpenDesc` status flags into portable bit positions (`0..1` access, bit `5` append, bit `8` nonblock). -/
def encodeOpenStatusFlags (desc : OpenDesc) : UInt32 :=
  let accBits : UInt32 := match desc.access with
    | .rdonly => 0
    | .wronly => 1
    | .rdwr => 2
  accBits ||| (if desc.append then 32 else 0) ||| (if desc.nonblock then 256 else 0)

/-- Strip setuid (`0o4000`) and setgid (`0o2000` when group-exec `0o0010` set or `dropAllSgid`) privilege bits on write/truncate. -/
def stripPrivBitsExt (dropAllSgid : Bool) (mode : Mode) : Mode :=
  let m1 := mode &&& ~~~(0o4000 : Mode)
  if dropAllSgid || (m1 &&& 0o2010) == 0o2010 then m1 &&& ~~~(0o2000 : Mode) else m1

/-- Strip setuid (`0o4000`) and setgid (`0o2000` when group-exec `0o0010` set) privilege bits on write/truncate. -/
def stripPrivBits (mode : Mode) : Mode :=
  stripPrivBitsExt false mode

/-- Synthesize a deterministic `StatInfo` from logical inode `(ino, vn)`. -/
def mkStatFromVNode (ino : InodeId) (vn : VNode) : StatInfo :=
  { kind := vn.kind
    size :=
      match vn.data with
      | .reg rd => rd.size
      | .symlink (.path b) => b.size
      | _ => 0
    mode := vn.mode
    ino := vn.kernelId.ino?.getD (UInt64.ofNat ino)
    dev := vn.kernelId.dev?.getD (UInt64.ofNat (vn.mountId + 1))
    nlink := vn.nlink
    mtimeSec := 0
    mtimeNsec := 0
    atimeSec := 0
    atimeNsec := 0 }

/-- Verify observed `StatInfo` matches `(vn)` inside `s`. -/
def checkStatMatch (s : FilesState) (vn : VNode) (st : StatInfo) : Bool :=
  let kindOk := (vn.isDynamic && vn.kind == .other) || st.kind == vn.kind
  let sizeOk :=
    if vn.isDynamic then true
    else
      match vn.data with
      | .reg rd => st.size == rd.size
      | .symlink (.path b) => st.size == b.size
      | _ => true
  let nlinkOk :=
    if vn.isDynamic then true
    else if vn.overlayMergedDir then st.nlink == 1
    else st.nlink == vn.nlink
  let modeOk :=
    if !mountPosixModes s vn.mountId || (vn.isDynamic && !vn.modeExact) then true
    else if vn.modeExact then (st.mode &&& 0o7777) == (vn.mode &&& 0o7777)
    else
      (st.mode &&& 0o0777) == (vn.mode &&& 0o0777) &&
      (vn.kind != .dir || (st.mode &&& 0o2000) == (vn.mode &&& 0o2000))
  let inoOk := if vn.mayCopyUp then true else match vn.kernelId.ino? with
    | none => true
    | some prevIno => st.ino == prevIno
  let devOk := if vn.mayCopyUp then true else match vn.kernelId.dev? with
    | none => true
    | some prevDev => st.dev == prevDev
  let nsecOk := st.mtimeNsec < 1000000000 && st.atimeNsec < 1000000000
  kindOk && sizeOk && nlinkOk && modeOk && inoOk && devOk && nsecOk

/-- Verify `StatInfo` matches `(ino, vn)` and has `(st_dev, st_ino)` distinct from other live or open inodes unless aliasing is allowed. -/
def checkStatMatchInState (s : FilesState) (ino : InodeId) (vn : VNode) (st : StatInfo) : Bool :=
  checkStatMatch s vn st &&
  (vn.mayCopyUp || vn.kernelId.allowAlias || !s.inodes.any fun (otherIno, otherVn) =>
    otherIno != ino &&
    !otherVn.kernelId.allowAlias &&
    (otherVn.nlink > 0 || s.fds.any (fun (_, d) => d.ino == otherIno)) &&
    otherVn.kernelId.dev? == some st.dev &&
    otherVn.kernelId.ino? == some st.ino)

private def promoteOverlayAncestors (inodes : List (InodeId × VNode)) (childIno : InodeId)
    (fuel : Nat := 16) : List (InodeId × VNode) :=
  match fuel with
  | 0 => inodes
  | fuel' + 1 =>
    match inodes.find? (fun (_, pvn) =>
        match pvn.data with
        | .dir dd => dd.children.any (fun (_, c) => c == childIno)
        | _ => false) with
    | none => inodes
    | some (pIno, pvn) =>
      if pvn.mayCopyUp then
        let data' := match pvn.data with
          | .dir dd => .dir { dd with lifecycle := .overlayMerged }
          | d => d
        let pvn' := { pvn with data := data', nlink := 1, origin := .managed false }
        promoteOverlayAncestors (assocSet inodes pIno pvn') pIno fuel'
      else inodes

private def dentryRefCount (inodes : List (InodeId × VNode)) (targetIno : InodeId) : Nat :=
  inodes.foldl (fun acc (_, pvn) =>
    match pvn.data with
    | .dir dd => dd.children.foldl (fun n (_, c) => if c == targetIno then n + 1 else n) acc
    | _ => acc) 0

private def isStickyCreateBlocked (s : FilesState) (parentIno? : Option InodeId)
    (flags : OpenFlags) (exclCreate : Bool) (vn : VNode) : Bool :=
  let (enabled, writeMask) : Bool × Mode :=
    match vn.data with
    | .reg _ => (s.sysctls.protectedRegular != 0, if s.sysctls.protectedRegular >= 2 then 0o022 else 0o002)
    | .fifo _ => (s.sysctls.protectedFifos != 0, if s.sysctls.protectedFifos >= 2 then 0o022 else 0o002)
    | .dir _ | .symlink _ => (false, 0)
    | .socket | .charDev _ | .blockDev | .other =>
      (true, 0o002)
  enabled &&
  flags.creat && !exclCreate &&
  !vn.owner.ownedByUid &&
  match parentIno? with
  | some pIno =>
    match assocGet s.inodes pIno with
    | some pvn =>
      (pvn.mode &&& 0o1000) != 0 && (pvn.mode &&& writeMask) != 0 &&
      !sameKnownOwner vn pvn
    | none => false
  | none => false

private def isStickySymlinkBlocked (s : FilesState) (parentIno? : Option InodeId) (vn : VNode) : Bool :=
  !vn.owner.ownedByUid &&
  match parentIno? with
  | some pIno =>
    match assocGet s.inodes pIno with
    | some pvn => (pvn.mode &&& 0o1002) == 0o1002 && !sameKnownOwner vn pvn
    | none => false
  | none => false

private def isStickyDeleteBlocked (s : FilesState) (pvn vn : VNode) : Bool :=
  !s.cred.capableWrtInode vn.owner (·.capFowner) &&
  (pvn.mode &&& 0o1000) != 0 && !pvn.owner.ownedByUid && !vn.owner.ownedByUid

private def copyUpUpdatedNode (vn' : VNode) : VNode :=
  let data' := match vn'.data with
    | .dir dd =>
      let lc' := if dd.lifecycle.isDead then DirLifecycle.overlayDeadMerged else DirLifecycle.overlayMerged
      .dir { dd with lifecycle := lc' }
    | d => d
  { vn' with
    data := data'
    nlink := if vn'.nlink > 1 || vn'.kind == .dir then 1 else vn'.nlink
    kernelId := { dev? := none, ino? := none, allowAlias := vn'.kernelId.allowAlias }
    origin := .managed false }

/-- Materialize an overlayfs copy-up update on `ino`, forking a fresh upper inode if shared across dentries. -/
def copyUpInode (s : FilesState) (ino : InodeId)
    (parentLeaf? : Option (InodeId × ByteArray)) (vn' : VNode) : FilesState × InodeId :=
  if !vn'.mayCopyUp then
    ({ s with inodes := assocSet s.inodes ino vn' }, ino)
  else
    let updated := copyUpUpdatedNode vn'
    let hasOtherFd := match parentLeaf? with
      | some pl => s.fds.any (fun (_, d) => d.ino == ino && d.dentry? != some pl)
      | none => false
    let shared := dentryRefCount s.inodes ino > 1 || hasOtherFd
    if shared then
      match parentLeaf? with
      | some (pIno, leaf) =>
        let newIno := s.nextIno
        let inodes1 := assocSet s.inodes newIno { updated with nlink := 1 }
        let inodes2 := match assocGet inodes1 pIno with
          | some pvn =>
            match pvn.data with
            | .dir dd =>
              let pvn' := { pvn with data := .dir { dd with children := bytesAssocSet dd.children leaf newIno } }
              assocSet inodes1 pIno pvn'
            | _ => inodes1
          | none => inodes1
        let fds' := rebindDentryFds s.fds ino (pIno, leaf) newIno
        ({ s with inodes := promoteOverlayAncestors inodes2 newIno, fds := fds', nextIno := s.nextIno + 1 }, newIno)
      | none =>
        let inodes1 := assocSet s.inodes ino updated
        ({ s with inodes := promoteOverlayAncestors inodes1 ino }, ino)
    else
      let inodes1 := assocSet s.inodes ino updated
      ({ s with inodes := promoteOverlayAncestors inodes1 ino }, ino)

private def applyCopyUpOnRename (inodes : List (InodeId × VNode)) (fds : List (HandleId × OpenDesc))
    (nextIno : InodeId) (newP : InodeId) (newLeaf : ByteArray) (ino : InodeId) (vn : VNode) :
    List (InodeId × VNode) × List (HandleId × OpenDesc) × InodeId :=
  if vn.mayCopyUp && vn.kind != .dir then
    let updated := copyUpUpdatedNode vn
    let hasOtherFd := fds.any (fun (_, d) => d.ino == ino && d.dentry? != some (newP, newLeaf))
    if dentryRefCount inodes ino > 1 || hasOtherFd then
      let forkedIno := nextIno
      let inodes1 := assocSet inodes forkedIno { updated with nlink := 1 }
      let inodes2 := match assocGet inodes1 newP with
        | some pvn =>
          match pvn.data with
          | .dir dd =>
            assocSet inodes1 newP { pvn with data := .dir { dd with children := bytesAssocSet dd.children newLeaf forkedIno } }
          | _ => inodes1
        | none => inodes1
      (promoteOverlayAncestors inodes2 forkedIno, rebindDentryFds fds ino (newP, newLeaf) forkedIno, nextIno + 1)
    else
      (promoteOverlayAncestors (assocSet inodes ino updated) ino, fds, nextIno)
  else (inodes, fds, nextIno)

private def markParentOverlay (pvn : VNode) (children' : List (ByteArray × InodeId)) (nlinkDelta : Int) : VNode :=
  let pOverlay := pvn.overlayMergedDir || pvn.mayCopyUp
  let dd' := match pvn.data with
    | .dir dd => { dd with children := children', lifecycle := if pOverlay then .overlayMerged else dd.lifecycle }
    | _ => { children := children' }
  let nl' :=
    if pOverlay then 1
    else if nlinkDelta < 0 then pvn.nlink - 1
    else if nlinkDelta > 0 then pvn.nlink + 1
    else pvn.nlink
  { pvn with
    data := .dir dd'
    nlink := nl'
    origin := if pvn.mayCopyUp then .managed false else pvn.origin }

/-- Map `FileKind` to the Linux `linux_dirent64.d_type` code (`DT_*`). -/
def fileKindToDType : FileKind → UInt8
  | .fifo => 1
  | .charDev => 2
  | .dir => 4
  | .blockDev => 6
  | .reg => 8
  | .symlink => 10
  | .socket => 12
  | .other => 0

/-- Aligned `linux_dirent64` record length in bytes for entry name `name`. -/
def dirent64Reclen (name : ByteArray) : Nat :=
  ((19 + name.size + 1 + 7) / 8) * 8

/-- Scan `[pos, stop)` for the NUL terminator of `d_name`, rejecting `'/'` bytes or missing NUL. -/
def findNulInSliceAux (bs : ByteArray) (pos stop fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if pos >= stop then none
    else
      let b := byteGetD bs pos
      if b == 0 then some pos
      else if b == slashByte then none
      else findNulInSliceAux bs (pos + 1) stop fuel'

/-- Decode and strictly validate a single `linux_dirent64` record starting at `pos`, returning `(d_name, d_type, nextPos)`. -/
def parseDirent64One (bs : ByteArray) (pos : Nat) : Option (ByteArray × UInt8 × Nat) :=
  if pos + 20 > bs.size then none
  else
    let lo := (byteGetD bs (pos + 16)).toNat
    let hi := (byteGetD bs (pos + 17)).toNat
    let reclen := lo + hi * 256
    let dType := byteGetD bs (pos + 18)
    if reclen < 24 || reclen % 8 != 0 || pos + reclen > bs.size then none
    else
      match findNulInSliceAux bs (pos + 19) (pos + reclen) (reclen - 18) with
      | none => none
      | some nulPos =>
        if nulPos == pos + 19 then none
        else some (sliceBytes bs (pos + 19) (nulPos - (pos + 19)), dType, pos + reclen)

/-- Strictly validate `linux_dirent64` framing, NUL-terminated `d_name`s, and return `(d_name, d_type)` pairs. -/
def parseDirents64StrictAux (bs : ByteArray) (pos fuel : Nat) (acc : List (ByteArray × UInt8)) :
    Option (List (ByteArray × UInt8)) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if pos == bs.size then some acc.reverse
    else
      match parseDirent64One bs pos with
      | none => none
      | some (nm, dType, nextPos) =>
        parseDirents64StrictAux bs nextPos fuel' ((nm, dType) :: acc)

/-- Validate raw `getdents64` buffer framing and decode `(d_name, d_type)` pairs (`none` if malformed). -/
def parseDirents64Strict (bs : ByteArray) : Option (List (ByteArray × UInt8)) :=
  parseDirents64StrictAux bs 0 (bs.size + 1) []

/-- Validate raw `getdents64` buffer framing and return record count (`none` if malformed). -/
def countDirents64Strict (bs : ByteArray) : Option Nat :=
  (parseDirents64Strict bs).map List.length

/-- Compute byte `i` of a `linux_dirent64` record for `(nm, dType, lo, hi, dIno, dOff)`. -/
@[inline] def direntEntryByteAt (nm : ByteArray) (dType lo hi : UInt8) (dIno dOff : UInt64)
    (i : Nat) : UInt8 :=
  if i < 8 then UInt8.ofNat ((dIno.toNat >>> (i * 8)) % 256)
  else if i < 16 then UInt8.ofNat ((dOff.toNat >>> ((i - 8) * 8)) % 256)
  else if i == 16 then lo
  else if i == 17 then hi
  else if i == 18 then dType
  else if 19 <= i && i < 19 + nm.size then byteGetD nm (i - 19)
  else 0

/-- Tail-recursive helper pushing `rem` encoded `linux_dirent64` bytes starting at `i` onto `acc`. -/
def mkDirentEntryLoop (nm : ByteArray) (dType lo hi : UInt8) (dIno dOff : UInt64)
    (i : Nat) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | rem + 1, acc =>
    mkDirentEntryLoop nm dType lo hi dIno dOff (i + 1) rem
      (acc.push (direntEntryByteAt nm dType lo hi dIno dOff i))

/-- Construct a single `linux_dirent64` record stub of size `dirent64Reclen nm` with `d_type`, `d_ino`, `d_off`, and NUL-terminated `d_name`. -/
def mkDirentEntry (nm : ByteArray) (dType : UInt8 := 0) (dIno : UInt64 := 1) (dOff : UInt64 := 1) : ByteArray :=
  let rl := dirent64Reclen nm
  let lo : UInt8 := UInt8.ofNat (rl % 256)
  let hi : UInt8 := UInt8.ofNat ((rl / 256) % 256)
  mkDirentEntryLoop nm dType lo hi dIno dOff 0 rl (ByteArray.emptyWithCapacity rl)

/-- Tail-recursive unboxed `ByteArray` index loop checking whether `target` occurs in `rem` bytes from `i`. -/
def hasByteLoop (b : ByteArray) (target : UInt8) (i : Nat) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    if h : i < b.size then
      if b[i] == target then true
      else hasByteLoop b target (i + 1) rem
    else false

/-- Construct a validated `linux_dirent64` record stub, returning `none` if `nm` is empty, contains NUL/`'/'`, or overflows `uint16` `d_reclen`. -/
def mkDirentEntryChecked? (nm : ByteArray) (dType : UInt8 := 0) (dIno : UInt64 := 1) (dOff : UInt64 := 1) : Option ByteArray :=
  if nm.size == 0 || dirent64Reclen nm >= 65536 ||
      hasEmbeddedNul nm || hasByteLoop nm slashByte 0 nm.size then none
  else some (mkDirentEntry nm dType dIno dOff)

/-- Compute total byte length of encoded `linux_dirent64` records for `entries`. -/
def direntStubTotalBytes (entries : List (ByteArray × UInt8 × UInt64)) : Nat :=
  entries.foldl (fun sz e => sz + dirent64Reclen e.1) 0

/-- Tail-recursive accumulator pushing `(name, d_type, d_ino)` `linux_dirent64` records directly into an unboxed `ByteArray`. -/
def mkTypedDirentStubAux (acc : ByteArray) : List (ByteArray × UInt8 × UInt64) → ByteArray
  | [] => acc
  | (nm, dt, ino) :: rest =>
    let rl := dirent64Reclen nm
    let lo : UInt8 := UInt8.ofNat (rl % 256)
    let hi : UInt8 := UInt8.ofNat ((rl / 256) % 256)
    mkTypedDirentStubAux (mkDirentEntryLoop nm dt lo hi ino 1 0 rl acc) rest

/-- Construct a framed `linux_dirent64` byte buffer encoding `(name, d_type, d_ino)` entries. -/
def mkTypedDirentStub (entries : List (ByteArray × UInt8 × UInt64)) : ByteArray :=
  mkTypedDirentStubAux (ByteArray.emptyWithCapacity (direntStubTotalBytes entries)) entries

/-- Construct a framed `linux_dirent64` byte buffer matching the record lengths and names of `names`. -/
def mkDirentStub (names : List ByteArray) : ByteArray :=
  mkTypedDirentStub (names.map fun nm => (nm, 0, 1))

/-- Greedily pack the maximal prefix of `entries` whose aligned `linux_dirent64` records fit in `cap`. -/
def packFittingDirentsGen {α : Type} (nameOf : α → ByteArray) (entries : List α) (cap : Nat) : List α :=
  let rec go (xs : List α) (used : Nat) (acc : List α) : List α :=
    match xs with
    | [] => acc.reverse
    | ent :: rest =>
      let rl := dirent64Reclen (nameOf ent)
      if used + rl <= cap then go rest (used + rl) (ent :: acc)
      else acc.reverse
  go entries 0 []

/-- Greedily pack the maximal prefix of `entries` whose aligned `linux_dirent64` records fit in `cap`. -/
def packFittingDirents (entries : List ByteArray) (cap : Nat) : List ByteArray :=
  packFittingDirentsGen id entries cap

/-- Bounded kernel nondeterminism payloads for syscalls whose Linux outcome is non-unique. -/
inductive NondetAction where
  /-- FIFO non-blocking write open with uncertain close-state readers. -/
  | openFifoUncertain (sOpen : FilesState) (hid : HandleId) (sClose : FilesState)
  /-- Regular-file read (`rd` up to `cap`). -/
  | readReg (hid : HandleId) (desc : OpenDesc) (rd : RegData) (cap : Nat)
  /-- Zero/full device read returning `1..cap` NUL bytes. -/
  | readZeroDev (cap : Nat)
  /-- Host-dynamic or generic charDev read. -/
  | readDynamic (hid : HandleId) (desc : OpenDesc) (cap : Nat) (nonblock isCharDev : Bool)
  /-- Named FIFO read (`pipeBuf`, `pipeSlots`, `cap`, `nonblock`, `isDynamic`). -/
  | readFifo (ino : InodeId) (ring : PipeRing) (cap : Nat) (nonblock isDynamic : Bool)
  /-- Regular-file write (`data`, `stripPriv`, `isOverlay`, `roMount`, `copyUp`). -/
  | writeReg (hid : HandleId) (desc : OpenDesc) (ino : InodeId) (data : ByteArray)
      (stripPriv isOverlay roMount copyUp : Bool)
  /-- Discarding write (`null`, `zero`, `pseudo`, generic charDev) allowing `1..len` or `extraErrs`. -/
  | writeDiscard (len : Nat) (extraErrs : List Errno) (nonblockEagain : Bool)
  /-- Named FIFO write with exact/uncalibrated pipe page capacity. -/
  | writeFifo (ino : InodeId) (ring : PipeRing) (data : ByteArray) (nonblock isDynamic : Bool)
  /-- `fstat` / `fstatat` metadata observation binding `(st_dev, st_ino)`. -/
  | statNode (ino : InodeId) (vn : VNode)
  /-- Dynamic `readlinkat` returning `0..cap` bytes. -/
  | readlinkDynamic (cap : Nat)
  /-- Directory `getdents64` batch read. -/
  | getdents (hid : HandleId) (desc : OpenDesc) (vn : VNode) (bufBytes : UInt32)
  /-- `flock` resolution when conflicting locks belong to uncertain-close descriptors. -/
  | flockUncertain (sWin sLose : FilesState) (nonblock : Bool)
  /-- First `getcwd` call binding `CwdPath.unbound` to the observed host CWD. -/
  | getcwdUnbound (cap : UInt32) (fallback : ByteArray)
  /-- Non-zero `lseek` on a directory returning an opaque kernel cookie (`pos := .dirStream _ false`). -/
  | lseekDir (hid : HandleId) (desc : OpenDesc)
  /-- `lseek` on a dynamic or external stdio descriptor returning an arbitrary valid offset `< 2^63`. -/
  | lseekDynamic (hid : HandleId) (desc : OpenDesc)
  /-- `dupStdio` duplicating host stdio slot `0`/`1`/`2` into a fresh `hostDynamic` descriptor. -/
  | dupStdio (slot : StdioFd)
  /-- `reopenReadOnly` on an external `dupStdio` descriptor. -/
  | reopenExternalStdio (desc : OpenDesc)
  /-- `fcntl .getFl` on an external `dupStdio` descriptor whose initial host flags are unknown. -/
  | getFlExternal
  /-- `fcntl .getSeals` on an external `dupStdio` descriptor whose backing file may be a memfd. -/
  | getSealsExternal
  /-- `openat` / `openat2` relative to an `isExternalStdio` `dirfd` (which may back a host directory). -/
  | externalStdioOpen (flags : OpenFlags)
  /-- `fstatat` relative to an `isExternalStdio` `dirfd`. -/
  | externalStdioStat
  /-- Mutating or query `*at` operation relative to an `isExternalStdio` `dirfd`. -/
  | externalStdioUnit
  deriving Repr

/-- Exact first-order transition result of evaluating one `FilesReq` prior to transient/seccomp fallback. -/
inductive StepResult where
  /-- Rejected in the Lean/C wrapper before kernel syscall entry (`isTransientOsErrno` and `ambientSeccomp` disallowed). -/
  | wrapperErr (err : Errno)
  /-- Deterministic kernel error (`alts` holds multi-errno Linux outcomes; `nextState?` for `flock(LOCK_NB)` unlock). -/
  | err (primary : Errno) (alts : List Errno := []) (nextState? : Option FilesState := none)
  /-- Deterministic kernel success (`extraErrs` holds genuine FS-dependent rejections such as `EXDEV` or `EAGAIN`). -/
  | ok (out : FilesOutcome) (next : FilesState) (extraErrs : List Errno := [])
  /-- Bounded nondeterministic kernel outcome verified by `verifyNondet`. -/
  | nondet (action : NondetAction) (extraErrs : List Errno := [])
  deriving Repr

/-- Return `true` iff any path argument in `req` contains an embedded NUL byte (`0x00`). -/
def precheckNul : FilesReq → Bool
  | .openat _ p _ _ | .openat2 _ p _ | .fstatat _ p _ | .faccessat _ p _ _
  | .mkdirat _ p _ | .unlinkat _ p _ | .readlinkat _ p _ | .fchmodat _ p _ =>
    hasEmbeddedNul p
  | .renameat2 _ op _ np _ => hasEmbeddedNul op || hasEmbeddedNul np
  | .symlinkat t _ lp => hasEmbeddedNul t || hasEmbeddedNul lp
  | _ => false

/-- Adjust `StepResult` errors for `openat2` cached/`RESOLVE_BENEATH`/`RESOLVE_IN_ROOT` bailouts. -/
def withOpenat2Eagain (strictOpenat2 : Bool) (resolve : ResolveFlags) (touchedDotDot : Bool) :
    StepResult → StepResult
  | r@(.wrapperErr _) => r
  | .err primary alts st? =>
    let addE := strictOpenat2 && (resolve.cached || ((resolve.beneath || resolve.inRoot) && touchedDotDot))
    let alts' := if addE && !alts.contains Errno.EAGAIN then Errno.EAGAIN :: alts else alts
    .err primary alts' st?
  | .ok out next extra =>
    let addE := strictOpenat2 && (resolve.cached || ((resolve.beneath || resolve.inRoot) && touchedDotDot))
    let extra' := if addE && !extra.contains Errno.EAGAIN then Errno.EAGAIN :: extra else extra
    .ok out next extra'
  | .nondet act extra =>
    let addE := strictOpenat2 && (resolve.cached || ((resolve.beneath || resolve.inRoot) && touchedDotDot))
    let extra' := if addE && !extra.contains Errno.EAGAIN then Errno.EAGAIN :: extra else extra
    .nondet act extra'

/-- Evaluate an `openat` or `openat2` transition into `StepResult`. -/
def evalOpen (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (rawFlags : OpenFlags) (mode : Mode) (resolve : ResolveFlags) (strictOpenat2 : Bool) : StepResult :=
  if strictOpenat2 && rawFlags.path &&
      (rawFlags.access != .rdonly || rawFlags.creat || rawFlags.excl || rawFlags.trunc ||
        rawFlags.append || rawFlags.nonblock || rawFlags.noctty || mode != 0) then
    .err Errno.EINVAL
  else if strictOpenat2 && !rawFlags.creat && mode != 0 then .err Errno.EINVAL
  else if strictOpenat2 && rawFlags.creat && mode > 0o7777 then .err Errno.EINVAL
  else if strictOpenat2 && resolve.beneath && resolve.inRoot then .err Errno.EINVAL
  else
    let flags : OpenFlags :=
      if !strictOpenat2 && rawFlags.path then
        { access := .rdonly, directory := rawFlags.directory, nofollow := rawFlags.nofollow,
          cloexec := rawFlags.cloexec, path := true }
      else rawFlags
    if flags.creat && flags.directory then
      .err Errno.EINVAL [Errno.ENOTDIR, Errno.EISDIR, Errno.ENOENT]
    else if strictOpenat2 && resolve.cached && (flags.creat || flags.trunc) then
      .err Errno.EAGAIN [Errno.EINVAL]
    else
      let exclCreate := flags.creat && flags.excl
      let followFinal := !flags.nofollow && !exclCreate
      let (walkRes, touchedDotDot) :=
        resolveOpenTargetWalk s dir path followFinal exclCreate resolve flags.creat
      let core : StepResult :=
        match walkRes with
        | .error re => .err re
        | .ok (.externalOpaque _) => .nondet (.externalStdioOpen flags)
        | .ok (.existing targetIno trailing isSpecialDotRoot parentIno? leaf? viaProcMagic procMagicHid?) =>
          if isSpecialDotRoot && exclCreate then .err Errno.EEXIST
          else if flags.creat && trailing then .err Errno.EISDIR
          else if exclCreate then .err Errno.EEXIST
          else
            let procLastDentry? : Option (InodeId × ByteArray) :=
              procMagicHid?.bind fun shid => (assocGet s.fds shid).bind (·.lastDentry?)
            let procExternalStdio : Bool :=
              (procMagicHid?.bind fun shid => assocGet s.fds shid).map (·.isExternalStdio) |>.getD false
            match assocGet s.inodes targetIno with
            | none => .err Errno.ENOENT
            | some vn =>
              if flags.path then
                let dentry? := match parentIno?, leaf? with
                  | some pIno, some lf => some (pIno, lf)
                  | _, _ => none
                match vn.data with
                | .symlink _ =>
                  if flags.directory || trailing then .err Errno.ENOTDIR
                  else
                    let desc : OpenDesc :=
                      { ino := targetIno, access := .rdonly, cloexec := flags.cloexec,
                        dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry?,
                        isPathFd := true, isExternalStdio := procExternalStdio }
                    let (hid, desc') :=
                      let h := s.nextHid
                      let (s1, d') := bindFreeStdioSlot s h desc
                      (h, { s1 with fds := assocSet s1.fds h d', nextHid := h + 1 })
                    .ok (.opened hid) desc'
                | .dir _ =>
                  let desc : OpenDesc :=
                    { ino := targetIno, access := .rdonly, cloexec := flags.cloexec,
                      pos := .dirStream 0 false,
                      dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry?,
                      isPathFd := true, isExternalStdio := procExternalStdio }
                  let hid := s.nextHid
                  let (s1, d') := bindFreeStdioSlot s hid desc
                  .ok (.opened hid) { s1 with fds := assocSet s1.fds hid d', nextHid := hid + 1 }
                | _ =>
                  if !(procExternalStdio || (viaProcMagic && vn.isDynamic && vn.kind == .other)) &&
                      (flags.directory || trailing) then
                    .err Errno.ENOTDIR
                  else
                    let isExt := procExternalStdio || (viaProcMagic && vn.isDynamic && vn.kind == .other)
                    let desc : OpenDesc :=
                      { ino := targetIno, access := .rdonly, cloexec := flags.cloexec,
                        dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry?,
                        isPathFd := true, isExternalStdio := isExt }
                    let hid := s.nextHid
                    if isExt && (flags.directory || trailing) then
                      .nondet (.reopenExternalStdio desc) [Errno.ENOTDIR, Errno.EACCES, Errno.ENOENT, Errno.ELOOP]
                    else
                      let (s1, d') := bindFreeStdioSlot s hid desc
                      .ok (.opened hid) { s1 with fds := assocSet s1.fds hid d', nextHid := hid + 1 }
              else
              match vn.data with
              | .symlink _ =>
                if flags.directory || trailing then .err Errno.ENOTDIR
                else if !viaProcMagic && flags.creat && !exclCreate && flags.nofollow &&
                    (s.sysctls.protectedSymlinks || s.sysctls.protectedRegular != 0 ||
                      s.sysctls.protectedFifos != 0) &&
                    isStickySymlinkBlocked s parentIno? vn then
                  .err Errno.EACCES [Errno.ELOOP]
                else .err Errno.ELOOP
              | .dir _ =>
                if flags.access != .rdonly || flags.creat || flags.trunc then .err Errno.EISDIR
                else if !hasVNodePermIn s vn true false false then .err Errno.EACCES
                else
                  let dentry? := match parentIno?, leaf? with
                    | some pIno, some lf => some (pIno, lf)
                    | _, _ => none
                  let hid := s.nextHid
                  let desc : OpenDesc :=
                    { ino := targetIno, access := .rdonly, append := flags.append,
                      nonblock := flags.nonblock, cloexec := flags.cloexec, pos := .dirStream 0 false,
                      dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry? }
                  let (s1, d') := bindFreeStdioSlot s hid desc
                  .ok (.opened hid) { s1 with fds := assocSet s1.fds hid d', nextHid := hid + 1 }
              | .socket =>
                if flags.directory || trailing then .err Errno.ENOTDIR
                else
                  let needR := flags.access == .rdonly || flags.access == .rdwr
                  let needW := flags.access == .wronly || flags.access == .rdwr || flags.trunc
                  let stickyBlocked := !viaProcMagic && isStickyCreateBlocked s parentIno? flags exclCreate vn
                  if !hasVNodePermIn s vn needR needW false || stickyBlocked then .err Errno.EACCES
                  else .err Errno.ENXIO
              | .charDev dk =>
                if flags.directory || trailing then .err Errno.ENOTDIR
                else
                  let dentry? := match parentIno?, leaf? with
                    | some pIno, some lf => some (pIno, lf)
                    | _, _ => none
                  let stickyBlocked := !viaProcMagic && isStickyCreateBlocked s parentIno? flags exclCreate vn
                  match dk with
                  | .nullDev | .zeroDev | .fullDev =>
                    let needR := flags.access == .rdonly || flags.access == .rdwr
                    let needW := flags.access == .wronly || flags.access == .rdwr || flags.trunc
                    if !hasVNodePermIn s vn needR needW false || stickyBlocked then .err Errno.EACCES
                    else
                      let hid := s.nextHid
                      let desc : OpenDesc :=
                        { ino := targetIno, access := flags.access, append := flags.append,
                          nonblock := flags.nonblock, cloexec := flags.cloexec,
                          dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry? }
                      let (s1, d') := bindFreeStdioSlot s hid desc
                      .ok (.opened hid) { s1 with fds := assocSet s1.fds hid d', nextHid := hid + 1 }
                  | _ =>
                    if stickyBlocked then .err Errno.EACCES
                    else
                      let hid := s.nextHid
                      let desc : OpenDesc :=
                        { ino := targetIno, access := flags.access, append := flags.append,
                          nonblock := flags.nonblock, cloexec := flags.cloexec,
                          dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry? }
                      let (s1, d') := bindFreeStdioSlot s hid desc
                      if vn.isDynamic then
                        .ok (.opened hid) { s1 with fds := assocSet s1.fds hid d', nextHid := hid + 1 }
                          [Errno.EACCES, Errno.ENXIO, Errno.ENODEV]
                      else .err Errno.ENXIO [Errno.EACCES, Errno.ENODEV]
              | .fifo ring =>
                if flags.directory || trailing then .err Errno.ENOTDIR
                else
                  let dentry? := match parentIno?, leaf? with
                    | some pIno, some lf => some (pIno, lf)
                    | _, _ => none
                  let needR := flags.access == .rdonly || flags.access == .rdwr
                  let openW := flags.access == .wronly || flags.access == .rdwr
                  let needW := openW || flags.trunc
                  let stickyBlocked := !viaProcMagic && isStickyCreateBlocked s parentIno? flags exclCreate vn
                  if !hasVNodePermIn s vn needR needW false || stickyBlocked then .err Errno.EACCES
                  else
                    let (minR, maxR, _, _) := fifoCounts s targetIno ring
                    if flags.access == .wronly && flags.nonblock && !vn.isDynamic && maxR == 0 then
                      .err Errno.ENXIO
                    else if flags.access == .wronly && flags.nonblock && !vn.isDynamic && minR == 0 then
                      let sClose := if s.ambientSeccomp then s else resolveUncertainFifo s targetIno true true
                      let sOpenBase := resolveUncertainFifo s targetIno true false
                      let ring1 := match assocGet sOpenBase.inodes targetIno with
                        | some v => match v.data with | .fifo r => r | _ => ring
                        | none => ring
                      let ring' :=
                        { ring1 with
                          readers := if needR then ring1.readers + 1 else ring1.readers
                          writers := if openW then ring1.writers + 1 else ring1.writers }
                      let vn' := { vn with data := .fifo ring' }
                      let hid := sOpenBase.nextHid
                      let desc : OpenDesc :=
                        { ino := targetIno, access := flags.access, append := flags.append,
                          nonblock := flags.nonblock, cloexec := flags.cloexec,
                          dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry? }
                      let (sOpen1, d') := bindFreeStdioSlot sOpenBase hid desc
                      let sOpen := { sOpen1 with
                        inodes := assocSet sOpen1.inodes targetIno vn'
                        fds := assocSet sOpen1.fds hid d'
                        nextHid := hid + 1 }
                      .nondet (.openFifoUncertain sOpen hid sClose)
                    else
                      let ring' :=
                        { ring with
                          readers := if needR then ring.readers + 1 else ring.readers
                          writers := if openW then ring.writers + 1 else ring.writers }
                      let vn' := { vn with data := .fifo ring' }
                      let hid := s.nextHid
                      let desc : OpenDesc :=
                        { ino := targetIno, access := flags.access, append := flags.append,
                          nonblock := flags.nonblock, cloexec := flags.cloexec,
                          dentry? := dentry?, lastDentry? := dentry? <|> procLastDentry? }
                      let (s1, d') := bindFreeStdioSlot s hid desc
                      .ok (.opened hid)
                        { s1 with inodes := assocSet s1.inodes targetIno vn', fds := assocSet s1.fds hid d', nextHid := hid + 1 }
                        (if vn.isDynamic && flags.access == .wronly && flags.nonblock then [Errno.ENXIO] else [])
              | _ =>
                if procExternalStdio || (viaProcMagic && vn.isDynamic && vn.kind == .other) then
                  let parentLeaf? := match parentIno?, leaf? with
                    | some pIno, some lf => some (pIno, lf)
                    | _, _ => none
                  let desc : OpenDesc :=
                    { ino := targetIno, access := flags.access, append := flags.append,
                      nonblock := flags.nonblock, cloexec := flags.cloexec,
                      dentry? := parentLeaf?, lastDentry? := parentLeaf? <|> procLastDentry?,
                      isExternalStdio := true }
                  .nondet (.reopenExternalStdio desc)
                    [Errno.EACCES, Errno.ENXIO, Errno.ELOOP, Errno.ENODEV, Errno.ENOENT,
                     Errno.EROFS, Errno.EISDIR, Errno.ENOTDIR, Errno.ETXTBSY]
                else if flags.directory || trailing then .err Errno.ENOTDIR
                else
                  let isReg := vn.kind == .reg
                  let needR := flags.access == .rdonly || flags.access == .rdwr
                  let needW := flags.access == .wronly || flags.access == .rdwr || (isReg && flags.trunc)
                  let roMount := isReadOnlyMount s vn.mountId
                  let stickyBlocked := !viaProcMagic && isStickyCreateBlocked s parentIno? flags exclCreate vn
                  let permOk := hasVNodePermIn s vn needR needW false
                  if roMount && isReg && flags.trunc then
                    .err Errno.EROFS (if stickyBlocked then [Errno.EACCES] else [])
                  else if roMount && flags.access != .rdonly then
                    .err Errno.EROFS (if !permOk || stickyBlocked then [Errno.EACCES] else [])
                  else if !permOk || stickyBlocked then .err Errno.EACCES
                  else
                    let regData := match vn.data with | .reg rd => rd | _ => {}
                    if regData.exeProtected && (flags.access != .rdonly || flags.trunc) then
                      .err Errno.ETXTBSY
                    else
                      let sealsMask : UInt32 := match regData.seals with | .sealable m => m | .unsealable => 0
                      if isReg && flags.trunc && regData.size > 0 && (sealsMask &&& 0x02) != 0 then
                        .err Errno.EPERM
                      else
                        let copyUp := vn.mayCopyUp && (flags.access != .rdonly || flags.trunc)
                        let parentLeaf? := match parentIno?, leaf? with
                          | some pIno, some lf => some (pIno, lf)
                          | _, _ => none
                        if copyUp && !isDentryLinked s targetIno parentLeaf? then
                          .err Errno.EEXIST
                        else
                          let truncReg := flags.trunc && isReg && !vn.isPseudo
                          let mode' := if truncReg && !s.cred.capableGlobalFsetid then
                            stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
                          let vnMod :=
                            match vn.data with
                            | .reg rd =>
                              let rd' := if truncReg then { rd with size := 0, extents := [] } else rd
                              { vn with data := .reg rd', mode := mode' }
                            | _ => { vn with mode := mode' }
                          let (s', targetIno') :=
                            if copyUp then copyUpInode s targetIno parentLeaf? vnMod
                            else if truncReg then ({ s with inodes := assocSet s.inodes targetIno vnMod }, targetIno)
                            else (s, targetIno)
                          let hid := s'.nextHid
                          let desc : OpenDesc :=
                            { ino := targetIno', access := flags.access, append := flags.append,
                              nonblock := flags.nonblock, cloexec := flags.cloexec,
                              dentry? := parentLeaf?, lastDentry? := parentLeaf? <|> procLastDentry? }
                          let (s'', d') := bindFreeStdioSlot s' hid desc
                          .ok (.opened hid) { s'' with fds := assocSet s''.fds hid d', nextHid := hid + 1 }
        | .ok (.missingInParent parentIno leaf trailing) =>
          if !flags.creat then .err Errno.ENOENT
          else
            match assocGet s.inodes parentIno with
            | none => .err Errno.ENOENT
            | some pvn =>
              match pvn.data with
              | .dir pdd =>
                if pvn.nlink == 0 || pdd.lifecycle.isDead then .err Errno.ENOENT
                else if trailing then .err Errno.EISDIR
                else if isReadOnlyMount s pvn.mountId then .err Errno.EROFS
                else if pvn.isPseudo then .err Errno.ENOENT [Errno.EACCES, Errno.EPERM]
                else if !hasVNodePermIn s pvn false true true then
                  .err Errno.EACCES (if !s.cred.initUserNs && hasVNodePermIn s pvn false false true then [(75 : Errno)] else [])
                else
                  let newIno := s.nextIno
                  let posix := mountPosixModes s pvn.mountId
                  let sgidDir := posix && (pvn.mode &&& 0o2000) != 0
                  let newOwner : InodeOwner :=
                    if sgidDir then { inGroup := pvn.owner.inGroup, uidMapped := s.cred.uidMapped, gidMapped := pvn.owner.gidMapped }
                    else { uidMapped := s.cred.uidMapped, gidMapped := s.cred.gidMapped }
                  let rawMode := (mode &&& ~~~(s.umask &&& 0o0777)) &&& 0o7777
                  let createdMode :=
                    if !posix then 0o644
                    else if sgidDir && (mode &&& 0o2010) == 0o2010 &&
                        !pvn.owner.inGroup && !s.cred.capableWrtInode pvn.owner (·.capFsetid) then
                      rawMode &&& ~~~(0o2000 : Mode)
                    else rawMode
                  let sealsInit : SealState := .unsealable
                  let newVn : VNode :=
                    { data := .reg { seals := sealsInit }, mode := createdMode, modeExact := posix,
                      mountId := pvn.mountId, owner := newOwner, nlink := 1 }
                  let pvn' := markParentOverlay pvn (bytesAssocSet pdd.children leaf newIno) 0
                  let hid := s.nextHid
                  let desc : OpenDesc :=
                    { ino := newIno, access := flags.access, append := flags.append,
                      nonblock := flags.nonblock, cloexec := flags.cloexec,
                      dentry? := some (parentIno, leaf), lastDentry? := some (parentIno, leaf) }
                  let (s1, d') := bindFreeStdioSlot s hid desc
                  .ok (.opened hid)
                    { s1 with
                      inodes := assocSet (assocSet s1.inodes parentIno pvn') newIno newVn
                      fds := assocSet s1.fds hid d'
                      nextIno := newIno + 1
                      nextHid := hid + 1 }
                    (if !s.cred.initUserNs then [(75 : Errno)] else [])
              | _ => .err Errno.ENOTDIR
      withOpenat2Eagain (strictOpenat2 && (validateOpenStart s dir path resolve).isOk) resolve touchedDotDot core

/-- Evaluate a `read` transition into `StepResult`. -/
def evalRead (s : FilesState) (hid : HandleId) (maxBytes : UInt32) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd || desc.access == .wronly then .err Errno.EBADF
    else if desc.isExternalStdio then
      let cap := min maxBytes.toNat MAX_READ_BYTES.toNat
      .nondet (.readDynamic hid desc cap desc.nonblock true)
        [Errno.EBADF, Errno.EISDIR, Errno.EPIPE, (107 : Errno), (104 : Errno)]
    else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        let cap := min maxBytes.toNat MAX_READ_BYTES.toNat
        match vn.data with
        | .dir _ => .err Errno.EISDIR (if desc.pos.dirCursor > 0 then [Errno.EINVAL] else [])
        | .charDev dk =>
          match dk with
          | .nullDev => .ok (.bytes (ByteArray.mk #[])) s
          | .zeroDev | .fullDev => .nondet (.readZeroDev cap)
          | _ =>
            if vn.isDynamic then
              .nondet (.readDynamic hid desc cap desc.nonblock true)
                [Errno.EINVAL, Errno.ENXIO, Errno.ENODEV]
            else .err Errno.ENXIO [Errno.EINVAL, Errno.ENODEV]
        | .fifo ring =>
          if cap == 0 then .ok (.bytes (ByteArray.mk #[])) s
          else if ring.buf.size == 0 then
            let (_, _, minW, maxW) := fifoCounts s desc.ino ring
            if !vn.isDynamic && maxW == 0 then .ok (.bytes (ByteArray.mk #[])) s
            else if !vn.isDynamic && minW == 0 then
              if desc.nonblock then
                .err Errno.EAGAIN [] (if s.ambientSeccomp then none else some (resolveUncertainFifo s desc.ino false false))
              else .ok (.bytes (ByteArray.mk #[])) (resolveUncertainFifo s desc.ino false true)
            else if desc.nonblock then
              if vn.isDynamic then .nondet (.readFifo desc.ino ring cap true true) [Errno.EAGAIN]
              else .err Errno.EAGAIN
            else
              .nondet (.readFifo desc.ino ring cap false vn.isDynamic)
          else .nondet (.readFifo desc.ino ring cap desc.nonblock vn.isDynamic)
        | .reg rd =>
          if vn.isDynamic then .nondet (.readDynamic hid desc cap desc.nonblock false) [Errno.EINVAL]
          else if desc.pos.offset + cap > 9223372036854775807 then .err Errno.EINVAL
          else .nondet (.readReg hid desc rd cap)
        | _ =>
          if vn.isDynamic then .nondet (.readDynamic hid desc cap desc.nonblock false) [Errno.EINVAL]
          else if desc.pos.offset + cap > 9223372036854775807 then .err Errno.EINVAL
          else .nondet (.readReg hid desc {} cap)

/-- Evaluate a `write` transition into `StepResult`. -/
def evalWrite (s : FilesState) (hid : HandleId) (data : ByteArray) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd || desc.access == .rdonly then .err Errno.EBADF
    else if desc.isExternalStdio then
      .nondet (.writeDiscard data.size
        [Errno.EBADF, Errno.EPIPE, Errno.EPERM, Errno.EINVAL, Errno.EROFS,
         Errno.ENXIO, Errno.ENODEV, Errno.EAGAIN, Errno.ENOSPC, Errno.EFBIG,
         Errno.EISDIR, (107 : Errno), (89 : Errno), (104 : Errno)] true)
    else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        match vn.data with
        | .dir _ => .err Errno.EBADF [Errno.EISDIR]
        | .charDev dk =>
          if vn.isPseudo then
            .nondet (.writeDiscard data.size
              [Errno.EINVAL, Errno.EACCES, Errno.EPERM, Errno.ERANGE, Errno.ENOENT, Errno.ESRCH] false)
          else
            match dk with
            | .fullDev => .err Errno.ENOSPC
            | .nullDev | .zeroDev => .nondet (.writeDiscard data.size [] false)
            | _ =>
              if vn.isDynamic then
                .nondet (.writeDiscard data.size [Errno.EINVAL, Errno.ENXIO, Errno.ENODEV] desc.nonblock)
                  (if desc.nonblock then [Errno.EAGAIN] else [])
              else .err Errno.ENXIO [Errno.EINVAL, Errno.ENODEV]
        | .fifo ring =>
          let (minR, maxR, _, _) := fifoCounts s desc.ino ring
          let (_, maxCanWrite) := pipeWriteSlots ring.slots ring.capacity.maxPages data.size
          if !vn.isDynamic && maxR == 0 then
            if data.size == 0 then .ok (.u32 0) s else .err Errno.EPIPE
          else if data.size == 0 then
            .ok (.u32 0) s (if vn.isDynamic then [Errno.EPIPE] else [])
          else if !vn.isDynamic && desc.nonblock && maxCanWrite == 0 then
            .err Errno.EAGAIN (if minR == 0 then [Errno.EPIPE] else [])
          else
            .nondet (.writeFifo desc.ino ring data desc.nonblock vn.isDynamic)
              (if vn.isDynamic then (if desc.nonblock then [Errno.EAGAIN, Errno.EPIPE] else [Errno.EPIPE])
               else if minR == 0 then [Errno.EPIPE] else [])
        | _ =>
          if vn.isPseudo then
            .nondet (.writeDiscard data.size
              [Errno.EINVAL, Errno.EACCES, Errno.EPERM, Errno.ERANGE, Errno.ENOENT, Errno.ESRCH] false)
          else
            let rd := match vn.data with | .reg r => r | _ => {}
            let sealsMask : UInt32 := match rd.seals with | .sealable m => m | .unsealable => 0
            let pos := if desc.append then rd.size else desc.pos.offset
            let growSealed := (sealsMask &&& 0x04) != 0
            let writeSealed := data.size > 0 && ((sealsMask &&& 0x18) != 0 ||
              (growSealed && pos >= rd.size))
            let stripPriv := vn.kind == .reg && !s.cred.capableGlobalFsetid
            if desc.pos.offset + data.size > 9223372036854775807 ||
                pos + data.size > 9223372036854775807 then
              .err Errno.EINVAL (if data.size > 0 && pos <= 9223372036854775807 then [Errno.EFBIG] else [])
            else if writeSealed then
              let s' :=
                if stripPriv then
                  let vn' := { vn with
                    mode := stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode
                    modeExact := if s.ambientSeccomp then false else vn.modeExact }
                  some { s with inodes := assocSet s.inodes desc.ino vn' }
                else none
              .err Errno.EPERM [Errno.EFBIG] s'
            else
              let roMount := isReadOnlyMount s vn.mountId
              let isOvl := (mountProfileOf s vn.mountId).isOverlay && vn.kind == .reg
              .nondet (.writeReg hid desc desc.ino data stripPriv isOvl roMount vn.mayCopyUp)
                (if roMount then [Errno.EROFS] else [])

/-- Evaluate a `fstat` or `fstatat` transition into `StepResult`. -/
def evalStat (s : FilesState) (req : FilesReq) : StepResult :=
  match req with
  | .fstat hid =>
    match assocGet s.fds hid with
    | none => .wrapperErr Errno.EBADF
    | some desc =>
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn => .nondet (.statNode desc.ino vn)
  | .fstatat dir path flags =>
    if flags.eaccess then .wrapperErr Errno.EINVAL
    else if path.size == 0 && flags.emptyPath then
      let targetRes : Except Errno InodeId := match dir with
        | none => .ok s.cwdIno
        | some hid => match assocGet s.fds hid with
          | none => .error Errno.EBADF
          | some d => .ok d.ino
      match targetRes with
      | .error e => .err e
      | .ok ino =>
        match assocGet s.inodes ino with
        | none => .err Errno.EBADF
        | some vn => .nondet (.statNode ino vn)
    else
      match resolveLookupOrExt s dir path (!flags.symlinkNofollow) with
      | .error re => .err re
      | .ok none => .nondet .externalStdioStat
      | .ok (some (ino, _, _)) =>
        match assocGet s.inodes ino with
        | none => .err Errno.ENOENT
        | some vn => .nondet (.statNode ino vn)
  | _ => .wrapperErr Errno.EINVAL

/-- Evaluate a `faccessat` transition into `StepResult`. -/
def evalAccess (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (mask : AccessModeMask) (flags : AtFlags) : StepResult :=
  let targetRes : Except Errno (Option InodeId) :=
    if path.size == 0 && flags.emptyPath then
      match dir with
      | none => .ok (some s.cwdIno)
      | some hid => match assocGet s.fds hid with
        | none => .error Errno.EBADF
        | some d => .ok (some d.ino)
    else (resolveLookupOrExt s dir path (!flags.symlinkNofollow)).map (·.map (·.1))
  match targetRes with
  | .error re => .err re
  | .ok none => .nondet .externalStdioUnit
  | .ok (some ino) =>
    match assocGet s.inodes ino with
    | none => .err Errno.ENOENT
    | some vn =>
      if vn.isDynamic && vn.kind == .other then
        .ok .unit s ([Errno.EACCES, Errno.ENOENT] ++ (if mask.write then [Errno.EROFS] else []))
      else
      let isRevalidatedProcLink := match vn.data with
        | .symlink (.procMagic _ (some h)) => vn.isPseudo && (assocGet s.fds h).isNone
        | _ => false
      let procRevalErrs := if isRevalidatedProcLink then [Errno.EACCES, Errno.ENOENT] else []
      let permOk := hasVNodePermIn s vn mask.read mask.write mask.exec
      if mask.write && isReadOnlyMount s vn.mountId &&
          (vn.kind == .reg || vn.kind == .dir || vn.kind == .symlink) then
        .err Errno.EROFS ((if !permOk then [Errno.EACCES] else []) ++ procRevalErrs)
      else if permOk then .ok .unit s procRevalErrs
      else .err Errno.EACCES (if isRevalidatedProcLink then [Errno.ENOENT] else [])

/-- Evaluate `mkdirat` against the tracked filesystem state. -/
def evalMkdir (s : FilesState) (dir : Option HandleId) (path : ByteArray) (mode : Mode) : StepResult :=
  match resolveParentOrExt s dir path with
  | .error pe => .err pe
  | .ok none => .nondet .externalStdioUnit
  | .ok (some (parentIno, leaf, _)) =>
    if bytesEq leaf slashBytes || bytesEq leaf dotBytes || bytesEq leaf dotDotBytes then .err Errno.EEXIST
    else
      match assocGet s.inodes parentIno with
      | none => .err Errno.ENOENT
      | some pvn =>
        match pvn.data with
        | .dir pdd =>
          if pvn.nlink == 0 || pdd.lifecycle.isDead then .err Errno.ENOENT
          else if (bytesAssocGet pdd.children leaf).isSome then .err Errno.EEXIST
          else if isReadOnlyMount s pvn.mountId then .err Errno.EROFS
          else if pvn.isPseudo then .err Errno.ENOENT [Errno.EACCES, Errno.EPERM]
          else if !hasVNodePermIn s pvn false true true then
            .err Errno.EACCES (if !s.cred.initUserNs && hasVNodePermIn s pvn false false true then [(75 : Errno)] else [])
          else
            let newIno := s.nextIno
            let posix := mountPosixModes s pvn.mountId
            let sgidDir := posix && (pvn.mode &&& 0o2000) != 0
            let newOwner : InodeOwner :=
              if sgidDir then { inGroup := pvn.owner.inGroup, uidMapped := s.cred.uidMapped, gidMapped := pvn.owner.gidMapped }
              else { uidMapped := s.cred.uidMapped, gidMapped := s.cred.gidMapped }
            let createdMode :=
              if !posix then 0o755
              else
                let baseMode := (mode &&& ~~~(s.umask &&& 0o0777)) &&& 0o1777
                if (pvn.mode &&& 0o2000) != 0 then baseMode ||| 0o2000 else baseMode
            let newDir : VNode :=
              { data := .dir { parentIno := parentIno, lifecycle := .live },
                mode := createdMode, modeExact := posix, mountId := pvn.mountId, owner := newOwner, nlink := 2 }
            let pvn' := markParentOverlay pvn (bytesAssocSet pdd.children leaf newIno) 1
            .ok .unit
              { s with inodes := assocSet (assocSet s.inodes parentIno pvn') newIno newDir, nextIno := newIno + 1 }
              (if !s.cred.initUserNs then [(75 : Errno)] else [])
        | _ => .err Errno.ENOTDIR

/-- Evaluate `unlinkat` against the tracked filesystem state. -/
def evalUnlink (s : FilesState) (dir : Option HandleId) (path : ByteArray) (removeDir : Bool) : StepResult :=
  match resolveParentOrExt s dir path (checkLeafNameMax := false) (checkDeadParent := false) with
  | .error pe => .err pe
  | .ok none => .nondet .externalStdioUnit
  | .ok (some (parentIno, leaf, trailing)) =>
    if bytesEq leaf slashBytes then .err (if removeDir then Errno.EBUSY else Errno.EISDIR)
    else if bytesEq leaf dotBytes then .err (if removeDir then Errno.EINVAL else Errno.EISDIR)
    else if bytesEq leaf dotDotBytes then
      if removeDir then .err Errno.ENOTEMPTY [Errno.EEXIST, Errno.EBUSY]
      else .err Errno.EISDIR
    else
      match assocGet s.inodes parentIno with
      | none => .err Errno.ENOENT
      | some pvn =>
        match pvn.data with
        | .dir pdd =>
          if isReadOnlyMount s pvn.mountId then .err Errno.EROFS
          else if pvn.nlink == 0 || pdd.lifecycle.isDead then .err Errno.ENOENT
          else if leaf.size > NAME_MAX then .err Errno.ENAMETOOLONG
          else
            match bytesAssocGet pdd.children leaf with
            | none => .err Errno.ENOENT (if pvn.isPseudo then [Errno.EPERM, Errno.EACCES] else [])
            | some childIno =>
              match assocGet s.inodes childIno with
              | none => .err Errno.ENOENT
              | some cvn =>
                if !removeDir && trailing then
                  .err (if cvn.kind != .dir then Errno.ENOTDIR else Errno.EISDIR)
                else if pvn.isPseudo || cvn.isPseudo then
                  let extras :=
                    [Errno.EACCES] ++
                    (if removeDir && cvn.kind != .dir then [Errno.ENOTDIR] else []) ++
                    (if !removeDir && cvn.kind == .dir then [Errno.EISDIR] else [])
                  .err Errno.EPERM extras
                else if !hasVNodePermIn s pvn false true true then .err Errno.EACCES
                else if isStickyDeleteBlocked s pvn cvn then .err Errno.EPERM
                else if removeDir then
                  match cvn.data with
                  | .dir cdd =>
                    if cvn.nlink == 0 && !cvn.mayCopyUp then .err Errno.ENOENT
                    else if !cdd.children.isEmpty then .err Errno.ENOTEMPTY [Errno.EEXIST]
                    else
                      let pvn' := markParentOverlay pvn (bytesAssocErase pdd.children leaf) (-1)
                      let cvn' :=
                        if cvn.mayCopyUp then { cvn with data := .dir { cdd with lifecycle := .overlayDeadLower } }
                        else if cdd.lifecycle == .overlayMerged then
                          { cvn with data := .dir { cdd with lifecycle := .overlayDeadMerged }, nlink := 1 }
                        else { cvn with data := .dir { cdd with lifecycle := .unlinked }, nlink := 0 }
                      let fds' := clearDentryOnFds s.fds (parentIno, leaf)
                      let inodes1 := assocSet (assocSet s.inodes parentIno pvn') childIno cvn'
                      let inodes2 := pruneIfDeadInode inodes1 fds' s.cwdIno s.rootIno childIno
                      .ok .unit { s with inodes := inodes2, fds := fds' }
                  | _ => .err Errno.ENOTDIR
                else if cvn.kind == .dir then .err Errno.EISDIR
                else
                  let pvn' := markParentOverlay pvn (bytesAssocErase pdd.children leaf) 0
                  let cvn' := if cvn.mayCopyUp then cvn else { cvn with nlink := cvn.nlink - 1 }
                  let fds' := clearDentryOnFds s.fds (parentIno, leaf)
                  let inodes1 := assocSet (assocSet s.inodes parentIno pvn') childIno cvn'
                  let inodes2 := pruneIfDeadInode inodes1 fds' s.cwdIno s.rootIno childIno
                  .ok .unit { s with inodes := inodes2, fds := fds' }
        | _ => .err Errno.ENOTDIR

private def setDirParent (vn : VNode) (newParent : InodeId) : VNode :=
  match vn.data with
  | .dir dd => { vn with data := .dir { dd with parentIno := newParent } }
  | _ => vn

/-- Evaluate `renameat2` against the tracked filesystem state. -/
def evalRename (s : FilesState) (oldDir : Option HandleId) (oldPath : ByteArray)
    (newDir : Option HandleId) (newPath : ByteArray) (flags : RenameFlags) : StepResult :=
  if flags.exchange && (flags.noreplace || flags.whiteout) then .err Errno.EINVAL
  else
    match resolveParentOrExt s oldDir oldPath (checkLeafNameMax := false) (checkDeadParent := false),
        resolveParentOrExt s newDir newPath (checkLeafNameMax := false) (checkDeadParent := false) with
    | .error pe, _ => .err pe
    | _, .error pe => .err pe
    | .ok none, _ => .nondet .externalStdioUnit
    | _, .ok none => .nondet .externalStdioUnit
    | .ok (some (oldP, oldLeaf, oldTrailing)), .ok (some (newP, newLeaf, newTrailing)) =>
      match assocGet s.inodes oldP, assocGet s.inodes newP with
      | some oldPvn, some newPvn =>
        match oldPvn.data, newPvn.data with
        | .dir oldDd, .dir newDd =>
          if oldPvn.mountId != newPvn.mountId then .err Errno.EXDEV
          else if bytesEq oldLeaf slashBytes || bytesEq newLeaf slashBytes ||
              bytesEq oldLeaf dotBytes || bytesEq oldLeaf dotDotBytes ||
              bytesEq newLeaf dotBytes || bytesEq newLeaf dotDotBytes then
            .err Errno.EBUSY (if flags.noreplace then [Errno.EEXIST] else [])
          else if isReadOnlyMount s oldPvn.mountId || isReadOnlyMount s newPvn.mountId then .err Errno.EROFS
          else if oldPvn.nlink == 0 || oldDd.lifecycle.isDead then .err Errno.ENOENT
          else if oldLeaf.size > NAME_MAX then .err Errno.ENAMETOOLONG
          else
            let pseudoErrs := if oldPvn.isPseudo || newPvn.isPseudo then [Errno.EPERM, Errno.EACCES, Errno.EINVAL] else []
            match bytesAssocGet oldDd.children oldLeaf with
            | none => .err Errno.ENOENT pseudoErrs
            | some srcIno =>
              match assocGet s.inodes srcIno with
              | none => .err Errno.ENOENT
              | some srcVn =>
                if newPvn.nlink == 0 || newDd.lifecycle.isDead then .err Errno.ENOENT
                else if newLeaf.size > NAME_MAX then .err Errno.ENAMETOOLONG
                else
                  let ovlErrs (extraCond : Bool) :=
                    (if extraCond then [Errno.EXDEV] else []) ++
                    (if flags.whiteout then [Errno.EPERM, Errno.EINVAL, Errno.EOPNOTSUPP] else [])
                  let isOvl := (mountProfileOf s oldPvn.mountId).isOverlay
                  match bytesAssocGet newDd.children newLeaf with
                  | none =>
                    if flags.exchange then .err Errno.ENOENT pseudoErrs
                    else if (oldTrailing || newTrailing) && srcVn.kind != .dir then .err Errno.ENOTDIR
                    else if srcVn.kind == .dir && isAncestorInode s srcIno newP then .err Errno.EINVAL
                    else if oldPvn.isPseudo || newPvn.isPseudo then
                      .err Errno.EPERM [Errno.EACCES, Errno.EINVAL, Errno.ENOENT, Errno.EEXIST]
                    else if !hasVNodePermIn s oldPvn false true true then .err Errno.EACCES
                    else if isStickyDeleteBlocked s oldPvn srcVn then .err Errno.EPERM
                    else if !hasVNodePermIn s newPvn false true true then .err Errno.EACCES
                    else if srcVn.kind == .dir && oldP != newP && !hasVNodePermIn s srcVn false true false then
                      .err Errno.EACCES
                    else if srcVn.nlink == 0 || srcVn.isDeadDir then .err Errno.ESTALE
                    else
                      let woIno := s.nextIno
                      let inodes1 :=
                        if oldP == newP then
                          let ch1 := if flags.whiteout then bytesAssocSet (bytesAssocSet oldDd.children oldLeaf woIno) newLeaf srcIno
                            else bytesAssocSet (bytesAssocErase oldDd.children oldLeaf) newLeaf srcIno
                          assocSet s.inodes oldP (markParentOverlay oldPvn ch1 0)
                        else
                          let oldCh := if flags.whiteout then bytesAssocSet oldDd.children oldLeaf woIno
                            else bytesAssocErase oldDd.children oldLeaf
                          let oldP' := markParentOverlay oldPvn oldCh (if srcVn.kind == .dir then (-1) else 0)
                          let newP' := markParentOverlay newPvn (bytesAssocSet newDd.children newLeaf srcIno)
                            (if srcVn.kind == .dir then 1 else 0)
                          assocSet (assocSet s.inodes oldP oldP') newP newP'
                      let inodes2 := if srcVn.kind == .dir then assocSet inodes1 srcIno (setDirParent srcVn newP) else inodes1
                      let (inodes3, next0) :=
                        if flags.whiteout then
                          let woVn : VNode :=
                            { data := .charDev .whiteout, mode := 0, modeExact := true,
                              mountId := oldPvn.mountId, nlink := 1 }
                          (assocSet inodes2 woIno woVn, s.nextIno + 1)
                        else (inodes2, s.nextIno)
                      let fds1 := moveDentryOnFds s.fds (oldP, oldLeaf) (newP, newLeaf) false
                      let (inodes4, fds2, nextIno') := applyCopyUpOnRename inodes3 fds1 next0 newP newLeaf srcIno srcVn
                      let cwdPath' :=
                        if srcVn.kind == .dir && isAncestorInode s srcIno s.cwdIno then .unbound s.cwdPath.bytes
                        else s.cwdPath
                      .ok .unit { s with inodes := inodes4, fds := fds2, nextIno := nextIno', cwdPath := cwdPath' }
                        (ovlErrs (isOvl && srcVn.kind == .dir))
                  | some dstIno =>
                    if flags.noreplace then .err Errno.EEXIST
                    else
                      match assocGet s.inodes dstIno with
                      | none => .err Errno.ENOENT
                      | some dstVn =>
                        if srcVn.kind == .dir && isAncestorInode s srcIno newP then .err Errno.EINVAL
                        else if dstVn.kind == .dir && isAncestorInode s dstIno oldP then
                          if flags.exchange then .err Errno.EINVAL
                          else .err Errno.ENOTEMPTY [Errno.EEXIST]
                        else if oldTrailing && srcVn.kind != .dir then .err Errno.ENOTDIR
                        else if newTrailing && !flags.exchange && srcVn.kind != .dir then .err Errno.ENOTDIR
                        else if flags.exchange && newTrailing && dstVn.kind != .dir then .err Errno.ENOTDIR
                        else if srcIno == dstIno && ((oldP == newP && bytesEq oldLeaf newLeaf) || !(isOvl && srcVn.mayCopyUp)) then
                          .ok .unit s (pseudoErrs ++ (if flags.whiteout then [Errno.EPERM, Errno.EINVAL, Errno.EOPNOTSUPP] else []))
                        else if oldPvn.isPseudo || newPvn.isPseudo then .err Errno.EPERM [Errno.EACCES, Errno.EINVAL]
                        else if !hasVNodePermIn s oldPvn false true true then .err Errno.EACCES
                        else if isStickyDeleteBlocked s oldPvn srcVn then .err Errno.EPERM
                        else if !hasVNodePermIn s newPvn false true true then .err Errno.EACCES
                        else if isStickyDeleteBlocked s newPvn dstVn then .err Errno.EPERM
                        else if newTrailing && dstVn.kind != .dir then .err Errno.ENOTDIR
                        else if srcVn.nlink == 0 || srcVn.isDeadDir || dstVn.nlink == 0 || dstVn.isDeadDir then
                          .err Errno.ESTALE
                        else if flags.exchange then
                          if oldP != newP &&
                              ((srcVn.kind == .dir && !hasVNodePermIn s srcVn false true false) ||
                               (dstVn.kind == .dir && !hasVNodePermIn s dstVn false true false)) then
                            .err Errno.EACCES
                          else
                            let nextSt :=
                              if oldP == newP && bytesEq oldLeaf newLeaf then s
                              else
                                let inodes1 :=
                                  if oldP == newP then
                                    let ch1 := bytesAssocSet (bytesAssocSet oldDd.children oldLeaf dstIno) newLeaf srcIno
                                    assocSet s.inodes oldP (markParentOverlay oldPvn ch1 0)
                                  else
                                    let oldDelta : Int := (if dstVn.kind == .dir then 1 else 0) - (if srcVn.kind == .dir then 1 else 0)
                                    let newDelta : Int := (if srcVn.kind == .dir then 1 else 0) - (if dstVn.kind == .dir then 1 else 0)
                                    let oldP' := markParentOverlay oldPvn (bytesAssocSet oldDd.children oldLeaf dstIno) oldDelta
                                    let newP' := markParentOverlay newPvn (bytesAssocSet newDd.children newLeaf srcIno) newDelta
                                    assocSet (assocSet s.inodes oldP oldP') newP newP'
                                let inodes2 := if srcVn.kind == .dir then assocSet inodes1 srcIno (setDirParent srcVn newP) else inodes1
                                let inodes3 := if dstVn.kind == .dir then assocSet inodes2 dstIno (setDirParent dstVn oldP) else inodes2
                                let fds1 := moveDentryOnFds s.fds (oldP, oldLeaf) (newP, newLeaf) true
                                let (inodes4, fds2, n1) := applyCopyUpOnRename inodes3 fds1 s.nextIno newP newLeaf srcIno srcVn
                                let (inodes5, fds3, n2) := applyCopyUpOnRename inodes4 fds2 n1 oldP oldLeaf dstIno dstVn
                                let cwdPath' :=
                                  if (srcVn.kind == .dir && isAncestorInode s srcIno s.cwdIno) ||
                                      (dstVn.kind == .dir && isAncestorInode s dstIno s.cwdIno) then .unbound s.cwdPath.bytes
                                  else s.cwdPath
                                { s with inodes := inodes5, fds := fds3, nextIno := n2, cwdPath := cwdPath' }
                            let exchErrs := [Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ENOSYS] ++
                              (if isOvl && (srcVn.kind == .dir || dstVn.kind == .dir) then [Errno.EXDEV] else [])
                            .ok .unit nextSt exchErrs
                        else if srcVn.kind == .dir && dstVn.kind != .dir then .err Errno.ENOTDIR
                        else if srcVn.kind != .dir && dstVn.kind == .dir then .err Errno.EISDIR
                        else if srcVn.kind == .dir && oldP != newP && !hasVNodePermIn s srcVn false true false then
                          .err Errno.EACCES
                        else if !dstVn.children.isEmpty then
                          .err Errno.ENOTEMPTY
                            ([Errno.EEXIST] ++
                             (if isOvl && (srcVn.kind == .dir || dstVn.kind == .dir) then [Errno.EXDEV] else []) ++
                             (if flags.whiteout then [Errno.EPERM, Errno.EINVAL, Errno.EOPNOTSUPP] else []))
                        else
                          let woIno := s.nextIno
                          let inodes1 :=
                            if oldP == newP then
                              let ch1 := if flags.whiteout then bytesAssocSet (bytesAssocSet oldDd.children oldLeaf woIno) newLeaf srcIno
                                else bytesAssocSet (bytesAssocErase oldDd.children oldLeaf) newLeaf srcIno
                              assocSet s.inodes oldP (markParentOverlay oldPvn ch1 (if dstVn.kind == .dir then (-1) else 0))
                            else
                              let oldCh := if flags.whiteout then bytesAssocSet oldDd.children oldLeaf woIno
                                else bytesAssocErase oldDd.children oldLeaf
                              let oldP' := markParentOverlay oldPvn oldCh (if srcVn.kind == .dir then (-1) else 0)
                              let newP' := markParentOverlay newPvn (bytesAssocSet newDd.children newLeaf srcIno) 0
                              assocSet (assocSet s.inodes oldP oldP') newP newP'
                          let (dstNlink', dstLife') :=
                            if dstVn.mayCopyUp then (dstVn.nlink, DirLifecycle.overlayDeadLower)
                            else if dstVn.kind == .dir && dstVn.overlayMergedDir then (1, DirLifecycle.overlayDeadMerged)
                            else (if dstVn.kind == .dir then 0 else dstVn.nlink - 1, DirLifecycle.unlinked)
                          let dstData' := match dstVn.data with
                            | .dir cdd => .dir { cdd with lifecycle := dstLife' }
                            | d => d
                          let inodes2 := assocSet inodes1 dstIno { dstVn with data := dstData', nlink := dstNlink' }
                          let inodes3 := if srcVn.kind == .dir then assocSet inodes2 srcIno (setDirParent srcVn newP) else inodes2
                          let (inodes4, next0) :=
                            if flags.whiteout then
                              let woVn : VNode :=
                                { data := .charDev .whiteout, mode := 0, modeExact := true,
                                  mountId := oldPvn.mountId, nlink := 1 }
                              (assocSet inodes3 woIno woVn, s.nextIno + 1)
                            else (inodes3, s.nextIno)
                          let fds1 := moveDentryOnFds s.fds (oldP, oldLeaf) (newP, newLeaf) false
                          let (inodes5, fds2, nextIno') := applyCopyUpOnRename inodes4 fds1 next0 newP newLeaf srcIno srcVn
                          let cwdPath' :=
                            if srcVn.kind == .dir && isAncestorInode s srcIno s.cwdIno then .unbound s.cwdPath.bytes
                            else s.cwdPath
                          .ok .unit { s with inodes := inodes5, fds := fds2, nextIno := nextIno', cwdPath := cwdPath' }
                            (ovlErrs (isOvl && (srcVn.kind == .dir || dstVn.kind == .dir)))
        | _, _ => .err Errno.ENOTDIR
      | _, _ => .err Errno.ENOENT

/-- Evaluate a `symlinkat` transition into `StepResult`. -/
def evalSymlink (s : FilesState) (target : ByteArray) (dir : Option HandleId) (linkPath : ByteArray) : StepResult :=
  if target.size >= PATH_MAX then .err Errno.ENAMETOOLONG
  else if target.size == 0 then .err Errno.ENOENT
  else
    match resolveParentOrExt s dir linkPath with
    | .error pe => .err pe
    | .ok none => .nondet .externalStdioUnit
    | .ok (some (parentIno, leaf, trailing)) =>
      if bytesEq leaf slashBytes || bytesEq leaf dotBytes || bytesEq leaf dotDotBytes then .err Errno.EEXIST
      else
        match assocGet s.inodes parentIno with
        | none => .err Errno.ENOENT
        | some pvn =>
          match pvn.data with
          | .dir pdd =>
            if pvn.nlink == 0 || pdd.lifecycle.isDead then .err Errno.ENOENT
            else if (bytesAssocGet pdd.children leaf).isSome then .err Errno.EEXIST
            else if trailing then .err Errno.ENOENT
            else if isReadOnlyMount s pvn.mountId then .err Errno.EROFS
            else if !hasVNodePermIn s pvn false false true then .err Errno.EACCES
            else if !mountSupportsSymlinks s pvn.mountId then
              .err Errno.EPERM ([Errno.EOPNOTSUPP, Errno.EINVAL] ++ (if !s.cred.initUserNs then [(75 : Errno)] else []))
            else if pvn.isPseudo then .err Errno.ENOENT [Errno.EACCES, Errno.EPERM]
            else if !hasVNodePermIn s pvn false true true then
              .err Errno.EACCES (if !s.cred.initUserNs && hasVNodePermIn s pvn false false true then [(75 : Errno)] else [])
            else
              let newIno := s.nextIno
              let symVn : VNode :=
                { data := .symlink (.path target), mode := 0o777, modeExact := true,
                  mountId := pvn.mountId, owner := { uidMapped := s.cred.uidMapped, gidMapped := s.cred.gidMapped }, nlink := 1 }
              let pvn' := markParentOverlay pvn (bytesAssocSet pdd.children leaf newIno) 0
              .ok .unit
                { s with inodes := assocSet (assocSet s.inodes parentIno pvn') newIno symVn, nextIno := newIno + 1 }
                (if !s.cred.initUserNs then [(75 : Errno)] else [])
          | _ => .err Errno.ENOTDIR

/-- Evaluate `readlinkat` against the tracked filesystem state. -/
def evalReadlink (s : FilesState) (dir : Option HandleId) (path : ByteArray) (cap : UInt32) : StepResult :=
  if cap == 0 then .err Errno.EINVAL
  else if path.size == 0 then
    match dir with
    | some hid =>
      match assocGet s.fds hid with
      | none => .err Errno.EBADF
      | some d =>
        if d.isExternalStdio then
          let maxCap := min cap.toNat MAX_READ_BYTES.toNat
          .nondet (.readlinkDynamic maxCap) [Errno.ENOENT, Errno.EINVAL, Errno.EACCES]
        else
        match assocGet s.inodes d.ino with
        | some vn =>
          match vn.data with
          | .symlink symTgt =>
            let maxCap := min cap.toNat MAX_READ_BYTES.toNat
            match symTgt with
            | .procMagic _ fdHid? =>
              match fdHid? with
              | some targetHid =>
                match assocGet s.fds targetHid with
                | none => .err Errno.ENOENT
                | some td =>
                  if td.closeState == .closeUncertain then
                    if !vn.owner.ownedByUid then .err Errno.EACCES [Errno.ENOENT]
                    else .nondet (.readlinkDynamic maxCap) [Errno.ENOENT]
                  else if !vn.owner.ownedByUid then .err Errno.EACCES
                  else .nondet (.readlinkDynamic maxCap)
              | none =>
                if !vn.owner.ownedByUid then .err Errno.EACCES
                else .nondet (.readlinkDynamic maxCap)
            | .path targetBytes =>
              if vn.isDynamic then .nondet (.readlinkDynamic maxCap)
              else .ok (.bytes (sliceBytes targetBytes 0 (min targetBytes.size maxCap))) s
          | _ => .err Errno.ENOENT
        | none => .err Errno.ENOENT
    | none => .err Errno.ENOENT
  else
    match resolveLookupOrExt s dir path false with
    | .error re => .err re
    | .ok none =>
      .nondet (.readlinkDynamic (min cap.toNat MAX_READ_BYTES.toNat))
        [Errno.ENOTDIR, Errno.ENOENT, Errno.EINVAL, Errno.EACCES, Errno.ELOOP, Errno.ENAMETOOLONG]
    | .ok (some (ino, _, _)) =>
      match assocGet s.inodes ino with
      | none => .err Errno.ENOENT
      | some vn =>
        match vn.data with
        | .symlink symTgt =>
          let maxCap := min cap.toNat MAX_READ_BYTES.toNat
          match symTgt with
          | .procMagic _ fdHid? =>
            match fdHid? with
            | some targetHid =>
              match assocGet s.fds targetHid with
              | none => .err Errno.ENOENT
              | some td =>
                if td.closeState == .closeUncertain then
                  if !vn.owner.ownedByUid then .err Errno.EACCES [Errno.ENOENT]
                  else .nondet (.readlinkDynamic maxCap) [Errno.ENOENT]
                else if !vn.owner.ownedByUid then .err Errno.EACCES
                else .nondet (.readlinkDynamic maxCap)
            | none =>
              if !vn.owner.ownedByUid then .err Errno.EACCES
              else .nondet (.readlinkDynamic maxCap)
          | .path targetBytes =>
            if vn.isDynamic then .nondet (.readlinkDynamic maxCap)
            else .ok (.bytes (sliceBytes targetBytes 0 (min targetBytes.size maxCap))) s
        | _ => .err Errno.EINVAL

/-- Evaluate `getdents64` against the target directory stream. -/
def evalGetdents (s : FilesState) (hid : HandleId) (bufBytes : UInt32) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd then .err Errno.EBADF
    else if desc.isExternalStdio then
      let dynDirVn : VNode :=
        { data := .dir { parentIno := desc.ino, lifecycle := .live }, mode := 0o755, nlink := 2, origin := .hostDynamic }
      .nondet (.getdents hid desc dynDirVn bufBytes) [Errno.ENOTDIR, Errno.EBADF, Errno.EINVAL, Errno.ENOENT]
    else
      match assocGet s.inodes desc.ino with
    | none => .err Errno.EBADF
    | some vn =>
      match vn.data with
      | .dir dd =>
        if vn.nlink == 0 || dd.lifecycle.isDead then .err Errno.ENOENT
        else .nondet (.getdents hid desc vn bufBytes)
      | _ => .err Errno.ENOTDIR

/-- Evaluate `fchmod`/`fchmodat` against the resolved inode. -/
def evalChmodNode (s : FilesState) (ino : InodeId) (vn : VNode) (mode : Mode)
    (parentLeaf? : Option (InodeId × ByteArray)) (updateDesc? : Option (HandleId × OpenDesc)) : StepResult :=
  if isReadOnlyMount s vn.mountId then .err Errno.EROFS
  else if vn.kind == .symlink then .err (95 : Errno)
  else if vn.isDynamic && vn.kind == .other then .ok .unit s [Errno.EPERM, Errno.EROFS, (95 : Errno)]
  else if !s.cred.ownerOrCapFowner vn.owner || vn.isPseudo then .err Errno.EPERM
  else if !mountPosixModes s vn.mountId then
    let s' :=
      if vn.kind == .dir then s
      else
        let newMode :=
          if (mode &&& 0o222) == 0 then vn.mode &&& ~~~(0o222 : Mode)
          else vn.mode ||| 0o200
        { s with inodes := assocSet s.inodes ino { vn with mode := newMode, modeExact := false } }
    .ok .unit s' [Errno.EPERM]
  else if vn.mayCopyUp && !isDentryLinked s ino parentLeaf? then
    let recreatedInfo? : Option (InodeId × Bool) :=
      if vn.kind != .dir then none
      else
        match updateDesc?.bind (fun (_, d) => d.lastDentry?) with
        | some (pIno, lf) =>
          match assocGet s.inodes pIno with
          | some pvn =>
            if !pvn.isDeadDir && pvn.nlink > 0 then
              match bytesAssocGet pvn.children lf with
              | some newIno =>
                if newIno != ino then
                  match assocGet s.inodes newIno with
                  | some nvn =>
                    match nvn.data with
                    | .dir ndd =>
                      if !nvn.isDeadDir && nvn.nlink > 0 then some (newIno, ndd.children.isEmpty)
                      else none
                    | _ => none
                  | none => none
                else none
              | none => none
            else none
          | none => none
        | none => none
    match recreatedInfo? with
    | some (_, false) => .err Errno.ENOTEMPTY [Errno.ENOTDIR]
    | some (clobberedIno, true) =>
      let rawMode := mode &&& 0o7777
      let effMode := if !s.cred.inGroupOrCapFsetid vn.owner then rawMode &&& ~~~(0o2000 : Mode) else rawMode
      let vn' := { vn with mode := effMode, modeExact := true }
      let (s', ino') := copyUpInode s ino none vn'
      let sClob := match assocGet s'.inodes clobberedIno with
        | some nvn =>
          let data' := match nvn.data with
            | .dir ndd => .dir { ndd with lifecycle := .unlinked }
            | d => d
          { s' with inodes := assocSet s'.inodes clobberedIno { nvn with data := data', nlink := 0 } }
        | none => s'
      let s'' := match updateDesc? with
        | some (hid, desc) => { sClob with fds := assocSet sClob.fds hid { desc with ino := ino' } }
        | none => sClob
      .ok .unit s'' [Errno.ENOTDIR]
    | none =>
      .err (if vn.kind == .dir then Errno.ENOTDIR else Errno.EEXIST)
  else
    let rawMode := mode &&& 0o7777
    let effMode := if !s.cred.inGroupOrCapFsetid vn.owner then rawMode &&& ~~~(0o2000 : Mode) else rawMode
    let execSealBlocked := match vn.data with
      | .reg rd =>
        match rd.seals with
        | .sealable mask => (mask &&& 0x20) != 0 && ((effMode ^^^ vn.mode) &&& 0o111) != 0
        | .unsealable => false
      | _ => false
    if execSealBlocked then .err Errno.EPERM
    else
      let vn' := { vn with mode := effMode, modeExact := true }
      let (s', ino') := copyUpInode s ino parentLeaf? vn'
      let s'' := match updateDesc? with
        | some (hid, desc) => { s' with fds := assocSet s'.fds hid { desc with ino := ino' } }
        | none => s'
      .ok .unit s''

/-- Evaluate `flock` against the tracked open file descriptors. -/
def evalFlock (s : FilesState) (hid : HandleId) (op : FlockOp) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd then .err Errno.EBADF
    else
      let isDyn := desc.isExternalStdio ||
        ((assocGet s.inodes desc.ino).map (·.isDynamic) |>.getD false)
      let extExtras := if desc.isExternalStdio then [Errno.EBADF] else []
      let clearExtLocks (st : FilesState) (excl : Bool) : FilesState :=
        { st with fds := st.fds.map fun (ohid, odesc) =>
            if ohid != hid && sameFlockTarget st desc odesc && odesc.isExternalStdio &&
                match odesc.lock? with
                | some .exclusive => true
                | some .shared => excl
                | none => false
            then (ohid, { odesc with lock? := none })
            else (ohid, odesc) }
      match op with
    | .unlock => .ok .unit { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) } extExtras
    | .shared nb =>
      let certain := hasCertainConflictingFlock s hid desc false
      let maybes := uncertainConflictingFlocks s hid desc false
      if certain then
        if desc.isExternalStdio then
          let sWinBase := clearExtLocks (maybes.foldl (fun st (ohid, odesc) => closeDescInState st ohid odesc) s) false
          let sWin := { sWinBase with fds := updateSharedDesc sWinBase.fds hid (fun d => { d with lock? := some .shared }) }
          let sLose := { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) }
          .nondet (.flockUncertain sWin sLose nb) extExtras
        else if nb then .err Errno.EAGAIN extExtras (some { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) })
        else .err Errno.EINTR extExtras (some { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) })
      else if !maybes.isEmpty then
        let sClosed := maybes.foldl (fun st (ohid, odesc) => closeDescInState st ohid odesc) s
        let sWin := { sClosed with fds := updateSharedDesc sClosed.fds hid (fun d => { d with lock? := some .shared }) }
        let sOpen1 := match maybes with
          | [(ohid, _)] => clearUncertain s ohid
          | _ => s
        let sLose := { sOpen1 with fds := updateSharedDesc sOpen1.fds hid (fun d => { d with lock? := none }) }
        .nondet (.flockUncertain sWin sLose nb) extExtras
      else .ok .unit { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := some .shared }) }
        ((if isDyn && nb then [Errno.EAGAIN] else []) ++ extExtras)
    | .exclusive nb =>
      let certain := hasCertainConflictingFlock s hid desc true
      let maybes := uncertainConflictingFlocks s hid desc true
      if certain then
        if desc.isExternalStdio then
          let sWinBase := clearExtLocks (maybes.foldl (fun st (ohid, odesc) => closeDescInState st ohid odesc) s) true
          let sWin := { sWinBase with fds := updateSharedDesc sWinBase.fds hid (fun d => { d with lock? := some .exclusive }) }
          let sLose := { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) }
          .nondet (.flockUncertain sWin sLose nb) extExtras
        else if nb then .err Errno.EAGAIN extExtras (some { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) })
        else .err Errno.EINTR extExtras (some { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := none }) })
      else if !maybes.isEmpty then
        let sClosed := maybes.foldl (fun st (ohid, odesc) => closeDescInState st ohid odesc) s
        let sWin := { sClosed with fds := updateSharedDesc sClosed.fds hid (fun d => { d with lock? := some .exclusive }) }
        let sOpen1 := match maybes with
          | [(ohid, _)] => clearUncertain s ohid
          | _ => s
        let sLose := { sOpen1 with fds := updateSharedDesc sOpen1.fds hid (fun d => { d with lock? := none }) }
        .nondet (.flockUncertain sWin sLose nb) extExtras
      else .ok .unit { s with fds := updateSharedDesc s.fds hid (fun d => { d with lock? := some .exclusive }) }
        ((if isDyn && nb then [Errno.EAGAIN] else []) ++ extExtras)

/-- Evaluate `fcntl` against the tracked open file descriptors. -/
def evalFcntl (s : FilesState) (hid : HandleId) (cmd : FcntlCmd) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    match cmd with
    | .getFl =>
      if desc.isExternalStdio then .nondet .getFlExternal
      else .ok (.u32 (encodeOpenStatusFlags desc)) s
    | .setFl nb ap =>
      if desc.isPathFd then .err Errno.EBADF
      else .ok (.u32 0) { s with fds := updateSharedDesc s.fds hid (fun d => { d with nonblock := nb, append := ap }) }
        (if desc.isExternalStdio then [Errno.EBADF] else [])
    | .getFd => .ok (.u32 (if desc.cloexec then 1 else 0)) s
    | .setFd clo => .ok (.u32 0) { s with fds := assocSet s.fds hid { desc with cloexec := clo } }
    | .addSeals seals =>
      if desc.isPathFd then .err Errno.EBADF
      else if desc.isExternalStdio then
        if (seals &&& ~~~(0x3f : UInt32)) != 0 then .err Errno.EINVAL [Errno.EPERM, Errno.EBADF]
        else .ok (.u32 0) s [Errno.EINVAL, Errno.EPERM, Errno.EBADF]
      else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        if desc.access == .rdonly then .err Errno.EPERM
        else if (seals &&& ~~~(0x3f : UInt32)) != 0 then .err Errno.EINVAL
        else
          match vn.data with
          | .reg rd =>
            match rd.seals with
            | .unsealable =>
              let sup := !vn.isPseudo && (mountProfileOf s vn.mountId).supportsSeals
              .err (if sup then Errno.EPERM else Errno.EINVAL) [Errno.EINVAL, Errno.EPERM]
            | .sealable mask =>
              if (mask &&& 1) != 0 then .err Errno.EPERM
              else
                let effSeals :=
                  if (seals &&& 0x20) != 0 && (vn.mode &&& 0o111) != 0 then seals ||| 0x1e
                  else seals
                let vn' := { vn with data := .reg { rd with seals := .sealable (mask ||| effSeals) } }
                .ok (.u32 0) { s with inodes := assocSet s.inodes desc.ino vn' } [Errno.EPERM, Errno.EINVAL]
          | _ => .err Errno.EINVAL [Errno.EPERM]
    | .getSeals =>
      if desc.isPathFd then .err Errno.EBADF
      else if desc.isExternalStdio then .nondet .getSealsExternal [Errno.EINVAL]
      else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        let sup := !vn.isPseudo && (mountProfileOf s vn.mountId).supportsSeals
        match vn.data with
        | .reg rd =>
          match rd.seals with
          | .sealable mask => .ok (.u32 mask) s
          | .unsealable => if sup then .ok (.u32 1) s else .err Errno.EINVAL
        | _ => .err Errno.EINVAL

/-- Evaluate `fsync` against the tracked open file descriptors. -/
def evalFsync (s : FilesState) (hid : HandleId) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd then .err Errno.EBADF
    else if desc.isExternalStdio then .ok .unit s [Errno.EINVAL, Errno.EROFS, Errno.EBADF]
    else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        if vn.kind == .fifo || vn.kind == .charDev || vn.kind == .socket then .err Errno.EINVAL
        else if vn.isPseudo then .ok .unit s [Errno.EINVAL]
        else .ok .unit s

/-- Evaluate `getcwd` against the tracked working-directory state. -/
def evalGetcwd (s : FilesState) (cap : UInt32) : StepResult :=
  let cwdDead := match assocGet s.inodes s.cwdIno with
    | none => true
    | some cvn => cvn.nlink == 0 || cvn.isDeadDir
  if cwdDead then .err Errno.ENOENT
  else
    match s.cwdPath with
    | .bound p =>
      if p.size >= PATH_MAX then .err Errno.ENAMETOOLONG
      else if cap == 0 then .err Errno.EINVAL [Errno.ERANGE]
      else if cap.toNat <= p.size then .err Errno.ERANGE
      else .ok (.bytes p) s
    | .unbound fallback =>
      if cap == 0 then .err Errno.EINVAL [Errno.ERANGE, Errno.ENAMETOOLONG]
      else .nondet (.getcwdUnbound cap fallback)

/-- Evaluate `lseek` against the tracked open file descriptors. -/
def evalLseek (s : FilesState) (hid : HandleId) (offset : Int64) (whence : SeekWhence) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    if desc.isPathFd then .err Errno.EBADF
    else if desc.isExternalStdio then
      .nondet (.lseekDynamic hid desc) [Errno.ESPIPE, Errno.EINVAL, Errno.EBADF, (75 : Errno)]
    else
      match assocGet s.inodes desc.ino with
      | none => .err Errno.EBADF
      | some vn =>
        match vn.data with
        | .fifo _ | .socket => .err Errno.ESPIPE
        | .charDev dk =>
          match dk with
          | .nullDev | .zeroDev | .fullDev => .ok (.u64 0) s
          | _ =>
            if vn.isDynamic then .nondet (.lseekDynamic hid desc) [Errno.ESPIPE, Errno.EINVAL]
            else .err Errno.ESPIPE [Errno.EINVAL]
        | .dir _ =>
          if whence == .seekSet && offset == 0 then
            .ok (.u64 0) { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .dirStream 0 false }) }
          else
            .nondet (.lseekDir hid desc) [Errno.EINVAL, (75 : Errno)]
        | .reg rd =>
          if vn.isDynamic then
            .nondet (.lseekDynamic hid desc) [Errno.EINVAL, Errno.ESPIPE, (75 : Errno)]
          else
            let base : Int := match whence with
              | .seekSet => 0
              | .seekCur => Int.ofNat desc.pos.offset
              | .seekEnd => Int.ofNat rd.size
            let target : Int := base + offset.toInt
            let maxOff : Int := (9223372036854775807 : Int)
            if target < 0 || target > maxOff then
              .err Errno.EINVAL [(75 : Errno)]
            else
              let u := UInt64.ofNat target.toNat
              let extraErrs := if target > (4294967295 : Int) then [Errno.EINVAL, (75 : Errno)] else []
              .ok (.u64 u) { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset target.toNat }) } extraErrs
        | _ =>
          if vn.isDynamic then .nondet (.lseekDynamic hid desc) [Errno.ESPIPE, Errno.EINVAL]
          else .err Errno.EINVAL [Errno.ESPIPE]

/-- Verify whether `/proc` is explicitly modeled (and if so, verify `/proc/self/fd` pseudo-FS traversal). Returns `true` when `/proc` is absent from `s` (unmodeled host `/proc`). -/
private def checkProcFdMount (s : FilesState) : Except Errno Bool :=
  match resolvePath s none (asciiBytes ['/', 'p', 'r', 'o', 'c']) false with
  | .error e => if e == Errno.ENOENT then .ok true else .error e
  | .ok _ =>
    match resolvePath s none (asciiBytes ['/', 'p', 'r', 'o', 'c']) true with
    | .error pe => .error pe
    | .ok procIno =>
      match assocGet s.inodes procIno with
      | none => .error Errno.ENOENT
      | some procVn =>
        if procVn.kind != .dir then .error Errno.ENOTDIR
        else if !procVn.isPseudo then .error Errno.ENOENT
        else
          match resolvePath s none (asciiBytes ['/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 'f', 'd']) true with
          | .error re => .error re
          | .ok fdDirIno =>
            match assocGet s.inodes fdDirIno with
            | none => .error Errno.ENOENT
            | some fdDirVn =>
              if fdDirVn.kind != .dir then .error Errno.ENOTDIR
              else if !hasVNodePermIn s fdDirVn false false true then .error Errno.EACCES
              else if !fdDirVn.isPseudo then .error Errno.ENOENT
              else .ok false

/-- Evaluate `reopenReadOnly` (`open("/proc/thread-self/fd/%d", O_RDONLY | O_CLOEXEC | O_NONBLOCK | O_NOCTTY)`) against `FilesState`. -/
def evalReopenReadOnly (s : FilesState) (hid : HandleId) : StepResult :=
  match assocGet s.fds hid with
  | none => .wrapperErr Errno.EBADF
  | some desc =>
    match checkProcFdMount s with
    | .error re => .err re
    | .ok unmodeledProc =>
        let procErrs := if unmodeledProc then [Errno.ENOENT] else []
        if desc.isExternalStdio then
          let desc' : OpenDesc :=
            { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true,
              dentry? := desc.dentry?, lastDentry? := desc.lastDentry?, isExternalStdio := true }
          .nondet (.reopenExternalStdio desc')
            [Errno.EACCES, Errno.ENXIO, Errno.ELOOP, Errno.ENODEV, Errno.ENOENT,
             Errno.EINVAL, Errno.EOPNOTSUPP, Errno.ESTALE, Errno.EROFS]
        else
          match assocGet s.inodes desc.ino with
          | none => .err Errno.ENOENT
          | some vn =>
            match vn.data with
            | .symlink _ => .err Errno.ELOOP procErrs
            | .dir _ =>
              if !hasVNodePermIn s vn true false false then .err Errno.EACCES procErrs
              else
                let hid' := s.nextHid
                let desc' : OpenDesc :=
                  { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true, pos := .dirStream 0 false,
                    dentry? := desc.dentry?, lastDentry? := desc.lastDentry? }
                let (s1, d') := bindFreeStdioSlot s hid' desc'
                .ok (.opened hid') { s1 with fds := assocSet s1.fds hid' d', nextHid := hid' + 1 } procErrs
            | .socket =>
              if !hasVNodePermIn s vn true false false then .err Errno.EACCES procErrs
              else .err Errno.ENXIO procErrs
            | .charDev dk =>
              match dk with
              | .nullDev | .zeroDev | .fullDev =>
                if !hasVNodePermIn s vn true false false then .err Errno.EACCES procErrs
                else
                  let hid' := s.nextHid
                  let desc' : OpenDesc :=
                    { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true,
                      dentry? := desc.dentry?, lastDentry? := desc.lastDentry? }
                  let (s1, d') := bindFreeStdioSlot s hid' desc'
                  .ok (.opened hid') { s1 with fds := assocSet s1.fds hid' d', nextHid := hid' + 1 } procErrs
              | _ =>
                let hid' := s.nextHid
                let desc' : OpenDesc :=
                  { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true,
                    dentry? := desc.dentry?, lastDentry? := desc.lastDentry? }
                let (s1, d') := bindFreeStdioSlot s hid' desc'
                if vn.isDynamic then
                  .ok (.opened hid') { s1 with fds := assocSet s1.fds hid' d', nextHid := hid' + 1 }
                    ([Errno.EACCES, Errno.ENXIO, Errno.ENODEV] ++ procErrs)
                else .err Errno.ENXIO ([Errno.EACCES, Errno.ENODEV] ++ procErrs)
            | .fifo ring =>
              if !hasVNodePermIn s vn true false false then .err Errno.EACCES procErrs
              else
                let ring' := { ring with readers := ring.readers + 1 }
                let vn' := { vn with data := .fifo ring' }
                let hid' := s.nextHid
                let desc' : OpenDesc :=
                  { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true,
                    dentry? := desc.dentry?, lastDentry? := desc.lastDentry? }
                let (s1, desc'') := bindFreeStdioSlot s hid' desc'
                .ok (.opened hid')
                  { s1 with inodes := assocSet s1.inodes desc.ino vn', fds := assocSet s1.fds hid' desc'', nextHid := hid' + 1 }
                  procErrs
            | _ =>
              if !hasVNodePermIn s vn true false false then .err Errno.EACCES procErrs
              else
                let hid' := s.nextHid
                let desc' : OpenDesc :=
                  { ino := desc.ino, access := .rdonly, cloexec := true, nonblock := true,
                    dentry? := desc.dentry?, lastDentry? := desc.lastDentry? }
                let (s1, desc'') := bindFreeStdioSlot s hid' desc'
                .ok (.opened hid') { s1 with fds := assocSet s1.fds hid' desc'', nextHid := hid' + 1 } procErrs

/-- Evaluate `dupStdio` (`fcntl(slot, F_DUPFD_CLOEXEC, 3)`) against host stdio or managed closed-slot bindings. -/
def evalDupStdio (s : FilesState) (slot : StdioFd) : StepResult :=
  if s.freeStdioSlots.contains slot then .err Errno.EBADF
  else
    match assocGet s.managedStdioMap slot with
    | some baseHid =>
      match assocGet s.fds baseHid with
      | some baseDesc =>
        let newHid := s.nextHid
        let desc' : OpenDesc := { baseDesc with cloexec := true }
        .ok (.opened newHid) { s with fds := assocSet s.fds newHid desc', nextHid := newHid + 1 } [Errno.EINVAL]
      | none => .err Errno.EBADF
    | none => .nondet (.dupStdio slot) [Errno.EINVAL]

private def isExtStdioDirHandle (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (beneathOrInRoot : Bool := false) : Bool :=
  match dir with
  | none => false
  | some hid =>
    match assocGet s.fds hid with
    | none => false
    | some d =>
      d.isExternalStdio && path.size > 0 &&
      (beneathOrInRoot || byteGetD path 0 != slashByte)

/-- Single-source transition core evaluating any `FilesReq` on `FilesState` into `StepResult`. -/
def evalReq (s : FilesState) (req : FilesReq) : StepResult :=
  if precheckNul req then .wrapperErr Errno.EINVAL
  else
    match req with
    | .openat dir path flags mode =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet (.externalStdioOpen flags)
      else evalOpen s dir path flags mode {} false
    | .openat2 dir path how =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else
        let isAbs := path.size > 0 && byteGetD path 0 == slashByte
        if !(isAbs && how.resolve.beneath) && isExtStdioDirHandle s dir path (how.resolve.beneath || how.resolve.inRoot) then
          .nondet (.externalStdioOpen how.flags)
        else evalOpen s dir path how.flags how.mode how.resolve true
    | .close hid =>
      match assocGet s.fds hid with
      | none => .wrapperErr Errno.EBADF
      | some desc => .ok .unit (closeDescInState s hid desc)
    | .read hid maxBytes => evalRead s hid maxBytes
    | .write hid data => evalWrite s hid data
    | .fstat _ => evalStat s req
    | .fstatat dir path flags =>
      if flags.eaccess then .wrapperErr Errno.EINVAL
      else if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet .externalStdioStat
      else evalStat s req
    | .faccessat dir path mask flags =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet .externalStdioUnit
      else evalAccess s dir path mask flags
    | .mkdirat dir path mode =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet .externalStdioUnit
      else evalMkdir s dir path mode
    | .unlinkat dir path removeDir =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet .externalStdioUnit
      else evalUnlink s dir path removeDir
    | .renameat2 oldDir oldPath newDir newPath flags =>
      if !(checkDirHandleOpen s oldDir).isOk || !(checkDirHandleOpen s newDir).isOk then
        .wrapperErr Errno.EBADF
      else if flags.exchange && (flags.noreplace || flags.whiteout) then .err Errno.EINVAL
      else if isExtStdioDirHandle s oldDir oldPath || isExtStdioDirHandle s newDir newPath then
        .nondet .externalStdioUnit
      else evalRename s oldDir oldPath newDir newPath flags
    | .symlinkat target dir linkPath =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if target.size > 0 && target.size < PATH_MAX && isExtStdioDirHandle s dir linkPath then .nondet .externalStdioUnit
      else evalSymlink s target dir linkPath
    | .readlinkat dir path cap =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if cap > 0 && isExtStdioDirHandle s dir path then
        .nondet (.readlinkDynamic (min cap.toNat MAX_READ_BYTES.toNat)) [Errno.ENOTDIR, Errno.ENOENT, Errno.EINVAL, Errno.EACCES, Errno.ELOOP, Errno.ENAMETOOLONG]
      else evalReadlink s dir path cap
    | .getdents64 hid bufBytes => evalGetdents s hid bufBytes
    | .fchmodat dir path mode =>
      if !(checkDirHandleOpen s dir).isOk then .wrapperErr Errno.EBADF
      else if isExtStdioDirHandle s dir path then .nondet .externalStdioUnit
      else
      match resolveLookupOrExt s dir path true with
      | .error re => .err re
      | .ok none => .nondet .externalStdioUnit
      | .ok (some (ino, parentLeaf?, procDesc?)) =>
        match assocGet s.inodes ino with
        | none => .err Errno.ENOENT
        | some vn => evalChmodNode s ino vn mode parentLeaf? procDesc?
    | .fchmod hid mode =>
      match assocGet s.fds hid with
      | none => .wrapperErr Errno.EBADF
      | some desc =>
        if desc.isPathFd then .err Errno.EBADF
        else if desc.isExternalStdio then
          .ok .unit s [Errno.EINVAL, Errno.EPERM, Errno.EROFS, Errno.EBADF, Errno.EACCES, Errno.EOPNOTSUPP]
        else
          match assocGet s.inodes desc.ino with
          | none => .err Errno.EBADF
          | some vn => evalChmodNode s desc.ino vn mode desc.dentry? (some (hid, desc))
    | .flock hid op => evalFlock s hid op
    | .fcntl hid cmd => evalFcntl s hid cmd
    | .fsync hid => evalFsync s hid
    | .getcwd cap => evalGetcwd s cap
    | .lseek hid offset whence => evalLseek s hid offset whence
    | .reopenReadOnly hid => evalReopenReadOnly s hid
    | .dupStdio slot => evalDupStdio s slot

/-- Enumerate `.` , `..` , and child `(name, d_type, d_ino)` entries for directory `vn` (`desc.ino`) in `s`. -/
def getdentsAllEntries (s : FilesState) (desc : OpenDesc) (vn : VNode) :
    List (ByteArray × UInt8 × UInt64) :=
  let childEntries : List (ByteArray × UInt8 × UInt64) :=
    vn.children.map fun (nm, cIno) =>
      let dt := match assocGet s.inodes cIno with
        | some cvn => fileKindToDType cvn.kind
        | none => 0
      (nm, dt, UInt64.ofNat (cIno + 1))
  [(dotBytes, 4, UInt64.ofNat (desc.ino + 1)),
   (dotDotBytes, 4, UInt64.ofNat (vn.parentIno + 1))] ++ childEntries

/-- Drop `cursor` entries from `.` , `..` , and `vn.children` before resolving child `d_type` fields. -/
def getdentsRawDrop (desc : OpenDesc) (vn : VNode) (cursor : Nat) :
    List (ByteArray × Option UInt8 × InodeId) :=
  match cursor with
  | 0 => (dotBytes, some 4, desc.ino) :: (dotDotBytes, some 4, vn.parentIno) ::
      vn.children.map (fun (nm, cIno) => (nm, none, cIno))
  | 1 => (dotDotBytes, some 4, vn.parentIno) ::
      vn.children.map (fun (nm, cIno) => (nm, none, cIno))
  | c + 2 => (vn.children.drop c).map (fun (nm, cIno) => (nm, none, cIno))

/-- Resolve `(name, d_type, d_ino)` for a raw directory entry descriptor. -/
def materializeDirentEntry (s : FilesState) (e : ByteArray × Option UInt8 × InodeId) :
    ByteArray × UInt8 × UInt64 :=
  let dt := match e.2.1 with
    | some k => k
    | none =>
      match assocGet s.inodes e.2.2 with
      | some cvn => fileKindToDType cvn.kind
      | none => 0
  (e.1, dt, UInt64.ofNat (e.2.2 + 1))

/-- Check whether `prev` has the exact same entry names in order as `children`. -/
def sameChildNamesAux : List (ByteArray × Option FileKind) → List (ByteArray × InodeId) → Bool
  | [], [] => true
  | (pnm, _) :: ps, (cnm, _) :: cs => bytesEq pnm cnm && sameChildNamesAux ps cs
  | _, _ => false

/-- Prepend any uncached `(name, kind?)` entries from `children` onto `prev`. -/
def mergeCachedDirChildren (s : FilesState)
    (prev : List (ByteArray × Option FileKind))
    (children : List (ByteArray × InodeId)) : List (ByteArray × Option FileKind) :=
  children.foldl (fun acc (cnm, cIno) =>
    if acc.any (fun (pnm, _) => bytesEq pnm cnm) then acc
    else (cnm, (assocGet s.inodes cIno).map (·.kind)) :: acc) prev

/-- Update cached directory entries from `children` in `O(N)` when names are unchanged. -/
def snapshotDirEntries (s : FilesState)
    (prev : List (ByteArray × Option FileKind))
    (children : List (ByteArray × InodeId)) : List (ByteArray × Option FileKind) :=
  if children.isEmpty then prev
  else if sameChildNamesAux prev.reverse children then prev
  else mergeCachedDirChildren s prev children

/-- Pick one deterministic representative outcome and next state for `act`. -/
def runNondetDefault (s : FilesState) (act : NondetAction) : FilesOutcome × FilesState :=
  match act with
  | .openFifoUncertain sOpen hid _ => (.opened hid, sOpen)
  | .readReg hid desc rd cap =>
    let off := desc.pos.offset
    let avail := if off < rd.size then rd.size - off else 0
    let want := min avail (min cap MAX_READ_BYTES.toNat)
    if want == 0 then (.bytes (ByteArray.mk #[]), s)
    else
      let chunk := rd.readSlice off want
      (.bytes chunk, { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset (off + want) }) })
  | .readZeroDev cap =>
    (.bytes (replicateZeroBytes cap), s)
  | .readDynamic _ _ _ _ _ =>
    (.bytes ByteArray.empty, s)
  | .readFifo ino ring cap _ _ =>
    let want := min cap ring.buf.size
    if want == 0 then (.bytes ByteArray.empty, s)
    else
      let chunk := sliceBytes ring.buf 0 want
      let restBuf := sliceBytes ring.buf want (ring.buf.size - want)
      let ring' := { ring with buf := restBuf, slots := pipeConsumeSlots ring.slots want }
      match assocGet s.inodes ino with
      | some vn => (.bytes chunk, { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } })
      | none => (.bytes chunk, s)
  | .writeReg hid desc ino data stripPriv _ roMount copyUp =>
    if roMount then (.err Errno.EROFS, s)
    else if data.size == 0 then (.u32 0, s)
    else
      match assocGet s.inodes ino with
      | none => (.err Errno.EBADF, s)
      | some vn =>
        let rd := match vn.data with | .reg r => r | _ => {}
        let sealsMask : UInt32 := match rd.seals with | .sealable m => m | .unsealable => 0
        let growSealed := (sealsMask &&& 0x04) != 0
        let pos := if desc.append then rd.size else desc.pos.offset
        if growSealed && pos >= rd.size then
          let mode' := if vn.kind == .reg && stripPriv then
            stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
          let vn' := { vn with
            mode := mode'
            modeExact := if s.ambientSeccomp then false else vn.modeExact }
          (.err Errno.EPERM, { s with inodes := assocSet s.inodes ino vn' })
        else
          let n := if growSealed then min data.size (rd.size - pos) else data.size
          let chunk := sliceBytes data 0 n
          let rd' := rd.writeAt pos chunk
          let mode' := if vn.kind == .reg && stripPriv then
            stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
          let vn' := { vn with
            data := .reg rd'
            mode := mode'
            kernelId := if copyUp then { dev? := none, ino? := none, allowAlias := vn.kernelId.allowAlias } else vn.kernelId
            origin := if copyUp then .managed false else vn.origin }
          (.u32 (UInt32.ofNat n),
            { s with
              inodes := assocSet s.inodes ino vn'
              fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset (pos + n) }) })
  | .writeDiscard len _ _ =>
    (.u32 (UInt32.ofNat len), s)
  | .writeFifo ino ring data nonblock isDyn =>
    let (minR, maxR, _, _) := fifoCounts s ino ring
    let (_, canW) := pipeWriteSlots ring.slots ring.capacity.minPages data.size
    let (_, maxAllow) := pipeWriteSlots ring.slots ring.capacity.maxPages data.size
    let n := if isDyn then data.size else min data.size (if !nonblock && canW == 0 then maxAllow else canW)
    let bound := if isDyn then data.size else min data.size maxAllow
    if !isDyn && maxR == 0 then
      (.err Errno.EPIPE, if s.ambientSeccomp then s else resolveUncertainFifo s ino true true)
    else if !isDyn && nonblock && n == 0 then
      let s1 :=
        if s.ambientSeccomp then s
        else
          let ring' := { ring with capacity := .exact ring.slots.length }
          match assocGet s.inodes ino with
          | some vn => { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } }
          | none => s
      (.err Errno.EAGAIN, s1)
    else if n == 0 then
      (.err Errno.EINTR, s)
    else
      let chunk := sliceBytes data 0 n
      let (slots', _) := pipeWriteSlots ring.slots ring.capacity.maxPages n
      let cap' :=
        if !isDyn && nonblock && n < bound then
          PipeCapacity.exact (max ring.capacity.minPages slots'.length)
        else
          match ring.capacity with
          | .exact p => .exact p
          | .uncalibrated lo hi => .uncalibrated (max lo slots'.length) hi
      let ring' := { ring with buf := ring.buf ++ chunk, slots := slots', capacity := cap' }
      let s1 := match assocGet s.inodes ino with
        | some vn => { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } }
        | none => s
      (.u32 (UInt32.ofNat n), if !isDyn && minR == 0 then resolveUncertainFifo s1 ino true false else s1)
  | .statNode ino vn =>
    let st := mkStatFromVNode ino vn
    let vn' := { vn with kernelId := { dev? := some st.dev, ino? := some st.ino, allowAlias := vn.kernelId.allowAlias } }
    (.statted st, { s with inodes := assocSet s.inodes ino vn' })
  | .readlinkDynamic _ => (.bytes (ByteArray.mk #[]), s)
  | .getdents hid desc vn bufBytes =>
    let cap := min bufBytes.toNat MAX_READ_BYTES.toNat
    let totalEntries := vn.children.length + 2
    let snapMax := max desc.dirCachedMaxReclen
      (vn.children.foldl (fun mx (nm, _) => max mx (dirent64Reclen nm)) 0)
    let snapEntries := snapshotDirEntries s desc.dirCachedEntries vn.children
    if desc.pos.dirAtEof then (.bytes (ByteArray.mk #[]), s)
    else if cap < 24 then
      if desc.pos.dirCursor >= 2 then
        (.bytes (ByteArray.mk #[]), { s with fds := updateSharedDesc s.fds hid (fun d =>
          { d with pos := .dirStream (max desc.pos.dirCursor totalEntries) true,
                   dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) })
      else
        (.err Errno.EINVAL, { s with fds := updateSharedDesc s.fds hid (fun d =>
          { d with dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) })
    else
      let remRaw := getdentsRawDrop desc vn desc.pos.dirCursor
      match remRaw with
      | [] =>
        (.bytes (ByteArray.mk #[]), { s with fds := updateSharedDesc s.fds hid (fun d =>
          { d with pos := .dirStream (max desc.pos.dirCursor totalEntries) true,
                   dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) })
      | first :: _ =>
        if dirent64Reclen first.1 > cap then
          (.err Errno.EINVAL, { s with fds := updateSharedDesc s.fds hid (fun d =>
            { d with dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) })
        else
          let packedRaw := packFittingDirentsGen Prod.fst remRaw cap
          let packed := packedRaw.map (materializeDirentEntry s)
          let stub := mkTypedDirentStub packed
          (.bytes stub, { s with fds := updateSharedDesc s.fds hid (fun d =>
            { d with pos := .dirStream (desc.pos.dirCursor + packed.length) false,
                     dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) })
  | .flockUncertain sWin _ _ => (.unit, sWin)
  | .getcwdUnbound cap fallback =>
    if cap.toNat <= fallback.size then (.err Errno.ERANGE, s)
    else (.bytes fallback, { s with cwdPath := .bound fallback })
  | .lseekDir hid _ =>
    (.u64 0, { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .dirStream 0 false }) })
  | .lseekDynamic hid desc =>
    let pos0 := match desc.pos with
      | .byteOffset _ => FilePos.byteOffset 0
      | .dirStream _ _ => FilePos.dirStream 0 false
    (.u64 0, { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := pos0 }) })
  | .dupStdio _ =>
    let newIno := s.nextIno
    let newHid := s.nextHid
    let vn : VNode :=
      { data := .other, mode := 0o600, nlink := 1,
        kernelId := { allowAlias := true }, origin := .hostDynamic }
    let desc : OpenDesc := { ino := newIno, access := .rdwr, cloexec := true, isExternalStdio := true }
    (.opened newHid,
      { s with
        inodes := assocSet s.inodes newIno vn
        fds := assocSet s.fds newHid desc
        nextIno := newIno + 1
        nextHid := newHid + 1 })
  | .reopenExternalStdio desc' =>
    let newHid := s.nextHid
    let (s1, d'') := bindFreeStdioSlot s newHid desc'
    (.opened newHid, { s1 with fds := assocSet s1.fds newHid d'', nextHid := max s1.nextHid (newHid + 1) })
  | .getFlExternal =>
    (.u32 0, s)
  | .getSealsExternal =>
    (.u32 0, s)
  | .externalStdioOpen _ | .externalStdioStat | .externalStdioUnit =>
    (.err Errno.ENOTDIR, s)

/-- Byte-array index loop verifying every byte is `0x00` without materializing a `List UInt8`. -/
def allBytesZeroLoop (b : ByteArray) (i : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 =>
    if h : i < b.size then
      if b[i] != 0 then false else allBytesZeroLoop b (i + 1) rem
    else true

private theorem replicateZeroBytesLoop_get (n : Nat) (acc : ByteArray)
    (hAcc : ∀ j (hj : j < acc.size), acc[j] = 0) :
    ∀ i (hi : i < (replicateZeroBytesLoop n acc).size), (replicateZeroBytesLoop n acc)[i] = 0 := by
  induction n generalizing acc with
  | zero => exact hAcc
  | succ k ih =>
    apply ih (acc.push 0)
    intro j hj
    show (acc.data.push 0)[j] = 0
    by_cases hLt : j < acc.data.size
    · rw [Array.getElem_push_lt hLt]; exact hAcc j hLt
    · have hEq : j = acc.data.size := by
        have hj' : j < (acc.data.push 0).size := hj
        rw [Array.size_push] at hj'
        omega
      subst hEq
      exact Array.getElem_push_eq

/-- Replicating `0x00` via `replicateZeroBytes` satisfies `allBytesZeroLoop`. -/
theorem allBytesZeroLoop_replicate_zero (cap : Nat) :
    ∀ rem i : Nat, allBytesZeroLoop (replicateZeroBytes cap) i rem = true
  | 0, _ => rfl
  | rem + 1, i => by
    unfold allBytesZeroLoop
    split
    · rename_i h
      have hElem : (replicateZeroBytes cap)[i] = (0 : UInt8) :=
        replicateZeroBytesLoop_get cap (ByteArray.emptyWithCapacity cap)
          (fun _ hj => absurd hj (Nat.not_lt_zero _)) i h
      simp only [hElem, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact allBytesZeroLoop_replicate_zero cap rem (i + 1)
    · rfl

/-- Validate a nondeterministic outcome `out` against `act` and return the updated `FilesState`. -/
def verifyNondet (s : FilesState) (act : NondetAction) (out : FilesOutcome) : Option FilesState :=
  match act with
  | .openFifoUncertain sOpen hid sClose =>
    match out with
    | .opened h => if h == hid then some sOpen else none
    | .err e => if e == Errno.ENXIO then some sClose else none
    | _ => none
  | .readReg hid desc rd cap =>
    match out with
    | .bytes got =>
      let avail := if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0
      let want := min cap avail
      if want == 0 then (if got.size == 0 then some s else none)
      else if got.size >= 1 && got.size <= want &&
          bytesEq got (rd.readSlice desc.pos.offset got.size) then
        some { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset (desc.pos.offset + got.size) }) }
      else none
    | _ => none
  | .readZeroDev cap =>
    match out with
    | .bytes got =>
      if got.size <= cap && (cap == 0 || got.size >= 1) &&
          allBytesZeroLoop got 0 got.size then some s
      else none
    | _ => none
  | .readDynamic hid desc cap nonblock isCharDev =>
    match out with
    | .bytes got =>
      if got.size == 0 then some s
      else if got.size <= cap then
        let off' := if isCharDev then desc.pos.offset else desc.pos.offset + got.size
        some { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset off' }) }
      else none
    | .err e =>
      if isCharDev && ((nonblock && e == Errno.EAGAIN) || e == Errno.EINVAL || e == Errno.ENXIO || e == Errno.ENODEV) then
        some s
      else none
    | _ => none
  | .readFifo ino ring cap nonblock isDynamic =>
    if ring.buf.size == 0 then
      match out with
      | .bytes got =>
        if got.size == 0 || (isDynamic && got.size <= cap) then some s else none
      | .err e =>
        if isDynamic && nonblock && e == Errno.EAGAIN then some s else none
      | _ => none
    else
      match out with
      | .bytes got =>
        let want := min cap ring.buf.size
        if want == 0 then (if got.size == 0 then some s else none)
        else if got.size >= 1 && got.size <= want &&
            bytesEq got (sliceBytes ring.buf 0 got.size) then
          let restBuf := sliceBytes ring.buf got.size (ring.buf.size - got.size)
          let ring' := { ring with buf := restBuf, slots := pipeConsumeSlots ring.slots got.size }
          match assocGet s.inodes ino with
          | some vn => some { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } }
          | none => some s
        else none
      | _ => none
  | .writeReg hid desc ino data stripPriv isOverlay roMount copyUp =>
    match out with
    | .u32 n32 =>
      let n := n32.toNat
      if data.size == 0 then (if n == 0 then some s else none)
      else
        match assocGet s.inodes ino with
        | none => none
        | some vn =>
          let rd := match vn.data with | .reg r => r | _ => {}
          let sealsMask : UInt32 := match rd.seals with | .sealable m => m | .unsealable => 0
          let growSealed := (sealsMask &&& 0x04) != 0
          let pos := if desc.append then rd.size else desc.pos.offset
          let maxAllow := if growSealed then min data.size (rd.size - pos) else data.size
          if n >= 1 && n <= maxAllow then
            let chunk := sliceBytes data 0 n
            let rd' := rd.writeAt pos chunk
            let mode' := if vn.kind == .reg && stripPriv then
            stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
            let vn' := { vn with
              data := .reg rd'
              mode := mode'
              kernelId := if copyUp then { dev? := none, ino? := none, allowAlias := vn.kernelId.allowAlias } else vn.kernelId
              origin := if copyUp then .managed false else vn.origin }
            some { s with
              inodes := assocSet s.inodes ino vn'
              fds := updateSharedDesc s.fds hid (fun d => { d with pos := .byteOffset (pos + n) }) }
          else none
    | .err e =>
      if roMount && e == Errno.EROFS then some s
      else if data.size > 0 && e == Errno.EFBIG then
        if isOverlay then
          match assocGet s.inodes ino with
          | none => some s
          | some vn =>
            let mode' := if stripPriv then
              stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
            let vn' := { vn with
              mode := mode'
              kernelId := if copyUp then { dev? := none, ino? := none, allowAlias := vn.kernelId.allowAlias } else vn.kernelId
              origin := if copyUp then .managed false else vn.origin }
            some { s with inodes := assocSet s.inodes ino vn' }
        else some s
      else if data.size > 0 && e == Errno.EPERM then
        match assocGet s.inodes ino with
        | none => none
        | some vn =>
          let rd := match vn.data with | .reg r => r | _ => {}
          let sealsMask : UInt32 := match rd.seals with | .sealable m => m | .unsealable => 0
          let growSealed := (sealsMask &&& 0x04) != 0
          let pos := if desc.append then rd.size else desc.pos.offset
          if growSealed && pos + data.size > rd.size then
            let mode' := if vn.kind == .reg && stripPriv then
              stripPrivBitsExt (!s.cred.inGroupOrCapFsetid vn.owner) vn.mode else vn.mode
            let vn' := { vn with
              mode := mode'
              modeExact := if s.ambientSeccomp then false else vn.modeExact }
            some { s with inodes := assocSet s.inodes ino vn' }
          else none
      else none
    | _ => none
  | .writeDiscard len extraErrs nonblockEagain =>
    match out with
    | .u32 n32 =>
      let n := n32.toNat
      if len == 0 then (if n == 0 then some s else none)
      else if n >= 1 && n <= len then some s else none
    | .err e =>
      if (nonblockEagain && e == Errno.EAGAIN) || extraErrs.contains e then some s else none
    | _ => none
  | .writeFifo ino ring data nonblock isDyn =>
    let (minR, _, _, _) := fifoCounts s ino ring
    let (_, maxAllow) := pipeWriteSlots ring.slots ring.capacity.maxPages data.size
    match out with
    | .u32 n32 =>
      let n := n32.toNat
      let bound := if isDyn then data.size else min data.size maxAllow
      if n >= 1 && n <= bound then
        let chunk := sliceBytes data 0 n
        let (slots', _) := pipeWriteSlots ring.slots ring.capacity.maxPages n
        let cap' :=
          if !isDyn && nonblock && n < bound then
            PipeCapacity.exact (max ring.capacity.minPages slots'.length)
          else
            match ring.capacity with
            | .exact p => .exact p
            | .uncalibrated lo hi => .uncalibrated (max lo slots'.length) hi
        let ring' := { ring with buf := ring.buf ++ chunk, slots := slots', capacity := cap' }
        let s1 := match assocGet s.inodes ino with
          | some vn => { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } }
          | none => s
        some (if !isDyn && minR == 0 then resolveUncertainFifo s1 ino true false else s1)
      else none
    | .err e =>
      if e == Errno.EPIPE && !isDyn && minR == 0 then
        some (if s.ambientSeccomp then s else resolveUncertainFifo s ino true true)
      else if !isDyn && nonblock && e == Errno.EAGAIN then
        if s.ambientSeccomp then some s
        else
          let minP := ring.capacity.minPages
          let (_, curCanW) := pipeWriteSlots ring.slots ring.slots.length data.size
          if ring.slots.length >= minP && (curCanW == 0 || (data.size <= 4096 && curCanW < data.size)) then
            let ring' := { ring with capacity := .exact ring.slots.length }
            match assocGet s.inodes ino with
            | some vn => some { s with inodes := assocSet s.inodes ino { vn with data := .fifo ring' } }
            | none => some s
          else none
      else none
    | _ => none
  | .statNode ino vn =>
    match out with
    | .statted st =>
      if checkStatMatchInState s ino vn st then
        let vn' := { vn with kernelId := { dev? := some st.dev, ino? := some st.ino, allowAlias := vn.kernelId.allowAlias } }
        some { s with inodes := assocSet s.inodes ino vn' }
      else none
    | _ => none
  | .readlinkDynamic cap =>
    match out with
    | .bytes got => if got.size <= cap then some s else none
    | _ => none
  | .getdents hid desc vn bufBytes =>
    let totalEntries := vn.children.length + 2
    let snapMax := max desc.dirCachedMaxReclen
      (vn.children.foldl (fun mx (nm, _) => max mx (dirent64Reclen nm)) 0)
    let snapEntries := snapshotDirEntries s desc.dirCachedEntries vn.children
    if desc.pos.dirAtEof then
      match out with
      | .bytes got => if got.size == 0 then some s else none
      | _ => none
    else if bufBytes.toNat < 24 then
      match out with
      | .bytes got =>
        if (desc.pos.dirCursor >= 2 || desc.isExternalStdio || bufBytes == 0) && got.size == 0 then
          some { s with fds := updateSharedDesc s.fds hid (fun d =>
            { d with pos := .dirStream (max desc.pos.dirCursor totalEntries) true,
                     dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) }
        else none
      | .err e =>
        if e == Errno.EINVAL then
          some { s with fds := updateSharedDesc s.fds hid (fun d =>
            { d with dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) }
        else none
      | _ => none
    else
      let cap := min bufBytes.toNat MAX_READ_BYTES.toNat
      let hasTooSmallBuf :=
        vn.isDynamic || desc.dirCachedMaxReclen > cap ||
        vn.children.any fun (name, _) => dirent64Reclen name > cap
      match out with
      | .bytes got =>
        let cap := min bufBytes.toNat MAX_READ_BYTES.toNat
        if got.size == 0 then
          if desc.pos.dirCursor >= 2 || desc.isExternalStdio then
            some { s with fds := updateSharedDesc s.fds hid (fun d =>
              { d with pos := .dirStream (max desc.pos.dirCursor totalEntries) true,
                       dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) }
          else none
        else if got.size >= 24 && got.size <= cap then
          match parseDirents64Strict got with
          | some ents =>
            let entriesOk :=
              vn.isDynamic ||
              ents.all fun (nm, dt) =>
                ((bytesEq nm dotBytes || bytesEq nm dotDotBytes) && (dt == 0 || dt == 4)) ||
                vn.children.any (fun (cnm, cIno) =>
                  bytesEq cnm nm &&
                  (dt == 0 ||
                    match assocGet s.inodes cIno with
                    | some cvn => dt == fileKindToDType cvn.kind
                    | none => true)) ||
                desc.dirCachedEntries.any (fun (cnm, k?) =>
                  bytesEq cnm nm &&
                  (dt == 0 ||
                    match k? with
                    | some k => dt == fileKindToDType k
                    | none => true))
            if ents.length >= 1 && entriesOk then
              some { s with fds := updateSharedDesc s.fds hid (fun d =>
                { d with pos := .dirStream (desc.pos.dirCursor + ents.length) false,
                         dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) }
            else none
          | none => none
        else none
      | .err e =>
        if hasTooSmallBuf && e == Errno.EINVAL then
          some { s with fds := updateSharedDesc s.fds hid (fun d =>
            { d with dirCachedMaxReclen := snapMax, dirCachedEntries := snapEntries }) }
        else none
      | _ => none
  | .flockUncertain sWin sLose nb =>
    match out with
    | .unit => some sWin
    | .err e => if (nb && e == Errno.EAGAIN) || (!nb && e == Errno.EINTR) then some sLose else none
    | _ => none
  | .getcwdUnbound cap _ =>
    match out with
    | .bytes got =>
      if ((got.size > 0 && byteGetD got 0 == slashByte) || startsWithBytes got unreachablePrefix) &&
          !hasEmbeddedNul got &&
          got.size < min cap.toNat MAX_READ_BYTES.toNat && got.size < PATH_MAX then
        some { s with cwdPath := .bound got }
      else none
    | .err e =>
      if (e == Errno.ERANGE && cap.toNat < PATH_MAX) || e == Errno.ENAMETOOLONG then some s else none
    | _ => none
  | .lseekDir hid desc =>
    match out with
    | .u64 cookie =>
      let cur := if cookie == 0 then 0 else max 2 desc.pos.dirCursor
      some { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := .dirStream cur false }) }
    | _ => none
  | .lseekDynamic hid desc =>
    match out with
    | .u64 off =>
      if off.toNat < 9223372036854775808 then
        let pos' := match desc.pos with
          | .byteOffset _ => FilePos.byteOffset off.toNat
          | .dirStream _ _ => FilePos.dirStream (if off == 0 then 0 else max 2 desc.pos.dirCursor) false
        some { s with fds := updateSharedDesc s.fds hid (fun d => { d with pos := pos' }) }
      else none
    | _ => none
  | .dupStdio _ =>
    match out with
    | .opened hid =>
      let newIno := s.nextIno
      let vn : VNode :=
        { data := .other, mode := 0o600, nlink := 1,
          kernelId := { allowAlias := true }, origin := .hostDynamic }
      let desc : OpenDesc := { ino := newIno, access := .rdwr, cloexec := true, isExternalStdio := true }
      some { s with
        inodes := assocSet s.inodes newIno vn
        fds := assocSet s.fds hid desc
        nextIno := newIno + 1
        nextHid := max s.nextHid (hid + 1) }
    | _ => none
  | .reopenExternalStdio desc' =>
    match out with
    | .opened hid =>
      let (s1, d'') := bindFreeStdioSlot s hid desc'
      some { s1 with fds := assocSet s1.fds hid d'', nextHid := max s1.nextHid (hid + 1) }
    | _ => none
  | .getFlExternal =>
    match out with
    | .u32 v =>
      if (v &&& ~~~(0x123 : UInt32)) == 0 && (v &&& 3) != 3 then some s else none
    | _ => none
  | .getSealsExternal =>
    match out with
    | .u32 v =>
      if (v &&& ~~~(0x3f : UInt32)) == 0 then some s else none
    | _ => none
  | .externalStdioOpen flags =>
    match out with
    | .opened hid =>
      let newIno := s.nextIno
      let vn : VNode :=
        { data := .other, mode := 0o600, nlink := 1,
          kernelId := { allowAlias := true }, origin := .hostDynamic }
      let desc : OpenDesc :=
        { ino := newIno, access := if flags.path then .rdonly else flags.access,
          append := if flags.path then false else flags.append,
          nonblock := if flags.path then false else flags.nonblock,
          cloexec := flags.cloexec, isPathFd := flags.path, isExternalStdio := true }
      let (s1, d'') := bindFreeStdioSlot s hid desc
      some { s1 with
        inodes := assocSet s1.inodes newIno vn
        fds := assocSet s1.fds hid d''
        nextIno := newIno + 1
        nextHid := max s1.nextHid (hid + 1) }
    | .err e =>
      if e != Errno.EFAULT then some s else none
    | _ => none
  | .externalStdioStat =>
    match out with
    | .statted st =>
      if st.mtimeNsec < 1000000000 && st.atimeNsec < 1000000000 then some s else none
    | .err e => if e != Errno.EFAULT then some s else none
    | _ => none
  | .externalStdioUnit =>
    match out with
    | .unit => some s
    | .err e => if e != Errno.EFAULT then some s else none
    | _ => none

/-- Deterministic transition evaluator derived directly from `evalReq`. -/
def evalModel (s : FilesState) (req : FilesReq) : FilesOutcome × FilesState :=
  match evalReq s req with
  | .wrapperErr e => (.err e, s)
  | .err e _ st? => (.err e, st?.getD s)
  | .ok out next _ => (out, next)
  | .nondet act _ => runNondetDefault s act

/-- Boolean equality on `FilesOutcome`. -/
def outcomeEq : FilesOutcome → FilesOutcome → Bool
  | .unit, .unit => true
  | .opened a, .opened b => a == b
  | .bytes a, .bytes b => bytesEq a b
  | .u32 a, .u32 b => a == b
  | .u64 a, .u64 b => a == b
  | .statted a, .statted b => a == b
  | .err a, .err b => a == b
  | _, _ => false

/-- Relational step verifier derived directly from `evalReq`. -/
def verifyStep (s : FilesState) (res : StepResult) (out : FilesOutcome) : Option FilesState :=
  match res with
  | .wrapperErr want =>
    if isOutcomeErr out want then some s else none
  | .err primary alts st? =>
    match out with
    | .err e =>
      if e == primary then some (st?.getD s)
      else if alts.contains e then some s
      else if Errno.isTransientOsErrno e then some s
      else none
    | _ => none
  | .ok wantOut next extraErrs =>
    if outcomeEq out wantOut then some next
    else
      match out with
      | .err e =>
        if extraErrs.contains e || Errno.isTransientOsErrno e then some s else none
      | _ => none
  | .nondet act extraErrs =>
    match verifyNondet s act out with
    | some s' => some s'
    | none =>
      match out with
      | .err e =>
        if extraErrs.contains e || Errno.isTransientOsErrno e then some s else none
      | _ => none

/-- Return `true` iff `StepResult` represents a pre-syscall wrapper error. -/
def StepResult.isWrapperErr : StepResult → Bool
  | .wrapperErr _ => true
  | _ => false

/-- Return the direct file descriptor referenced by `req`, if any. -/
def directHid? : FilesReq → Option HandleId
  | .read hid _ | .write hid _ | .fstat hid | .getdents64 hid _
  | .fchmod hid _ | .flock hid _ | .fcntl hid _ | .fsync hid
  | .lseek hid _ _ | .reopenReadOnly hid => some hid
  | _ => none

/-- Return all directory handles referenced by an `*at` request `req`. -/
def candidateDirFds : FilesReq → List HandleId
  | .openat dir _ _ _ | .openat2 dir _ _ | .fstatat dir _ _
  | .faccessat dir _ _ _ | .mkdirat dir _ _ | .unlinkat dir _ _
  | .symlinkat _ dir _ | .readlinkat dir _ _ | .fchmodat dir _ _ =>
    match dir with | some h => [h] | none => []
  | .renameat2 d1 _ d2 _ _ =>
    (match d1 with | some h => [h] | none => []) ++
    (match d2 with | some h => [h] | none => [])
  | _ => []

/-- Verify `(req, out)` on `s` including optional ambient `seccomp` fallback for non-wrapper errors. -/
def verifyWithSeccomp (s : FilesState) (req : FilesReq) (out : FilesOutcome) : Option FilesState :=
  let res := evalReq s req
  match verifyStep s res out with
  | some s' => some s'
  | none =>
    if s.ambientSeccomp && !res.isWrapperErr then
      match out with
      | .err e => if Errno.isSafeSeccompErrno e then some s else none
      | _ => none
    else none

/-- Verify a `close` step under `LeanFdBox` pinning and optional ambient `seccomp`. -/
def allowedCloseStep (s : FilesState) (hid : HandleId) (out : FilesOutcome) : Option FilesState :=
  match assocGet s.fds hid with
  | none => verifyStep s (.wrapperErr Errno.EBADF) out
  | some desc =>
    match out with
    | .unit => some (closeDescInState s hid desc)
    | .err e =>
      if e == Errno.EBUSY then
        some (clearUncertain s hid)
      else if isKernelCloseErr e then
        if e == Errno.EBADF && !s.ambientSeccomp then none
        else some (closeDescInState s hid desc)
      else if s.ambientSeccomp && Errno.isSafeSeccompErrno e then
        some (clearUncertain s hid)
      else none
    | _ => none

/-- Return `true` iff erasing uncertain handle `hid` makes `evalReq` return `.wrapperErr EBADF` or `.err EBADF`. -/
def dirFdErasingMakesEbadf (s : FilesState) (req : FilesReq) (hid : HandleId) : Bool :=
  let s' := { s with fds := assocErase s.fds hid }
  match evalReq s' req with
  | .wrapperErr e | .err e _ _ => e == Errno.EBADF
  | _ => false

/-- Relational step verifier for all 23 curated `Files` syscalls: returns `some s'` iff `out` is permitted from `s` on `req`. -/
def allowedStep (s : FilesState) (req : FilesReq) (out : FilesOutcome) : Option FilesState :=
  match req with
  | .close hid => allowedCloseStep s hid out
  | .dupStdio _ =>
    if !s.ambientSeccomp && isOutcomeErr out Errno.ENOSPC then none
    else verifyWithSeccomp s req out
  | _ =>
    match directHid? req with
    | some hid =>
      match assocGet s.fds hid with
      | some desc =>
        if desc.closeState == .closeUncertain then
          if isOutcomeErr out Errno.EBADF then some s
          else (verifyWithSeccomp s req out).map (clearUncertain · hid)
        else verifyWithSeccomp s req out
      | none => verifyWithSeccomp s req out
    | none =>
      let uncDirs := (candidateDirFds req).filter fun h =>
        match assocGet s.fds h with
        | some d => d.closeState == .closeUncertain
        | none => false
      if uncDirs.isEmpty then verifyWithSeccomp s req out
      else
        let res := evalReq s req
        if res.isWrapperErr then verifyStep s res out
        else if isOutcomeErr out Errno.EBADF then
          let canTriggerEbadf :=
            (verifyStep s res out).isSome ||
            uncDirs.any (dirFdErasingMakesEbadf s req)
          if canTriggerEbadf then some s else none
        else
          match verifyStep s res out with
          | some s' =>
            let isNonTransient := match out with
              | .err e => !Errno.isTransientOsErrno e
              | _ => true
            if isNonTransient then
              some (uncDirs.foldl (fun st h =>
                if dirFdErasingMakesEbadf s req h then clearUncertain st h else st) s')
            else some s'
          | none =>
            if s.ambientSeccomp then
              match out with
              | .err e => if Errno.isSafeSeccompErrno e then some s else none
              | _ => none
            else none

/-- Execute `evalModel` in `StateM FilesState`, returning `(outcome, nextState)`. -/
def runOp (req : FilesReq) : StateM FilesState (FilesOutcome × FilesState) := do
  let s ← get
  let (out, s') := evalModel s req
  set s'
  return (out, s')

/-- Deterministic reference `StateM FilesState` implementation projected from `evalModel` for all 23 `Files` syscalls. -/
def modelOps : FilesOpsM (StateM FilesState) HandleId :=
  { openat := fun dir path flags mode => do
      let (out, _) ← runOp (.openat dir path flags mode)
      match out with | .opened h => return .ok h | .err e => return .error e | _ => return .error Errno.EIO
    openat2 := fun dir path how => do
      let (out, _) ← runOp (.openat2 dir path how)
      match out with | .opened h => return .ok h | .err e => return .error e | _ => return .error Errno.EIO
    close := fun hid => do
      let (out, _) ← runOp (.close hid)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    read := fun hid maxBytes => do
      let (out, _) ← runOp (.read hid maxBytes)
      match out with | .bytes bs => return .ok bs | .err e => return .error e | _ => return .error Errno.EIO
    write := fun hid data => do
      let (out, _) ← runOp (.write hid data)
      match out with | .u32 n => return .ok n | .err e => return .error e | _ => return .error Errno.EIO
    fstat := fun hid => do
      let (out, _) ← runOp (.fstat hid)
      match out with | .statted st => return .ok st | .err e => return .error e | _ => return .error Errno.EIO
    fstatat := fun dir path flags => do
      let (out, _) ← runOp (.fstatat dir path flags)
      match out with | .statted st => return .ok st | .err e => return .error e | _ => return .error Errno.EIO
    faccessat := fun dir path mask flags => do
      let (out, _) ← runOp (.faccessat dir path mask flags)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    mkdirat := fun dir path mode => do
      let (out, _) ← runOp (.mkdirat dir path mode)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    unlinkat := fun dir path removeDir => do
      let (out, _) ← runOp (.unlinkat dir path removeDir)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    renameat2 := fun od op nd np fl => do
      let (out, _) ← runOp (.renameat2 od op nd np fl)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    symlinkat := fun tgt dir lp => do
      let (out, _) ← runOp (.symlinkat tgt dir lp)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    readlinkat := fun dir path cap => do
      let (out, _) ← runOp (.readlinkat dir path cap)
      match out with | .bytes bs => return .ok bs | .err e => return .error e | _ => return .error Errno.EIO
    getdents64 := fun hid bufBytes => do
      let (out, _) ← runOp (.getdents64 hid bufBytes)
      match out with | .bytes bs => return .ok bs | .err e => return .error e | _ => return .error Errno.EIO
    fchmodat := fun dir path mode => do
      let (out, _) ← runOp (.fchmodat dir path mode)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    fchmod := fun hid mode => do
      let (out, _) ← runOp (.fchmod hid mode)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    flock := fun hid op => do
      let (out, _) ← runOp (.flock hid op)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    fcntl := fun hid cmd => do
      let (out, _) ← runOp (.fcntl hid cmd)
      match out with | .u32 v => return .ok v | .err e => return .error e | _ => return .error Errno.EIO
    fsync := fun hid => do
      let (out, _) ← runOp (.fsync hid)
      match out with | .unit => return .ok () | .err e => return .error e | _ => return .error Errno.EIO
    getcwd := fun cap => do
      let (out, _) ← runOp (.getcwd cap)
      match out with | .bytes bs => return .ok bs | .err e => return .error e | _ => return .error Errno.EIO
    lseek := fun hid off w => do
      let (out, _) ← runOp (.lseek hid off w)
      match out with | .u64 v => return .ok v | .err e => return .error e | _ => return .error Errno.EIO
    reopenReadOnly := fun hid => do
      let (out, _) ← runOp (.reopenReadOnly hid)
      match out with | .opened h => return .ok h | .err e => return .error e | _ => return .error Errno.EIO
    dupStdio := fun slot => do
      let (out, _) ← runOp (.dupStdio slot)
      match out with | .opened h => return .ok h | .err e => return .error e | _ => return .error Errno.EIO }

/-- Attach or update a live `/proc/self/fd/<name>` magic link pointing to `tgtIno` and descriptor `hid`. -/
def FilesState.attachProcFdLink (s : FilesState) (fdName : ByteArray) (tgtIno : InodeId)
    (hid : HandleId) (mode : Mode := 0o777) : FilesState :=
  match resolvePath s none "/proc/self/fd".toUTF8 true with
  | .error _ => s
  | .ok fdDirIno =>
    match assocGet s.inodes fdDirIno with
    | some dirVn =>
      match dirVn.data with
      | .dir dd =>
        match bytesAssocGet dd.children fdName with
        | some exIno =>
          match assocGet s.inodes exIno with
          | some exVn =>
            let exVn' :=
              { exVn with
                data := .symlink (.procMagic tgtIno (some hid))
                mode := mode
                nlink := 1
                kernelId := { dev? := none, ino? := none, allowAlias := true } }
            { s with inodes := assocSet s.inodes exIno exVn' }
          | none => s
        | none =>
          let newIno := s.nextIno
          let linkVn : VNode :=
            { data := .symlink (.procMagic tgtIno (some hid)), mode := mode, mountId := dirVn.mountId,
              origin := .pseudoFs, kernelId := { allowAlias := true },
              owner := dirVn.owner, nlink := 1 }
          let dirVn' := { dirVn with data := .dir { dd with children := bytesAssocSet dd.children fdName newIno } }
          { s with
            inodes := assocSet (assocSet s.inodes fdDirIno dirVn') newIno linkVn
            nextIno := newIno + 1 }
      | _ => s
    | none => s

/-- Remove a `/proc/self/fd/<name>` magic link upon descriptor close. -/
def FilesState.detachProcFdLink (s : FilesState) (fdName : ByteArray) : FilesState :=
  match resolvePath s none "/proc/self/fd".toUTF8 true with
  | .error _ => s
  | .ok fdDirIno =>
    match assocGet s.inodes fdDirIno with
    | some dirVn =>
      match dirVn.data with
      | .dir dd =>
        let dirVn' := { dirVn with data := .dir { dd with children := bytesAssocErase dd.children fdName } }
        let inodes1 := assocSet s.inodes fdDirIno dirVn'
        let inodes2 := match bytesAssocGet dd.children fdName with
          | some oldIno =>
            if s.fds.any (·.2.ino == oldIno) then inodes1
            else match assocGet inodes1 oldIno with
            | some vn =>
              match vn.data with
              | .symlink (.procMagic _ _) => assocErase inodes1 oldIno
              | _ => inodes1
            | none => inodes1
          | none => inodes1
        { s with inodes := inodes2 }
      | _ => s
    | none => s

/-- Convert `Except Errno Unit` into `FilesOutcome`. -/
def outcomeOfUnit : Except Errno Unit → FilesOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno HandleId` into `FilesOutcome`. -/
def outcomeOfOpened : Except Errno HandleId → FilesOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Convert `Except Errno ByteArray` into `FilesOutcome`. -/
def outcomeOfBytes : Except Errno ByteArray → FilesOutcome
  | .ok b => .bytes b
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `FilesOutcome`. -/
def outcomeOfU32 : Except Errno UInt32 → FilesOutcome
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert `Except Errno UInt64` into `FilesOutcome`. -/
def outcomeOfU64 : Except Errno UInt64 → FilesOutcome
  | .ok v => .u64 v
  | .error e => .err e

/-- Convert `Except Errno StatInfo` into `FilesOutcome`. -/
def outcomeOfStatted : Except Errno StatInfo → FilesOutcome
  | .ok st => .statted st
  | .error e => .err e

/-- Return `true` iff `out` is a curated catastrophic OS fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isCriticalFault : FilesOutcome → Bool
  | .err e => Errno.isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `out` is an interrupted syscall outcome (`.err Errno.EINTR`). -/
def isEintrOutcome : FilesOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Return `true` iff `req` is `.close` and `out` is `.err Errno.EBUSY` (excluded in sequential single-thread `healthyStep`). -/
def isCloseEbusy (req : FilesReq) (out : FilesOutcome) : Bool :=
  match req, out with
  | .close _, .err e => e == Errno.EBUSY
  | _, _ => false

/-- Healthy execution environment wrapping `FilesState` with a finite `EINTR` interruption budget (`ambientSeccomp = false`). -/
structure HealthyEnv where
  /-- Underlying `Files` world state. -/
  state : FilesState := FilesState.initial
  /-- Remaining bound on `EINTR` signal interruptions (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving BEq, Inhabited

/-- Initial healthy `Files` environment with optional `eintrBudget`. -/
def HealthyEnv.initial (eintrBudget : Nat := 0) : HealthyEnv :=
  { state := FilesState.initial, eintrBudget := eintrBudget }

/-- Return `true` iff `env` has no ambient `seccomp` `SECCOMP_RET_ERRNO` filter interception. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Files`, excluding critical OS faults, ambient `seccomp`, and `.close`/`EBUSY` while bounding `EINTR` via `eintrBudget`. -/
def healthyStep (env : HealthyEnv) (req : FilesReq) (out : FilesOutcome) : Option HealthyEnv :=
  if !env.wf || isCriticalFault out || isCloseEbusy req out then
    none
  else
    match allowedStep env.state req out with
    | none => none
    | some s' =>
      if isEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Execute one `FilesReq` against a `FilesOpsM m HandleId` capability bundle and decode its `FilesOutcome`. -/
def execFilesReq {m : Type → Type} [Monad m]
    (ops : FilesOpsM m HandleId) : FilesReq → m FilesOutcome
  | .openat d p fl md => outcomeOfOpened <$> ops.openat d p fl md
  | .openat2 d p how => outcomeOfOpened <$> ops.openat2 d p how
  | .close h => outcomeOfUnit <$> ops.close h
  | .read h n => outcomeOfBytes <$> ops.read h n
  | .write h bs => outcomeOfU32 <$> ops.write h bs
  | .fstat h => outcomeOfStatted <$> ops.fstat h
  | .fstatat d p fl => outcomeOfStatted <$> ops.fstatat d p fl
  | .faccessat d p mk fl => outcomeOfUnit <$> ops.faccessat d p mk fl
  | .mkdirat d p md => outcomeOfUnit <$> ops.mkdirat d p md
  | .unlinkat d p rd => outcomeOfUnit <$> ops.unlinkat d p rd
  | .renameat2 od op nd np fl => outcomeOfUnit <$> ops.renameat2 od op nd np fl
  | .symlinkat t d lp => outcomeOfUnit <$> ops.symlinkat t d lp
  | .readlinkat d p c => outcomeOfBytes <$> ops.readlinkat d p c
  | .getdents64 h c => outcomeOfBytes <$> ops.getdents64 h c
  | .fchmodat d p md => outcomeOfUnit <$> ops.fchmodat d p md
  | .fchmod h md => outcomeOfUnit <$> ops.fchmod h md
  | .flock h op => outcomeOfUnit <$> ops.flock h op
  | .fcntl h cmd => outcomeOfU32 <$> ops.fcntl h cmd
  | .fsync h => outcomeOfUnit <$> ops.fsync h
  | .getcwd c => outcomeOfBytes <$> ops.getcwd c
  | .lseek h off wh => outcomeOfU64 <$> ops.lseek h off wh
  | .reopenReadOnly h => outcomeOfOpened <$> ops.reopenReadOnly h
  | .dupStdio sl => outcomeOfOpened <$> ops.dupStdio sl

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthyFilesAt {W : Type} (proj : W → HealthyEnv)
    (ops : FilesOpsM (StateM W) HandleId) : Prop :=
  ∀ (w : W) (req : FilesReq),
    (proj w).wf = true →
    let (out, w') := (execFilesReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Direct healthy-world refinement predicate specialized to `StateM HealthyEnv`. -/
abbrev RefinesHealthyFiles (ops : FilesOpsM (StateM HealthyEnv) HandleId) : Prop :=
  RefinesHealthyFilesAt id ops

end LeanSwe.LinuxSyscall.Files

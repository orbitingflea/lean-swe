import LeanSwe.LinuxSyscall.Files.Model

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Pre-populated entry description relative to a seeded directory for `FilesState.withSeededTree`. -/
structure SeedEntry where
  /-- Relative parent directory path segments inside the seeded directory (`[]` for immediate child). -/
  relDir : List ByteArray := []
  /-- Entry leaf name. -/
  name : ByteArray
  /-- File kind (`.reg`, `.dir`, `.symlink`, `.fifo`, `.socket`, `.charDev`). -/
  kind : FileKind := .reg
  /-- Permission bits (`0o7777`). -/
  mode : Mode := 0o644
  /-- Whether `mode` should be compared strictly (`0o7777`). -/
  modeExact : Bool := false
  /-- Initial regular file contents. -/
  bytes : ByteArray := ByteArray.mk #[]
  /-- Symlink target bytes when `kind = .symlink`. -/
  symlinkTarget : ByteArray := ByteArray.mk #[]
  /-- Optional character-device specialization. -/
  devKind? : Option CharDevKind := none
  /-- Optional hardlink group ID: entries with the same `some g` share one `InodeId` (`nlink >= 2`) unless on an uncopied overlayfs lower layer. -/
  hardlinkGroup? : Option Nat := none
  /-- Optional pre-bound real `st_ino`. -/
  kernelIno? : Option UInt64 := none
  /-- Optional pre-bound real `st_dev`. -/
  kernelDev? : Option UInt64 := none
  /-- Whether the seeded node resides on an `overlayfs` lower layer (`InodeOrigin.managed true`). -/
  mayCopyUp : Bool := false
  /-- Whether the current UID owns this seeded entry (`false` uses world permission bits). -/
  ownedByUid : Bool := true
  /-- Whether the current process belongs to this seeded entry's owning GID (`in_group_p`). -/
  inGroup : Bool := true
  /-- Optional numeric UID of this seeded entry for sticky-directory checks. -/
  ownerUid? : Option UInt32 := none
  /-- Optional opaque UID tag distinguishing unmapped host UIDs in sticky directories. -/
  ownerUidTag? : Option UInt32 := none
  /-- Whether this seeded entry's UID is mapped in the active user namespace. -/
  uidMapped : Bool := true
  /-- Whether this seeded entry's GID is mapped in the active user namespace. -/
  gidMapped : Bool := true
  /-- Optional explicit logical mount ID override. -/
  mountId? : Option Nat := none
  /-- Whether this seeded node may share `(st_dev, st_ino)` across mounts or dentries. -/
  allowDevInoAlias : Bool := false
  /-- Whether metadata (`st_size`, `st_nlink`) is kernel-generated (`InodeOrigin.hostDynamic`). -/
  dynamicMeta : Bool := false
  /-- Pipe ring capacity for `.fifo` seeded nodes. -/
  pipeCapacity : PipeCapacity := .uncalibrated 2 16
  deriving Repr, BEq

/-- Configuration for `FilesState.withSeededTree`, capturing host environment and pre-populated scratch state. -/
structure SeedTreeConfig where
  /-- Absolute host CWD byte path. -/
  cwdPath : ByteArray := ByteArray.mk #[47]
  /-- Whether `cwdPath` is already exact and bound for `getcwd`. -/
  cwdBound : Bool := false
  /-- Process `umask` (`0o022` default). -/
  umask : Mode := 0o022
  /-- Initial permission mode of `cwdIno`. -/
  cwdMode : Mode := 0o755
  /-- Logical mount ID of `cwdIno`. -/
  cwdMountId : Nat := 4
  /-- Logical mount ID of `cwdIno`'s immediate parent directory. -/
  cwdParentMountId : Nat := 4
  /-- Permission mode of `cwdIno`'s immediate parent directory. -/
  cwdParentMode : Mode := 0o755
  /-- Whether `cwdIno`'s immediate parent directory is owned by the current UID. -/
  cwdParentOwnedByUid : Bool := false
  /-- Optional numeric UID of `cwdIno`'s immediate parent directory. -/
  cwdParentOwnerUid? : Option UInt32 := none
  /-- Optional pre-bound `st_ino` for `cwdIno`. -/
  cwdKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `cwdIno`. -/
  cwdKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `cwdIno`'s parent. -/
  cwdParentKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `cwdIno`'s parent. -/
  cwdParentKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/`. -/
  rootKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `/`. -/
  rootKernelDev? : Option UInt64 := none
  /-- Initial permission mode of `/`. -/
  rootMode : Mode := 0o755
  /-- Optional ownership override for `/` (`none` uses `!includeHostTree`). -/
  rootOwnedByUid? : Option Bool := none
  /-- Logical mount ID for `/sys` (`3` on host, `0` inside unmounted chroot trees). -/
  sysMountId : Nat := 3
  /-- Whether `/etc`, `/etc/passwd`, and `/sys` entries in `includeHostTree` are owned by current UID. -/
  hostSyntheticOwnedByUid : Bool := false
  /-- Optional cross-mount directory path for cross-mount `renameat2`/`openat2` probes. -/
  crossMountPath? : Option ByteArray := none
  /-- Permission mode of the cross-mount scratch directory. -/
  crossMountMode : Mode := 0o755
  /-- Logical mount ID of the cross-mount scratch directory. -/
  crossMountId : Nat := 5
  /-- Logical mount ID of the cross-mount directory's immediate parent. -/
  crossParentMountId : Nat := 5
  /-- Optional pre-bound `st_ino` for the cross-mount directory. -/
  crossMountKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for the cross-mount directory. -/
  crossMountKernelDev? : Option UInt64 := none
  /-- Logical mount ID for `/dev`. -/
  devMountId : Nat := 1
  /-- Per-mount VFS capability profiles keyed by `mountId`. -/
  mountProfiles : List (Nat × MountProfile) := []
  /-- Optional ancestor metadata overrides `(absPath, mode, ownedByUid, mountId, kernelDev?, kernelIno?)`. -/
  ancestorMeta : List (ByteArray × Mode × Bool × Nat × Option UInt64 × Option UInt64) := []
  /-- Optional numeric UID overrides keyed by ancestor `absPath`. -/
  ancestorOwnerUids : List (ByteArray × UInt32) := []
  /-- Whether to seed `/`, `/etc/passwd`, `/dev/{null,zero,full}`, `/proc/self/*`, and `/sys/kernel/*`. -/
  includeHostTree : Bool := true
  /-- Whether `CAP_DAC_OVERRIDE` is active in effective capabilities. -/
  hasCapDacOverride : Bool := false
  /-- Whether `CAP_DAC_READ_SEARCH` is active in effective capabilities. -/
  hasCapDacReadSearch : Bool := false
  /-- Whether `CAP_FOWNER` is active in effective capabilities. -/
  hasCapFowner : Bool := false
  /-- Whether `CAP_FSETID` is active in effective capabilities. -/
  hasCapFsetid : Bool := false
  /-- Whether running in the initial user namespace. -/
  inInitUserNs : Bool := true
  /-- Kernel `fs.protected_regular` sysctl level (`0`, `1`, or `2`). -/
  protectedRegular : UInt32 := 2
  /-- Kernel `fs.protected_fifos` sysctl level (`0`, `1`, or `2`). -/
  protectedFifos : UInt32 := 1
  /-- Whether kernel `fs.protected_symlinks` is enabled (`1`). -/
  protectedSymlinks : Bool := false
  /-- Whether unowned host synthetic nodes have a mapped UID. -/
  hostUidMapped : Bool := true
  /-- Whether unowned host synthetic nodes have a mapped GID. -/
  hostGidMapped : Bool := true
  /-- Optional `uidMapped` override for `/` (`none` uses `selfUidMapped` if owned, else `hostUidMapped`). -/
  rootUidMapped? : Option Bool := none
  /-- Optional `gidMapped` override for `/` (`none` uses `selfGidMapped` if owned, else `hostGidMapped`). -/
  rootGidMapped? : Option Bool := none
  /-- Optional `uidMapped` override for the current process (`none` defaults to `hostUidMapped`). -/
  selfUidMapped? : Option Bool := none
  /-- Optional `gidMapped` override for the current process (`none` defaults to `hostGidMapped`). -/
  selfGidMapped? : Option Bool := none
  /-- Whether the current process belongs to its own primary filesystem GID (`in_group_p`). -/
  selfInGroup : Bool := true
  /-- Whether `/dev/{null,zero,full}` are owned by the current UID. -/
  devOwnedByUid : Bool := false
  /-- Optional `uidMapped` override for `/dev/{null,zero,full}` (defaults to `hostUidMapped`). -/
  devUidMapped? : Option Bool := none
  /-- Optional `gidMapped` override for `/dev/{null,zero,full}` (defaults to `hostGidMapped`). -/
  devGidMapped? : Option Bool := none
  /-- Whether `/proc/1` has a mapped UID in the active user namespace. -/
  proc1UidMapped : Bool := false
  /-- Whether `/proc/1` has a mapped GID in the active user namespace. -/
  proc1GidMapped : Bool := false
  /-- Whether fd `0`'s UID is mapped in the active user namespace. -/
  stdinUidMapped : Bool := true
  /-- Whether fd `0`'s GID is mapped in the active user namespace. -/
  stdinGidMapped : Bool := true
  /-- Whether fd `1`'s UID is mapped in the active user namespace. -/
  stdoutUidMapped : Bool := true
  /-- Whether fd `1`'s GID is mapped in the active user namespace. -/
  stdoutGidMapped : Bool := true
  /-- Whether fd `2`'s UID is mapped in the active user namespace. -/
  stderrUidMapped : Bool := true
  /-- Whether fd `2`'s GID is mapped in the active user namespace. -/
  stderrGidMapped : Bool := true
  /-- Optional `(absPath, uidMapped, gidMapped)` overrides for ancestors. -/
  ancestorMapped : List (ByteArray × Bool × Bool) := []
  /-- Optional numeric UID override for `/`. -/
  rootOwnerUid? : Option UInt32 := none
  /-- Whether an inherited safe outer `seccomp(SECCOMP_RET_ERRNO)` filter is active. -/
  ambientSeccomp : Bool := false
  /-- Entries seeded at the outer root above `chroot` when `chrootUnreachable` is `true`. -/
  chrootOuterEntries : List SeedEntry := []
  /-- Whether `cwdIno` is a merged `overlayfs` directory reporting `st_nlink = 1`. -/
  cwdOverlayMerged : Bool := false
  /-- Whether `cwdIno` starts on an uncopied `overlayfs` lower layer. -/
  cwdMayCopyUp : Bool := false
  /-- Whether `cwdIno` sits outside the `chroot` root (`getcwd` starts unbound). -/
  chrootUnreachable : Bool := false
  /-- Ancestor directories above `cwdIno` when `chrootUnreachable` is `true`. -/
  chrootOutsideAncestors : List (Mode × Bool × Nat × Option UInt64 × Option UInt64) := []
  /-- Whether `/proc/1` is owned by the current UID. -/
  proc1OwnedByUid : Bool := false
  /-- ASCII PID string for `/proc/self` target. -/
  selfPidBytes : ByteArray := ByteArray.mk #[50]
  /-- Whether `/proc/self/exe`'s target binary is owned by the current UID. -/
  exeOwnedByUid : Bool := true
  /-- Observed `FileKind` of fd `0` (`/proc/self/fd/0`). -/
  stdinKind : FileKind := .charDev
  /-- Optional character-device specialization of fd `0`. -/
  stdinDevKind? : Option CharDevKind := some .nullDev
  /-- Logical mount ID of fd `0`'s target inode. -/
  stdinMountId : Nat := 1
  /-- Logical mount ID of fd `1`'s target inode. -/
  stdoutMountId : Nat := 1
  /-- Logical mount ID of fd `2`'s target inode. -/
  stderrMountId : Nat := 1
  /-- Observed permission mode of fd `0`. -/
  stdinMode : Mode := 0o666
  /-- Whether fd `0` is owned by the current UID. -/
  stdinOwnedByUid : Bool := false
  /-- Optional pre-bound `st_dev` for fd `0`. -/
  stdinKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for fd `0`. -/
  stdinKernelIno? : Option UInt64 := none
  /-- Observed `FileKind` of fd `1` (`/proc/self/fd/1`). -/
  stdoutKind : FileKind := .charDev
  /-- Optional character-device specialization of fd `1`. -/
  stdoutDevKind? : Option CharDevKind := some .nullDev
  /-- Observed permission mode of fd `1`. -/
  stdoutMode : Mode := 0o666
  /-- Whether fd `1` is owned by the current UID. -/
  stdoutOwnedByUid : Bool := false
  /-- Optional pre-bound `st_dev` for fd `1`. -/
  stdoutKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for fd `1`. -/
  stdoutKernelIno? : Option UInt64 := none
  /-- Observed `FileKind` of fd `2` (`/proc/self/fd/2`). -/
  stderrKind : FileKind := .charDev
  /-- Optional character-device specialization of fd `2`. -/
  stderrDevKind? : Option CharDevKind := some .nullDev
  /-- Observed permission mode of fd `2`. -/
  stderrMode : Mode := 0o666
  /-- Whether fd `2` is owned by the current UID. -/
  stderrOwnedByUid : Bool := false
  /-- Optional pre-bound `st_dev` for fd `2`. -/
  stderrKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for fd `2`. -/
  stderrKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `/dev/null`. -/
  devNullKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/dev/null`. -/
  devNullKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `/dev/zero`. -/
  devZeroKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/dev/zero`. -/
  devZeroKernelIno? : Option UInt64 := none
  /-- Optional pre-bound `st_dev` for `/dev/full`. -/
  devFullKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/dev/full`. -/
  devFullKernelIno? : Option UInt64 := none
  /-- Observed `lstat` mode of `/proc/self/fd/0`. -/
  procFd0LinkMode : Mode := 0o777
  /-- Observed `lstat` mode of `/proc/self/fd/1`. -/
  procFd1LinkMode : Mode := 0o777
  /-- Observed `lstat` mode of `/proc/self/fd/2`. -/
  procFd2LinkMode : Mode := 0o777
  /-- Optional `inGroup` override for `/`. -/
  rootInGroup? : Option Bool := none
  /-- Whether unowned host synthetic nodes share the current primary/supplementary GID. -/
  hostSyntheticInGroup : Bool := true
  /-- Optional `inGroup` override for `/dev/{null,zero,full}`. -/
  devInGroup? : Option Bool := none
  /-- Optional `inGroup` override for `/proc/self/exe`'s target binary. -/
  exeInGroup? : Option Bool := none
  /-- Whether `/proc/1` is in the current process's GID set. -/
  proc1InGroup : Bool := false
  /-- Permission mode of `/proc/1/cwd` when `PID != 1`. -/
  proc1CwdMode : Mode := 0o755
  /-- Optional `ownedByUid` override for `/proc/1/cwd`. -/
  proc1CwdOwnedByUid? : Option Bool := none
  /-- Optional `inGroup` override for `/proc/1/cwd`. -/
  proc1CwdInGroup? : Option Bool := none
  /-- Optional `uidMapped` override for `/proc/1/cwd`. -/
  proc1CwdUidMapped? : Option Bool := none
  /-- Optional `gidMapped` override for `/proc/1/cwd`. -/
  proc1CwdGidMapped? : Option Bool := none
  /-- Logical mount ID for `/proc/1/cwd`. -/
  proc1CwdMountId : Nat := 0
  /-- Optional pre-bound `st_dev` for `/proc/1/cwd`. -/
  proc1CwdKernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/proc/1/cwd`. -/
  proc1CwdKernelIno? : Option UInt64 := none
  /-- Observed `FileKind` of `/proc/1/fd/0` when `PID != 1`. -/
  proc1Fd0Kind : FileKind := .charDev
  /-- Optional character-device specialization of `/proc/1/fd/0`. -/
  proc1Fd0DevKind? : Option CharDevKind := some .nullDev
  /-- Logical mount ID for `/proc/1/fd/0`. -/
  proc1Fd0MountId : Nat := 1
  /-- Observed permission mode of `/proc/1/fd/0`. -/
  proc1Fd0Mode : Mode := 0o666
  /-- Optional `ownedByUid` override for `/proc/1/fd/0`. -/
  proc1Fd0OwnedByUid? : Option Bool := none
  /-- Optional `inGroup` override for `/proc/1/fd/0`. -/
  proc1Fd0InGroup? : Option Bool := none
  /-- Optional `uidMapped` override for `/proc/1/fd/0`. -/
  proc1Fd0UidMapped? : Option Bool := none
  /-- Optional `gidMapped` override for `/proc/1/fd/0`. -/
  proc1Fd0GidMapped? : Option Bool := none
  /-- Optional pre-bound `st_dev` for `/proc/1/fd/0`. -/
  proc1Fd0KernelDev? : Option UInt64 := none
  /-- Optional pre-bound `st_ino` for `/proc/1/fd/0`. -/
  proc1Fd0KernelIno? : Option UInt64 := none
  /-- Observed `lstat` mode of `/proc/1/fd/0`. -/
  proc1Fd0LinkMode : Mode := 0o777
  /-- Whether fd `0` is in the current process's GID set. -/
  stdinInGroup : Bool := true
  /-- Whether fd `1` is in the current process's GID set. -/
  stdoutInGroup : Bool := true
  /-- Whether fd `2` is in the current process's GID set. -/
  stderrInGroup : Bool := true
  /-- Optional `(absPath, inGroup)` overrides for ancestors. -/
  ancestorInGroups : List (ByteArray × Bool) := []
  /-- Entries to pre-populate inside `cwdIno`. -/
  cwdEntries : List SeedEntry := []
  /-- Entries to pre-populate inside `crossMountPath?`. -/
  crossEntries : List SeedEntry := []
  deriving Repr, BEq

private def mkInodeData (kind : FileKind) (parentIno : InodeId) (bytes symTarget : ByteArray)
    (devKind? : Option CharDevKind) (pipeCap : PipeCapacity) : InodeData :=
  match kind with
  | .reg => .reg (RegData.ofBytes bytes .unsealable)
  | .dir => .dir { parentIno := parentIno, lifecycle := .live }
  | .symlink => .symlink (.path symTarget)
  | .fifo => .fifo { capacity := pipeCap }
  | .charDev => .charDev (devKind?.getD .generic)
  | .socket => .socket
  | .blockDev => .blockDev
  | .other => .other

private def seedAllocNode (s : FilesState) (vn : VNode) : FilesState × InodeId :=
  let ino := s.nextIno
  ({ s with inodes := assocSet s.inodes ino vn, nextIno := ino + 1 }, ino)

private def seedAttachChild (s : FilesState) (parentIno : InodeId) (name : ByteArray)
    (childIno : InodeId) (isDir : Bool) : FilesState :=
  match assocGet s.inodes parentIno with
  | none => s
  | some pvn =>
    match pvn.data with
    | .dir pdd =>
      let already := (bytesAssocGet pdd.children name).isSome
      let pvn' :=
        { pvn with
          data := .dir { pdd with children := bytesAssocSet pdd.children name childIno }
          nlink := if pdd.lifecycle == .overlayMerged then pvn.nlink else if isDir && !already then pvn.nlink + 1 else pvn.nlink }
      { s with inodes := assocSet s.inodes parentIno pvn' }
    | _ => s

private def seedEnsureDirSegs (s : FilesState) (startIno : InodeId) (segs : List ByteArray)
    (template : VNode) : FilesState × InodeId :=
  match segs with
  | [] => (s, startIno)
  | seg :: rest =>
    match assocGet s.inodes startIno with
    | none => (s, startIno)
    | some pvn =>
      match bytesAssocGet pvn.children seg with
      | some existingIno => seedEnsureDirSegs s existingIno rest template
      | none =>
        let dd := match template.data with | .dir d => d | _ => {}
        let (s1, childIno) :=
          seedAllocNode s { template with data := .dir { dd with parentIno := startIno }, nlink := 2 }
        let s2 := seedAttachChild s1 startIno seg childIno true
        seedEnsureDirSegs s2 childIno rest template

private def mkSeedVNode (s : FilesState) (e : SeedEntry) (parentIno effMountId nl : Nat) (ovlCopyUp : Bool) : VNode :=
  let posix := mountPosixModes s effMountId
  let origin : InodeOrigin :=
    if e.dynamicMeta then .hostDynamic
    else .managed ovlCopyUp
  { data := mkInodeData e.kind parentIno e.bytes e.symlinkTarget e.devKind? e.pipeCapacity
    mode := e.mode
    modeExact := e.modeExact && posix
    nlink := nl
    mountId := effMountId
    owner := {
      ownedByUid := e.ownedByUid
      inGroup := e.inGroup
      uid? := e.ownerUid?
      uidMapped := e.uidMapped
      gidMapped := e.gidMapped
      uidTag? := e.ownerUidTag? }
    kernelId := { dev? := e.kernelDev?, ino? := e.kernelIno?, allowAlias := e.allowDevInoAlias }
    origin := origin }

private def seedApplyEntriesAux (s : FilesState) (baseIno baseMountId : Nat)
    (entries : List SeedEntry) (hlMap : List (Nat × InodeId)) : FilesState :=
  match entries with
  | [] => s
  | e :: rest =>
    let dirTemplate : VNode :=
      { data := .dir {}, mode := 0o755, mountId := baseMountId, nlink := 2 }
    let (s1, parentIno) := seedEnsureDirSegs s baseIno e.relDir dirTemplate
    let parentMountId := inodeMountId s1 parentIno
    let effMountId := e.mountId?.getD parentMountId
    let posix := mountPosixModes s1 effMountId
    let ovlCopyUp := e.mayCopyUp
    let existingChild? := (assocGet s1.inodes parentIno).bind fun pvn => bytesAssocGet pvn.children e.name
    match e.kind, existingChild? with
    | .dir, some exIno =>
      let s2 := match assocGet s1.inodes exIno with
        | none => s1
        | some exVn =>
          let origin' : InodeOrigin := if e.dynamicMeta then .hostDynamic else .managed ovlCopyUp
          let exVn' := { exVn with
            mode := e.mode
            modeExact := e.modeExact && posix
            mountId := e.mountId?.getD exVn.mountId
            kernelId := {
              dev? := e.kernelDev?.orElse (fun _ => exVn.kernelId.dev?)
              ino? := e.kernelIno?.orElse (fun _ => exVn.kernelId.ino?)
              allowAlias := exVn.kernelId.allowAlias || e.allowDevInoAlias }
            owner := {
              ownedByUid := e.ownedByUid
              inGroup := e.inGroup
              uid? := e.ownerUid?.orElse (fun _ => exVn.owner.uid?)
              uidMapped := e.uidMapped
              gidMapped := e.gidMapped }
            origin := origin' }
          { s1 with inodes := assocSet s1.inodes exIno exVn' }
      seedApplyEntriesAux s2 baseIno baseMountId rest hlMap
    | _, _ =>
      match e.hardlinkGroup? with
      | some gid =>
        match assocGet hlMap gid with
        | some existingIno =>
          let s2 := match assocGet s1.inodes existingIno with
            | none => s1
            | some vn => { s1 with inodes := assocSet s1.inodes existingIno { vn with nlink := vn.nlink + 1 } }
          let s3 := seedAttachChild s2 parentIno e.name existingIno (e.kind == .dir)
          seedApplyEntriesAux s3 baseIno baseMountId rest hlMap
        | none =>
          let nl := if e.kind == .dir then 2 else 1
          let newVn := mkSeedVNode s1 e parentIno effMountId nl ovlCopyUp
          let (s2, newIno) := seedAllocNode s1 newVn
          let s3 := seedAttachChild s2 parentIno e.name newIno (e.kind == .dir)
          seedApplyEntriesAux s3 baseIno baseMountId rest ((gid, newIno) :: hlMap)
      | none =>
        let nl := if e.kind == .dir then 2 else 1
        let newVn := mkSeedVNode s1 e parentIno effMountId nl ovlCopyUp
        let (s2, newIno) := seedAllocNode s1 newVn
        let s3 := seedAttachChild s2 parentIno e.name newIno (e.kind == .dir)
        seedApplyEntriesAux s3 baseIno baseMountId rest hlMap

private def seedApplyEntries (s : FilesState) (baseIno baseMountId : Nat)
    (entries : List SeedEntry) : FilesState :=
  seedApplyEntriesAux s baseIno baseMountId entries []

private def seedFindSegsIno (s : FilesState) (cur : InodeId) : List ByteArray → Option InodeId
  | [] => some cur
  | seg :: rest =>
    match assocGet s.inodes cur with
    | none => none
    | some vn =>
      match bytesAssocGet vn.children seg with
      | none => none
      | some c => seedFindSegsIno s c rest

private def seedApplyAncestorMeta (s : FilesState) :
    List (ByteArray × Mode × Bool × Nat × Option UInt64 × Option UInt64) → FilesState
  | [] => s
  | (absPath, md, owned, mid, dev?, ino?) :: rest =>
    let segs := (splitPathBytes absPath).2.1
    let s' := match seedFindSegsIno s 0 segs with
      | none => s
      | some ino =>
        match assocGet s.inodes ino with
        | none => s
        | some vn =>
          let vn' := { vn with
            mode := md
            owner := { vn.owner with ownedByUid := owned }
            mountId := mid
            kernelId := {
              dev? := dev?.orElse (fun _ => vn.kernelId.dev?)
              ino? := ino?.orElse (fun _ => vn.kernelId.ino?)
              allowAlias := vn.kernelId.allowAlias }
            origin := .hostDynamic }
          { s with inodes := assocSet s.inodes ino vn' }
    seedApplyAncestorMeta s' rest

private def seedApplyAncestorOwnerUids (s : FilesState) : List (ByteArray × UInt32) → FilesState
  | [] => s
  | (absPath, uid) :: rest =>
    let segs := (splitPathBytes absPath).2.1
    let s' := match seedFindSegsIno s 0 segs with
      | none => s
      | some ino =>
        match assocGet s.inodes ino with
        | none => s
        | some vn => { s with inodes := assocSet s.inodes ino { vn with owner := { vn.owner with uid? := some uid } } }
    seedApplyAncestorOwnerUids s' rest

private def seedApplyAncestorMapped (s : FilesState) : List (ByteArray × Bool × Bool) → FilesState
  | [] => s
  | (absPath, uMap, gMap) :: rest =>
    let segs := (splitPathBytes absPath).2.1
    let s' := match seedFindSegsIno s 0 segs with
      | none => s
      | some ino =>
        match assocGet s.inodes ino with
        | none => s
        | some vn =>
          { s with inodes := assocSet s.inodes ino { vn with owner := { vn.owner with uidMapped := uMap, gidMapped := gMap } } }
    seedApplyAncestorMapped s' rest

private def seedApplyAncestorInGroups (s : FilesState) : List (ByteArray × Bool) → FilesState
  | [] => s
  | (absPath, inGrp) :: rest =>
    let segs := (splitPathBytes absPath).2.1
    let s' := match seedFindSegsIno s 0 segs with
      | none => s
      | some ino =>
        match assocGet s.inodes ino with
        | none => s
        | some vn =>
          { s with inodes := assocSet s.inodes ino { vn with owner := { vn.owner with inGroup := inGrp } } }
    seedApplyAncestorInGroups s' rest

private def seedChrootOutsideAncestorsAux (s : FilesState) (pIno outRootIno : InodeId) (hasRoot : Bool) :
    List (Mode × Bool × Nat × Option UInt64 × Option UInt64) → FilesState × InodeId × InodeId
  | [] => (s, pIno, if hasRoot then outRootIno else s.rootIno)
  | (mode, owned, mid, kDev?, kIno?) :: rest =>
    let outIno := s.nextIno
    let parent := if hasRoot then pIno else outIno
    let outVn : VNode :=
      { data := .dir { parentIno := parent }, mode := mode, mountId := mid,
        kernelId := { dev? := kDev?, ino? := kIno? }, nlink := 2,
        origin := .hostDynamic, owner := { ownedByUid := owned } }
    let s1 := { s with inodes := assocSet s.inodes outIno outVn, nextIno := outIno + 1 }
    seedChrootOutsideAncestorsAux s1 outIno (if hasRoot then outRootIno else outIno) true rest

private def seedChrootOutsideAncestors (s : FilesState)
    (ancs : List (Mode × Bool × Nat × Option UInt64 × Option UInt64)) : FilesState × InodeId × InodeId :=
  seedChrootOutsideAncestorsAux s s.rootIno s.rootIno false ancs.reverse

private def seedInsertAtPath (s : FilesState) (parentIno : InodeId) (name : ByteArray)
    (vn : VNode) : FilesState × InodeId :=
  let vn' := match vn.data with
    | .dir dd => { vn with data := .dir { dd with parentIno := parentIno } }
    | _ => vn
  let (s1, newIno) := seedAllocNode s vn'
  let s2 := seedAttachChild s1 parentIno name newIno (vn.kind == .dir)
  (s2, newIno)

private def seedApplyOuterEntries (s : FilesState) (outRootIno : InodeId)
    (entries : List SeedEntry) : FilesState :=
  let (reused, rest) := entries.partition fun e =>
    e.relDir.isEmpty && e.kernelDev?.isSome && e.kernelIno?.isSome &&
    s.inodes.any fun (ino, vn) =>
      ino != outRootIno && vn.parentIno == outRootIno && vn.kind == e.kind &&
      vn.kernelId.dev? == e.kernelDev? && vn.kernelId.ino? == e.kernelIno?
  let s1 := reused.foldl (fun st e =>
    match st.inodes.find? (fun (ino, vn) =>
        ino != outRootIno && vn.parentIno == outRootIno && vn.kind == e.kind &&
        vn.kernelId.dev? == e.kernelDev? && vn.kernelId.ino? == e.kernelIno?) with
    | none => st
    | some (existingIno, existingVn) =>
      let existingVn' :=
        { existingVn with
          mode := e.mode
          modeExact := e.modeExact
          mountId := e.mountId?.getD existingVn.mountId
          owner := {
            ownedByUid := e.ownedByUid
            inGroup := e.inGroup
            uid? := e.ownerUid?
            uidMapped := e.uidMapped
            gidMapped := e.gidMapped
            uidTag? := e.ownerUidTag? }
          origin := if e.dynamicMeta then .hostDynamic else .managed e.mayCopyUp }
      let st1 := { st with inodes := assocSet st.inodes existingIno existingVn' }
      seedAttachChild st1 outRootIno e.name existingIno false) s
  seedApplyEntries s1 outRootIno (inodeMountId s1 outRootIno) rest

/-- Build a seeded `FilesState` modeling host ancestors, `/dev/{null,zero,full}`, `/proc/self/*`, `/sys/kernel/*`, `umask`, cross-mount dirs, and pre-populated scratch entries. -/
def FilesState.withSeededTree (cfg : SeedTreeConfig := {}) : FilesState :=
  let rootOwned := cfg.rootOwnedByUid?.getD (!cfg.includeHostTree)
  let rootVn : VNode :=
    { data := .dir { parentIno := 0, lifecycle := .live }
      mode := cfg.rootMode
      mountId := 0
      nlink := 2
      kernelId := { dev? := cfg.rootKernelDev?, ino? := cfg.rootKernelIno? }
      origin := if cfg.includeHostTree then .hostDynamic else .managed false
      owner := {
        ownedByUid := rootOwned
        inGroup := cfg.rootInGroup?.getD (rootOwned || cfg.hostSyntheticInGroup)
        uid? := cfg.rootOwnerUid?
        uidMapped := rootOwned || cfg.hostUidMapped
        gidMapped := rootOwned || cfg.hostGidMapped } }
  let cwdPathInit : CwdPath :=
    if !cfg.chrootUnreachable && (cfg.cwdBound || cfg.cwdPath.size > 1) then .bound cfg.cwdPath
    else .unbound cfg.cwdPath
  let s0 : FilesState :=
    { inodes := [(0, rootVn)]
      fds := []
      cwdPath := cwdPathInit
      rootIno := 0
      cwdIno := 0
      umask := cfg.umask &&& 0o0777
      mountProfiles := cfg.mountProfiles
      cred := {
        capDacOverride := cfg.hasCapDacOverride
        capDacReadSearch := cfg.hasCapDacReadSearch
        capFowner := cfg.hasCapFowner
        capFsetid := cfg.hasCapFsetid
        initUserNs := cfg.inInitUserNs }
      sysctls := {
        protectedRegular := cfg.protectedRegular
        protectedFifos := cfg.protectedFifos
        protectedSymlinks := cfg.protectedSymlinks }
      ambientSeccomp := cfg.ambientSeccomp
      nextIno := 1
      nextHid := 0 }
  let selfUMap := cfg.selfUidMapped?.getD cfg.hostUidMapped
  let selfGMap := cfg.selfGidMapped?.getD cfg.hostGidMapped
  let rootVnFixed : VNode :=
    { rootVn with
      owner := {
        rootVn.owner with
        inGroup := cfg.rootInGroup?.getD (if rootOwned then cfg.selfInGroup else cfg.hostSyntheticInGroup)
        uidMapped := cfg.rootUidMapped?.getD (if rootOwned then selfUMap else cfg.hostUidMapped)
        gidMapped := cfg.rootGidMapped?.getD (if rootOwned then selfGMap else cfg.hostGidMapped) } }
  let s0 : FilesState :=
    { s0 with
      inodes := [(0, rootVnFixed)]
      cred := { s0.cred with uidMapped := selfUMap, gidMapped := selfGMap } }
  let hostDirTpl : VNode :=
    { data := .dir {}, mode := 0o755, mountId := 0, origin := .hostDynamic,
      owner := {
        ownedByUid := false
        inGroup := cfg.hostSyntheticInGroup
        uidMapped := cfg.hostUidMapped
        gidMapped := cfg.hostGidMapped }, nlink := 2 }
  let (sBase, cwdAnchorIno, outRootIno) :=
    if !cfg.chrootUnreachable then (s0, 0, 0)
    else
      let ancs :=
        if cfg.chrootOutsideAncestors.isEmpty then
          [(cfg.cwdParentMode, cfg.cwdParentOwnedByUid, cfg.cwdParentMountId, cfg.cwdParentKernelDev?, cfg.cwdParentKernelIno?)]
        else cfg.chrootOutsideAncestors
      seedChrootOutsideAncestors s0 ancs
  let cwdSegs := (splitPathBytes cfg.cwdPath).2.1
  let (s1, cwdIno) :=
    match cwdSegs.reverse with
    | [] => (sBase, cwdAnchorIno)
    | cwdLeaf :: revAnc =>
      let (sa, cwdParentIno) := seedEnsureDirSegs sBase cwdAnchorIno revAnc.reverse hostDirTpl
      let sa' :=
        if revAnc.isEmpty then sa
        else
          match assocGet sa.inodes cwdParentIno with
          | none => sa
          | some pvn =>
            let pvn' :=
              { pvn with
                mode := cfg.cwdParentMode
                mountId := cfg.cwdParentMountId
                kernelId := { dev? := cfg.cwdParentKernelDev?, ino? := cfg.cwdParentKernelIno? }
                origin := .hostDynamic
                owner := { pvn.owner with ownedByUid := cfg.cwdParentOwnedByUid, uid? := cfg.cwdParentOwnerUid? } }
            { sa with inodes := assocSet sa.inodes cwdParentIno pvn' }
      let cwdLifecycle : DirLifecycle := if cfg.cwdOverlayMerged then .overlayMerged else .live
      let cwdOrigin : InodeOrigin := .managed cfg.cwdMayCopyUp
      let cwdVn : VNode :=
        { data := .dir { parentIno := cwdParentIno, lifecycle := cwdLifecycle }
          mode := cfg.cwdMode
          modeExact := false
          mountId := cfg.cwdMountId
          kernelId := { dev? := cfg.cwdKernelDev?, ino? := cfg.cwdKernelIno? }
          nlink := if cfg.cwdOverlayMerged then 1 else 2
          origin := cwdOrigin
          owner := { ownedByUid := true, inGroup := cfg.selfInGroup, uidMapped := selfUMap, gidMapped := selfGMap } }
      seedInsertAtPath sa' cwdParentIno cwdLeaf cwdVn
  let s2 := { s1 with cwdIno := cwdIno }
  let (s3, crossIno?) :=
    match cfg.crossMountPath? with
    | none => (s2, none)
    | some crossPath =>
      let crossSegs := (splitPathBytes crossPath).2.1
      match crossSegs.reverse with
      | [] => (s2, none)
      | crossLeaf :: revAnc =>
        let (sa, crossParentIno) := seedEnsureDirSegs s2 0 revAnc.reverse hostDirTpl
        let sa' :=
          if revAnc.isEmpty then sa
          else
            match assocGet sa.inodes crossParentIno with
            | none => sa
            | some pvn =>
              { sa with inodes := assocSet sa.inodes crossParentIno { pvn with mountId := cfg.crossParentMountId, origin := .hostDynamic } }
        let crossVn : VNode :=
          { data := .dir { parentIno := crossParentIno }
            mode := cfg.crossMountMode
            mountId := cfg.crossMountId
            kernelId := { dev? := cfg.crossMountKernelDev?, ino? := cfg.crossMountKernelIno? }
            owner := { ownedByUid := true, inGroup := cfg.selfInGroup, uidMapped := selfUMap, gidMapped := selfGMap }
            nlink := 2 }
        let (sb, cIno) := seedInsertAtPath sa' crossParentIno crossLeaf crossVn
        (sb, some cIno)
  let s4 :=
    if !cfg.includeHostTree then s3
    else
      let (sa, etcIno) := seedEnsureDirSegs s3 0 [asciiBytes ['e', 't', 'c']]
        { hostDirTpl with
          owner := {
            ownedByUid := cfg.hostSyntheticOwnedByUid
            inGroup := if cfg.hostSyntheticOwnedByUid then cfg.selfInGroup else cfg.hostSyntheticInGroup
            uidMapped := if cfg.hostSyntheticOwnedByUid then selfUMap else cfg.hostUidMapped
            gidMapped := if cfg.hostSyntheticOwnedByUid then selfGMap else cfg.hostGidMapped } }
      let (sa, _) := seedInsertAtPath sa etcIno (asciiBytes ['p', 'a', 's', 's', 'w', 'd'])
        { data := .reg {}, mode := 0o644, mountId := 0, origin := .hostDynamic,
          owner := {
            ownedByUid := cfg.hostSyntheticOwnedByUid
            inGroup := if cfg.hostSyntheticOwnedByUid then cfg.selfInGroup else cfg.hostSyntheticInGroup
            uidMapped := if cfg.hostSyntheticOwnedByUid then selfUMap else cfg.hostUidMapped
            gidMapped := if cfg.hostSyntheticOwnedByUid then selfGMap else cfg.hostGidMapped },
          nlink := 1 }
      let devOwner : InodeOwner :=
        { ownedByUid := cfg.devOwnedByUid
          inGroup := cfg.devInGroup?.getD (if cfg.devOwnedByUid then cfg.selfInGroup else cfg.hostSyntheticInGroup)
          uidMapped := cfg.devUidMapped?.getD (if cfg.devOwnedByUid then selfUMap else cfg.hostUidMapped)
          gidMapped := cfg.devGidMapped?.getD (if cfg.devOwnedByUid then selfGMap else cfg.hostGidMapped) }
      let (sa, devIno) := seedEnsureDirSegs sa 0 [asciiBytes ['d', 'e', 'v']]
        { hostDirTpl with mountId := cfg.devMountId, owner := devOwner }
      let sa := match assocGet sa.inodes devIno with
        | some dvn => { sa with inodes := assocSet sa.inodes devIno { dvn with mountId := cfg.devMountId, owner := devOwner } }
        | none => sa
      let devChar (dk : CharDevKind) (d? i? : Option UInt64) : VNode :=
        { data := .charDev dk, mode := 0o666, modeExact := true, mountId := cfg.devMountId,
          kernelId := { dev? := d?, ino? := i? }, origin := .hostDynamic,
          owner := devOwner,
          nlink := 1 }
      let (sa, devNullIno) := seedInsertAtPath sa devIno (asciiBytes ['n', 'u', 'l', 'l'])
        (devChar .nullDev cfg.devNullKernelDev? cfg.devNullKernelIno?)
      let (sa, devZeroIno) := seedInsertAtPath sa devIno (asciiBytes ['z', 'e', 'r', 'o'])
        (devChar .zeroDev cfg.devZeroKernelDev? cfg.devZeroKernelIno?)
      let (sa, devFullIno) := seedInsertAtPath sa devIno (asciiBytes ['f', 'u', 'l', 'l'])
        (devChar .fullDev cfg.devFullKernelDev? cfg.devFullKernelIno?)
      let (sa, exeTargetIno) := seedAllocNode sa
        { data := .reg { exeProtected := true }, mode := 0o755, mountId := 0,
          kernelId := { allowAlias := true }, origin := .hostDynamic,
          owner := {
            ownedByUid := cfg.exeOwnedByUid
            inGroup := cfg.exeInGroup?.getD (if cfg.exeOwnedByUid then cfg.selfInGroup else cfg.hostSyntheticInGroup)
            uidMapped := if cfg.exeOwnedByUid then selfUMap else cfg.hostUidMapped
            gidMapped := if cfg.exeOwnedByUid then selfGMap else cfg.hostGidMapped },
          nlink := 1 }
      let sameDevIno (d1? i1? d2? i2? : Option UInt64) : Bool :=
        match d1?, i1?, d2?, i2? with
        | some d1, some i1, some d2, some i2 => d1 == d2 && i1 == i2
        | _, _, _, _ => false
      let matchDevAlias (d? i? : Option UInt64) : Option InodeId :=
        if sameDevIno d? i? cfg.devNullKernelDev? cfg.devNullKernelIno? then some devNullIno
        else if sameDevIno d? i? cfg.devZeroKernelDev? cfg.devZeroKernelIno? then some devZeroIno
        else if sameDevIno d? i? cfg.devFullKernelDev? cfg.devFullKernelIno? then some devFullIno
        else none
      let mkStdNode (k : FileKind) (dk? : Option CharDevKind) (m : Mode) (mid : Nat)
          (d? i? : Option UInt64) (owned inGrp uMap gMap : Bool) : VNode :=
        let effK := if k == .dir then .other else k
        { data := mkInodeData effK 0 (ByteArray.mk #[]) (ByteArray.mk #[]) dk? (.uncalibrated 2 16)
          mode := m, mountId := mid, kernelId := { dev? := d?, ino? := i?, allowAlias := true }, origin := .hostDynamic,
          owner := { ownedByUid := owned, inGroup := inGrp, uidMapped := uMap, gidMapped := gMap }, nlink := 1 }
      let (sa, stdinIno) := match matchDevAlias cfg.stdinKernelDev? cfg.stdinKernelIno? with
        | some ino => (sa, ino)
        | none =>
          seedAllocNode sa (mkStdNode cfg.stdinKind cfg.stdinDevKind? cfg.stdinMode cfg.stdinMountId
            cfg.stdinKernelDev? cfg.stdinKernelIno? cfg.stdinOwnedByUid cfg.stdinInGroup cfg.stdinUidMapped cfg.stdinGidMapped)
      let (sa, stdoutIno) :=
        if sameDevIno cfg.stdoutKernelDev? cfg.stdoutKernelIno? cfg.stdinKernelDev? cfg.stdinKernelIno? then (sa, stdinIno)
        else match matchDevAlias cfg.stdoutKernelDev? cfg.stdoutKernelIno? with
          | some ino => (sa, ino)
          | none =>
            seedAllocNode sa (mkStdNode cfg.stdoutKind cfg.stdoutDevKind? cfg.stdoutMode cfg.stdoutMountId
              cfg.stdoutKernelDev? cfg.stdoutKernelIno? cfg.stdoutOwnedByUid cfg.stdoutInGroup cfg.stdoutUidMapped cfg.stdoutGidMapped)
      let (sa, stderrIno) :=
        if sameDevIno cfg.stderrKernelDev? cfg.stderrKernelIno? cfg.stdinKernelDev? cfg.stdinKernelIno? then (sa, stdinIno)
        else if sameDevIno cfg.stderrKernelDev? cfg.stderrKernelIno? cfg.stdoutKernelDev? cfg.stdoutKernelIno? then (sa, stdoutIno)
        else match matchDevAlias cfg.stderrKernelDev? cfg.stderrKernelIno? with
          | some ino => (sa, ino)
          | none =>
            seedAllocNode sa (mkStdNode cfg.stderrKind cfg.stderrDevKind? cfg.stderrMode cfg.stderrMountId
              cfg.stderrKernelDev? cfg.stderrKernelIno? cfg.stderrOwnedByUid cfg.stderrInGroup cfg.stderrUidMapped cfg.stderrGidMapped)
      let procDir (m : Mode) (owned : Bool) (uMap : Bool := true) (gMap : Bool := true) (inGrp : Bool := true) : VNode :=
        { data := .dir {}, mode := m, mountId := 2, origin := .pseudoFs,
          owner := { ownedByUid := owned, inGroup := inGrp, uidMapped := uMap, gidMapped := gMap }, nlink := 2 }
      let (sa, procIno) := seedInsertAtPath sa 0 (asciiBytes ['p', 'r', 'o', 'c'])
        (procDir 0o555 false cfg.hostUidMapped cfg.hostGidMapped cfg.hostSyntheticInGroup)
      let procReg (m : Mode) (owned : Bool := true) (uMap : Bool := true) (gMap : Bool := true) (inGrp : Bool := true) : VNode :=
        { data := .reg {}, mode := m, mountId := 2, origin := .pseudoFs,
          owner := { ownedByUid := owned, inGroup := inGrp, uidMapped := uMap, gidMapped := gMap }, nlink := 1 }
      let procMagic (tgt : InodeId) (owned : Bool := true) (m : Mode := 0o777)
          (uMap : Bool := true) (gMap : Bool := true) (inGrp : Bool := true) : VNode :=
        { data := .symlink (.procMagic tgt), mode := m, mountId := 2, origin := .pseudoFs,
          kernelId := { allowAlias := true },
          owner := { ownedByUid := owned, inGroup := inGrp, uidMapped := uMap, gidMapped := gMap }, nlink := 1 }
      let pidOne := asciiBytes ['1']
      let selfIsOne := bytesEq cfg.selfPidBytes pidOne
      let initOwned := cfg.proc1OwnedByUid || selfIsOne
      let initInGrp := if selfIsOne then cfg.selfInGroup else cfg.proc1InGroup
      let initUMap := if selfIsOne then selfUMap else (cfg.proc1UidMapped || (cfg.proc1OwnedByUid && selfUMap))
      let initGMap := if selfIsOne then selfGMap else (cfg.proc1GidMapped || (cfg.proc1OwnedByUid && selfGMap))
      let (sa, proc1CwdIno) :=
        if selfIsOne || sameDevIno cfg.proc1CwdKernelDev? cfg.proc1CwdKernelIno? cfg.cwdKernelDev? cfg.cwdKernelIno? then
          (sa, cwdIno)
        else if sameDevIno cfg.proc1CwdKernelDev? cfg.proc1CwdKernelIno? cfg.rootKernelDev? cfg.rootKernelIno? then
          (sa, 0)
        else
          seedAllocNode sa
            { data := .dir {}, mode := cfg.proc1CwdMode, mountId := cfg.proc1CwdMountId,
              kernelId := { dev? := cfg.proc1CwdKernelDev?, ino? := cfg.proc1CwdKernelIno?, allowAlias := true },
              origin := .hostDynamic, nlink := 2,
              owner := {
                ownedByUid := cfg.proc1CwdOwnedByUid?.getD cfg.proc1OwnedByUid
                inGroup := cfg.proc1CwdInGroup?.getD initInGrp
                uidMapped := cfg.proc1CwdUidMapped?.getD initUMap
                gidMapped := cfg.proc1CwdGidMapped?.getD initGMap } }
      let (sa, proc1Fd0Ino) :=
        if selfIsOne || sameDevIno cfg.proc1Fd0KernelDev? cfg.proc1Fd0KernelIno? cfg.stdinKernelDev? cfg.stdinKernelIno? then
          (sa, stdinIno)
        else if sameDevIno cfg.proc1Fd0KernelDev? cfg.proc1Fd0KernelIno? cfg.stdoutKernelDev? cfg.stdoutKernelIno? then
          (sa, stdoutIno)
        else if sameDevIno cfg.proc1Fd0KernelDev? cfg.proc1Fd0KernelIno? cfg.stderrKernelDev? cfg.stderrKernelIno? then
          (sa, stderrIno)
        else match matchDevAlias cfg.proc1Fd0KernelDev? cfg.proc1Fd0KernelIno? with
          | some ino => (sa, ino)
          | none =>
            seedAllocNode sa (mkStdNode cfg.proc1Fd0Kind cfg.proc1Fd0DevKind? cfg.proc1Fd0Mode cfg.proc1Fd0MountId
              cfg.proc1Fd0KernelDev? cfg.proc1Fd0KernelIno?
              (cfg.proc1Fd0OwnedByUid?.getD cfg.proc1OwnedByUid)
              (cfg.proc1Fd0InGroup?.getD initInGrp)
              (cfg.proc1Fd0UidMapped?.getD initUMap)
              (cfg.proc1Fd0GidMapped?.getD initGMap))
      let (sa, pid1Ino) := seedInsertAtPath sa procIno pidOne (procDir 0o555 initOwned initUMap initGMap initInGrp)
      let (sa, _) := seedInsertAtPath sa pid1Ino (asciiBytes ['s', 't', 'a', 't', 'u', 's'])
        (procReg 0o444 initOwned initUMap initGMap initInGrp)
      let (sa, _) := seedInsertAtPath sa pid1Ino (asciiBytes ['c', 'w', 'd'])
        (procMagic proc1CwdIno initOwned 0o777 initUMap initGMap initInGrp)
      let (sa, p1FdDirIno) := seedInsertAtPath sa pid1Ino (asciiBytes ['f', 'd'])
        (procDir 0o500 initOwned initUMap initGMap initInGrp)
      let (sa, _) := seedInsertAtPath sa p1FdDirIno (asciiBytes ['0'])
        (procMagic proc1Fd0Ino initOwned (if selfIsOne then cfg.procFd0LinkMode else cfg.proc1Fd0LinkMode) initUMap initGMap initInGrp)
      let (sa, selfIno) :=
        if selfIsOne then (sa, pid1Ino)
        else seedInsertAtPath sa procIno cfg.selfPidBytes (procDir 0o555 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) :=
        if selfIsOne then (sa, 0)
        else seedInsertAtPath sa selfIno (asciiBytes ['s', 't', 'a', 't', 'u', 's']) (procReg 0o444 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa selfIno (asciiBytes ['c', 'm', 'd', 'l', 'i', 'n', 'e']) (procReg 0o444 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa selfIno (asciiBytes ['s', 't', 'a', 't']) (procReg 0o444 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa selfIno
        (asciiBytes ['o', 'o', 'm', '_', 's', 'c', 'o', 'r', 'e', '_', 'a', 'd', 'j']) (procReg 0o644 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa selfIno (asciiBytes ['e', 'x', 'e']) (procMagic exeTargetIno true 0o777 selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) :=
        if selfIsOne then (sa, 0)
        else seedInsertAtPath sa selfIno (asciiBytes ['c', 'w', 'd']) (procMagic cwdIno true 0o777 selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa selfIno (asciiBytes ['r', 'o', 'o', 't']) (procMagic 0 true 0o777 selfUMap selfGMap cfg.selfInGroup)
      let (sa, fdDirIno) :=
        if selfIsOne then (sa, p1FdDirIno)
        else seedInsertAtPath sa selfIno (asciiBytes ['f', 'd']) (procDir 0o500 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) :=
        if selfIsOne then (sa, 0)
        else seedInsertAtPath sa fdDirIno (asciiBytes ['0']) (procMagic stdinIno true cfg.procFd0LinkMode selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa fdDirIno (asciiBytes ['1']) (procMagic stdoutIno true cfg.procFd1LinkMode selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa fdDirIno (asciiBytes ['2']) (procMagic stderrIno true cfg.procFd2LinkMode selfUMap selfGMap cfg.selfInGroup)
      let (sa, fdinfoDirIno) := seedInsertAtPath sa selfIno
        (asciiBytes ['f', 'd', 'i', 'n', 'f', 'o']) (procDir 0o500 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa fdinfoDirIno (asciiBytes ['0']) (procReg 0o400 true selfUMap selfGMap cfg.selfInGroup)
      let (sa, _) := seedInsertAtPath sa procIno (asciiBytes ['s', 'e', 'l', 'f'])
        { data := .symlink (.path cfg.selfPidBytes), mode := 0o777, mountId := 2, origin := .pseudoFs,
          owner := { ownedByUid := true, inGroup := cfg.selfInGroup, uidMapped := selfUMap, gidMapped := selfGMap }, nlink := 1 }
      let sysOrigin : InodeOrigin := if cfg.hostSyntheticOwnedByUid then .hostDynamic else .pseudoFs
      let sysDir (m : Mode) : VNode :=
        { data := .dir {}, mode := m, mountId := cfg.sysMountId, origin := sysOrigin,
          owner := {
            ownedByUid := cfg.hostSyntheticOwnedByUid
            inGroup := cfg.hostSyntheticOwnedByUid || cfg.hostSyntheticInGroup
            uidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostUidMapped
            gidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostGidMapped },
          nlink := 2 }
      let (sa, sysIno) := seedInsertAtPath sa 0 (asciiBytes ['s', 'y', 's']) (sysDir 0o555)
      let (sa, kernIno) := seedInsertAtPath sa sysIno
        (asciiBytes ['k', 'e', 'r', 'n', 'e', 'l']) (sysDir 0o755)
      let sysReg (m : Mode) : VNode :=
        { data := .reg {}, mode := m, mountId := cfg.sysMountId, origin := sysOrigin,
          owner := {
            ownedByUid := cfg.hostSyntheticOwnedByUid
            inGroup := cfg.hostSyntheticOwnedByUid || cfg.hostSyntheticInGroup
            uidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostUidMapped
            gidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostGidMapped },
          nlink := 1 }
      let (sa, _) := seedInsertAtPath sa kernIno
        (asciiBytes ['c', 'p', 'u', '_', 'b', 'y', 't', 'e', 'o', 'r', 'd', 'e', 'r']) (sysReg 0o444)
      let (sa, _) := seedInsertAtPath sa kernIno
        (asciiBytes ['p', 'r', 'o', 'f', 'i', 'l', 'i', 'n', 'g']) (sysReg 0o644)
      let (sa, _) := seedInsertAtPath sa kernIno (asciiBytes ['d', 'e', 'b', 'u', 'g']) (sysDir 0o700)
      let (sa, _) := seedInsertAtPath sa kernIno
        (asciiBytes ['c', 'r', 'a', 's', 'h', '_', 'e', 'l', 'f', 'c', 'o', 'r', 'e', 'h', 'd', 'r', '_', 's', 'i', 'z', 'e'])
        { data := .symlink (.path (ByteArray.mk #[])), mode := 0o777, mountId := cfg.sysMountId, origin := sysOrigin,
          owner := {
            ownedByUid := cfg.hostSyntheticOwnedByUid
            inGroup := cfg.hostSyntheticOwnedByUid || cfg.hostSyntheticInGroup
            uidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostUidMapped
            gidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostGidMapped },
          nlink := 1 }
      if cfg.chrootUnreachable then sa
      else
        (seedEnsureDirSegs sa 0 [asciiBytes ['t', 'm', 'p']]
          { hostDirTpl with
            mode := 0o1777
            owner := {
              ownedByUid := cfg.hostSyntheticOwnedByUid
              inGroup := cfg.hostSyntheticOwnedByUid || cfg.hostSyntheticInGroup
              uid? := some 0
              uidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostUidMapped
              gidMapped := cfg.hostSyntheticOwnedByUid || cfg.hostGidMapped } }).1
  let s5 := seedApplyAncestorInGroups
    (seedApplyAncestorMapped
      (seedApplyAncestorOwnerUids (seedApplyAncestorMeta s4 cfg.ancestorMeta) cfg.ancestorOwnerUids)
      cfg.ancestorMapped)
    cfg.ancestorInGroups
  let s5b :=
    if cfg.chrootUnreachable && cfg.includeHostTree then
      let outerEntries :=
        if cfg.chrootOuterEntries.isEmpty then
          let maxBuiltinMountId :=
            max 5 (max cfg.sysMountId (max cfg.cwdMountId (max cfg.cwdParentMountId
              (max cfg.crossMountId (max cfg.crossParentMountId (max cfg.devMountId
                (max cfg.stdinMountId (max cfg.stdoutMountId (max cfg.stderrMountId
                  (max cfg.proc1CwdMountId cfg.proc1Fd0MountId))))))))))
          let maxSeededMountId :=
            s5.inodes.foldl (fun acc (_, vn) => max acc vn.mountId) maxBuiltinMountId
          let maxAncMountId :=
            cfg.ancestorMeta.foldl (fun acc (_, _, _, mid, _, _) => max acc mid) maxSeededMountId
          let maxProfileMountId :=
            cfg.mountProfiles.foldl (fun acc (mid, _) => max acc mid) maxAncMountId
          let maxEntryMountId (acc : Nat) (entries : List SeedEntry) : Nat :=
            entries.foldl (fun m e => match e.mountId? with | some mid => max m mid | none => m) acc
          let outerSysMountId :=
            maxEntryMountId (maxEntryMountId maxProfileMountId cfg.cwdEntries) cfg.crossEntries + 1
          [ { name := asciiBytes ['e', 't', 'c'], kind := .dir, mode := 0o755, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, dynamicMeta := true },
            { relDir := [asciiBytes ['e', 't', 'c']], name := asciiBytes ['p', 'a', 's', 's', 'w', 'd'], kind := .reg, mode := 0o644, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, dynamicMeta := true },
            { name := asciiBytes ['s', 'y', 's'], kind := .dir, mode := 0o555, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, mountId? := some outerSysMountId, dynamicMeta := true },
            { relDir := [asciiBytes ['s', 'y', 's']], name := asciiBytes ['k', 'e', 'r', 'n', 'e', 'l'], kind := .dir, mode := 0o755, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, mountId? := some outerSysMountId, dynamicMeta := true },
            { relDir := [asciiBytes ['s', 'y', 's'], asciiBytes ['k', 'e', 'r', 'n', 'e', 'l']], name := asciiBytes ['c', 'p', 'u', '_', 'b', 'y', 't', 'e', 'o', 'r', 'd', 'e', 'r'], kind := .reg, mode := 0o444, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, mountId? := some outerSysMountId, dynamicMeta := true },
            { name := asciiBytes ['t', 'm', 'p'], kind := .dir, mode := 0o1777, ownedByUid := false, inGroup := cfg.hostSyntheticInGroup, ownerUid? := some 0, dynamicMeta := true } ]
        else cfg.chrootOuterEntries
      seedApplyOuterEntries s5 outRootIno outerEntries
    else s5
  let s6 := seedApplyEntries s5b cwdIno cfg.cwdMountId cfg.cwdEntries
  match crossIno? with
  | none => s6
  | some cIno => seedApplyEntries s6 cIno cfg.crossMountId cfg.crossEntries

end LeanSwe.LinuxSyscall.Files

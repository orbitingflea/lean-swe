import LeanSweProofs.LinuxSyscall.Files.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.Files`

Defines portable C-ABI wire decoders, the raw `PosixFilesOpsM` single-step
contract (`RawFilesOpsM`, `RawFilesReq`, `RawFilesOut`, `execRawStep`,
`allowedRawStep`, `rawHealthyModelOps`), and package-level `HandleId`
single-step entry points (`HandleFilesOpsM`, `healthyModelOps`, `execPkgStep`,
`allowedPkgStep`) over `HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.Files.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Monad-parameterized raw C-ABI `Files` capability family specialized to `HandleId`. -/
abbrev RawFilesOpsM (m : Type → Type) : Type :=
  Internal.PosixFilesOpsM m HandleId

/-- Monad-parameterized public `Files` capability family specialized to `HandleId`. -/
abbrev HandleFilesOpsM (m : Type → Type) : Type :=
  FilesOpsM m HandleId

/-- Decode portable 2-bit `AccessMode` (`0 = rdonly`, `1 = wronly`, `2 = rdwr`). -/
def decodeRawAccessMode? : UInt32 → Option AccessMode
  | 0 => some .rdonly
  | 1 => some .wronly
  | 2 => some .rdwr
  | _ => none

/-- Decode portable 12-bit `OpenFlags` bitmask (`0..4095`, `bits & 3 != 3`). -/
def decodeRawOpenFlags? (bits : UInt32) : Option OpenFlags :=
  if bits < 4096 then
    match decodeRawAccessMode? (bits &&& 3) with
    | some acc =>
      some { access := acc
             creat := (bits &&& ((1 : UInt32) <<< 2)) != 0
             excl := (bits &&& ((1 : UInt32) <<< 3)) != 0
             trunc := (bits &&& ((1 : UInt32) <<< 4)) != 0
             append := (bits &&& ((1 : UInt32) <<< 5)) != 0
             nofollow := (bits &&& ((1 : UInt32) <<< 6)) != 0
             directory := (bits &&& ((1 : UInt32) <<< 7)) != 0
             nonblock := (bits &&& ((1 : UInt32) <<< 8)) != 0
             cloexec := (bits &&& ((1 : UInt32) <<< 9)) != 0
             noctty := (bits &&& ((1 : UInt32) <<< 10)) != 0
             path := (bits &&& ((1 : UInt32) <<< 11)) != 0 }
    | none => none
  else
    none

/-- Decode portable 6-bit `ResolveFlags` bitmask (`0..63`). -/
def decodeRawResolveFlags? (bits : UInt64) : Option ResolveFlags :=
  if bits < 64 then
    some { noXdev := (bits &&& ((1 : UInt64) <<< 0)) != 0
           noMagiclinks := (bits &&& ((1 : UInt64) <<< 1)) != 0
           noSymlinks := (bits &&& ((1 : UInt64) <<< 2)) != 0
           beneath := (bits &&& ((1 : UInt64) <<< 3)) != 0
           inRoot := (bits &&& ((1 : UInt64) <<< 4)) != 0
           cached := (bits &&& ((1 : UInt64) <<< 5)) != 0 }
  else
    none

/-- Decode portable 3-bit `AtFlags` bitmask (`0..7`). -/
def decodeRawAtFlags? (bits : UInt32) : Option AtFlags :=
  if bits < 8 then
    some { symlinkNofollow := (bits &&& ((1 : UInt32) <<< 0)) != 0
           emptyPath := (bits &&& ((1 : UInt32) <<< 1)) != 0
           eaccess := (bits &&& ((1 : UInt32) <<< 2)) != 0 }
  else
    none

/-- Decode portable 3-bit `AccessModeMask` bitmask (`0..7`). -/
def decodeRawAccessModeMask? (bits : UInt32) : Option AccessModeMask :=
  if bits < 8 then
    some { read := (bits &&& ((1 : UInt32) <<< 0)) != 0
           write := (bits &&& ((1 : UInt32) <<< 1)) != 0
           exec := (bits &&& ((1 : UInt32) <<< 2)) != 0 }
  else
    none

/-- Decode portable `unlinkat` `removeDir` byte (`0 = false`, `1 = true`). -/
def decodeRawUnlinkDir? : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- Decode portable 3-bit `RenameFlags` bitmask (`0..7`). -/
def decodeRawRenameFlags? (bits : UInt32) : Option RenameFlags :=
  if bits < 8 then
    some { noreplace := (bits &&& ((1 : UInt32) <<< 0)) != 0
           exchange := (bits &&& ((1 : UInt32) <<< 1)) != 0
           whiteout := (bits &&& ((1 : UInt32) <<< 2)) != 0 }
  else
    none

/-- Decode portable `FlockOp` bitmask (`1`, `9`, `2`, `10`, `4`). -/
def decodeRawFlockOp? : UInt32 → Option FlockOp
  | 1 => some (.shared false)
  | 9 => some (.shared true)
  | 2 => some (.exclusive false)
  | 10 => some (.exclusive true)
  | 4 => some .unlock
  | _ => none

/-- Decode portable `(cmdTag, arg)` pair into `FcntlCmd`. -/
def decodeRawFcntlCmd? (tag arg : UInt32) : Option FcntlCmd :=
  match tag with
  | 0 => if arg == 0 then some .getFl else none
  | 1 => if arg < 4 then some (.setFl ((arg &&& 1) != 0) ((arg &&& 2) != 0)) else none
  | 2 => if arg == 0 then some .getFd else none
  | 3 =>
    if arg == 0 then some (.setFd false)
    else if arg == 1 then some (.setFd true)
    else none
  | 4 => some (.addSeals arg)
  | 5 => if arg == 0 then some .getSeals else none
  | _ => none

/-- Decode portable `SeekWhence` wire tag (`0..2`). -/
def decodeRawSeekWhence? : UInt32 → Option SeekWhence
  | 0 => some .seekSet
  | 1 => some .seekCur
  | 2 => some .seekEnd
  | _ => none

/-- Decode portable `StdioFd` slot tag (`0..2`). -/
def decodeRawStdioFd? : UInt32 → Option StdioFd
  | 0 => some .stdin
  | 1 => some .stdout
  | 2 => some .stderr
  | _ => none

/-- Encode `FileKind` into its `RawStatTuple` tag (`0..7`). -/
def encodeFileKind : FileKind → UInt8
  | .reg => 0
  | .dir => 1
  | .symlink => 2
  | .fifo => 3
  | .socket => 4
  | .charDev => 5
  | .blockDev => 6
  | .other => 7

/-- Encode `StatInfo` into a `RawStatTuple` for C-ABI witness transport. -/
def encodeRawStatTuple (st : StatInfo) : RawStatTuple :=
  (encodeFileKind st.kind, UInt64.ofNat st.size, st.mode &&& 0o7777,
   st.ino, st.dev, UInt64.ofNat st.nlink,
   st.mtimeSec, st.mtimeNsec, st.atimeSec, st.atimeNsec)

/-- Single-step request sum for `PosixFilesOpsM` C-ABI syscall hooks. -/
inductive RawFilesReq where
  /-- Raw `openat(dir, path, flagsBits, mode)`. -/
  | openat (dir : Option HandleId) (path : ByteArray) (flagsBits : UInt32) (mode : Mode)
  /-- Raw `openat2(dir, path, flagsBits, mode, resolveBits)`. -/
  | openat2 (dir : Option HandleId) (path : ByteArray) (flagsBits : UInt32)
      (mode : Mode) (resolveBits : UInt64)
  /-- Raw `close(hid)`. -/
  | close (hid : HandleId)
  /-- Raw `read(hid, maxBytes)`. -/
  | read (hid : HandleId) (maxBytes : UInt32)
  /-- Raw `write(hid, data)`. -/
  | write (hid : HandleId) (data : ByteArray)
  /-- Raw `fstat(hid)`. -/
  | fstat (hid : HandleId)
  /-- Raw `fstatat(dir, path, flagsBits)`. -/
  | fstatat (dir : Option HandleId) (path : ByteArray) (flagsBits : UInt32)
  /-- Raw `faccessat(dir, path, maskBits, flagsBits)`. -/
  | faccessat (dir : Option HandleId) (path : ByteArray) (maskBits : UInt32) (flagsBits : UInt32)
  /-- Raw `mkdirat(dir, path, mode)`. -/
  | mkdirat (dir : Option HandleId) (path : ByteArray) (mode : Mode)
  /-- Raw `unlinkat(dir, path, removeDirByte)`. -/
  | unlinkat (dir : Option HandleId) (path : ByteArray) (removeDirByte : UInt8)
  /-- Raw `renameat2(oldDir, oldPath, newDir, newPath, flagsBits)`. -/
  | renameat2 (oldDir : Option HandleId) (oldPath : ByteArray) (newDir : Option HandleId)
      (newPath : ByteArray) (flagsBits : UInt32)
  /-- Raw `symlinkat(target, dir, linkPath)`. -/
  | symlinkat (target : ByteArray) (dir : Option HandleId) (linkPath : ByteArray)
  /-- Raw `readlinkat(dir, path, cap)`. -/
  | readlinkat (dir : Option HandleId) (path : ByteArray) (cap : UInt32)
  /-- Raw `getdents64(hid, bufBytes)`. -/
  | getdents64 (hid : HandleId) (bufBytes : UInt32)
  /-- Raw `fchmodat(dir, path, mode)`. -/
  | fchmodat (dir : Option HandleId) (path : ByteArray) (mode : Mode)
  /-- Raw `fchmod(hid, mode)`. -/
  | fchmod (hid : HandleId) (mode : Mode)
  /-- Raw `flock(hid, opBits)`. -/
  | flock (hid : HandleId) (opBits : UInt32)
  /-- Raw `fcntl(hid, cmdTag, arg)`. -/
  | fcntl (hid : HandleId) (cmdTag : UInt32) (arg : UInt32)
  /-- Raw `fsync(hid)`. -/
  | fsync (hid : HandleId)
  /-- Raw `getcwd(cap)`. -/
  | getcwd (cap : UInt32)
  /-- Raw `lseek(hid, offset, whenceRaw)`. -/
  | lseek (hid : HandleId) (offset : Int64) (whenceRaw : UInt32)
  /-- Raw `reopenReadOnly(hid)`. -/
  | reopenReadOnly (hid : HandleId)
  /-- Raw `dupStdio(slotRaw)`. -/
  | dupStdio (slotRaw : UInt32)
  deriving Repr, Inhabited

/-- Single-step output sum for `PosixFilesOpsM` C-ABI syscall hooks. -/
inductive RawFilesOut where
  /-- Succeeded returning `HandleId`. -/
  | opened (hid : HandleId)
  /-- Succeeded returning `Unit`. -/
  | unit
  /-- Succeeded returning `ByteArray`. -/
  | bytes (data : ByteArray)
  /-- Succeeded returning `UInt32`. -/
  | u32 (val : UInt32)
  /-- Succeeded returning `UInt64`. -/
  | u64 (val : UInt64)
  /-- Succeeded returning `RawStatTuple`. -/
  | rawStat (t : RawStatTuple)
  /-- Failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, Inhabited

/-- Wrap `Except Errno HandleId` into `RawFilesOut`. -/
def outcomeOfRawOpened : Except Errno HandleId → RawFilesOut
  | .ok h => .opened h
  | .error e => .err e

/-- Wrap `Except Errno Unit` into `RawFilesOut`. -/
def outcomeOfRawUnit : Except Errno Unit → RawFilesOut
  | .ok () => .unit
  | .error e => .err e

/-- Wrap `Except Errno ByteArray` into `RawFilesOut`. -/
def outcomeOfRawBytes : Except Errno ByteArray → RawFilesOut
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Wrap `Except Errno UInt32` into `RawFilesOut`. -/
def outcomeOfRawU32 : Except Errno UInt32 → RawFilesOut
  | .ok v => .u32 v
  | .error e => .err e

/-- Wrap `Except Errno UInt64` into `RawFilesOut`. -/
def outcomeOfRawU64 : Except Errno UInt64 → RawFilesOut
  | .ok v => .u64 v
  | .error e => .err e

/-- Wrap `Except Errno RawStatTuple` into `RawFilesOut`. -/
def outcomeOfRawStat : Except Errno RawStatTuple → RawFilesOut
  | .ok t => .rawStat t
  | .error e => .err e

/-- Convert a `RawFilesOut` into its domain `FilesOutcome`. -/
def toModelOutcome : RawFilesOut → FilesOutcome
  | .opened h => .opened h
  | .unit => .unit
  | .bytes bs => .bytes bs
  | .u32 v => .u32 v
  | .u64 v => .u64 v
  | .rawStat t => .statted (StatInfo.ofRawTuple t)
  | .err e => .err e

/-- Decode a `RawFilesReq` into its domain `FilesReq` if all wire flags/tags are portable. -/
def decodeRawFilesReq? : RawFilesReq → Option FilesReq
  | .openat dir path flBits mode =>
    (decodeRawOpenFlags? flBits).map (FilesReq.openat dir path · mode)
  | .openat2 dir path flBits mode resBits =>
    match decodeRawOpenFlags? flBits, decodeRawResolveFlags? resBits with
    | some fl, some res => some (.openat2 dir path { flags := fl, mode := mode, resolve := res })
    | _, _ => none
  | .close hid => some (.close hid)
  | .read hid maxBytes => some (.read hid maxBytes)
  | .write hid data => some (.write hid data)
  | .fstat hid => some (.fstat hid)
  | .fstatat dir path flBits =>
    (decodeRawAtFlags? flBits).map (FilesReq.fstatat dir path ·)
  | .faccessat dir path maskBits flBits =>
    match decodeRawAccessModeMask? maskBits, decodeRawAtFlags? flBits with
    | some m, some f => some (.faccessat dir path m f)
    | _, _ => none
  | .mkdirat dir path mode => some (.mkdirat dir path mode)
  | .unlinkat dir path rmByte =>
    (decodeRawUnlinkDir? rmByte).map (FilesReq.unlinkat dir path ·)
  | .renameat2 od op nd np flBits =>
    (decodeRawRenameFlags? flBits).map (FilesReq.renameat2 od op nd np ·)
  | .symlinkat target dir linkPath => some (.symlinkat target dir linkPath)
  | .readlinkat dir path cap => some (.readlinkat dir path cap)
  | .getdents64 hid bufBytes => some (.getdents64 hid bufBytes)
  | .fchmodat dir path mode => some (.fchmodat dir path mode)
  | .fchmod hid mode => some (.fchmod hid mode)
  | .flock hid opBits => (decodeRawFlockOp? opBits).map (FilesReq.flock hid ·)
  | .fcntl hid tag arg => (decodeRawFcntlCmd? tag arg).map (FilesReq.fcntl hid ·)
  | .fsync hid => some (.fsync hid)
  | .getcwd cap => some (.getcwd cap)
  | .lseek hid off whRaw => (decodeRawSeekWhence? whRaw).map (FilesReq.lseek hid off ·)
  | .reopenReadOnly hid => some (.reopenReadOnly hid)
  | .dupStdio slotRaw => (decodeRawStdioFd? slotRaw).map FilesReq.dupStdio

/-- Execute one `RawFilesReq` against a `RawFilesOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : RawFilesOpsM (StateM W)) :
    RawFilesReq → StateM W RawFilesOut
  | .openat d p fl md => outcomeOfRawOpened <$> raw.openat d p fl md
  | .openat2 d p fl md rs => outcomeOfRawOpened <$> raw.openat2 d p fl md rs
  | .close h => outcomeOfRawUnit <$> raw.close h
  | .read h n => outcomeOfRawBytes <$> raw.read h n
  | .write h bs => outcomeOfRawU32 <$> raw.write h bs
  | .fstat h => outcomeOfRawStat <$> raw.fstat h
  | .fstatat d p fl => outcomeOfRawStat <$> raw.fstatat d p fl
  | .faccessat d p mk fl => outcomeOfRawUnit <$> raw.faccessat d p mk fl
  | .mkdirat d p md => outcomeOfRawUnit <$> raw.mkdirat d p md
  | .unlinkat d p rm => outcomeOfRawUnit <$> raw.unlinkat d p rm
  | .renameat2 od op nd np fl => outcomeOfRawUnit <$> raw.renameat2 od op nd np fl
  | .symlinkat t d lp => outcomeOfRawUnit <$> raw.symlinkat t d lp
  | .readlinkat d p c => outcomeOfRawBytes <$> raw.readlinkat d p c
  | .getdents64 h c => outcomeOfRawBytes <$> raw.getdents64 h c
  | .fchmodat d p md => outcomeOfRawUnit <$> raw.fchmodat d p md
  | .fchmod h md => outcomeOfRawUnit <$> raw.fchmod h md
  | .flock h op => outcomeOfRawUnit <$> raw.flock h op
  | .fcntl h tg ag => outcomeOfRawU32 <$> raw.fcntl h tg ag
  | .fsync h => outcomeOfRawUnit <$> raw.fsync h
  | .getcwd c => outcomeOfRawBytes <$> raw.getcwd c
  | .lseek h off wh => outcomeOfRawU64 <$> raw.lseek h off wh
  | .reopenReadOnly h => outcomeOfRawOpened <$> raw.reopenReadOnly h
  | .dupStdio sl => outcomeOfRawOpened <$> raw.dupStdio sl

/-- Allowed single-step relation for `PosixFilesOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawFilesReq) (out : RawFilesOut)
    (env' : HealthyEnv) : Prop :=
  match decodeRawFilesReq? req with
  | some freq => healthyStep env freq (toModelOutcome out) = some env'
  | none => out = .err Errno.EINVAL ∧ env' = env

/-- Non-critical, non-`EINTR` fallback `Errno` accepted by `healthyStep` on any non-`close` `FilesReq`. -/
def fallbackFilesErrno (s : FilesState) (req : FilesReq) : Errno :=
  match evalReq s req with
  | .wrapperErr e => e
  | _ => Errno.EMFILE

/-- Run `evalModel` for a non-`close` `FilesReq` over `HealthyEnv`, falling back to `fallbackFilesErrno` whenever `healthyStep` or `extraOk` rejects the candidate outcome. -/
def runHealthyFilesOp {α : Type}
    (req : FilesReq)
    (pack : Except Errno α → FilesOutcome)
    (unpack : FilesOutcome → Option (Except Errno α))
    (extraOk : Except Errno α → Bool := fun _ => true) :
    StateM HealthyEnv (Except Errno α) := fun env =>
  let fbErr := fallbackFilesErrno env.state req
  let runFb (_ : Unit) : Except Errno α × HealthyEnv :=
    match healthyStep env req (.err fbErr) with
    | some envFb => (.error fbErr, envFb)
    | none => (.error fbErr, env)
  let (candOut, _) := evalModel env.state req
  match unpack candOut with
  | some candRes =>
    if extraOk candRes then
      match healthyStep env req (pack candRes) with
      | some env' => if env'.wf then (candRes, env') else runFb ()
      | none => runFb ()
    else
      runFb ()
  | none => runFb ()

/-- Check that a `StatInfo` outcome round-trips losslessly through `encodeRawStatTuple`. -/
def statResFitsRaw : Except Errno StatInfo → Bool
  | .ok st => decide (StatInfo.ofRawTuple (encodeRawStatTuple st) = st)
  | .error _ => true

/-- Reference `HandleFilesOpsM (StateM HealthyEnv)` satisfying `healthyStep` from every well-formed `HealthyEnv`. -/
def healthyModelOps : HandleFilesOpsM (StateM HealthyEnv) :=
  { openat := fun d p fl md =>
      runHealthyFilesOp (.openat d p fl md) outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    openat2 := fun d p how =>
      runHealthyFilesOp (.openat2 d p how) outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    close := fun hid env =>
      let (res, s') := (modelOps.close hid).run env.state
      (res, { env with state := s' })
    read := fun h n =>
      runHealthyFilesOp (.read h n) outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    write := fun h bs =>
      runHealthyFilesOp (.write h bs) outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    fstat := fun h =>
      runHealthyFilesOp (.fstat h) outcomeOfStatted
        (fun | .statted st => some (.ok st) | .err e => some (.error e) | _ => none)
        statResFitsRaw
    fstatat := fun d p fl =>
      runHealthyFilesOp (.fstatat d p fl) outcomeOfStatted
        (fun | .statted st => some (.ok st) | .err e => some (.error e) | _ => none)
        statResFitsRaw
    faccessat := fun d p mk fl =>
      runHealthyFilesOp (.faccessat d p mk fl) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    mkdirat := fun d p md =>
      runHealthyFilesOp (.mkdirat d p md) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    unlinkat := fun d p rm =>
      runHealthyFilesOp (.unlinkat d p rm) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    renameat2 := fun od op nd np fl =>
      runHealthyFilesOp (.renameat2 od op nd np fl) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    symlinkat := fun t d lp =>
      runHealthyFilesOp (.symlinkat t d lp) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    readlinkat := fun d p c =>
      runHealthyFilesOp (.readlinkat d p c) outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    getdents64 := fun h c =>
      runHealthyFilesOp (.getdents64 h c) outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    fchmodat := fun d p md =>
      runHealthyFilesOp (.fchmodat d p md) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    fchmod := fun h md =>
      runHealthyFilesOp (.fchmod h md) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    flock := fun h op =>
      runHealthyFilesOp (.flock h op) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    fcntl := fun h cmd =>
      runHealthyFilesOp (.fcntl h cmd) outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    fsync := fun h =>
      runHealthyFilesOp (.fsync h) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getcwd := fun c =>
      runHealthyFilesOp (.getcwd c) outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    lseek := fun h off wh =>
      runHealthyFilesOp (.lseek h off wh) outcomeOfU64
        (fun | .u64 v => some (.ok v) | .err e => some (.error e) | _ => none)
    reopenReadOnly := fun h =>
      runHealthyFilesOp (.reopenReadOnly h) outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    dupStdio := fun sl =>
      runHealthyFilesOp (.dupStdio sl) outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none) }

/-- Reference `RawFilesOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : RawFilesOpsM (StateM HealthyEnv) :=
  { openat := fun d p flBits md =>
      match decodeRawOpenFlags? flBits with
      | some fl => healthyModelOps.openat d p fl md
      | none => pure (.error Errno.EINVAL)
    openat2 := fun d p flBits md resBits =>
      match decodeRawOpenFlags? flBits, decodeRawResolveFlags? resBits with
      | some fl, some res => healthyModelOps.openat2 d p { flags := fl, mode := md, resolve := res }
      | _, _ => pure (.error Errno.EINVAL)
    close := healthyModelOps.close
    read := healthyModelOps.read
    write := healthyModelOps.write
    fstat := fun h => do
      match ← healthyModelOps.fstat h with
      | .ok st => return .ok (encodeRawStatTuple st)
      | .error e => return .error e
    fstatat := fun d p flBits =>
      match decodeRawAtFlags? flBits with
      | some fl => do
        match ← healthyModelOps.fstatat d p fl with
        | .ok st => return .ok (encodeRawStatTuple st)
        | .error e => return .error e
      | none => pure (.error Errno.EINVAL)
    faccessat := fun d p mkBits flBits =>
      match decodeRawAccessModeMask? mkBits, decodeRawAtFlags? flBits with
      | some mk, some fl => healthyModelOps.faccessat d p mk fl
      | _, _ => pure (.error Errno.EINVAL)
    mkdirat := healthyModelOps.mkdirat
    unlinkat := fun d p rmByte =>
      match decodeRawUnlinkDir? rmByte with
      | some rm => healthyModelOps.unlinkat d p rm
      | none => pure (.error Errno.EINVAL)
    renameat2 := fun od op nd np flBits =>
      match decodeRawRenameFlags? flBits with
      | some fl => healthyModelOps.renameat2 od op nd np fl
      | none => pure (.error Errno.EINVAL)
    symlinkat := healthyModelOps.symlinkat
    readlinkat := healthyModelOps.readlinkat
    getdents64 := healthyModelOps.getdents64
    fchmodat := healthyModelOps.fchmodat
    fchmod := healthyModelOps.fchmod
    flock := fun h opBits =>
      match decodeRawFlockOp? opBits with
      | some op => healthyModelOps.flock h op
      | none => pure (.error Errno.EINVAL)
    fcntl := fun h tg ag =>
      match decodeRawFcntlCmd? tg ag with
      | some cmd => healthyModelOps.fcntl h cmd
      | none => pure (.error Errno.EINVAL)
    fsync := healthyModelOps.fsync
    getcwd := healthyModelOps.getcwd
    lseek := fun h off whRaw =>
      match decodeRawSeekWhence? whRaw with
      | some wh => healthyModelOps.lseek h off wh
      | none => pure (.error Errno.EINVAL)
    reopenReadOnly := healthyModelOps.reopenReadOnly
    dupStdio := fun slRaw =>
      match decodeRawStdioFd? slRaw with
      | some sl => healthyModelOps.dupStdio sl
      | none => pure (.error Errno.EINVAL) }

/-- Execute one `FilesReq` over any `[Monad m]` `HandleFilesOpsM` capability bundle. -/
def execFilesReqM {m : Type → Type} [Monad m]
    (ops : HandleFilesOpsM m) : FilesReq → m FilesOutcome
  | .openat d p fl md => do let r ← ops.openat d p fl md; return outcomeOfOpened r
  | .openat2 d p how => do let r ← ops.openat2 d p how; return outcomeOfOpened r
  | .close h => do let r ← ops.close h; return outcomeOfUnit r
  | .read h n => do let r ← ops.read h n; return outcomeOfBytes r
  | .write h bs => do let r ← ops.write h bs; return outcomeOfU32 r
  | .fstat h => do let r ← ops.fstat h; return outcomeOfStatted r
  | .fstatat d p fl => do let r ← ops.fstatat d p fl; return outcomeOfStatted r
  | .faccessat d p mk fl => do let r ← ops.faccessat d p mk fl; return outcomeOfUnit r
  | .mkdirat d p md => do let r ← ops.mkdirat d p md; return outcomeOfUnit r
  | .unlinkat d p rm => do let r ← ops.unlinkat d p rm; return outcomeOfUnit r
  | .renameat2 od op nd np fl => do let r ← ops.renameat2 od op nd np fl; return outcomeOfUnit r
  | .symlinkat t d lp => do let r ← ops.symlinkat t d lp; return outcomeOfUnit r
  | .readlinkat d p c => do let r ← ops.readlinkat d p c; return outcomeOfBytes r
  | .getdents64 h c => do let r ← ops.getdents64 h c; return outcomeOfBytes r
  | .fchmodat d p md => do let r ← ops.fchmodat d p md; return outcomeOfUnit r
  | .fchmod h md => do let r ← ops.fchmod h md; return outcomeOfUnit r
  | .flock h op => do let r ← ops.flock h op; return outcomeOfUnit r
  | .fcntl h cmd => do let r ← ops.fcntl h cmd; return outcomeOfU32 r
  | .fsync h => do let r ← ops.fsync h; return outcomeOfUnit r
  | .getcwd c => do let r ← ops.getcwd c; return outcomeOfBytes r
  | .lseek h off wh => do let r ← ops.lseek h off wh; return outcomeOfU64 r
  | .reopenReadOnly h => do let r ← ops.reopenReadOnly h; return outcomeOfOpened r
  | .dupStdio sl => do let r ← ops.dupStdio sl; return outcomeOfOpened r

/-- Execute one `FilesReq` against a `HandleFilesOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : HandleFilesOpsM (StateM W)) (req : FilesReq) :
    StateM W FilesOutcome :=
  execFilesReqM ops req

/-- Allowed single-step relation for `FilesOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : FilesReq) (out : FilesOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Capability-parametric function family `Option HandleId → m Unit` of `Files.closeOpt`. -/
abbrev CloseOptFn (m : Type → Type) : Type :=
  Option HandleId → m Unit

/-- Execute `Files.closeOpt` on `optFd` inside `StateM W`. -/
def execCloseOpt {W : Type} (fn : CloseOptFn (StateM W)) (optFd : Option HandleId) :
    StateM W Unit :=
  fn optFd

/-- Relational single-step postcondition for `Files.closeOpt` over `HealthyEnv`. -/
def allowedCloseOpt (env : HealthyEnv) (optFd : Option HandleId) (_ : Unit)
    (env' : HealthyEnv) : Prop :=
  match optFd with
  | none => env.wf = true ∧ env' = env
  | some h => ∃ r : Except Errno Unit, healthyStep env (.close h) (outcomeOfUnit r) = some env'

/-- Capability-parametric function family `Option HandleId → m Unit` of `Files.setNonblockingOpt`. -/
abbrev SetNonblockingOptFn (m : Type → Type) : Type :=
  Option HandleId → m Unit

/-- Execute `Files.setNonblockingOpt` on `optFd` inside `StateM W`. -/
def execSetNonblockingOpt {W : Type} (fn : SetNonblockingOptFn (StateM W))
    (optFd : Option HandleId) : StateM W Unit :=
  fn optFd

/-- Relational single-step postcondition for `Files.setNonblockingOpt` over `HealthyEnv`. -/
def allowedSetNonblockingOpt (env : HealthyEnv) (optFd : Option HandleId) (_ : Unit)
    (env' : HealthyEnv) : Prop :=
  match optFd with
  | none => env.wf = true ∧ env' = env
  | some h =>
    ∃ r : Except Errno UInt32,
      healthyStep env (.fcntl h (.setFl true false)) (outcomeOfU32 r) = some env'

end LeanSwe.LinuxSyscall.Files.Model

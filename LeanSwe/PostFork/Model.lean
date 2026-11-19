import Std.Data.HashSet
import LeanSwe.PostFork.Types

namespace LeanSwe.PostFork.Model

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Failure-wire magic byte (`0x50` = `'P'`). -/
def WIRE_MAGIC : UInt8 := 0x50

/-- Failure-wire protocol version byte (`0x01`). -/
def WIRE_VERSION : UInt8 := 0x01

/-- Wire stage tag for pre-execution validation errors (`1`). -/
def STAGE_VALIDATE : UInt8 := 1
/-- Wire stage tag for `setpgid(0, 0)` errors (`2`). -/
def STAGE_PROCESS_GROUP : UInt8 := 2
/-- Wire stage tag for `SIGPIPE` reset/unblock errors (`3`). -/
def STAGE_SIGNAL_RESET : UInt8 := 3
/-- Wire stage tag for FD probe/relocation/stdio/cloexec errors (`4`). -/
def STAGE_FD_SETUP : UInt8 := 4
/-- Wire stage tag for `close_fds_above2_except` errors (`5`). -/
def STAGE_CLOSE_UNKEPT : UInt8 := 5
/-- Wire stage tag for `chdir` errors (`6`). -/
def STAGE_CHDIR : UInt8 := 6
/-- Wire stage tag for `execve` errors (`7`). -/
def STAGE_EXECVE : UInt8 := 7

/-- Child flag bit `0`: invoke `setpgid(0, 0)`. -/
def FLAG_SET_PGID : UInt32 := 1
/-- Child flag bit `1`: reset `SIGPIPE` to `SIG_DFL` and unblock `SIGPIPE`. -/
def FLAG_RESET_SIGPIPE : UInt32 := 2
/-- Child flag bit `2`: wait for 1-byte token on `sync_r` (`_exit(125)` on EOF). -/
def FLAG_HAS_SYNC_BARRIER : UInt32 := 4
/-- Child flag bit `3`: redirect `(stdin, stdout, stderr)` onto `(0, 1, 2)` and relocate `rep_w`. -/
def FLAG_REDIRECT_STDIO : UInt32 := 8
/-- Child flag bit `4`: close unkept descriptors `> 2` via `close_range` + `/proc/self/fd`. -/
def FLAG_CLOSE_UNKEPT_ABOVE2 : UInt32 := 16
/-- Child flag bit `5`: close redirected stdio source descriptors `> 2` in `setup_stdio`. -/
def FLAG_CLOSE_STDIO_SOURCES : UInt32 := 32

/-- Map a `FailureStage` to its wire tag byte (`none` for host-only `.wireTruncated`). -/
def FailureStage.toTag? : FailureStage → Option UInt8
  | .validate => some STAGE_VALIDATE
  | .processGroup => some STAGE_PROCESS_GROUP
  | .signalReset => some STAGE_SIGNAL_RESET
  | .fdSetup => some STAGE_FD_SETUP
  | .closeUnkept => some STAGE_CLOSE_UNKEPT
  | .chdir => some STAGE_CHDIR
  | .execve => some STAGE_EXECVE
  | .wireTruncated => none

/-- Decode a wire stage tag byte (`1..7`). -/
def FailureStage.ofTag? (tag : UInt8) : Option FailureStage :=
  match tag.toNat with
  | 1 => some .validate
  | 2 => some .processGroup
  | 3 => some .signalReset
  | 4 => some .fdSetup
  | 5 => some .closeUnkept
  | 6 => some .chdir
  | 7 => some .execve
  | _ => none

/-- Total 2's-complement 32-bit signed integer comparison. -/
@[inline] def i32Le (a b : Int32) : Bool :=
  decide (a.toInt ≤ b.toInt)

/-- Construct a `ChildFailure` normalizing non-positive/out-of-range errnos to `Errno.EIO`. -/
def normalizeWireErrno (raw : UInt32) : Errno :=
  if 1 ≤ raw.toNat && raw.toNat ≤ 4095 then raw else Errno.EIO

/-- Pack a signed 32-bit integer in 4 little-endian bytes. -/
def packI32Le (v : Int32) : ByteArray :=
  let u := v.toUInt32.toNat
  ByteArray.mk #[
    UInt8.ofNat (u % 256),
    UInt8.ofNat ((u / 256) % 256),
    UInt8.ofNat ((u / 65536) % 256),
    UInt8.ofNat ((u / 16777216) % 256)
  ]

/-- Concatenate two `ByteArray` values cleanly without internal kernel wrappers. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  b.foldl (fun acc x => acc.push x) a

/-- Concatenate a list of packed `Int32` values into little-endian bytes. -/
def packI32LeList (xs : List Int32) : ByteArray :=
  xs.foldl (fun acc x => appendBytes acc (packI32Le x)) ByteArray.empty

/-- Encode a child failure `(stage, errno)` into the uniform 8-byte wire frame `[0x50, 0x01, stage, 0x00, err_le32]`. -/
def encodeFailureReport (stage : FailureStage) (err : Errno) : ByteArray :=
  let tag := (FailureStage.toTag? stage).getD STAGE_EXECVE
  let e := normalizeWireErrno err
  let u := e.toNat
  ByteArray.mk #[
    WIRE_MAGIC,
    WIRE_VERSION,
    tag,
    0,
    UInt8.ofNat (u % 256),
    UInt8.ofNat ((u / 256) % 256),
    UInt8.ofNat ((u / 65536) % 256),
    UInt8.ofNat ((u / 16777216) % 256)
  ]

/-- Decode the uniform 8-byte failure report read from `repR` (`none` on 0-byte `EOF` indicating `execve` succeeded). -/
def decodeChildFailure (bs : ByteArray) : Option ChildFailure :=
  if bs.size == 0 then
    none
  else if bs.size != 8 then
    some { stage := .wireTruncated, errno := Errno.EIO }
  else
    let b0 := bs.get! 0
    let b1 := bs.get! 1
    let b2 := bs.get! 2
    let b3 := bs.get! 3
    if b0 != WIRE_MAGIC || b1 != WIRE_VERSION || b3 != 0 then
      some { stage := .wireTruncated, errno := Errno.EIO }
    else
      match FailureStage.ofTag? b2 with
      | none => some { stage := .wireTruncated, errno := Errno.EIO }
      | some stage =>
        let e0 := (bs.get! 4).toNat
        let e1 := (bs.get! 5).toNat
        let e2 := (bs.get! 6).toNat
        let e3 := (bs.get! 7).toNat
        let rawU := e0 + 256 * e1 + 65536 * e2 + 16777216 * e3
        if 1 ≤ rawU && rawU ≤ 4095 then
          some { stage := stage, errno := UInt32.ofNat rawU }
        else
          some { stage := .wireTruncated, errno := Errno.EIO }

/-- Compute the `LEANSWE_PF_FLAG_*` child setup bitmask for `(spec, withBarrier)`. -/
def flagsOfSpec {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) : UInt32 :=
  let fPgid : UInt32 := match spec.processGroup with | .newGroup => FLAG_SET_PGID | .inherit => 0
  let fSig : UInt32 := match spec.sigpipe with | .resetDefault => FLAG_RESET_SIGPIPE | .inherit => 0
  let fSync : UInt32 := if withBarrier then FLAG_HAS_SYNC_BARRIER else 0
  let fStdio : UInt32 := match spec.stdio with | .redirect .. => FLAG_REDIRECT_STDIO | .inherit => 0
  let fClose : UInt32 := match spec.fdPolicy with | .closeAllAbove2Except _ => FLAG_CLOSE_UNKEPT_ABOVE2 | .inheritNonCloexec _ => 0
  let fCloseSrc : UInt32 := match spec.stdio, spec.fdPolicy with
    | .redirect _ _ _ true, .inheritNonCloexec _ => FLAG_CLOSE_STDIO_SOURCES
    | _, _ => 0
  fPgid ||| fSig ||| fSync ||| fStdio ||| fClose ||| fCloseSrc

/-- Return `true` iff UTF-8 bytes of `s` contain an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNulStr (s : String) : Bool :=
  s.toUTF8.toList.any (· == (0 : UInt8))

/-- Return `true` iff `(k, v)` is a valid NUL-free `KEY=VALUE` environment binding (`k` non-empty, no `'='`). -/
def isValidEnvBinding (kv : String × String) : Bool :=
  !kv.1.isEmpty && !kv.1.contains '=' && !hasEmbeddedNulStr kv.1 && !hasEmbeddedNulStr kv.2

/-- Format valid `(key, value)` bindings as `"KEY=VALUE"` C strings. -/
def formatEnvEntries (env : Array (String × String)) : Array String :=
  env.map (fun (k, v) => s!"{k}={v}")

/-- Extract kept descriptor references from `FdPolicy`. -/
def FdPolicy.keepFds {fd : Type} : FdPolicy fd → Array (FdRef fd)
  | .inheritNonCloexec ks => ks
  | .closeAllAbove2Except ks => ks

/-- Return `true` iff `ref` is either a managed handle or a non-negative `.raw` FD. -/
def FdRef.isNonneg {fd : Type} : FdRef fd → Bool
  | .handle _ => true
  | .raw n => decide (n.toInt ≥ 0)

/-- Return `true` iff two `FdRef` values denote the exact same descriptor (`eqFd` on handles or equal `.raw`). -/
def FdRef.sameRef {fd : Type} (eqFd : fd → fd → Bool) : FdRef fd → FdRef fd → Bool
  | .handle a, .handle b => eqFd a b
  | .raw a, .raw b => a == b
  | _, _ => false

/-- Return `true` iff `tok` has NUL-free strings and non-negative `.raw` FD reference. -/
def ArgToken.isValid {fd : Type} : ArgToken fd → Bool
  | .lit s => !hasEmbeddedNulStr s
  | .fdDecimal r => FdRef.isNonneg r
  | .prefixedFd p r s => !hasEmbeddedNulStr p && !hasEmbeddedNulStr s && FdRef.isNonneg r

/-- Extract the optional `FdRef` inside an `ArgToken`. -/
def ArgToken.ref? {fd : Type} : ArgToken fd → Option (FdRef fd)
  | .lit _ => none
  | .fdDecimal r => some r
  | .prefixedFd _ r _ => some r

/-- Return `true` iff `r` is a raw stdio slot `0`, `1`, or `2`. -/
def FdRef.isRawStdioSlot {fd : Type} : FdRef fd → Bool
  | .raw n => n == 0 || n == 1 || n == 2
  | .handle _ => false

/-- Return `true` iff `closeFds` and `keepFds` share no common descriptor under `eqFd` (`O(N)` on `.raw` descriptors via `Std.HashSet`, and `O(N)` overall when `checkHandles = false`). -/
def disjointFdRefArrays {fd : Type} (eqFd : fd → fd → Bool)
    (closeFds keepFds : Array (FdRef fd)) (checkHandles : Bool := true) : Bool :=
  if closeFds.size ≤ 8 || keepFds.size ≤ 8 then
    if !checkHandles then
      !(closeFds.any (fun c => keepFds.any (FdRef.sameRef (fun _ _ => false) c)))
    else
      !(closeFds.any (fun c => keepFds.any (FdRef.sameRef eqFd c)))
  else
    let rawKeep : Std.HashSet Int32 :=
      keepFds.foldl (fun acc r => match r with | .raw n => acc.insert n | .handle _ => acc)
        (Std.HashSet.emptyWithCapacity keepFds.size)
    if closeFds.any (fun r => match r with | .raw n => rawKeep.contains n | .handle _ => false) then
      false
    else if !checkHandles then
      true
    else
      let closeHandles := closeFds.filterMap (fun r => match r with | .handle h => some h | .raw _ => none)
      let keepHandles := keepFds.filterMap (fun r => match r with | .handle h => some h | .raw _ => none)
      !(closeHandles.any (fun ch => keepHandles.any (eqFd ch)))

/-- Pre-`fork` pure specification validation parameterized by handle equality `eqFd` (`fun _ _ => false` for opaque handles). -/
def validateSpecWith {fd : Type} (eqFd : fd → fd → Bool) (spec : ChildSpecM fd)
    (checkHandles : Bool := true) : Bool :=
  let cwdOk := match spec.cwd with | some d => !hasEmbeddedNulStr d | none => true
  let pathOk := !spec.path.isEmpty && !hasEmbeddedNulStr spec.path
  let argvOk := spec.argv.all ArgToken.isValid
  let envOk := spec.env.all isValidEnvBinding
  let keepFds := FdPolicy.keepFds spec.fdPolicy
  let closeOk := spec.closeFds.all FdRef.isNonneg
  let keepOk := keepFds.all FdRef.isNonneg
  let stdioOk := match spec.stdio with
    | .inherit => true
    | .redirect sIn sOut sErr closeSrcs =>
      FdRef.isNonneg sIn && FdRef.isNonneg sOut && FdRef.isNonneg sErr &&
      !(keepFds.any FdRef.isRawStdioSlot) &&
      !(spec.closeFds.any (fun c => FdRef.sameRef eqFd c sIn || FdRef.sameRef eqFd c sOut || FdRef.sameRef eqFd c sErr)) &&
      match spec.fdPolicy with
      | .inheritNonCloexec _ =>
        if !closeSrcs then true
        else !(keepFds.any (fun k =>
          (!FdRef.isRawStdioSlot k) &&
          (FdRef.sameRef eqFd k sIn || FdRef.sameRef eqFd k sOut || FdRef.sameRef eqFd k sErr)))
      | .closeAllAbove2Except _ => true
  let disjointCloseKeep := disjointFdRefArrays eqFd spec.closeFds keepFds checkHandles
  pathOk && cwdOk && argvOk && envOk && closeOk && keepOk && stdioOk && disjointCloseKeep

/-- Default pure validation checking string hygiene, signs, stdio slots, and `.raw` overlaps in linear `O(N)` time. -/
def validateSpec {fd : Type} (spec : ChildSpecM fd) : Bool :=
  validateSpecWith (fun _ _ => false) spec false

namespace Internal

/-- Low-level 1-syscall host operations consumed by `LeanSwe.PostFork.Impl.mkHostOps`. -/
structure PosixHostOpsM (m : Type → Type) (fd : Type) where
  /-- Probe whether raw OS descriptor `fd` is open (`F_GETFD`). -/
  probeFdOpen : Int32 → m (Except Errno Unit)
  /-- Probe whether managed handle `h` is open (`F_GETFD`). -/
  probeHandleOpen : fd → m (Except Errno Unit)
  /-- Allocate a `pipe2(..., O_CLOEXEC)` pair `(readEnd, writeEnd)`. -/
  mkPipeCloexec : m (Except Errno (fd × fd))
  /-- Close a managed handle `h`. -/
  closeFd : fd → m (Except Errno Unit)
  /-- Invoke `setpgid(pid, pgid)` once. -/
  setpgidOnce : Pid → Pid → m (Except Errno Unit)
  /-- Invoke `write(fd, data[off..off+len))` once. -/
  writeOnce : fd → ByteArray → UInt64 → UInt64 → m (Except Errno UInt64)
  /-- Invoke `read(fd, maxBytes)` once. -/
  readOnce : fd → UInt64 → m (Except Errno ByteArray)
  /-- Invoke `waitpid(pid, &st, 0)` once. -/
  waitOnce : Pid → m (Except Errno ChildWaitStatus)
  /-- Fork a child (directly or via immortal spawner thread) and invoke `leanswe_postfork_run_child`. -/
  forkRun :
    UInt32 → ForkMode → Option fd → fd →
    Array (FdRef fd) → Array (FdRef fd) → Array (FdRef fd) →
    Option String → String → Array (ArgToken fd) → Array String →
    m (Except Errno Pid)

/-- Predicate stating that all operations of `raw` in `IO` terminate without throwing an `IO.Error`. -/
structure NoThrowOps (raw : PosixHostOpsM IO RawFd) : Prop where
  /-- `probeFdOpen` never throws an `IO.Error`. -/
  probeFdOpen_ok : ∀ n w, ∃ r w', raw.probeFdOpen n w = .ok r w'
  /-- `probeHandleOpen` never throws an `IO.Error`. -/
  probeHandleOpen_ok : ∀ h w, ∃ r w', raw.probeHandleOpen h w = .ok r w'
  /-- `mkPipeCloexec` never throws an `IO.Error`. -/
  mkPipeCloexec_ok : ∀ w, ∃ r w', raw.mkPipeCloexec w = .ok r w'
  /-- `closeFd` never throws an `IO.Error`. -/
  closeFd_ok : ∀ h w, ∃ r w', raw.closeFd h w = .ok r w'
  /-- `setpgidOnce` never throws an `IO.Error`. -/
  setpgidOnce_ok : ∀ p g w, ∃ r w', raw.setpgidOnce p g w = .ok r w'
  /-- `writeOnce` never throws an `IO.Error`. -/
  writeOnce_ok : ∀ h d o l w, ∃ r w', raw.writeOnce h d o l w = .ok r w'
  /-- `readOnce` never throws an `IO.Error`. -/
  readOnce_ok : ∀ h c w, ∃ r w', raw.readOnce h c w = .ok r w'
  /-- `waitOnce` never throws an `IO.Error`. -/
  waitOnce_ok : ∀ p w, ∃ r w', raw.waitOnce p w = .ok r w'
  /-- `forkRun` never throws an `IO.Error`. -/
  forkRun_ok : ∀ fl fm sr ew std cl kp cwd path argv env w,
    ∃ r w', raw.forkRun fl fm sr ew std cl kp cwd path argv env w = .ok r w'

/-- Flattened representation of `forkRun` descriptor handles and slots for C FFI marshaling, parameterized over handle type `fd`. -/
structure FlattenedForkArgsM (fd : Type) where
  /-- Managed handles pinned across `fork()`. -/
  handles : Array fd
  /-- Packed 5-slot `Int32` header `[sync_r, rep_w, stdin, stdout, stderr]`. -/
  metaSlots : ByteArray
  /-- Packed `Int32` slots for `closeFds`. -/
  closeSlots : ByteArray
  /-- Packed `Int32` slots for `keepFds`. -/
  keepSlots : ByteArray
  /-- Prefix strings for each `argv` token. -/
  argPrefixes : Array String
  /-- Suffix strings for each `argv` token. -/
  argSuffixes : Array String
  /-- Packed `Int32` descriptor slots (`-1` for `.lit`, `>= 0` for `.raw`, `-(idx+2)` for `.handle`). -/
  argSlots : ByteArray

/-- Real-world `RawFd` specialization of `FlattenedForkArgsM`. -/
abbrev FlattenedForkArgs := FlattenedForkArgsM RawFd

/-- Deterministic in-memory mock host state for pure `SpecTests` verification of `LeanSwe.PostFork.Impl`. -/
structure HostMockState where
  /-- Total primitive calls executed so far. -/
  callCount : Nat := 0
  /-- Next synthetic pipe descriptor number. -/
  nextFd : Int32 := 10
  /-- Caller raw OS descriptors treated as closed (`EBADF`). -/
  closedCallerFds : List Int32 := []
  /-- Managed handles already closed. -/
  closedHandles : List Int32 := []
  /-- Optional primitive call index at which `mkPipeCloexec` fails with `EMFILE`. -/
  failNextPipeAt : Option Nat := none
  /-- Optional `errno` injected into `forkRun`. -/
  failForkErrno : Option Errno := none
  /-- Optional `errno` injected into `setpgidOnce`. -/
  failSetpgidErrno : Option Errno := none
  /-- Remaining transient `EINTR` failures injected into `writeOnce`. -/
  writeEintrCount : Nat := 0
  /-- Optional terminal `errno` injected into `writeOnce`. -/
  failWriteErrno : Option Errno := none
  /-- Remaining transient `EINTR` failures injected into `readOnce`. -/
  readEintrCount : Nat := 0
  /-- Optional terminal `errno` injected into `readOnce`. -/
  failReadErrno : Option Errno := none
  /-- Remaining transient `EINTR` failures injected into `waitOnce`. -/
  waitEintrCount : Nat := 0
  /-- Optional terminal `errno` injected into `waitOnce`. -/
  failWaitErrno : Option Errno := none
  /-- Sync-barrier write handle allocated by the second `mkPipeCloexec`. -/
  allocSyncWriteFd : Int32 := -1
  /-- Failure-report read handle allocated by the first `mkPipeCloexec`. -/
  allocRepReadFd : Int32 := -1
  /-- Queued failure-report wire bytes drained by `readOnce` on `allocRepReadFd`. -/
  repWire : ByteArray := ByteArray.empty
  /-- Reaped child status returned once `waitEintrCount = 0`. -/
  waitResult : ChildWaitStatus := .exited 0
  /-- Handles closed before `forkRun` executed. -/
  closedBeforeFork : List Int32 := []
  /-- All handles closed across the run. -/
  closedFds : List Int32 := []
  /-- Recorded `(pid, pgid)` arguments passed to `setpgidOnce`. -/
  setpgidCalls : List (Pid × Pid) := []
  /-- Sync bytes written to `allocSyncWriteFd`. -/
  syncWritten : ByteArray := ByteArray.empty
  /-- Flags passed to `forkRun`. -/
  spawnedFlags : UInt32 := 0
  /-- `ForkMode` passed to `forkRun`. -/
  spawnedForkMode : ForkMode := .direct
  /-- Resolved `argv` strings passed to `forkRun`. -/
  spawnedArgv : Array String := #[]
  /-- Formatted `KEY=VALUE` environment entries passed to `forkRun`. -/
  spawnedEnv : Array String := #[]
  /-- `closeRefs` array passed to `forkRun`. -/
  spawnedCloseRefs : Array (FdRef Int32) := #[]
  /-- Whether `forkRun` has succeeded. -/
  hasSpawned : Bool := false
  deriving BEq, DecidableEq, Inhabited

/-- Render an `ArgToken Int32` into its resolved child `argv` string in the pure mock model. -/
def renderMockArgToken : ArgToken Int32 → String
  | .lit s => s
  | .fdDecimal (.handle h) => s!"{h}"
  | .fdDecimal (.raw n) => s!"{n}"
  | .prefixedFd p (.handle h) s => s!"{p}{h}{s}"
  | .prefixedFd p (.raw n) s => s!"{p}{n}{s}"

/-- Pure `StateM HostMockState` implementation of `PosixHostOpsM` exercising `EINTR`, `EPIPE`, and barrier races. -/
def mockPosixHostOps : PosixHostOpsM (StateM HostMockState) Int32 where
  probeFdOpen fd := do
    modify fun st => { st with callCount := st.callCount + 1 }
    let st ← get
    if st.closedCallerFds.contains fd then
      return .error Errno.EBADF
    else
      return .ok ()
  probeHandleOpen h := do
    modify fun st => { st with callCount := st.callCount + 1 }
    let st ← get
    if st.closedCallerFds.contains h || st.closedHandles.contains h then
      return .error Errno.EBADF
    else
      return .ok ()
  mkPipeCloexec := do
    let st ← get
    let c := st.callCount
    match st.failNextPipeAt with
    | some k =>
      if c == k then
        set { st with callCount := c + 1 }
        return .error Errno.EMFILE
    | none => pure ()
    let rFd := st.nextFd
    let wFd := st.nextFd + 1
    let isRep := st.allocRepReadFd < 0
    set { st with
      callCount := c + 1
      nextFd := st.nextFd + 2
      allocRepReadFd := if isRep then rFd else st.allocRepReadFd
      allocSyncWriteFd := if isRep then st.allocSyncWriteFd else wFd }
    return .ok (rFd, wFd)
  closeFd h := do
    let st ← get
    if st.closedHandles.contains h then
      set { st with callCount := st.callCount + 1 }
      return .error Errno.EBADF
    else
      set { st with
        callCount := st.callCount + 1
        closedHandles := h :: st.closedHandles
        closedFds := h :: st.closedFds
        closedBeforeFork := if st.hasSpawned then st.closedBeforeFork else h :: st.closedBeforeFork }
      return .ok ()
  setpgidOnce pid pgid := do
    let st ← get
    set { st with callCount := st.callCount + 1, setpgidCalls := st.setpgidCalls ++ [(pid, pgid)] }
    match st.failSetpgidErrno with
    | some e => return .error e
    | none => return .ok ()
  writeOnce fd data off len := do
    let st ← get
    if st.closedHandles.contains fd then
      set { st with callCount := st.callCount + 1 }
      return .error Errno.EBADF
    match st.failWriteErrno with
    | some e =>
      set { st with callCount := st.callCount + 1 }
      return .error e
    | none =>
      if st.writeEintrCount > 0 then
        set { st with callCount := st.callCount + 1, writeEintrCount := st.writeEintrCount - 1 }
        return .error Errno.EINTR
      else
        let takeN := Nat.min len.toNat 2
        let slice := data.extract off.toNat (off.toNat + takeN)
        set { st with
          callCount := st.callCount + 1
          syncWritten := if fd == st.allocSyncWriteFd then appendBytes st.syncWritten slice else st.syncWritten }
        return .ok (UInt64.ofNat slice.size)
  readOnce fd maxBytes := do
    let st ← get
    if st.closedHandles.contains fd then
      set { st with callCount := st.callCount + 1 }
      return .error Errno.EBADF
    match st.failReadErrno with
    | some e =>
      set { st with callCount := st.callCount + 1 }
      return .error e
    | none =>
      if st.readEintrCount > 0 then
        set { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }
        return .error Errno.EINTR
      else
        let cur := if fd == st.allocRepReadFd then st.repWire else ByteArray.empty
        let takeN := Nat.min (Nat.min cur.size maxBytes.toNat) 3
        let chunk := cur.extract 0 takeN
        let rest := cur.extract takeN cur.size
        set { st with
          callCount := st.callCount + 1
          repWire := if fd == st.allocRepReadFd then rest else st.repWire }
        return .ok chunk
  waitOnce _ := do
    let st ← get
    match st.failWaitErrno with
    | some e =>
      set { st with callCount := st.callCount + 1 }
      return .error e
    | none =>
      if st.waitEintrCount > 0 then
        set { st with callCount := st.callCount + 1, waitEintrCount := st.waitEintrCount - 1 }
        return .error Errno.EINTR
      else
        set { st with callCount := st.callCount + 1 }
        return .ok st.waitResult
  forkRun flags forkMode _ _ _ closeRefs _ _ _ argv envEntries := do
    let st ← get
    match st.failForkErrno with
    | some e =>
      set { st with callCount := st.callCount + 1 }
      return .error e
    | none =>
      set { st with
        callCount := st.callCount + 1
        hasSpawned := true
        spawnedFlags := flags
        spawnedForkMode := forkMode
        spawnedArgv := argv.map renderMockArgToken
        spawnedEnv := envEntries
        spawnedCloseRefs := closeRefs }
      return .ok 4242

end Internal

end LeanSwe.PostFork.Model

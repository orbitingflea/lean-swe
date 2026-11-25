import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Types.Internal
import LeanSwe.PostFork.Model

namespace LeanSwe.PostFork.Impl

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model

namespace Internal

/-- Binary-exponentiated retry combinator executing up to `2 ^ depth` iterations without `partial`. -/
def loopPow2 {m : Type → Type} [Monad m] {σ α : Type}
    (step : σ → m (Sum σ α)) : Nat → σ → m (Sum σ α)
  | 0, s => step s
  | d + 1, s => do
    match ← loopPow2 step d s with
    | .inr done => pure (.inr done)
    | .inl next => loopPow2 step d next

/-- Construct an `.invalidInput` `PostForkError`. -/
def mkInvalidErr (msg : String) : PostForkError :=
  { kind := .invalidInput, errno := none, childFailure := none, message := msg }

/-- Construct a `.sysError` `PostForkError` carrying `errnoVal`. -/
def mkSysErr (errnoVal : UInt32) (msg : String) : PostForkError :=
  { kind := .sysError, errno := some errnoVal, childFailure := none, message := msg }

/-- Construct a `.childFailed` `PostForkError` carrying `cf`. -/
def mkChildFailedErr (cf : ChildFailure) (msg : String) : PostForkError :=
  { kind := .childFailed, errno := some cf.errno, childFailure := some cf, message := msg }

/-- Concatenates chunks in linear `O(N)` time. -/
def concatByteChunks (chunks : Array ByteArray) : ByteArray :=
  let total := chunks.foldl (fun n c => n + c.size) 0
  chunks.foldl (fun buf c => appendBytes buf c) (ByteArray.emptyWithCapacity total)

/-- Write all bytes of `data[off..)` to `fd`, retrying `EINTR` (`4`) (`2 ^ depth` max steps). -/
def writeAllRetryEintr
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (h : fd)
    (data : ByteArray)
    (off : Nat)
    (depth : Nat) : m (Except PostForkError Unit) := do
  let res ← loopPow2
    (fun curOff =>
      if curOff ≥ data.size then
        pure (.inr (.ok ()))
      else do
        let rem := data.size - curOff
        match ← raw.writeOnce h data (UInt64.ofNat curOff) (UInt64.ofNat rem) with
        | .ok n =>
          if n == 0 then
            pure (.inr (.error (mkSysErr 5 "host write returned zero bytes")))
          else
            pure (.inl (curOff + n.toNat))
        | .error e =>
          if e == 4 then
            pure (.inl curOff)
          else
            pure (.inr (.error (mkSysErr e "host write failed"))))
    depth off
  match res with
  | .inr out => pure out
  | .inl finalOff =>
    if finalOff ≥ data.size then
      pure (.ok ())
    else
      pure (.error (mkSysErr 5 "host write exceeded retry fuel"))

/-- Read from `h` until `EOF` (`0`-byte chunk), retrying `EINTR` (`4`) (`2 ^ depth` max steps). -/
def readAllRetryEintr
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (h : fd)
    (chunkCap : UInt64)
    (acc : ByteArray)
    (depth : Nat) : m (Except PostForkError ByteArray) := do
  let initChunks : Array ByteArray := if acc.size == 0 then #[] else #[acc]
  let res ← loopPow2
    (fun curChunks => do
      match ← raw.readOnce h chunkCap with
      | .ok chunk =>
        if chunk.size == 0 then
          pure (.inr (.ok (concatByteChunks curChunks)))
        else
          pure (.inl (curChunks.push chunk))
      | .error e =>
        if e == 4 then
          pure (.inl curChunks)
        else
          pure (.inr (.error (mkSysErr e "host read failed"))))
    depth initChunks
  match res with
  | .inr out => pure out
  | .inl _ => pure (.error (mkSysErr 5 "host read exceeded retry fuel"))

/-- Reap child `pid` via `waitOnce`, retrying `EINTR` (`4`) (`2 ^ depth` max steps). -/
def waitRetryEintr
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (pid : Pid)
    (depth : Nat) : m (Except PostForkError ChildWaitStatus) := do
  let res ← loopPow2
    (fun (_ : Unit) => do
      match ← raw.waitOnce pid with
      | .ok st => pure (.inr (.ok st))
      | .error e =>
        if e == 4 then
          pure (.inl ())
        else
          pure (.inr (.error (mkSysErr e "waitpid failed"))))
    depth ()
  match res with
  | .inr out => pure out
  | .inl () => pure (.error (mkSysErr 4 "waitpid exceeded EINTR retry fuel"))

/-- Best-effort close each managed handle in `hs`. -/
def closeListQuiet
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List fd → m Unit
  | [] => pure ()
  | h :: hs => do
    let _ ← raw.closeFd h
    closeListQuiet raw hs

/-- Probe whether a single `FdRef` is open in the host process. -/
def probeRef
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : FdRef fd → m (Except PostForkError Unit)
  | .raw n => do
    match ← raw.probeFdOpen n with
    | .ok () => pure (.ok ())
    | .error e => pure (.error (mkSysErr e s!"caller fd {n} is not open"))
  | .handle h => do
    match ← raw.probeHandleOpen h with
    | .ok () => pure (.ok ())
    | .error e => pure (.error (mkSysErr e "caller handle is not open"))

/-- Probe every `FdRef` in `rs` sequentially, stopping at the first closed descriptor. -/
def probeRefList
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List (FdRef fd) → m (Except PostForkError Unit)
  | [] => pure (.ok ())
  | r :: rs => do
    match ← probeRef raw r with
    | .ok () => probeRefList raw rs
    | .error err => pure (.error err)

/-- Probe any source descriptors referenced by a `StdioPlan`. -/
def probeStdioPlan
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : StdioPlan fd → m (Except PostForkError Unit)
  | .inherit => pure (.ok ())
  | .redirect sIn sOut sErr _ => probeRefList raw [sIn, sOut, sErr]

/-- Extract the 3 source descriptor refs of a `.redirect` plan (or `#[]` for `.inherit`). -/
def stdioRefsArray {fd : Type} : StdioPlan fd → Array (FdRef fd)
  | .inherit => #[]
  | .redirect sIn sOut sErr _ => #[sIn, sOut, sErr]

/-- Encode `ForkMode` as the C shim `immortal_thread` ABI word (`0` = direct, `1` = immortal spawner pthread). -/
@[inline] def forkModeToUInt32 : ForkMode → UInt32
  | .direct => 0
  | .immortalThread => 1

/-- Append 4 little-endian bytes of `v` onto `buf` in amortized `O(1)` time. -/
@[inline] def pushI32Le (buf : ByteArray) (v : Int32) : ByteArray :=
  let u := v.toUInt32.toNat
  (((buf.push (UInt8.ofNat (u % 256)))
      |>.push (UInt8.ofNat ((u / 256) % 256)))
      |>.push (UInt8.ofNat ((u / 65536) % 256)))
      |>.push (UInt8.ofNat ((u / 16777216) % 256))

/-- Pin managed handle `h` at the end of `handles` and return its negative slot tag `-(idx + 2)`. -/
def pushHandleSlot {fd : Type} (handles : Array fd) (h : fd) : Int32 × Array fd :=
  let slot : Int32 := Int32.ofInt (- (Int.ofNat handles.size + 2))
  (slot, handles.push h)

/-- Encode an `FdRef` into a C FFI slot tag (`>= 0` for non-negative `.raw`, `-1` for negative `.raw`, `-(idx + 2)` for `.handle`). -/
def encodeFdRefSlot {fd : Type} (handles : Array fd) : FdRef fd → Int32 × Array fd
  | .raw n => (if decide (n.toInt ≥ 0) then n else -1, handles)
  | .handle h => pushHandleSlot handles h

/-- Pack an array of `FdRef` values into little-endian 32-bit slots in linear `O(N)` time. -/
def encodeRefArray {fd : Type} (handles : Array fd) (refs : Array (FdRef fd)) : ByteArray × Array fd :=
  let (hs, buf) :=
    refs.foldl
      (fun (hs, buf) r =>
        let (s, hs') := encodeFdRefSlot hs r
        (hs', pushI32Le buf s))
      (handles, ByteArray.emptyWithCapacity (refs.size * 4))
  (buf, hs)

/-- Step function encoding a single `ArgToken` into `(handles, argPrefixes, argSuffixes, argSlots)`. -/
def stepFlattenArg {fd : Type}
    (acc : Array fd × Array String × Array String × ByteArray)
    (tok : ArgToken fd) : Array fd × Array String × Array String × ByteArray :=
  let (hs, pfxs, sfxs, argSlotsBuf) := acc
  match tok with
  | .lit s =>
    (hs, pfxs.push s, sfxs.push "", pushI32Le argSlotsBuf (-1))
  | .fdDecimal r =>
    let (sl, hs') := encodeFdRefSlot hs r
    (hs', pfxs.push "", sfxs.push "", pushI32Le argSlotsBuf sl)
  | .prefixedFd p r s =>
    let (sl, hs') := encodeFdRefSlot hs r
    (hs', pfxs.push p, sfxs.push s, pushI32Le argSlotsBuf sl)

/-- Flatten `forkRun` descriptor references and `ArgToken` vector into linear `O(N)` packed slot buffers. -/
def flattenForkArgs {fd : Type}
    (syncRead? : Option fd) (errWrite : fd)
    (stdioRefs closeRefs keepRefs : Array (FdRef fd))
    (argv : Array (ArgToken fd)) : FlattenedForkArgsM fd :=
  let (syncSlot, hs0) :=
    match syncRead? with
    | some h => pushHandleSlot #[] h
    | none => (-1, #[])
  let (repSlot, hs1) := pushHandleSlot hs0 errWrite
  let (inSlot, outSlot, errSlot, hs2) :=
    if h : stdioRefs.size = 3 then
      let (s0, h0) := encodeFdRefSlot hs1 (stdioRefs[0]'(by omega))
      let (s1, h1) := encodeFdRefSlot h0 (stdioRefs[1]'(by omega))
      let (s2, h2) := encodeFdRefSlot h1 (stdioRefs[2]'(by omega))
      (s0, s1, s2, h2)
    else
      (-1, -1, -1, hs1)
  let metaSlots :=
    pushI32Le (pushI32Le (pushI32Le (pushI32Le (pushI32Le (ByteArray.emptyWithCapacity 20) syncSlot) repSlot) inSlot) outSlot) errSlot
  let (closeSlots, hs3) := encodeRefArray hs2 closeRefs
  let (keepSlots, hs4) := encodeRefArray hs3 keepRefs
  let (hs5, pfxs, sfxs, argSlotsBuf) :=
    argv.foldl stepFlattenArg
      (hs4, Array.mkEmpty argv.size, Array.mkEmpty argv.size, ByteArray.emptyWithCapacity (argv.size * 4))
  { handles := hs5
    metaSlots := metaSlots
    closeSlots := closeSlots
    keepSlots := keepSlots
    argPrefixes := pfxs
    argSuffixes := sfxs
    argSlots := argSlotsBuf }

/-- Filter `spec.closeFds` before allocating internal pipes: retain `.handle` entries and currently-open `.raw` descriptors while dropping already-closed `.raw` descriptors so `pipe2` reuse cannot collide with `close_fds`. -/
def filterOpenCloseList
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List (FdRef fd) → Array (FdRef fd) → m (Array (FdRef fd))
  | [], acc => pure acc
  | .handle h :: rest, acc => filterOpenCloseList raw rest (acc.push (.handle h))
  | .raw n :: rest, acc => do
    match ← raw.probeFdOpen n with
    | .ok () => filterOpenCloseList raw rest (acc.push (.raw n))
    | .error _ => filterOpenCloseList raw rest acc

/-- Return `true` iff `e` is a post-syscall `close()` error after which Linux `filp_close` and `leanswe_fd_box_close` have already detached the descriptor (`EINTR`, `EIO`, `ENOMEM`, `ENOSPC`, `ECONNRESET`, `ESTALE`, `EDQUOT`). -/
def isKernelCloseDetachNonBadf (e : Errno) : Bool :=
  match e.toNat with
  | 4 | 5 | 12 | 28 | 104 | 116 | 122 => true
  | _ => false

/-- Return `true` iff `writeOnce` failed prior to touching the OS pipe because `syncWrite` was closed, busy, or pin-saturated (`EBADF = 9`, `EBUSY = 16`, `EOVERFLOW = 75`). -/
def isFastFailSyncWriteErr : Option Errno → Bool
  | some e =>
    match e.toNat with
    | 9 | 16 | 75 => true
    | _ => false
  | none => false

/-- Drain the failure pipe `errRead`, close it, decode any `ChildFailure` (treating `0`-byte `EOF` as `.wireTruncated` `EIO` when `barrierBroken = true`), and reap on child failure. -/
def awaitExecOrFailure
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (pid : Pid)
    (pgid? : Option Pid)
    (errRead : fd)
    (fuel : Nat)
    (barrierBroken : Bool := false) : m (Except PostForkError SpawnedChild) := do
  let repRes ← readAllRetryEintr raw errRead 16 ByteArray.empty fuel
  let _ ← raw.closeFd errRead
  match repRes with
  | .error err =>
    pure (.error err)
  | .ok repBytes =>
    let cf? : Option ChildFailure :=
      match decodeChildFailure repBytes with
      | some cf => some cf
      | none =>
        if barrierBroken then
          some { stage := .wireTruncated, errno := Errno.EIO }
        else
          none
    match cf? with
    | none => pure (.ok { pid := pid, pgid := pgid? })
    | some cf =>
      match ← waitRetryEintr raw pid fuel with
      | .error err => pure (.error err)
      | .ok wst =>
        let fullCf := { cf with waitStatus := some wst }
        pure (.error (mkChildFailedErr fullCf "child setup or execve failed"))

/-- Invoke `raw.forkRun` and best-effort parent `setpgid` for `.newGroup`. -/
def performFork
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (spec : ChildSpecM fd)
    (syncRead? : Option fd)
    (errWrite : fd)
    (openCloseFds : Array (FdRef fd))
    (extraClose : Array (FdRef fd))
    (withBarrier : Bool) : m (Except PostForkError Pid) := do
  let flags := flagsOfSpec spec withBarrier
  let stdioArr := stdioRefsArray spec.stdio
  let closeArr := openCloseFds ++ extraClose
  let keepArr := FdPolicy.keepFds spec.fdPolicy
  let envEntries := formatEnvEntriesBytes spec.rawEnv spec.env
  match ← raw.forkRun
      flags spec.forkMode syncRead? errWrite stdioArr closeArr keepArr
      spec.cwd spec.path spec.argv envEntries with
  | .error e => pure (.error (mkSysErr e "fork failed"))
  | .ok pid =>
    match spec.processGroup with
    | .newGroup =>
      let _ ← raw.setpgidOnce pid pid
      pure (.ok pid)
    | .inherit => pure (.ok pid)

/-- Build a caller-agnostic `PostForkOpsM` orchestrator from low-level `PosixHostOpsM` host primitives. -/
def mkHostOps
    {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd)
    (fuel : Nat := 18) : PostForkOpsM m fd where
  spawn spec := do
    if !validateSpec spec then
      return .error (mkInvalidErr "invalid ChildSpecM")
    if let .error err ← probeStdioPlan raw spec.stdio then
      return .error err
    if let .error err ← probeRefList raw (FdPolicy.keepFds spec.fdPolicy).toList then
      return .error err
    let openCloseFds ← filterOpenCloseList raw spec.closeFds.toList #[]
    let (errR, errW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e => return .error (mkSysErr e "pipe2 error-pipe failed")
    let forkRes ← performFork raw spec none errW openCloseFds #[FdRef.handle errR] false
    let _ ← raw.closeFd errW
    match forkRes with
    | .error err =>
      let _ ← raw.closeFd errR
      return .error err
    | .ok pid =>
      let pgid? := match spec.processGroup with | .newGroup => some pid | .inherit => none
      awaitExecOrFailure raw pid pgid? errR fuel

  spawnWithBarrier spec := do
    if !validateSpec spec then
      return .error (mkInvalidErr "invalid ChildSpecM")
    if let .error err ← probeStdioPlan raw spec.stdio then
      return .error err
    if let .error err ← probeRefList raw (FdPolicy.keepFds spec.fdPolicy).toList then
      return .error err
    let openCloseFds ← filterOpenCloseList raw spec.closeFds.toList #[]
    let (errR, errW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e => return .error (mkSysErr e "pipe2 error-pipe failed")
    let (syncR, syncW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e =>
        closeListQuiet raw [errW, errR]
        return .error (mkSysErr e "pipe2 sync-barrier failed")
    let forkRes ← performFork raw spec (some syncR) errW openCloseFds #[FdRef.handle errR, FdRef.handle syncW] true
    closeListQuiet raw [errW, syncR]
    match forkRes with
    | .error err =>
      closeListQuiet raw [syncW, errR]
      return .error err
    | .ok pid =>
      let pgid? := match spec.processGroup with | .newGroup => some pid | .inherit => none
      return .ok { pid := pid, pgid := pgid?, syncWrite := syncW, errRead := errR }

  releaseBarrier pending := do
    if let .error e ← raw.probeHandleOpen pending.errRead then
      return .error (mkSysErr e "failure report handle is not open")
    match ← writeAllRetryEintr raw pending.syncWrite (ByteArray.mk #[1]) 0 fuel with
    | .ok () =>
      let _ ← raw.closeFd pending.syncWrite
      awaitExecOrFailure raw pending.pid pending.pgid pending.errRead fuel
    | .error err =>
      if err.errno == some Errno.EPIPE then
        let _ ← raw.closeFd pending.syncWrite
        awaitExecOrFailure raw pending.pid pending.pgid pending.errRead fuel true
      else if isFastFailSyncWriteErr err.errno then
        return .error err
      else
        match ← raw.closeFd pending.syncWrite with
        | .error e =>
          if !isKernelCloseDetachNonBadf e then
            return .error err
          else
            pure ()
        | .ok () => pure ()
        let _ ← raw.closeFd pending.errRead
        let _ ← waitRetryEintr raw pending.pid fuel
        return .error err

  abortBarrier pending := do
    match ← raw.closeFd pending.syncWrite with
    | .error e =>
      if !isKernelCloseDetachNonBadf e then
        return .error (mkSysErr e "sync barrier handle already closed or busy")
      else
        pure ()
    | .ok () => pure ()
    let repRes ← readAllRetryEintr raw pending.errRead 16 ByteArray.empty fuel
    let _ ← raw.closeFd pending.errRead
    match repRes with
    | .error err =>
      let _ ← waitRetryEintr raw pending.pid fuel
      return .error err
    | .ok repBytes =>
      let wst ← match ← waitRetryEintr raw pending.pid fuel with
        | .ok s => pure s
        | .error err => return .error err
      match decodeChildFailure repBytes with
      | none => return .ok (.aborted wst)
      | some cf => return .ok (.failedBeforeBarrier { cf with waitStatus := some wst } wst)

/-- Monadic `Nat`-specialized `PostForkOpsM` builder for `Core.ObeysStepFrom`. -/
def mkHostOpsM {m : Type → Type} [Monad m]
    (raw : PosixHostOpsM m Nat) : PostForkOpsM m Nat :=
  mkHostOps raw

end Internal

end LeanSwe.PostFork.Impl

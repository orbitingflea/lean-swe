import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Types.Internal
import LeanSweProofs.PostFork.Model

/-!
Pure spec-passing reference host orchestrator and argument flattener over `PostFork.Types`
and `PostFork.Model` for single-bug `PostFork` specification mutants.
-/

namespace LeanSwe.PostFork

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Impl.Internal (PosixHostOpsM FlattenedForkArgsM)

private def loopPow2Ref {m : Type → Type} [Monad m] {σ α : Type}
    (step : σ → m (Sum σ α)) : Nat → σ → m (Sum σ α)
  | 0, s => step s
  | d + 1, s => do
    match ← loopPow2Ref step d s with
    | .inr done => pure (.inr done)
    | .inl next => loopPow2Ref step d next

/-- Construct an `.invalidInput` `PostForkError`. -/
def refMkInvalidErr (msg : String) : PostForkError :=
  { kind := .invalidInput, errno := none, childFailure := none, message := msg }

/-- Construct a `.sysError` `PostForkError` carrying `errnoVal`. -/
def refMkSysErr (errnoVal : UInt32) (msg : String) : PostForkError :=
  { kind := .sysError, errno := some errnoVal, childFailure := none, message := msg }

private def mkChildFailedErrRef (cf : ChildFailure) (msg : String) : PostForkError :=
  { kind := .childFailed, errno := some cf.errno, childFailure := some cf, message := msg }

private def concatByteChunksRef (chunks : Array ByteArray) : ByteArray :=
  let total := chunks.foldl (fun n c => n + c.size) 0
  chunks.foldl (fun buf c => appendBytes buf c) (ByteArray.emptyWithCapacity total)

private def writeAllRetryEintrRef {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (h : fd) (data : ByteArray) (off depth : Nat) :
    m (Except PostForkError Unit) := do
  let res ← loopPow2Ref
    (fun curOff =>
      if curOff ≥ data.size then pure (.inr (.ok ()))
      else do
        let rem := data.size - curOff
        match ← raw.writeOnce h data (UInt64.ofNat curOff) (UInt64.ofNat rem) with
        | .ok n =>
          if n == 0 then pure (.inr (.error (refMkSysErr 5 "host write returned zero bytes")))
          else pure (.inl (curOff + n.toNat))
        | .error e =>
          if e == 4 then pure (.inl curOff)
          else pure (.inr (.error (refMkSysErr e "host write failed"))))
    depth off
  match res with
  | .inr out => pure out
  | .inl finalOff =>
    if finalOff ≥ data.size then pure (.ok ())
    else pure (.error (refMkSysErr 5 "host write exceeded retry fuel"))

private def readAllRetryEintrRef {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (h : fd) (chunkCap : UInt64) (acc : ByteArray) (depth : Nat) :
    m (Except PostForkError ByteArray) := do
  let initChunks : Array ByteArray := if acc.size == 0 then #[] else #[acc]
  let res ← loopPow2Ref
    (fun curChunks => do
      match ← raw.readOnce h chunkCap with
      | .ok chunk =>
        if chunk.size == 0 then pure (.inr (.ok (concatByteChunksRef curChunks)))
        else pure (.inl (curChunks.push chunk))
      | .error e =>
        if e == 4 then pure (.inl curChunks)
        else pure (.inr (.error (refMkSysErr e "host read failed"))))
    depth initChunks
  match res with
  | .inr out => pure out
  | .inl _ => pure (.error (refMkSysErr 5 "host read exceeded retry fuel"))

private def waitRetryEintrRef {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (pid : Pid) (depth : Nat) :
    m (Except PostForkError ChildWaitStatus) := do
  let res ← loopPow2Ref
    (fun (_ : Unit) => do
      match ← raw.waitOnce pid with
      | .ok st => pure (.inr (.ok st))
      | .error e =>
        if e == 4 then pure (.inl ())
        else pure (.inr (.error (refMkSysErr e "waitpid failed"))))
    depth ()
  match res with
  | .inr out => pure out
  | .inl () => pure (.error (refMkSysErr 4 "waitpid exceeded EINTR retry fuel"))

/-- Best-effort close each managed handle in `hs`. -/
def refCloseListQuiet {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List fd → m Unit
  | [] => pure ()
  | h :: hs => do
    let _ ← raw.closeFd h
    refCloseListQuiet raw hs

/-- Probe whether a single `FdRef` is open in the host process. -/
def refProbeSingle {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : FdRef fd → m (Except PostForkError Unit)
  | .raw n => do
    match ← raw.probeFdOpen n with
    | .ok () => pure (.ok ())
    | .error e => pure (.error (refMkSysErr e s!"caller fd {n} is not open"))
  | .handle h => do
    match ← raw.probeHandleOpen h with
    | .ok () => pure (.ok ())
    | .error e => pure (.error (refMkSysErr e "caller handle is not open"))

/-- Probe every `FdRef` in `rs` sequentially. -/
def refProbeList {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List (FdRef fd) → m (Except PostForkError Unit)
  | [] => pure (.ok ())
  | r :: rs => do
    match ← refProbeSingle raw r with
    | .ok () => refProbeList raw rs
    | .error err => pure (.error err)

/-- Probe any source descriptors referenced by a `StdioPlan`. -/
def refProbeStdioPlan {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : StdioPlan fd → m (Except PostForkError Unit)
  | .inherit => pure (.ok ())
  | .redirect sIn sOut sErr _ => refProbeList raw [sIn, sOut, sErr]

/-- Extract the 3 source descriptor refs of a `.redirect` plan (or `#[]` for `.inherit`). -/
def refStdioRefsArray {fd : Type} : StdioPlan fd → Array (FdRef fd)
  | .inherit => #[]
  | .redirect sIn sOut sErr _ => #[sIn, sOut, sErr]

/-- Reference `ForkMode` wire encoder (`0` = direct, `1` = immortalThread). -/
def refForkModeToUInt32 : ForkMode → UInt32
  | .direct => 0
  | .immortalThread => 1

private def pushI32LeRef (buf : ByteArray) (v : Int32) : ByteArray :=
  let u := v.toUInt32.toNat
  (((buf.push (UInt8.ofNat (u % 256)))
      |>.push (UInt8.ofNat ((u / 256) % 256)))
      |>.push (UInt8.ofNat ((u / 65536) % 256)))
      |>.push (UInt8.ofNat ((u / 16777216) % 256))

private def pushHandleSlotRef {fd : Type} (handles : Array fd) (h : fd) : Int32 × Array fd :=
  let slot : Int32 := Int32.ofInt (- (Int.ofNat handles.size + 2))
  (slot, handles.push h)

private def encodeFdRefSlotRef {fd : Type} (handles : Array fd) : FdRef fd → Int32 × Array fd
  | .raw n => (if decide (n.toInt ≥ 0) then n else -1, handles)
  | .handle h => pushHandleSlotRef handles h

private def encodeRefArrayRef {fd : Type} (handles : Array fd) (refs : Array (FdRef fd)) :
    ByteArray × Array fd :=
  let (hs, buf) :=
    refs.foldl
      (fun (hs, buf) r =>
        let (s, hs') := encodeFdRefSlotRef hs r
        (hs', pushI32LeRef buf s))
      (handles, ByteArray.emptyWithCapacity (refs.size * 4))
  (buf, hs)

private def stepFlattenArgRef {fd : Type}
    (acc : Array fd × Array String × Array String × ByteArray)
    (tok : ArgToken fd) : Array fd × Array String × Array String × ByteArray :=
  let (hs, pfxs, sfxs, argSlotsBuf) := acc
  match tok with
  | .lit s => (hs, pfxs.push s, sfxs.push "", pushI32LeRef argSlotsBuf (-1))
  | .fdDecimal r =>
    let (sl, hs') := encodeFdRefSlotRef hs r
    (hs', pfxs.push "", sfxs.push "", pushI32LeRef argSlotsBuf sl)
  | .prefixedFd p r s =>
    let (sl, hs') := encodeFdRefSlotRef hs r
    (hs', pfxs.push p, sfxs.push s, pushI32LeRef argSlotsBuf sl)

/-- Pure reference `flattenForkArgs` over `PostFork.Types` and `PostFork.Types.Internal`. -/
def refFlattenForkArgs {fd : Type}
    (syncRead? : Option fd) (errWrite : fd)
    (stdioRefs closeRefs keepRefs : Array (FdRef fd))
    (argv : Array (ArgToken fd)) : FlattenedForkArgsM fd :=
  let (syncSlot, hs0) :=
    match syncRead? with
    | some h => pushHandleSlotRef #[] h
    | none => (-1, #[])
  let (repSlot, hs1) := pushHandleSlotRef hs0 errWrite
  let (inSlot, outSlot, errSlot, hs2) :=
    if h : stdioRefs.size = 3 then
      let (s0, h0) := encodeFdRefSlotRef hs1 (stdioRefs[0]'(by omega))
      let (s1, h1) := encodeFdRefSlotRef h0 (stdioRefs[1]'(by omega))
      let (s2, h2) := encodeFdRefSlotRef h1 (stdioRefs[2]'(by omega))
      (s0, s1, s2, h2)
    else
      (-1, -1, -1, hs1)
  let metaSlots :=
    pushI32LeRef (pushI32LeRef (pushI32LeRef (pushI32LeRef (pushI32LeRef
      (ByteArray.emptyWithCapacity 20) syncSlot) repSlot) inSlot) outSlot) errSlot
  let (closeSlots, hs3) := encodeRefArrayRef hs2 closeRefs
  let (keepSlots, hs4) := encodeRefArrayRef hs3 keepRefs
  let (hs5, pfxs, sfxs, argSlotsBuf) :=
    argv.foldl stepFlattenArgRef
      (hs4, Array.mkEmpty argv.size, Array.mkEmpty argv.size, ByteArray.emptyWithCapacity (argv.size * 4))
  { handles := hs5
    metaSlots := metaSlots
    closeSlots := closeSlots
    keepSlots := keepSlots
    argPrefixes := pfxs
    argSuffixes := sfxs
    argSlots := argSlotsBuf }

/-- Filter `spec.closeFds` before allocating internal pipes. -/
def refFilterOpenCloseList {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) : List (FdRef fd) → Array (FdRef fd) → m (Array (FdRef fd))
  | [], acc => pure acc
  | .handle h :: rest, acc => refFilterOpenCloseList raw rest (acc.push (.handle h))
  | .raw n :: rest, acc => do
    match ← raw.probeFdOpen n with
    | .ok () => refFilterOpenCloseList raw rest (acc.push (.raw n))
    | .error _ => refFilterOpenCloseList raw rest acc

private def isKernelCloseDetachNonBadfRef (e : Errno) : Bool :=
  match e.toNat with
  | 4 | 5 | 12 | 28 | 104 | 116 | 122 => true
  | _ => false

private def isFastFailSyncWriteErrRef : Option Errno → Bool
  | some e =>
    match e.toNat with
    | 9 | 16 | 75 => true
    | _ => false
  | none => false

private def awaitExecOrFailureRef {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (pid : Pid) (pgid? : Option Pid) (errRead : fd)
    (fuel : Nat) (barrierBroken : Bool := false) : m (Except PostForkError SpawnedChild) := do
  let repRes ← readAllRetryEintrRef raw errRead 16 ByteArray.empty fuel
  let _ ← raw.closeFd errRead
  match repRes with
  | .error err => pure (.error err)
  | .ok repBytes =>
    let cf? : Option ChildFailure :=
      match decodeChildFailure repBytes with
      | some cf => some cf
      | none => if barrierBroken then some { stage := .wireTruncated, errno := Errno.EIO } else none
    match cf? with
    | none => pure (.ok { pid := pid, pgid := pgid? })
    | some cf =>
      match ← waitRetryEintrRef raw pid fuel with
      | .error err => pure (.error err)
      | .ok wst =>
        pure (.error (mkChildFailedErrRef { cf with waitStatus := some wst } "child setup or execve failed"))

/-- Invoke `raw.forkRun` and best-effort parent `setpgid` for `.newGroup`. -/
def refPerformFork {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (spec : ChildSpecM fd) (syncRead? : Option fd) (errWrite : fd)
    (openCloseFds extraClose : Array (FdRef fd)) (withBarrier : Bool) :
    m (Except PostForkError Pid) := do
  let flags := flagsOfSpec spec withBarrier
  let stdioArr := refStdioRefsArray spec.stdio
  let closeArr := openCloseFds ++ extraClose
  let keepArr := FdPolicy.keepFds spec.fdPolicy
  let envEntries := formatEnvEntriesBytes spec.rawEnv spec.env
  match ← raw.forkRun flags spec.forkMode syncRead? errWrite stdioArr closeArr keepArr
      spec.cwd spec.path spec.argv envEntries with
  | .error e => pure (.error (refMkSysErr e "fork failed"))
  | .ok pid =>
    match spec.processGroup with
    | .newGroup =>
      let _ ← raw.setpgidOnce pid pid
      pure (.ok pid)
    | .inherit => pure (.ok pid)

/-- Pure spec-passing reference `PostForkOpsM` builder over `PosixHostOpsM`. -/
def refMkHostOps {m : Type → Type} [Monad m] {fd : Type}
    (raw : PosixHostOpsM m fd) (fuel : Nat := 18) : PostForkOpsM m fd where
  spawn spec := do
    if !validateSpec spec then return .error (refMkInvalidErr "invalid ChildSpecM")
    if let .error err ← refProbeStdioPlan raw spec.stdio then return .error err
    if let .error err ← refProbeList raw (FdPolicy.keepFds spec.fdPolicy).toList then return .error err
    let openCloseFds ← refFilterOpenCloseList raw spec.closeFds.toList #[]
    let (errR, errW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e => return .error (refMkSysErr e "pipe2 error-pipe failed")
    let forkRes ← refPerformFork raw spec none errW openCloseFds #[FdRef.handle errR] false
    let _ ← raw.closeFd errW
    match forkRes with
    | .error err =>
      let _ ← raw.closeFd errR
      return .error err
    | .ok pid =>
      let pgid? := match spec.processGroup with | .newGroup => some pid | .inherit => none
      awaitExecOrFailureRef raw pid pgid? errR fuel

  spawnWithBarrier spec := do
    if !validateSpec spec then return .error (refMkInvalidErr "invalid ChildSpecM")
    if let .error err ← refProbeStdioPlan raw spec.stdio then return .error err
    if let .error err ← refProbeList raw (FdPolicy.keepFds spec.fdPolicy).toList then return .error err
    let openCloseFds ← refFilterOpenCloseList raw spec.closeFds.toList #[]
    let (errR, errW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e => return .error (refMkSysErr e "pipe2 error-pipe failed")
    let (syncR, syncW) ← match ← raw.mkPipeCloexec with
      | .ok p => pure p
      | .error e =>
        refCloseListQuiet raw [errW, errR]
        return .error (refMkSysErr e "pipe2 sync-barrier failed")
    let forkRes ← refPerformFork raw spec (some syncR) errW openCloseFds #[FdRef.handle errR, FdRef.handle syncW] true
    refCloseListQuiet raw [errW, syncR]
    match forkRes with
    | .error err =>
      refCloseListQuiet raw [syncW, errR]
      return .error err
    | .ok pid =>
      let pgid? := match spec.processGroup with | .newGroup => some pid | .inherit => none
      return .ok { pid := pid, pgid := pgid?, syncWrite := syncW, errRead := errR }

  releaseBarrier pending := do
    if let .error e ← raw.probeHandleOpen pending.errRead then
      return .error (refMkSysErr e "failure report handle is not open")
    match ← writeAllRetryEintrRef raw pending.syncWrite (ByteArray.mk #[1]) 0 fuel with
    | .ok () =>
      let _ ← raw.closeFd pending.syncWrite
      awaitExecOrFailureRef raw pending.pid pending.pgid pending.errRead fuel
    | .error err =>
      if err.errno == some Errno.EPIPE then
        let _ ← raw.closeFd pending.syncWrite
        awaitExecOrFailureRef raw pending.pid pending.pgid pending.errRead fuel true
      else if isFastFailSyncWriteErrRef err.errno then
        return .error err
      else
        match ← raw.closeFd pending.syncWrite with
        | .error e =>
          if !isKernelCloseDetachNonBadfRef e then return .error err else pure ()
        | .ok () => pure ()
        let _ ← raw.closeFd pending.errRead
        let _ ← waitRetryEintrRef raw pending.pid fuel
        return .error err

  abortBarrier pending := do
    match ← raw.closeFd pending.syncWrite with
    | .error e =>
      if !isKernelCloseDetachNonBadfRef e then
        return .error (refMkSysErr e "sync barrier handle already closed or busy")
      else pure ()
    | .ok () => pure ()
    let repRes ← readAllRetryEintrRef raw pending.errRead 16 ByteArray.empty fuel
    let _ ← raw.closeFd pending.errRead
    match repRes with
    | .error err =>
      let _ ← waitRetryEintrRef raw pending.pid fuel
      return .error err
    | .ok repBytes =>
      let wst ← match ← waitRetryEintrRef raw pending.pid fuel with
        | .ok s => pure s
        | .error err => return .error err
      match decodeChildFailure repBytes with
      | none => return .ok (.aborted wst)
      | some cf => return .ok (.failedBeforeBarrier { cf with waitStatus := some wst } wst)

end LeanSwe.PostFork

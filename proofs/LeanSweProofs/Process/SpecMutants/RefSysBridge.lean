import Core.ConcOps
import LeanSwe.LinuxSyscall.Process.Types
import LeanSweProofs.Process.SpecMutants.RefSysBridgeIo

/-!
Pure spec-passing reference `ProcTableOpsM`, `mkRawOpsM`, and `mkApiM` builders over `.Types`
and `.Model` for single-bug `LeanSwe.Process` specification mutants.
-/

namespace LeanSwe.Process.SpecMutants

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.Internal
  (SysDepsM ProcSlotM ProcTableState ProcTableOpsM StreamLoopState)

private def findSlotPureRef {fd : Type} (hid : Nat) : List (Nat × ProcSlotM fd) → Option (ProcSlotM fd)
  | [] => none
  | (k, v) :: rest => if k == hid then some v else findSlotPureRef hid rest

private def removeSlotListRef {fd : Type} (hid : Nat) :
    List (Nat × ProcSlotM fd) → Option (ProcSlotM fd) × List (Nat × ProcSlotM fd)
  | [] => (none, [])
  | (k, v) :: rest =>
    if k == hid then (some v, rest)
    else
      let (found?, rest') := removeSlotListRef hid rest
      (found?, (k, v) :: rest')

/-- Pure `StateM S` instantiation of `ProcTableOpsM` via lens `(getTbl, setTbl)`. -/
def refStateProcTableOps {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S) : ProcTableOpsM (StateM S) fd where
  insertSlot slot := modifyGet fun s =>
    let st := getTbl s
    let hid := st.nextId
    (hid, setTbl s { nextId := hid + 1, slots := (hid, slot) :: st.slots })
  takeSlotIo hid := modifyGet fun s =>
    let st := getTbl s
    match findSlotPureRef hid st.slots with
    | none => (none, s)
    | some slot =>
      let slots' := st.slots.map fun (k, sl) =>
        if k == hid then (k, { sl with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
        else (k, sl)
      (some (slot.pid, slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?), setTbl s { st with slots := slots' })
  markWaited hid waited := modifyGet fun s =>
    let st := getTbl s
    match findSlotPureRef hid st.slots with
    | none => (false, s)
    | some _ =>
      let slots' := st.slots.map fun (k, sl) =>
        if k == hid then (k, { sl with waited := sl.waited || waited }) else (k, sl)
      (true, setTbl s { st with slots := slots' })
  lookupPgid hid := do
    let s ← get
    return (findSlotPureRef hid (getTbl s).slots).map (·.pgid)
  detachSlot hid := modifyGet fun s =>
    let st := getTbl s
    let (found?, slots') := removeSlotListRef hid st.slots
    (found?, setTbl s { st with slots := slots' })
  activeCount := do
    let s ← get
    return (getTbl s).slots.length

private def isInvalidSpawnRequestRef (req : ExecRequest) : Bool :=
  req.program.isEmpty ||
  Model.hasNulModel req.program ||
  PostFork.Model.hasEmbeddedNulStr req.program ||
  req.args.toList.any (fun a => Model.hasNulModel a || PostFork.Model.hasEmbeddedNulStr a) ||
  (match req.cwd with
   | some d => Model.hasNulModel d || PostFork.Model.hasEmbeddedNulStr d
   | none => false) ||
  req.env.toList.any (fun kv =>
    Model.isInvalidEnvEntryModel kv ||
    PostFork.Model.hasEmbeddedNulStr kv.1 ||
    match kv.2 with | some v => PostFork.Model.hasEmbeddedNulStr v | none => false)

private def mapPostForkErrorRef (req : ExecRequest) (pfErr : PostFork.PostForkError) : ProcessError :=
  match pfErr.childFailure with
  | some cf =>
    let target := if cf.stage == .chdir && req.cwd.isSome then req.cwd.getD req.program else req.program
    refMapErrno (some target) "spawn" cf.errno
  | none =>
    match pfErr.kind with
    | .invalidInput =>
      Model.mapRawErrorModel (.invalidArgument (some req.program) (pfErr.errno.getD Errno.EINVAL) pfErr.message)
    | _ =>
      match pfErr.errno with
      | some e => refMapErrno (some req.program) "spawn" e
      | none =>
        let mapped := Model.mapRawErrorModel (.userError pfErr.message)
        { mapped with program := some req.program }

private def spawnOsPhaseRef {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (eintrFuel : Nat) (req : ExecRequest) :
    m (Except ProcessError (ProcSlotM fd)) := do
  if isInvalidSpawnRequestRef req then
    return .error (Model.mapRawErrorModel (.invalidArgument (some req.program) Errno.EINVAL "invalid process spawn argument"))
  match ← refValidateWorkingDir deps.files req.cwd eintrFuel with
  | .error cwdErr => return .error cwdErr
  | .ok _ =>
    match ← (if req.inheritEnv then deps.listAmbientEnv else pure (.ok #[])) with
    | .error envErr => return .error (refEnsureNonEmptyMsg "failed to read environment" envErr)
    | .ok baseEnv =>
      let envBytes := refMergeRawEnvOverrides baseEnv req.env
      match ← refResolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel with
      | .error resErr => return .error resErr
      | .ok resolvedPath =>
        if resolvedPath.isEmpty || PostFork.Model.hasEmbeddedNulStr resolvedPath then
          return .error (Model.mapRawErrorModel (.invalidArgument (some req.program) Errno.EINVAL "invalid resolved executable path"))
        match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
        | .error e1 => return .error (refMapErrno (some req.program) "pipe2" e1)
        | .ok (inR, inW) =>
          match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
          | .error e2 =>
            refCloseOpt deps.files (some inR)
            refCloseOpt deps.files (some inW)
            return .error (refMapErrno (some req.program) "pipe2" e2)
          | .ok (outR, outW) =>
            match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
            | .error e3 =>
              refCloseOpt deps.files (some inR)
              refCloseOpt deps.files (some inW)
              refCloseOpt deps.files (some outR)
              refCloseOpt deps.files (some outW)
              return .error (refMapErrno (some req.program) "pipe2" e3)
            | .ok (errR, errW) =>
              let childSpec : PostFork.ChildSpecM fd :=
                { path := resolvedPath
                  argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                  cwd := req.cwd
                  env := #[]
                  rawEnv := envBytes
                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                  fdPolicy := .inheritNonCloexec #[]
                  closeFds := #[.handle inW, .handle outR, .handle errR]
                  processGroup := .newGroup
                  sigpipe := .resetDefault
                  forkMode := .direct }
              let spawnRes ← deps.postFork.spawn childSpec
              refCloseOpt deps.files (some inR)
              refCloseOpt deps.files (some outW)
              refCloseOpt deps.files (some errW)
              match spawnRes with
              | .error pfErr =>
                refCloseOpt deps.files (some inW)
                refCloseOpt deps.files (some outR)
                refCloseOpt deps.files (some errR)
                return .error (mapPostForkErrorRef req pfErr)
              | .ok child =>
                let rawPgid := child.pgid.getD child.pid
                if child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID ||
                   rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID then
                  refCloseOpt deps.files (some inW)
                  refCloseOpt deps.files (some outR)
                  refCloseOpt deps.files (some errR)
                  return .error (Model.mapRawErrorModel (.userError "spawned child returned out-of-range PID"))
                return .ok
                  { pid := child.pid, pgid := rawPgid,
                    stdinFd? := some inW, stdoutFd? := some outR, stderrFd? := some errR,
                    waited := false }

/-- Pure capability-parameterized reference `spawnPure`. -/
def refSpawnPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat) (req : ExecRequest) : m (Except ProcessError ProcessHandle) := do
  match ← spawnOsPhaseRef deps eintrFuel req with
  | .error err => return .error err
  | .ok slot =>
    let hid ← tbl.insertSlot slot
    return .ok { handleId := hid, pid := Int.ofNat slot.pid.toNat, pgid := Int.ofNat slot.pgid.toNat }

private def decodeWaitOutcomeRef (wr : LinuxSyscall.Process.WaitResult) (stdout stderr : ByteArray) : ExecOutcome :=
  match wr with
  | .exited _ code => .exited { exitCode := Int.ofNat code.toNat, stdout := stdout, stderr := stderr }
  | .signaled _ sig _ => .signaled (Int.ofNat sig.toNat) stdout stderr
  | _ => .exited { exitCode := 1, stdout := stdout, stderr := stderr }

private def waitBlockingLoopRef {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32)
    (stdout stderr : ByteArray) : Nat → m (Except ProcessError ExecOutcome)
  | 0 => pure (.error (Model.mapRawErrorModel (.userError "waitpid EINTR retry budget exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok wr => return .ok (decodeWaitOutcomeRef wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then waitBlockingLoopRef proc pid stdout stderr fuel
      else if e == Errno.ECHILD then return .ok (.exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else return .error (refMapErrno none "waitpid" e)

private def waitTimedLoopRef {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) :
    Nat → m (Except ProcessError (Bool × ExecOutcome))
  | 0 => pure (.error (Model.mapRawErrorModel (.userError "waitpid timeout loop fuel exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid { nohang := true } with
    | .ok .stillRunning =>
      match ← refCheckTimedOut timeRand startMs (some timeoutMs) with
      | .error e => return .error (refMapErrno none "clock_gettime" e)
      | .ok (true, _) => return .ok (false, .timedOut stdout stderr)
      | .ok (false, remMs) =>
        refSleepMonoMs timeRand (Nat.min remMs 5)
        waitTimedLoopRef proc timeRand pid startMs timeoutMs stdout stderr fuel
    | .ok wr => return .ok (true, decodeWaitOutcomeRef wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then waitTimedLoopRef proc timeRand pid startMs timeoutMs stdout stderr fuel
      else if e == Errno.ECHILD then return .ok (true, .exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else return .error (refMapErrno none "waitpid" e)

private def awaitOutputPureRef {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel ioFuel : Nat) (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs? maxOutputBytes? : Option Nat) : m (Except ProcessError ExecOutcome) := do
  match ← tbl.takeSlotIo h.handleId with
  | none => return .error (Model.mapRawErrorModel (.userError "invalid process handle"))
  | some (pid, inFd0?, outFd0?, errFd0?) =>
    let inFd? ←
      if stdin.size == 0 then do refCloseOpt deps.files inFd0?; pure none
      else match inFd0? with
        | none => pure none
        | some inFd => do let _ ← deps.files.fcntl inFd (.setFl true false); pure (some inFd)
    refSetNonblockingOpt deps.files outFd0?
    refSetNonblockingOpt deps.files errFd0?
    let startRes : Except ProcessError Nat ← match timeoutMs? with
      | none => pure (.ok 0)
      | some _ => do
        match ← refMonoNowMs deps.timeRand with
        | .ok ms => pure (.ok ms)
        | .error e => pure (.error (refMapErrno none "clock_gettime" e))
    match startRes with
    | .error e =>
      refCloseOpt deps.files inFd?
      refCloseOpt deps.files outFd0?
      refCloseOpt deps.files errFd0?
      return .error e
    | .ok startMs =>
      let initSt : StreamLoopState fd := { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
      let phaseRes : Except ProcessError (Bool × ExecOutcome) ←
        match ← refStreamPipesLoop deps.files deps.poll deps.timeRand stdin startMs timeoutMs? maxOutputBytes? eintrFuel initSt ioFuel with
        | .error e => pure (.error e)
        | .ok (.timedOut out err) => pure (.ok (false, .timedOut out err))
        | .ok (.limitExceeded out err) => pure (.ok (false, .outputLimitExceeded out err))
        | .ok (.eof out err) =>
          let pidI32 := pid.toInt32
          match timeoutMs? with
          | none =>
            match ← waitBlockingLoopRef deps.proc pidI32 out err eintrFuel with
            | .error e => pure (.error e)
            | .ok outcome => pure (.ok (true, outcome))
          | some timeoutMs =>
            waitTimedLoopRef deps.proc deps.timeRand pidI32 startMs timeoutMs out err ioFuel
      match phaseRes with
      | .error err => return .error err
      | .ok (waited, outcome) =>
        let ok ← tbl.markWaited h.handleId waited
        if !ok then return .error (Model.mapRawErrorModel (.userError "process handle vanished"))
        return .ok outcome

private def killGraceProbeLoopRef {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (target : Int32) : Nat → m Bool
  | 0 => pure false
  | steps + 1 => do
    refSleepMonoMs timeRand 5
    match ← proc.kill target .sigzero with
    | .error e => if e == Errno.ESRCH then return true else killGraceProbeLoopRef proc timeRand target steps
    | .ok () => killGraceProbeLoopRef proc timeRand target steps

private def killProcessGroupPureRef {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.lookupPgid h.handleId with
  | none => return .ok ()
  | some pgid =>
    if pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID then return .ok ()
    let target : Int32 := if pgid == 1 then 1 else -(pgid.toInt32)
    match ← retryEintr (deps.proc.kill target .sigterm) eintrFuel with
    | .error e =>
      if e == Errno.ESRCH then return .ok () else return .error (refMapErrno none "kill" e)
    | .ok () =>
      if ← killGraceProbeLoopRef deps.proc deps.timeRand target 5 then return .ok ()
      match ← retryEintr (deps.proc.kill target .sigkill) eintrFuel with
      | .error e =>
        if e == Errno.ESRCH then return .ok () else return .error (refMapErrno none "kill" e)
      | .ok () => return .ok ()

private def waitpidReapLoopRef {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32) :
    Nat → m (Except (Option Errno) Unit)
  | 0 => pure (.error none)
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok _ => return .ok ()
    | .error e =>
      if e == Errno.EINTR then waitpidReapLoopRef proc pid fuel
      else if e == Errno.ECHILD then return .ok ()
      else return .error (some e)

private def reapPureRef {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.detachSlot h.handleId with
  | none => return .ok ()
  | some slot =>
    refCloseOpt deps.files slot.stdinFd?
    refCloseOpt deps.files slot.stdoutFd?
    refCloseOpt deps.files slot.stderrFd?
    if !slot.waited && slot.pid > 0 && slot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
      match ← waitpidReapLoopRef deps.proc slot.pid.toInt32 eintrFuel with
      | .ok () => return .ok ()
      | .error none => return .error (Model.mapRawErrorModel (.userError "reap waitpid EINTR retry budget exhausted"))
      | .error (some e) => return .error (refMapErrno none "waitpid" e)
    else return .ok ()

/-- Spec-passing reference `mkRawOpsM` over `SysDepsM` and `ProcTableOpsM`. -/
def refMkRawOpsM {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL)
    (ioFuel : Nat := DEFAULT_IO_FUEL) : RawProcessOpsM m :=
  { mapRawError := Model.mapRawErrorModel
    spawn := refSpawnPure deps tbl eintrFuel
    awaitOutput := awaitOutputPureRef deps tbl eintrFuel ioFuel
    killProcessGroup := killProcessGroupPureRef deps tbl eintrFuel
    reap := reapPureRef deps tbl eintrFuel
    activeProcessCount := tbl.activeCount }

private def runRef {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (req : ExecRequest) :
    m (Except ProcessError ExecResult) := do
  match Model.validateRequestModel req with
  | .error err => return .error err
  | .ok norm =>
    match ← raw.spawn norm with
    | .error err => return .error (refEnsureNonEmptyMsg "process spawn failed" err)
    | .ok h =>
      match ← raw.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes with
      | .error err =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error (refEnsureNonEmptyMsg "process I/O failed" err)
      | .ok (.exited res) =>
        match ← raw.reap h with
        | .error err => return .error (refEnsureNonEmptyMsg "process reap failed" err)
        | .ok () => return .ok res
      | .ok (.signaled sig out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .terminatedBySignal, program := some norm.program, signal := some sig,
            stdout := some out, stderr := some err,
            message := s!"process '{norm.program}' terminated by signal {sig}" }
      | .ok (.timedOut out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .timedOut, program := some norm.program,
            stdout := some out, stderr := some err,
            message := s!"process '{norm.program}' timed out" }
      | .ok (.outputLimitExceeded out err) =>
        let _ ← raw.killProcessGroup h
        let _ ← raw.reap h
        return .error
          { kind := .outputLimitExceeded, program := some norm.program,
            stdout := some out, stderr := some err,
            message := s!"process '{norm.program}' exceeded output byte limit" }

private def runCheckedRef {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) (req : ExecRequest) :
    m (Except ProcessError ExecResult) := do
  match ← runRef raw req with
  | .error err => return .error err
  | .ok res =>
    if res.exitCode == 0 then return .ok res
    else
      return .error
        { kind := .nonZeroExit, program := some req.program, exitCode := some res.exitCode,
          stdout := some res.stdout, stderr := some res.stderr,
          message := s!"process '{req.program}' exited with status {res.exitCode}" }

/-- Spec-passing reference `mkApiM` over `RawProcessOpsM`. -/
def refMkApiM {m : Type → Type} [Monad m] (raw : RawProcessOpsM m) : ProcessApiM m :=
  { mapRawError := raw.mapRawError
    validateRequest := Model.validateRequestModel
    mkCommandRequest := Model.mkCommandRequestModel
    withTextInput := Model.withTextInputModel
    spawn := fun req => do
      match Model.validateSpawnRequestModel req with
      | .error err => return .error err
      | .ok norm =>
        match ← raw.spawn { toSpawnRequest := norm } with
        | .error err => return .error (refEnsureNonEmptyMsg "process spawn failed" err)
        | .ok h => return .ok h
    awaitOutput := fun h stdin timeoutMs maxOutputBytes => do
      if timeoutMs == some 0 then
        return .error { kind := .invalidInput, message := "timeoutMs must be greater than zero" }
      match ← raw.awaitOutput h stdin timeoutMs maxOutputBytes with
      | .error err => return .error (refEnsureNonEmptyMsg "process I/O failed" err)
      | .ok out => return .ok out
    killProcessGroup := fun h => do
      match ← raw.killProcessGroup h with
      | .error err => return .error (refEnsureNonEmptyMsg "process group termination failed" err)
      | .ok () => return .ok ()
    reap := fun h => do
      match ← raw.reap h with
      | .error err => return .error (refEnsureNonEmptyMsg "process reap failed" err)
      | .ok () => return .ok ()
    run := runRef raw
    runChecked := runCheckedRef raw
    runCommand := fun program args => runRef raw (Model.mkCommandRequestModel program args)
    runCommandChecked := fun program args => runCheckedRef raw (Model.mkCommandRequestModel program args)
    activeProcessCount := raw.activeProcessCount }

end LeanSwe.Process.SpecMutants

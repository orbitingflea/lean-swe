import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.SysBridge.ErrorAndEnv
import LeanSwe.Process.SysBridge.PathAndSpawn
import LeanSwe.Process.SysBridge.StreamIo

/-!
Blocking/timed `waitpid` loops, `SIGTERM` -> `SIGKILL` process-group termination,
`reap`, and capability-parameterized `mkRawOpsM` / `mkFullRawOpsM` builders for
`LeanSwe.Process.SysBridge`.
-/

namespace LeanSwe.Process.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Decode a reaped `WaitResult` into `ExecOutcome`. -/
def decodeWaitOutcome (wr : LinuxSyscall.Process.WaitResult) (stdout stderr : ByteArray) : ExecOutcome :=
  match wr with
  | .exited _ code => .exited { exitCode := Int.ofNat code.toNat, stdout := stdout, stderr := stderr }
  | .signaled _ sig _ => .signaled (Int.ofNat sig.toNat) stdout stderr
  | _ => .exited { exitCode := 1, stdout := stdout, stderr := stderr }

/-- Blocking `waitpid` loop used when `timeoutMs? = none` (retries `EINTR`, treats `ECHILD` as exit `0`). -/
def waitBlockingLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (pid : Int32)
    (stdout stderr : ByteArray) : Nat → m (Except ProcessError ExecOutcome)
  | 0 => pure (.error (mapRawError (.userError "waitpid EINTR retry budget exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid {} with
    | .ok wr => return .ok (decodeWaitOutcome wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then
        waitBlockingLoop proc pid stdout stderr fuel
      else if e == Errno.ECHILD then
        return .ok (.exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else
        return .error (mapErrno none "waitpid" e)

/-- Non-blocking `WNOHANG` `waitpid` + `clock_nanosleep` loop used when `timeoutMs? = some timeoutMs`. -/
def waitTimedLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) :
    Nat → m (Except ProcessError (Bool × ExecOutcome))
  | 0 => pure (.error (mapRawError (.userError "waitpid timeout loop fuel exhausted")))
  | fuel + 1 => do
    match ← proc.waitpid pid { nohang := true } with
    | .ok .stillRunning =>
      match ← TimeRand.checkTimedOut timeRand startMs (some timeoutMs) with
      | .error e => return .error (mapErrno none "clock_gettime" e)
      | .ok (true, _) => return .ok (false, .timedOut stdout stderr)
      | .ok (false, remMs) =>
        TimeRand.sleepMonoMs timeRand (Nat.min remMs 5)
        waitTimedLoop proc timeRand pid startMs timeoutMs stdout stderr fuel
    | .ok wr =>
      return .ok (true, decodeWaitOutcome wr stdout stderr)
    | .error e =>
      if e == Errno.EINTR then
        waitTimedLoop proc timeRand pid startMs timeoutMs stdout stderr fuel
      else if e == Errno.ECHILD then
        return .ok (true, .exited { exitCode := 0, stdout := stdout, stderr := stderr })
      else
        return .error (mapErrno none "waitpid" e)

/-- Close `inFd0?` immediately when `stdin` is empty, or set `O_NONBLOCK` and retain it otherwise. -/
def setupStdinPipe {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (stdin : ByteArray) (inFd0? : Option fd) : m (Option fd) :=
  if stdin.size == 0 then do
    Files.closeOpt files inFd0?
    pure none
  else
    match inFd0? with
    | none => pure none
    | some inFd => do
      let _ ← files.fcntl inFd (.setFl true false)
      pure (some inFd)

/-- Read monotonic start timestamp when `timeoutMs?` is `some _`, or return `0` when `none`. -/
def readStartMsOpt {m : Type → Type} [Monad m]
    (timeRand : TimeRand.TimeRandOpsM m) : Option Nat → m (Except ProcessError Nat)
  | none => pure (.ok 0)
  | some _ => do
    match ← TimeRand.monoNowMs timeRand with
    | .ok ms => return .ok ms
    | .error e => return .error (mapErrno none "clock_gettime" e)

/-- OS-only streaming and wait phase of `awaitOutput` (never touches the handle table). -/
def awaitOsPhase {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (eintrFuel ioFuel : Nat)
    (pid : UInt32) (inFd0? outFd0? errFd0? : Option fd)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat) :
    m (Except ProcessError (Bool × ExecOutcome)) := do
  let inFd? ← setupStdinPipe deps.files stdin inFd0?
  Files.setNonblockingOpt deps.files outFd0?
  Files.setNonblockingOpt deps.files errFd0?
  match ← readStartMsOpt deps.timeRand timeoutMs? with
  | .error e =>
    Files.closeOpt deps.files inFd?
    Files.closeOpt deps.files outFd0?
    Files.closeOpt deps.files errFd0?
    return .error e
  | .ok startMs =>
    let initSt : StreamLoopState fd :=
      { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
    match ← streamPipesLoop deps.files deps.poll deps.timeRand stdin startMs timeoutMs? maxOutputBytes? eintrFuel initSt ioFuel with
    | .error e => return .error e
    | .ok (.timedOut out err) => return .ok (false, .timedOut out err)
    | .ok (.limitExceeded out err) => return .ok (false, .outputLimitExceeded out err)
    | .ok (.eof out err) =>
      let pidI32 := pid.toInt32
      match timeoutMs? with
      | none =>
        match ← waitBlockingLoop deps.proc pidI32 out err eintrFuel with
        | .error e => return .error e
        | .ok outcome => return .ok (true, outcome)
      | some timeoutMs =>
        waitTimedLoop deps.proc deps.timeRand pidI32 startMs timeoutMs out err ioFuel

/-- Pure capability-parameterized implementation of `RawProcessOpsM.awaitOutput`, delegating OS work to `awaitOsPhase`. -/
def awaitOutputPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel ioFuel : Nat) (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs? maxOutputBytes? : Option Nat) : m (Except ProcessError ExecOutcome) := do
  match ← tbl.takeSlotIo h.handleId with
  | none =>
    return .error (mapRawError (.userError "invalid process handle"))
  | some (pid, inFd0?, outFd0?, errFd0?) =>
    match ← awaitOsPhase deps eintrFuel ioFuel pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOutputBytes? with
    | .error err => return .error err
    | .ok (waited, outcome) =>
      let ok ← tbl.markWaited h.handleId waited
      if !ok then
        return .error (mapRawError (.userError "process handle vanished"))
      return .ok outcome

/-- 5-step × 5ms grace probe loop between `SIGTERM` and `SIGKILL` (`true` if group already vanished). -/
def killGraceProbeLoop {m : Type → Type} [Monad m] {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (target : Int32) : Nat → m Bool
  | 0 => pure false
  | steps + 1 => do
    TimeRand.sleepMonoMs timeRand 5
    match ← proc.kill target .sigzero with
    | .error e =>
      if e == Errno.ESRCH then return true
      else killGraceProbeLoop proc timeRand target steps
    | .ok () =>
      killGraceProbeLoop proc timeRand target steps

/-- OS-only phase of `killProcessGroup` for a resolved `pgid` (never touches the handle table). -/
def killGroupOsPhase {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (eintrFuel : Nat) (pgid : UInt32) :
    m (Except ProcessError Unit) := do
  if pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID then
    return .ok ()
  let target := LinuxSyscall.Process.killTargetOfPgid pgid
  match ← retryEintr (deps.proc.kill target .sigterm) eintrFuel with
  | .error e =>
    if e == Errno.ESRCH then return .ok ()
    else return .error (mapErrno none "kill" e)
  | .ok () =>
    let vanished ← killGraceProbeLoop deps.proc deps.timeRand target 5
    if vanished then
      return .ok ()
    match ← retryEintr (deps.proc.kill target .sigkill) eintrFuel with
    | .error e =>
      if e == Errno.ESRCH then return .ok ()
      else return .error (mapErrno none "kill" e)
    | .ok () =>
      return .ok ()

/-- Pure capability-parameterized implementation of `RawProcessOpsM.killProcessGroup`, delegating OS work to `killGroupOsPhase`. -/
def killProcessGroupPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.lookupPgid h.handleId with
  | none => return .ok ()
  | some pgid => killGroupOsPhase deps eintrFuel pgid

/-- OS-only phase of `reap` for a detached `ProcSlotM` (never touches the handle table). -/
def reapOsPhase {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (eintrFuel : Nat) (slot : ProcSlotM fd) :
    m (Except ProcessError Unit) := do
  Files.closeOpt deps.files slot.stdinFd?
  Files.closeOpt deps.files slot.stdoutFd?
  Files.closeOpt deps.files slot.stderrFd?
  if !slot.waited && slot.pid > 0 && slot.pid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
    match ← LinuxSyscall.Process.waitpidReapLoop deps.proc slot.pid.toInt32 eintrFuel with
    | .ok () => return .ok ()
    | .error none => return .error (mapRawError (.userError "reap waitpid EINTR retry budget exhausted"))
    | .error (some e) => return .error (mapErrno none "waitpid" e)
  else
    return .ok ()

/-- Pure capability-parameterized implementation of `RawProcessOpsM.reap`, delegating OS work to `reapOsPhase`. -/
def reapPure {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd) (eintrFuel : Nat)
    (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← tbl.detachSlot h.handleId with
  | none => return .ok ()
  | some slot => reapOsPhase deps eintrFuel slot

/-- Construct a `RawProcessOpsM m` bundle purely over `SysDepsM m fd` and `ProcTableOpsM m fd`. -/
def mkRawOpsM {m : Type → Type} [Monad m] {fd : Type}
    (deps : SysDepsM m fd) (tbl : ProcTableOpsM m fd)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL)
    (ioFuel : Nat := DEFAULT_IO_FUEL) : RawProcessOpsM m :=
  { mapRawError := mapRawError
    spawn := spawnPure deps tbl eintrFuel
    awaitOutput := awaitOutputPure deps tbl eintrFuel ioFuel
    killProcessGroup := killProcessGroupPure deps tbl eintrFuel
    reap := reapPure deps tbl eintrFuel
    activeProcessCount := tbl.activeCount }

/-- Project `SysDepsM m RawFd` from `ProcessSysCapsM m`. -/
def sysDepsOfCaps {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) : SysDepsM m RawFd where
  proc := sys.proc
  files := sys.files
  poll := sys.poll
  timeRand := sys.timeRand
  postFork := sys.postFork
  listAmbientEnv := Except.ok <$> sys.envRaw.listEnvironBytes

/-- Normalize a caught `ConcOpsM.tryCatchMsg` error message into a `ProcessError`. -/
def mapCaughtMsg (prog? : Option String) (msg : String) : ProcessError :=
  let mapped := mapRawError (.userError msg)
  { mapped with program := mapped.program <|> prog? }

/-- `ConcOpsM` + `StateCellM` implementation of `RawProcessOpsM.spawn` keeping `cell` outside `tryCatchMsg`. -/
def spawnConc {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcTableState RawFd))
    (eintrFuel : Nat) (req : ExecRequest) : m (Except ProcessError ProcessHandle) := do
  match ← conc.tryCatchMsg (spawnOsPhase (sysDepsOfCaps sys) eintrFuel req) with
  | .error msg => return .error (mapCaughtMsg (some req.program) msg)
  | .ok (.error err) => return .error err
  | .ok (.ok slot) =>
    let hid ← cell.modifyGet (fun st => insertSlotPure st slot)
    return .ok
      { handleId := hid
        pid := Int.ofNat slot.pid.toNat
        pgid := Int.ofNat slot.pgid.toNat }

/-- `ConcOpsM` + `StateCellM` implementation of `RawProcessOpsM.awaitOutput` keeping `cell` outside `tryCatchMsg`. -/
def awaitOutputConc {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcTableState RawFd))
    (eintrFuel ioFuel : Nat) (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs? maxOutputBytes? : Option Nat) : m (Except ProcessError ExecOutcome) := do
  match ← cell.modifyGet (fun st => takeSlotIoPure st h.handleId) with
  | none => return .error (mapRawError (.userError "invalid process handle"))
  | some (pid, inFd0?, outFd0?, errFd0?) =>
    match ← conc.tryCatchMsg
        (awaitOsPhase (sysDepsOfCaps sys) eintrFuel ioFuel pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOutputBytes?) with
    | .error msg => return .error (mapCaughtMsg none msg)
    | .ok (.error err) => return .error err
    | .ok (.ok (waitedFlag, outcome)) =>
      let ok ← cell.modifyGet (fun st => markWaitedPure st h.handleId waitedFlag)
      if !ok then
        return .error (mapRawError (.userError "process handle vanished"))
      return .ok outcome

/-- `ConcOpsM` + `StateCellM` implementation of `RawProcessOpsM.killProcessGroup` keeping `cell` outside `tryCatchMsg`. -/
def killProcessGroupConc {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcTableState RawFd))
    (eintrFuel : Nat) (h : ProcessHandle) : m (Except ProcessError Unit) := do
  let st ← cell.get
  match (findSlotPure h.handleId st.slots).map (·.pgid) with
  | none => return .ok ()
  | some pgid =>
    match ← conc.tryCatchMsg (killGroupOsPhase (sysDepsOfCaps sys) eintrFuel pgid) with
    | .error msg => return .error (mapCaughtMsg none msg)
    | .ok res => return res

/-- `ConcOpsM` + `StateCellM` implementation of `RawProcessOpsM.reap` keeping `cell` outside `tryCatchMsg`. -/
def reapConc {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcTableState RawFd))
    (eintrFuel : Nat) (h : ProcessHandle) : m (Except ProcessError Unit) := do
  match ← cell.modifyGet (fun st => detachSlotPure st h.handleId) with
  | none => return .ok ()
  | some slot =>
    match ← conc.tryCatchMsg (reapOsPhase (sysDepsOfCaps sys) eintrFuel slot) with
    | .error msg => return .error (mapCaughtMsg none msg)
    | .ok res => return res

/-- Construct a `RawProcessOpsM m` directly over `ProcessSysCapsM m`, `Core.ConcOpsM m`, and `Core.StateCellM m`. -/
def mkFullRawOpsM {m : Type → Type} [Monad m]
    (sys : ProcessSysCapsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (ProcTableState RawFd))
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL)
    (ioFuel : Nat := DEFAULT_IO_FUEL) : RawProcessOpsM m :=
  { mapRawError := mapRawError
    spawn := spawnConc sys conc cell eintrFuel
    awaitOutput := awaitOutputConc sys conc cell eintrFuel ioFuel
    killProcessGroup := killProcessGroupConc sys conc cell eintrFuel
    reap := reapConc sys conc cell eintrFuel
    activeProcessCount := do
      let st ← cell.get
      return st.slots.length }

end LeanSwe.Process.SysBridge

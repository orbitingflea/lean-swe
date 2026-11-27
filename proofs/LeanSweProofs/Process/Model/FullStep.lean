import LeanSwe.LinuxSyscall.Common.Types
import LeanSweProofs.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Process.Types
import LeanSweProofs.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSweProofs.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSweProofs.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import LeanSwe.PostFork.Types
import LeanSwe.EnvVars.Types
import LeanSweProofs.EnvVars.Model
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSweProofs.Process.Model
import LeanSweProofs.Process.Model.HealthyHost

/-!
Compositional `RawFd`-specialized step specification for `LeanSwe.Process` over
`Internal.ProcessSysCapsM`, `Core.ConcOpsM`, and `Core.StateCellM` (`Core.ObeysStepFromConcCell`).
-/

namespace LeanSwe.Process.Model

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- Scoped `LinuxSyscall.Process` request sum over `RawFd` consumed by `Process.SysBridge`. -/
inductive RawFdProcReq where
  /-- Allocate a pipe descriptor pair via `pipe2(2)`. -/
  | pipe2 (flags : LinuxSyscall.Process.PipeFlags)
  /-- Wait on child process `pid` via `waitpid(2)`. -/
  | waitpid (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags)
  /-- Deliver signal `sig` to `target` via `kill(2)`. -/
  | kill (target : Int32) (sig : LinuxSyscall.Process.Signal)
  deriving BEq, DecidableEq

instance : Inhabited RawFdProcReq where
  default := .pipe2 {}

/-- Embed `RawFdProcReq` into `LinuxSyscall.Process.ProcessReq`. -/
def mapRawFdProcReq : RawFdProcReq → LinuxSyscall.Process.ProcessReq
  | .pipe2 flags => .pipe2 flags
  | .waitpid pid flags => .waitpid pid flags
  | .kill target sig => .kill target sig

/-- Outcome sum for `RawFdProcReq` over `RawFd`. -/
inductive RawFdProcOut where
  /-- `pipe2` succeeded returning `(readFd, writeFd)`. -/
  | piped (readFd writeFd : RawFd)
  /-- `waitpid` succeeded returning `wr`. -/
  | waited (wr : LinuxSyscall.Process.WaitResult)
  /-- `kill` succeeded returning `()`. -/
  | unit
  /-- Process syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdProcOut` to a model `LinuxSyscall.Process.ProcessOutcome`. -/
def RawFdProcOut.MatchesModel : RawFdProcOut → LinuxSyscall.Process.ProcessOutcome → Prop
  | .piped _ _, .piped _ _ => True
  | .waited wr, .waited wr' => wr = wr'
  | .unit, .unit => True
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Wrap `Except Errno (RawFd × RawFd)` into `RawFdProcOut`. -/
def rawFdProcOutOfPiped : Except Errno (RawFd × RawFd) → RawFdProcOut
  | .ok (r, w) => .piped r w
  | .error e => .err e

/-- Wrap `Except Errno WaitResult` into `RawFdProcOut`. -/
def rawFdProcOutOfWaited : Except Errno LinuxSyscall.Process.WaitResult → RawFdProcOut
  | .ok wr => .waited wr
  | .error e => .err e

/-- Wrap `Except Errno Unit` into `RawFdProcOut`. -/
def rawFdProcOutOfUnit : Except Errno Unit → RawFdProcOut
  | .ok () => .unit
  | .error e => .err e

/-- Execute one `RawFdProcReq` against `proc : LinuxSyscall.Process.ProcessOpsM (StateM W) RawFd`. -/
def execRawFdProcReq {W : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM (StateM W) RawFd) :
    RawFdProcReq → StateM W RawFdProcOut
  | .pipe2 flags => rawFdProcOutOfPiped <$> proc.pipe2 flags
  | .waitpid pid flags => rawFdProcOutOfWaited <$> proc.waitpid pid flags
  | .kill target sig => rawFdProcOutOfUnit <$> proc.kill target sig

/-- Scoped `LinuxSyscall.Files` request sum over `RawFd` consumed by `Process.SysBridge`. -/
inductive RawFdFilesReq where
  /-- Close file descriptor `fd` via `close(2)`. -/
  | close (fd : RawFd)
  /-- Read up to `maxBytes` from `fd` via `read(2)`. -/
  | read (fd : RawFd) (maxBytes : UInt32)
  /-- Write `data` to `fd` via `write(2)`. -/
  | write (fd : RawFd) (data : ByteArray)
  /-- Stat `path` relative to `dir` via `fstatat(2)`. -/
  | fstatat (dir : Option RawFd) (path : ByteArray) (flags : Files.AtFlags)
  /-- Check access permissions on `path` relative to `dir` via `faccessat(2)`. -/
  | faccessat (dir : Option RawFd) (path : ByteArray) (mask : Files.AccessModeMask) (flags : Files.AtFlags)
  /-- Manipulate descriptor flags on `fd` via `fcntl(2)`. -/
  | fcntl (fd : RawFd) (cmd : Files.FcntlCmd)

/-- Map `RawFdFilesReq` into `LinuxSyscall.Files.FilesReq` via `toHid : RawFd → Nat`. -/
def mapRawFdFilesReq (toHid : RawFd → Nat) : RawFdFilesReq → Files.FilesReq
  | .close fd => .close (toHid fd)
  | .read fd maxBytes => .read (toHid fd) maxBytes
  | .write fd data => .write (toHid fd) data
  | .fstatat dir path flags => .fstatat (dir.map toHid) path flags
  | .faccessat dir path mask flags => .faccessat (dir.map toHid) path mask flags
  | .fcntl fd cmd => .fcntl (toHid fd) cmd

/-- Execute one `RawFdFilesReq` against `files : LinuxSyscall.Files.FilesOpsM (StateM W) RawFd`. -/
def execRawFdFilesReq {W : Type} (files : Files.FilesOpsM (StateM W) RawFd) :
    RawFdFilesReq → StateM W Files.FilesOutcome
  | .close fd => Files.outcomeOfUnit <$> files.close fd
  | .read fd maxBytes => Files.outcomeOfBytes <$> files.read fd maxBytes
  | .write fd data => Files.outcomeOfU32 <$> files.write fd data
  | .fstatat dir path flags => Files.outcomeOfStatted <$> files.fstatat dir path flags
  | .faccessat dir path mask flags => Files.outcomeOfUnit <$> files.faccessat dir path mask flags
  | .fcntl fd cmd => Files.outcomeOfU32 <$> files.fcntl fd cmd

/-- Outcome sum for `PostFork.spawn` over `RawFd`. -/
inductive RawFdPostForkOut where
  /-- Child process launched returning `child`. -/
  | spawned (child : PostFork.SpawnedChild)
  /-- Child launch failed with `err`. -/
  | err (err : PostFork.PostForkError)
  deriving BEq, DecidableEq

/-- Wrap `Except PostForkError SpawnedChild` into `RawFdPostForkOut`. -/
def rawFdPostForkOutOf : Except PostFork.PostForkError PostFork.SpawnedChild → RawFdPostForkOut
  | .ok child => .spawned child
  | .error err => .err err

/-- Wrap `Except Errno (Array Poll.PollEvents)` into `Poll.PollOutcome`. -/
def rawFdPollOutOf : Except Errno (Array Poll.PollEvents) → Poll.PollOutcome
  | .ok revents => .polled revents
  | .error e => .err e

/-- Unified raw OS capability request across all 6 `manifest.deps` in `Internal.ProcessSysCapsM`. -/
inductive FullRawReq where
  /-- Execute a `LinuxSyscall.Process` request over `RawFd`. -/
  | proc (req : RawFdProcReq)
  /-- Execute a `LinuxSyscall.Files` request over `RawFd`. -/
  | files (req : RawFdFilesReq)
  /-- Execute a `LinuxSyscall.Poll.ppoll` readiness check over `RawFd`. -/
  | poll (entries : Array (RawFd × Poll.PollEvents)) (timeout? : Option Poll.Timespec)
  /-- Execute a `LinuxSyscall.TimeRand` clock/sleep/random request. -/
  | timeRand (req : TimeRand.TimeRandReq)
  /-- Execute a verified `PostFork.spawn` child launch over `RawFd`. -/
  | postFork (spec : PostFork.ChildSpecM RawFd)
  /-- Execute an `EnvVars` environment snapshot/query request. -/
  | envRaw (req : EnvVars.Model.PkgStepReq)

instance : Inhabited FullRawReq where
  default := .envRaw .listEnvironBytes

/-- Unified raw OS capability outcome paired with `FullRawReq`. -/
inductive FullRawOut where
  /-- Decoded `LinuxSyscall.Process` outcome over `RawFd`. -/
  | proc (out : RawFdProcOut)
  /-- Decoded `LinuxSyscall.Files` outcome. -/
  | files (out : Files.FilesOutcome)
  /-- Decoded `LinuxSyscall.Poll` outcome. -/
  | poll (out : Poll.PollOutcome)
  /-- Decoded `LinuxSyscall.TimeRand` outcome. -/
  | timeRand (out : TimeRand.TimeRandOutcome)
  /-- Decoded `PostFork.spawn` outcome. -/
  | postFork (out : RawFdPostForkOut)
  /-- Decoded `EnvVars` outcome. -/
  | envRaw (out : EnvVars.Model.PkgStepOut)

instance : Inhabited FullRawOut where
  default := .envRaw default

/-- Execute one `FullRawReq` against `sys : Internal.ProcessSysCapsM (StateM W)`. -/
def execFullRawStep {W : Type} (sys : Internal.ProcessSysCapsM (StateM W)) :
    FullRawReq → StateM W FullRawOut
  | .proc r => .proc <$> execRawFdProcReq sys.proc r
  | .files r => .files <$> execRawFdFilesReq sys.files r
  | .poll entries to? => (fun res => .poll (rawFdPollOutOf res)) <$> sys.poll.ppoll entries to?
  | .timeRand r => .timeRand <$> TimeRand.execTimeRandReq sys.timeRand r
  | .postFork spec => (fun res => .postFork (rawFdPostForkOutOf res)) <$> sys.postFork.spawn spec
  | .envRaw r => .envRaw <$> EnvVars.Model.execPkgStep sys.envRaw r

/-- Healthy OS world state across `LinuxSyscall.{Process,Files,TimeRand}` and `EnvVars`. -/
structure FullHostWorld where
  /-- Healthy Linux process environment. -/
  proc : LinuxSyscall.Process.HealthyEnv := LinuxSyscall.Process.HealthyEnv.initial
  /-- Healthy Linux filesystem environment. -/
  files : Files.HealthyEnv := Files.HealthyEnv.initial
  /-- Healthy Linux clock/random environment. -/
  time : TimeRand.HealthyEnv := TimeRand.HealthyEnv.initial
  /-- Ambient POSIX `environ(7)` byte table. -/
  env : EnvVars.Model.EnvironState := { entries := #["PATH=/bin:/usr/bin".toUTF8] }

instance : Inhabited FullHostWorld where
  default := {}

/-- Well-formedness guard on `FullHostWorld` requiring healthy syscall subsystems and NUL-free `environ(7)`. -/
def fullRawWf (w : FullHostWorld) : Bool :=
  w.proc.wf && w.files.wf && w.time.wf && w.env.isWellFormed

/-- Relational single-step contract for `Internal.ProcessSysCapsM` over `FullHostWorld`. -/
def allowedFullRawStep (w : FullHostWorld) (req : FullRawReq) (out : FullRawOut)
    (w' : FullHostWorld) : Prop :=
  fullRawWf w = true ∧
  fullRawWf w' = true ∧
  match req, out with
  | .proc r, .proc po =>
    ∃ mo : LinuxSyscall.Process.ProcessOutcome,
      RawFdProcOut.MatchesModel po mo ∧
      LinuxSyscall.Process.healthyStep w.proc (mapRawFdProcReq r) mo = some w'.proc ∧
      w'.time = w.time ∧
      w'.env = w.env
  | .files r, .files fo =>
    (∃ toHid : RawFd → Nat,
      Files.healthyStep w.files (mapRawFdFilesReq toHid r) fo = some w'.files) ∧
    w'.proc = w.proc ∧
    w'.time = w.time ∧
    w'.env = w.env ∧
    (∀ fd cap bs, r = .read fd cap → fo = .bytes bs → bs.size ≤ cap.toNat) ∧
    (∀ fd data n, r = .write fd data → fo = .u32 n → n.toNat ≤ data.size)
  | .poll entries _, .poll po =>
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.env = w.env ∧
    match po with
    | .polled revents => revents.size = entries.size
    | .err e => Errno.isCriticalOsErrno e = false
    | .opened _ => False
  | .timeRand r, .timeRand to =>
    TimeRand.healthyStep w.time r to = some w'.time ∧
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.env = w.env
  | .postFork spec, .postFork pfo =>
    w'.time = w.time ∧
    w'.env = w.env ∧
    match pfo with
    | .spawned child =>
      1 ≤ child.pid ∧
      child.pid ≤ maxLinuxPidModel ∧
      (spec.processGroup = .newGroup → child.pgid = some child.pid)
    | .err err =>
      (∀ e, err.errno = some e → Errno.isCriticalOsErrno e = false) ∧
      (∀ cf, err.childFailure = some cf → Errno.isCriticalOsErrno cf.errno = false)
  | .envRaw r, .envRaw eo =>
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.time = w.time ∧
    EnvVars.Model.allowedPkgStep w.env r eo w'.env
  | _, _ => False

/-- Project a `(handleId, ProcSlotM fd)` entry into a public `ProcessHandleEntry`. -/
def rawSlotToEntry {fd : Type} (p : Nat × Internal.ProcSlotM fd) : ProcessHandleEntry :=
  { handleId := p.1
    pid := Int.ofNat p.2.pid.toNat
    pgid := Int.ofNat p.2.pgid.toNat
    ioConsumed := p.2.stdinFd?.isNone && p.2.stdoutFd?.isNone && p.2.stderrFd?.isNone
    waited := p.2.waited }

/-- Project `Internal.ProcTableState fd` into abstract `ProcessModelState`. -/
def rawTableToState {fd : Type} (t : Internal.ProcTableState fd) : ProcessModelState :=
  { nextHandleId := t.nextId
    activeHandles := t.slots.map rawSlotToEntry }

/-- Well-formedness check on a single `ProcSlotM fd` requiring positive 32-bit Linux PID/PGID bounds. -/
def procSlotWf {fd : Type} (s : Internal.ProcSlotM fd) : Bool :=
  decide (1 ≤ s.pid ∧ s.pid ≤ maxLinuxPidModel ∧ 1 ≤ s.pgid ∧ s.pgid ≤ maxLinuxPidModel)

/-- Well-formedness guard on `Internal.ProcTableState fd` combining slot PID/PGID bounds and `processStateWf`. -/
def procCellWf {fd : Type} (t : Internal.ProcTableState fd) : Bool :=
  t.slots.all (fun p => procSlotWf p.2) && processStateWf (rawTableToState t)

/-- Project `Internal.ProcCellS Ref TaskH` into `ProcessModelState` (mapping ill-formed tables to `nextHandleId = 0`). -/
def procCellToState {Ref TaskH : Type → Type} (t : Internal.ProcCellS Ref TaskH) : ProcessModelState :=
  if procCellWf t then rawTableToState t else { nextHandleId := 0, activeHandles := [] }

/-- Combine `FullHostWorld` health and cell-projected `ProcessModelState` for `Core.ObeysStepFromConcCell`. -/
def mapFullWorldToState (w : FullHostWorld) (s : ProcessModelState) : ProcessModelState :=
  if fullRawWf w then s else { nextHandleId := 0, activeHandles := [] }

end LeanSwe.Process.Model

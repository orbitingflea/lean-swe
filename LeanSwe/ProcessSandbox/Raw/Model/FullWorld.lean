import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Sandbox.Model.Refines
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.LinuxSyscall.Passwd.Model.Refines
import LeanSwe.PostFork.Model.Refines
import LeanSwe.EnvVars.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Types.Internal
import LeanSwe.ProcessSandbox.Raw.Model.Refines

namespace LeanSwe.ProcessSandbox.Raw.Model

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

/-- Unified OS capability bundle over `manifest.deps` specialized to `LinuxSyscall.RawFd` for compositional `Core.ObeysStepFromConcCell` verification. -/
structure FullSysOpsM (m : Type → Type) where
  /-- Curated Linux file/descriptor syscalls (`LinuxSyscall.Files`). -/
  files : Files.FilesOpsM m RawFd
  /-- Curated Linux socket syscalls (`LinuxSyscall.Net`). -/
  net : Net.NetOpsM m RawFd
  /-- Curated Linux `ppoll` / `eventfd2` syscalls (`LinuxSyscall.Poll`). -/
  poll : Poll.PollOpsM m RawFd
  /-- Curated Linux process syscalls (`LinuxSyscall.Process`). -/
  proc : LinuxSyscall.Process.ProcessOpsM m RawFd
  /-- Curated Linux sandbox syscalls (`LinuxSyscall.Sandbox`). -/
  sandbox : Sandbox.SandboxOpsM m RawFd
  /-- Curated Linux monotonic clock and nanosleep syscalls (`LinuxSyscall.TimeRand`). -/
  timeRand : TimeRand.TimeRandOpsM m
  /-- Curated Linux `getpwuid` / `getpwnam` syscalls (`LinuxSyscall.Passwd`). -/
  passwd : Passwd.PasswdOpsM m
  /-- Verified post-`fork` child setup and sync-barrier bundle (`PostFork`). -/
  postFork : PostFork.PostForkOpsM m RawFd
  /-- Raw OS environment lookup bundle (`EnvVars.Raw`). -/
  envVars : EnvVars.Raw.RawEnvVarsOpsM m

/-- Combined healthy OS world state across all 9 `manifest.deps` capabilities consumed by `LeanSwe.ProcessSandbox.Raw`. -/
structure HealthyRawSysWorld where
  /-- `LinuxSyscall.Files` healthy environment. -/
  filesEnv : Files.HealthyEnv := Files.HealthyEnv.initial
  /-- `LinuxSyscall.Net` healthy environment. -/
  netEnv : Net.HealthyEnv := Net.HealthyEnv.initial
  /-- `LinuxSyscall.Poll` healthy environment. -/
  pollEnv : Poll.HealthyEnv := Poll.HealthyEnv.initial
  /-- `LinuxSyscall.Process` healthy environment. -/
  procEnv : LinuxSyscall.Process.HealthyEnv := LinuxSyscall.Process.HealthyEnv.initial
  /-- `LinuxSyscall.Sandbox` healthy environment. -/
  sandboxEnv : Sandbox.HealthyEnv := Sandbox.HealthyEnv.initial 0
  /-- `LinuxSyscall.TimeRand` healthy environment. -/
  timeEnv : TimeRand.HealthyEnv := TimeRand.HealthyEnv.initial 0 0 true
  /-- `LinuxSyscall.Passwd` healthy environment. -/
  passwdEnv : Passwd.HealthyEnv := Passwd.HealthyEnv.initial 0 true
  /-- `PostFork` host step state. -/
  postForkSt : PostFork.Model.HostStepState := {}
  /-- `EnvVars.Raw` environment snapshot state. -/
  envVarsSt : EnvVars.Raw.Model.EnvironState := {}

/-- Initial well-formed `HealthyRawSysWorld`. -/
def HealthyRawSysWorld.initial : HealthyRawSysWorld := {}

instance : Inhabited HealthyRawSysWorld :=
  ⟨HealthyRawSysWorld.initial⟩

/-- Combined well-formedness check across all 9 `HealthyRawSysWorld` subsystem states. -/
def HealthyRawSysWorld.wf (w : HealthyRawSysWorld) : Bool :=
  w.filesEnv.wf &&
  w.netEnv.wf &&
  w.pollEnv.wf &&
  w.procEnv.wf &&
  w.sandboxEnv.wf &&
  w.timeEnv.wf &&
  w.passwdEnv.wf &&
  PostFork.Model.rawStepWf w.postForkSt &&
  EnvVars.Raw.Model.rawStepWf w.envVarsSt

/-- Canonical well-formedness guard on `HealthyRawSysWorld` for `Core.ObeysStepFromConcCell`. -/
def fullWorldWf (w : HealthyRawSysWorld) : Bool :=
  w.wf

/-- Host platform Linux predicate matching `System.Platform` (`!isWindows && !isOSX`). -/
def hostPlatformIsLinux : Bool :=
  !System.Platform.isWindows && !System.Platform.isOSX

/-- Host compiler target triple (`System.Platform.target`). -/
def hostPlatformTarget : String :=
  System.Platform.target

/-- Project an internal `PlanSlotM fd` onto a model `RawPlanRecord`. -/
def slotPlanToModel {fd : Type} (s : PlanSlotM fd) : RawPlanRecord :=
  { plan := s.plan, planMemfd := 0, initMemfd := 0, hostsMemfd := 0 }

/-- Project an internal `BoxSlotM fd` onto a model `RawBoxRecord`. -/
def slotBoxToModel {fd : Type} (s : BoxSlotM fd) : RawBoxRecord :=
  { pid := s.pid
    pgid := s.pgid
    pidfd := 0
    stdinFd? := s.stdinFd?.map (fun _ => 0)
    stdoutFd? := s.stdoutFd?.map (fun _ => 0)
    stderrFd? := s.stderrFd?.map (fun _ => 0)
    statusFd? := s.statusFd?.map (fun _ => 0)
    goFd? := s.goFd?.map (fun _ => 0)
    readStarted := s.readStarted
    fwdsTaken := s.fwdsTaken
    listenerFds := s.listenerFds.map (fun _ => 0)
    cgroupDir := s.cgroupDir
    program := s.program
    cwd := s.cwd }

/-- Project an internal `ForwarderSlotM fwdTask` onto a model `RawFwdRecord`. -/
def slotFwdToModel {fwdTask : Type} (s : ForwarderSlotM fwdTask) : RawFwdRecord :=
  { boxHandleId := s.boxHandleId, taskHandle := 0 }

/-- Project any `HostTableState fd fwdTask` onto `RawTableState`. -/
def cellTableToModel {fd fwdTask : Type} (t : HostTableState fd fwdTask) : RawTableState :=
  { nextId := t.nextId
    cgSeq := t.cgSeq
    plans := t.plans.map fun (k, v) => (k, slotPlanToModel v)
    boxes := t.boxes.map fun (k, v) => (k, slotBoxToModel v)
    fwds := t.forwarders.map fun (k, v) => (k, slotFwdToModel v) }

/-- Canonical `CellS -> RawTableState` projection for `Core.ObeysStepFromConcCell`. -/
def cellToRawTable {Ref TaskH : Type → Type} (c : HostCellState Ref TaskH) : RawTableState :=
  cellTableToModel c

/-- Combine `(sys : HealthyRawSysWorld)` and `(tbl : RawTableState)` into `RawHostWorld`, gating `rawHostWorldWf` on `sys.wf`. -/
def mapFullToRawWorld (sys : HealthyRawSysWorld) (tbl : RawTableState) : RawHostWorld :=
  if sys.wf then
    { isLinux := hostPlatformIsLinux, target := hostPlatformTarget, table := tbl }
  else
    { isLinux := hostPlatformIsLinux, target := hostPlatformTarget, table := { tbl with nextId := 0 } }

/-- File syscall request over `RawFd` covering all 11 `LinuxSyscall.Files` operations consumed by `ProcessSandbox.Raw`. -/
inductive RawFdFilesReq where
  /-- `files.openat`. -/
  | openat (dir : Option RawFd) (path : ByteArray) (flags : Files.OpenFlags) (mode : Mode)
  /-- `files.close`. -/
  | close (fd : RawFd)
  /-- `files.read`. -/
  | read (fd : RawFd) (maxBytes : UInt32)
  /-- `files.write`. -/
  | write (fd : RawFd) (data : ByteArray)
  /-- `files.fstatat`. -/
  | fstatat (dir : Option RawFd) (path : ByteArray) (flags : Files.AtFlags)
  /-- `files.faccessat`. -/
  | faccessat (dir : Option RawFd) (path : ByteArray) (mask : Files.AccessModeMask) (flags : Files.AtFlags)
  /-- `files.mkdirat`. -/
  | mkdirat (dir : Option RawFd) (path : ByteArray) (mode : Mode)
  /-- `files.unlinkat`. -/
  | unlinkat (dir : Option RawFd) (path : ByteArray) (removeDir : Bool)
  /-- `files.readlinkat`. -/
  | readlinkat (dir : Option RawFd) (path : ByteArray) (cap : UInt32)
  /-- `files.fcntl`. -/
  | fcntl (fd : RawFd) (cmd : Files.FcntlCmd)
  /-- `files.reopenReadOnly`. -/
  | reopenReadOnly (fd : RawFd)

/-- Map a `RawFdFilesReq` into `Files.FilesReq` under handle projection `toHid : RawFd → Nat`. -/
def mapRawFdFilesReq (toHid : RawFd → Nat) : RawFdFilesReq → Files.FilesReq
  | .openat d p fl m => .openat (d.map toHid) p fl m
  | .close fd => .close (toHid fd)
  | .read fd n => .read (toHid fd) n
  | .write fd bs => .write (toHid fd) bs
  | .fstatat d p fl => .fstatat (d.map toHid) p fl
  | .faccessat d p mk fl => .faccessat (d.map toHid) p mk fl
  | .mkdirat d p m => .mkdirat (d.map toHid) p m
  | .unlinkat d p rm => .unlinkat (d.map toHid) p rm
  | .readlinkat d p c => .readlinkat (d.map toHid) p c
  | .fcntl fd cmd => .fcntl (toHid fd) cmd
  | .reopenReadOnly fd => .reopenReadOnly (toHid fd)

/-- File syscall outcome over `RawFd` paired with `RawFdFilesReq`. -/
inductive RawFdFilesOut where
  /-- Descriptor-allocating `openat` or `reopenReadOnly` succeeded. -/
  | opened (fd : RawFd)
  /-- Unit-returning file syscall succeeded. -/
  | unit
  /-- Byte-returning `read` or `readlinkat` succeeded. -/
  | bytes (data : ByteArray)
  /-- Scalar-returning `write` or `fcntl` succeeded. -/
  | u32 (val : UInt32)
  /-- `fstatat` succeeded. -/
  | statted (st : Files.StatInfo)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdFilesOut` to a model `Files.FilesOutcome`. -/
def RawFdFilesOut.MatchesModel : RawFdFilesOut → Files.FilesOutcome → Prop
  | .opened _, .opened _ => True
  | .unit, .unit => True
  | .bytes bs, .bytes bs' => bs = bs'
  | .u32 v, .u32 v' => v = v'
  | .statted st, .statted st' => st = st'
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Execute one `RawFdFilesReq` against `files : Files.FilesOpsM (StateM W) RawFd`. -/
def execRawFdFilesReq {W : Type} (files : Files.FilesOpsM (StateM W) RawFd) :
    RawFdFilesReq → StateM W RawFdFilesOut
  | .openat d p fl m => (fun | .ok fd => .opened fd | .error e => .err e) <$> files.openat d p fl m
  | .close fd => (fun | .ok () => .unit | .error e => .err e) <$> files.close fd
  | .read fd n => (fun | .ok bs => .bytes bs | .error e => .err e) <$> files.read fd n
  | .write fd bs => (fun | .ok v => .u32 v | .error e => .err e) <$> files.write fd bs
  | .fstatat d p fl => (fun | .ok st => .statted st | .error e => .err e) <$> files.fstatat d p fl
  | .faccessat d p mk fl => (fun | .ok () => .unit | .error e => .err e) <$> files.faccessat d p mk fl
  | .mkdirat d p m => (fun | .ok () => .unit | .error e => .err e) <$> files.mkdirat d p m
  | .unlinkat d p rm => (fun | .ok () => .unit | .error e => .err e) <$> files.unlinkat d p rm
  | .readlinkat d p c => (fun | .ok bs => .bytes bs | .error e => .err e) <$> files.readlinkat d p c
  | .fcntl fd cmd => (fun | .ok v => .u32 v | .error e => .err e) <$> files.fcntl fd cmd
  | .reopenReadOnly fd => (fun | .ok nfd => .opened nfd | .error e => .err e) <$> files.reopenReadOnly fd

/-- Socket syscall request over `RawFd` covering all 9 `LinuxSyscall.Net` operations consumed by `ProcessSandbox.Raw` and `Forwarder`. -/
inductive RawFdNetReq where
  /-- `net.socket`. -/
  | socket (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags) (proto : UInt32)
  /-- `net.socketpair`. -/
  | socketpair (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags)
  /-- `net.accept4`. -/
  | accept4 (fd : RawFd) (fl : Net.SockFlags)
  /-- `net.connect`. -/
  | connect (fd : RawFd) (addr : Net.SockAddr)
  /-- `net.getsockopt`. -/
  | getsockopt (fd : RawFd) (opt : Net.SockOpt)
  /-- `net.recvfrom`. -/
  | recvfrom (fd : RawFd) (maxBytes : UInt32) (fl : Net.MsgFlags)
  /-- `net.sendto`. -/
  | sendto (fd : RawFd) (data : ByteArray) (fl : Net.MsgFlags)
  /-- `net.shutdown`. -/
  | shutdown (fd : RawFd) (how : Net.ShutHow)
  /-- `net.recvmsg`. -/
  | recvmsg (fd : RawFd) (maxFds : UInt32)

/-- Map a `RawFdNetReq` into `Net.NetReq` under handle projection `toHid : RawFd → Nat`. -/
def mapRawFdNetReq (toHid : RawFd → Nat) : RawFdNetReq → Net.NetReq
  | .socket dom st fl p => .socket dom st fl p
  | .socketpair dom st fl => .socketpair dom st fl
  | .accept4 d fl => .accept4 (toHid d) fl
  | .connect d sa => .connect (toHid d) sa
  | .getsockopt d opt => .getsockopt (toHid d) opt
  | .recvfrom d n fl => .recvfrom (toHid d) n fl
  | .sendto d bs fl => .sendto (toHid d) bs fl
  | .shutdown d how => .shutdown (toHid d) how
  | .recvmsg d mf => .recvmsg (toHid d) mf

/-- Socket syscall outcome over `RawFd` paired with `RawFdNetReq`. -/
inductive RawFdNetOut where
  /-- `socket` succeeded. -/
  | opened (fd : RawFd)
  /-- `socketpair` succeeded. -/
  | pair (fd0 fd1 : RawFd)
  /-- `accept4` succeeded. -/
  | accepted (fd : RawFd) (addr : Net.SockAddr)
  /-- `recvfrom` succeeded. -/
  | bytes (data : ByteArray)
  /-- `getsockopt` or `sendto` succeeded. -/
  | u32 (val : UInt32)
  /-- `recvmsg` succeeded returning `fds`. -/
  | fds (fds : Array RawFd)
  /-- `connect` or `shutdown` succeeded. -/
  | unit
  /-- Socket syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdNetOut` to a model `Net.NetOutcome`. -/
def RawFdNetOut.MatchesModel : RawFdNetOut → Net.NetOutcome → Prop
  | .opened _, .opened _ => True
  | .pair _ _, .pair _ _ => True
  | .accepted _ sa, .accepted _ sa' => sa = sa'
  | .bytes bs, .bytes bs' => bs = bs'
  | .u32 v, .u32 v' => v = v'
  | .fds ds, .fds hs => ds.size = hs.size
  | .unit, .unit => True
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Execute one `RawFdNetReq` against `net : Net.NetOpsM (StateM W) RawFd`. -/
def execRawFdNetReq {W : Type} (net : Net.NetOpsM (StateM W) RawFd) :
    RawFdNetReq → StateM W RawFdNetOut
  | .socket dom st fl p => (fun | .ok d => .opened d | .error e => .err e) <$> net.socket dom st fl p
  | .socketpair dom st fl => (fun | .ok (a, b) => .pair a b | .error e => .err e) <$> net.socketpair dom st fl
  | .accept4 d fl => (fun | .ok (c, sa) => .accepted c sa | .error e => .err e) <$> net.accept4 d fl
  | .connect d sa => (fun | .ok () => .unit | .error e => .err e) <$> net.connect d sa
  | .getsockopt d opt => (fun | .ok v => .u32 v | .error e => .err e) <$> net.getsockopt d opt
  | .recvfrom d n fl => (fun | .ok bs => .bytes bs | .error e => .err e) <$> net.recvfrom d n fl
  | .sendto d bs fl => (fun | .ok v => .u32 v | .error e => .err e) <$> net.sendto d bs fl
  | .shutdown d how => (fun | .ok () => .unit | .error e => .err e) <$> net.shutdown d how
  | .recvmsg d mf => (fun | .ok ds => .fds ds | .error e => .err e) <$> net.recvmsg d mf

end LeanSwe.ProcessSandbox.Raw.Model

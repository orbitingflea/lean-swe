import Core.ConcOps
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Types.Internal
import LeanSwe.ProcessSandbox.Raw.Model.FullWorld
import LeanSwe.ProcessSandbox.Raw.SysBridge

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.Driver

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge

/-- Execute `act : m (Except Errno α)` via `conc.tryCatchMsg`, mapping runtime exceptions to `Errno.EIO`. -/
def catchSysErrno {m : Type → Type} [Monad m] {α : Type}
    (conc : Core.ConcOpsM m) (act : m (Except Errno α)) : m (Except Errno α) := do
  match ← conc.tryCatchMsg act with
  | .ok res => return res
  | .error _ => return .error Errno.EIO

/-- Execute `act : m (Except PostForkError α)` via `conc.tryCatchMsg`, mapping runtime exceptions to `.sysError`. -/
def catchSysPf {m : Type → Type} [Monad m] {α : Type}
    (conc : Core.ConcOpsM m) (act : m (Except PostFork.PostForkError α)) :
    m (Except PostFork.PostForkError α) := do
  match ← conc.tryCatchMsg act with
  | .ok res => return res
  | .error msg =>
    return .error
      { kind := .sysError
        errno := some Errno.EIO
        message := if msg.isEmpty then "postfork error" else msg }

/-- Execute `act : m (Option α)` via `conc.tryCatchMsg`, mapping runtime exceptions to `none`. -/
def catchSysOpt {m : Type → Type} [Monad m] {α : Type}
    (conc : Core.ConcOpsM m) (act : m (Option α)) : m (Option α) := do
  match ← conc.tryCatchMsg act with
  | .ok res => return res
  | .error _ => return none

/-- Wrap `FilesOpsM m fd` with `catchSysErrno conc`. -/
def mkSafeFilesOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (files : Files.FilesOpsM m fd) : Files.FilesOpsM m fd where
  openat d p fl md := catchSysErrno conc (files.openat d p fl md)
  openat2 d p how := catchSysErrno conc (files.openat2 d p how)
  close h := catchSysErrno conc (files.close h)
  read h n := catchSysErrno conc (files.read h n)
  write h bs := catchSysErrno conc (files.write h bs)
  fstat h := catchSysErrno conc (files.fstat h)
  fstatat d p fl := catchSysErrno conc (files.fstatat d p fl)
  faccessat d p mk fl := catchSysErrno conc (files.faccessat d p mk fl)
  mkdirat d p md := catchSysErrno conc (files.mkdirat d p md)
  unlinkat d p rm := catchSysErrno conc (files.unlinkat d p rm)
  renameat2 od op nd np fl := catchSysErrno conc (files.renameat2 od op nd np fl)
  symlinkat t d lp := catchSysErrno conc (files.symlinkat t d lp)
  readlinkat d p c := catchSysErrno conc (files.readlinkat d p c)
  getdents64 h c := catchSysErrno conc (files.getdents64 h c)
  fchmodat d p md := catchSysErrno conc (files.fchmodat d p md)
  fchmod h md := catchSysErrno conc (files.fchmod h md)
  flock h op := catchSysErrno conc (files.flock h op)
  fcntl h cmd := catchSysErrno conc (files.fcntl h cmd)
  fsync h := catchSysErrno conc (files.fsync h)
  getcwd c := catchSysErrno conc (files.getcwd c)
  lseek h off wh := catchSysErrno conc (files.lseek h off wh)
  reopenReadOnly h := catchSysErrno conc (files.reopenReadOnly h)
  dupStdio sl := catchSysErrno conc (files.dupStdio sl)

/-- Wrap `NetOpsM m fd` with `catchSysErrno conc`. -/
def mkSafeNetOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (net : Net.NetOpsM m fd) : Net.NetOpsM m fd where
  socket dom st fl p := catchSysErrno conc (net.socket dom st fl p)
  socketpair dom st fl := catchSysErrno conc (net.socketpair dom st fl)
  bind h sa := catchSysErrno conc (net.bind h sa)
  listen h bl := catchSysErrno conc (net.listen h bl)
  accept4 h fl := catchSysErrno conc (net.accept4 h fl)
  connect h sa := catchSysErrno conc (net.connect h sa)
  getsockopt h opt := catchSysErrno conc (net.getsockopt h opt)
  setsockopt h opt v := catchSysErrno conc (net.setsockopt h opt v)
  getsockname h := catchSysErrno conc (net.getsockname h)
  recvfrom h n fl := catchSysErrno conc (net.recvfrom h n fl)
  sendto h bs fl := catchSysErrno conc (net.sendto h bs fl)
  shutdown h how := catchSysErrno conc (net.shutdown h how)
  sendmsg h ds := catchSysErrno conc (net.sendmsg h ds)
  recvmsg h mf := catchSysErrno conc (net.recvmsg h mf)
  ioctl h op ifn := catchSysErrno conc (net.ioctl h op ifn)

/-- Wrap `PollOpsM m fd` with `catchSysErrno conc`. -/
def mkSafePollOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (poll : Poll.PollOpsM m fd) : Poll.PollOpsM m fd where
  ppoll es to? := catchSysErrno conc (poll.ppoll es to?)
  eventfd2 iv fl := catchSysErrno conc (poll.eventfd2 iv fl)

/-- Wrap `ProcessOpsM m fd` with `catchSysErrno conc`. -/
def mkSafeProcOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (proc : LinuxSyscall.Process.ProcessOpsM m fd) :
    LinuxSyscall.Process.ProcessOpsM m fd where
  pipe2 fl := catchSysErrno conc (proc.pipe2 fl)
  waitpid pid fl := catchSysErrno conc (proc.waitpid pid fl)
  kill pid sig := catchSysErrno conc (proc.kill pid sig)
  pidfd_open pid fl := catchSysErrno conc (proc.pidfd_open pid fl)
  pidfd_send_signal h sig fl := catchSysErrno conc (proc.pidfd_send_signal h sig fl)
  getpid := catchSysErrno conc proc.getpid
  getuid := catchSysErrno conc proc.getuid

/-- Wrap `SandboxOpsM m fd` with `catchSysErrno conc`. -/
def mkSafeSandboxOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (sb : Sandbox.SandboxOpsM m fd) : Sandbox.SandboxOpsM m fd where
  landlockCreateRuleset a fl := catchSysErrno conc (sb.landlockCreateRuleset a fl)
  landlockAddRule rs rl := catchSysErrno conc (sb.landlockAddRule rs rl)
  landlockRestrictSelf rs := catchSysErrno conc (sb.landlockRestrictSelf rs)
  seccomp op fl bs := catchSysErrno conc (sb.seccomp op fl bs)
  prctl op := catchSysErrno conc (sb.prctl op)
  setrlimit r cur mx := catchSysErrno conc (sb.setrlimit r cur mx)
  memfdCreate nm fl := catchSysErrno conc (sb.memfdCreate nm fl)

/-- Wrap `TimeRandOpsM m` with `catchSysErrno conc`. -/
def mkSafeTimeRandOps {m : Type → Type} [Monad m]
    (conc : Core.ConcOpsM m) (tr : TimeRand.TimeRandOpsM m) : TimeRand.TimeRandOpsM m where
  clock_gettime clk := catchSysErrno conc (tr.clock_gettime clk)
  clock_nanosleep clk ab ts := catchSysErrno conc (tr.clock_nanosleep clk ab ts)
  getrandom n fl := catchSysErrno conc (tr.getrandom n fl)

/-- Wrap `PasswdOpsM m` with `catchSysErrno conc`. -/
def mkSafePasswdOps {m : Type → Type} [Monad m]
    (conc : Core.ConcOpsM m) (pw : Passwd.PasswdOpsM m) : Passwd.PasswdOpsM m where
  getpwuid uid := catchSysErrno conc (pw.getpwuid uid)
  getpwnam nm := catchSysErrno conc (pw.getpwnam nm)

/-- Wrap `PostForkOpsM m fd` with `catchSysPf conc`. -/
def mkSafePostForkOps {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (pf : PostFork.PostForkOpsM m fd) : PostFork.PostForkOpsM m fd where
  spawn sp := catchSysPf conc (pf.spawn sp)
  spawnWithBarrier sp := catchSysPf conc (pf.spawnWithBarrier sp)
  releaseBarrier p := catchSysPf conc (pf.releaseBarrier p)
  abortBarrier p := catchSysPf conc (pf.abortBarrier p)

/-- Build `HostSysDepsM` over `Model.FullSysOpsM m` and `Core.ConcOpsM m` for platform `(isLinux, target)`. -/
def mkSafeSysDepsM {m : Type → Type} [Monad m]
    (sys : Model.FullSysOpsM m) (conc : Core.ConcOpsM m)
    (isLinux : Bool) (target : String) :
    HostSysDepsM m RawFd (ConcForwarderHandle RawFd conc.Ref conc.TaskHandle) :=
  let sFiles := mkSafeFilesOps conc sys.files
  let sNet := mkSafeNetOps conc sys.net
  let sPoll := mkSafePollOps conc sys.poll
  { files := sFiles
    net := sNet
    poll := sPoll
    proc := mkSafeProcOps conc sys.proc
    sandbox := mkSafeSandboxOps conc sys.sandbox
    timeRand := mkSafeTimeRandOps conc sys.timeRand
    passwd := mkSafePasswdOps conc sys.passwd
    postFork := mkSafePostForkOps conc sys.postFork
    isLinux := isLinux
    target := target
    getEnvPath := catchSysOpt conc do
      match ← sys.envVars.getEnv "PATH" with
      | .ok (some s) => return some s.toUTF8
      | _ => return none
    getEnvHome := catchSysOpt conc do
      match ← sys.envVars.getEnv "HOME" with
      | .ok v? => return v?
      | .error _ => return none
    startFwdTask := fun lfds hports =>
      catchSysErrno conc (Forwarder.startForwarderM sFiles sNet sPoll conc lfds hports)
    stopFwdTask := fun h => do
      let _ ← conc.tryCatchMsg (Forwarder.stopForwarderM sFiles sNet conc h)
      pure () }

/-- Construct `RawProcessSandboxOpsM m` over `FullSysOpsM m`, `ConcOpsM m`, `StateCellM m`, and explicit platform identity `(isLinux, target)`. -/
def mkFullOpsWithPlatformM {m : Type → Type} [Monad m]
    (isLinux : Bool) (target : String)
    (sys : Model.FullSysOpsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (HostCellState conc.Ref conc.TaskHandle)) :
    RawProcessSandboxOpsM m :=
  mkRawOpsM (mkSafeSysDepsM sys conc isLinux target) (mkCellTableOps cell)

/-- Construct `RawProcessSandboxOpsM m` over `FullSysOpsM m`, `ConcOpsM m`, and `StateCellM m` on the native host platform. -/
def mkFullOpsM {m : Type → Type} [Monad m] [MonadFinally m]
    (sys : Model.FullSysOpsM m) (conc : Core.ConcOpsM m)
    (cell : Core.StateCellM m (HostCellState conc.Ref conc.TaskHandle)) :
    RawProcessSandboxOpsM m :=
  mkFullOpsWithPlatformM Model.hostPlatformIsLinux Model.hostPlatformTarget sys conc cell

end LeanSwe.ProcessSandbox.Raw.SysBridge.Driver

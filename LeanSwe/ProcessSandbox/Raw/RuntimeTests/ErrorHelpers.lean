import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Model.InitStatus

namespace LeanSwe.ProcessSandbox.Raw.RuntimeTests.ErrorHelpers

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model

/-- Assert that `res` failed with the exact `expected` `SandboxErrorKind` and a non-empty message. -/
def assertErrKind {α : Type} (res : Except SandboxError α) (expected : SandboxErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

/-- Minimal valid `CompiledSandboxPlan` and 1-instruction `seccomp` BPF payload for error-path probes. -/
def samplePlan : CompiledSandboxPlan :=
  { program := "/bin/true" }

/-- Minimal valid 8-byte `SECCOMP_RET_ALLOW` BPF instruction payload. -/
def sampleSeccomp : ByteArray :=
  ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]

/-- Forged zero `BoxHandle` rejected by handle validation. -/
def forgedBox : BoxHandle :=
  { handleId := 0, pid := 1, pgid := 1, pidfd := 0 }

/-- Forged zero `PortForwarderHandle` rejected by handle validation. -/
def forgedFwd : PortForwarderHandle :=
  { handleId := 0, boxHandleId := 0 }

/-- Active `PlanHandle` matching `seededPlanTable`. -/
def activePlan : PlanHandle :=
  { handleId := 1 }

/-- Active `BoxHandle` matching `seededBoxTable`. -/
def activeBox : BoxHandle :=
  { handleId := 1, pid := 42, pgid := 42, pidfd := 0 }

/-- Active `PortForwarderHandle` matching `seededFwdTable`. -/
def activeFwd : PortForwarderHandle :=
  { handleId := 1, boxHandleId := 1 }

/-- Default `FilesOpsM IO Nat` returning `ENOSYS` for mock fault-injection probes. -/
def baseFilesOps : Files.FilesOpsM IO Nat where
  openat _ _ _ _ := pure (.error Errno.ENOSYS)
  openat2 _ _ _ := pure (.error Errno.ENOSYS)
  close _ := pure (.ok ())
  read _ _ := pure (.ok ByteArray.empty)
  write _ bs := pure (.ok (UInt32.ofNat bs.size))
  fstat _ := pure (.error Errno.ENOSYS)
  fstatat _ _ _ := pure (.error Errno.ENOENT)
  faccessat _ _ _ _ := pure (.error Errno.ENOENT)
  mkdirat _ _ _ := pure (.error Errno.ENOSYS)
  unlinkat _ _ _ := pure (.ok ())
  renameat2 _ _ _ _ _ := pure (.error Errno.ENOSYS)
  symlinkat _ _ _ := pure (.error Errno.ENOSYS)
  readlinkat _ _ _ := pure (.error Errno.ENOSYS)
  getdents64 _ _ := pure (.error Errno.ENOSYS)
  fchmodat _ _ _ := pure (.error Errno.ENOSYS)
  fchmod _ _ := pure (.error Errno.ENOSYS)
  flock _ _ := pure (.error Errno.ENOSYS)
  fcntl _ _ := pure (.ok 0)
  fsync _ := pure (.ok ())
  getcwd _ := pure (.error Errno.ENOSYS)
  lseek _ _ _ := pure (.error Errno.ENOSYS)
  reopenReadOnly fd := pure (.ok fd)
  dupStdio _ := pure (.error Errno.ENOSYS)

/-- Default `NetOpsM IO Nat` returning `ENOSYS` for mock fault-injection probes. -/
def baseNetOps : Net.NetOpsM IO Nat where
  socket _ _ _ _ := pure (.error Errno.ENOSYS)
  socketpair _ _ _ := pure (.error Errno.ENOSYS)
  bind _ _ := pure (.error Errno.ENOSYS)
  listen _ _ := pure (.error Errno.ENOSYS)
  accept4 _ _ := pure (.error Errno.ENOSYS)
  connect _ _ := pure (.error Errno.ENOSYS)
  getsockopt _ _ := pure (.error Errno.ENOSYS)
  setsockopt _ _ _ := pure (.error Errno.ENOSYS)
  getsockname _ := pure (.error Errno.ENOSYS)
  recvfrom _ _ _ := pure (.error Errno.ENOSYS)
  sendto _ _ _ := pure (.error Errno.ENOSYS)
  shutdown _ _ := pure (.error Errno.ENOSYS)
  sendmsg _ _ := pure (.error Errno.ENOSYS)
  recvmsg _ _ := pure (.error Errno.ENOSYS)
  ioctl _ _ _ := pure (.error Errno.ENOSYS)

/-- Default `PollOpsM IO Nat` for mock fault-injection probes. -/
def basePollOps : Poll.PollOpsM IO Nat where
  ppoll entries _ := pure (.ok (entries.map fun _ => ({ pollin := true } : Poll.PollEvents)))
  eventfd2 _ _ := pure (.error Errno.ENOSYS)

/-- Default `ProcessOpsM IO Nat` for mock fault-injection probes. -/
def baseProcOps : LinuxSyscall.Process.ProcessOpsM IO Nat where
  pipe2 _ := pure (.error Errno.EMFILE)
  waitpid _ _ := pure (.error Errno.ECHILD)
  kill _ _ := pure (.ok ())
  pidfd_open _ _ := pure (.error Errno.ENOSYS)
  pidfd_send_signal _ _ _ := pure (.ok ())
  getpid := pure (.ok 42)
  getuid := pure (.ok 1000)

/-- Default `SandboxOpsM IO Nat` returning `ENOMEM` on `memfdCreate` for mock fault-injection probes. -/
def baseSandboxOps : Sandbox.SandboxOpsM IO Nat where
  landlockCreateRuleset _ _ := pure (.error Errno.ENOSYS)
  landlockAddRule _ _ := pure (.error Errno.ENOSYS)
  landlockRestrictSelf _ := pure (.error Errno.ENOSYS)
  seccomp _ _ _ := pure (.error Errno.ENOSYS)
  prctl _ := pure (.error Errno.ENOSYS)
  setrlimit _ _ _ := pure (.error Errno.ENOSYS)
  memfdCreate _ _ := pure (.error Errno.ENOMEM)

/-- Default `TimeRandOpsM IO` for mock fault-injection probes. -/
def baseTimeRandOps : TimeRand.TimeRandOpsM IO where
  clock_gettime _ := pure (.ok { sec := 1, nsec := 0 })
  clock_nanosleep _ _ _ := pure (.ok ())
  getrandom _ _ := pure (.error Errno.ENOSYS)

/-- Default `PasswdOpsM IO` for mock fault-injection probes. -/
def basePasswdOps : Passwd.PasswdOpsM IO where
  getpwuid _ := pure (.ok none)
  getpwnam _ := pure (.ok none)

/-- Default `PostForkOpsM IO Nat` for mock fault-injection probes. -/
def basePostForkOps : PostFork.PostForkOpsM IO Nat where
  spawn _ := pure (.error { kind := .sysError, message := "mock spawn" })
  spawnWithBarrier _ := pure (.error { kind := .sysError, message := "mock spawnWithBarrier" })
  releaseBarrier _ := pure (.error { kind := .sysError, message := "mock releaseBarrier" })
  abortBarrier _ := pure (.error { kind := .sysError, message := "mock abortBarrier" })

/-- Construct a baseline `Model.RawHostCapM IO` backed by `tblRef`. -/
def mkBaseCap (tblRef : IO.Ref Model.RawTableState) : Model.RawHostCapM IO where
  files := baseFilesOps
  net := baseNetOps
  poll := basePollOps
  proc := baseProcOps
  sandbox := baseSandboxOps
  timeRand := baseTimeRandOps
  passwd := basePasswdOps
  postFork := basePostForkOps
  isLinux := true
  target := "x86_64-unknown-linux-gnu"
  getEnvPath := pure (some "/usr/bin".toUTF8)
  getEnvHome := pure none
  startFwdTask _ _ := pure (.error Errno.EMFILE)
  stopFwdTask _ := pure ()
  getTable := tblRef.get
  modifyTable f := tblRef.modifyGet fun st => (st, f st)

/-- Seed `RawTableState` with an active plan (`handleId = 1`) carrying `mounts`. -/
def seededPlanTable (mounts : Array SandboxMount := #[.scratch "/tmp"]) : Model.RawTableState :=
  { nextId := 2
    plans := [(1, { plan := { samplePlan with userMounts := mounts }, planMemfd := 10, initMemfd := 11, hostsMemfd := 12 })] }

/-- Seed `RawTableState` with an active box (`handleId = 1`) carrying optional status FD, listener FDs, and cgroup dir. -/
def seededBoxTable (statusFd? : Option Nat := none) (listeners : Array Nat := #[])
    (cgDir : String := "") : Model.RawTableState :=
  { nextId := 2
    boxes := [(1, {
      pid := 42, pgid := 42, pidfd := 20,
      stdinFd? := none, stdoutFd? := none, stderrFd? := none,
      statusFd? := statusFd?, goFd? := none,
      listenerFds := listeners, cgroupDir := cgDir,
      program := "/bin/true", cwd := "/tmp" })] }

/-- Seed `RawTableState` with an active forwarder (`handleId = 1`, `boxHandleId = 1`). -/
def seededFwdTable : Model.RawTableState :=
  { nextId := 2
    fwds := [(1, { boxHandleId := 1, taskHandle := 30 })] }

/-- Build a capability bundle with `isLinux := false` for non-Linux fail-closed probes. -/
def capNonLinux : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef ({} : Model.RawTableState)
  return { mkBaseCap tbl with isLinux := false }

/-- Build a baseline capability bundle seeded with `tblState`. -/
def capWithTable (tblState : Model.RawTableState := {}) : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef tblState
  return mkBaseCap tbl

/-- Build a `spawnBox` mount-precheck capability returning `errCode` from `files.fstatat`. -/
def capSpawnMountErrno (errCode : Errno) : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef (seededPlanTable #[.readOnly "/mock/missing" "/mnt"])
  return { mkBaseCap tbl with files := { baseFilesOps with fstatat := fun _ _ _ => pure (.error errCode) } }

/-- Build a `spawnBox` capability resolving `bwrap` and failing `pipe2` with `EMFILE`. -/
def capSpawnPipeIoError : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef seededPlanTable
  let regStat : Files.StatInfo := {
    kind := .reg, size := 1, mode := 0o755, ino := 1, dev := 1, nlink := 1,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }
  return { mkBaseCap tbl with
    files := { baseFilesOps with
      fstatat := fun _ _ _ => pure (.ok regStat)
      faccessat := fun _ _ _ _ => pure (.ok ()) } }

/-- Build a `readBoxOutput` status-frame capability returning `msg` over `statusFd`. -/
def capReadStatusFrame (msg : InitStatusMsg) : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef (seededBoxTable (some 5))
  let frame := encodeInitStatusMsg msg
  return { mkBaseCap tbl with files := { baseFilesOps with read := fun _ _ => pure (.ok frame) } }

/-- Build a `readBoxOutput` capability failing `clock_gettime` with `EINVAL`. -/
def capReadClockEinval : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef (seededBoxTable (some 5))
  return { mkBaseCap tbl with timeRand := { baseTimeRandOps with clock_gettime := fun _ => pure (.error Errno.EINVAL) } }

/-- Build a `killProcessGroup` capability returning `EPERM` from `proc.kill`. -/
def capKillPgEperm : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef seededBoxTable
  return { mkBaseCap tbl with proc := { baseProcOps with kill := fun _ _ => pure (.error Errno.EPERM) } }

/-- Build a `pidfdKill` capability returning `EPERM` from `proc.pidfd_send_signal`. -/
def capPidfdKillEperm : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef seededBoxTable
  return { mkBaseCap tbl with proc := { baseProcOps with pidfd_send_signal := fun _ _ _ => pure (.error Errno.EPERM) } }

/-- Build a `reapBox` capability returning `EACCES` from `files.unlinkat`. -/
def capReapUnlinkEacces : IO (Model.RawHostCapM IO) := do
  let tbl ← IO.mkRef (seededBoxTable none #[] "/sys/fs/cgroup/mock-box")
  return { mkBaseCap tbl with files := { baseFilesOps with unlinkat := fun _ _ _ => pure (.error Errno.EACCES) } }

end LeanSwe.ProcessSandbox.Raw.RuntimeTests.ErrorHelpers

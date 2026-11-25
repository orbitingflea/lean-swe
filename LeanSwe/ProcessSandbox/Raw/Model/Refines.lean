import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.PostFork.Types
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Model

namespace LeanSwe.ProcessSandbox.Raw.Model

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

/-- Decode a raw Linux `AUDIT_ARCH_*` constant (`0xc000003e` or `0xc00000b7`) into `SeccompArch`, failing closed with `.unavailable`. -/
def decodeHostAuditArch (raw : UInt32) : Except SandboxError SeccompArch :=
  match LeanSwe.ProcessSandbox.Model.seccompArchOfAudit? raw with
  | some arch => .ok arch
  | none => .error (Model.Internal.mapRawError (.unavailable none "unsupported host architecture for seccomp"))

/-- Pure host platform detection mapping `(isLinux, targetTriple)` to its Linux `AUDIT_ARCH_*` word (`0` if unsupported). -/
def detectHostAuditArch (isLinux : Bool) (target : String) : UInt32 :=
  let cs := target.toList
  if !isLinux then 0
  else if "x86_64-".toList.isPrefixOf cs then 0xc000003e
  else if "aarch64-".toList.isPrefixOf cs then 0xc00000b7
  else 0

/-- Pure check that a `CompiledSandboxPlan` satisfies all mandatory hardening, non-empty path, positive limit, and non-zero port invariants. -/
def planMandatoryInvariantsOk (plan : CompiledSandboxPlan) : Bool :=
  plan.emptyRoot && plan.unshareAllNamespaces && plan.mountFreshProc && plan.mountSafeDev &&
  plan.directCgroupV2Fs && plan.landlockMinAbi ≥ 4 && plan.blockUnixSocketAndSmc &&
  plan.allowAnonUnixSocketpair && plan.clone3EnosysFallback && plan.seccompStrictDenylist &&
  plan.noNewPrivs && plan.rlimitCoreZero && plan.subreaperAndPdeathsig && plan.cleanEnv &&
  !plan.program.isEmpty && !plan.cwd.isEmpty &&
  plan.limits.timeoutMs != 0 && plan.limits.memoryMaxBytes != some 0 && plan.limits.pidsMax != some 0 &&
  !(plan.portForwards.any fun pf => pf.boxPort == 0 || pf.hostPort == 0)

/-- Pure check that compiled `seccomp` filter bytes contain `1..SECCOMP_MAX_INSNS` 8-byte instructions. -/
def seccompFilterBytesValid (seccompBytes : ByteArray) : Bool :=
  seccompBytes.size != 0 && seccompBytes.size % 8 == 0 && seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS

/-- Pure check that string `s` is NUL-free and fits within a 32-bit UTF-8 byte length prefix. -/
def wireStringValid (s : String) : Bool :=
  !(s.toUTF8.data.toList.contains 0) && s.toUTF8.size < UInt32.size

/-- Pure check that every string carried by `plan` is valid for `LSWP0002` serialization. -/
def planStringsValid (plan : CompiledSandboxPlan) : Bool :=
  wireStringValid plan.program &&
  wireStringValid plan.cwd &&
  plan.args.toList.all wireStringValid &&
  plan.env.toList.all (fun kv => wireStringValid kv.1 && wireStringValid kv.2) &&
  plan.presetSystemEntries.toList.all (fun
    | .readOnlyDir p => wireStringValid p
    | .topSymlink lp tgt => wireStringValid lp && wireStringValid tgt) &&
  plan.presetEtcPaths.toList.all wireStringValid &&
  plan.maskedPresetPaths.toList.all wireStringValid &&
  plan.userMounts.toList.all (fun
    | .readOnly hp bp => wireStringValid hp && wireStringValid bp
    | .readWrite hp bp => wireStringValid hp && wireStringValid bp
    | .scratch bp => wireStringValid bp)

/-- Declarative specification for `encodePlan`: validates mandatory plan/filter invariants and frames `.ok` outputs with `LSWP0002` header and little-endian `u32` instruction count plus trailing `seccompBytes`. -/
def allowedEncodePlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray)
    (out : Except SandboxError ByteArray) : Prop :=
  match out with
  | .ok wire =>
    let nInsns := seccompBytes.size / 8
    let countOff := wire.size - (4 + seccompBytes.size)
    planMandatoryInvariantsOk plan = true ∧
    seccompFilterBytesValid seccompBytes = true ∧
    planStringsValid plan = true ∧
    wire.size ≥ 12 + seccompBytes.size ∧
    wire[0]! = 0x4c ∧ wire[1]! = 0x53 ∧ wire[2]! = 0x57 ∧ wire[3]! = 0x50 ∧
    wire[4]! = 0x30 ∧ wire[5]! = 0x30 ∧ wire[6]! = 0x30 ∧ wire[7]! = 0x32 ∧
    wire[countOff]! = UInt8.ofNat (nInsns % 256) ∧
    wire[countOff + 1]! = UInt8.ofNat ((nInsns / 256) % 256) ∧
    wire[countOff + 2]! = UInt8.ofNat ((nInsns / 65536) % 256) ∧
    wire[countOff + 3]! = UInt8.ofNat ((nInsns / 16777216) % 256) ∧
    (∀ i, i < seccompBytes.size → wire[wire.size - seccompBytes.size + i]! = seccompBytes[i]!)
  | .error err =>
    err.kind = .invalidInput ∧ err.message ≠ "" ∧
      (planMandatoryInvariantsOk plan = false ∨
       seccompFilterBytesValid seccompBytes = false ∨
       planStringsValid plan = false)

/-- Top-level host system roots inspected for immutable OS runtime preset discovery. -/
def presetSystemRoots : Array String :=
  #["/usr", "/bin", "/sbin", "/lib", "/lib64"]

/-- Allowlisted safe `/etc` host entries mirrored read-only into the sandbox when present. -/
def presetEtcAllowlist : Array String :=
  #[
    "/etc/ld.so.cache",
    "/etc/passwd",
    "/etc/group",
    "/etc/nsswitch.conf",
    "/etc/localtime",
    "/etc/os-release",
    "/etc/alternatives",
    "/etc/ssl/certs",
    "/etc/ssl/openssl.cnf"
  ]

/-- Return `true` iff `p` is strictly nested beneath one of `/usr/`, `/bin/`, `/sbin/`, `/lib/`, or `/lib64/`. -/
def isUnderSystemRoot (p : String) : Bool :=
  let cs := p.toList
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any fun pre =>
    let pcs := pre.toList
    pcs.isPrefixOf cs && cs.length > pcs.length

/-- Model record for a sealed plan slot using abstract `Nat` descriptor identifiers. -/
structure RawPlanRecord where
  /-- Validated structured sandbox plan. -/
  plan : CompiledSandboxPlan
  /-- Sealed `memfd` identifier for the `LSWP0002` wire payload. -/
  planMemfd : Nat
  /-- Sealed `memfd` identifier for the embedded init binary. -/
  initMemfd : Nat
  /-- Sealed `memfd` identifier for synthetic `/etc/hosts`. -/
  hostsMemfd : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Model record for an active spawned box slot using abstract `Nat` descriptor identifiers. -/
structure RawBoxRecord where
  /-- Host-visible `bwrap` PID (`1 ≤ pid ≤ MAX_LINUX_PID`). -/
  pid : UInt32
  /-- Dedicated host process group ID (`pgid = pid`). -/
  pgid : UInt32
  /-- Race-free `pidfd` descriptor identifier. -/
  pidfd : Nat
  /-- Optional parent write end of guest `stdin` pipe. -/
  stdinFd? : Option Nat
  /-- Optional parent read end of guest `stdout` pipe. -/
  stdoutFd? : Option Nat
  /-- Optional parent read end of guest `stderr` pipe. -/
  stderrFd? : Option Nat
  /-- Optional parent read end of init `status_pipe`. -/
  statusFd? : Option Nat
  /-- Optional parent write end of init `go_pipe`. -/
  goFd? : Option Nat
  /-- Whether `readBoxOutput` has claimed this box's streaming pipes. -/
  readStarted : Bool := false
  /-- Whether `startPortForwarders` has claimed `listenerFds`. -/
  fwdsTaken : Bool := false
  /-- Handed-off in-box listener descriptor identifiers. -/
  listenerFds : Array Nat := #[]
  /-- Per-box direct `/sys/fs/cgroup/...` directory path. -/
  cgroupDir : String
  /-- Guest executable path for `execvp` diagnostics. -/
  program : String
  /-- Guest working directory for `chdir` diagnostics. -/
  cwd : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Model record for a running host-side port forwarder handle. -/
structure RawFwdRecord where
  /-- Associated `BoxHandle.handleId`. -/
  boxHandleId : Nat
  /-- Abstract forwarder task handle identifier. -/
  taskHandle : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure abstract host handle-table state for `LeanSwe.ProcessSandbox.Raw` refinement proofs. -/
structure RawTableState where
  /-- Next monotonically increasing 64-bit handle ID (`≥ 1`). -/
  nextId : Nat := 1
  /-- Monotonic per-box cgroup directory sequence counter (`≥ 1`). -/
  cgSeq : Nat := 1
  /-- Active sealed plan slots keyed by `handleId`. -/
  plans : List (Nat × RawPlanRecord) := []
  /-- Active unreaped box slots keyed by `handleId`. -/
  boxes : List (Nat × RawBoxRecord) := []
  /-- Active running forwarder slots keyed by `handleId`. -/
  fwds : List (Nat × RawFwdRecord) := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Snapshot of active `(openPlans, activeBoxes, activeForwarders)` counts from `RawTableState`. -/
def tableCounts (t : RawTableState) : SandboxResourceCounts :=
  { openPlans := t.plans.length
    activeBoxes := t.boxes.length
    activeForwarders := t.fwds.length }

/-- Return `true` iff `hid` occurs as a key in association list `xs`. -/
def tableHasKey {α : Type} (hid : Nat) (xs : List (Nat × α)) : Bool :=
  xs.any fun p => p.1 == hid

/-- Public abstract host world state pairing platform identity with `RawTableState`. -/
structure RawHostWorld where
  /-- Whether the host OS is Linux. -/
  isLinux : Bool := true
  /-- Compiler target triple (e.g. `x86_64-unknown-linux-gnu`). -/
  target : String := "x86_64-unknown-linux-gnu"
  /-- Abstract host handle-table state. -/
  table : RawTableState := {}
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Well-formedness invariant on `RawHostWorld`: `nextId > 0` and every live handle ID is a valid positive 64-bit ID. -/
def rawHostWorldWf (w : RawHostWorld) : Bool :=
  decide (0 < w.table.nextId) &&
  w.table.plans.all (fun p => isValidSandboxHandleId p.1) &&
  w.table.boxes.all (fun b => isValidSandboxHandleId b.1) &&
  w.table.fwds.all (fun f => isValidSandboxHandleId f.1)

/-- Public capability bundle supplying `LinuxSyscall.*`, `PostFork`, environment probes, forwarder hooks, and table state access for `ProcessSandbox.Raw`. -/
structure RawHostCapM (m : Type → Type) where
  /-- Curated Linux file/descriptor syscalls. -/
  files : Files.FilesOpsM m Nat
  /-- Curated Linux socket syscalls. -/
  net : Net.NetOpsM m Nat
  /-- Curated Linux `ppoll` syscall. -/
  poll : Poll.PollOpsM m Nat
  /-- Curated Linux process syscalls. -/
  proc : LinuxSyscall.Process.ProcessOpsM m Nat
  /-- Curated Linux sandbox syscalls. -/
  sandbox : Sandbox.SandboxOpsM m Nat
  /-- Curated Linux monotonic clock and nanosleep syscalls. -/
  timeRand : TimeRand.TimeRandOpsM m
  /-- Curated Linux `getpwuid` syscall. -/
  passwd : Passwd.PasswdOpsM m
  /-- Verified post-`fork` child setup and sync-barrier bundle. -/
  postFork : PostFork.PostForkOpsM m Nat
  /-- Whether the host OS is Linux. -/
  isLinux : Bool
  /-- Compiler target triple. -/
  target : String
  /-- Read raw `PATH` environment bytes. -/
  getEnvPath : m (Option ByteArray)
  /-- Read `HOME` environment string. -/
  getEnvHome : m (Option String)
  /-- Start a host-side port forwarder for handed-off listeners and target host ports. -/
  startFwdTask : Array Nat → Array UInt16 → m (Except Errno Nat)
  /-- Stop a running forwarder task handle. -/
  stopFwdTask : Nat → m Unit
  /-- Read the current `RawTableState`. -/
  getTable : m RawTableState
  /-- Atomically apply `f` to `RawTableState` and return the prior snapshot. -/
  modifyTable : (RawTableState → RawTableState) → m RawTableState

/-- Single-step request algebra over `RawHostCapM`. -/
inductive RawCapStepReq where
  /-- Read host platform `(isLinux, target)` identity. -/
  | metaInfo
  /-- Read current handle-table state. -/
  | getTable
  /-- Atomically transform handle-table state via `f` and return the prior snapshot. -/
  | modifyTable (f : RawTableState → RawTableState)
  /-- Invoke `files.openat`. -/
  | filesOpenat (dir : Option Nat) (path : ByteArray) (flags : Files.OpenFlags) (mode : Mode)
  /-- Invoke `files.close`. -/
  | filesClose (fd : Nat)
  /-- Invoke `files.read`. -/
  | filesRead (fd : Nat) (maxBytes : UInt32)
  /-- Invoke `files.write`. -/
  | filesWrite (fd : Nat) (data : ByteArray)
  /-- Invoke `files.fstatat`. -/
  | filesFstatat (dir : Option Nat) (path : ByteArray) (flags : Files.AtFlags)
  /-- Invoke `files.faccessat`. -/
  | filesFaccessat (dir : Option Nat) (path : ByteArray) (mask : Files.AccessModeMask) (flags : Files.AtFlags)
  /-- Invoke `files.mkdirat`. -/
  | filesMkdirat (dir : Option Nat) (path : ByteArray) (mode : Mode)
  /-- Invoke `files.unlinkat`. -/
  | filesUnlinkat (dir : Option Nat) (path : ByteArray) (removeDir : Bool)
  /-- Invoke `files.readlinkat`. -/
  | filesReadlinkat (dir : Option Nat) (path : ByteArray) (cap : UInt32)
  /-- Invoke `files.fcntl`. -/
  | filesFcntl (fd : Nat) (cmd : Files.FcntlCmd)
  /-- Invoke `files.reopenReadOnly`. -/
  | filesReopenReadOnly (fd : Nat)
  /-- Invoke `net.socketpair`. -/
  | netSocketpair (dom : Net.SockDomain) (st : Net.SockType) (flags : Net.SockFlags)
  /-- Invoke `net.recvmsg`. -/
  | netRecvmsg (fd : Nat) (maxFds : UInt32)
  /-- Invoke `poll.ppoll`. -/
  | pollPpoll (fds : Array (Nat × Poll.PollEvents)) (timeout : Option Poll.Timespec)
  /-- Invoke `proc.pipe2`. -/
  | procPipe2 (flags : LinuxSyscall.Process.PipeFlags)
  /-- Invoke `proc.waitpid`. -/
  | procWaitpid (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags)
  /-- Invoke `proc.kill`. -/
  | procKill (target : Int32) (sig : LinuxSyscall.Process.Signal)
  /-- Invoke `proc.pidfd_open`. -/
  | procPidfdOpen (pid : UInt32) (flags : LinuxSyscall.Process.PidfdOpenFlags)
  /-- Invoke `proc.pidfd_send_signal`. -/
  | procPidfdSendSignal (pidfd : Nat) (sig : LinuxSyscall.Process.Signal) (flags : LinuxSyscall.Process.PidfdSignalFlags)
  /-- Invoke `proc.getpid`. -/
  | procGetpid
  /-- Invoke `proc.getuid`. -/
  | procGetuid
  /-- Invoke `sandbox.landlockCreateRuleset`. -/
  | sandboxLandlockCreateRuleset (attr? : Option Sandbox.LandlockRulesetAttr) (flags : UInt32)
  /-- Invoke `sandbox.seccomp`. -/
  | sandboxSeccomp (op : Sandbox.SeccompOp) (flags : Sandbox.SeccompFlags) (filterBytes : ByteArray)
  /-- Invoke `sandbox.memfdCreate`. -/
  | sandboxMemfdCreate (name : ByteArray) (flags : Sandbox.MemfdFlags)
  /-- Invoke `timeRand.clock_gettime`. -/
  | timeRandClockGettime (clk : TimeRand.ClockId)
  /-- Invoke `timeRand.clock_nanosleep`. -/
  | timeRandClockNanosleep (clk : TimeRand.ClockId) (abstime : Bool) (req : TimeRand.Timespec)
  /-- Invoke `passwd.getpwuid`. -/
  | passwdGetpwuid (uid : UInt32)
  /-- Invoke `postFork.spawn`. -/
  | postForkSpawn (spec : PostFork.ChildSpecM Nat)
  /-- Invoke `postFork.spawnWithBarrier`. -/
  | postForkSpawnWithBarrier (spec : PostFork.ChildSpecM Nat)
  /-- Invoke `postFork.releaseBarrier`. -/
  | postForkReleaseBarrier (p : PostFork.PendingChildM Nat)
  /-- Invoke `postFork.abortBarrier`. -/
  | postForkAbortBarrier (p : PostFork.PendingChildM Nat)
  /-- Invoke `getEnvPath`. -/
  | getEnvPath
  /-- Invoke `getEnvHome`. -/
  | getEnvHome
  /-- Invoke `startFwdTask`. -/
  | startFwdTask (fds : Array Nat) (ports : Array UInt16)
  /-- Invoke `stopFwdTask`. -/
  | stopFwdTask (h : Nat)
  deriving Inhabited

/-- Single-step outcome algebra over `RawHostCapM`. -/
inductive RawCapStepOut where
  /-- Platform identity `(isLinux, target)`. -/
  | metaInfo (isLinux : Bool) (target : String)
  /-- Current handle-table snapshot. -/
  | table (t : RawTableState)
  /-- Completed table write or OS syscall step. -/
  | unit
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Execute one `RawCapStepReq` against `cap : RawHostCapM (StateM W)`. -/
def execRawCapStep {W : Type} (cap : RawHostCapM (StateM W)) : RawCapStepReq → StateM W RawCapStepOut
  | .metaInfo => pure (.metaInfo cap.isLinux cap.target)
  | .getTable => RawCapStepOut.table <$> cap.getTable
  | .modifyTable f => RawCapStepOut.table <$> cap.modifyTable f
  | .filesOpenat d p f m => cap.files.openat d p f m *> pure .unit
  | .filesClose fd => cap.files.close fd *> pure .unit
  | .filesRead fd n => cap.files.read fd n *> pure .unit
  | .filesWrite fd bs => cap.files.write fd bs *> pure .unit
  | .filesFstatat d p f => cap.files.fstatat d p f *> pure .unit
  | .filesFaccessat d p m f => cap.files.faccessat d p m f *> pure .unit
  | .filesMkdirat d p m => cap.files.mkdirat d p m *> pure .unit
  | .filesUnlinkat d p r => cap.files.unlinkat d p r *> pure .unit
  | .filesReadlinkat d p c => cap.files.readlinkat d p c *> pure .unit
  | .filesFcntl fd cmd => cap.files.fcntl fd cmd *> pure .unit
  | .filesReopenReadOnly fd => cap.files.reopenReadOnly fd *> pure .unit
  | .netSocketpair d s f => cap.net.socketpair d s f *> pure .unit
  | .netRecvmsg fd n => cap.net.recvmsg fd n *> pure .unit
  | .pollPpoll fds to => cap.poll.ppoll fds to *> pure .unit
  | .procPipe2 f => cap.proc.pipe2 f *> pure .unit
  | .procWaitpid pid f => cap.proc.waitpid pid f *> pure .unit
  | .procKill tgt sig => cap.proc.kill tgt sig *> pure .unit
  | .procPidfdOpen pid f => cap.proc.pidfd_open pid f *> pure .unit
  | .procPidfdSendSignal fd sig f => cap.proc.pidfd_send_signal fd sig f *> pure .unit
  | .procGetpid => cap.proc.getpid *> pure .unit
  | .procGetuid => cap.proc.getuid *> pure .unit
  | .sandboxLandlockCreateRuleset a f => cap.sandbox.landlockCreateRuleset a f *> pure .unit
  | .sandboxSeccomp op f bs => cap.sandbox.seccomp op f bs *> pure .unit
  | .sandboxMemfdCreate n f => cap.sandbox.memfdCreate n f *> pure .unit
  | .timeRandClockGettime clk => cap.timeRand.clock_gettime clk *> pure .unit
  | .timeRandClockNanosleep clk a r => cap.timeRand.clock_nanosleep clk a r *> pure .unit
  | .passwdGetpwuid uid => cap.passwd.getpwuid uid *> pure .unit
  | .postForkSpawn sp => cap.postFork.spawn sp *> pure .unit
  | .postForkSpawnWithBarrier sp => cap.postFork.spawnWithBarrier sp *> pure .unit
  | .postForkReleaseBarrier p => cap.postFork.releaseBarrier p *> pure .unit
  | .postForkAbortBarrier p => cap.postFork.abortBarrier p *> pure .unit
  | .getEnvPath => cap.getEnvPath *> pure .unit
  | .getEnvHome => cap.getEnvHome *> pure .unit
  | .startFwdTask fds ps => cap.startFwdTask fds ps *> pure .unit
  | .stopFwdTask h => cap.stopFwdTask h *> pure .unit

/-- Allowed transition contract for `RawHostCapM`: table reads/writes reflect `s.table`, platform identity matches `(s.isLinux, s.target)`, and OS syscalls preserve `s` without corrupting host table state. -/
def allowedRawCapStep (s : RawHostWorld) (req : RawCapStepReq) (out : RawCapStepOut) (s' : RawHostWorld) : Prop :=
  match req with
  | .metaInfo => out = .metaInfo s.isLinux s.target ∧ s' = s
  | .getTable => out = .table s.table ∧ s' = s
  | .modifyTable f => out = .table s.table ∧ s' = { s with table := f s.table }
  | _ => out = .unit ∧ s' = s

/-- Single-step request algebra covering all 13 effectful operations of `RawProcessSandboxOpsM`. -/
inductive RawOpsStepReq where
  /-- Query native host `SeccompArch`. -/
  | hostSeccompArch
  /-- Run host capability preflight check. -/
  | preflight (req : PreflightReq)
  /-- Discover immutable host runtime preset. -/
  | discoverHostPreset
  /-- Seal a compiled plan and seccomp filter into a `PlanHandle`. -/
  | sealPlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray)
  /-- Close and release a `PlanHandle`. -/
  | closePlan (ph : PlanHandle)
  /-- Spawn a sandbox box from a `PlanHandle`. -/
  | spawnBox (ph : PlanHandle)
  /-- Start host-side TCP port forwarders for a `BoxHandle`. -/
  | startPortForwarders (bh : BoxHandle) (fwds : Array PortForward)
  /-- Stop a running `PortForwarderHandle`. -/
  | stopPortForwarders (fh : PortForwarderHandle)
  /-- Release guest gate and collect bounded `stdout`/`stderr`. -/
  | readBoxOutput (bh : BoxHandle) (stdin : ByteArray) (timeoutMs : Nat) (maxOutputBytes : Option Nat)
  /-- Send `SIGKILL` to box process group. -/
  | killProcessGroup (bh : BoxHandle)
  /-- Send `SIGKILL` via `pidfd_send_signal`. -/
  | pidfdKill (bh : BoxHandle)
  /-- Kill cgroup, reap process, remove cgroup dir, and release `BoxHandle`. -/
  | reapBox (bh : BoxHandle)
  /-- Snapshot active resource counts. -/
  | activeResourceCounts
  deriving Inhabited

/-- Single-step outcome algebra covering all 13 effectful operations of `RawProcessSandboxOpsM`. -/
inductive RawOpsStepOut where
  /-- Outcome of `hostSeccompArch`. -/
  | exceptArch (res : Except SandboxError SeccompArch)
  /-- Outcome of `preflight`, `closePlan`, `stopPortForwarders`, `killProcessGroup`, `pidfdKill`, `reapBox`. -/
  | exceptUnit (res : Except SandboxError Unit)
  /-- Outcome of `discoverHostPreset`. -/
  | exceptPreset (res : Except SandboxError HostRuntimePreset)
  /-- Outcome of `sealPlan`. -/
  | exceptPlan (res : Except SandboxError PlanHandle)
  /-- Outcome of `spawnBox`. -/
  | exceptBox (res : Except SandboxError BoxHandle)
  /-- Outcome of `startPortForwarders`. -/
  | exceptFwd (res : Except SandboxError PortForwarderHandle)
  /-- Outcome of `readBoxOutput`. -/
  | exceptResult (res : Except SandboxError SandboxResult)
  /-- Outcome of `activeResourceCounts`. -/
  | counts (c : SandboxResourceCounts)
  deriving Inhabited

/-- Execute one `RawOpsStepReq` against `ops : RawProcessSandboxOpsM (StateM W)`. -/
def execRawOpsStep {W : Type} (ops : RawProcessSandboxOpsM (StateM W)) : RawOpsStepReq → StateM W RawOpsStepOut
  | .hostSeccompArch => RawOpsStepOut.exceptArch <$> ops.hostSeccompArch
  | .preflight req => RawOpsStepOut.exceptUnit <$> ops.preflight req
  | .discoverHostPreset => RawOpsStepOut.exceptPreset <$> ops.discoverHostPreset
  | .sealPlan plan sec => RawOpsStepOut.exceptPlan <$> ops.sealPlan plan sec
  | .closePlan ph => RawOpsStepOut.exceptUnit <$> ops.closePlan ph
  | .spawnBox ph => RawOpsStepOut.exceptBox <$> ops.spawnBox ph
  | .startPortForwarders bh fwds => RawOpsStepOut.exceptFwd <$> ops.startPortForwarders bh fwds
  | .stopPortForwarders fh => RawOpsStepOut.exceptUnit <$> ops.stopPortForwarders fh
  | .readBoxOutput bh stdin toMs maxOut? => RawOpsStepOut.exceptResult <$> ops.readBoxOutput bh stdin toMs maxOut?
  | .killProcessGroup bh => RawOpsStepOut.exceptUnit <$> ops.killProcessGroup bh
  | .pidfdKill bh => RawOpsStepOut.exceptUnit <$> ops.pidfdKill bh
  | .reapBox bh => RawOpsStepOut.exceptUnit <$> ops.reapBox bh
  | .activeResourceCounts => RawOpsStepOut.counts <$> ops.activeResourceCounts

/-- Predicate stating that `SandboxOutcome` carries non-negative exit/signal status. -/
def outcomeNonNeg : SandboxOutcome → Prop
  | .exited code => 0 ≤ code
  | .signaled sig => 0 ≤ sig
  | .timedOut => True
  | .outputLimitExceeded => True

/-- Allowed transition specification across all 13 effectful `RawProcessSandboxOpsM` operations over `RawHostWorld`. -/
def allowedRawOpsStep (s : RawHostWorld) (req : RawOpsStepReq) (out : RawOpsStepOut) (s' : RawHostWorld) : Prop :=
  rawHostWorldWf s' = true ∧ s'.isLinux = s.isLinux ∧ s'.target = s.target ∧
  match req, out with
  | .hostSeccompArch, .exceptArch res =>
    res = decodeHostAuditArch (detectHostAuditArch s.isLinux s.target) ∧ s' = s
  | .preflight _, .exceptUnit res =>
    tableCounts s'.table = tableCounts s.table ∧
    s'.table.plans = s.table.plans ∧ s'.table.boxes = s.table.boxes ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok () => s.isLinux = true
    | .error err => err.kind = .unavailable ∧ err.message ≠ ""
  | .discoverHostPreset, .exceptPreset res =>
    s' = s ∧
    match res with
    | .ok preset =>
      s.isLinux = true ∧
      (∀ e ∈ preset.systemEntries.toList, presetEntryBoxPath e ∈ presetSystemRoots.toList) ∧
      (∀ p ∈ preset.etcPaths.toList, p ∈ presetEtcAllowlist.toList) ∧
      (∀ h ∈ preset.excludedHomePaths.toList, isUnderSystemRoot h = true)
    | .error err => s.isLinux = false ∧ err.kind = .unavailable ∧ err.message ≠ ""
  | .sealPlan plan sec, .exceptPlan res =>
    s'.table.boxes = s.table.boxes ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok ph =>
      s.isLinux = true ∧
      planMandatoryInvariantsOk plan = true ∧
      seccompFilterBytesValid sec = true ∧
      isValidSandboxHandleId ph.handleId = true ∧
      ph.handleId = s.table.nextId ∧
      s'.table.plans.length = s.table.plans.length + 1
    | .error err =>
      err.message ≠ "" ∧ s' = s
  | .closePlan ph, .exceptUnit res =>
    s'.table.boxes = s.table.boxes ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok () =>
      isValidSandboxHandleId ph.handleId = true ∧
      tableHasKey ph.handleId s.table.plans = true ∧
      s'.table.plans.length + 1 = s.table.plans.length
    | .error err =>
      err.kind = .invalidInput ∧ err.message ≠ "" ∧
      (isValidSandboxHandleId ph.handleId = false ∨ tableHasKey ph.handleId s.table.plans = false) ∧
      s' = s
  | .spawnBox ph, .exceptBox res =>
    s'.table.plans = s.table.plans ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok bh =>
      isValidSandboxHandleId ph.handleId = true ∧
      tableHasKey ph.handleId s.table.plans = true ∧
      isValidSandboxHandleId bh.handleId = true ∧
      bh.handleId = s.table.nextId ∧
      0 < bh.pid ∧ 0 < bh.pgid ∧ bh.pidfd = 0 ∧
      s'.table.boxes.length = s.table.boxes.length + 1
    | .error err =>
      err.message ≠ "" ∧ s'.table.boxes = s.table.boxes ∧
      ((isValidSandboxHandleId ph.handleId = false ∨ tableHasKey ph.handleId s.table.plans = false) →
        err.kind = .invalidInput ∧ s' = s)
  | .startPortForwarders bh _, .exceptFwd res =>
    s'.table.plans = s.table.plans ∧ s'.table.boxes.length = s.table.boxes.length ∧
    match res with
    | .ok fh =>
      isValidSandboxHandleId bh.handleId = true ∧
      tableHasKey bh.handleId s.table.boxes = true ∧
      isValidSandboxHandleId fh.handleId = true ∧
      fh.boxHandleId = bh.handleId ∧
      s'.table.fwds.length = s.table.fwds.length + 1
    | .error err =>
      err.message ≠ "" ∧ s'.table.fwds = s.table.fwds ∧
      ((isValidSandboxHandleId bh.handleId = false ∨ tableHasKey bh.handleId s.table.boxes = false) →
        err.kind = .invalidInput ∧ s' = s)
  | .stopPortForwarders fh, .exceptUnit res =>
    s'.table.plans = s.table.plans ∧ s'.table.boxes = s.table.boxes ∧
    match res with
    | .ok () =>
      isValidSandboxHandleId fh.handleId = true ∧
      tableHasKey fh.handleId s.table.fwds = true ∧
      s'.table.fwds.length + 1 = s.table.fwds.length
    | .error err =>
      err.kind = .invalidInput ∧ err.message ≠ "" ∧
      (isValidSandboxHandleId fh.handleId = false ∨ tableHasKey fh.handleId s.table.fwds = false) ∧
      s' = s
  | .readBoxOutput bh _ _ maxOut?, .exceptResult res =>
    s'.table.plans = s.table.plans ∧ s'.table.boxes.length = s.table.boxes.length ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok boxRes =>
      isValidSandboxHandleId bh.handleId = true ∧
      tableHasKey bh.handleId s.table.boxes = true ∧
      outcomeNonNeg boxRes.outcome ∧
      (∀ m, maxOut? = some m → boxRes.stdout.size + boxRes.stderr.size ≤ m)
    | .error err =>
      err.message ≠ "" ∧
      ((isValidSandboxHandleId bh.handleId = false ∨ tableHasKey bh.handleId s.table.boxes = false) →
        err.kind = .invalidInput ∧ s' = s)
  | .killProcessGroup bh, .exceptUnit res =>
    s' = s ∧
    match res with
    | .ok () =>
      isValidSandboxHandleId bh.handleId = true ∧ tableHasKey bh.handleId s.table.boxes = true
    | .error err =>
      err.message ≠ "" ∧
      (if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
        err.kind = .ioError
       else
        err.kind = .invalidInput)
  | .pidfdKill bh, .exceptUnit res =>
    s' = s ∧
    match res with
    | .ok () =>
      isValidSandboxHandleId bh.handleId = true ∧ tableHasKey bh.handleId s.table.boxes = true
    | .error err =>
      err.message ≠ "" ∧
      (if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
        err.kind = .ioError
       else
        err.kind = .invalidInput)
  | .reapBox bh, .exceptUnit res =>
    s'.table.plans = s.table.plans ∧ s'.table.fwds = s.table.fwds ∧
    match res with
    | .ok () =>
      isValidSandboxHandleId bh.handleId = true ∧
      tableHasKey bh.handleId s.table.boxes = true ∧
      s'.table.boxes.length + 1 = s.table.boxes.length
    | .error err =>
      err.message ≠ "" ∧
      (if isValidSandboxHandleId bh.handleId && tableHasKey bh.handleId s.table.boxes then
        err.kind = .ioError ∧ s'.table.boxes.length + 1 = s.table.boxes.length
       else
        err.kind = .invalidInput ∧ s' = s)
  | .activeResourceCounts, .counts c =>
    c = tableCounts s.table ∧ s' = s
  | _, _ => False

end LeanSwe.ProcessSandbox.Raw.Model

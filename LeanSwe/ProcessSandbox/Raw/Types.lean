import LeanSwe.ProcessSandbox.Model.Seccomp

namespace LeanSwe.ProcessSandbox.Raw

export LeanSwe.ProcessSandbox.Model
  (SeccompArch SockFilter)

private def reprByteArray (bs : ByteArray) : Std.Format :=
  repr bs.toList

/-- Machine-checkable error categories returned by `LeanSwe.ProcessSandbox`. -/
inductive SandboxErrorKind where
  /-- Malformed `BoxSpec`, invalid mount/env/port/limit option, or closed/forged raw handle. -/
  | invalidInput
  /-- Host lacks Linux namespaces, `bwrap`, Landlock ABI >= 4, `seccomp`, direct `cgroup v2` delegation, or pre-`execvp` box setup failed closed. -/
  | unavailable
  /-- Host mount source path, guest working directory, or guest executable does not exist (`ENOENT`). -/
  | notFound
  /-- Host mount source path, guest working directory, or guest executable lacks required permissions (`EACCES` / `EPERM`). -/
  | permissionDenied
  /-- Underlying pipe, socket forwarder, `memfd`, `poll`, or wait OS I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.ProcessSandbox.Raw` and `LeanSwe.ProcessSandbox` operations. -/
structure SandboxError where
  /-- Machine-checkable error category. -/
  kind : SandboxErrorKind
  /-- Associated host or box path, when applicable. -/
  path : Option String := none
  /-- Underlying POSIX `errno` value, when applicable. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure representation of raw C-shim and OS error records for total error-mapping specifications. -/
inductive SandboxRawError where
  /-- Sandbox backend unavailable or failed closed prior to guest `execvp`. -/
  | unavailable (errno? : Option UInt32) (detail : String)
  /-- Missing host mount path, box working directory, or guest executable (`ENOENT`). -/
  | notFound (path : String) (errno : UInt32) (detail : String)
  /-- Permission denied on host mount path, box working directory, or guest executable (`EACCES` / `EPERM`). -/
  | permissionDenied (path? : Option String) (errno : UInt32) (detail : String)
  /-- Invalid argument or closed/forged handle (`EINVAL`). -/
  | invalidArgument (path? : Option String) (errno? : Option UInt32) (detail : String)
  /-- Numeric POSIX OS I/O failure. -/
  | ioError (path? : Option String) (errno : UInt32) (detail : String)
  /-- Generic fallback diagnostic failure. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Explicit filesystem mount entry mapped into the sandbox's empty root. -/
inductive SandboxMount where
  /-- Bind `hostPath` read-only at `boxPath` inside the box. -/
  | readOnly (hostPath : String) (boxPath : String)
  /-- Bind `hostPath` read-write at `boxPath` inside the box. -/
  | readWrite (hostPath : String) (boxPath : String)
  /-- Mount a fresh writable in-memory `tmpfs` at `boxPath` inside the box, discarded on exit. -/
  | scratch (boxPath : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Extract the target path inside the sandbox for a `SandboxMount`. -/
def mountBoxPath : SandboxMount → String
  | .readOnly _ bp => bp
  | .readWrite _ bp => bp
  | .scratch bp => bp

/-- Extract the source path on the host for a `SandboxMount`, or `none` for `.scratch`. -/
def mountHostPath? : SandboxMount → Option String
  | .readOnly hp _ => some hp
  | .readWrite hp _ => some hp
  | .scratch _ => none

/-- Raw TCP loopback port forward relaying `127.0.0.1:boxPort` inside the box to `127.0.0.1:hostPort` on the host. -/
structure PortForward where
  /-- Listener TCP port (`1..65535`) bound on `127.0.0.1` inside the box's network namespace. -/
  boxPort : UInt16
  /-- Target TCP port (`1..65535`) on host `127.0.0.1` to which raw bytes are relayed. -/
  hostPort : UInt16
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whole-box `cgroup v2`, per-process kernel `rlimit`, wall-clock timeout, and output capture caps. -/
structure SandboxLimits where
  /-- Positive wall-clock execution timeout in milliseconds (`0` is rejected as `.invalidInput`). -/
  timeoutMs : Nat := 60_000
  /-- Whole-box combined RAM limit in bytes enforced via direct `cgroup v2` `memory.max` with `memory.swap.max = "0"`, ignoring `ENOENT` on swapless kernels (`some 0` is rejected). -/
  memoryMaxBytes : Option Nat := some (8 * (1024 ^ 3))
  /-- Whole-box combined guest task/process limit enforced via direct `cgroup v2` `pids.max = pidsMax + 2` accounting for the 2 wrapper tasks (`some 0` is rejected). -/
  pidsMax : Option Nat := some 512
  /-- Per-process maximum writable file size in bytes enforced via `RLIMIT_FSIZE` (`some 0` forbids non-empty writes). -/
  fileSizeMaxBytes : Option Nat := some (4 * (1024 ^ 3))
  /-- Maximum combined captured `stdout.size + stderr.size` in bytes (`some 0` caps output at 0 bytes). -/
  maxOutputBytes : Option Nat := some (16 * 1024 * 1024)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unvalidated one-shot sandboxed command specification. -/
structure BoxSpec where
  /-- Executable name or path passed directly to `execvp` inside the box (never via a shell). -/
  program : String
  /-- Explicit argument array (`argv[1..]`) passed verbatim to `execvp`. -/
  args : Array String := #[]
  /-- Optional absolute working directory inside the box (defaults deterministically to `"/tmp"` when `none`). -/
  cwd : Option String := none
  /-- Bytes written to the guest's `stdin` pipe before closing `stdin`. -/
  stdin : ByteArray := ByteArray.empty
  /-- Explicit filesystem mounts added atop the empty root and read-only OS runtime preset (`.scratch "/tmp"` is injected iff no mount targets `"/tmp"`). -/
  mounts : Array SandboxMount := #[]
  /-- Whether processes inside the box may communicate over the box's private `127.0.0.1` loopback. -/
  allowBoxLocalhost : Bool := false
  /-- Explicit `(boxPort, hostPort)` raw TCP loopback relays (`1..65535`, distinct `boxPort`s). -/
  portForwards : Array PortForward := #[]
  /-- Clean-slate environment variables (`("PATH", "/usr/bin:/bin")` is injected iff `"PATH"` is absent). -/
  env : Array (String × String) := #[]
  /-- Whole-box and per-process resource, timeout, and output limits. -/
  limits : SandboxLimits := {}
  deriving BEq, DecidableEq

instance : Inhabited BoxSpec where
  default := { program := "" }

instance : Repr BoxSpec where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "program := " ++ repr s.program,
        "args := " ++ repr s.args,
        "cwd := " ++ repr s.cwd,
        "stdin := " ++ reprByteArray s.stdin,
        "mounts := " ++ repr s.mounts,
        "allowBoxLocalhost := " ++ repr s.allowBoxLocalhost,
        "portForwards := " ++ repr s.portForwards,
        "env := " ++ repr s.env,
        "limits := " ++ repr s.limits
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Validated and normalized `BoxSpec` produced at the boundary by `validateSpec`. -/
structure ValidBoxSpec where
  /-- Non-empty, NUL-free executable name or path. -/
  program : String
  /-- NUL-free argument array (`argv[1..]`). -/
  args : Array String
  /-- Canonical absolute working directory inside the box (`"/tmp"` when `spec.cwd = none`). -/
  cwd : String
  /-- Standard input bytes fed to the guest's `stdin` pipe. -/
  stdin : ByteArray
  /-- Canonicalized mounts with distinct `boxPath`s disjoint from system preset paths, guaranteed to cover `"/tmp"`. -/
  mounts : Array SandboxMount
  /-- Whether box-private `127.0.0.1` loopback traffic is permitted on unforwarded ports. -/
  allowBoxLocalhost : Bool
  /-- Validated TCP port forwards (`1..65535`, pairwise distinct `boxPort`s). -/
  portForwards : Array PortForward
  /-- Validated, deduplicated clean-slate environment entries guaranteed to define `"PATH"`. -/
  env : Array (String × String)
  /-- Validated resource limits (`timeoutMs > 0`, non-zero `memoryMaxBytes` and `pidsMax` when `some`). -/
  limits : SandboxLimits
  deriving BEq, DecidableEq

instance : Inhabited ValidBoxSpec where
  default :=
    { program := "/bin/true"
      args := #[]
      cwd := "/tmp"
      stdin := ByteArray.empty
      mounts := #[.scratch "/tmp"]
      allowBoxLocalhost := false
      portForwards := #[]
      env := #[("PATH", "/usr/bin:/bin")]
      limits := {} }

instance : Repr ValidBoxSpec where
  reprPrec s _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "program := " ++ repr s.program,
        "args := " ++ repr s.args,
        "cwd := " ++ repr s.cwd,
        "stdin := " ++ reprByteArray s.stdin,
        "mounts := " ++ repr s.mounts,
        "allowBoxLocalhost := " ++ repr s.allowBoxLocalhost,
        "portForwards := " ++ repr s.portForwards,
        "env := " ++ repr s.env,
        "limits := " ++ repr s.limits
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Project a `ValidBoxSpec` back into a normalized `BoxSpec`. -/
def validBoxSpecToBoxSpec (v : ValidBoxSpec) : BoxSpec :=
  { program := v.program
    args := v.args
    cwd := some v.cwd
    stdin := v.stdin
    mounts := v.mounts
    allowBoxLocalhost := v.allowBoxLocalhost
    portForwards := v.portForwards
    env := v.env
    limits := v.limits }

/-- Clean guest termination classification once launched inside a verified box (zero magic exit codes). -/
inductive SandboxOutcome where
  /-- Guest exited normally (`WIFEXITED`) with `exitCode` (any integer status, never hijacked for sandbox errors). -/
  | exited (exitCode : Int)
  /-- Guest was terminated by OS signal `signal` (`WIFSIGNALED`, e.g. `SIGKILL` on cgroup OOM or `SIGXFSZ`). -/
  | signaled (signal : Int)
  /-- Guest exceeded `limits.timeoutMs`; entire box was killed and reaped. -/
  | timedOut
  /-- Combined `stdout` and `stderr` exceeded `limits.maxOutputBytes`; entire box was killed and reaped. -/
  | outputLimitExceeded
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Completed sandbox execution result carrying `outcome` and bounded in-memory `stdout`/`stderr`. -/
structure SandboxResult where
  /-- Termination outcome of the sandboxed command. -/
  outcome : SandboxOutcome
  /-- Captured standard output bytes (bounded by `limits.maxOutputBytes`). -/
  stdout : ByteArray
  /-- Captured standard error bytes (bounded by `limits.maxOutputBytes`). -/
  stderr : ByteArray
  deriving BEq, DecidableEq

instance : Inhabited SandboxResult where
  default := { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }

instance : Repr SandboxResult where
  reprPrec r _ :=
    Std.Format.bracket "{" (
      Std.Format.joinSep [
        "outcome := " ++ repr r.outcome,
        "stdout := " ++ reprByteArray r.stdout,
        "stderr := " ++ reprByteArray r.stderr
      ] (", " ++ Std.Format.line)
    ) "}"

/-- Host capability requirements checked by `preflight` prior to box creation. -/
structure PreflightReq where
  /-- Whether direct `cgroup v2` cgroupfs `memory` delegation (`memory.max` + `memory.swap.max = "0"`) must be enforceable. -/
  needMemoryCgroup : Bool := true
  /-- Whether direct `cgroup v2` cgroupfs `pids` delegation (`pids.max`) must be enforceable. -/
  needPidsCgroup : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Discovered top-level host runtime entry among `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`. -/
inductive PresetSystemEntry where
  /-- Existing host directory to bind read-only at `path` inside the box. -/
  | readOnlyDir (path : String)
  /-- Existing top-level host symlink at `linkPath` (e.g. `"/bin"`) preserved with `target` (e.g. `"usr/bin"`). -/
  | topSymlink (linkPath : String) (target : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Extract the box target path of a `PresetSystemEntry`. -/
def presetEntryBoxPath : PresetSystemEntry → String
  | .readOnlyDir p => p
  | .topSymlink lp _ => lp

/-- Host runtime preset discovered before compiling an immutable `CompiledSandboxPlan`. -/
structure HostRuntimePreset where
  /-- Discovered entries among `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`. -/
  systemEntries : Array PresetSystemEntry := #[]
  /-- Discovered existing safe `/etc` files/directories on the host. -/
  etcPaths : Array String := #[]
  /-- Host `$HOME` and `passwd.pw_dir` paths to mask if nested beneath a mounted preset directory. -/
  excludedHomePaths : Array String := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure compiled sandbox execution plan sealed into an immutable `memfd` before launching `bwrap`. -/
structure CompiledSandboxPlan where
  /-- Start from an empty root `tmpfs` (never `--ro-bind / /`). -/
  emptyRoot : Bool := true
  /-- Unshare isolated `user`, `pid`, `net`, `mount`, `ipc`, and `uts` namespaces. -/
  unshareAllNamespaces : Bool := true
  /-- Mount a fresh box-private `/proc` inside the box PID namespace. -/
  mountFreshProc : Bool := true
  /-- Mount a minimal safe `/dev` (`/dev/null`, `/dev/zero`, `/dev/urandom`, `/dev/tty`, `/dev/ptmx`, `/dev/pts`). -/
  mountSafeDev : Bool := true
  /-- Immutable read-only top-level system directories and symlinks (`/usr`, `/bin`, `/sbin`, `/lib`, `/lib64`). -/
  presetSystemEntries : Array PresetSystemEntry := #[]
  /-- Immutable read-only safe `/etc` entries. -/
  presetEtcPaths : Array String := #[]
  /-- Read-only empty `tmpfs` masks hiding nested host `$HOME` / `passwd.pw_dir` paths inside preset mounts. -/
  maskedPresetPaths : Array String := #[]
  /-- Depth-ordered mounts (`readOnly`, `readWrite`, `scratch`) applied after system presets, always covering `"/tmp"`. -/
  userMounts : Array SandboxMount := #[.scratch "/tmp"]
  /-- Enforce whole-box `memory.max` (`memory.swap.max = "0"`) and `pids.max` via direct `/sys/fs/cgroup` cgroupfs (never `systemd-run --user --scope`). -/
  directCgroupV2Fs : Bool := true
  /-- Minimum required Landlock ABI version (`>= 4` for filesystem + TCP bind/connect confinement). -/
  landlockMinAbi : Nat := 4
  /-- Whether box-local `127.0.0.1` TCP connections are permitted on unforwarded ports. -/
  allowBoxLocalhost : Bool := false
  /-- Validated `(boxPort, hostPort)` TCP relays bound inside the box and handed off via `SCM_RIGHTS`. -/
  portForwards : Array PortForward := #[]
  /-- Block `socket(AF_UNIX, ...)`, `AF_SMC`, and `MSG_FASTOPEN` via `seccomp` after pre-`execvp` setup completes. -/
  blockUnixSocketAndSmc : Bool := true
  /-- Allow anonymous in-box `socketpair(AF_UNIX, SOCK_STREAM | SOCK_SEQPACKET, ...)` IPC inside `seccomp`. -/
  allowAnonUnixSocketpair : Bool := true
  /-- Return `ENOSYS` on `clone3` (so glibc falls back to `clone`) and block `CLONE_NEW*` flags on `clone` with `EPERM`. -/
  clone3EnosysFallback : Bool := true
  /-- Install strict `seccomp` BPF denylist blocking admin/reboot/clock/module/mount/bpf/io_uring/keyctl/escape syscalls. -/
  seccompStrictDenylist : Bool := true
  /-- Set `PR_SET_NO_NEW_PRIVS = 1` before applying Landlock and `seccomp`. -/
  noNewPrivs : Bool := true
  /-- Enforce `RLIMIT_CORE = 0` inside the box. -/
  rlimitCoreZero : Bool := true
  /-- Run `leanswe-psandbox-init` with `PR_SET_CHILD_SUBREAPER` and `PR_SET_PDEATHSIG(SIGKILL)`. -/
  subreaperAndPdeathsig : Bool := true
  /-- Clear all inherited host environment variables (`clearenv`) before populating `env`. -/
  cleanEnv : Bool := true
  /-- Exact environment key-value pairs passed to `execvp` inside the box. -/
  env : Array (String × String) := #[("PATH", "/usr/bin:/bin")]
  /-- Executable name or path passed to `execvp`. -/
  program : String
  /-- Explicit argument array (`argv[1..]`). -/
  args : Array String := #[]
  /-- Canonical absolute working directory inside the box (`"/tmp"` by default). -/
  cwd : String := "/tmp"
  /-- Whole-box `cgroup v2`, `RLIMIT_FSIZE`, timeout, and output byte limits. -/
  limits : SandboxLimits := {}
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return `true` iff `id` is a valid non-zero 64-bit C-shim slot identifier (`0 < id < UInt64.size`). -/
def isValidSandboxHandleId (id : Nat) : Bool :=
  decide (0 < id ∧ id < UInt64.size)

/-- Opaque handle referencing an immutable `F_ADD_SEALS`-sealed `memfd` sandbox plan. -/
structure PlanHandle where
  /-- Non-zero C-shim plan slot identifier (`0 < handleId < UInt64.size`). -/
  handleId : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Opaque handle referencing a spawned sandbox instance inside its isolated process group and per-box `/sys/fs/cgroup` directory. -/
structure BoxHandle where
  /-- Non-zero C-shim box slot identifier (`0 < handleId < UInt64.size`). -/
  handleId : Nat
  /-- Host-visible root process ID of the sandbox instance (`> 0`). -/
  pid : Int
  /-- Dedicated host process group ID covering the sandbox launcher (`> 0`). -/
  pgid : Int
  /-- Race-free Linux `pidfd` descriptor tracking the sandbox root (`≥ 0`). -/
  pidfd : Int
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Opaque handle referencing a running host-side non-blocking TCP `poll()` port forwarder. -/
structure PortForwarderHandle where
  /-- Non-zero C-shim forwarder slot identifier (`0 < handleId < UInt64.size`). -/
  handleId : Nat
  /-- Associated `BoxHandle.handleId` owning the handed-off box listener descriptors. -/
  boxHandleId : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Active resource counts tracked by `RawProcessSandboxOpsM` for leak-conservation verification. -/
structure SandboxResourceCounts where
  /-- Number of currently open sealed `memfd` plan handles. -/
  openPlans : Nat := 0
  /-- Number of currently un-reaped spawned `BoxHandle` instances (including per-box cgroup directories). -/
  activeBoxes : Nat := 0
  /-- Number of currently running host-side TCP port-forwarder handles. -/
  activeForwarders : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single-step OS and C-shim primitives for `LeanSwe.ProcessSandbox`, parameterized over effect monad `m`. -/
structure RawProcessSandboxOpsM (m : Type → Type) where
  /-- Normalize a `SandboxRawError` into a `SandboxError` with a non-empty diagnostic message. -/
  mapRawError : SandboxRawError → SandboxError
  /-- Query the host's native 64-bit Linux `seccomp` audit architecture (`x86_64` or `aarch64`), failing closed with `.unavailable` on unsupported hosts. -/
  hostSeccompArch : m (Except SandboxError SeccompArch)
  /-- Probe Linux kernel, `bwrap`, namespaces, Landlock ABI >= 4, `seccomp`, and direct `/sys/fs/cgroup` sibling directory plus `memory`/`pids` delegation, failing closed with `.unavailable`. -/
  preflight : PreflightReq → m (Except SandboxError Unit)
  /-- Discover existing `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64` entries, safe `/etc` files, and existing nested host `$HOME` / `passwd.pw_dir` directories without touching `/home` autofs. -/
  discoverHostPreset : m (Except SandboxError HostRuntimePreset)
  /-- Serialize and `F_ADD_SEALS`-seal a `CompiledSandboxPlan` (plus embedded init and synthetic `/etc/hosts` payloads) into immutable `memfd`s. -/
  sealPlan : CompiledSandboxPlan → m (Except SandboxError PlanHandle)
  /-- Close and release a sealed `PlanHandle`. -/
  closePlan : PlanHandle → m (Except SandboxError Unit)
  /-- Create per-box direct `cgroup v2` directory (`memory.max`, `memory.swap.max = "0"`, `pids.max = pidsMax + 2`), spawn `bwrap --unshare-all --as-pid-1 --die-with-parent` via the dedicated `pthread_once` spawner thread using fresh `O_RDONLY` `/proc/self/fd/<memfd>` descriptors, place child into `cgroup.procs` before `execvp`, open `pidfd`, and complete pre-`execvp` setup barrier. -/
  spawnBox : PlanHandle → m (Except SandboxError BoxHandle)
  /-- Start the host-side non-blocking raw TCP `poll()` forwarder (`MAX_RELAY_SLOTS = 128`, `16 KiB` ring buffers, independent half-close `SHUT_WR` drain) for the box's handed-off `127.0.0.1:boxPort` listeners. -/
  startPortForwarders : BoxHandle → Array PortForward → m (Except SandboxError PortForwarderHandle)
  /-- Stop a running port forwarder and close all listener and relay descriptors. -/
  stopPortForwarders : PortForwarderHandle → m (Except SandboxError Unit)
  /-- Release the pre-`execvp` gate, stream `stdin`, and read bounded `stdout`/`stderr` under `timeoutMs` and `maxOutputBytes`. -/
  readBoxOutput : BoxHandle → ByteArray → Nat → Option Nat → m (Except SandboxError SandboxResult)
  /-- Send `SIGKILL` to the sandbox's host process group (`-pgid`). -/
  killProcessGroup : BoxHandle → m (Except SandboxError Unit)
  /-- Send `SIGKILL` via `pidfd_send_signal` to the sandbox root without PID-reuse races. -/
  pidfdKill : BoxHandle → m (Except SandboxError Unit)
  /-- Write `cgroup.kill = "1"`, wait/reap the sandbox until all box processes exit, poll `cgroup.events` (`populated 0`) and `rmdir` the per-box cgroup directory, close `pidfd`/pipes, and release `BoxHandle`. -/
  reapBox : BoxHandle → m (Except SandboxError Unit)
  /-- Return counts of currently open `PlanHandle`, `BoxHandle`, and `PortForwarderHandle` resources. -/
  activeResourceCounts : m SandboxResourceCounts

/-- Concrete `IO` primitive bundle exported by `LeanSwe.ProcessSandbox.Raw`. -/
abbrev RawProcessSandboxOps := RawProcessSandboxOpsM IO

end LeanSwe.ProcessSandbox.Raw

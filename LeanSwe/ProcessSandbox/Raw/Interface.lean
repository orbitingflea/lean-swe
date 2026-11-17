import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl

namespace LeanSwe.ProcessSandbox.Raw

@[extern "leanswe_psandbox_host_arch"]
private opaque rawHostArch : IO UInt32

@[extern "leanswe_psandbox_preflight"]
private opaque rawPreflight : Bool → Bool → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_discover_preset"]
private opaque rawDiscoverPreset :
  IO (UInt8 × UInt32 × String × Array (UInt8 × String × String) × Array String × Array String)

@[extern "leanswe_psandbox_seal_plan"]
private opaque rawSealPlan : @& ByteArray → IO (UInt8 × UInt32 × String × String × UInt64)

@[extern "leanswe_psandbox_close_plan"]
private opaque rawClosePlan : UInt64 → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_spawn_box"]
private opaque rawSpawnBox : UInt64 → IO (UInt8 × UInt32 × String × String × UInt64 × UInt32 × UInt32 × UInt32)

@[extern "leanswe_psandbox_start_forwarders"]
private opaque rawStartForwarders :
  UInt64 → @& Array UInt16 → @& Array UInt16 → IO (UInt8 × UInt32 × String × String × UInt64)

@[extern "leanswe_psandbox_stop_forwarders"]
private opaque rawStopForwarders : UInt64 → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_read_output"]
private opaque rawReadOutput :
  UInt64 → @& ByteArray → UInt64 → Bool → UInt64 →
  IO (UInt8 × UInt32 × String × String × UInt8 × UInt32 × ByteArray × ByteArray)

@[extern "leanswe_psandbox_kill_pg"]
private opaque rawKillPg : UInt64 → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_pidfd_kill"]
private opaque rawPidfdKill : UInt64 → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_reap_box"]
private opaque rawReapBox : UInt64 → IO (UInt8 × UInt32 × String × String)

@[extern "leanswe_psandbox_active_counts"]
private opaque rawActiveCounts : IO (Nat × Nat × Nat)

private def posixRawOps : Internal.PosixRawOps :=
  { hostArch := rawHostArch
    preflight := rawPreflight
    discoverPreset := rawDiscoverPreset
    sealPlan := rawSealPlan
    closePlan := rawClosePlan
    spawnBox := rawSpawnBox
    startForwarders := rawStartForwarders
    stopForwarders := rawStopForwarders
    readOutput := rawReadOutput
    killPg := rawKillPg
    pidfdKill := rawPidfdKill
    reapBox := rawReapBox
    activeCounts := rawActiveCounts }

/-- Default OS sandbox primitive operations backed by `c/psandbox_shim.c` and `c/psandbox_init.c`. -/
def defaultOps : RawProcessSandboxOps :=
  Internal.mkRawOps posixRawOps

/-- Normalize a `SandboxRawError` into a `SandboxError` with a non-empty diagnostic message. -/
@[inline] def mapRawError (err : SandboxRawError) : SandboxError :=
  defaultOps.mapRawError err

/-- Query the host's native 64-bit Linux `seccomp` audit architecture (`x86_64` or `aarch64`), failing closed with `.unavailable`. -/
@[inline] def hostSeccompArch : IO (Except SandboxError SeccompArch) :=
  defaultOps.hostSeccompArch

/-- Probe Linux kernel, `bwrap`, namespaces, Landlock ABI >= 4, `seccomp`, and direct `/sys/fs/cgroup` delegation. -/
@[inline] def preflight (req : PreflightReq := {}) : IO (Except SandboxError Unit) :=
  defaultOps.preflight req

/-- Discover immutable host runtime preset entries and nested `$HOME` masks. -/
@[inline] def discoverHostPreset : IO (Except SandboxError HostRuntimePreset) :=
  defaultOps.discoverHostPreset

/-- Serialize and `F_ADD_SEALS`-seal a `CompiledSandboxPlan` into immutable `memfd` descriptors. -/
@[inline] def sealPlan (plan : CompiledSandboxPlan) : IO (Except SandboxError PlanHandle) :=
  defaultOps.sealPlan plan

/-- Close and release a sealed `PlanHandle`. -/
@[inline] def closePlan (ph : PlanHandle) : IO (Except SandboxError Unit) :=
  defaultOps.closePlan ph

/-- Spawn an isolated sandbox instance inside its per-box direct `cgroup v2` directory. -/
@[inline] def spawnBox (ph : PlanHandle) : IO (Except SandboxError BoxHandle) :=
  defaultOps.spawnBox ph

/-- Start the host-side non-blocking TCP `poll()` forwarder for a spawned sandbox's listeners. -/
@[inline] def startPortForwarders (bh : BoxHandle) (fwds : Array PortForward) :
    IO (Except SandboxError PortForwarderHandle) :=
  defaultOps.startPortForwarders bh fwds

/-- Stop a running port forwarder and close all listener and relay descriptors. -/
@[inline] def stopPortForwarders (fh : PortForwarderHandle) : IO (Except SandboxError Unit) :=
  defaultOps.stopPortForwarders fh

/-- Release the pre-`execvp` gate, stream `stdin`, and read bounded `stdout`/`stderr`. -/
@[inline] def readBoxOutput
    (bh : BoxHandle)
    (stdin : ByteArray := ByteArray.empty)
    (timeoutMs : Nat := 60_000)
    (maxOutputBytes : Option Nat := some (16 * 1024 * 1024)) :
    IO (Except SandboxError SandboxResult) :=
  defaultOps.readBoxOutput bh stdin timeoutMs maxOutputBytes

/-- Send `SIGKILL` to the sandbox's host process group (`-pgid`). -/
@[inline] def killProcessGroup (bh : BoxHandle) : IO (Except SandboxError Unit) :=
  defaultOps.killProcessGroup bh

/-- Send `SIGKILL` via `pidfd_send_signal` to the sandbox root. -/
@[inline] def pidfdKill (bh : BoxHandle) : IO (Except SandboxError Unit) :=
  defaultOps.pidfdKill bh

/-- Kill the box cgroup, reap the sandbox process, remove its cgroup directory, and release `BoxHandle`. -/
@[inline] def reapBox (bh : BoxHandle) : IO (Except SandboxError Unit) :=
  defaultOps.reapBox bh

/-- Return counts of currently open `PlanHandle`, `BoxHandle`, and `PortForwarderHandle` resources. -/
@[inline] def activeResourceCounts : IO SandboxResourceCounts :=
  defaultOps.activeResourceCounts

end LeanSwe.ProcessSandbox.Raw

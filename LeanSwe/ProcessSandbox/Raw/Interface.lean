import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Host.SysBridge

namespace LeanSwe.ProcessSandbox.Raw

/-- Default OS sandbox primitive operations backed by pure Lean `Host.SysBridge` and embedded `leanswe-psandbox-init`. -/
def defaultOps : RawProcessSandboxOps :=
  { Host.SysBridge.defaultOps with
    mapRawError := Internal.mapRawError
    decodeHostAuditArch := Internal.decodeHostAuditArch
    encodePlan := Internal.encodePlan }

/-- Normalize a `SandboxRawError` into a `SandboxError` with a non-empty diagnostic message. -/
@[inline] def mapRawError (err : SandboxRawError) : SandboxError :=
  defaultOps.mapRawError err

/-- Decode a raw Linux `AUDIT_ARCH_*` constant into `SeccompArch`, failing closed with `.unavailable`. -/
@[inline] def decodeHostAuditArch (raw : UInt32) : Except SandboxError SeccompArch :=
  defaultOps.decodeHostAuditArch raw

/-- Validate `CompiledSandboxPlan` and `8 * n`-byte `seccomp` filter bytes and serialize them into `LSWP0002` wire format. -/
@[inline] def encodePlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Except SandboxError ByteArray :=
  defaultOps.encodePlan plan seccompBytes

/-- Query the host's native 64-bit Linux `seccomp` audit architecture (`x86_64` or `aarch64`), failing closed with `.unavailable`. -/
@[inline] def hostSeccompArch : IO (Except SandboxError SeccompArch) :=
  defaultOps.hostSeccompArch

/-- Probe Linux kernel, `bwrap`, namespaces, Landlock ABI >= 4, `seccomp`, and direct `/sys/fs/cgroup` delegation. -/
@[inline] def preflight (req : PreflightReq := {}) : IO (Except SandboxError Unit) :=
  defaultOps.preflight req

/-- Discover immutable host runtime preset entries and nested `$HOME` masks. -/
@[inline] def discoverHostPreset : IO (Except SandboxError HostRuntimePreset) :=
  defaultOps.discoverHostPreset

/-- Serialize via `encodePlan` and `F_ADD_SEALS`-seal a `CompiledSandboxPlan` and encoded `seccomp` filter into immutable `memfd` descriptors. -/
@[inline] def sealPlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    IO (Except SandboxError PlanHandle) :=
  defaultOps.sealPlan plan seccompBytes

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

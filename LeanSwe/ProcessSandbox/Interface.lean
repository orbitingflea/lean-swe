import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Raw.Interface

namespace LeanSwe.ProcessSandbox

/-- Default `ProcessSandboxApi` backed by `LeanSwe.ProcessSandbox.Raw.defaultOps`. -/
def defaultApi : ProcessSandboxApi :=
  Internal.mkApiM Raw.defaultOps

/-- Validate and normalize a `BoxSpec`, failing with `.invalidInput` on invalid paths, ports, env, or limits. -/
@[inline] def validateSpec (spec : BoxSpec) : Except SandboxError ValidBoxSpec :=
  defaultApi.validateSpec spec

/-- Compile the architecture-specific `seccomp` classic BPF filter program for a sandboxed guest. -/
@[inline] def compileSeccompBpf (arch : SeccompArch) : Array SockFilter :=
  defaultApi.compileSeccompBpf arch

/-- Serialize an `Array SockFilter` into contiguous `8 * n`-byte little-endian `struct sock_filter` wire bytes. -/
@[inline] def encodeSeccompBpf (prog : Array SockFilter) : ByteArray :=
  defaultApi.encodeSeccompBpf prog

/-- Execute `BoxSpec` inside a fresh isolated Linux process sandbox and reap all descendants before returning. -/
@[inline] def run (spec : BoxSpec) : IO (Except SandboxError SandboxResult) :=
  defaultApi.run spec

/-- Probe whether the current host supports `ProcessSandbox.run` with default `cgroup v2` limits. -/
@[inline] def isAvailable : IO Bool :=
  defaultApi.isAvailable

end LeanSwe.ProcessSandbox

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

/-- Execute `BoxSpec` inside a fresh isolated Linux process sandbox and reap all descendants before returning. -/
@[inline] def run (spec : BoxSpec) : IO (Except SandboxError SandboxResult) :=
  defaultApi.run spec

/-- Probe whether the current host supports `ProcessSandbox.run` with default `cgroup v2` limits. -/
@[inline] def isAvailable : IO Bool :=
  defaultApi.isAvailable

end LeanSwe.ProcessSandbox

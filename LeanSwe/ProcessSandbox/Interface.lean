import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Impl

namespace LeanSwe.ProcessSandbox

/-- Default `ProcessSandboxApi` backed by `LeanSwe.Process.defaultApi` and `LeanSwe.Fs.defaultApi`. -/
def defaultApi : ProcessSandboxApi :=
  Internal.mkApiM LeanSwe.Process.defaultApi LeanSwe.Fs.defaultApi

/-- Validate and normalize an untrusted `BoxSpec`, failing with `.invalidInput` on malformed inputs. -/
@[inline] def validateSpec (spec : BoxSpec) : Except SandboxError ValidBoxSpec :=
  defaultApi.validateSpec spec

/-- Execute `BoxSpec` inside an isolated `bwrap` sandbox, reaping all guest descendants before returning. -/
@[inline] def run (spec : BoxSpec) : IO (Except SandboxError SandboxResult) :=
  defaultApi.run spec

/-- Probe whether the current host supports `ProcessSandbox.run`. -/
@[inline] def isAvailable : IO Bool :=
  defaultApi.isAvailable

end LeanSwe.ProcessSandbox

import LeanSwe.ProcessSandbox.Raw.Types

namespace LeanSwe.ProcessSandbox

export LeanSwe.ProcessSandbox.Raw
  (SandboxErrorKind SandboxError SandboxRawError SandboxMount mountBoxPath mountHostPath?
   PortForward SandboxLimits BoxSpec ValidBoxSpec validBoxSpecToBoxSpec
   SandboxOutcome SandboxResult PreflightReq PresetSystemEntry presetEntryBoxPath
   HostRuntimePreset CompiledSandboxPlan isValidSandboxHandleId
   PlanHandle BoxHandle PortForwarderHandle SandboxResourceCounts
   RawProcessSandboxOpsM RawProcessSandboxOps)

/-- Public isolated one-shot command execution API exported by `LeanSwe.ProcessSandbox`, parameterized over `m`. -/
structure ProcessSandboxApiM (m : Type → Type) where
  /-- Validate and normalize an untrusted `BoxSpec`, failing with `.invalidInput` on malformed paths, ports, env, or limits. -/
  validateSpec : BoxSpec → Except SandboxError ValidBoxSpec
  /-- Execute `BoxSpec` inside a fresh Linux namespace + Landlock + `seccomp` + direct whole-box `cgroup v2` sandbox, reaping all descendants before returning. -/
  run : BoxSpec → m (Except SandboxError SandboxResult)
  /-- Probe whether the current host supports `ProcessSandbox.run` (Linux, `bwrap`, namespaces, Landlock ABI >= 4, `seccomp`, and direct `cgroup v2` `memory`/`pids` delegation). -/
  isAvailable : m Bool

/-- Concrete `IO` sandbox API bundle exported by `LeanSwe.ProcessSandbox`. -/
abbrev ProcessSandboxApi := ProcessSandboxApiM IO

/-- Pure builder signature assembling a `ProcessSandboxApiM m` from injected `RawProcessSandboxOpsM m` primitives. -/
abbrev ProcessSandboxBuilder (m : Type → Type) :=
  RawProcessSandboxOpsM m → ProcessSandboxApiM m

end LeanSwe.ProcessSandbox

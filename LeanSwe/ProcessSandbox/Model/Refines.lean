import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Raw.Model.Refines

namespace LeanSwe.ProcessSandbox.Model

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Raw.Model

/-- Reference specification for `ProcessSandbox.validateSpec`, delegating to `validateSpecPure`. -/
def validateSpecModel (spec : BoxSpec) : Except SandboxError ValidBoxSpec :=
  validateSpecPure spec

/-- Well-formedness predicate on `RawHostWorld` for `ProcessSandbox` compositional refinement. -/
def rawStepWf (s : RawHostWorld) : Bool :=
  rawHostWorldWf s

/-- Single-step executor for injected `RawProcessSandboxOpsM (StateM W)` primitives. -/
def execRawStep {W : Type} (raw : RawProcessSandboxOpsM (StateM W))
    (req : RawOpsStepReq) : StateM W RawOpsStepOut :=
  execRawOpsStep raw req

/-- Allowed transition specification for injected `RawProcessSandboxOpsM` primitives over `RawHostWorld`. -/
def allowedRawStep (s : RawHostWorld) (req : RawOpsStepReq)
    (out : RawOpsStepOut) (s' : RawHostWorld) : Prop :=
  allowedRawOpsStep s req out s'

/-- Single-step request algebra covering all 3 public operations of `ProcessSandboxApiM`. -/
inductive PkgStepReq where
  /-- Validate and normalize an untrusted `BoxSpec`. -/
  | validateSpec (spec : BoxSpec)
  /-- Execute `spec` inside an isolated sandbox box. -/
  | run (spec : BoxSpec)
  /-- Probe whether the host supports `ProcessSandbox.run` with default `cgroup v2` limits. -/
  | isAvailable
  deriving Inhabited

/-- Single-step outcome algebra covering all 3 public operations of `ProcessSandboxApiM`. -/
inductive PkgStepOut where
  /-- Outcome of `validateSpec`. -/
  | validateSpec (res : Except SandboxError ValidBoxSpec)
  /-- Outcome of `run`. -/
  | run (res : Except SandboxError SandboxResult)
  /-- Outcome of `isAvailable`. -/
  | isAvailable (avail : Bool)
  deriving Inhabited

/-- Execute one `PkgStepReq` against `api : ProcessSandboxApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : ProcessSandboxApiM (StateM W)) :
    PkgStepReq → StateM W PkgStepOut
  | .validateSpec spec => pure (.validateSpec (api.validateSpec spec))
  | .run spec => PkgStepOut.run <$> api.run spec
  | .isAvailable => PkgStepOut.isAvailable <$> api.isAvailable

/-- Allowed transition specification for `ProcessSandboxApiM` operations over `RawHostWorld`. -/
def allowedPkgStep (s : RawHostWorld) (req : PkgStepReq)
    (out : PkgStepOut) (s' : RawHostWorld) : Prop :=
  rawHostWorldWf s' = true ∧ s'.isLinux = s.isLinux ∧ s'.target = s.target ∧
  match req, out with
  | .validateSpec spec, .validateSpec res =>
    res = validateSpecModel spec ∧ s' = s
  | .isAvailable, .isAvailable avail =>
    tableCounts s'.table = tableCounts s.table ∧
    s'.table.plans = s.table.plans ∧
    s'.table.boxes = s.table.boxes ∧
    s'.table.fwds = s.table.fwds ∧
    (avail = true → s.isLinux = true)
  | .run spec, .run res =>
    match validateSpecPure spec with
    | .error _ =>
      s' = s ∧
      match res with
      | .ok _ => False
      | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
    | .ok valid =>
      s'.table.plans.length ≤ s.table.plans.length + 1 ∧
      s'.table.boxes.length ≤ s.table.boxes.length + 1 ∧
      s'.table.fwds.length ≤ s.table.fwds.length + 1 ∧
      (valid.portForwards.isEmpty = true → s'.table.fwds = s.table.fwds) ∧
      match res with
      | .ok boxRes =>
        s.isLinux = true ∧
        (decodeHostAuditArch (detectHostAuditArch s.isLinux s.target)).isOk = true ∧
        outcomeNonNeg boxRes.outcome ∧
        (∀ m, valid.limits.maxOutputBytes = some m → boxRes.stdout.size + boxRes.stderr.size ≤ m)
      | .error err =>
        err.message ≠ "" ∧
        (s.isLinux = false →
          err.kind = .unavailable ∧ tableCounts s'.table = tableCounts s.table) ∧
        ((decodeHostAuditArch (detectHostAuditArch s.isLinux s.target)).isOk = false →
          err.kind = .unavailable ∧ tableCounts s'.table = tableCounts s.table)
  | _, _ => False

end LeanSwe.ProcessSandbox.Model

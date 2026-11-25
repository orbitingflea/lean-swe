import Core.Obeys
import LeanSwe.PostFork.Model.Refines
import LeanSwe.PostFork.Proofs.Base
import LeanSwe.PostFork.Proofs.FdOps
import LeanSwe.PostFork.Proofs.FdOpsClose
import LeanSwe.PostFork.Proofs.PureAndWire
import LeanSwe.PostFork.Proofs.IoAndReport
import LeanSwe.PostFork.Proofs.ChildCommon
import LeanSwe.PostFork.Proofs.RunChildPre
import LeanSwe.PostFork.Proofs.RunChild
import LeanSwe.PostFork.Proofs.HostOrchBase
import LeanSwe.PostFork.Proofs.HostOrch
import LeanSwe.PostFork.Proofs.CleanApiRefinement
import LeanSwe.PostFork.Proofs.ObeysHelpers
import LeanSwe.PostFork.Proofs.ObeysModel

/-!
# PostFork Kernel Proof Suite Barrel

Re-exports all modular proof suites covering the `LeanSwe.PostFork` crate,
abstract Linux kernel world model, host orchestrator, `SpecTests.lean` promises,
and canonical `obeys_model` capability refinement (`Core.ObeysStepFrom`).
-/

namespace LeanSwe.PostFork.Proofs

open LeanSwe.PostFork
open LeanSwe.PostFork.Model

/-- Canonical `Core.ObeysStepFrom` capability refinement for `LeanSwe.PostFork`,
covering `Impl.Internal.mkHostOpsM` and all 4 public `Interface` operations (`spawn`,
`spawnWithBarrier`, `releaseBarrier`, `abortBarrier`) over `Model.HostStepState`. -/
theorem obeys_model :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Impl.Internal.mkHostOpsM Model.execPkgStep Model.allowedPkgStep :=
  obeysStepFrom_postfork

/-- Non-vacuity witness showing both `Model.rawStepWf` and the raw `PosixHostOpsM`
contract in `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ s : Model.HostStepState, Model.rawStepWf s = true) ∧
    (∃ raw : Model.RawHostOpsM (StateM Model.HostStepState),
      Core.ObeysStep id Model.rawStepWf (Model.execRawStep raw) Model.allowedRawStep) :=
  ⟨⟨{}, rfl⟩, ⟨Model.modelRawOps, modelRawOps_obeys_allowedRawStep⟩⟩

end LeanSwe.PostFork.Proofs

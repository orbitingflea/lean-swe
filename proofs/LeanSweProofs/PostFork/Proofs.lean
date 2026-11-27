import Core.Obeys
import LeanSweProofs.PostFork.Model.Refines
import LeanSweProofs.PostFork.Proofs.Base
import LeanSweProofs.PostFork.Proofs.FdOps
import LeanSweProofs.PostFork.Proofs.FdOpsClose
import LeanSweProofs.PostFork.Proofs.PureAndWire
import LeanSweProofs.PostFork.Proofs.IoAndReport
import LeanSweProofs.PostFork.Proofs.ChildCommon
import LeanSweProofs.PostFork.Proofs.RunChildPre
import LeanSweProofs.PostFork.Proofs.RunChild
import LeanSweProofs.PostFork.Proofs.HostOrchBase
import LeanSweProofs.PostFork.Proofs.HostOrch
import LeanSweProofs.PostFork.Proofs.CleanApiRefinement
import LeanSweProofs.PostFork.Proofs.ObeysHelpers
import LeanSweProofs.PostFork.Proofs.ObeysModel

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

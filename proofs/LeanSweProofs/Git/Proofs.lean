import Core.Obeys
import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSweProofs.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests
import LeanSweProofs.Git.Proofs.ParserProofs
import LeanSweProofs.Git.Proofs.ImpossibleBase
import LeanSweProofs.Git.Proofs.ImpossibleProofs
import LeanSweProofs.Git.Proofs.DagProofs
import LeanSweProofs.Git.Proofs.ApiProofs
import LeanSweProofs.Git.Proofs.BridgeProofs
import LeanSweProofs.Git.Proofs.IsolationProofs
import LeanSweProofs.Git.Proofs.MutationDelegationProofs
import LeanSweProofs.Git.Proofs.FlagCoverageProofs
import LeanSweProofs.Git.Proofs.SemanticsProofs
import LeanSweProofs.Git.Proofs.GuardsProofs
import LeanSweProofs.Git.Proofs.WorktreeAndRevGuardsProofs
import LeanSweProofs.Git.Proofs.ObeysBase
import LeanSweProofs.Git.Proofs.ObeysParsers
import LeanSweProofs.Git.Proofs.ObeysQueryOps1
import LeanSweProofs.Git.Proofs.ObeysQueryOps2
import LeanSweProofs.Git.Proofs.ObeysMutOps1
import LeanSweProofs.Git.Proofs.ObeysMutOps2
import LeanSweProofs.Git.Proofs.ObeysWitness

/-!
Top-level umbrella verification module for `LeanSwe.Git`. Re-exports all specification
proofs (`AllPass`, `CanReach`, and `.provedImpossible`) and exposes the canonical
`obeys_model` theorem over `LeanSwe.EnvVars.Model` and `LeanSwe.Process.Model`
alongside `obeys_model_nonvacuous`.
-/

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Full public `Interface` refinement (`Core.ObeysPureEq`, `Core.ObeysPureEq2`, and
`Core.ObeysStepFromFinally`) of `LeanSwe.Git` (`mapEnvVarsError`, `mapProcessError`,
`Impl.mkApiFromCapsM`, and all 26 operations of `GitApiM`) over `GitHostState`
(`LeanSwe.EnvVars.Model` + `LeanSwe.Process.Model`). -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.Git.mapEnvVarsError Model.mapEnvVarsErrorModel ∧
    Core.ObeysPureEq2 LeanSwe.Git.mapProcessError Model.mapProcessErrorModel ∧
    Core.ObeysStepFromFinally id Model.hostStepWf
      Model.execCapsStep Model.allowedHostCapsStep
      Model.hostStepWf Impl.mkApiFromCapsM
      Model.execPkgStep Model.allowedPkgStep :=
  ⟨fun _ => rfl, fun _ _ => rfl, obeysStepFromFinally_mkApiFromCapsM⟩

/-- Non-vacuity witness showing `allowedHostCapsStep` in `obeys_model` is inhabited. -/
theorem obeys_model_nonvacuous :
    ∃ caps : Model.GitHostCapsM (StateM Model.GitHostState),
      Core.ObeysStep id Model.hostStepWf
        (Model.execCapsStep caps) Model.allowedHostCapsStep :=
  ⟨modelHostCaps, modelHostCaps_obeys_allowedHostCapsStep⟩

end LeanSwe.Git.Proofs

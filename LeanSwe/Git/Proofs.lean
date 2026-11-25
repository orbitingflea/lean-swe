import Core.Obeys
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests
import LeanSwe.Git.Proofs.ParserProofs
import LeanSwe.Git.Proofs.ImpossibleBase
import LeanSwe.Git.Proofs.ImpossibleProofs
import LeanSwe.Git.Proofs.DagProofs
import LeanSwe.Git.Proofs.ApiProofs
import LeanSwe.Git.Proofs.BridgeProofs
import LeanSwe.Git.Proofs.IsolationProofs
import LeanSwe.Git.Proofs.MutationDelegationProofs
import LeanSwe.Git.Proofs.FlagCoverageProofs
import LeanSwe.Git.Proofs.SemanticsProofs
import LeanSwe.Git.Proofs.GuardsProofs
import LeanSwe.Git.Proofs.WorktreeAndRevGuardsProofs
import LeanSwe.Git.Proofs.ObeysBase
import LeanSwe.Git.Proofs.ObeysParsers
import LeanSwe.Git.Proofs.ObeysQueryOps1
import LeanSwe.Git.Proofs.ObeysQueryOps2
import LeanSwe.Git.Proofs.ObeysMutOps1
import LeanSwe.Git.Proofs.ObeysMutOps2
import LeanSwe.Git.Proofs.ObeysWitness

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

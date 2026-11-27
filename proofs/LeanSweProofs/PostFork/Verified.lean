import LeanSweProofs.PostFork.Aeneas.TypesExternal
import LeanSweProofs.PostFork.Aeneas.Types
import LeanSweProofs.PostFork.Aeneas.Model.World
import LeanSweProofs.PostFork.Aeneas.Model.Sys
import LeanSweProofs.PostFork.Aeneas.Model
import LeanSweProofs.PostFork.Aeneas.FunsExternal
import LeanSweProofs.PostFork.Aeneas.Funs
import LeanSweProofs.PostFork.Aeneas.Api
import LeanSweProofs.PostFork.SpecTests
import LeanSweProofs.PostFork.SpecMutants
import LeanSweProofs.PostFork.Proofs.Base
import LeanSweProofs.PostFork.Proofs.FdOps
import LeanSweProofs.PostFork.Proofs.FdOpsClose
import LeanSweProofs.PostFork.Proofs.PureAndWire
import LeanSweProofs.PostFork.Proofs.IoAndReport
import LeanSweProofs.PostFork.Proofs.ChildCommon
import LeanSweProofs.PostFork.Proofs.RunChildPre
import LeanSweProofs.PostFork.Proofs.RunChild
import LeanSweProofs.PostFork.Model.Refines
import LeanSweProofs.PostFork.Proofs.HostOrchBase
import LeanSweProofs.PostFork.Proofs.HostOrch
import LeanSweProofs.PostFork.Proofs.CleanApiRefinement
import LeanSweProofs.PostFork.Proofs.ObeysHelpers
import LeanSweProofs.PostFork.Proofs.ObeysModel
import LeanSweProofs.PostFork.Proofs

/-!
# PostFork Aeneas & Proof Verification Root

Standalone verification root importing the Aeneas-generated `PostFork` bindings,
`SpecTests`, `SpecMutants`, and modular kernel proof suites so that `import LeanSwe`
remains free of `Aeneas` and `Mathlib`.
-/

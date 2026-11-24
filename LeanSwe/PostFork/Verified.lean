import LeanSwe.PostFork.Aeneas.TypesExternal
import LeanSwe.PostFork.Aeneas.Types
import LeanSwe.PostFork.Aeneas.Model.World
import LeanSwe.PostFork.Aeneas.Model.Sys
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.FunsExternal
import LeanSwe.PostFork.Aeneas.Funs
import LeanSwe.PostFork.Aeneas.Api
import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.SpecMutants
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
import LeanSwe.PostFork.Proofs

/-!
# PostFork Aeneas & Proof Verification Root

Standalone verification root importing the Aeneas-generated `PostFork` bindings,
`SpecTests`, `SpecMutants`, and modular kernel proof suites so that `import LeanSwe`
remains free of `Aeneas` and `Mathlib`.
-/

import LeanSwe.EnvVars.Types
import LeanSwe.Process.Types
import LeanSwe.Git.Types

/-!
Internal host-capability container shape shared between `LeanSwe.Git.Impl`
and `LeanSwe.Git.Model.Refines`.
-/

namespace LeanSwe.Git.Internal

open LeanSwe.EnvVars
open LeanSwe.Process

/-- Pure capability container bundling `EnvVarsApiM m` and `ProcessApiM m` for `LeanSwe.Git`. -/
structure GitHostCapsM (m : Type → Type) where
  /-- Inherited environment capability (`LeanSwe.EnvVars`). -/
  env : EnvVarsApiM m
  /-- Subprocess execution capability (`LeanSwe.Process`). -/
  proc : ProcessApiM m

end LeanSwe.Git.Internal

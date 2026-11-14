import LeanSwe.Glob.Types
import LeanSwe.Glob.Impl

/-!
# Glob Package Interface

Public entry point for `LeanSwe.Glob`. Exposes `GlobErrorKind`, `GlobError`, and
`GlobApi` from `LeanSwe.Glob.Types`, exports top-level glob operations
(`Glob.validate`, `Glob.isMatch`, `Glob.filter`, `Glob.countMatches`, `Glob.escape`),
and provides `defaultApi` for parameterized `SpecTests` and `Proofs`.
-/

namespace LeanSwe.Glob

/-- Validate glob pattern syntax without matching against a path. -/
@[inline] def validate (pattern : String) : Except GlobError Unit :=
  Internal.validate pattern

/-- Return `true` iff `pattern` matches slash-separated `path`. -/
@[inline] def isMatch (pattern path : String) : Except GlobError Bool :=
  Internal.isMatch pattern path

/-- Filter `paths` in order, keeping elements matching `pattern`. -/
@[inline] def filter (pattern : String) (paths : Array String) : Except GlobError (Array String) :=
  Internal.filter pattern paths

/-- Count elements of `paths` matching `pattern`. -/
@[inline] def countMatches (pattern : String) (paths : Array String) : Except GlobError Nat :=
  Internal.countMatches pattern paths

/-- Escape glob metacharacters (`*`, `?`, `[`, `]`, `\`) while preserving `/` separators. -/
@[inline] def escape (literal : String) : String :=
  Internal.escape literal

/-- Default `GlobApi` record bundling concrete glob operations for `SpecTests` and `Proofs`. -/
def defaultApi : GlobApi :=
  { validate := validate
    isMatch := isMatch
    filter := filter
    countMatches := countMatches
    escape := escape }

end LeanSwe.Glob

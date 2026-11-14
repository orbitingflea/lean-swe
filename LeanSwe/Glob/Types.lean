namespace LeanSwe.Glob

/-- Classification of glob pattern syntax failures. -/
inductive GlobErrorKind where
  /-- A `[` character class was opened without a closing `]`. -/
  | unclosedClass
  /-- A character class `[]` or `[!]` contained no characters or ranges. -/
  | emptyClass
  /-- A character range `[lo-hi]` had `lo > hi`. -/
  | invalidRange
  /-- A trailing backslash `\` appeared with no character to escape. -/
  | trailingEscape
  deriving Repr, BEq, DecidableEq

/-- Typed error returned when parsing or validating a glob pattern fails. -/
structure GlobError where
  /-- Machine-checkable error category. -/
  kind : GlobErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Public operations exported by `LeanSwe.Glob`. -/
structure GlobApi where
  /-- Validate glob pattern syntax without matching against a path. -/
  validate : String → Except GlobError Unit
  /-- Return `true` iff `pattern` matches slash-separated `path`. -/
  isMatch : String → String → Except GlobError Bool
  /-- Filter `paths` in order, keeping elements matching `pattern` (or erroring on invalid `pattern`). -/
  filter : String → Array String → Except GlobError (Array String)
  /-- Count elements of `paths` matching `pattern` (or erroring on invalid `pattern`). -/
  countMatches : String → Array String → Except GlobError Nat
  /-- Escape glob metacharacters (`*`, `?`, `[`, `]`, `\`) while preserving `/` separators. -/
  escape : String → String

end LeanSwe.Glob

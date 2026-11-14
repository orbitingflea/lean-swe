import LeanSwe.RegExp.Types
import LeanSwe.RegExp.Impl

/-!
# Regex Package Interface

Public entry point for `LeanSwe.RegExp`. Exposes `RegexErrorKind`, `RegexError`,
`MatchSpan`, and `RegexApi` from `LeanSwe.RegExp.Types`, exports top-level regex
operations (`RegExp.testPattern`, `RegExp.findFirst`, etc.), and provides `defaultApi`
for parameterized `SpecTests` and `Proofs`. Callers import only this module.
-/

namespace LeanSwe.RegExp

/-- Return `true` iff `pattern` matches any substring of `haystack`. -/
@[inline] def testPattern (pattern haystack : String) : Except RegexError Bool :=
  Internal.testPattern pattern haystack

/-- Return the first matched span in `haystack`, or `none` if no match exists. -/
@[inline] def findFirst (pattern haystack : String) : Except RegexError (Option MatchSpan) :=
  Internal.findFirst pattern haystack

/-- Return all non-overlapping matches in `haystack`. -/
@[inline] def findAll (pattern haystack : String) : Except RegexError (Array MatchSpan) :=
  Internal.findAll pattern haystack

/-- Count non-overlapping matches in `haystack`. -/
@[inline] def countMatches (pattern haystack : String) : Except RegexError Nat :=
  Internal.countMatches pattern haystack

/-- Replace every match in `haystack` with `replacement`. -/
@[inline] def replaceAll (pattern haystack replacement : String) : Except RegexError String :=
  Internal.replaceAll pattern haystack replacement

/-- Split `haystack` around every match, always returning at least one piece. -/
@[inline] def splitBy (pattern haystack : String) : Except RegexError (Array String) :=
  Internal.splitBy pattern haystack

/-- Default `RegexApi` record bundling the concrete regex operations for `SpecTests` and `Proofs`. -/
def defaultApi : RegexApi :=
  { testPattern := testPattern
    findFirst := findFirst
    findAll := findAll
    countMatches := countMatches
    replaceAll := replaceAll
    splitBy := splitBy }

end LeanSwe.RegExp

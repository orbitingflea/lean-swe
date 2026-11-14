import Regex
import LeanSwe.RegExp.Types

namespace LeanSwe.RegExp.Internal

open LeanSwe.RegExp (RegexErrorKind RegexError MatchSpan)

/-- Map upstream regex parser errors to `RegexErrorKind`. -/
def mapErrorKind : _root_.Regex.Syntax.Parser.Error → RegexErrorKind
  | .unexpectedEof => .unexpectedEof
  | _ => .invalidSyntax

/-- Wrap an upstream regex parser error as a `RegexError`. -/
def mapError (err : _root_.Regex.Syntax.Parser.Error) : RegexError :=
  { kind := mapErrorKind err
    message := toString err }

/-- Parse a regex pattern into an upstream compiled `Regex`. -/
def compilePattern (pattern : String) : Except RegexError _root_.Regex :=
  match _root_.Regex.parse pattern with
  | .ok re => .ok re
  | .error err => .error (mapError err)

/-- Convert an upstream `String.Slice` match into a public `MatchSpan`. -/
def sliceToSpan (s : String.Slice) : MatchSpan :=
  { matched := s.copy
    startByte := s.startInclusive.offset.byteIdx
    stopByte := s.endExclusive.offset.byteIdx }

/-- Return `true` iff `pattern` matches any substring of `haystack`. -/
def testPattern (pattern haystack : String) : Except RegexError Bool := do
  let re ← compilePattern pattern
  return re.test haystack

/-- Return the first matched span in `haystack`, or `none` if no match exists. -/
def findFirst (pattern haystack : String) : Except RegexError (Option MatchSpan) := do
  let re ← compilePattern pattern
  return (re.find haystack).map sliceToSpan

/-- Return all non-overlapping matches in `haystack`. -/
def findAll (pattern haystack : String) : Except RegexError (Array MatchSpan) := do
  let re ← compilePattern pattern
  return (re.findAll haystack).map sliceToSpan

/-- Count non-overlapping matches in `haystack`. -/
def countMatches (pattern haystack : String) : Except RegexError Nat := do
  let re ← compilePattern pattern
  return re.count haystack

/-- Replace every match in `haystack` with `replacement`. -/
def replaceAll (pattern haystack replacement : String) : Except RegexError String := do
  let re ← compilePattern pattern
  return re.replaceAll haystack replacement

/-- Split `haystack` around every match, always returning at least one piece. -/
def splitBy (pattern haystack : String) : Except RegexError (Array String) := do
  let re ← compilePattern pattern
  return (re.split haystack).map (·.copy)

end LeanSwe.RegExp.Internal

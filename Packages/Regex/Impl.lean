import Regex
import Packages.Regex.Interface

/-!
# Regex Package Implementation

Implements `Packages.Regex.RegexApi` on top of `pandaman64/lean-regex`.
-/

namespace Packages.Regex

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

/-- Concrete `RegexApi` backed by `pandaman64/lean-regex`. -/
def liveApi : RegexApi :=
  { testPattern := fun pattern haystack => do
      let re ← compilePattern pattern
      return re.test haystack
    findFirst := fun pattern haystack => do
      let re ← compilePattern pattern
      return (re.find haystack).map sliceToSpan
    findAll := fun pattern haystack => do
      let re ← compilePattern pattern
      return (re.findAll haystack).map sliceToSpan
    countMatches := fun pattern haystack => do
      let re ← compilePattern pattern
      return re.count haystack
    replaceAll := fun pattern haystack replacement => do
      let re ← compilePattern pattern
      return re.replaceAll haystack replacement
    splitBy := fun pattern haystack => do
      let re ← compilePattern pattern
      return (re.split haystack).map (·.copy) }

end Packages.Regex

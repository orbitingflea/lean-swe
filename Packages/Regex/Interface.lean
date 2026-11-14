/-!
# Regex Package Interface

Public data types, error enum, and exported API for `Packages.Regex`.
Specifications in `SpecTests` depend only on this interface, while callers import
`Packages.Regex.Impl` for `liveApi` without referencing upstream `Regex` internals directly.
-/

namespace Packages.Regex

/-- Classification of regex compilation failures. -/
inductive RegexErrorKind where
  /-- Every parser failure except premature EOF (e.g. unexpected character, invalid range, bad repetition, or unsupported class). -/
  | invalidSyntax
  /-- Pattern terminated prematurely while expecting closing delimiter or escape. -/
  | unexpectedEof
  deriving Repr, BEq, DecidableEq

/-- Typed error returned when parsing a regex pattern fails. -/
structure RegexError where
  /-- Machine-checkable error category. -/
  kind : RegexErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Matched substring together with UTF-8 byte bounds `[startByte, stopByte)` inside haystack. -/
structure MatchSpan where
  /-- Copy of the matched substring. -/
  matched : String
  /-- Inclusive UTF-8 byte start offset in the searched string. -/
  startByte : Nat
  /-- Exclusive UTF-8 byte end offset in the searched string. -/
  stopByte : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public operations exported by `Packages.Regex`. -/
structure RegexApi where
  /-- Return `true` iff `pattern` matches any substring of `haystack`. -/
  testPattern : String → String → Except RegexError Bool
  /-- Return the first matched span in `haystack`, or `none` if no match exists. -/
  findFirst : String → String → Except RegexError (Option MatchSpan)
  /-- Return all non-overlapping matches in `haystack`. -/
  findAll : String → String → Except RegexError (Array MatchSpan)
  /-- Count non-overlapping matches in `haystack`. -/
  countMatches : String → String → Except RegexError Nat
  /-- Replace every match in `haystack` with `replacement`. -/
  replaceAll : String → String → String → Except RegexError String
  /-- Split `haystack` around every match, always returning at least one piece. -/
  splitBy : String → String → Except RegexError (Array String)

end Packages.Regex

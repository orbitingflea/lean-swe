import LeanSwe.Glob.Types

/-!
# Glob Package Internal Implementation

Total, pure-Lean implementation of slash-separated path globbing (`*`, `?`, `[...]` /
`[!...]`, `\` escapes, and `**` segment wildcards). Kept under `namespace LeanSwe.Glob.Internal`
so `open LeanSwe.Glob` does not expose parser or AST helpers.
-/

namespace LeanSwe.Glob.Internal

open LeanSwe.Glob (GlobErrorKind GlobError)

/-- An item inside a `[...]` character class. -/
inductive CharClassItem where
  /-- Matches a single character `c`. -/
  | single (c : Char)
  /-- Matches any character `x` with `lo ≤ x ∧ x ≤ hi`. -/
  | range (lo hi : Char)
  deriving Repr, BEq, DecidableEq

/-- Parsed `[...]` or `[!...]` character class. -/
structure CharClass where
  /-- `true` if class starts with `!`. -/
  negated : Bool
  /-- Non-empty list of class items. -/
  items : List CharClassItem
  deriving Repr, BEq, DecidableEq

/-- Atomic matcher within a single `/` path segment. -/
inductive SegAtom where
  /-- Literal character match. -/
  | lit (c : Char)
  /-- Single-character wildcard (`?`). -/
  | anyChar
  /-- Zero-or-more-character wildcard (`*`). -/
  | star
  /-- Bracket character class (`[...]` / `[!...]`). -/
  | charClass (cc : CharClass)
  deriving Repr, BEq, DecidableEq

/-- Parsed representation of one `/` path segment in a glob pattern. -/
inductive SegmentPat where
  /-- Recursive zero-or-more segment wildcard (`**`). -/
  | globStar
  /-- Sequence of intra-segment atoms. -/
  | atoms (xs : List SegAtom)
  deriving Repr, BEq, DecidableEq

/-- Error returned when a `[` character class lacks a closing `]`. -/
def classUnclosedErr : GlobError :=
  { kind := .unclosedClass, message := "unclosed '[' character class in glob pattern" }

/-- Error returned when a character class `[]` or `[!]` is empty. -/
def classEmptyErr : GlobError :=
  { kind := .emptyClass, message := "empty '[]' character class in glob pattern" }

/-- Error returned when a trailing backslash appears with no character to escape. -/
def trailingEscapeErr : GlobError :=
  { kind := .trailingEscape, message := "trailing escape '\\' in glob pattern" }

/-- Error returned when `[lo-hi]` has `lo > hi`. -/
def invalidRangeErr (lo hi : Char) : GlobError :=
  { kind := .invalidRange
    message := s!"invalid character range '{lo}-{hi}' in glob pattern" }

/-- Split a character list on `sep`, always producing at least one segment. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then
      [] :: splitOnChar sep cs
    else
      match splitOnChar sep cs with
      | [] => [[c]]
      | seg :: rest => (c :: seg) :: rest

/-- Read one possibly escaped character inside `[...]` and prove the tail strictly shrinks. -/
def readClassAtom :
    (cs : List Char) → Except GlobError (Char × { r : List Char // r.length < cs.length })
  | [] => .error classUnclosedErr
  | '\\' :: [] => .error trailingEscapeErr
  | '\\' :: c :: rest => .ok (c, ⟨rest, by simp; omega⟩)
  | c :: rest => .ok (c, ⟨rest, by simp⟩)

/-- Parse items and closing `]` inside a character class. -/
def parseClassItems :
    (cs : List Char) → List CharClassItem →
      Except GlobError (List CharClassItem × { r : List Char // r.length ≤ cs.length })
  | [], _ => .error classUnclosedErr
  | ']' :: rest, acc =>
    if acc.isEmpty then .error classEmptyErr
    else .ok (acc.reverse, ⟨rest, by simp⟩)
  | c :: rest, acc => do
    let (lo, ⟨afterLo, hLo⟩) ← readClassAtom (c :: rest)
    match afterLo with
    | '-' :: ']' :: tail =>
      .ok ((.single '-' :: .single lo :: acc).reverse,
        ⟨tail, by simp only [List.length_cons] at hLo ⊢; omega⟩)
    | '-' :: rest2 =>
      let (hi, ⟨afterHi, hHi⟩) ← readClassAtom rest2
      have hSub : afterHi.length < (c :: rest).length := by
        simp only [List.length_cons] at hLo ⊢; omega
      if lo ≤ hi then
        let ⟨items, ⟨r, hr⟩⟩ ← parseClassItems afterHi (.range lo hi :: acc)
        return (items, ⟨r, by omega⟩)
      else
        .error (invalidRangeErr lo hi)
    | rest1 =>
      let ⟨items, ⟨r, hr⟩⟩ ← parseClassItems rest1 (.single lo :: acc)
      return (items, ⟨r, by omega⟩)
termination_by cs _ => cs.length

/-- Parse the interior and closing `]` of a character class after `[`. -/
def parseCharClass (cs : List Char) :
    Except GlobError (CharClass × { r : List Char // r.length ≤ cs.length }) :=
  match cs with
  | '!' :: rest => do
    let (items, ⟨r, hr⟩) ← parseClassItems rest []
    return ({ negated := true, items }, ⟨r, by simp; omega⟩)
  | other => do
    let (items, ⟨r, hr⟩) ← parseClassItems other []
    return ({ negated := false, items }, ⟨r, hr⟩)

/-- Parse one `/` segment's characters into intra-segment atoms (collapsing adjacent `*`). -/
def parseAtoms : (cs : List Char) → Except GlobError (List SegAtom)
  | [] => .ok []
  | '\\' :: [] => .error trailingEscapeErr
  | '\\' :: c :: rest => do
    let tail ← parseAtoms rest
    return .lit c :: tail
  | '*' :: rest => do
    let tail ← parseAtoms rest
    match tail with
    | .star :: _ => return tail
    | _ => return .star :: tail
  | '?' :: rest => do
    let tail ← parseAtoms rest
    return .anyChar :: tail
  | '[' :: rest => do
    let (cc, ⟨after, _⟩) ← parseCharClass rest
    let tail ← parseAtoms after
    return .charClass cc :: tail
  | c :: rest => do
    let tail ← parseAtoms rest
    return .lit c :: tail
termination_by cs => cs.length

/-- Parse one `/` segment into either `.globStar` (`**`) or intra-segment atoms. -/
def parseSegment (seg : List Char) : Except GlobError SegmentPat :=
  if seg == ['*', '*'] then
    .ok .globStar
  else
    (parseAtoms seg).map .atoms

/-- Parse all `/` segments in `segs`, coalescing consecutive `globStar` segments. -/
def parseSegList : List (List Char) → Except GlobError (List SegmentPat)
  | [] => .ok []
  | seg :: rest => do
    let p ← parseSegment seg
    let ps ← parseSegList rest
    match p, ps with
    | .globStar, .globStar :: _ => return ps
    | _, _ => return p :: ps

/-- Parse a full glob pattern string into slash-separated segment patterns. -/
def compilePattern (pattern : String) : Except GlobError (List SegmentPat) :=
  parseSegList (splitOnChar '/' pattern.toList)

/-- Test whether `c` satisfies any item in `items`. -/
def matchClassItems (c : Char) : List CharClassItem → Bool
  | [] => false
  | .single x :: rest => (x == c) || matchClassItems c rest
  | .range lo hi :: rest => (decide (lo ≤ c) && decide (c ≤ hi)) || matchClassItems c rest

/-- Test whether `c` matches parsed character class `cc`. -/
def matchCharClass (cc : CharClass) (c : Char) : Bool :=
  let hit := matchClassItems c cc.items
  if cc.negated then !hit else hit

/-- Match parsed intra-segment atoms against characters of a single path segment. -/
def matchSegAtoms : List SegAtom → List Char → Bool
  | [], [] => true
  | .star :: atoms, [] => matchSegAtoms atoms []
  | .star :: atoms, c :: cs =>
    matchSegAtoms atoms (c :: cs) || matchSegAtoms (.star :: atoms) cs
  | _ :: _, [] => false
  | [], _ :: _ => false
  | .lit p :: atoms, c :: cs => (p == c) && matchSegAtoms atoms cs
  | .anyChar :: atoms, _ :: cs => matchSegAtoms atoms cs
  | .charClass cc :: atoms, c :: cs => matchCharClass cc c && matchSegAtoms atoms cs
termination_by atoms cs => (atoms.length, cs.length)

/-- Match compiled segment patterns against slash-separated path segments. -/
def matchSegPats : List SegmentPat → List (List Char) → Bool
  | [], [] => true
  | .globStar :: pats, [] => matchSegPats pats []
  | .globStar :: pats, s :: ss =>
    matchSegPats pats (s :: ss) || matchSegPats (.globStar :: pats) ss
  | _ :: _, [] => false
  | [], _ :: _ => false
  | .atoms a :: pats, s :: ss =>
    matchSegAtoms a s && matchSegPats pats ss
termination_by pats segs => (pats.length, segs.length)

/-- Filter `paths` against an already-compiled pattern `pats`. -/
def filterCompiled (pats : List SegmentPat) (paths : Array String) : Array String :=
  paths.filter fun p => matchSegPats pats (splitOnChar '/' p.toList)

/-- Escape glob metacharacters in `cs` while leaving `/` intact. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == '*' || c == '?' || c == '[' || c == ']' || c == '\\' then
      '\\' :: c :: escapeChars cs
    else
      c :: escapeChars cs

/-- Validate glob pattern syntax without matching against a path. -/
def validate (pattern : String) : Except GlobError Unit := do
  let _ ← compilePattern pattern
  return ()

/-- Return `true` iff `pattern` matches slash-separated `path`. -/
def isMatch (pattern path : String) : Except GlobError Bool := do
  let pats ← compilePattern pattern
  return matchSegPats pats (splitOnChar '/' path.toList)

/-- Filter `paths` in order, keeping elements matching `pattern`. -/
def filter (pattern : String) (paths : Array String) : Except GlobError (Array String) := do
  let pats ← compilePattern pattern
  return filterCompiled pats paths

/-- Count elements of `paths` matching `pattern`. -/
def countMatches (pattern : String) (paths : Array String) : Except GlobError Nat := do
  let kept ← filter pattern paths
  return kept.size

/-- Escape glob metacharacters (`*`, `?`, `[`, `]`, `\`) while preserving `/` separators. -/
def escape (literal : String) : String :=
  String.ofList (escapeChars literal.toList)

end LeanSwe.Glob.Internal

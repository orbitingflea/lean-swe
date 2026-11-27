import LeanSwe.Glob.Types

namespace LeanSwe.Glob.Model

open LeanSwe.Glob (GlobErrorKind)

/-- One item inside a glob `[...]` character class. -/
inductive ClassItem where
  /-- Matches the exact character `c`. -/
  | single (c : Char)
  /-- Matches any character `x` with `lo ≤ x` and `x ≤ hi`. -/
  | range (lo hi : Char)
  deriving Repr, BEq, DecidableEq

/-- Parsed `[...]` or `[!...]` glob character class. -/
structure CharClass where
  /-- Whether the class is negated via leading `!`. -/
  negated : Bool
  /-- Character and range entries inside the class. -/
  items : List ClassItem
  deriving Repr, BEq, DecidableEq

/-- One atomic matcher within a single `/` path segment. -/
inductive Atom where
  /-- Literal character match. -/
  | lit (c : Char)
  /-- Single-character intra-segment wildcard (`?`). -/
  | any
  /-- Zero-or-more-character intra-segment wildcard (`*`). -/
  | star
  /-- Bracket character class (`[...]` or `[!...]`). -/
  | charClass (cc : CharClass)
  deriving Repr, BEq, DecidableEq

/-- One `/` segment in a parsed glob pattern. -/
inductive Segment where
  /-- Recursive zero-or-more path-segment wildcard (`**`). -/
  | globStar
  /-- Sequence of intra-segment atoms. -/
  | atoms (xs : List Atom)
  deriving Repr, BEq, DecidableEq

/-- Split `cs` at every `'/'` separator, always producing at least one segment. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == '/' then
      [] :: splitSlash cs
    else
      match splitSlash cs with
      | [] => [[c]]
      | seg :: rest => (c :: seg) :: rest

mutual
  /-- Parse one `/` segment's characters into intra-segment glob atoms. -/
  def parseAtoms : List Char → Except GlobErrorKind (List Atom)
    | [] => .ok []
    | '\\' :: [] => .error .trailingEscape
    | '\\' :: c :: rest => (parseAtoms rest).map (.lit c :: ·)
    | '*' :: rest => (parseAtoms rest).map (.star :: ·)
    | '?' :: rest => (parseAtoms rest).map (.any :: ·)
    | '[' :: '!' :: rest => parseClass true [] rest
    | '[' :: rest => parseClass false [] rest
    | c :: rest => (parseAtoms rest).map (.lit c :: ·)

  /-- Continue parsing a character class after reading item start character `lo`. -/
  def parseClassAfter (neg : Bool) (acc : List ClassItem) (lo : Char) :
      List Char → Except GlobErrorKind (List Atom)
    | [] => .error .unclosedClass
    | '-' :: rest => parseClassRange neg acc lo rest
    | ']' :: rest =>
      (parseAtoms rest).map
        (.charClass { negated := neg, items := (.single lo :: acc).reverse } :: ·)
    | '\\' :: [] => .error .trailingEscape
    | '\\' :: lo2 :: rest => parseClassAfter neg (.single lo :: acc) lo2 rest
    | lo2 :: rest => parseClassAfter neg (.single lo :: acc) lo2 rest

  /-- Parse the upper bound of a character range `lo-hi` (or trailing `lo-]`). -/
  def parseClassRange (neg : Bool) (acc : List ClassItem) (lo : Char) :
      List Char → Except GlobErrorKind (List Atom)
    | [] => .error .unclosedClass
    | ']' :: rest =>
      (parseAtoms rest).map
        (.charClass { negated := neg, items := (.single '-' :: .single lo :: acc).reverse } :: ·)
    | '\\' :: [] => .error .trailingEscape
    | '\\' :: hi :: rest =>
      if lo ≤ hi then parseClass neg (.range lo hi :: acc) rest else .error .invalidRange
    | hi :: rest =>
      if lo ≤ hi then parseClass neg (.range lo hi :: acc) rest else .error .invalidRange

  /-- Parse the interior and closing `']'` of a `[...]` or `[!...]` character class. -/
  def parseClass (neg : Bool) (acc : List ClassItem) : List Char → Except GlobErrorKind (List Atom)
    | [] => .error .unclosedClass
    | ']' :: rest =>
      if acc.isEmpty then .error .emptyClass
      else (parseAtoms rest).map (.charClass { negated := neg, items := acc.reverse } :: ·)
    | '\\' :: [] => .error .trailingEscape
    | '\\' :: lo :: rest => parseClassAfter neg acc lo rest
    | lo :: rest => parseClassAfter neg acc lo rest
end

/-- Parse a single `/` segment into either `.globStar` (`**`) or `.atoms`. -/
def parseSegment (seg : List Char) : Except GlobErrorKind Segment :=
  if seg == ['*', '*'] then
    .ok .globStar
  else
    (parseAtoms seg).map .atoms

/-- Parse a list of `/` segments left-to-right. -/
def parseSegments : List (List Char) → Except GlobErrorKind (List Segment)
  | [] => .ok []
  | seg :: rest => do
    let p ← parseSegment seg
    let ps ← parseSegments rest
    return p :: ps

/-- Parse a glob pattern string into slash-separated segment patterns. -/
def parsePattern (pattern : String) : Except GlobErrorKind (List Segment) :=
  parseSegments (splitSlash pattern.toList)

/-- Test whether `c` matches one `ClassItem`. -/
def classItemMatches (c : Char) : ClassItem → Bool
  | .single x => x == c
  | .range lo hi => decide (lo ≤ c) && decide (c ≤ hi)

/-- Test whether `c` matches character class `cc`. -/
def charClassMatches (cc : CharClass) (c : Char) : Bool :=
  let hit := cc.items.any (classItemMatches c)
  if cc.negated then !hit else hit

/-- Declarative language-membership relation for matching intra-segment atoms against one path segment. -/
inductive MatchSeg : List Atom → List Char → Prop where
  /-- Empty atom list matches the empty segment. -/
  | nil : MatchSeg [] []
  /-- Literal atom matches the exact head character. -/
  | lit (c : Char) {atoms : List Atom} {cs : List Char} :
      MatchSeg atoms cs → MatchSeg (.lit c :: atoms) (c :: cs)
  /-- Single-character wildcard `?` matches any single character. -/
  | any (c : Char) {atoms : List Atom} {cs : List Char} :
      MatchSeg atoms cs → MatchSeg (.any :: atoms) (c :: cs)
  /-- Character class matches any single character accepted by `charClassMatches`. -/
  | charClass {cc : CharClass} {c : Char} {atoms : List Atom} {cs : List Char} :
      charClassMatches cc c = true → MatchSeg atoms cs →
      MatchSeg (.charClass cc :: atoms) (c :: cs)
  /-- Intra-segment wildcard `*` matches any prefix `pre` followed by suffix `suf`. -/
  | star (pre suf : List Char) {atoms : List Atom} :
      MatchSeg atoms suf → MatchSeg (.star :: atoms) (pre ++ suf)

/-- Declarative language-membership relation for matching glob segment patterns against slash-separated path segments. -/
inductive MatchPath : List Segment → List (List Char) → Prop where
  /-- Empty segment pattern list matches empty segment list. -/
  | nil : MatchPath [] []
  /-- An intra-segment pattern matches one path segment. -/
  | seg {atoms : List Atom} {seg : List Char} {pats : List Segment} {rest : List (List Char)} :
      MatchSeg atoms seg → MatchPath pats rest →
      MatchPath (.atoms atoms :: pats) (seg :: rest)
  /-- Recursive `**` wildcard matches zero or more path segments `pre` before `suf`. -/
  | globStar (pre suf : List (List Char)) {pats : List Segment} :
      MatchPath pats suf → MatchPath (.globStar :: pats) (pre ++ suf)

/-- Match a leading `*` against any prefix of `cs` by checking `matchRest` on every suffix. -/
def evalSegStar (matchRest : List Char → Bool) : List Char → Bool
  | [] => matchRest []
  | c :: cs => matchRest (c :: cs) || evalSegStar matchRest cs

/-- Computable decider for `MatchSeg`. -/
def evalSeg : List Atom → List Char → Bool
  | [], [] => true
  | [], _ :: _ => false
  | .star :: atoms, cs => evalSegStar (evalSeg atoms) cs
  | .lit p :: atoms, c :: cs => (p == c) && evalSeg atoms cs
  | .any :: atoms, _ :: cs => evalSeg atoms cs
  | .charClass cc :: atoms, c :: cs => charClassMatches cc c && evalSeg atoms cs
  | _ :: _, [] => false

/-- Match a leading `**` against any prefix of `segs` by checking `matchRest` on every suffix. -/
def evalPathGlobStar (matchRest : List (List Char) → Bool) : List (List Char) → Bool
  | [] => matchRest []
  | s :: ss => matchRest (s :: ss) || evalPathGlobStar matchRest ss

/-- Computable decider for `MatchPath`. -/
def evalPath : List Segment → List (List Char) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | .globStar :: pats, segs => evalPathGlobStar (evalPath pats) segs
  | .atoms a :: pats, s :: ss => evalSeg a s && evalPath pats ss
  | _ :: _, [] => false

private theorem evalSegStar_append (f : List Char → Bool) (pre suf : List Char)
    (h : f suf = true) :
    evalSegStar f (pre ++ suf) = true := by
  induction pre with
  | nil =>
    cases suf with
    | nil => simpa [evalSegStar] using h
    | cons c cs => simp [evalSegStar, h]
  | cons c pre ih =>
    simp [evalSegStar, ih]

private theorem evalSegStar_sound (atoms : List Atom) (cs : List Char)
    (h : evalSegStar (evalSeg atoms) cs = true)
    (ihAtoms : ∀ cs', evalSeg atoms cs' = true → MatchSeg atoms cs') :
    MatchSeg (.star :: atoms) cs := by
  induction cs with
  | nil =>
    simp only [evalSegStar] at h
    exact MatchSeg.star [] [] (ihAtoms [] h)
  | cons c rest ih =>
    simp only [evalSegStar, Bool.or_eq_true] at h
    rcases h with h0 | h1
    · exact MatchSeg.star [] (c :: rest) (ihAtoms (c :: rest) h0)
    · have hm := ih h1
      cases hm with
      | star pre suf hs =>
        exact MatchSeg.star (c :: pre) suf hs

/-- `evalSeg` is sound and complete with respect to declarative `MatchSeg`. -/
theorem evalSeg_eq_true_iff (atoms : List Atom) (cs : List Char) :
    evalSeg atoms cs = true ↔ MatchSeg atoms cs := by
  constructor
  · induction atoms generalizing cs with
    | nil =>
      cases cs with
      | nil => intro _; exact MatchSeg.nil
      | cons _ _ => intro h; simp [evalSeg] at h
    | cons a rest ih =>
      cases a with
      | lit p =>
        cases cs with
        | nil => intro h; simp [evalSeg] at h
        | cons c tl =>
          intro h
          simp only [evalSeg, Bool.and_eq_true, beq_iff_eq] at h
          rcases h with ⟨rfl, htl⟩
          exact MatchSeg.lit p (ih tl htl)
      | any =>
        cases cs with
        | nil => intro h; simp [evalSeg] at h
        | cons c tl =>
          intro h
          simp only [evalSeg] at h
          exact MatchSeg.any c (ih tl h)
      | charClass cc =>
        cases cs with
        | nil => intro h; simp [evalSeg] at h
        | cons c tl =>
          intro h
          simp only [evalSeg, Bool.and_eq_true] at h
          exact MatchSeg.charClass h.1 (ih tl h.2)
      | star =>
        intro h
        exact evalSegStar_sound rest cs h ih
  · intro hm
    induction hm with
    | nil => rfl
    | lit c _ ih => simp [evalSeg, ih]
    | any c _ ih => simp [evalSeg, ih]
    | charClass hc _ ih => simp [evalSeg, hc, ih]
    | star pre suf _ ih => exact evalSegStar_append _ pre suf ih

private theorem evalPathGlobStar_append (f : List (List Char) → Bool) (pre suf : List (List Char))
    (h : f suf = true) :
    evalPathGlobStar f (pre ++ suf) = true := by
  induction pre with
  | nil =>
    cases suf with
    | nil => simpa [evalPathGlobStar] using h
    | cons s ss => simp [evalPathGlobStar, h]
  | cons s pre ih =>
    simp [evalPathGlobStar, ih]

private theorem evalPathGlobStar_sound (pats : List Segment) (segs : List (List Char))
    (h : evalPathGlobStar (evalPath pats) segs = true)
    (ihPats : ∀ segs', evalPath pats segs' = true → MatchPath pats segs') :
    MatchPath (.globStar :: pats) segs := by
  induction segs with
  | nil =>
    simp only [evalPathGlobStar] at h
    exact MatchPath.globStar [] [] (ihPats [] h)
  | cons s rest ih =>
    simp only [evalPathGlobStar, Bool.or_eq_true] at h
    rcases h with h0 | h1
    · exact MatchPath.globStar [] (s :: rest) (ihPats (s :: rest) h0)
    · have hm := ih h1
      cases hm with
      | globStar pre suf hs =>
        exact MatchPath.globStar (s :: pre) suf hs

/-- `evalPath` is sound and complete with respect to declarative `MatchPath`. -/
theorem evalPath_eq_true_iff (pats : List Segment) (segs : List (List Char)) :
    evalPath pats segs = true ↔ MatchPath pats segs := by
  constructor
  · induction pats generalizing segs with
    | nil =>
      cases segs with
      | nil => intro _; exact MatchPath.nil
      | cons _ _ => intro h; simp [evalPath] at h
    | cons p rest ih =>
      cases p with
      | atoms a =>
        cases segs with
        | nil => intro h; simp [evalPath] at h
        | cons s ss =>
          intro h
          simp only [evalPath, Bool.and_eq_true] at h
          exact MatchPath.seg ((evalSeg_eq_true_iff a s).mp h.1) (ih ss h.2)
      | globStar =>
        intro h
        exact evalPathGlobStar_sound rest segs h ih
  · intro hm
    induction hm with
    | nil => rfl
    | seg hseg _ ih =>
      simp [evalPath, (evalSeg_eq_true_iff _ _).mpr hseg, ih]
    | globStar pre suf _ ih => exact evalPathGlobStar_append _ pre suf ih

/-- Reference model for `GlobApi.validate`. -/
def validateModel (pattern : String) : Except GlobErrorKind Unit :=
  (parsePattern pattern).map fun _ => ()

/-- Reference model for `GlobApi.isMatch`. -/
def isMatchModel (pattern path : String) : Except GlobErrorKind Bool :=
  (parsePattern pattern).map fun pats => evalPath pats (splitSlash path.toList)

/-- Reference model for `GlobApi.filter`. -/
def filterModel (pattern : String) (paths : Array String) : Except GlobErrorKind (Array String) :=
  (parsePattern pattern).map fun pats =>
    paths.filter fun p => evalPath pats (splitSlash p.toList)

/-- Reference model for `GlobApi.countMatches`. -/
def countMatchesModel (pattern : String) (paths : Array String) : Except GlobErrorKind Nat :=
  (filterModel pattern paths).map Array.size

/-- Escape glob metacharacters (`*`, `?`, `[`, `]`, `\`) in a character list while preserving `'/'`. -/
def escapeCharsModel : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == '*' || c == '?' || c == '[' || c == ']' || c == '\\' then
      '\\' :: c :: escapeCharsModel cs
    else
      c :: escapeCharsModel cs

/-- Reference model for `GlobApi.escape`. -/
def escapeModel (literal : String) : String :=
  String.ofList (escapeCharsModel literal.toList)

/-- Allowed outcome relation for `Glob.validate` against `validateModel`. -/
def allowedValidate (pattern : String) (out : Except GlobError Unit) : Prop :=
  match out, validateModel pattern with
  | .ok (), .ok () => True
  | .error e, .error k => e.kind = k ∧ e.message ≠ ""
  | _, _ => False

/-- Allowed outcome relation for `Glob.isMatch` against `isMatchModel`. -/
def allowedIsMatch (pattern path : String) (out : Except GlobError Bool) : Prop :=
  match out, isMatchModel pattern path with
  | .ok b1, .ok b2 => b1 = b2
  | .error e, .error k => e.kind = k ∧ e.message ≠ ""
  | _, _ => False

/-- Allowed outcome relation for `Glob.filter` against `filterModel`. -/
def allowedFilter (pattern : String) (paths : Array String) (out : Except GlobError (Array String)) : Prop :=
  match out, filterModel pattern paths with
  | .ok a1, .ok a2 => a1 = a2
  | .error e, .error k => e.kind = k ∧ e.message ≠ ""
  | _, _ => False

/-- Allowed outcome relation for `Glob.countMatches` against `countMatchesModel`. -/
def allowedCountMatches (pattern : String) (paths : Array String) (out : Except GlobError Nat) : Prop :=
  match out, countMatchesModel pattern paths with
  | .ok n1, .ok n2 => n1 = n2
  | .error e, .error k => e.kind = k ∧ e.message ≠ ""
  | _, _ => False

end LeanSwe.Glob.Model

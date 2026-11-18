import LeanSwe.RegExp.Types

namespace LeanSwe.RegExp.Model

open LeanSwe.RegExp (RegexErrorKind MatchSpan)

/-- Check whether `c` is an ASCII decimal digit `[0-9]`. -/
def isDigitChar (c : Char) : Bool :=
  c >= '0' && c <= '9'

/-- Check whether `c` is an ASCII regex word character `[A-Za-z0-9_]`. -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Check whether `c` is an ASCII regex whitespace character. -/
def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- Shorthand character predicate (`\d`, `\D`, `\w`, `\W`, `\s`, `\S`). -/
inductive CharPred where
  /-- ASCII digit `\d`. -/
  | digit
  /-- Non-digit `\D`. -/
  | nonDigit
  /-- Word character `\w`. -/
  | word
  /-- Non-word character `\W`. -/
  | nonWord
  /-- Whitespace character `\s`. -/
  | space
  /-- Non-whitespace character `\S`. -/
  | nonSpace
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Evaluate a shorthand predicate on character `c`. -/
def charPredMatches (p : CharPred) (c : Char) : Bool :=
  match p with
  | .digit => isDigitChar c
  | .nonDigit => !isDigitChar c
  | .word => isWordChar c
  | .nonWord => !isWordChar c
  | .space => isSpaceChar c
  | .nonSpace => !isSpaceChar c

/-- Character matching atom in the reference regex AST. -/
inductive CharAtom where
  /-- Any character except `'\n'`. -/
  | any
  /-- Shorthand predicate (`\d`, `\D`, `\w`, `\W`, `\s`, `\S`). -/
  | pred (p : CharPred)
  /-- Exact literal character. -/
  | literal (c : Char)
  /-- Bracket character class `[...]` or `[^...]`. -/
  | charClass (negated : Bool) (ranges : List (Char × Char)) (preds : List CharPred)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Test whether character `c` matches `atom`. -/
def charAtomMatches (atom : CharAtom) (c : Char) : Bool :=
  match atom with
  | .any => c != '\n'
  | .pred p => charPredMatches p c
  | .literal x => c == x
  | .charClass negated ranges preds =>
    let inRange := ranges.any fun (lo, hi) => lo <= c && c <= hi
    let inPred := preds.any fun p => charPredMatches p c
    let hit := inRange || inPred
    if negated then !hit else hit

/-- Reference abstract syntax tree for regular expressions. -/
inductive Regex where
  /-- Empty expression matching zero characters. -/
  | empty
  /-- Single-character atom matcher. -/
  | char (atom : CharAtom)
  /-- Start-of-string assertion `^`. -/
  | anchorStart
  /-- End-of-string assertion `$`. -/
  | anchorEnd
  /-- Word boundary assertion `\b` (`positive = true`) or `\B` (`positive = false`). -/
  | wordBoundary (positive : Bool)
  /-- Sequential concatenation `lhs` followed by `rhs`. -/
  | seq (lhs rhs : Regex)
  /-- Ordered alternation `lhs | rhs` (`lhs` has higher priority). -/
  | alt (lhs rhs : Regex)
  /-- Repetition `inner{min, max?}` with greedy (`true`) or lazy (`false`) priority. -/
  | rep (inner : Regex) (min : Nat) (max? : Option Nat) (greedy : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Maximum allowed brace repetition count (`{m}`, `{m,}`, `{m,n}`). -/
def maxRepetitionCount : Nat := 1000

/-- Token parsed from an escape sequence inside a `[...]` character class. -/
inductive ClassToken where
  /-- Literal character token. -/
  | single (c : Char)
  /-- Shorthand predicate token (`\d`, `\D`, `\w`, `\W`, `\s`, `\S`). -/
  | pred (p : CharPred)
  deriving Repr, BEq, DecidableEq

/-- Decode the escaped character `c` inside `[...]`. -/
def decodeClassEscape (c : Char) : ClassToken :=
  match c with
  | 'd' => .pred .digit
  | 'D' => .pred .nonDigit
  | 'w' => .pred .word
  | 'W' => .pred .nonWord
  | 's' => .pred .space
  | 'S' => .pred .nonSpace
  | 'n' => .single '\n'
  | 'r' => .single '\r'
  | 't' => .single '\t'
  | _ => .single c

mutual
  /-- Parse body items and closing `']'` of a `[...]` character class. -/
  def parseClassBody (neg : Bool) (ranges : List (Char × Char)) (preds : List CharPred) :
      List Char → Except RegexErrorKind (CharAtom × List Char)
    | [] => .error .unexpectedEof
    | ']' :: rest =>
      if ranges.isEmpty && preds.isEmpty then
        .error .invalidSyntax
      else
        .ok (.charClass neg ranges.reverse preds.reverse, rest)
    | '\\' :: [] => .error .unexpectedEof
    | '\\' :: c :: rest =>
      match decodeClassEscape c with
      | .pred p => parseClassBody neg ranges (p :: preds) rest
      | .single lo => parseClassAfter neg ranges preds lo rest
    | lo :: rest => parseClassAfter neg ranges preds lo rest

  /-- Handle optional `'-'` range continuation after literal character `lo` inside `[...]`. -/
  def parseClassAfter (neg : Bool) (ranges : List (Char × Char)) (preds : List CharPred)
      (lo : Char) : List Char → Except RegexErrorKind (CharAtom × List Char)
    | [] => .error .unexpectedEof
    | ']' :: rest =>
      .ok (.charClass neg ((lo, lo) :: ranges).reverse preds.reverse, rest)
    | '-' :: rest => parseClassRange neg ranges preds lo rest
    | '\\' :: [] => .error .unexpectedEof
    | '\\' :: c :: rest =>
      let ranges' := (lo, lo) :: ranges
      match decodeClassEscape c with
      | .pred p => parseClassBody neg ranges' (p :: preds) rest
      | .single lo2 => parseClassAfter neg ranges' preds lo2 rest
    | lo2 :: rest => parseClassAfter neg ((lo, lo) :: ranges) preds lo2 rest

  /-- Handle upper bound of `lo-hi` (or trailing `lo-]` / `lo-\d`) inside `[...]`. -/
  def parseClassRange (neg : Bool) (ranges : List (Char × Char)) (preds : List CharPred)
      (lo : Char) : List Char → Except RegexErrorKind (CharAtom × List Char)
    | [] => .error .unexpectedEof
    | ']' :: rest =>
      .ok (.charClass neg (('-', '-') :: (lo, lo) :: ranges).reverse preds.reverse, rest)
    | '\\' :: [] => .error .unexpectedEof
    | '\\' :: c :: rest =>
      match decodeClassEscape c with
      | .pred p =>
        parseClassBody neg (('-', '-') :: (lo, lo) :: ranges) (p :: preds) rest
      | .single hi =>
        if lo.toNat > hi.toNat then .error .invalidSyntax
        else parseClassBody neg ((lo, hi) :: ranges) preds rest
    | hi :: rest =>
      if lo.toNat > hi.toNat then .error .invalidSyntax
      else parseClassBody neg ((lo, hi) :: ranges) preds rest
end

/-- Parse a `[...]` or `[^...]` character class immediately after `'['`. -/
def parseCharClass : List Char → Except RegexErrorKind (CharAtom × List Char)
  | '^' :: rest => parseClassBody true [] [] rest
  | other => parseClassBody false [] [] other

/-- Parse consecutive ASCII decimal digits, returning `(value, digitCount, remainder)`. -/
def parseDigits (acc count : Nat) : List Char → Nat × Nat × List Char
  | [] => (acc, count, [])
  | c :: rest =>
    if isDigitChar c then
      parseDigits (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) rest
    else
      (acc, count, c :: rest)

/-- Parse `{m}`, `{m,}`, or `{m,n}` quantifier bounds immediately after `'{'`. -/
def parseBraceQuantifier (cs : List Char) :
    Except RegexErrorKind (Nat × Option Nat × List Char) :=
  let (minVal, minDigits, rest1) := parseDigits 0 0 cs
  if minDigits == 0 then
    .error .invalidSyntax
  else if minVal > maxRepetitionCount then
    .error .invalidSyntax
  else
    match rest1 with
    | [] => .error .unexpectedEof
    | '}' :: rest2 => .ok (minVal, some minVal, rest2)
    | ',' :: rest2 =>
      match rest2 with
      | [] => .error .unexpectedEof
      | '}' :: rest3 => .ok (minVal, none, rest3)
      | _ =>
        let (maxVal, maxDigits, rest3) := parseDigits 0 0 rest2
        if maxDigits == 0 then
          .error .invalidSyntax
        else if maxVal > maxRepetitionCount then
          .error .invalidSyntax
        else if maxVal < minVal then
          .error .invalidSyntax
        else
          match rest3 with
          | [] => .error .unexpectedEof
          | '}' :: rest4 => .ok (minVal, some maxVal, rest4)
          | _ => .error .invalidSyntax
    | _ => .error .invalidSyntax

/-- Parse an escape sequence immediately after `'\\'`. -/
def parseEscape : List Char → Except RegexErrorKind (Regex × List Char)
  | [] => .error .unexpectedEof
  | c :: rest =>
    match c with
    | 'd' => .ok (.char (.pred .digit), rest)
    | 'D' => .ok (.char (.pred .nonDigit), rest)
    | 'w' => .ok (.char (.pred .word), rest)
    | 'W' => .ok (.char (.pred .nonWord), rest)
    | 's' => .ok (.char (.pred .space), rest)
    | 'S' => .ok (.char (.pred .nonSpace), rest)
    | 'b' => .ok (.wordBoundary true, rest)
    | 'B' => .ok (.wordBoundary false, rest)
    | 'n' => .ok (.char (.literal '\n'), rest)
    | 'r' => .ok (.char (.literal '\r'), rest)
    | 't' => .ok (.char (.literal '\t'), rest)
    | _ => .ok (.char (.literal c), rest)

/-- Consume an optional lazy `'?'` modifier after a quantifier. -/
def parseLazyFlag : List Char → Bool × List Char
  | '?' :: rest => (false, rest)
  | other => (true, other)

/-- Reject ungrouped consecutive quantifiers (`**`, `*+`, `*??`, `{1}{2}`, etc.). -/
def rejectExtraQuantifier : List Char → Except RegexErrorKind Unit
  | '*' :: _ | '+' :: _ | '?' :: _ | '{' :: _ => .error .invalidSyntax
  | _ => .ok ()

/-- Parse an optional quantifier suffix (`*`, `+`, `?`, `{...}`) plus optional lazy `?`. -/
def parseQuantifierSuffix (atom : Regex) : List Char → Except RegexErrorKind (Regex × List Char)
  | '*' :: rest =>
    let (greedy, rest1) := parseLazyFlag rest
    (rejectExtraQuantifier rest1).map fun () => (.rep atom 0 none greedy, rest1)
  | '+' :: rest =>
    let (greedy, rest1) := parseLazyFlag rest
    (rejectExtraQuantifier rest1).map fun () => (.rep atom 1 none greedy, rest1)
  | '?' :: rest =>
    let (greedy, rest1) := parseLazyFlag rest
    (rejectExtraQuantifier rest1).map fun () => (.rep atom 0 (some 1) greedy, rest1)
  | '{' :: rest => do
    let (minVal, maxVal?, rest1) ← parseBraceQuantifier rest
    let (greedy, rest2) := parseLazyFlag rest1
    let () ← rejectExtraQuantifier rest2
    return (.rep atom minVal maxVal? greedy, rest2)
  | other => .ok (atom, other)

mutual
  /-- Parse `|`-separated alternation branches. -/
  def parseAlt : Nat → List Char → Except RegexErrorKind (Regex × List Char)
    | 0, _ => .error .unexpectedEof
    | fuel + 1, cs => do
      let (lhs, rest1) ← parseSeq fuel cs
      match rest1 with
      | '|' :: rest2 =>
        let (rhs, rest3) ← parseAlt fuel rest2
        return (.alt lhs rhs, rest3)
      | _ => return (lhs, rest1)

  /-- Parse a sequence of zero or more quantified atoms. -/
  def parseSeq : Nat → List Char → Except RegexErrorKind (Regex × List Char)
    | 0, _ => .error .unexpectedEof
    | fuel + 1, cs =>
      match cs with
      | [] | '|' :: _ | ')' :: _ => .ok (.empty, cs)
      | '*' :: _ | '+' :: _ | '?' :: _ | '{' :: _ => .error .invalidSyntax
      | _ => do
        let (atom, rest1) ← parseAtom fuel cs
        let (quant, rest2) ← parseQuantifierSuffix atom rest1
        match rest2 with
        | [] | '|' :: _ | ')' :: _ => return (quant, rest2)
        | _ =>
          let (tail, rest3) ← parseSeq fuel rest2
          return (.seq quant tail, rest3)

  /-- Parse a single regex atom (`.`, `^`, `$`, `\...`, `[...]`, `(...)`, `(?:...)`, or literal). -/
  def parseAtom : Nat → List Char → Except RegexErrorKind (Regex × List Char)
    | 0, _ => .error .unexpectedEof
    | fuel + 1, cs =>
      match cs with
      | [] => .error .unexpectedEof
      | '.' :: rest => .ok (.char .any, rest)
      | '^' :: rest => .ok (.anchorStart, rest)
      | '$' :: rest => .ok (.anchorEnd, rest)
      | '\\' :: rest => parseEscape rest
      | '[' :: rest =>
        (parseCharClass rest).map fun (atom, rest1) => (.char atom, rest1)
      | '(' :: rest => do
        let body :=
          match rest with
          | '?' :: ':' :: rest2 => rest2
          | _ => rest
        let (inner, rest1) ← parseAlt fuel body
        match rest1 with
        | ')' :: rest2 => return (inner, rest2)
        | [] => .error .unexpectedEof
        | _ => .error .invalidSyntax
      | c :: rest => .ok (.char (.literal c), rest)
end

/-- Parse a regex pattern character list into a `Regex` AST. -/
def parseRegexChars (cs : List Char) : Except RegexErrorKind Regex :=
  if cs.isEmpty then
    .ok .empty
  else
    let fuel := cs.length * 4 + 4
    match parseAlt fuel cs with
    | .error k => .error k
    | .ok (ast, rest) =>
      match rest with
      | [] => .ok ast
      | _ => .error .invalidSyntax

/-- Parse a regex pattern string into a `Regex` AST. -/
def parseRegex (pattern : String) : Except RegexErrorKind Regex :=
  parseRegexChars pattern.toList

/-- Check whether the character at index `idx` in `cs` is a word character. -/
def isWordAt (cs : List Char) (idx : Nat) : Bool :=
  match cs[idx]? with
  | some c => isWordChar c
  | none => false

/-- Check whether position `idx` in `cs` is a word boundary (`\b`). -/
def isWordBoundary (cs : List Char) (idx : Nat) : Bool :=
  let prevWord := if idx == 0 then false else isWordAt cs (idx - 1)
  let nextWord := isWordAt cs idx
  prevWord != nextWord

/-- Compute the UTF-8 byte offset corresponding to character index `idx` in `cs`. -/
def utf8ByteOffset (cs : List Char) (idx : Nat) : Nat :=
  ((cs.take idx).map Char.utf8Size).sum

/-- Construct a `MatchSpan` from character indices `[i, j)` in `cs`. -/
def mkMatchSpan (cs : List Char) (i j : Nat) : MatchSpan :=
  { matched := String.ofList ((cs.drop i).take (j - i))
    startByte := utf8ByteOffset cs i
    stopByte := utf8ByteOffset cs j }

/-- `k`-fold relational repetition of a match relation `P` bounded by haystack length `len`. -/
def MatchesRep (len : Nat) (P : Nat → Nat → Prop) : Nat → Nat → Nat → Prop
  | 0, i, j => i ≤ len ∧ i = j
  | k + 1, i, j => ∃ mid, P i mid ∧ MatchesRep len P k mid j

/-- Declarative language-membership semantics: `r` matches `hay[i..j)` inside full haystack `hay`. -/
def MatchesAt (hay : List Char) : Regex → Nat → Nat → Prop
  | .empty, i, j => i ≤ hay.length ∧ i = j
  | .char atom, i, j => ∃ c, hay[i]? = some c ∧ charAtomMatches atom c = true ∧ j = i + 1
  | .anchorStart, i, j => i = 0 ∧ j = 0
  | .anchorEnd, i, j => i = hay.length ∧ j = hay.length
  | .wordBoundary pos, i, j => i ≤ hay.length ∧ isWordBoundary hay i = pos ∧ i = j
  | .seq r1 r2, i, j => ∃ mid, MatchesAt hay r1 i mid ∧ MatchesAt hay r2 mid j
  | .alt r1 r2, i, j => MatchesAt hay r1 i j ∨ MatchesAt hay r2 i j
  | .rep inner min max? _, i, j =>
      ∃ k, min ≤ k ∧ (∀ m, max? = some m → k ≤ m) ∧
        MatchesRep hay.length (MatchesAt hay inner) k i j

/-- Existence of any match of `r` inside `hay`. -/
def HasMatch (r : Regex) (hay : List Char) : Prop :=
  ∃ i j, MatchesAt hay r i j

/-- Deduplicate a priority-ordered list of positions while keeping the earliest (highest-priority) occurrence of each index. -/
def dedupFirstAux (seen : List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if seen.contains x then dedupFirstAux seen xs
    else x :: dedupFirstAux (x :: seen) xs

/-- Deduplicate `xs`, preserving first-occurrence priority order. -/
def dedupFirst (xs : List Nat) : List Nat :=
  dedupFirstAux [] xs

/-- Apply `step` exactly `k` times from `pos`, preserving leftmost-first priority order. -/
def evalExact (step : Nat → List Nat) : Nat → Nat → List Nat
  | 0, pos => [pos]
  | k + 1, pos => dedupFirst ((step pos).flatMap (evalExact step k))

/-- Apply `step` between `0` and `k` times from `pos` in greedy (`true`) or lazy (`false`) priority order. -/
def evalOpt (step : Nat → List Nat) (greedy : Bool) : Nat → Nat → List Nat
  | 0, pos => [pos]
  | k + 1, pos =>
    let more := dedupFirst ((step pos).flatMap (evalOpt step greedy k))
    if greedy then dedupFirst (more ++ [pos]) else dedupFirst (pos :: more)

/-- Apply `step` zero or more times with strict forward progress (`p' > pos`) bounded by remaining length `fuel`. -/
def evalStarAux (step : Nat → List Nat) (greedy : Bool) : Nat → Nat → List Nat
  | 0, pos => [pos]
  | fuel + 1, pos =>
    let nexts := (step pos).filter (· > pos)
    let more := dedupFirst (nexts.flatMap (evalStarAux step greedy fuel))
    if greedy then dedupFirst (more ++ [pos]) else dedupFirst (pos :: more)

/-- Priority-ordered backtracking evaluator returning all ending character indices reachable by `r` from `pos` in `hay`. -/
def evalAt (hay : List Char) : Regex → Nat → List Nat
  | .empty, pos => [pos]
  | .char atom, pos =>
    match hay[pos]? with
    | some c => if charAtomMatches atom c then [pos + 1] else []
    | none => []
  | .anchorStart, pos => if pos == 0 then [pos] else []
  | .anchorEnd, pos => if pos == hay.length then [pos] else []
  | .wordBoundary positive, pos => if isWordBoundary hay pos == positive then [pos] else []
  | .seq r1 r2, pos => dedupFirst ((evalAt hay r1 pos).flatMap (evalAt hay r2))
  | .alt r1 r2, pos => dedupFirst (evalAt hay r1 pos ++ evalAt hay r2 pos)
  | .rep inner min max? greedy, pos =>
    let step := evalAt hay inner
    match max? with
    | some max =>
      if max < min then []
      else
        let base := evalExact step min pos
        dedupFirst (base.flatMap (evalOpt step greedy (max - min)))
    | none =>
      let base := evalExact step min pos
      dedupFirst (base.flatMap fun p => evalStarAux step greedy (hay.length - p) p)

private theorem dedupFirstAux_mem (seen xs : List Nat) (a : Nat) :
    a ∈ dedupFirstAux seen xs ↔ a ∈ xs ∧ a ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [dedupFirstAux]
  | cons x rest ih =>
    simp only [dedupFirstAux]
    by_cases h : seen.contains x = true
    · have hx : x ∈ seen := by simpa [List.contains_iff_mem] using h
      simp only [h, ↓reduceIte, ih, List.mem_cons]
      constructor
      · rintro ⟨ha, hns⟩
        exact ⟨Or.inr ha, hns⟩
      · rintro ⟨rfl | ha, hns⟩
        · exact absurd hx hns
        · exact ⟨ha, hns⟩
    · have hx : x ∉ seen := by simpa [List.contains_iff_mem] using h
      simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨ha, hns⟩)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr ha, fun hm => hns (Or.inr hm)⟩
      · rintro ⟨rfl | ha, hns⟩
        · exact Or.inl rfl
        · by_cases hax : a = x
          · exact Or.inl hax
          · exact Or.inr ⟨ha, fun hm => by
              rcases hm with rfl | hm'
              · exact hax rfl
              · exact hns hm'⟩

private theorem dedupFirst_mem (xs : List Nat) (a : Nat) :
    a ∈ dedupFirst xs ↔ a ∈ xs := by
  simp [dedupFirst, dedupFirstAux_mem]

private theorem matchesRep_bounds {len : Nat} {P : Nat → Nat → Prop}
    (hP : ∀ i j, P i j → i ≤ j ∧ j ≤ len) :
    ∀ k i j, MatchesRep len P k i j → i ≤ j ∧ j ≤ len
  | 0, i, j, h => by rcases h with ⟨hi, rfl⟩; exact ⟨Nat.le_refl _, hi⟩
  | k + 1, i, j, ⟨mid, hm, hrest⟩ => by
    have h1 := hP i mid hm
    have h2 := matchesRep_bounds hP k mid j hrest
    omega

private theorem matchesAt_bounds {hay : List Char} (r : Regex) :
    ∀ i j, MatchesAt hay r i j → i ≤ j ∧ j ≤ hay.length := by
  induction r with
  | empty => intro i j ⟨hi, hij⟩; subst hij; exact ⟨Nat.le_refl _, hi⟩
  | char atom =>
    intro i j ⟨c, hget, _, hj⟩
    have hlt : i < hay.length := (List.getElem?_eq_some_iff.mp hget).1
    omega
  | anchorStart => intro i j ⟨hi, hj⟩; subst hi; subst hj; exact ⟨Nat.le_refl 0, Nat.zero_le _⟩
  | anchorEnd => intro i j ⟨hi, hj⟩; subst hi; subst hj; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | wordBoundary pos => intro i j ⟨hi, _, hij⟩; subst hij; exact ⟨Nat.le_refl _, hi⟩
  | seq r1 r2 ih1 ih2 =>
    intro i j ⟨mid, h1, h2⟩
    have b1 := ih1 i mid h1
    have b2 := ih2 mid j h2
    omega
  | alt r1 r2 ih1 ih2 =>
    intro i j h
    rcases h with h1 | h2
    · exact ih1 i j h1
    · exact ih2 i j h2
  | rep inner min max? greedy ih =>
    intro i j ⟨k, _, _, hrep⟩
    exact matchesRep_bounds ih k i j hrep

private theorem matchesRep_split {len : Nat} {P : Nat → Nat → Prop}
    (hP : ∀ i j, P i j → i ≤ j ∧ j ≤ len) :
    ∀ a b i j, MatchesRep len P (a + b) i j →
      ∃ mid, MatchesRep len P a i mid ∧ MatchesRep len P b mid j
  | 0, b, i, j, h => by
    rw [Nat.zero_add] at h
    have hb := matchesRep_bounds hP b i j h
    exact ⟨i, ⟨Nat.le_trans hb.1 hb.2, rfl⟩, h⟩
  | a + 1, b, i, j, h => by
    rw [Nat.succ_add] at h
    rcases h with ⟨mid, hm, hrest⟩
    obtain ⟨mid2, h1, h2⟩ := matchesRep_split hP a b mid j hrest
    exact ⟨mid2, ⟨mid, hm, h1⟩, h2⟩

private theorem matchesRep_append {len : Nat} {P : Nat → Nat → Prop} :
    ∀ a b i mid j, MatchesRep len P a i mid → MatchesRep len P b mid j →
      MatchesRep len P (a + b) i j
  | 0, b, i, mid, j, h1, h2 => by
    rcases h1 with ⟨_, rfl⟩
    simpa using h2
  | a + 1, b, i, mid, j, ⟨mid1, hm, hrest⟩, h2 => by
    rw [Nat.succ_add]
    exact ⟨mid1, hm, matchesRep_append a b mid1 mid j hrest h2⟩

private theorem evalExact_mem_iff {hay : List Char} {r : Regex} {step : Nat → List Nat}
    (hstep : ∀ pos p, pos ≤ hay.length → (p ∈ step pos ↔ MatchesAt hay r pos p))
    (k pos p : Nat) (hpos : pos ≤ hay.length) :
    p ∈ evalExact step k pos ↔ MatchesRep hay.length (MatchesAt hay r) k pos p := by
  induction k generalizing pos with
  | zero =>
    simp only [evalExact, List.mem_singleton, MatchesRep]
    constructor
    · rintro rfl; exact ⟨hpos, rfl⟩
    · rintro ⟨_, rfl⟩; rfl
  | succ k ih =>
    simp only [evalExact, dedupFirst_mem, List.mem_flatMap, MatchesRep]
    constructor
    · rintro ⟨mid, hmid, hp⟩
      have hm := (hstep pos mid hpos).mp hmid
      exact ⟨mid, hm, (ih mid (matchesAt_bounds r pos mid hm).2).mp hp⟩
    · rintro ⟨mid, hm, hrest⟩
      exact ⟨mid, (hstep pos mid hpos).mpr hm, (ih mid (matchesAt_bounds r pos mid hm).2).mpr hrest⟩

private theorem evalOpt_mem_iff {hay : List Char} {r : Regex} {step : Nat → List Nat}
    (hstep : ∀ pos p, pos ≤ hay.length → (p ∈ step pos ↔ MatchesAt hay r pos p))
    (greedy : Bool) (k pos p : Nat) (hpos : pos ≤ hay.length) :
    p ∈ evalOpt step greedy k pos ↔ ∃ n ≤ k, MatchesRep hay.length (MatchesAt hay r) n pos p := by
  induction k generalizing pos with
  | zero =>
    simp only [evalOpt, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨0, Nat.le_refl 0, hpos, rfl⟩
    · rintro ⟨n, hn, hrep⟩
      have : n = 0 := Nat.le_zero.mp hn
      subst this
      exact hrep.2.symm
  | succ k ih =>
    simp only [evalOpt]
    have hSplit :
        p ∈ (if greedy then dedupFirst (dedupFirst ((step pos).flatMap (evalOpt step greedy k)) ++ [pos])
             else dedupFirst (pos :: dedupFirst ((step pos).flatMap (evalOpt step greedy k)))) ↔
          p = pos ∨ ∃ mid, mid ∈ step pos ∧ p ∈ evalOpt step greedy k mid := by
      cases greedy <;> simp [dedupFirst_mem, List.mem_append, List.mem_flatMap, Or.comm]
    rw [hSplit]
    constructor
    · rintro (rfl | ⟨mid, hmid, hp⟩)
      · exact ⟨0, Nat.zero_le _, hpos, rfl⟩
      · have hm := (hstep pos mid hpos).mp hmid
        obtain ⟨n, hn, hrep⟩ := (ih mid (matchesAt_bounds r pos mid hm).2).mp hp
        exact ⟨n + 1, Nat.succ_le_succ hn, mid, hm, hrep⟩
    · rintro ⟨n, hn, hrep⟩
      cases n with
      | zero => exact Or.inl hrep.2.symm
      | succ n' =>
        rcases hrep with ⟨mid, hm, hrest⟩
        have hnk : n' ≤ k := Nat.le_of_succ_le_succ hn
        exact Or.inr ⟨mid, (hstep pos mid hpos).mpr hm,
          (ih mid (matchesAt_bounds r pos mid hm).2).mpr ⟨n', hnk, hrest⟩⟩

private theorem evalStarAux_sound {hay : List Char} {r : Regex} {step : Nat → List Nat}
    (hstep : ∀ pos p, pos ≤ hay.length → (p ∈ step pos ↔ MatchesAt hay r pos p))
    (greedy : Bool) (fuel pos p : Nat) (hpos : pos ≤ hay.length)
    (hp : p ∈ evalStarAux step greedy fuel pos) :
    ∃ n, MatchesRep hay.length (MatchesAt hay r) n pos p := by
  induction fuel generalizing pos with
  | zero =>
    simp only [evalStarAux, List.mem_singleton] at hp
    subst hp
    exact ⟨0, hpos, rfl⟩
  | succ fuel ih =>
    simp only [evalStarAux] at hp
    have hSplit :
        p = pos ∨ ∃ mid, (mid ∈ step pos ∧ mid > pos) ∧ p ∈ evalStarAux step greedy fuel mid := by
      cases greedy <;>
        simpa [dedupFirst_mem, List.mem_append, List.mem_flatMap, List.mem_filter, Or.comm] using hp
    rcases hSplit with rfl | ⟨mid, ⟨hmid, _⟩, hrest⟩
    · exact ⟨0, hpos, rfl⟩
    · have hm := (hstep pos mid hpos).mp hmid
      obtain ⟨n, hrep⟩ := ih mid (matchesAt_bounds r pos mid hm).2 hrest
      exact ⟨n + 1, mid, hm, hrep⟩

private theorem evalStarAux_complete {hay : List Char} {r : Regex} {step : Nat → List Nat}
    (hstep : ∀ pos p, pos ≤ hay.length → (p ∈ step pos ↔ MatchesAt hay r pos p))
    (greedy : Bool) :
    ∀ n pos p, MatchesRep hay.length (MatchesAt hay r) n pos p →
      ∀ fuel, hay.length - pos ≤ fuel → p ∈ evalStarAux step greedy fuel pos
  | 0, pos, p, ⟨_, hEq⟩, fuel, _ => by
    subst hEq
    cases fuel with
    | zero => simp [evalStarAux]
    | succ fuel => cases greedy <;> simp [evalStarAux, dedupFirst_mem]
  | n + 1, pos, p, ⟨mid, hm, hrest⟩, fuel, hfuel => by
    have hbm := matchesAt_bounds r pos mid hm
    by_cases heq : pos = mid
    · subst heq
      exact evalStarAux_complete hstep greedy n pos p hrest fuel hfuel
    · have hlt : pos < mid := Nat.lt_of_le_of_ne hbm.1 heq
      have hpos : pos ≤ hay.length := Nat.le_trans hbm.1 hbm.2
      have hmid_mem : mid ∈ step pos := (hstep pos mid hpos).mpr hm
      cases fuel with
      | zero => omega
      | succ fuel' =>
        have hfuel' : hay.length - mid ≤ fuel' := by omega
        have hrec := evalStarAux_complete hstep greedy n mid p hrest fuel' hfuel'
        cases greedy
        · simp only [evalStarAux, Bool.false_eq_true, ↓reduceIte, dedupFirst_mem, List.mem_cons,
            List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          exact Or.inr ⟨mid, ⟨hmid_mem, hlt⟩, hrec⟩
        · simp only [evalStarAux, ↓reduceIte, dedupFirst_mem, List.mem_append,
            List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          exact Or.inl ⟨mid, ⟨hmid_mem, hlt⟩, hrec⟩

/-- `evalAt` is sound and complete with respect to declarative `MatchesAt` for every regex and valid start position. -/
theorem evalAt_mem_iff (hay : List Char) (r : Regex) (pos p : Nat) (hpos : pos ≤ hay.length) :
    p ∈ evalAt hay r pos ↔ MatchesAt hay r pos p := by
  induction r generalizing pos p with
  | empty =>
    simp only [evalAt, List.mem_singleton, MatchesAt]
    constructor
    · rintro rfl; exact ⟨hpos, rfl⟩
    · rintro ⟨_, rfl⟩; rfl
  | char atom =>
    simp only [evalAt, MatchesAt]
    cases hget : hay[pos]? with
    | none =>
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨c, hget', _, _⟩
      cases hget'
    | some c =>
      by_cases hmatch : charAtomMatches atom c = true
      · simp only [hmatch, ↓reduceIte, List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨c, rfl, hmatch, rfl⟩
        · rintro ⟨c', hc', _, hp⟩; exact hp
      · simp only [hmatch, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff]
        rintro ⟨c', hc', hm', _⟩
        cases hc'
        exact hmatch hm'
  | anchorStart =>
    simp only [evalAt, MatchesAt]
    by_cases h0 : pos = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton, true_and]
    · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff]
      exact fun ⟨h, _⟩ => h0 h
  | anchorEnd =>
    simp only [evalAt, MatchesAt]
    by_cases he : pos = hay.length
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton, true_and]
    · simp only [beq_false_of_ne he, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff]
      exact fun ⟨h, _⟩ => he h
  | wordBoundary positive =>
    simp only [evalAt, MatchesAt]
    by_cases hb : isWordBoundary hay pos = positive
    · simp only [hb, beq_self_eq_true, ↓reduceIte, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨hpos, trivial, rfl⟩
      · rintro ⟨_, _, rfl⟩; rfl
    · simp only [beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff]
      exact fun ⟨_, hb', _⟩ => hb hb'
  | seq r1 r2 ih1 ih2 =>
    simp only [evalAt, MatchesAt, dedupFirst_mem, List.mem_flatMap]
    constructor
    · rintro ⟨mid, hmid, hp⟩
      have h1 := (ih1 pos mid hpos).mp hmid
      have h2 := (ih2 mid p (matchesAt_bounds r1 pos mid h1).2).mp hp
      exact ⟨mid, h1, h2⟩
    · rintro ⟨mid, h1, h2⟩
      exact ⟨mid, (ih1 pos mid hpos).mpr h1, (ih2 mid p (matchesAt_bounds r1 pos mid h1).2).mpr h2⟩
  | alt r1 r2 ih1 ih2 =>
    simp only [evalAt, MatchesAt, dedupFirst_mem, List.mem_append]
    rw [ih1 pos p hpos, ih2 pos p hpos]
  | rep inner min max? greedy ih =>
    simp only [evalAt, MatchesAt]
    have hstep : ∀ q1 q2, q1 ≤ hay.length → (q2 ∈ evalAt hay inner q1 ↔ MatchesAt hay inner q1 q2) :=
      fun q1 q2 hq1 => ih q1 q2 hq1
    cases max? with
    | some max =>
      by_cases hlt : max < min
      · simp only [hlt, ↓reduceIte, List.not_mem_nil, false_iff]
        rintro ⟨k, hmin, hmax, _⟩
        have hkm := hmax max rfl
        omega
      · simp only [hlt, ↓reduceIte, dedupFirst_mem, List.mem_flatMap]
        constructor
        · rintro ⟨mid, hmid, hp⟩
          have hmin := (evalExact_mem_iff hstep min pos mid hpos).mp hmid
          have hmid_le := (matchesRep_bounds (matchesAt_bounds inner) min pos mid hmin).2
          obtain ⟨extra, hextra, hopt⟩ :=
            (evalOpt_mem_iff hstep greedy (max - min) mid p hmid_le).mp hp
          exact ⟨min + extra, Nat.le_add_right min extra,
            fun m hm => by cases hm; omega,
            matchesRep_append min extra pos mid p hmin hopt⟩
        · rintro ⟨k, hmin, hmax, hrep⟩
          have hkm := hmax max rfl
          have hadd : min + (k - min) = k := Nat.add_sub_of_le hmin
          rw [← hadd] at hrep
          obtain ⟨mid, h1, h2⟩ := matchesRep_split (matchesAt_bounds inner) min (k - min) pos p hrep
          have hmid_le := (matchesRep_bounds (matchesAt_bounds inner) min pos mid h1).2
          exact ⟨mid, (evalExact_mem_iff hstep min pos mid hpos).mpr h1,
            (evalOpt_mem_iff hstep greedy (max - min) mid p hmid_le).mpr ⟨k - min, by omega, h2⟩⟩
    | none =>
      simp only [dedupFirst_mem, List.mem_flatMap]
      constructor
      · rintro ⟨mid, hmid, hp⟩
        have hmin := (evalExact_mem_iff hstep min pos mid hpos).mp hmid
        have hmid_le := (matchesRep_bounds (matchesAt_bounds inner) min pos mid hmin).2
        obtain ⟨extra, hstar⟩ := evalStarAux_sound hstep greedy (hay.length - mid) mid p hmid_le hp
        exact ⟨min + extra, Nat.le_add_right min extra, (fun _ hm => by cases hm),
          matchesRep_append min extra pos mid p hmin hstar⟩
      · rintro ⟨k, hmin, _, hrep⟩
        have hadd : min + (k - min) = k := Nat.add_sub_of_le hmin
        rw [← hadd] at hrep
        obtain ⟨mid, h1, h2⟩ := matchesRep_split (matchesAt_bounds inner) min (k - min) pos p hrep
        exact ⟨mid, (evalExact_mem_iff hstep min pos mid hpos).mpr h1,
          evalStarAux_complete hstep greedy (k - min) mid p h2 (hay.length - mid) (Nat.le_refl _)⟩

/-- Scan character positions `start, start + 1, ..., cs.length` for the leftmost-first match of `r`. -/
def findFirstIdxAux (r : Regex) (cs : List Char) : Nat → Nat → Option (Nat × Nat)
  | 0, pos =>
    match evalAt cs r pos with
    | p :: _ => some (pos, p)
    | [] => none
  | rem + 1, pos =>
    match evalAt cs r pos with
    | p :: _ => some (pos, p)
    | [] => findFirstIdxAux r cs rem (pos + 1)

/-- Find the leftmost-first character-index match `(i, j)` of `r` in `cs` starting at or after `start`. -/
def findFirstIdx (r : Regex) (cs : List Char) (start : Nat) : Option (Nat × Nat) :=
  if start ≤ cs.length then
    findFirstIdxAux r cs (cs.length - start) start
  else
    none

private theorem findFirstIdxAux_isSome_iff (r : Regex) (cs : List Char) (rem start : Nat)
    (hEnd : start + rem = cs.length) :
    (findFirstIdxAux r cs rem start).isSome = true ↔
      ∃ i j, start ≤ i ∧ MatchesAt cs r i j := by
  induction rem generalizing start with
  | zero =>
    have hle : start ≤ cs.length := by omega
    simp only [findFirstIdxAux]
    cases he : evalAt cs r start with
    | nil =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨i, j, hi, hm⟩
      have hib := matchesAt_bounds r i j hm
      have hieq : i = start := by omega
      subst hieq
      have hmem := (evalAt_mem_iff cs r i j hle).mpr hm
      rw [he] at hmem
      cases hmem
    | cons p rest =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨start, p, Nat.le_refl _, (evalAt_mem_iff cs r start p hle).mp (by simp [he])⟩
  | succ rem ih =>
    have hle : start ≤ cs.length := by omega
    simp only [findFirstIdxAux]
    cases he : evalAt cs r start with
    | cons p rest =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨start, p, Nat.le_refl _, (evalAt_mem_iff cs r start p hle).mp (by simp [he])⟩
    | nil =>
      rw [ih (start + 1) (by omega)]
      constructor
      · rintro ⟨i, j, hi, hm⟩
        exact ⟨i, j, by omega, hm⟩
      · rintro ⟨i, j, hi, hm⟩
        by_cases hEq : i = start
        · subst hEq
          have hmem := (evalAt_mem_iff cs r i j hle).mpr hm
          rw [he] at hmem
          cases hmem
        · exact ⟨i, j, by omega, hm⟩

/-- `findFirstIdx r hay 0` succeeds iff declarative `HasMatch r hay` holds. -/
theorem findFirstIdx_isSome_iff_hasMatch (r : Regex) (hay : List Char) :
    (findFirstIdx r hay 0).isSome = true ↔ HasMatch r hay := by
  simp only [findFirstIdx, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  rw [findFirstIdxAux_isSome_iff r hay hay.length 0 (Nat.zero_add _)]
  constructor
  · rintro ⟨i, j, _, hm⟩; exact ⟨i, j, hm⟩
  · rintro ⟨i, j, hm⟩; exact ⟨i, j, Nat.zero_le _, hm⟩

/-- Collect all non-overlapping leftmost-first character-index matches of `r` in `cs` starting at `cursor`. -/
def findAllIdxAux (r : Regex) (cs : List Char) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, cursor =>
    match findFirstIdx r cs cursor with
    | none => []
    | some (i, j) =>
      if i < j then
        (i, j) :: findAllIdxAux r cs fuel j
      else if j < cs.length then
        (i, j) :: findAllIdxAux r cs fuel (j + 1)
      else
        [(i, j)]

/-- Collect all non-overlapping leftmost-first character-index matches of `r` in `cs`. -/
def findAllIdx (r : Regex) (cs : List Char) : List (Nat × Nat) :=
  findAllIdxAux r cs (cs.length + 1) 0

/-- Replace matched character-index spans in `cs` with `rep`. -/
def replaceSpans (cs : List Char) (rep : String) (cursor : Nat) : List (Nat × Nat) → String
  | [] => String.ofList (cs.drop cursor)
  | (i, j) :: rest =>
    String.ofList ((cs.drop cursor).take (i - cursor)) ++ rep ++ replaceSpans cs rep j rest

/-- Split `cs` around matched character-index spans, always emitting at least one piece. -/
def splitSpans (cs : List Char) (cursor : Nat) : List (Nat × Nat) → List String
  | [] => [String.ofList (cs.drop cursor)]
  | (i, j) :: rest =>
    String.ofList ((cs.drop cursor).take (i - cursor)) :: splitSpans cs j rest

/-- Reference model for `RegexApi.testPattern`. -/
def testPatternModel (pattern haystack : String) : Except RegexErrorKind Bool :=
  (parseRegex pattern).map fun r => (findFirstIdx r haystack.toList 0).isSome

/-- Reference model for `RegexApi.findFirst`. -/
def findFirstModel (pattern haystack : String) : Except RegexErrorKind (Option MatchSpan) :=
  let cs := haystack.toList
  (parseRegex pattern).map fun r =>
    (findFirstIdx r cs 0).map fun (i, j) => mkMatchSpan cs i j

/-- Reference model for `RegexApi.findAll`. -/
def findAllModel (pattern haystack : String) : Except RegexErrorKind (Array MatchSpan) :=
  let cs := haystack.toList
  (parseRegex pattern).map fun r =>
    ((findAllIdx r cs).map fun (i, j) => mkMatchSpan cs i j).toArray

/-- Reference model for `RegexApi.countMatches`. -/
def countMatchesModel (pattern haystack : String) : Except RegexErrorKind Nat :=
  (findAllModel pattern haystack).map Array.size

/-- Reference model for `RegexApi.replaceAll`. -/
def replaceAllModel (pattern haystack replacement : String) : Except RegexErrorKind String :=
  let cs := haystack.toList
  (parseRegex pattern).map fun r => replaceSpans cs replacement 0 (findAllIdx r cs)

/-- Reference model for `RegexApi.splitBy`. -/
def splitByModel (pattern haystack : String) : Except RegexErrorKind (Array String) :=
  let cs := haystack.toList
  (parseRegex pattern).map fun r => (splitSpans cs 0 (findAllIdx r cs)).toArray

end LeanSwe.RegExp.Model

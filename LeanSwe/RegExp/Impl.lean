import LeanSwe.RegExp.Types

namespace LeanSwe.RegExp.Internal

/-- Maximum allowed brace repetition count (`{m}`, `{m,}`, `{m,n}`). -/
def maxRepetitionCount : Nat := 1000

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

/-- Character matching atom in the regex AST. -/
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

/-- Abstract syntax tree for parsed regular expressions. -/
inductive RegexAst where
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
  | seq (lhs rhs : RegexAst)
  /-- Ordered alternation `lhs | rhs`. -/
  | alt (lhs rhs : RegexAst)
  /-- Repetition `inner{min, max?}` with greedy (`true`) or lazy (`false`) priority. -/
  | rep (inner : RegexAst) (min : Nat) (max? : Option Nat) (greedy : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Construct a `RegexError` guaranteed to carry a non-empty message. -/
def mkError (kind : RegexErrorKind) (msg : String) : RegexError :=
  { kind := kind
    message := if msg.isEmpty then "regular expression syntax error" else msg }

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
  /-- Parse body items and closing `']'` of a `[...]` character class from `chars` at `pos`. -/
  def parseClassBody (chars : Array Char) (neg : Bool) (ranges : List (Char × Char))
      (preds : List CharPred) (pos : Nat) : Except RegexError (CharAtom × Nat) :=
    if h : pos < chars.size then
      let c := chars[pos]
      if c == ']' then
        if ranges.isEmpty && preds.isEmpty then
          .error (mkError .invalidSyntax "empty character class")
        else
          .ok (.charClass neg ranges.reverse preds.reverse, pos + 1)
      else if c == '\\' then
        if h1 : pos + 1 < chars.size then
          let esc := chars[pos + 1]
          match decodeClassEscape esc with
          | .pred p => parseClassBody chars neg ranges (p :: preds) (pos + 2)
          | .single lo => parseClassAfter chars neg ranges preds lo (pos + 2)
        else
          .error (mkError .unexpectedEof "trailing backslash in character class")
      else
        parseClassAfter chars neg ranges preds c (pos + 1)
    else
      .error (mkError .unexpectedEof "unterminated character class")
  termination_by chars.size - pos
  decreasing_by
    all_goals omega

  /-- Handle optional `'-'` range continuation after literal `lo` inside `[...]`. -/
  def parseClassAfter (chars : Array Char) (neg : Bool) (ranges : List (Char × Char))
      (preds : List CharPred) (lo : Char) (pos : Nat) : Except RegexError (CharAtom × Nat) :=
    if h : pos < chars.size then
      let c := chars[pos]
      if c == ']' then
        .ok (.charClass neg ((lo, lo) :: ranges).reverse preds.reverse, pos + 1)
      else if c == '-' then
        parseClassRange chars neg ranges preds lo (pos + 1)
      else if c == '\\' then
        if h1 : pos + 1 < chars.size then
          let ranges' := (lo, lo) :: ranges
          match decodeClassEscape chars[pos + 1] with
          | .pred p => parseClassBody chars neg ranges' (p :: preds) (pos + 2)
          | .single lo2 => parseClassAfter chars neg ranges' preds lo2 (pos + 2)
        else
          .error (mkError .unexpectedEof "trailing backslash in character class")
      else
        parseClassAfter chars neg ((lo, lo) :: ranges) preds c (pos + 1)
    else
      .error (mkError .unexpectedEof "unterminated character class")
  termination_by chars.size - pos
  decreasing_by
    all_goals omega

  /-- Handle upper bound of `lo-hi` (or trailing `lo-]` / `lo-\d`) inside `[...]`. -/
  def parseClassRange (chars : Array Char) (neg : Bool) (ranges : List (Char × Char))
      (preds : List CharPred) (lo : Char) (pos : Nat) : Except RegexError (CharAtom × Nat) :=
    if h : pos < chars.size then
      let c := chars[pos]
      if c == ']' then
        .ok (.charClass neg (('-', '-') :: (lo, lo) :: ranges).reverse preds.reverse, pos + 1)
      else if c == '\\' then
        if h1 : pos + 1 < chars.size then
          match decodeClassEscape chars[pos + 1] with
          | .pred p =>
            parseClassBody chars neg (('-', '-') :: (lo, lo) :: ranges) (p :: preds) (pos + 2)
          | .single hi =>
            if lo.toNat > hi.toNat then
              .error (mkError .invalidSyntax "reversed character class range")
            else
              parseClassBody chars neg ((lo, hi) :: ranges) preds (pos + 2)
        else
          .error (mkError .unexpectedEof "trailing backslash in character class")
      else
        if lo.toNat > c.toNat then
          .error (mkError .invalidSyntax "reversed character class range")
        else
          parseClassBody chars neg ((lo, c) :: ranges) preds (pos + 1)
    else
      .error (mkError .unexpectedEof "unterminated character class range")
  termination_by chars.size - pos
  decreasing_by
    all_goals omega
end

/-- Parse a `[...]` or `[^...]` character class immediately after `'['`. -/
def parseCharClass (chars : Array Char) (pos : Nat) : Except RegexError (CharAtom × Nat) :=
  if h : pos < chars.size then
    if chars[pos] == '^' then
      parseClassBody chars true [] [] (pos + 1)
    else
      parseClassBody chars false [] [] pos
  else
    parseClassBody chars false [] [] pos

/-- Parse consecutive ASCII decimal digits starting at `pos`, returning `(value, count, nextPos)`. -/
def parseDigits (chars : Array Char) (acc count pos : Nat) : Nat × Nat × Nat :=
  if h : pos < chars.size then
    let c := chars[pos]
    if isDigitChar c then
      parseDigits chars (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) (pos + 1)
    else
      (acc, count, pos)
  else
    (acc, count, pos)
termination_by chars.size - pos

/-- Parse `{m}`, `{m,}`, or `{m,n}` quantifier bounds immediately after `'{'`. -/
def parseBraceQuantifier (chars : Array Char) (pos : Nat) :
    Except RegexError (Nat × Option Nat × Nat) :=
  let (minVal, minDigits, pos1) := parseDigits chars 0 0 pos
  if minDigits == 0 then
    .error (mkError .invalidSyntax "missing minimum count in repetition quantifier")
  else if minVal > maxRepetitionCount then
    .error (mkError .invalidSyntax "repetition quantifier exceeds maximum bound")
  else if h1 : pos1 < chars.size then
    let c1 := chars[pos1]
    if c1 == '}' then
      .ok (minVal, some minVal, pos1 + 1)
    else if c1 == ',' then
      let pos2 := pos1 + 1
      if h2 : pos2 < chars.size then
        if chars[pos2] == '}' then
          .ok (minVal, none, pos2 + 1)
        else
          let (maxVal, maxDigits, pos3) := parseDigits chars 0 0 pos2
          if maxDigits == 0 then
            .error (mkError .invalidSyntax "invalid maximum count in repetition quantifier")
          else if maxVal > maxRepetitionCount then
            .error (mkError .invalidSyntax "repetition quantifier exceeds maximum bound")
          else if maxVal < minVal then
            .error (mkError .invalidSyntax "repetition quantifier max is less than min")
          else if h3 : pos3 < chars.size then
            if chars[pos3] == '}' then
              .ok (minVal, some maxVal, pos3 + 1)
            else
              .error (mkError .invalidSyntax "expected closing '}' in repetition quantifier")
          else
            .error (mkError .unexpectedEof "unterminated repetition quantifier")
      else
        .error (mkError .unexpectedEof "unterminated repetition quantifier")
    else
      .error (mkError .invalidSyntax "invalid character in repetition quantifier")
  else
    .error (mkError .unexpectedEof "unterminated repetition quantifier")

/-- Parse an escape sequence immediately after `'\\'`. -/
def parseEscape (chars : Array Char) (pos : Nat) : Except RegexError (RegexAst × Nat) :=
  if h : pos < chars.size then
    let c := chars[pos]
    let nextPos := pos + 1
    match c with
    | 'd' => .ok (.char (.pred .digit), nextPos)
    | 'D' => .ok (.char (.pred .nonDigit), nextPos)
    | 'w' => .ok (.char (.pred .word), nextPos)
    | 'W' => .ok (.char (.pred .nonWord), nextPos)
    | 's' => .ok (.char (.pred .space), nextPos)
    | 'S' => .ok (.char (.pred .nonSpace), nextPos)
    | 'b' => .ok (.wordBoundary true, nextPos)
    | 'B' => .ok (.wordBoundary false, nextPos)
    | 'n' => .ok (.char (.literal '\n'), nextPos)
    | 'r' => .ok (.char (.literal '\r'), nextPos)
    | 't' => .ok (.char (.literal '\t'), nextPos)
    | _ => .ok (.char (.literal c), nextPos)
  else
    .error (mkError .unexpectedEof "trailing backslash escape")

/-- Consume an optional lazy `'?'` modifier after a quantifier. -/
def parseLazyFlag (chars : Array Char) (pos : Nat) : Bool × Nat :=
  if h : pos < chars.size then
    if chars[pos] == '?' then
      (false, pos + 1)
    else
      (true, pos)
  else
    (true, pos)

/-- Reject ungrouped consecutive quantifiers (`**`, `*+`, `*??`, `{1}{2}`, etc.). -/
def rejectExtraQuantifier (chars : Array Char) (pos : Nat) : Except RegexError Unit :=
  if h : pos < chars.size then
    let c := chars[pos]
    if c == '*' || c == '+' || c == '?' || c == '{' then
      .error (mkError .invalidSyntax "unexpected repeated quantifier")
    else
      .ok ()
  else
    .ok ()

/-- Parse an optional quantifier suffix (`*`, `+`, `?`, `{...}`) plus optional lazy `'?'`. -/
def parseQuantifierSuffix (atom : RegexAst) (chars : Array Char) (pos : Nat) :
    Except RegexError (RegexAst × Nat) :=
  if h : pos < chars.size then
    let c := chars[pos]
    if c == '*' then
      let (greedy, pos1) := parseLazyFlag chars (pos + 1)
      (rejectExtraQuantifier chars pos1).map fun () => (.rep atom 0 none greedy, pos1)
    else if c == '+' then
      let (greedy, pos1) := parseLazyFlag chars (pos + 1)
      (rejectExtraQuantifier chars pos1).map fun () => (.rep atom 1 none greedy, pos1)
    else if c == '?' then
      let (greedy, pos1) := parseLazyFlag chars (pos + 1)
      (rejectExtraQuantifier chars pos1).map fun () => (.rep atom 0 (some 1) greedy, pos1)
    else if c == '{' then do
      let (minVal, maxVal?, pos1) ← parseBraceQuantifier chars (pos + 1)
      let (greedy, pos2) := parseLazyFlag chars pos1
      let () ← rejectExtraQuantifier chars pos2
      return (.rep atom minVal maxVal? greedy, pos2)
    else
      .ok (atom, pos)
  else
    .ok (atom, pos)

/-- Check whether position `pos` terminates the current concatenation sequence (`EOF`, `'|'`, or `')'`). -/
def isSeqStop (chars : Array Char) (pos : Nat) : Bool :=
  if h : pos < chars.size then
    let c := chars[pos]
    c == '|' || c == ')'
  else
    true

/-- Check whether `c` is a quantifier token that cannot begin a regex atom. -/
def isLeadingQuantifier (c : Char) : Bool :=
  c == '*' || c == '+' || c == '?' || c == '{'

mutual
  /-- Parse `|`-separated alternation branches from `chars` at `pos`. -/
  def parseAlt (fuel : Nat) (chars : Array Char) (pos : Nat) :
      Except RegexError (RegexAst × Nat) :=
    match fuel with
    | 0 => .error (mkError .unexpectedEof "unexpected end of pattern")
    | fuel' + 1 => do
      let (lhs, pos1) ← parseSeq fuel' chars pos
      if h : pos1 < chars.size then
        if chars[pos1] == '|' then
          let (rhs, pos2) ← parseAlt fuel' chars (pos1 + 1)
          return (.alt lhs rhs, pos2)
        else
          return (lhs, pos1)
      else
        return (lhs, pos1)

  /-- Parse a sequence of zero or more quantified atoms from `chars` at `pos`. -/
  def parseSeq (fuel : Nat) (chars : Array Char) (pos : Nat) :
      Except RegexError (RegexAst × Nat) :=
    match fuel with
    | 0 => .error (mkError .unexpectedEof "unexpected end of pattern")
    | fuel' + 1 =>
      if h : pos < chars.size then
        let c := chars[pos]
        if c == '|' || c == ')' then
          .ok (.empty, pos)
        else if isLeadingQuantifier c then
          .error (mkError .invalidSyntax "quantifier with nothing to repeat")
        else do
          let (atom, pos1) ← parseAtom fuel' chars pos
          let (quant, pos2) ← parseQuantifierSuffix atom chars pos1
          if isSeqStop chars pos2 then
            return (quant, pos2)
          else
            let (tail, pos3) ← parseSeq fuel' chars pos2
            return (.seq quant tail, pos3)
      else
        .ok (.empty, pos)

  /-- Parse a single regex atom from `chars` at `pos`. -/
  def parseAtom (fuel : Nat) (chars : Array Char) (pos : Nat) :
      Except RegexError (RegexAst × Nat) :=
    match fuel with
    | 0 => .error (mkError .unexpectedEof "unexpected end of pattern")
    | fuel' + 1 =>
      if h : pos < chars.size then
        let c := chars[pos]
        let nextPos := pos + 1
        if c == '.' then
          .ok (.char .any, nextPos)
        else if c == '^' then
          .ok (.anchorStart, nextPos)
        else if c == '$' then
          .ok (.anchorEnd, nextPos)
        else if c == '\\' then
          parseEscape chars nextPos
        else if c == '[' then
          (parseCharClass chars nextPos).map fun (atom, pos1) => (.char atom, pos1)
        else if c == '(' then do
          let bodyPos :=
            if h2 : nextPos + 1 < chars.size then
              if chars[nextPos] == '?' && chars[nextPos + 1] == ':' then
                nextPos + 2
              else
                nextPos
            else
              nextPos
          let (inner, pos1) ← parseAlt fuel' chars bodyPos
          if h1 : pos1 < chars.size then
            if chars[pos1] == ')' then
              return (inner, pos1 + 1)
            else
              .error (mkError .invalidSyntax "unmatched group delimiter")
          else
            .error (mkError .unexpectedEof "unclosed group '('")
        else
          .ok (.char (.literal c), nextPos)
      else
        .error (mkError .unexpectedEof "unexpected end of pattern")
end

/-- Parse a regular expression pattern string into a `RegexAst`. -/
def parseRegex (pattern : String) : Except RegexError RegexAst :=
  let chars := pattern.toList.toArray
  if chars.isEmpty then
    .ok .empty
  else
    let fuel := chars.size * 4 + 4
    match parseAlt fuel chars 0 with
    | .error e => .error e
    | .ok (ast, pos) =>
      if pos < chars.size then
        .error (mkError .invalidSyntax "unexpected trailing pattern character")
      else
        .ok ast

/-- Check whether the character at index `idx` in `chars` is a word character. -/
def isWordAt (chars : Array Char) (idx : Nat) : Bool :=
  match chars[idx]? with
  | some c => isWordChar c
  | none => false

/-- Check whether position `idx` in `chars` is a word boundary. -/
def isWordBoundary (chars : Array Char) (idx : Nat) : Bool :=
  let prevWord := if idx == 0 then false else isWordAt chars (idx - 1)
  let nextWord := isWordAt chars idx
  prevWord != nextWord

/-- Precompute the array of UTF-8 byte offsets for character indices `0..chars.size`. -/
def buildByteOffsets (chars : Array Char) : Array Nat :=
  let rec loop (i acc : Nat) (out : Array Nat) : Array Nat :=
    if h : i < chars.size then
      let nextAcc := acc + chars[i].utf8Size
      loop (i + 1) nextAcc (out.push nextAcc)
    else
      out
  termination_by chars.size - i
  loop 0 0 (Array.mkEmpty (chars.size + 1) |>.push 0)

/-- Deduplicate a list of indices keeping earliest occurrence, via explicit seen list. -/
def dedupFirstAux (seen : List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if seen.contains x then dedupFirstAux seen xs
    else x :: dedupFirstAux (x :: seen) xs

/-- Deduplicate a list of bounded indices keeping earliest occurrence, via boolean array. -/
def dedupFirstBoolAux (seen : Array Bool) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    if seen[x]! then dedupFirstBoolAux seen xs
    else x :: dedupFirstBoolAux (seen.setIfInBounds x true) xs

/-- Deduplicate a priority-ordered list of positions `≤ bound`, preserving first-occurrence order. -/
def dedupFirstFast (bound : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ =>
    if xs.length <= 16 then
      dedupFirstAux [] xs
    else
      dedupFirstBoolAux (Array.replicate (bound + 1) false) xs

/-- Compose two `n + 1`-entry match tables sequentially with deduplication. -/
def composeTab (n : Nat) (t1 t2 : Array (List Nat)) : Array (List Nat) :=
  Array.ofFn fun (i : Fin (n + 1)) =>
    dedupFirstFast n (t1[i.val]!.flatMap fun mid => t2[mid]!)

/-- Combine two `n + 1`-entry match tables in ordered alternation priority. -/
def altTab (n : Nat) (t1 t2 : Array (List Nat)) : Array (List Nat) :=
  Array.ofFn fun (i : Fin (n + 1)) =>
    dedupFirstFast n (t1[i.val]! ++ t2[i.val]!)

/-- Identity match table mapping each `pos ≤ n` to `[pos]`. -/
def idTab (n : Nat) : Array (List Nat) :=
  Array.ofFn fun (i : Fin (n + 1)) => [i.val]

/-- Iterate `f` `k` times on `acc` starting at `idTab n`, stopping early on a fixed point. -/
def iterTab (f : Array (List Nat) → Array (List Nat)) : Nat → Array (List Nat) → Array (List Nat)
  | 0, acc => acc
  | k + 1, acc =>
    let next := f acc
    if next == acc then acc
    else iterTab f k next

/-- Single-step extension for optional repetition `evalOpt`. -/
def optStep (n : Nat) (stepTab : Array (List Nat)) (greedy : Bool)
    (acc : Array (List Nat)) : Array (List Nat) :=
  Array.ofFn fun (i : Fin (n + 1)) =>
    let pos := i.val
    let more := dedupFirstFast n (stepTab[pos]!.flatMap fun mid => acc[mid]!)
    if greedy then dedupFirstFast n (more ++ [pos])
    else dedupFirstFast n (pos :: more)

/-- Fill the `evalStarAux` table bottom-up from `n` down to `0`. -/
def fillStarAux (n : Nat) (stepTab : Array (List Nat)) (greedy : Bool) :
    Nat → Array (List Nat) → Array (List Nat)
  | 0, acc => acc
  | rem + 1, acc =>
    let pos := rem
    let nexts := (stepTab[pos]!).filter (· > pos)
    let more := dedupFirstFast n (nexts.flatMap fun q => acc[q]!)
    let row :=
      if greedy then dedupFirstFast n (more ++ [pos])
      else dedupFirstFast n (pos :: more)
    fillStarAux n stepTab greedy rem (acc.setIfInBounds pos row)

/-- Compute the `evalStarAux` match table for `stepTab` across all positions `0..n`. -/
def starTab (n : Nat) (stepTab : Array (List Nat)) (greedy : Bool) : Array (List Nat) :=
  let init := Array.replicate (n + 1) [n]
  fillStarAux n stepTab greedy n init

/-- Build the bottom-up match table `tab[pos] = evalAt chars ast pos` for all `pos ≤ chars.size`. -/
def evalTable (chars : Array Char) (ast : RegexAst) : Array (List Nat) :=
  let n := chars.size
  match ast with
  | .empty => idTab n
  | .char atom =>
    Array.ofFn fun (i : Fin (n + 1)) =>
      match chars[i.val]? with
      | some c => if charAtomMatches atom c then [i.val + 1] else []
      | none => []
  | .anchorStart =>
    Array.ofFn fun (i : Fin (n + 1)) => if i.val == 0 then [0] else []
  | .anchorEnd =>
    Array.ofFn fun (i : Fin (n + 1)) => if i.val == n then [n] else []
  | .wordBoundary positive =>
    Array.ofFn fun (i : Fin (n + 1)) =>
      if isWordBoundary chars i.val == positive then [i.val] else []
  | .seq r1 r2 =>
    composeTab n (evalTable chars r1) (evalTable chars r2)
  | .alt r1 r2 =>
    altTab n (evalTable chars r1) (evalTable chars r2)
  | .rep inner minVal max? greedy =>
    let step := evalTable chars inner
    match max? with
    | some maxVal =>
      if maxVal < minVal then
        Array.replicate (n + 1) []
      else
        let base := iterTab (composeTab n step) minVal (idTab n)
        let opt := iterTab (optStep n step greedy) (maxVal - minVal) (idTab n)
        composeTab n base opt
    | none =>
      let base := iterTab (composeTab n step) minVal (idTab n)
      composeTab n base (starTab n step greedy)

/-- Scan positions `start .. start + rem` in `tab` for the first match. -/
def findFirstIdxAux (tab : Array (List Nat)) : Nat → Nat → Option (Nat × Nat)
  | 0, pos =>
    match tab[pos]! with
    | p :: _ => some (pos, p)
    | [] => none
  | rem + 1, pos =>
    match tab[pos]! with
    | p :: _ => some (pos, p)
    | [] => findFirstIdxAux tab rem (pos + 1)

/-- Find the leftmost-first match `(i, j)` in `tab` starting at or after `start`. -/
def findFirstIdx (tab : Array (List Nat)) (n start : Nat) : Option (Nat × Nat) :=
  if start ≤ n then
    findFirstIdxAux tab (n - start) start
  else
    none

/-- Collect all non-overlapping leftmost-first match index pairs from `tab`. -/
def findAllIdxAux (tab : Array (List Nat)) (n : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, cursor =>
    match findFirstIdx tab n cursor with
    | none => []
    | some (i, j) =>
      if i < j then
        (i, j) :: findAllIdxAux tab n fuel j
      else if j < n then
        (i, j) :: findAllIdxAux tab n fuel (j + 1)
      else
        [(i, j)]

/-- Collect all non-overlapping match index pairs for `ast` in `chars`. -/
def findAllIdx (chars : Array Char) (ast : RegexAst) : List (Nat × Nat) :=
  let n := chars.size
  let tab := evalTable chars ast
  findAllIdxAux tab n (n + 1) 0

/-- Construct a `MatchSpan` for character range `[i, j)` using precomputed UTF-8 offsets. -/
def mkMatchSpanFast (chars : Array Char) (offsets : Array Nat) (i j : Nat) : MatchSpan :=
  { matched := String.ofList (chars.extract i j).toList
    startByte := offsets[i]!
    stopByte := offsets[j]! }

/-- Replace matched `[i, j)` character-index spans in `chars` with `rep`. -/
def replaceSpansFast (chars : Array Char) (rep : String) (cursor : Nat) :
    List (Nat × Nat) → String
  | [] => String.ofList (chars.extract cursor chars.size).toList
  | (i, j) :: rest =>
    String.ofList (chars.extract cursor i).toList ++ rep ++ replaceSpansFast chars rep j rest

/-- Split `chars` around matched `[i, j)` character-index spans. -/
def splitSpansFast (chars : Array Char) (cursor : Nat) : List (Nat × Nat) → List String
  | [] => [String.ofList (chars.extract cursor chars.size).toList]
  | (i, j) :: rest =>
    String.ofList (chars.extract cursor i).toList :: splitSpansFast chars j rest

/-- Return `true` iff `pattern` matches anywhere in `haystack`. -/
def testPattern (pattern haystack : String) : Except RegexError Bool :=
  (parseRegex pattern).map fun ast =>
    let chars := haystack.toList.toArray
    let tab := evalTable chars ast
    (findFirstIdx tab chars.size 0).isSome

/-- Find the first leftmost-first match span of `pattern` in `haystack`, if any. -/
def findFirst (pattern haystack : String) : Except RegexError (Option MatchSpan) :=
  (parseRegex pattern).map fun ast =>
    let chars := haystack.toList.toArray
    let tab := evalTable chars ast
    (findFirstIdx tab chars.size 0).map fun (i, j) =>
      let offsets := buildByteOffsets chars
      mkMatchSpanFast chars offsets i j

/-- Find all non-overlapping match spans of `pattern` in `haystack`. -/
def findAll (pattern haystack : String) : Except RegexError (Array MatchSpan) :=
  (parseRegex pattern).map fun ast =>
    let chars := haystack.toList.toArray
    let offsets := buildByteOffsets chars
    ((findAllIdx chars ast).map fun (i, j) => mkMatchSpanFast chars offsets i j).toArray

/-- Count all non-overlapping matches of `pattern` in `haystack`. -/
def countMatches (pattern haystack : String) : Except RegexError Nat :=
  (findAll pattern haystack).map Array.size

/-- Replace every non-overlapping match of `pattern` in `haystack` with `replacement`. -/
def replaceAll (pattern haystack replacement : String) : Except RegexError String :=
  (parseRegex pattern).map fun ast =>
    let chars := haystack.toList.toArray
    replaceSpansFast chars replacement 0 (findAllIdx chars ast)

/-- Split `haystack` around all non-overlapping matches of `pattern`. -/
def splitBy (pattern haystack : String) : Except RegexError (Array String) :=
  (parseRegex pattern).map fun ast =>
    let chars := haystack.toList.toArray
    (splitSpansFast chars 0 (findAllIdx chars ast)).toArray

end LeanSwe.RegExp.Internal

import LeanSwe.RegExp.Types

namespace LeanSwe.RegExp.Internal

private def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

private def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

private def isDigitChar (c : Char) : Bool :=
  c >= '0' && c <= '9'

/-- Character matching atom in the regex AST. -/
inductive CharAtom where
  | /-- Any character except newline. -/ any
  | /-- ASCII digit `[0-9]`. -/ digit
  | /-- Non-digit `[^0-9]`. -/ nonDigit
  | /-- Word character `[A-Za-z0-9_]`. -/ word
  | /-- Non-word character. -/ nonWord
  | /-- Whitespace character. -/ space
  | /-- Non-whitespace character. -/ nonSpace
  | /-- Exact literal character. -/ literal (c : Char)
  | /-- Bracket character class. -/ charClass (negated : Bool) (ranges : Array (Char × Char)) (preds : Array CharAtom)
  deriving Repr, BEq, Inhabited

private def matchCharAtom (atom : CharAtom) (c : Char) : Bool :=
  match atom with
  | .any => c != '\n'
  | .digit => isDigitChar c
  | .nonDigit => !isDigitChar c
  | .word => isWordChar c
  | .nonWord => !isWordChar c
  | .space => isSpaceChar c
  | .nonSpace => !isSpaceChar c
  | .literal x => c == x
  | .charClass negated ranges preds =>
    let inRange := ranges.any (fun (lo, hi) => lo <= c && c <= hi)
    let inPred := preds.any (fun p =>
      match p with
      | .digit => isDigitChar c
      | .nonDigit => !isDigitChar c
      | .word => isWordChar c
      | .nonWord => !isWordChar c
      | .space => isSpaceChar c
      | .nonSpace => !isSpaceChar c
      | _ => false)
    let hit := inRange || inPred
    if negated then !hit else hit

/-- Abstract syntax tree for parsed regular expressions. -/
inductive RegexAst where
  | /-- Empty sequence matching zero characters. -/ empty
  | /-- Single character atom. -/ char (atom : CharAtom)
  | /-- Start-of-string anchor `^`. -/ anchorStart
  | /-- End-of-string anchor `$`. -/ anchorEnd
  | /-- Word boundary `\b` or `\B`. -/ wordBoundary (positive : Bool)
  | /-- Concatenation of sub-expressions. -/ seq (items : List RegexAst)
  | /-- Ordered alternation branches. -/ alt (branches : List RegexAst)
  | /-- Bounded or unbounded repetition. -/ rep (inner : RegexAst) (min : Nat) (max? : Option Nat) (greedy : Bool)
  deriving Repr, BEq, Inhabited

/-- Construct an `invalidSyntax` error. -/
def errSyntax (msg : String) : RegexError :=
  { kind := .invalidSyntax, message := msg }

/-- Construct an `unexpectedEof` error. -/
def errEof (msg : String) : RegexError :=
  { kind := .unexpectedEof, message := msg }

/-- Parser cursor state over pattern characters. -/
structure ParseState where
  /-- Pattern characters. -/
  chars : Array Char
  /-- Current index in `chars`. -/
  pos : Nat

/-- Peek current character at parser cursor. -/
def ParseState.peek? (st : ParseState) : Option Char :=
  st.chars[st.pos]?

/-- Advance parser cursor by one character. -/
def ParseState.advance (st : ParseState) : ParseState :=
  { st with pos := st.pos + 1 }

/-- Maximum allowed brace repetition count. -/
def maxRepetitionCount : Nat := 1000

/-- Token parsed inside a character class. -/
inductive ClassToken where
  | /-- Literal character inside class. -/ single (c : Char)
  | /-- Shorthand predicate inside class. -/ pred (p : CharAtom)

/-- Parse an escape sequence inside `[...]`. -/
def parseClassEscape (st : ParseState) : Except RegexError (ClassToken × ParseState) :=
  match st.peek? with
  | none => .error (errEof "unexpected end of pattern in character class escape")
  | some c =>
    let st' := st.advance
    match c with
    | 'd' => .ok (.pred .digit, st')
    | 'D' => .ok (.pred .nonDigit, st')
    | 'w' => .ok (.pred .word, st')
    | 'W' => .ok (.pred .nonWord, st')
    | 's' => .ok (.pred .space, st')
    | 'S' => .ok (.pred .nonSpace, st')
    | 'n' => .ok (.single '\n', st')
    | 'r' => .ok (.single '\r', st')
    | 't' => .ok (.single '\t', st')
    | _ => .ok (.single c, st')

/-- Parse body of a `[...]` character class until `]`. -/
def parseCharClassBody
    (fuel : Nat)
    (st : ParseState)
    (negated : Bool)
    (ranges : Array (Char × Char))
    (preds : Array CharAtom) :
    Except RegexError (CharAtom × ParseState) :=
  match fuel with
  | 0 => .error (errEof "unclosed character class '['")
  | fuel' + 1 =>
    match st.peek? with
    | none => .error (errEof "unclosed character class '['")
    | some ']' =>
      if ranges.isEmpty && preds.isEmpty then
        .error (errSyntax "empty character class '[]'")
      else
        .ok (.charClass negated ranges preds, st.advance)
    | some c =>
      let resTok : Except RegexError (ClassToken × ParseState) :=
        if c == '\\' then parseClassEscape st.advance
        else .ok (.single c, st.advance)
      match resTok with
      | .error e => .error e
      | .ok (.pred p, st1) =>
        parseCharClassBody fuel' st1 negated ranges (preds.push p)
      | .ok (.single lo, st1) =>
        match st1.peek? with
        | some '-' =>
          let stAfterDash := st1.advance
          match stAfterDash.peek? with
          | some ']' =>
            let ranges' := (ranges.push (lo, lo)).push ('-', '-')
            parseCharClassBody fuel' stAfterDash negated ranges' preds
          | none => .error (errEof "unclosed character class '['")
          | some c2 =>
            let resHi : Except RegexError (ClassToken × ParseState) :=
              if c2 == '\\' then parseClassEscape stAfterDash.advance
              else .ok (.single c2, stAfterDash.advance)
            match resHi with
            | .error e => .error e
            | .ok (.pred p, st2) =>
              let ranges' := (ranges.push (lo, lo)).push ('-', '-')
              parseCharClassBody fuel' st2 negated ranges' (preds.push p)
            | .ok (.single hi, st2) =>
              if lo.toNat > hi.toNat then
                .error (errSyntax "character class range is out of order")
              else
                parseCharClassBody fuel' st2 negated (ranges.push (lo, hi)) preds
        | _ =>
          parseCharClassBody fuel' st1 negated (ranges.push (lo, lo)) preds

/-- Parse a `[...]` or `[^...]` character class after `[`. -/
def parseCharClass (fuel : Nat) (st : ParseState) : Except RegexError (CharAtom × ParseState) :=
  match st.peek? with
  | some '^' => parseCharClassBody fuel st.advance true #[] #[]
  | _ => parseCharClassBody fuel st false #[] #[]

private def parseDigits (fuel : Nat) (st : ParseState) (acc : Nat) (count : Nat) :
    Nat × Nat × ParseState :=
  match fuel with
  | 0 => (acc, count, st)
  | fuel' + 1 =>
    match st.peek? with
    | some c =>
      if isDigitChar c then
        let d := c.toNat - '0'.toNat
        parseDigits fuel' st.advance (acc * 10 + d) (count + 1)
      else
        (acc, count, st)
    | none => (acc, count, st)

/-- Parse `{m}`, `{m,}`, or `{m,n}` quantifier bounds after `{`. -/
def parseBraceQuantifier (fuel : Nat) (st : ParseState) :
    Except RegexError (Nat × Option Nat × ParseState) :=
  let (minVal, minDigits, st1) := parseDigits fuel st 0 0
  if minDigits == 0 then
    .error (errSyntax "invalid brace quantifier")
  else if minVal > maxRepetitionCount then
    .error (errSyntax "quantifier count exceeds maximum limit")
  else
    match st1.peek? with
    | none => .error (errEof "unclosed brace quantifier '{'")
    | some '}' => .ok (minVal, some minVal, st1.advance)
    | some ',' =>
      let st2 := st1.advance
      match st2.peek? with
      | none => .error (errEof "unclosed brace quantifier '{'")
      | some '}' => .ok (minVal, none, st2.advance)
      | some _ =>
        let (maxVal, maxDigits, st3) := parseDigits fuel st2 0 0
        if maxDigits == 0 then
          .error (errSyntax "invalid brace quantifier")
        else if maxVal > maxRepetitionCount then
          .error (errSyntax "quantifier count exceeds maximum limit")
        else if maxVal < minVal then
          .error (errSyntax "quantifier upper bound is smaller than lower bound")
        else
          match st3.peek? with
          | some '}' => .ok (minVal, some maxVal, st3.advance)
          | none => .error (errEof "unclosed brace quantifier '{'")
          | some _ => .error (errSyntax "invalid brace quantifier")
    | some _ => .error (errSyntax "invalid brace quantifier")

/-- Parse an escape sequence after `\\`. -/
def parseEscape (st : ParseState) : Except RegexError (RegexAst × ParseState) :=
  match st.peek? with
  | none => .error (errEof "unexpected end of pattern after '\\'")
  | some c =>
    let st' := st.advance
    match c with
    | 'd' => .ok (.char .digit, st')
    | 'D' => .ok (.char .nonDigit, st')
    | 'w' => .ok (.char .word, st')
    | 'W' => .ok (.char .nonWord, st')
    | 's' => .ok (.char .space, st')
    | 'S' => .ok (.char .nonSpace, st')
    | 'b' => .ok (.wordBoundary true, st')
    | 'B' => .ok (.wordBoundary false, st')
    | 'n' => .ok (.char (.literal '\n'), st')
    | 'r' => .ok (.char (.literal '\r'), st')
    | 't' => .ok (.char (.literal '\t'), st')
    | _ => .ok (.char (.literal c), st')

private def applyLazyFlag (st : ParseState) : Bool × ParseState :=
  match st.peek? with
  | some '?' => (false, st.advance)
  | _ => (true, st)

/-- Parse an optional quantifier suffix after a regex atom. -/
def parseQuantifierSuffix (fuel : Nat) (atom : RegexAst) (st : ParseState) :
    Except RegexError (RegexAst × ParseState) :=
  match st.peek? with
  | some '*' =>
    let (greedy, st1) := applyLazyFlag st.advance
    .ok (.rep atom 0 none greedy, st1)
  | some '+' =>
    let (greedy, st1) := applyLazyFlag st.advance
    .ok (.rep atom 1 none greedy, st1)
  | some '?' =>
    let (greedy, st1) := applyLazyFlag st.advance
    .ok (.rep atom 0 (some 1) greedy, st1)
  | some '{' =>
    match parseBraceQuantifier fuel st.advance with
    | .error e => .error e
    | .ok (minVal, maxVal?, st1) =>
      let (greedy, st2) := applyLazyFlag st1
      .ok (.rep atom minVal maxVal? greedy, st2)
  | _ => .ok (atom, st)

/-- Reject ungrouped consecutive quantifiers. -/
def rejectExtraQuantifier (st : ParseState) : Except RegexError Unit :=
  match st.peek? with
  | some '*' | some '+' | some '?' | some '{' =>
    .error (errSyntax "nested quantifier is not supported")
  | _ => .ok ()

mutual
/-- Parse an alternation expression. -/
def parseAlternation (fuel : Nat) (st : ParseState) :
    Except RegexError (RegexAst × ParseState) :=
  match fuel with
  | 0 => .error (errEof "pattern nesting exceeded limit")
  | fuel' + 1 =>
    parseAltLoop fuel' st #[]

/-- Parse remaining `|`-separated branches. -/
def parseAltLoop (fuel : Nat) (st : ParseState) (branches : Array RegexAst) :
    Except RegexError (RegexAst × ParseState) :=
  match fuel with
  | 0 => .error (errEof "pattern nesting exceeded limit")
  | fuel' + 1 =>
    match parseSeqLoop fuel' st #[] with
    | .error e => .error e
    | .ok (seqAst, st1) =>
      let branches' := branches.push seqAst
      match st1.peek? with
      | some '|' => parseAltLoop fuel' st1.advance branches'
      | _ =>
        if branches'.size == 1 then
          .ok (branches'[0]!, st1)
        else
          .ok (.alt branches'.toList, st1)

/-- Parse a sequence of quantified atoms. -/
def parseSeqLoop (fuel : Nat) (st : ParseState) (items : Array RegexAst) :
    Except RegexError (RegexAst × ParseState) :=
  match fuel with
  | 0 => .error (errEof "pattern nesting exceeded limit")
  | fuel' + 1 =>
    match st.peek? with
    | none | some '|' | some ')' =>
      if items.isEmpty then
        .ok (.empty, st)
      else if items.size == 1 then
        .ok (items[0]!, st)
      else
        .ok (.seq items.toList, st)
    | some c =>
      if c == '*' || c == '+' || c == '?' || c == '{' then
        .error (errSyntax "quantifier has nothing to repeat")
      else
        match parseAtom fuel' st with
        | .error e => .error e
        | .ok (atom, st1) =>
          match parseQuantifierSuffix fuel' atom st1 with
          | .error e => .error e
          | .ok (quantAst, st2) =>
            match quantAst with
            | .rep _ _ _ _ =>
              match rejectExtraQuantifier st2 with
              | .error e => .error e
              | .ok () => parseSeqLoop fuel' st2 (items.push quantAst)
            | _ =>
              parseSeqLoop fuel' st2 (items.push quantAst)

/-- Parse a single regex atom. -/
def parseAtom (fuel : Nat) (st : ParseState) :
    Except RegexError (RegexAst × ParseState) :=
  match fuel with
  | 0 => .error (errEof "unexpected end of pattern")
  | fuel' + 1 =>
    match st.peek? with
    | none => .error (errEof "unexpected end of pattern")
    | some '.' => .ok (.char .any, st.advance)
    | some '^' => .ok (.anchorStart, st.advance)
    | some '$' => .ok (.anchorEnd, st.advance)
    | some '\\' => parseEscape st.advance
    | some '[' =>
      match parseCharClass (fuel' + 1) st.advance with
      | .error e => .error e
      | .ok (atom, st1) => .ok (.char atom, st1)
    | some '(' =>
      let st1 := st.advance
      let stBody :=
        if st1.peek? == some '?' then
          let stQ := st1.advance
          if stQ.peek? == some ':' then stQ.advance else st1
        else
          st1
      match parseAlternation fuel' stBody with
      | .error e => .error e
      | .ok (inner, st2) =>
        match st2.peek? with
        | some ')' => .ok (inner, st2.advance)
        | none => .error (errEof "unclosed group '('")
        | some _ => .error (errSyntax "expected ')'")
    | some c => .ok (.char (.literal c), st.advance)
end

/-- Ensure a `RegexError` always carries a non-empty diagnostic message. -/
def ensureNonEmptyMsg (fallback : String) (e : RegexError) : RegexError :=
  if e.message.isEmpty then { e with message := fallback } else e

/-- Parse a regex pattern string into an AST. -/
def parseRegex (pattern : String) : Except RegexError RegexAst :=
  if pattern.isEmpty then
    .ok .empty
  else
    let chars := pattern.toList.toArray
    let st : ParseState := { chars := chars, pos := 0 }
    let fuel := chars.size * 2 + 8
    match parseAlternation fuel st with
    | .error e => .error (ensureNonEmptyMsg "invalid regular expression" e)
    | .ok (ast, stEnd) =>
      match stEnd.peek? with
      | none => .ok ast
      | some ')' => .error (errSyntax "unmatched ')'")
      | some _ => .error (errSyntax "unexpected trailing pattern characters")

/-- NFA instruction for Thompson / PikeVM simulation. -/
inductive NfaState where
  | /-- Accepting state. -/ accept
  | /-- Match character atom and transition to `next`. -/ char (atom : CharAtom) (next : Nat)
  | /-- Start-of-string assertion. -/ anchorStart (next : Nat)
  | /-- End-of-string assertion. -/ anchorEnd (next : Nat)
  | /-- Word boundary assertion. -/ wordBoundary (positive : Bool) (next : Nat)
  | /-- Ordered epsilon split (`first` higher priority than `second`). -/ split (first second : Nat)
  | /-- Unconditional epsilon jump. -/ jmp (next : Nat)
  deriving Repr, Inhabited

/-- Append an NFA state and return its index. -/
def emitState (nfa : Array NfaState) (st : NfaState) : Nat × Array NfaState :=
  (nfa.size, nfa.push st)

mutual
/-- Compile a regex AST node into NFA states ending at `nextPc`. -/
def compileAst (ast : RegexAst) (nextPc : Nat) (nfa : Array NfaState) :
    Nat × Array NfaState :=
  match ast with
  | .empty => (nextPc, nfa)
  | .char atom => emitState nfa (.char atom nextPc)
  | .anchorStart => emitState nfa (.anchorStart nextPc)
  | .anchorEnd => emitState nfa (.anchorEnd nextPc)
  | .wordBoundary pos => emitState nfa (.wordBoundary pos nextPc)
  | .seq items => compileSeq items nextPc nfa
  | .alt branches => compileAlt branches nextPc nfa
  | .rep inner min max? greedy =>
    let tail := compileRepTail inner max? min greedy nextPc nfa
    compileCopies inner min tail.1 tail.2

/-- Compile a sequence of AST nodes. -/
def compileSeq (items : List RegexAst) (nextPc : Nat) (nfa : Array NfaState) :
    Nat × Array NfaState :=
  match items with
  | [] => (nextPc, nfa)
  | item :: rest =>
    let (restPc, nfa1) := compileSeq rest nextPc nfa
    compileAst item restPc nfa1

/-- Compile alternation branches into ordered splits. -/
def compileAlt (branches : List RegexAst) (nextPc : Nat) (nfa : Array NfaState) :
    Nat × Array NfaState :=
  match branches with
  | [] => (nextPc, nfa)
  | [b] => compileAst b nextPc nfa
  | b :: rest =>
    let (bPc, nfa1) := compileAst b nextPc nfa
    let (restPc, nfa2) := compileAlt rest nextPc nfa1
    emitState nfa2 (.split bPc restPc)

/-- Compile `count` mandatory repetitions of `inner`. -/
def compileCopies (inner : RegexAst) (count : Nat) (nextPc : Nat) (nfa : Array NfaState) :
    Nat × Array NfaState :=
  match count with
  | 0 => (nextPc, nfa)
  | k + 1 =>
    let (tailPc, nfa1) := compileCopies inner k nextPc nfa
    compileAst inner tailPc nfa1

/-- Compile `count` optional repetitions of `inner`. -/
def compileOptCopies (inner : RegexAst) (count : Nat) (greedy : Bool)
    (nextPc : Nat) (nfa : Array NfaState) : Nat × Array NfaState :=
  match count with
  | 0 => (nextPc, nfa)
  | k + 1 =>
    let (tailPc, nfa1) := compileOptCopies inner k greedy nextPc nfa
    let (bodyPc, nfa2) := compileAst inner tailPc nfa1
    let st := if greedy then NfaState.split bodyPc tailPc else NfaState.split tailPc bodyPc
    emitState nfa2 st

/-- Compile the variable tail of a repetition AST node. -/
def compileRepTail (inner : RegexAst) (max? : Option Nat) (min : Nat) (greedy : Bool)
    (nextPc : Nat) (nfa : Array NfaState) : Nat × Array NfaState :=
  match max? with
  | none =>
    let (splitPc, nfa1) := emitState nfa (.jmp nextPc)
    let (bodyPc, nfa2) := compileAst inner splitPc nfa1
    let st := if greedy then NfaState.split bodyPc nextPc else NfaState.split nextPc bodyPc
    let nfa3 := if _ : splitPc < nfa2.size then nfa2.set splitPc st else nfa2
    (splitPc, nfa3)
  | some max =>
    compileOptCopies inner (max - min) greedy nextPc nfa
end

/-- Compile a parsed regex AST into `(entryPc, nfa)`. -/
def compileRegex (ast : RegexAst) : Nat × Array NfaState :=
  let (acceptPc, nfa0) := emitState #[] .accept
  compileAst ast acceptPc nfa0

/-- Reflexivity on `String.Pos`. -/
theorem pos_le_refl {s : String} (p : s.Pos) : p ≤ p :=
  String.Pos.le_iff.mpr (Nat.le_refl _)

/-- Transitivity on `String.Pos`. -/
theorem pos_le_trans {s : String} {a b c : s.Pos} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  String.Pos.le_iff.mpr (Nat.le_trans (String.Pos.le_iff.mp h1) (String.Pos.le_iff.mp h2))

/-- Weaken strict order to non-strict order on `String.Pos`. -/
theorem pos_le_of_lt {s : String} {a b : s.Pos} (h : a < b) : a ≤ b :=
  String.Pos.le_iff.mpr (Nat.le_of_lt (String.Pos.lt_iff.mp h))

/-- Validated match span of positions inside `hay`. -/
structure PosSpan (hay : String) where
  /-- Match start position. -/
  startPos : hay.Pos
  /-- Match end position. -/
  stopPos : hay.Pos
  /-- Proof that `startPos ≤ stopPos`. -/
  hle : startPos ≤ stopPos

/-- Active PikeVM thread at `curPos`. -/
structure Thread (hay : String) (curPos : hay.Pos) where
  /-- Current NFA instruction pointer. -/
  pc : Nat
  /-- Recorded match start position. -/
  startPos : hay.Pos
  /-- Proof that `startPos ≤ curPos`. -/
  hle : startPos ≤ curPos

private def isWordOpt (c? : Option Char) : Bool :=
  match c? with
  | none => false
  | some c => isWordChar c

/-- Expand epsilon transitions from `pc` at `curPos`. -/
def addThread
    (nfa : Array NfaState)
    (hay : String)
    (curPos : hay.Pos)
    (prevChar? : Option Char)
    (nextChar? : Option Char)
    (pc : Nat)
    (startPos : hay.Pos)
    (hle : startPos ≤ curPos)
    (visited : Array Bool)
    (out : Array (Thread hay curPos))
    (best? : Option (PosSpan hay))
    (fuel : Nat) :
    Array Bool × Array (Thread hay curPos) × Option (PosSpan hay) × Bool :=
  match fuel with
  | 0 => (visited, out, best?, false)
  | fuel' + 1 =>
    if hVis : pc < visited.size then
      if visited[pc] then
        (visited, out, best?, false)
      else
        let visited' := visited.set pc true
        match nfa[pc]? with
        | none => (visited', out, best?, false)
        | some .accept =>
          let cand : PosSpan hay := { startPos := startPos, stopPos := curPos, hle := hle }
          let best'' :=
            match best? with
            | none => some cand
            | some prevBest =>
              if startPos ≤ prevBest.startPos then some cand else some prevBest
          (visited', out, best'', true)
        | some (.char _ _) =>
          (visited', out.push { pc := pc, startPos := startPos, hle := hle }, best?, false)
        | some (.jmp nextPc) =>
          addThread nfa hay curPos prevChar? nextChar? nextPc startPos hle visited' out best? fuel'
        | some (.anchorStart nextPc) =>
          if curPos.offset.byteIdx == 0 then
            addThread nfa hay curPos prevChar? nextChar? nextPc startPos hle visited' out best? fuel'
          else
            (visited', out, best?, false)
        | some (.anchorEnd nextPc) =>
          if curPos.offset.byteIdx == hay.utf8ByteSize then
            addThread nfa hay curPos prevChar? nextChar? nextPc startPos hle visited' out best? fuel'
          else
            (visited', out, best?, false)
        | some (.wordBoundary posFlag nextPc) =>
          let isBound := isWordOpt prevChar? != isWordOpt nextChar?
          if isBound == posFlag then
            addThread nfa hay curPos prevChar? nextChar? nextPc startPos hle visited' out best? fuel'
          else
            (visited', out, best?, false)
        | some (.split firstPc secondPc) =>
          let (v1, o1, b1, hit1) :=
            addThread nfa hay curPos prevChar? nextChar? firstPc startPos hle visited' out best? fuel'
          if hit1 then
            (v1, o1, b1, true)
          else
            addThread nfa hay curPos prevChar? nextChar? secondPc startPos hle v1 o1 b1 fuel'
    else
      (visited, out, best?, false)

/-- Expand epsilon closure across active `threads` in priority order. -/
def expandThreads
    (nfa : Array NfaState)
    (hay : String)
    (curPos : hay.Pos)
    (prevChar? : Option Char)
    (nextChar? : Option Char)
    (threads : Array (Thread hay curPos))
    (idx : Nat)
    (visited : Array Bool)
    (out : Array (Thread hay curPos))
    (best? : Option (PosSpan hay)) :
    Array Bool × Array (Thread hay curPos) × Option (PosSpan hay) × Bool :=
  if h : idx < threads.size then
    let th := threads[idx]
    let (v1, o1, b1, hit1) :=
      addThread nfa hay curPos prevChar? nextChar? th.pc th.startPos th.hle visited out best? nfa.size
    if hit1 then
      (v1, o1, b1, true)
    else
      expandThreads nfa hay curPos prevChar? nextChar? threads (idx + 1) v1 o1 b1
  else
    (visited, out, best?, false)
termination_by threads.size - idx

private def advanceThreads
    (nfa : Array NfaState)
    (hay : String)
    (curPos : hay.Pos)
    (nextPos : hay.Pos)
    (hleStep : curPos ≤ nextPos)
    (c : Char)
    (threads : Array (Thread hay curPos)) :
    Array (Thread hay nextPos) :=
  threads.foldl (fun acc th =>
    match (nfa[th.pc]? : Option NfaState) with
    | some (.char atom nextPc) =>
      if matchCharAtom atom c then
        acc.push { pc := nextPc, startPos := th.startPos, hle := pos_le_trans th.hle hleStep }
      else
        acc
    | _ => acc
  ) #[]

/-- Run PikeVM search loop from `curPos` until match completes or string ends. -/
def runVmLoop
    (nfa : Array NfaState)
    (entryPc : Nat)
    (hay : String)
    (curPos : hay.Pos)
    (prevChar? : Option Char)
    (threads : Array (Thread hay curPos))
    (best? : Option (PosSpan hay)) :
    Option (PosSpan hay) :=
  let nextChar? : Option Char :=
    if h : curPos ≠ hay.endPos then some (curPos.get h) else none
  let initVis := Array.replicate nfa.size false
  let (vis1, step1, best1, hit1) :=
    expandThreads nfa hay curPos prevChar? nextChar? threads 0 initVis #[] best?
  let (step2, best2) :=
    if hit1 then
      (step1, best1)
    else
      match best1 with
      | some _ => (step1, best1)
      | none =>
        let (_, o2, b2, _) :=
          addThread nfa hay curPos prevChar? nextChar? entryPc curPos (pos_le_refl curPos)
            vis1 step1 best1 nfa.size
        (o2, b2)
  if hEnd : curPos = hay.endPos then
    best2
  else if step2.isEmpty && best2.isSome then
    best2
  else
    let c := curPos.get hEnd
    let hleStep : curPos ≤ curPos.next hEnd := pos_le_of_lt String.Pos.lt_next
    let nextThreads := advanceThreads nfa hay curPos (curPos.next hEnd) hleStep c step2
    runVmLoop nfa entryPc hay (curPos.next hEnd) (some c) nextThreads best2
termination_by hay.utf8ByteSize - curPos.offset.byteIdx
decreasing_by
  have hlt : curPos.offset.byteIdx < (curPos.next hEnd).offset.byteIdx :=
    String.Pos.lt_iff.mp String.Pos.lt_next
  have hle : (curPos.next hEnd).offset.byteIdx ≤ hay.utf8ByteSize :=
    (curPos.next hEnd).isValid.le_utf8ByteSize
  omega

/-- Find first match span starting at or after `startPos`. -/
def findFirstSpanFrom
    (nfa : Array NfaState)
    (entryPc : Nat)
    (hay : String)
    (startPos : hay.Pos)
    (prevChar? : Option Char) :
    Option (PosSpan hay) :=
  runVmLoop nfa entryPc hay startPos prevChar? #[] none

/-- Convert an internal `PosSpan` to a public `MatchSpan`. -/
def posSpanToMatchSpan (hay : String) (sp : PosSpan hay) : MatchSpan :=
  { matched := String.extract sp.startPos sp.stopPos
    startByte := sp.startPos.offset.byteIdx
    stopByte := sp.stopPos.offset.byteIdx }

/-- Collect all non-overlapping match spans starting at or after `cursor`. -/
def findAllSpansLoop
    (nfa : Array NfaState)
    (entryPc : Nat)
    (hay : String)
    (cursor : hay.Pos)
    (prevChar? : Option Char)
    (acc : Array (PosSpan hay)) :
    Array (PosSpan hay) :=
  match findFirstSpanFrom nfa entryPc hay cursor prevChar? with
  | none => acc
  | some sp =>
    let acc' := acc.push sp
    if _hNonEmpty : sp.startPos < sp.stopPos then
      if hAdvance : cursor < sp.stopPos then
        let prev' :=
          if hne : sp.stopPos ≠ hay.startPos then
            some ((sp.stopPos.prev hne).get (by
              intro heq
              have hlt : sp.stopPos.prev hne < sp.stopPos := String.Pos.prev_lt
              have hle : sp.stopPos ≤ hay.endPos := String.Pos.le_endPos sp.stopPos
              rw [heq] at hlt
              exact absurd hlt (Nat.not_lt_of_le (String.Pos.le_iff.mp hle))))
          else
            prevChar?
        findAllSpansLoop nfa entryPc hay sp.stopPos prev' acc'
      else if hNotEnd : cursor ≠ hay.endPos then
        let c := cursor.get hNotEnd
        findAllSpansLoop nfa entryPc hay (cursor.next hNotEnd) (some c) acc'
      else
        acc'
    else
      let basePos := if cursor < sp.stopPos then sp.stopPos else cursor
      if hNotEnd : basePos ≠ hay.endPos then
        let c := basePos.get hNotEnd
        findAllSpansLoop nfa entryPc hay (basePos.next hNotEnd) (some c) acc'
      else
        acc'
termination_by hay.utf8ByteSize - cursor.offset.byteIdx
decreasing_by
  · have hlt : cursor.offset.byteIdx < sp.stopPos.offset.byteIdx :=
      String.Pos.lt_iff.mp hAdvance
    have hle : sp.stopPos.offset.byteIdx ≤ hay.utf8ByteSize :=
      sp.stopPos.isValid.le_utf8ByteSize
    omega
  · have hlt : cursor.offset.byteIdx < (cursor.next hNotEnd).offset.byteIdx :=
      String.Pos.lt_iff.mp String.Pos.lt_next
    have hle : (cursor.next hNotEnd).offset.byteIdx ≤ hay.utf8ByteSize :=
      (cursor.next hNotEnd).isValid.le_utf8ByteSize
    omega
  · have hbase : cursor.offset.byteIdx ≤ basePos.offset.byteIdx := by
      dsimp only [basePos]
      split
      · next hlt => exact Nat.le_of_lt (String.Pos.lt_iff.mp hlt)
      · exact Nat.le_refl _
    have hlt : basePos.offset.byteIdx < (basePos.next hNotEnd).offset.byteIdx :=
      String.Pos.lt_iff.mp String.Pos.lt_next
    have hle : (basePos.next hNotEnd).offset.byteIdx ≤ hay.utf8ByteSize :=
      (basePos.next hNotEnd).isValid.le_utf8ByteSize
    dsimp only [basePos] at hbase hlt hle
    omega

/-- Compile `pattern` and find all non-overlapping `PosSpan` matches in `haystack`. -/
def findAllSpans (pattern haystack : String) : Except RegexError (Array (PosSpan haystack)) :=
  match parseRegex pattern with
  | .error e => .error e
  | .ok ast =>
    let (entryPc, nfa) := compileRegex ast
    .ok (findAllSpansLoop nfa entryPc haystack haystack.startPos none #[])

/-- Compile `pattern` and find the first `PosSpan` match in `haystack`. -/
def findFirstSpan (pattern haystack : String) : Except RegexError (Option (PosSpan haystack)) :=
  match parseRegex pattern with
  | .error e => .error e
  | .ok ast =>
    let (entryPc, nfa) := compileRegex ast
    .ok (findFirstSpanFrom nfa entryPc haystack haystack.startPos none)

/-- Replace matched `PosSpan` intervals in `haystack` with `replacement`. -/
def replaceFromSpans (haystack replacement : String) (spans : Array (PosSpan haystack)) :
    String :=
  let (acc, cursor) :=
    spans.foldl (fun (acc, prev) sp =>
      let prefixChunk := String.extract prev sp.startPos
      (acc ++ prefixChunk ++ replacement, sp.stopPos)
    ) ("", haystack.startPos)
  acc ++ String.extract cursor haystack.endPos

/-- Split `haystack` around matched `PosSpan` intervals. -/
def splitFromSpans (haystack : String) (spans : Array (PosSpan haystack)) :
    Array String :=
  let (parts, cursor) :=
    spans.foldl (fun (acc, prev) sp =>
      (acc.push (String.extract prev sp.startPos), sp.stopPos)
    ) (#[], haystack.startPos)
  parts.push (String.extract cursor haystack.endPos)

/-- Return `true` iff `pattern` matches anywhere in `haystack`. -/
def testPattern (pattern haystack : String) : Except RegexError Bool :=
  (findFirstSpan pattern haystack).map Option.isSome

/-- Find the first leftmost-first match span of `pattern` in `haystack`, if any. -/
def findFirst (pattern haystack : String) : Except RegexError (Option MatchSpan) :=
  (findFirstSpan pattern haystack).map (Option.map (posSpanToMatchSpan haystack))

/-- Find all non-overlapping match spans of `pattern` in `haystack`. -/
def findAll (pattern haystack : String) : Except RegexError (Array MatchSpan) :=
  (findAllSpans pattern haystack).map (Array.map (posSpanToMatchSpan haystack))

/-- Count all non-overlapping matches of `pattern` in `haystack`. -/
def countMatches (pattern haystack : String) : Except RegexError Nat :=
  (findAll pattern haystack).map Array.size

/-- Replace every non-overlapping match of `pattern` in `haystack` with `replacement`. -/
def replaceAll (pattern haystack replacement : String) : Except RegexError String :=
  (findAllSpans pattern haystack).map (replaceFromSpans haystack replacement)

/-- Split `haystack` around all non-overlapping matches of `pattern`. -/
def splitBy (pattern haystack : String) : Except RegexError (Array String) :=
  (findAllSpans pattern haystack).map (splitFromSpans haystack)

end LeanSwe.RegExp.Internal

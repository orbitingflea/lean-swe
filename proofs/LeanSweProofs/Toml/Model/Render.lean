import LeanSwe.Toml.Types
import LeanSweProofs.Toml.Model.Equiv
import LeanSweProofs.Toml.Model.Tape
import LeanSweProofs.NumParse.Model

namespace LeanSwe.Toml.Model

open LeanSwe.Toml
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Decode a `BasicEscapeAtom` into its Unicode scalar `Char`, returning `none` if invalid. -/
def decodeBasicEscape : BasicEscapeAtom → Option Char
  | .backspace => some '\x08'
  | .tab => some '\t'
  | .linefeed => some '\n'
  | .formfeed => some '\x0c'
  | .carriageReturn => some '\r'
  | .quote => some '"'
  | .backslash => some '\\'
  | .unicode4 h1 h2 h3 h4 =>
    match hexValModel? h1, hexValModel? h2, hexValModel? h3, hexValModel? h4 with
    | some d1, some d2, some d3, some d4 =>
      let code := ((d1 * 16 + d2) * 16 + d3) * 16 + d4
      if code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF) then none
      else some (Char.ofNat code)
    | _, _, _, _ => none
  | .unicode8 h1 h2 h3 h4 h5 h6 h7 h8 =>
    match hexValModel? h1, hexValModel? h2, hexValModel? h3, hexValModel? h4,
          hexValModel? h5, hexValModel? h6, hexValModel? h7, hexValModel? h8 with
    | some d1, some d2, some d3, some d4, some d5, some d6, some d7, some d8 =>
      let code := ((((((d1 * 16 + d2) * 16 + d3) * 16 + d4) * 16 + d5) * 16 + d6) * 16 + d7) * 16 + d8
      if code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF) then none
      else some (Char.ofNat code)
    | _, _, _, _, _, _, _, _ => none

/-- Render the backslash-prefixed source characters for a `BasicEscapeAtom`. -/
def renderBasicEscapeChars : BasicEscapeAtom → List Char
  | .backspace => ['\\', 'b']
  | .tab => ['\\', 't']
  | .linefeed => ['\\', 'n']
  | .formfeed => ['\\', 'f']
  | .carriageReturn => ['\\', 'r']
  | .quote => ['\\', '"']
  | .backslash => ['\\', '\\']
  | .unicode4 h1 h2 h3 h4 => ['\\', 'u', h1, h2, h3, h4]
  | .unicode8 h1 h2 h3 h4 h5 h6 h7 h8 => ['\\', 'U', h1, h2, h3, h4, h5, h6, h7, h8]

/-- Render a character list using per-character `BasicCharAtom` choices for `"..."`. -/
def renderBasicAtoms : List Char → List BasicCharAtom → Option (List Char)
  | [], [] => some []
  | c :: cs, .plain :: atoms =>
    if c != '"' && c != '\\' && c != '\n' && c != '\r' && !isDisallowedControl c then do
      let rest ← renderBasicAtoms cs atoms
      some (c :: rest)
    else none
  | c :: cs, .escape esc :: atoms =>
    match decodeBasicEscape esc with
    | some c' =>
      if c == c' then do
        let rest ← renderBasicAtoms cs atoms
        some (renderBasicEscapeChars esc ++ rest)
      else none
    | none => none
  | _, _ => none

/-- Render a character list using `MultilineBasicAtom` choices for `"""..."""`. -/
def renderMultilineAtoms (forbidLeadingNl afterTrim : Bool) (quoteRun : Nat) :
    List Char → List MultilineBasicAtom → Option (List Char)
  | [], [] => some []
  | c :: cs, .plain :: atoms =>
    if c == '\\' || c == '\r' || isDisallowedControl c then none
    else if forbidLeadingNl && c == '\n' then none
    else if afterTrim && (isModelHorizWs c || c == '\n') then none
    else if c == '"' then
      if quoteRun ≥ 2 then none
      else do
        let rest ← renderMultilineAtoms false false (quoteRun + 1) cs atoms
        some (c :: rest)
    else do
      let rest ← renderMultilineAtoms false false 0 cs atoms
      some (c :: rest)
  | c :: cs, .escape esc :: atoms =>
    match decodeBasicEscape esc with
    | some c' =>
      if c == c' then do
        let rest ← renderMultilineAtoms false false 0 cs atoms
        some (renderBasicEscapeChars esc ++ rest)
      else none
    | none => none
  | cs, .lineTrim ws1 ws2 :: atoms =>
    if isHorizWsStr ws1 && isHorizAndNlStr ws2 then do
      let rest ← renderMultilineAtoms false true 0 cs atoms
      some ('\\' :: ws1.toList ++ '\n' :: ws2.toList ++ rest)
    else none
  | _, _ => none

/-- Render a TOML key segment according to `KeyStyle`, returning `none` if invalid for that style. -/
def renderKey (k : String) : KeyStyle → Option String
  | .bare => if isValidBareKey k then some k else none
  | .basic none => some ("\"" ++ escapeBasicBody false k ++ "\"")
  | .basic (some atoms) => do
    let cs ← renderBasicAtoms k.toList atoms
    some ("\"" ++ String.ofList cs ++ "\"")
  | .literal =>
    if isSingleLineClean k && !k.contains '\'' then some ("'" ++ k ++ "'") else none

/-- Render continuation `. key` segments of a `DottedKeyTape`. -/
def renderDottedKeyCont : List DottedSegCont → Option String
  | [] => some ""
  | seg :: rest =>
    if !isHorizWsStr seg.wsBeforeDot || !isHorizWsStr seg.wsAfterDot then none
    else do
      let rk ← renderKey seg.key seg.style
      let tail ← renderDottedKeyCont rest
      some (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk ++ tail)

/-- Render a `DottedKeyTape` into TOML 1.0 surface text. -/
def renderDottedKey (dk : DottedKeyTape) : Option String := do
  let rk0 ← renderKey dk.firstKey dk.firstStyle
  let tail ← renderDottedKeyCont dk.rest
  some (rk0 ++ tail)

/-- Render a TOML string literal according to `StringStyle`, returning `none` if invalid for that style. -/
def renderStringLiteral (s : String) : StringStyle → Option String
  | .basic none => some ("\"" ++ escapeBasicBody false s ++ "\"")
  | .basic (some atoms) => do
    let cs ← renderBasicAtoms s.toList atoms
    some ("\"" ++ String.ofList cs ++ "\"")
  | .multilineBasic none =>
    some ("\"\"\"\n" ++ escapeBasicBody true s ++ "\"\"\"")
  | .multilineBasic (some (leadNl, atoms)) => do
    let cs ← renderMultilineAtoms (!leadNl) false 0 s.toList atoms
    some ((if leadNl then "\"\"\"\n" else "\"\"\"") ++ String.ofList cs ++ "\"\"\"")
  | .literal =>
    if isSingleLineClean s && !s.contains '\'' then some ("'" ++ s ++ "'") else none
  | .multilineLiteral leadNl =>
    let clean := s.toList.all fun c => !isDisallowedControl c && c != '\r'
    let leadOk := leadNl || s.toList.head? != some '\n'
    if clean && leadOk && !containsSubstr s "'''" then
      some ((if leadNl then "'''\n" else "'''") ++ s ++ "'''")
    else
      none

/-- Check whether `s` is a valid lowercase-prefixed or decimal integer token evaluating to `n`. -/
def isValidIntLex (s : String) (n : Int64) : Bool :=
  let noBadPrefix :=
    !(s.startsWith "0X" || s.startsWith "0O" || s.startsWith "0B" ||
      s.startsWith "+0X" || s.startsWith "+0O" || s.startsWith "+0B" ||
      s.startsWith "-0X" || s.startsWith "-0O" || s.startsWith "-0B")
  let noTerm := s.toList.all fun c =>
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && !isDisallowedControl c
  let noExpUnlessHex :=
    if s.startsWith "0x" then true else !(s.contains 'e' || s.contains 'E')
  noBadPrefix && noTerm && noExpUnlessHex &&
    (match parseInt64Model s with
     | .ok parsed => parsed == n
     | .error _ => false)

/-- Format an `Int64` in canonical base-10 decimal. -/
def formatInt64Canonical (n : Int64) : String :=
  toString n.toInt

/-- Check whether `s` is a valid TOML 1.0 float token evaluating via `parseFloatModel` to a `FloatEquiv` float. -/
def isValidFloatLex (s : String) (f : Float) : Bool :=
  let hasFloatMarker :=
    s.contains '.' || s.contains 'e' || s.contains 'E' ||
    s == "inf" || s == "+inf" || s == "-inf" ||
    s == "nan" || s == "+nan" || s == "-nan"
  let noTerm := s.toList.all fun c =>
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c
  hasFloatMarker && noTerm &&
    (match parseFloatModel s with
     | .ok g => (g.isNaN && f.isNaN) || (g == f)
     | .error _ => false)

/-- Render `Std.Time.PlainDate` as `YYYY-MM-DD`, returning `none` if out of `0000..9999`. -/
def renderDate (d : Std.Time.PlainDate) : Option String :=
  if validTomlDate d then
    some (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat)
  else none

/-- Render `Std.Time.PlainTime` as `HH:MM:SS(.frac)?` using optional fractional digit string `fracLex`. -/
def renderTime (t : Std.Time.PlainTime) (fracLex : Option String) : Option String :=
  if !validTomlTime t then none
  else
    match fracLex with
    | none =>
      if t.nanosecond.val == 0 then
        some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat)
      else none
    | some ds =>
      if !ds.isEmpty && ds.toList.all isAsciiDigitModel &&
          fracDigitsToNanosModel ds.toList == t.nanosecond.val.toNat then
        some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
          padNatZero 2 t.second.val.toNat ++ "." ++ ds)
      else none

/-- Render `Std.Time.TimeZone.Offset` according to `OffsetStyle`. -/
def renderOffset (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) : Option String :=
  if !validTomlOffset o then none
  else if o.second.val == 0 then
    match style with
    | .upperZ => some "Z"
    | .lowerZ => some "z"
    | .numeric => some "+00:00"
    | .negZero => some "-00:00"
  else
    let sign := if o.second.val < 0 then "-" else "+"
    let absMin := o.second.val.natAbs / 60
    some (sign ++ padNatZero 2 (absMin / 60) ++ ":" ++ padNatZero 2 (absMin % 60))

/-- Render a `DateTimeSep` as a single-character string. -/
def renderDateTimeSep : DateTimeSep → String
  | .upperT => "T"
  | .lowerT => "t"
  | .space => " "

/-- Look up key `k` in a `SkeletonNode` association list. -/
def assocLookupSkel (k : String) : List (String × SkeletonNode) → Option SkeletonNode
  | [] => none
  | (k', v) :: rest => if k == k' then some v else assocLookupSkel k rest

/-- Insert or replace key `k` in a `SkeletonNode` association list. -/
def assocSetSkel (k : String) (v : SkeletonNode) : List (String × SkeletonNode) → List (String × SkeletonNode)
  | [] => [(k, v)]
  | (k', old) :: rest =>
    if k == k' then (k', v) :: rest
    else (k', old) :: assocSetSkel k v rest

/-- Apply a skeleton update along a dotted key path while extracting the target `TomlValue` from `docEntries`. -/
def insertDottedAndLookup :
    List (String × TomlValue) → List (String × SkeletonNode) → List String →
      Option (List (String × SkeletonNode) × TomlValue)
  | _, _, [] => none
  | docEntries, skel, [k] =>
    match assocLookupSkel k skel, lookupKeyList k docEntries with
    | none, some v =>
      let node := match v with | .table _ => SkeletonNode.inlineTable | _ => SkeletonNode.leaf
      some (assocSetSkel k node skel, v)
    | _, _ => none
  | docEntries, skel, k :: k' :: rest =>
    match lookupKeyList k docEntries with
    | some (.table subDoc) =>
      match assocLookupSkel k skel with
      | none => do
        let (nextSub, v) ← insertDottedAndLookup subDoc.toList [] (k' :: rest)
        some (assocSetSkel k (.table .dotted nextSub) skel, v)
      | some (.table .subtableImplicit subSkel) | some (.table .dotted subSkel) => do
        let (nextSub, v) ← insertDottedAndLookup subDoc.toList subSkel (k' :: rest)
        some (assocSetSkel k (.table .dotted nextSub) skel, v)
      | _ => none
    | _ => none

mutual
  /-- Verify that `SkeletonNode` matches the container shape and child coverage of a `TomlValue`. -/
  def skelNodeMatchesValue : SkeletonNode → TomlValue → Bool
    | .leaf, .table _ => false
    | .leaf, _ => true
    | .inlineTable, .table _ => true
    | .inlineTable, _ => false
    | .table _ subSkel, .table subDoc => skelMatchesEntries subSkel subDoc.toList
    | .table _ _, _ => false
    | .aot elems, .array xs => skelMatchesAot elems xs.toList
    | .aot _, _ => false
  termination_by sn _ => sizeOf sn * 2
  decreasing_by all_goals simp +arith

  /-- Verify bidirectional key coverage between `skel` and `docEntries`. -/
  def skelMatchesEntries (skel : List (String × SkeletonNode))
      (docEntries : List (String × TomlValue)) : Bool :=
    (docEntries.all fun p => (assocLookupSkel p.1 skel).isSome) &&
      skelMatchesEntriesAll skel docEntries
  termination_by sizeOf skel * 2 + 1
  decreasing_by all_goals simp +arith

  /-- Verify every `(k, sn)` in `skel` is present in `docEntries` with matching child shape. -/
  def skelMatchesEntriesAll :
      List (String × SkeletonNode) → List (String × TomlValue) → Bool
    | [], _ => true
    | (k, sn) :: rest, docEntries =>
      (match lookupKeyList k docEntries with
       | some v => skelNodeMatchesValue sn v
       | none => false) && skelMatchesEntriesAll rest docEntries
  termination_by skel _ => sizeOf skel * 2
  decreasing_by all_goals simp +arith

  /-- Verify 1-to-1 element coverage of an `[[array_of_tables]]` skeleton against `xs`. -/
  def skelMatchesAot :
      List (List (String × SkeletonNode)) → List TomlValue → Bool
    | [], [] => true
    | eSkel :: restSkel, .table elemDoc :: restDoc =>
      skelMatchesEntries eSkel elemDoc.toList && skelMatchesAot restSkel restDoc
    | _, _ => false
  termination_by elems _ => sizeOf elems * 2
  decreasing_by all_goals simp +arith
end

mutual
  /-- Render a `TomlValue` inline (`key = <this>`, inside `{ ... }`, or inside `[ ... ]`). -/
  def renderValueInline (v : TomlValue) (tape : ValueTape) : Option String :=
    match v, tape with
    | .string s, .string style => renderStringLiteral s style
    | .int n, .int none => some (formatInt64Canonical n)
    | .int n, .int (some lex) => if isValidIntLex lex n then some lex else none
    | .float f, .float none =>
      if f.isNaN then some "nan"
      else if f == Float.inf then some "inf"
      else if f == -Float.inf then some "-inf"
      else if f.toBits == (0.0 : Float).toBits then some "0.0"
      else if f.toBits == (-0.0 : Float).toBits then some "-0.0"
      else none
    | .float f, .float (some lex) => if isValidFloatLex lex f then some lex else none
    | .bool b, .bool => some (if b then "true" else "false")
    | .offsetDateTime odt, .offsetDateTime sep oStyle fracLex => do
      let ds ← renderDate odt.dateTime.date
      let ts ← renderTime odt.dateTime.time fracLex
      let os ← renderOffset odt.offset oStyle
      some (ds ++ renderDateTimeSep sep ++ ts ++ os)
    | .localDateTime dt, .localDateTime sep fracLex => do
      let ds ← renderDate dt.date
      let ts ← renderTime dt.time fracLex
      some (ds ++ renderDateTimeSep sep ++ ts)
    | .localDate d, .localDate => renderDate d
    | .localTime t, .localTime fracLex => renderTime t fracLex
    | .array xs, .array elemTapes trailingTrivia =>
      match xs.toList, elemTapes with
      | [], [] =>
        let inner := trailingTrivia.getD ""
        if isClosedTrivia inner then some ("[" ++ inner ++ "]") else none
      | x0 :: xr, t0 :: tr => do
        let strs ← renderArrayElems (x0 :: xr) (t0 :: tr)
        let trail ←
          match trailingTrivia with
          | none => some ""
          | some trv => if isClosedTrivia trv then some ("," ++ trv) else none
        some ("[" ++ String.intercalate "," strs ++ trail ++ "]")
      | _, _ => none
    | .table sub, .inlineTable assigns emptyWs =>
      if !noDupKeysBool sub.toList then none
      else
        match assigns with
        | [] =>
          if sub.isEmpty && isHorizWsStr emptyWs then some ("{" ++ emptyWs ++ "}") else none
        | a0 :: as =>
          if emptyWs != "" then none
          else do
            let (localSkel, kvs) ← renderInlineAssigns sub.toList [] (a0 :: as)
            if skelMatchesEntries localSkel sub.toList then
              some ("{" ++ String.intercalate "," kvs ++ "}")
            else none
    | _, _ => none
  termination_by sizeOf tape
  decreasing_by all_goals simp [wfParam] <;> omega

  /-- Render non-empty array elements paired 1-to-1 with `(preTrivia, ValueTape, postTrivia)` instructions. -/
  def renderArrayElems : List TomlValue → List (String × ValueTape × String) → Option (List String)
    | [], [] => some []
    | x :: xs, (pre, tp, post) :: tps =>
      if !isClosedTrivia pre || !isClosedTrivia post then none
      else do
        let s ← renderValueInline x tp
        let rest ← renderArrayElems xs tps
        some ((pre ++ s ++ post) :: rest)
    | _, _ => none
  termination_by _ tps => sizeOf tps
  decreasing_by all_goals simp +arith

  /-- Render inline-table dotted-key assignments sequentially while tracking provenance in `localSkel`. -/
  def renderInlineAssigns (tableEntries : List (String × TomlValue))
      (localSkel : List (String × SkeletonNode)) :
      List (String × DottedKeyTape × String × String × ValueTape × String) →
        Option (List (String × SkeletonNode) × List String)
    | [] => some (localSkel, [])
    | (wsPre, dk, wsEqL, wsEqR, vt, wsPost) :: rest =>
      if !isHorizWsStr wsPre || !isHorizWsStr wsEqL || !isHorizWsStr wsEqR || !isHorizWsStr wsPost then
        none
      else do
        let rk ← renderDottedKey dk
        let (nextSkel, v) ← insertDottedAndLookup tableEntries localSkel dk.path
        let rv ← renderValueInline v vt
        let (finalSkel, tail) ← renderInlineAssigns tableEntries nextSkel rest
        some (finalSkel, (wsPre ++ rk ++ wsEqL ++ "=" ++ wsEqR ++ rv ++ wsPost) :: tail)
  termination_by assigns => sizeOf assigns
  decreasing_by all_goals simp +arith
end

/-- Update the last open element of an `[[aot]]` skeleton list. -/
def mapLastSkelAot (f : List (String × SkeletonNode) → Option (List (String × SkeletonNode))) :
    List (List (String × SkeletonNode)) → Option (List (List (String × SkeletonNode)))
  | [] => none
  | [last] => do
    let updated ← f last
    some [updated]
  | hd :: tl => do
    let rest ← mapLastSkelAot f tl
    some (hd :: rest)

/-- Apply the leaf update of `[path]` (`isAot = false`) or `[[path]]` (`isAot = true`) to `skel`. -/
def applyHeaderLeafSkel (isAot : Bool) (skel : List (String × SkeletonNode)) (k : String) :
    Option (List (String × SkeletonNode)) :=
  match isAot, assocLookupSkel k skel with
  | false, none => some (assocSetSkel k (.table .explicit []) skel)
  | false, some (.table .subtableImplicit sub) => some (assocSetSkel k (.table .explicit sub) skel)
  | false, _ => none
  | true, none => some (assocSetSkel k (.aot [[]]) skel)
  | true, some (.aot elems) => some (assocSetSkel k (.aot (elems ++ [[]])) skel)
  | true, _ => none

/-- Traverse `skel` along `path` and apply `applyHeaderLeafSkel isAot` at the final segment. -/
def applyHeaderSkel (isAot : Bool) :
    List (String × SkeletonNode) → List String → Option (List (String × SkeletonNode))
  | _, [] => none
  | skel, [k] => applyHeaderLeafSkel isAot skel k
  | skel, k :: k' :: rest =>
    match assocLookupSkel k skel with
    | none => do
      let sub ← applyHeaderSkel isAot [] (k' :: rest)
      some (assocSetSkel k (.table .subtableImplicit sub) skel)
    | some (.table kind sub) => do
      let nextSub ← applyHeaderSkel isAot sub (k' :: rest)
      some (assocSetSkel k (.table kind nextSub) skel)
    | some (.aot elems) => do
      let nextElems ← mapLastSkelAot (fun elem => applyHeaderSkel isAot elem (k' :: rest)) elems
      some (assocSetSkel k (.aot nextElems) skel)
    | _ => none

/-- Update the last open element of `elems` while selecting the matching index in `xs`. -/
def mapLastSkelWithDoc
    (f : List (String × TomlValue) → List (String × SkeletonNode) →
      Option (List (String × SkeletonNode) × TomlValue)) :
    List TomlValue → List (List (String × SkeletonNode)) →
      Option (List (List (String × SkeletonNode)) × TomlValue)
  | .table curDoc :: _, [lastSkel] => do
    let (updated, v) ← f curDoc.toList lastSkel
    some ([updated], v)
  | .table _ :: restDoc, hdSkel :: nextSkel :: tlSkel => do
    let (restUpdated, v) ← mapLastSkelWithDoc f restDoc (nextSkel :: tlSkel)
    some (hdSkel :: restUpdated, v)
  | _, _ => none

/-- Insert a `relPath = val` assignment under `activePath` while extracting the target `TomlValue` from `docEntries`. -/
def insertAtActiveAndLookup :
    List (String × TomlValue) → List (String × SkeletonNode) → List String → List String →
      Option (List (String × SkeletonNode) × TomlValue)
  | docEntries, skel, [], relPath =>
    insertDottedAndLookup docEntries skel relPath
  | docEntries, skel, k :: rest, relPath =>
    match lookupKeyList k docEntries, assocLookupSkel k skel with
    | some (.table subDoc), some (.table kind subSkel) => do
      let (nextSub, v) ← insertAtActiveAndLookup subDoc.toList subSkel rest relPath
      some (assocSetSkel k (.table kind nextSub) skel, v)
    | some (.array xs), some (.aot elems) => do
      let (nextElems, v) ←
        mapLastSkelWithDoc (fun elemDoc elemSkel => insertAtActiveAndLookup elemDoc elemSkel rest relPath)
          xs.toList elems
      some (assocSetSkel k (.aot nextElems) skel, v)
    | _, _ => none

/-- Render a `LineSuffixTape` (`ws` + optional `#comment`), returning `none` if invalid. -/
def renderLineSuffix (suf : LineSuffixTape) : Option String :=
  if !isHorizWsStr suf.ws then none
  else
    match suf.comment with
    | none => some suf.ws
    | some c => if isSingleLineClean c then some (suf.ws ++ "#" ++ c) else none

/-- Render top-level `StmtTape` instructions sequentially against `docEntries`. -/
def renderStmts (docEntries : List (String × TomlValue)) (activePath : List String)
    (skel : List (String × SkeletonNode)) (trailingNl : Bool) :
    List StmtTape → Option (List (String × SkeletonNode) × String)
  | [] => some (skel, "")
  | stmt :: rest =>
    let lineEnd := if rest.isEmpty then (if trailingNl then "\n" else "") else "\n"
    match stmt with
    | .tableHeader pre wsOpen dk wsClose suf =>
      if !isClosedTrivia pre || !isHorizWsStr wsOpen || !isHorizWsStr wsClose then none
      else do
        let rk ← renderDottedKey dk
        let rsuf ← renderLineSuffix suf
        let nextSkel ← applyHeaderSkel false skel dk.path
        let (finalSkel, tailStr) ← renderStmts docEntries dk.path nextSkel trailingNl rest
        some (finalSkel, pre ++ "[" ++ wsOpen ++ rk ++ wsClose ++ "]" ++ rsuf ++ lineEnd ++ tailStr)
    | .aotHeader pre wsOpen dk wsClose suf =>
      if !isClosedTrivia pre || !isHorizWsStr wsOpen || !isHorizWsStr wsClose then none
      else do
        let rk ← renderDottedKey dk
        let rsuf ← renderLineSuffix suf
        let nextSkel ← applyHeaderSkel true skel dk.path
        let (finalSkel, tailStr) ← renderStmts docEntries dk.path nextSkel trailingNl rest
        some (finalSkel, pre ++ "[[" ++ wsOpen ++ rk ++ wsClose ++ "]]" ++ rsuf ++ lineEnd ++ tailStr)
    | .assign pre dk wsEqL wsEqR vt suf =>
      if !isClosedTrivia pre || !isHorizWsStr wsEqL || !isHorizWsStr wsEqR then none
      else do
        let rk ← renderDottedKey dk
        let rsuf ← renderLineSuffix suf
        let (nextSkel, v) ← insertAtActiveAndLookup docEntries skel activePath dk.path
        let rv ← renderValueInline v vt
        let (finalSkel, tailStr) ← renderStmts docEntries activePath nextSkel trailingNl rest
        some (finalSkel, pre ++ rk ++ wsEqL ++ "=" ++ wsEqR ++ rv ++ rsuf ++ lineEnd ++ tailStr)

/-- Expand LF newlines into LF or CRLF according to `crlfMask` (`[]` keeps remaining newlines as LF). -/
def expandNewlines : List Bool → List Char → Option (List Char)
  | [], [] => some []
  | _ :: _, [] => none
  | [], '\n' :: cs => do
    let rest ← expandNewlines [] cs
    some ('\n' :: rest)
  | false :: bs, '\n' :: cs => do
    let rest ← expandNewlines bs cs
    some ('\n' :: rest)
  | true :: bs, '\n' :: cs => do
    let rest ← expandNewlines bs cs
    some ('\r' :: '\n' :: rest)
  | bs, c :: cs => do
    let rest ← expandNewlines bs cs
    some (c :: rest)

/-- Normalize CRLF pairs (`\r\n`) to LF (`\n`) in a character list. -/
def stripCrBeforeLf : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: stripCrBeforeLf rest
  | c :: rest => c :: stripCrBeforeLf rest
  | [] => []

/-- Render a `WellFormedTable` to LF-normalized TOML 1.0 text according to `RenderTape`. -/
def renderLF (doc : TomlTable) (tape : RenderTape) : Option String :=
  if !wellFormedTableBool doc then none
  else if !tape.stmts.isEmpty && !tape.trailingNewline && !tape.eofTrivia.isEmpty then none
  else if !isEofTrivia tape.eofTrivia then none
  else do
    let (finalSkel, bodyStr) ← renderStmts doc.toList [] [] tape.trailingNewline tape.stmts
    if !skelMatchesEntries finalSkel doc.toList then none
    else some (bodyStr ++ tape.eofTrivia)

/-- Nondeterministic generative specification rendering a `WellFormedTable` to TOML 1.0 text according to `RenderTape`. -/
def render (doc : TomlTable) (tape : RenderTape) : Option String := do
  let lfStr ← renderLF doc tape
  let rawCs ← expandNewlines tape.crlfMask lfStr.toList
  some (String.ofList rawCs)

end LeanSwe.Toml.Model

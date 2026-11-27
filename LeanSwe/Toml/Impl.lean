import LeanSwe.Toml.Types
import LeanSwe.NumParse.Types
import LeanSwe.Toml.Impl.LexerAndScalar

namespace LeanSwe.Toml.Impl

open LeanSwe.Toml
open LeanSwe.NumParse

/-- Look up the first value associated with `k` in an association list. -/
def lookupKeyListImpl (k : String) : List (String × TomlValue) → Option TomlValue
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupKeyListImpl k rest

/-- Look up the first value associated with `k` in a `TomlTable`. -/
def lookupKeyImpl (k : String) (t : TomlTable) : Option TomlValue :=
  lookupKeyListImpl k t.toList

/-- Check whether `s` is a valid non-empty ASCII bare key. -/
def isValidBareKeyImpl (s : String) : Bool :=
  !s.isEmpty && s.toList.all isBareKeyCharImpl

/-- Encode a single byte `n < 16` as an uppercase hexadecimal character. -/
def hexDigitUpperImpl (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + (n - 10))

/-- Escape a single character for canonical TOML basic strings/keys. -/
def escapeBasicCharImpl (allowNewline : Bool) (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\x08' then "\\b"
  else if c == '\t' then "\\t"
  else if c == '\n' then if allowNewline then "\n" else "\\n"
  else if c == '\x0c' then "\\f"
  else if c == '\r' then "\\r"
  else if isDisallowedControlImpl c then
    let n := c.toNat
    "\\u00" ++ String.ofList [hexDigitUpperImpl (n / 16), hexDigitUpperImpl (n % 16)]
  else String.singleton c

/-- Render a canonical basic string body (`allowNewline = false` for `"..."`, `true` for `"""..."""`). -/
def escapeBasicBodyImpl (allowNewline : Bool) (s : String) : String :=
  String.join (s.toList.map (escapeBasicCharImpl allowNewline))

/-- Pad a natural number with leading zeros to width `w`. -/
def padNatZeroImpl (w : Nat) (n : Nat) : String :=
  let s := toString n
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Provenance classification of a TOML table node during document construction. -/
inductive TableKind where
  /-- Table explicitly opened by `[t]` or element of `[[t]]`. -/
  | explicit
  /-- Intermediate ancestor implicitly created by `[t.u]` or `[[t.u]]`. -/
  | subtableImplicit
  /-- Table created or extended by dotted key `t.u = ...`. -/
  | dotted
  /-- Immutable closed inline table `{ ... }`. -/
  | inline
  deriving Repr, BEq, DecidableEq

/-- Builder AST tracking table provenance and arrays of tables during parsing. -/
inductive Node where
  /-- Scalar or static array value. -/
  | leaf (val : TomlValue)
  /-- Table with tracked provenance and distinct keys. -/
  | table (kind : TableKind) (entries : List (String × Node))
  /-- Array of tables created by `[[...]]` headers. -/
  | aot (elems : List (List (String × Node)))
  deriving Repr

/-- Lookup a key in an association list of builder nodes. -/
def assocLookupNode (k : String) : List (String × Node) → Option Node
  | [] => none
  | (k', v) :: rest => if k == k' then some v else assocLookupNode k rest

/-- Insert or replace a key in an association list of builder nodes, preserving key uniqueness and order. -/
def assocSetNode (k : String) (v : Node) : List (String × Node) → List (String × Node)
  | [] => [(k, v)]
  | (k', old) :: rest =>
    if k == k' then (k', v) :: rest
    else (k', old) :: assocSetNode k v rest

mutual
  /-- Convert a builder `Node` into its public `TomlValue`. -/
  def nodeToTomlValue : Node → TomlValue
    | .leaf v => v
    | .table _ entries => .table (entriesToTomlList entries).toArray
    | .aot elems => .array (aotElemsToToml elems).toArray

  /-- Convert an association list of builder nodes into `List (String × TomlValue)`. -/
  def entriesToTomlList : List (String × Node) → List (String × TomlValue)
    | [] => []
    | (k, n) :: rest => (k, nodeToTomlValue n) :: entriesToTomlList rest

  /-- Convert `[[aot]]` element builders into `List TomlValue`. -/
  def aotElemsToToml : List (List (String × Node)) → List TomlValue
    | [] => []
    | e :: rest => .table (entriesToTomlList e).toArray :: aotElemsToToml rest
end

mutual
  /-- Convert a parsed `TomlValue` (preserving inline tables as `.table .inline`) into a builder `Node`. -/
  def valueToInlineNode : TomlValue → Node
    | .table t => .table .inline (inlineListToNodes t.toList)
    | other => .leaf other

  /-- Convert inline table entries into builder nodes. -/
  def inlineListToNodes : List (String × TomlValue) → List (String × Node)
    | [] => []
    | (k, v) :: rest => (k, valueToInlineNode v) :: inlineListToNodes rest
end

/-- Format a dot-joined path string for error diagnostics. -/
def joinPath (path : List String) : String :=
  String.intercalate "." path

/-- Insert a dotted key assignment `relPath = newNode` into an enclosing table's entries. -/
def insertDottedEntries (fullPath : List String) :
    List (String × Node) → List String → Node → Except TomlError (List (String × Node))
  | _, [], _ => .error (mkErr .parseError "empty key path")
  | entries, [k], newNode =>
    match assocLookupNode k entries with
    | none => .ok (assocSetNode k newNode entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot modify immutable inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some _ =>
      .error (mkErr .duplicateKey ("duplicate key: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
  | entries, k :: rest, newNode =>
    match assocLookupNode k entries with
    | none => do
      let sub ← insertDottedEntries fullPath [] rest newNode
      .ok (assocSetNode k (.table .dotted sub) entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot modify immutable inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.table .explicit _) =>
      .error (mkErr .redefinedTable ("cannot add dotted key to explicitly defined table: " ++ k)
        (path := some (joinPath fullPath)))
    | some (.table .subtableImplicit sub) => do
      let nextSub ← insertDottedEntries fullPath sub rest newNode
      .ok (assocSetNode k (.table .dotted nextSub) entries)
    | some (.table .dotted sub) => do
      let nextSub ← insertDottedEntries fullPath sub rest newNode
      .ok (assocSetNode k (.table .dotted nextSub) entries)
    | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot modify immutable inline table: " ++ k)
        (path := some (joinPath fullPath)))
    | some (.leaf _) =>
      .error (mkErr .duplicateKey ("cannot extend non-table value with dotted key: " ++ k)
        (path := some (joinPath fullPath)))
    | some (.aot _) =>
      .error (mkErr .duplicateKey ("cannot extend array of tables with dotted key: " ++ k)
        (path := some (joinPath fullPath)))

mutual
  /-- Fuel-indexed value parser covering strings, arrays, inline tables, booleans, datetimes, floats, and ints. -/
  def parseValueFuel (numApi : CharNumApi) : Nat → List Char → Except TomlError (TomlValue × List Char)
    | 0, _ => .error (mkErr .parseError "TOML value nesting exceeded parser fuel")
    | fuel + 1, cs =>
      match cs with
      | '"' :: '"' :: '"' :: rest => do
        let (s, after) ← parseMultilineBasicString rest
        .ok (.string s, after)
      | '"' :: rest => do
        let (s, after) ← parseBasicStringBody rest
        .ok (.string s, after)
      | '\'' :: '\'' :: '\'' :: rest => do
        let (s, after) ← parseMultilineLiteralString rest
        .ok (.string s, after)
      | '\'' :: rest => do
        let (s, after) ← parseLiteralStringBody [] rest
        .ok (.string s, after)
      | '[' :: rest => parseArrayFuel numApi fuel rest []
      | '{' :: rest =>
        match skipHorizWs rest with
        | '}' :: afterClose => .ok (.table #[], afterClose)
        | other => parseInlineTableFuel numApi fuel other []
      | _ => do
        let (tok, after) := takeUnquotedTokenChars cs
        let v ← classifyScalarChars numApi tok
        .ok (v, after)

  /-- Fuel-indexed array parser supporting multiline whitespace, `#` comments, and trailing commas. -/
  def parseArrayFuel (numApi : CharNumApi) : Nat → List Char → List TomlValue → Except TomlError (TomlValue × List Char)
    | 0, _, _ => .error (mkErr .parseError "unterminated TOML array")
    | fuel + 1, cs, revAcc =>
      match skipTriviaNewlines cs with
      | ']' :: afterClose => .ok (.array revAcc.reverse.toArray, afterClose)
      | [] => .error (mkErr .parseError "unterminated TOML array")
      | cs1 => do
        let (v, r1) ← parseValueFuel numApi fuel cs1
        let r2 := skipTriviaNewlines r1
        let nextAcc := v :: revAcc
        match r2 with
        | ',' :: afterComma => parseArrayFuel numApi fuel afterComma nextAcc
        | ']' :: afterClose => .ok (.array nextAcc.reverse.toArray, afterClose)
        | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array")

  /-- Fuel-indexed single-line inline table parser allowing dotted keys and forbidding trailing commas or structural newlines. -/
  def parseInlineTableFuel (numApi : CharNumApi) :
      Nat → List Char → List (String × Node) → Except TomlError (TomlValue × List Char)
    | 0, _, _ => .error (mkErr .parseError "unterminated inline table")
    | fuel + 1, cs, entries => do
      let cs1 := skipHorizWs cs
      let (relPath, r1) ← parseDottedKey cs1
      let r2 := skipHorizWs r1
      match r2 with
      | '=' :: r3 => do
        let r4 := skipHorizWs r3
        let (v, r5) ← parseValueFuel numApi fuel r4
        let nextEntries ← insertDottedEntries relPath entries relPath (valueToInlineNode v)
        let r6 := skipHorizWs r5
        match r6 with
        | ',' :: afterComma =>
          match skipHorizWs afterComma with
          | '}' :: _ => .error (mkErr .parseError "trailing comma is not allowed in inline table")
          | nextCs => parseInlineTableFuel numApi fuel nextCs nextEntries
        | '}' :: afterClose => .ok (.table (entriesToTomlList nextEntries).toArray, afterClose)
        | _ => .error (mkErr .parseError "expected ',' or '}' in inline table")
      | _ => .error (mkErr .parseError "expected '=' in inline table")
end

/-- Parse a TOML value starting at the head of `cs`. -/
def parseValue (numApi : CharNumApi) (cs : List Char) : Except TomlError (TomlValue × List Char) :=
  parseValueFuel numApi (cs.length + 2) cs

/-- Update the last element of an `[[aot]]` list. -/
def mapLastAot (f : List (String × Node) → Except TomlError (List (String × Node))) :
    List (List (String × Node)) → Except TomlError (List (List (String × Node)))
  | [] => .error (mkErr .parseError "internal error: empty array of tables")
  | [last] => do
    let updated ← f last
    .ok [updated]
  | hd :: tl => do
    let rest ← mapLastAot f tl
    .ok (hd :: rest)

/-- Leaf action applied at the final key segment of a `[table]` or `[[aot]]` header. -/
inductive HeaderMode where
  /-- Standard `[table]` header. -/
  | table
  /-- Array-of-tables `[[aot]]` header. -/
  | aot
  deriving Repr, BEq, DecidableEq

/-- Apply the leaf update of a `[table]` or `[[aot]]` header at key `k`. -/
def applyHeaderLeaf (mode : HeaderMode) (fullPath : List String)
    (entries : List (String × Node)) (k : String) : Except TomlError (List (String × Node)) :=
  match mode, assocLookupNode k entries with
  | .table, none => .ok (assocSetNode k (.table .explicit []) entries)
  | .table, some (.table .subtableImplicit sub) => .ok (assocSetNode k (.table .explicit sub) entries)
  | .table, some (.table .inline _) | .table, some (.leaf (.table _)) =>
    .error (mkErr .immutableInlineTable ("cannot reopen inline table: " ++ joinPath fullPath)
      (path := some (joinPath fullPath)))
  | .table, some _ =>
    .error (mkErr .redefinedTable ("table already defined: " ++ joinPath fullPath)
      (path := some (joinPath fullPath)))
  | .aot, none => .ok (assocSetNode k (.aot [[]]) entries)
  | .aot, some (.aot elems) => .ok (assocSetNode k (.aot (elems ++ [[]])) entries)
  | .aot, some (.table .inline _) | .aot, some (.leaf (.table _)) =>
    .error (mkErr .immutableInlineTable ("cannot append to inline table as array of tables: " ++ joinPath fullPath)
      (path := some (joinPath fullPath)))
  | .aot, some _ =>
    .error (mkErr .redefinedTable ("cannot redefine non-AoT entry as array of tables: " ++ joinPath fullPath)
      (path := some (joinPath fullPath)))

/-- Traverse along `path` and apply `applyHeaderLeaf mode` at the final key. -/
def applyHeader (mode : HeaderMode) (fullPath : List String) :
    List (String × Node) → List String → Except TomlError (List (String × Node))
  | _, [] =>
    .error (mkErr .parseError (match mode with
      | .table => "empty table header path"
      | .aot => "empty array-of-tables header path"))
  | entries, [k] => applyHeaderLeaf mode fullPath entries k
  | entries, k :: k' :: rest =>
    match assocLookupNode k entries with
    | none => do
      let sub ← applyHeader mode fullPath [] (k' :: rest)
      .ok (assocSetNode k (.table .subtableImplicit sub) entries)
    | some (.table .inline _) | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot traverse inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.table kind sub) => do
      let nextSub ← applyHeader mode fullPath sub (k' :: rest)
      .ok (assocSetNode k (.table kind nextSub) entries)
    | some (.aot elems) => do
      let nextElems ← mapLastAot (fun elem => applyHeader mode fullPath elem (k' :: rest)) elems
      .ok (assocSetNode k (.aot nextElems) entries)
    | some (.leaf _) =>
      .error (mkErr .redefinedTable ("cannot traverse non-table value in header: " ++ k)
        (path := some (joinPath fullPath)))

/-- Insert a `key = value` statement at `relPath` relative to the active header `activePath`. -/
def insertAtActivePath (fullPath : List String) :
    List (String × Node) → List String → List String → Node → Except TomlError (List (String × Node))
  | entries, [], relPath, valNode =>
    insertDottedEntries fullPath entries relPath valNode
  | entries, k :: rest, relPath, valNode =>
    match assocLookupNode k entries with
    | some (.table kind sub) => do
      let nextSub ← insertAtActivePath fullPath sub rest relPath valNode
      .ok (assocSetNode k (.table kind nextSub) entries)
    | some (.aot elems) => do
      let nextElems ← mapLastAot (fun elem => insertAtActivePath fullPath elem rest relPath valNode) elems
      .ok (assocSetNode k (.aot nextElems) entries)
    | _ => .error (mkErr .parseError ("invalid active table path: " ++ joinPath fullPath))

/-- Verify that a statement line ends cleanly after horizontal whitespace and an optional `# ...` comment. -/
def consumeStatementEnd (cs : List Char) : Except TomlError (List Char) :=
  match skipHorizAndComment cs with
  | [] => .ok []
  | '\n' :: rest => .ok rest
  | _ => .error (mkErr .parseError "unexpected trailing characters after TOML statement")

/-- Fuel-indexed top-level TOML statement loop. -/
def parseDocumentFuel (numApi : CharNumApi) :
    Nat → List Char → List String → List (String × Node) → Except TomlError (List (String × Node))
  | 0, cs, _, root =>
    match skipTriviaNewlines cs with
    | [] => .ok root
    | _ => .error (mkErr .parseError "TOML document statement count exceeded fuel")
  | fuel + 1, cs, activePath, root =>
    match skipTriviaNewlines cs with
    | [] => .ok root
    | '[' :: '[' :: rest => do
      let (path, r1) ← parseDottedKey (skipHorizWs rest)
      match skipHorizWs r1 with
      | ']' :: ']' :: r2 => do
        let nextCs ← consumeStatementEnd r2
        let nextRoot ← applyHeader .aot path root path
        parseDocumentFuel numApi fuel nextCs path nextRoot
      | _ => .error (mkErr .parseError "expected ']]' closing array-of-tables header")
    | '[' :: rest => do
      let (path, r1) ← parseDottedKey (skipHorizWs rest)
      match skipHorizWs r1 with
      | ']' :: r2 => do
        let nextCs ← consumeStatementEnd r2
        let nextRoot ← applyHeader .table path root path
        parseDocumentFuel numApi fuel nextCs path nextRoot
      | _ => .error (mkErr .parseError "expected ']' closing table header")
    | cs1 => do
      let (relPath, r1) ← parseDottedKey cs1
      match skipHorizWs r1 with
      | '=' :: r2 => do
        let (val, r3) ← parseValue numApi (skipHorizWs r2)
        let nextCs ← consumeStatementEnd r3
        let nextRoot ← insertAtActivePath (activePath ++ relPath) root activePath relPath (valueToInlineNode val)
        parseDocumentFuel numApi fuel nextCs activePath nextRoot
      | _ => .error (mkErr .parseError "expected '=' after key")

/-- Parse already-decoded character list using `CharNumApi`. -/
def parseCharsWithNum (numApi : CharNumApi) (cs : List Char) : Except TomlError TomlTable := do
  let normalized ← normalizeChars 1 1 cs
  let root ← parseDocumentFuel numApi (normalized.length + 1) normalized [] []
  .ok (entriesToTomlList root).toArray

/-- Pure TOML 1.0 parser parameterized over `NumParseApi`. -/
def parseWithNum (numApi : NumParseApi) (input : String) : Except TomlError TomlTable :=
  parseCharsWithNum (toCharNumApi numApi) input.toList

/-- Format a key using bare syntax when ASCII bare-valid, or basic escaped quotes otherwise. -/
def formatKey (k : String) : String :=
  if isValidBareKeyImpl k then k else "\"" ++ escapeBasicBodyImpl false k ++ "\""

/-- Format a fractional nanosecond value trimming trailing zeros, or `""` when zero. -/
def formatNanosTrimmed (nano : Nat) : String :=
  if nano == 0 then ""
  else
    let padded := padNatZeroImpl 9 nano
    let trimmedRev := padded.toList.reverse.dropWhile (· == '0')
    "." ++ String.ofList trimmedRev.reverse

/-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
def formatDate (d : Std.Time.PlainDate) : String :=
  padNatZeroImpl 4 d.year.toNat ++ "-" ++ padNatZeroImpl 2 d.month.val.toNat ++ "-" ++ padNatZeroImpl 2 d.day.val.toNat

/-- Format a `Std.Time.PlainTime` as `HH:MM:SS(.trimmed)?`. -/
def formatTime (t : Std.Time.PlainTime) : String :=
  padNatZeroImpl 2 t.hour.val.toNat ++ ":" ++ padNatZeroImpl 2 t.minute.val.toNat ++ ":" ++
    padNatZeroImpl 2 t.second.val.toNat ++ formatNanosTrimmed t.nanosecond.val.toNat

/-- Format a `Std.Time.TimeZone.Offset` as `Z` when `0` or `±HH:MM` otherwise. -/
def formatOffset (o : Std.Time.TimeZone.Offset) : String :=
  if o.second.val == 0 then "Z"
  else
    let sign := if o.second.val < 0 then "-" else "+"
    let absMin := o.second.val.natAbs / 60
    sign ++ padNatZeroImpl 2 (absMin / 60) ++ ":" ++ padNatZeroImpl 2 (absMin % 60)

/-- Check whether `xs` is a non-empty array whose elements are all `.table _` values (eligible for `[[...]]`). -/
def isNonEmptyTableArray (xs : Array TomlValue) : Bool :=
  !xs.isEmpty && xs.toList.all fun v => match v with | .table _ => true | _ => false

mutual
  /-- Format any `TomlValue` on a single line (used for scalars, arrays, and inline tables). -/
  def formatValueInline (numApi : NumParseApi) : TomlValue → String
    | .string s => "\"" ++ escapeBasicBodyImpl false s ++ "\""
    | .int n => numApi.formatInt n.toInt
    | .float f => numApi.formatFloat f
    | .bool b => if b then "true" else "false"
    | .offsetDateTime odt =>
      formatDate odt.dateTime.date ++ "T" ++ formatTime odt.dateTime.time ++ formatOffset odt.offset
    | .localDateTime dt => formatDate dt.date ++ "T" ++ formatTime dt.time
    | .localDate d => formatDate d
    | .localTime t => formatTime t
    | .array xs => "[" ++ String.intercalate ", " (formatArrayElems numApi xs.toList) ++ "]"
    | .table t => "{" ++ String.intercalate ", " (formatInlineEntries numApi t.toList) ++ "}"

  /-- Format elements of an inline array. -/
  def formatArrayElems (numApi : NumParseApi) : List TomlValue → List String
    | [] => []
    | v :: rest => formatValueInline numApi v :: formatArrayElems numApi rest

  /-- Format entries of an inline table. -/
  def formatInlineEntries (numApi : NumParseApi) : List (String × TomlValue) → List String
    | [] => []
    | (k, v) :: rest => (formatKey k ++ " = " ++ formatValueInline numApi v) :: formatInlineEntries numApi rest
end

/-- Format only inline scalar and non-AoT-array entries of a table entry list. -/
def formatTableInlinePart (numApi : NumParseApi) : List (String × TomlValue) → List String
  | [] => []
  | (_, .table _) :: rest => formatTableInlinePart numApi rest
  | (k, .array xs) :: rest =>
    if isNonEmptyTableArray xs then formatTableInlinePart numApi rest
    else (formatKey k ++ " = " ++ formatValueInline numApi (.array xs)) :: formatTableInlinePart numApi rest
  | (k, v) :: rest => (formatKey k ++ " = " ++ formatValueInline numApi v) :: formatTableInlinePart numApi rest

mutual
  /-- Format section-scoped (`[table]` and `[[aot]]`) entries of a table entry list. -/
  def formatTableSectionPart (numApi : NumParseApi) (revPrefix : List String) :
      List (String × TomlValue) → List String
    | [] => []
    | (k, .table ⟨subList⟩) :: rest =>
      let nextRev := formatKey k :: revPrefix
      let hdr := "[" ++ String.intercalate "." nextRev.reverse ++ "]"
      hdr :: formatTableInlinePart numApi subList ++
        formatTableSectionPart numApi nextRev subList ++
        formatTableSectionPart numApi revPrefix rest
    | (k, .array ⟨xsList⟩) :: rest =>
      if isNonEmptyTableArray ⟨xsList⟩ then
        let nextRev := formatKey k :: revPrefix
        let hdr := "[[" ++ String.intercalate "." nextRev.reverse ++ "]]"
        formatAotElemList numApi nextRev hdr xsList ++ formatTableSectionPart numApi revPrefix rest
      else formatTableSectionPart numApi revPrefix rest
    | _ :: rest => formatTableSectionPart numApi revPrefix rest

  /-- Format elements of an `[[array_of_tables]]` section. -/
  def formatAotElemList (numApi : NumParseApi) (revPath : List String) (hdr : String) :
      List TomlValue → List String
    | [] => []
    | .table ⟨elemList⟩ :: rest =>
      hdr :: formatTableInlinePart numApi elemList ++
        formatTableSectionPart numApi revPath elemList ++
        formatAotElemList numApi revPath hdr rest
    | _ :: rest => formatAotElemList numApi revPath hdr rest
end

/-- Format section-scoped and inline-scoped entries of a `TomlTable` deterministically. -/
def formatSectionLines (numApi : NumParseApi) (revPrefix : List String) (doc : TomlTable) : List String :=
  formatTableInlinePart numApi doc.toList ++ formatTableSectionPart numApi revPrefix doc.toList

/-- Pure deterministic TOML 1.0 canonical formatter parameterized over `NumParseApi`. -/
def formatWithNum (numApi : NumParseApi) (doc : TomlTable) : String :=
  match formatSectionLines numApi [] doc with
  | [] => ""
  | lines => String.intercalate "\n" lines ++ "\n"

/-- Decode a `TomlValue` using `[FromToml α]`. -/
def tomlDecode {α : Type} [FromToml α] (v : TomlValue) : Except TomlError α :=
  match FromToml.fromToml v with
  | .ok a => .ok a
  | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message }

/-- Encode `α` into a `TomlValue` using `[ToToml α]`. -/
def tomlEncode {α : Type} [ToToml α] (x : α) : TomlValue :=
  ToToml.toToml x

/-- Extract entries from `.table`, failing with `.typeMismatch` (`path := none`) on non-tables. -/
def tomlGetTable : TomlValue → Except TomlError TomlTable
  | .table t => .ok t
  | _ => .error (mkErr .typeMismatch "expected TOML table")

/-- Extract elements from `.array`, failing with `.typeMismatch` (`path := none`) on non-arrays. -/
def tomlGetArray : TomlValue → Except TomlError (Array TomlValue)
  | .array xs => .ok xs
  | _ => .error (mkErr .typeMismatch "expected TOML array")

/-- Look up required `key` in `t` and decode via `FromToml`. -/
def tomlGetField {α : Type} [FromToml α] (t : TomlTable) (key : String) : Except TomlError α :=
  match lookupKeyImpl key t with
  | none => .error (mkErr .missingField ("missing TOML field: " ++ key) (path := some key))
  | some v =>
    match FromToml.fromToml v with
    | .ok a => .ok a
    | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := some key }

/-- Look up optional `key` in `t`, returning `none` when absent and decoding via `FromToml` when present. -/
def tomlGetOptField {α : Type} [FromToml α] (t : TomlTable) (key : String) : Except TomlError (Option α) :=
  match lookupKeyImpl key t with
  | none => .ok none
  | some v =>
    match FromToml.fromToml v with
    | .ok a => .ok (some a)
    | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := some key }

/-- Traverse nested tables along `keys` recording the dot-joined prefix path on failure. -/
def tomlGetPathAux {α : Type} [FromToml α] (revPrefix : List String) (t : TomlTable) :
    List String → Except TomlError α
  | [] =>
    match FromToml.fromToml (.table t) with
    | .ok a => .ok a
    | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := none }
  | [k] =>
    let full := joinPath (revPrefix.reverse ++ [k])
    match lookupKeyImpl k t with
    | none => .error (mkErr .missingField ("missing TOML field: " ++ full) (path := some full))
    | some v =>
      match FromToml.fromToml v with
      | .ok a => .ok a
      | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := some full }
  | k :: k' :: rest =>
    let full := joinPath (revPrefix.reverse ++ [k])
    match lookupKeyImpl k t with
    | none => .error (mkErr .missingField ("missing TOML field: " ++ full) (path := some full))
    | some (.table sub) => tomlGetPathAux (k :: revPrefix) sub (k' :: rest)
    | some _ => .error (mkErr .typeMismatch ("expected TOML table at: " ++ full) (path := some full))

/-- Traverse `keys` inside `t` and decode the leaf value via `FromToml`. -/
def tomlGetPath {α : Type} [FromToml α] (t : TomlTable) (keys : List String) : Except TomlError α :=
  tomlGetPathAux [] t keys

/-- Bundle `TomlApi` given a verified `NumParseApi`. -/
def makeTomlApi (numApi : NumParseApi) : TomlApi :=
  { parse := parseWithNum numApi
  , format := formatWithNum numApi
  , decode := tomlDecode
  , encode := tomlEncode
  , getTable := tomlGetTable
  , getArray := tomlGetArray
  , getField := tomlGetField
  , getOptField := tomlGetOptField
  , getPath := tomlGetPath
  }

/-- Construct a `TomlApi` bundle parameterized over an injected `NumParseApi`. -/
def _root_.LeanSwe.Toml.Internal.mkApi (num : NumParseApi) : TomlApi :=
  makeTomlApi num

end LeanSwe.Toml.Impl

import LeanSwe.Toml.Types
import LeanSwe.Toml.Model.Equiv

namespace LeanSwe.Toml.Model

open LeanSwe.Toml

/-- Check whether `c` is TOML 1.0 horizontal whitespace (`' '` or `'\t'`). -/
def isModelHorizWs (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Check whether every character of `s` is TOML 1.0 horizontal whitespace. -/
def isHorizWsStr (s : String) : Bool :=
  s.toList.all isModelHorizWs

/-- Check whether every character of `s` is horizontal whitespace or `'\n'`. -/
def isHorizAndNlStr (s : String) : Bool :=
  s.toList.all fun c => isModelHorizWs c || c == '\n'

/-- Check whether `c` is an ASCII bare-key character `[A-Za-z0-9_-]`. -/
def isBareKeyChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-'

/-- Check whether `c` is a disallowed TOML 1.0 control character (`U+0000..U+0008`, `U+000B`, `U+000C`, `U+000E..U+001F`, `U+007F`). -/
def isDisallowedControl (c : Char) : Bool :=
  let n := c.toNat
  n ≤ 0x08 || n == 0x0B || n == 0x0C || (0x0E ≤ n && n ≤ 0x1F) || n == 0x7F

/-- Check whether `s` contains no disallowed control chars, no `\n`, and no `\r`. -/
def isSingleLineClean (s : String) : Bool :=
  s.toList.all fun c => !isDisallowedControl c && c != '\n' && c != '\r'

/-- Check whether `s` contains `sub` as a substring. -/
def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check whether `s` is a valid non-empty ASCII bare key. -/
def isValidBareKey (s : String) : Bool :=
  !s.isEmpty && s.toList.all isBareKeyChar

/-- Encode a single byte `n < 16` as an uppercase hexadecimal character. -/
def hexDigitUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + (n - 10))

/-- Decode an ASCII hexadecimal digit into `0..15`. -/
def hexValModel? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Check whether `c` is an ASCII decimal digit `'0'..'9'`. -/
def isAsciiDigitModel (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Escape a single character for canonical TOML basic strings/keys. -/
def escapeBasicChar (allowNewline : Bool) (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\x08' then "\\b"
  else if c == '\t' then "\\t"
  else if c == '\n' then if allowNewline then "\n" else "\\n"
  else if c == '\x0c' then "\\f"
  else if c == '\r' then "\\r"
  else if isDisallowedControl c then
    let n := c.toNat
    "\\u00" ++ String.ofList [hexDigitUpper (n / 16), hexDigitUpper (n % 16)]
  else String.singleton c

/-- Render a canonical basic string body (`allowNewline = false` for `"..."`, `true` for `"""..."""`). -/
def escapeBasicBody (allowNewline : Bool) (s : String) : String :=
  String.join (s.toList.map (escapeBasicChar allowNewline))

/-- Pad a natural number with leading zeros to width `w`. -/
def padNatZero (w : Nat) (n : Nat) : String :=
  let s := toString n
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Compute `10^k` for `k : Nat`. -/
def pow10Nat : Nat → Nat
  | 0 => 1
  | k + 1 => 10 * pow10Nat k

/-- Accumulate up to `k` fractional second digits right-padded with zeros. -/
def fracDigitsToNanosAuxModel : Nat → Nat → List Char → Nat
  | 0, acc, _ => acc
  | k + 1, acc, c :: rest => fracDigitsToNanosAuxModel k (acc * 10 + (c.toNat - '0'.toNat)) rest
  | k + 1, acc, [] => fracDigitsToNanosAuxModel k (acc * 10) []

/-- Evaluate fractional second digits (truncating beyond 9 per TOML 1.0) into nanoseconds `0..999999999`. -/
def fracDigitsToNanosModel (ds : List Char) : Nat :=
  min 999999999 (fracDigitsToNanosAuxModel 9 0 ds)

/-- Check multiline whitespace/newline/`#...\n` trivia ending outside a comment. -/
def checkClosedTriviaAux : Bool → List Char → Bool
  | inComment, [] => !inComment
  | _, '\n' :: rest => checkClosedTriviaAux false rest
  | true, c :: rest => !isDisallowedControl c && c != '\r' && checkClosedTriviaAux true rest
  | false, c :: rest =>
    if isModelHorizWs c then checkClosedTriviaAux false rest
    else if c == '#' then checkClosedTriviaAux true rest
    else false

/-- Check that `s` is valid multiline trivia whose `#` comments are all newline-terminated. -/
def isClosedTrivia (s : String) : Bool :=
  checkClosedTriviaAux false s.toList

/-- Check trailing end-of-file trivia (allowing a final `#...` comment without a trailing newline). -/
def checkEofTriviaAux : Bool → List Char → Bool
  | _, [] => true
  | _, '\n' :: rest => checkEofTriviaAux false rest
  | true, c :: rest => !isDisallowedControl c && c != '\r' && checkEofTriviaAux true rest
  | false, c :: rest =>
    if isModelHorizWs c then checkEofTriviaAux false rest
    else if c == '#' then checkEofTriviaAux true rest
    else false

/-- Check that `s` is valid end-of-file TOML 1.0 trivia. -/
def isEofTrivia (s : String) : Bool :=
  checkEofTriviaAux false s.toList

/-- Escape sequence spelling choice inside a TOML basic string or basic key. -/
inductive BasicEscapeAtom where
  /-- `\b` (`U+0008`). -/
  | backspace
  /-- `\t` (`U+0009`). -/
  | tab
  /-- `\n` (`U+000A`). -/
  | linefeed
  /-- `\f` (`U+000C`). -/
  | formfeed
  /-- `\r` (`U+000D`). -/
  | carriageReturn
  /-- `\"` (`U+0022`). -/
  | quote
  /-- `\\` (`U+005C`). -/
  | backslash
  /-- `\uXXXX` 4-hex-digit Unicode scalar escape. -/
  | unicode4 (h1 h2 h3 h4 : Char)
  /-- `\UXXXXXXXX` 8-hex-digit Unicode scalar escape. -/
  | unicode8 (h1 h2 h3 h4 h5 h6 h7 h8 : Char)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Per-character encoding choice inside a single-line basic string or basic key `"..."`. -/
inductive BasicCharAtom where
  /-- Emit the character unescaped. -/
  | plain
  /-- Emit the character via an explicit backslash escape. -/
  | escape (esc : BasicEscapeAtom)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Atom inside a multiline basic string `"""..."""` body. -/
inductive MultilineBasicAtom where
  /-- Emit the next string character unescaped. -/
  | plain
  /-- Emit the next string character via an explicit backslash escape. -/
  | escape (esc : BasicEscapeAtom)
  /-- Emit a line-ending backslash `\` + horizontal whitespace + `\n` + trimmed whitespace/newlines. -/
  | lineTrim (wsBeforeNl : String := "") (wsAndNlAfter : String := "")
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of TOML key surface syntax in `render`. -/
inductive KeyStyle where
  /-- Unquoted ASCII bare key `[A-Za-z0-9_-]+`. -/
  | bare
  /-- Basic quoted key `"..."` (`none` uses canonical escaping; `some atoms` uses per-char atoms). -/
  | basic (atoms : Option (List BasicCharAtom) := none)
  /-- Literal quoted key `'...'`. -/
  | literal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Continuation segment `. key` in a dotted TOML key path. -/
structure DottedSegCont where
  /-- Horizontal whitespace before `'.'`. -/
  wsBeforeDot : String := ""
  /-- Horizontal whitespace after `'.'`. -/
  wsAfterDot : String := ""
  /-- Segment key string. -/
  key : String
  /-- Surface key style for `key`. -/
  style : KeyStyle := .bare
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Non-empty dotted key path with per-segment styles and horizontal whitespace around dots. -/
structure DottedKeyTape where
  /-- First segment key string. -/
  firstKey : String
  /-- Surface key style for `firstKey`. -/
  firstStyle : KeyStyle := .bare
  /-- Remaining `. key` segments. -/
  rest : List DottedSegCont := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Extract the logical key path from a `DottedKeyTape`. -/
def DottedKeyTape.path (dk : DottedKeyTape) : List String :=
  dk.firstKey :: dk.rest.map DottedSegCont.key

/-- Choice of TOML string literal surface syntax in `render`. -/
inductive StringStyle where
  /-- Single-line basic string `"..."` (`none` uses canonical escaping). -/
  | basic (atoms : Option (List BasicCharAtom) := none)
  /-- Multiline basic string `"""..."""` (`none` uses canonical `"""\n..."""`; `some (leadNl, atoms)` uses custom atoms). -/
  | multilineBasic (custom : Option (Bool × List MultilineBasicAtom) := none)
  /-- Single-line literal string `'...'`. -/
  | literal
  /-- Multiline literal string `'''...'''` with optional trimmed opener newline. -/
  | multilineLiteral (leadingNewline : Bool := true)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of RFC 3339 date-time separator in `render`. -/
inductive DateTimeSep where
  /-- Uppercase `'T'` separator. -/
  | upperT
  /-- Lowercase `'t'` separator. -/
  | lowerT
  /-- Single ASCII space `' '` separator. -/
  | space
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of RFC 3339 UTC offset formatting in `render`. -/
inductive OffsetStyle where
  /-- Uppercase `'Z'` when offset is `0` (otherwise `±HH:MM`). -/
  | upperZ
  /-- Lowercase `'z'` when offset is `0` (otherwise `±HH:MM`). -/
  | lowerZ
  /-- Explicit numeric `+00:00` when offset is `0` (otherwise `±HH:MM`). -/
  | numeric
  /-- Explicit negative zero `-00:00` when offset is `0`. -/
  | negZero
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Nondeterministic choices for rendering a TOML value in `render`. -/
inductive ValueTape where
  /-- Rendering choice for `.string`. -/
  | string (style : StringStyle := .basic)
  /-- Rendering choice for `.int` (optional custom TOML integer literal validated by `parseInt64Model`). -/
  | int (lex : Option String := none)
  /-- Rendering choice for `.float` (optional custom TOML float literal validated by `parseFloatModel`). -/
  | float (lex : Option String := none)
  /-- Rendering choice for `.bool`. -/
  | bool
  /-- Rendering choice for `.offsetDateTime` (`fracLex` is optional fractional digits after `'.'`). -/
  | offsetDateTime (sep : DateTimeSep := .upperT) (offsetStyle : OffsetStyle := .upperZ)
      (fracLex : Option String := none)
  /-- Rendering choice for `.localDateTime` (`fracLex` is optional fractional digits after `'.'`). -/
  | localDateTime (sep : DateTimeSep := .upperT) (fracLex : Option String := none)
  /-- Rendering choice for `.localDate`. -/
  | localDate
  /-- Rendering choice for `.localTime` (`fracLex` is optional fractional digits after `'.'`). -/
  | localTime (fracLex : Option String := none)
  /-- Rendering choice for `.array`: `(preTrivia, elemTape, postTrivia)` per element, plus inner trivia (when empty) or trailing-comma trivia (when `some` on non-empty). -/
  | array (elems : List (String × ValueTape × String)) (trailingTrivia : Option String := none)
  /-- Rendering choice for inline `.table`: `(wsBeforeKey, dottedKey, wsBeforeEq, wsAfterEq, valTape, wsAfterVal)` assignments, or `emptyWs` when empty. -/
  | inlineTable
      (assigns : List (String × DottedKeyTape × String × String × ValueTape × String))
      (emptyWs : String := "")
  deriving Repr, Inhabited

/-- Optional trailing horizontal whitespace and `#...` comment at the end of a statement line. -/
structure LineSuffixTape where
  /-- Horizontal whitespace before `#` (or before line end when `comment = none`). -/
  ws : String := ""
  /-- Optional comment text after `#` (must satisfy `isSingleLineClean`). -/
  comment : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single top-level TOML 1.0 statement instruction in `RenderTape`. -/
inductive StmtTape where
  /-- Standard `[path]` table header statement. -/
  | tableHeader (preTrivia : String := "") (wsAfterOpen : String := "")
      (path : DottedKeyTape) (wsBeforeClose : String := "")
      (suffix : LineSuffixTape := {})
  /-- Array-of-tables `[[path]]` header statement. -/
  | aotHeader (preTrivia : String := "") (wsAfterOpen : String := "")
      (path : DottedKeyTape) (wsBeforeClose : String := "")
      (suffix : LineSuffixTape := {})
  /-- Key-value `key = val` assignment statement in the active table scope. -/
  | assign (preTrivia : String := "") (key : DottedKeyTape)
      (wsBeforeEq : String := "") (wsAfterEq : String := "")
      (val : ValueTape) (suffix : LineSuffixTape := {})
  deriving Repr, Inhabited

/-- Root rendering tape specifying top-level statements, trailing newline/EOF trivia, and CRLF line-ending choices. -/
structure RenderTape where
  /-- Sequential TOML 1.0 statement instructions. -/
  stmts : List StmtTape := []
  /-- Whether the final statement (when `stmts` is non-empty) ends with a newline. -/
  trailingNewline : Bool := true
  /-- Trailing whitespace/blank lines/comments after all statements. -/
  eofTrivia : String := ""
  /-- Per-newline CRLF choices (`[]` leaves all newlines as `"\n"`; otherwise `true` emits `"\r\n"`, `false` emits `"\n"`). -/
  crlfMask : List Bool := []
  deriving Repr, Inhabited

/-- Mutable TOML 1.0 table provenance states tracked during document/inline-table rendering. -/
inductive OpenTableKind where
  /-- Table explicitly opened by `[t]` or element of `[[t]]`. -/
  | explicit
  /-- Intermediate ancestor implicitly created by `[t.u]` or `[[t.u]]`. -/
  | subtableImplicit
  /-- Table created or extended by dotted key `t.u = ...`. -/
  | dotted
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure TOML 1.0 provenance and coverage skeleton node (carrying zero `TomlValue` data). -/
inductive SkeletonNode where
  /-- Non-table scalar or static inline array assigned once. -/
  | leaf
  /-- Closed immutable inline table `{ ... }`. -/
  | inlineTable
  /-- Openable/dotted table with tracked `OpenTableKind` and child skeleton entries. -/
  | table (kind : OpenTableKind) (entries : List (String × SkeletonNode))
  /-- Array of tables created by `[[...]]` headers. -/
  | aot (elems : List (List (String × SkeletonNode)))
  deriving Repr, Inhabited

end LeanSwe.Toml.Model

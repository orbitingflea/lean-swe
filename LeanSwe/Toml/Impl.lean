import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Impl

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Ensure error diagnostic messages are always non-empty. -/
def nonEmptyMsg (msg : String) : String :=
  if msg.isEmpty then "TOML error" else msg

/-- Construct a `TomlError` with a guaranteed non-empty message. -/
def mkErr (kind : TomlErrorKind) (msg : String)
    (line : Option Nat := none) (col : Option Nat := none) (path : Option String := none) : TomlError :=
  { kind := kind, message := nonEmptyMsg msg, line := line, col := col, path := path }

/-- Validate input characters and normalize CRLF line endings to LF. -/
def normalizeChars (line col : Nat) : List Char → Except TomlError (List Char)
  | [] => .ok []
  | '\r' :: '\n' :: rest => do
    let tail ← normalizeChars (line + 1) 1 rest
    .ok ('\n' :: tail)
  | '\r' :: _ =>
    .error (mkErr .invalidUtf8OrControl "bare carriage return is not allowed in TOML" (some line) (some col))
  | '\n' :: rest => do
    let tail ← normalizeChars (line + 1) 1 rest
    .ok ('\n' :: tail)
  | c :: rest =>
    if isDisallowedControl c then
      .error (mkErr .invalidUtf8OrControl "disallowed control character in TOML input" (some line) (some col))
    else do
      let tail ← normalizeChars line (col + 1) rest
      .ok (c :: tail)

/-- Check whether `c` is horizontal TOML whitespace (`' '` or `'\t'`). -/
def isHorizWs (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Skip leading horizontal whitespace (`' '` and `'\t'`). -/
def skipHorizWs : List Char → List Char
  | c :: rest => if isHorizWs c then skipHorizWs rest else c :: rest
  | [] => []

/-- Skip leading horizontal whitespace and newlines (used for multiline line-ending backslash). -/
def skipHorizAndNl : List Char → List Char
  | c :: rest => if isHorizWs c || c == '\n' then skipHorizAndNl rest else c :: rest
  | [] => []

/-- Skip `# ...` comment characters up to `\n` or EOF. -/
def skipCommentBody : List Char → List Char
  | [] => []
  | '\n' :: rest => '\n' :: rest
  | _ :: rest => skipCommentBody rest

/-- Skip horizontal whitespace and an optional `# ...` comment up to `\n` or EOF. -/
def skipHorizAndComment (cs : List Char) : List Char :=
  match skipHorizWs cs with
  | '#' :: rest => skipCommentBody rest
  | other => other

/-- Two-state structural trivia skipper consuming whitespace, newlines, and `# ...` comments. -/
def skipTriviaNewlinesAux (inComment : Bool) : List Char → List Char
  | [] => []
  | '\n' :: rest => skipTriviaNewlinesAux false rest
  | c :: rest =>
    if inComment then
      skipTriviaNewlinesAux true rest
    else if isHorizWs c then
      skipTriviaNewlinesAux false rest
    else if c == '#' then
      skipTriviaNewlinesAux true rest
    else
      c :: rest

/-- Skip whitespace, newlines, and `# ...` comments across multiple lines. -/
def skipTriviaNewlines (cs : List Char) : List Char :=
  skipTriviaNewlinesAux false cs

/-- Parse a single hexadecimal digit into `0..15`. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Consume `count` hexadecimal digits for `\uXXXX` / `\UXXXXXXXX`. -/
def takeHexDigits : Nat → Nat → List Char → Option (Nat × List Char)
  | 0, acc, rest => some (acc, rest)
  | k + 1, acc, c :: rest =>
    match hexVal? c with
    | some d => takeHexDigits k (acc * 16 + d) rest
    | none => none
  | _ + 1, _, [] => none

/-- Parse `count` hexadecimal digits from `cs`, checking Unicode scalar range `0..0x10FFFF` excluding surrogates. -/
def parseUnicodeHex (count : Nat) (cs : List Char) : Except TomlError (Char × List Char) :=
  match takeHexDigits count 0 cs with
  | none => .error (mkErr .parseError "invalid hexadecimal digits in Unicode escape")
  | some (code, rest) =>
    if code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF) then
      .error (mkErr .invalidUtf8OrControl "Unicode escape scalar value out of valid UTF-8 range")
    else
      .ok (Char.ofNat code, rest)

/-- Parse one basic-string escape sequence after `'\\'`. -/
def parseBasicEscape : List Char → Except TomlError (Char × List Char)
  | 'b' :: rest => .ok ('\x08', rest)
  | 't' :: rest => .ok ('\t', rest)
  | 'n' :: rest => .ok ('\n', rest)
  | 'f' :: rest => .ok ('\x0c', rest)
  | 'r' :: rest => .ok ('\r', rest)
  | '"' :: rest => .ok ('"', rest)
  | '\\' :: rest => .ok ('\\', rest)
  | 'u' :: rest => parseUnicodeHex 4 rest
  | 'U' :: rest => parseUnicodeHex 8 rest
  | _ => .error (mkErr .parseError "invalid escape sequence in basic string")

/-- Fuel-indexed parser for single-line basic string body after opening `'"'`. -/
def parseBasicStringBodyFuel : Nat → List Char → List Char → Except TomlError (String × List Char)
  | 0, _, _ => .error (mkErr .parseError "unterminated basic string")
  | _ + 1, _, [] => .error (mkErr .parseError "unterminated basic string")
  | _ + 1, _, '\n' :: _ => .error (mkErr .parseError "newline not allowed in single-line basic string")
  | _ + 1, acc, '"' :: rest => .ok (String.ofList acc.reverse, rest)
  | fuel + 1, acc, '\\' :: rest => do
    let (ch, afterEsc) ← parseBasicEscape rest
    parseBasicStringBodyFuel fuel (ch :: acc) afterEsc
  | fuel + 1, acc, c :: rest => parseBasicStringBodyFuel fuel (c :: acc) rest

/-- Parse a single-line basic string after opening `'"'`. -/
def parseBasicStringBody (cs : List Char) : Except TomlError (String × List Char) :=
  parseBasicStringBodyFuel (cs.length + 1) [] cs

/-- Structural parser for single-line literal string body after opening `'\''`. -/
def parseLiteralStringBody (acc : List Char) : List Char → Except TomlError (String × List Char)
  | [] => .error (mkErr .parseError "unterminated literal string")
  | '\n' :: _ => .error (mkErr .parseError "newline not allowed in single-line literal string")
  | '\'' :: rest => .ok (String.ofList acc.reverse, rest)
  | c :: rest => parseLiteralStringBody (c :: acc) rest

/-- Fuel-indexed parser for multiline basic string body after optional opener newline trim. -/
def parseMultilineBasicBodyFuel : Nat → List Char → List Char → Except TomlError (String × List Char)
  | 0, _, _ => .error (mkErr .parseError "unterminated multiline basic string")
  | _ + 1, _, [] => .error (mkErr .parseError "unterminated multiline basic string")
  | _ + 1, _, '"' :: '"' :: '"' :: '"' :: '"' :: '"' :: _ =>
    .error (mkErr .parseError "too many consecutive quotes at end of multiline basic string")
  | _ + 1, acc, '"' :: '"' :: '"' :: '"' :: '"' :: rest =>
    .ok (String.ofList ('"' :: '"' :: acc).reverse, rest)
  | _ + 1, acc, '"' :: '"' :: '"' :: '"' :: rest =>
    .ok (String.ofList ('"' :: acc).reverse, rest)
  | _ + 1, acc, '"' :: '"' :: '"' :: rest =>
    .ok (String.ofList acc.reverse, rest)
  | fuel + 1, acc, '\\' :: rest =>
    match parseBasicEscape rest with
    | .ok (ch, afterEsc) => parseMultilineBasicBodyFuel fuel (ch :: acc) afterEsc
    | .error err =>
      match skipHorizWs rest with
      | '\n' :: afterNl => parseMultilineBasicBodyFuel fuel acc (skipHorizAndNl afterNl)
      | _ =>
        match rest with
        | 'u' :: _ => .error err
        | 'U' :: _ => .error err
        | _ => .error (mkErr .parseError "invalid escape sequence in multiline basic string")
  | fuel + 1, acc, c :: rest => parseMultilineBasicBodyFuel fuel (c :: acc) rest

/-- Parse a multiline basic string after opening `"""`. -/
def parseMultilineBasicString (cs : List Char) : Except TomlError (String × List Char) :=
  let body := match cs with | '\n' :: r => r | r => r
  parseMultilineBasicBodyFuel (body.length + 1) [] body

/-- Fuel-indexed parser for multiline literal string body after optional opener newline trim. -/
def parseMultilineLiteralBodyFuel : Nat → List Char → List Char → Except TomlError (String × List Char)
  | 0, _, _ => .error (mkErr .parseError "unterminated multiline literal string")
  | _ + 1, _, [] => .error (mkErr .parseError "unterminated multiline literal string")
  | _ + 1, _, '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: _ =>
    .error (mkErr .parseError "too many consecutive single quotes at end of multiline literal string")
  | _ + 1, acc, '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: rest =>
    .ok (String.ofList ('\'' :: '\'' :: acc).reverse, rest)
  | _ + 1, acc, '\'' :: '\'' :: '\'' :: '\'' :: rest =>
    .ok (String.ofList ('\'' :: acc).reverse, rest)
  | _ + 1, acc, '\'' :: '\'' :: '\'' :: rest =>
    .ok (String.ofList acc.reverse, rest)
  | fuel + 1, acc, c :: rest => parseMultilineLiteralBodyFuel fuel (c :: acc) rest

/-- Parse a multiline literal string after opening `'''`. -/
def parseMultilineLiteralString (cs : List Char) : Except TomlError (String × List Char) :=
  let body := match cs with | '\n' :: r => r | r => r
  parseMultilineLiteralBodyFuel (body.length + 1) [] body

/-- Consume leading ASCII bare-key characters `[A-Za-z0-9_-]`. -/
def takeBareKeyChars (acc : List Char) : List Char → List Char × List Char
  | c :: rest =>
    if isBareKeyChar c then takeBareKeyChars (c :: acc) rest
    else (acc.reverse, c :: rest)
  | [] => (acc.reverse, [])

/-- Parse a single key segment (bare, basic quoted, or literal quoted; multiline keys rejected). -/
def parseKeySegment : List Char → Except TomlError (String × List Char)
  | '"' :: '"' :: '"' :: _ => .error (mkErr .parseError "multiline basic string cannot be used as a key")
  | '\'' :: '\'' :: '\'' :: _ => .error (mkErr .parseError "multiline literal string cannot be used as a key")
  | '"' :: rest => parseBasicStringBody rest
  | '\'' :: rest => parseLiteralStringBody [] rest
  | cs =>
    let (ks, rest) := takeBareKeyChars [] cs
    if ks.isEmpty then .error (mkErr .parseError "expected key")
    else .ok (String.ofList ks, rest)

/-- Fuel-indexed parser for a non-empty dotted key path `k1.k2...`. -/
def parseDottedKeyFuel : Nat → List Char → Except TomlError (List String × List Char)
  | 0, _ => .error (mkErr .parseError "expected key")
  | fuel + 1, cs => do
    let (k, r1) ← parseKeySegment cs
    let r2 := skipHorizWs r1
    match r2 with
    | '.' :: r3 => do
      let (restKeys, r4) ← parseDottedKeyFuel fuel (skipHorizWs r3)
      .ok (k :: restKeys, r4)
    | other => .ok ([k], other)

/-- Parse a non-empty dotted key path. -/
def parseDottedKey (cs : List Char) : Except TomlError (List String × List Char) :=
  parseDottedKeyFuel (cs.length + 1) cs

/-- Check whether `c` is an ASCII decimal digit. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Convert an ASCII decimal digit character to its numeric value `0..9`. -/
def digitVal (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Parse two ASCII digits into a natural number `< 100`. -/
def twoDigitsNat? (c1 c2 : Char) : Option Nat :=
  if isAsciiDigit c1 && isAsciiDigit c2 then some (digitVal c1 * 10 + digitVal c2) else none

/-- Parse four ASCII digits into a natural number `< 10000`. -/
def fourDigitsNat? (c1 c2 c3 c4 : Char) : Option Nat :=
  if isAsciiDigit c1 && isAsciiDigit c2 && isAsciiDigit c3 && isAsciiDigit c4 then
    some (((digitVal c1 * 10 + digitVal c2) * 10 + digitVal c3) * 10 + digitVal c4)
  else none

/-- Check whether `cs` begins with `YYYY-MM-DD`. -/
def hasDatePrefix : List Char → Bool
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: _ =>
    isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
    isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2
  | _ => false

/-- Check whether `cs` begins with `HH:MM:SS`. -/
def hasTimePrefix : List Char → Bool
  | h1 :: h2 :: ':' :: m1 :: m2 :: ':' :: s1 :: s2 :: _ =>
    isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit m1 && isAsciiDigit m2 &&
    isAsciiDigit s1 && isAsciiDigit s2
  | _ => false

/-- Consume consecutive ASCII decimal digits from `cs`. -/
def takeDigits (acc : List Char) : List Char → List Char × List Char
  | c :: rest => if isAsciiDigit c then takeDigits (c :: acc) rest else (acc.reverse, c :: rest)
  | [] => (acc.reverse, [])

/-- Helper accumulating up to 9 fractional digits right-padded with zeros. -/
def fracDigitsToNanosAux : Nat → Nat → List Char → Nat
  | 0, acc, _ => acc
  | k + 1, acc, c :: rest => fracDigitsToNanosAux k (acc * 10 + digitVal c) rest
  | k + 1, acc, [] => fracDigitsToNanosAux k (acc * 10) []

/-- Convert fractional second digits (truncating beyond 9) into nanoseconds clamped to `0..999999999`. -/
def fracDigitsToNanos (ds : List Char) : Nat :=
  min 999999999 (fracDigitsToNanosAux 9 0 ds)

/-- Parse `YYYY-MM-DD` from the head of `cs`. -/
def parseDatePart : List Char → Except TomlError (Std.Time.PlainDate × List Char)
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: rest =>
    match fourDigitsNat? y1 y2 y3 y4, twoDigitsNat? m1 m2, twoDigitsNat? d1 d2 with
    | some y, some m, some d =>
      if hm : m ≥ 1 ∧ m ≤ 12 then
        if hd : d ≥ 1 ∧ d ≤ 31 then
          match Std.Time.PlainDate.ofYearMonthDay?
              (Std.Time.Year.Offset.ofInt (Int.ofNat y))
              (Std.Time.Month.Ordinal.ofNat m hm)
              (Std.Time.Day.Ordinal.ofNat d hd) with
          | some date =>
            if validTomlDate date then .ok (date, rest)
            else .error (mkErr .parseError "RFC 3339 date year out of TOML range")
          | none => .error (mkErr .parseError "invalid calendar date in RFC 3339 literal")
        else .error (mkErr .parseError "invalid day in RFC 3339 date")
      else .error (mkErr .parseError "invalid month in RFC 3339 date")
    | _, _, _ => .error (mkErr .parseError "invalid digits in RFC 3339 date")
  | _ => .error (mkErr .parseError "expected RFC 3339 date YYYY-MM-DD")

/-- Parse `HH:MM:SS(.frac)?` from the head of `cs`. -/
def parseTimePart : List Char → Except TomlError (Std.Time.PlainTime × List Char)
  | h1 :: h2 :: ':' :: m1 :: m2 :: ':' :: s1 :: s2 :: rest =>
    match twoDigitsNat? h1 h2, twoDigitsNat? m1 m2, twoDigitsNat? s1 s2 with
    | some hh, some mm, some ss =>
      if hh_ok : hh ≤ 23 then
        if mm_ok : mm ≤ 59 then
          if ss_ok : ss ≤ 59 then
            match rest with
            | '.' :: fracStart =>
              let (fracDs, afterFrac) := takeDigits [] fracStart
              if fracDs.isEmpty then
                .error (mkErr .parseError "fractional second dot must be followed by digits")
              else
                let nano := fracDigitsToNanos fracDs
                let tm := Std.Time.PlainTime.mk
                  (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
                  (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
                  (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
                  (Std.Time.Nanosecond.Ordinal.ofNat nano (Nat.min_le_left _ _))
                .ok (tm, afterFrac)
            | other =>
              let tm := Std.Time.PlainTime.mk
                (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
                (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
                (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
                0
              .ok (tm, other)
          else .error (mkErr .parseError "RFC 3339 second out of range 00..59")
        else .error (mkErr .parseError "RFC 3339 minute out of range 00..59")
      else .error (mkErr .parseError "RFC 3339 hour out of range 00..23")
    | _, _, _ => .error (mkErr .parseError "invalid digits in RFC 3339 time")
  | _ => .error (mkErr .parseError "expected RFC 3339 time HH:MM:SS")

/-- Parse an RFC 3339 timezone offset (`Z`, `z`, or `±HH:MM`) consuming the entire list. -/
def parseOffsetPart : List Char → Except TomlError Std.Time.TimeZone.Offset
  | ['Z'] => .ok (Std.Time.TimeZone.Offset.ofSeconds 0)
  | ['z'] => .ok (Std.Time.TimeZone.Offset.ofSeconds 0)
  | [sign, h1, h2, ':', m1, m2] =>
    if sign == '+' || sign == '-' then
      match twoDigitsNat? h1 h2, twoDigitsNat? m1 m2 with
      | some hh, some mm =>
        if hh ≤ 23 && mm ≤ 59 then
          let total : Int := Int.ofNat (hh * 3600 + mm * 60)
          let sec : Int := if total == 0 then 0 else if sign == '-' then -total else total
          let off := Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt sec)
          if validTomlOffset off then .ok off
          else .error (mkErr .parseError "RFC 3339 offset out of range")
        else .error (mkErr .parseError "RFC 3339 offset hour/minute out of range")
      | _, _ => .error (mkErr .parseError "invalid digits in RFC 3339 offset")
    else .error (mkErr .parseError "invalid sign in RFC 3339 offset")
  | _ => .error (mkErr .parseError "invalid RFC 3339 timezone offset")

/-- Attempt to classify and parse an unquoted token as one of the 4 RFC 3339 datetime kinds. -/
def parseDateTimeToken (tok : String) : Option (Except TomlError TomlValue) :=
  let cs := tok.toList
  if hasDatePrefix cs then
    match parseDatePart cs with
    | .error e => some (.error e)
    | .ok (date, []) => some (.ok (.localDate date))
    | .ok (date, sep :: timeCs) =>
      if sep == 'T' || sep == 't' || sep == ' ' then
        match parseTimePart timeCs with
        | .error e => some (.error e)
        | .ok (tm, []) => some (.ok (.localDateTime (Std.Time.PlainDateTime.mk date tm)))
        | .ok (tm, offCs) =>
          match parseOffsetPart offCs with
          | .error e => some (.error e)
          | .ok off => some (.ok (.offsetDateTime { dateTime := Std.Time.PlainDateTime.mk date tm, offset := off }))
      else
        some (.error (mkErr .parseError "invalid separator in RFC 3339 date-time"))
  else if hasTimePrefix cs then
    match parseTimePart cs with
    | .error e => some (.error e)
    | .ok (tm, []) => some (.ok (.localTime tm))
    | .ok (_, _ :: _) => some (.error (mkErr .parseError "unexpected trailing characters in local time"))
  else if tok.toList.contains ':' then
    some (.error (mkErr .parseError "malformed time literal"))
  else
    none

/-- Check whether `c` terminates an unquoted TOML scalar token. -/
def isUnquotedDelim (c : Char) : Bool :=
  isHorizWs c || c == '\n' || c == '#' || c == ',' || c == ']' || c == '}'

/-- Consume non-delimiter characters into an unquoted token string and remaining chars. -/
def takeNonDelim (acc : List Char) : List Char → List Char × List Char
  | c :: rest =>
    if isUnquotedDelim c then (acc.reverse, c :: rest)
    else takeNonDelim (c :: acc) rest
  | [] => (acc.reverse, [])

/-- Consume an unquoted scalar token, allowing a single `0x20` space separator in `YYYY-MM-DD HH:MM:SS...`. -/
def takeUnquotedToken (cs : List Char) : String × List Char :=
  match cs with
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: ' ' ::
      h1 :: h2 :: ':' :: min1 :: min2 :: ':' :: s1 :: s2 :: rest =>
    if isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
       isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
       isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
       isAsciiDigit s1 && isAsciiDigit s2 then
      let pfx := [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2]
      let (tail, after) := takeNonDelim [] rest
      (String.ofList (pfx ++ tail), after)
    else
      let (tok, after) := takeNonDelim [] cs
      (String.ofList tok, after)
  | _ =>
    let (tok, after) := takeNonDelim [] cs
    (String.ofList tok, after)

/-- Map `NumParseError` to `TomlError` (`overflow` -> `.numericOverflow`, others -> `.parseError`). -/
def mapNumParseErr (e : NumParseError) : TomlError :=
  let kind := if e.kind == .overflow then TomlErrorKind.numericOverflow else TomlErrorKind.parseError
  mkErr kind e.message

/-- Check whether an integer token begins with a forbidden uppercase base prefix `0X`/`0O`/`0B`. -/
def hasUppercaseBasePrefix (tok : String) : Bool :=
  tok.startsWith "0X" || tok.startsWith "0O" || tok.startsWith "0B" ||
  tok.startsWith "+0X" || tok.startsWith "+0O" || tok.startsWith "+0B" ||
  tok.startsWith "-0X" || tok.startsWith "-0O" || tok.startsWith "-0B"

/-- Check whether an unquoted token should be routed to float parsing rather than integer parsing. -/
def isFloatTokenCandidate (tok : String) : Bool :=
  let isSpecial :=
    tok == "inf" || tok == "+inf" || tok == "-inf" ||
    tok == "nan" || tok == "+nan" || tok == "-nan"
  let hasHexPrefix :=
    tok.startsWith "0x" || tok.startsWith "0X" ||
    tok.startsWith "+0x" || tok.startsWith "-0x" ||
    tok.startsWith "+0X" || tok.startsWith "-0X"
  isSpecial || (!hasHexPrefix && (tok.toList.contains '.' || tok.toList.contains 'e' || tok.toList.contains 'E'))

/-- Classify and parse an unquoted TOML scalar token using `numApi`. -/
def classifyScalarToken (numApi : NumParseApi) (tok : String) : Except TomlError TomlValue :=
  if tok.isEmpty then
    .error (mkErr .parseError "expected TOML value")
  else if tok == "true" then
    .ok (.bool true)
  else if tok == "false" then
    .ok (.bool false)
  else
    match parseDateTimeToken tok with
    | some res => res
    | none =>
      if isFloatTokenCandidate tok then
        match numApi.parseFloat tok with
        | .ok f => .ok (.float f)
        | .error e => .error (mapNumParseErr e)
      else if hasUppercaseBasePrefix tok then
        .error (mkErr .parseError "uppercase integer base prefix is not allowed in TOML")
      else
        match numApi.parseInt64 tok with
        | .ok n => .ok (.int n)
        | .error e => .error (mapNumParseErr e)

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
  def parseValueFuel (numApi : NumParseApi) : Nat → List Char → Except TomlError (TomlValue × List Char)
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
        let (tok, after) := takeUnquotedToken cs
        let v ← classifyScalarToken numApi tok
        .ok (v, after)

  /-- Fuel-indexed array parser supporting multiline whitespace, `#` comments, and trailing commas. -/
  def parseArrayFuel (numApi : NumParseApi) : Nat → List Char → List TomlValue → Except TomlError (TomlValue × List Char)
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
  def parseInlineTableFuel (numApi : NumParseApi) :
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
def parseValue (numApi : NumParseApi) (cs : List Char) : Except TomlError (TomlValue × List Char) :=
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

/-- Traverse or open a `[table]` header along `path`, enforcing 4-state provenance rules. -/
def applyTableHeader (fullPath : List String) :
    List (String × Node) → List String → Except TomlError (List (String × Node))
  | _, [] => .error (mkErr .parseError "empty table header path")
  | entries, [k] =>
    match assocLookupNode k entries with
    | none => .ok (assocSetNode k (.table .explicit []) entries)
    | some (.table .subtableImplicit sub) => .ok (assocSetNode k (.table .explicit sub) entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot reopen inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot reopen inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some _ =>
      .error (mkErr .redefinedTable ("table already defined: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
  | entries, k :: rest =>
    match assocLookupNode k entries with
    | none => do
      let sub ← applyTableHeader fullPath [] rest
      .ok (assocSetNode k (.table .subtableImplicit sub) entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot traverse inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot traverse inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.table kind sub) => do
      let nextSub ← applyTableHeader fullPath sub rest
      .ok (assocSetNode k (.table kind nextSub) entries)
    | some (.aot elems) => do
      let nextElems ← mapLastAot (fun elem => applyTableHeader fullPath elem rest) elems
      .ok (assocSetNode k (.aot nextElems) entries)
    | some (.leaf _) =>
      .error (mkErr .redefinedTable ("cannot traverse non-table value in header: " ++ k)
        (path := some (joinPath fullPath)))

/-- Traverse or append an `[[array_of_tables]]` header along `path`. -/
def applyAotHeader (fullPath : List String) :
    List (String × Node) → List String → Except TomlError (List (String × Node))
  | _, [] => .error (mkErr .parseError "empty array-of-tables header path")
  | entries, [k] =>
    match assocLookupNode k entries with
    | none => .ok (assocSetNode k (.aot [[]]) entries)
    | some (.aot elems) => .ok (assocSetNode k (.aot (elems ++ [[]])) entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot append to inline table as array of tables: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot append to inline table as array of tables: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some _ =>
      .error (mkErr .redefinedTable ("cannot redefine non-AoT entry as array of tables: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
  | entries, k :: rest =>
    match assocLookupNode k entries with
    | none => do
      let sub ← applyAotHeader fullPath [] rest
      .ok (assocSetNode k (.table .subtableImplicit sub) entries)
    | some (.table .inline _) =>
      .error (mkErr .immutableInlineTable ("cannot traverse inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.leaf (.table _)) =>
      .error (mkErr .immutableInlineTable ("cannot traverse inline table: " ++ joinPath fullPath)
        (path := some (joinPath fullPath)))
    | some (.table kind sub) => do
      let nextSub ← applyAotHeader fullPath sub rest
      .ok (assocSetNode k (.table kind nextSub) entries)
    | some (.aot elems) => do
      let nextElems ← mapLastAot (fun elem => applyAotHeader fullPath elem rest) elems
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
def parseDocumentFuel (numApi : NumParseApi) :
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
        let nextRoot ← applyAotHeader path root path
        parseDocumentFuel numApi fuel nextCs path nextRoot
      | _ => .error (mkErr .parseError "expected ']]' closing array-of-tables header")
    | '[' :: rest => do
      let (path, r1) ← parseDottedKey (skipHorizWs rest)
      match skipHorizWs r1 with
      | ']' :: r2 => do
        let nextCs ← consumeStatementEnd r2
        let nextRoot ← applyTableHeader path root path
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

/-- Pure TOML 1.0 parser parameterized over `NumParseApi`. -/
def parseWithNum (numApi : NumParseApi) (input : String) : Except TomlError TomlTable := do
  let normalized ← normalizeChars 1 1 input.toList
  let root ← parseDocumentFuel numApi (normalized.length + 1) normalized [] []
  .ok (entriesToTomlList root).toArray

/-- Format a key using bare syntax when ASCII bare-valid, or basic escaped quotes otherwise. -/
def formatKey (k : String) : String :=
  if isValidBareKey k then k else "\"" ++ escapeBasicBody false k ++ "\""

/-- Format a fractional nanosecond value trimming trailing zeros, or `""` when zero. -/
def formatNanosTrimmed (nano : Nat) : String :=
  if nano == 0 then ""
  else
    let padded := padNatZero 9 nano
    let trimmedRev := padded.toList.reverse.dropWhile (· == '0')
    "." ++ String.ofList trimmedRev.reverse

/-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
def formatDate (d : Std.Time.PlainDate) : String :=
  padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat

/-- Format a `Std.Time.PlainTime` as `HH:MM:SS(.trimmed)?`. -/
def formatTime (t : Std.Time.PlainTime) : String :=
  padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
    padNatZero 2 t.second.val.toNat ++ formatNanosTrimmed t.nanosecond.val.toNat

/-- Format a `Std.Time.TimeZone.Offset` as `Z` when `0` or `±HH:MM` otherwise. -/
def formatOffset (o : Std.Time.TimeZone.Offset) : String :=
  if o.second.val == 0 then "Z"
  else
    let sign := if o.second.val < 0 then "-" else "+"
    let absMin := o.second.val.natAbs / 60
    sign ++ padNatZero 2 (absMin / 60) ++ ":" ++ padNatZero 2 (absMin % 60)

/-- Check whether `xs` is a non-empty array whose elements are all `.table _` values (eligible for `[[...]]`). -/
def isNonEmptyTableArray (xs : Array TomlValue) : Bool :=
  !xs.isEmpty && xs.toList.all fun v => match v with | .table _ => true | _ => false

mutual
  /-- Format any `TomlValue` on a single line (used for scalars, arrays, and inline tables). -/
  def formatValueInline (numApi : NumParseApi) : TomlValue → String
    | .string s => "\"" ++ escapeBasicBody false s ++ "\""
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
  match lookupKey key t with
  | none => .error (mkErr .missingField ("missing TOML field: " ++ key) (path := some key))
  | some v =>
    match FromToml.fromToml v with
    | .ok a => .ok a
    | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := some key }

/-- Look up optional `key` in `t`, returning `none` when absent and decoding via `FromToml` when present. -/
def tomlGetOptField {α : Type} [FromToml α] (t : TomlTable) (key : String) : Except TomlError (Option α) :=
  match lookupKey key t with
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
    match lookupKey k t with
    | none => .error (mkErr .missingField ("missing TOML field: " ++ full) (path := some full))
    | some v =>
      match FromToml.fromToml v with
      | .ok a => .ok a
      | .error e => .error { e with kind := .decodeError, message := nonEmptyMsg e.message, path := some full }
  | k :: k' :: rest =>
    let full := joinPath (revPrefix.reverse ++ [k])
    match lookupKey k t with
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

end LeanSwe.Toml.Impl

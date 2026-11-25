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

/-- Tail-recursive helper for `normalizeChars`, accumulating normalized characters in reverse order. -/
def normalizeCharsAux (line col : Nat) (acc : List Char) : List Char → Except TomlError (List Char)
  | [] => .ok acc.reverse
  | '\r' :: '\n' :: rest =>
    normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest
  | '\r' :: _ =>
    .error (mkErr .invalidUtf8OrControl "bare carriage return is not allowed in TOML" (some line) (some col))
  | '\n' :: rest =>
    normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest
  | c :: rest =>
    if isDisallowedControl c then
      .error (mkErr .invalidUtf8OrControl "disallowed control character in TOML input" (some line) (some col))
    else
      normalizeCharsAux line (col + 1) (c :: acc) rest

/-- Validate input characters and normalize CRLF line endings to LF. -/
def normalizeChars (line col : Nat) (cs : List Char) : Except TomlError (List Char) :=
  normalizeCharsAux line col [] cs

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

/-- Internal char-list numeric parser interface avoiding `String.ofList`/`toList` ping-pong. -/
structure CharNumApi where
  /-- Parse an integer literal from characters. -/
  parseInt64Chars : List Char → Except NumParseError Int64
  /-- Parse a float literal from characters. -/
  parseFloatChars : List Char → Except NumParseError Float

/-- Lift a `NumParseApi` to `CharNumApi` at the outer boundary. -/
def toCharNumApi (numApi : NumParseApi) : CharNumApi :=
  { parseInt64Chars := fun cs => numApi.parseInt64 (String.ofList cs)
  , parseFloatChars := fun cs => numApi.parseFloat (String.ofList cs)
  }

/-- Attempt to classify and parse an unquoted character token as one of the 4 RFC 3339 datetime kinds. -/
def parseDateTimeChars (cs : List Char) : Option (Except TomlError TomlValue) :=
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
  else if cs.contains ':' then
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

/-- Consume an unquoted scalar token as `List Char`, allowing a single `0x20` space separator in `YYYY-MM-DD HH:MM:SS...`. -/
def takeUnquotedTokenChars (cs : List Char) : List Char × List Char :=
  match cs with
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: ' ' ::
      h1 :: h2 :: ':' :: min1 :: min2 :: ':' :: s1 :: s2 :: rest =>
    if isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
       isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
       isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
       isAsciiDigit s1 && isAsciiDigit s2 then
      let pfx := [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2]
      let (tail, after) := takeNonDelim [] rest
      (pfx ++ tail, after)
    else
      takeNonDelim [] cs
  | _ =>
    takeNonDelim [] cs

/-- Map `NumParseError` to `TomlError` (`overflow` -> `.numericOverflow`, others -> `.parseError`). -/
def mapNumParseErr (e : NumParseError) : TomlError :=
  let kind := if e.kind == .overflow then TomlErrorKind.numericOverflow else TomlErrorKind.parseError
  mkErr kind e.message

/-- Check whether an integer char token begins with a forbidden uppercase base prefix `0X`/`0O`/`0B`. -/
def hasUppercaseBasePrefixChars : List Char → Bool
  | '0' :: 'X' :: _ | '0' :: 'O' :: _ | '0' :: 'B' :: _
  | '+' :: '0' :: 'X' :: _ | '+' :: '0' :: 'O' :: _ | '+' :: '0' :: 'B' :: _
  | '-' :: '0' :: 'X' :: _ | '-' :: '0' :: 'O' :: _ | '-' :: '0' :: 'B' :: _ => true
  | _ => false

/-- Check whether an unquoted char token routes to float parsing rather than integer parsing. -/
def isFloatTokenCandidateChars (cs : List Char) : Bool :=
  let isSpecial :=
    cs == ['i', 'n', 'f'] || cs == ['+', 'i', 'n', 'f'] || cs == ['-', 'i', 'n', 'f'] ||
    cs == ['n', 'a', 'n'] || cs == ['+', 'n', 'a', 'n'] || cs == ['-', 'n', 'a', 'n']
  let hasHexPrefix :=
    match cs with
    | '0' :: 'x' :: _ | '0' :: 'X' :: _
    | '+' :: '0' :: 'x' :: _ | '-' :: '0' :: 'x' :: _
    | '+' :: '0' :: 'X' :: _ | '-' :: '0' :: 'X' :: _ => true
    | _ => false
  isSpecial || (!hasHexPrefix && (cs.contains '.' || cs.contains 'e' || cs.contains 'E'))

/-- Classify and parse an unquoted TOML scalar character token using `numApi`. -/
def classifyScalarChars (numApi : CharNumApi) (cs : List Char) : Except TomlError TomlValue :=
  match cs with
  | [] => .error (mkErr .parseError "expected TOML value")
  | ['t', 'r', 'u', 'e'] => .ok (.bool true)
  | ['f', 'a', 'l', 's', 'e'] => .ok (.bool false)
  | _ =>
    match parseDateTimeChars cs with
    | some res => res
    | none =>
      if isFloatTokenCandidateChars cs then
        match numApi.parseFloatChars cs with
        | .ok f => .ok (.float f)
        | .error e => .error (mapNumParseErr e)
      else if hasUppercaseBasePrefixChars cs then
        .error (mkErr .parseError "uppercase integer base prefix is not allowed in TOML")
      else
        match numApi.parseInt64Chars cs with
        | .ok n => .ok (.int n)
        | .error e => .error (mapNumParseErr e)

end LeanSwe.Toml.Impl

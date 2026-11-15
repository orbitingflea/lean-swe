import Init.Data.Float.Model
import LeanSwe.NumParse.Types

namespace LeanSwe.NumParse.Internal

/-- Human-readable label prefix for each `NumParseErrorKind`. -/
def errorKindLabel : NumParseErrorKind → String
  | .emptyInput => "empty numeric input"
  | .invalidSyntax => "invalid numeric syntax"
  | .invalidSignForBase => "disallowed sign before base-prefixed integer"
  | .leadingZero => "disallowed leading zero"
  | .invalidUnderscore => "invalid underscore separator"
  | .overflow => "64-bit integer overflow"
  | .trailingChars => "unexpected trailing characters"

/-- Construct a `NumParseError` guaranteed to have a non-empty diagnostic message. -/
def makeError (kind : NumParseErrorKind) (detail : String) : NumParseError :=
  { kind := kind, message := errorKindLabel kind ++ ": " ++ detail }

/-- Predicate checking whether `c` is an ASCII decimal digit `'0'..'9'`. -/
def isDecDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Map base prefix character (`x`/`X`, `o`/`O`, `b`/`B`) to its numerical radix. -/
def parseBasePrefix? : Char → Option Nat
  | 'x' | 'X' => some 16
  | 'o' | 'O' => some 8
  | 'b' | 'B' => some 2
  | _ => none

/-- Digit value of `c` in `radix` (`2`, `8`, `10`, `16`), or `none`. -/
def digitValue? (radix : Nat) (c : Char) : Option Nat :=
  if radix == 2 then
    if c == '0' then some 0 else if c == '1' then some 1 else none
  else if radix == 8 then
    if '0' ≤ c && c ≤ '7' then some (c.toNat - '0'.toNat) else none
  else if radix == 10 then
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
  else if radix == 16 then
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  else none

/-- Scan remaining digits and underscore separators for an integer literal in `radix`. -/
def scanIntDigits (raw : String) (radix acc : Nat) : List Char → Except NumParseError Nat
  | [] => .ok acc
  | '_' :: c :: cs =>
    match digitValue? radix c with
    | some d => scanIntDigits raw radix (acc * radix + d) cs
    | none => .error (makeError .invalidUnderscore raw)
  | '_' :: [] => .error (makeError .invalidUnderscore raw)
  | c :: cs =>
    match digitValue? radix c with
    | some d => scanIntDigits raw radix (acc * radix + d) cs
    | none => .error (makeError .trailingChars raw)

/-- Parse an unprefixed signed decimal integer literal body. -/
def parseDecSigned (raw : String) (neg : Bool) : List Char → Except NumParseError Int
  | [] => .error (makeError .invalidSyntax raw)
  | '_' :: _ => .error (makeError .invalidUnderscore raw)
  | '0' :: rest =>
    match rest with
    | [] => .ok 0
    | c :: _ =>
      if isDecDigit c then .error (makeError .leadingZero raw)
      else if c == '_' then
        match rest with
        | '_' :: c2 :: _ =>
          if isDecDigit c2 then .error (makeError .leadingZero raw)
          else .error (makeError .invalidUnderscore raw)
        | _ => .error (makeError .invalidUnderscore raw)
      else .error (makeError .trailingChars raw)
  | c :: rest =>
    match digitValue? 10 c with
    | some d =>
      match scanIntDigits raw 10 d rest with
      | .ok n => .ok (if neg then -Int.ofNat n else Int.ofNat n)
      | .error e => .error e
    | none => .error (makeError .invalidSyntax raw)

/-- Parse an integer literal over `List Char` with deterministic left-to-right error precedence. -/
def parseIntChars (raw : String) : List Char → Except NumParseError Int
  | [] => .error (makeError .emptyInput "input string is empty")
  | '+' :: '0' :: b :: rest =>
    if (parseBasePrefix? b).isSome then .error (makeError .invalidSignForBase raw)
    else parseDecSigned raw false ('0' :: b :: rest)
  | '-' :: '0' :: b :: rest =>
    if (parseBasePrefix? b).isSome then .error (makeError .invalidSignForBase raw)
    else parseDecSigned raw true ('0' :: b :: rest)
  | '+' :: rest => parseDecSigned raw false rest
  | '-' :: rest => parseDecSigned raw true rest
  | '0' :: b :: rest =>
    match parseBasePrefix? b with
    | some radix =>
      match rest with
      | [] => .error (makeError .invalidSyntax raw)
      | '_' :: _ => .error (makeError .invalidUnderscore raw)
      | c :: cs =>
        match digitValue? radix c with
        | some d =>
          match scanIntDigits raw radix d cs with
          | .ok n => .ok (Int.ofNat n)
          | .error e => .error e
        | none => .error (makeError .invalidSyntax raw)
    | none => parseDecSigned raw false ('0' :: b :: rest)
  | cs => parseDecSigned raw false cs

/-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into an unbounded `Int`. -/
def parseInt (s : String) : Except NumParseError Int :=
  parseIntChars s s.toList

/-- Minimum signed 64-bit integer bound `-2^63`. -/
def minInt64Bound : Int := -9223372036854775808

/-- Maximum signed 64-bit integer bound `2^63 - 1`. -/
def maxInt64Bound : Int := 9223372036854775807

/-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into a signed `Int64`. -/
def parseInt64 (s : String) : Except NumParseError Int64 :=
  match parseInt s with
  | .error e => .error e
  | .ok n =>
    if minInt64Bound ≤ n && n ≤ maxInt64Bound then
      .ok (Int64.ofInt n)
    else
      .error (makeError .overflow s)

/-- Convert a positive `Nat` to non-empty big-endian ASCII decimal characters prepended onto `acc`. -/
def natToDecCharsPos : Nat → List Char → List Char
  | 0, acc => acc
  | n + 1, acc =>
    let q := (n + 1) / 10
    let r := (n + 1) % 10
    natToDecCharsPos q (Char.ofNat ('0'.toNat + r) :: acc)
termination_by n => n

/-- Format an `Int` as a canonical list of ASCII decimal characters. -/
def formatIntChars : Int → List Char
  | .ofNat 0 => ['0']
  | .ofNat (n + 1) => natToDecCharsPos (n + 1) []
  | .negSucc n => '-' :: natToDecCharsPos (n + 1) []

/-- Format an `Int` as a canonical base-10 decimal string without underscores. -/
def formatInt (n : Int) : String :=
  String.ofList (formatIntChars n)

/-- Scan decimal digits and underscore separators for a float part. -/
def scanDecFloatDigits (raw : String) (acc count : Nat) :
    List Char → Except NumParseError (Nat × Nat × List Char)
  | [] => .ok (acc, count, [])
  | '_' :: c :: cs =>
    if isDecDigit c then
      scanDecFloatDigits raw (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) cs
    else
      .error (makeError .invalidUnderscore raw)
  | '_' :: [] => .error (makeError .invalidUnderscore raw)
  | c :: cs =>
    if isDecDigit c then
      scanDecFloatDigits raw (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) cs
    else
      .ok (acc, count, c :: cs)

/-- Parse the integer significand part of a float literal. -/
def parseFloatIntPart (raw : String) : List Char → Except NumParseError (Nat × List Char)
  | [] => .error (makeError .invalidSyntax raw)
  | '_' :: _ => .error (makeError .invalidUnderscore raw)
  | '0' :: rest =>
    match rest with
    | c :: _ =>
      if isDecDigit c then .error (makeError .leadingZero raw)
      else if c == '_' then
        match rest with
        | '_' :: c2 :: _ =>
          if isDecDigit c2 then .error (makeError .leadingZero raw)
          else .error (makeError .invalidUnderscore raw)
        | _ => .error (makeError .invalidUnderscore raw)
      else .ok (0, rest)
    | [] => .ok (0, [])
  | c :: rest =>
    if isDecDigit c then
      match scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
      | .ok (m, _, rem) => .ok (m, rem)
      | .error e => .error e
    else
      .error (makeError .invalidSyntax raw)

/-- Parse the signed exponent part of a float literal. -/
def parseFloatExpPart (raw : String) (cs : List Char) :
    Except NumParseError (Int × List Char) :=
  let (expNeg, afterSign) :=
    match cs with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  match afterSign with
  | [] => .error (makeError .invalidSyntax raw)
  | '_' :: _ => .error (makeError .invalidUnderscore raw)
  | c :: rest =>
    if isDecDigit c then
      match scanDecFloatDigits raw (c.toNat - '0'.toNat) 1 rest with
      | .ok (eMag, _, rem) => .ok (if expNeg then -Int.ofNat eMag else Int.ofNat eMag, rem)
      | .error e => .error e
    else
      .error (makeError .invalidSyntax raw)

/-- Evaluate `(-1)^neg * mantissa * 10^exp10` as a binary64 `Float` via `Float.Model.ofScientific`. -/
def evalScientificFloat (neg : Bool) (mantissa : Nat) (exp10 : Int) : Float :=
  let m := Float.Model.ofScientific mantissa exp10
  Float.ofModel (if neg then -m else m)

/-- Parse an exponent tail after `'e'`/`'E'` and ensure no trailing characters remain. -/
def parseFloatExpTail (raw : String) (neg : Bool) (mantissa : Nat) (fracAdj : Int)
    (afterE : List Char) : Except NumParseError Float :=
  match parseFloatExpPart raw afterE with
  | .error e => .error e
  | .ok (expVal, afterExp) =>
    if afterExp.isEmpty then .ok (evalScientificFloat neg mantissa (expVal + fracAdj))
    else .error (makeError .trailingChars raw)

/-- Parse a TOML 1.0 float literal over `List Char`. -/
def parseFloatChars (raw : String) : List Char → Except NumParseError Float
  | [] => .error (makeError .emptyInput "input string is empty")
  | cs =>
    let (neg, body) :=
      match cs with
      | '+' :: rest => (false, rest)
      | '-' :: rest => (true, rest)
      | _ => (false, cs)
    match body with
    | 'i' :: 'n' :: 'f' :: rest =>
      match rest with
      | [] => .ok (if neg then -Float.inf else Float.inf)
      | _ :: _ => .error (makeError .trailingChars raw)
    | 'n' :: 'a' :: 'n' :: rest =>
      match rest with
      | [] => .ok Float.nan
      | _ :: _ => .error (makeError .trailingChars raw)
    | _ =>
      match parseFloatIntPart raw body with
      | .error e => .error e
      | .ok (intVal, afterInt) =>
        match afterInt with
        | '.' :: afterDot =>
          match afterDot with
          | '_' :: _ => .error (makeError .invalidUnderscore raw)
          | c :: rest =>
            if isDecDigit c then
              match scanDecFloatDigits raw (intVal * 10 + (c.toNat - '0'.toNat)) 1 rest with
              | .error e => .error e
              | .ok (mantissa, fracCount, afterFrac) =>
                match afterFrac with
                | 'e' :: afterE => parseFloatExpTail raw neg mantissa (-Int.ofNat fracCount) afterE
                | 'E' :: afterE => parseFloatExpTail raw neg mantissa (-Int.ofNat fracCount) afterE
                | [] => .ok (evalScientificFloat neg mantissa (-Int.ofNat fracCount))
                | _ :: _ => .error (makeError .trailingChars raw)
            else
              .error (makeError .invalidSyntax raw)
          | [] => .error (makeError .invalidSyntax raw)
        | 'e' :: afterE => parseFloatExpTail raw neg intVal 0 afterE
        | 'E' :: afterE => parseFloatExpTail raw neg intVal 0 afterE
        | _ => .error (makeError .invalidSyntax raw)

/-- Parse a TOML 1.0 decimal float or lowercase special literal (`inf`, `-inf`, `nan`) into binary64 `Float`. -/
def parseFloat (s : String) : Except NumParseError Float :=
  parseFloatChars s s.toList

/-- Render a positive scientific pair `(mant, exp10)` strictly in scientific notation (`d.ddde±k` or `de±k`). -/
def renderScientific (neg : Bool) (mant : Nat) (exp10 : Int) : String :=
  let ds := natToDecCharsPos mant []
  let prefixChars := if neg then ['-'] else []
  match ds with
  | [] => "0.0"
  | [d] => String.ofList (prefixChars ++ [d, 'e'] ++ formatIntChars exp10)
  | d :: rest =>
    let adjExp := exp10 + Int.ofNat rest.length
    String.ofList (prefixChars ++ [d, '.'] ++ rest ++ ['e'] ++ formatIntChars adjExp)

/-- Choose a clean decimal or scientific formatting for `(neg, mant, exp10)` alongside the exact `(effMant, effExp)` parsed back by `parseFloat`. -/
def renderFloatChoice (neg : Bool) (mant : Nat) (exp10 : Int) : Nat × Int × String :=
  let ds := natToDecCharsPos mant []
  let len := ds.length
  let sciExp : Int := exp10 + Int.ofNat len - 1
  if -4 ≤ sciExp && sciExp ≤ 6 then
    let prefixChars := if neg then ['-'] else []
    if 0 ≤ exp10 then
      let pad := exp10.toNat
      let s := String.ofList (prefixChars ++ ds ++ List.replicate pad '0' ++ ['.', '0'])
      (mant * 10 ^ (pad + 1), -1, s)
    else
      let k := (-exp10).toNat
      if k < len then
        let s := String.ofList (prefixChars ++ ds.take (len - k) ++ ['.'] ++ ds.drop (len - k))
        (mant, exp10, s)
      else
        let s := String.ofList (prefixChars ++ ['0', '.'] ++ List.replicate (k - len) '0' ++ ds)
        (mant, exp10, s)
  else
    (mant, exp10, renderScientific neg mant exp10)

/-- Strip trailing base-10 zeros from a positive mantissa while incrementing `exp10`. -/
def stripTrailingZeros (mant : Nat) (exp10 : Int) : Nat × Int :=
  if _h : mant = 0 then (0, exp10)
  else if mant % 10 == 0 then stripTrailingZeros (mant / 10) (exp10 + 1)
  else (mant, exp10)
termination_by mant
decreasing_by omega

/-- Format a candidate `(mant, exp10)` and return it iff parsing back preserves `x.toBits`. -/
def checkFloatCandidate (x : Float) (neg : Bool) (mant : Nat) (exp10 : Int) : Option String :=
  if mant == 0 then none
  else
    let (m', e') := stripTrailingZeros mant exp10
    let (effMant, effExp, str) := renderFloatChoice neg m' e'
    if (evalScientificFloat neg effMant effExp).toBits == x.toBits then some str else none

/-- Round `num / den` to the nearest integer with ties rounded up. -/
def roundScaledCandidate (num den : Nat) : Nat :=
  (2 * num + den) / (2 * den)

/-- Try formatting `(-1)^neg * m * 2^e2` using `digits` decimal digits. -/
def tryDigitsCount (x : Float) (neg : Bool) (m : Nat) (e2 : Int) (kEst : Int) (digits : Nat) :
    Option String :=
  let tryOne (e10 : Int) : Option String :=
    let (num, den) :=
      if 0 ≤ e10 then
        let p := e10.toNat
        if 0 ≤ e2 then (m <<< e2.toNat, 10 ^ p)
        else (m, (10 ^ p) <<< (-e2).toNat)
      else
        let p := (-e10).toNat
        let s := e2 + Int.ofNat p
        if 0 ≤ s then ((m * 5 ^ p) <<< s.toNat, 1)
        else (m * 5 ^ p, 1 <<< (-s).toNat)
    let q := roundScaledCandidate num den
    match checkFloatCandidate x neg q e10 with
    | some s => some s
    | none =>
      match checkFloatCandidate x neg (q + 1) e10 with
      | some s => some s
      | none =>
        if 1 < q then checkFloatCandidate x neg (q - 1) e10 else none
  let baseExp := kEst - Int.ofNat digits + 1
  match tryOne baseExp with
  | some s => some s
  | none => tryOne (baseExp - 1)

/-- Search for the shortest 1..17-digit decimal string matching `x.toBits`. -/
def searchShortCandidate (x : Float) (neg : Bool) (m : Nat) (e2 : Int) (kEst : Int) :
    Nat → Option String
  | 0 => none
  | n + 1 =>
    let d := 18 - (n + 1)
    match tryDigitsCount x neg m e2 kEst d with
    | some s => some s
    | none => searchShortCandidate x neg m e2 kEst n

/-- Format a `Float` into a canonical TOML 1.0 decimal/scientific or lowercase special literal preserving bit identity for non-NaNs. -/
def formatFloat (x : Float) : String :=
  if x.isNaN then
    "nan"
  else if x == Float.inf then
    "inf"
  else if x == -Float.inf then
    "-inf"
  else
    match x.toModel.unpack with
    | .notANumber => "nan"
    | .infinity .positive => "inf"
    | .infinity .negative => "-inf"
    | .zero .positive => "0.0"
    | .zero .negative => "-0.0"
    | .finite sign m e2 _ =>
      let neg := match sign with | .positive => false | .negative => true
      let b : Int := Int.ofNat m.log2 + 1 + e2
      let kEst : Int := Int.fdiv (b * 1233) 4096
      match searchShortCandidate x neg m e2 kEst 17 with
      | some s => s
      | none =>
        if 0 ≤ e2 then
          renderScientific neg (m <<< e2.toNat) 0
        else
          renderScientific neg (m * 5 ^ (-e2).toNat) e2

/-- Default `NumParseApi` instance bundling the concrete `LeanSwe.NumParse` operations. -/
def defaultApi : NumParseApi :=
  { parseInt := parseInt
  , parseInt64 := parseInt64
  , formatInt := formatInt
  , parseFloat := parseFloat
  , formatFloat := formatFloat
  }

end LeanSwe.NumParse.Internal

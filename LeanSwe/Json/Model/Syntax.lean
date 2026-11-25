import Lean.Data.Json.Basic
import LeanSwe.Json.Model.Equiv

namespace LeanSwe.Json.Model

/-- Check whether `c` is one of the four RFC 8259 JSON whitespace characters (`' '`, `'\t'`, `'\n'`, `'\r'`). -/
def isJsonWsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Check whether every character of `s` is RFC 8259 JSON whitespace. -/
def isJsonWs (s : String) : Bool :=
  s.toList.all isJsonWsChar

/-- Independent uppercase/lowercase selection for each nibble of a 4-digit `\uXXXX` hex escape. -/
structure HexCase4 where
  /-- Select `'A'..'F'` (`true`) vs `'a'..'f'` (`false`) for bits `12..15`. -/
  u0 : Bool := false
  /-- Select `'A'..'F'` (`true`) vs `'a'..'f'` (`false`) for bits `8..11`. -/
  u1 : Bool := false
  /-- Select `'A'..'F'` (`true`) vs `'a'..'f'` (`false`) for bits `4..7`. -/
  u2 : Bool := false
  /-- Select `'A'..'F'` (`true`) vs `'a'..'f'` (`false`) for bits `0..3`. -/
  u3 : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of RFC 8259 surface representation for one Unicode scalar character in a JSON string. -/
inductive CharEscapeStyle where
  /-- Unescaped UTF-8 scalar (`U+0020..U+10FFFF` excluding `'"'` and `'\\'`). -/
  | raw
  /-- Two-character backslash escape (`\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`). -/
  | shortEscape
  /-- Four-hex-digit BMP escape `\uXXXX` (`c.toNat < 0x10000`). -/
  | unicodeHex (casing : HexCase4 := {})
  /-- Paired UTF-16 surrogate escape `\uHHHH\uLLLL` (`0x10000 ≤ c.toNat`). -/
  | surrogatePair (hiCase : HexCase4 := {}) (loCase : HexCase4 := {})
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Render a nibble `n < 16` as a hex character using `upper` for `10..15`. -/
def renderHexNibble (upper : Bool) (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)
  else if upper then Char.ofNat (0x41 + (n - 10))
  else Char.ofNat (0x61 + (n - 10))

/-- Render a 16-bit unsigned integer `u16 < 0x10000` as `['\\', 'u', d0, d1, d2, d3]`. -/
def renderHex4 (casing : HexCase4) (u16 : Nat) : List Char :=
  [ '\\', 'u'
  , renderHexNibble casing.u0 ((u16 / 4096) % 16)
  , renderHexNibble casing.u1 ((u16 / 256) % 16)
  , renderHexNibble casing.u2 ((u16 / 16) % 16)
  , renderHexNibble casing.u3 (u16 % 16) ]

/-- Render a single Unicode scalar `c` according to `style`, or `none` if `style` is invalid for `c`. -/
def renderCharWithStyle (c : Char) : CharEscapeStyle → Option (List Char)
  | .raw =>
    if 0x20 ≤ c.toNat && c != '"' && c != '\\' then some [c] else none
  | .shortEscape =>
    if c == '"' then some ['\\', '"']
    else if c == '\\' then some ['\\', '\\']
    else if c == '/' then some ['\\', '/']
    else if c == '\x08' then some ['\\', 'b']
    else if c == '\x0c' then some ['\\', 'f']
    else if c == '\n' then some ['\\', 'n']
    else if c == '\r' then some ['\\', 'r']
    else if c == '\t' then some ['\\', 't']
    else none
  | .unicodeHex casing =>
    if c.toNat < 0x10000 then some (renderHex4 casing c.toNat) else none
  | .surrogatePair hiCase loCase =>
    if 0x10000 ≤ c.toNat then
      let v := c.toNat - 0x10000
      let hi := 0xD800 + v / 1024
      let lo := 0xDC00 + v % 1024
      some (renderHex4 hiCase hi ++ renderHex4 loCase lo)
    else none

/-- Render a list of characters paired 1-to-1 with `CharEscapeStyle` instructions. -/
def renderStringChars : List Char → List CharEscapeStyle → Option (List Char)
  | [], [] => some []
  | c :: cs, st :: sts => do
    let hd ← renderCharWithStyle c st
    let tl ← renderStringChars cs sts
    some (hd ++ tl)
  | _, _ => none

/-- Render `s` as an RFC 8259 quoted JSON string literal according to `styles`. -/
def renderStringLiteral (s : String) (styles : List CharEscapeStyle) : Option String := do
  let body ← renderStringChars s.toList styles
  some ("\"" ++ String.ofList body ++ "\"")

/-- Check whether `c` is an ASCII decimal digit `'0'..'9'`. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Check whether `s` is a non-empty string of ASCII decimal digits. -/
def isNonEmptyDigits (s : String) : Bool :=
  !s.toList.isEmpty && s.toList.all isAsciiDigit

/-- Single-digit accumulation step for `parseDecDigitsLoop`. -/
def parseDecDigitStep (acc : Nat) (c : Char) : Nat :=
  acc * 10 + (c.toNat - 0x30)

/-- Accumulate the base-10 natural number value of a list of ASCII decimal digit characters. -/
def parseDecDigitsLoop (acc : Nat) (cs : List Char) : Nat :=
  cs.foldl parseDecDigitStep acc

/-- Base-case reduction for `parseDecDigitsLoop`. -/
theorem parseDecDigitsLoop_nil (acc : Nat) :
    parseDecDigitsLoop acc [] = acc := List.foldl_nil

/-- Step reduction for `parseDecDigitsLoop` avoiding `brecOn` unfolding. -/
theorem parseDecDigitsLoop_cons (acc : Nat) (c : Char) (cs : List Char) :
    parseDecDigitsLoop acc (c :: cs) = parseDecDigitsLoop (acc * 10 + (c.toNat - 0x30)) cs :=
  List.foldl_cons

/-- Parse a string of ASCII decimal digits into its exact natural number value. -/
def parseDecDigits (s : String) : Nat :=
  parseDecDigitsLoop 0 s.toList

/-- Optional sign in an RFC 8259 scientific exponent (`e10`, `e+10`, `e-10`). -/
inductive ExpSign where
  /-- Unsigned exponent (`e10`). -/
  | none
  /-- Explicit `'+'` sign (`e+10`). -/
  | plus
  /-- Explicit `'-'` sign (`e-10`). -/
  | minus
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Nondeterministic choice of RFC 8259 exponent spelling (`e`/`E`, sign, digit string). -/
structure ExpTape where
  /-- Select `'E'` (`true`) vs `'e'` (`false`). -/
  upperE : Bool := false
  /-- Sign token immediately following `'e'`/`'E'`. -/
  sign : ExpSign := .none
  /-- Non-empty ASCII digit sequence (may include leading zeros such as `"002"`). -/
  digits : String := "0"
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Nondeterministic choice of pure RFC 8259 numeric literal spelling (`-? int (. digits)? (e [+-]? digits)?`). -/
structure NumTape where
  /-- Whether a leading `'-'` sign is emitted (including `"-0"`). -/
  minus : Bool := false
  /-- Non-negative integer part (`0` emits `"0"`, `n > 0` emits canonical digits without leading zeros). -/
  whole : Nat := 0
  /-- Optional fractional digit sequence after `'.'` (non-empty ASCII digits). -/
  fracDigits : Option String := none
  /-- Optional scientific exponent suffix. -/
  exp : Option ExpTape := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Check pure RFC 8259 lexical validity of `nt` (no resource caps). -/
def validNumTape (nt : NumTape) : Bool :=
  (match nt.fracDigits with | none => true | some f => isNonEmptyDigits f) &&
  (match nt.exp with | none => true | some e => isNonEmptyDigits e.digits)

/-- Evaluate a lexically valid `NumTape` into its exact `Lean.JsonNumber` representation. -/
def evalNumTape (nt : NumTape) : Lean.JsonNumber :=
  let sign : Int := if nt.minus then -1 else 1
  let base : Lean.JsonNumber :=
    match nt.fracDigits with
    | none => Lean.JsonNumber.fromInt (sign * (nt.whole : Int))
    | some f =>
      let d := f.toList.length
      Lean.JsonNumber.mk (sign * (nt.whole * (10 ^ d) + parseDecDigits f)) d
  match nt.exp with
  | none => base
  | some e =>
    let expVal := parseDecDigits e.digits
    match e.sign with
    | .minus => base.shiftr expVal
    | .none | .plus => base.shiftl expVal

/-- Render an `ExpSign` token. -/
def renderExpSign : ExpSign → String
  | .none => ""
  | .plus => "+"
  | .minus => "-"

/-- Format the surface string of a `NumTape`. -/
def renderNumTape (nt : NumTape) : String :=
  let sgn := if nt.minus then "-" else ""
  let fracStr := match nt.fracDigits with | none => "" | some f => "." ++ f
  let expStr := match nt.exp with
    | none => ""
    | some e => (if e.upperE then "E" else "e") ++ renderExpSign e.sign ++ e.digits
  sgn ++ nt.whole.repr ++ fracStr ++ expStr

/-- Render `n : Lean.JsonNumber` using `nt` when `nt` is pure RFC 8259 valid and decimal-equivalent to `n`. -/
def renderNum (n : Lean.JsonNumber) (nt : NumTape) : Option String :=
  if validNumTape nt && numEquivBool n (evalNumTape nt) then some (renderNumTape nt)
  else none

/-- Key and surrounding whitespace instructions for one JSON object member. -/
structure ObjKeyTape where
  /-- Whitespace immediately preceding the key string literal (after `'{'` or `','`). -/
  wsBeforeKey : String := ""
  /-- Unescaped object member key. -/
  key : String := ""
  /-- Per-character escape choices for rendering `key`. -/
  keyChars : List CharEscapeStyle := []
  /-- Whitespace between the closing `'"'` of the key and `':'`. -/
  wsBeforeColon : String := ""
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Nondeterministic formatting tape for pure RFC 8259 JSON rendering. -/
inductive RenderTape where
  /-- Render `null` with surrounding JSON whitespace. -/
  | null (wsBefore : String := "") (wsAfter : String := "")
  /-- Render `true` or `false` with surrounding JSON whitespace. -/
  | bool (wsBefore : String := "") (wsAfter : String := "")
  /-- Render a JSON number using `nt` with surrounding JSON whitespace. -/
  | num (wsBefore : String := "") (nt : NumTape := {}) (wsAfter : String := "")
  /-- Render a JSON string using `chars` with surrounding JSON whitespace. -/
  | str (wsBefore : String := "") (chars : List CharEscapeStyle := []) (wsAfter : String := "")
  /-- Render an empty JSON array `[ wsInside ]` with surrounding JSON whitespace. -/
  | emptyArr (wsBefore : String := "") (wsInside : String := "") (wsAfter : String := "")
  /-- Render a non-empty JSON array `[ e0, e1, ... ]` with surrounding JSON whitespace. -/
  | arr (wsBefore : String := "") (elems : List RenderTape) (wsAfter : String := "")
  /-- Render an empty JSON object `{ wsInside }` with surrounding JSON whitespace. -/
  | emptyObj (wsBefore : String := "") (wsInside : String := "") (wsAfter : String := "")
  /-- Render a non-empty JSON object `{ k0 : v0, k1 : v1, ... }` in any permutation of its unique keys. -/
  | obj (wsBefore : String := "") (entries : List (ObjKeyTape × RenderTape)) (wsAfter : String := "")
  deriving Repr, Inhabited

/-- Verify that `plan` specifies a duplicate-free bijection over the keys of `entries`. -/
def isObjPlanPerm (entries : List (String × Lean.Json))
    (plan : List (ObjKeyTape × RenderTape)) : Bool :=
  noDupKeysBool entries &&
  noDupStringsBool (plan.map fun p => p.1.key) &&
  plan.length == entries.length &&
  plan.all (fun p => hasKeyList p.1.key entries)

mutual
  /-- Render a JSON value according to `tape` (pure RFC 8259 grammar). -/
  def renderVal (j : Lean.Json) (tape : RenderTape) : Option String :=
    match j, tape with
    | .null, .null wb wa =>
      if isJsonWs wb && isJsonWs wa then some (wb ++ "null" ++ wa) else none
    | .bool b, .bool wb wa =>
      if isJsonWs wb && isJsonWs wa then some (wb ++ (if b then "true" else "false") ++ wa) else none
    | .num n, .num wb nt wa =>
      if isJsonWs wb && isJsonWs wa then (renderNum n nt).map (fun s => wb ++ s ++ wa) else none
    | .str s, .str wb st wa =>
      if isJsonWs wb && isJsonWs wa then (renderStringLiteral s st).map (fun s' => wb ++ s' ++ wa) else none
    | .arr elems, .emptyArr wb wi wa =>
      if elems.isEmpty && isJsonWs wb && isJsonWs wi && isJsonWs wa then
        some (wb ++ "[" ++ wi ++ "]" ++ wa)
      else none
    | .arr elems, .arr wb elemTapes wa =>
      if !elems.isEmpty && isJsonWs wb && isJsonWs wa then do
        let parts ← renderArrElems elems.toList elemTapes
        some (wb ++ "[" ++ String.intercalate "," parts ++ "]" ++ wa)
      else none
    | .obj kvs, .emptyObj wb wi wa =>
      if (objEntries kvs).isEmpty && isJsonWs wb && isJsonWs wi && isJsonWs wa then
        some (wb ++ "{" ++ wi ++ "}" ++ wa)
      else none
    | .obj kvs, .obj wb entryTapes wa =>
      let entries := objEntries kvs
      if !entries.isEmpty && isJsonWs wb && isJsonWs wa && isObjPlanPerm entries entryTapes then do
        let parts ← renderObjEntries entries entryTapes
        some (wb ++ "{" ++ String.intercalate "," parts ++ "}" ++ wa)
      else none
    | _, _ => none
  termination_by sizeOf tape * 2 + 1
  decreasing_by
    all_goals simp +arith

  /-- Render array elements paired 1-to-1 with `RenderTape` instructions. -/
  def renderArrElems : List Lean.Json → List RenderTape → Option (List String)
    | [], [] => some []
    | x :: xs, tp :: tps => do
      let hd ← renderVal x tp
      let tl ← renderArrElems xs tps
      some (hd :: tl)
    | _, _ => none
  termination_by _ ts => sizeOf ts * 2 + 2
  decreasing_by
    all_goals simp +arith

  /-- Render object entries in the order specified by `entryTapes`. -/
  def renderObjEntries (entries : List (String × Lean.Json)) :
      List (ObjKeyTape × RenderTape) → Option (List String)
    | [] => some []
    | (kt, vt) :: rest =>
      if !isJsonWs kt.wsBeforeKey || !isJsonWs kt.wsBeforeColon then none
      else
        match lookupKeyList kt.key entries with
        | none => none
        | some v => do
          let rk ← renderStringLiteral kt.key kt.keyChars
          let rv ← renderVal v vt
          let tl ← renderObjEntries entries rest
          some ((kt.wsBeforeKey ++ rk ++ kt.wsBeforeColon ++ ":" ++ rv) :: tl)
  termination_by ts => sizeOf ts * 2 + 2
  decreasing_by
    all_goals simp +arith
end

/-- Strict nondeterministic pure RFC 8259 inverse-renderer specification for `Lean.Json`. -/
def render (doc : Lean.Json) (tape : RenderTape) : Option String :=
  if !wellFormedJsonBool doc then none
  else renderVal doc tape

/-- Documented runtime limit on fractional decimal digit count (`100_000`) enforced by `LeanSwe.Json.parse`. -/
def maxFracDigits : Nat := 100_000

/-- Documented symmetric runtime limit on scientific exponent magnitude (`|exp| ≤ 100_000`) enforced by `LeanSwe.Json.parse`. -/
def maxAbsExponent : Nat := 100_000

/-- Check whether `nt` satisfies the symmetric runtime fractional-digit and exponent-value bounds. -/
def numTapeWithinLimits (nt : NumTape) : Bool :=
  decide ((match nt.fracDigits with | none => 0 | some f => f.toList.length) ≤ maxFracDigits) &&
  decide ((match nt.exp with | none => 0 | some e => parseDecDigits e.digits) ≤ maxAbsExponent)

mutual
  /-- Computable check that every numeric token in `tape` respects `maxFracDigits` and `maxAbsExponent`. -/
  def withinResourceLimitsBool : RenderTape → Bool
    | .null _ _ | .bool _ _ | .str _ _ _ | .emptyArr _ _ _ | .emptyObj _ _ _ => true
    | .num _ nt _ => numTapeWithinLimits nt
    | .arr _ ts _ => withinResourceLimitsListBool ts
    | .obj _ es _ => withinResourceLimitsObjBool es
  termination_by t => sizeOf t

  /-- Computable resource-limit check across array element tapes. -/
  def withinResourceLimitsListBool : List RenderTape → Bool
    | [] => true
    | t :: ts => withinResourceLimitsBool t && withinResourceLimitsListBool ts
  termination_by ts => sizeOf ts

  /-- Computable resource-limit check across object member tapes. -/
  def withinResourceLimitsObjBool : List (ObjKeyTape × RenderTape) → Bool
    | [] => true
    | (_, t) :: es => withinResourceLimitsBool t && withinResourceLimitsObjBool es
  termination_by es => sizeOf es
end

/-- Runtime resource-limit predicate separating `Impl.parse` scanner bounds from pure RFC 8259 `render`. -/
def withinResourceLimits (tape : RenderTape) : Prop :=
  withinResourceLimitsBool tape = true

mutual
  /-- Check whether `tape` contains zero whitespace in every leading, trailing, and interior slot. -/
  def isCompactTape : RenderTape → Bool
    | .null wb wa | .bool wb wa | .num wb _ wa | .str wb _ wa => wb.isEmpty && wa.isEmpty
    | .emptyArr wb wi wa | .emptyObj wb wi wa => wb.isEmpty && wi.isEmpty && wa.isEmpty
    | .arr wb ts wa => wb.isEmpty && wa.isEmpty && isCompactListTape ts
    | .obj wb es wa => wb.isEmpty && wa.isEmpty && isCompactObjTape es
  termination_by t => sizeOf t

  /-- Check zero-whitespace compactness across array element tapes. -/
  def isCompactListTape : List RenderTape → Bool
    | [] => true
    | t :: ts => isCompactTape t && isCompactListTape ts
  termination_by ts => sizeOf ts

  /-- Check zero-whitespace compactness across object member tapes. -/
  def isCompactObjTape : List (ObjKeyTape × RenderTape) → Bool
    | [] => true
    | (kt, vt) :: es =>
      kt.wsBeforeKey.isEmpty && kt.wsBeforeColon.isEmpty && isCompactTape vt && isCompactObjTape es
  termination_by es => sizeOf es
end

/-- Count base-10 digits of `n` (`modelCountDigits 0 = 1`) for canonical number formatting. -/
def modelCountDigitsAux (n digits : Nat) : Nat :=
  if h : n ≤ 9 then digits
  else
    have : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
    modelCountDigitsAux (n / 10) (digits + 1)
termination_by n

/-- Canonical RFC 8259 decimal string of a `Lean.JsonNumber`. -/
def canonicalNumString : Lean.JsonNumber → String
  | ⟨0, _⟩ => "0"
  | ⟨m, 0⟩ => (if m < 0 then "-" else "") ++ m.natAbs.repr
  | ⟨m, e⟩ =>
    let sign := if m < 0 then "-" else ""
    let mAbs := m.natAbs
    let exp : Int := 9 + modelCountDigitsAux mAbs 1 - (e : Int)
    let exp := if exp < 0 then exp else 0
    let k := e - exp.natAbs
    let e' := 10 ^ k
    let left := (mAbs / e').repr
    let rem := mAbs % e'
    if rem == 0 && exp == 0 then sign ++ left
    else
      let raw := Nat.toDigits 10 rem
      let right := String.ofList (((List.replicate (k - raw.length) '0' ++ raw).reverse.dropWhile (· == '0')).reverse)
      let expStr := if exp == 0 then "" else "e-" ++ exp.natAbs.repr
      sign ++ left ++ "." ++ right ++ expStr

/-- Canonical escape sequence for a single `Char` in compact/pretty JSON output. -/
def canonicalEscapeChar (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\r' then ['\\', 'r']
  else if 0x0020 ≤ c.toNat then [c]
  else
    let n := c.toNat
    [ '\\', 'u'
    , renderHexNibble false (n / 4096)
    , renderHexNibble false ((n % 4096) / 256)
    , renderHexNibble false ((n % 256) / 16)
    , renderHexNibble false (n % 16) ]

/-- Canonical quoted JSON string literal for `s`. -/
def canonicalStringLit (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap canonicalEscapeChar) ++ "\""

mutual
  /-- Single-line spaced rendering of `j` (emitted by `pretty j lineWidth` whenever it fits in `lineWidth`). -/
  def flatPretty : Lean.Json → String
    | .null => "null"
    | .bool true => "true"
    | .bool false => "false"
    | .num n => canonicalNumString n
    | .str s => canonicalStringLit s
    | .arr elems =>
      match elems.toList with
      | [] => "[]"
      | _ => "[" ++ String.intercalate ", " (flatPrettyList elems.toList) ++ "]"
    | .obj kvs =>
      match objEntries kvs with
      | [] => "{}"
      | _ => "{" ++ String.intercalate ", " (flatPrettyTree kvs.inner.inner) ++ "}"
  termination_by j => sizeOf j
  decreasing_by
    · cases elems; simp +arith
    · cases kvs with | mk inner => cases inner; simp +arith

  /-- Single-line spaced rendering of array elements. -/
  def flatPrettyList : List Lean.Json → List String
    | [] => []
    | x :: xs => flatPretty x :: flatPrettyList xs
  termination_by xs => sizeOf xs

  /-- Single-line spaced rendering of `Std.DTreeMap` entries in in-order traversal. -/
  def flatPrettyTree : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → List String
    | .leaf => []
    | .inner _ k v l r =>
      flatPrettyTree l ++ (canonicalStringLit k ++ ": " ++ flatPretty v) :: flatPrettyTree r
  termination_by t => sizeOf t
end

end LeanSwe.Json.Model

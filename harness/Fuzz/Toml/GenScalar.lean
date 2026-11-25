import Fuzz.Common.Rng
import LeanSwe.Toml.Interface
import LeanSwe.Toml.Model
import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.Model

namespace Fuzz.Toml

open Fuzz.Common
open LeanSwe.Toml

/-- One differential fuzz case for `Fuzz.Toml.suite`. -/
inductive TomlFuzzCase where
  /-- Valid TOML 1.0 document rendered from `doc` with accurately attributed syntax/feature tags. -/
  | validRender (doc : TomlTable) (raw : String) (tags : List String)
  /-- Arbitrary or syntactically/semantically malformed UTF-8 TOML string candidate. -/
  | malformedStr (raw : String) (tag : String)
  /-- TOML document containing an integer outside `Int64` bounds (`strictValidToml` means valid for `tomllib`). -/
  | int64Overflow (raw : String) (strictValidToml : Bool)
  /-- Combined `encode`/`decode`/`getTable`/`getArray`/`getField`/`getOptField`/`getPath` check. -/
  | codecAndAccessors (doc : TomlTable) (primBool : Bool) (primInt64 : Int64) (primFloat : Float)
      (primStr : String) (odt : TomlOffsetDateTime) (ldt : Std.Time.PlainDateTime)
      (ld : Std.Time.PlainDate) (lt : Std.Time.PlainTime) (arrVals : Array Int64)
      (key1 key2 : String) (pathKeys : List String)
  deriving BEq, Inhabited

private def truncPreview (s : String) (lim : Nat := 48) : String :=
  let cs := s.toList
  if cs.length ≤ lim then reprStr s
  else reprStr (String.ofList (cs.take lim) ++ "...")

/-- Concise human-readable formatting for shrunk `TomlFuzzCase` counterexamples. -/
def reprTomlFuzzCase : TomlFuzzCase → String
  | .validRender doc raw tags =>
    s!"validRender(doc={truncPreview (LeanSwe.Toml.format doc)}, raw={truncPreview raw}, tags={reprStr tags})"
  | .malformedStr raw tag =>
    s!"malformedStr(tag={reprStr tag}, raw={truncPreview raw})"
  | .int64Overflow raw strict =>
    s!"int64Overflow(strict={strict}, raw={truncPreview raw})"
  | .codecAndAccessors doc b i f s _ _ _ _ xs k1 k2 pks =>
    s!"codecAndAccessors(doc={truncPreview (LeanSwe.Toml.format doc)}, b={b}, i={i}, f={f}, s={truncPreview s}, xs={reprStr xs}, k1={reprStr k1}, k2={reprStr k2}, path={reprStr pks})"

instance : Repr TomlFuzzCase where
  reprPrec c _ := reprTomlFuzzCase c

/-- Generate optional TOML 1.0 horizontal whitespace (`' '` and `'\t'`). -/
def genHorizWs (r : Rng) (maxLen : Nat := 3) : String × Rng := Id.run do
  let (useWs, r0) := r.chance 2 5
  if !useWs then return ("", r0)
  let (len, r1) := r0.nextRange 1 maxLen
  let mut cur := r1
  let mut cs : List Char := []
  for _ in [0 : len] do
    let (isTab, rn) := cur.chance 1 4
    cur := rn
    cs := (if isTab then '\t' else ' ') :: cs
  return (String.ofList cs.reverse, cur)

/-- Generate an optional trailing horizontal-whitespace and `# comment` suffix. -/
def genLineSuffix (r : Rng) : Model.LineSuffixTape × List String × Rng :=
  let (ws, r1) := genHorizWs r 2
  let (hasCmt, r2) := r1.chance 1 4
  if !hasCmt then
    ({ ws := ws, comment := none }, [], r2)
  else
    let pool : Array String := #[" note", " toml 1.0", "", "\tαΩ🚀", " trailing # hash"]
    let (cmt, r3) := r2.choose pool " note"
    ({ ws := ws, comment := some cmt }, ["comments_blank_lines"], r3)

/-- Generate valid multiline closed trivia (whitespace, blank lines, and `#...\n` comments). -/
def genClosedTrivia (r : Rng) : String × List String × Rng :=
  let (pick, r1) := r.nextNat 8
  if pick < 5 then
    ("", [], r1)
  else if pick == 5 then
    ("\n", ["comments_blank_lines"], r1)
  else if pick == 6 then
    ("  \n# blank and comment\n\t", ["comments_blank_lines"], r1)
  else
    ("# section lead\n", ["comments_blank_lines"], r1)

private def hexCharMixed (upper : Bool) (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ((if upper then 'A'.toNat else 'a'.toNat) + (n - 10))

private def makeUnicode4Atom (code : Nat) (upper : Bool) : Model.BasicEscapeAtom :=
  let h1 := hexCharMixed upper ((code >>> 12) &&& 0xf)
  let h2 := hexCharMixed upper ((code >>> 8) &&& 0xf)
  let h3 := hexCharMixed upper ((code >>> 4) &&& 0xf)
  let h4 := hexCharMixed upper (code &&& 0xf)
  .unicode4 h1 h2 h3 h4

private def makeUnicode8Atom (code : Nat) (upper : Bool) : Model.BasicEscapeAtom :=
  let h1 := hexCharMixed upper ((code >>> 28) &&& 0xf)
  let h2 := hexCharMixed upper ((code >>> 24) &&& 0xf)
  let h3 := hexCharMixed upper ((code >>> 20) &&& 0xf)
  let h4 := hexCharMixed upper ((code >>> 16) &&& 0xf)
  let h5 := hexCharMixed upper ((code >>> 12) &&& 0xf)
  let h6 := hexCharMixed upper ((code >>> 8) &&& 0xf)
  let h7 := hexCharMixed upper ((code >>> 4) &&& 0xf)
  let h8 := hexCharMixed upper (code &&& 0xf)
  .unicode8 h1 h2 h3 h4 h5 h6 h7 h8

private def genValidChar (r : Rng) : Char × Rng :=
  let (sel, r1) := r.nextNat 10
  if sel < 5 then
    let (code, r2) := r1.nextRange 0x20 0x7e
    (Char.ofNat code, r2)
  else if sel < 7 then
    let specials : Array Char := #['"', '\'', '\\', '\x08', '\t', '\n', '\x0c', '\r', '\x00', '\x1f', '\x7f']
    r1.choose specials 'a'
  else if sel < 9 then
    let bmp : Array Nat := #[0x00a9, 0x00e9, 0x03b1, 0x03a9, 0x20ac, 0x4e2d]
    let (cp, r2) := r1.choose bmp 0x03b1
    (Char.ofNat cp, r2)
  else
    let astral : Array Nat := #[0x10000, 0x1f600, 0x1f680, 0x10ffff]
    let (cp, r2) := r1.choose astral 0x1f680
    (Char.ofNat cp, r2)

private def genAtomForBasicChar (c : Char) (r : Rng) : Model.BasicCharAtom × Bool × Rng :=
  let code := c.toNat
  let (upper, r1) := r.nextBool
  if c == '\x08' then (.escape .backspace, true, r1)
  else if c == '\x0c' then (.escape .formfeed, true, r1)
  else if c == '\n' then (.escape .linefeed, true, r1)
  else if c == '\r' then (.escape .carriageReturn, true, r1)
  else if c == '"' then (.escape .quote, true, r1)
  else if c == '\\' then (.escape .backslash, true, r1)
  else if c == '\t' then
    let (escTab, r2) := r1.nextBool
    if escTab then (.escape .tab, true, r2) else (.plain, false, r2)
  else if Model.isDisallowedControl c then
    (.escape (makeUnicode4Atom code upper), true, r1)
  else if code ≥ 0x10000 then
    let (useU8, r2) := r1.nextBool
    if useU8 then (.escape (makeUnicode8Atom code upper), true, r2) else (.plain, false, r2)
  else
    let (useHex, r2) := r1.chance 1 6
    if useHex then
      let (asU8, r3) := r2.chance 1 3
      let esc := if asU8 then makeUnicode8Atom code upper else makeUnicode4Atom code upper
      (.escape esc, true, r3)
    else (.plain, false, r2)

private def hasCanonicalBasicEscape (s : String) : Bool :=
  s.toList.any fun c =>
    c == '\\' || c == '"' || c == '\x08' || c == '\t' || c == '\n' ||
      c == '\x0c' || c == '\r' || Model.isDisallowedControl c

/-- Generate a TOML key string paired with a valid `Model.KeyStyle` and exact feature tags. -/
def genKeyAndStyle (r : Rng) : String × Model.KeyStyle × List String × Rng := Id.run do
  let (kind, r1) := r.nextNat 10
  if kind < 5 then
    let barePool : Array String := #["a", "key_1", "sub-2", "1234", "007", "1979-05-27", "true", "_x"]
    let (k, r2) := r1.choose barePool "k"
    return (k, .bare, ["key_bare"], r2)
  else if kind < 8 then
    let (len, r2) := r1.nextRange 0 6
    let mut cur := r2
    let mut cs : List Char := []
    let mut atoms : List Model.BasicCharAtom := []
    let mut usedEsc := false
    for _ in [0 : len] do
      let (ch, ra) := genValidChar cur
      let (atm, esc, rb) := genAtomForBasicChar ch ra
      cur := rb
      cs := ch :: cs
      atoms := atm :: atoms
      if esc then usedEsc := true
    let k := String.ofList cs.reverse
    let style : Model.KeyStyle := .basic (some atoms.reverse)
    let escTag := if usedEsc then ["str_escape"] else []
    match Model.renderKey k style with
    | some _ => return (k, style, "key_basic" :: escTag, cur)
    | none =>
      let fbEsc := if hasCanonicalBasicEscape k then ["str_escape"] else []
      return (k, .basic none, "key_basic" :: fbEsc, cur)
  else
    let litPool : Array String := #["", "a.b", "lit key", "C:\\dir\\k", "127.0.0.1", "quote\"ok"]
    let (k, r2) := r1.choose litPool "a.b"
    match Model.renderKey k .literal with
    | some _ => return (k, .literal, ["key_literal"], r2)
    | none => return (k, .basic none, ["key_basic"], r2)

/-- Generate a TOML string value paired with a valid `Model.StringStyle` and exact feature tags. -/
def genStringAndStyle (r : Rng) : String × Model.StringStyle × List String × Rng := Id.run do
  let (mode, r1) := r.nextNat 12
  if mode < 5 then
    let (len, r2) := r1.nextRange 0 10
    let mut cur := r2
    let mut cs : List Char := []
    let mut atoms : List Model.BasicCharAtom := []
    let mut usedEsc := false
    for _ in [0 : len] do
      let (ch, ra) := genValidChar cur
      let (atm, esc, rb) := genAtomForBasicChar ch ra
      cur := rb
      cs := ch :: cs
      atoms := atm :: atoms
      if esc then usedEsc := true
    let s := String.ofList cs.reverse
    let st := Model.StringStyle.basic (some atoms.reverse)
    let escTag := if usedEsc then ["str_escape"] else []
    match Model.renderStringLiteral s st with
    | some _ => return (s, st, "str_basic" :: escTag, cur)
    | none =>
      let fbEsc := if hasCanonicalBasicEscape s then ["str_escape"] else []
      return (s, .basic none, "str_basic" :: fbEsc, cur)
  else if mode < 7 then
    let litPool : Array String := #["", "raw\\path\\x", "hello \"world\"", "no\\nescape", "αΩ🚀"]
    let (s, r2) := r1.choose litPool "raw\\path"
    match Model.renderStringLiteral s .literal with
    | some _ => return (s, .literal, ["str_literal"], r2)
    | none => return (s, .basic none, ["str_basic"], r2)
  else if mode < 10 then
    let (useTrim, r2) := r1.nextBool
    if useTrim then
      let (w1, r3) := r2.choose #["", " ", "\t "] " "
      let (w2, r4) := r3.choose #["", "  ", "\n  \t"] "  "
      let (s, r5) := r4.choose #["alphaBeta", "line1\nnext", "x\"y"] "alphaBeta"
      match s.toList with
      | _ :: _ :: rest =>
        let atoms : List Model.MultilineBasicAtom :=
          [.plain, .lineTrim w1 w2, .plain] ++ rest.map (fun _ => Model.MultilineBasicAtom.plain)
        let (leadNl, r6) := r5.nextBool
        let st := Model.StringStyle.multilineBasic (some (leadNl, atoms))
        match Model.renderStringLiteral s st with
        | some _ => return (s, st, ["str_multiline_basic", "str_line_trim"], r6)
        | none => return (s, .multilineBasic none, ["str_multiline_basic"], r6)
      | _ => return (s, .multilineBasic none, ["str_multiline_basic"], r5)
    else
      let mlPool : Array String := #["", "line1\nline2", "\"quoted\"", "two\"\"quotes", "\nleading"]
      let (s, r3) := r2.choose mlPool "line1\nline2"
      let escTag := if s.toList.any (fun c => c == '\\' || c == '"') then ["str_escape"] else []
      return (s, .multilineBasic none, "str_multiline_basic" :: escTag, r3)
  else
    let mllPool : Array String := #["", "raw\nline2", "one'quote'two''quotes", "C:\\a\\b\nc"]
    let (s, r2) := r1.choose mllPool "raw\nline2"
    let (leadNl, r3) := r2.nextBool
    let st := Model.StringStyle.multilineLiteral leadNl
    match Model.renderStringLiteral s st with
    | some _ => return (s, st, ["str_multiline_literal"], r3)
    | none =>
      let st2 := Model.StringStyle.multilineLiteral true
      match Model.renderStringLiteral s st2 with
      | some _ => return (s, st2, ["str_multiline_literal"], r3)
      | none => return (s, .basic none, ["str_basic"], r3)

private def insertUnderscores (digits : String) (r : Rng) : String × Bool × Rng := Id.run do
  let cs := digits.toList
  if cs.length < 2 then return (digits, false, r)
  let (doUnder, r0) := r.chance 1 2
  if !doUnder then return (digits, false, r0)
  let mut cur := r0
  let mut acc : List Char := [cs.head!]
  let mut used := false
  for ch in cs.tail! do
    let (putU, rn) := cur.chance 1 2
    cur := rn
    if putU then
      acc := ch :: '_' :: acc
      used := true
    else
      acc := ch :: acc
  return (String.ofList acc.reverse, used, cur)

private def natToRadixDigits (radix : Nat) (upper : Bool) (n : Nat) : String := Id.run do
  if n == 0 then return "0"
  let mut v := n
  let mut cs : List Char := []
  let mut fuel := 70
  while v > 0 && fuel > 0 do
    cs := hexCharMixed upper (v % radix) :: cs
    v := v / radix
    fuel := fuel - 1
  return String.ofList cs

/-- Generate a signed `Int64` value with a valid `Model.ValueTape` and exact integer tags. -/
def genIntAndTape (r : Rng) : Int64 × Model.ValueTape × List String × Rng := Id.run do
  let (kind, r1) := r.nextNat 12
  if kind == 0 then
    let specials : Array Int64 := #[0, -1, 1, -9223372036854775808, 9223372036854775807]
    let (n, r2) := r1.choose specials 0
    return (n, .int none, ["int_dec"], r2)
  else if kind < 6 then
    let (iv, r2) := r1.nextIntRange (-1000000000) 1000000000
    let n := Int64.ofInt iv
    let magStr := toString iv.natAbs
    let (uStr, usedU, r3) := insertUnderscores magStr r2
    let (plusSign, r4) := r3.chance 1 3
    let signPfx := if iv < 0 then "-" else if plusSign then "+" else ""
    let lex := signPfx ++ uStr
    let uTag := if usedU then ["int_underscore"] else []
    if Model.isValidIntLex lex n then
      return (n, .int (some lex), "int_dec" :: uTag, r4)
    else
      return (n, .int none, ["int_dec"], r4)
  else
    let (mag, r2) := r1.nextRange 0 0x7fffffff
    let n := Int64.ofInt (Int.ofNat mag)
    let (baseSel, r3) := r2.nextNat 3
    let (upper, r4) := r3.nextBool
    let (radix, pfx, baseTag) :=
      if baseSel == 0 then (16, "0x", "int_hex")
      else if baseSel == 1 then (8, "0o", "int_oct")
      else (2, "0b", "int_bin")
    let rawDigits := natToRadixDigits radix (baseSel == 0 && upper) mag
    let (leadZeros, r5) := r4.nextRange 0 2
    let padded := String.ofList (List.replicate leadZeros '0') ++ rawDigits
    let (uStr, usedU, r6) := insertUnderscores padded r5
    let lex := pfx ++ uStr
    let uTag := if usedU then ["int_underscore"] else []
    if Model.isValidIntLex lex n then
      return (n, .int (some lex), baseTag :: uTag, r6)
    else
      return (n, .int none, ["int_dec"], r6)

/-- Generate an IEEE-754 `Float` with a valid `Model.ValueTape` and exact float tags. -/
def genFloatAndTape (r : Rng) : Float × Model.ValueTape × List String × Rng :=
  let (kind, r1) := r.nextNat 10
  if kind < 2 then
    let specPool : Array (Float × String) := #[
      (Float.inf, "inf"), (Float.inf, "+inf"), (-Float.inf, "-inf"),
      (Float.nan, "nan"), (Float.nan, "+nan"), (Float.nan, "-nan")
    ]
    let ((f, lex), r2) := r1.choose specPool (Float.nan, "nan")
    (f, .float (some lex), ["float_special"], r2)
  else if kind < 6 then
    let (neg, r2) := r1.nextBool
    let (plusSign, r3) := r2.chance 1 3
    let (whole, r4) := r3.nextRange 0 9999
    let (fracN, r5) := r4.nextRange 0 99999
    let (uFrac, _, r6) := insertUnderscores (toString fracN) r5
    let sgn := if neg then "-" else if plusSign then "+" else ""
    let lex := sgn ++ toString whole ++ "." ++ uFrac
    match LeanSwe.NumParse.Model.parseFloatModel lex with
    | .ok f =>
      if Model.isValidFloatLex lex f then (f, .float (some lex), ["float_frac"], r6)
      else (0.0, .float none, ["float_frac"], r6)
    | .error _ => (0.0, .float none, ["float_frac"], r6)
  else
    let (neg, r2) := r1.nextBool
    let (whole, r3) := r2.nextRange 0 999
    let (hasFrac, r4) := r3.nextBool
    let (fracPart, fTags, r5) :=
      if hasFrac then
        let (fn, rn) := r4.nextRange 0 999
        ("." ++ toString fn, ["float_frac", "float_exp"], rn)
      else ("", ["float_exp"], r4)
    let (upperE, r6) := r5.nextBool
    let (expSgn, r7) := r6.choose #["", "+", "-"] ""
    let (expVal, r8) := r7.choose #[0, 1, 6, 22, 34, 308, 400] 6
    let (lz, r9) := r8.nextRange 0 2
    let expDigits := String.ofList (List.replicate lz '0') ++ toString expVal
    let lex := (if neg then "-" else "") ++ toString whole ++ fracPart ++
      (if upperE then "E" else "e") ++ expSgn ++ expDigits
    match LeanSwe.NumParse.Model.parseFloatModel lex with
    | .ok f =>
      if Model.isValidFloatLex lex f then (f, .float (some lex), fTags, r9)
      else (1.0, .float (some "1.0"), ["float_frac"], r9)
    | .error _ => (1.0, .float (some "1.0"), ["float_frac"], r9)

/-- Generate a valid RFC 3339 `Std.Time.PlainDate` (`year == 0` allowed iff `allowYearZero`). -/
def genValidDate (allowYearZero : Bool) (r : Rng) : Std.Time.PlainDate × Rng :=
  let fallback := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 1979) 5 27
  let (useSpecial, r1) := r.chance 1 3
  let (yNat, mNat, dNat, r2) :=
    if useSpecial then
      let pool : Array (Nat × Nat × Nat) :=
        if allowYearZero then
          #[(0, 1, 1), (0, 2, 29), (0, 12, 31), (2000, 2, 29), (2024, 2, 29), (9999, 12, 31)]
        else
          #[(1, 1, 1), (1979, 5, 27), (2000, 2, 29), (2024, 2, 29), (9999, 12, 31)]
      let ((y, m, d), rn) := r1.choose pool (1979, 5, 27)
      (y, m, d, rn)
    else
      let loY := if allowYearZero then 0 else 1
      let (y, ra) := r1.nextRange loY 9999
      let (m, rb) := ra.nextRange 1 12
      let (d, rc) := rb.nextRange 1 28
      (y, m, d, rc)
  if hm : mNat ≥ 1 ∧ mNat ≤ 12 then
    if hd : dNat ≥ 1 ∧ dNat ≤ 31 then
      match Std.Time.PlainDate.ofYearMonthDay?
          (Std.Time.Year.Offset.ofInt (Int.ofNat yNat))
          (Std.Time.Month.Ordinal.ofNat mNat hm)
          (Std.Time.Day.Ordinal.ofNat dNat hd) with
      | some dt => (dt, r2)
      | none => (fallback, r2)
    else (fallback, r2)
  else (fallback, r2)

/-- Generate a valid TOML 1.0 `Std.Time.PlainTime` paired with an optional fractional digit lexeme. -/
def genValidTimeAndFrac (r : Rng) : Std.Time.PlainTime × Option String × Rng :=
  let (hh, r1) := r.nextRange 0 23
  let (mm, r2) := r1.nextRange 0 59
  let (ss, r3) := r2.nextRange 0 59
  let (fracKind, r4) := r3.nextNat 5
  let (ns, fracLex, r5) :=
    if fracKind < 2 then (0, none, r4)
    else if fracKind == 2 then
      let (zeros, rn) := r4.choose #["0", "000", "000000"] "0"
      (0, some zeros, rn)
    else if fracKind == 3 then
      let (us, rn) := r4.nextRange 1 999999
      let ds := Model.padNatZero 6 us
      (us * 1000, some ds, rn)
    else
      let (rawNs, ra) := r4.nextRange 1 999999999
      let (extraTail, rb) := ra.choose #["", "7", "429"] ""
      let ds := Model.padNatZero 9 rawNs ++ extraTail
      (rawNs, some ds, rb)
  let clNano := min 999999999 ns
  if hh_ok : hh ≤ 23 then
    if mm_ok : mm ≤ 59 then
      if ss_ok : ss ≤ 59 then
        let tm := Std.Time.PlainTime.mk
          (Std.Time.Hour.Ordinal.ofNat hh hh_ok)
          (Std.Time.Minute.Ordinal.ofNat mm mm_ok)
          (Std.Time.Second.Ordinal.ofNat ss (Nat.le_trans ss_ok (by decide)))
          (Std.Time.Nanosecond.Ordinal.ofNat clNano (Nat.min_le_left _ _))
        (tm, fracLex, r5)
      else (default, none, r5)
    else (default, none, r5)
  else (default, none, r5)

/-- Generate a valid RFC 3339 minute-granularity `Std.Time.TimeZone.Offset`. -/
def genValidOffset (r : Rng) : Std.Time.TimeZone.Offset × Model.OffsetStyle × Rng :=
  let (isUtc, r1) := r.chance 2 5
  let (st, r2) := r1.choose #[Model.OffsetStyle.upperZ, .lowerZ, .numeric, .negZero] .upperZ
  if isUtc then
    (Std.Time.TimeZone.Offset.ofSeconds 0, st, r2)
  else
    let (mins, r3) := r2.nextIntRange (-1439) 1439
    (Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt (mins * 60)), st, r3)

/-- Generate an RFC 3339 `TomlValue` paired with a valid `Model.ValueTape` and exact datetime tags. -/
def genDateTimeAndTape (allowYearZero : Bool) (r : Rng) :
    TomlValue × Model.ValueTape × List String × Rng :=
  let (kind, r1) := r.nextNat 4
  let (sep, r2) := r1.choose #[Model.DateTimeSep.upperT, .lowerT, .space] .upperT
  if kind == 0 then
    let (d, r3) := genValidDate allowYearZero r2
    let (t, frac?, r4) := genValidTimeAndFrac r3
    let (off, oStyle, r5) := genValidOffset r4
    let yTag := if d.year == 0 then ["year_zero"] else []
    let fTag := if frac?.isSome then ["datetime_frac"] else []
    (.offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d t, offset := off },
      .offsetDateTime sep oStyle frac?, "offset_datetime" :: (fTag ++ yTag), r5)
  else if kind == 1 then
    let (d, r3) := genValidDate allowYearZero r2
    let (t, frac?, r4) := genValidTimeAndFrac r3
    let yTag := if d.year == 0 then ["year_zero"] else []
    let fTag := if frac?.isSome then ["datetime_frac"] else []
    (.localDateTime (Std.Time.PlainDateTime.mk d t),
      .localDateTime sep frac?, "local_datetime" :: (fTag ++ yTag), r4)
  else if kind == 2 then
    let (d, r3) := genValidDate allowYearZero r2
    let yTag := if d.year == 0 then ["year_zero"] else []
    (.localDate d, .localDate, "local_date" :: yTag, r3)
  else
    let (t, frac?, r3) := genValidTimeAndFrac r2
    let fTag := if frac?.isSome then ["datetime_frac"] else []
    (.localTime t, .localTime frac?, "local_time" :: fTag, r3)

end Fuzz.Toml

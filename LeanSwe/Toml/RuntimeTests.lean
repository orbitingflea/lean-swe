import Core.Assumptions
import LeanSwe.Toml.Interface

namespace LeanSwe.Toml.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except TomlError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} [Repr α]
    (res : Except TomlError α) (expectedKind : TomlErrorKind) (msg : String) : IO Unit := do
  match res with
  | .ok v => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expectedKind}, got {repr v})")
  | .error e =>
    if e.kind != expectedKind || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expectedKind})")

private def runPython3 (script : String) (stdinData : String) : IO String := do
  let out ← IO.Process.output
    { cmd := "python3"
    , args := #["-c", script]
    }
    (some stdinData)
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 failed (exit={out.exitCode}): {out.stderr}")
  return out.stdout

private def hexByte (b : UInt8) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))
  String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

private def encodeHexUtf8 (s : String) : String :=
  String.join (s.toUTF8.toList.map hexByte)

private def padZero (w n : Nat) : String :=
  let s := toString n
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) '0') ++ s

private def fmtTimeIso (t : Std.Time.PlainTime) : String :=
  let base := padZero 2 t.hour.val.toNat ++ ":" ++ padZero 2 t.minute.val.toNat ++ ":" ++ padZero 2 t.second.val.toNat
  let ns := t.nanosecond.val.toNat
  if ns == 0 then base else base ++ "." ++ padZero 9 ns

private def fmtDateIso (d : Std.Time.PlainDate) : String :=
  padZero 4 d.year.toNat ++ "-" ++ padZero 2 d.month.val.toNat ++ "-" ++ padZero 2 d.day.val.toNat

private def fmtOffsetIso (o : Std.Time.TimeZone.Offset) : String :=
  if o.second.val == 0 then "+00:00"
  else
    let sign := if o.second.val < 0 then "-" else "+"
    let absMin := o.second.val.natAbs / 60
    sign ++ padZero 2 (absMin / 60) ++ ":" ++ padZero 2 (absMin % 60)

private theorem sizeOf_toList_lt {α : Type} [SizeOf α] (xs : Array α) : sizeOf xs.toList < sizeOf xs := by
  cases xs
  simp +arith

mutual
  private def canonicalizeValue : TomlValue → String
    | .string s => "S:" ++ encodeHexUtf8 s
    | .int n => "I:" ++ toString n.toInt
    | .float f => if f.isNaN then "F:nan" else "F:" ++ toString f.toBits.toNat
    | .bool b => if b then "B:true" else "B:false"
    | .offsetDateTime odt =>
      "ODT:" ++ fmtDateIso odt.dateTime.date ++ "T" ++ fmtTimeIso odt.dateTime.time ++ fmtOffsetIso odt.offset
    | .localDateTime dt =>
      "LDT:" ++ fmtDateIso dt.date ++ "T" ++ fmtTimeIso dt.time
    | .localDate d => "LD:" ++ fmtDateIso d
    | .localTime t => "LT:" ++ fmtTimeIso t
    | .array xs =>
      "[" ++ String.intercalate "," (canonicalizeArray xs.toList) ++ "]"
    | .table t =>
      let pairs := canonicalizeEntries t.toList
      let sorted := pairs.mergeSort (fun a b => a.1 < b.1)
      "{" ++ String.intercalate "," (sorted.map Prod.snd) ++ "}"
  termination_by v => sizeOf v
  decreasing_by
    · exact Nat.lt_trans (sizeOf_toList_lt _) (by simp +arith)
    · exact Nat.lt_trans (sizeOf_toList_lt _) (by simp +arith)

  private def canonicalizeArray : List TomlValue → List String
    | [] => []
    | v :: rest => canonicalizeValue v :: canonicalizeArray rest
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith

  private def canonicalizeEntries : List (String × TomlValue) → List (String × String)
    | [] => []
    | (k, v) :: rest => (k, encodeHexUtf8 k ++ "=" ++ canonicalizeValue v) :: canonicalizeEntries rest
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp +arith
end

private def canonicalizeTable (t : TomlTable) : String :=
  canonicalizeValue (.table t)

private def jsonEscape (s : String) : String :=
  let escChar (c : Char) : String :=
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat < 32 then
      let n := c.toNat
      let h (k : Nat) : Char :=
        if k < 10 then Char.ofNat ('0'.toNat + k) else Char.ofNat ('a'.toNat + (k - 10))
      "\\u00" ++ String.ofList [h (n / 16), h (n % 16)]
    else String.singleton c
  "\"" ++ String.join (s.toList.map escChar) ++ "\""

private def validDifferentialDocs : List (String × String) :=
  [ ("empty", "")
  , ("comments_and_crlf", "# lead\r\na = 1 # tail\r\nb = true\r\n")
  , ("keys_and_dotted",
      "bare_key-1 = 1\n\"quoted key\" = 2\n'literal.key' = 3\na.b.c = \"deep\"\n1234 = 9\n")
  , ("strings_and_escapes",
      "basic = \"hi\\b\\t\\n\\f\\r\\\"\\\\\\u0041\\U0001F600\"\n" ++
      "lit = 'C:\\Users\\test'\n" ++
      "mlb = \"\"\"\nline1\\\n   line2\"\"\"\n" ++
      "ml_quotes = \"\"\"\"hello\"\"\"\"\"\n" ++
      "mll = '''\nraw\\nline'''\n" ++
      "mll_quotes = '''''raw'''''\n")
  , ("integers_and_floats",
      "dec = +1_000\nneg = -42\nhex = 0xdead_BEEF\noct = 0o7_5_5\nbin = 0b1010_0101\n" ++
      "imin = -9223372036854775808\nimax = 9223372036854775807\n" ++
      "f1 = +1.0\nf2 = -0.0\nf3 = 5e+22\nf4 = 1e06\nf5 = -2E-2\nf6 = 6.626e-34\n" ++
      "finf = inf\nfninf = -inf\nfpinf = +inf\nfnan = nan\nfpnan = +nan\nfnnan = -nan\n")
  , ("datetimes",
      "odt1 = 1979-05-27T07:32:00Z\n" ++
      "odt2 = 1979-05-27 00:32:00.123456-07:00\n" ++
      "odt3 = 1979-05-27t07:32:00z\n" ++
      "ldt = 1979-05-27T07:32:00.5\n" ++
      "ld = 1979-05-27\n" ++
      "lt = 07:32:00.0001\n" ++
      "leap = 2000-02-29\n")
  , ("arrays_and_inline_tables",
      "arr = [1, 2, 3, ]\n" ++
      "nested = [[1, 2], [\"a\", \"b\"], ]\n" ++
      "inl = { x = 1, y.z = \"ok\", sub = { p = true } }\n")
  , ("tables_and_super_tables",
      "[a.b]\nx = 1\n[a]\ny = 2\n[a.c]\nz = 3\n")
  , ("array_of_tables",
      "[[products]]\nname = \"Hammer\"\nsku = 738594937\n\n" ++
      "[[products]]\n\n" ++
      "[[products]]\nname = \"Nail\"\nsku = 284758393\n\n" ++
      "[[fruits]]\nname = \"apple\"\n[fruits.physical]\ncolor = \"red\"\n" ++
      "[[fruits.varieties]]\nname = \"red delicious\"\n" ++
      "[[fruits.varieties]]\nname = \"granny smith\"\n")
  , ("no_trailing_newline", "a = 1")
  , ("interleaved_sections_and_crlf",
      "\r\n# header comment\r\n[a]\r\nx = 1\r\n\r\n# second section\r\n[b]\r\ny = 2\r\n[a.sub]\r\nz = 3")
  , ("inline_dotted_neg_zero_and_ml_no_nl",
      "inl = { a.b = 1 , a.c = 2 }\n" ++
      "odt = 1979-05-27T07:32:00-00:00\n" ++
      "mlb = \"\"\"hello\"\"\"\n" ++
      "mll = '''world'''")
  ]

private def invalidDifferentialDocs : List (String × String × TomlErrorKind) :=
  [ ("duplicate_key", "a = 1\na = 2\n", .duplicateKey)
  , ("redefine_table", "[a]\nb = 1\n[a]\nc = 2\n", .redefinedTable)
  , ("inline_table_reopen", "a = { b = 1 }\n[a]\nc = 2\n", .immutableInlineTable)
  , ("inline_table_subtable", "a = { b = 1 }\n[a.c]\nd = 2\n", .immutableInlineTable)
  , ("dotted_reopen_header", "[a]\nb.c = 1\n[a.b]\nd = 2\n", .redefinedTable)
  , ("static_overwrite_aot", "[[a]]\nb = 1\n[a]\nc = 2\n", .redefinedTable)
  , ("aot_overwrite_inline_arr", "a = [1, 2]\n[[a]]\nb = 3\n", .redefinedTable)
  , ("inline_table_trailing_comma", "a = { b = 1, }\n", .parseError)
  , ("inline_table_newline", "a = {\nb = 1\n}\n", .parseError)
  , ("leading_zero_int", "a = 012\n", .parseError)
  , ("bad_hex_sign", "a = +0x1\n", .parseError)
  , ("float_leading_dot", "a = .5\n", .parseError)
  , ("float_trailing_dot", "a = 1.\n", .parseError)
  , ("invalid_leap_day", "d = 2021-02-29\n", .parseError)
  , ("invalid_month", "d = 2020-13-01\n", .parseError)
  , ("invalid_offset_hour", "d = 2020-01-01T00:00:00+24:00\n", .parseError)
  , ("leap_second_60", "t = 12:00:60\n", .parseError)
  , ("unescaped_control_char", "s = \"a\x01b\"\n", .invalidUtf8OrControl)
  , ("bare_cr", "s = \"a\rb\"\n", .invalidUtf8OrControl)
  , ("nine_quotes_mll", "s = '''''''''\n", .parseError)
  ]

private def parsePythonTagOutput (raw : String) : List (Bool × String) :=
  let lines := raw.splitOn "\n"
  lines.filterMap fun ln =>
    if ln.isEmpty then none
    else if ln.startsWith "OK:" then some (true, (ln.drop 3).toString)
    else if ln.startsWith "ERR:" then some (false, (ln.drop 4).toString)
    else none

private def pythonDiffLineScript : String :=
  "import sys, tomllib, math, struct, datetime, json\n" ++
  "def hx(s):\n" ++
  "  return s.encode('utf-8').hex()\n" ++
  "def fmt_off(off):\n" ++
  "  sec = int(off.total_seconds())\n" ++
  "  if sec == 0: return '+00:00'\n" ++
  "  sgn = '-' if sec < 0 else '+'\n" ++
  "  mins = abs(sec) // 60\n" ++
  "  return f'{sgn}{mins // 60:02d}:{mins % 60:02d}'\n" ++
  "def fmt_tm(t):\n" ++
  "  base = f'{t.hour:02d}:{t.minute:02d}:{t.second:02d}'\n" ++
  "  ns = t.microsecond * 1000\n" ++
  "  return base if ns == 0 else f'{base}.{ns:09d}'\n" ++
  "def fmt_dt(d):\n" ++
  "  return f'{d.year:04d}-{d.month:02d}-{d.day:02d}'\n" ++
  "def canon(v):\n" ++
  "  if isinstance(v, dict):\n" ++
  "    items = sorted(v.items(), key=lambda kv: kv[0])\n" ++
  "    return '{' + ','.join(hx(k) + '=' + canon(val) for k, val in items) + '}'\n" ++
  "  if isinstance(v, list):\n" ++
  "    return '[' + ','.join(canon(x) for x in v) + ']'\n" ++
  "  if isinstance(v, bool):\n" ++
  "    return 'B:true' if v else 'B:false'\n" ++
  "  if isinstance(v, int):\n" ++
  "    return f'I:{v}'\n" ++
  "  if isinstance(v, float):\n" ++
  "    if math.isnan(v): return 'F:nan'\n" ++
  "    bits = struct.unpack('>Q', struct.pack('>d', v))[0]\n" ++
  "    return f'F:{bits}'\n" ++
  "  if isinstance(v, str):\n" ++
  "    return 'S:' + hx(v)\n" ++
  "  if isinstance(v, datetime.datetime):\n" ++
  "    if v.tzinfo is not None:\n" ++
  "      return 'ODT:' + fmt_dt(v) + 'T' + fmt_tm(v) + fmt_off(v.utcoffset())\n" ++
  "    return 'LDT:' + fmt_dt(v) + 'T' + fmt_tm(v)\n" ++
  "  if isinstance(v, datetime.date):\n" ++
  "    return 'LD:' + fmt_dt(v)\n" ++
  "  if isinstance(v, datetime.time):\n" ++
  "    return 'LT:' + fmt_tm(v)\n" ++
  "  raise TypeError(repr(type(v)))\n" ++
  "cases = json.loads(sys.stdin.read())\n" ++
  "for src in cases:\n" ++
  "  try:\n" ++
  "    doc = tomllib.loads(src)\n" ++
  "    print('OK:' + canon(doc))\n" ++
  "  except tomllib.TOMLDecodeError as e:\n" ++
  "    print('ERR:' + repr(str(e)))\n"

private def testDifferentialVsPython : IO Unit := do
  let validSrcs := validDifferentialDocs.map Prod.snd
  let invalidSrcs := invalidDifferentialDocs.map (fun p => p.2.1)
  let allSrcs := validSrcs ++ invalidSrcs
  let payload := "[" ++ String.intercalate "," (allSrcs.map jsonEscape) ++ "]"
  let pyOut ← runPython3 pythonDiffLineScript payload
  let pyResults := parsePythonTagOutput pyOut
  assertTrue (pyResults.length == allSrcs.length)
    s!"python output line count mismatch: {pyResults.length} vs {allSrcs.length}"
  let validCount := validDifferentialDocs.length
  let pyValid := pyResults.take validCount
  let pyInvalid := pyResults.drop validCount
  for ((name, src), (pyOk, pyVal)) in validDifferentialDocs.zip pyValid do
    assertTrue pyOk s!"python tomllib unexpectedly rejected valid case {name}: {pyVal}"
    let leanTab ← assertOk (parse src) s!"lean parse({name})"
    let leanCanon := canonicalizeTable leanTab
    assertTrue (leanCanon == pyVal)
      s!"differential mismatch on {name}:\nlean={leanCanon}\npy  ={pyVal}"
    let formatted := format leanTab
    let reparsed ← assertOk (parse formatted) s!"lean reparse(format({name}))"
    assertTrue (canonicalizeTable reparsed == leanCanon)
      s!"format->parse mismatch on {name}"
  for ((name, src, expectedKind), (pyOk, _)) in invalidDifferentialDocs.zip pyInvalid do
    assertTrue (!pyOk) s!"python tomllib unexpectedly accepted invalid case {name}"
    assertErrKind (parse src) expectedKind s!"lean reject({name})"

private def testFormattedRoundTripViaPython : IO Unit := do
  let tbl : TomlTable :=
    #[ ("title", .string "TOML \"Example\"\nLine2")
     , ("count", .int (-42))
     , ("ratio", .float (-0.0))
     , ("infv", .float Float.inf)
     , ("nanv", .float Float.nan)
     , ("flag", .bool true)
     , ("tags", .array #[.string "alpha", .string "beta"])
     , ("empty_arr", .array #[])
     , ("owner", .table #[("name", .string "Alice"), ("nested", .table #[("ok", .bool false)])])
     , ("items", .array #[.table #[("id", .int 1)], .table #[("id", .int 2), ("sub", .table #[("k", .string "v")])]])
     ]
  let formatted := format tbl
  let payload := "[" ++ jsonEscape formatted ++ "]"
  let pyOut ← runPython3 pythonDiffLineScript payload
  let pyResults := parsePythonTagOutput pyOut
  match pyResults with
  | [(true, pyCanon)] =>
    assertTrue (canonicalizeTable tbl == pyCanon)
      s!"formatted roundtrip vs python mismatch:\nlean={canonicalizeTable tbl}\npy  ={pyCanon}"
  | other =>
    throw (IO.userError s!"python failed on formatted document: {repr other}\n{formatted}")

private def testYear0000DirectRfc3339 : IO Unit := do
  let doc :=
    "d0 = 0000-01-01\n" ++
    "d_leap = 0000-02-29\n" ++
    "odt0 = 0000-12-31T23:59:59.123456789Z\n" ++
    "ldt0 = 0000-06-15 01:02:03.4\n"
  let tab ← assertOk (parse doc) "parse year 0000 RFC 3339"
  let d0 : Std.Time.PlainDate ← assertOk (getField tab "d0") "getField d0"
  assertTrue (d0.year == 0 && d0.month.val == 1 && d0.day.val == 1) "d0 values"
  let dl : Std.Time.PlainDate ← assertOk (getField tab "d_leap") "getField d_leap"
  assertTrue (dl.year == 0 && dl.month.val == 2 && dl.day.val == 29) "year 0000 leap day"
  let odt0 : TomlOffsetDateTime ← assertOk (getField tab "odt0") "getField odt0"
  assertTrue (odt0.dateTime.date.year == 0 && odt0.dateTime.time.nanosecond.val == 123456789 &&
    odt0.offset.second.val == 0) "odt0 values"
  let formatted := format tab
  let reparsed ← assertOk (parse formatted) "reparse year 0000 formatted"
  assertTrue (canonicalizeTable reparsed == canonicalizeTable tab) "year 0000 format round-trip"
  let subNsTab ← assertOk (parse "tm = 07:32:00.123456789999") "parse >9 fractional digits without trailing newline"
  let tm : Std.Time.PlainTime ← assertOk (getField subNsTab "tm") "getField tm"
  assertTrue (tm.nanosecond.val == 123456789) "sub-nanosecond truncation to 9 digits"

private def testCodecsAndAccessors : IO Unit := do
  let doc :=
    "port = 8080\n" ++
    "name = \"srv\"\n" ++
    "hosts = [\"a\", \"b\"]\n" ++
    "[db.primary]\n" ++
    "host = \"localhost\"\n" ++
    "retries = 3\n"
  let tab ← assertOk (parse doc) "parse config"
  let port : Nat ← assertOk (getField tab "port") "getField port"
  assertTrue (port == 8080) "port == 8080"
  let optMissing : Option String ← assertOk (getOptField tab "missing_key") "getOptField missing"
  assertTrue (optMissing == none) "optMissing == none"
  let optPresent : Option String ← assertOk (getOptField tab "name") "getOptField name"
  assertTrue (optPresent == some "srv") "optPresent == some srv"
  let hosts : Array String ← assertOk (getField tab "hosts") "getField hosts"
  assertTrue (hosts == #["a", "b"]) "hosts array"
  let host : String ← assertOk (getPath tab ["db", "primary", "host"]) "getPath db.primary.host"
  assertTrue (host == "localhost") "host == localhost"
  let rootDecoded : TomlTable ← assertOk (getPath tab []) "getPath []"
  let directDecoded : TomlTable ← assertOk (decode (.table tab)) "decode table"
  assertTrue (canonicalizeTable rootDecoded == canonicalizeTable directDecoded) "getPath [] matches decode"
  assertErrKind (getField (α := Nat) tab "absent") .missingField "missing field error"
  assertErrKind (getField (α := Nat) tab "name") .decodeError "decode error on type mismatch"
  assertErrKind (getPath (α := String) tab ["port", "sub"]) .typeMismatch "non-table intermediate path"
  assertErrKind (getPath (α := String) tab ["db", "missing", "host"]) .missingField "missing intermediate path"
  assertErrKind (getTable (.int 1)) .typeMismatch "getTable non-table"
  assertErrKind (getArray (.bool false)) .typeMismatch "getArray non-array"
  let encoded := encode (#[1, 2, 3] : Array Int64)
  let arr ← assertOk (getArray encoded) "getArray encoded"
  assertTrue (arr.size == 3) "encoded array size"

/-- Verify `parse` rejects malformed syntax with `.parseError`. -/
def err_toml_parse_parseError : IO Unit :=
  assertErrKind (parse "a =") .parseError "parse syntax error"

/-- Verify `parse` rejects duplicate keys with `.duplicateKey`. -/
def err_toml_parse_duplicateKey : IO Unit :=
  assertErrKind (parse "a = 1\na = 2\n") .duplicateKey "parse duplicate key"

/-- Verify `parse` rejects redefined table headers with `.redefinedTable`. -/
def err_toml_parse_redefinedTable : IO Unit :=
  assertErrKind (parse "[t]\na = 1\n[t]\nb = 2\n") .redefinedTable "parse redefined table"

/-- Verify `parse` rejects dotted extension of an inline table with `.immutableInlineTable`. -/
def err_toml_parse_immutableInlineTable : IO Unit :=
  assertErrKind (parse "t = { a = 1 }\nt.b = 2\n") .immutableInlineTable "parse immutable inline table"

/-- Verify `parse` rejects bare carriage return / control chars with `.invalidUtf8OrControl`. -/
def err_toml_parse_invalidUtf8OrControl : IO Unit :=
  assertErrKind (parse "a = 1\r b = 2\n") .invalidUtf8OrControl "parse bare CR"

/-- Verify `parse` rejects 64-bit integer overflow with `.numericOverflow`. -/
def err_toml_parse_numericOverflow : IO Unit :=
  assertErrKind (parse "a = 9223372036854775808\n") .numericOverflow "parse int64 overflow"

/-- Verify `decode` rejects incompatible `TomlValue` with `.decodeError`. -/
def err_toml_decode_decodeError : IO Unit :=
  assertErrKind (decode (α := Int64) (.string "not_an_int")) .decodeError "decode string as Int64"

/-- Verify `getTable` rejects non-table `TomlValue` with `.typeMismatch`. -/
def err_toml_getTable_typeMismatch : IO Unit :=
  assertErrKind (getTable (.int 1)) .typeMismatch "getTable non-table"

/-- Verify `getArray` rejects non-array `TomlValue` with `.typeMismatch`. -/
def err_toml_getArray_typeMismatch : IO Unit :=
  assertErrKind (getArray (.bool false)) .typeMismatch "getArray non-array"

/-- Verify `getField` rejects absent key with `.missingField`. -/
def err_toml_getField_missingField : IO Unit :=
  assertErrKind (getField (α := Nat) #[("a", .int 1)] "absent") .missingField "getField missing"

/-- Verify `getField` rejects ill-typed field value with `.decodeError`. -/
def err_toml_getField_decodeError : IO Unit :=
  assertErrKind (getField (α := Nat) #[("name", .string "srv")] "name") .decodeError "getField decode error"

/-- Verify `getOptField` rejects present ill-typed field value with `.decodeError`. -/
def err_toml_getOptField_decodeError : IO Unit :=
  assertErrKind (getOptField (α := Nat) #[("name", .string "srv")] "name") .decodeError "getOptField decode error"

/-- Verify `getPath` rejects missing nested key with `.missingField`. -/
def err_toml_getPath_missingField : IO Unit :=
  let tab : TomlTable := #[("db", .table #[("host", .string "localhost")])]
  assertErrKind (getPath (α := String) tab ["db", "missing", "host"]) .missingField "getPath missing"

/-- Verify `getPath` rejects non-table intermediate key with `.typeMismatch`. -/
def err_toml_getPath_typeMismatch : IO Unit :=
  let tab : TomlTable := #[("port", .int 8080)]
  assertErrKind (getPath (α := String) tab ["port", "sub"]) .typeMismatch "getPath non-table intermediate"

/-- Verify `getPath` rejects ill-typed leaf value with `.decodeError`. -/
def err_toml_getPath_decodeError : IO Unit :=
  let tab : TomlTable := #[("db", .table #[("host", .string "localhost")])]
  assertErrKind (getPath (α := Nat) tab ["db", "host"]) .decodeError "getPath decode error"

/-- Registered error-coverage tests for `LeanSwe.Toml`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_parseError", mode := .real, run := err_toml_parse_parseError }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_duplicateKey", mode := .real, run := err_toml_parse_duplicateKey }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_redefinedTable", mode := .real, run := err_toml_parse_redefinedTable }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_immutableInlineTable", mode := .real, run := err_toml_parse_immutableInlineTable }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_invalidUtf8OrControl", mode := .real, run := err_toml_parse_invalidUtf8OrControl }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_parse_numericOverflow", mode := .real, run := err_toml_parse_numericOverflow }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_decode_decodeError", mode := .real, run := err_toml_decode_decodeError }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getTable_typeMismatch", mode := .real, run := err_toml_getTable_typeMismatch }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getArray_typeMismatch", mode := .real, run := err_toml_getArray_typeMismatch }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getField_missingField", mode := .real, run := err_toml_getField_missingField }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getField_decodeError", mode := .real, run := err_toml_getField_decodeError }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getOptField_decodeError", mode := .real, run := err_toml_getOptField_decodeError }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getPath_missingField", mode := .real, run := err_toml_getPath_missingField }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getPath_typeMismatch", mode := .real, run := err_toml_getPath_typeMismatch }
   , { testName := "LeanSwe.Toml.RuntimeTests.err_toml_getPath_decodeError", mode := .real, run := err_toml_getPath_decodeError } ]

/-- Run all differential and runtime verification tests for `LeanSwe.Toml`. -/
def runAll : IO Unit := do
  testDifferentialVsPython
  testFormattedRoundTripViaPython
  testYear0000DirectRfc3339
  testCodecsAndAccessors
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Toml runtime tests"

end LeanSwe.Toml.RuntimeTests

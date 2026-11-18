import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.NumParse.Model

/-- Assert that parsing `case.1` succeeds with a table `TomlTableEquiv` to `case.2`. -/
def checkParseEquiv {runner} [NondetTest runner] (api : TomlApi) (case : String × TomlTable) :
    runner Unit :=
  match api.parse case.1 with
  | .ok parsed => NondetTest.assert (Model.TomlTableEquiv case.2 parsed)
  | .error _ => NondetTest.assert False

/-- Assert that parsing `case.1` fails with exact `case.2` error kind and a non-empty message. -/
def checkParseErrorKind {runner} [NondetTest runner] (api : TomlApi)
    (case : String × TomlErrorKind) : runner Unit :=
  match api.parse case.1 with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = case.2 ∧ !e.message.isEmpty = true)

/-- Assert that parsing `src` yields a `.float` entry at `key` matching `expectedBits?` (`none` means `NaN`). -/
def checkParseFloatBits {runner} [NondetTest runner] (api : TomlApi)
    (case : String × String × Option UInt64) : runner Unit :=
  match api.parse case.1 with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    match Model.lookupKey case.2.1 parsed with
    | some (.float f) =>
      match case.2.2 with
      | none => NondetTest.assert (f.isNaN = true)
      | some bits => NondetTest.assert (f.toBits = bits)
    | _ => NondetTest.assert False

/-- Construct a concrete `Std.Time.PlainDate` for spec test expectations. -/
def specDate (y : Int) (m : Std.Time.Month.Ordinal) (d : Std.Time.Day.Ordinal) :
    Std.Time.PlainDate :=
  Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt y) m d

/-- Construct a concrete `Std.Time.PlainTime` for spec test expectations. -/
def specTime (h : Std.Time.Hour.Ordinal) (m : Std.Time.Minute.Ordinal)
    (s : Std.Time.Second.Ordinal true) (ns : Std.Time.Nanosecond.Ordinal := 0) :
    Std.Time.PlainTime :=
  Std.Time.PlainTime.mk h m s ns

/-- Construct a concrete `Std.Time.TimeZone.Offset` from signed UTC seconds. -/
def specOffset (sec : Int) : Std.Time.TimeZone.Offset :=
  Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt sec)

/-- Any parsing failure returned by `api.parse` must carry a non-empty diagnostic message. -/
def test_toml_onError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let s ← nondet String
  match api.parse s with
  | .ok _ => pure ()
  | .error e => NondetTest.assert (!e.message.isEmpty = true)

/-- Any navigation or decoding error returned by `api` accessors carries a non-empty diagnostic message. -/
def test_toml_accessorError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let v ← nondet TomlValue
  let t ← nondet TomlTable
  let k ← nondet String
  let path ← nondet (List String)
  (match api.getTable v with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.getArray v with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.getField (α := TomlValue) t k with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.getOptField (α := String) t k with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))
  (match api.getPath (α := TomlValue) t path with
   | .ok _ => pure ()
   | .error e => NondetTest.assert (!e.message.isEmpty = true))

/-- Every `TomlTable` successfully returned by `api.parse` satisfies `Model.WellFormedTable`. -/
def test_toml_parse_returnsWellFormedTable
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let s ← nondet String
  match api.parse s with
  | .error _ => pure ()
  | .ok t => NondetTest.assert (Model.WellFormedTable t)

/-- Every TOML document accepted by `Model.render` parses back to a `TomlTableEquiv` table. -/
def test_toml_render_parse_roundTrip
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let pair ← nondet (TomlTable × Model.RenderTape)
  match Model.render pair.1 pair.2 with
  | none => assume False
  | some txt =>
    match api.parse txt with
    | .error _ => NondetTest.assert False
    | .ok parsed => NondetTest.assert (Model.TomlTableEquiv pair.1 parsed)

/-- Formatting any `WellFormedTable` produces valid TOML text that parses back `TomlTableEquiv` to the input. -/
def test_toml_format_validAndRoundTrip
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let doc ← nondet TomlTable
  assume (Model.WellFormedTable doc)
  let txt := api.format doc
  match api.parse txt with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (Model.TomlTableEquiv doc parsed)

/-- Concrete positive cases for keys, dotted keys, comments, CRLF, and 4-state table provenance. -/
def keyProvenanceOkCases : List (String × TomlTable) :=
  [ ("", #[])
  , ("# comment only\t\r\n   \r\n# eof without newline", #[])
  , ("1234 = \"num\"\r\n007 = true\n1979-05-27 = 1\ntrue = 2\n_a-b = 3",
      #[("1234", .string "num"), ("007", .bool true), ("1979-05-27", .int 1),
        ("true", .int 2), ("_a-b", .int 3)])
  , ("\"\" = 1\n'a.b' = 2\n\"x y\" = 3", #[("", .int 1), ("a.b", .int 2), ("x y", .int 3)])
  , ("a.b.c = 1\na.\"\".d = 2\na.e = 3",
      #[("a", .table #[("b", .table #[("c", .int 1)]),
                        ("", .table #[("d", .int 2)]),
                        ("e", .int 3)])])
  , ("[a.b]\nx = 1\n[a]\ny = 2",
      #[("a", .table #[("b", .table #[("x", .int 1)]), ("y", .int 2)])])
  , ("a.b = 1\n[a.c]\nx = 2",
      #[("a", .table #[("b", .int 1), ("c", .table #[("x", .int 2)])])])
  , ("[parent.a.b]\nx = 1\n[parent]\na.c = 2\n[parent.a.d]\ny = 3",
      #[("parent", .table #[("a", .table #[("b", .table #[("x", .int 1)]),
                                           ("c", .int 2),
                                           ("d", .table #[("y", .int 3)])])])])
  ]

/-- Concrete negative cases for key syntax, duplicate keys, provenance errors, and statement boundaries. -/
def keyProvenanceErrCases : List (String × TomlErrorKind) :=
  [ ("café = 1", .parseError)
  , ("a..b = 1", .parseError)
  , (".a = 1", .parseError)
  , ("\"\"\"a\"\"\" = 1", .parseError)
  , ("'''a''' = 1", .parseError)
  , ("a = 1 b = 2", .parseError)
  , ("[a] b = 1", .parseError)
  , ("a =\n1", .parseError)
  , ("a = 1\n\"a\" = 2", .duplicateKey)
  , ("1 = 1\n\"1\" = 2", .duplicateKey)
  , ("a = 1\na.b = 2", .duplicateKey)
  , ("a = [1]\na.b = 2", .duplicateKey)
  , ("[a]\nx = 1\n[a]\ny = 2", .redefinedTable)
  , ("[a.b]\nx = 1\n[a]\ny = 2\n[a]\nz = 3", .redefinedTable)
  , ("a.b = 1\n[a]\nc = 2", .redefinedTable)
  , ("[parent.a.b]\nx = 1\n[parent]\na.c = 2\n[parent.a]\nd = 3", .redefinedTable)
  , ("[parent.a]\nx = 1\n[parent]\na.y = 2", .redefinedTable)
  , ("a = 1\n[a]\nx = 2", .redefinedTable)
  , ("a = [1]\n[a]\nx = 2", .redefinedTable)
  ]

/-- Keys, dotted keys, statement boundaries, and 4-state table provenance conform to TOML 1.0. -/
def test_toml_keysAndProvenance_conformsToSpec
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  keyProvenanceOkCases.forM (checkParseEquiv api)
  keyProvenanceErrCases.forM (checkParseErrorKind api)

/-- Concrete positive cases for inline tables, arrays, and arrays of tables `[[...]]`. -/
def inlineAotOkCases : List (String × TomlTable) :=
  [ ("empty = {}\nnested = { a.b = 1, a.c = 2 }",
      #[("empty", .table #[]),
        ("nested", .table #[("a", .table #[("b", .int 1), ("c", .int 2)])])])
  , ("t = { s = \"\"\"\na\nb\"\"\", xs = [\n  1,\n  2,\n] }",
      #[("t", .table #[("s", .string "a\nb"), ("xs", .array #[.int 1, .int 2])])])
  , ("mix = [ 1, \"two\", true, { k = 3 }, # comment\n]",
      #[("mix", .array #[.int 1, .string "two", .bool true, .table #[("k", .int 3)]])])
  , ("[[products]]\nname = \"Hammer\"\n[[products]]\n[[products]]\nname = \"Nail\"",
      #[("products", .array #[.table #[("name", .string "Hammer")],
                              .table #[],
                              .table #[("name", .string "Nail")]])])
  , ("[[fruits]]\nname = \"apple\"\n[fruits.physical]\ncolor = \"red\"\n[[fruits.varieties]]\nname = \"fuji\"\n[[fruits]]\nname = \"orange\"\n[[fruits.varieties]]\nname = \"navel\"",
      #[("fruits", .array #[
            .table #[("name", .string "apple"),
                     ("physical", .table #[("color", .string "red")]),
                     ("varieties", .array #[.table #[("name", .string "fuji")]])],
            .table #[("name", .string "orange"),
                     ("varieties", .array #[.table #[("name", .string "navel")]])]])])
  , ("a.b = 1\n[[a.c]]\nx = 2",
      #[("a", .table #[("b", .int 1), ("c", .array #[.table #[("x", .int 2)]])])])
  ]

/-- Concrete negative cases for inline table immutability/syntax and array-of-tables conflicts. -/
def inlineAotErrCases : List (String × TomlErrorKind) :=
  [ ("t = { a = 1 }\nt.b = 2", .immutableInlineTable)
  , ("t = { a.b = 1 }\n[t.c]\nx = 2", .immutableInlineTable)
  , ("t = { a = {} }\nt.a.b = 1", .immutableInlineTable)
  , ("t = { a = 1 }\n[t]\nb = 2", .immutableInlineTable)
  , ("t = { a = 1 }\n[[t]]\nb = 2", .immutableInlineTable)
  , ("t = { a = 1, a = 2 }", .duplicateKey)
  , ("t = { a = 1, }", .parseError)
  , ("t = {\na = 1}", .parseError)
  , ("t = {a =\n1}", .parseError)
  , ("t = {a = 1,\nb = 2}", .parseError)
  , ("t = {a = 1\n}", .parseError)
  , ("a = [{}]\n[[a]]\nx = 1", .redefinedTable)
  , ("[a]\nx = 1\n[[a]]\ny = 2", .redefinedTable)
  , ("[[a]]\nx = 1\n[a]\ny = 2", .redefinedTable)
  , ("[[parent.a]]\nx = 1\n[parent]\na = []", .duplicateKey)
  ]

/-- Inline tables, arrays, and `[[array_of_tables]]` rules conform to TOML 1.0. -/
def test_toml_inlineTablesAndAot_conformsToSpec
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  inlineAotOkCases.forM (checkParseEquiv api)
  inlineAotErrCases.forM (checkParseErrorKind api)

/-- Concrete positive cases for basic, multiline basic, literal, and multiline literal strings. -/
def stringOkCases : List (String × TomlTable) :=
  [ ("s = \"\\b\\t\\n\\f\\r\\\"\\\\\\u0041\\U0001F600\"",
      #[("s", .string "\x08\t\n\x0c\r\"\\A😀")])
  , ("s1 = \"\"\"\nhello\"\"\"\ns2 = \"\"\"\n\nhello\"\"\"",
      #[("s1", .string "hello"), ("s2", .string "\nhello")])
  , ("crlf = \"\"\"a\r\nb\"\"\"\nlcrlf = '''\r\na\r\nb'''",
      #[("crlf", .string "a\nb"), ("lcrlf", .string "a\nb")])
  , ("trim = \"\"\"the \\\n  \t quick\"\"\"\nkeep = \"\"\"the \\\\\n  quick\"\"\"",
      #[("trim", .string "the quick"), ("keep", .string "the \\\n  quick")])
  , ("q0 = \"\"\"\"\"\"\nq1 = \"\"\"\"\"\"\"\nq2 = \"\"\"\"\"\"\"\"",
      #[("q0", .string ""), ("q1", .string "\""), ("q2", .string "\"\"")])
  , ("lit = 'C:\\Users\\name'\nmlit = '''\n\\no\\escape\\'''\nlq2 = ''''''''",
      #[("lit", .string "C:\\Users\\name"), ("mlit", .string "\\no\\escape\\"), ("lq2", .string "''")])
  ]

/-- Concrete negative cases for disallowed control chars, bare CR, surrogates, and invalid escapes/quotes. -/
def stringErrCases : List (String × TomlErrorKind) :=
  [ ("a = 1 # bad\x00comment", .invalidUtf8OrControl)
  , ("a = 1 # bad\x7fcomment", .invalidUtf8OrControl)
  , ("a = 1\r", .invalidUtf8OrControl)
  , ("a = \"bad\x00str\"", .invalidUtf8OrControl)
  , ("a = \"bad\x1fstr\"", .invalidUtf8OrControl)
  , ("a = \"bad\rstr\"", .invalidUtf8OrControl)
  , ("a = 'bad\x08str'", .invalidUtf8OrControl)
  , ("a = 'bad\x7fstr'", .invalidUtf8OrControl)
  , ("a = \"\"\"bad\rline\"\"\"", .invalidUtf8OrControl)
  , ("a = '''bad\rline'''", .invalidUtf8OrControl)
  , ("a = \"\\uD800\"", .invalidUtf8OrControl)
  , ("a = \"\\uDFFF\"", .invalidUtf8OrControl)
  , ("a = \"\\U00110000\"", .invalidUtf8OrControl)
  , ("a = \"\\a\"", .parseError)
  , ("a = \"\\x20\"", .parseError)
  , ("a = \"unclosed", .parseError)
  , ("a = \"line\nbreak\"", .parseError)
  , ("a = 'line\nbreak'", .parseError)
  , ("a = \"\"\"\"\"\"\"\"\"", .parseError)
  , ("a = '''''''''", .parseError)
  ]

/-- String escapes, multiline whitespace/quote boundaries, CRLF normalization, and control rejections conform to TOML 1.0. -/
def test_toml_stringsAndControls_conformsToSpec
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  stringOkCases.forM (checkParseEquiv api)
  stringErrCases.forM (checkParseErrorKind api)

/-- Concrete positive cases for integers, booleans, and all 4 RFC 3339 datetime variants. -/
def numberDatetimeOkCases : List (String × TomlTable) :=
  [ ("min = -9223372036854775808\nmax = 9223372036854775807\nhex = 0xdead_beef\noct = 0o755\nbin = 0b1010_0101\nbt = true\nbf = false",
      #[("min", .int (-9223372036854775808)),
        ("max", .int 9223372036854775807),
        ("hex", .int 0xdeadbeef),
        ("oct", .int 0o755),
        ("bin", .int 0b10100101),
        ("bt", .bool true),
        ("bf", .bool false)])
  , ("odt1 = 1979-05-27T07:32:00Z\nodt2 = 1979-05-27t07:32:00z\nodt3 = 1979-05-27 07:32:00+00:00\nodt4 = 1979-05-27T07:32:00-00:00",
      let dt := Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0)
      let v := TomlValue.offsetDateTime { dateTime := dt, offset := specOffset 0 }
      #[("odt1", v), ("odt2", v), ("odt3", v), ("odt4", v)])
  , ("pos = 1979-05-27T07:32:00+05:30\nneg = 1979-05-27T07:32:00.1234567899-07:00",
      let d := specDate 1979 5 27
      #[("pos", .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d (specTime 7 32 0),
                                   offset := specOffset 19800 }),
        ("neg", .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d (specTime 7 32 0 123456789),
                                   offset := specOffset (-25200) })])
  , ("ldt = 1979-05-27 07:32:00.5\nld0 = 0000-01-01\nleap = 2024-02-29\nldmax = 9999-12-31\nlt = 23:59:59.9999999999",
      #[("ldt", .localDateTime (Std.Time.PlainDateTime.mk (specDate 1979 5 27) (specTime 7 32 0 500000000))),
        ("ld0", .localDate (specDate 0 1 1)),
        ("leap", .localDate (specDate 2024 2 29)),
        ("ldmax", .localDate (specDate 9999 12 31)),
        ("lt", .localTime (specTime 23 59 59 999999999))])
  ]

/-- Concrete float bit-level verification cases (`-0.0`, `+0.0`, `inf`, `-inf`, `nan`). -/
def floatBitCases : List (String × String × Option UInt64) :=
  [ ("f = 0.0", "f", some (0.0 : Float).toBits)
  , ("f = -0.0", "f", some (-0.0 : Float).toBits)
  , ("f = 1.0", "f", some (1.0 : Float).toBits)
  , ("f = 5e+22", "f", some (5e22 : Float).toBits)
  , ("f = inf", "f", some Float.inf.toBits)
  , ("f = +inf", "f", some Float.inf.toBits)
  , ("f = -inf", "f", some (-Float.inf).toBits)
  , ("f = nan", "f", none)
  , ("f = +nan", "f", none)
  , ("f = -nan", "f", none)
  ]

/-- Concrete negative cases for integers, overflows, floats, and RFC 3339 datetimes. -/
def numberDatetimeErrCases : List (String × TomlErrorKind) :=
  [ ("i = 9223372036854775808", .numericOverflow)
  , ("i = -9223372036854775809", .numericOverflow)
  , ("i = 0X1", .parseError)
  , ("i = 0O7", .parseError)
  , ("i = 0B1", .parseError)
  , ("i = +0x1", .parseError)
  , ("i = -0b1", .parseError)
  , ("i = 01", .parseError)
  , ("f = .5", .parseError)
  , ("f = 1.", .parseError)
  , ("f = NaN", .parseError)
  , ("f = Inf", .parseError)
  , ("d = 2024-01-01T23:59:60Z", .parseError)
  , ("d = 2023-02-29", .parseError)
  , ("d = 12:00:00.", .parseError)
  , ("d = 2024-01-01T12:00:00 +01:00", .parseError)
  , ("d = 2024-01-01  12:00:00", .parseError)
  , ("d = 2024-01-01\t12:00:00", .parseError)
  , ("d = 2024-01-01T12:00:00+24:00", .parseError)
  ]

/-- Integer/float delegation (`NumParse`), `0X` rejection, overflow classification, and RFC 3339 datetimes conform to TOML 1.0. -/
def test_toml_numbersAndDatetimes_conformsToSpec
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  numberDatetimeOkCases.forM (checkParseEquiv api)
  floatBitCases.forM (checkParseFloatBits api)
  numberDatetimeErrCases.forM (checkParseErrorKind api)

/-- Codecs (`FromToml`/`ToToml`) and strict accessors (`getTable`, `getArray`, `getField`, `getOptField`, `getPath`) satisfy round-trip and error invariants. -/
def test_toml_codecsAndAccessors_conformsToSpec
    {runner} [NondetTest runner] (api : TomlApi) : runner Unit := do
  let s ← nondet String
  let n64 ← nondet Int64
  let f ← nondet Float
  let b ← nondet Bool
  let odt ← nondet TomlOffsetDateTime
  let ldt ← nondet Std.Time.PlainDateTime
  let ld ← nondet Std.Time.PlainDate
  let lt ← nondet Std.Time.PlainTime
  let xs ← nondet (Array Int64)
  let tbl ← nondet TomlTable
  NondetTest.assert (api.decode (api.encode s) = .ok s)
  NondetTest.assert (api.decode (api.encode n64) = .ok n64)
  NondetTest.assert (match api.decode (α := Float) (api.encode f) with
    | .ok g => FloatEquiv f g
    | .error _ => False)
  NondetTest.assert (api.decode (api.encode b) = .ok b)
  NondetTest.assert (api.decode (api.encode odt) = .ok odt)
  NondetTest.assert (api.decode (api.encode ldt) = .ok ldt)
  NondetTest.assert (api.decode (api.encode ld) = .ok ld)
  NondetTest.assert (api.decode (api.encode lt) = .ok lt)
  NondetTest.assert (api.decode (api.encode xs) = .ok xs)
  NondetTest.assert (api.decode (api.encode tbl) = .ok tbl)
  NondetTest.assert (api.decode (α := Int) (.int (-5)) = .ok (-5))
  NondetTest.assert (api.decode (α := Nat) (.int 42) = .ok 42)
  NondetTest.assert (match api.decode (α := Nat) (.int (-1)) with
    | .error e => e.kind = .decodeError ∧ !e.message.isEmpty = true
    | .ok _ => False)
  let sample : TomlTable :=
    #[("port", .int 8080),
      ("db", .table #[("host", .string "localhost"), ("tags", .array #[.string "a"])]),
      ("flag", .bool true)]
  NondetTest.assert (api.getTable (.table sample) = .ok sample)
  NondetTest.assert (match api.getTable (.int 1) with
    | .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (api.getArray (.array #[.int 1]) = .ok #[.int 1])
  NondetTest.assert (match api.getArray (.string "x") with
    | .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (api.getField (α := Int64) sample "port" = .ok 8080)
  NondetTest.assert (match api.getField (α := Int64) sample "missing" with
    | .error e => e.kind = .missingField ∧ e.path = some "missing" ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (match api.getField (α := String) sample "port" with
    | .error e => e.kind = .decodeError ∧ e.path = some "port" ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (api.getOptField (α := Int64) sample "port" = .ok (some 8080))
  NondetTest.assert (api.getOptField (α := Int64) sample "missing" = .ok none)
  NondetTest.assert (match api.getOptField (α := String) sample "port" with
    | .error e => e.kind = .decodeError ∧ e.path = some "port" ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (api.getPath (α := TomlTable) sample [] = .ok sample)
  NondetTest.assert (match api.getPath (α := Int64) sample [] with
    | .error e => e.kind = .decodeError ∧ e.path = none ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (api.getPath (α := String) sample ["db", "host"] = .ok "localhost")
  NondetTest.assert (match api.getPath (α := String) sample ["db", "missing"] with
    | .error e => e.kind = .missingField ∧ e.path = some "db.missing" ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (match api.getPath (α := String) sample ["port", "sub"] with
    | .error e => e.kind = .typeMismatch ∧ e.path = some "port" ∧ !e.message.isEmpty = true
    | .ok _ => False)
  NondetTest.assert (match api.getPath (α := Int64) sample ["db", "host"] with
    | .error e => e.kind = .decodeError ∧ e.path = some "db.host" ∧ !e.message.isEmpty = true
    | .ok _ => False)

end LeanSwe.Toml

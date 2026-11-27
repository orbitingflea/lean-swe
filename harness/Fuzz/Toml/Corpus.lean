import Fuzz.Common.Rng
import Fuzz.Toml.Gen
import LeanSwe.Toml.Interface
import LeanSweProofs.Toml.Model

namespace Fuzz.Toml

open Fuzz.Common
open LeanSwe.Toml

private def genMalformedCase (r : Rng) : TomlFuzzCase × Rng :=
  let (cat, r1) := r.nextNat 10
  if cat == 0 then
    let pool : Array String := #[
      "a = 1\na = 2\n",
      "a = 1\n\"a\" = 2\n",
      "'x' = 1\nx = 2\n",
      "1 = 1\n\"1\" = 2\n",
      "t = { k = 1, k = 2 }\n",
      "t = { a.b = 1, a = { b = 2 } }\n",
      "a = 1\na.b = 2\n",
      "a = [1]\na.b = 2\n",
      "[[p.a]]\nx = 1\n[p]\na = []\n"
    ]
    let (s, r2) := r1.choose pool "a = 1\na = 2\n"
    (.malformedStr s "duplicate_key", r2)
  else if cat == 1 then
    let pool : Array String := #[
      "[a]\nx = 1\n[a]\ny = 2\n",
      "a.b = 1\n[a]\nc = 2\n",
      "[a]\nb.c = 1\n[a.b]\nd = 2\n",
      "[parent.a.b]\nx = 1\n[parent]\na.c = 2\n[parent.a]\nd = 3\n",
      "[parent.a]\nx = 1\n[parent]\na.y = 2\n",
      "[a]\nx = 1\n[[a]]\ny = 2\n",
      "[[a]]\nx = 1\n[a]\ny = 2\n",
      "a = [1, 2]\n[[a]]\nx = 3\n",
      "a = [{}]\n[[a]]\nx = 1\n",
      "a = 1\n[a]\nx = 2\n"
    ]
    let (s, r2) := r1.choose pool "[a]\nx = 1\n[a]\ny = 2\n"
    (.malformedStr s "redefined_table", r2)
  else if cat == 2 then
    let pool : Array String := #[
      "t = { a = 1 }\nt.b = 2\n",
      "t = { a = 1 }\n[t]\nb = 2\n",
      "t = { a.b = 1 }\n[t.c]\nx = 2\n",
      "t = { a = {} }\nt.a.b = 1\n",
      "t = { a = 1 }\n[[t]]\nb = 2\n"
    ]
    let (s, r2) := r1.choose pool "t = { a = 1 }\nt.b = 2\n"
    (.malformedStr s "immutable_inline_table", r2)
  else if cat == 3 then
    let ctrlPool : Array Char := #[
      '\x00', '\x01', '\x07', '\x08', '\x0b', '\x0c', '\x0e', '\x1f', '\x7f'
    ]
    let (sub, r2) := r1.nextNat 5
    if sub == 0 then
      let (ch, r3) := r2.choose ctrlPool '\x00'
      (.malformedStr ("s = \"pre" ++ String.singleton ch ++ "post\"\n") "control_or_bare_cr", r3)
    else if sub == 1 then
      let (ch, r3) := r2.choose ctrlPool '\x7f'
      (.malformedStr ("s = 'pre" ++ String.singleton ch ++ "post'\n") "control_or_bare_cr", r3)
    else if sub == 2 then
      let (ch, r3) := r2.choose ctrlPool '\x01'
      (.malformedStr ("a = 1 # bad" ++ String.singleton ch ++ "comment\n") "control_or_bare_cr", r3)
    else if sub == 3 then
      (.malformedStr "s = \"bare\rcr\"\n" "control_or_bare_cr", r2)
    else
      (.malformedStr "a = 1 # comment\rb = 2\n" "control_or_bare_cr", r2)
  else if cat == 4 then
    let pool : Array String := #[
      "s = \"\\uD800\"\n",
      "s = \"\\uDBFF\"\n",
      "s = \"\\uDC00\"\n",
      "s = \"\\uDFFF\"\n",
      "s = \"\\U00D80000\"\n",
      "s = \"\\U00110000\"\n",
      "s = \"\\UFFFFFFFF\"\n",
      "s = \"\\x41\"\n",
      "s = \"\\a\"\n",
      "s = \"\\v\"\n",
      "s = \"\\0\"\n",
      "s = \"\\'\"\n",
      "s = \"\\u123\"\n",
      "s = \"\\u123g\"\n",
      "s = \"\\U1234\"\n",
      "s = \"\"\"bad \\q esc\"\"\"\n"
    ]
    let (s, r2) := r1.choose pool "s = \"\\uD800\"\n"
    (.malformedStr s "bad_escape_or_surrogate", r2)
  else if cat == 5 then
    let pool : Array String := #[
      "s = \"unclosed",
      "s = 'unclosed",
      "s = \"\"\"unclosed",
      "s = '''unclosed",
      "s = \"line\nbreak\"\n",
      "s = 'line\nbreak'\n",
      "s = \"\"\"\"\"\"\"\"\"\n",
      "s = '''''''''\n",
      "a = [1, 2",
      "a = { x = 1",
      "[header\na = 1\n",
      "[[aot]\na = 1\n",
      "[]\n",
      "[[]]\n"
    ]
    let (s, r2) := r1.choose pool "s = \"unclosed"
    (.malformedStr s "unclosed_string_or_bracket", r2)
  else if cat == 6 then
    let pool : Array String := #[
      "i = 01\n", "i = -01\n", "i = +00\n", "i = 0_1\n",
      "i = 0X1\n", "i = 0O7\n", "i = 0B1\n",
      "i = +0x1\n", "i = -0x1\n", "i = +0o7\n", "i = -0b1\n",
      "i = 0x\n", "i = 0x_1\n", "i = 1__2\n", "i = 1_\n", "i = _1\n",
      "f = .5\n", "f = -.5\n", "f = 1.\n", "f = 1.e2\n",
      "f = 1._2\n", "f = 1_.2\n", "f = 1e\n", "f = 1e+\n", "f = 1e_2\n",
      "f = NaN\n", "f = Inf\n", "f = Infinity\n", "f = -Infinity\n",
      "x = 0x1.2\n", "x = 0x1p2\n"
    ]
    let (s, r2) := r1.choose pool "i = 01\n"
    (.malformedStr s "leading_zero_or_bad_num", r2)
  else if cat == 7 then
    let pool : Array String := #[
      "d = 2021-02-29\n",
      "d = 2024-02-30\n",
      "d = 2024-04-31\n",
      "d = 2024-00-01\n",
      "d = 2024-13-01\n",
      "d = 2024-01-00\n",
      "d = 2024-01-32\n",
      "d = 0000-02-30\n",
      "t = 24:00:00\n",
      "t = 12:60:00\n",
      "t = 12:00:60\n",
      "t = 12:00:00.\n",
      "d = 2024-01-01T00:00:00+24:00\n",
      "d = 2024-01-01T00:00:00-24:00\n",
      "d = 2024-01-01T00:00:00+00:60\n",
      "d = 2024-01-01  00:00:00\n",
      "d = 2024-01-01\t00:00:00\n",
      "d = 2024-01-01X00:00:00\n"
    ]
    let (s, r2) := r1.choose pool "d = 2024-02-30\n"
    (.malformedStr s "invalid_datetime", r2)
  else if cat == 8 then
    let pool : Array String := #[
      "t = { a = 1, }\n",
      "t = { , }\n",
      "t = {\na = 1\n}\n",
      "t = { a = 1,\nb = 2 }\n",
      "t = { a = 1\n}\n",
      "t = { a }\n",
      "t = { = 1 }\n",
      "t = { a = 1 b = 2 }\n"
    ]
    let (s, r2) := r1.choose pool "t = { a = 1, }\n"
    (.malformedStr s "inline_table_syntax", r2)
  else
    let pool : Array String := #[
      "a = 1 b = 2\n",
      "[t] x = 1\n",
      "[[t]] [u]\n",
      "= 1\n",
      "a =\n",
      "a =\n1\n",
      "\"\"\"key\"\"\" = 1\n",
      "'''key''' = 1\n",
      "café = 1\n",
      "a..b = 1\n",
      ".a = 1\n",
      "a. = 1\n",
      "\ufeffa = 1\n"
    ]
    let (s, r2) := r1.choose pool "a = 1 b = 2\n"
    (.malformedStr s "trailing_garbage", r2)

private def genInt64OverflowCase (r : Rng) : TomlFuzzCase × Rng :=
  let (kind, r1) := r.nextNat 6
  let (lit, r2) :=
    if kind == 0 then ("9223372036854775808", r1)
    else if kind == 1 then ("-9223372036854775809", r1)
    else if kind == 2 then
      let (extra, rn) := r1.nextRange 1 999999999
      ("+" ++ toString (9223372036854775807 + extra), rn)
    else if kind == 3 then
      let pool : Array String := #[
        "0x8000_0000_0000_0000", "0xffff_ffff_ffff_ffff", "0x1_0000_0000_0000_0000"
      ]
      r1.choose pool "0x8000_0000_0000_0000"
    else if kind == 4 then
      ("0o1000000000000000000000", r1)
    else
      ("0b1" ++ String.ofList (List.replicate 63 '0'), r1)
  let (wrapMode, r3) := r2.nextNat 3
  let doc :=
    if wrapMode == 0 then s!"over = {lit}\n"
    else if wrapMode == 1 then s!"xs = [1, {lit}, 2]\n"
    else s!"tbl = \{ ok = true, big = {lit} }\n"
  (.int64Overflow doc true, r3)

private def genCodecAccessorCase (r : Rng) : TomlFuzzCase × Rng := Id.run do
  let (doc, _, _, r1) := genTableAndTape false 2 r
  let (b, r2) := r1.nextBool
  let (iv, r3) := r2.nextIntRange (-1000000) 1000000
  let i64 := Int64.ofInt iv
  let (f, _, _, r4) := genFloatAndTape r3
  let (s, _, _, r5) := genStringAndStyle r4
  let (d1, r6) := genValidDate true r5
  let (t1, _, r7) := genValidTimeAndFrac r6
  let (off, _, r8) := genValidOffset r7
  let odt : TomlOffsetDateTime := { dateTime := Std.Time.PlainDateTime.mk d1 t1, offset := off }
  let (d2, r9) := genValidDate true r8
  let (t2, _, r10) := genValidTimeAndFrac r9
  let ldt := Std.Time.PlainDateTime.mk d2 t2
  let (ld, r11) := genValidDate true r10
  let (lt, _, r12) := genValidTimeAndFrac r11
  let (arrLen, r13) := r12.nextRange 0 4
  let mut cur := r13
  let mut xs : Array Int64 := Array.mkEmpty arrLen
  for _ in [0 : arrLen] do
    let (elemI, rn) := cur.nextIntRange (-500) 500
    cur := rn
    xs := xs.push (Int64.ofInt elemI)
  let (k1, _, _, r14) := genKeyAndStyle cur
  let (k2Raw, _, _, r15) := genKeyAndStyle r14
  let k2 := if k2Raw == k1 then k1 ++ "_alt" else k2Raw
  let (pLen, r16) := r15.nextRange 1 3
  let mut curP := r16
  let mut pks : List String := []
  for _ in [0 : pLen] do
    let (pk, _, _, rn) := genKeyAndStyle curP
    curP := rn
    pks := pk :: pks
  return (.codecAndAccessors doc b i64 f s odt ldt ld lt xs k1 k2 pks.reverse, curP)

/-- Draw one randomized `TomlFuzzCase` from `r`. -/
def genTomlFuzzCase (r : Rng) : TomlFuzzCase × Rng :=
  let (pick, r1) := r.nextNat 24
  if pick < 9 then
    let (doc, raw, tags, r2) := genTableAndTape false 2 r1
    (.validRender doc raw tags, r2)
  else if pick == 9 then
    let (dRaw, r2) := genValidDate false r1
    let d0 := Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt 0) dRaw.month dRaw.day
    let (t0, frac?, r3) := genValidTimeAndFrac r2
    let (off, oStyle, r4) := genValidOffset r3
    let odt : TomlOffsetDateTime := { dateTime := Std.Time.PlainDateTime.mk d0 t0, offset := off }
    let doc : TomlTable := #[("y0_date", .localDate d0), ("y0_odt", .offsetDateTime odt)]
    let tape : Model.RenderTape := {
      stmts := [
        .assign "" { firstKey := "y0_date" } " " " " .localDate {},
        .assign "" { firstKey := "y0_odt" } " " " " (.offsetDateTime .upperT oStyle frac?) {}
      ]
    }
    let fTag := if frac?.isSome then ["datetime_frac"] else []
    match Model.render doc tape with
    | some raw =>
      (.validRender doc raw ("year_zero" :: "local_date" :: "offset_datetime" :: "key_bare" :: fTag), r4)
    | none =>
      (.validRender doc (LeanSwe.Toml.format doc) ["year_zero", "local_date", "offset_datetime", "key_bare"], r4)
  else if pick == 10 then
    genDeepNestedTomlCase r1
  else if pick < 18 then
    genMalformedCase r1
  else if pick < 20 then
    genInt64OverflowCase r1
  else
    genCodecAccessorCase r1

private def mkDateClip (y : Int) (m : Std.Time.Month.Ordinal) (d : Std.Time.Day.Ordinal) :
    Std.Time.PlainDate :=
  Std.Time.PlainDate.ofYearMonthDayClip (Std.Time.Year.Offset.ofInt y) m d

private def mkTimeVal (h : Std.Time.Hour.Ordinal) (m : Std.Time.Minute.Ordinal)
    (s : Std.Time.Second.Ordinal true) (ns : Std.Time.Nanosecond.Ordinal := 0) :
    Std.Time.PlainTime :=
  Std.Time.PlainTime.mk h m s ns

private def mkOffSec (sec : Int) : Std.Time.TimeZone.Offset :=
  Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt sec)

/-- Deterministic smoke corpus exercising every TOML 1.0 value kind, header, trivia, divergence, and error path. -/
def smokeCases : Array TomlFuzzCase := Id.run do
  let mut out : Array TomlFuzzCase := #[]
  out := out.push (.validRender #[] "" [])
  out := out.push (.validRender #[] "# only comment\r\n  \t \r\n# final" ["comments_blank_lines", "crlf"])
  out := out.push (.validRender
    #[("bare_1", .int 1), ("quoted key", .int 2), ("lit.key", .int 3),
      ("a", .table #[("b", .table #[("c", .string "deep")])]), ("1234", .bool true), ("flag", .bool false)]
    ("bare_1 = 1\n\"quoted key\" = 2\n'lit.key' = 3\na . b . c = \"deep\"\n1234 = true\nflag = false")
    ["key_bare", "key_basic", "key_literal", "key_dotted", "int_dec", "str_basic", "bool_true", "bool_false",
      "no_trailing_newline"])
  out := out.push (.validRender
    #[("esc", .string "\x08\t\n\x0c\r\"\\A🚀"),
      ("lit", .string "C:\\raw\\path"),
      ("mlb", .string "alphaBeta"),
      ("mll", .string "line1\n'quote'")]
    ("esc = \"\\b\\t\\n\\f\\r\\\"\\\\\\u0041\\U0001F680\"\r\n" ++
     "lit = 'C:\\raw\\path'\r\n" ++
     "mlb = \"\"\"\r\nalpha\\\r\n   Beta\"\"\"\r\n" ++
     "mll = '''\r\nline1\r\n'quote''''\r\n")
    ["key_bare", "str_basic", "str_escape", "str_literal", "str_multiline_basic", "str_line_trim",
      "str_multiline_literal", "crlf"])
  out := out.push (.validRender
    #[("dec", .int 1000), ("imin", .int (-9223372036854775808)), ("imax", .int 9223372036854775807),
      ("hex", .int 0xdeadbeef), ("oct", .int 0o755), ("bin", .int 0b10100101),
      ("ffrac", .float (-0.0)), ("fexp", .float 5e22), ("finf", .float Float.inf), ("fnan", .float Float.nan)]
    ("dec = +1_000\nimin = -9223372036854775808\nimax = 9223372036854775807\n" ++
     "hex = 0xdead_BEEF\noct = 0o7_5_5\nbin = 0b1010_0101\n" ++
     "ffrac = -0.0\nfexp = 5e+22\nfinf = +inf\nfnan = -nan\n")
    ["key_bare", "int_dec", "int_hex", "int_oct", "int_bin", "int_underscore",
      "float_frac", "float_exp", "float_special"])
  let d79 := mkDateClip 1979 5 27
  let dLeap := mkDateClip 2000 2 29
  out := out.push (.validRender
    #[("odt1", .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d79 (mkTimeVal 7 32 0 123456789),
                                  offset := mkOffSec (-25200) }),
      ("odt2", .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d79 (mkTimeVal 7 32 0 0),
                                  offset := mkOffSec 0 }),
      ("ldt", .localDateTime (Std.Time.PlainDateTime.mk d79 (mkTimeVal 7 32 0 500000000))),
      ("ld", .localDate dLeap),
      ("lt", .localTime (mkTimeVal 23 59 59 999999999))]
    ("odt1 = 1979-05-27 07:32:00.123456789-07:00\n" ++
     "odt2 = 1979-05-27t07:32:00-00:00\n" ++
     "ldt = 1979-05-27T07:32:00.5\n" ++
     "ld = 2000-02-29\n" ++
     "lt = 23:59:59.999999999999\n")
    ["key_bare", "offset_datetime", "local_datetime", "local_date", "local_time", "datetime_frac"])
  let d0Leap := mkDateClip 0 2 29
  out := out.push (.validRender
    #[("0000-01-01", .string "0000-02-30"),
      ("d0", .localDate d0Leap),
      ("odt0", .offsetDateTime { dateTime := Std.Time.PlainDateTime.mk d0Leap (mkTimeVal 12 0 0 123456789),
                                  offset := mkOffSec 0 })]
    ("0000-01-01 = \"0000-02-30\" # 0000-02-30\n" ++
     "d0 = 0000-02-29\nodt0 = 0000-02-29T12:00:00.123456789Z\n")
    ["key_bare", "str_basic", "comments_blank_lines", "local_date", "offset_datetime", "datetime_frac", "year_zero"])
  out := out.push (.validRender
    #[("empty_arr", .array #[]),
      ("nested_arr", .array #[.array #[.int 1, .int 2], .array #[.string "x"]]),
      ("empty_inl", .table #[]),
      ("inl", .table #[("x", .int 1), ("y", .table #[("z", .bool true)])]),
      ("sec", .table #[("sub", .table #[("k", .int 9)]), ("top", .int 4)]),
      ("items", .array #[.table #[("id", .int 1)], .table #[("id", .int 2)]])]
    ("# containers\nempty_arr = [ # inner\n]\nnested_arr = [ [1, 2, ], [\"x\"], ]\n" ++
     "empty_inl = { }\ninl = { x = 1, y.z = true }\n\n" ++
     "[sec.sub]\nk = 9\n[sec]\ntop = 4\n" ++
     "[[items]]\nid = 1\n[[items]]\nid = 2\n")
    ["key_bare", "key_dotted", "array_empty", "array_nested_trailing", "inline_table_empty",
      "inline_table_nonempty", "table_header", "aot_header", "comments_blank_lines", "int_dec",
      "str_basic", "bool_true"])
  let (deepCase, _) := genDeepNestedTomlCase (Rng.seed 0x42)
  out := out.push deepCase
  let badCorpus : Array (String × String) := #[
    ("a = 1\na = 2\n", "duplicate_key"),
    ("a = 1\n\"a\" = 2\n", "duplicate_key"),
    ("[t]\nx = 1\n[t]\ny = 2\n", "redefined_table"),
    ("a.b = 1\n[a]\nc = 2\n", "redefined_table"),
    ("t = { a = 1 }\nt.b = 2\n", "immutable_inline_table"),
    ("t = { a = 1 }\n[t]\nb = 2\n", "immutable_inline_table"),
    ("s = \"bad\x00nul\"\n", "control_or_bare_cr"),
    ("a = 1\rb = 2\n", "control_or_bare_cr"),
    ("s = \"\\uD800\"\n", "bad_escape_or_surrogate"),
    ("s = \"\\x41\"\n", "bad_escape_or_surrogate"),
    ("s = \"unclosed", "unclosed_string_or_bracket"),
    ("a = [1, 2", "unclosed_string_or_bracket"),
    ("i = 01\n", "leading_zero_or_bad_num"),
    ("i = +0x1\n", "leading_zero_or_bad_num"),
    ("f = .5\n", "leading_zero_or_bad_num"),
    ("d = 2024-02-30\n", "invalid_datetime"),
    ("d = 0000-02-30\n", "invalid_datetime"),
    ("t = 12:00:60\n", "invalid_datetime"),
    ("t = { a = 1, }\n", "inline_table_syntax"),
    ("t = {\na = 1\n}\n", "inline_table_syntax"),
    ("a = 1 b = 2\n", "trailing_garbage"),
    ("café = 1\n", "trailing_garbage")
  ]
  for (raw, tg) in badCorpus do
    out := out.push (.malformedStr raw tg)
  out := out.push (.int64Overflow "i = 9223372036854775808\n" true)
  out := out.push (.int64Overflow "i = -9223372036854775809\n" true)
  out := out.push (.int64Overflow "i = 0x8000_0000_0000_0000\n" true)
  let sampleDoc : TomlTable := #[
    ("port", .int 8080),
    ("db", .table #[("host", .string "localhost")])
  ]
  let sampleOdt : TomlOffsetDateTime := {
    dateTime := Std.Time.PlainDateTime.mk d79 (mkTimeVal 7 32 0 123456789)
    offset := mkOffSec 3600
  }
  out := out.push (.codecAndAccessors sampleDoc true (-42) (-0.0) "hello\n🚀"
    sampleOdt (Std.Time.PlainDateTime.mk d79 (mkTimeVal 8 0 0 0)) d79 (mkTimeVal 9 15 30 500)
    #[1, -2, 3] "port" "absent" ["db", "host"])
  return out

end Fuzz.Toml

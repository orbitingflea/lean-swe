import Fuzz.Common.Rng
import Fuzz.Json.Gen
import LeanSwe.Json.Interface
import LeanSwe.Json.Model

namespace Fuzz.Json

open Fuzz.Common
open LeanSwe.Json

private def genMalformedCase (r : Rng) : JsonFuzzCase × Rng :=
  let (cat, r1) := r.nextNat 11
  if cat == 0 then
    let pool : Array String := #[
      "{\"a\":1,\"a\":2}",
      "{\"a\":1,\"\\u0061\":2}",
      "{\"🚀\":true,\"\\ud83d\\ude80\":false}",
      "[{\"x\":0,\"y\":1,\"x\":2}]",
      "{\"\":\"first\",\"\":\"second\"}"
    ]
    let (s, r2) := r1.choose pool "{\"a\":1,\"a\":2}"
    (.malformedStr s "duplicate_key", r2)
  else if cat == 1 then
    let (hiOff, r2) := r1.nextRange 0 0x3ff
    let hiHex := String.ofList (Model.renderHex4 {} (0xd800 + hiOff))
    let (suffix, r3) := r2.choose #["", "xyz", "\\n", "\\u0041"] ""
    (.malformedStr ("\"" ++ hiHex ++ suffix ++ "\"") "lone_high_surrogate", r3)
  else if cat == 2 then
    let (loOff, r2) := r1.nextRange 0 0x3ff
    let loHex := String.ofList (Model.renderHex4 {} (0xdc00 + loOff))
    let (prefixStr, r3) := r2.choose #["", "abc", "\\u0041"] ""
    (.malformedStr ("\"" ++ prefixStr ++ loHex ++ "\"") "lone_low_surrogate", r3)
  else if cat == 3 then
    let pool : Array String := #[
      "\"\\ud800\\ud800\"",
      "\"\\udbff\\udbff\"",
      "\"\\ud83d\\u0041\"",
      "\"\\udc00\\ud800\"",
      "\"\\ud83d\\ude8\""
    ]
    let (s, r2) := r1.choose pool "\"\\ud800\\ud800\""
    (.malformedStr s "bad_surrogate_pair", r2)
  else if cat == 4 then
    let (ctrlCode, r2) := r1.nextRange 0 0x1f
    let ch := Char.ofNat ctrlCode
    (.malformedStr ("\"pre" ++ String.singleton ch ++ "post\"") "control_char", r2)
  else if cat == 5 then
    let pool : Array String := #[
      "\"\\'\"", "\"\\x41\"", "\"\\a\"", "\"\\v\"", "\"\\0\"",
      "\"\\u12\"", "\"\\u123g\"", "\"\\u\"", "\"\\\"", "\"unclosed\\"
    ]
    let (s, r2) := r1.choose pool "\"\\x41\""
    (.malformedStr s "bad_escape", r2)
  else if cat == 6 then
    let pool : Array String := #[
      "+1", "+0", "01", "-01", "00", "-00.5", ".5", "-.5", "1.", "-1.",
      "1.e2", "1e", "1E", "1e+", "1e-", "-", "0x10", "1_000", "1.2.3"
    ]
    let (s, r2) := r1.choose pool "01"
    (.malformedStr s "bad_number", r2)
  else if cat == 7 then
    let pool : Array String := #[
      "NaN", "-NaN", "Infinity", "-Infinity", "+Infinity",
      "[NaN]", "{\"k\":Infinity}", "undefined", "True", "False", "NULL"
    ]
    let (s, r2) := r1.choose pool "NaN"
    (.malformedStr s "nonfinite_constant", r2)
  else if cat == 8 then
    let (sub, r2) := r1.nextNat 3
    if sub == 0 then
      (.malformedStr "1e100001" "limit_exceeded", r2)
    else if sub == 1 then
      (.malformedStr "-1e-100001" "limit_exceeded", r2)
    else
      let overFrac := "0." ++ String.ofList (List.replicate 100001 '5')
      (.malformedStr overFrac "limit_exceeded", r2)
  else if cat == 9 then
    let pool : Array String := #[
      "", "   \t\r\n ", "{", "}", "[", "]", "[1,]", "{\"a\":1,}",
      "{\"a\" 1}", "{a:1}", "[1 2]", "{\"a\":}", "\"unterminated", "'single'"
    ]
    let (s, r2) := r1.choose pool "[1,]"
    (.malformedStr s "container_syntax", r2)
  else
    let pool : Array String := #[
      "true false", "1 2", "{\"a\":1}{\"b\":2}", "[]0", "null,",
      "\ufeff1", "\u00a0true", "true\x0c", "[\x0b1]"
    ]
    let (s, r2) := r1.choose pool "true false"
    (.malformedStr s "trailing_tokens", r2)

private def genInvalidUtf8Case (r : Rng) : JsonFuzzCase × Rng :=
  let badSeqs : Array ByteArray := #[
    ByteArray.mk #[0x22, 0xff, 0x22],
    ByteArray.mk #[0x22, 0x80, 0x22],
    ByteArray.mk #[0x22, 0xc0, 0x80, 0x22],
    ByteArray.mk #[0x22, 0xe2, 0x82, 0x22],
    ByteArray.mk #[0x22, 0xf0, 0x9f, 0x9a, 0x22],
    ByteArray.mk #[0x22, 0xed, 0xa0, 0x80, 0x22],
    ByteArray.mk #[0x22, 0xed, 0xbf, 0xbf, 0x22],
    ByteArray.mk #[0x7b, 0x22, 0x6b, 0x22, 0x3a, 0x22, 0xf4, 0x90, 0x80, 0x80, 0x22, 0x7d],
    ByteArray.mk #[0xff, 0x31]
  ]
  let (bs, r1) := r.choose badSeqs (ByteArray.mk #[0x22, 0xff, 0x22])
  (.invalidUtf8 bs "invalid_utf8", r1)

private def genCodecAccessorCase (r : Rng) : JsonFuzzCase × Rng := Id.run do
  let (doc, r1) := genAstOnly 3 r
  let (b, r2) := r1.nextBool
  let (n, r3) := r2.nextRange 0 1000000
  let (i, r4) := r3.nextIntRange (-1000000) 1000000
  let (s, _, _, r5) := genStyledString r4 8
  let (hasOpt, r6) := r5.nextBool
  let (optV, r7) := if hasOpt then
    let (v, rn) := r6.nextIntRange (-500) 500
    (some v, rn)
  else (none, r6)
  let (arrLen, r8) := r7.nextRange 0 4
  let mut cur := r8
  let mut xs : Array String := Array.mkEmpty arrLen
  for _ in [0 : arrLen] do
    let (item, _, _, rn) := genStyledString cur 5
    cur := rn
    xs := xs.push item
  let (k1, _, _, r9) := genStyledString cur 5
  let (k2Raw, _, _, r10) := genStyledString r9 5
  let k2 := if k2Raw == k1 then k1 ++ "_alt" else k2Raw
  let (pLen, r11) := r10.nextRange 0 3
  let mut curP := r11
  let mut pks : List String := []
  for _ in [0 : pLen] do
    let (pk, _, _, rn) := genStyledString curP 4
    curP := rn
    pks := pk :: pks
  return (.codecAndAccessors doc b n i s optV xs k1 k2 pks.reverse, curP)

/-- Draw one randomized `JsonFuzzCase` from `r`. -/
def genJsonFuzzCase (r : Rng) : JsonFuzzCase × Rng :=
  let (pick, r1) := r.nextNat 20
  if pick < 5 then
    let (doc, r2) := genAstOnly 3 r1
    let (tape, tags, r3) := buildCanonicalTape doc r2
    let (pw, r4) := r3.choose #[0, 1, 10, 24, 40, 80, 120] 80
    let (df, r5) := r4.nextU8
    match Model.render doc tape with
    | some raw =>
      if Model.withinResourceLimitsBool tape then
        (.validRender doc raw pw df tags, r5)
      else
        (.validRender doc (LeanSwe.Json.compress doc) pw df tags, r5)
    | none => (.validRender doc (LeanSwe.Json.compress doc) pw df tags, r5)
  else if pick < 10 then
    let (doc, tape, tags, r2) := genJsonAndTape 3 r1
    let (pw, r3) := r2.choose #[0, 8, 30, 80, 160] 80
    let (df, r4) := r3.nextU8
    match Model.render doc tape with
    | some raw =>
      if Model.withinResourceLimitsBool tape then
        (.validRender doc raw pw df tags, r4)
      else
        (.validRender doc (LeanSwe.Json.compress doc) pw df tags, r4)
    | none => (.validRender doc (LeanSwe.Json.compress doc) pw df tags, r4)
  else if pick == 10 then
    genDeepNestedCase r1
  else if pick < 16 then
    genMalformedCase r1
  else if pick == 16 then
    genInvalidUtf8Case r1
  else
    genCodecAccessorCase r1

/-- Deterministic smoke corpus exercising every RFC 8259 value kind, escape, boundary, and error path. -/
def smokeCases : Array JsonFuzzCase := Id.run do
  let mut out : Array JsonFuzzCase := #[]
  out := out.push (.validRender .null " \t\nnull\r\n " 80 0 ["null", "whitespace"])
  out := out.push (.validRender (.bool true) "true" 80 1 ["bool_true"])
  out := out.push (.validRender (.bool false) "\n false \t" 80 2 ["bool_false", "whitespace"])
  out := out.push (.validRender (.num ⟨0, 0⟩) "-0.00" 80 3 ["num_neg_zero", "num_frac"])
  out := out.push (.validRender (.num ⟨-42, 0⟩) "-42" 80 4 ["num_int"])
  out := out.push (.validRender (.num ⟨314159, 5⟩) "3.14159" 80 5 ["num_frac"])
  out := out.push (.validRender (.num ⟨15, 4⟩) "1.5e-003" 80 6 ["num_exp"])
  out := out.push (.validRender (.num ⟨20000, 0⟩) "2E+4" 80 7 ["num_exp"])
  let bigInt : Int := 123456789012345678901234567890123456789
  out := out.push (.validRender (.num ⟨bigInt, 0⟩) "123456789012345678901234567890123456789" 80 8 ["num_big", "num_int"])
  out := out.push (.validRender (.num ⟨1, 100000⟩) "1e-100000" 80 0 ["num_exp", "limit_boundary"])
  let exactFracStr := "0." ++ String.ofList (List.replicate 99999 '0') ++ "1"
  out := out.push (.validRender (.num ⟨1, 100000⟩) exactFracStr 80 0 ["num_frac", "limit_boundary"])
  out := out.push (.validRender (.str "hello") "\"hello\"" 80 9 ["str_ascii"])
  out := out.push (.validRender (.str "\"\\/\x08\x0c\n\r\t") "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" 80 10 ["short_escape", "str_ascii"])
  out := out.push (.validRender (.str "\x00\x1fαΩ") "\"\\u0000\\u001f\\u03b1\\u03A9\"" 80 11 ["unicode_hex", "str_unicode"])
  out := out.push (.validRender (.str "🚀𐍈") "\"\\ud83d\\ude80\\uD800\\uDF48\"" 80 13 ["surrogate_pair", "str_unicode"])
  out := out.push (.validRender (.arr #[]) "[ \n ]" 80 16 ["arr_empty", "whitespace"])
  out := out.push (.validRender (.obj ∅) "{ \t }" 80 17 ["obj_empty", "whitespace"])
  let sampleObj := Lean.Json.mkObj [
    ("alpha", .arr #[.num ⟨1, 0⟩, .str "line1\nline2", .bool true, .null]),
    ("🚀", Lean.Json.mkObj [("nested", .num ⟨-25, 2⟩)])
  ]
  out := out.push (.validRender sampleObj (LeanSwe.Json.compress sampleObj) 12 5 ["obj_nonempty", "arr_nonempty", "str_unicode"])
  out := out.push (.validRender sampleObj (LeanSwe.Json.pretty sampleObj 200) 200 18 ["obj_nonempty", "arr_nonempty", "whitespace"])
  let mut deepDoc : Lean.Json := Lean.Json.mkObj [("leaf", .str "ok")]
  for idx in [0 : 32] do
    deepDoc := Lean.Json.mkObj [(s!"k{idx}", .arr #[deepDoc, .num (Lean.JsonNumber.fromInt (Int.ofNat idx))])]
  out := out.push (.validRender deepDoc (LeanSwe.Json.compress deepDoc) 24 1 ["deep_nested", "obj_nonempty", "arr_nonempty"])
  let badCorpus : Array (String × String) := #[
    ("{\"a\":1,\"a\":2}", "duplicate_key"),
    ("{\"🚀\":1,\"\\ud83d\\ude80\":2}", "duplicate_key"),
    ("\"\\ud800\"", "lone_high_surrogate"),
    ("\"\\udfff\"", "lone_low_surrogate"),
    ("\"\\ud800\\u0041\"", "bad_surrogate_pair"),
    ("\"\\udc00\\ud800\"", "bad_surrogate_pair"),
    ("\"raw\x00nul\"", "control_char"),
    ("\"raw\ntext\"", "control_char"),
    ("\"\\x41\"", "bad_escape"),
    ("\"\\u123g\"", "bad_escape"),
    ("01", "bad_number"),
    ("+1", "bad_number"),
    ("1.", "bad_number"),
    ("NaN", "nonfinite_constant"),
    ("Infinity", "nonfinite_constant"),
    ("-Infinity", "nonfinite_constant"),
    ("1e100001", "limit_exceeded"),
    ("1e-100001", "limit_exceeded"),
    ("0." ++ String.ofList (List.replicate 100001 '1'), "limit_exceeded"),
    ("[1,]", "container_syntax"),
    ("{\"a\":1,}", "container_syntax"),
    ("true false", "trailing_tokens"),
    ("\ufeff1", "trailing_tokens")
  ]
  for (raw, tag) in badCorpus do
    out := out.push (.malformedStr raw tag)
  out := out.push (.invalidUtf8 (ByteArray.mk #[0x22, 0xff, 0x22]) "invalid_utf8")
  out := out.push (.invalidUtf8 (ByteArray.mk #[0x22, 0xed, 0xa0, 0x80, 0x22]) "invalid_utf8")
  out := out.push (.invalidUtf8 (ByteArray.mk #[0x22, 0xc0, 0x80, 0x22]) "invalid_utf8")
  out := out.push (.codecAndAccessors sampleObj true 42 (-17) "hello\n🚀" (some (-9)) #["a", "b"] "alpha" "missing" ["🚀", "nested"])
  out := out.push (.codecAndAccessors (.arr #[.num ⟨1, 0⟩]) false 0 0 "" none #[] "k1" "k2" [])
  return out

end Fuzz.Json

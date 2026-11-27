import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.SpecTests.Cases
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model
import LeanSwe.NumParse.Model.Obeys

namespace LeanSwe.Toml

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.NumParse.Model

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
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
  let pair ← nondet (TomlTable × Model.RenderTape)
  match Model.render pair.1 pair.2 with
  | none => assume False
  | some txt =>
    match api.parse txt with
    | .error _ => NondetTest.assert False
    | .ok parsed => NondetTest.assert (Model.TomlTableEquiv pair.1 parsed)

/-- Formatting any `WellFormedTable` produces valid TOML text that parses back `TomlTableEquiv` to the input. -/
def test_toml_format_validAndRoundTrip
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
  let doc ← nondet TomlTable
  assume (Model.WellFormedTable doc)
  let txt := api.format doc
  match api.parse txt with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (Model.TomlTableEquiv doc parsed)

/-- Keys, dotted keys, statement boundaries, and 4-state table provenance conform to TOML 1.0. -/
def test_toml_keysAndProvenance_conformsToSpec
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
  keyProvenanceOkCases.forM (checkParseEquiv api)
  keyProvenanceErrCases.forM (checkParseErrorKind api)

/-- Inline tables, arrays, and `[[array_of_tables]]` rules conform to TOML 1.0. -/
def test_toml_inlineTablesAndAot_conformsToSpec
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
  inlineAotOkCases.forM (checkParseEquiv api)
  inlineAotErrCases.forM (checkParseErrorKind api)

/-- String escapes, multiline whitespace/quote boundaries, CRLF normalization, and control rejections conform to TOML 1.0. -/
def test_toml_stringsAndControls_conformsToSpec
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
  stringOkCases.forM (checkParseEquiv api)
  stringErrCases.forM (checkParseErrorKind api)

/-- Integer/float delegation (`NumParse`), `0X` rejection, overflow classification, and RFC 3339 datetimes conform to TOML 1.0. -/
def test_toml_numbersAndDatetimes_conformsToSpec
    {runner} [NondetTest runner] (mkApi : LeanSwe.NumParse.NumParseApi → TomlApi)
    (num : LeanSwe.NumParse.NumParseApi) : runner Unit := do
  assume (LeanSwe.NumParse.Model.ObeysApi num)
  let api := mkApi num
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

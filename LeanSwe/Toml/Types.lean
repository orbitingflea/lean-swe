import Std.Time

namespace LeanSwe.Toml

/-- Offset-aware RFC 3339 date-time value preserving the timezone offset in seconds. -/
structure TomlOffsetDateTime where
  /-- Local date and time components. -/
  dateTime : Std.Time.PlainDateTime
  /-- Signed offset from UTC in seconds (`Z`, `z`, `+00:00`, and `-00:00` normalize to `0`). -/
  offset : Std.Time.TimeZone.Offset
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Classification of TOML parsing, validation, navigation, and decoding failures. -/
inductive TomlErrorKind where
  /-- Input text violated TOML 1.0 syntax or numeric/datetime grammar. -/
  | parseError
  /-- Key was defined more than once in the same table or extended a non-table value. -/
  | duplicateKey
  /-- Table or array-of-tables header attempted an invalid reopening or incompatible redefinition. -/
  | redefinedTable
  /-- Statement attempted to modify or traverse a closed inline table `{ ... }`. -/
  | immutableInlineTable
  /-- Input contained a disallowed control character, bare `\r`, or invalid `\u`/`\U` scalar value. -/
  | invalidUtf8OrControl
  /-- Integer literal fell outside signed 64-bit bounds `[-2^63, 2^63 - 1]`. -/
  | numericOverflow
  /-- Expected table field was absent during lookup. -/
  | missingField
  /-- Value did not match the expected container shape (`table` or `array`). -/
  | typeMismatch
  /-- `FromToml` decoding failed on a `TomlValue`. -/
  | decodeError
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Toml` parsing, navigation, and decoding operations. -/
structure TomlError where
  /-- Machine-checkable error category. -/
  kind : TomlErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  /-- Optional 1-based source line where the error occurred. -/
  line : Option Nat := none
  /-- Optional 1-based source column where the error occurred. -/
  col : Option Nat := none
  /-- Optional key name or dot-separated key path where the error occurred. -/
  path : Option String := none
  deriving Repr, BEq, DecidableEq

/-- TOML 1.0 abstract syntax tree value. -/
inductive TomlValue where
  /-- UTF-8 string value. -/
  | string (s : String)
  /-- Signed 64-bit integer value. -/
  | int (n : Int64)
  /-- IEEE-754 binary64 floating-point value. -/
  | float (f : Float)
  /-- Boolean value. -/
  | bool (b : Bool)
  /-- Offset date-time value (`YYYY-MM-DDTHH:MM:SS(.frac)?(Z|±HH:MM)`). -/
  | offsetDateTime (dt : TomlOffsetDateTime)
  /-- Local date-time value (`YYYY-MM-DDTHH:MM:SS(.frac)?`). -/
  | localDateTime (dt : Std.Time.PlainDateTime)
  /-- Local date value (`YYYY-MM-DD`). -/
  | localDate (d : Std.Time.PlainDate)
  /-- Local time value (`HH:MM:SS(.frac)?`). -/
  | localTime (t : Std.Time.PlainTime)
  /-- Ordered array of `TomlValue` elements (possibly heterogeneous). -/
  | array (xs : Array TomlValue)
  /-- Key-value table entries (`Array (String × TomlValue)`). -/
  | table (t : Array (String × TomlValue))
  deriving Repr, Inhabited

/-- Ordered key-value association array representing a TOML table. -/
abbrev TomlTable := Array (String × TomlValue)

/-- Structural boolean equality on `TomlValue` (using `Float.beq` for `.float`). -/
def tomlValueBeq : TomlValue → TomlValue → Bool
  | .string a, .string b => a == b
  | .int a, .int b => a == b
  | .float a, .float b => a == b
  | .bool a, .bool b => a == b
  | .offsetDateTime a, .offsetDateTime b => a == b
  | .localDateTime a, .localDateTime b => a == b
  | .localDate a, .localDate b => a == b
  | .localTime a, .localTime b => a == b
  | .array xs, .array ys => tomlArrayBeq xs.toList ys.toList
  | .table t1, .table t2 => tomlTableListBeq t1.toList t2.toList
  | _, _ => false
where
  /-- Structural boolean equality on `List TomlValue`. -/
  tomlArrayBeq : List TomlValue → List TomlValue → Bool
    | [], [] => true
    | x :: xs, y :: ys => tomlValueBeq x y && tomlArrayBeq xs ys
    | _, _ => false
  /-- Structural boolean equality on `List (String × TomlValue)`. -/
  tomlTableListBeq : List (String × TomlValue) → List (String × TomlValue) → Bool
    | [], [] => true
    | (k1, v1) :: r1, (k2, v2) :: r2 => k1 == k2 && tomlValueBeq v1 v2 && tomlTableListBeq r1 r2
    | _, _ => false

instance : BEq TomlValue where
  beq := tomlValueBeq

/-- Typeclass for decoding a typed Lean value from a `TomlValue`. -/
class FromToml (α : Type) where
  /-- Attempt to decode `TomlValue` into `α`. -/
  fromToml : TomlValue → Except TomlError α

/-- Typeclass for encoding a Lean value into a `TomlValue`. -/
class ToToml (α : Type) where
  /-- Encode `α` as a `TomlValue`. -/
  toToml : α → TomlValue

instance : FromToml TomlValue where
  fromToml v := .ok v

instance : ToToml TomlValue where
  toToml v := v

instance : FromToml String where
  fromToml
    | .string s => .ok s
    | _ => .error { kind := .decodeError, message := "expected TOML string" }

instance : ToToml String where
  toToml s := .string s

instance : FromToml Int64 where
  fromToml
    | .int n => .ok n
    | _ => .error { kind := .decodeError, message := "expected TOML integer" }

instance : ToToml Int64 where
  toToml n := .int n

instance : FromToml Int where
  fromToml
    | .int n => .ok n.toInt
    | _ => .error { kind := .decodeError, message := "expected TOML integer" }

instance : FromToml Nat where
  fromToml
    | .int n =>
      let i := n.toInt
      if 0 ≤ i then .ok i.toNat
      else .error { kind := .decodeError, message := "expected non-negative TOML integer" }
    | _ => .error { kind := .decodeError, message := "expected TOML integer" }

instance : FromToml Float where
  fromToml
    | .float f => .ok f
    | _ => .error { kind := .decodeError, message := "expected TOML float" }

instance : ToToml Float where
  toToml f := .float f

instance : FromToml Bool where
  fromToml
    | .bool b => .ok b
    | _ => .error { kind := .decodeError, message := "expected TOML boolean" }

instance : ToToml Bool where
  toToml b := .bool b

instance : FromToml TomlOffsetDateTime where
  fromToml
    | .offsetDateTime dt => .ok dt
    | _ => .error { kind := .decodeError, message := "expected TOML offset date-time" }

instance : ToToml TomlOffsetDateTime where
  toToml dt := .offsetDateTime dt

instance : FromToml Std.Time.PlainDateTime where
  fromToml
    | .localDateTime dt => .ok dt
    | _ => .error { kind := .decodeError, message := "expected TOML local date-time" }

instance : ToToml Std.Time.PlainDateTime where
  toToml dt := .localDateTime dt

instance : FromToml Std.Time.PlainDate where
  fromToml
    | .localDate d => .ok d
    | _ => .error { kind := .decodeError, message := "expected TOML local date" }

instance : ToToml Std.Time.PlainDate where
  toToml d := .localDate d

instance : FromToml Std.Time.PlainTime where
  fromToml
    | .localTime t => .ok t
    | _ => .error { kind := .decodeError, message := "expected TOML local time" }

instance : ToToml Std.Time.PlainTime where
  toToml t := .localTime t

/-- Decode a list of `TomlValue` elements using `[FromToml α]`. -/
def decodeTomlList {α : Type} [FromToml α] : List TomlValue → Except TomlError (List α)
  | [] => .ok []
  | x :: xs => do
    let v ← FromToml.fromToml x
    let rest ← decodeTomlList xs
    .ok (v :: rest)

instance {α : Type} [FromToml α] : FromToml (Array α) where
  fromToml
    | .array xs => do
      let ys ← decodeTomlList xs.toList
      .ok ys.toArray
    | _ => .error { kind := .decodeError, message := "expected TOML array" }

instance {α : Type} [ToToml α] : ToToml (Array α) where
  toToml xs := .array (xs.map ToToml.toToml)

instance : FromToml TomlTable where
  fromToml
    | .table t => .ok t
    | _ => .error { kind := .decodeError, message := "expected TOML table" }

instance : ToToml TomlTable where
  toToml t := .table t

/-- Public pure operations exported by `LeanSwe.Toml`. -/
structure TomlApi where
  /-- Parse a TOML 1.0 document string into a `TomlTable`. -/
  parse : String → Except TomlError TomlTable
  /-- Render a `TomlTable` as canonical TOML 1.0 text. -/
  format : TomlTable → String
  /-- Decode a `TomlValue` using its `FromToml` instance. -/
  decode : {α : Type} → [FromToml α] → TomlValue → Except TomlError α
  /-- Encode a value into a `TomlValue` using its `ToToml` instance. -/
  encode : {α : Type} → [ToToml α] → α → TomlValue
  /-- Extract the entries from a `.table` value, failing with `.typeMismatch` on non-tables. -/
  getTable : TomlValue → Except TomlError TomlTable
  /-- Extract the elements from an `.array` value, failing with `.typeMismatch` on non-arrays. -/
  getArray : TomlValue → Except TomlError (Array TomlValue)
  /-- Look up required field `key` in a `TomlTable` and decode it as `α`. -/
  getField : {α : Type} → [FromToml α] → TomlTable → String → Except TomlError α
  /-- Look up optional field `key` in a `TomlTable`, returning `none` when absent. -/
  getOptField : {α : Type} → [FromToml α] → TomlTable → String → Except TomlError (Option α)
  /-- Traverse a list of nested table keys and decode the leaf `TomlValue` as `α`. -/
  getPath : {α : Type} → [FromToml α] → TomlTable → List String → Except TomlError α

end LeanSwe.Toml

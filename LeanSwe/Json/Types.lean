import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson

namespace LeanSwe.Json

/-- Classification of JSON parsing, navigation, and decoding failures. -/
inductive JsonErrorKind where
  /-- Input text was not valid RFC 8259 JSON syntax. -/
  | parseError
  /-- Expected object field was absent during lookup. -/
  | missingField
  /-- JSON value did not match the expected container or target shape (e.g. non-object or non-array). -/
  | typeMismatch
  /-- `Lean.FromJson` decoding failed on a JSON value. -/
  | decodeError
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Json` operations. -/
structure JsonError where
  /-- Machine-checkable error category. -/
  kind : JsonErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  /-- Optional JSON field name or dot-separated field path where the failure occurred. -/
  path : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Public pure operations exported by `LeanSwe.Json`. -/
structure JsonApi where
  /-- Parse a JSON text string into `Lean.Json`. -/
  parse : String → Except JsonError Lean.Json
  /-- Render a `Lean.Json` value as compact single-line JSON. -/
  compress : Lean.Json → String
  /-- Render a `Lean.Json` value as formatted JSON targeting `lineWidth` columns. -/
  pretty : Lean.Json → Nat → String
  /-- Decode a `Lean.Json` value using its `Lean.FromJson` instance. -/
  decode : {α : Type} → [Lean.FromJson α] → Lean.Json → Except JsonError α
  /-- Encode a value into `Lean.Json` using its `Lean.ToJson` instance. -/
  encode : {α : Type} → [Lean.ToJson α] → α → Lean.Json
  /-- Extract the key-value map from a JSON object, failing with `.typeMismatch` on non-objects. -/
  getObject : Lean.Json → Except JsonError (Std.TreeMap.Raw String Lean.Json compare)
  /-- Extract the element array from a JSON array, failing with `.typeMismatch` on non-arrays. -/
  getArray : Lean.Json → Except JsonError (Array Lean.Json)
  /-- Look up required field `key` on a JSON object and decode it as `α`. -/
  getField : {α : Type} → [Lean.FromJson α] → Lean.Json → String → Except JsonError α
  /-- Look up optional field `key` on a JSON object, returning `none` when absent or `null`. -/
  getOptField : {α : Type} → [Lean.FromJson α] → Lean.Json → String → Except JsonError (Option α)
  /-- Traverse a list of object keys and decode the leaf JSON value as `α`. -/
  getPath : {α : Type} → [Lean.FromJson α] → Lean.Json → List String → Except JsonError α

end LeanSwe.Json

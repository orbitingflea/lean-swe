import LeanSwe.Json.Types
import LeanSwe.Json.Impl

namespace LeanSwe.Json

/-- Parse a JSON text string into `Lean.Json`. -/
@[inline] def parse (raw : String) : Except JsonError Lean.Json :=
  Internal.parse raw

/-- Render a `Lean.Json` value as compact single-line JSON. -/
@[inline] def compress (j : Lean.Json) : String :=
  Internal.compress j

/-- Render a `Lean.Json` value as formatted JSON targeting `lineWidth` columns. -/
@[inline] def pretty (j : Lean.Json) (lineWidth : Nat := 80) : String :=
  Internal.pretty j lineWidth

/-- Decode a `Lean.Json` value using its `Lean.FromJson` instance. -/
@[inline] def decode {α : Type} [Lean.FromJson α] (j : Lean.Json) : Except JsonError α :=
  Internal.decode j

/-- Encode a value into `Lean.Json` using its `Lean.ToJson` instance. -/
@[inline] def encode {α : Type} [Lean.ToJson α] (a : α) : Lean.Json :=
  Internal.encode a

/-- Extract the key-value map from a JSON object, failing with `.typeMismatch` on non-objects. -/
@[inline] def getObject (j : Lean.Json) : Except JsonError (Std.TreeMap.Raw String Lean.Json compare) :=
  Internal.getObject j

/-- Extract the element array from a JSON array, failing with `.typeMismatch` on non-arrays. -/
@[inline] def getArray (j : Lean.Json) : Except JsonError (Array Lean.Json) :=
  Internal.getArray j

/-- Look up required field `key` on a JSON object and decode it as `α`. -/
@[inline] def getField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) : Except JsonError α :=
  Internal.getField j key

/-- Look up optional field `key` on a JSON object, returning `none` when absent or `null`. -/
@[inline] def getOptField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) :
    Except JsonError (Option α) :=
  Internal.getOptField j key

/-- Traverse a list of object keys and decode the leaf JSON value as `α`. -/
@[inline] def getPath {α : Type} [Lean.FromJson α] (j : Lean.Json) (keys : List String) :
    Except JsonError α :=
  Internal.getPath j keys

/-- Default `JsonApi` record bundling the concrete `LeanSwe.Json` operations for `SpecTests` and `Proofs`. -/
def defaultApi : JsonApi :=
  Internal.defaultApi

end LeanSwe.Json

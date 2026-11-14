import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson
import LeanSwe.Json.Types

namespace LeanSwe.Json.Internal

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def ensureNonEmpty (fallback msg : String) : String :=
  if msg == "" then fallback else msg

/-- Join path segments with `"."`. -/
def joinSegments : List String → String
  | [] => ""
  | [k] => k
  | k :: rest => k ++ "." ++ joinSegments rest

/-- Format a reversed path prefix as an optional dot-separated field path. -/
def joinPath (revPrefix : List String) : Option String :=
  if revPrefix.isEmpty then none else some (joinSegments revPrefix.reverse)

/-- Parse a JSON text string into `Lean.Json`. -/
def parse (raw : String) : Except JsonError Lean.Json :=
  match Lean.Json.parse raw with
  | .ok j => .ok j
  | .error msg =>
    .error { kind := .parseError, message := ensureNonEmpty "JSON parse error" msg, path := none }

/-- Render a `Lean.Json` value as compact single-line JSON. -/
def compress (j : Lean.Json) : String :=
  Lean.Json.compress j

/-- Render a `Lean.Json` value as formatted JSON targeting `lineWidth` columns. -/
def pretty (j : Lean.Json) (lineWidth : Nat := 80) : String :=
  Lean.Json.pretty j lineWidth

/-- Decode a `Lean.Json` value using its `Lean.FromJson` instance. -/
def decode {α : Type} [Lean.FromJson α] (j : Lean.Json) : Except JsonError α :=
  match Lean.fromJson? j with
  | .ok a => .ok a
  | .error msg =>
    .error { kind := .decodeError, message := ensureNonEmpty "JSON decode error" msg, path := none }

/-- Encode a value into `Lean.Json` using its `Lean.ToJson` instance. -/
def encode {α : Type} [Lean.ToJson α] (a : α) : Lean.Json :=
  Lean.toJson a

/-- Extract the key-value map from a JSON object, failing with `.typeMismatch` on non-objects. -/
def getObject (j : Lean.Json) : Except JsonError (Std.TreeMap.Raw String Lean.Json compare) :=
  match j with
  | .obj kvs => .ok kvs
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Extract the element array from a JSON array, failing with `.typeMismatch` on non-arrays. -/
def getArray (j : Lean.Json) : Except JsonError (Array Lean.Json) :=
  match j with
  | .arr xs => .ok xs
  | _ => .error { kind := .typeMismatch, message := "expected JSON array", path := none }

/-- Look up required field `key` on a JSON object and decode it as `α`. -/
def getField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) : Except JsonError α :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | some v =>
      match decode v with
      | .ok a => .ok a
      | .error e => .error { e with path := some key }
    | none => .error { kind := .missingField, message := s!"missing field: {key}", path := some key }
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Look up optional field `key` on a JSON object, returning `none` when absent or `null`. -/
def getOptField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) :
    Except JsonError (Option α) :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | none => .ok none
    | some .null => .ok none
    | some v =>
      match decode v with
      | .ok a => .ok (some a)
      | .error e => .error { e with path := some key }
  | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := none }

/-- Traverse `keys` accumulating `revPrefix` and decode the leaf JSON value. -/
def getPathAux {α : Type} [Lean.FromJson α]
    (revPrefix : List String) (j : Lean.Json) : List String → Except JsonError α
  | [] =>
    match decode j with
    | .ok a => .ok a
    | .error e =>
      if revPrefix.isEmpty then .error e
      else .error { e with path := joinPath revPrefix }
  | key :: rest =>
    match j with
    | .obj kvs =>
      let nextPrefix := key :: revPrefix
      match kvs.get? key with
      | some v => getPathAux nextPrefix v rest
      | none =>
        .error { kind := .missingField, message := s!"missing field: {key}", path := joinPath nextPrefix }
    | _ => .error { kind := .typeMismatch, message := "expected JSON object", path := joinPath revPrefix }

/-- Traverse a list of object keys and decode the leaf JSON value as `α`. -/
def getPath {α : Type} [Lean.FromJson α] (j : Lean.Json) (keys : List String) : Except JsonError α :=
  getPathAux [] j keys

/-- Concrete `JsonApi` record bundling the pure `LeanSwe.Json` operations. -/
def defaultApi : JsonApi :=
  { parse := parse
    compress := compress
    pretty := fun j w => pretty j w
    decode := decode
    encode := encode
    getObject := getObject
    getArray := getArray
    getField := getField
    getOptField := getOptField
    getPath := getPath }

end LeanSwe.Json.Internal

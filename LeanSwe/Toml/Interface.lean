import LeanSwe.Toml.Types
import LeanSwe.Toml.Impl
import LeanSwe.NumParse.Interface

namespace LeanSwe.Toml

/-- Default `TomlApi` record bundling the concrete `LeanSwe.Toml` operations for `SpecTests` and `Proofs`. -/
def defaultApi : TomlApi :=
  Internal.mkApi NumParse.defaultApi

/-- Parse a TOML 1.0 document string into a `TomlTable`. -/
@[inline] def parse (raw : String) : Except TomlError TomlTable :=
  defaultApi.parse raw

/-- Render a `TomlTable` as canonical TOML 1.0 text. -/
@[inline] def format (doc : TomlTable) : String :=
  defaultApi.format doc

/-- Decode a `TomlValue` using its `FromToml` instance. -/
@[inline] def decode {α : Type} [FromToml α] (v : TomlValue) : Except TomlError α :=
  defaultApi.decode v

/-- Encode a value into a `TomlValue` using its `ToToml` instance. -/
@[inline] def encode {α : Type} [ToToml α] (x : α) : TomlValue :=
  defaultApi.encode x

/-- Extract the entries from a `.table` value, failing with `.typeMismatch` on non-tables. -/
@[inline] def getTable (v : TomlValue) : Except TomlError TomlTable :=
  defaultApi.getTable v

/-- Extract the elements from an `.array` value, failing with `.typeMismatch` on non-arrays. -/
@[inline] def getArray (v : TomlValue) : Except TomlError (Array TomlValue) :=
  defaultApi.getArray v

/-- Look up required field `key` in a `TomlTable` and decode it as `α`. -/
@[inline] def getField {α : Type} [FromToml α] (t : TomlTable) (key : String) : Except TomlError α :=
  defaultApi.getField t key

/-- Look up optional field `key` in a `TomlTable`, returning `none` when absent. -/
@[inline] def getOptField {α : Type} [FromToml α] (t : TomlTable) (key : String) :
    Except TomlError (Option α) :=
  defaultApi.getOptField t key

/-- Traverse a list of nested table keys and decode the leaf `TomlValue` as `α`. -/
@[inline] def getPath {α : Type} [FromToml α] (t : TomlTable) (keys : List String) :
    Except TomlError α :=
  defaultApi.getPath t keys

end LeanSwe.Toml

import LeanSwe.Toml.Types
import LeanSwe.Toml.Impl
import LeanSwe.NumParse.Interface

namespace LeanSwe.Toml

/-- Parse a TOML 1.0 document string into a `TomlTable`. -/
@[inline] def parse (raw : String) : Except TomlError TomlTable :=
  Impl.parseWithNum NumParse.defaultApi raw

/-- Render a `TomlTable` as canonical TOML 1.0 text. -/
@[inline] def format (doc : TomlTable) : String :=
  Impl.formatWithNum NumParse.defaultApi doc

/-- Decode a `TomlValue` using its `FromToml` instance. -/
@[inline] def decode {α : Type} [FromToml α] (v : TomlValue) : Except TomlError α :=
  Impl.tomlDecode v

/-- Encode a value into a `TomlValue` using its `ToToml` instance. -/
@[inline] def encode {α : Type} [ToToml α] (x : α) : TomlValue :=
  Impl.tomlEncode x

/-- Extract the entries from a `.table` value, failing with `.typeMismatch` on non-tables. -/
@[inline] def getTable (v : TomlValue) : Except TomlError TomlTable :=
  Impl.tomlGetTable v

/-- Extract the elements from an `.array` value, failing with `.typeMismatch` on non-arrays. -/
@[inline] def getArray (v : TomlValue) : Except TomlError (Array TomlValue) :=
  Impl.tomlGetArray v

/-- Look up required field `key` in a `TomlTable` and decode it as `α`. -/
@[inline] def getField {α : Type} [FromToml α] (t : TomlTable) (key : String) : Except TomlError α :=
  Impl.tomlGetField t key

/-- Look up optional field `key` in a `TomlTable`, returning `none` when absent. -/
@[inline] def getOptField {α : Type} [FromToml α] (t : TomlTable) (key : String) :
    Except TomlError (Option α) :=
  Impl.tomlGetOptField t key

/-- Traverse a list of nested table keys and decode the leaf `TomlValue` as `α`. -/
@[inline] def getPath {α : Type} [FromToml α] (t : TomlTable) (keys : List String) :
    Except TomlError α :=
  Impl.tomlGetPath t keys

/-- Default `TomlApi` record bundling the concrete `LeanSwe.Toml` operations for `SpecTests` and `Proofs`. -/
def defaultApi : TomlApi :=
  Impl.makeTomlApi NumParse.defaultApi

end LeanSwe.Toml

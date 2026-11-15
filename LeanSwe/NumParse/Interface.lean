import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Impl

namespace LeanSwe.NumParse

/-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into an unbounded `Int`. -/
@[inline] def parseInt (s : String) : Except NumParseError Int :=
  Internal.parseInt s

/-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into a signed `Int64`. -/
@[inline] def parseInt64 (s : String) : Except NumParseError Int64 :=
  Internal.parseInt64 s

/-- Format an `Int` as a canonical base-10 decimal string without underscores. -/
@[inline] def formatInt (n : Int) : String :=
  Internal.formatInt n

/-- Parse a TOML 1.0 decimal float or lowercase special literal (`inf`, `-inf`, `nan`) into IEEE-754 binary64 `Float`. -/
@[inline] def parseFloat (s : String) : Except NumParseError Float :=
  Internal.parseFloat s

/-- Format a `Float` into a canonical TOML 1.0 decimal/scientific or lowercase special literal preserving bit identity for non-NaNs. -/
@[inline] def formatFloat (x : Float) : String :=
  Internal.formatFloat x

/-- Default `NumParseApi` record bundling the concrete `LeanSwe.NumParse` operations for `SpecTests` and `Proofs`. -/
def defaultApi : NumParseApi :=
  Internal.defaultApi

end LeanSwe.NumParse

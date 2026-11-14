namespace LeanSwe.NumParse

/-- Classification of integer and floating-point parsing failures. -/
inductive NumParseErrorKind where
  /-- Input string was empty. -/
  | emptyInput
  /-- Input syntax did not form a valid numeric literal. -/
  | invalidSyntax
  /-- A `+` or `-` sign preceded a base-prefixed integer literal (`0x`, `0o`, `0b`). -/
  | invalidSignForBase
  /-- Decimal integer or float integer significand had a disallowed leading zero. -/
  | leadingZero
  /-- Underscore `_` separator appeared outside two valid digits in the active base. -/
  | invalidUnderscore
  /-- Parsed integer value fell outside the target signed 64-bit integer range `[-2^63, 2^63 - 1]`. -/
  | overflow
  /-- Valid numeric prefix was followed by unconsumed trailing characters. -/
  | trailingChars
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.NumParse` parsing operations. -/
structure NumParseError where
  /-- Machine-checkable error category. -/
  kind : NumParseErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Public pure operations exported by `LeanSwe.NumParse`. -/
structure NumParseApi where
  /-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into an unbounded `Int`. -/
  parseInt : String → Except NumParseError Int
  /-- Parse a TOML 1.0 (plus `0X`/`0O`/`0B`) integer literal into a signed `Int64`. -/
  parseInt64 : String → Except NumParseError Int64
  /-- Format an `Int` as a canonical base-10 decimal string. -/
  formatInt : Int → String
  /-- Parse a TOML 1.0 decimal float or lowercase special literal (`inf`, `-inf`, `nan`) into IEEE-754 binary64 `Float`. -/
  parseFloat : String → Except NumParseError Float
  /-- Format a `Float` into a canonical TOML 1.0 float or lowercase special literal preserving bit identity for non-NaNs. -/
  formatFloat : Float → String

end LeanSwe.NumParse

import LeanSwe.NumParse.Model

namespace LeanSwe.NumParse.Model

/-- Allowed outcome relation for `NumParse.formatFloat` against `FloatFormatSpec`. -/
abbrev allowedFormatFloat (x : Float) (s : String) : Prop :=
  FloatFormatSpec x s

end LeanSwe.NumParse.Model

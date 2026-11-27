import LeanSweProofs.Base64.Model

namespace LeanSwe.Base64.Model

/-- Canonical `OBEYS_SYNTH` model alias for `Base64.encode` (`encodeDefaultModel`). -/
abbrev encode (bs : ByteArray) : String :=
  encodeDefaultModel bs

/-- Canonical `OBEYS_SYNTH` model alias for `Base64.encodeWith` (`encodeModel`). -/
abbrev encodeWithModel (opts : EncodeOptions) (bs : ByteArray) : String :=
  encodeModel opts bs

end LeanSwe.Base64.Model

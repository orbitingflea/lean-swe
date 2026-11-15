import LeanSwe.Base64.Types
import LeanSwe.Base64.Impl

namespace LeanSwe.Base64

/-- Encode bytes using standard RFC 4648 §4 alphabet with `'='` padding. -/
@[inline] def encode (bytes : ByteArray) : String :=
  Internal.encode bytes

/-- Encode bytes using URL-safe RFC 4648 §5 alphabet without `'='` padding. -/
@[inline] def encodeUrl (bytes : ByteArray) : String :=
  Internal.encodeUrl bytes

/-- Encode bytes using explicit `EncodeOptions`. -/
@[inline] def encodeWith (opts : EncodeOptions) (bytes : ByteArray) : String :=
  Internal.encodeWith opts bytes

/-- Decode standard RFC 4648 §4 Base64 text requiring `'='` padding and canonical trailing bits. -/
@[inline] def decode (s : String) : Except Base64Error ByteArray :=
  Internal.decode s

/-- Decode URL-safe RFC 4648 §5 Base64 text with optional padding and canonical trailing bits. -/
@[inline] def decodeUrl (s : String) : Except Base64Error ByteArray :=
  Internal.decodeUrl s

/-- Decode Base64 text using explicit `DecodeOptions`. -/
@[inline] def decodeWith (opts : DecodeOptions) (s : String) : Except Base64Error ByteArray :=
  Internal.decodeWith opts s

/-- Default `Base64Api` record bundling the concrete `LeanSwe.Base64` operations for `SpecTests` and `Proofs`. -/
def defaultApi : Base64Api :=
  Internal.defaultApi

end LeanSwe.Base64

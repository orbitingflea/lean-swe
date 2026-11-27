import LeanSweProofs.CryptoHash.Model
import LeanSweProofs.CryptoHash.Proofs.HmacEmptyInner

namespace LeanSwe.CryptoHash.Proofs

set_option maxRecDepth 16384 in
/-- Empty-key empty-message RFC 2104 HMAC-SHA256 vector for `Model.hmacSha256Bytes`. -/
theorem hmac_empty_vec :
    Model.hmacSha256Bytes ByteArray.empty ByteArray.empty = ByteArray.mk #[
      0xb6, 0x13, 0x67, 0x9a, 0x08, 0x14, 0xd9, 0xec,
      0x77, 0x2f, 0x95, 0xd7, 0x78, 0xc3, 0x5f, 0xc5,
      0xff, 0x16, 0x97, 0xc4, 0x93, 0x71, 0x56, 0x53,
      0xc6, 0xc7, 0x12, 0x14, 0x42, 0x92, 0xc5, 0xad] := by
  let kb := ByteArray.mk (Array.replicate 64 0)
  let ipad := ByteArray.mk (Array.replicate 64 0x36)
  let opad := ByteArray.mk (Array.replicate 64 0x5c)
  let ipadH : Array UInt32 := #[4099202733, 2535792975, 2430268064, 3742509290, 1692759311, 2744271233, 2185925419, 4175449650]
  let opadH : Array UInt32 := #[3548727311, 2059101303, 935970104, 1574446183, 2382641778, 1966355632, 3736610840, 907888038]
  let innerB := ByteArray.mk #[
    0xe7, 0x2b, 0xbd, 0x4d, 0x42, 0x9a, 0xc9, 0x14,
    0xa8, 0xa6, 0xc5, 0xbd, 0x49, 0x63, 0x2f, 0xf6,
    0xb0, 0x0d, 0x4f, 0xef, 0x42, 0xaf, 0xb4, 0x43,
    0xf0, 0xb8, 0x04, 0x7d, 0xf0, 0x6c, 0x85, 0xd2]
  exact hmac_decomposed ByteArray.empty ByteArray.empty kb ipad opad innerB _ ipadH opadH
    (by decide) (by decide) (by decide) hmac_empty_hi0 hmac_empty_hi1 (by decide) (by decide)

end LeanSwe.CryptoHash.Proofs

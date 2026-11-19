import LeanSwe.CryptoHash.Raw.Model
import LeanSwe.CryptoHash.Raw.HmacEmptyInner
import LeanSwe.CryptoHash.Raw.HmacTc2Inner
import LeanSwe.CryptoHash.Raw.HmacTc2Outer

namespace LeanSwe.CryptoHash.Raw.Proofs

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 2 HMAC-SHA256 vector for `Model.hmacSha256Bytes`. -/
theorem hmac_tc2_vec :
    Model.hmacSha256Bytes "Jefe".toUTF8 "what do ya want for nothing?".toUTF8 = ByteArray.mk #[
      0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e,
      0x6a, 0x04, 0x24, 0x26, 0x08, 0x95, 0x75, 0xc7,
      0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83,
      0x9d, 0xec, 0x58, 0xb9, 0x64, 0xec, 0x38, 0x43] := by
  let kb := ByteArray.mk (#[0x4a, 0x65, 0x66, 0x65] ++ Array.replicate 60 0)
  let ipad := ByteArray.mk (#[0x7c, 0x53, 0x50, 0x53] ++ Array.replicate 60 0x36)
  let opad := ByteArray.mk (#[0x16, 0x39, 0x3a, 0x39] ++ Array.replicate 60 0x5c)
  let ipadH : Array UInt32 := #[1700636666, 3426962231, 1511839179, 110292494, 2759467987, 1278932041, 3684834018, 2026328076]
  let opadH : Array UInt32 := #[246408149, 323038828, 1785343979, 758602444, 1369767239, 1840289256, 599761290, 1391542741]
  let innerB := ByteArray.mk #[
    0xa2, 0xe4, 0x85, 0x86, 0x3d, 0x27, 0xf9, 0xd8,
    0x64, 0xac, 0x8d, 0x80, 0x24, 0x32, 0xa1, 0xed,
    0x47, 0x7d, 0x8c, 0x4c, 0x6f, 0x34, 0x9d, 0x16,
    0xd4, 0xe7, 0xe9, 0x17, 0xc6, 0x29, 0xca, 0xd7]
  exact hmac_decomposed "Jefe".toUTF8 "what do ya want for nothing?".toUTF8 kb ipad opad innerB _ ipadH opadH
    (by decide) (by decide) (by decide) hmac_tc2_hi0 hmac_tc2_hi1 hmac_tc2_ho0 (by decide)

end LeanSwe.CryptoHash.Raw.Proofs

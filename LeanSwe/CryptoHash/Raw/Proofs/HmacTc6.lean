import LeanSwe.CryptoHash.Raw.Model
import LeanSwe.CryptoHash.Raw.Proofs.Sha256Vec131
import LeanSwe.CryptoHash.Raw.Proofs.HmacEmptyInner
import LeanSwe.CryptoHash.Raw.Proofs.HmacTc6Inner

namespace LeanSwe.CryptoHash.Raw.Proofs

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 6 HMAC-SHA256 vector for `Model.hmacSha256Bytes`. -/
theorem hmac_tc6_vec :
    Model.hmacSha256Bytes (ByteArray.mk (Array.replicate 131 0xaa))
      "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8 = ByteArray.mk #[
      0x60, 0xe4, 0x31, 0x59, 0x1e, 0xe0, 0xb6, 0x7f,
      0x0d, 0x8a, 0x26, 0xaa, 0xcb, 0xf5, 0xb7, 0x7f,
      0x8e, 0x0b, 0xc6, 0x21, 0x37, 0x28, 0xc5, 0x14,
      0x05, 0x46, 0x04, 0x0f, 0x0e, 0xe3, 0x7f, 0x54] := by
  let ipad := Model.xorBytes hmac_tc6_kb 0x36
  let opad := Model.xorBytes hmac_tc6_kb 0x5c
  let ipadH : Array UInt32 := #[3029354092, 1517828824, 336977084, 1886346799, 1304654973, 2804865202, 697719117, 431043809]
  let opadH : Array UInt32 := #[4080067489, 3723680084, 3015647870, 3142309557, 2900031423, 1374314071, 3516336225, 1549019650]
  let innerB := ByteArray.mk #[
    0xa7, 0x30, 0x38, 0xbb, 0xcc, 0x5d, 0x6f, 0x03,
    0x37, 0x21, 0x55, 0x8c, 0xa4, 0x81, 0xf3, 0x74,
    0x72, 0xca, 0x01, 0xc3, 0xb4, 0x07, 0x2f, 0x32,
    0x5c, 0x10, 0x72, 0xa1, 0x92, 0xbf, 0xe2, 0xc0]
  have hk : Model.hmacKeyBlock256 (ByteArray.mk (Array.replicate 131 0xaa)) = hmac_tc6_kb := by
    unfold Model.hmacKeyBlock256
    rw [sha256_131aa_vec]
    decide
  exact hmac_decomposed (ByteArray.mk (Array.replicate 131 0xaa))
    "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8
    hmac_tc6_kb ipad opad innerB _ ipadH opadH
    hk rfl rfl hmac_tc6_hi0 hmac_tc6_hi1 (by decide) (by decide)

end LeanSwe.CryptoHash.Raw.Proofs

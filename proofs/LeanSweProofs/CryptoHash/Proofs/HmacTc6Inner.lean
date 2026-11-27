import LeanSweProofs.CryptoHash.Model

namespace LeanSwe.CryptoHash.Proofs

/-- RFC 4231 Test Case 6 normalized 64-byte key block. -/
def hmac_tc6_kb : ByteArray :=
  ByteArray.mk (#[
    0x45, 0xad, 0x4b, 0x37, 0xc6, 0xe2, 0xfc, 0x0a,
    0x2c, 0xfc, 0xc1, 0xb5, 0xda, 0x52, 0x41, 0x32,
    0xec, 0x70, 0x76, 0x15, 0xc2, 0xca, 0xe1, 0xdb,
    0xbc, 0x43, 0xc9, 0x7a, 0xa5, 0x21, 0xdb, 0x81] ++ Array.replicate 32 0)

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 6 inner key-block SHA-256 compression lemma. -/
theorem hmac_tc6_hi0 :
    Model.Sha256State.init.update (Model.xorBytes hmac_tc6_kb 0x36) =
      { h := #[3029354092, 1517828824, 336977084, 1886346799, 1304654973, 2804865202, 697719117, 431043809],
        buf := ByteArray.empty,
        totalBytes := 64 } := by
  decide

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 6 inner digest lemma. -/
theorem hmac_tc6_hi1 :
    (({ h := #[3029354092, 1517828824, 336977084, 1886346799, 1304654973, 2804865202, 697719117, 431043809],
        buf := ByteArray.empty,
        totalBytes := 64 } : Model.Sha256State).update
      "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8).finalize = ByteArray.mk #[
      0xa7, 0x30, 0x38, 0xbb, 0xcc, 0x5d, 0x6f, 0x03,
      0x37, 0x21, 0x55, 0x8c, 0xa4, 0x81, 0xf3, 0x74,
      0x72, 0xca, 0x01, 0xc3, 0xb4, 0x07, 0x2f, 0x32,
      0x5c, 0x10, 0x72, 0xa1, 0x92, 0xbf, 0xe2, 0xc0] := by
  decide

end LeanSwe.CryptoHash.Proofs

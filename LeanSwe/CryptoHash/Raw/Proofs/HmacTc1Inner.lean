import LeanSwe.CryptoHash.Raw.Model

namespace LeanSwe.CryptoHash.Raw.Proofs

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 1 inner key-block SHA-256 compression lemma. -/
theorem hmac_tc1_hi0 :
    Model.Sha256State.init.update (ByteArray.mk (Array.replicate 20 0x3d ++ Array.replicate 44 0x36)) =
      { h := #[733091844, 599350265, 3035112844, 4206224980, 301109790, 1340831982, 2559632894, 1689747510],
        buf := ByteArray.empty,
        totalBytes := 64 } := by
  decide

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 1 inner digest lemma. -/
theorem hmac_tc1_hi1 :
    (({ h := #[733091844, 599350265, 3035112844, 4206224980, 301109790, 1340831982, 2559632894, 1689747510],
        buf := ByteArray.empty,
        totalBytes := 64 } : Model.Sha256State).update "Hi There".toUTF8).finalize = ByteArray.mk #[
      0x92, 0xab, 0x4d, 0x9a, 0x1f, 0x3b, 0x61, 0x52,
      0xbc, 0xa9, 0xdd, 0x9e, 0x69, 0xaf, 0x43, 0xf4,
      0xce, 0x99, 0xe4, 0x2f, 0xd4, 0xe3, 0x0f, 0xf9,
      0x72, 0xc4, 0x80, 0x25, 0xb9, 0xf9, 0xcf, 0xef] := by
  decide

end LeanSwe.CryptoHash.Raw.Proofs

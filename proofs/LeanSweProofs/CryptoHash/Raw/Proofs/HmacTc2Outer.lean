import LeanSweProofs.CryptoHash.Raw.Model

namespace LeanSwe.CryptoHash.Raw.Proofs

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 2 outer key-block SHA-256 compression lemma. -/
theorem hmac_tc2_ho0 :
    Model.Sha256State.init.update (ByteArray.mk (#[0x16, 0x39, 0x3a, 0x39] ++ Array.replicate 60 0x5c)) =
      { h := #[246408149, 323038828, 1785343979, 758602444, 1369767239, 1840289256, 599761290, 1391542741],
        buf := ByteArray.empty,
        totalBytes := 64 } := by
  decide

end LeanSwe.CryptoHash.Raw.Proofs

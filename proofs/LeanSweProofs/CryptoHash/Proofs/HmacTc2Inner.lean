import LeanSweProofs.CryptoHash.Model

namespace LeanSwe.CryptoHash.Proofs

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 2 inner key-block SHA-256 compression lemma. -/
theorem hmac_tc2_hi0 :
    Model.Sha256State.init.update (ByteArray.mk (#[0x7c, 0x53, 0x50, 0x53] ++ Array.replicate 60 0x36)) =
      { h := #[1700636666, 3426962231, 1511839179, 110292494, 2759467987, 1278932041, 3684834018, 2026328076],
        buf := ByteArray.empty,
        totalBytes := 64 } := by
  decide

set_option maxRecDepth 16384 in
/-- RFC 4231 Test Case 2 inner digest lemma. -/
theorem hmac_tc2_hi1 :
    (({ h := #[1700636666, 3426962231, 1511839179, 110292494, 2759467987, 1278932041, 3684834018, 2026328076],
        buf := ByteArray.empty,
        totalBytes := 64 } : Model.Sha256State).update "what do ya want for nothing?".toUTF8).finalize = ByteArray.mk #[
      0xa2, 0xe4, 0x85, 0x86, 0x3d, 0x27, 0xf9, 0xd8,
      0x64, 0xac, 0x8d, 0x80, 0x24, 0x32, 0xa1, 0xed,
      0x47, 0x7d, 0x8c, 0x4c, 0x6f, 0x34, 0x9d, 0x16,
      0xd4, 0xe7, 0xe9, 0x17, 0xc6, 0x29, 0xca, 0xd7] := by
  decide

end LeanSwe.CryptoHash.Proofs

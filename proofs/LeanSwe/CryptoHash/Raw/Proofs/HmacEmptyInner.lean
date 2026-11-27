import LeanSwe.CryptoHash.Raw.Model

namespace LeanSwe.CryptoHash.Raw.Proofs

/-- Decompose RFC 2104 HMAC-SHA256 evaluation into single-block inner and outer SHA-256 steps. -/
theorem hmac_decomposed (key msg kBlock ipad opad innerBytes outerBytes : ByteArray)
    (ipadH opadH : Array UInt32)
    (hk : Model.hmacKeyBlock256 key = kBlock)
    (hipad : Model.xorBytes kBlock 0x36 = ipad)
    (hopad : Model.xorBytes kBlock 0x5c = opad)
    (hi0 : Model.Sha256State.init.update ipad = { h := ipadH, buf := ByteArray.empty, totalBytes := 64 })
    (hi1 : (({ h := ipadH, buf := ByteArray.empty, totalBytes := 64 } : Model.Sha256State).update msg).finalize = innerBytes)
    (ho0 : Model.Sha256State.init.update opad = { h := opadH, buf := ByteArray.empty, totalBytes := 64 })
    (ho1 : (({ h := opadH, buf := ByteArray.empty, totalBytes := 64 } : Model.Sha256State).update innerBytes).finalize = outerBytes) :
    Model.hmacSha256Bytes key msg = outerBytes := by
  unfold Model.hmacSha256Bytes Model.HmacSha256State.init Model.HmacSha256State.update Model.HmacSha256State.finalize
  dsimp only
  rw [hk, hipad, hopad, hi0, hi1, ho0, ho1]

set_option maxRecDepth 16384 in
/-- Empty-key HMAC inner key-block SHA-256 compression lemma. -/
theorem hmac_empty_hi0 :
    Model.Sha256State.init.update (ByteArray.mk (Array.replicate 64 0x36)) =
      { h := #[4099202733, 2535792975, 2430268064, 3742509290, 1692759311, 2744271233, 2185925419, 4175449650],
        buf := ByteArray.empty,
        totalBytes := 64 } := by
  decide

set_option maxRecDepth 16384 in
/-- Empty-key empty-message HMAC inner digest lemma. -/
theorem hmac_empty_hi1 :
    (({ h := #[4099202733, 2535792975, 2430268064, 3742509290, 1692759311, 2744271233, 2185925419, 4175449650],
        buf := ByteArray.empty,
        totalBytes := 64 } : Model.Sha256State).update ByteArray.empty).finalize = ByteArray.mk #[
      0xe7, 0x2b, 0xbd, 0x4d, 0x42, 0x9a, 0xc9, 0x14,
      0xa8, 0xa6, 0xc5, 0xbd, 0x49, 0x63, 0x2f, 0xf6,
      0xb0, 0x0d, 0x4f, 0xef, 0x42, 0xaf, 0xb4, 0x43,
      0xf0, 0xb8, 0x04, 0x7d, 0xf0, 0x6c, 0x85, 0xd2] := by
  decide

end LeanSwe.CryptoHash.Raw.Proofs

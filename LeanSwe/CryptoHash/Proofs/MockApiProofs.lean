import Core.Obeys
import LeanSwe.CryptoHash.Proofs.HexHelpers

namespace LeanSwe.CryptoHash.Proofs

open Core
open Core.NondetTest
open LeanSwe.CryptoHash

private theorem hashM_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg bs : ByteArray)
    (hraw : raw.digestRaw alg msg s = (.ok bs, s'))
    (hlen : bs.size = digestLen alg) :
    (Internal.hashM raw alg msg).run s =
      (.ok { alg := alg, bytes := bs }, s') := by
  have hs : (bs.size != digestLen alg) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem hashM_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg : ByteArray) (err : CryptoHashError)
    (hraw : raw.digestRaw alg msg s = (.error err, s')) :
    (Internal.hashM raw alg msg).run s = (.error err, s') := by
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  rfl

private theorem hashM_raw_corrupt (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg : ByteArray) (badLen : Nat)
    (hraw : raw.digestRaw alg msg s = (.ok (ByteArray.mk (Array.replicate badLen 0)), s'))
    (hbad : badLen ≠ digestLen alg) :
    (Internal.hashM raw alg msg).run s =
      (.error { kind := .lengthMismatch, message := s!"digest length mismatch: expected {digestLen alg} bytes, got {badLen}" },
        s') := by
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  have hsz : (ByteArray.mk (Array.replicate badLen 0)).size = badLen := by
    change (Array.replicate badLen (0 : UInt8)).size = badLen
    simp
  have hne : (badLen != digestLen alg) = true := bne_iff_ne.mpr hbad
  simp only [hsz, hne, ↓reduceIte]
  rfl

private theorem hmacSha256M_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg bs : ByteArray)
    (hraw : raw.hmacSha256Raw key msg s = (.ok bs, s'))
    (hlen : bs.size = 32) :
    (Internal.hmacSha256M raw key msg).run s =
      (.ok { alg := .sha256, bytes := bs }, s') := by
  have hs : (bs.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem hmacSha256M_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg : ByteArray) (err : CryptoHashError)
    (hraw : raw.hmacSha256Raw key msg s = (.error err, s')) :
    (Internal.hmacSha256M raw key msg).run s = (.error err, s') := by
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  rfl

private theorem hmacSha256M_raw_corrupt (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg : ByteArray) (badLen : Nat)
    (hraw : raw.hmacSha256Raw key msg s = (.ok (ByteArray.mk (Array.replicate badLen 0)), s'))
    (hbad : badLen ≠ 32) :
    (Internal.hmacSha256M raw key msg).run s =
      (.error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {badLen}" },
        s') := by
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  have hsz : (ByteArray.mk (Array.replicate badLen 0)).size = badLen := by
    change (Array.replicate badLen (0 : UInt8)).size = badLen
    simp
  have hne : (badLen != 32) = true := bne_iff_ne.mpr hbad
  simp only [hsz, hne, ↓reduceIte]
  rfl

private theorem ctEqM_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (a b : ByteArray)
    (heq : a.size = b.size)
    (hraw : raw.ctEqualRaw a b s = (.ok (a == b), s')) :
    (Internal.ctEqM raw a b).run s = (.ok (a == b), s') := by
  have hne : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr heq
  dsimp [Internal.ctEqM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact hraw

private theorem ctEqM_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (a b : ByteArray) (err : CryptoHashError)
    (heq : a.size = b.size)
    (hraw : raw.ctEqualRaw a b s = (.error err, s')) :
    (Internal.ctEqM raw a b).run s = (.error err, s') := by
  have hne : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr heq
  dsimp [Internal.ctEqM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact hraw

private theorem verifyHmacSha256M_raw_hmacErr (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (err : CryptoHashError)
    (key msg : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hraw : raw.hmacSha256Raw key msg s = (.error err, s')) :
    (Internal.verifyHmacSha256M raw key msg expected).run s = (.error err, s') := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_err raw s s' key msg err hraw]
  rfl

private theorem verifyHmacSha256M_raw_ctEqErr (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s sH sC : MockCryptoHashState) (err : CryptoHashError)
    (key msg bs : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hbs : bs.size = 32)
    (hrawH : raw.hmacSha256Raw key msg s = (.ok bs, sH))
    (hrawC : raw.ctEqualRaw bs expected.bytes sH = (.error err, sC)) :
    (Internal.verifyHmacSha256M raw key msg expected).run s = (.error err, sC) := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_ok raw s sH key msg bs hrawH hbs]
  dsimp only [Bind.bind, Monad.toBind, Id.instMonad]
  have hsz : bs.size = expected.bytes.size := by rw [hbs, hlen]
  exact ctEqM_raw_err raw sH sC bs expected.bytes err hsz hrawC

private theorem verifyHmacSha256M_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s sH sC : MockCryptoHashState)
    (key msg bs : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hbs : bs.size = 32)
    (hrawH : raw.hmacSha256Raw key msg s = (.ok bs, sH))
    (hrawC : raw.ctEqualRaw bs expected.bytes sH = (.ok (bs == expected.bytes), sC)) :
    (Internal.verifyHmacSha256M raw key msg expected).run s =
      (.ok (bs == expected.bytes), sC) := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_ok raw s sH key msg bs hrawH hbs]
  dsimp only [Bind.bind, Monad.toBind, Id.instMonad]
  have hsz : bs.size = expected.bytes.size := by rw [hbs, hlen]
  exact ctEqM_raw_ok raw sH sC bs expected.bytes hsz hrawC


set_option maxRecDepth 2048 in
/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_delegatesAndChecksLength`. -/
theorem cryptohash_hash_delegatesAndChecksLength :
    AllPass (test_cryptohash_hash_delegatesAndChecksLength Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ alg msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hash_delegatesAndChecksLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc + 1, hmacCalls := hc, ctEqCalls := cc,
      failDigestWith := none, failHmacWith := fh, failCtEqWith := fc,
      corruptDigestLen := none, corruptHmacLen := ch }
  cases alg
  · rw [hashM_raw_ok _ _ s₁ .sha256 msg (mockDigestBytes .sha256 msg) rfl (mockDigestBytes_size .sha256 msg),
      hashM_raw_ok _ _ s₁ .sha512 msg (mockDigestBytes .sha512 msg) rfl (mockDigestBytes_size .sha512 msg)]
    dsimp only
    refine ⟨⟨rfl, rfl, rfl⟩,
      ⟨rfl, mockDigestBytes_size .sha256 msg, mockDigestBytes_size .sha256 msg,
        by simp [Digest.isValid, mockDigestBytes_size]⟩, ?_⟩
    simp
  · rw [hashM_raw_ok _ _ s₁ .sha512 msg (mockDigestBytes .sha512 msg) rfl (mockDigestBytes_size .sha512 msg),
      hashM_raw_ok _ _ s₁ .sha256 msg (mockDigestBytes .sha256 msg) rfl (mockDigestBytes_size .sha256 msg)]
    dsimp only
    refine ⟨⟨rfl, rfl, rfl⟩,
      ⟨rfl, mockDigestBytes_size .sha512 msg, mockDigestBytes_size .sha512 msg,
        by simp [Digest.isValid, mockDigestBytes_size]⟩, ?_⟩
    simp

/-- Non-vacuity witness for `test_cryptohash_hash_delegatesAndChecksLength`. -/
theorem reach_cryptohash_hash_delegatesAndChecksLength :
    CanReach (test_cryptohash_hash_delegatesAndChecksLength Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl⟩, .sha256, ByteArray.empty,
    cryptohash_hash_delegatesAndChecksLength {} ⟨rfl, rfl⟩ .sha256 ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_propagatesRawError`. -/
theorem cryptohash_hash_propagatesRawError :
    AllPass (test_cryptohash_hash_propagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail alg msg
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_hash_propagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hashM_raw_err _ _ _ alg msg err rfl,
    hashM_raw_err _ _ _ .sha256 msg err rfl,
    hashM_raw_err _ _ _ .sha512 msg err rfl]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hash_propagatesRawError`. -/
theorem reach_cryptohash_hash_propagatesRawError :
    CanReach (test_cryptohash_hash_propagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failDigestWith := some err }, rfl, .sha256, ByteArray.empty,
    cryptohash_hash_propagatesRawError err (by decide) { failDigestWith := some err } rfl .sha256 ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_rejectsWrongRawLength`. -/
theorem cryptohash_hash_rejectsWrongRawLength :
    AllPass (test_cryptohash_hash_rejectsWrongRawLength Internal.mkApiM) := by
  intro alg badLen hbad ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hash_rejectsWrongRawLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hashM_raw_corrupt _ _ _ alg msg badLen rfl hbad]
  dsimp only
  refine ⟨rfl, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen
  have hpos : 0 < (toString ("digest length mismatch: expected " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_hash_rejectsWrongRawLength`. -/
theorem reach_cryptohash_hash_rejectsWrongRawLength :
    CanReach (test_cryptohash_hash_rejectsWrongRawLength Internal.mkApiM) :=
  ⟨.sha256, 0, by decide, { corruptDigestLen := some 0 }, ⟨rfl, rfl⟩, ByteArray.empty,
    cryptohash_hash_rejectsWrongRawLength .sha256 0 (by decide) { corruptDigestLen := some 0 } ⟨rfl, rfl⟩ ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_delegatesAndChecksLength`. -/
theorem cryptohash_hmacSha256_delegatesAndChecksLength :
    AllPass (test_cryptohash_hmacSha256_delegatesAndChecksLength Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ key msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hmacSha256_delegatesAndChecksLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_ok _ _ _ key msg (mockHmacBytes key msg) rfl (mockHmacBytes_size key msg)]
  dsimp only
  exact ⟨⟨rfl, rfl, rfl⟩,
    ⟨rfl, mockHmacBytes_size key msg, by unfold ValidDigest; rw [mockHmacBytes_size]; rfl,
      by simp [Digest.isValid, digestLen, mockHmacBytes_size]⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_delegatesAndChecksLength`. -/
theorem reach_cryptohash_hmacSha256_delegatesAndChecksLength :
    CanReach (test_cryptohash_hmacSha256_delegatesAndChecksLength Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl⟩, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_delegatesAndChecksLength {} ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_propagatesRawError`. -/
theorem cryptohash_hmacSha256_propagatesRawError :
    AllPass (test_cryptohash_hmacSha256_propagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail key msg
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_hmacSha256_propagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_err _ _ _ key msg err rfl]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_propagatesRawError`. -/
theorem reach_cryptohash_hmacSha256_propagatesRawError :
    CanReach (test_cryptohash_hmacSha256_propagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failHmacWith := some err }, rfl, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_propagatesRawError err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_rejectsWrongRawLength`. -/
theorem cryptohash_hmacSha256_rejectsWrongRawLength :
    AllPass (test_cryptohash_hmacSha256_rejectsWrongRawLength Internal.mkApiM) := by
  intro badLen hbad ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ key msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hmacSha256_rejectsWrongRawLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_corrupt _ _ _ key msg badLen rfl hbad]
  dsimp only
  refine ⟨rfl, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen
  have hpos : 0 < (toString ("HMAC-SHA256 length mismatch: expected 32 bytes, got " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_rejectsWrongRawLength`. -/
theorem reach_cryptohash_hmacSha256_rejectsWrongRawLength :
    CanReach (test_cryptohash_hmacSha256_rejectsWrongRawLength Internal.mkApiM) :=
  ⟨0, by decide, { corruptHmacLen := some 0 }, ⟨rfl, rfl⟩, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_rejectsWrongRawLength 0 (by decide) { corruptHmacLen := some 0 } ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall`. -/
theorem cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall :
    AllPass (test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall Internal.mkApiM) := by
  intro s₀ a b hneq
  dsimp [test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall, Internal.mkApiM, Internal.ctEqM,
    Pure.pure, StateT.pure, StateT.run, Core.NondetTest.assert]
  have hne : (a.size != b.size) = true := bne_iff_ne.mpr hneq
  simp only [hne, ↓reduceIte]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall`. -/
theorem reach_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall :
    CanReach (test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.mk #[0], by decide,
    cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall {} ByteArray.empty (ByteArray.mk #[0]) (by decide)⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_equalLengthsDelegates`. -/
theorem cryptohash_ctEq_equalLengthsDelegates :
    AllPass (test_cryptohash_ctEq_equalLengthsDelegates Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail a b heq
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_ctEq_equalLengthsDelegates, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc, ctEqCalls := cc + 1,
      failDigestWith := fd, failHmacWith := fh, failCtEqWith := none,
      corruptDigestLen := cd, corruptHmacLen := ch }
  rw [ctEqM_raw_ok _ _ s₁ a b heq (by change (if (a.size != b.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq]; rfl),
    ctEqM_raw_ok _ _ s₁ b a heq.symm (by change (if (b.size != a.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq.symm]; rfl),
    ctEqM_raw_ok _ _ s₁ a a rfl (by change (if (a.size != a.size) = true then _ else _) = _; simp; rfl)]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, ⟨congrArg Except.ok (byteArray_beq_symm a b), congrArg Except.ok (beq_self_eq_true a)⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_equalLengthsDelegates`. -/
theorem reach_cryptohash_ctEq_equalLengthsDelegates :
    CanReach (test_cryptohash_ctEq_equalLengthsDelegates Internal.mkApiM) :=
  ⟨{}, rfl, ByteArray.empty, ByteArray.empty, rfl,
    cryptohash_ctEq_equalLengthsDelegates {} rfl ByteArray.empty ByteArray.empty rfl⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_equalLengthsPropagatesRawError`. -/
theorem cryptohash_ctEq_equalLengthsPropagatesRawError :
    AllPass (test_cryptohash_ctEq_equalLengthsPropagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail a b heq
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_ctEq_equalLengthsPropagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc, ctEqCalls := cc + 1,
      failDigestWith := fd, failHmacWith := fh, failCtEqWith := some err,
      corruptDigestLen := cd, corruptHmacLen := ch }
  rw [ctEqM_raw_err _ _ s₁ a b err heq (by change (if (a.size != b.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq]; rfl)]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_equalLengthsPropagatesRawError`. -/
theorem reach_cryptohash_ctEq_equalLengthsPropagatesRawError :
    CanReach (test_cryptohash_ctEq_equalLengthsPropagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failCtEqWith := some err }, rfl, ByteArray.empty, ByteArray.empty, rfl,
    cryptohash_ctEq_equalLengthsPropagatesRawError err (by decide) { failCtEqWith := some err } rfl ByteArray.empty ByteArray.empty rfl⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls`. -/
theorem cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls :
    AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls Internal.mkApiM) := by
  intro s₀ key msg expected halg
  have hne : (expected.alg != .sha256) = true := by
    cases h : expected.alg with
    | sha256 => exact absurd h halg
    | sha512 => decide
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls, Internal.mkApiM,
    Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run,
    Core.NondetTest.assert]
  simp only [hne, ↓reduceIte]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls`. -/
theorem reach_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls :
    CanReach (test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.empty, { alg := .sha512, bytes := ByteArray.empty }, by decide,
    cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls {} ByteArray.empty ByteArray.empty { alg := .sha512, bytes := ByteArray.empty } (by decide)⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls`. -/
theorem cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls :
    AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls Internal.mkApiM) := by
  intro s₀ key msg expected ⟨halg, hlen⟩
  dsimp only at halg hlen ⊢
  have hf : (expected.alg != .sha256) = false := by rw [halg]; decide
  have ht : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls, AllPassRun,
    Internal.mkApiM, Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
    StateT.run, Core.NondetTest.assert]
  simp only [hf, Bool.false_eq_true, ↓reduceIte, ht]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen2 := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen2
  have hpos : 0 < (toString ("HMAC-SHA256 length mismatch: expected 32 bytes, got " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls`. -/
theorem reach_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls :
    CanReach (test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.empty, { alg := .sha256, bytes := ByteArray.empty }, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls {} ByteArray.empty ByteArray.empty { alg := .sha256, bytes := ByteArray.empty } ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_propagatesHmacError`. -/
theorem cryptohash_verifyHmacSha256_propagatesHmacError :
    AllPass (test_cryptohash_verifyHmacSha256_propagatesHmacError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail key msg expected ⟨halg, hlen⟩
  dsimp only at hfail halg hlen
  subst hfail
  dsimp [test_cryptohash_verifyHmacSha256_propagatesHmacError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [verifyHmacSha256M_raw_hmacErr _ _ _ err key msg expected halg hlen rfl]
  dsimp only
  exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_propagatesHmacError`. -/
theorem reach_cryptohash_verifyHmacSha256_propagatesHmacError :
    CanReach (test_cryptohash_verifyHmacSha256_propagatesHmacError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨err, by decide, { failHmacWith := some err }, rfl, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_propagatesHmacError err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_propagatesCtEqError`. -/
theorem cryptohash_verifyHmacSha256_propagatesCtEqError :
    AllPass (test_cryptohash_verifyHmacSha256_propagatesCtEqError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hf1, hcorr, hf2⟩ key msg expected ⟨halg, hlen⟩
  dsimp only at hf1 hcorr hf2 halg hlen
  subst hf1
  subst hcorr
  subst hf2
  dsimp [test_cryptohash_verifyHmacSha256_propagatesCtEqError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let sH : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc + 1, ctEqCalls := cc,
      failDigestWith := fd, failHmacWith := none, failCtEqWith := some err,
      corruptDigestLen := cd, corruptHmacLen := none }
  let sC : MockCryptoHashState := { sH with ctEqCalls := cc + 1 }
  have hbs := mockHmacBytes_size key msg
  have hne : ((mockHmacBytes key msg).size != expected.bytes.size) = false :=
    bne_eq_false_iff_eq.mpr (by rw [hbs, hlen])
  rw [verifyHmacSha256M_raw_ctEqErr _ _ sH sC err key msg (mockHmacBytes key msg) expected halg hlen hbs]
  · dsimp only
    exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩
  · rfl
  · revert hne
    generalize (mockHmacBytes key msg) = x
    intro hne
    change (if (x.size != expected.bytes.size) = true then
      (Except.error { kind := .lengthMismatch, message := "length mismatch" }, sC)
      else (Except.error err, sC)) = _
    simp [hne]

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_propagatesCtEqError`. -/
theorem reach_cryptohash_verifyHmacSha256_propagatesCtEqError :
    CanReach (test_cryptohash_verifyHmacSha256_propagatesCtEqError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨err, by decide, { failCtEqWith := some err }, ⟨rfl, rfl, rfl⟩, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_propagatesCtEqError err (by decide) { failCtEqWith := some err } ⟨rfl, rfl, rfl⟩ ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered`. -/
theorem cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered :
    AllPass (test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hf1, hcorr, hf2⟩ key msg expected ⟨halg, hlen⟩
  dsimp only at hf1 hcorr hf2 halg hlen
  subst hf1
  subst hcorr
  subst hf2
  let tagBytes := mockHmacBytes key msg
  have hts : tagBytes.size = 32 := mockHmacBytes_size key msg
  let tampBytes := tagBytes.set! 0 (tagBytes[0]! ^^^ 1)
  have htamp_size : tampBytes.size = 32 := by simp [tampBytes, ByteArray.size_set!, hts]
  have hne_exp : (tagBytes.size != expected.bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [hts, hlen])
  have hne_tamp : (tagBytes.size != tampBytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [hts, htamp_size])
  let t1Bytes := mockHmacBytes "k1".toUTF8 "m1".toUTF8
  have ht1s : t1Bytes.size = 32 := mockHmacBytes_size "k1".toUTF8 "m1".toUTF8
  let t2Bytes := mockHmacBytes "k2".toUTF8 "m1".toUTF8
  have ht2s : t2Bytes.size = 32 := mockHmacBytes_size "k2".toUTF8 "m1".toUTF8
  have hne_21 : (t2Bytes.size != t1Bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [ht2s, ht1s])
  let t3Bytes := mockHmacBytes "k1".toUTF8 "m2".toUTF8
  have ht3s : t3Bytes.size = 32 := mockHmacBytes_size "k1".toUTF8 "m2".toUTF8
  have hne_31 : (t3Bytes.size != t1Bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [ht3s, ht1s])
  let sH : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc + 1, ctEqCalls := cc,
      failDigestWith := fd, failHmacWith := none, failCtEqWith := none,
      corruptDigestLen := cd, corruptHmacLen := none }
  let sC : MockCryptoHashState := { sH with ctEqCalls := cc + 1 }
  dsimp [test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_ok _ _ sH key msg tagBytes rfl hts]
  dsimp only
  rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes expected halg hlen hts]
  · dsimp only
    rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes { alg := .sha256, bytes := tagBytes } rfl hts hts]
    · rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes { alg := .sha256, bytes := tampBytes } rfl htamp_size hts]
      · rw [hmacSha256M_raw_ok _ _ sH "k1".toUTF8 "m1".toUTF8 t1Bytes rfl ht1s]
        dsimp only
        rw [verifyHmacSha256M_raw_ok _ _ sH sC "k2".toUTF8 "m1".toUTF8 t2Bytes { alg := .sha256, bytes := t1Bytes } rfl ht1s ht2s]
        · rw [verifyHmacSha256M_raw_ok _ _ sH sC "k1".toUTF8 "m2".toUTF8 t3Bytes { alg := .sha256, bytes := t1Bytes } rfl ht1s ht3s]
          · dsimp only
            exact ⟨⟨rfl, rfl⟩, rfl, congrArg Except.ok (beq_self_eq_true tagBytes),
              congrArg Except.ok (byteArray_tamper_byte0_ne tagBytes hts),
              congrArg Except.ok mockHmacBytes_k2_m1_ne,
              congrArg Except.ok mockHmacBytes_k1_m2_ne, trivial⟩
          · rfl
          · revert hne_31
            generalize t3Bytes = x3; generalize t1Bytes = x1; intro hne_31
            change (if (x3.size != x1.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (x3 == x1), sC)) = _
            simp [hne_31]
        · rfl
        · revert hne_21
          generalize t2Bytes = x2; generalize t1Bytes = x1; intro hne_21
          change (if (x2.size != x1.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (x2 == x1), sC)) = _
          simp [hne_21]
      · rfl
      · revert hne_tamp
        generalize tagBytes = xt; generalize tampBytes = xp; intro hne_tamp
        change (if (xt.size != xp.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xt == xp), sC)) = _
        simp [hne_tamp]
    · rfl
    · generalize tagBytes = xs
      change (if (xs.size != xs.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xs == xs), sC)) = _
      simp
  · rfl
  · revert hne_exp
    generalize tagBytes = xe; intro hne_exp
    change (if (xe.size != expected.bytes.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xe == expected.bytes), sC)) = _
    simp [hne_exp]

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered`. -/
theorem reach_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered :
    CanReach (test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered Internal.mkApiM) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨{}, ⟨rfl, rfl, rfl⟩, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered {} ⟨rfl, rfl, rfl⟩ ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩


end LeanSwe.CryptoHash.Proofs

import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Impl
import LeanSwe.CryptoHash.Raw.Interface
import LeanSwe.CryptoHash.Raw.SpecTests

namespace LeanSwe.CryptoHash.Raw.Proofs

open Core (AllPass CanReach)
open LeanSwe.CryptoHash.Raw

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hfb
  · rename_i hne
    intro hemp
    apply hne
    simp [hemp]

/-- `defaultOps.mapRawError` satisfies `test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage`. -/
theorem raw_mapRawError_mapsKindsAndNonEmptyMessage :
    AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage defaultOps) := by
  intro raw
  cases raw with
  | invalidArgument detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | invalidHexInput detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid hex input" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | lengthError expected got detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail (by
        intro h
        have hlen := congrArg String.length h
        simp [String.length] at hlen)
    · exact ⟨rfl, rfl⟩
    · trivial
  | opensslError code detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | userError detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "cryptohash error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial

private def pureModelRawOps : RawCryptoHashOpsM (StateM Unit) :=
  { mapRawError := Internal.mapRawError
    digestRaw := fun alg _ => pure (.ok (ByteArray.mk (Array.replicate (digestLen alg) 0)))
    hmacSha256Raw := fun _ _ => pure (.ok (ByteArray.mk (Array.replicate 32 0)))
    ctEqualRaw := fun a b =>
      if a.size != b.size then
        pure (.error (Internal.mapRawError (.lengthError a.size b.size "length mismatch")))
      else
        pure (.ok (a == b)) }

/-- `pureModelRawOps` satisfies `test_cryptohashraw_digestRaw_returnsExpectedLengthOrError`. -/
theorem raw_digestRaw_returnsExpectedLengthOrError :
    AllPass (test_cryptohashraw_digestRaw_returnsExpectedLengthOrError pureModelRawOps) := by
  intro _ alg _
  dsimp [test_cryptohashraw_digestRaw_returnsExpectedLengthOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_hmacSha256Raw_returns32BytesOrError`. -/
theorem raw_hmacSha256Raw_returns32BytesOrError :
    AllPass (test_cryptohashraw_hmacSha256Raw_returns32BytesOrError pureModelRawOps) := by
  intro _ _ _
  dsimp [test_cryptohashraw_hmacSha256Raw_returns32BytesOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_returnsLengthMismatch :
    AllPass (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch pureModelRawOps) := by
  intro _ a b hne
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind, Core.NondetTest.assume]
  have hneB : (a.size != b.size) = true := bne_iff_ne.mpr hne
  simp [hneB, StateT.pure, pure, Internal.mapRawError, Internal.nonEmptyMsg]

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch pureModelRawOps) := by
  refine ⟨(), ByteArray.empty, ByteArray.mk #[1], by decide, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp [ByteArray.size, Internal.mapRawError, Internal.nonEmptyMsg, StateT.pure, pure]

/-- `pureModelRawOps` satisfies `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_returnsBoolOrError :
    AllPass (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError pureModelRawOps) := by
  intro _ a b heq
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  have hfalse : (a.size != b.size) = false := by simp [heq]
  simp [hfalse, StateT.pure, pure]

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError pureModelRawOps) := by
  refine ⟨(), ByteArray.empty, ByteArray.empty, rfl, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, pureModelRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  simp

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_baseIO {α β : Type} (act : BaseIO α) (k : α → IO β) (w : Void IO.RealWorld) :
    ((liftM act : IO α) >>= k) w = k (act w).val (act w).state := by
  rcases baseIO_liftM_never_throws act w with ⟨v, w', hv⟩
  have hst : act w = .mk v w' := by
    simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO] at hv
    cases h : act w with
    | mk a s =>
      rw [h] at hv
      have ha : a = v := by injection hv
      have hs : s = w' := by injection hv
      subst ha hs
      rfl
  rw [hst]
  have hbind : ((liftM act : IO α) >>= k) w =
      match (liftM act : IO α) w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := rfl
  rw [hbind, hv]

/-- Exact outcome characterization of `Raw.defaultOps.digestRaw`: either `.ok bs` of length `digestLen alg` or `.error` with `.cryptoError`. -/
theorem defaultOps_digestRaw_outcome (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.digestRaw alg data) w = .ok (.ok bs) w' ∧ bs.size = digestLen alg) ∨
    (∃ e w', (defaultOps.digestRaw alg data) w = .ok (.error e) w' ∧ e.kind = .cryptoError) := by
  dsimp [defaultOps, Internal.mkRawOps]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, by simp [Internal.decodeOpenSslError, Internal.mapRawError]⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.decodeOpenSslError, Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      have heq : bs.size = digestLen alg := by
        cases hsz : (bs.size == digestLen alg)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- Exact outcome characterization of `Raw.defaultOps.hmacSha256Raw`: either `.ok bs` of length `32` or `.error` with `.cryptoError`. -/
theorem defaultOps_hmacSha256Raw_outcome (key msg : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.hmacSha256Raw key msg) w = .ok (.ok bs) w' ∧ bs.size = 32) ∨
    (∃ e w', (defaultOps.hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind = .cryptoError) := by
  dsimp [defaultOps, Internal.mkRawOps]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, by simp [Internal.decodeOpenSslError, Internal.mapRawError]⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.decodeOpenSslError, Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      have heq : bs.size = 32 := by
        cases hsz : (bs.size == 32)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- Exact outcome characterization of `Raw.defaultOps.ctEqualRaw`: `.error` with `.lengthMismatch` when sizes differ, else `.ok eq`. -/
theorem defaultOps_ctEqualRaw_outcome (a b : ByteArray) (w : Void IO.RealWorld) :
    (a.size ≠ b.size ∧ ∃ e w', (defaultOps.ctEqualRaw a b) w = .ok (.error e) w' ∧ e.kind = .lengthMismatch) ∨
    (a.size = b.size ∧ ∃ eq w', (defaultOps.ctEqualRaw a b) w = .ok (.ok eq) w') := by
  dsimp [defaultOps, Internal.mkRawOps]
  by_cases hne : (a.size != b.size) = true
  · simp only [hne, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inl ⟨bne_iff_ne.mp hne, _, _, rfl, rfl⟩
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    rw [io_pure_eq]
    have heq : a.size = b.size := by
      cases hsz : (a.size == b.size)
      · simp [bne, hsz] at hne
      · exact beq_iff_eq.mp hsz
    exact Or.inr ⟨heq, _, _, rfl⟩

private theorem digestRaw_never (k : CryptoHashErrorKind) (hk : k ≠ .cryptoError)
    (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind k (digestRaw alg data) w := by
  unfold Core.NeverErrorKindIO digestRaw
  rcases defaultOps_digestRaw_outcome alg data w with ⟨bs, w', hok, _⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]; trivial
  · rw [herr]; simp [hek, hk.symm]

private theorem hmacSha256Raw_never (k : CryptoHashErrorKind) (hk : k ≠ .cryptoError)
    (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind k (hmacSha256Raw key msg) w := by
  unfold Core.NeverErrorKindIO hmacSha256Raw
  rcases defaultOps_hmacSha256Raw_outcome key msg w with ⟨bs, w', hok, _⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]; trivial
  · rw [herr]; simp [hek, hk.symm]

private theorem ctEqualRaw_never (k : CryptoHashErrorKind) (hk : k ≠ .lengthMismatch)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind k (ctEqualRaw a b) w := by
  unfold Core.NeverErrorKindIO ctEqualRaw
  rcases defaultOps_ctEqualRaw_outcome a b w with ⟨_, e, w', herr, hek⟩ | ⟨_, eq, w', hok⟩
  · rw [herr]; simp [hek, hk.symm]
  · rw [hok]; trivial

/-- `Raw.digestRaw` never returns `.invalidInput`. -/
theorem raw_digestRaw_never_invalidInput (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidInput (digestRaw alg data) w :=
  digestRaw_never .invalidInput (by decide) alg data w

/-- `Raw.digestRaw` never returns `.invalidHex`. -/
theorem raw_digestRaw_never_invalidHex (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (digestRaw alg data) w :=
  digestRaw_never .invalidHex (by decide) alg data w

/-- `Raw.digestRaw` never returns `.lengthMismatch`. -/
theorem raw_digestRaw_never_lengthMismatch (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .lengthMismatch (digestRaw alg data) w :=
  digestRaw_never .lengthMismatch (by decide) alg data w

/-- `Raw.hmacSha256Raw` never returns `.invalidInput`. -/
theorem raw_hmacSha256Raw_never_invalidInput (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidInput (hmacSha256Raw key msg) w :=
  hmacSha256Raw_never .invalidInput (by decide) key msg w

/-- `Raw.hmacSha256Raw` never returns `.invalidHex`. -/
theorem raw_hmacSha256Raw_never_invalidHex (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (hmacSha256Raw key msg) w :=
  hmacSha256Raw_never .invalidHex (by decide) key msg w

/-- `Raw.hmacSha256Raw` never returns `.lengthMismatch`. -/
theorem raw_hmacSha256Raw_never_lengthMismatch (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .lengthMismatch (hmacSha256Raw key msg) w :=
  hmacSha256Raw_never .lengthMismatch (by decide) key msg w

/-- `Raw.ctEqualRaw` never returns `.invalidInput`. -/
theorem raw_ctEqualRaw_never_invalidInput (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidInput (ctEqualRaw a b) w :=
  ctEqualRaw_never .invalidInput (by decide) a b w

/-- `Raw.ctEqualRaw` never returns `.invalidHex`. -/
theorem raw_ctEqualRaw_never_invalidHex (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (ctEqualRaw a b) w :=
  ctEqualRaw_never .invalidHex (by decide) a b w

/-- `Raw.ctEqualRaw` never returns `.cryptoError`. -/
theorem raw_ctEqualRaw_never_cryptoError (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .cryptoError (ctEqualRaw a b) w :=
  ctEqualRaw_never .cryptoError (by decide) a b w

end LeanSwe.CryptoHash.Raw.Proofs

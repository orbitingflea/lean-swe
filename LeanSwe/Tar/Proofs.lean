import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.RoundTrip
import LeanSwe.Tar.Proofs.ConcretePack
import LeanSwe.Tar.Proofs.ConcreteUnpack
import LeanSwe.Tar.Proofs.ConcreteUnpackHeader

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

local macro "solve_nonempty_msg" : tactic =>
  `(tactic| (dsimp only [ToString.toString]; repeat (first | rfl | apply nonEmpty_append_left)))

local macro "close_err_nonempty" h:ident : tactic =>
  `(tactic| repeat (any_goals first | split at $h:ident | (cases $h:ident <;> solve_nonempty_msg)))

private theorem parsePaxNat_nonEmptyMsg (val : String) (offset : Nat) (key : String)
    {e : TarError} (h : parsePaxNat val offset key = .error e) : (!e.message.isEmpty) = true := by
  unfold parsePaxNat at h; dsimp only at h; close_err_nonempty h

private theorem parsePaxMtime_nonEmptyMsg (val : String) (offset : Nat)
    {e : TarError} (h : parsePaxMtime val offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parsePaxMtime at h; dsimp only at h; close_err_nonempty h

private theorem applyPaxKey_nonEmptyMsg (ov : PaxOverrides) (key val : String) (offset : Nat)
    {e : TarError} (h : applyPaxKey ov key val offset = .error e) : (!e.message.isEmpty) = true := by
  unfold applyPaxKey at h; dsimp only [Except.map] at h
  repeat (any_goals first
    | split at h
    | (cases h <;> first | solve_nonempty_msg | exact parsePaxNat_nonEmptyMsg _ _ _ ‹_› | exact parsePaxMtime_nonEmptyMsg _ _ ‹_›))

private theorem parsePaxPayload_go_nonEmptyMsg (pax : ByteArray) (offset fuel pos : Nat)
    (seenKeys : List String) (ov : PaxOverrides) {e : TarError}
    (h : parsePaxPayload.go pax offset fuel pos seenKeys ov = .error e) : (!e.message.isEmpty) = true := by
  fun_induction parsePaxPayload.go pax offset fuel pos seenKeys ov <;>
    first
      | (cases h; try (first | rfl | solve_nonempty_msg | exact applyPaxKey_nonEmptyMsg _ _ _ _ ‹_›))
      | (rename_i ih; exact ih h)

private theorem parsePaxPayload_nonEmptyMsg (pax : ByteArray) (offset : Nat)
    {e : TarError} (h : parsePaxPayload pax offset = .error e) : (!e.message.isEmpty) = true :=
  parsePaxPayload_go_nonEmptyMsg pax offset (pax.size + 1) 0 [] {} h

private theorem parseChecksumOctal_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    {e : TarError} (h : parseChecksumOctal bytes start stop offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parseChecksumOctal at h; dsimp only at h; close_err_nonempty h

private theorem parseUstarNumeric_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String)
    {e : TarError} (h : parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName = .error e) :
    (!e.message.isEmpty) = true := by
  unfold parseUstarNumeric at h; dsimp only at h; close_err_nonempty h

private theorem decodeCStringUtf8_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (fieldName : String) {e : TarError}
    (h : decodeCStringUtf8 bytes start stop offset fieldName = .error e) : (!e.message.isEmpty) = true := by
  unfold decodeCStringUtf8 at h; dsimp only at h; close_err_nonempty h

private theorem parseUstarHeader_nonEmptyMsg (bytes : ByteArray) (offset : Nat)
    {e : TarError} (h : parseUstarHeader bytes offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parseUstarHeader at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hc : parseChecksumOctal bytes (offset + 148) (offset + 156) offset <;> rw [hc] at h
  · cases h; exact parseChecksumOctal_nonEmptyMsg _ _ _ _ hc
  dsimp only at h
  iterate 2 (split at h; · cases h; solve_nonempty_msg)
  cases hm : parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode" <;> rw [hm] at h
  · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hm
  dsimp only at h
  cases hu : parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid" <;> rw [hu] at h
  · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hu
  dsimp only at h
  cases hg : parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid" <;> rw [hg] at h
  · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hg
  dsimp only at h
  cases hs : parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size" <;> rw [hs] at h
  · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hs
  dsimp only at h
  cases hmt : parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime" <;> rw [hmt] at h
  · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hmt
  cases h

private theorem decodeTarEntry_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hdr : UstarHeaderFields) (pendingPax : Option PaxOverrides)
    (seen : List String) (accLen totalBytes : Nat) {e : TarError}
    (h : decodeTarEntry opts bytes offset hdr pendingPax seen accLen totalBytes = .error e) :
    (!e.message.isEmpty) = true := by
  unfold decodeTarEntry at h
  cases hKind : (if hdr.typeflag == 0x30 || hdr.typeflag == 0x00 then some EntryKind.regular
    else if hdr.typeflag == 0x35 then some EntryKind.directory
    else if hdr.typeflag == 0x32 then some EntryKind.symlink else none) with
  | none => simp only [hKind] at h; cases h; solve_nonempty_msg
  | some kind =>
    simp only [hKind] at h
    iterate 4 (split at h; · (cases h; rfl))
    split at h
    · cases h; rename_i heqP; split at heqP
      · cases heqP
      · split at heqP <;> cases heqP <;> exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ ‹_›
    · cases h; rename_i heqL; split at heqL
      · split at heqL <;> first | exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqL | cases heqL
      · cases heqL
      · cases heqL
    · cases h; rename_i heqU; split at heqU <;> first | exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqU | cases heqU
    · cases h; rename_i heqG; split at heqG <;> first | exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqG | cases heqG
    · split at h
      · rename_i hV; cases h; exact (validateEntryPath_err_props _ _ _ _ hV).1
      · cases hk3 : kind <;> simp only [hk3] at h
        · split at h <;> cases h <;> solve_nonempty_msg
        · split at h <;> cases h <;> solve_nonempty_msg
        · split at h
          · rename_i hSym; cases h; exact (validateSymlinkTarget_err_props _ _ _ _ hSym).1
          · split at h <;> cases h <;> solve_nonempty_msg

private theorem unpackStep_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    {e : TarError} (h : unpackStep opts bytes offset pendingPax seen acc totalBytes = .error e) :
    (!e.message.isEmpty) = true := by
  unfold unpackStep at h; dsimp only at h
  split at h; · cases h; rfl
  split at h
  · iterate 4 (split at h; · cases h; rfl)
    cases h
  · split at h; · cases h; rfl
    cases hp : parseUstarHeader bytes offset with
    | error e' => rw [hp] at h; cases h; exact parseUstarHeader_nonEmptyMsg _ _ hp
    | ok hdr =>
      rw [hp] at h; dsimp only at h
      split at h
      · iterate 3 (split at h; · cases h; rfl)
        cases hpx : parsePaxPayload (bytes.extract (offset + 512) (offset + 512 + hdr.size)) offset with
        | error e' => rw [hpx] at h; cases h; exact parsePaxPayload_nonEmptyMsg _ _ hpx
        | ok _ => rw [hpx] at h; cases h
      · cases hd : decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes with
        | error e' => rw [hd] at h; cases h; exact decodeTarEntry_nonEmptyMsg _ _ _ _ _ _ _ _ hd
        | ok _ => rw [hd] at h; cases h

private theorem unpackLoopFuel_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) :
    ∀ (fuel offset : Nat) (pendingPax : Option PaxOverrides)
      (seen : List String) (acc : List TarEntry) (totalBytes : Nat) {e : TarError},
      unpackLoopFuel fuel opts bytes offset pendingPax seen acc totalBytes = .error e →
      (!e.message.isEmpty) = true := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ _ _ h; cases h; rfl
  | succ _ ih =>
    intro offset pendingPax seen acc totalBytes _ h
    unfold unpackLoopFuel at h; split at h
    · cases h; rfl
    · cases hStep : unpackStep opts bytes offset pendingPax seen acc totalBytes <;> rw [hStep] at h
      · cases h; exact unpackStep_nonEmptyMsg _ _ _ _ _ _ _ hStep
      · cases ‹UnpackStep› with
        | done _ => cases h
        | cont _ _ _ _ _ => dsimp only at h; split at h <;> first | exact ih _ _ _ _ _ h | (cases h; rfl)

private theorem unpackWith_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray)
    {e : TarError} (h : Impl.unpackWith opts bytes = .error e) : (!e.message.isEmpty) = true := by
  unfold Impl.unpackWith Impl.unpackLoop at h; split at h
  · cases h; rfl
  · exact unpackLoopFuel_nonEmptyMsg opts bytes _ 0 none [] [] 0 h

/-- Prove `test_tar_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem allPass_onError_returnsNonEmptyMessage :
    AllPass (test_tar_onError_returnsNonEmptyMessage defaultApi) := by
  intro entries packOpts bytes unpackOpts
  dsimp only [test_tar_onError_returnsNonEmptyMessage, defaultApi, Impl.makeTarApi, Impl.pack, Impl.unpack,
    Bind.bind, Pure.pure, NondetTest.assert, AllPassRun]
  cases h1 : Impl.packWith {} entries <;> (dsimp only; try refine ⟨by simpa using packWith_nonEmptyMsg {} entries h1, ?_⟩) <;>
  cases h2 : Impl.packWith packOpts entries <;> (dsimp only; try refine ⟨by simpa using packWith_nonEmptyMsg packOpts entries h2, ?_⟩) <;>
  cases h3 : Impl.unpackWith {} bytes <;> (dsimp only; try refine ⟨by simpa using unpackWith_nonEmptyMsg {} bytes h3, ?_⟩) <;>
  cases h4 : Impl.unpackWith unpackOpts bytes <;> dsimp only <;>
    first | trivial | exact ⟨by simpa using unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩

/-- Prove `test_tar_defaultWrappers_matchOptionsDefaults` for `defaultApi`. -/
theorem allPass_defaultWrappers_matchOptionsDefaults :
    AllPass (test_tar_defaultWrappers_matchOptionsDefaults defaultApi) :=
  fun _ _ => ⟨rfl, ⟨rfl, trivial⟩⟩

private theorem packWith_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.packWith opts entries) := by
  unfold Core.NeverErrorKindPure LeanSwe.Tar.packWith
  cases h : Impl.packWith opts entries with
  | ok _ => trivial
  | error _ => exact fun hek => hk (hek ▸ packWith_err_kind opts entries h)

private theorem pack_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (entries : List TarEntry) : Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.pack entries) :=
  packWith_never_of_not_packKind k hk {} entries

/-- `Tar.pack` never returns `.checksumMismatch`. -/
theorem tar_pack_never_checksumMismatch (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .checksumMismatch (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .checksumMismatch (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.truncatedArchive`. -/
theorem tar_pack_never_truncatedArchive (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .truncatedArchive (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .truncatedArchive (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.unsupportedEntry`. -/
theorem tar_pack_never_unsupportedEntry (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .unsupportedEntry (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .unsupportedEntry (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.invalidEncoding`. -/
theorem tar_pack_never_invalidEncoding (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .invalidEncoding (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .invalidEncoding (by unfold IsPackErrorKind; decide) entries

/-- `Tar.pack` never returns `.resourceLimitExceeded`. -/
theorem tar_pack_never_resourceLimitExceeded (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .resourceLimitExceeded (LeanSwe.Tar.pack entries) :=
  pack_never_of_not_packKind .resourceLimitExceeded (by unfold IsPackErrorKind; decide) entries

/-- `Tar.packWith` never returns `.checksumMismatch`. -/
theorem tar_packWith_never_checksumMismatch (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .checksumMismatch (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .checksumMismatch (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.truncatedArchive`. -/
theorem tar_packWith_never_truncatedArchive (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .truncatedArchive (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .truncatedArchive (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.unsupportedEntry`. -/
theorem tar_packWith_never_unsupportedEntry (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .unsupportedEntry (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .unsupportedEntry (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.invalidEncoding`. -/
theorem tar_packWith_never_invalidEncoding (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .invalidEncoding (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .invalidEncoding (by unfold IsPackErrorKind; decide) opts entries

/-- `Tar.packWith` never returns `.resourceLimitExceeded`. -/
theorem tar_packWith_never_resourceLimitExceeded (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind .resourceLimitExceeded (LeanSwe.Tar.packWith opts entries) :=
  packWith_never_of_not_packKind .resourceLimitExceeded (by unfold IsPackErrorKind; decide) opts entries

end LeanSwe.Tar.Proofs

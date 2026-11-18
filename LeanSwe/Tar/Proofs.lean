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

/-!
# Top-Level Tar Proof Aggregator

Re-exports all 9 modular `LeanSwe.Tar.Proofs.*` components and discharges the
universal non-empty error-message property, default wrapper equivalence, and
`pack`/`packWith` error-kind exclusion theorems for `LeanSwe.Tar`.
-/

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

local macro "solve_nonempty_msg" : tactic =>
  `(tactic| (dsimp only [ToString.toString]; repeat (first | rfl | apply nonEmpty_append_left)))

local macro "close_err_nonempty" h:ident : tactic =>
  `(tactic| repeat (any_goals first | (cases $h:ident <;> solve_nonempty_msg) | split at $h:ident))

private theorem parsePaxNat_nonEmptyMsg (val : String) (offset : Nat) (key : String)
    {e : TarError} (h : parsePaxNat val offset key = .error e) : (!e.message.isEmpty) = true := by
  unfold parsePaxNat at h
  dsimp only at h
  close_err_nonempty h

private theorem parsePaxMtime_nonEmptyMsg (val : String) (offset : Nat)
    {e : TarError} (h : parsePaxMtime val offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parsePaxMtime at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · have hTail : ∀ (fracOk : Bool) (n : Nat),
            (if !fracOk then
               Except.error { kind := TarErrorKind.invalidHeader, message := "malformed PAX mtime fraction", offset := some offset }
             else if n ≥ u64Limit then
               Except.error { kind := TarErrorKind.sizeOverflow, message := "PAX mtime overflows 2^64", offset := some offset }
             else Except.ok n) = Except.error e → (!e.message.isEmpty) = true := by
          intro fracOk n hm
          cases fracOk
          · cases hm; rfl
          · by_cases hN : n ≥ u64Limit
            · simp only [hN, ↓reduceIte] at hm; cases hm; rfl
            · simp only [hN, ↓reduceIte] at hm; cases hm
        exact hTail _ _ h

private theorem applyPaxKey_nonEmptyMsg (ov : PaxOverrides) (key val : String) (offset : Nat)
    {e : TarError} (h : applyPaxKey ov key val offset = .error e) : (!e.message.isEmpty) = true := by
  unfold applyPaxKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h <;> cases h <;> rfl
      · split at h
        · split at h <;> cases h <;> rfl
        · split at h
          · simp only [Except.map] at h; split at h <;> cases h; exact parsePaxNat_nonEmptyMsg val offset "size" ‹_›
          · split at h
            · simp only [Except.map] at h; split at h <;> cases h; exact parsePaxNat_nonEmptyMsg val offset "uid" ‹_›
            · split at h
              · simp only [Except.map] at h; split at h <;> cases h; exact parsePaxNat_nonEmptyMsg val offset "gid" ‹_›
              · split at h
                · simp only [Except.map] at h; split at h <;> cases h; exact parsePaxMtime_nonEmptyMsg val offset ‹_›
                · cases h

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
  unfold parseChecksumOctal at h
  dsimp only at h
  close_err_nonempty h

private theorem parseUstarNumeric_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String)
    {e : TarError} (h : parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName = .error e) :
    (!e.message.isEmpty) = true := by
  unfold parseUstarNumeric at h
  dsimp only at h
  close_err_nonempty h

private theorem decodeCStringUtf8_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (fieldName : String) {e : TarError}
    (h : decodeCStringUtf8 bytes start stop offset fieldName = .error e) :
    (!e.message.isEmpty) = true := by
  unfold decodeCStringUtf8 at h
  dsimp only at h
  close_err_nonempty h

private theorem parseUstarHeader_nonEmptyMsg (bytes : ByteArray) (offset : Nat)
    {e : TarError} (h : parseUstarHeader bytes offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parseUstarHeader at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  cases hChk : parseChecksumOctal bytes (offset + 148) (offset + 156) offset <;> rw [hChk] at h
  · cases h; exact parseChecksumOctal_nonEmptyMsg _ _ _ _ hChk
  · dsimp only at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases hM : parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode" <;> rw [hM] at h
        · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hM
        · dsimp only at h
          cases hU : parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid" <;> rw [hU] at h
          · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hU
          · dsimp only at h
            cases hG : parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid" <;> rw [hG] at h
            · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hG
            · dsimp only at h
              cases hS : parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size" <;> rw [hS] at h
              · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hS
              · dsimp only at h
                cases hT : parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime" <;> rw [hT] at h
                · cases h; exact parseUstarNumeric_nonEmptyMsg _ _ _ _ _ _ _ hT
                · cases h

private theorem checkSegments_nonEmptyMsg (allowTrav : Bool) (segs : List (List Char))
    {e : TarError} (h : checkSegments allowTrav segs = .error e) : (!e.message.isEmpty) = true := by
  unfold checkSegments at h
  split at h
  · cases h; rfl
  · suffices ∀ xs {e'}, checkSegments.go allowTrav xs = .error e' → (!e'.message.isEmpty) = true from this _ h
    intro xs
    induction xs with
    | nil => intro e' hx; simp [checkSegments.go] at hx
    | cons x rest ih =>
      intro e' hx
      unfold checkSegments.go at hx
      close_err_nonempty hx <;> exact ih hx

private theorem validateEntryPath_nonEmptyMsg (allowAbs allowTrav : Bool) (kind : EntryKind) (path : String)
    {e : TarError} (h : validateEntryPath allowAbs allowTrav kind path = .error e) :
    (!e.message.isEmpty) = true := by
  unfold validateEntryPath at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · cases h; exact match_1_nonEmptyMsg ‹_›
        · split at h
          · rename_i eSeg hSeg
            cases h
            have hne := checkSegments_nonEmptyMsg allowTrav _ hSeg
            exact hne
          · cases h
where
  match_1_nonEmptyMsg {kind : EntryKind} {path : String} {e : TarError} :
      (match kind with
       | .directory =>
         let stripped := stripTrailingSlashesChars path.toList
         if stripped.isEmpty then
           Except.error { kind := .invalidPath, message := "directory tar path cannot be root-only", entryPath := some path }
         else Except.ok stripped
       | .regular | .symlink =>
         if path.toList.reverse.head? == some '/' then
           Except.error { kind := .invalidPath, message := "non-directory tar path cannot end with '/'", entryPath := some path }
         else Except.ok path.toList) = Except.error e → (!e.message.isEmpty) = true := by
    intro hm
    cases kind <;> simp only at hm <;> split at hm <;> cases hm <;> rfl

private theorem validateSymlinkTarget_nonEmptyMsg (allowAbs allowTrav : Bool) (ep lt : String)
    {e : TarError} (h : validateSymlinkTarget allowAbs allowTrav ep lt = .error e) :
    (!e.message.isEmpty) = true := by
  unfold validateSymlinkTarget at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · cases h
        · suffices ∀ d xs {e'}, validateSymlinkTarget.walkDepth ep d xs = .error e' → (!e'.message.isEmpty) = true
            from this _ _ h
          intro d xs
          induction xs generalizing d with
          | nil => intro e' hx; simp [validateSymlinkTarget.walkDepth] at hx
          | cons seg rest ih =>
            intro e' hx
            unfold validateSymlinkTarget.walkDepth at hx
            split at hx
            · exact ih d hx
            · split at hx
              · split at hx
                · cases hx; rfl
                · exact ih (d - 1) hx
              · exact ih (d + 1) hx

private theorem decodeTarEntry_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hdr : UstarHeaderFields) (pendingPax : Option PaxOverrides)
    (seen : List String) (accLen totalBytes : Nat) {e : TarError}
    (h : decodeTarEntry opts bytes offset hdr pendingPax seen accLen totalBytes = .error e) :
    (!e.message.isEmpty) = true := by
  unfold decodeTarEntry at h
  cases hKind : (if hdr.typeflag == 0x30 || hdr.typeflag == 0x00 then some EntryKind.regular
    else if hdr.typeflag == 0x35 then some EntryKind.directory
    else if hdr.typeflag == 0x32 then some EntryKind.symlink
    else none) with
  | none =>
    simp only [hKind] at h
    cases h; solve_nonempty_msg
  | some kind =>
    simp only [hKind] at h
    by_cases h1 : (kind != EntryKind.regular && (pendingPax.getD {}).size?.getD hdr.size != 0) = true
    · simp only [h1] at h; cases h; rfl
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : accLen + 1 > opts.maxEntries
      · simp only [h2, ↓reduceIte] at h; cases h; rfl
      · simp only [h2, ↓reduceIte] at h
        by_cases h3 : totalBytes + (pendingPax.getD {}).size?.getD hdr.size > opts.maxTotalBytes
        · simp only [h3, ↓reduceIte] at h; cases h; rfl
        · simp only [h3, ↓reduceIte] at h
          by_cases h4 : offset + 512 + pad512 ((pendingPax.getD {}).size?.getD hdr.size) > bytes.size
          · simp only [h4, ↓reduceIte] at h; cases h; rfl
          · simp only [h4, ↓reduceIte] at h
            split at h
            · cases h
              rename_i heqP
              split at heqP
              · cases heqP
              · split at heqP <;> cases heqP <;> exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ ‹_›
            · cases h
              rename_i heqL
              split at heqL
              · split at heqL
                · cases heqL
                · exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqL
              · cases heqL
              · cases heqL
            · cases h
              rename_i heqU
              split at heqU
              · cases heqU
              · exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqU
            · cases h
              rename_i heqG
              split at heqG
              · cases heqG
              · exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ heqG
            · split at h
              · rename_i eV hV
                cases h
                have hne := validateEntryPath_nonEmptyMsg _ _ _ _ hV
                exact hne
              · cases hk3 : kind <;> simp only [hk3] at h
                · split at h
                  · cases h; solve_nonempty_msg
                  · cases h
                · split at h
                  · cases h; solve_nonempty_msg
                  · cases h
                · split at h
                  · rename_i eS hSym
                    cases h
                    have hne := validateSymlinkTarget_nonEmptyMsg _ _ _ _ hSym
                    exact hne
                  · split at h
                    · cases h; solve_nonempty_msg
                    · cases h

private theorem unpackStep_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    {e : TarError} (h : unpackStep opts bytes offset pendingPax seen acc totalBytes = .error e) :
    (!e.message.isEmpty) = true := by
  unfold unpackStep at h
  split at h
  · cases h; rfl
  · split at h
    · repeat (first | split at h <;> try (cases h; try rfl))
    · split at h
      · cases h; rfl
      · cases hHdr : parseUstarHeader bytes offset <;> rw [hHdr] at h
        · cases h; exact parseUstarHeader_nonEmptyMsg _ _ hHdr
        · dsimp only at h
          split at h
          · split at h
            · cases h; rfl
            · split at h
              · cases h; rfl
              · split at h
                · cases h; rfl
                · cases hPax : parsePaxPayload (bytes.extract (offset + 512) (offset + 512 + ‹UstarHeaderFields›.size)) offset <;>
                    rw [hPax] at h
                  · cases h; exact parsePaxPayload_nonEmptyMsg _ _ hPax
                  · cases h
          · cases hDec : decodeTarEntry opts bytes offset ‹_› pendingPax seen acc.length totalBytes <;>
              rw [hDec] at h
            · cases h; exact decodeTarEntry_nonEmptyMsg _ _ _ _ _ _ _ _ hDec
            · cases h

private theorem unpackLoopFuel_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) :
    ∀ (fuel offset : Nat) (pendingPax : Option PaxOverrides)
      (seen : List String) (acc : List TarEntry) (totalBytes : Nat) {e : TarError},
      unpackLoopFuel fuel opts bytes offset pendingPax seen acc totalBytes = .error e →
      (!e.message.isEmpty) = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; cases h; rfl
  | succ fuel ih =>
    intro offset pendingPax seen acc totalBytes e h
    unfold unpackLoopFuel at h
    split at h
    · cases h; rfl
    · cases hStep : unpackStep opts bytes offset pendingPax seen acc totalBytes <;> rw [hStep] at h
      · cases h; exact unpackStep_nonEmptyMsg _ _ _ _ _ _ _ hStep
      · cases ‹UnpackStep› with
        | done res => cases h
        | cont no np ns na nt =>
          dsimp only at h
          split at h
          · exact ih _ _ _ _ _ h
          · cases h; rfl

private theorem unpackWith_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray)
    {e : TarError} (h : Impl.unpackWith opts bytes = .error e) : (!e.message.isEmpty) = true := by
  unfold Impl.unpackWith at h
  split at h
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
    AllPass (test_tar_defaultWrappers_matchOptionsDefaults defaultApi) := by
  intro entries bytes
  exact ⟨rfl, ⟨rfl, trivial⟩⟩

private theorem packWith_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (opts : PackOptions) (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.packWith opts entries) := by
  unfold Core.NeverErrorKindPure LeanSwe.Tar.packWith
  cases h : Impl.packWith opts entries with
  | ok _ => trivial
  | error e =>
    dsimp only
    intro hek
    exact hk (hek ▸ packWith_err_kind opts entries h)

private theorem pack_never_of_not_packKind (k : TarErrorKind) (hk : ¬IsPackErrorKind k)
    (entries : List TarEntry) :
    Core.NeverErrorKindPure TarError.kind k (LeanSwe.Tar.pack entries) := by
  unfold Core.NeverErrorKindPure LeanSwe.Tar.pack Impl.pack
  exact packWith_never_of_not_packKind k hk {} entries

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

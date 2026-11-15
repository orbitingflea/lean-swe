import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.Universal
import LeanSwe.Tar.Proofs.Concrete

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem nonEmpty_append_left {a b : String} (ha : (!a.isEmpty) = true) :
    (!(a ++ b).isEmpty) = true := by
  have hPos : 0 < a.utf8ByteSize := by
    cases h0 : a.utf8ByteSize with
    | zero =>
      exfalso
      have he : a.isEmpty = true := by simp [String.isEmpty, h0]
      rw [he] at ha
      contradiction
    | succ _ => omega
  have hSum : (a ++ b).utf8ByteSize = a.utf8ByteSize + b.utf8ByteSize :=
    String.utf8ByteSize_append
  cases hEmp : (a ++ b).isEmpty
  · rfl
  · exfalso
    have hEq : a ++ b = "" := String.isEmpty_iff.mp hEmp
    have hSize : (a ++ b).utf8ByteSize = 0 := by rw [hEq]; rfl
    omega

/-- Solve non-empty error message goals by descending left through string concatenation. -/
local macro "solve_nonempty_msg" : tactic =>
  `(tactic| (dsimp only [ToString.toString]; repeat (first | rfl | apply nonEmpty_append_left)))

private theorem parsePaxNat_nonEmptyMsg (val : String) (offset : Nat) (key : String)
    {e : TarError} (h : parsePaxNat val offset key = .error e) : (!e.message.isEmpty) = true := by
  unfold parsePaxNat at h
  dsimp only at h
  split at h
  · cases h; solve_nonempty_msg
  · split at h
    · cases h; solve_nonempty_msg
    · split at h
      · cases h; solve_nonempty_msg
      · split at h
        · cases h; solve_nonempty_msg
        · cases h

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

private theorem parsePaxPayload_go_nonEmptyMsg (pax : ByteArray) (offset pos : Nat)
    (seenKeys : List String) (ov : PaxOverrides) {e : TarError}
    (h : parsePaxPayload.go pax offset pos seenKeys ov = .error e) : (!e.message.isEmpty) = true := by
  fun_induction parsePaxPayload.go pax offset pos seenKeys ov with
  | case1 => simp at h
  | case2 => cases h; rfl
  | case3 => cases h; rfl
  | case4 => cases h; rfl
  | case5 => cases h; rfl
  | case6 => cases h; rfl
  | case7 => cases h; rfl
  | case8 => cases h; rfl
  | case9 => cases h; rfl
  | case10 => cases h; rfl
  | case11 => cases h; solve_nonempty_msg
  | case12 => cases h; rfl
  | case13 =>
    cases h
    exact applyPaxKey_nonEmptyMsg _ _ _ _ ‹_›
  | case14 =>
    rename_i ih
    exact ih h

private theorem parseChecksumOctal_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    {e : TarError} (h : parseChecksumOctal bytes start stop offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parseChecksumOctal at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

private theorem parseUstarNumeric_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String)
    {e : TarError} (h : parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName = .error e) :
    (!e.message.isEmpty) = true := by
  unfold parseUstarNumeric at h
  dsimp only at h
  split at h
  · cases h; solve_nonempty_msg
  · split at h
    · split at h
      · cases h; solve_nonempty_msg
      · split at h
        · cases h; solve_nonempty_msg
        · cases h
    · split at h
      · split at h
        · cases h
        · cases h; solve_nonempty_msg
      · split at h
        · cases h; solve_nonempty_msg
        · split at h
          · cases h; solve_nonempty_msg
          · split at h
            · cases h; solve_nonempty_msg
            · cases h

private theorem decodeCStringUtf8_nonEmptyMsg (bytes : ByteArray) (start stop offset : Nat)
    (fieldName : String) {e : TarError}
    (h : decodeCStringUtf8 bytes start stop offset fieldName = .error e) :
    (!e.message.isEmpty) = true := by
  unfold decodeCStringUtf8 at h
  dsimp only at h
  split at h
  · cases h
  · cases h; solve_nonempty_msg

private theorem parseUstarHeader_nonEmptyMsg (bytes : ByteArray) (offset : Nat)
    {e : TarError} (h : parseUstarHeader bytes offset = .error e) : (!e.message.isEmpty) = true := by
  unfold parseUstarHeader at h
  cases hChk : parseChecksumOctal bytes (offset + 148) (offset + 156) offset <;> rw [hChk] at h
  · cases h; exact parseChecksumOctal_nonEmptyMsg _ _ _ _ hChk
  · dsimp only at h
    cases hEq : (‹Nat› != ustarChecksumAt bytes offset) <;> rw [hEq] at h
    · cases hMagic : (!hasValidMagic bytes offset) <;> rw [hMagic] at h
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
      · cases h; rfl
    · cases h; rfl

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
      split at hx
      · cases hx; rfl
      · split at hx
        · cases hx; rfl
        · split at hx
          · cases hx; rfl
          · exact ih hx

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

private theorem packWith_go_nonEmptyMsg (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) {e : TarError}
    (h : packWith.go opts rest seen acc = .error e) : (!e.message.isEmpty) = true := by
  induction rest generalizing seen acc with
  | nil => simp [packWith.go] at h
  | cons hd tl ih =>
    unfold packWith.go at h
    cases hPath : validateEntryPath opts.allowAbsolute opts.allowParentTraversal hd.kind hd.path with
    | error eP =>
      rw [hPath] at h; cases h; exact validateEntryPath_nonEmptyMsg _ _ _ _ hPath
    | ok normPath =>
      rw [hPath] at h
      dsimp only at h
      have finishRest :
          ∀ {b1 b2 b3 b4 : Bool},
            (if b1 = true then
               Except.error { kind := TarErrorKind.invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some hd.path }
             else if b2 = true then
               Except.error { kind := TarErrorKind.invalidHeader, message := "non-symlink tar entry cannot have linkTarget", entryPath := some hd.path }
             else if b3 = true then
               Except.error { kind := TarErrorKind.invalidHeader, message := "uname/gname cannot contain NUL byte", entryPath := some hd.path }
             else if b4 = true then
               Except.error { kind := TarErrorKind.sizeOverflow, message := "tar entry numeric field exceeds 2^64 - 1", entryPath := some hd.path }
             else if seen.contains normPath = true then
               Except.error { kind := TarErrorKind.duplicatePath, message := toString "duplicate tar entry path: " ++ toString normPath, entryPath := some normPath }
             else packWith.go opts tl (normPath :: seen) (acc ++ encodeEntryBlocks (if opts.deterministic = true then zeroDeterministicMeta hd else hd) normPath)) = Except.error e →
            (!e.message.isEmpty) = true := by
        intro b1 b2 b3 b4 hr
        split at hr
        · cases hr; rfl
        · split at hr
          · cases hr; rfl
          · split at hr
            · cases hr; rfl
            · split at hr
              · cases hr; rfl
              · split at hr
                · cases hr; solve_nonempty_msg
                · exact ih _ _ hr
      cases hk : hd.kind <;> rw [hk] at h <;> dsimp only at h
      · exact finishRest h
      · exact finishRest h
      · cases hSym : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath hd.linkTarget <;> rw [hSym] at h
        · cases h; exact validateSymlinkTarget_nonEmptyMsg _ _ _ _ hSym
        · dsimp only at h; exact finishRest h

private theorem packWith_nonEmptyMsg (opts : PackOptions) (entries : List TarEntry)
    {e : TarError} (h : Impl.packWith opts entries = .error e) : (!e.message.isEmpty) = true :=
  packWith_go_nonEmptyMsg opts entries [] ByteArray.empty h

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
              · split at heqP
                · cases heqP; exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ ‹_›
                · cases heqP; exact decodeCStringUtf8_nonEmptyMsg _ _ _ _ _ ‹_›
                · cases heqP
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
          cases hTy : (‹UstarHeaderFields›.typeflag == 120)
          · simp only [hTy, Bool.false_eq_true, ↓reduceIte] at h
            cases hDec : decodeTarEntry opts bytes offset ‹_› pendingPax seen acc.length totalBytes <;> rw [hDec] at h
            · cases h; exact decodeTarEntry_nonEmptyMsg _ _ _ _ _ _ _ _ hDec
            · cases h
          · simp only [hTy, ↓reduceIte] at h
            by_cases hPend : pendingPax.isSome = true
            · simp only [hPend] at h; cases h; rfl
            · simp only [hPend] at h
              by_cases hMax : ‹UstarHeaderFields›.size > maxPaxHeaderBytes
              · simp only [hMax, ↓reduceIte] at h; cases h; rfl
              · simp only [hMax, ↓reduceIte] at h
                by_cases hTr : offset + 512 + pad512 ‹UstarHeaderFields›.size > bytes.size
                · simp only [hTr, ↓reduceIte] at h; cases h; rfl
                · simp only [hTr, ↓reduceIte] at h
                  cases hPax : parsePaxPayload (bytes.extract (offset + 512) (offset + 512 + ‹UstarHeaderFields›.size)) offset <;> rw [hPax] at h
                  · cases h; exact parsePaxPayload_go_nonEmptyMsg _ _ _ _ _ hPax
                  · cases h

private theorem unpackLoop_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    {e : TarError} (h : unpackLoop opts bytes offset pendingPax seen acc totalBytes = .error e) :
    (!e.message.isEmpty) = true := by
  fun_induction unpackLoop opts bytes offset pendingPax seen acc totalBytes with
  | case1 => cases h; rfl
  | case2 =>
    cases h
    exact unpackStep_nonEmptyMsg _ _ _ _ _ _ _ ‹_›
  | case3 => cases h
  | case4 =>
    rename_i ih
    exact ih h
  | case5 => cases h; rfl

private theorem unpackWith_nonEmptyMsg (opts : UnpackOptions) (bytes : ByteArray)
    {e : TarError} (h : Impl.unpackWith opts bytes = .error e) : (!e.message.isEmpty) = true := by
  unfold Impl.unpackWith at h
  split at h
  · cases h; rfl
  · exact unpackLoop_nonEmptyMsg opts bytes 0 none [] [] 0 h

/-- Prove `test_tar_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem allPass_onError_returnsNonEmptyMessage :
    AllPass (test_tar_onError_returnsNonEmptyMessage defaultApi) := by
  intro entries packOpts bytes unpackOpts
  dsimp only [AllPassRun, test_tar_onError_returnsNonEmptyMessage, Bind.bind, Pure.pure,
    NondetTest.assert, defaultApi, Impl.makeTarApi, Impl.pack, Impl.unpack]
  cases h1 : Impl.packWith {} entries with
  | ok _ =>
    dsimp only
    cases h2 : Impl.packWith packOpts entries with
    | ok _ =>
      dsimp only
      cases h3 : Impl.unpackWith {} bytes with
      | ok _ =>
        dsimp only
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
      | error e3 =>
        refine ⟨unpackWith_nonEmptyMsg {} bytes h3, ?_⟩
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
    | error e2 =>
      refine ⟨packWith_nonEmptyMsg packOpts entries h2, ?_⟩
      cases h3 : Impl.unpackWith {} bytes with
      | ok _ =>
        dsimp only
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
      | error e3 =>
        refine ⟨unpackWith_nonEmptyMsg {} bytes h3, ?_⟩
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
  | error e1 =>
    refine ⟨packWith_nonEmptyMsg {} entries h1, ?_⟩
    cases h2 : Impl.packWith packOpts entries with
    | ok _ =>
      dsimp only
      cases h3 : Impl.unpackWith {} bytes with
      | ok _ =>
        dsimp only
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
      | error e3 =>
        refine ⟨unpackWith_nonEmptyMsg {} bytes h3, ?_⟩
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
    | error e2 =>
      refine ⟨packWith_nonEmptyMsg packOpts entries h2, ?_⟩
      cases h3 : Impl.unpackWith {} bytes with
      | ok _ =>
        dsimp only
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩
      | error e3 =>
        refine ⟨unpackWith_nonEmptyMsg {} bytes h3, ?_⟩
        cases h4 : Impl.unpackWith unpackOpts bytes with
        | ok _ => trivial
        | error e4 => exact ⟨unpackWith_nonEmptyMsg unpackOpts bytes h4, trivial⟩

/-- Prove `test_tar_defaultWrappers_matchOptionsDefaults` for `defaultApi`. -/
theorem allPass_defaultWrappers_matchOptionsDefaults :
    AllPass (test_tar_defaultWrappers_matchOptionsDefaults defaultApi) := by
  intro entries bytes
  exact ⟨rfl, ⟨rfl, trivial⟩⟩

end LeanSwe.Tar.Proofs

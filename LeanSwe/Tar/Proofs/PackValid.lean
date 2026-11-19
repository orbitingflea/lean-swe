import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Predicate characterizing every `TarErrorKind` that `Impl.packWith` / `Impl.pack` can emit. -/
def IsPackErrorKind (k : TarErrorKind) : Prop :=
  k = .invalidPath ∨ k = .unsafePath ∨ k = .invalidHeader ∨ k = .sizeOverflow ∨ k = .duplicatePath

local macro "solve_pack_err" : tactic =>
  `(tactic| refine ⟨by dsimp only [ToString.toString]; repeat (first | rfl | apply nonEmpty_append_left),
    by simp [IsPackErrorKind]⟩)

local macro "close_err_nonempty" h:ident : tactic =>
  `(tactic| repeat (any_goals first | (cases $h:ident <;> solve_pack_err) | split at $h:ident))

private theorem checkSegments_err_props (allowPar : Bool) (segs : List (List Char))
    {e : TarError} (h : checkSegments allowPar segs = .error e) :
    (!e.message.isEmpty) = true ∧ IsPackErrorKind e.kind := by
  unfold checkSegments at h; split at h
  · cases h; solve_pack_err
  · suffices ∀ xs {e'}, checkSegments.go allowPar xs = .error e' →
        (!e'.message.isEmpty) = true ∧ IsPackErrorKind e'.kind from this _ h
    intro xs; induction xs with
    | nil => intro _ hx; cases hx
    | cons _ _ ih =>
      intro _ hx; rw [checkSegments.go.eq_2] at hx
      iterate 3 (split at hx; · (cases hx; solve_pack_err))
      exact ih hx

/-- Every `validateEntryPath` error has a non-empty message and an allowed pack error kind. -/
theorem validateEntryPath_err_props (allowAbs allowPar : Bool) (kind : EntryKind)
    (path : String) {e : TarError} (h : validateEntryPath allowAbs allowPar kind path = .error e) :
    (!e.message.isEmpty) = true ∧ IsPackErrorKind e.kind := by
  unfold validateEntryPath at h; dsimp only at h
  iterate 3 (split at h; · (cases h; solve_pack_err))
  split at h
  · rename_i hm; cases h; cases kind <;> dsimp only at hm <;> close_err_nonempty hm
  · split at h
    · rename_i hc; cases h; simpa using checkSegments_err_props allowPar _ hc
    · cases h

/-- Every `validateSymlinkTarget` error has a non-empty message and an allowed pack error kind. -/
theorem validateSymlinkTarget_err_props (allowAbs allowPar : Bool)
    (entryPath linkTarget : String) {e : TarError}
    (h : validateSymlinkTarget allowAbs allowPar entryPath linkTarget = .error e) :
    (!e.message.isEmpty) = true ∧ IsPackErrorKind e.kind := by
  unfold validateSymlinkTarget at h; dsimp only at h
  iterate 3 (split at h; · (cases h; solve_pack_err))
  split at h
  · cases h
  · suffices ∀ d xs {e'}, validateSymlinkTarget.walkDepth entryPath d xs = .error e' →
        (!e'.message.isEmpty) = true ∧ IsPackErrorKind e'.kind from this _ _ h
    intro d xs; induction xs generalizing d with
    | nil => intro _ hx; cases hx
    | cons _ _ ih =>
      intro _ hx; rw [validateSymlinkTarget.walkDepth.eq_2] at hx
      split at hx; · exact ih d hx
      split at hx
      · split at hx
        · cases hx; solve_pack_err
        · exact ih (d - 1) hx
      · exact ih (d + 1) hx

/-- Every `validatePackEntry` error has a non-empty message and an allowed pack error kind. -/
theorem validatePackEntry_err_props (opts : PackOptions) (e : TarEntry)
    {err : TarError} (h : validatePackEntry opts e = .error err) :
    (!err.message.isEmpty) = true ∧ IsPackErrorKind err.kind := by
  unfold validatePackEntry at h
  change (validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path >>= _) = .error err at h
  rw [except_bind_eq_error] at h
  rcases h with hv | ⟨_, _, hs⟩
  · exact validateEntryPath_err_props _ _ _ _ hv
  · dsimp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hs
    cases hk : e.kind <;> simp only [hk] at hs
    · close_err_nonempty hs
    · close_err_nonempty hs
    · rw [except_bind_eq_error] at hs
      rcases hs with hsym | ⟨_, _, hif⟩
      · exact validateSymlinkTarget_err_props _ _ _ _ hsym
      · close_err_nonempty hif

private theorem packWith_go_err_props (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) {e : TarError}
    (h : packWith.go opts rest seen acc = .error e) :
    (!e.message.isEmpty) = true ∧ IsPackErrorKind e.kind := by
  induction rest generalizing seen acc with
  | nil => rw [packWith.go.eq_1] at h; cases h
  | cons entry _ ih =>
    rw [packWith.go.eq_2] at h; dsimp only at h
    cases hv : validatePackEntry opts entry with
    | error _ => rw [hv] at h; cases h; exact validatePackEntry_err_props opts entry hv
    | ok _ =>
      rw [hv] at h; dsimp only at h; split at h
      · cases h; solve_pack_err
      · exact ih _ _ h

/-- Every error returned by `Impl.packWith` has a non-empty message. -/
theorem packWith_nonEmptyMsg (opts : PackOptions) (entries : List TarEntry) {e : TarError}
    (h : Impl.packWith opts entries = .error e) : (!e.message.isEmpty) = true :=
  (packWith_go_err_props opts entries [] ByteArray.empty h).1

/-- Every error returned by `Impl.packWith` has an allowed pack `TarErrorKind`. -/
theorem packWith_err_kind (opts : PackOptions) (entries : List TarEntry) {e : TarError}
    (h : Impl.packWith opts entries = .error e) : IsPackErrorKind e.kind :=
  (packWith_go_err_props opts entries [] ByteArray.empty h).2

private theorem list_dropWhile_idemp {α : Type} (p : α → Bool) (xs : List α) :
    (xs.dropWhile p).dropWhile p = xs.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons x _ ih => rw [List.dropWhile_cons]; cases hp : p x <;> simp [hp, ih]

private theorem stripTrailingSlashesChars_idemp (cs : List Char) :
    stripTrailingSlashesChars (stripTrailingSlashesChars cs) = stripTrailingSlashesChars cs := by
  simp only [stripTrailingSlashesChars, List.reverse_reverse, list_dropWhile_idemp]

private theorem stripTrailingSlashesChars_cons (a : Char) (rest : List Char) :
    stripTrailingSlashesChars (a :: rest) =
      if (stripTrailingSlashesChars rest).isEmpty then (if a == '/' then [] else [a])
      else a :: stripTrailingSlashesChars rest := by
  unfold stripTrailingSlashesChars; rw [List.reverse_cons, List.dropWhile_append]
  rcases rest.reverse.dropWhile (· == '/') with _ | ⟨_, _⟩
  · cases h : (a == '/') <;> simp [List.dropWhile, h]
  · simp

private theorem not_hasNulChars_stripTrailing {cs : List Char} (h : hasNulChars cs = false) :
    hasNulChars (stripTrailingSlashesChars cs) = false := by
  induction cs with
  | nil => rfl
  | cons a _ ih =>
    simp only [hasNulChars, Bool.or_eq_false_iff] at h; rw [stripTrailingSlashesChars_cons]
    split
    · split <;> simp [hasNulChars, h.1]
    · simp [hasNulChars, h.1, ih h.2]

private theorem stripTrailingSlashesChars_head {cs : List Char}
    (hne : (stripTrailingSlashesChars cs).isEmpty = false) :
    (stripTrailingSlashesChars cs).head? = cs.head? := by
  cases cs with
  | nil => contradiction
  | cons a rest =>
    rw [stripTrailingSlashesChars_cons] at hne ⊢
    cases h1 : (stripTrailingSlashesChars rest).isEmpty <;> cases h2 : (a == '/') <;> simp [h1, h2] at hne ⊢

/-- When `validateEntryPath` succeeds, it returns `normalizeTarPath kind path`. -/
theorem validateEntryPath_normPath {allowAbs allowPar : Bool} {kind : EntryKind} {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    normPath = normalizeTarPath kind path := by
  unfold validateEntryPath at h; dsimp only at h
  iterate 4 (split at h; · cases h)
  rename_i _ heq; split at h; · cases h
  cases h; cases kind <;> unfold normalizeTarPath <;> dsimp only at heq ⊢ <;> split at heq <;> cases heq
  · exact String.ofList_toList
  · rfl
  · exact String.ofList_toList

/-- `validateEntryPath` is idempotent on its normalized output and preserves `normalizeTarPath`. -/
theorem validateEntryPath_idemp {allowAbs allowPar : Bool} {kind : EntryKind} {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    validateEntryPath allowAbs allowPar kind normPath = .ok normPath ∧
    normalizeTarPath kind normPath = normPath ∧ !hasNulString normPath = true := by
  have hnp := validateEntryPath_normPath h
  have hnoNul : hasNulChars path.toList = false := by
    unfold validateEntryPath at h; dsimp only at h; cases hn : hasNulChars path.toList <;> simp [hn] at h; rfl
  cases kind with
  | regular | symlink => subst hnp; exact ⟨h, rfl, by simp [hasNulString, hnoNul]⟩
  | directory =>
    unfold validateEntryPath at h; dsimp only at h
    iterate 3 (split at h; · cases h)
    rename_i _ _ hnotAbs; split at h; · cases h
    rename_i _ heq; split at heq; · cases heq
    rename_i hne_st; cases heq; split at h; · cases h
    rename_i hchk; cases h
    have hne_stF : (stripTrailingSlashesChars path.toList).isEmpty = false := Bool.eq_false_iff.mpr hne_st
    have hnoNul_st := not_hasNulChars_stripTrailing hnoNul
    refine ⟨?_, by simp only [normalizeTarPath, String.toList_ofList, stripTrailingSlashesChars_idemp],
      by simp [hasNulString, String.toList_ofList, hnoNul_st]⟩
    unfold validateEntryPath; dsimp only; rw [String.toList_ofList]
    simp only [hnoNul_st, Bool.false_eq_true, ↓reduceIte, hne_stF, stripTrailingSlashesChars_head hne_stF,
      hnotAbs, stripTrailingSlashesChars_idemp, hchk]

/-- Validating `wirePathOf kind normPath` reproduces `normPath` and has no NUL bytes. -/
theorem validateEntryPath_wirePathOf {allowAbs allowPar : Bool} {kind : EntryKind} {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    validateEntryPath allowAbs allowPar kind (wirePathOf kind normPath) = .ok normPath ∧
    !hasNulString (wirePathOf kind normPath) = true := by
  have ⟨hid, _, hnul⟩ := validateEntryPath_idemp h
  cases kind with
  | regular | symlink => exact ⟨hid, hnul⟩
  | directory =>
    have hnoNul_nm : hasNulChars normPath.toList = false := by
      cases hc : hasNulChars normPath.toList <;> simp [hasNulString, hc] at hnul; rfl
    have hnoNulF : hasNulChars (normPath ++ "/").toList = false := by
      rw [String.toList_append, hasNulChars_append, hnoNul_nm]; rfl
    have hstrip_wp : stripTrailingSlashesChars (normPath ++ "/").toList =
        stripTrailingSlashesChars normPath.toList := by
      simp only [stripTrailingSlashesChars, String.toList_append]
      change ((normPath.toList ++ ['/']).reverse.dropWhile (· == '/')).reverse = _; rw [List.reverse_append]; rfl
    unfold validateEntryPath at hid; dsimp only at hid
    iterate 3 (split at hid; · cases hid)
    rename_i _ hne_nm hnotAbs
    have hne_wp : (normPath ++ "/").toList.isEmpty = false := by rw [String.toList_append]; cases normPath.toList <;> simp
    have hhead_wp : (normPath ++ "/").toList.head? = normPath.toList.head? := by
      rw [String.toList_append]; cases hnl : normPath.toList <;> first | rfl | simp [hnl] at hne_nm
    split at hid; · cases hid
    rename_i _ heq; split at heq; · cases heq
    rename_i hne_st; cases heq; split at hid; · cases hid
    rename_i hchk
    refine ⟨?_, by rw [wirePathOf, hasNulString, hnoNulF]; rfl⟩
    change validateEntryPath allowAbs allowPar .directory (normPath ++ "/") = .ok normPath
    unfold validateEntryPath; dsimp only
    simp only [hnoNulF, Bool.false_eq_true, ↓reduceIte, hne_wp, hhead_wp, hnotAbs,
      hstrip_wp, Bool.eq_false_iff.mpr hne_st, hchk, Except.ok.inj hid]

private theorem checkSegments_mono {p1 p2 : Bool} (hp : (!p1 || p2) = true)
    (segs : List (List Char)) (h : checkSegments p1 segs = .ok ()) : checkSegments p2 segs = .ok () := by
  unfold checkSegments at h ⊢; cases segs with
  | nil => cases h
  | cons _ _ =>
    suffices ∀ xs, checkSegments.go p1 xs = .ok () → checkSegments.go p2 xs = .ok () from this _ h
    intro xs; induction xs with
    | nil => exact id
    | cons s _ ih =>
      intro hx; rw [checkSegments.go.eq_2] at hx ⊢
      iterate 3 (split at hx; · cases hx)
      rename_i h1 h2 _; have h3' : (s == ['.', '.'] && !p2) = false := by cases p1 <;> cases p2 <;> simp_all
      simp only [h1, h2, h3', Bool.false_eq_true, ↓reduceIte]; exact ih hx

private theorem validateEntryPath_mono {a1 a2 p1 p2 : Bool} (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true)
    {kind : EntryKind} {path normPath : String}
    (h : validateEntryPath a1 p1 kind path = .ok normPath) : validateEntryPath a2 p2 kind path = .ok normPath := by
  unfold validateEntryPath at h ⊢; dsimp only at h ⊢
  iterate 3 (split at h; · cases h)
  rename_i h1 h2 _; have h3' : (path.toList.head? == some '/' && !a2) = false := by cases a1 <;> cases a2 <;> simp_all
  simp only [h1, h2, h3', Bool.false_eq_true, ↓reduceIte]
  iterate 2 (split at h; · cases h)
  rename_i hchk; simp only [checkSegments_mono hp _ hchk, h]

private theorem validateSymlinkTarget_mono {a1 a2 p1 p2 : Bool} (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true)
    {entryPath linkTarget : String}
    (h : validateSymlinkTarget a1 p1 entryPath linkTarget = .ok ()) :
    validateSymlinkTarget a2 p2 entryPath linkTarget = .ok () := by
  unfold validateSymlinkTarget at h ⊢; dsimp only at h ⊢
  iterate 3 (split at h; · cases h)
  rename_i h1 h2 _; have h3' : (linkTarget.toList.head? == some '/' && !a2) = false := by cases a1 <;> cases a2 <;> simp_all
  simp only [h1, h2, h3', Bool.false_eq_true, ↓reduceIte]; cases p1 <;> cases p2 <;> simp_all

/-- Monotonicity of `validArchiveBool` with respect to security options. -/
theorem validArchiveBool_mono {a1 a2 p1 p2 : Bool} (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true)
    (es : List TarEntry) (h : validArchiveBool a1 p1 es = true) : validArchiveBool a2 p2 es = true := by
  unfold validArchiveBool at h ⊢; rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨fun e he => ?_, h.2⟩
  have hve := h.1 e he; unfold validEntryBool at hve ⊢
  cases hv : validateEntryPath a1 p1 e.kind e.path with
  | error _ => rw [hv] at hve; cases hve
  | ok np =>
    rw [hv] at hve; rw [validateEntryPath_mono ha hp hv]; dsimp only at hve ⊢
    cases hk : e.kind <;> simp only [hk] at hve ⊢
    · exact hve
    · exact hve
    · cases hs : validateSymlinkTarget a1 p1 np e.linkTarget with
      | error _ => rw [hs] at hve; cases hve
      | ok _ => rw [hs] at hve; rw [validateSymlinkTarget_mono ha hp hs]; exact hve

/-- Preservation of `validArchiveBool` under `zeroDeterministicMeta`. -/
theorem validArchiveBool_map_zeroDeterministicMeta {a p : Bool} {es : List TarEntry}
    (h : validArchiveBool a p es = true) : validArchiveBool a p (es.map zeroDeterministicMeta) = true := by
  unfold validArchiveBool at h ⊢; rw [Bool.and_eq_true] at h ⊢; refine ⟨?_, ?_⟩
  · rw [List.all_map, List.all_eq_true]; rw [List.all_eq_true] at h; intro e he
    have hve := h.1 e he; unfold validEntryBool at hve ⊢
    dsimp only [Function.comp_def, zeroDeterministicMeta] at hve ⊢
    cases hv : validateEntryPath a p e.kind e.path with
    | error _ => simp [hv] at hve
    | ok _ =>
      have h0 : decide (0 < u64Limit) = true := by decide
      have hn : !hasNulString "" = true := by decide
      simp only [hv, Bool.and_eq_true] at hve ⊢
      exact ⟨hve.1, ⟨⟨⟨⟨⟨hn, hn⟩, h0⟩, h0⟩, h0⟩, hve.2.2⟩⟩
  · suffices ∀ seen xs, noDupNormalizedPathsBool.go seen (xs.map zeroDeterministicMeta) =
        noDupNormalizedPathsBool.go seen xs from (this [] es).trans h.2
    intro seen xs; induction xs generalizing seen with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, noDupNormalizedPathsBool.go]; exact congrArg (_ && ·) (ih _)

/-- Preservation of `fitsPaxLimit` under `zeroDeterministicMeta`. -/
theorem fitsPaxLimit_zeroDeterministicMeta {e : TarEntry}
    (h : fitsPaxLimit e = true) : fitsPaxLimit (zeroDeterministicMeta e) = true := by
  let wp := wirePathOf e.kind (normalizeTarPath e.kind e.path)
  have hasc : (!isAsciiString "") = false := by simp [isAsciiString]
  have hsz0 : "".toUTF8.size = 0 := rfl
  have h32 : decide (0 > 32) = false := rfl
  have h7 : ¬(0 ≥ ustarOctal7Limit) := by decide
  have h11 : ¬(0 ≥ ustarOctal11Limit) := by decide
  unfold fitsPaxLimit at h ⊢
  change (if needsPax (zeroDeterministicMeta e) wp then _ else true) = true
  by_cases hnz : needsPax (zeroDeterministicMeta e) wp = true
  · simp only [hnz, ↓reduceIte]
    have hne : needsPax e wp = true := by
      rcases e with ⟨_, _, _, _, _, _, _, _, _, _⟩
      unfold needsPax at hnz ⊢; dsimp only [zeroDeterministicMeta] at hnz
      simp only [hasc, hsz0, h32, h7, h11, decide_false, Bool.or_false] at hnz
      simp only [Bool.or_eq_true] at hnz ⊢
      rcases hnz with ((h1 | h2) | h3) | h4 <;> simp_all [wp]
    have hlim : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes := by
      change (if needsPax e wp then _ else true) = true at h; simpa [hne] using h
    have hle : (buildPaxPayload (zeroDeterministicMeta e) wp).size ≤ (buildPaxPayload e wp).size := by
      rcases e with ⟨_, _, _, _, _, _, _, _, _, _⟩
      unfold buildPaxPayload zeroDeterministicMeta; dsimp only
      simp only [hasc, hsz0, h32, h7, h11, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        ByteArray.size_append, ByteArray.size_empty]; omega
    exact decide_eq_true (Nat.le_trans hle hlim)
  · simp [hnz]

private theorem ite_throw_eq_ok {ε α} (c : Bool) (err : ε) (rest : Except ε α) (v : α) :
    (if c then Except.error err else rest) = .ok v ↔ c = false ∧ rest = .ok v := by cases c <;> simp

private theorem validatePackEntry_eq_ok_iff (opts : PackOptions) (e : TarEntry) (np : String) :
    validatePackEntry opts e = .ok np ↔
      validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path = .ok np ∧
      (match e.kind with
        | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget
        | .regular | .directory => .ok ()) = .ok () ∧
      (e.kind != .regular && e.data.size != 0) = false ∧ (e.kind != .symlink && e.linkTarget != "") = false ∧
      (hasNulString e.uname || hasNulString e.gname) = false ∧
      (e.uid ≥ u64Limit || e.gid ≥ u64Limit || e.mtime ≥ u64Limit || e.data.size ≥ u64Limit) = false := by
  unfold validatePackEntry
  change (validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path >>= _) = .ok np ↔ _
  rw [except_bind_eq_ok]; dsimp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  constructor
  · rintro ⟨_, hv, hrest⟩
    cases hk : e.kind <;> simp only [hk, except_bind_eq_ok, PUnit.eq_punit, exists_const,
        ite_throw_eq_ok, Except.ok.injEq] at hv hrest ⊢
    · rcases hrest with ⟨c1, c2, c3, c4, rfl⟩; exact ⟨hv, trivial, c1, c2, c3, c4⟩
    · rcases hrest with ⟨c1, c2, c3, c4, rfl⟩; exact ⟨hv, trivial, c1, c2, c3, c4⟩
    · rcases hrest with ⟨hsym, c1, c2, c3, c4, rfl⟩; exact ⟨hv, hsym, c1, c2, c3, c4⟩
  · rintro ⟨hv, hsym, c1, c2, c3, c4⟩; refine ⟨np, hv, ?_⟩
    cases hk : e.kind <;> simp only [hk, except_bind_eq_ok, PUnit.eq_punit, exists_const, ite_throw_eq_ok] at hsym c1 c2 ⊢
    · exact ⟨c1, c2, c3, c4, trivial⟩
    · exact ⟨c1, c2, c3, c4, trivial⟩
    · exact ⟨hsym, c1, c2, c3, c4, trivial⟩

/-- If `validatePackEntry` succeeds with `np`, then `np = normalizeTarPath e.kind e.path`. -/
theorem validatePackEntry_ok_eq (opts : PackOptions) (e : TarEntry) {np : String}
    (h : validatePackEntry opts e = .ok np) : np = normalizeTarPath e.kind e.path :=
  validateEntryPath_normPath ((validatePackEntry_eq_ok_iff opts e np).mp h).1

/-- `validatePackEntry opts e` succeeds iff `validEntryBool` holds for `e`. -/
theorem validatePackEntry_ok_iff (opts : PackOptions) (e : TarEntry) :
    (∃ np, validatePackEntry opts e = .ok np) ↔
      validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true := by
  simp only [validatePackEntry_eq_ok_iff]; unfold validEntryBool
  cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | error _ => simp
  | ok normPath =>
    simp only [Except.ok.injEq]; constructor
    · rintro ⟨np, rfl, hsym, hdata, hlink, hnul, hu64⟩
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hnul hu64
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, ?_⟩, ⟨⟨⟨⟨⟨by simp [hnul.1], by simp [hnul.2]⟩, hu64.1.1.1⟩, hu64.1.1.2⟩, hu64.1.2⟩, hu64.2⟩⟩
      · cases hk : e.kind <;> simp only [hk] at hsym hlink ⊢
        · cases hl : e.linkTarget == "" <;> simp [bne, hl] at hlink <;> first | rfl | cases hlink
        · cases hl : e.linkTarget == "" <;> simp [bne, hl] at hlink <;> first | rfl | cases hlink
        · rw [hsym]
      · cases hk : e.kind <;> simp only [hk] at hdata ⊢ <;>
          (cases hd : e.data.size == 0 <;> simp [bne, hd] at hdata <;> first | rfl | cases hdata)
    · intro hve; simp only [Bool.and_eq_true, decide_eq_true_eq] at hve
      rcases hve with ⟨⟨hsym, hdata⟩, ⟨⟨⟨⟨⟨hu, hg⟩, huid⟩, hgid⟩, hmtime⟩, hsz⟩⟩
      refine ⟨normPath, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · cases hk : e.kind <;> simp only [hk] at hsym ⊢
        cases hs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath e.linkTarget with
        | error _ => rw [hs] at hsym; cases hsym
        | ok _ => rfl
      · cases hk : e.kind <;> simp only [hk] at hdata ⊢ <;> first | rfl | simp [bne, hdata]
      · cases hk : e.kind <;> simp only [hk] at hsym ⊢ <;> first | rfl | simp [bne, hsym]
      · cases h1 : hasNulString e.uname <;> cases h2 : hasNulString e.gname <;> simp_all
      · simp [Nat.not_le_of_lt huid, Nat.not_le_of_lt hgid, Nat.not_le_of_lt hmtime, Nat.not_le_of_lt hsz]

/-- Full functional specification of `Impl.packWith.go`. -/
theorem packWith_go_spec (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) :
    (∀ out, packWith.go opts rest seen acc = .ok out →
      (rest.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
        noDupNormalizedPathsBool.go seen rest) = true ∧
      out = acc ++
        (rest.foldl (fun b e => b ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta e else e)
          (normalizeTarPath e.kind e.path)) ByteArray.empty) ++ (zeroBlock ++ zeroBlock)) ∧
    ((rest.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
        noDupNormalizedPathsBool.go seen rest) = true →
      ∃ out, packWith.go opts rest seen acc = .ok out) := by
  let enc (e : TarEntry) := encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta e else e)
    (normalizeTarPath e.kind e.path)
  have hfold : ∀ (init : ByteArray) (xs : List TarEntry),
      xs.foldl (fun b e => b ++ enc e) init = init ++ xs.foldl (fun b e => b ++ enc e) ByteArray.empty := by
    intro init xs; induction xs generalizing init with
    | nil => simp only [List.foldl_nil, ByteArray.append_empty]
    | cons _ _ ihx => simp only [List.foldl_cons, ByteArray.empty_append]; rw [ihx, ihx (enc _), ByteArray.append_assoc]
  induction rest generalizing seen acc with
  | nil =>
    exact ⟨fun out hout => by
        rw [packWith.go.eq_1] at hout; cases hout
        exact ⟨rfl, by rw [List.foldl_nil, ByteArray.append_empty, ByteArray.append_assoc]⟩,
      fun _ => ⟨acc ++ zeroBlock ++ zeroBlock, rfl⟩⟩
  | cons entry tail ih =>
    constructor
    · intro out hout; rw [packWith.go.eq_2] at hout; dsimp only at hout
      cases hv : validatePackEntry opts entry with
      | error _ => rw [hv] at hout; cases hout
      | ok normPath =>
        rw [hv] at hout; dsimp only at hout
        have hnp := validatePackEntry_ok_eq opts entry hv
        have hve := (validatePackEntry_ok_iff opts entry).mp ⟨normPath, hv⟩
        split at hout; · cases hout
        rename_i hndup
        have ⟨hand_t, hout_eq⟩ := (ih (normPath :: seen)
          (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)).1 out hout
        rw [Bool.and_eq_true] at hand_t
        have hndup_b : (!seen.contains normPath) = true := by rw [Bool.eq_false_iff.mpr hndup]; rfl
        refine ⟨?_, ?_⟩
        · simp only [List.all_cons, noDupNormalizedPathsBool.go.eq_2, Bool.and_eq_true, ← hnp]
          exact ⟨⟨hve, hand_t.1⟩, hndup_b, hand_t.2⟩
        · change (out = acc ++ (entry :: tail).foldl (fun b e => b ++ enc e) ByteArray.empty ++ (zeroBlock ++ zeroBlock))
          rw [hout_eq, List.foldl_cons, ByteArray.empty_append, hfold (enc entry) tail]
          dsimp only [enc]; rw [← hnp]; repeat rw [ByteArray.append_assoc]
    · intro hvalid
      simp only [Bool.and_eq_true, List.all_cons, noDupNormalizedPathsBool.go.eq_2] at hvalid
      rcases hvalid with ⟨⟨hve, hall_t⟩, hnot_seen, hnodup_t⟩
      obtain ⟨np, hv⟩ := (validatePackEntry_ok_iff opts entry).mpr hve
      rw [validatePackEntry_ok_eq opts entry hv] at hv
      let normPath := normalizeTarPath entry.kind entry.path
      have hseen_f : seen.contains normPath = false :=
        Bool.eq_false_iff.mpr fun hc => by rw [hc] at hnot_seen; cases hnot_seen
      obtain ⟨out, hout⟩ := (ih (normPath :: seen)
        (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)).2
        (by rw [Bool.and_eq_true]; exact ⟨hall_t, hnodup_t⟩)
      exact ⟨out, by rw [packWith.go.eq_2, hv]; dsimp only; simp only [normPath, hseen_f, Bool.false_eq_true, ↓reduceIte]; exact hout⟩

/-- Prove `test_tar_packWith_iffValidArchive` for `defaultApi`. -/
theorem allPass_packWith_iffValidArchive : AllPass (test_tar_packWith_iffValidArchive defaultApi) := by
  dsimp [AllPass, test_tar_packWith_iffValidArchive, Bind.bind, Pure.pure,
    NondetTest.nondet, NondetTest.assert, defaultApi, makeTarApi]
  intro opts entries
  cases h : Impl.packWith opts entries with
  | ok out => exact ⟨((packWith_go_spec opts entries [] ByteArray.empty).1 out h).1, trivial⟩
  | error _ =>
    refine ⟨⟨fun hv => ?_, packWith_nonEmptyMsg opts entries h⟩, trivial⟩
    obtain ⟨out, hout⟩ := (packWith_go_spec opts entries [] ByteArray.empty).2 hv
    unfold Impl.packWith at h; rw [h] at hout; cases hout

end LeanSwe.Tar.Proofs

import LeanSwe.Tar.Proofs.ByteModel

namespace LeanSwe.Tar.Proofs

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

private theorem validatePackEntry_err_props (opts : PackOptions) (e : TarEntry)
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

/-- Every error returned by `Impl.packWith` has an allowed pack `TarErrorKind`. -/
theorem packWith_err_kind (opts : PackOptions) (entries : List TarEntry) {e : TarError}
    (h : Impl.packWith opts entries = .error e) : IsPackErrorKind e.kind :=
  (packWith_go_err_props opts entries [] ByteArray.empty h).2

end LeanSwe.Tar.Proofs

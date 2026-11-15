import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers

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

private theorem checkSegments_go_nonEmptyMsg (allowPar : Bool) (segs : List (List Char))
    {e : TarError} (h : checkSegments.go allowPar segs = .error e) : (!e.message.isEmpty) = true := by
  induction segs with
  | nil => rw [checkSegments.go.eq_1] at h; cases h
  | cons seg rest ih =>
    rw [checkSegments.go.eq_2] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · exact ih h

private theorem checkSegments_nonEmptyMsg (allowPar : Bool) (segs : List (List Char))
    {e : TarError} (h : checkSegments allowPar segs = .error e) : (!e.message.isEmpty) = true := by
  unfold checkSegments at h
  cases segs with
  | nil => cases h; rfl
  | cons seg rest => exact checkSegments_go_nonEmptyMsg allowPar (seg :: rest) h

private theorem validateEntryPath_nonEmptyMsg (allowAbs allowPar : Bool) (kind : EntryKind)
    (path : String) {e : TarError} (h : validateEntryPath allowAbs allowPar kind path = .error e) :
    (!e.message.isEmpty) = true := by
  unfold validateEntryPath at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases hk : kind <;> simp only [hk] at h
        · split at h
          · rename_i heq
            cases h
            split at heq <;> cases heq; rfl
          · split at h
            · rename_i ce hc
              cases h
              simpa using checkSegments_nonEmptyMsg allowPar _ hc
            · cases h
        · split at h
          · rename_i heq
            cases h
            split at heq <;> cases heq; rfl
          · split at h
            · rename_i ce hc
              cases h
              simpa using checkSegments_nonEmptyMsg allowPar _ hc
            · cases h
        · split at h
          · rename_i heq
            cases h
            split at heq <;> cases heq; rfl
          · split at h
            · rename_i ce hc
              cases h
              simpa using checkSegments_nonEmptyMsg allowPar _ hc
            · cases h

private theorem walkDepth_nonEmptyMsg (entryPath : String) (depth : Nat)
    (segs : List (List Char)) {e : TarError}
    (h : validateSymlinkTarget.walkDepth entryPath depth segs = .error e) :
    (!e.message.isEmpty) = true := by
  induction segs generalizing depth with
  | nil => rw [validateSymlinkTarget.walkDepth.eq_1] at h; cases h
  | cons seg rest ih =>
    rw [validateSymlinkTarget.walkDepth.eq_2] at h
    split at h
    · exact ih depth h
    · split at h
      · split at h
        · cases h; rfl
        · exact ih (depth - 1) h
      · exact ih (depth + 1) h

private theorem validateSymlinkTarget_nonEmptyMsg (allowAbs allowPar : Bool)
    (entryPath linkTarget : String) {e : TarError}
    (h : validateSymlinkTarget allowAbs allowPar entryPath linkTarget = .error e) :
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
        · exact walkDepth_nonEmptyMsg entryPath _ _ h

private theorem packWith_go_nonEmptyMsg (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) {e : TarError}
    (h : packWith.go opts rest seen acc = .error e) : (!e.message.isEmpty) = true := by
  induction rest generalizing seen acc with
  | nil => rw [packWith.go.eq_1] at h; cases h
  | cons entry tail ih =>
    rw [packWith.go.eq_2] at h
    dsimp only at h
    cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal entry.kind entry.path with
    | error ev =>
      rw [hv] at h; cases h
      exact validateEntryPath_nonEmptyMsg _ _ _ _ hv
    | ok normPath =>
      rw [hv] at h
      dsimp only at h
      have hsym : ∀ u, (match entry.kind with
          | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath entry.linkTarget
          | .regular | .directory => Except.ok ()) = u →
          (match u with
          | .error err => Except.error err
          | .ok () =>
            if (entry.kind != EntryKind.regular && entry.data.size != 0) = true then
              Except.error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some entry.path }
            else if (entry.kind != EntryKind.symlink && entry.linkTarget != "") = true then
              Except.error { kind := .invalidHeader, message := "non-symlink tar entry cannot have linkTarget", entryPath := some entry.path }
            else if (hasNulString entry.uname || hasNulString entry.gname) = true then
              Except.error { kind := .invalidHeader, message := "uname/gname cannot contain NUL byte", entryPath := some entry.path }
            else if (entry.uid ≥ u64Limit || entry.gid ≥ u64Limit || entry.mtime ≥ u64Limit || entry.data.size ≥ u64Limit) = true then
              Except.error { kind := .sizeOverflow, message := "tar entry numeric field exceeds 2^64 - 1", entryPath := some entry.path }
            else if seen.contains normPath = true then
              Except.error { kind := .duplicatePath, message := s!"duplicate tar entry path: {normPath}", entryPath := some normPath }
            else
              packWith.go opts tail (normPath :: seen) (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)) = .error e →
          (!e.message.isEmpty) = true := by
        intro u hu hm
        cases u with
        | error se =>
          cases hm
          cases hk : entry.kind with
          | regular => simp only [hk] at hu; cases hu
          | directory => simp only [hk] at hu; cases hu
          | symlink =>
            simp only [hk] at hu
            exact validateSymlinkTarget_nonEmptyMsg _ _ _ _ hu
        | ok _ =>
          dsimp only at hm
          split at hm
          · cases hm; rfl
          · split at hm
            · cases hm; rfl
            · split at hm
              · cases hm; rfl
              · split at hm
                · cases hm; rfl
                · split at hm
                  · cases hm; exact nonEmpty_append_left rfl
                  · exact ih (normPath :: seen) _ hm
      exact hsym _ rfl h

private theorem list_dropWhile_idemp {α : Type} (p : α → Bool) (xs : List α) :
    (xs.dropWhile p).dropWhile p = xs.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.dropWhile_cons]
    cases hp : p x
    · simp [hp]
    · exact ih

private theorem stripTrailingSlashesChars_idemp (cs : List Char) :
    stripTrailingSlashesChars (stripTrailingSlashesChars cs) = stripTrailingSlashesChars cs := by
  simp only [stripTrailingSlashesChars, List.reverse_reverse, list_dropWhile_idemp]

private theorem mem_dropWhile {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (h : x ∈ xs.dropWhile p) : x ∈ xs := by
  induction xs with
  | nil => cases h
  | cons a rest ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact List.mem_cons_of_mem a (ih h)
    · exact h

private theorem mem_stripTrailingSlashesChars {c : Char} {cs : List Char}
    (h : c ∈ stripTrailingSlashesChars cs) : c ∈ cs := by
  simp only [stripTrailingSlashesChars, List.mem_reverse] at h
  exact List.mem_reverse.mp (mem_dropWhile h)

private theorem not_hasNulChars_stripTrailing {cs : List Char} (h : hasNulChars cs = false) :
    hasNulChars (stripTrailingSlashesChars cs) = false := by
  rw [hasNulChars_false_iff] at h ⊢
  intro hin
  exact h (mem_stripTrailingSlashesChars hin)

private theorem dropWhile_eq_nil_of_forall {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : xs.dropWhile p = [] := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.dropWhile_cons, h a (by simp)]
    exact ih (fun x hx => h x (by simp [hx]))

private theorem forall_of_dropWhile_eq_nil {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.dropWhile p = []) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · rename_i hpa
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hrest
      · exact hpa
      · exact ih h x hrest
    · cases h

private theorem stripTrailingSlashesChars_head {cs : List Char}
    (hne : (stripTrailingSlashesChars cs).isEmpty = false) :
    (stripTrailingSlashesChars cs).head? = cs.head? := by
  have ⟨c0, hc0_mem, hc0_ne⟩ : ∃ c0 ∈ cs, c0 ≠ '/' :=
    Classical.byContradiction fun hnone => by
      have hall : ∀ c ∈ cs, (c == '/') = true := fun c hc =>
        Classical.byContradiction fun hne' =>
          hnone ⟨c, hc, fun heq => hne' (beq_iff_eq.mpr heq)⟩
      have hdrop : cs.reverse.dropWhile (· == '/') = [] :=
        dropWhile_eq_nil_of_forall fun x hx => hall x (List.mem_reverse.mp hx)
      have hemp : stripTrailingSlashesChars cs = [] := by
        simp [stripTrailingSlashesChars, hdrop]
      rw [hemp] at hne
      contradiction
  cases cs with
  | nil => contradiction
  | cons a rest =>
    by_cases ha : a = '/'
    · subst ha
      have ⟨c1, hc1_mem, hc1_ne⟩ : ∃ c1 ∈ rest, c1 ≠ '/' := by
        rcases List.mem_cons.mp hc0_mem with rfl | hc0_rest
        · exact absurd rfl hc0_ne
        · exact ⟨c0, hc0_rest, hc0_ne⟩
      have hdrop_app : (rest.reverse ++ ['/']).dropWhile (· == '/') =
          rest.reverse.dropWhile (· == '/') ++ ['/'] := by
        rw [List.dropWhile_append]
        have hne_nil : rest.reverse.dropWhile (· == '/') ≠ [] := by
          intro hnil
          have hc1_rev : c1 ∈ rest.reverse := List.mem_reverse.mpr hc1_mem
          have hall := forall_of_dropWhile_eq_nil hnil c1 hc1_rev
          exact hc1_ne (beq_iff_eq.mp hall)
        simp [hne_nil]
      have hst : stripTrailingSlashesChars ('/' :: rest) =
          '/' :: stripTrailingSlashesChars rest := by
        simp only [stripTrailingSlashesChars, List.reverse_cons, hdrop_app, List.reverse_append,
          List.reverse_cons, List.reverse_nil, List.nil_append]
        rfl
      rw [hst]
      rfl
    · have hbeq : (a == '/') = false := Bool.eq_false_iff.mpr (fun heq => ha (beq_iff_eq.mp heq))
      have hdrop_app : (rest.reverse ++ [a]).dropWhile (· == '/') =
          rest.reverse.dropWhile (· == '/') ++ [a] := by
        rw [List.dropWhile_append]
        by_cases hnil : rest.reverse.dropWhile (· == '/') = []
        · simp [hnil, hbeq]
        · simp [hnil]
      have hst : stripTrailingSlashesChars (a :: rest) =
          a :: stripTrailingSlashesChars rest := by
        simp only [stripTrailingSlashesChars, List.reverse_cons, hdrop_app, List.reverse_append,
          List.reverse_cons, List.reverse_nil, List.nil_append]
        rfl
      rw [hst]
      rfl

private theorem stripTrailingSlashesChars_not_end_slash (cs : List Char) :
    (stripTrailingSlashesChars cs).reverse.head? ≠ some '/' := by
  simp only [stripTrailingSlashesChars, List.reverse_reverse]
  intro h
  have hmem : ∀ l : List Char, (l.dropWhile (· == '/')).head? = some '/' → False := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons a rs ih =>
      rw [List.dropWhile_cons] at hl
      split at hl
      · exact ih hl
      · rename_i hne
        cases hl
        simp at hne
  exact hmem cs.reverse h

/-- When `validateEntryPath` succeeds, it returns `normalizeTarPath kind path`. -/
theorem validateEntryPath_normPath {allowAbs allowPar : Bool} {kind : EntryKind}
    {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    normPath = normalizeTarPath kind path := by
  unfold validateEntryPath at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases kind with
          | directory =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · cases heq
              split at h
              · cases h
              · cases h
                rfl
          | regular =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · cases heq
              split at h
              · cases h
              · cases h
                exact String.ofList_toList
          | symlink =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · cases heq
              split at h
              · cases h
              · cases h
                exact String.ofList_toList

/-- `validateEntryPath` is idempotent on its normalized output and preserves `normalizeTarPath`. -/
theorem validateEntryPath_idemp {allowAbs allowPar : Bool} {kind : EntryKind}
    {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    validateEntryPath allowAbs allowPar kind normPath = .ok normPath ∧
    normalizeTarPath kind normPath = normPath ∧
    !hasNulString normPath = true := by
  unfold validateEntryPath at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hnoNul
    have hnoNulF : hasNulChars path.toList = false := Bool.eq_false_iff.mpr hnoNul
    split at h
    · cases h
    · rename_i hne_cs
      split at h
      · cases h
      · rename_i hnotAbs
        split at h
        · cases h
        · cases kind with
          | directory =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · rename_i hne_strip
              cases heq
              split at h
              · cases h
              · rename_i hchk
                cases h
                have hne_stripF : (stripTrailingSlashesChars path.toList).isEmpty = false :=
                  Bool.eq_false_iff.mpr hne_strip
                have hnoNul_norm : hasNulChars (stripTrailingSlashesChars path.toList) = false :=
                  not_hasNulChars_stripTrailing hnoNulF
                have hhead_norm : (stripTrailingSlashesChars path.toList).head? = path.toList.head? :=
                  stripTrailingSlashesChars_head hne_stripF
                have hnorm_id : normalizeTarPath .directory (String.ofList (stripTrailingSlashesChars path.toList)) =
                    String.ofList (stripTrailingSlashesChars path.toList) := by
                  simp only [normalizeTarPath, String.toList_ofList, stripTrailingSlashesChars_idemp]
                refine ⟨?_, hnorm_id, by simp [hasNulString, String.toList_ofList, hnoNul_norm]⟩
                unfold validateEntryPath
                dsimp only
                rw [String.toList_ofList]
                simp only [hnoNul_norm, Bool.false_eq_true, ↓reduceIte, hne_stripF, hhead_norm, hnotAbs,
                  stripTrailingSlashesChars_idemp, hchk]
          | regular =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · rename_i hnoEnd
              cases heq
              split at h
              · cases h
              · rename_i hchk
                cases h
                rw [String.ofList_toList] at *
                refine ⟨?_, rfl, by simp [hasNulString, hnoNulF]⟩
                unfold validateEntryPath
                dsimp only
                simp only [hnoNulF, Bool.false_eq_true, ↓reduceIte, Bool.eq_false_iff.mpr hne_cs, hnotAbs, hnoEnd, hchk, String.ofList_toList]
          | symlink =>
            dsimp only at *
            rename_i normChars heq
            split at heq
            · cases heq
            · rename_i hnoEnd
              cases heq
              split at h
              · cases h
              · rename_i hchk
                cases h
                rw [String.ofList_toList] at *
                refine ⟨?_, rfl, by simp [hasNulString, hnoNulF]⟩
                unfold validateEntryPath
                dsimp only
                simp only [hnoNulF, Bool.false_eq_true, ↓reduceIte, Bool.eq_false_iff.mpr hne_cs, hnotAbs, hnoEnd, hchk, String.ofList_toList]

/-- Validating `wirePathOf kind normPath` reproduces `normPath` and has no NUL bytes. -/
theorem validateEntryPath_wirePathOf {allowAbs allowPar : Bool} {kind : EntryKind}
    {path normPath : String}
    (h : validateEntryPath allowAbs allowPar kind path = .ok normPath) :
    validateEntryPath allowAbs allowPar kind (wirePathOf kind normPath) = .ok normPath ∧
    !hasNulString (wirePathOf kind normPath) = true := by
  have ⟨hid, hnorm, hnul⟩ := validateEntryPath_idemp h
  cases kind with
  | regular => exact ⟨hid, hnul⟩
  | symlink => exact ⟨hid, hnul⟩
  | directory =>
    have hnul_slash : (!hasNulString "/") = true := by decide
    have hnul_norm : (!hasNulString normPath) = true := by
      cases hc : hasNulString normPath <;> simp_all
    have hnul_wp : !hasNulString (normPath ++ "/") = true := by
      have happ : (!hasNulString (normPath ++ "/")) = true := by
        rw [not_hasNulString_append, hnul_norm, hnul_slash]; rfl
      cases hc : hasNulString (normPath ++ "/") <;> simp_all
    have hnoNulF : hasNulChars (normPath ++ "/").toList = false := by
      have hn : hasNulString (normPath ++ "/") = false := by cases hc : hasNulString (normPath ++ "/") <;> simp_all
      exact hn
    have hstrip_wp : stripTrailingSlashesChars (normPath ++ "/").toList =
        stripTrailingSlashesChars normPath.toList := by
      simp only [stripTrailingSlashesChars, String.toList_append]
      have hsl : "/".toList = ['/'] := rfl
      rw [hsl, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.dropWhile_cons]
      rfl
    have hne_wp : (normPath ++ "/").toList.isEmpty = false := by
      rw [String.toList_append]
      cases normPath.toList <;> simp
    have hhead_wp : (normPath ++ "/").toList.head? = normPath.toList.head? := by
      rw [String.toList_append]
      cases hnl : normPath.toList with
      | nil =>
        exfalso
        unfold validateEntryPath at hid
        simp [hnl, hasNulChars] at hid
      | cons c cs => rfl
    have hhid := hid
    unfold validateEntryPath at hhid
    dsimp only at hhid
    split at hhid
    · cases hhid
    · split at hhid
      · cases hhid
      · split at hhid
        · cases hhid
        · rename_i hnotAbs
          split at hhid
          · cases hhid
          · rename_i hne_st
            split at hhid
            · cases hhid
            · rename_i hchk
              have hne_st_f : (stripTrailingSlashesChars normPath.toList).isEmpty = false := by
                cases hc : (stripTrailingSlashesChars normPath.toList).isEmpty <;> simp [hc] at hne_st ⊢
              simp only [hne_st_f, Bool.false_eq_true, ↓reduceIte] at hne_st
              have hnc_eq := Except.ok.inj hne_st
              subst hnc_eq
              have hstr_eq := Except.ok.inj hhid
              have hval_wp : validateEntryPath allowAbs allowPar .directory (normPath ++ "/") =
                  .ok normPath := by
                unfold validateEntryPath
                dsimp only
                simp only [hnoNulF, Bool.false_eq_true, ↓reduceIte, hne_wp, hhead_wp, hnotAbs,
                  hstrip_wp, hne_st_f, hchk, hstr_eq]
              exact ⟨hval_wp, hnul_wp⟩

private theorem checkSegments_go_mono {p1 p2 : Bool} (hp : (!p1 || p2) = true)
    (segs : List (List Char)) (h : checkSegments.go p1 segs = .ok ()) :
    checkSegments.go p2 segs = .ok () := by
  induction segs with
  | nil => exact h
  | cons s rs ih =>
    rw [checkSegments.go.eq_2] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hne1 hne2 hnot_par
          have hnot_par2 : (s == ['.', '.'] && !p2) = false := by
            cases p1 <;> cases p2 <;> simp_all
          simp only [hne1, ↓reduceIte, hne2, hnot_par2, Bool.false_eq_true]
          exact ih h

private theorem checkSegments_mono {p1 p2 : Bool} (hp : (!p1 || p2) = true)
    (segs : List (List Char)) (h : checkSegments p1 segs = .ok ()) :
    checkSegments p2 segs = .ok () := by
  unfold checkSegments at h ⊢
  cases segs with
  | nil => cases h
  | cons seg rest => exact checkSegments_go_mono hp (seg :: rest) h

private theorem validateEntryPath_mono {a1 a2 p1 p2 : Bool}
    (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true)
    {kind : EntryKind} {path normPath : String}
    (h : validateEntryPath a1 p1 kind path = .ok normPath) :
    validateEntryPath a2 p2 kind path = .ok normPath := by
  unfold validateEntryPath at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hnoNul hne hnotAbs
        have hnotAbs2 : (path.toList.head? == some '/' && !a2) = false := by
          cases a1 <;> cases a2 <;> simp_all
        simp only [hnoNul, ↓reduceIte, hne, hnotAbs2, Bool.false_eq_true]
        split at h
        · cases h
        · rename_i normChars heq
          split at h
          · cases h
          · rename_i hchk
            have hchk2 := checkSegments_mono hp _ hchk
            simp only [hchk2]
            exact h

private theorem validateSymlinkTarget_mono {a1 a2 p1 p2 : Bool}
    (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true)
    {entryPath linkTarget : String}
    (h : validateSymlinkTarget a1 p1 entryPath linkTarget = .ok ()) :
    validateSymlinkTarget a2 p2 entryPath linkTarget = .ok () := by
  unfold validateSymlinkTarget at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hne hnoNul hnotAbs
        have hnotAbs2 : (linkTarget.toList.head? == some '/' && !a2) = false := by
          cases a1 <;> cases a2 <;> simp_all
        simp only [hne, ↓reduceIte, hnoNul, hnotAbs2, Bool.false_eq_true]
        cases p1 <;> cases p2
        · exact h
        · simp
        · simp at hp
        · exact h

private theorem validEntryBool_mono {a1 a2 p1 p2 : Bool}
    (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true) (e : TarEntry)
    (h : validEntryBool a1 p1 e = true) : validEntryBool a2 p2 e = true := by
  unfold validEntryBool at h ⊢
  cases hv : validateEntryPath a1 p1 e.kind e.path with
  | error _ => rw [hv] at h; cases h
  | ok normPath =>
    rw [hv] at h
    rw [validateEntryPath_mono ha hp hv]
    dsimp only at h ⊢
    cases hk : e.kind <;> simp only [hk] at h ⊢
    · exact h
    · exact h
    · cases hs : validateSymlinkTarget a1 p1 normPath e.linkTarget with
      | error _ => rw [hs] at h; cases h
      | ok _ =>
        rw [hs] at h
        rw [validateSymlinkTarget_mono ha hp hs]
        exact h

/-- Monotonicity of `validArchiveBool` with respect to security options. -/
theorem validArchiveBool_mono {a1 a2 p1 p2 : Bool}
    (ha : (!a1 || a2) = true) (hp : (!p1 || p2) = true) (es : List TarEntry)
    (h : validArchiveBool a1 p1 es = true) : validArchiveBool a2 p2 es = true := by
  unfold validArchiveBool at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, h.2⟩
  rw [List.all_eq_true] at h ⊢
  intro e he
  exact validEntryBool_mono ha hp e (h.1 e he)

private theorem validEntryBool_zeroDeterministicMeta {a p : Bool} {e : TarEntry}
    (h : validEntryBool a p e = true) :
    validEntryBool a p (zeroDeterministicMeta e) = true := by
  unfold validEntryBool at h ⊢
  simp only [zeroDeterministicMeta] at h ⊢
  have hlt : decide (0 < u64Limit) = true := by decide
  have hnul : !hasNulString "" = true := by decide
  cases hv : validateEntryPath a p e.kind e.path with
  | error _ => rw [hv] at h; cases h
  | ok normPath =>
    simp only [hv, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hsz⟩
    exact ⟨⟨⟨⟨⟨hnul, hnul⟩, hlt⟩, hlt⟩, hlt⟩, hsz⟩

private theorem noDupNormalizedPathsBool_go_map_zeroDet (seen : List String) (es : List TarEntry) :
    noDupNormalizedPathsBool.go seen (es.map zeroDeterministicMeta) =
      noDupNormalizedPathsBool.go seen es := by
  induction es generalizing seen with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, noDupNormalizedPathsBool.go.eq_2, zeroDeterministicMeta, normalizeTarPath]
    cases hmem : seen.contains (match e.kind with
        | EntryKind.directory => String.ofList (stripTrailingSlashesChars e.path.toList)
        | EntryKind.regular => e.path
        | EntryKind.symlink => e.path) <;> simp [ih]

/-- Preservation of `validArchiveBool` under `zeroDeterministicMeta`. -/
theorem validArchiveBool_map_zeroDeterministicMeta {a p : Bool} {es : List TarEntry}
    (h : validArchiveBool a p es = true) :
    validArchiveBool a p (es.map zeroDeterministicMeta) = true := by
  unfold validArchiveBool at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at h ⊢
    intro e he
    rw [List.mem_map] at he
    rcases he with ⟨e0, he0, rfl⟩
    exact validEntryBool_zeroDeterministicMeta (h.1 e0 he0)
  · simp only [noDupNormalizedPathsBool, noDupNormalizedPathsBool_go_map_zeroDet]
    exact h.2

/-- Preservation of `fitsPaxLimit` under `zeroDeterministicMeta`. -/
theorem fitsPaxLimit_zeroDeterministicMeta {e : TarEntry}
    (h : fitsPaxLimit e = true) : fitsPaxLimit (zeroDeterministicMeta e) = true := by
  have hwp : wirePathOf (zeroDeterministicMeta e).kind
      (normalizeTarPath (zeroDeterministicMeta e).kind (zeroDeterministicMeta e).path) =
      wirePathOf e.kind (normalizeTarPath e.kind e.path) := by
    simp [zeroDeterministicMeta, normalizeTarPath, wirePathOf]
  let wp := wirePathOf e.kind (normalizeTarPath e.kind e.path)
  have hasc_empty : isAsciiString "" = true := by
    unfold isAsciiString
    rw [toUTF8_toList]
    rfl
  have hsz_empty : "".toUTF8.size = 0 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]
    rfl
  have hasc1 : (!isAsciiString "") = false := by rw [hasc_empty]; rfl
  have h0_32b : decide (0 > 32) = false := rfl
  have h7_p : ¬(0 ≥ ustarOctal7Limit) := by decide
  have h11_p : ¬(0 ≥ ustarOctal11Limit) := by decide
  have h7_pb : decide (0 ≥ ustarOctal7Limit) = false := rfl
  have h11_pb : decide (0 ≥ ustarOctal11Limit) = false := rfl
  have hk_eq : (zeroDeterministicMeta e).kind = e.kind := rfl
  have hl_eq : (zeroDeterministicMeta e).linkTarget = e.linkTarget := rfl
  have hd_eq : (zeroDeterministicMeta e).data = e.data := rfl
  have hu_eq : (zeroDeterministicMeta e).uname = "" := rfl
  have hg_eq : (zeroDeterministicMeta e).gname = "" := rfl
  have huid_eq : (zeroDeterministicMeta e).uid = 0 := rfl
  have hgid_eq : (zeroDeterministicMeta e).gid = 0 := rfl
  have hmt_eq : (zeroDeterministicMeta e).mtime = 0 := rfl
  have hbp_le : (buildPaxPayload (zeroDeterministicMeta e) wp).size ≤ (buildPaxPayload e wp).size := by
    simp only [buildPaxPayload, hk_eq, hl_eq, hd_eq, hu_eq, hg_eq, huid_eq, hgid_eq, hmt_eq,
      hasc1, hsz_empty, Bool.false_or, h0_32b, h7_p, h11_p, Bool.false_eq_true, ↓reduceIte,
      ByteArray.size_append, ByteArray.size_empty]
    omega
  unfold fitsPaxLimit at h ⊢
  dsimp only at h ⊢
  rw [hwp]
  split
  · rename_i hneed_z
    split at h
    · exact decide_eq_true (Nat.le_trans hbp_le (decide_eq_true_eq.mp h))
    · rename_i hnot_need
      exfalso
      apply hnot_need
      unfold needsPax at hneed_z ⊢
      simp only [hl_eq, hd_eq, hu_eq, hg_eq, huid_eq, hgid_eq, hmt_eq, hasc1, hsz_empty,
        h0_32b, h7_pb, h11_pb, Bool.or_false] at hneed_z
      simp only [Bool.or_eq_true] at hneed_z ⊢
      rcases hneed_z with ((h1 | h2) | h3) | h4
      · simp only [h1, true_or]
      · simp only [h2, or_true, true_or]
      · simp only [h3, or_true, true_or]
      · simp only [h4, or_true, true_or]
  · rfl

/-- Full functional specification of `Impl.packWith.go`. -/
theorem packWith_go_spec (opts : PackOptions) (rest : List TarEntry)
    (seen : List String) (acc : ByteArray) :
    (∀ out, packWith.go opts rest seen acc = .ok out →
      (rest.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
        noDupNormalizedPathsBool.go seen rest) = true ∧
      out = acc ++
        (rest.foldl (fun b e => b ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta e else e)
          (normalizeTarPath e.kind e.path)) ByteArray.empty) ++
        (zeroBlock ++ zeroBlock)) ∧
    ((rest.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
        noDupNormalizedPathsBool.go seen rest) = true →
      ∃ out, packWith.go opts rest seen acc = .ok out) := by
  induction rest generalizing seen acc with
  | nil =>
    constructor
    · intro out hout
      rw [packWith.go.eq_1] at hout
      cases hout
      refine ⟨rfl, ?_⟩
      simp [ByteArray.append_empty, ByteArray.append_assoc]
    · intro _
      exact ⟨acc ++ zeroBlock ++ zeroBlock, rfl⟩
  | cons entry tail ih =>
    constructor
    · intro out hout
      rw [packWith.go.eq_2] at hout
      dsimp only at hout
      cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal entry.kind entry.path with
      | error _ => rw [hv] at hout; cases hout
      | ok normPath =>
        rw [hv] at hout
        dsimp only at hout
        have hnp : normPath = normalizeTarPath entry.kind entry.path :=
          validateEntryPath_normPath hv
        have hsym_outer : ∀ u, (match entry.kind with
            | EntryKind.symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath entry.linkTarget
            | EntryKind.regular | EntryKind.directory => Except.ok ()) = u →
            (match u with
            | .error err => Except.error err
            | .ok () =>
              if (entry.kind != EntryKind.regular && entry.data.size != 0) = true then
                Except.error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some entry.path }
              else if (entry.kind != EntryKind.symlink && entry.linkTarget != "") = true then
                Except.error { kind := .invalidHeader, message := "non-symlink tar entry cannot have linkTarget", entryPath := some entry.path }
              else if (hasNulString entry.uname || hasNulString entry.gname) = true then
                Except.error { kind := .invalidHeader, message := "uname/gname cannot contain NUL byte", entryPath := some entry.path }
              else if (entry.uid ≥ u64Limit || entry.gid ≥ u64Limit || entry.mtime ≥ u64Limit || entry.data.size ≥ u64Limit) = true then
                Except.error { kind := .sizeOverflow, message := "tar entry numeric field exceeds 2^64 - 1", entryPath := some entry.path }
              else if seen.contains normPath = true then
                Except.error { kind := .duplicatePath, message := s!"duplicate tar entry path: {normPath}", entryPath := some normPath }
              else
                packWith.go opts tail (normPath :: seen)
                  (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)) = .ok out →
            (List.all (entry :: tail) (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
              noDupNormalizedPathsBool.go seen (entry :: tail)) = true ∧
            out = acc ++ List.foldl (fun b e => b ++ encodeEntryBlocks
              (if opts.deterministic then zeroDeterministicMeta e else e)
              (normalizeTarPath e.kind e.path)) ByteArray.empty (entry :: tail) ++ (zeroBlock ++ zeroBlock) := by
          intro u hsym hm
          cases u with
          | error _ => cases hm
          | ok _ =>
            dsimp only at hm
            split at hm
            · cases hm
            · split at hm
              · cases hm
              · split at hm
                · cases hm
                · split at hm
                  · cases hm
                  · split at hm
                    · cases hm
                    · rename_i hndata hnlink hnnul hnu64 hndup
                      have hve : validEntryBool opts.allowAbsolute opts.allowParentTraversal entry = true := by
                        unfold validEntryBool
                        rw [hv]
                        dsimp only
                        simp only [Bool.and_eq_true]
                        refine ⟨⟨?_, ?_⟩, ?_⟩
                        · cases hk : entry.kind with
                          | regular =>
                            simp only [hk] at hnlink ⊢
                            have hne : (EntryKind.regular != EntryKind.symlink) = true := by decide
                            cases hl : entry.linkTarget == ""
                            · exfalso; apply hnlink; rw [hne, Bool.true_and, bne, hl]; rfl
                            · rfl
                          | directory =>
                            simp only [hk] at hnlink ⊢
                            have hne : (EntryKind.directory != EntryKind.symlink) = true := by decide
                            cases hl : entry.linkTarget == ""
                            · exfalso; apply hnlink; rw [hne, Bool.true_and, bne, hl]; rfl
                            · rfl
                          | symlink =>
                            simp only [hk] at hsym ⊢
                            rw [hsym]
                        · cases hk : entry.kind with
                          | regular => rfl
                          | directory =>
                            simp only [hk] at hndata ⊢
                            have hne : (EntryKind.directory != EntryKind.regular) = true := by decide
                            cases hd : entry.data.size == 0
                            · exfalso; apply hndata; rw [hne, Bool.true_and, bne, hd]; rfl
                            · rfl
                          | symlink =>
                            simp only [hk] at hndata ⊢
                            have hne : (EntryKind.symlink != EntryKind.regular) = true := by decide
                            cases hd : entry.data.size == 0
                            · exfalso; apply hndata; rw [hne, Bool.true_and, bne, hd]; rfl
                            · rfl
                        · have hu_f : hasNulString entry.uname = false := by
                            cases hc : hasNulString entry.uname <;> simp_all
                          have hg_f : hasNulString entry.gname = false := by
                            cases hc : hasNulString entry.gname <;> simp_all
                          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hnu64
                          have h1_lt : entry.uid < u64Limit := hnu64.1.1.1
                          have h2_lt : entry.gid < u64Limit := hnu64.1.1.2
                          have h3_lt : entry.mtime < u64Limit := hnu64.1.2
                          have h4_lt : entry.data.size < u64Limit := hnu64.2
                          simp [hu_f, hg_f, h1_lt, h2_lt, h3_lt, h4_lt]
                      have ⟨hand_t, hout_eq⟩ := (ih (normPath :: seen)
                        (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)).1 out hm
                      rw [Bool.and_eq_true] at hand_t
                      rcases hand_t with ⟨hall_t, hnodup_t⟩
                      have hndup_b : (!seen.contains normPath) = true := by
                        cases hc : seen.contains normPath <;> simp_all
                      refine ⟨?_, ?_⟩
                      · simp only [List.all_cons, noDupNormalizedPathsBool.go.eq_2, Bool.and_eq_true]
                        rw [← hnp]
                        exact ⟨⟨hve, hall_t⟩, hndup_b, hnodup_t⟩
                      · rw [hout_eq]
                        have hfold : ∀ (init : ByteArray) (xs : List TarEntry),
                            xs.foldl (fun b e => b ++ encodeEntryBlocks
                              (if opts.deterministic then zeroDeterministicMeta e else e)
                              (normalizeTarPath e.kind e.path)) init =
                            init ++ xs.foldl (fun b e => b ++ encodeEntryBlocks
                              (if opts.deterministic then zeroDeterministicMeta e else e)
                              (normalizeTarPath e.kind e.path)) ByteArray.empty := by
                          intro init xs
                          induction xs generalizing init with
                          | nil => simp [ByteArray.append_empty]
                          | cons x xs ihx =>
                            simp only [List.foldl_cons, ByteArray.empty_append]
                            rw [ihx, ihx (encodeEntryBlocks _ _), ByteArray.append_assoc]
                        have hcons : (entry :: tail).foldl (fun b e => b ++ encodeEntryBlocks
                              (if opts.deterministic then zeroDeterministicMeta e else e)
                              (normalizeTarPath e.kind e.path)) ByteArray.empty =
                            encodeEntryBlocks
                              (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath ++
                            tail.foldl (fun b e => b ++ encodeEntryBlocks
                              (if opts.deterministic then zeroDeterministicMeta e else e)
                              (normalizeTarPath e.kind e.path)) ByteArray.empty := by
                          simp only [List.foldl_cons, ByteArray.empty_append, ← hnp]
                          exact hfold _ tail
                        rw [hcons]
                        simp only [ByteArray.append_assoc]
        exact hsym_outer _ rfl hout
    · intro hvalid
      simp only [Bool.and_eq_true, List.all_cons, noDupNormalizedPathsBool.go.eq_2] at hvalid
      rcases hvalid with ⟨⟨hve, hall_t⟩, hndup⟩
      unfold validEntryBool at hve
      cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal entry.kind entry.path with
      | error _ => rw [hv] at hve; cases hve
      | ok normPath =>
        rw [hv] at hve
        dsimp only at hve
        have hnp : normPath = normalizeTarPath entry.kind entry.path :=
          validateEntryPath_normPath hv
        rw [← hnp] at hndup
        rcases hndup with ⟨hnot_seen, hnodup_t⟩
        simp only [Bool.and_eq_true] at hve
        rcases hve with ⟨⟨hsym_ok, hdata_ok⟩, hmeta_ok⟩
        simp only [decide_eq_true_eq] at hmeta_ok
        rcases hmeta_ok with ⟨⟨⟨⟨⟨hnul_u, hnul_g⟩, huid⟩, hgid⟩, hmtime⟩, hsz⟩
        have hndata : (entry.kind != .regular && entry.data.size != 0) = false := by
          cases hk : entry.kind with
          | regular =>
            have hb : (EntryKind.regular != EntryKind.regular) = false := by decide
            simp [hb]
          | directory => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
          | symlink => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
        have hnlink : (entry.kind != .symlink && entry.linkTarget != "") = false := by
          cases hk : entry.kind with
          | regular => simp only [hk] at hsym_ok ⊢; simp [bne, hsym_ok]
          | directory => simp only [hk] at hsym_ok ⊢; simp [bne, hsym_ok]
          | symlink =>
            have hb : (EntryKind.symlink != EntryKind.symlink) = false := by decide
            simp [hb]
        have hnnul : (hasNulString entry.uname || hasNulString entry.gname) = false := by
          cases h1 : hasNulString entry.uname <;> cases h2 : hasNulString entry.gname <;> simp_all
        have hnu64 : (entry.uid ≥ u64Limit || entry.gid ≥ u64Limit ||
            entry.mtime ≥ u64Limit || entry.data.size ≥ u64Limit) = false := by
          simp [Nat.not_le_of_lt huid, Nat.not_le_of_lt hgid, Nat.not_le_of_lt hmtime, Nat.not_le_of_lt hsz]
        have hseen_f : seen.contains normPath = false := by
          cases hc : seen.contains normPath <;> simp_all
        have ⟨out, hout⟩ := (ih (normPath :: seen)
          (acc ++ encodeEntryBlocks (if opts.deterministic then zeroDeterministicMeta entry else entry) normPath)).2
          (by simp [hall_t, hnodup_t])
        refine ⟨out, ?_⟩
        rw [packWith.go.eq_2]
        dsimp only
        rw [hv]
        dsimp only
        cases hk : entry.kind with
        | regular =>
          simp only [hk] at hndata hnlink
          simp only [hndata, hnlink, hnnul, hnu64, hseen_f, Bool.false_eq_true, ↓reduceIte]
          exact hout
        | directory =>
          simp only [hk] at hndata hnlink
          simp only [hndata, hnlink, hnnul, hnu64, hseen_f, Bool.false_eq_true, ↓reduceIte]
          exact hout
        | symlink =>
          simp only [hk] at hsym_ok hndata hnlink
          cases hs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath entry.linkTarget with
          | error _ => rw [hs] at hsym_ok; cases hsym_ok
          | ok _ =>
            simp only [hndata, hnlink, hnnul, hnu64, hseen_f, Bool.false_eq_true, ↓reduceIte]
            exact hout

/-- Prove `test_tar_packWith_iffValidArchive` for `defaultApi`. -/
theorem allPass_packWith_iffValidArchive :
    AllPass (test_tar_packWith_iffValidArchive defaultApi) := by
  dsimp [AllPass, test_tar_packWith_iffValidArchive, Bind.bind, Pure.pure,
    NondetTest.nondet, NondetTest.assert, defaultApi, makeTarApi]
  intro opts entries
  cases h : Impl.packWith opts entries with
  | ok out =>
    refine ⟨?_, trivial⟩
    exact ((packWith_go_spec opts entries [] ByteArray.empty).1 out h).1
  | error err =>
    refine ⟨⟨?_, by simpa using packWith_go_nonEmptyMsg opts entries [] ByteArray.empty h⟩, trivial⟩
    intro hv
    unfold Impl.packWith at h
    have ⟨out, hout⟩ := (packWith_go_spec opts entries [] ByteArray.empty).2 hv
    rw [h] at hout
    cases hout


end LeanSwe.Tar.Proofs

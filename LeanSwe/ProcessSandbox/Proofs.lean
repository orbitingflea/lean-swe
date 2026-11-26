import Core.Assumptions
import Core.Obeys
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Interface

namespace LeanSwe.ProcessSandbox.Proofs

open LeanSwe.Process
open LeanSwe.ProcessSandbox

private theorem stateT_pure_run {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

private theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

private theorem stateT_map_run {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := by
  dsimp only [Functor.map, StateT.map, StateT.run]
  cases x s
  rfl

private theorem hasNulChar_eq (cs : List Char) :
    Internal.hasNulChar cs = Model.hasNulChar cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [Internal.hasNulChar, Model.hasNulChar, ih]

private theorem splitSlashChars_go_eq (acc cs : List Char) :
    Internal.splitSlashChars.go acc cs = Model.splitSlashChars.go acc cs := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c rest ih =>
    unfold Internal.splitSlashChars.go Model.splitSlashChars.go
    split <;> simp [ih]

private theorem splitSlashChars_eq (cs : List Char) :
    Internal.splitSlashChars cs = Model.splitSlashChars cs :=
  splitSlashChars_go_eq [] cs

private theorem allDistinct_eq {α : Type} [BEq α] (xs : List α) :
    Internal.allDistinct xs = Model.allDistinct xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [Internal.allDistinct, Model.allDistinct, ih]

private theorem dedupEnvPairs_eq (xs : List (String × String)) :
    Internal.dedupEnvPairs xs = Model.dedupEnvPairs xs := by
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    unfold Internal.dedupEnvPairs Model.dedupEnvPairs
    dsimp only
    rw [ih]

private theorem parseCleanAbsSegs_eq (p : String) :
    Internal.parseCleanAbsSegs p = Model.parseCleanAbsSegs p := by
  unfold Internal.parseCleanAbsSegs Model.parseCleanAbsSegs
  dsimp only
  rw [hasNulChar_eq, splitSlashChars_eq]

private theorem formatAbsSegs_eq (segs : List String) :
    Internal.formatAbsSegs segs = Model.formatAbsSegs segs := by
  cases segs <;> rfl

private theorem normalizeCleanAbsPath_eq (p : String) :
    Internal.normalizeCleanAbsPath p = Model.normalizeCleanAbsPath p := by
  unfold Internal.normalizeCleanAbsPath Model.normalizeCleanAbsPath
  rw [parseCleanAbsSegs_eq]
  have hf : Internal.formatAbsSegs = Model.formatAbsSegs := funext formatAbsSegs_eq
  rw [hf]

private theorem isReservedBoxSegs_eq (segs : List String) :
    Internal.isReservedBoxSegs segs = Model.isReservedBoxSegs segs := by
  cases segs <;> rfl

private theorem isValidEnvPair_eq (kv : String × String) :
    Internal.isValidEnvPair kv = Model.isValidEnvPair kv := by
  unfold Internal.isValidEnvPair Model.isValidEnvPair
  dsimp only
  rw [hasNulChar_eq, hasNulChar_eq]

private theorem invalidInput_eq (msg : String) (p : Option String) :
    Internal.invalidInput msg p = Model.invalidInput msg p := rfl

private theorem validateHostBoxPair_eq (ctor : String → String → SandboxMount) (hp bp : String) :
    Internal.validateHostBoxPair ctor hp bp = Model.validateHostBoxPair ctor hp bp := by
  unfold Internal.validateHostBoxPair Model.validateHostBoxPair
  rw [parseCleanAbsSegs_eq, parseCleanAbsSegs_eq]
  cases Model.parseCleanAbsSegs hp with
  | none => rfl
  | some hSegs =>
    cases Model.parseCleanAbsSegs bp with
    | none => rfl
    | some bSegs =>
      dsimp only
      rw [isReservedBoxSegs_eq, formatAbsSegs_eq, formatAbsSegs_eq]
      rfl

private theorem validateAndNormalizeMount_eq (m : SandboxMount) :
    Internal.validateAndNormalizeMount m = Model.validateAndNormalizeMount m := by
  cases m with
  | readOnly hp bp => exact validateHostBoxPair_eq .readOnly hp bp
  | readWrite hp bp => exact validateHostBoxPair_eq .readWrite hp bp
  | scratch bp =>
    unfold Internal.validateAndNormalizeMount Model.validateAndNormalizeMount
    dsimp only
    rw [parseCleanAbsSegs_eq]
    cases Model.parseCleanAbsSegs bp with
    | none => rfl
    | some bSegs =>
      dsimp only
      rw [isReservedBoxSegs_eq, formatAbsSegs_eq]
      rfl

private theorem validateMountsList_eq (ms : List SandboxMount) :
    Internal.validateMountsList ms = Model.validateMountsList ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    unfold Internal.validateMountsList Model.validateMountsList
    rw [validateAndNormalizeMount_eq, ih]

private theorem isReadWriteMount_eq (m : SandboxMount) :
    Internal.isReadWriteMount m = Model.isReadWriteMount m := by
  cases m <;> rfl

private theorem hasUnshadowedRwOverlapPair_eq (m₁ m₂ : SandboxMount) :
    Internal.hasUnshadowedRwOverlapPair m₁ m₂ = Model.hasUnshadowedRwOverlapPair m₁ m₂ := by
  unfold Internal.hasUnshadowedRwOverlapPair Model.hasUnshadowedRwOverlapPair
  rw [isReadWriteMount_eq, isReadWriteMount_eq]
  cases mountHostPath? m₁ with
  | none => rfl
  | some hp₁ =>
    cases mountHostPath? m₂ with
    | none => rfl
    | some hp₂ =>
      dsimp only
      rw [parseCleanAbsSegs_eq hp₁, parseCleanAbsSegs_eq (mountBoxPath m₁),
          parseCleanAbsSegs_eq hp₂, parseCleanAbsSegs_eq (mountBoxPath m₂)]
      rfl

private theorem hasUnshadowedRwOverlap_eq (ms : List SandboxMount) :
    Internal.hasUnshadowedRwOverlap ms = Model.hasUnshadowedRwOverlap ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    unfold Internal.hasUnshadowedRwOverlap Model.hasUnshadowedRwOverlap
    have hp : Internal.hasUnshadowedRwOverlapPair m = Model.hasUnshadowedRwOverlapPair m :=
      funext (hasUnshadowedRwOverlapPair_eq m)
    rw [hp, ih]

/-- `Internal.validateSpec` matches `Model.validateSpecPure` identically on every `BoxSpec`. -/
theorem validateSpec_eq_model (spec : BoxSpec) :
    Internal.validateSpec spec = Model.validateSpecPure spec := by
  unfold Internal.validateSpec Model.validateSpecPure
  have hNul : (fun a : String => Internal.hasNulChar a.toList) =
      (fun a : String => Model.hasNulChar a.toList) := funext fun a => hasNulChar_eq a.toList
  have hEnv : Internal.isValidEnvPair = Model.isValidEnvPair := funext isValidEnvPair_eq
  rw [hasNulChar_eq, hNul, hEnv]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  dsimp only [Bind.bind, Except.bind]
  cases spec.cwd with
  | none =>
    dsimp only
    rw [validateMountsList_eq]
    cases Model.validateMountsList spec.mounts.toList with
    | error _ => rfl
    | ok _ =>
      dsimp only
      rw [allDistinct_eq, hasUnshadowedRwOverlap_eq, dedupEnvPairs_eq]
      rfl
  | some d =>
    dsimp only
    rw [normalizeCleanAbsPath_eq]
    cases Model.normalizeCleanAbsPath d with
    | none => rfl
    | some _ =>
      dsimp only
      rw [validateMountsList_eq]
      cases Model.validateMountsList spec.mounts.toList with
      | error _ => rfl
      | ok _ =>
        dsimp only
        rw [allDistinct_eq, hasUnshadowedRwOverlap_eq, dedupEnvPairs_eq]
        rfl

private theorem validateAndNormalizeMount_err_kind (m : SandboxMount) (e : SandboxError)
    (h : Internal.validateAndNormalizeMount m = .error e) : e.kind = .invalidInput := by
  cases m with
  | readOnly hp bp | readWrite hp bp =>
    simp only [Internal.validateAndNormalizeMount, Internal.validateHostBoxPair] at h
    cases h1 : Internal.parseCleanAbsSegs hp <;> cases h2 : Internal.parseCleanAbsSegs bp <;>
      simp [h1, h2] at h
    · subst h; rfl
    · subst h; rfl
    · subst h; rfl
    · split at h <;> simp at h; subst h; rfl
  | scratch bp =>
    simp only [Internal.validateAndNormalizeMount] at h
    cases h1 : Internal.parseCleanAbsSegs bp <;> simp [h1] at h
    · subst h; rfl
    · split at h <;> simp at h; subst h; rfl

private theorem validateMountsList_err_kind :
    ∀ (ms : List SandboxMount) (e : SandboxError),
      Internal.validateMountsList ms = .error e → e.kind = .invalidInput
  | [], _, h => by simp [Internal.validateMountsList] at h
  | m :: rest, e, h => by
    unfold Internal.validateMountsList at h
    cases hm : Internal.validateAndNormalizeMount m with
    | error em =>
      simp only [hm, Bind.bind, Except.bind, Except.error.injEq] at h; subst h
      exact validateAndNormalizeMount_err_kind m em hm
    | ok _ =>
      cases hr : Internal.validateMountsList rest with
      | error er =>
        simp only [hm, hr, Bind.bind, Except.bind, Except.error.injEq] at h; subst h
        exact validateMountsList_err_kind rest er hr
      | ok _ => simp [hm, hr, Bind.bind, Except.bind] at h

private theorem validateSpec_err_kind (spec : BoxSpec) (e : SandboxError)
    (h : Internal.validateSpec spec = .error e) : e.kind = .invalidInput := by
  unfold Internal.validateSpec at h
  simp only [Bind.bind, Except.bind] at h
  split at h; · (injection h with h; subst h; rfl)
  split at h; · (injection h with h; subst h; rfl)
  split at h; · (injection h with h; subst h; rfl)
  split at h; · (injection h with h; subst h; rfl)
  split at h; · (injection h with h; subst h; rfl)
  split at h; · (injection h with h; subst h; rfl)
  cases hCwd : spec.cwd with
  | none =>
    simp only [hCwd] at h
    cases hm : Internal.validateMountsList spec.mounts.toList with
    | error em =>
      simp only [hm] at h; injection h with h; subst h
      exact validateMountsList_err_kind _ em hm
    | ok _ =>
      simp only [hm] at h
      split at h; · (injection h with h; subst h; rfl)
      split at h; · (injection h with h; subst h; rfl)
      · contradiction
  | some d =>
    simp only [hCwd] at h
    cases hNorm : Internal.normalizeCleanAbsPath d with
    | none => simp only [hNorm] at h; injection h with h; subst h; rfl
    | some _ =>
      simp only [hNorm] at h
      cases hm : Internal.validateMountsList spec.mounts.toList with
      | error em =>
        simp only [hm] at h; injection h with h; subst h
        exact validateMountsList_err_kind _ em hm
      | ok _ =>
        simp only [hm] at h
        split at h; · (injection h with h; subst h; rfl)
        split at h; · (injection h with h; subst h; rfl)
        · contradiction

private theorem validateSpec_never_of (forbidden : SandboxErrorKind)
    (hne : forbidden ≠ .invalidInput) (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind forbidden (LeanSwe.ProcessSandbox.validateSpec spec) := by
  unfold Core.NeverErrorKindPure LeanSwe.ProcessSandbox.validateSpec
    LeanSwe.ProcessSandbox.defaultApi Internal.mkApiM
  dsimp only
  cases h : Internal.validateSpec spec with
  | ok _ => trivial
  | error e =>
    dsimp only
    rw [validateSpec_err_kind spec e h]
    exact hne.symm

/-- `LeanSwe.ProcessSandbox.validateSpec` never returns `.unavailable`. -/
theorem validateSpec_never_unavailable (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_of .unavailable (by decide) spec

/-- `LeanSwe.ProcessSandbox.validateSpec` never returns `.notFound`. -/
theorem validateSpec_never_notFound (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .notFound (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_of .notFound (by decide) spec

/-- `LeanSwe.ProcessSandbox.validateSpec` never returns `.permissionDenied`. -/
theorem validateSpec_never_permissionDenied (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_of .permissionDenied (by decide) spec

/-- `LeanSwe.ProcessSandbox.validateSpec` never returns `.ioError`. -/
theorem validateSpec_never_ioError (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .ioError (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_of .ioError (by decide) spec

private theorem hasNulChar_eq_contains (cs : List Char) :
    Internal.hasNulChar cs = cs.contains '\x00' := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [Internal.hasNulChar, List.contains_cons, ih]
    have hc : (c == Char.ofNat 0) = ('\x00' == c) := by
      cases h : (c == Char.ofNat 0) with
      | true =>
        have : c = '\x00' := beq_iff_eq.mp h
        subst this; rfl
      | false =>
        have hne : c ≠ '\x00' := fun heq => by subst heq; cases h
        exact (beq_false_of_ne hne.symm).symm
    rw [hc]

private theorem hasNulModel_iff_hasNulChar (s : String) :
    LeanSwe.Process.Model.hasNulModel s = Internal.hasNulChar s.toList := by
  unfold LeanSwe.Process.Model.hasNulModel
  exact (hasNulChar_eq_contains s.toList).symm

private theorem list_contains_append_false {xs ys : List Char} {c : Char}
    (hx : xs.contains c = false) (hy : ys.contains c = false) :
    (xs ++ ys).contains c = false := by
  induction xs with
  | nil => exact hy
  | cons x rest ih =>
    simp only [List.cons_append, List.contains_cons, Bool.or_eq_false_iff] at hx ⊢
    exact ⟨hx.1, ih hx.2⟩

private theorem hasNulModel_append {a b : String}
    (ha : LeanSwe.Process.Model.hasNulModel a = false)
    (hb : LeanSwe.Process.Model.hasNulModel b = false) :
    LeanSwe.Process.Model.hasNulModel (a ++ b) = false := by
  unfold LeanSwe.Process.Model.hasNulModel at ha hb ⊢
  rw [String.toList_append]
  exact list_contains_append_false ha hb

private theorem hasNulChar_reverse (cs : List Char) :
    Internal.hasNulChar cs.reverse = Internal.hasNulChar cs := by
  rw [hasNulChar_eq_contains, hasNulChar_eq_contains]
  cases h : cs.contains '\x00' with
  | true =>
    exact List.contains_iff_mem.mpr (List.mem_reverse.mpr (List.contains_iff_mem.mp h))
  | false =>
    cases hr : cs.reverse.contains '\x00' with
    | false => rfl
    | true =>
      have hm : '\x00' ∈ cs := List.mem_reverse.mp (List.contains_iff_mem.mp hr)
      have hc : cs.contains '\x00' = true := List.contains_iff_mem.mpr hm
      rw [h] at hc; cases hc

private theorem splitSlashChars_go_no_nul (acc cs : List Char)
    (hAcc : Internal.hasNulChar acc = false) (hCs : Internal.hasNulChar cs = false) :
    ∀ seg ∈ Internal.splitSlashChars.go acc cs, Internal.hasNulChar seg = false := by
  induction cs generalizing acc with
  | nil =>
    intro seg hSeg
    simp only [Internal.splitSlashChars.go, List.mem_singleton] at hSeg
    subst hSeg
    rw [hasNulChar_reverse]
    exact hAcc
  | cons c rest ih =>
    simp only [Internal.hasNulChar, Bool.or_eq_false_iff] at hCs
    unfold Internal.splitSlashChars.go
    split
    · intro seg hSeg
      rcases List.mem_cons.mp hSeg with rfl | hTail
      · rw [hasNulChar_reverse]; exact hAcc
      · exact ih [] rfl hCs.2 seg hTail
    · apply ih (c :: acc)
      · simp [Internal.hasNulChar, hCs.1, hAcc]
      · exact hCs.2

private theorem parseCleanAbsSegs_no_nul (p : String) (segs : List String)
    (h : Internal.parseCleanAbsSegs p = some segs) :
    ∀ s ∈ segs, LeanSwe.Process.Model.hasNulModel s = false := by
  unfold Internal.parseCleanAbsSegs at h
  dsimp only at h
  split at h
  · contradiction
  rename_i hCond
  have hNoNul : Internal.hasNulChar p.toList = false := by
    cases hn : Internal.hasNulChar p.toList with
    | false => rfl
    | true => simp [hn] at hCond
  have hTailNoNul : Internal.hasNulChar p.toList.tail = false := by
    cases hCs : p.toList with
    | nil => rfl
    | cons _ _ =>
      rw [hCs] at hNoNul
      simp only [Internal.hasNulChar, Bool.or_eq_false_iff] at hNoNul
      exact hNoNul.2
  split at h
  · contradiction
  injection h with hEq
  subst hEq
  intro s hs
  rcases List.mem_filterMap.mp hs with ⟨raw, hRawMem, hRawEq⟩
  split at hRawEq
  · contradiction
  injection hRawEq with hsEq
  subst hsEq
  rw [hasNulModel_iff_hasNulChar, String.toList_ofList]
  exact splitSlashChars_go_no_nul [] p.toList.tail rfl hTailNoNul raw hRawMem

private theorem intercalate_cons_no_nul (sep : String) :
    ∀ (rest : List String) (acc : String),
      LeanSwe.Process.Model.hasNulModel acc = false →
      LeanSwe.Process.Model.hasNulModel sep = false →
      (∀ s ∈ rest, LeanSwe.Process.Model.hasNulModel s = false) →
      LeanSwe.Process.Model.hasNulModel (String.intercalate sep (acc :: rest)) = false
  | [], _, hAcc, _, _ => hAcc
  | y :: ys, acc, hAcc, hSep, hRest =>
    intercalate_cons_no_nul sep ys (acc ++ sep ++ y)
      (hasNulModel_append (hasNulModel_append hAcc hSep) (hRest y List.mem_cons_self))
      hSep
      (fun s hs => hRest s (List.mem_cons_of_mem y hs))

private theorem formatAbsSegs_no_nul (segs : List String)
    (h : ∀ s ∈ segs, LeanSwe.Process.Model.hasNulModel s = false) :
    LeanSwe.Process.Model.hasNulModel (Internal.formatAbsSegs segs) = false := by
  cases segs with
  | nil => rfl
  | cons x rest =>
    unfold Internal.formatAbsSegs
    exact hasNulModel_append rfl
      (intercalate_cons_no_nul "/" rest x (h x List.mem_cons_self) rfl
        (fun s hs => h s (List.mem_cons_of_mem x hs)))

private theorem mountFlags_no_nul_of_valid (m norm : SandboxMount)
    (h : Internal.validateAndNormalizeMount m = .ok norm) :
    ∀ s ∈ Internal.mountFlags norm, LeanSwe.Process.Model.hasNulModel s = false := by
  cases m with
  | readOnly hp bp =>
    simp only [Internal.validateAndNormalizeMount, Internal.validateHostBoxPair] at h
    cases h1 : Internal.parseCleanAbsSegs hp with
    | none => simp [h1] at h
    | some hs =>
      cases h2 : Internal.parseCleanAbsSegs bp with
      | none => simp [h1, h2] at h
      | some bs =>
        simp only [h1, h2] at h
        split at h; · contradiction
        injection h with hEq; subst hEq
        intro s hMem
        simp only [Internal.mountFlags, List.mem_cons, List.not_mem_nil, or_false] at hMem
        rcases hMem with rfl | rfl | rfl
        · rfl
        · exact formatAbsSegs_no_nul hs (parseCleanAbsSegs_no_nul hp hs h1)
        · exact formatAbsSegs_no_nul bs (parseCleanAbsSegs_no_nul bp bs h2)
  | readWrite hp bp =>
    simp only [Internal.validateAndNormalizeMount, Internal.validateHostBoxPair] at h
    cases h1 : Internal.parseCleanAbsSegs hp with
    | none => simp [h1] at h
    | some hs =>
      cases h2 : Internal.parseCleanAbsSegs bp with
      | none => simp [h1, h2] at h
      | some bs =>
        simp only [h1, h2] at h
        split at h; · contradiction
        injection h with hEq; subst hEq
        intro s hMem
        simp only [Internal.mountFlags, List.mem_cons, List.not_mem_nil, or_false] at hMem
        rcases hMem with rfl | rfl | rfl
        · rfl
        · exact formatAbsSegs_no_nul hs (parseCleanAbsSegs_no_nul hp hs h1)
        · exact formatAbsSegs_no_nul bs (parseCleanAbsSegs_no_nul bp bs h2)
  | scratch bp =>
    simp only [Internal.validateAndNormalizeMount] at h
    cases h1 : Internal.parseCleanAbsSegs bp with
    | none => simp [h1] at h
    | some bs =>
      simp only [h1] at h
      split at h; · contradiction
      injection h with hEq; subst hEq
      intro s hMem
      simp only [Internal.mountFlags, List.mem_cons, List.not_mem_nil, or_false] at hMem
      rcases hMem with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rfl
      · exact formatAbsSegs_no_nul bs (parseCleanAbsSegs_no_nul bp bs h1)

private theorem validateMountsList_no_nul :
    ∀ (ms norms : List SandboxMount),
      Internal.validateMountsList ms = .ok norms →
      ∀ m ∈ norms, ∀ s ∈ Internal.mountFlags m, LeanSwe.Process.Model.hasNulModel s = false
  | [], norms, h => by
    simp only [Internal.validateMountsList, Except.ok.injEq] at h
    subst h
    intro _ hm; nomatch hm
  | m :: rest, norms, h => by
    unfold Internal.validateMountsList at h
    cases hm : Internal.validateAndNormalizeMount m with
    | error _ => simp [hm, Bind.bind, Except.bind] at h
    | ok nm =>
      cases hr : Internal.validateMountsList rest with
      | error _ => simp [hm, hr, Bind.bind, Except.bind] at h
      | ok nrest =>
        simp only [hm, hr, Bind.bind, Except.bind, Except.ok.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hTail
        · exact mountFlags_no_nul_of_valid m x hm
        · exact validateMountsList_no_nul rest nrest hr x hTail

private theorem dedupEnvPairs_subset {xs : List (String × String)} {kv : String × String}
    (h : kv ∈ Internal.dedupEnvPairs xs) : kv ∈ xs := by
  induction xs with
  | nil => simp [Internal.dedupEnvPairs] at h
  | cons p rest ih =>
    unfold Internal.dedupEnvPairs at h
    dsimp only at h
    split at h
    · exact List.mem_cons_of_mem p (ih h)
    · rcases List.mem_cons.mp h with rfl | hTail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem p (ih hTail)

private theorem envFlags_no_nul (kvs : List (String × String))
    (h : ∀ kv ∈ kvs,
      LeanSwe.Process.Model.hasNulModel kv.1 = false ∧
      LeanSwe.Process.Model.hasNulModel kv.2 = false) :
    ∀ s ∈ Internal.envFlags kvs, LeanSwe.Process.Model.hasNulModel s = false := by
  induction kvs with
  | nil => intro _ hm; nomatch hm
  | cons kv rest ih =>
    intro s hs
    simp only [Internal.envFlags, List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hTail
    · rfl
    · exact (h kv List.mem_cons_self).1
    · exact (h kv List.mem_cons_self).2
    · exact ih (fun p hp => h p (List.mem_cons_of_mem kv hp)) s hTail

private theorem osPresetFlags_no_nul :
    ∀ s ∈ Internal.osPresetFlags, LeanSwe.Process.Model.hasNulModel s = false := by
  decide

private theorem list_any_false_of_forall {α : Type} {xs : List α} {p : α → Bool}
    (h : ∀ x ∈ xs, p x = false) : xs.any p = false := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

private theorem validateSpec_ok_request_valid (spec : BoxSpec) (valid : ValidBoxSpec)
    (hVal : Internal.validateSpec spec = .ok valid) :
    ∃ norm, LeanSwe.Process.Model.validateRequestModel (Internal.mkBwrapRequest valid) = .ok norm := by
  have hProps :
      (valid.timeoutMs == some 0) = false ∧
      LeanSwe.Process.Model.hasNulModel valid.program = false ∧
      (∀ a ∈ valid.args.toList, LeanSwe.Process.Model.hasNulModel a = false) ∧
      (∀ kv ∈ valid.env.toList,
        LeanSwe.Process.Model.hasNulModel kv.1 = false ∧
        LeanSwe.Process.Model.hasNulModel kv.2 = false) ∧
      LeanSwe.Process.Model.hasNulModel valid.cwd = false ∧
      (∀ m ∈ valid.mounts.toList, ∀ s ∈ Internal.mountFlags m,
        LeanSwe.Process.Model.hasNulModel s = false) := by
    unfold Internal.validateSpec at hVal
    simp only [Bind.bind, Except.bind] at hVal
    split at hVal; · contradiction
    split at hVal; · contradiction
    rename_i hProgNul
    split at hVal; · contradiction
    rename_i hArgsNul
    split at hVal; · contradiction
    rename_i hEnvOk
    split at hVal; · contradiction
    rename_i hToZero
    split at hVal; · contradiction
    have hProgF : LeanSwe.Process.Model.hasNulModel spec.program = false := by
      rw [hasNulModel_iff_hasNulChar]
      cases hn : Internal.hasNulChar spec.program.toList <;> simp_all
    have hArgsF : ∀ a ∈ spec.args.toList, LeanSwe.Process.Model.hasNulModel a = false := by
      intro a ha
      rw [hasNulModel_iff_hasNulChar]
      cases hn : Internal.hasNulChar a.toList with
      | false => rfl
      | true =>
        exfalso; apply hArgsNul
        exact List.any_eq_true.mpr ⟨a, ha, hn⟩
    have hEnvAll : ∀ kv ∈ spec.env.toList, Internal.isValidEnvPair kv = true := by
      have hall : spec.env.toList.all Internal.isValidEnvPair = true := by
        cases hc : spec.env.toList.all Internal.isValidEnvPair <;> simp_all
      exact List.all_eq_true.mp hall
    have hCleanEnvF : ∀ kv ∈
        (let deduped := Internal.dedupEnvPairs spec.env.toList
         if deduped.any (fun kv => kv.1 == "PATH") then deduped
         else ("PATH", Internal.defaultSandboxPath) :: deduped),
        LeanSwe.Process.Model.hasNulModel kv.1 = false ∧
        LeanSwe.Process.Model.hasNulModel kv.2 = false := by
      intro kv hkv
      have hFromOrig : ∀ p ∈ Internal.dedupEnvPairs spec.env.toList,
          LeanSwe.Process.Model.hasNulModel p.1 = false ∧
          LeanSwe.Process.Model.hasNulModel p.2 = false := by
        intro p hp
        have hv := hEnvAll p (dedupEnvPairs_subset hp)
        unfold Internal.isValidEnvPair at hv
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv
        rw [hasNulModel_iff_hasNulChar, hasNulModel_iff_hasNulChar]
        exact ⟨hv.1.2, hv.2⟩
      dsimp only at hkv
      split at hkv
      · exact hFromOrig kv hkv
      · rcases List.mem_cons.mp hkv with rfl | hTail
        · exact ⟨rfl, rfl⟩
        · exact hFromOrig kv hTail
    have hToF : (spec.timeoutMs == some 0) = false := by
      cases hc : (spec.timeoutMs == some 0) <;> simp_all
    have hTmpOk : ∀ s ∈ Internal.mountFlags (.scratch "/tmp"),
        LeanSwe.Process.Model.hasNulModel s = false := by
      decide
    cases hCwd : spec.cwd with
    | none =>
      simp only [hCwd] at hVal
      cases hm : Internal.validateMountsList spec.mounts.toList with
      | error _ => rw [hm] at hVal; contradiction
      | ok normMounts =>
        rw [hm] at hVal; dsimp only at hVal
        split at hVal; · contradiction
        split at hVal; · contradiction
        injection hVal with hEq; subst hEq
        refine ⟨hToF, hProgF, hArgsF, hCleanEnvF, ?_, ?_⟩
        · exact (show LeanSwe.Process.Model.hasNulModel Internal.defaultSandboxCwd = false from rfl)
        · intro m hmem
          dsimp only at hmem
          split at hmem
          · exact validateMountsList_no_nul spec.mounts.toList normMounts hm m hmem
          · rcases List.mem_cons.mp hmem with rfl | hTail
            · exact hTmpOk
            · exact validateMountsList_no_nul spec.mounts.toList normMounts hm m hTail
    | some d =>
      simp only [hCwd] at hVal
      cases hNorm : Internal.normalizeCleanAbsPath d with
      | none => simp [hNorm] at hVal
      | some cleanD =>
        simp only [hNorm] at hVal
        have hCleanF : LeanSwe.Process.Model.hasNulModel cleanD = false := by
          unfold Internal.normalizeCleanAbsPath at hNorm
          cases hp : Internal.parseCleanAbsSegs d with
          | none => simp [hp] at hNorm
          | some segs =>
            simp only [hp, Option.map_some, Option.some.injEq] at hNorm
            subst hNorm
            exact formatAbsSegs_no_nul segs (parseCleanAbsSegs_no_nul d segs hp)
        cases hm : Internal.validateMountsList spec.mounts.toList with
        | error _ => rw [hm] at hVal; contradiction
        | ok normMounts =>
          rw [hm] at hVal; dsimp only at hVal
          split at hVal; · contradiction
          split at hVal; · contradiction
          injection hVal with hEq; subst hEq
          refine ⟨hToF, hProgF, hArgsF, hCleanEnvF, hCleanF, ?_⟩
          intro m hmem
          dsimp only at hmem
          split at hmem
          · exact validateMountsList_no_nul spec.mounts.toList normMounts hm m hmem
          · rcases List.mem_cons.mp hmem with rfl | hTail
            · exact hTmpOk
            · exact validateMountsList_no_nul spec.mounts.toList normMounts hm m hTail
  rcases hProps with ⟨hToF, hProgF, hArgsF, hEnvF, hCwdF, hMountsF⟩
  have hAllArgsNoNul : ∀ s ∈ (Internal.mkBwrapArgs valid).toList,
      LeanSwe.Process.Model.hasNulModel s = false := by
    intro s hs
    unfold Internal.mkBwrapArgs at hs
    simp only [List.mem_append] at hs
    rcases hs with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8
    · exact osPresetFlags_no_nul s h1
    · rcases List.mem_flatMap.mp h2 with ⟨m, hmSort, hsM⟩
      have hmOrig : m ∈ valid.mounts.toList :=
        (List.mem_mergeSort (l := valid.mounts.toList)).mp hmSort
      exact hMountsF m hmOrig s hsM
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
      rcases h3 with rfl | rfl | rfl <;> rfl
    · cases hNet : valid.network with
      | closed => rw [hNet] at h4; cases h4
      | «open» =>
        rw [hNet] at h4
        cases h4 with
        | head => rfl
        | tail _ ht => cases ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h5
      rcases h5 with rfl | rfl | rfl <;> rfl
    · exact envFlags_no_nul valid.env.toList hEnvF s h6
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h7
      rcases h7 with rfl | rfl | rfl | rfl
      · rfl
      · exact hCwdF
      · rfl
      · exact hProgF
    · exact hArgsF s h8
  unfold LeanSwe.Process.Model.validateRequestModel
    LeanSwe.Process.Model.validateSpawnRequestModel Internal.mkBwrapRequest
  have hArgsAnyF := list_any_false_of_forall hAllArgsNoNul
  have hProgEmpty : ("bwrap".isEmpty) = false := rfl
  have hProgNul : LeanSwe.Process.Model.hasNulModel "bwrap" = false := rfl
  have hEnvEmpty : (#[].toList.any LeanSwe.Process.Model.isInvalidEnvEntryModel) = false := rfl
  simp only [hProgEmpty, hProgNul, hArgsAnyF, hEnvEmpty, hToF, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

private theorem validateRequestModel_mkProbeRequest :
    ∃ norm, LeanSwe.Process.Model.validateRequestModel Internal.mkProbeRequest = .ok norm :=
  ⟨Internal.mkProbeRequest, rfl⟩

private theorem truncateToCap_withinOutputCap (cap? : Option Nat) (out err : ByteArray) :
    let p := Internal.truncateToCap cap? out err
    Model.withinOutputCap cap? p.1 p.2 := by
  cases cap? with
  | none => trivial
  | some cap =>
    dsimp only [Internal.truncateToCap, Model.withinOutputCap]
    have hExtractOut : (out.extract 0 cap).size = min cap out.size := by simp
    by_cases h1 : out.size ≤ cap
    · simp only [h1, ↓reduceIte]
      by_cases h2 : err.size ≤ cap - out.size
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]; rw [ByteArray.size_extract]; omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : err.size ≤ cap - (out.extract 0 cap).size
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]; rw [ByteArray.size_extract, ByteArray.size_extract]; omega

private theorem nonEmptyMsg_not_isEmpty (fallback msg : String)
    (hfb : (!fallback.isEmpty) = true) :
    (!(Internal.nonEmptyMsg fallback msg).isEmpty) = true := by
  unfold Internal.nonEmptyMsg
  cases hm : msg.isEmpty with
  | true => rw [ite_eq_left rfl]; exact hfb
  | false => rw [ite_eq_right Bool.false_ne_true, hm]; rfl

private theorem mapFsPrecheckError_post (target : String) (e : LeanSwe.Fs.FsError) :
    Model.isHostErrorKind (Internal.mapFsPrecheckError target e).kind = true ∧
    (!(Internal.mapFsPrecheckError target e).message.isEmpty) = true := by
  unfold Internal.mapFsPrecheckError
  refine ⟨?_, nonEmptyMsg_not_isEmpty "mount path unavailable" e.message (by decide)⟩
  cases e.kind <;> rfl

private theorem checkNoSymlinkPrefix_step {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (fs : LeanSwe.Fs.FsApiM (StateM W))
    (hStat : Core.ObeysStep proj Model.processStepWf (Model.execFsLstatStep fs) Model.allowedFsLstatStep) :
    ∀ (baseSegs relSegs : List String) (w : W),
      Model.processStepWf (proj w) = true →
      let r := (Internal.checkNoSymlinkPrefix fs baseSegs relSegs).run w
      proj r.2 = proj w ∧
      match r.1 with
      | .ok _ => True
      | .error e => Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty = true
  | baseSegs, [], w, hWf => by
    simp only [Internal.checkNoSymlinkPrefix]
    rw [stateT_bind_run]
    have hOne := hStat w (Internal.formatAbsSegs baseSegs) hWf
    dsimp only [Model.execFsLstatStep, Model.allowedFsLstatStep, id] at hOne
    cases hs : (fs.lstat (Internal.formatAbsSegs baseSegs)).run w with
    | mk res w1 =>
      rw [hs] at hOne
      have hEq : proj w1 = proj w := hOne.1
      cases res with
      | error e =>
        rw [stateT_pure_run]
        exact ⟨hEq, mapFsPrecheckError_post _ e⟩
      | ok st =>
        by_cases hSym : (st.kind == .symlink) = true
        · simp only [hSym, ↓reduceIte]; rw [stateT_pure_run]
          exact ⟨hEq, rfl, (show (!"mount path refuses symlink".isEmpty) = true from rfl)⟩
        · simp only [hSym, Bool.false_eq_true, ↓reduceIte]; rw [stateT_pure_run]
          exact ⟨hEq, trivial⟩
  | baseSegs, [last], w, hWf => by
    simp only [Internal.checkNoSymlinkPrefix]
    rw [stateT_bind_run]
    have hOne := hStat w (Internal.formatAbsSegs (baseSegs ++ [last])) hWf
    dsimp only [Model.execFsLstatStep, Model.allowedFsLstatStep, id] at hOne
    cases hs : (fs.lstat (Internal.formatAbsSegs (baseSegs ++ [last]))).run w with
    | mk res w1 =>
      rw [hs] at hOne
      have hEq : proj w1 = proj w := hOne.1
      cases res with
      | error e =>
        rw [stateT_pure_run]
        exact ⟨hEq, mapFsPrecheckError_post _ e⟩
      | ok st =>
        by_cases hSym : (st.kind == .symlink) = true
        · simp only [hSym, ↓reduceIte]; rw [stateT_pure_run]
          exact ⟨hEq, rfl, (show (!"mount path refuses symlink".isEmpty) = true from rfl)⟩
        · simp only [hSym, Bool.false_eq_true, ↓reduceIte]; rw [stateT_pure_run]
          exact ⟨hEq, trivial⟩
  | baseSegs, seg :: seg2 :: rest, w, hWf => by
    simp only [Internal.checkNoSymlinkPrefix]
    rw [stateT_bind_run]
    have hOne := hStat w (Internal.formatAbsSegs (baseSegs ++ [seg])) hWf
    dsimp only [Model.execFsLstatStep, Model.allowedFsLstatStep, id] at hOne
    cases hs : (fs.lstat (Internal.formatAbsSegs (baseSegs ++ [seg]))).run w with
    | mk res w1 =>
      rw [hs] at hOne
      have hEq : proj w1 = proj w := hOne.1
      cases res with
      | error e =>
        rw [stateT_pure_run]
        exact ⟨hEq, mapFsPrecheckError_post _ e⟩
      | ok st =>
        by_cases hSym : (st.kind == .symlink) = true
        · simp only [hSym, ↓reduceIte]; rw [stateT_pure_run]
          exact ⟨hEq, rfl, (show (!"mount path refuses symlink".isEmpty) = true from rfl)⟩
        · simp only [hSym, Bool.false_eq_true, ↓reduceIte]
          by_cases hDir : (st.kind != .dir) = true
          · simp only [hDir, ↓reduceIte]; rw [stateT_pure_run]
            exact ⟨hEq, rfl, (show (!"mount path component is not a directory".isEmpty) = true from rfl)⟩
          · simp only [hDir, Bool.false_eq_true, ↓reduceIte]
            have ih := checkNoSymlinkPrefix_step proj fs hStat (baseSegs ++ [seg]) (seg2 :: rest) w1 (hEq ▸ hWf)
            exact ⟨ih.1.trans hEq, ih.2⟩

private theorem checkOneMountPreconditions_step {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (fs : LeanSwe.Fs.FsApiM (StateM W))
    (hStat : Core.ObeysStep proj Model.processStepWf (Model.execFsLstatStep fs) Model.allowedFsLstatStep)
    (sorted : List SandboxMount) (m : SandboxMount) (w : W)
    (hWf : Model.processStepWf (proj w) = true) :
    let r := (Internal.checkOneMountPreconditions fs sorted m).run w
    proj r.2 = proj w ∧
    match r.1 with
    | .ok () => True
    | .error e => Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty = true := by
  have hCont : ∀ (srcIsDir : Bool) (w1 : W), proj w1 = proj w →
      let r := ((match Internal.parseCleanAbsSegs (mountBoxPath m) with
        | none => pure (.ok ())
        | some cSegs =>
          match Internal.deepestProperAncestorMount sorted cSegs with
          | some (.readOnly php pbp) | some (.readWrite php pbp) =>
            match Internal.parseCleanAbsSegs php, Internal.parseCleanAbsSegs pbp with
            | some phpSegs, some pbpSegs => do
              let rel := cSegs.drop pbpSegs.length
              match ← Internal.checkNoSymlinkPrefix fs phpSegs rel with
              | .error e => return .error e
              | .ok dstIsDir =>
                if dstIsDir != srcIsDir then
                  return .error { kind := .notFound, path := some (Internal.formatAbsSegs (phpSegs ++ rel)), message := "nested mount target kind mismatch" }
                else return .ok ()
            | _, _ => pure (.ok ())
          | some (.scratch _) | none => pure (.ok ())) : StateM W (Except SandboxError Unit)).run w1
      proj r.2 = proj w ∧
      match r.1 with
      | .ok () => True
      | .error e => Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty = true := by
    intro srcIsDir w1 hEq1
    cases Internal.parseCleanAbsSegs (mountBoxPath m) with
    | none => dsimp only; rw [stateT_pure_run]; exact ⟨hEq1, trivial⟩
    | some cSegs =>
      dsimp only
      cases Internal.deepestProperAncestorMount sorted cSegs with
      | none => dsimp only; rw [stateT_pure_run]; exact ⟨hEq1, trivial⟩
      | some anc =>
        cases anc with
        | scratch _ => dsimp only; rw [stateT_pure_run]; exact ⟨hEq1, trivial⟩
        | readOnly php pbp | readWrite php pbp =>
          dsimp only
          cases Internal.parseCleanAbsSegs php with
          | none => dsimp only; rw [stateT_pure_run]; exact ⟨hEq1, trivial⟩
          | some phpSegs =>
            cases Internal.parseCleanAbsSegs pbp with
            | none => dsimp only; rw [stateT_pure_run]; exact ⟨hEq1, trivial⟩
            | some pbpSegs =>
              dsimp only
              rw [stateT_bind_run]
              have hDst := checkNoSymlinkPrefix_step proj fs hStat phpSegs (cSegs.drop pbpSegs.length) w1 (hEq1 ▸ hWf)
              cases hDr : (Internal.checkNoSymlinkPrefix fs phpSegs (cSegs.drop pbpSegs.length)).run w1 with
              | mk dstRes w2 =>
                rw [hDr] at hDst
                dsimp only
                have hEq2 : proj w2 = proj w := hDst.1.trans hEq1
                cases dstRes with
                | error e =>
                  dsimp only
                  rw [stateT_pure_run]
                  exact ⟨hEq2, hDst.2⟩
                | ok dstIsDir =>
                  dsimp only
                  by_cases hMis : (dstIsDir != srcIsDir) = true
                  · simp only [hMis, ↓reduceIte]; rw [stateT_pure_run]
                    exact ⟨hEq2, rfl, (show (!"nested mount target kind mismatch".isEmpty) = true from rfl)⟩
                  · simp only [hMis, Bool.false_eq_true, ↓reduceIte]; rw [stateT_pure_run]
                    exact ⟨hEq2, trivial⟩
  dsimp only [Internal.checkOneMountPreconditions]
  cases mountHostPath? m with
  | none =>
    dsimp only
    rw [stateT_bind_run, stateT_pure_run]
    exact hCont true w rfl
  | some hp =>
    dsimp only
    cases Internal.parseCleanAbsSegs hp with
    | none =>
      dsimp only
      rw [stateT_bind_run, stateT_pure_run, stateT_pure_run]
      exact ⟨rfl, rfl, (show (!"invalid mount hostPath".isEmpty) = true from rfl)⟩
    | some hpSegs =>
      dsimp only
      rw [stateT_bind_run]
      have hSrc := checkNoSymlinkPrefix_step proj fs hStat [] hpSegs w hWf
      cases hSr : (Internal.checkNoSymlinkPrefix fs [] hpSegs).run w with
      | mk srcRes w1 =>
        rw [hSr] at hSrc
        dsimp only
        cases srcRes with
        | error e =>
          dsimp only
          rw [stateT_pure_run]
          exact ⟨hSrc.1, hSrc.2⟩
        | ok srcIsDir => exact hCont srcIsDir w1 hSrc.1

private theorem checkAllMountsPreconditions_step {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (fs : LeanSwe.Fs.FsApiM (StateM W))
    (hStat : Core.ObeysStep proj Model.processStepWf (Model.execFsLstatStep fs) Model.allowedFsLstatStep)
    (sorted : List SandboxMount) :
    ∀ (ms : List SandboxMount) (w : W),
      Model.processStepWf (proj w) = true →
      let r := (Internal.checkAllMountsPreconditions fs sorted ms).run w
      proj r.2 = proj w ∧
      match r.1 with
      | .ok () => True
      | .error e => Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty = true
  | [], w, _ => by
    simp only [Internal.checkAllMountsPreconditions]
    rw [stateT_pure_run]
    exact ⟨rfl, trivial⟩
  | m :: rest, w, hWf => by
    simp only [Internal.checkAllMountsPreconditions]
    rw [stateT_bind_run]
    have hOne := checkOneMountPreconditions_step proj fs hStat sorted m w hWf
    cases hs : (Internal.checkOneMountPreconditions fs sorted m).run w with
    | mk res w1 =>
      rw [hs] at hOne
      have hEq : proj w1 = proj w := hOne.1
      cases res with
      | error e =>
        rw [stateT_pure_run]
        exact ⟨hEq, hOne.2⟩
      | ok u =>
        cases u
        have ih := checkAllMountsPreconditions_step proj fs hStat sorted rest w1 (hEq ▸ hWf)
        exact ⟨ih.1.trans hEq, ih.2⟩

private theorem classifyProcessError_post (valid : ValidBoxSpec) (pe : ProcessError)
    (hExec : LeanSwe.Process.Model.allowedExecResult false (Internal.mkBwrapRequest valid) (.error pe)) :
    match Internal.classifyProcessError valid.maxOutputBytes pe with
    | .ok r =>
      Model.withinOutputCap valid.maxOutputBytes r.stdout r.stderr ∧
      (r.outcome = .timedOut → valid.timeoutMs.isSome = true) ∧
      (r.outcome = .outputLimitExceeded → valid.maxOutputBytes.isSome = true)
    | .error e =>
      Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty := by
  unfold Internal.classifyProcessError
  have hCap := truncateToCap_withinOutputCap valid.maxOutputBytes
    (pe.stdout.getD ByteArray.empty) (pe.stderr.getD ByteArray.empty)
  cases hk : pe.kind with
  | timedOut =>
    exact ⟨hCap, (fun _ => (hExec.2.1 hk).1), (fun h => nomatch h)⟩
  | outputLimitExceeded =>
    refine ⟨hCap, (fun h => nomatch h), ?_⟩
    intro _
    have hm := (hExec.2.2.1 hk).1
    unfold Internal.mkBwrapRequest at hm
    cases hc : valid.maxOutputBytes with
    | none => simp [hc] at hm
    | some _ => rfl
  | terminatedBySignal =>
    dsimp only
    refine ⟨hCap, ?_, ?_⟩
    · cases valid.maxOutputBytes with
      | none => exact fun h => nomatch h
      | some _ =>
        dsimp only
        split <;> exact fun h => nomatch h
    · cases valid.maxOutputBytes with
      | none => exact fun h => nomatch h
      | some _ => exact fun _ => rfl
  | notFound | permissionDenied =>
    exact ⟨rfl, nonEmptyMsg_not_isEmpty "bwrap unavailable on host" pe.message (by decide)⟩
  | invalidInput | nonZeroExit | ioError =>
    exact ⟨rfl, nonEmptyMsg_not_isEmpty "sandbox process execution failed" pe.message (by decide)⟩

private theorem classifyExecResult_post (cap? : Option Nat) (res : ExecResult) :
    match Internal.classifyExecResult cap? res with
    | .ok r =>
      Model.withinOutputCap cap? r.stdout r.stderr ∧
      (r.outcome = .timedOut → False) ∧
      (r.outcome = .outputLimitExceeded → cap?.isSome = true)
    | .error e =>
      Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty := by
  unfold Internal.classifyExecResult
  cases cap? with
  | none => exact ⟨trivial, (fun h => nomatch h), (fun h => nomatch h)⟩
  | some cap =>
    dsimp only
    by_cases hGt : res.stdout.size + res.stderr.size > cap
    · simp only [hGt, ↓reduceIte]
      exact ⟨truncateToCap_withinOutputCap (some cap) res.stdout res.stderr,
        (fun h => nomatch h), (fun _ => rfl)⟩
    · simp only [hGt, ↓reduceIte]
      exact ⟨by unfold Model.withinOutputCap; omega, (fun h => nomatch h), (fun h => nomatch h)⟩

private theorem isAvailable_step {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (proc : ProcessApiM (StateM W))
    (hProc : Core.ObeysStep proj Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep)
    (w : W) (hWf : Model.processStepWf (proj w) = true) :
    let r := (Internal.isAvailable proc).run w
    LeanSwe.Process.Model.processStateWf (proj r.2) = true ∧
    (proj r.2).activeHandles = (proj w).activeHandles ∧
    ((proj r.2).nextHandleId = (proj w).nextHandleId ∨
     (proj r.2).nextHandleId = (proj w).nextHandleId + 1) := by
  dsimp only [Internal.isAvailable]
  rw [stateT_bind_run]
  rcases validateRequestModel_mkProbeRequest with ⟨norm, hReqOk⟩
  have hRaw := hProc w (.run Internal.mkProbeRequest) hWf
  dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
    Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep] at hRaw
  rw [stateT_map_run] at hRaw
  cases hRun : (proc.run Internal.mkProbeRequest).run w with
  | mk rawRes w1 =>
    rw [hRun] at hRaw
    rcases hRaw with ⟨_, hw2, hPkgRun⟩
    dsimp only [LeanSwe.Process.Model.allowedPkgRun] at hPkgRun
    rw [hReqOk] at hPkgRun
    cases rawRes <;> (rw [stateT_pure_run]; exact ⟨hw2, hPkgRun.1, hPkgRun.2.1⟩)

private theorem checkAvailOr_step {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (proc : ProcessApiM (StateM W))
    (hProc : Core.ObeysStep proj Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep)
    (valid : ValidBoxSpec) (w0 w1 : W)
    (hWf0 : LeanSwe.Process.Model.processStateWf (proj w0) = true)
    (hWf1 : LeanSwe.Process.Model.processStateWf (proj w1) = true)
    (hAct1 : (proj w1).activeHandles = (proj w0).activeHandles)
    (hId1 : (proj w1).nextHandleId = (proj w0).nextHandleId ∨
            (proj w1).nextHandleId = (proj w0).nextHandleId + 1)
    (fallback : Except SandboxError SandboxResult)
    (hFb : match fallback with
      | .ok r =>
        Model.withinOutputCap valid.maxOutputBytes r.stdout r.stderr ∧
        (r.outcome = .timedOut → valid.timeoutMs.isSome = true) ∧
        (r.outcome = .outputLimitExceeded → valid.maxOutputBytes.isSome = true)
      | .error e =>
        Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty) :
    let r := (Internal.checkAvailOr proc fallback).run w1
    Model.allowedProcessHandleStep (proj w0) (proj r.2) ∧
    match r.1 with
    | .ok res =>
      Model.withinOutputCap valid.maxOutputBytes res.stdout res.stderr ∧
      (res.outcome = .timedOut → valid.timeoutMs.isSome = true) ∧
      (res.outcome = .outputLimitExceeded → valid.maxOutputBytes.isSome = true)
    | .error e =>
      Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty := by
  dsimp only [Internal.checkAvailOr]
  rw [stateT_bind_run]
  have hAv := isAvailable_step proj proc hProc w1 hWf1
  cases hA : (Internal.isAvailable proc).run w1 with
  | mk ok w2 =>
    rw [hA] at hAv
    rcases hAv with ⟨hw2, hAct2, hId2⟩
    dsimp only at hw2 hAct2 hId2
    have hHdl : Model.allowedProcessHandleStep (proj w0) (proj w2) :=
      ⟨hWf0, hw2, hAct2.trans hAct1, by omega, by omega⟩
    cases ok with
    | true =>
      simp only [↓reduceIte]
      rw [stateT_pure_run]
      exact ⟨hHdl, hFb⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [stateT_pure_run]
      exact ⟨hHdl, rfl, by decide⟩

private theorem obeysStepFrom_process :
    Core.ObeysStepFrom2 id Model.processStepWf
      Model.execProcessStep Model.allowedProcessStep
      Model.execFsLstatStep Model.allowedFsLstatStep
      Model.processStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj proc fs hProc hStat w req hWf
  have hWfP : LeanSwe.Process.Model.processStateWf (proj w) = true := hWf
  cases req with
  | validateSpec spec =>
    exact ⟨validateSpec_eq_model spec, rfl, hWf⟩
  | isAvailable =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Function.comp, id]
    rw [stateT_map_run]
    have hAv := isAvailable_step proj proc hProc w hWf
    cases hA : (Internal.isAvailable proc).run w with
    | mk _ w1 =>
      rw [hA] at hAv
      rcases hAv with ⟨hw1, hAct1, hId1⟩
      dsimp only at hw1 hAct1 hId1 ⊢
      exact ⟨hWfP, hw1, hAct1, by omega, by omega⟩
  | run spec =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.run, Function.comp, id]
    rw [stateT_map_run]
    dsimp only [Model.allowedPkgStep]
    rw [← validateSpec_eq_model spec]
    cases hv : Internal.validateSpec spec with
    | error e =>
      rw [stateT_pure_run]
      exact ⟨rfl, rfl, hWf⟩
    | ok valid =>
      rw [stateT_bind_run]
      let sorted := Internal.sortMountsByDepth valid.mounts.toList
      have hPre := checkAllMountsPreconditions_step proj fs hStat sorted sorted w hWf
      cases hChk : (Internal.checkAllMountsPreconditions fs sorted sorted).run w with
      | mk chkRes wPre =>
        rw [hChk] at hPre
        have hEqPre : proj wPre = proj w := hPre.1
        cases chkRes with
        | error e =>
          rw [stateT_pure_run]
          exact ⟨⟨hWfP, hEqPre ▸ hWfP, by rw [hEqPre],
            by dsimp only; rw [hEqPre]; exact Nat.le_refl _,
            by dsimp only; rw [hEqPre]; omega⟩, hPre.2⟩
        | ok _ =>
          rw [stateT_bind_run]
          have hWfPre : Model.processStepWf (proj wPre) = true := hEqPre ▸ hWf
          rcases validateSpec_ok_request_valid spec valid hv with ⟨norm, hReqOk⟩
          have hRaw := hProc wPre (.run (Internal.mkBwrapRequest valid)) hWfPre
          dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
            Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep] at hRaw
          rw [stateT_map_run] at hRaw
          cases hRun : (proc.run (Internal.mkBwrapRequest valid)).run wPre with
          | mk rawRes w1 =>
            rw [hRun] at hRaw
            rcases hRaw with ⟨_, hw2, hPkgRun⟩
            dsimp only [LeanSwe.Process.Model.allowedPkgRun] at hPkgRun
            rw [hReqOk] at hPkgRun
            have hAct1 : (proj w1).activeHandles = (proj w).activeHandles := by
              rw [hPkgRun.1, hEqPre]
            have hId1 : (proj w1).nextHandleId = (proj w).nextHandleId ∨
                (proj w1).nextHandleId = (proj w).nextHandleId + 1 := by
              simpa [hEqPre] using hPkgRun.2.1
            have hHdl1 : Model.allowedProcessHandleStep (proj w) (proj w1) :=
              ⟨hWfP, hw2, hAct1, by omega, by omega⟩
            cases rawRes with
            | error pe =>
              have hPost := classifyProcessError_post valid pe hPkgRun.2.2
              by_cases hOut : (pe.kind == .outputLimitExceeded || pe.kind == .terminatedBySignal || pe.kind == .timedOut) = true
              · simp only [hOut, ↓reduceIte]
                exact checkAvailOr_step proj proc hProc valid w w1 hWfP hw2 hAct1 hId1 _ hPost
              · simp only [hOut, Bool.false_eq_true, ↓reduceIte]
                rw [stateT_pure_run]
                exact ⟨hHdl1, hPost⟩
            | ok er =>
              have hPostRaw := classifyExecResult_post valid.maxOutputBytes er
              have hPost : match Internal.classifyExecResult valid.maxOutputBytes er with
                  | .ok r =>
                    Model.withinOutputCap valid.maxOutputBytes r.stdout r.stderr ∧
                    (r.outcome = .timedOut → valid.timeoutMs.isSome = true) ∧
                    (r.outcome = .outputLimitExceeded → valid.maxOutputBytes.isSome = true)
                  | .error e =>
                    Model.isHostErrorKind e.kind = true ∧ !e.message.isEmpty := by
                cases hCl : Internal.classifyExecResult valid.maxOutputBytes er with
                | error e => rw [hCl] at hPostRaw; exact hPostRaw
                | ok r =>
                  rw [hCl] at hPostRaw
                  exact ⟨hPostRaw.1, fun ht => False.elim (hPostRaw.2.1 ht), hPostRaw.2.2⟩
              by_cases hExNz : (er.exitCode != 0) = true
              · simp only [hExNz, ↓reduceIte]
                exact checkAvailOr_step proj proc hProc valid w w1 hWfP hw2 hAct1 hId1 _ hPost
              · simp only [hExNz, Bool.false_eq_true, ↓reduceIte]
                rw [stateT_pure_run]
                exact ⟨hHdl1, hPost⟩

/-- Full public `Interface` refinement of `LeanSwe.ProcessSandbox`: exact pure equality on
    `validateSpec` against `Model.validateSpecModel` and compositional `Core.ObeysStepFrom2`
    lifting `LeanSwe.Process.Model.allowedPkgStep` and `Model.allowedFsLstatStep` to `Internal.mkApiM`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.ProcessSandbox.validateSpec Model.validateSpecModel ∧
    Core.ObeysStepFrom2 id Model.processStepWf
      Model.execProcessStep Model.allowedProcessStep
      Model.execFsLstatStep Model.allowedFsLstatStep
      Model.processStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨validateSpec_eq_model, obeysStepFrom_process⟩

private theorem list_contains_map_filter_false {xs : List LeanSwe.Process.Model.ProcessHandleEntry}
    {p : LeanSwe.Process.Model.ProcessHandleEntry → Bool} {x : Nat}
    (h : (xs.map (·.handleId)).contains x = false) :
    ((xs.filter p).map (·.handleId)).contains x = false := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩
    · exact ih h.2

private theorem hasNoDupHandleIds_filter (xs : List LeanSwe.Process.Model.ProcessHandleEntry)
    (p : LeanSwe.Process.Model.ProcessHandleEntry → Bool)
    (h : LeanSwe.Process.Model.hasNoDupHandleIds (xs.map (·.handleId)) = true) :
    LeanSwe.Process.Model.hasNoDupHandleIds ((xs.filter p).map (·.handleId)) = true := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds,
      Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds,
        Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨list_contains_map_filter_false h.1, ih h.2⟩
    · exact ih h.2

private theorem processStateWf_filter (s : LeanSwe.Process.Model.ProcessModelState)
    (p : LeanSwe.Process.Model.ProcessHandleEntry → Bool)
    (hWf : LeanSwe.Process.Model.processStateWf s = true) :
    LeanSwe.Process.Model.processStateWf { s with activeHandles := s.activeHandles.filter p } = true := by
  unfold LeanSwe.Process.Model.processStateWf at hWf ⊢
  simp only [Bool.and_eq_true] at hWf ⊢
  refine ⟨⟨hWf.1.1, hasNoDupHandleIds_filter s.activeHandles p hWf.1.2⟩, ?_⟩
  rw [List.all_eq_true] at hWf ⊢
  intro e he
  exact hWf.2 e (List.mem_filter.mp he).1

private def simRunPure (req : ExecRequest) (s : LeanSwe.Process.Model.ProcessModelState) :
    Except ProcessError ExecResult × LeanSwe.Process.Model.ProcessModelState :=
  match LeanSwe.Process.Model.validateRequestModel req with
  | .error verr => (.error verr, s)
  | .ok _ => (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)

private theorem simRunPure_snd (req : ExecRequest) (s : LeanSwe.Process.Model.ProcessModelState) :
    (simRunPure req s).2 = s := by
  unfold simRunPure
  cases LeanSwe.Process.Model.validateRequestModel req <;> rfl

private theorem simRunPure_allowedPkgRun (checked : Bool) (req : ExecRequest)
    (s : LeanSwe.Process.Model.ProcessModelState) :
    LeanSwe.Process.Model.allowedPkgRun checked s req (simRunPure req s).1 (simRunPure req s).2 := by
  unfold simRunPure LeanSwe.Process.Model.allowedPkgRun
  cases LeanSwe.Process.Model.validateRequestModel req with
  | error _ => exact ⟨rfl, rfl⟩
  | ok _ =>
    refine ⟨rfl, Or.inl rfl, fun _ => rfl, fun lim _ => ?_⟩
    change 0 ≤ lim
    exact Nat.zero_le lim

private def witnessProcessApi : ProcessApiM (StateM LeanSwe.Process.Model.ProcessModelState) :=
  { mapRawError := LeanSwe.Process.Model.mapRawErrorModel
    validateRequest := LeanSwe.Process.Model.validateRequestModel
    mkCommandRequest := LeanSwe.Process.Model.mkCommandRequestModel
    withTextInput := LeanSwe.Process.Model.withTextInputModel
    spawn := fun r s =>
      match LeanSwe.Process.Model.validateSpawnRequestModel r with
      | .error err => (.error err, s)
      | .ok _ => (.error { kind := .ioError, message := "mock spawn unavailable" }, s)
    awaitOutput := fun _ _ timeoutMs _ s =>
      if timeoutMs == some 0 then
        (.error { kind := .invalidInput, message := "timeoutMs must be greater than zero" }, s)
      else
        (.error { kind := .ioError, message := "mock await unavailable" }, s)
    killProcessGroup := fun _ s => (.ok (), s)
    reap := fun h s =>
      (.ok (), { s with activeHandles := s.activeHandles.filter (·.handleId != h.handleId) })
    run := simRunPure
    runChecked := simRunPure
    runCommand := fun prog args => simRunPure (LeanSwe.Process.Model.mkCommandRequestModel prog args)
    runCommandChecked := fun prog args => simRunPure (LeanSwe.Process.Model.mkCommandRequestModel prog args)
    activeProcessCount := fun s => (s.activeHandles.length, s) }

private def mockFsErr : LeanSwe.Fs.FsError :=
  { kind := .notFound, message := "mock fs unavailable" }

private def witnessFsApi :
    LeanSwe.Fs.FsApiM (StateM LeanSwe.Process.Model.ProcessModelState) :=
  { join := fun a b => a ++ "/" ++ b
    joinMany := fun _ => ""
    normPath := id
    parent := fun _ => none
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun _ _ => .error mockFsErr
    withSuffix := fun _ _ => .error mockFsErr
    isAbsolute := fun _ => false
    relativeTo := fun _ _ => .error mockFsErr
    mapRawError := fun _ => mockFsErr
    readText := fun _ s => (.error mockFsErr, s)
    writeText := fun _ _ s => (.error mockFsErr, s)
    appendText := fun _ _ s => (.error mockFsErr, s)
    readBytes := fun _ s => (.error mockFsErr, s)
    writeBytes := fun _ _ s => (.error mockFsErr, s)
    atomicWriteBytes := fun _ _ s => (.error mockFsErr, s)
    atomicWriteText := fun _ _ s => (.error mockFsErr, s)
    touch := fun _ _ s => (.error mockFsErr, s)
    mkdir := fun _ _ _ s => (.error mockFsErr, s)
    unlink := fun _ _ s => (.error mockFsErr, s)
    rmdir := fun _ s => (.error mockFsErr, s)
    rmtree := fun _ _ s => (.error mockFsErr, s)
    rename := fun _ _ s => (.error mockFsErr, s)
    copyFile := fun _ _ s => (.error mockFsErr, s)
    copyTree := fun _ _ _ s => (.error mockFsErr, s)
    pathExists := fun _ s => (.error mockFsErr, s)
    isFile := fun _ s => (.error mockFsErr, s)
    isDir := fun _ s => (.error mockFsErr, s)
    isSymlink := fun _ s => (.error mockFsErr, s)
    stat := fun _ s => (.error mockFsErr, s)
    lstat := fun _ s => (.error mockFsErr, s)
    chmod := fun _ _ s => (.error mockFsErr, s)
    symlink := fun _ _ s => (.error mockFsErr, s)
    readLink := fun _ s => (.error mockFsErr, s)
    resolve := fun _ s => (.error mockFsErr, s)
    cwd := fun s => (.error mockFsErr, s)
    listDir := fun _ s => (.error mockFsErr, s)
    walk := fun _ s => (.error mockFsErr, s)
    glob := fun _ _ s => (.error mockFsErr, s)
    rglob := fun _ _ s => (.error mockFsErr, s)
    withFileLock := fun _ _ _ _ s => (.error mockFsErr, s)
    tryWithFileLock := fun _ _ _ _ s => (.error mockFsErr, s) }

/-- Non-vacuity witness showing both `ProcessApiM` and `FsApiM` contracts assumed by `obeys_model` are inhabited. -/
theorem obeys_model_nonvacuous :
    (∃ proc : ProcessApiM (StateM LeanSwe.Process.Model.ProcessModelState),
      Core.ObeysStep id Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep) ∧
    (∃ fs : LeanSwe.Fs.FsApiM (StateM LeanSwe.Process.Model.ProcessModelState),
      Core.ObeysStep id Model.processStepWf (Model.execFsLstatStep fs) Model.allowedFsLstatStep) := by
  refine ⟨⟨witnessProcessApi, ?_⟩, ⟨witnessFsApi, ?_⟩⟩
  · intro s req hWf
    have hWfP : LeanSwe.Process.Model.processStateWf s = true := hWf
    cases req with
    | spawn r =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      cases LeanSwe.Process.Model.validateSpawnRequestModel r with
      | error _ => exact ⟨hWfP, hWfP, rfl, rfl⟩
      | ok _ =>
        refine ⟨hWfP, hWfP, rfl, ?_⟩
        dsimp only [LeanSwe.Process.Model.isNonOutcomeError]
        decide
    | awaitOutput h stdin timeoutMs maxOutputBytes =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      cases hT : (timeoutMs == some 0) with
      | true =>
        rw [ite_eq_left rfl, ite_eq_left rfl]
        exact ⟨hWfP, hWfP, rfl, rfl⟩
      | false =>
        rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        dsimp only [LeanSwe.Process.Model.allowedAwaitCore, LeanSwe.Process.Model.isNonOutcomeError]
        exact ⟨hWfP, hWfP, hWfP, rfl, rfl, rfl, by decide⟩
    | killProcessGroup _ => exact ⟨hWfP, hWfP, rfl, trivial⟩
    | reap _ => exact ⟨hWfP, processStateWf_filter s _ hWfP, rfl, rfl, trivial⟩
    | run r =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      refine ⟨hWfP, ?_, simRunPure_allowedPkgRun false r s⟩
      rw [simRunPure_snd]; exact hWfP
    | runChecked r =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      refine ⟨hWfP, ?_, simRunPure_allowedPkgRun true r s⟩
      rw [simRunPure_snd]; exact hWfP
    | runCommand prog args =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      refine ⟨hWfP, ?_, simRunPure_allowedPkgRun false (LeanSwe.Process.Model.mkCommandRequestModel prog args) s⟩
      rw [simRunPure_snd]; exact hWfP
    | runCommandChecked prog args =>
      dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
        Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
      rw [stateT_map_run]
      dsimp only [StateT.run, witnessProcessApi]
      refine ⟨hWfP, ?_, simRunPure_allowedPkgRun true (LeanSwe.Process.Model.mkCommandRequestModel prog args) s⟩
      rw [simRunPure_snd]; exact hWfP
    | activeProcessCount => exact ⟨hWfP, hWfP, rfl, rfl⟩
  · intro s _ hWf
    refine ⟨rfl, hWf, ?_⟩
    dsimp only [Model.execFsLstatStep, witnessFsApi, mockFsErr, StateT.run]
    decide

/-- Exact structural layout of the `bwrap` argv emitted by `Internal.mkBwrapArgs`. -/
theorem mkBwrapArgs_toList_eq (valid : ValidBoxSpec) :
    (Internal.mkBwrapArgs valid).toList =
      Internal.osPresetFlags ++
      (Internal.sortMountsByDepth valid.mounts.toList).flatMap Internal.mountFlags ++
      ["--remount-ro", "/", "--unshare-all"] ++
      Internal.networkFlags valid.network ++
      ["--die-with-parent", "--new-session", "--clearenv"] ++
      Internal.envFlags valid.env.toList ++
      ["--chdir", valid.cwd, "--", valid.program] ++
      valid.args.toList :=
  rfl

/-- `Internal.networkFlags` emits `"--share-net"` iff `net = .open`. -/
theorem networkFlags_share_net_iff (net : NetworkMode) :
    "--share-net" ∈ Internal.networkFlags net ↔ net = .«open» := by
  cases net with
  | closed => simp [Internal.networkFlags]
  | «open» => simp [Internal.networkFlags]

/-- `Internal.mkBwrapArgs` unconditionally includes all core namespace, session, root-ro, and clean-env flags. -/
theorem mkBwrapArgs_core_isolation_flags (valid : ValidBoxSpec) :
    "--remount-ro" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--unshare-all" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--die-with-parent" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--new-session" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--clearenv" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--chdir" ∈ (Internal.mkBwrapArgs valid).toList ∧
    "--" ∈ (Internal.mkBwrapArgs valid).toList := by
  rw [mkBwrapArgs_toList_eq]
  simp

/-- `Internal.envFlags` expands each `(k, v)` entry into `["--setenv", k, v]` in order. -/
theorem envFlags_eq_flatMap :
    ∀ kvs : List (String × String),
      Internal.envFlags kvs = kvs.flatMap (fun kv => ["--setenv", kv.1, kv.2])
  | [] => rfl
  | (k, v) :: rest => by
    simp [Internal.envFlags, envFlags_eq_flatMap rest]

private theorem list_contains_map_fst_eq_any (xs : List (String × String)) (k : String) :
    (xs.map Prod.fst).contains k = xs.any (fun p => p.1 == k) := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    have hSwap : (k == p.1) = (p.1 == k) := by
      by_cases h : k = p.1
      · subst h; simp
      · have h' : p.1 ≠ k := fun heq => h heq.symm
        simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']
    simp only [List.map_cons, List.contains_cons, List.any_cons, ih, hSwap]

/-- `Internal.dedupEnvPairs` yields pairwise distinct environment variable keys. -/
theorem dedupEnvPairs_distinct_keys :
    ∀ kvs : List (String × String),
      Internal.allDistinct ((Internal.dedupEnvPairs kvs).map Prod.fst) = true
  | [] => rfl
  | kv :: rest => by
    have ih := dedupEnvPairs_distinct_keys rest
    unfold Internal.dedupEnvPairs
    dsimp only
    cases hAny : (Internal.dedupEnvPairs rest).any (fun p => p.1 == kv.1) with
    | true => simp [ih]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, Internal.allDistinct,
        Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨by rw [list_contains_map_fst_eq_any, hAny], ih⟩

/-- Every validated `ValidBoxSpec` carries deduplicated environment keys including `"PATH"`. -/
theorem validateSpec_ok_env_distinct_and_path (spec : BoxSpec) (valid : ValidBoxSpec)
    (hVal : LeanSwe.ProcessSandbox.validateSpec spec = .ok valid) :
    Internal.allDistinct (valid.env.toList.map Prod.fst) = true ∧
    valid.env.toList.any (fun kv => kv.1 == "PATH") = true := by
  have hInt : Internal.validateSpec spec = .ok valid := hVal
  have hClean :
      let deduped := Internal.dedupEnvPairs spec.env.toList
      let cleanEnv :=
        if deduped.any (fun kv => kv.1 == "PATH") then deduped
        else ("PATH", Internal.defaultSandboxPath) :: deduped
      Internal.allDistinct (cleanEnv.map Prod.fst) = true ∧
      cleanEnv.any (fun kv => kv.1 == "PATH") = true := by
    dsimp only
    cases hPath : (Internal.dedupEnvPairs spec.env.toList).any (fun kv => kv.1 == "PATH") with
    | true => exact ⟨by simpa [hPath] using dedupEnvPairs_distinct_keys spec.env.toList, by simp [hPath]⟩
    | false =>
      simp only [hPath, Bool.false_eq_true, ↓reduceIte, List.map_cons, Internal.allDistinct,
        List.any_cons, Bool.and_eq_true, Bool.not_eq_true', beq_self_eq_true, Bool.true_or, and_true]
      exact ⟨by rw [list_contains_map_fst_eq_any, hPath], dedupEnvPairs_distinct_keys spec.env.toList⟩
  unfold Internal.validateSpec at hInt
  simp only [Bind.bind, Except.bind] at hInt
  repeat (split at hInt; · contradiction)
  cases hCwd : spec.cwd with
  | none =>
    simp only [hCwd] at hInt
    cases hm : Internal.validateMountsList spec.mounts.toList with
    | error _ => rw [hm] at hInt; contradiction
    | ok _ =>
      rw [hm] at hInt; dsimp only at hInt
      split at hInt; · contradiction
      split at hInt; · contradiction
      injection hInt with hEq; subst hEq
      simpa using hClean
  | some d =>
    simp only [hCwd] at hInt
    cases hNorm : Internal.normalizeCleanAbsPath d with
    | none => simp [hNorm] at hInt
    | some _ =>
      simp only [hNorm] at hInt
      cases hm : Internal.validateMountsList spec.mounts.toList with
      | error _ => rw [hm] at hInt; contradiction
      | ok _ =>
        rw [hm] at hInt; dsimp only at hInt
        split at hInt; · contradiction
        split at hInt; · contradiction
        injection hInt with hEq; subst hEq
        simpa using hClean

/-- `Internal.sortMountsByDepth` preserves the exact multiset of mounts (`List.Perm`). -/
theorem sortMountsByDepth_perm (ms : List SandboxMount) :
    (Internal.sortMountsByDepth ms).Perm ms :=
  List.mergeSort_perm ms _

/-- `Internal.sortMountsByDepth` orders mounts by ascending canonical `boxPath` segment depth. -/
theorem sortMountsByDepth_pairwise (ms : List SandboxMount) :
    (Internal.sortMountsByDepth ms).Pairwise
      (fun a b => Internal.mountBoxDepth a ≤ Internal.mountBoxDepth b) := by
  have hPw := List.pairwise_mergeSort (le := fun a b => decide (Internal.mountBoxDepth a ≤ Internal.mountBoxDepth b))
    (fun _ _ _ hab hbc => decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      cases h : decide (Internal.mountBoxDepth a ≤ Internal.mountBoxDepth b) with
      | true => rfl
      | false =>
        have hNot := of_decide_eq_false h
        exact decide_eq_true (by omega))
    ms
  exact hPw.imp (fun h => of_decide_eq_true h)

/-- A strictly nested child mount can never appear before its parent mount in `Internal.sortMountsByDepth`. -/
theorem sortMountsByDepth_child_not_before_parent (ms pre mid post : List SandboxMount)
    (parent child : SandboxMount) (pSegs cSegs : List String)
    (hp : Internal.parseCleanAbsSegs (mountBoxPath parent) = some pSegs)
    (hc : Internal.parseCleanAbsSegs (mountBoxPath child) = some cSegs)
    (hStrict : pSegs.length < cSegs.length)
    (hSplit : Internal.sortMountsByDepth ms = pre ++ [child] ++ mid ++ [parent] ++ post) :
    False := by
  have hPw := sortMountsByDepth_pairwise ms
  rw [hSplit] at hPw
  have hLe : Internal.mountBoxDepth child ≤ Internal.mountBoxDepth parent := by
    have h1 := (List.pairwise_append.mp (by simpa [List.append_assoc] using hPw)).2.1
    have h2 := (List.pairwise_cons.mp h1).1 parent (by simp)
    exact h2
  unfold Internal.mountBoxDepth at hLe
  rw [hp, hc] at hLe
  dsimp only at hLe
  omega

end LeanSwe.ProcessSandbox.Proofs

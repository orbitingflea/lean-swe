import LeanSwe.ProcessSandbox.Host.Cgroup
import LeanSwe.ProcessSandbox.Host.Preset

namespace LeanSwe.ProcessSandbox.Proofs.HostCgroupPreset

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Host.Cgroup
open LeanSwe.ProcessSandbox.Host.Preset

private theorem list_isPrefixOf_append_self (p r : List Char) :
    p.isPrefixOf (p ++ r) = true := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- `cappedPidsMax` always adds the 2 `--as-pid-1` wrapper tasks unless saturated at `UInt64.size - 1`, and never exceeds `UInt64.size - 1`. -/
theorem cappedPidsMax_bounds (n : Nat) :
    cappedPidsMax n ≤ UInt64.size - 1 ∧
    (n + 2 ≤ UInt64.size - 1 → cappedPidsMax n = n + 2) := by
  unfold cappedPidsMax
  constructor
  · exact Nat.min_le_right _ _
  · intro h
    exact Nat.min_eq_left h

/-- `cgroupSubfile` joins directory and control filename with `'/'`. -/
theorem cgroupSubfile_eq (dir name : String) :
    cgroupSubfile dir name = s!"{dir}/{name}" := rfl

/-- `parseDelegatedCgroupParent` maps root `"0::/"` to `some "/sys/fs/cgroup"`. -/
theorem parseDelegatedCgroupParent_root :
    parseDelegatedCgroupParent "0::/\n" = some "/sys/fs/cgroup" := by
  decide

/-- `parseDelegatedCgroupParent` maps a nested delegated scope to its parent under `"/sys/fs/cgroup"`. -/
theorem parseDelegatedCgroupParent_nested :
    parseDelegatedCgroupParent "0::/user.slice/user-1000.slice/session.scope\n" =
      some "/sys/fs/cgroup/user.slice/user-1000.slice" := by
  decide

/-- `parseDelegatedCgroupParent` handles trailing slashes and hybrid v1/v2 lines. -/
theorem parseDelegatedCgroupParent_hybrid_and_slash :
    parseDelegatedCgroupParent "1:name=systemd:/a\n0::/user.slice/run.scope/\r\n" =
      some "/sys/fs/cgroup/user.slice" := by
  decide

/-- `parseDelegatedCgroupParent` rejects missing `0::` lines and non-absolute v2 paths. -/
theorem parseDelegatedCgroupParent_rejects_invalid :
    parseDelegatedCgroupParent "1:cpu:/foo\n" = none ∧
    parseDelegatedCgroupParent "0::relative/path\n" = none := by
  decide

/-- Whenever `parseDelegatedCgroupParent` succeeds, the returned directory begins with `"/sys/fs/cgroup"`. -/
theorem parseDelegatedCgroupParent_startsWith_cgroupfs (txt p : String)
    (h : parseDelegatedCgroupParent txt = some p) :
    "/sys/fs/cgroup".toList.isPrefixOf p.toList = true := by
  unfold parseDelegatedCgroupParent at h
  dsimp only at h
  split at h
  · cases h
  · next v2Rel _ =>
    split at h
    · cases h
    · split at h
      · cases h
        decide
      · cases h
        rw [String.toList_append]
        exact list_isPrefixOf_append_self _ _

/-- `isPopulatedZero` distinguishes empty vs populated `cgroup.events` text. -/
theorem isPopulatedZero_examples :
    isPopulatedZero "populated 0\nfrozen 0\n" = true ∧
    isPopulatedZero "populated 1\nfrozen 0\n" = false ∧
    isPopulatedZero "" = false := by
  decide

/-- `cleanupCgroupDir` succeeds immediately with `.ok ()` when `cgDir` is empty. -/
theorem cleanupCgroupDir_empty_ok {m : Type → Type} [Monad m] [LawfulMonad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m) :
    cleanupCgroupDir files timeRand "" = pure (.ok ()) := by
  simp [cleanupCgroupDir]

/-- `normalizeAbsLexical` rejects any non-slash-prefixed path. -/
theorem normalizeAbsLexical_rejects_relative (p : String) (h : p.toList.head? ≠ some '/') :
    normalizeAbsLexical p = none := by
  unfold normalizeAbsLexical
  have hb : (p.toList.head? != some '/') = true := by
    simp [bne, beq_false_of_ne h]
  simp [hb]

/-- `normalizeAbsLexical` collapses redundant slashes/dots, preserves `"/"`, and rejects `".."`. -/
theorem normalizeAbsLexical_examples :
    normalizeAbsLexical "/" = some "/" ∧
    normalizeAbsLexical "///usr/./local//home/" = some "/usr/local/home" ∧
    normalizeAbsLexical "/usr/../etc" = none ∧
    normalizeAbsLexical "usr/local" = none := by
  decide

private theorem normalizeAbsLexical_go_head_slash (segs : List (List Char)) (accRev : List String) (q : String)
    (h : normalizeAbsLexical.go segs accRev = some q) :
    q.toList.head? = some '/' := by
  induction segs generalizing accRev with
  | nil =>
    unfold normalizeAbsLexical.go at h
    split at h
    · cases h; rfl
    · cases h; simp [String.toList_append]
  | cons seg rest ih =>
    unfold normalizeAbsLexical.go at h
    split at h
    · exact ih accRev h
    · split at h
      · cases h
      · exact ih (String.ofList seg :: accRev) h

/-- Every output of `normalizeAbsLexical` is guaranteed to start with `'/'`. -/
theorem normalizeAbsLexical_head_slash (p q : String)
    (h : normalizeAbsLexical p = some q) :
    q.toList.head? = some '/' := by
  unfold normalizeAbsLexical at h
  dsimp only at h
  split at h
  · cases h
  · exact normalizeAbsLexical_go_head_slash (splitChar '/' p.toList) [] q h

/-- `isUnderSystemRootLexical` accepts strict children of the 5 system roots and rejects roots themselves or non-system roots. -/
theorem isUnderSystemRootLexical_examples :
    isUnderSystemRootLexical "/usr/local/share/dir" = true ∧
    isUnderSystemRootLexical "/lib64/nested" = true ∧
    isUnderSystemRootLexical "/usr" = false ∧
    isUnderSystemRootLexical "/usr/" = false ∧
    isUnderSystemRootLexical "/opt/u" = false ∧
    isUnderSystemRootLexical "/usr2/u" = false := by
  decide

private theorem dedupStrings_fold_mem (acc : Array String) (xs : List String) (s : String) :
    s ∈ xs.foldl (fun a x => if a.contains x then a else a.push x) acc ↔ (s ∈ acc ∨ s ∈ xs) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hx : x ∈ acc
    · have hax : acc.contains x = true := Array.contains_iff_mem.mpr hx
      simp only [hax, ↓reduceIte]
      constructor
      · intro h; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | rfl | h
        · exact Or.inl h
        · exact Or.inl hx
        · exact Or.inr h
    · have hax : acc.contains x = false := by
        cases hc : acc.contains x
        · rfl
        · exact False.elim (hx (Array.contains_iff_mem.mp hc))
      simp only [hax, Bool.false_eq_true, ↓reduceIte, Array.mem_push]
      constructor
      · intro h; rcases h with (h | rfl) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | rfl | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr h

/-- `dedupStrings` preserves exact element membership. -/
theorem dedupStrings_mem_iff (xs : List String) (s : String) :
    s ∈ dedupStrings xs ↔ s ∈ xs := by
  unfold dedupStrings
  rw [dedupStrings_fold_mem]
  simp

/-- `presetEtcAllowlist` never includes sensitive credential files such as `/etc/shadow` or `/etc/gshadow`. -/
theorem presetEtcAllowlist_excludes_shadow :
    presetEtcAllowlist.toList.contains "/etc/shadow" = false ∧
    presetEtcAllowlist.toList.contains "/etc/gshadow" = false := by
  decide

end LeanSwe.ProcessSandbox.Proofs.HostCgroupPreset

import LeanSwe.Env.Interface
import LeanSwe.Env.SpecTests
import LeanSwe.Env.Raw.Proofs

namespace LeanSwe.Env.Proofs

open Core
open Core.NondetTest

private theorem hasInvalidKeyChar_iff (cs : List Char) :
    Internal.hasInvalidKeyChar cs = true ↔ '=' ∈ cs ∨ Char.ofNat 0 ∈ cs := by
  induction cs with
  | nil => simp [Internal.hasInvalidKeyChar]
  | cons c rest ih =>
    simp only [Internal.hasInvalidKeyChar, Bool.or_eq_true, beq_iff_eq, List.mem_cons, ih]
    constructor
    · intro h
      rcases h with (h1 | h2) | h3 | h4
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inl (Or.inr h3)
      · exact Or.inr (Or.inr h4)
    · intro h
      rcases h with (h1 | h2) | (h3 | h4)
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (Or.inr h3.symm)
      · exact Or.inr (Or.inr h4)

private theorem isValidKey_true_iff (key : String) :
    Internal.isValidKey key = true ↔ key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
  unfold Internal.isValidKey
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', List.isEmpty_eq_false_iff]
  have hmem : Internal.hasInvalidKeyChar key.toList = false ↔
      '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · intro heq
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inl heq)
        rw [hf] at ht
        cases ht
      · intro hnul
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inr hnul)
        rw [hf] at ht
        cases ht
    · intro ⟨h1, h2⟩
      cases h : Internal.hasInvalidKeyChar key.toList with
      | false => rfl
      | true =>
        rcases (hasInvalidKeyChar_iff key.toList).mp h with heq | hnul
        · exact absurd heq h1
        · exact absurd hnul h2
  have hne : key.toList ≠ [] ↔ key ≠ "" := by
    constructor
    · intro h heq
      subst heq
      exact h rfl
    · intro h hl
      apply h
      rw [← String.ofList_toList (s := key), hl]
  rw [hmem, hne]

private theorem isValidKey_false_iff (key : String) :
    Internal.isValidKey key = false ↔ key = "" ∨ '=' ∈ key.toList ∨ Char.ofNat 0 ∈ key.toList := by
  cases hk : Internal.isValidKey key with
  | true =>
    have ht := (isValidKey_true_iff key).mp hk
    constructor
    · intro h; cases h
    · intro h
      rcases h with h1 | h2 | h3
      · exact absurd h1 ht.1
      · exact absurd h2 ht.2.1
      · exact absurd h3 ht.2.2
  | false =>
    constructor
    · intro _
      by_cases h1 : key = ""
      · exact Or.inl h1
      · by_cases h2 : '=' ∈ key.toList
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : Char.ofNat 0 ∈ key.toList
          · exact Or.inr (Or.inr h3)
          · have ht := (isValidKey_true_iff key).mpr ⟨h1, h2, h3⟩
            rw [hk] at ht
            cases ht
    · intro _; rfl

private theorem splitColonRaw_ne_nil (cs : List Char) :
    Internal.splitColonRaw cs ≠ [] := by
  induction cs with
  | nil => simp [Internal.splitColonRaw]
  | cons c rest _ =>
    simp only [Internal.splitColonRaw]
    split
    · simp
    · cases Internal.splitColonRaw rest <;> simp

private theorem splitColonRaw_no_colon (cs : List Char) :
    ∀ seg ∈ Internal.splitColonRaw cs, ':' ∉ seg := by
  induction cs with
  | nil => simp [Internal.splitColonRaw]
  | cons c rest ih =>
    simp only [Internal.splitColonRaw]
    split
    · intro seg hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp
      · exact ih seg hmem
    · next hne =>
      have hcne : c ≠ ':' := fun h => hne (by subst h; exact beq_self_eq_true _)
      cases hsp : Internal.splitColonRaw rest with
      | nil => exact absurd hsp (splitColonRaw_ne_nil rest)
      | cons hd tl =>
        intro seg hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · intro hIn
          simp only [List.mem_cons] at hIn
          rcases hIn with hce | hIn
          · exact hcne hce.symm
          · exact ih hd (by rw [hsp]; simp) hIn
        · exact ih seg (by rw [hsp]; simp [hmem])

private theorem splitColonRaw_of_no_colon (a : List Char) (hno : ':' ∉ a) :
    Internal.splitColonRaw a = [a] := by
  induction a with
  | nil => simp [Internal.splitColonRaw]
  | cons c rest ih =>
    have hcne : c ≠ ':' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitColonRaw, hcne, ih']

private theorem splitColonRaw_append_colon (a b : List Char) (hno : ':' ∉ a) :
    Internal.splitColonRaw (a ++ ':' :: b) = a :: Internal.splitColonRaw b := by
  induction a with
  | nil => simp [Internal.splitColonRaw]
  | cons c rest ih =>
    have hcne : c ≠ ':' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitColonRaw, hcne, ih']

private theorem intercalate_prepend (a b sep : String) (xs : List String) :
    String.intercalate sep ((a ++ b) :: xs) = a ++ String.intercalate sep (b :: xs) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x rest ih =>
    change String.intercalate sep (((a ++ b) ++ sep ++ x) :: rest) =
      a ++ String.intercalate sep ((b ++ sep ++ x) :: rest)
    simp [String.append_assoc]

private theorem intercalate_cons_cons (s r sep : String) (rs : List String) :
    String.intercalate sep (s :: r :: rs) = s ++ sep ++ String.intercalate sep (r :: rs) := by
  change String.intercalate sep ((s ++ sep ++ r) :: rs) = _
  simp [String.append_assoc]

private theorem splitColonRaw_intercalate (segs : List String)
    (hall : segs.all (fun s => !s.isEmpty && !(':' ∈ s.toList)) = true) :
    (Internal.splitColonRaw (String.intercalate ":" segs).toList).filter (fun s => !s.isEmpty) =
      segs.map String.toList := by
  induction segs with
  | nil => simp [String.intercalate, Internal.splitColonRaw]
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    rcases hall with ⟨⟨hs_ne, hs_no⟩, hrest⟩
    have hs_no' : ':' ∉ s.toList := by
      intro hmem
      have hb : decide (':' ∈ s.toList) = true := decide_eq_true hmem
      rw [hs_no] at hb
      cases hb
    have hs_list_ne : !s.toList.isEmpty = true := by
      cases hs : s.toList with
      | nil =>
        have hem : s = "" := by rw [← String.ofList_toList (s := s), hs]
        subst hem
        simp [String.isEmpty] at hs_ne
      | cons _ _ => rfl
    cases rest with
    | nil =>
      change (Internal.splitColonRaw s.toList).filter (fun s => !s.isEmpty) = [s.toList]
      rw [splitColonRaw_of_no_colon s.toList hs_no']
      simp only [List.filter_cons, List.filter_nil]
      cases hs2 : s.toList with
      | nil =>
        exfalso
        have hem : s = "" := by rw [← String.ofList_toList (s := s), hs2]
        subst hem
        simp [String.isEmpty] at hs_ne
      | cons c cs => simp
    | cons r rs =>
      rw [intercalate_cons_cons s r ":" rs]
      have hinter : (s ++ ":" ++ String.intercalate ":" (r :: rs)).toList =
          s.toList ++ ':' :: (String.intercalate ":" (r :: rs)).toList := by
        simp [String.toList_append]
      rw [hinter, splitColonRaw_append_colon _ _ hs_no']
      simp only [List.filter_cons, List.map_cons]
      have hs_empty_false : s.toList.isEmpty = false := by
        cases hs2 : s.toList with
        | nil =>
          exfalso
          have hem : s = "" := by rw [← String.ofList_toList (s := s), hs2]
          subst hem
          simp [String.isEmpty] at hs_ne
        | cons _ _ => rfl
      simp only [hs_empty_false, Bool.not_false, ↓reduceIte]
      exact congrArg (s.toList :: ·) (ih hrest)

/-- Proof of `test_env_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_env_mapRawError_returnsNonEmptyMessage :
    AllPass (test_env_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  simpa [defaultApi, Internal.mkApiM] using
    Env.Raw.Proofs.proof_envraw_mapRawError_returnsNonEmptyMessage raw

/-- Non-vacuity `CanReach` witness for `test_env_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_env_mapRawError_returnsNonEmptyMessage :
    CanReach (test_env_mapRawError_returnsNonEmptyMessage defaultApi) :=
  ⟨.userError "", proof_env_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_env_mapRawError_delegatesToRaw` for `Internal.mkApiM`. -/
theorem proof_env_mapRawError_delegatesToRaw :
    AllPass (test_env_mapRawError_delegatesToRaw (Internal.mkApiM (m := Id))) := by
  intro rawErr mapFn
  simp [Internal.mkApiM, assert]

/-- Non-vacuity `CanReach` witness for `test_env_mapRawError_delegatesToRaw`. -/
theorem reach_env_mapRawError_delegatesToRaw :
    CanReach (test_env_mapRawError_delegatesToRaw (Internal.mkApiM (m := Id))) :=
  ⟨.userError "", fun r => Raw.Internal.mapRawError r,
    proof_env_mapRawError_delegatesToRaw (.userError "") (fun r => Raw.Internal.mapRawError r)⟩

/-- Proof of `test_env_getEnv_rejectsInvalidKey` for `Internal.mkApiM`. -/
theorem proof_env_getEnv_rejectsInvalidKey :
    AllPass (test_env_getEnv_rejectsInvalidKey (Internal.mkApiM (m := Id))) := by
  intro key leak hbad
  have hk : Internal.isValidKey key = false := (isValidKey_false_iff key).mpr hbad
  simp only [Internal.mkApiM, hk, Bool.not_false, ↓reduceIte, pure, assert]
  exact ⟨⟨_, rfl, rfl, rfl, rfl, by simp⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_env_getEnv_rejectsInvalidKey`. -/
theorem reach_env_getEnv_rejectsInvalidKey :
    CanReach (test_env_getEnv_rejectsInvalidKey (Internal.mkApiM (m := Id))) :=
  ⟨"", true, Or.inl rfl, proof_env_getEnv_rejectsInvalidKey "" true (Or.inl rfl)⟩

/-- Proof of `test_env_getEnv_foundInMockList` for `Internal.mkApiM`. -/
theorem proof_env_getEnv_foundInMockList :
    AllPass (test_env_getEnv_foundInMockList (Internal.mkApiM (m := Id))) := by
  intro entries key val hvalid hfind
  have hk : Internal.isValidKey key = true := (isValidKey_true_iff key).mpr hvalid
  simp only [Internal.mkApiM, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, pure, assert]
  change (Except.ok ((entries.find? fun p => p.1 == key).map (·.2)) : Except EnvError (Option String)) =
    Except.ok (some val) ∧ True
  rw [hfind]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_env_getEnv_foundInMockList`. -/
theorem reach_env_getEnv_foundInMockList :
    CanReach (test_env_getEnv_foundInMockList (Internal.mkApiM (m := Id))) :=
  ⟨[("PATH", "/bin")], "PATH", "/bin",
    ⟨by decide, by decide, by decide⟩, rfl,
    proof_env_getEnv_foundInMockList [("PATH", "/bin")] "PATH" "/bin"
      ⟨by decide, by decide, by decide⟩ rfl⟩

/-- Proof of `test_env_getEnv_missingInMockList` for `Internal.mkApiM`. -/
theorem proof_env_getEnv_missingInMockList :
    AllPass (test_env_getEnv_missingInMockList (Internal.mkApiM (m := Id))) := by
  intro entries key hvalid hfind
  have hk : Internal.isValidKey key = true := (isValidKey_true_iff key).mpr hvalid
  simp only [Internal.mkApiM, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, pure, assert]
  change (Except.ok ((entries.find? fun p => p.1 == key).map (·.2)) : Except EnvError (Option String)) =
    Except.ok none ∧ True
  rw [hfind]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_env_getEnv_missingInMockList`. -/
theorem reach_env_getEnv_missingInMockList :
    CanReach (test_env_getEnv_missingInMockList (Internal.mkApiM (m := Id))) :=
  ⟨[], "PATH", ⟨by decide, by decide, by decide⟩, rfl,
    proof_env_getEnv_missingInMockList [] "PATH" ⟨by decide, by decide, by decide⟩ rfl⟩

/-- Proof of `test_env_getEnv_propagatesRawError` for `Internal.mkApiM`. -/
theorem proof_env_getEnv_propagatesRawError :
    AllPass (test_env_getEnv_propagatesRawError (Internal.mkApiM (m := Id))) := by
  intro key rawErr mapFn hvalid
  have hk : Internal.isValidKey key = true := (isValidKey_true_iff key).mpr hvalid
  simp [Internal.mkApiM, hk, bind, pure, assert]

/-- Non-vacuity `CanReach` witness for `test_env_getEnv_propagatesRawError`. -/
theorem reach_env_getEnv_propagatesRawError :
    CanReach (test_env_getEnv_propagatesRawError (Internal.mkApiM (m := Id))) :=
  ⟨"PATH", .userError "boom", Raw.Internal.mapRawError,
    ⟨by decide, by decide, by decide⟩,
    proof_env_getEnv_propagatesRawError "PATH" (.userError "boom") Raw.Internal.mapRawError
      ⟨by decide, by decide, by decide⟩⟩

/-- Proof of `test_env_listEnv_returnsMockEntries` for `Internal.mkApiM`. -/
theorem proof_env_listEnv_returnsMockEntries :
    AllPass (test_env_listEnv_returnsMockEntries (Internal.mkApiM (m := Id))) := by
  intro entries
  simp only [Internal.mkApiM, bind, pure, assert]
  change (Except.ok entries.toArray : Except EnvError (Array (String × String))) =
    Except.ok entries.toArray ∧ True
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_env_listEnv_returnsMockEntries`. -/
theorem reach_env_listEnv_returnsMockEntries :
    CanReach (test_env_listEnv_returnsMockEntries (Internal.mkApiM (m := Id))) :=
  ⟨[("PATH", "/bin")], proof_env_listEnv_returnsMockEntries [("PATH", "/bin")]⟩

/-- Proof of `test_env_listEnv_propagatesRawError` for `Internal.mkApiM`. -/
theorem proof_env_listEnv_propagatesRawError :
    AllPass (test_env_listEnv_propagatesRawError (Internal.mkApiM (m := Id))) := by
  intro rawErr mapFn
  simp [Internal.mkApiM, bind, pure, assert]

/-- Non-vacuity `CanReach` witness for `test_env_listEnv_propagatesRawError`. -/
theorem reach_env_listEnv_propagatesRawError :
    CanReach (test_env_listEnv_propagatesRawError (Internal.mkApiM (m := Id))) :=
  ⟨.userError "boom", Raw.Internal.mapRawError,
    proof_env_listEnv_propagatesRawError (.userError "boom") Raw.Internal.mapRawError⟩

/-- Proof of `test_env_homeDir_returnsNonEmptyHome` for `Internal.mkApiM`. -/
theorem proof_env_homeDir_returnsNonEmptyHome :
    AllPass (test_env_homeDir_returnsNonEmptyHome (Internal.mkApiM (m := Id))) := by
  intro entries home hne hfind
  change (match (Except.ok (Option.map (·.2) (entries.find? fun p => p.1 == "HOME")) :
      Except EnvRawError (Option String)) with
    | Except.error err => Except.error (Raw.Internal.mapRawError err)
    | Except.ok none => Except.error
        { kind := Raw.EnvErrorKind.notFound, key := some "HOME", errnoCode := none,
          message := "HOME environment variable is not set" }
    | Except.ok (some "") => Except.error
        { kind := Raw.EnvErrorKind.notFound, key := some "HOME", errnoCode := none,
          message := "HOME environment variable is empty" }
    | Except.ok (some h) => Except.ok h) = Except.ok home ∧ True
  rw [hfind, Option.map_some]
  refine ⟨?_, trivial⟩
  cases hhome : home.toList with
  | nil =>
    exfalso
    exact hne (by rw [← String.ofList_toList (s := home), hhome])
  | cons c cs => simp

/-- Non-vacuity `CanReach` witness for `test_env_homeDir_returnsNonEmptyHome`. -/
theorem reach_env_homeDir_returnsNonEmptyHome :
    CanReach (test_env_homeDir_returnsNonEmptyHome (Internal.mkApiM (m := Id))) :=
  ⟨[("HOME", "example-home")], "example-home", by decide, rfl,
    proof_env_homeDir_returnsNonEmptyHome [("HOME", "example-home")] "example-home" (by decide) rfl⟩

/-- Proof of `test_env_homeDir_missingOrEmptyFails` for `Internal.mkApiM`. -/
theorem proof_env_homeDir_missingOrEmptyFails :
    AllPass (test_env_homeDir_missingOrEmptyFails (Internal.mkApiM (m := Id))) := by
  intro entries hfind
  change (∃ e : EnvError, (match (Except.ok (Option.map (·.2) (entries.find? fun p => p.1 == "HOME")) :
      Except EnvRawError (Option String)) with
    | Except.error err => Except.error (Raw.Internal.mapRawError err)
    | Except.ok none => Except.error
        { kind := Raw.EnvErrorKind.notFound, key := some "HOME", errnoCode := none,
          message := "HOME environment variable is not set" }
    | Except.ok (some "") => Except.error
        { kind := Raw.EnvErrorKind.notFound, key := some "HOME", errnoCode := none,
          message := "HOME environment variable is empty" }
    | Except.ok (some h) => Except.ok h) = Except.error e ∧
      e.kind = Raw.EnvErrorKind.notFound ∧ e.key = some "HOME" ∧ e.message ≠ "") ∧ True
  rcases hfind with hnone | hempty
  · rw [hnone, Option.map_none]
    exact ⟨⟨_, rfl, rfl, rfl, by decide⟩, trivial⟩
  · rw [hempty, Option.map_some]
    exact ⟨⟨_, rfl, rfl, rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_env_homeDir_missingOrEmptyFails`. -/
theorem reach_env_homeDir_missingOrEmptyFails :
    CanReach (test_env_homeDir_missingOrEmptyFails (Internal.mkApiM (m := Id))) :=
  ⟨[], Or.inl rfl, proof_env_homeDir_missingOrEmptyFails [] (Or.inl rfl)⟩

/-- Proof of `test_env_homeDir_propagatesRawError` for `Internal.mkApiM`. -/
theorem proof_env_homeDir_propagatesRawError :
    AllPass (test_env_homeDir_propagatesRawError (Internal.mkApiM (m := Id))) := by
  intro rawErr mapFn
  simp [Internal.mkApiM, bind, pure, assert]

/-- Non-vacuity `CanReach` witness for `test_env_homeDir_propagatesRawError`. -/
theorem reach_env_homeDir_propagatesRawError :
    CanReach (test_env_homeDir_propagatesRawError (Internal.mkApiM (m := Id))) :=
  ⟨.userError "boom", Raw.Internal.mapRawError,
    proof_env_homeDir_propagatesRawError (.userError "boom") Raw.Internal.mapRawError⟩

/-- Proof of `test_env_splitSearchPath_emptyReturnsEmpty` for `defaultApi`. -/
theorem proof_env_splitSearchPath_emptyReturnsEmpty :
    AllPass (test_env_splitSearchPath_emptyReturnsEmpty defaultApi) := by
  simp [test_env_splitSearchPath_emptyReturnsEmpty, Core.AllPass, defaultApi, Internal.mkApiM,
    Internal.splitSearchPath, Internal.splitColonRaw, assert]

/-- Non-vacuity `CanReach` witness for `test_env_splitSearchPath_emptyReturnsEmpty`. -/
theorem reach_env_splitSearchPath_emptyReturnsEmpty :
    CanReach (test_env_splitSearchPath_emptyReturnsEmpty defaultApi) := by
  simp [test_env_splitSearchPath_emptyReturnsEmpty, Core.CanReach, defaultApi, Internal.mkApiM,
    Internal.splitSearchPath, Internal.splitColonRaw, assert]

/-- Proof of `test_env_splitSearchPath_entriesNonEmptyAndColonFree` for `defaultApi`. -/
theorem proof_env_splitSearchPath_entriesNonEmptyAndColonFree :
    AllPass (test_env_splitSearchPath_entriesNonEmptyAndColonFree defaultApi) := by
  intro path
  simp only [defaultApi, Internal.mkApiM, Internal.splitSearchPath, assert]
  refine ⟨?_, trivial⟩
  change (((Internal.splitColonRaw path.toList).filter fun s => !s.isEmpty).map String.ofList).all
    (fun p => !p.isEmpty && !(':' ∈ p.toList)) = true
  rw [List.all_eq_true]
  intro p hp
  simp only [List.mem_map, List.mem_filter, Bool.not_eq_true'] at hp
  rcases hp with ⟨seg, ⟨hseg_mem, hseg_ne⟩, rfl⟩
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  constructor
  · cases hseg : seg with
    | nil => simp [hseg] at hseg_ne
    | cons c cs =>
      simp only [String.isEmpty]
      have hne : (String.ofList (c :: cs)).utf8ByteSize ≠ 0 := by
        intro h0
        have hlen := String.utf8ByteSize_eq_zero_iff.mp h0
        have hto := congrArg String.toList hlen
        rw [String.toList_ofList] at hto
        cases hto
      cases hsz : (String.ofList (c :: cs)).utf8ByteSize == 0 with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hsz) hne
  · have hno : ':' ∉ seg := splitColonRaw_no_colon path.toList seg hseg_mem
    rw [String.toList_ofList]
    exact decide_eq_false hno

/-- Non-vacuity `CanReach` witness for `test_env_splitSearchPath_entriesNonEmptyAndColonFree`. -/
theorem reach_env_splitSearchPath_entriesNonEmptyAndColonFree :
    CanReach (test_env_splitSearchPath_entriesNonEmptyAndColonFree defaultApi) :=
  ⟨"", proof_env_splitSearchPath_entriesNonEmptyAndColonFree ""⟩

/-- Proof of `test_env_splitSearchPath_dropsEmptySegments` for `defaultApi`. -/
theorem proof_env_splitSearchPath_dropsEmptySegments :
    AllPass (test_env_splitSearchPath_dropsEmptySegments defaultApi) := by
  intro a b ⟨ha_ne, ha_no⟩ ⟨hb_ne, hb_no⟩
  have ha_list : a.toList ≠ [] := by
    intro hl
    exact ha_ne (by rw [← String.ofList_toList (s := a), hl])
  have hb_list : b.toList ≠ [] := by
    intro hl
    exact hb_ne (by rw [← String.ofList_toList (s := b), hl])
  have ha_empty : (!a.toList.isEmpty) = true := by
    cases h : a.toList with
    | nil => exact absurd h ha_list
    | cons _ _ => rfl
  have hb_empty : (!b.toList.isEmpty) = true := by
    cases h : b.toList with
    | nil => exact absurd h hb_list
    | cons _ _ => rfl
  simp only [defaultApi, Internal.mkApiM, Internal.splitSearchPath, assert]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · have hcs : (":" ++ a ++ "::" ++ b ++ ":").toList =
        ':' :: (a.toList ++ ':' :: (':' :: (b.toList ++ [':']))) := by
      simp [String.toList_append]
    rw [hcs, Internal.splitColonRaw]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [splitColonRaw_append_colon _ _ ha_no]
    simp only [Internal.splitColonRaw, beq_self_eq_true, ↓reduceIte]
    rw [splitColonRaw_append_colon _ _ hb_no]
    simp [Internal.splitColonRaw, ha_empty, hb_empty, String.ofList_toList]
  · decide

/-- Non-vacuity `CanReach` witness for `test_env_splitSearchPath_dropsEmptySegments`. -/
theorem reach_env_splitSearchPath_dropsEmptySegments :
    CanReach (test_env_splitSearchPath_dropsEmptySegments defaultApi) :=
  ⟨"/a", "/b", ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    proof_env_splitSearchPath_dropsEmptySegments "/a" "/b"
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩⟩

/-- Proof of `test_env_splitSearchPath_roundTripsCleanSegments` for `defaultApi`. -/
theorem proof_env_splitSearchPath_roundTripsCleanSegments :
    AllPass (test_env_splitSearchPath_roundTripsCleanSegments defaultApi) := by
  intro segs hall
  simp only [defaultApi, Internal.mkApiM, Internal.splitSearchPath, assert]
  refine ⟨?_, trivial⟩
  rw [splitColonRaw_intercalate segs hall, List.map_map]
  have hcomp : (String.ofList ∘ String.toList) = id := by
    funext s
    exact String.ofList_toList
  simp [hcomp]

/-- Non-vacuity `CanReach` witness for `test_env_splitSearchPath_roundTripsCleanSegments`. -/
theorem reach_env_splitSearchPath_roundTripsCleanSegments :
    CanReach (test_env_splitSearchPath_roundTripsCleanSegments defaultApi) :=
  ⟨["/a", "/b"], by decide,
    proof_env_splitSearchPath_roundTripsCleanSegments ["/a", "/b"] (by decide)⟩

end LeanSwe.Env.Proofs

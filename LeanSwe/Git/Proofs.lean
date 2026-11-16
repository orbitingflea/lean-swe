import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private instance : LawfulBEq CommitId where
  eq_of_beq {a b} h := by
    cases a with | mk ha =>
    cases b with | mk hb =>
    have h' : (ha == hb) = true := h
    exact congrArg CommitId.mk (beq_iff_eq.mp h')
  rfl {a} := by
    cases a with | mk ha =>
    change (ha == ha) = true
    exact beq_self_eq_true ha

private instance : LawfulBEq RefName where
  eq_of_beq {a b} h := by
    cases a with | mk ra =>
    cases b with | mk rb =>
    have h' : (ra == rb) = true := h
    exact congrArg RefName.mk (beq_iff_eq.mp h')
  rfl {a} := by
    cases a with | mk ra =>
    change (ra == ra) = true
    exact beq_self_eq_true ra

private theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

private theorem toUTF8_eq_empty_iff (s : String) : s.toUTF8.isEmpty = true ↔ s = "" := by
  change (s.toByteArray.size == 0) = true ↔ s = ""
  rw [beq_iff_eq]
  exact String.utf8ByteSize_eq_zero_iff

private theorem hasNulChar_eq_false_iff {cs : List Char} :
    hasNulChar cs = false ↔ ∀ c ∈ cs, c ≠ Char.ofNat 0 := by
  induction cs with
  | nil => simp [hasNulChar]
  | cons c cs ih =>
    simp [hasNulChar, ih]

private theorem string_ofList_append (xs ys : List Char) :
    String.ofList (xs ++ ys) = String.ofList xs ++ String.ofList ys :=
  String.toList_injective (by simp)

private theorem decodeUtf8Lossy_toUTF8 (s : String) :
    Impl.decodeUtf8Lossy s.toUTF8 = s := by
  unfold Impl.decodeUtf8Lossy
  rw [fromUTF8_toUTF8]
  rfl

private theorem decodeUtf8Checked_toUTF8 (s : String) :
    Impl.decodeUtf8Checked s.toUTF8 = .ok s := by
  unfold Impl.decodeUtf8Checked
  rw [fromUTF8_toUTF8]

private theorem all_no_nul_of_list (xs : List String)
    (h : xs.all (fun a => !hasNulChar a.toList) = true) :
    (xs.toArray.all fun a => !hasNulChar a.toList) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hmem : xs.toArray[i] ∈ xs := by simp
  exact List.all_eq_true.mp h _ hmem

private theorem splitNulRecordsAux_eof (acc cs : List Char)
    (hno : hasNulChar cs = false) (hne : ¬ (acc = [] ∧ cs = [])) :
    splitNulRecordsAux acc cs = none := by
  induction cs generalizing acc with
  | nil =>
    have hacc : acc ≠ [] := fun h => hne ⟨h, rfl⟩
    simp [splitNulRecordsAux, hacc]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx =>
        hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hne' : ¬ (c :: acc = [] ∧ cs = []) := fun ⟨h, _⟩ => by cases h
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulRecordsAux, hbeq, ih (c :: acc) hcs hne']

private theorem toUTF8_nonempty_of_ne {s : String} (hne : s ≠ "") : s.toUTF8.isEmpty = false :=
  Bool.eq_false_iff.mpr fun hc => hne ((toUTF8_eq_empty_iff s).mp hc)

private theorem splitNulRecordsAux_append_nul (acc cs rest : List Char)
    (hno : hasNulChar cs = false) (hne : ¬ (acc = [] ∧ cs = [])) :
    splitNulRecordsAux acc (cs ++ Char.ofNat 0 :: rest) =
      (splitNulRecordsAux [] rest).map (String.ofList (acc.reverse ++ cs) :: ·) := by
  induction cs generalizing acc with
  | nil =>
    have hacc : acc ≠ [] := fun h => hne ⟨h, rfl⟩
    have hem : acc.isEmpty = false := by
      cases acc with
      | nil => contradiction
      | cons _ _ => rfl
    simp [splitNulRecordsAux, hem]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx =>
        hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hne' : ¬ (c :: acc = [] ∧ cs = []) := fun ⟨h, _⟩ => by cases h
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulRecordsAux, hbeq, ih (c :: acc) hcs hne', List.reverse_cons, List.append_assoc]

/-- Proof of `test_git_cleanGitEnv_stripsInheritedGitKeys` for `cleanGitEnv`. -/
theorem proof_git_cleanGitEnv_stripsInheritedGitKeys :
    AllPass (test_git_cleanGitEnv_stripsInheritedGitKeys (fun inh ext => cleanGitEnv inh ext)) := by
  intro inherited extra
  simp only [cleanGitEnv, assert]
  refine ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩
  · simp only [List.all_eq_true]
    intro kv hkv
    by_cases hgit : isGitKey kv.1 = true
    · simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem, List.mem_append,
        List.mem_map, List.mem_filter]
      exact Or.inr (Or.inl (Or.inl ⟨kv, ⟨hkv, hgit⟩, rfl⟩))
    · simp [hgit]
  · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
    intro kv hkv
    exact Or.inl (Or.inr hkv)
  · simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem]
    intro kv hkv
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hkv
    rcases hkv with (⟨p, _, rfl⟩ | hdef) | ⟨_, hvalid⟩
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr hdef)
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨_, _⟩, hgit | hallow⟩
      · exact Or.inl (Or.inl (Or.inl hgit))
      · exact Or.inr hallow

/-- Proof of `test_git_cleanGitEnv_preservesValidNonGitExtra` for `cleanGitEnv`. -/
theorem proof_git_cleanGitEnv_preservesValidNonGitExtra :
    AllPass (test_git_cleanGitEnv_preservesValidNonGitExtra (fun inh ext => cleanGitEnv inh ext)) := by
  intro _inherited key val hKey hVal hNotGit
  simp only [cleanGitEnv, assert, List.contains_iff_mem,
    List.mem_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨Or.inr ⟨trivial, by simp [hKey, hVal, hNotGit]⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_cleanGitEnv_preservesValidNonGitExtra`. -/
theorem reach_git_cleanGitEnv_preservesValidNonGitExtra :
    CanReach (test_git_cleanGitEnv_preservesValidNonGitExtra (fun inh ext => cleanGitEnv inh ext)) :=
  ⟨#[], "FOO", some "bar", rfl, rfl, rfl,
    proof_git_cleanGitEnv_preservesValidNonGitExtra #[] "FOO" (some "bar") rfl rfl rfl⟩

/-- Proof of `test_git_mkCommitId_validatesHexLengthAndChars` for `mkCommitId`. -/
theorem proof_git_mkCommitId_validatesHexLengthAndChars :
    AllPass (test_git_mkCommitId_validatesHexLengthAndChars mkCommitId) := by
  intro s
  dsimp [test_git_mkCommitId_validatesHexLengthAndChars, AllPass, bind, assert, mkCommitId]
  split
  · next h => exact ⟨⟨rfl, h⟩, trivial⟩
  · next h =>
    have hf : isValidCommitIdStr s = false := Bool.eq_false_iff.mpr h
    exact ⟨⟨rfl, by simp [toString], hf⟩, trivial⟩

/-- Proof of `test_git_mkRefName_rejectsUnsafeRefs` for `mkRefName`. -/
theorem proof_git_mkRefName_rejectsUnsafeRefs :
    AllPass (test_git_mkRefName_rejectsUnsafeRefs mkRefName) := by
  intro s hbad
  have hFalse : isValidRefNameStr s = false := by
    unfold isValidRefNameStr
    rcases hbad with rfl | hhead | rfl | hdots
    · rfl
    · simp [hhead]
    · rfl
    · simp [hdots]
  simp only [mkRefName, hFalse, Bool.false_eq_true, ↓reduceIte, assert, toString]
  simp

/-- Non-vacuity `CanReach` witness for `test_git_mkRefName_rejectsUnsafeRefs`. -/
theorem reach_git_mkRefName_rejectsUnsafeRefs :
    CanReach (test_git_mkRefName_rejectsUnsafeRefs mkRefName) := by
  exact ⟨"-rf", Or.inr (Or.inl rfl), ⟨rfl, by decide⟩, trivial⟩

/-- Proof of `test_git_parsePorcelainStatusZ_framingAndEmpty` for `parsePorcelainStatusZ`. -/
theorem proof_git_parsePorcelainStatusZ_framingAndEmpty :
    AllPass (test_git_parsePorcelainStatusZ_framingAndEmpty parsePorcelainStatusZ) := by
  dsimp only [test_git_parsePorcelainStatusZ_framingAndEmpty, AllPass, assert]
  have hEmpty : parsePorcelainStatusZ ByteArray.empty = .ok #[] := rfl
  have hBad : parsePorcelainStatusZ (" M a.txt" : String).toUTF8 =
      .error { kind := .parseError, message := "unterminated or empty record in git status -z output" } := by
    unfold parsePorcelainStatusZ
    rw [toUTF8_nonempty_of_ne (by decide), fromUTF8_toUTF8]
    dsimp only
    have hSplit : splitNulRecords " M a.txt" = none :=
      splitNulRecordsAux_eof [] " M a.txt".toList (by decide) (by intro ⟨_, hc⟩; cases hc)
    rw [hSplit]
    rfl
  exact ⟨hEmpty, ⟨{ kind := .parseError, message := "unterminated or empty record in git status -z output" },
    hBad, rfl, fun h => by have hl := congrArg String.length h; contradiction⟩, trivial⟩

private theorem prefix_rename_status_no_nul (dst : String) (hdst : hasNulChar dst.toList = false) :
    hasNulChar ('R' :: ' ' :: ' ' :: dst.toList) = false := by
  simp [hasNulChar, hdst]

private theorem parsePorcelainStatusZ_renameDestFirst_eq (src dst : String)
    (hsrc : src ≠ "" ∧ (!hasNulChar src.toList) = true)
    (hdst : dst ≠ "" ∧ (!hasNulChar dst.toList) = true) :
    parsePorcelainStatusZ ("R  " ++ dst ++ "\x00" ++ src ++ "\x00").toUTF8 =
      .ok #[{ indexStatus := some .renamed, worktreeStatus := none, path := dst, origPath := some src }] := by
  rcases hsrc with ⟨hsrcNe, hsrcNul⟩
  rcases hdst with ⟨hdstNe, hdstNul⟩
  have hsrcNul' : hasNulChar src.toList = false := by simpa using hsrcNul
  have hdstNul' : hasNulChar dst.toList = false := by simpa using hdstNul
  let s := "R  " ++ dst ++ "\x00" ++ src ++ "\x00"
  have hsNe : s ≠ "" := by
    intro h
    simp [s, String.append_eq_empty_iff] at h
  have hEmptyFalse : s.toUTF8.isEmpty = false :=
    Bool.eq_false_iff.mpr fun hc => hsNe ((toUTF8_eq_empty_iff s).mp hc)
  have hsList : s.toList = ('R' :: ' ' :: ' ' :: dst.toList) ++ Char.ofNat 0 :: (src.toList ++ [Char.ofNat 0]) := by
    simp [s, String.toList_append, List.append_assoc]
  have hSplit1 := splitNulRecordsAux_append_nul [] ('R' :: ' ' :: ' ' :: dst.toList)
    (src.toList ++ [Char.ofNat 0]) (prefix_rename_status_no_nul dst hdstNul') (by intro ⟨_, hc⟩; cases hc)
  have hSplit2 := splitNulRecordsAux_append_nul [] src.toList [] hsrcNul'
    (by intro ⟨_, hc⟩; apply hsrcNe; exact String.toList_injective hc)
  have hRPrefix : String.ofList ('R' :: ' ' :: ' ' :: dst.toList) = "R  " ++ dst := by
    have h1 : ('R' :: ' ' :: ' ' :: dst.toList) = ['R', ' ', ' '] ++ dst.toList := rfl
    rw [h1, string_ofList_append]
    simp [String.ofList_toList]
  have hSplit : splitNulRecords s = some ["R  " ++ dst, src] := by
    unfold splitNulRecords
    rw [hsList, hSplit1, hSplit2]
    simp [splitNulRecordsAux, hRPrefix, String.ofList_toList]
  have hDstChars : dst.toList ≠ [] := fun hc => hdstNe (String.toList_injective hc)
  have hDstEmpty : dst.toList.isEmpty = false := by
    cases h : dst.toList with
    | nil => exact absurd h hDstChars
    | cons _ _ => rfl
  have hRecList : ("R  " ++ dst).toList = 'R' :: ' ' :: ' ' :: dst.toList := by
    simp [String.toList_append]
  unfold parsePorcelainStatusZ
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  rw [hSplit]
  simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  have hRecs : parsePorcelainStatusRecords ["R  " ++ dst, src] =
      .ok [{ indexStatus := some .renamed, worktreeStatus := none, path := dst, origPath := some src }] := by
    unfold parsePorcelainStatusRecords
    rw [hRecList]
    split
    · next x y pathChars heq =>
      cases heq
      have hPair : isValidStatusPair 'R' ' ' = true := by decide
      have hEnd : parsePorcelainStatusRecords [] = .ok [] := rfl
      simp [hDstEmpty, hPair, statusCharToKind?, hEnd, Except.map, String.ofList_toList]
    · next h => exact absurd rfl (h 'R' ' ' dst.toList)
  rw [hRecs]

/-- Proof of `test_git_parsePorcelainStatusZ_renameDestFirst` for `parsePorcelainStatusZ`. -/
theorem proof_git_parsePorcelainStatusZ_renameDestFirst :
    AllPass (test_git_parsePorcelainStatusZ_renameDestFirst parsePorcelainStatusZ) := by
  intro src dst hsrc hdst
  dsimp only [assert]
  rw [parsePorcelainStatusZ_renameDestFirst_eq src dst hsrc hdst]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_parsePorcelainStatusZ_renameDestFirst`. -/
theorem reach_git_parsePorcelainStatusZ_renameDestFirst :
    CanReach (test_git_parsePorcelainStatusZ_renameDestFirst parsePorcelainStatusZ) := by
  refine ⟨"src.txt", "dest.txt", ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  dsimp only [assert]
  rw [parsePorcelainStatusZ_renameDestFirst_eq "src.txt" "dest.txt" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  exact ⟨rfl, trivial⟩

private theorem parseDiffNameStatusZ_renameSourceFirst_eq (src dst : String)
    (hsrc : src ≠ "" ∧ (!hasNulChar src.toList) = true)
    (hdst : dst ≠ "" ∧ (!hasNulChar dst.toList) = true) :
    parseDiffNameStatusZ ("R095\x00" ++ src ++ "\x00" ++ dst ++ "\x00").toUTF8 =
      .ok #[{ kind := .renamed 95, path := dst, origPath := some src }] := by
  rcases hsrc with ⟨hsrcNe, hsrcNul⟩
  rcases hdst with ⟨hdstNe, hdstNul⟩
  have hsrcNul' : hasNulChar src.toList = false := by simpa using hsrcNul
  have hdstNul' : hasNulChar dst.toList = false := by simpa using hdstNul
  let s := "R095\x00" ++ src ++ "\x00" ++ dst ++ "\x00"
  have hsNe : s ≠ "" := by
    intro h
    simp [s, String.append_eq_empty_iff] at h
  have hEmptyFalse : s.toUTF8.isEmpty = false :=
    Bool.eq_false_iff.mpr fun hc => hsNe ((toUTF8_eq_empty_iff s).mp hc)
  have hsList : s.toList = ['R', '0', '9', '5'] ++ Char.ofNat 0 :: (src.toList ++ Char.ofNat 0 :: (dst.toList ++ [Char.ofNat 0])) := by
    simp [s, String.toList_append, List.append_assoc]
  have hSplit1 := splitNulRecordsAux_append_nul [] ['R', '0', '9', '5']
    (src.toList ++ Char.ofNat 0 :: (dst.toList ++ [Char.ofNat 0])) (by decide) (by intro ⟨_, hc⟩; cases hc)
  have hSplit2 := splitNulRecordsAux_append_nul [] src.toList
    (dst.toList ++ [Char.ofNat 0]) hsrcNul' (by intro ⟨_, hc⟩; apply hsrcNe; exact String.toList_injective hc)
  have hSplit3 := splitNulRecordsAux_append_nul [] dst.toList [] hdstNul'
    (by intro ⟨_, hc⟩; apply hdstNe; exact String.toList_injective hc)
  have hSplit : splitNulRecords s = some ["R095", src, dst] := by
    unfold splitNulRecords
    rw [hsList, hSplit1, hSplit2, hSplit3]
    simp [splitNulRecordsAux, String.ofList_toList]
  unfold parseDiffNameStatusZ
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  rw [hSplit]
  simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  have hDiffs : parseDiffTokens ["R095", src, dst] =
      .ok [{ kind := .renamed 95, path := dst, origPath := some src }] := by
    unfold parseDiffTokens
    rw [show ("R095" : String).toList = ['R', '0', '9', '5'] from by decide]
    split
    all_goals
      first
      | (next _ heq => cases heq)
      | (next scoreChars heq =>
          cases heq
          have hScore : parseSimilarityScore ['0', '9', '5'] = some 95 := by decide
          have hEnd : parseDiffTokens [] = .ok [] := rfl
          simp [hScore, hEnd, Except.map])
      | (next _ _ _ _ _ hR _ => exact absurd rfl (hR ['0', '9', '5']))
  rw [hDiffs]

/-- Proof of `test_git_parseDiffNameStatusZ_renameSourceFirst` for `parseDiffNameStatusZ`. -/
theorem proof_git_parseDiffNameStatusZ_renameSourceFirst :
    AllPass (test_git_parseDiffNameStatusZ_renameSourceFirst parseDiffNameStatusZ) := by
  intro src dst hsrc hdst
  dsimp only [assert]
  rw [parseDiffNameStatusZ_renameSourceFirst_eq src dst hsrc hdst]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_parseDiffNameStatusZ_renameSourceFirst`. -/
theorem reach_git_parseDiffNameStatusZ_renameSourceFirst :
    CanReach (test_git_parseDiffNameStatusZ_renameSourceFirst parseDiffNameStatusZ) := by
  refine ⟨"src.txt", "dest.txt", ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  dsimp only [assert]
  rw [parseDiffNameStatusZ_renameSourceFirst_eq "src.txt" "dest.txt" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  exact ⟨rfl, trivial⟩

private theorem splitNulTokensAllowEmptyAux_append_nul (acc cs rest : List Char)
    (hno : hasNulChar cs = false) :
    splitNulTokensAllowEmptyAux acc (cs ++ Char.ofNat 0 :: rest) =
      (splitNulTokensAllowEmptyAux [] rest).map (String.ofList (acc.reverse ++ cs) :: ·) := by
  induction cs generalizing acc with
  | nil => simp [splitNulTokensAllowEmptyAux]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx => hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulTokensAllowEmptyAux, hbeq, ih (c :: acc) hcs, List.reverse_cons, List.append_assoc]

private theorem splitWorktreeStanzas_empty (cur rest : List String) (hne : cur.isEmpty = false) :
    splitWorktreeStanzas cur ("" :: rest) = (splitWorktreeStanzas [] rest).map (cur.reverse :: ·) := by
  conv => lhs; unfold splitWorktreeStanzas
  simp [hne]

private theorem splitWorktreeStanzas_tok (cur : List String) (tok : String) (rest : List String)
    (hne : tok ≠ "") :
    splitWorktreeStanzas cur (tok :: rest) = splitWorktreeStanzas (tok :: cur) rest := by
  conv => lhs; unfold splitWorktreeStanzas
  split <;> rename_i heq <;> cases heq
  · exact absurd rfl hne
  · rfl

private theorem parseWorktreeAttrs_bare (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("bare" :: rest) =
      parseWorktreeAttrs { info with isBare := true } hs rest := rfl

private theorem parseWorktreeAttrs_detached (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("detached" :: rest) =
      parseWorktreeAttrs { info with isDetached := true } hs rest := rfl

private theorem parseWorktreeAttrs_locked (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("locked" :: rest) =
      parseWorktreeAttrs { info with isLocked := true, lockReason := none } hs rest := rfl

private theorem list_all_replicate_true {α : Type} (n : Nat) (x : α) (p : α → Bool)
    (hp : p x = true) : (List.replicate n x).all p = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, hp, ih]

private theorem hasNulChar_head_rep40 (n : Nat) (ch : Char) (hch : ch ≠ Char.ofNat 0) :
    hasNulChar ("HEAD " ++ String.ofList (List.replicate n ch)).toList = false := by
  rw [hasNulChar_eq_false_iff, String.toList_append, String.toList_ofList]
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · have hno : hasNulChar "HEAD ".toList = false := by decide
    exact hasNulChar_eq_false_iff.mp hno c hc
  · rw [String.toList_ofList] at hc
    rcases List.mem_replicate.mp hc with ⟨_, rfl⟩
    exact hch

private theorem isAllZeros_rep40_zero :
    isAllZerosCommitStr (String.ofList (List.replicate 40 '0')) = true := by
  unfold isAllZerosCommitStr
  rw [String.toList_ofList]
  dsimp only
  rw [List.length_replicate, list_all_replicate_true _ _ _ (by decide)]
  rfl

private theorem isAllZeros_rep40_a :
    isAllZerosCommitStr (String.ofList (List.replicate 40 'a')) = false := by
  unfold isAllZerosCommitStr
  rw [String.toList_ofList]
  simp [List.replicate_succ]

private theorem isValidCommitIdStr_rep40_a :
    isValidCommitIdStr (String.ofList (List.replicate 40 'a')) = true := by
  unfold isValidCommitIdStr
  rw [String.toList_ofList]
  dsimp only
  rw [List.length_replicate, list_all_replicate_true _ _ _ (by decide)]
  rfl

private theorem stripPrefixChars_append (p cs : List Char) :
    stripPrefixChars p (p ++ cs) = some cs := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [stripPrefixChars, ih]

private theorem head_str_ne_empty (sha : String) : ("HEAD " ++ sha) ≠ "" := by
  intro heq
  have ht := congrArg (fun s : String => s.toList.head?) heq
  rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl] at ht
  cases ht

private theorem head_str_ne_tag (sha tag : String) (h : tag.toList.head? ≠ some 'H') :
    ("HEAD " ++ sha == tag) = false := by
  apply beq_false_of_ne
  intro heq
  have ht := congrArg (fun s : String => s.toList.head?) heq
  rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl] at ht
  exact h ht.symm

private theorem parseWorktreeAttrs_head_zeros (info : WorktreeInfo) (hs : Bool)
    (sha : String) (rest : List String) (hz : isAllZerosCommitStr sha = true) :
    parseWorktreeAttrs info hs (("HEAD " ++ sha) :: rest) =
      parseWorktreeAttrs { info with head? := none } true rest := by
  have hB := head_str_ne_tag sha "bare" (by decide)
  have hD := head_str_ne_tag sha "detached" (by decide)
  have hL := head_str_ne_tag sha "locked" (by decide)
  have hP := head_str_ne_tag sha "prunable" (by decide)
  have hPref : stripPrefixChars ['H', 'E', 'A', 'D', ' '] ("HEAD " ++ sha).toList = some sha.toList := by
    rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl]
    exact stripPrefixChars_append ['H', 'E', 'A', 'D', ' '] sha.toList
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hPref, String.ofList_toList, hz]

private theorem parseWorktreeAttrs_head_commit (info : WorktreeInfo) (hs : Bool)
    (sha : String) (cid : CommitId) (rest : List String)
    (hz : isAllZerosCommitStr sha = false) (hCid : mkCommitId sha = .ok cid) :
    parseWorktreeAttrs info hs (("HEAD " ++ sha) :: rest) =
      parseWorktreeAttrs { info with head? := some cid } true rest := by
  have hB := head_str_ne_tag sha "bare" (by decide)
  have hD := head_str_ne_tag sha "detached" (by decide)
  have hL := head_str_ne_tag sha "locked" (by decide)
  have hP := head_str_ne_tag sha "prunable" (by decide)
  have hPref : stripPrefixChars ['H', 'E', 'A', 'D', ' '] ("HEAD " ++ sha).toList = some sha.toList := by
    rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl]
    exact stripPrefixChars_append ['H', 'E', 'A', 'D', ' '] sha.toList
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hPref, String.ofList_toList, hz, hCid]

private theorem parseWorktreeAttrs_branch (info : WorktreeInfo) (hs : Bool)
    (line refStr shortStr : String) (ref : RefName) (rest : List String)
    (hB : (line == "bare") = false) (hD : (line == "detached") = false)
    (hL : (line == "locked") = false) (hP : (line == "prunable") = false)
    (hNoH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList = none)
    (hBr : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList = some refStr.toList)
    (hRh : stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refStr.toList =
      some shortStr.toList)
    (hRef : mkRefName shortStr = .ok ref) :
    parseWorktreeAttrs info hs (line :: rest) =
      parseWorktreeAttrs { info with branch? := some ref } hs rest := by
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hNoH, hBr, hRh, String.ofList_toList, hRef]

private theorem parseWorktreeAttrs_prunable_reason (info : WorktreeInfo) (hs : Bool)
    (line reason : String) (rest : List String)
    (hB : (line == "bare") = false) (hD : (line == "detached") = false)
    (hL : (line == "locked") = false) (hP : (line == "prunable") = false)
    (hNoH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList = none)
    (hNoBr : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList = none)
    (hNoLk : stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] line.toList = none)
    (hPr : stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] line.toList = some reason.toList) :
    parseWorktreeAttrs info hs (line :: rest) =
      parseWorktreeAttrs { info with isPrunable := true, pruneReason := some reason } hs rest := by
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hNoH, hNoBr, hNoLk, hPr, String.ofList_toList]

private theorem parseWorktreeStanza_worktree (header path : String) (attrs : List String)
    (hHdr : stripPrefixChars ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList = some path.toList)
    (hNe : path.toList.isEmpty = false) :
    parseWorktreeStanza (header :: attrs) =
      Except.bind (parseWorktreeAttrs { path := path, head? := none, branch? := none } false attrs)
        (fun p =>
          if !p.1.isBare && !p.2 then
            .error { kind := .parseError, message := s!"non-bare worktree '{p.1.path}' missing HEAD attribute" }
          else
            .ok p.1) := by
  unfold parseWorktreeStanza
  simp only [hHdr, hNe, Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
  rfl

private theorem parseWorktreeListPorcelain_ok_of (s : String) (toks : List String)
    (stanzas : List (List String)) (infos : List WorktreeInfo)
    (hNe : s.toUTF8.isEmpty = false)
    (hToks : splitNulTokensAllowEmptyAux [] s.toList = some toks)
    (hStz : splitWorktreeStanzas [] toks = some stanzas)
    (hInfos : parseWorktreeStanzas stanzas = .ok infos) :
    parseWorktreeListPorcelain s.toUTF8 = .ok infos.toArray := by
  unfold parseWorktreeListPorcelain
  rw [hNe, fromUTF8_toUTF8]
  dsimp only
  rw [hToks]
  dsimp only
  rw [hStz]
  dsimp only
  rw [hInfos]
  rfl

private theorem splitNulTokensAllowEmptyAux_step (a : String) (rest : List Char)
    (toks : List String)
    (hno : hasNulChar a.toList = false)
    (hrest : splitNulTokensAllowEmptyAux [] rest = some toks) :
    splitNulTokensAllowEmptyAux [] (a.toList ++ Char.ofNat 0 :: rest) = some (a :: toks) := by
  rw [splitNulTokensAllowEmptyAux_append_nul [] a.toList rest hno, hrest]
  simp [String.ofList_toList]

private theorem splitNulRecordsAux_step (a : String) (rest : List Char) (recs : List String)
    (hne : a ≠ "") (hno : hasNulChar a.toList = false)
    (hrest : splitNulRecordsAux [] rest = some recs) :
    splitNulRecordsAux [] (a.toList ++ Char.ofNat 0 :: rest) = some (a :: recs) := by
  have hacs : ¬ (([] : List Char) = [] ∧ a.toList = []) := fun h => hne (String.toList_injective h.2)
  rw [splitNulRecordsAux_append_nul [] a.toList rest hno hacs, hrest]
  simp [String.ofList_toList]

private theorem parsePorcelainStatusZ_ok_of (s : String) (toks : List String)
    (recs : List StatusEntry)
    (hNe : s.toUTF8.isEmpty = false)
    (hToks : splitNulRecordsAux [] s.toList = some toks)
    (hRecs : parsePorcelainStatusRecords toks = .ok recs) :
    parsePorcelainStatusZ s.toUTF8 = .ok recs.toArray := by
  unfold parsePorcelainStatusZ
  rw [hNe, fromUTF8_toUTF8]
  dsimp only
  have hSplit : splitNulRecords s = some toks := hToks
  rw [hSplit]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hRecs]
  rfl

private theorem parsePorcelainStatusRecords_plain (tok path : String) (x y : Char)
    (rest : List String) (kx ky : Option StatusKind)
    (hTok : tok.toList = x :: y :: ' ' :: path.toList)
    (hNe : path.toList.isEmpty = false) (hPair : isValidStatusPair x y = true)
    (hx : statusCharToKind? x = some kx) (hy : statusCharToKind? y = some ky)
    (hxNot : x ≠ 'R' ∧ x ≠ 'C') (hyNot : y ≠ 'R' ∧ y ≠ 'C') :
    parsePorcelainStatusRecords (tok :: rest) =
      (parsePorcelainStatusRecords rest).map
        ({ indexStatus := kx, worktreeStatus := ky, path := path } :: ·) := by
  conv => lhs; unfold parsePorcelainStatusRecords
  rw [hTok]
  split
  · next x' y' pathChars heq =>
    cases heq
    simp [hNe, hPair, hx, hy, hxNot.1, hxNot.2, hyNot.1, hyNot.2, String.ofList_toList]
  · next h => exact absurd rfl (h x y path.toList)

private theorem parsePorcelainStatusRecords_rc (tok path orig : String) (x y : Char)
    (rest : List String) (kx ky : Option StatusKind)
    (hTok : tok.toList = x :: y :: ' ' :: path.toList)
    (hNe : path.toList.isEmpty = false) (hPair : isValidStatusPair x y = true)
    (hx : statusCharToKind? x = some kx) (hy : statusCharToKind? y = some ky)
    (hRc : (x == 'R' || x == 'C') = true) :
    parsePorcelainStatusRecords (tok :: orig :: rest) =
      (parsePorcelainStatusRecords rest).map
        ({ indexStatus := kx, worktreeStatus := ky, path := path, origPath := some orig } :: ·) := by
  conv => lhs; unfold parsePorcelainStatusRecords
  rw [hTok]
  split
  · next x' y' pathChars heq =>
    cases heq
    simp [hNe, hPair, hx, hy, hRc, String.ofList_toList]
  · next h => exact absurd rfl (h x y path.toList)

/-- Proof of `test_git_parseWorktreeListPorcelain_bareUnbornLocked` for `parseWorktreeListPorcelain`. -/
theorem proof_git_parseWorktreeListPorcelain_bareUnbornLocked :
    AllPass (test_git_parseWorktreeListPorcelain_bareUnbornLocked parseWorktreeListPorcelain) := by
  have hBare : parseWorktreeListPorcelain "worktree /tmp/bare.git\x00bare\x00\x00".toUTF8 =
      .ok #[{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }] := by
    let sb := "worktree /tmp/bare.git\x00bare\x00\x00"
    have hbList : sb.toList =
        "worktree /tmp/bare.git".toList ++ Char.ofNat 0 ::
        ("bare".toList ++ Char.ofNat 0 ::
        ("".toList ++ Char.ofNat 0 :: [])) := by decide
    have hToksB : splitNulTokensAllowEmptyAux [] sb.toList =
        some ["worktree /tmp/bare.git", "bare", ""] := by
      rw [hbList]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      have hNil : splitNulTokensAllowEmptyAux [] [] = some [] := rfl
      rw [hNil]
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.map]
    have hStzB : splitWorktreeStanzas [] ["worktree /tmp/bare.git", "bare", ""] =
        some [["worktree /tmp/bare.git", "bare"]] := by
      rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (by decide)]
      rw [splitWorktreeStanzas_empty _ _ (by decide)]
      rfl
    have hPBare : parseWorktreeStanza ["worktree /tmp/bare.git", "bare"] =
        .ok { path := "/tmp/bare.git", head? := none, branch? := none, isBare := true } := by
      rw [parseWorktreeStanza_worktree "worktree /tmp/bare.git" "/tmp/bare.git" ["bare"] (by decide) (by decide)]
      rw [parseWorktreeAttrs_bare]
      rfl
    have hInfosB : parseWorktreeStanzas [["worktree /tmp/bare.git", "bare"]] =
        .ok [{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }] := by
      unfold parseWorktreeStanzas
      rw [hPBare]
      rfl
    exact parseWorktreeListPorcelain_ok_of "worktree /tmp/bare.git\x00bare\x00\x00"
      ["worktree /tmp/bare.git", "bare", ""]
      [["worktree /tmp/bare.git", "bare"]]
      [{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }]
      (toUTF8_nonempty_of_ne (by decide)) hToksB hStzB hInfosB
  refine ⟨hBare, ⟨?_, trivial⟩⟩
  let z40 := String.ofList (List.replicate 40 '0')
  let s := "worktree /tmp/wt\x00HEAD " ++ z40 ++ "\x00branch refs/heads/main\x00locked\x00prunable gone\x00\x00"
  have hEmptyFalse : s.toUTF8.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (toUTF8_eq_empty_iff s).mp h
    have hl := congrArg String.length he
    simp [s] at hl
  have hHead : hasNulChar ("HEAD " ++ z40).toList = false :=
    hasNulChar_head_rep40 40 '0' (by decide)
  have h1 : "worktree /tmp/wt\x00HEAD ".toList =
      "worktree /tmp/wt".toList ++ Char.ofNat 0 :: "HEAD ".toList := by decide
  have h2 : "\x00branch refs/heads/main\x00locked\x00prunable gone\x00\x00".toList =
      Char.ofNat 0 :: ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("locked".toList ++ Char.ofNat 0 :: ("prunable gone".toList ++ Char.ofNat 0 :: ("".toList ++ Char.ofNat 0 :: [])))) := by decide
  have hsList : s.toList =
      "worktree /tmp/wt".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ z40).toList ++ Char.ofNat 0 ::
      ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("locked".toList ++ Char.ofNat 0 ::
      ("prunable gone".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: []))))) := by
    simp only [s, String.toList_append, h1, h2, List.append_assoc, List.cons_append]
  unfold parseWorktreeListPorcelain
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  have hToks : splitNulTokensAllowEmptyAux [] s.toList =
      some ["worktree /tmp/wt", "HEAD " ++ z40, "branch refs/heads/main", "locked", "prunable gone", ""] := by
    rw [hsList]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ hHead]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    have hNil : splitNulTokensAllowEmptyAux [] [] = some [] := rfl
    rw [hNil]
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.map]
  let hzLine := "HEAD " ++ z40
  have hStz : splitWorktreeStanzas []
      ["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone", ""] =
      some [["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"]] := by
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty z40)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (by decide)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rfl
  have hRefMain : mkRefName "main" = .ok { raw := "main" } := by
    unfold mkRefName
    rw [show isValidRefNameStr "main" = true from by decide]
    rfl
  have hPWt : parseWorktreeStanza
      ["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"] =
      .ok { path := "/tmp/wt", head? := none, branch? := some { raw := "main" },
            isLocked := true, isPrunable := true, pruneReason := some "gone" } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/wt" "/tmp/wt"
      [hzLine, "branch refs/heads/main", "locked", "prunable gone"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_zeros _ _ z40 _ isAllZeros_rep40_zero]
    rw [parseWorktreeAttrs_branch _ _ "branch refs/heads/main" "refs/heads/main" "main" { raw := "main" } _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hRefMain]
    rw [parseWorktreeAttrs_locked]
    rw [parseWorktreeAttrs_prunable_reason _ _ "prunable gone" "gone" _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  have hInfos : parseWorktreeStanzas
      [["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"]] =
      .ok [{ path := "/tmp/wt", head? := none, branch? := some { raw := "main" },
             isLocked := true, isPrunable := true, pruneReason := some "gone" }] := by
    unfold parseWorktreeStanzas
    rw [hPWt]
    rfl
  rw [hToks]
  dsimp only
  rw [hStz]
  dsimp only
  rw [hInfos]
  rfl

private theorem mem_dedupCommitIds_iff {x : CommitId} {xs : List CommitId} :
    x ∈ dedupCommitIds xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [dedupCommitIds]
  | cons y ys ih =>
    simp only [dedupCommitIds]
    split
    · next hc =>
      have hy : y ∈ ys := ih.mp (List.contains_iff_mem.mp hc)
      constructor
      · intro h; exact List.mem_cons_of_mem y (ih.mp h)
      · intro h
        rcases List.mem_cons.mp h with rfl | hys
        · exact ih.mpr hy
        · exact ih.mpr hys
    · constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hrest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem y (ih.mp hrest)
      · intro h
        rcases List.mem_cons.mp h with rfl | hys
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem y (ih.mpr hys)

private theorem mem_ancestorsStep_iff {s : RepoState} {frontier : List CommitId} {a : CommitId} :
    a ∈ ancestorsStep s frontier ↔ ∃ c ∈ frontier, a ∈ parentsOf s c := by
  simp only [ancestorsStep, mem_dedupCommitIds_iff, List.mem_flatMap]

private inductive PathN (s : RepoState) : Nat → CommitId → CommitId → Prop where
  | zero (x : CommitId) : PathN s 0 x x
  | succ {k : Nat} {a u b : CommitId} : PathN s k a u → u ∈ parentsOf s b → PathN s (k + 1) a b

private theorem pathN_trans {s : RepoState} {k1 k2 : Nat} {a b c : CommitId}
    (h1 : PathN s k1 a b) (h2 : PathN s k2 b c) : PathN s (k1 + k2) a c := by
  induction h2 with
  | zero => simpa using h1
  | succ _ hu ih => simpa [Nat.add_assoc] using PathN.succ (ih h1) hu

private theorem pathN_one_of_parent {s : RepoState} {a b : CommitId} (h : a ∈ parentsOf s b) :
    PathN s 1 a b :=
  PathN.succ (PathN.zero a) h

private theorem pathN_unfold_first {s : RepoState} {k : Nat} {a c : CommitId}
    (h : PathN s (k + 1) a c) : ∃ u, PathN s k a u ∧ u ∈ parentsOf s c := by
  cases h with
  | succ hp hu => exact ⟨_, hp, hu⟩

private theorem mem_ancestorsFuel_iff (s : RepoState) (n : Nat) (frontier : List CommitId) (a : CommitId) :
    a ∈ ancestorsFuel s n frontier ↔ ∃ c ∈ frontier, ∃ k, 1 ≤ k ∧ k ≤ n ∧ PathN s k a c := by
  induction n generalizing frontier with
  | zero =>
    simp [ancestorsFuel]
    intro _ _ k hk1 hk0
    omega
  | succ n ih =>
    unfold ancestorsFuel
    cases frontier with
    | nil =>
      simp
    | cons x xs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, mem_dedupCommitIds_iff,
        List.mem_append, mem_ancestorsStep_iff, ih]
      constructor
      · rintro (⟨c, hc, hac⟩ | ⟨u, ⟨c, hc, huc⟩, k, hk1, hkn, hpk⟩)
        · exact ⟨c, hc, 1, Nat.le_refl 1, Nat.le_add_left 1 n, pathN_one_of_parent hac⟩
        · exact ⟨c, hc, k + 1, by omega, Nat.succ_le_succ hkn, PathN.succ hpk huc⟩
      · rintro ⟨c, hc, k, hk1, hkn, hpk⟩
        cases k with
        | zero => omega
        | succ k' =>
          cases k' with
          | zero =>
            obtain ⟨u, h0, huc⟩ := pathN_unfold_first hpk
            cases h0
            exact Or.inl ⟨c, hc, huc⟩
          | succ k'' =>
            obtain ⟨u, hpk', huc⟩ := pathN_unfold_first hpk
            exact Or.inr ⟨u, ⟨c, hc, huc⟩, k'' + 1, by omega, by omega, hpk'⟩

private theorem hasCommit_eq_true_iff {s : RepoState} {id : CommitId} :
    hasCommit s id = true ↔ ∃ c ∈ s.commits, c.id = id := by
  simp [hasCommit, List.any_eq_true]

private theorem validCommitDagAux_all_seen (seen : List CommitId) (cs : List CommitNode)
    (h : validCommitDagAux seen cs = true) :
    ∀ c ∈ cs, c.id ∉ seen ∧ ∀ p ∈ c.parents, p ∈ seen ∨ ∃ c' ∈ cs, c'.id = p := by
  induction cs generalizing seen with
  | nil => intro c hc; cases hc
  | cons hd tl ih =>
    simp only [validCommitDagAux, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    rcases h with ⟨⟨hNotSeen, hParents⟩, hTl⟩
    have hNotSeen' : hd.id ∉ seen := fun hmem => by
      have hc := List.contains_iff_mem.mpr hmem
      rw [hc] at hNotSeen
      cases hNotSeen
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hMemTl
    · refine ⟨hNotSeen', fun p hp => Or.inl (List.contains_iff_mem.mp (hParents p hp))⟩
    · obtain ⟨hNotInHdSeen, hPar⟩ := ih (hd.id :: seen) hTl c hMemTl
      refine ⟨fun hs => hNotInHdSeen (List.mem_cons_of_mem hd.id hs), fun p hp => ?_⟩
      rcases hPar p hp with hpSeen | ⟨c', hc', rfl⟩
      · rcases List.mem_cons.mp hpSeen with rfl | hpOrig
        · exact Or.inr ⟨hd, List.mem_cons_self, rfl⟩
        · exact Or.inl hpOrig
      · exact Or.inr ⟨c', List.mem_cons_of_mem hd hc', rfl⟩

private def nodeIdxAux (idx : Nat) : List CommitNode → CommitId → Option Nat
  | [], _ => none
  | c :: cs, id => if c.id == id then some idx else nodeIdxAux (idx + 1) cs id

private theorem nodeIdxAux_shift (k idx : Nat) (cs : List CommitNode) (id : CommitId) :
    nodeIdxAux (k + idx) cs id = (nodeIdxAux idx cs id).map (k + ·) := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    simp only [nodeIdxAux]
    split
    · rfl
    · simpa [Nat.add_assoc] using ih (idx + 1)

private theorem nodeIdxAux_lt_length (idx : Nat) (cs : List CommitNode) (id : CommitId) {j : Nat}
    (hj : nodeIdxAux idx cs id = some j) : idx ≤ j ∧ j < idx + cs.length := by
  induction cs generalizing idx with
  | nil => simp [nodeIdxAux] at hj
  | cons c cs ih =>
    simp only [nodeIdxAux] at hj
    split at hj
    · cases hj; exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨h1, h2⟩ := ih (idx + 1) hj
      exact ⟨by omega, by simp; omega⟩

private theorem nodeIdxAux_some_of_mem (idx : Nat) (cs : List CommitNode) {c : CommitNode}
    (hc : c ∈ cs) : ∃ j, nodeIdxAux idx cs c.id = some j := by
  induction cs generalizing idx with
  | nil => cases hc
  | cons hd tl ih =>
    simp only [nodeIdxAux]
    rcases List.mem_cons.mp hc with rfl | htl
    · exact ⟨idx, by simp⟩
    · split
      · exact ⟨idx, rfl⟩
      · exact ih (idx + 1) htl

private theorem nodeIdxAux_some_mem (idx : Nat) (cs : List CommitNode) (id : CommitId) {j : Nat}
    (hj : nodeIdxAux idx cs id = some j) : ∃ c ∈ cs, c.id = id := by
  induction cs generalizing idx with
  | nil => simp [nodeIdxAux] at hj
  | cons hd tl ih =>
    simp only [nodeIdxAux] at hj
    split at hj
    · next heq => exact ⟨hd, List.mem_cons_self, beq_iff_eq.mp heq⟩
    · obtain ⟨c, hc, hid⟩ := ih (idx + 1) hj
      exact ⟨c, List.mem_cons_of_mem hd hc, hid⟩

private theorem validCommitDagAux_find_parent_lt (seen : List CommitId) (cs : List CommitNode)
    (h : validCommitDagAux seen cs = true)
    {id : CommitId} {v : CommitNode} (hfind : cs.find? (fun c => c.id == id) = some v)
    {u : CommitId} (hu : u ∈ v.parents) :
    u ∈ seen ∨ ∃ ju jv, nodeIdxAux 0 cs u = some ju ∧ nodeIdxAux 0 cs id = some jv ∧ ju < jv := by
  induction cs generalizing seen with
  | nil => simp at hfind
  | cons hd tl ih =>
    simp only [validCommitDagAux, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    rcases h with ⟨⟨_, hParents⟩, hTl⟩
    have hTlAll := validCommitDagAux_all_seen (hd.id :: seen) tl hTl
    by_cases heq : hd.id = id
    · simp only [List.find?, heq, beq_self_eq_true] at hfind
      cases hfind
      exact Or.inl (List.contains_iff_mem.mp (hParents u hu))
    · have hbeq : (hd.id == id) = false := beq_false_of_ne heq
      simp only [List.find?, hbeq] at hfind
      have hvid : v.id = id := by
        have hp : (v.id == id) = true := List.find?_some (p := fun (c : CommitNode) => c.id == id) hfind
        exact beq_iff_eq.mp hp
      rcases ih (hd.id :: seen) hTl hfind with huSeen | ⟨ju', jv', hju', hjv', hlt⟩
      · rcases List.mem_cons.mp huSeen with rfl | huOrig
        · have hvmem : v ∈ tl := List.mem_of_find?_eq_some hfind
          have hjvShift : nodeIdxAux 1 tl id = (nodeIdxAux 0 tl id).map (1 + ·) :=
            nodeIdxAux_shift 1 0 tl id
          obtain ⟨jv', hjv'⟩ := nodeIdxAux_some_of_mem 0 tl hvmem
          rw [hvid] at hjv'
          refine Or.inr ⟨0, 1 + jv', ?_, ?_, by omega⟩
          · simp [nodeIdxAux]
          · simp only [nodeIdxAux, hbeq, Bool.false_eq_true, ↓reduceIte, hjvShift, hjv', Option.map]
        · exact Or.inl huOrig
      · have hneU : hd.id ≠ u := by
          intro hEq
          obtain ⟨cu, hcu, hcuId⟩ := nodeIdxAux_some_mem 0 tl u hju'
          have hns := (hTlAll cu hcu).1
          rw [hcuId, ← hEq] at hns
          exact hns List.mem_cons_self
        have hbeqU : (hd.id == u) = false := beq_false_of_ne hneU
        have hShiftU : nodeIdxAux 1 tl u = (nodeIdxAux 0 tl u).map (1 + ·) :=
          by simpa using nodeIdxAux_shift 1 0 tl u
        have hShiftV : nodeIdxAux 1 tl id = (nodeIdxAux 0 tl id).map (1 + ·) :=
          by simpa using nodeIdxAux_shift 1 0 tl id
        refine Or.inr ⟨1 + ju', 1 + jv', ?_, ?_, Nat.add_lt_add_left hlt 1⟩
        · simp only [nodeIdxAux, hbeqU, Bool.false_eq_true, ↓reduceIte, hShiftU, hju', Option.map]
        · simp only [nodeIdxAux, hbeq, Bool.false_eq_true, ↓reduceIte, hShiftV, hjv', Option.map]

private theorem parent_lt_of_validDag {s : RepoState}
    (hdag : validCommitDagAux [] s.commits = true) {u v : CommitId} (huv : u ∈ parentsOf s v) :
    ∃ ju jv, nodeIdxAux 0 s.commits u = some ju ∧ nodeIdxAux 0 s.commits v = some jv ∧ ju < jv := by
  unfold parentsOf at huv
  cases hf : s.commits.find? (fun c => c.id == v) with
  | none => simp [hf] at huv
  | some node =>
    simp [hf] at huv
    rcases validCommitDagAux_find_parent_lt [] s.commits hdag hf huv with hnil | hres
    · cases hnil
    · exact hres

private theorem pathN_index_bound {s : RepoState} (hdag : validCommitDagAux [] s.commits = true)
    {k : Nat} {a b : CommitId} (hp : PathN s k a b) (hb : hasCommit s b = true) :
    ∃ ja jb, nodeIdxAux 0 s.commits a = some ja ∧ nodeIdxAux 0 s.commits b = some jb ∧ ja + k ≤ jb := by
  induction hp with
  | zero x =>
    obtain ⟨c, hc, hcid⟩ := hasCommit_eq_true_iff.mp hb
    obtain ⟨jx, hjx⟩ := nodeIdxAux_some_of_mem 0 s.commits hc
    rw [hcid] at hjx
    exact ⟨jx, jx, hjx, hjx, Nat.le_refl jx⟩
  | succ _ hub ih =>
    obtain ⟨ju, jb, hju, hjb, hlt⟩ := parent_lt_of_validDag hdag hub
    match nodeIdxAux_some_mem 0 s.commits _ hju with
    | ⟨cu, hcu, hcuId⟩ =>
      have huMem := hasCommit_eq_true_iff.mpr ⟨cu, hcu, hcuId⟩
      obtain ⟨ja, ju', hja, hju', hle⟩ := ih huMem
      rw [hju] at hju'
      cases hju'
      exact ⟨ja, jb, hja, hjb, by omega⟩

/-- Proof of `test_git_model_isAncestor_reflexiveAndGuarded` for `Model.isAncestor`. -/
theorem proof_git_model_isAncestor_reflexiveAndGuarded :
    AllPass (test_git_model_isAncestor_reflexiveAndGuarded Model.isAncestor) := by
  intro s a b
  by_cases ha : hasCommit s a = true
  · simp [ha, Model.isAncestor, assert]
  · have ha' : hasCommit s a = false := Bool.eq_false_iff.mpr ha
    simp [ha', Model.isAncestor, assert]

private theorem isAncestor_eq_true_iff_pathN {s : RepoState} (hdag : validCommitDagAux [] s.commits = true)
    {a b : CommitId} :
    Model.isAncestor s a b = true ↔ hasCommit s a = true ∧ hasCommit s b = true ∧ ∃ k, PathN s k a b := by
  simp only [Model.isAncestor, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    mem_ancestorsFuel_iff, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨ha, hb⟩, rfl | ⟨c, rfl, k, _, _, hpk⟩⟩
    · exact ⟨ha, hb, 0, PathN.zero a⟩
    · exact ⟨ha, hb, k, hpk⟩
  · rintro ⟨ha, hb, k, hpk⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    cases k with
    | zero =>
      cases hpk
      exact Or.inl rfl
    | succ k' =>
      obtain ⟨_, jb, _, hjb, hbound⟩ := pathN_index_bound hdag hpk hb
      have hjbLt := (nodeIdxAux_lt_length 0 s.commits b hjb).2
      exact Or.inr ⟨b, rfl, k' + 1, by omega, by omega, hpk⟩

private theorem foldl_min_mem (xs : List CommitId) (acc : Option CommitId) (m : CommitId)
    (h : xs.foldl
      (fun best c => match best with | none => some c | some b => if c.hex < b.hex then some c else some b)
      acc = some m) :
    m ∈ xs ∨ acc = some m := by
  induction xs generalizing acc with
  | nil => exact Or.inr h
  | cons x rest ih =>
    simp only [List.foldl] at h
    rcases ih _ h with hx | hacc
    · exact Or.inl (List.mem_cons_of_mem x hx)
    · cases acc with
      | none =>
        simp at hacc
        exact Or.inl (by subst hacc; exact List.mem_cons_self)
      | some b =>
        simp at hacc
        split at hacc
        · cases hacc; exact Or.inl List.mem_cons_self
        · exact Or.inr hacc

private theorem mergeBase_mem_commonAncestors (s : RepoState) (a b m : CommitId)
    (h : Model.mergeBase? s a b = some m) : m ∈ commonAncestors s a b := by
  unfold Model.mergeBase? lowestCommonAncestors at h
  rcases foldl_min_mem _ none m h with hmem | hnone
  · exact (List.mem_filter.mp hmem).1
  · cases hnone

/-- Standalone transitivity theorem for `Model.isAncestor` under `ValidRepoState`. -/
theorem proof_git_isAncestor_validRepoState_transitive {s : RepoState} (hValid : ValidRepoState s)
    {a b c : CommitId} (hab : Model.isAncestor s a b = true) (hbc : Model.isAncestor s b c = true) :
    Model.isAncestor s a c = true := by
  have hdag : validCommitDagAux [] s.commits = true := by
    unfold ValidRepoState isValidRepoState at hValid
    simp only [Bool.and_eq_true] at hValid
    exact hValid.1.1.1.1.1.1.1
  obtain ⟨ha, _, k1, hk1⟩ := (isAncestor_eq_true_iff_pathN hdag).mp hab
  obtain ⟨_, hc, k2, hk2⟩ := (isAncestor_eq_true_iff_pathN hdag).mp hbc
  exact (isAncestor_eq_true_iff_pathN hdag).mpr ⟨ha, hc, k1 + k2, pathN_trans hk1 hk2⟩

/-- Standalone soundness theorem for `Model.mergeBase?` returning a common ancestor. -/
theorem proof_git_mergeBase_returns_commonAncestor {s : RepoState} {a b m : CommitId}
    (h : Model.mergeBase? s a b = some m) : Model.isAncestor s m a = true ∧ Model.isAncestor s m b = true := by
  have hm := mergeBase_mem_commonAncestors s a b m h
  unfold commonAncestors at hm
  split at hm
  · cases hm
  · simp only [List.mem_filter, Bool.and_eq_true] at hm
    exact hm.2

/-- Proof of `test_git_model_isAncestor_transitiveAndMergeBaseValid` for `Model.isAncestor` and `Model.mergeBase?`. -/
theorem proof_git_model_isAncestor_transitiveAndMergeBaseValid :
    AllPass (test_git_model_isAncestor_transitiveAndMergeBaseValid Model.isAncestor Model.mergeBase?) := by
  intro s a b c hValid
  dsimp [test_git_model_isAncestor_transitiveAndMergeBaseValid, AllPass, AllPassRun, bind, pure, assert]
  by_cases hand : (Model.isAncestor s a b && Model.isAncestor s b c) = true
  · split
    · have ⟨hab, hbc⟩ := Bool.and_eq_true_iff.mp hand
      refine ⟨proof_git_isAncestor_validRepoState_transitive hValid hab hbc, ?_⟩
      cases hmb : Model.mergeBase? s a b with
      | none => trivial
      | some m => exact ⟨proof_git_mergeBase_returns_commonAncestor hmb, trivial⟩
    · next hnot => exact absurd hand hnot
  · split
    · next htr => exact absurd htr hand
    · cases hmb : Model.mergeBase? s a b with
      | none => trivial
      | some m => exact ⟨proof_git_mergeBase_returns_commonAncestor hmb, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_model_isAncestor_transitiveAndMergeBaseValid`. -/
theorem reach_git_model_isAncestor_transitiveAndMergeBaseValid :
    CanReach (test_git_model_isAncestor_transitiveAndMergeBaseValid Model.isAncestor Model.mergeBase?) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let s : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    worktrees := [{ path := "/repo", head := .detached c0 }]
  }
  have hValid : ValidRepoState s := by unfold ValidRepoState; decide
  exact ⟨s, c0, c0, c0, hValid,
    proof_git_model_isAncestor_transitiveAndMergeBaseValid s c0 c0 c0 hValid⟩

private theorem freshSyntheticCommitIdAux_not_hasCommit (s : RepoState) (idx remaining : Nat) :
    hasCommit s (freshSyntheticCommitIdAux s idx remaining) = false := by
  induction remaining generalizing idx with
  | zero =>
    unfold freshSyntheticCommitIdAux
    have hmax : ∀ c ∈ s.commits, c.id.hex.length ≤ s.commits.foldl (fun m c => Nat.max m c.id.hex.length) 40 := by
      have hgen : ∀ (cs : List CommitNode) (acc : Nat),
          ∀ c ∈ cs, c.id.hex.length ≤ cs.foldl (fun m c => Nat.max m c.id.hex.length) acc := by
        intro cs
        induction cs with
        | nil => intro _ _ hc; cases hc
        | cons hd tl ih =>
          intro acc c hc
          simp only [List.foldl]
          rcases List.mem_cons.mp hc with rfl | htl
          · have hmono : ∀ (ys : List CommitNode) (a b : Nat), a ≤ b →
                a ≤ ys.foldl (fun m c => Nat.max m c.id.hex.length) b := by
              intro ys
              induction ys with
              | nil => intro _ _ h; exact h
              | cons y ys ihy =>
                intro a b hab
                exact ihy _ _ (Nat.le_trans hab (Nat.le_max_left _ _))
            exact hmono tl _ _ (Nat.le_max_right _ _)
          · exact ih _ c htl
      exact hgen s.commits 40
    apply Bool.eq_false_iff.mpr
    intro hmem
    obtain ⟨c, hc, heq⟩ := hasCommit_eq_true_iff.mp hmem
    have hlen := hmax c hc
    have hEqLen : c.id.hex.length =
        (String.ofList (List.replicate (s.commits.foldl (fun m c => Nat.max m c.id.hex.length) 40 + 1) '0')).length :=
      congrArg String.length (congrArg CommitId.hex heq)
    simp [String.length_ofList, List.length_replicate] at hEqLen
    omega
  | succ r ih =>
    unfold freshSyntheticCommitIdAux
    dsimp only
    split
    · next hnot => simpa using hnot
    · exact ih (idx + 1)

/-- `freshSyntheticCommitId s` is never already present in `s.commits`. -/
theorem proof_git_freshSyntheticCommitId_not_hasCommit (s : RepoState) :
    hasCommit s (freshSyntheticCommitId s) = false :=
  freshSyntheticCommitIdAux_not_hasCommit s s.commits.length (s.commits.length + 1)

/-- Proof of `test_git_api_unbornHead_behavior` for `mockGitApi`. -/
theorem proof_git_api_unbornHead_behavior :
    AllPass (test_git_api_unbornHead_behavior mockGitApi) := by
  intro _s0 path branch hPath _hInit
  have hPath' : (!isValidPathArg path) = false := by simp [hPath]
  have hRevHead : isValidRevSpec "HEAD" = true := by decide
  simp only [mockGitApi, runRepoStepUnit, runRepoStep, stepInit, hPath', Bool.false_eq_true, ↓reduceIte,
    Except.map, StateT.run, bind, pure, findWorktree?, List.find?,
    beq_self_eq_true, headCommitOfSlot, resolveRefStrInRepo, hRevHead, assert,
    Option.getD, Bool.not_true]
  refine ⟨trivial, trivial, ⟨{ kind := .invalidRef, message := "unknown revision 'HEAD'" }, rfl, rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_unbornHead_behavior`. -/
theorem reach_git_api_unbornHead_behavior :
    CanReach (test_git_api_unbornHead_behavior mockGitApi) := by
  let s0 : RepoState := { rootPath := "/repo" }
  let branch : RefName := { raw := "main" }
  have hPath : isValidPathArg "/repo" = true := by decide
  have hInit : ((mockGitApi.init "/repo" false (some branch)).run s0).1 = .ok () := by
    simp [mockGitApi, runRepoStepUnit, runRepoStep, stepInit, hPath, Except.map, StateT.run]
  exact ⟨s0, "/repo", branch, hPath, hInit,
    proof_git_api_unbornHead_behavior s0 "/repo" branch hPath hInit⟩

/-- Proof of `test_git_api_commit_emptyVsAllowEmpty` for `mockGitApi`. -/
theorem proof_git_api_commit_emptyVsAllowEmpty :
    AllPass (test_git_api_commit_emptyVsAllowEmpty mockGitApi) := by
  intro s0 wt _hValid ⟨hWts, hBare, hStaged, hConf⟩
  have hFresh := proof_git_freshSyntheticCommitId_not_hasCommit s0
  have hFind : findWorktree? s0 wt.path = some wt := by
    simp [findWorktree?, hWts]
  have hm1 : hasNulChar ['e', 'm', 'p', 't', 'y'] = false := by decide
  have hm2 : ("allow".isEmpty || hasNulChar "allow".toList) = false := by decide
  have hEmpty : (mockGitApi.commit wt.path { message := "empty", allowEmpty := false }).run s0 =
      (.error { kind := .nothingToCommit, message := "nothing to commit" }, s0) := by
    simp [mockGitApi, StateT.run, runRepoStep, stepCommit, hm1, hFresh, hFind, hBare, hConf, hStaged]
  have hOk : ∃ sOk,
      (mockGitApi.commit wt.path { message := "allow", allowEmpty := true }).run s0 =
        (.ok (freshSyntheticCommitId s0), sOk) ∧
      (mockGitApi.headCommit? wt.path).run sOk = (.ok (some (freshSyntheticCommitId s0)), sOk) := by
    cases hHead : wt.head <;>
    · simp only [mockGitApi, StateT.run, runRepoStep, stepCommit, hm2, hFresh, hFind, hBare, hConf,
        hHead, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure, bind]
      refine ⟨_, rfl, ?_⟩
      simp [updateWorktree, hWts, findWorktree?, List.map, headCommitOfSlot]
  rcases hOk with ⟨sOk, hCommitOk, hHeadOk⟩
  simp only [assert, hEmpty, hCommitOk, hHeadOk]
  exact ⟨⟨{ kind := .nothingToCommit, message := "nothing to commit" }, rfl, rfl, trivial⟩, trivial, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_commit_emptyVsAllowEmpty`. -/
theorem reach_git_api_commit_emptyVsAllowEmpty :
    CanReach (test_git_api_commit_emptyVsAllowEmpty mockGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { path := "/repo", head := .attached b (some c0) }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by unfold ValidRepoState; decide
  exact ⟨s0, wt, hValid, ⟨rfl, rfl, rfl, rfl⟩,
    proof_git_api_commit_emptyVsAllowEmpty s0 wt hValid ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem isValidRevSpec_of_isValidRefNameStr {s : String} (h : isValidRefNameStr s = true) :
    isValidRevSpec s = true ∧ s.toList.any isAsciiWhitespace = false := by
  unfold isValidRefNameStr at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hne, hdash⟩, _⟩, _⟩, _⟩, hbadChar⟩, _⟩, _⟩, _⟩, _⟩
  have hNoCtrl : s.toList.any isControlChar = false := by
    apply Bool.eq_false_iff.mpr
    intro ha
    simp only [List.any_eq_true] at ha
    rcases ha with ⟨c, hc, hctrl⟩
    have hinv : isInvalidRefChar c = true := by simp [isInvalidRefChar, hctrl]
    have := List.any_eq_true.mpr ⟨c, hc, hinv⟩
    rw [this] at hbadChar
    cases hbadChar
  have hNoWs : s.toList.any isAsciiWhitespace = false := by
    apply Bool.eq_false_iff.mpr
    intro ha
    simp only [List.any_eq_true] at ha
    rcases ha with ⟨c, hc, hws⟩
    have hinv : isInvalidRefChar c = true := by
      simp only [isAsciiWhitespace, Bool.or_eq_true, beq_iff_eq] at hws
      rcases hws with ((rfl | rfl) | rfl) | rfl <;> decide
    have := List.any_eq_true.mpr ⟨c, hc, hinv⟩
    rw [this] at hbadChar
    cases hbadChar
  refine ⟨?_, hNoWs⟩
  simp only [isValidRevSpec, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  exact ⟨⟨hne, hdash⟩, hNoCtrl⟩

/-- Proof of `test_git_api_worktreeAdd_branchInUseRejected` for `mockGitApi`. -/
theorem proof_git_api_worktreeAdd_branchInUseRejected :
    AllPass (test_git_api_worktreeAdd_branchInUseRejected mockGitApi) := by
  intro s0 mainWt b c newWtPath hValid ⟨hWts, hHead⟩ ⟨hPath, hNe⟩ hRef
  have hSlotValid : validWorktreeSlot s0 mainWt = true := by
    unfold ValidRepoState isValidRepoState at hValid
    simp only [Bool.and_eq_true, List.all_eq_true] at hValid
    exact hValid.2 mainWt (by rw [hWts]; exact List.mem_cons_self)
  have hBranchMem : (b, c) ∈ s0.branches := by
    unfold validWorktreeSlot at hSlotValid
    simp only [hHead, Bool.and_eq_true] at hSlotValid
    exact List.contains_iff_mem.mp hSlotValid.1.2
  have hFindWt : findWorktree? s0 newWtPath = none := by
    simp [findWorktree?, hWts, List.find?, beq_false_of_ne (Ne.symm hNe)]
  have ⟨hRev, hNoWs⟩ := isValidRevSpec_of_isValidRefNameStr hRef
  have hFindBr : ∃ b' c', s0.branches.find? (fun p => p.1.raw == b.raw) = some (b', c') ∧ b' = b := by
    cases hf : s0.branches.find? (fun p => p.1.raw == b.raw) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf (b, c) hBranchMem
      simp at this
    | some p =>
      have hp : p.1.raw = b.raw := beq_iff_eq.mp (List.find?_some (p := fun (q : RefName × CommitId) => q.1.raw == b.raw) hf)
      have hbEq : p.1 = b := by rcases p with ⟨⟨pr⟩, pc⟩; cases b; dsimp at hp; subst hp; rfl
      exact ⟨p.1, p.2, rfl, hbEq⟩
  rcases hFindBr with ⟨b', c', hFindBr, rfl⟩
  have hCheckedOut : isBranchCheckedOut s0 b' = true := by
    simp [isBranchCheckedOut, hWts, hHead]
  have hNoWs' : ¬ (∃ x, x ∈ b'.raw.toList ∧ isAsciiWhitespace x = true) := by
    simpa [List.any_eq_true] using hNoWs
  have hRes : (mockGitApi.worktreeAdd mainWt.path { path := newWtPath, target? := some b'.raw }).run s0 =
      (.error { kind := .branchInUse, message := s!"branch '{b'.raw}' is already used by worktree" }, s0) := by
    simp [mockGitApi, StateT.run, runRepoStepUnit, runRepoStep, stepWorktreeAdd,
      stepWorktreeAdd.stepWorktreeAddValidated, Except.map,
      hPath, hFindWt, hRev, hNoWs', hFindBr, hCheckedOut]
  simp only [assert, hRes]
  exact ⟨⟨{ kind := .branchInUse, message := s!"branch '{b'.raw}' is already used by worktree" }, rfl, rfl, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_worktreeAdd_branchInUseRejected`. -/
theorem reach_git_api_worktreeAdd_branchInUseRejected :
    CanReach (test_git_api_worktreeAdd_branchInUseRejected mockGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { path := "/repo", head := .attached b (some c0) }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by unfold ValidRepoState; decide
  exact ⟨s0, wt, b, c0, "/wt2", hValid, ⟨rfl, rfl⟩, ⟨by decide, by decide⟩, by decide,
    proof_git_api_worktreeAdd_branchInUseRejected s0 wt b c0 "/wt2" hValid ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ (by decide)⟩

/-- Proof of `test_git_api_checkout_dirtyWorktreeRejected` for `mockGitApi`. -/
theorem proof_git_api_checkout_dirtyWorktreeRejected :
    AllPass (test_git_api_checkout_dirtyWorktreeRejected mockGitApi) := by
  intro s0 mainWt b _c _hValid ⟨hWts, hNotBare, hDirty⟩ _hMem
  have hBare : mainWt.isBare = false := by simpa using hNotBare
  have hFind : findWorktree? s0 mainWt.path = some mainWt := by
    simp [findWorktree?, hWts]
  have hRes : (mockGitApi.checkout mainWt.path (.branch b) false).run s0 =
      (.error { kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }, s0) := by
    simp [mockGitApi, StateT.run, runRepoStepUnit, runRepoStep, stepCheckout, Except.map, hFind, hBare, hDirty]
  simp only [assert, hRes]
  exact ⟨⟨{ kind := .dirtyWorktree, message := "local changes would be overwritten by checkout" }, rfl, rfl, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_api_checkout_dirtyWorktreeRejected`. -/
theorem reach_git_api_checkout_dirtyWorktreeRejected :
    CanReach (test_git_api_checkout_dirtyWorktreeRejected mockGitApi) := by
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := {
    path := "/repo"
    head := .attached b (some c0)
    unstaged := [("a.txt", some "dirty")]
  }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by unfold ValidRepoState; decide
  exact ⟨s0, wt, b, c0, hValid, ⟨rfl, rfl, by decide⟩, List.Mem.head _,
    proof_git_api_checkout_dirtyWorktreeRejected s0 wt b c0 hValid ⟨rfl, rfl, by decide⟩ (List.Mem.head _)⟩

/-- Proof of `test_git_api_withWorktree_cleanupAndErrorPrecedence` for `Impl.mkApiM`. -/
theorem proof_git_api_withWorktree_cleanupAndErrorPrecedence :
    AllPass (test_git_api_withWorktree_cleanupAndErrorPrecedence (fun ops => Impl.mkApiM ops)) := by
  intro repoPath wtPath actOk cleanOk ⟨hRepo, hWt⟩
  have hRepo' : Impl.validateRepoPath repoPath = .ok () := by simp [Impl.validateRepoPath, hRepo]
  have hCwdRepo : Impl.validateCwd? (some repoPath) = .ok () := by simp [Impl.validateCwd?, hRepo]
  have hExtra : Impl.validateExtraEnv #[] = .ok () := by unfold Impl.validateExtraEnv; simp
  have hNulWt : hasNulChar wtPath.toList = false := by
    simp [isValidPathArg] at hWt
    exact hWt.2
  let addArgs : Array String := #["worktree", "add", "--detach", "--", wtPath]
  let remArgs : Array String := #["worktree", "remove", "--", wtPath]
  let addReq : GitRawRequest := { cwd := some repoPath, args := addArgs }
  let remReq : GitRawRequest := { cwd := some repoPath, args := remArgs }
  have hArgsAdd : (addArgs.all fun a => !hasNulChar a.toList) = true := by
    rw [Array.all_eq_true]
    intro i hi
    match i with
    | 0 => simp [addArgs]; decide
    | 1 => simp [addArgs]; decide
    | 2 => simp [addArgs]; decide
    | 3 => simp [addArgs]; decide
    | 4 => simpa [addArgs] using hNulWt
    | _ + 5 => exfalso; simp [addArgs] at hi; omega
  have hArgsRem : (remArgs.all fun a => !hasNulChar a.toList) = true := by
    rw [Array.all_eq_true]
    intro i hi
    match i with
    | 0 => simp [remArgs]; decide
    | 1 => simp [remArgs]; decide
    | 2 => simp [remArgs]; decide
    | 3 => simpa [remArgs] using hNulWt
    | _ + 4 => exfalso; simp [remArgs] at hi; omega
  have hAddRaw :
      Impl.runGitRaw mockRawOps { cwd := some repoPath, args := #["worktree", "add", "--detach", "--", wtPath] } =
      (do
        match ← mockRawOps.listEnv with
        | .error e => return .error e
        | .ok inherited =>
          mockRawOps.execGit (cleanGitEnv inherited #[])
            { cwd := some repoPath, args := #["worktree", "add", "--detach", "--", wtPath] }) := by
    change Impl.runGitRaw mockRawOps addReq = _
    unfold Impl.runGitRaw
    rw [hCwdRepo, hExtra]
    simp only [addReq, addArgs, hArgsAdd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hRemRaw :
      Impl.runGitRaw mockRawOps { cwd := some repoPath, args := #["worktree", "remove", "--", wtPath] } =
      (do
        match ← mockRawOps.listEnv with
        | .error e => return .error e
        | .ok inherited =>
          mockRawOps.execGit (cleanGitEnv inherited #[])
            { cwd := some repoPath, args := #["worktree", "remove", "--", wtPath] }) := by
    change Impl.runGitRaw mockRawOps remReq = _
    unfold Impl.runGitRaw
    rw [hCwdRepo, hExtra]
    simp only [remReq, remArgs, hArgsRem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  cases actOk <;> cases cleanOk
  · simp [Impl.mkApiM, Impl.withWorktreeImpl, Impl.worktreeAddImpl, Impl.worktreeRemoveImpl,
      Impl.runGitChecked, hRepo', hWt, hAddRaw, hRemRaw]
    simp [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadFinally.tryFinally', assert]
  · simp [Impl.mkApiM, Impl.withWorktreeImpl, Impl.worktreeAddImpl, Impl.worktreeRemoveImpl,
      Impl.runGitChecked, hRepo', hWt, hAddRaw, hRemRaw]
    simp [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadFinally.tryFinally', assert]
  · have hRemKind :
        (Impl.classifyError "worktree remove"
          { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 }).kind =
          .commandFailed := by
      unfold Impl.classifyError
      rw [decodeUtf8Lossy_toUTF8, show Impl.decodeUtf8Lossy ByteArray.empty = "" from rfl]
      decide
    simp [Impl.mkApiM, Impl.withWorktreeImpl, Impl.worktreeAddImpl, Impl.worktreeRemoveImpl,
      Impl.runGitChecked, hRepo', hWt, hAddRaw, hRemRaw]
    simp [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadFinally.tryFinally', assert]
    exact hRemKind
  · simp [Impl.mkApiM, Impl.withWorktreeImpl, Impl.worktreeAddImpl, Impl.worktreeRemoveImpl,
      Impl.runGitChecked, hRepo', hWt, hAddRaw, hRemRaw]
    simp [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadFinally.tryFinally', assert]

/-- Non-vacuity `CanReach` witness for `test_git_api_withWorktree_cleanupAndErrorPrecedence`. -/
theorem reach_git_api_withWorktree_cleanupAndErrorPrecedence :
    CanReach (test_git_api_withWorktree_cleanupAndErrorPrecedence (fun ops => Impl.mkApiM ops)) :=
  ⟨"/repo", "/wt", true, true, ⟨by decide, by decide⟩,
    proof_git_api_withWorktree_cleanupAndErrorPrecedence "/repo" "/wt" true true ⟨by decide, by decide⟩⟩

/-- Proof of `test_git_raw_mkApi_isolationAndGuards` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_isolationAndGuards :
    AllPass (test_git_raw_mkApi_isolationAndGuards (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_isolationAndGuards, AllPass, assert]
  let st₀ : GitCliMockState :=
    { inheritedEnv := #[("GIT_DIR", "/evil/.git"), ("GIT_TERMINAL_PROMPT", "1"), ("PATH", "/usr/bin")]
      handler := fun req _ =>
        if req.args.toList.contains "commit" then
          .ok { exitCode := 1, stdout := "nothing to commit, working tree clean\n".toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "rev-parse" then
          .ok { exitCode := 0, stdout := (String.ofList (List.replicate 40 'a') ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "cat-file" then
          .ok { exitCode := 0, stdout := "tree\n".toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by
    unfold Impl.validateRepoPath
    simp [show isValidPathArg "/repo" = true from by decide]
  have hCwdOk : Impl.validateCwd? (some "/repo") = .ok () := by
    unfold Impl.validateCwd?
    simp [show isValidPathArg "/repo" = true from by decide]
  have hExtraOk : Impl.validateExtraEnv #[] = .ok () := by
    unfold Impl.validateExtraEnv; simp
  have hEnvCheck :
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_DIR", none) ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
      (cleanGitEnv st₀.inheritedEnv #[]).toList.contains ("GIT_CONFIG_VALUE_0", some "all") := by
    decide
  let commitOut : GitRawOutput :=
    { exitCode := 1, stdout := "nothing to commit, working tree clean\n".toUTF8, stderr := ByteArray.empty }
  have hCommitRun :
      ((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀ =
        (.error (Impl.classifyError "commit" commitOut),
         { st₀ with
           recordedEnvs := [cleanGitEnv st₀.inheritedEnv #[]]
           recordedRequests := [{ cwd := some "/repo", args := #["commit", "--no-gpg-sign", "-m", "msg"] }]
           callCount := 1 }) := by
    change Impl.commitImpl mockRawOps "/repo" { message := "msg" } st₀ = _
    have hMsg : (("msg" : String).isEmpty || hasNulChar "msg".toList) = false := by decide
    have hExtraApp : (#[] ++ (#[] : Array (String × Option String))) = #[] := rfl
    have hArgsApp : (#["commit", "--no-gpg-sign", "-m", "msg"] ++ #[]) =
        #["commit", "--no-gpg-sign", "-m", "msg"] := rfl
    have hArgs : (#["commit", "--no-gpg-sign", "-m", "msg"].all fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["commit", "--no-gpg-sign", "-m", "msg"] (by decide)
    have hCont : (#["commit", "--no-gpg-sign", "-m", "msg"].toList.contains "commit") = true := by decide
    unfold Impl.commitImpl Impl.runGitChecked Impl.runGitRaw
    simp only [hRepoOk, hMsg, Bool.false_eq_true, ↓reduceIte, hExtraApp, hArgsApp, hCwdOk, hExtraOk,
      hArgs, Bool.not_true, bind, StateT.bind, pure, List.nil_append, mockRawOps, st₀]
    rw [hCont]
    rfl
  have hCommit :
      ∃ e, (((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀).1 = .error e ∧
        e.kind = .nothingToCommit := by
    rw [hCommitRun]
    have hKind : (Impl.classifyError "commit" commitOut).kind = .nothingToCommit := by
      unfold Impl.classifyError
      dsimp only [commitOut]
      rw [show Impl.decodeUtf8Lossy ByteArray.empty = "" from rfl, decodeUtf8Lossy_toUTF8]
      decide
    exact ⟨_, rfl, hKind⟩
  have hCommitEnv :
      ((((Impl.mkApiM mockRawOps).commit "/repo" { message := "msg" }).run st₀).2.recordedEnvs.all fun env =>
        env.toList.contains ("GIT_DIR", none) ∧
        env.toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
        env.toList.contains ("GIT_CONFIG_VALUE_0", some "all")) := by
    rw [hCommitRun]
    dsimp only [List.all, Bool.and_true]
    exact decide_eq_true hEnvCheck
  have hShowRun :
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD" "subdir").run st₀).1 = .ok none ∧
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD" "subdir").run st₀).2.callCount = 2 := by
    change (Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀).1 = .ok none ∧
      (Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀).2.callCount = 2
    have hStrict : isValidStrictRevSpec "HEAD" = true := by decide
    have hRel : isValidRelRepoPath "subdir" = true := by decide
    have hRev : isValidRevSpec "HEAD" = true := by decide
    have hRevStr : ("HEAD" ++ "^{commit}") = "HEAD^{commit}" := rfl
    have hArgs1 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].all fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["rev-parse", "-q", "--verify", "HEAD^{commit}"] (by decide)
    have hC1 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].toList.contains "commit") = false := by decide
    have hC2 : (#["rev-parse", "-q", "--verify", "HEAD^{commit}"].toList.contains "rev-parse") = true := by decide
    have hCid : mkCommitId (Impl.trimTrailingNewlines (String.ofList (List.replicate 40 'a') ++ "\n")) =
        .ok { hex := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" } := by
      rw [show Impl.trimTrailingNewlines (String.ofList (List.replicate 40 'a') ++ "\n") =
          "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" from by decide]
      unfold mkCommitId
      rw [show isValidCommitIdStr "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = true from by decide]
      rfl
    have hCatStr : (toString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++ toString ":" ++ toString "subdir") =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir" := rfl
    have hArgs2 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].all
        fun a => !hasNulChar a.toList) = true :=
      all_no_nul_of_list ["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"] (by decide)
    have hD1 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "commit") = false := by decide
    have hD2 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "rev-parse") = false := by decide
    have hD3 : (#["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"].toList.contains "cat-file") = true := by decide
    have hTrim : (Impl.trimAsciiWhitespace "tree\n" != "blob") = true := by decide
    have hShowEq : Impl.showFileImpl mockRawOps "/repo" "HEAD" "subdir" st₀ =
        (.ok none,
         { st₀ with
           recordedEnvs := [cleanGitEnv st₀.inheritedEnv #[], cleanGitEnv st₀.inheritedEnv #[]]
           recordedRequests :=
             [{ cwd := some "/repo", args := #["rev-parse", "-q", "--verify", "HEAD^{commit}"] },
              { cwd := some "/repo", args := #["cat-file", "-t", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa:subdir"] }]
           callCount := 2 }) := by
      unfold Impl.showFileImpl Impl.revParseCommitImpl Impl.runGitChecked Impl.runGitRaw
      simp only [hRepoOk, hStrict, hRel, hRev, hCwdOk, hExtraOk,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, pure,
        mockRawOps, st₀]
      rw [hRevStr, hArgs1]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      rw [hC1, hC2]
      simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      rw [decodeUtf8Checked_toUTF8]
      dsimp only
      rw [hCid]
      dsimp only [bind, StateT.bind, pure, StateT.pure, mockRawOps]
      rw [hCatStr, hArgs2]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      rw [hD1, hD2, hD3]
      simp only [Bool.false_eq_true, ↓reduceIte, show (0 != (0 : Int)) = false from rfl]
      rw [decodeUtf8Checked_toUTF8]
      dsimp only
      rw [hTrim]
      simp only [↓reduceIte]
      rfl
    rw [hShowEq]
    exact ⟨rfl, rfl⟩
  have hFetch : ∃ e, (((Impl.mkApiM mockRawOps).fetch "/repo" "--upload-pack=evil" none false).run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).fetch "/repo" "--upload-pack=evil" none false).run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.fetchImpl mockRawOps "/repo" "--upload-pack=evil" none false st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.fetchImpl mockRawOps "/repo" "--upload-pack=evil" none false st₀).2.callCount = 0
    unfold Impl.fetchImpl
    rw [hRepoOk, show isValidRemoteOrRefspec "--upload-pack=evil" = false from by decide]
    exact ⟨_, rfl, rfl, rfl⟩
  have hAdd : ∃ e, (((Impl.mkApiM mockRawOps).add "/repo" #[] false).run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).add "/repo" #[] false).run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.addImpl mockRawOps "/repo" #[] false st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.addImpl mockRawOps "/repo" #[] false st₀).2.callCount = 0
    unfold Impl.addImpl
    rw [hRepoOk]
    exact ⟨_, rfl, rfl, rfl⟩
  have hColon : ∃ e, (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD:etc/passwd" "a").run st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (((Impl.mkApiM mockRawOps).showFile? "/repo" "HEAD:etc/passwd" "a").run st₀).2.callCount = 0 := by
    change ∃ e, (Impl.showFileImpl mockRawOps "/repo" "HEAD:etc/passwd" "a" st₀).1 = .error e ∧
      e.kind = .invalidInput ∧
      (Impl.showFileImpl mockRawOps "/repo" "HEAD:etc/passwd" "a" st₀).2.callCount = 0
    unfold Impl.showFileImpl
    rw [hRepoOk, show isValidStrictRevSpec "HEAD:etc/passwd" = false from by decide]
    exact ⟨_, rfl, rfl, rfl⟩
  exact ⟨hCommit, hCommitEnv, hShowRun, hFetch, hAdd, hColon, trivial⟩

/-- Proof of `empirical_git_status_parsesRealOutput` for `parsePorcelainStatusZ`. -/
theorem proof_empirical_git_status_parsesRealOutput :
    AllPass (empirical_git_status_parsesRealOutput parsePorcelainStatusZ) := by
  dsimp only [empirical_git_status_parsesRealOutput, AllPass, assert]
  refine ⟨?_, trivial⟩
  let s := " M a b.txt\x00R  new name.txt\x00old name.txt\x00?? untrack.txt\x00"
  have hsList : s.toList =
      " M a b.txt".toList ++ Char.ofNat 0 ::
      ("R  new name.txt".toList ++ Char.ofNat 0 ::
      ("old name.txt".toList ++ Char.ofNat 0 ::
      ("?? untrack.txt".toList ++ Char.ofNat 0 :: []))) := by decide
  have h4 : splitNulRecordsAux [] ("?? untrack.txt".toList ++ Char.ofNat 0 :: []) = some ["?? untrack.txt"] :=
    splitNulRecordsAux_step "?? untrack.txt" [] [] (by decide) (by decide) rfl
  have h3 := splitNulRecordsAux_step "old name.txt" _ _ (by decide) (by decide) h4
  have h2 := splitNulRecordsAux_step "R  new name.txt" _ _ (by decide) (by decide) h3
  have h1 := splitNulRecordsAux_step " M a b.txt" _ _ (by decide) (by decide) h2
  have hToks : splitNulRecordsAux [] s.toList =
      some [" M a b.txt", "R  new name.txt", "old name.txt", "?? untrack.txt"] := by
    rw [hsList]; exact h1
  have hRecs : parsePorcelainStatusRecords
      [" M a b.txt", "R  new name.txt", "old name.txt", "?? untrack.txt"] =
      .ok [ { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" },
            { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
            { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" } ] := by
    have hr3 : parsePorcelainStatusRecords ["?? untrack.txt"] =
        .ok [{ indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" }] := by
      rw [parsePorcelainStatusRecords_plain "?? untrack.txt" "untrack.txt" '?' '?' [] (some .untracked) (some .untracked)
        (by decide) (by decide) (by decide) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      rfl
    have hr2 : parsePorcelainStatusRecords ["R  new name.txt", "old name.txt", "?? untrack.txt"] =
        .ok [ { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
              { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" } ] := by
      rw [parsePorcelainStatusRecords_rc "R  new name.txt" "new name.txt" "old name.txt" 'R' ' ' ["?? untrack.txt"]
        (some .renamed) none (by decide) (by decide) (by decide) rfl rfl (by decide), hr3]
      rfl
    rw [parsePorcelainStatusRecords_plain " M a b.txt" "a b.txt" ' ' 'M'
      ["R  new name.txt", "old name.txt", "?? untrack.txt"] none (some .modified)
      (by decide) (by decide) (by decide) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩, hr2]
    rfl
  exact parsePorcelainStatusZ_ok_of s _ _ (toUTF8_nonempty_of_ne (by decide)) hToks hRecs

/-- Proof of `empirical_git_worktreeList_parsesRealOutput` for `parseWorktreeListPorcelain`. -/
theorem proof_empirical_git_worktreeList_parsesRealOutput :
    AllPass (empirical_git_worktreeList_parsesRealOutput parseWorktreeListPorcelain) := by
  dsimp only [empirical_git_worktreeList_parsesRealOutput, AllPass, assert]
  refine ⟨?_, trivial⟩
  let sha := String.ofList (List.replicate 40 'a')
  let s := "worktree /tmp/main\x00HEAD " ++ sha ++ "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD " ++ sha ++ "\x00detached\x00\x00"
  have hEmptyFalse : s.toUTF8.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (toUTF8_eq_empty_iff s).mp h
    have hl := congrArg String.length he
    simp [s] at hl
  have hHead : hasNulChar ("HEAD " ++ sha).toList = false :=
    hasNulChar_head_rep40 40 'a' (by decide)
  have h1 : "worktree /tmp/main\x00HEAD ".toList =
      "worktree /tmp/main".toList ++ Char.ofNat 0 :: "HEAD ".toList := by decide
  have h2 : "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD ".toList =
      Char.ofNat 0 :: ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: ("worktree /tmp/wt".toList ++ Char.ofNat 0 :: "HEAD ".toList))) := by decide
  have h3 : "\x00detached\x00\x00".toList =
      Char.ofNat 0 :: ("detached".toList ++ Char.ofNat 0 :: ("".toList ++ Char.ofNat 0 :: [])) := by decide
  have hsList : s.toList =
      "worktree /tmp/main".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ sha).toList ++ Char.ofNat 0 ::
      ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 ::
      ("worktree /tmp/wt".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ sha).toList ++ Char.ofNat 0 ::
      ("detached".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: []))))))) := by
    simp only [s, String.toList_append, h1, h2, h3, List.append_assoc, List.cons_append]
  have ht8 : splitNulTokensAllowEmptyAux [] ("".toList ++ Char.ofNat 0 :: []) = some [""] :=
    splitNulTokensAllowEmptyAux_step "" [] [] (by decide) rfl
  have ht7 := splitNulTokensAllowEmptyAux_step "detached" _ _ (by decide) ht8
  have ht6 := splitNulTokensAllowEmptyAux_step ("HEAD " ++ sha) _ _ hHead ht7
  have ht5 := splitNulTokensAllowEmptyAux_step "worktree /tmp/wt" _ _ (by decide) ht6
  have ht4 := splitNulTokensAllowEmptyAux_step "" _ _ (by decide) ht5
  have ht3 := splitNulTokensAllowEmptyAux_step "branch refs/heads/main" _ _ (by decide) ht4
  have ht2 := splitNulTokensAllowEmptyAux_step ("HEAD " ++ sha) _ _ hHead ht3
  have ht1 := splitNulTokensAllowEmptyAux_step "worktree /tmp/main" _ _ (by decide) ht2
  have hToks : splitNulTokensAllowEmptyAux [] s.toList =
      some ["worktree /tmp/main", "HEAD " ++ sha, "branch refs/heads/main", "", "worktree /tmp/wt", "HEAD " ++ sha, "detached", ""] := by
    rw [hsList]; exact ht1
  let haLine := "HEAD " ++ sha
  have hCidA : mkCommitId sha = .ok { hex := sha } := by
    unfold mkCommitId
    rw [isValidCommitIdStr_rep40_a]
    rfl
  have hRefMain : mkRefName "main" = .ok { raw := "main" } := by
    unfold mkRefName
    rw [show isValidRefNameStr "main" = true from by decide]
    rfl
  have hStz : splitWorktreeStanzas []
      ["worktree /tmp/main", haLine, "branch refs/heads/main", "", "worktree /tmp/wt", haLine, "detached", ""] =
      some [["worktree /tmp/main", haLine, "branch refs/heads/main"],
            ["worktree /tmp/wt", haLine, "detached"]] := by
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty sha)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty sha)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rfl
  have hP1 : parseWorktreeStanza ["worktree /tmp/main", haLine, "branch refs/heads/main"] =
      .ok { path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/main" "/tmp/main"
      [haLine, "branch refs/heads/main"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_commit _ _ sha { hex := sha } _ isAllZeros_rep40_a hCidA]
    rw [parseWorktreeAttrs_branch _ _ "branch refs/heads/main" "refs/heads/main" "main" { raw := "main" } _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hRefMain]
    rfl
  have hP2 : parseWorktreeStanza ["worktree /tmp/wt", haLine, "detached"] =
      .ok { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/wt" "/tmp/wt"
      [haLine, "detached"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_commit _ _ sha { hex := sha } _ isAllZeros_rep40_a hCidA]
    rw [parseWorktreeAttrs_detached]
    rfl
  have hInfos : parseWorktreeStanzas
      [["worktree /tmp/main", haLine, "branch refs/heads/main"],
       ["worktree /tmp/wt", haLine, "detached"]] =
      .ok [{ path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } },
           { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true }] := by
    unfold parseWorktreeStanzas
    rw [hP1]
    dsimp only [bind, Except.bind, pure, Except.pure]
    unfold parseWorktreeStanzas
    rw [hP2]
    rfl
  exact parseWorktreeListPorcelain_ok_of s _ _ _ hEmptyFalse hToks hStz hInfos

/-- `Impl.ensureNonEmptyMsg` always returns a non-empty string when `fallback ≠ ""`. -/
theorem proof_git_ensureNonEmptyMsg_nonEmpty (fallback msg : String) (hf : fallback ≠ "") :
    Impl.ensureNonEmptyMsg fallback msg ≠ "" := by
  unfold Impl.ensureNonEmptyMsg
  dsimp only
  split
  · exact hf
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- `Impl.classifyError` always produces a non-empty diagnostic message. -/
theorem proof_git_classifyError_nonEmptyMessage (cmd : String) (out : GitRawOutput) :
    (Impl.classifyError cmd out).message ≠ "" := by
  dsimp only [Impl.classifyError]
  refine proof_git_ensureNonEmptyMsg_nonEmpty _ _ ?_
  intro h
  have hl := congrArg String.length h
  have h4 : (toString ("git " : String)).length = 4 := rfl
  have h0 : ("" : String).length = 0 := rfl
  simp only [String.length_append, h4, h0] at hl
  omega

/-- `mapEnvVarsError` always produces a non-empty diagnostic message. -/
theorem proof_git_mapEnvVarsError_nonEmptyMessage (e : LeanSwe.EnvVars.EnvVarsError) :
    (mapEnvVarsError e).message ≠ "" := by
  unfold mapEnvVarsError
  dsimp only
  split
  · decide
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

/-- `mapProcessError` always produces a non-empty diagnostic message. -/
theorem proof_git_mapProcessError_nonEmptyMessage (cmd : String) (e : LeanSwe.Process.ProcessError) :
    (mapProcessError cmd e).message ≠ "" := by
  unfold mapProcessError
  dsimp only
  split
  · intro h
    have hl := congrArg String.length h
    have h4 : (toString ("git " : String)).length = 4 := rfl
    have h0 : ("" : String).length = 0 := rfl
    simp only [String.length_append, h4, h0] at hl
    omega
  · next h =>
    intro hem
    rw [hem] at h
    simp [String.isEmpty] at h

end LeanSwe.Git.Proofs

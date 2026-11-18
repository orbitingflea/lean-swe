import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests
import LeanSwe.Git.Proofs.ParserProofs
import LeanSwe.Git.Proofs.ImpossibleProofs

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

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

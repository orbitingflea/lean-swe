import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private instance : LawfulBEq CommitId where
  eq_of_beq {a b} h := by
    cases a with
    | mk ha =>
      cases b with
      | mk hb =>
        change (ha == hb) = true at h
        simp [beq_iff_eq] at h
        exact congrArg CommitId.mk h
  rfl {a} := by
    cases a with
    | mk ha =>
      change (ha == ha) = true
      simp

private inductive PathN (s : RepoInstance) : Nat → CommitId → CommitId → Prop where
  | zero (x : CommitId) : PathN s 0 x x
  | succ {k : Nat} {a u b : CommitId} : PathN s k a u → u ∈ parentsOf s b → PathN s (k + 1) a b

private theorem pathN_trans {s : RepoInstance} {k1 k2 : Nat} {a b c : CommitId}
    (h1 : PathN s k1 a b) (h2 : PathN s k2 b c) : PathN s (k1 + k2) a c := by
  induction h2 with
  | zero => simpa using h1
  | succ _ hu ih => simpa [Nat.add_assoc] using PathN.succ (ih h1) hu

private theorem pathN_one_of_parent {s : RepoInstance} {a b : CommitId} (h : a ∈ parentsOf s b) :
    PathN s 1 a b :=
  PathN.succ (PathN.zero a) h

private theorem mem_foldl_cons (xs acc : List CommitId) (x : CommitId) :
    x ∈ xs.foldl (fun v y => y :: v) acc ↔ x ∈ xs ∨ x ∈ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl, ih, List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

private theorem mem_parents_fold (repo : RepoInstance) (visited : List CommitId)
    (ps acc : List CommitId) (x : CommitId) :
    x ∈ ps.foldl (fun acc2 p =>
      if hasCommit repo p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc ↔
      x ∈ acc ∨ (x ∈ ps ∧ hasCommit repo x = true ∧ x ∉ visited) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl]
    split
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      rw [ih]
      constructor
      · rintro (hx | ⟨hxMem, hxHas, hxNot⟩)
        · rcases List.mem_cons.mp hx with rfl | hxAcc
          · have hxNot : x ∉ visited := fun hm => by
              have hct := List.contains_iff_mem.mpr hm
              rw [hct] at hc
              cases hc.1.2
            exact Or.inr ⟨List.mem_cons_self, hc.1.1, hxNot⟩
          · exact Or.inl hxAcc
        · exact Or.inr ⟨List.mem_cons_of_mem p hxMem, hxHas, hxNot⟩
      · rintro (hxAcc | ⟨hxMem, hxHas, hxNot⟩)
        · exact Or.inl (List.mem_cons_of_mem p hxAcc)
        · rcases List.mem_cons.mp hxMem with rfl | hxPs
          · exact Or.inl List.mem_cons_self
          · exact Or.inr ⟨hxPs, hxHas, hxNot⟩
    · next hc =>
      rw [ih]
      constructor
      · rintro (hxAcc | ⟨hxMem, hxHas, hxNot⟩)
        · exact Or.inl hxAcc
        · exact Or.inr ⟨List.mem_cons_of_mem p hxMem, hxHas, hxNot⟩
      · rintro (hxAcc | ⟨hxMem, hxHas, hxNot⟩)
        · exact Or.inl hxAcc
        · rcases List.mem_cons.mp hxMem with rfl | hxPs
          · by_cases hmem : x ∈ acc
            · exact Or.inl hmem
            · exfalso
              apply hc
              simp only [Bool.and_eq_true, Bool.not_eq_true']
              refine ⟨⟨hxHas, ?_⟩, ?_⟩
              · exact Bool.eq_false_iff.mpr fun hm => hxNot (List.contains_iff_mem.mp hm)
              · exact Bool.eq_false_iff.mpr fun hm => hmem (List.contains_iff_mem.mp hm)
          · exact Or.inr ⟨hxPs, hxHas, hxNot⟩

private theorem mem_frontier_fold (repo : RepoInstance) (visited frontier acc : List CommitId)
    (x : CommitId) :
    x ∈ frontier.foldl (fun acc1 cid =>
      (parentsOf repo cid).foldl (fun acc2 p =>
        if hasCommit repo p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc1) acc ↔
      x ∈ acc ∨ ∃ c ∈ frontier, x ∈ parentsOf repo c ∧ hasCommit repo x = true ∧ x ∉ visited := by
  induction frontier generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl, ih, mem_parents_fold, List.mem_cons]
    constructor
    · rintro ((hxAcc | ⟨hxc, hxHas, hxNot⟩) | ⟨c', hc', hxc', hxHas, hxNot⟩)
      · exact Or.inl hxAcc
      · exact Or.inr ⟨c, Or.inl rfl, hxc, hxHas, hxNot⟩
      · exact Or.inr ⟨c', Or.inr hc', hxc', hxHas, hxNot⟩
    · rintro (hxAcc | ⟨c', rfl | hc', hxc', hxHas, hxNot⟩)
      · exact Or.inl (Or.inl hxAcc)
      · exact Or.inl (Or.inr ⟨hxc', hxHas, hxNot⟩)
      · exact Or.inr ⟨c', hc', hxc', hxHas, hxNot⟩

private theorem subset_bfsAncestorsLoop (repo : RepoInstance) (n : Nat) (frontier visited : List CommitId)
    {x : CommitId} (hx : x ∈ visited) :
    x ∈ bfsAncestorsLoop repo n frontier visited := by
  induction n generalizing frontier visited with
  | zero => exact hx
  | succ n ih =>
    unfold bfsAncestorsLoop
    split
    · exact hx
    · exact ih _ _ ((mem_foldl_cons _ _ x).mpr (Or.inr hx))

private theorem bfsAncestorsLoop_sound (repo : RepoInstance) (n : Nat) (frontier visited : List CommitId)
    (a : CommitId) (ha : a ∈ bfsAncestorsLoop repo n frontier visited) :
    hasCommit repo a = true ∨ a ∈ visited := by
  induction n generalizing frontier visited with
  | zero => exact Or.inr ha
  | succ n ih =>
    unfold bfsAncestorsLoop at ha
    split at ha
    · exact Or.inr ha
    · rcases ih _ _ ha with hHas | hVis'
      · exact Or.inl hHas
      · rcases (mem_foldl_cons _ _ a).mp hVis' with hNext | hVis
        · rcases (mem_frontier_fold repo visited frontier [] a).mp hNext with hEmpty | ⟨_, _, _, hHas, _⟩
          · cases hEmpty
          · exact Or.inl hHas
        · exact Or.inr hVis

private theorem bfsAncestorsLoop_sound_path (repo : RepoInstance) (n : Nat) (frontier visited : List CommitId)
    (a : CommitId) (ha : a ∈ bfsAncestorsLoop repo n frontier visited) :
    a ∈ visited ∨ ∃ c ∈ frontier, ∃ k, 1 ≤ k ∧ k ≤ n ∧ PathN repo k a c := by
  induction n generalizing frontier visited with
  | zero => exact Or.inl ha
  | succ n ih =>
    unfold bfsAncestorsLoop at ha
    split at ha
    · exact Or.inl ha
    · rcases ih _ _ ha with hVis' | ⟨u, huNext, k, hk1, hkn, hpk⟩
      · rcases (mem_foldl_cons _ _ a).mp hVis' with hNext | hVis
        · rcases (mem_frontier_fold repo visited frontier [] a).mp hNext with hEmpty | ⟨c, hcFr, hac, _, _⟩
          · cases hEmpty
          · exact Or.inr ⟨c, hcFr, 1, Nat.le_refl 1, Nat.le_add_left 1 n, pathN_one_of_parent hac⟩
        · exact Or.inl hVis
      · rcases (mem_frontier_fold repo visited frontier [] u).mp huNext with hEmpty | ⟨c, hcFr, huc, _, _⟩
        · cases hEmpty
        · exact Or.inr ⟨c, hcFr, k + 1, by omega, Nat.succ_le_succ hkn, PathN.succ hpk huc⟩

private def BfsClosed (repo : RepoInstance) (frontier visited : List CommitId) : Prop :=
  ∀ u ∈ visited, u ∉ frontier → ∀ p ∈ parentsOf repo u, hasCommit repo p = true → p ∈ visited

private theorem bfsClosed_step (repo : RepoInstance) (frontier visited : List CommitId)
    (hcl : BfsClosed repo frontier visited) :
    let next := frontier.foldl (fun acc cid =>
      (parentsOf repo cid).foldl (fun acc2 p =>
        if hasCommit repo p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc) []
    let visited' := next.foldl (fun v x => x :: v) visited
    BfsClosed repo next visited' := by
  intro next visited' u hu huNot p hp hHasP
  have huVis : u ∈ visited := by
    rcases (mem_foldl_cons next visited u).mp hu with hIn | hV
    · exact absurd hIn huNot
    · exact hV
  apply (mem_foldl_cons next visited p).mpr
  by_cases huFr : u ∈ frontier
  · by_cases hpVis : p ∈ visited
    · exact Or.inr hpVis
    · exact Or.inl ((mem_frontier_fold repo visited frontier [] p).mpr (Or.inr ⟨u, huFr, hp, hHasP, hpVis⟩))
  · exact Or.inr (hcl u huVis huFr p hp hHasP)

private theorem bfs_path_reach_frontier (repo : RepoInstance) (frontier visited : List CommitId)
    (hcl : BfsClosed repo frontier visited)
    (hParentsHas : ∀ x y, y ∈ parentsOf repo x → hasCommit repo x = true → hasCommit repo y = true) :
    ∀ {k : Nat} {a u : CommitId}, PathN repo k a u → u ∈ visited → hasCommit repo u = true →
      a ∈ visited ∨ ∃ w ∈ frontier, ∃ k1, k1 ≤ k ∧ PathN repo k1 a w := by
  intro k a u hpk huVis huHas
  induction hpk with
  | zero => exact Or.inl huVis
  | @succ k' a v u hpk' hvu ih =>
    by_cases huFr : u ∈ frontier
    · exact Or.inr ⟨u, huFr, k' + 1, Nat.le_refl _, PathN.succ hpk' hvu⟩
    · have hvHas : hasCommit repo v = true := hParentsHas u v hvu huHas
      have hvVis : v ∈ visited := hcl u huVis huFr v hvu hvHas
      rcases ih hvVis hvHas with haVis | ⟨w, hwFr, k1, hk1, hpk1⟩
      · exact Or.inl haVis
      · exact Or.inr ⟨w, hwFr, k1, by omega, hpk1⟩

private theorem bfsAncestorsLoop_complete (repo : RepoInstance) (n : Nat)
    (frontier visited : List CommitId)
    (hcl : BfsClosed repo frontier visited)
    (hsub : ∀ x ∈ frontier, x ∈ visited)
    (hParentsHas : ∀ x y, y ∈ parentsOf repo x → hasCommit repo x = true → hasCommit repo y = true) :
    ∀ {a w : CommitId} {k : Nat}, w ∈ frontier → k ≤ n → PathN repo k a w → hasCommit repo w = true →
      a ∈ bfsAncestorsLoop repo n frontier visited := by
  induction n generalizing frontier visited with
  | zero =>
    intro a w k hw hk hpk _
    have hk0 : k = 0 := by omega
    subst hk0
    cases hpk
    exact subset_bfsAncestorsLoop repo 0 frontier visited (hsub a hw)
  | succ n ih =>
    intro a w k hw hk hpk hwHas
    unfold bfsAncestorsLoop
    have hNeEmpty : frontier.isEmpty = false := by
      cases frontier with
      | nil => cases hw
      | cons _ _ => rfl
    simp only [hNeEmpty, Bool.false_eq_true, ↓reduceIte]
    cases hpk with
    | zero =>
      exact subset_bfsAncestorsLoop repo n _ _
        ((mem_foldl_cons _ visited a).mpr (Or.inr (hsub a hw)))
    | @succ k' a u w hpk' huw =>
      have huHas : hasCommit repo u = true := hParentsHas w u huw hwHas
      let next := frontier.foldl (fun acc cid =>
        (parentsOf repo cid).foldl (fun acc2 p =>
          if hasCommit repo p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc) []
      let visited' := next.foldl (fun v x => x :: v) visited
      have huVis' : u ∈ visited' := by
        apply (mem_foldl_cons next visited u).mpr
        by_cases huVis : u ∈ visited
        · exact Or.inr huVis
        · exact Or.inl ((mem_frontier_fold repo visited frontier [] u).mpr (Or.inr ⟨w, hw, huw, huHas, huVis⟩))
      have hcl' : BfsClosed repo next visited' := bfsClosed_step repo frontier visited hcl
      have hsub' : ∀ x ∈ next, x ∈ visited' := fun x hx =>
        (mem_foldl_cons next visited x).mpr (Or.inl hx)
      rcases bfs_path_reach_frontier repo next visited' hcl' hParentsHas hpk' huVis' huHas with
        haVis' | ⟨w', hw'Next, k1, hk1, hpk1⟩
      · exact subset_bfsAncestorsLoop repo n next visited' haVis'
      · have hw'Has : hasCommit repo w' = true := by
          rcases (mem_frontier_fold repo visited frontier [] w').mp hw'Next with hEmpty | ⟨_, _, _, hH, _⟩
          · cases hEmpty
          · exact hH
        exact ih next visited' hcl' hsub' hw'Next (by omega) hpk1 hw'Has

private theorem hasCommit_eq_true_iff {s : RepoInstance} {id : CommitId} :
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

private theorem parent_lt_of_validDag {s : RepoInstance}
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

private theorem pathN_index_bound {s : RepoInstance} (hdag : validCommitDagAux [] s.commits = true)
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

private theorem compare_hex_beq (a b : CommitId) :
    (compare a.hex b.hex == .eq) = (a == b) := by
  cases a with | mk ha => cases b with | mk hb =>
    change (compare ha hb == .eq) = (ha == hb)
    by_cases h : ha = hb
    · subst h; simp [Std.ReflCmp.compare_self]
    · have hbeqf : (ha == hb) = false := beq_false_of_ne h
      have hcmpne : compare ha hb ≠ .eq := fun hc => h (Std.LawfulEqCmp.compare_eq_iff_eq.mp hc)
      rw [hbeqf]
      cases hord : compare ha hb <;> simp_all

private theorem compare_hex_eq_iff (a b : CommitId) :
    compare a.hex b.hex = .eq ↔ a = b := by
  cases a with | mk ha => cases b with | mk hb =>
    constructor
    · intro hc; exact congrArg CommitId.mk (Std.LawfulEqCmp.compare_eq_iff_eq.mp hc)
    · intro heq; cases heq; exact Std.ReflCmp.compare_self

private theorem foldl_buildCommitParentsMap_spec (cs : List CommitNode)
    (init : Std.TreeMap.Raw String (List CommitId) compare) (hWF : init.WF)
    (hDef : ∀ id : CommitId, init.contains id.hex = false → init.getD id.hex [] = []) :
    let out := cs.foldl (fun m c => if m.contains c.id.hex then m else m.insert c.id.hex c.parents) init
    out.WF ∧
    (∀ id : CommitId, out.contains id.hex = (init.contains id.hex || cs.any (fun c => c.id == id))) ∧
    (∀ id : CommitId, out.getD id.hex [] =
      if init.contains id.hex then init.getD id.hex []
      else match cs.find? (fun c => c.id == id) with | some c => c.parents | none => []) := by
  induction cs generalizing init with
  | nil =>
    refine ⟨hWF, fun id => by simp, fun id => ?_⟩
    cases hInit : init.contains id.hex
    · simp [hDef id hInit]
    · simp
  | cons hd tl ih =>
    simp only [List.foldl, List.any_cons, List.find?]
    split
    · next hIn =>
      obtain ⟨hWF', hCont, hGet⟩ := ih init hWF hDef
      refine ⟨hWF', fun id => ?_, fun id => ?_⟩
      · rw [hCont id]
        by_cases heq : hd.id = id
        · subst heq; simp [hIn]
        · simp [beq_false_of_ne heq]
      · rw [hGet id]
        by_cases heq : hd.id = id
        · subst heq; simp [hIn]
        · simp [beq_false_of_ne heq]
    · next hNotIn =>
      have hInF : init.contains hd.id.hex = false := Bool.eq_false_iff.mpr hNotIn
      let init1 := init.insert hd.id.hex hd.parents
      have hDef1 : ∀ id : CommitId, init1.contains id.hex = false → init1.getD id.hex [] = [] := by
        intro id hc1
        dsimp only [init1] at hc1 ⊢
        rw [Std.TreeMap.Raw.contains_insert hWF, compare_hex_beq hd.id id] at hc1
        rw [Std.TreeMap.Raw.getD_insert hWF]
        by_cases heq : hd.id = id
        · subst heq; simp at hc1
        · have hBeqF : (hd.id == id) = false := beq_false_of_ne heq
          rw [hBeqF, Bool.false_or] at hc1
          have hCmpNe : ¬ (compare hd.id.hex id.hex = .eq) := fun hc => heq ((compare_hex_eq_iff hd.id id).mp hc)
          simp [hCmpNe, hDef id hc1]
      obtain ⟨hWF', hCont, hGet⟩ := ih init1 hWF.insert hDef1
      refine ⟨hWF', fun id => ?_, fun id => ?_⟩
      · rw [hCont id, Std.TreeMap.Raw.contains_insert hWF, compare_hex_beq hd.id id]
        cases hd.id == id <;> cases init.contains id.hex <;> cases tl.any (fun c => c.id == id) <;> rfl
      · rw [hGet id, Std.TreeMap.Raw.contains_insert hWF, Std.TreeMap.Raw.getD_insert hWF, compare_hex_beq hd.id id]
        by_cases heq : hd.id = id
        · subst heq
          simp [hInF]
        · have hBeqF : (hd.id == id) = false := beq_false_of_ne heq
          have hCmpNe : ¬ (compare hd.id.hex id.hex = .eq) := fun hc => heq ((compare_hex_eq_iff hd.id id).mp hc)
          simp [hBeqF, hCmpNe]

private theorem buildCommitParentsMap_contains (s : RepoInstance) (id : CommitId) :
    (buildCommitParentsMap s.commits).contains id.hex = hasCommit s id := by
  unfold buildCommitParentsMap hasCommit
  have ⟨_, hCont, _⟩ := foldl_buildCommitParentsMap_spec s.commits .empty Std.TreeMap.Raw.WF.empty (fun _ _ => rfl)
  have hEmp : (Std.TreeMap.Raw.empty : Std.TreeMap.Raw String (List CommitId) compare).contains id.hex = false := rfl
  rw [hCont id, hEmp, Bool.false_or]

private theorem buildCommitParentsMap_getD (s : RepoInstance) (id : CommitId) :
    (buildCommitParentsMap s.commits).getD id.hex [] = parentsOf s id := by
  unfold buildCommitParentsMap parentsOf
  have ⟨_, _, hGet⟩ := foldl_buildCommitParentsMap_spec s.commits .empty Std.TreeMap.Raw.WF.empty (fun _ _ => rfl)
  have hEmp : (Std.TreeMap.Raw.empty : Std.TreeMap.Raw String (List CommitId) compare).contains id.hex = false := rfl
  rw [hGet id, hEmp]
  rfl

private theorem rawTreeSet_foldl_insert_spec (xs : List CommitId)
    (init : Std.TreeSet.Raw String compare) (hWF : init.WF) :
    let out := xs.foldl (fun s c => s.insert c.hex) init
    out.WF ∧ (∀ q : CommitId, out.contains q.hex = (xs.contains q || init.contains q.hex)) := by
  induction xs generalizing init with
  | nil => exact ⟨hWF, fun q => by simp⟩
  | cons x rest ih =>
    simp only [List.foldl, List.contains_cons]
    obtain ⟨hWF', hCont⟩ := ih (init.insert x.hex) hWF.insert
    refine ⟨hWF', fun q => ?_⟩
    rw [hCont q, Std.TreeSet.Raw.contains_insert hWF, compare_hex_beq x q]
    have hSymm : (x == q) = (q == x) := by
      by_cases h : x = q
      · subst h; simp
      · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
    rw [hSymm]
    cases q == x <;> cases rest.contains q <;> cases init.contains q.hex <;> rfl

private theorem bfsInnerParents_eq (s : RepoInstance) (visited : List CommitId)
    (ps acc : List CommitId) (vs : Std.TreeSet.Raw String compare) (hWF : vs.WF)
    (hInv : ∀ q : CommitId, vs.contains q.hex = (visited.contains q || acc.contains q)) :
    let (acc', vs') := ps.foldl (fun (acc2, vs2) p =>
      if (buildCommitParentsMap s.commits).contains p.hex && !vs2.contains p.hex then
        (p :: acc2, vs2.insert p.hex)
      else
        (acc2, vs2)) (acc, vs)
    acc' = ps.foldl (fun acc2 p =>
      if hasCommit s p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc ∧
    vs'.WF ∧
    (∀ q : CommitId, vs'.contains q.hex = (visited.contains q || acc'.contains q)) := by
  induction ps generalizing acc vs with
  | nil => exact ⟨rfl, hWF, hInv⟩
  | cons p rest ih =>
    simp only [List.foldl, buildCommitParentsMap_contains s p, hInv p]
    have hCond : (hasCommit s p && !(visited.contains p || acc.contains p)) =
        (hasCommit s p && !visited.contains p && !acc.contains p) := by
      cases hasCommit s p <;> cases visited.contains p <;> cases acc.contains p <;> rfl
    rw [hCond]
    split
    · apply ih (p :: acc) (vs.insert p.hex) hWF.insert
      intro q
      rw [Std.TreeSet.Raw.contains_insert hWF, hInv q, List.contains_cons, compare_hex_beq p q]
      have hSymm : (p == q) = (q == p) := by
        by_cases h : p = q
        · subst h; simp
        · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
      rw [hSymm]
      cases q == p <;> cases visited.contains q <;> cases acc.contains q <;> rfl
    · exact ih acc vs hWF hInv

private theorem bfsFrontierStep_eq (s : RepoInstance) (visited frontier acc : List CommitId)
    (vs : Std.TreeSet.Raw String compare) (hWF : vs.WF)
    (hInv : ∀ q : CommitId, vs.contains q.hex = (visited.contains q || acc.contains q)) :
    let (next, vs') := frontier.foldl (fun (acc1, vs1) cid =>
      ((buildCommitParentsMap s.commits).getD cid.hex []).foldl (fun (acc2, vs2) p =>
        if (buildCommitParentsMap s.commits).contains p.hex && !vs2.contains p.hex then
          (p :: acc2, vs2.insert p.hex)
        else
          (acc2, vs2)) (acc1, vs1)) (acc, vs)
    next = frontier.foldl (fun acc1 cid =>
      (parentsOf s cid).foldl (fun acc2 p =>
        if hasCommit s p && !visited.contains p && !acc2.contains p then p :: acc2 else acc2) acc1) acc ∧
    vs'.WF ∧
    (∀ q : CommitId, vs'.contains q.hex = (visited.contains q || next.contains q)) := by
  induction frontier generalizing acc vs with
  | nil => exact ⟨rfl, hWF, hInv⟩
  | cons cid rest ih =>
    simp only [List.foldl, buildCommitParentsMap_getD s cid]
    have ⟨hAcc1, hWF1, hInv1⟩ := bfsInnerParents_eq s visited (parentsOf s cid) acc vs hWF hInv
    have ⟨hNext, hWF2, hInv2⟩ := ih _ _ hWF1 hInv1
    rw [← hAcc1]
    exact ⟨hNext, hWF2, hInv2⟩

private theorem foldl_cons_contains (xs acc : List CommitId) (q : CommitId) :
    (xs.foldl (fun v x => x :: v) acc).contains q = (acc.contains q || xs.contains q) := by
  by_cases h : (xs.foldl (fun v x => x :: v) acc).contains q = true
  · have hm := (mem_foldl_cons xs acc q).mp (List.contains_iff_mem.mp h)
    rw [h]
    rcases hm with hx | ha
    · have hcx := List.contains_iff_mem.mpr hx
      rw [hcx]; cases acc.contains q <;> rfl
    · have hca := List.contains_iff_mem.mpr ha
      rw [hca]; rfl
  · have hf := Bool.eq_false_iff.mpr h
    rw [hf]
    cases hca : acc.contains q with
    | true =>
      exfalso; apply h
      exact List.contains_iff_mem.mpr ((mem_foldl_cons xs acc q).mpr (Or.inr (List.contains_iff_mem.mp hca)))
    | false =>
      cases hcx : xs.contains q with
      | true =>
        exfalso; apply h
        exact List.contains_iff_mem.mpr ((mem_foldl_cons xs acc q).mpr (Or.inl (List.contains_iff_mem.mp hcx)))
      | false => rfl

private theorem bfsAncestorsFastLoop_eq (s : RepoInstance) (n : Nat)
    (frontier visited : List CommitId) (vs : Std.TreeSet.Raw String compare) (hWF : vs.WF)
    (hInv : ∀ q : CommitId, vs.contains q.hex = visited.contains q) :
    bfsAncestorsFastLoop (buildCommitParentsMap s.commits) n frontier visited vs =
      bfsAncestorsLoop s n frontier visited := by
  induction n generalizing frontier visited vs with
  | zero => rfl
  | succ n ih =>
    unfold bfsAncestorsFastLoop bfsAncestorsLoop
    split
    · rfl
    · have hInv0 : ∀ q : CommitId, vs.contains q.hex = (visited.contains q || ([] : List CommitId).contains q) := by
        intro q
        have hNil : ([] : List CommitId).contains q = false := rfl
        rw [hInv q, hNil, Bool.or_false]
      have ⟨hNext, hWFNext, hInvNext⟩ := bfsFrontierStep_eq s visited frontier [] vs hWF hInv0
      dsimp only at hNext hWFNext hInvNext ⊢
      rw [hNext]
      apply ih _ _ _ hWFNext
      intro q
      rw [hInvNext q, hNext, foldl_cons_contains]

private theorem singleton_rawTreeSet_spec (x : CommitId) :
    ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert x.hex).WF ∧
    (∀ q : CommitId,
      ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert x.hex).contains q.hex =
        ([x] : List CommitId).contains q) := by
  have ⟨hWF, hCont⟩ := rawTreeSet_foldl_insert_spec [x] .empty Std.TreeSet.Raw.WF.empty
  refine ⟨hWF, fun q => ?_⟩
  have h1 := hCont q
  have hEmp : (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).contains q.hex = false := rfl
  rw [hEmp, Bool.or_false] at h1
  exact h1

private theorem isAncestor_eq_slow (s : RepoInstance) (a b : CommitId) :
    Model.isAncestor s a b =
      (hasCommit s a && hasCommit s b &&
        (a == b || (bfsAncestorsLoop s s.commits.length [b] [b]).contains a)) := by
  unfold Model.isAncestor
  split
  · rfl
  · dsimp only
    rw [buildCommitParentsMap_contains s a, buildCommitParentsMap_contains s b]
    obtain ⟨hWFb, hContB⟩ := singleton_rawTreeSet_spec b
    have hBfs : bfsAncestorsFastLoop (buildCommitParentsMap s.commits) s.commits.length [b] [b]
        ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert b.hex) =
        bfsAncestorsLoop s s.commits.length [b] [b] :=
      bfsAncestorsFastLoop_eq s s.commits.length [b] [b] _ hWFb hContB
    rw [hBfs]

/-- Proof of `test_git_model_isAncestor_reflexiveAndGuarded` for `Model.isAncestor`. -/
theorem proof_git_model_isAncestor_reflexiveAndGuarded :
    AllPass (test_git_model_isAncestor_reflexiveAndGuarded Model.isAncestor) := by
  intro s a b
  by_cases ha : hasCommit s a = true
  · simp [isAncestor_eq_slow, ha, assert]
  · have ha' : hasCommit s a = false := Bool.eq_false_iff.mpr ha
    simp [isAncestor_eq_slow, ha', assert]

private theorem isAncestor_eq_true_iff_pathN {s : RepoInstance} (hdag : validCommitDagAux [] s.commits = true)
    {a b : CommitId} :
    Model.isAncestor s a b = true ↔ hasCommit s a = true ∧ hasCommit s b = true ∧ ∃ k, PathN s k a b := by
  rw [isAncestor_eq_slow]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
  have hParentsHas : ∀ x y, y ∈ parentsOf s x → hasCommit s x = true → hasCommit s y = true := by
    intro x y hy _
    obtain ⟨ju, _, hju, _, _⟩ := parent_lt_of_validDag hdag hy
    obtain ⟨cu, hcu, hcuId⟩ := nodeIdxAux_some_mem 0 s.commits y hju
    exact hasCommit_eq_true_iff.mpr ⟨cu, hcu, hcuId⟩
  constructor
  · rintro ⟨⟨ha, hb⟩, rfl | hmem⟩
    · exact ⟨ha, hb, 0, PathN.zero a⟩
    · rcases bfsAncestorsLoop_sound_path s s.commits.length [b] [b] a hmem with hVis | ⟨c, hc, k, _, _, hpk⟩
      · rcases List.mem_singleton.mp hVis with rfl
        exact ⟨ha, hb, 0, PathN.zero a⟩
      · rcases List.mem_singleton.mp hc with rfl
        exact ⟨ha, hb, k, hpk⟩
  · rintro ⟨ha, hb, k, hpk⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    cases k with
    | zero =>
      cases hpk
      exact Or.inl rfl
    | succ k' =>
      obtain ⟨_, jb, _, hjb, hbound⟩ := pathN_index_bound hdag hpk hb
      have hjbLt := (nodeIdxAux_lt_length 0 s.commits b hjb).2
      have hcl : BfsClosed s [b] [b] := fun u hu hnf => absurd hu hnf
      have hsub : ∀ x ∈ ([b] : List CommitId), x ∈ ([b] : List CommitId) := fun _ hx => hx
      exact Or.inr (bfsAncestorsLoop_complete s s.commits.length [b] [b] hcl hsub hParentsHas
        List.mem_cons_self (by omega) hpk hb)

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

private theorem mergeBase_mem_commonAncestors_slow (s : RepoInstance) (a b m : CommitId)
    (h : Model.mergeBase? s a b = some m) :
    hasCommit s a = true ∧ hasCommit s b = true ∧
    m ∈ bfsAncestorsLoop s s.commits.length [a] [a] ∧
    m ∈ bfsAncestorsLoop s s.commits.length [b] [b] := by
  unfold Model.mergeBase? lowestCommonAncestors at h
  split at h
  · rcases foldl_min_mem _ none m h with hmem | hnone
    · have hmemCa := (List.mem_filter.mp hmem).1
      split at hmemCa
      · cases hmemCa
      · next hNot =>
        have ha : hasCommit s a = true := by cases h0 : hasCommit s a <;> simp_all
        have hb : hasCommit s b = true := by cases h0 : hasCommit s b <;> simp_all
        obtain ⟨hmA, hmB⟩ := List.mem_filter.mp hmemCa
        exact ⟨ha, hb, hmA, List.contains_iff_mem.mp hmB⟩
    · cases hnone
  · dsimp only at h
    split at h
    · simp at h
    · next hNot =>
      simp only [Bool.or_eq_true, Bool.not_eq_true', buildCommitParentsMap_contains] at hNot
      have ha : hasCommit s a = true := by cases h0 : hasCommit s a <;> simp_all
      have hb : hasCommit s b = true := by cases h0 : hasCommit s b <;> simp_all
      rcases foldl_min_mem _ none m h with hmem | hnone
      · have hmemCa := (List.mem_filter.mp hmem).1
        obtain ⟨hInFastA, hInSetB⟩ := List.mem_filter.mp hmemCa
        obtain ⟨hWFa, hContA⟩ := singleton_rawTreeSet_spec a
        have hEqA : bfsAncestorsFastLoop (buildCommitParentsMap s.commits) s.commits.length [a] [a]
            ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert a.hex) =
            bfsAncestorsLoop s s.commits.length [a] [a] :=
          bfsAncestorsFastLoop_eq s s.commits.length [a] [a] _ hWFa hContA
        obtain ⟨hWFb, hContB⟩ := singleton_rawTreeSet_spec b
        have hEqB : bfsAncestorsFastLoop (buildCommitParentsMap s.commits) s.commits.length [b] [b]
            ((Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).insert b.hex) =
            bfsAncestorsLoop s s.commits.length [b] [b] :=
          bfsAncestorsFastLoop_eq s s.commits.length [b] [b] _ hWFb hContB
        rw [hEqA] at hInFastA
        rw [hEqB] at hInSetB
        have ⟨_, hContReachB⟩ := rawTreeSet_foldl_insert_spec
          (bfsAncestorsLoop s s.commits.length [b] [b]) .empty Std.TreeSet.Raw.WF.empty
        have hEmpM : (Std.TreeSet.Raw.empty : Std.TreeSet.Raw String compare).contains m.hex = false := rfl
        rw [hContReachB m, hEmpM, Bool.or_false] at hInSetB
        exact ⟨ha, hb, hInFastA, List.contains_iff_mem.mp hInSetB⟩
      · cases hnone

/-- Standalone transitivity theorem for `Model.isAncestor` under `isValidRepoInstance`. -/
theorem proof_git_isAncestor_validRepoState_transitive {s : RepoInstance} (hValid : isValidRepoInstance s = true)
    {a b c : CommitId} (hab : Model.isAncestor s a b = true) (hbc : Model.isAncestor s b c = true) :
    Model.isAncestor s a c = true := by
  have hdag : validCommitDagAux [] s.commits = true := by
    unfold isValidRepoInstance at hValid
    simp only [Bool.and_eq_true] at hValid
    exact hValid.1.1.1.1.1
  obtain ⟨ha, _, k1, hk1⟩ := (isAncestor_eq_true_iff_pathN hdag).mp hab
  obtain ⟨_, hc, k2, hk2⟩ := (isAncestor_eq_true_iff_pathN hdag).mp hbc
  exact (isAncestor_eq_true_iff_pathN hdag).mpr ⟨ha, hc, k1 + k2, pathN_trans hk1 hk2⟩

/-- Standalone soundness theorem for `Model.mergeBase?` returning a common ancestor. -/
theorem proof_git_mergeBase_returns_commonAncestor {s : RepoInstance} {a b m : CommitId}
    (h : Model.mergeBase? s a b = some m) : Model.isAncestor s m a = true ∧ Model.isAncestor s m b = true := by
  obtain ⟨ha, hb, hmA, hmB⟩ := mergeBase_mem_commonAncestors_slow s a b m h
  have hmHasA : hasCommit s m = true := by
    rcases bfsAncestorsLoop_sound s s.commits.length [a] [a] m hmA with hHas | hVis
    · exact hHas
    · rcases List.mem_singleton.mp hVis with rfl; exact ha
  rw [isAncestor_eq_slow s m a, isAncestor_eq_slow s m b]
  simp only [ha, hb, hmHasA, Bool.true_and, Bool.and_true, Bool.or_eq_true, List.contains_iff_mem]
  exact ⟨Or.inr hmA, Or.inr hmB⟩

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
  let s : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    worktrees := [{ rootPath := "/repo".toUTF8, head := .detached c0 }]
  }
  have hValid : isValidRepoInstance s = true := by cbv
  exact ⟨s, c0, c0, c0, hValid,
    proof_git_model_isAncestor_transitiveAndMergeBaseValid s c0 c0 c0 hValid⟩

private theorem freshSyntheticCommitIdAux_not_hasCommit (s : RepoInstance) (idx remaining : Nat) :
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
theorem proof_git_freshSyntheticCommitId_not_hasCommit (s : RepoInstance) :
    hasCommit s (freshSyntheticCommitId s) = false :=
  freshSyntheticCommitIdAux_not_hasCommit s s.commits.length (s.commits.length + 1)


end LeanSwe.Git.Proofs

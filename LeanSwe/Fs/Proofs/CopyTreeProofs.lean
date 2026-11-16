import LeanSwe.Fs.Proofs.PurePathProofs
import LeanSwe.Fs.Proofs.VfsShared

namespace LeanSwe.Fs.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs
open LeanSwe.Fs.ProofsInternal

private theorem vfsResolveSegs_dir_child (nodes : String → Option VfsNode)
    (lastSeg parCanon : String) (parMode : Nat) (hExec : ((parMode / 64) % 2 == 0) = false)
    (hChild : nodes (vfsChildPath parCanon lastSeg) = some (.dir 0o755)) :
    ∀ fuel cur parSegs,
      vfsResolveSegs nodes cur parSegs true fuel = .ok (parCanon, .dir parMode) →
      vfsResolveSegs nodes cur (parSegs ++ [lastSeg]) true (fuel + 1) =
        .ok (vfsChildPath parCanon lastSeg, .dir 0o755) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; simp [vfsResolveSegs] at h
  | succ f ih =>
    intro cur parSegs hOk
    simp only [vfsResolveSegs] at hOk
    cases parSegs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir m =>
          simp only [Prod.mk.injEq, Except.ok.injEq, VfsNode.dir.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          simp only [List.nil_append, vfsResolveSegs, hNode, hExec, Bool.false_eq_true, ↓reduceIte, hChild]
        | symlink target m =>
          simp only [List.nil_append, vfsResolveSegs, hNode]
          exact ih "/" (vfsSplitSegs (Internal.normPath
            (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target))) hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir m =>
          by_cases he : ((m / 64) % 2 == 0) = true
          · simp [he] at hOk
          · have hef : ((m / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte] at hOk
            simp only [List.cons_append, vfsResolveSegs, hNode, hef, Bool.false_eq_true, ↓reduceIte]
            exact ih (vfsChildPath cur seg) rest hOk
        | symlink target m =>
          simp only [List.cons_append, vfsResolveSegs, hNode]
          have hAssoc : vfsSplitSegs (Internal.normPath
              (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target)) ++
              seg :: (rest ++ [lastSeg]) =
            (vfsSplitSegs (Internal.normPath
              (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target)) ++
              seg :: rest) ++ [lastSeg] := by
            simp [List.append_assoc]
          rw [hAssoc]
          exact ih "/" _ hOk


private theorem vfsTreeGet_set_emptyDir (m' : Nat) :
    ∀ (segs : List String) (lastSeg : String) (t : VfsTree) (q : List String),
      (∃ dm dch, vfsTreeGet t segs = some (.dir dm dch)) →
      vfsTreeGet t (segs ++ [lastSeg]) = none →
      (vfsTreeGet (vfsTreeSet t (segs ++ [lastSeg]) (some (vfsEmptyDir m'))) q).map vfsTreeTopNode =
        if q == (segs ++ [lastSeg]) then some (.dir m') else (vfsTreeGet t q).map vfsTreeTopNode := by
  intro segs
  induction segs with
  | nil =>
    intro lastSeg t q hDir hNone
    rcases hDir with ⟨dm, dch, hGet⟩
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir mode ch =>
      simp only [List.nil_append, vfsTreeSet]
      have hChNone : ch lastSeg = none := by
        cases hCl : ch lastSeg with
        | none => rfl
        | some sub => simp [vfsTreeGet, hCl] at hNone
      cases q with
      | nil => rfl
      | cons qh qt =>
        by_cases hEq : qh = lastSeg
        · subst hEq
          cases qt with
          | nil => simp [vfsTreeGet, vfsEmptyDir, vfsTreeTopNode]
          | cons rh rt =>
            simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte, vfsEmptyDir]
            simp [hChNone]
        · have hNe : (qh == lastSeg) = false := beq_false_of_ne hEq
          have hListNe : ((qh :: qt) == [lastSeg]) = false := by
            simp [hEq]
          simp [vfsTreeGet, hNe, hListNe]
  | cons seg rest ih =>
    intro lastSeg t q hDir hNone
    rcases hDir with ⟨dm, dch, hGet⟩
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir mode ch =>
      cases hCh : ch seg with
      | none => simp [vfsTreeGet, hCh] at hGet
      | some sub =>
        have hSubDir : ∃ dm dch, vfsTreeGet sub rest = some (.dir dm dch) := by
          refine ⟨dm, dch, ?_⟩
          simpa [vfsTreeGet, hCh] using hGet
        have hSubNone : vfsTreeGet sub (rest ++ [lastSeg]) = none := by
          simpa [vfsTreeGet, hCh] using hNone
        have hNonEmpty : rest ++ [lastSeg] ≠ [] := by simp
        cases hRest : rest ++ [lastSeg] with
        | nil => exact absurd hRest hNonEmpty
        | cons rhd rtl =>
          have hSetEq : vfsTreeSet (.dir mode ch) ((seg :: rest) ++ [lastSeg]) (some (vfsEmptyDir m')) =
              .dir mode (fun s => if s == seg then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) else ch s) := by
            simp only [List.cons_append, vfsTreeSet, hRest, hCh]
          rw [hSetEq]
          cases q with
          | nil => rfl
          | cons qh qt =>
            by_cases hEq : qh = seg
            · subst hEq
              have hIh := ih lastSeg sub qt hSubDir hSubNone
              have hLhs :
                  (vfsTreeGet (.dir mode fun s =>
                    if s == qh then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) else ch s) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) qt).map vfsTreeTopNode := by
                simp [vfsTreeGet]
              have hRhs :
                  (vfsTreeGet (.dir mode ch) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet sub qt).map vfsTreeTopNode := by
                simp [vfsTreeGet, hCh]
              have hCond : ((qh :: qt) == ((qh :: rest) ++ [lastSeg])) = (qt == (rest ++ [lastSeg])) := by
                simp [List.cons_append]
              rw [hLhs, hRhs, hCond, hIh]
            · have hNe : (qh == seg) = false := beq_false_of_ne hEq
              unfold vfsTreeGet
              simp [hNe]


private theorem vfsTreeNodes_insert_dir (t : VfsTree) (parCanon lastSeg : String)
    (hParCanon : isCanonPath parCanon = true)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hParDir : ∃ dm, vfsTreeNodes t parCanon = some (.dir dm))
    (hNewNone : vfsTreeNodes t (vfsChildPath parCanon lastSeg) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))) =
      fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else vfsTreeNodes t k := by
  have ⟨hChildCanon, hChildSp⟩ := vfsChildPath_valid parCanon lastSeg hParCanon hLastValid
  have hParTreeDir : ∃ dm dch, vfsTreeGet t (vfsSplitSegs parCanon) = some (.dir dm dch) := by
    rcases hParDir with ⟨dm, hPar⟩
    simp only [vfsTreeNodes, hParCanon, ↓reduceIte] at hPar
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon) with
    | none => simp [hGet] at hPar
    | some sub =>
      cases sub with
      | dir dm' dch => exact ⟨dm', dch, rfl⟩
      | file _ _ => simp [hGet, vfsTreeTopNode] at hPar
      | symlink _ _ => simp [hGet, vfsTreeTopNode] at hPar
  have hNewTreeNone : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) = none := by
    have hNn := hNewNone
    simp only [vfsTreeNodes, hChildCanon, ↓reduceIte, hChildSp] at hNn
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) with
    | none => rfl
    | some _ => simp [hGet] at hNn
  funext k
  by_cases hKCanon : isCanonPath k = true
  · simp only [vfsTreeNodes, hKCanon, ↓reduceIte, hChildSp]
    rw [vfsTreeGet_set_emptyDir 0o755 (vfsSplitSegs parCanon) lastSeg t (vfsSplitSegs k) hParTreeDir hNewTreeNone]
    by_cases hEq : k = vfsChildPath parCanon lastSeg
    · subst hEq
      simp [hChildSp]
    · have hBeqF : (k == vfsChildPath parCanon lastSeg) = false := beq_false_of_ne hEq
      have hSpNe : vfsSplitSegs k ≠ vfsSplitSegs parCanon ++ [lastSeg] := by
        intro heq
        apply hEq
        exact vfsSplitSegs_inj_canon k (vfsChildPath parCanon lastSeg) hKCanon hChildCanon (by simpa [hChildSp] using heq)
      have hSpBeqF : (vfsSplitSegs k == vfsSplitSegs parCanon ++ [lastSeg]) = false := beq_false_of_ne hSpNe
      simp [hBeqF, hSpBeqF]
  · have hKCanonF : isCanonPath k = false := Bool.eq_false_iff.mpr hKCanon
    have hKNe : k ≠ vfsChildPath parCanon lastSeg := fun h => by subst h; simp [hChildCanon] at hKCanonF
    have hBeqF : (k == vfsChildPath parCanon lastSeg) = false := beq_false_of_ne hKNe
    simp [vfsTreeNodes, hKCanonF, hBeqF]


private theorem vfsTreeNodes_set_preserves_none (t : VfsTree) (segs : List String) (lastSeg : String) (m' : Nat)
    (hDir : ∃ dm dch, vfsTreeGet t segs = some (.dir dm dch))
    (hNone : vfsTreeGet t (segs ++ [lastSeg]) = none) (q : String) (hq : vfsTreeNodes t q = none)
    (hQCanon : isCanonPath q = true) (hNe : vfsSplitSegs q ≠ segs ++ [lastSeg]) :
    vfsTreeNodes (vfsTreeSet t (segs ++ [lastSeg]) (some (vfsEmptyDir m'))) q = none := by
  simp only [vfsTreeNodes, hQCanon, ↓reduceIte] at hq ⊢
  rw [vfsTreeGet_set_emptyDir m' segs lastSeg t (vfsSplitSegs q) hDir hNone]
  have hBeqF : (vfsSplitSegs q == segs ++ [lastSeg]) = false := beq_false_of_ne hNe
  simp [hBeqF, hq]


private theorem vfsTreeSet_emptyDir_nodes_root_child (t : VfsTree) (child : String)
    (hPar : ∃ dm, vfsTreeNodes t "/" = some (.dir dm))
    (hValid : Internal.validFileName child = true)
    (hNone : vfsTreeNodes t (vfsChildPath "/" child) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath "/" child)) (some (vfsEmptyDir 0o755))) =
      fun k => if k == vfsChildPath "/" child then some (.dir 0o755) else vfsTreeNodes t k :=
  vfsTreeNodes_insert_dir t "/" child (by decide) hValid hPar hNone


private theorem vfsCreateDir_sets_isDir (path : String) (s₀ s₁ : VfsState)
    (hCreate : (vfsOps.createDir path).run s₀ = (.ok (), s₁)) :
    ((vfsApi.isDir path).run s₁).1 = .ok true := by
  dsimp only [vfsOps, vfsCreateDirPure, StateT.run] at hCreate
  cases hPre : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p =>
    simp only [hPre] at hCreate
    cases (congrArg Prod.fst hCreate)
  | error e =>
    simp only [hPre] at hCreate
    by_cases hNf : (e.kind != .notFound) = true
    · simp only [hNf, ↓reduceIte] at hCreate
      cases (congrArg Prod.fst hCreate)
    · have hNfFalse : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
      simp only [hNfFalse, Bool.false_eq_true, ↓reduceIte] at hCreate
      cases hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] with
      | none =>
        simp only [hSplit] at hCreate
        cases (congrArg Prod.fst hCreate)
      | some pair =>
        rcases pair with ⟨parSegs, lastSeg⟩
        simp only [hSplit] at hCreate
        cases hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 with
        | error pe =>
          simp only [hPar] at hCreate
          cases (congrArg Prod.fst hCreate)
        | ok parRes =>
          rcases parRes with ⟨parCanon, parNode⟩
          cases parNode with
          | file _ _ =>
            simp only [hPar] at hCreate
            cases (congrArg Prod.fst hCreate)
          | symlink _ _ =>
            simp only [hPar] at hCreate
            cases (congrArg Prod.fst hCreate)
          | dir parMode =>
            simp only [hPar] at hCreate
            by_cases hPerm : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = true
            · simp only [hPerm, ↓reduceIte] at hCreate
              cases (congrArg Prod.fst hCreate)
            · have hPermFalse : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false :=
                Bool.eq_false_iff.mpr hPerm
              have hExec : ((parMode / 64) % 2 == 0) = false := by
                cases hx : (parMode / 64) % 2 == 0 <;> simp_all
              simp only [hPermFalse, Bool.false_eq_true, ↓reduceIte] at hCreate
              cases hExisting : s₀.nodes (vfsChildPath parCanon lastSeg) with
              | some _ =>
                simp only [hExisting] at hCreate
                cases (congrArg Prod.fst hCreate)
              | none =>
                simp only [hExisting] at hCreate
                have hsEq : s₁ = { s₀ with
                    tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))
                    keys := vfsChildPath parCanon lastSeg :: s₀.keys } := (congrArg Prod.snd hCreate).symm
                subst hsEq
                have hAllSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd path) = parSegs ++ [lastSeg] := by
                  simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] parSegs lastSeg hSplit
                have hAllValid := vfsSplitSegs_normPath_valid (if Internal.isAbsolute path then path else Internal.join s₀.cwd path)
                have hParValid : ∀ s ∈ parSegs, Internal.validFileName s = true := fun s hs =>
                  hAllValid s (by rw [← vfsAbsNorm, hAllSegs]; simp [hs])
                have hLastValid : Internal.validFileName lastSeg = true :=
                  hAllValid lastSeg (by rw [← vfsAbsNorm, hAllSegs]; simp)
                have hParCanon : isCanonPath parCanon = true :=
                  vfsResolveSegs_isCanon s₀.nodes 512 "/" parSegs true (parCanon, .dir parMode) (by decide) hParValid hPar
                have hParLookup : s₀.nodes parCanon = some (.dir parMode) :=
                  vfsResolveSegs_ok_node s₀.nodes 512 "/" parSegs true parCanon (.dir parMode) hPar
                have hNodesEq :
                    ({ s₀ with
                        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))
                        keys := vfsChildPath parCanon lastSeg :: s₀.keys } : VfsState).nodes =
                      fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k := by
                  change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))) = _
                  exact vfsTreeNodes_insert_dir s₀.tree parCanon lastSeg hParCanon hLastValid ⟨parMode, hParLookup⟩ hExisting
                have hParNew := vfsResolveSegs_insert_fresh s₀.nodes (vfsChildPath parCanon lastSeg)
                  (.dir 0o755) hExisting 512 "/" parSegs true (parCanon, .dir parMode) hPar
                have hChildNew :
                    (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                      (vfsChildPath parCanon lastSeg) = some (.dir 0o755) := by
                  simp
                have hChildStep := vfsResolveSegs_dir_child
                  (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                  lastSeg parCanon parMode hExec hChildNew 512 "/" parSegs hParNew
                have h1024 := vfsResolveSegs_fuel_mono
                  (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                  513 1024 "/" (parSegs ++ [lastSeg]) true (vfsChildPath parCanon lastSeg, .dir 0o755)
                  (by omega) hChildStep
                rw [← hAllSegs] at h1024
                dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
                rw [hNodesEq, h1024]
                rfl


/-- Proof of `test_fs_vfs_mkdir_existingFails` on `vfsApi`. -/
theorem proof_fs_vfs_mkdir_existingFails :
    AllPass (test_fs_vfs_mkdir_existingFails vfsApi) := by
  intro s₀ path parents hOk
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hOk
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes, Except.isOk, Except.toBool] at hOk
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkdirImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩


private theorem vfsResolveSegs_root_dir (m : Nat) :
    vfsResolveSegs (fun k => if k == "/" then some (.dir m) else none) "/" [] true 512 = .ok ("/", .dir m) := by
  unfold vfsResolveSegs
  rfl


private theorem vfsLstat_broken_symlink :
    let st : VfsState :=
      { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
        keys := ["/", "/broken"]
        cwd := "/"
        nonce := 0 }
    ((vfsApi.lstat "/broken").run st).1.isOk = true := by
  intro st
  have hAbs : vfsAbsNorm "/" "/broken" = "/broken" := by decide
  have hSegs : vfsSplitSegs "/broken" = ["broken"] := by decide
  have hChild : vfsChildPath "/" "broken" = "/broken" := by decide
  have hCwd : st.cwd = "/" := rfl
  have hRes : vfsResolveSegs st.nodes "/" ["broken"] false 1024 = .ok ("/broken", .symlink "/nope" 0o777) := by
    unfold vfsResolveSegs
    have hRoot : st.nodes "/" = some (.dir 0o755) := rfl
    have hExec : ((0o755 / 64) % 2 == 0) = false := by decide
    rw [hRoot]
    dsimp only
    rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hChild]
    unfold vfsResolveSegs
    have hBrk : st.nodes "/broken" = some (.symlink "/nope" 0o777) := rfl
    rw [hBrk]
    rfl
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
  rw [hCwd, hAbs, hSegs, hRes]
  rfl


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_mkdir_existingFails`. -/
theorem reach_fs_vfs_mkdir_existingFails :
    CanReach (test_fs_vfs_mkdir_existingFails vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  exact ⟨st, "/broken", true, vfsLstat_broken_symlink, proof_fs_vfs_mkdir_existingFails st "/broken" true vfsLstat_broken_symlink⟩


/-- Proof of `test_fs_vfs_touch_existingFails` on `vfsApi`. -/
theorem proof_fs_vfs_touch_existingFails :
    AllPass (test_fs_vfs_touch_existingFails vfsApi) := by
  intro s₀ path hOk
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hOk
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes, Except.isOk, Except.toBool] at hOk
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only [vfsApi, Internal.mkApiM, Internal.touchImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.not_false, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_touch_existingFails`. -/
theorem reach_fs_vfs_touch_existingFails :
    CanReach (test_fs_vfs_touch_existingFails vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  exact ⟨st, "/broken", vfsLstat_broken_symlink, proof_fs_vfs_touch_existingFails st "/broken" vfsLstat_broken_symlink⟩


/-- Proof of `test_fs_vfs_walk_preservesStatError` on `vfsApi`. -/
theorem proof_fs_vfs_walk_preservesStatError :
    AllPass (test_fs_vfs_walk_preservesStatError vfsApi) := by
  intro s₀ root
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd root)) true 1024 with
  | error err =>
    dsimp only [vfsApi, Internal.mkApiM, Internal.walkImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp [Pure.pure, StateT.pure]
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only
    by_cases hNotDir : ((vfsToStat nd).kind != .dir) = true
    · simp only [hNotDir, ↓reduceIte]
      dsimp only [vfsApi, Internal.mkApiM, Internal.walkImplM, vfsOps, vfsStatPure, StateT.run,
        bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
      rw [hRes]
      simp only [hNotDir, ↓reduceIte, StateT.pure]
      exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
    · have hNotDirFalse : ((vfsToStat nd).kind != .dir) = false := Bool.eq_false_iff.mpr hNotDir
      simp only [hNotDirFalse, Bool.false_eq_true, ↓reduceIte]
      trivial


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_walk_preservesStatError` exercising `EACCES`. -/
theorem reach_fs_vfs_walk_preservesStatError :
    CanReach (test_fs_vfs_walk_preservesStatError vfsApi) := by
  let st : VfsState :=
    { tree := vfsEmptyDir 0o000
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  refine ⟨st, "/locked", ?_⟩
  exact proof_fs_vfs_walk_preservesStatError st "/locked"


private theorem mkdirImpl_parents_ok {S : Type} (ops : RawFsOpsM (StateM S)) (path : String) (s₀ : S)
    (hMk : ((Internal.mkdirImplM ops path true false).run s₀).1 = .ok ()) :
    ∃ s_mid,
      ((ops.createDir path).run s_mid).1 = .ok () ∧
      ((Internal.mkdirImplM ops path true false).run s₀).2 = ((ops.createDir path).run s_mid).2 := by
  dsimp only [Internal.mkdirImplM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hMk ⊢
  cases hPre : ops.stat false path s₀ with
  | mk resPre sPre =>
    rw [hPre] at hMk
    dsimp only at hMk ⊢
    cases resPre with
    | ok _ =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hMk
      cases hMk
    | error e =>
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte, StateT.pure] at hMk
        cases hMk
      · have hNfFalse : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfFalse, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hMk ⊢
        cases hAnc : Internal.ensureAncestorsM ops (Internal.ancestorChain path path.toList.length) sPre with
        | mk ancRes s_mid =>
          dsimp only [StateT.bind] at hMk ⊢
          rw [hAnc] at hMk ⊢
          cases ancRes with
          | error _ =>
            cases hMk
          | ok _ =>
            exact ⟨s_mid, hMk, rfl⟩


/-- Proof of `test_fs_vfs_mkdir_parentsCreatesDir` on `vfsApi`. -/
theorem proof_fs_vfs_mkdir_parentsCreatesDir :
    AllPass (test_fs_vfs_mkdir_parentsCreatesDir vfsApi) := by
  intro s₀ path hRes
  have hMk : ((Internal.mkdirImplM vfsOps path true false).run s₀).1 = .ok () := hRes
  rcases mkdirImpl_parents_ok vfsOps path s₀ hMk with ⟨s_mid, hCr, hSnd⟩
  dsimp only [assert]
  change ((vfsApi.isDir path).run ((Internal.mkdirImplM vfsOps path true false).run s₀).2).1 = .ok true ∧ True
  rw [hSnd]
  exact ⟨vfsCreateDir_sets_isDir path s_mid _ (Prod.ext hCr rfl), trivial⟩


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_mkdir_parentsCreatesDir`. -/
theorem reach_fs_vfs_mkdir_parentsCreatesDir :
    CanReach (test_fs_vfs_mkdir_parentsCreatesDir vfsApi) := by
  let st : VfsState :=
    { tree := vfsEmptyDir 0o755
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  let stA : VfsState :=
    { st with
      tree := vfsTreeSet st.tree (vfsSplitSegs "/a") (some (vfsEmptyDir 0o755))
      keys := "/a" :: st.keys }
  have hCwd : st.cwd = "/" := rfl
  have hPre : vfsStatPure st false "/a/b" =
      .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
    have hAbs : vfsAbsNorm "/" "/a/b" = "/a/b" := by decide
    have hSegs : vfsSplitSegs "/a/b" = ["a", "b"] := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    dsimp only [vfsStatPure]
    rw [hCwd, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
    unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
    rfl
  have hStatA : vfsStatPure st true "/a" =
      .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
    have hAbs : vfsAbsNorm "/" "/a" = "/a" := by decide
    have hSegs : vfsSplitSegs "/a" = ["a"] := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    dsimp only [vfsStatPure]
    rw [hCwd, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
    unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
    rfl
  have hCreA : vfsCreateDirPure st "/a" = (.ok (), stA) := by
    have hAbs : vfsAbsNorm "/" "/a" = "/a" := by decide
    have hSegs : vfsSplitSegs "/a" = ["a"] := by decide
    have hPar : Internal.splitLastAux ["a"] [] = some ([], "a") := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    have hPreA : vfsResolveSegs st.nodes "/" ["a"] false 1024 =
        .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
      rfl
    have hRootA : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
    dsimp only [vfsCreateDirPure]
    rw [hCwd, hAbs, hSegs, hPreA]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]
    dsimp only
    rw [hRootA]
    dsimp only
    rw [hC1, show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show st.nodes "/a" = none from rfl]
  have hAnc : Internal.ensureAncestorsM vfsOps ["/a"] st = (.ok (), stA) := by
    dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat true "/a" st = (vfsStatPure st true "/a", st) from rfl, hStatA]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.bind]
    rw [show vfsOps.createDir "/a" st = vfsCreateDirPure st "/a" from rfl, hCreA]
    rfl
  have hCreB : ((vfsOps.createDir "/a/b").run stA).1 = .ok () := by
    have hAbs : vfsAbsNorm "/" "/a/b" = "/a/b" := by decide
    have hSegs : vfsSplitSegs "/a/b" = ["a", "b"] := by decide
    have hPar : Internal.splitLastAux ["a", "b"] [] = some (["a"], "b") := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    have hC2 : vfsChildPath "/a" "b" = "/a/b" := by decide
    have hCwdA : stA.cwd = "/" := rfl
    have hPreB : vfsResolveSegs stA.nodes "/" ["a", "b"] false 1024 =
        .error { kind := .notFound, path := some "/a/b", message := "no such file or directory: /a/b" } := by
      unfold vfsResolveSegs; rw [show stA.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show stA.nodes "/a" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC2]
      unfold vfsResolveSegs; rw [show stA.nodes "/a/b" = none from rfl]
      rfl
    have hParB : vfsResolveSegs stA.nodes "/" ["a"] true 512 = .ok ("/a", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show stA.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show stA.nodes "/a" = some (.dir 0o755) from rfl]
    dsimp only [vfsOps, vfsCreateDirPure, StateT.run]
    rw [hCwdA, hAbs, hSegs, hPreB]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]
    dsimp only
    rw [hParB]
    dsimp only
    rw [hC2, show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show stA.nodes "/a/b" = none from rfl]
  have hChain : Internal.ancestorChain "/a/b" "/a/b".toList.length = ["/a"] := by decide
  have hMk : ((vfsApi.mkdir "/a/b" true false).run st).1 = .ok () := by
    change ((Internal.mkdirImplM vfsOps "/a/b" true false).run st).1 = .ok ()
    dsimp only [Internal.mkdirImplM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/a/b" st = (vfsStatPure st false "/a/b", st) from rfl, hPre]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [hChain, show StateT.bind (Internal.ensureAncestorsM vfsOps ["/a"]) = fun k s =>
      match Internal.ensureAncestorsM vfsOps ["/a"] s with | (a, s') => k a s' from rfl]
    dsimp only
    rw [hAnc]
    exact hCreB
  exact ⟨st, "/a/b", hMk, proof_fs_vfs_mkdir_parentsCreatesDir st "/a/b" hMk⟩


private theorem joinSlashChars_last_not_slash :
    ∀ xs : List (List Char), xs ≠ [] → (∀ s ∈ xs, !s.isEmpty ∧ '/' ∉ s) →
      ('/' :: Internal.joinSlashChars xs).getLast? ≠ some '/' := by
  intro xs hne hvalid
  induction xs with
  | nil => exact absurd rfl hne
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [Internal.joinSlashChars]
      rcases hHd : hd.reverse with _ | ⟨c, _⟩
      · have : hd = [] := by simpa using congrArg List.reverse hHd
        have hv := (hvalid hd (by simp)).1
        simp [this] at hv
      · have hC : c ∈ hd := by
          have : c ∈ hd.reverse := by rw [hHd]; simp
          exact List.mem_reverse.mp this
        have hNoSlash : '/' ∉ hd := (hvalid hd (by simp)).2
        have hLast : ('/' :: hd).getLast? = some c := by
          have hHdLast : hd.getLast? = some c := by
            rw [← List.head?_reverse, hHd]; rfl
          rw [List.getLast?_cons, hHdLast]
          rfl
        rw [hLast]
        intro heq
        cases heq
        exact hNoSlash hC
    | cons b bs =>
      have ih' := ih (by simp) (fun s hs => hvalid s (by simp [hs]))
      simp only [Internal.joinSlashChars]
      have hApp : ('/' :: (hd ++ '/' :: Internal.joinSlashChars (b :: bs))).getLast? =
          ('/' :: Internal.joinSlashChars (b :: bs)).getLast? := by
        change (('/' :: hd) ++ ('/' :: Internal.joinSlashChars (b :: bs))).getLast? =
          ('/' :: Internal.joinSlashChars (b :: bs)).getLast?
        exact list_getLast?_append ('/' :: hd) ('/' :: Internal.joinSlashChars (b :: bs)) (by simp)
      rw [hApp]
      exact ih'


private theorem join_vfsChildPath (c child : String)
    (hc : isCanonPath c = true) (hcNe : c ≠ "/") (hchild : Internal.validFileName child = true) :
    Internal.join c child = c ++ "/" ++ child := by
  obtain ⟨hCEq, hParts⟩ := isCanonPath_normPath_parts c hc
  have hChildL := validFileName_charList child hchild
  have hNotAbs : Internal.isAbsolute child = false := by
    unfold Internal.isAbsolute
    cases hList : child.toList with
    | nil => rfl
    | cons ch _ =>
      by_cases hSl : ch = '/'
      · subst hSl
        exfalso
        exact hChildL.2.2.1 (by rw [hList]; simp)
      · unfold Internal.isAbsChars; simp [hSl]
  have hPartsNe : (vfsSplitSegs c).map String.toList ≠ [] := by
    intro hEmp
    cases hSp : vfsSplitSegs c with
    | nil =>
      have : c = "/" := by rw [hCEq, hSp]; rfl
      exact hcNe this
    | cons _ _ => simp [hSp] at hEmp
  have hCNeEmpty : c ≠ "" := by
    intro h
    have hToL : c.toList = [] := by simp [h]
    rw [hCEq] at hToL
    simp at hToL
  have hCNotEmpty : c.isEmpty = false := by
    cases he : c.isEmpty
    · rfl
    · exfalso; exact hCNeEmpty (by simpa [String.isEmpty] using he)
  have hNotEnd : (c.toList.getLast? == some '/') = false := by
    have hGl := joinSlashChars_last_not_slash ((vfsSplitSegs c).map String.toList) hPartsNe
      (fun s hs => ⟨(hParts s hs).1, (hParts s hs).2.2.1⟩)
    rw [hCEq, String.toList_ofList]
    exact beq_false_of_ne hGl
  simp [Internal.join, hNotAbs, hCNotEmpty, hNotEnd]


private theorem vfsResolveSegs_abs_root_realPath (s₀ : VfsState) (stRoot : FileStat)
    (hStat : ((vfsApi.stat "/").run s₀).1 = .ok stRoot)
    (hKind : stRoot.kind = .dir)
    (hRes : ((vfsApi.resolve "/").run s₀).1 = .ok "/") :
    s₀.nodes "/" = some (.dir stRoot.mode) := by
  have hAbs : vfsAbsNorm s₀.cwd "/" = "/" := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hSegs : vfsSplitSegs "/" = [] := by decide
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hRes
  rw [hAbs, hSegs] at hRes
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStat
  rw [hAbs, hSegs] at hStat
  cases hR : vfsResolveSegs s₀.nodes "/" [] true 1024 with
  | error _ => simp [hR] at hRes
  | ok p =>
    rcases p with ⟨canon, nd⟩
    simp only [hR, Except.ok.injEq] at hRes hStat
    subst hRes
    have hNode := vfsResolveSegs_ok_node s₀.nodes 1024 "/" [] true "/" nd hR
    cases nd with
    | dir m =>
      have : stRoot.mode = m := by rw [← hStat]; rfl
      subst this; exact hNode
    | file _ _ => rw [← hStat] at hKind; simp [vfsToStat] at hKind
    | symlink _ _ => rw [← hStat] at hKind; simp [vfsToStat] at hKind


private theorem vfsTree_noOrphan_child (t : VfsTree) (hNone : vfsTreeNodes t "/new_parent" = none) :
    vfsTreeNodes t "/new_parent/copy" = none := by
  have hC1 : isCanonPath "/new_parent" = true := by decide
  have hC2 : isCanonPath "/new_parent/copy" = true := by decide
  have hS1 : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
  have hS2 : vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] := by decide
  simp only [vfsTreeNodes, hC1, hC2, ↓reduceIte, hS1, hS2] at hNone ⊢
  cases t with
  | file _ _ => rfl
  | symlink _ _ => rfl
  | dir m ch =>
    simp only [vfsTreeGet] at hNone ⊢
    cases hCh : ch "new_parent" with
    | none => rfl
    | some _ => simp [hCh] at hNone


private theorem copyTree_selfCopyRejected_exec (s₀ : VfsState) (src dst : String)
    (st : FileStat) (hStat : ((vfsApi.stat src).run s₀).1 = .ok st) (hKind : st.kind = .dir)
    (c : String) (hResSrc : ((vfsApi.resolve src).run s₀).1 = .ok c)
    (hCAbs : vfsApi.isAbsolute c = true) (hCNeRoot : c ≠ "/")
    (hResC : ((vfsApi.resolve c).run s₀).1 = .ok c)
    (hDstCase : dst = c ∨ ∃ child, (!child.isEmpty) = true ∧ (!decide ('/' ∈ child.toList)) = true ∧
      (child != ".") = true ∧ (child != "..") = true ∧ dst = c ++ "/" ++ child ∧ ((vfsApi.resolve dst).run s₀).1.isOk = false) :
    ∃ e, (vfsApi.copyTree src dst false).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput := by
  have hAllValid := vfsSplitSegs_normPath_valid (if Internal.isAbsolute src then src else Internal.join s₀.cwd src)
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hResSrc
  cases hRS : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd src)) true 1024 with
  | error _ => simp [hRS] at hResSrc
  | ok rp =>
    rcases rp with ⟨c', nd'⟩
    simp only [hRS, Except.ok.injEq] at hResSrc
    have hCCanon : isCanonPath c = true := by
      subst hResSrc
      exact vfsResolveSegs_isCanon s₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd src)) true (c', nd')
        (by decide) hAllValid hRS
    have hCNorm : Internal.normPath c = c := by
      have hAnd : (Internal.isAbsolute c && (Internal.normPath c == c)) = true := hCCanon
      exact beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hAnd).2
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStat
    dsimp only [vfsApi, Internal.mkApiM, Internal.copyTreeImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    change (match (vfsStatPure s₀ true src, s₀) with | (a, s) => _)
    have hStatP : vfsStatPure s₀ true src = .ok st := hStat
    rw [hStatP]
    have hNotDirF : (st.kind != .dir) = false := by rw [hKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hRpSrc : vfsRealPathPure s₀ src = .ok c := by
      dsimp only [vfsRealPathPure]
      rw [hRS, hResSrc]
    rw [hRpSrc]
    dsimp only
    cases hDstCase with
    | inl hEqDst =>
      subst hEqDst
      have hAbsC : Internal.isAbsolute dst = true := hCAbs
      simp only [hAbsC, ↓reduceIte, hCNorm]
      cases hL : dst.toList.length + 1 with
      | zero => omega
      | succ fuel =>
        unfold Internal.resolveApproxGoM
        dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
        rw [show vfsOps.realPath dst s₀ = (vfsRealPathPure s₀ dst, s₀) from rfl]
        have hRpC : vfsRealPathPure s₀ dst = .ok dst := hResC
        rw [hRpC]
        simp only [List.foldl_nil]
        dsimp only [StateT.pure, Pure.pure, pure]
        rw [show (dst == dst || dst == "/" || (dst.toList ++ ['/']).isPrefixOf dst.toList) = true from by simp]
        simp only [↓reduceIte]
        exact ⟨_, rfl, rfl⟩
    | inr hSub =>
      rcases hSub with ⟨child, hChNeEmpty, hChNoSlash, hChNeDot, hChNeDotDot, hDstEq, hResDstBad⟩
      subst hDstEq
      have hChNoSlashP : '/' ∉ child.toList := by simpa using hChNoSlash
      have hChListNe : (!child.toList.isEmpty) = true := by
        cases hcL : child.toList with
        | nil =>
          have hE : child = "" := by rw [← String.ofList_toList (s := child), hcL]
          rw [hE] at hChNeEmpty; cases hChNeEmpty
        | cons _ _ => rfl
      have hChListDot : (child.toList != ['.']) = true := bne_iff_ne.mpr fun heq => by
        have hE : child = "." := by rw [← String.ofList_toList (s := child), heq]
        rw [hE] at hChNeDot; cases hChNeDot
      have hChListDotDot : (child.toList != ['.', '.']) = true := bne_iff_ne.mpr fun heq => by
        have hE : child = ".." := by rw [← String.ofList_toList (s := child), heq]
        rw [hE] at hChNeDotDot; cases hChNeDotDot
      have hChValid : Internal.validFileName child = true := by
        simp only [Internal.validFileName, Bool.and_eq_true]
        exact ⟨⟨⟨hChListNe, by simpa using hChNoSlashP⟩, hChListDot⟩, hChListDotDot⟩
      have ⟨hParDst, hNameDst⟩ := parent_name_vfsChildPath c child hCCanon hCNeRoot hChValid
      have hBeqRootF : (c == "/") = false := beq_false_of_ne hCNeRoot
      have hChildV : vfsChildPath c child = c ++ "/" ++ child := by simp [vfsChildPath, hBeqRootF]
      have ⟨hDstCanon, _⟩ := hChildV ▸ vfsChildPath_valid c child hCCanon hChValid
      have hDstAnd : (Internal.isAbsolute (c ++ "/" ++ child) && (Internal.normPath (c ++ "/" ++ child) == (c ++ "/" ++ child))) = true := hDstCanon
      have hDstPair := Bool.and_eq_true _ _ |>.mp hDstAnd
      have hDstAbs : Internal.isAbsolute (c ++ "/" ++ child) = true := hDstPair.1
      have hDstNorm : Internal.normPath (c ++ "/" ++ child) = c ++ "/" ++ child := beq_iff_eq.mp hDstPair.2
      have hCLenPos : 0 < c.toList.length := by
        have hCAbs' : Internal.isAbsolute c = true := hCAbs
        cases hCl : c.toList with
        | nil => rw [Internal.isAbsolute] at hCAbs'; rw [hCl] at hCAbs'; cases hCAbs'
        | cons _ _ => simp
      have hChildLenPos : 0 < child.toList.length := by
        cases hCl : child.toList with
        | nil =>
          have hE : child = "" := by rw [← String.ofList_toList (s := child), hCl]
          rw [hE] at hChNeEmpty; cases hChNeEmpty
        | cons _ _ => simp
      have hFuel2 : ∃ k, (c ++ "/" ++ child).toList.length + 1 = k + 2 := by
        have hLen : (c ++ "/" ++ child).toList.length = c.toList.length + 1 + child.toList.length := by
          rw [String.toList_append, String.toList_append, List.length_append, List.length_append,
              show "/".toList = ['/'] by decide, List.length_singleton]
        exact ⟨c.toList.length + child.toList.length, by omega⟩
      rcases hFuel2 with ⟨k, hFuelEq⟩
      simp only [hDstAbs, ↓reduceIte, hDstNorm]
      dsimp only [Bind.bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [hFuelEq]
      unfold Internal.resolveApproxGoM
      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.realPath (c ++ "/" ++ child) s₀ = (vfsRealPathPure s₀ (c ++ "/" ++ child), s₀) from rfl]
      have hErrDst : ∃ err, vfsRealPathPure s₀ (c ++ "/" ++ child) = .error err := by
        cases hRd : vfsRealPathPure s₀ (c ++ "/" ++ child) with
        | ok _ =>
          have : ((vfsApi.resolve (c ++ "/" ++ child)).run s₀).1.isOk = true := by
            change (vfsRealPathPure s₀ (c ++ "/" ++ child)).isOk = true
            rw [hRd]; rfl
          simp [this] at hResDstBad
        | error e => exact ⟨e, rfl⟩
      rcases hErrDst with ⟨err, hRd⟩
      rw [hRd]
      dsimp only
      rw [hParDst, hNameDst]
      dsimp only
      unfold Internal.resolveApproxGoM
      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.realPath c s₀ = (vfsRealPathPure s₀ c, s₀) from rfl]
      have hRpC : vfsRealPathPure s₀ c = .ok c := hResC
      rw [hRpC]
      simp only [List.foldl_cons, List.foldl_nil, join_vfsChildPath c child hCCanon hCNeRoot hChValid]
      have hPref : (c.toList ++ ['/']).isPrefixOf (c ++ "/" ++ child).toList = true := by
        apply List.isPrefixOf_iff_prefix.mpr
        refine ⟨child.toList, ?_⟩
        rw [String.toList_append, String.toList_append, show "/".toList = ['/'] by decide, List.append_assoc]
      have hCondTrue : (c ++ "/" ++ child == c || c == "/" || (c.toList ++ ['/']).isPrefixOf (c ++ "/" ++ child).toList) = true := by
        simp only [hPref, Bool.or_true]
      dsimp only [StateT.pure, Pure.pure, pure]
      rw [hCondTrue]
      simp only [↓reduceIte]
      exact ⟨_, rfl, rfl⟩


/-- Proof of `test_fs_vfs_copyTree_selfCopyRejected` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_selfCopyRejected :
    AllPass (test_fs_vfs_copyTree_selfCopyRejected vfsApi) := by
  intro s₀ src dst ⟨st, hStat, hKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hResC, hDstCase⟩
  rcases copyTree_selfCopyRejected_exec s₀ src dst st hStat hKind c hResSrc hCAbs hCNeRoot hResC hDstCase with ⟨e, hEq, hEk⟩
  rw [hEq]
  exact ⟨⟨⟨e, rfl, hEk⟩, rfl⟩, trivial⟩


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_selfCopyRejected`. -/
theorem reach_fs_vfs_copyTree_selfCopyRejected :
    CanReach (test_fs_vfs_copyTree_selfCopyRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    have hAbs : vfsAbsNorm "/" "/src" = "/src" := by decide
    have hSegs : vfsSplitSegs "/src" = ["src"] := by decide
    have hChild : vfsChildPath "/" "src" = "/src" := by decide
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hChild]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    have hAbs : vfsAbsNorm "/" "/src" = "/src" := by decide
    have hSegs : vfsSplitSegs "/src" = ["src"] := by decide
    have hChild : vfsChildPath "/" "src" = "/src" := by decide
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hChild]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  exact ⟨st, "/src", "/src",
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, hResSrc, Or.inl rfl⟩,
    proof_fs_vfs_copyTree_selfCopyRejected st "/src" "/src"
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, hResSrc, Or.inl rfl⟩⟩


private theorem not_prefix_new_parent_copy (c : String)
    (hAbs : Internal.isAbsolute c = true) (hNe2 : c ≠ "/new_parent") :
    (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList = false := by
  by_cases hPref : (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList = true
  · exfalso
    have hP := List.isPrefixOf_iff_prefix.mp hPref
    rcases hP with ⟨tail, hEq⟩
    cases hCl : c.toList with
    | nil => simp [Internal.isAbsolute, Internal.isAbsChars, hCl] at hAbs
    | cons c0 cs =>
      have hC0 : c0 = '/' := by
        have hI : Internal.isAbsChars (c0 :: cs) = true := hCl ▸ hAbs
        cases hEqS : (c0 == '/') with
        | true => exact beq_iff_eq.mp hEqS
        | false =>
          exfalso
          have : Internal.isAbsChars (c0 :: cs) = false := by
            unfold Internal.isAbsChars
            split
            · next h => cases h; simp at hEqS
            · rfl
          simp [this] at hI
      subst hC0
      have hTarget : "/new_parent/copy".toList = '/' :: "new_parent/copy".toList := by decide
      rw [hCl, hTarget, List.append_assoc] at hEq
      simp only [List.cons_append, List.cons.injEq, true_and] at hEq
      have hLen : cs.length < 15 := by
        have hL := congrArg List.length hEq
        simp at hL
        omega
      have hAt : ("new_parent/copy".toList[cs.length]! == '/') = true := by
        have hIdx : (cs ++ '/' :: tail)[cs.length]! = "new_parent/copy".toList[cs.length]! :=
          congrArg (fun l : List Char => l[cs.length]!) hEq
        have hSlash : (cs ++ '/' :: tail)[cs.length]! = '/' := by simp
        rw [← hIdx, hSlash]
        rfl
      have hOnly : ∀ i : Fin 15, ("new_parent/copy".toList[i.val]! == '/') = true → i.val = 10 := by decide
      have hCsLen : cs.length = 10 := hOnly ⟨cs.length, hLen⟩ hAt
      have hTake : (cs ++ '/' :: tail).take 10 = "new_parent/copy".toList.take 10 :=
        congrArg (List.take 10) hEq
      have hCsEq : cs = "new_parent".toList := by
        have hTakeL : (cs ++ '/' :: tail).take cs.length = cs := by simp
        have hTakeR : "new_parent/copy".toList.take 10 = "new_parent".toList := by decide
        rw [← hCsLen, hTakeL] at hTake
        rw [← hCsLen] at hTakeR
        exact hTake.trans hTakeR
      apply hNe2
      apply String.ext_iff.mpr
      rw [hCl, hCsEq]
      decide
  · exact Bool.eq_false_iff.mpr hPref


private theorem not_prefix_loop_dst (c : String)
    (hAbs : Internal.isAbsolute c = true) :
    (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList = false := by
  by_cases hPref : (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList = true
  · exfalso
    have hP := List.isPrefixOf_iff_prefix.mp hPref
    rcases hP with ⟨tail, hEq⟩
    cases hCl : c.toList with
    | nil => simp [Internal.isAbsolute, Internal.isAbsChars, hCl] at hAbs
    | cons c0 cs =>
      have hC0 : c0 = '/' := by
        have hI : Internal.isAbsChars (c0 :: cs) = true := hCl ▸ hAbs
        cases hEqS : (c0 == '/') with
        | true => exact beq_iff_eq.mp hEqS
        | false =>
          exfalso
          have : Internal.isAbsChars (c0 :: cs) = false := by
            unfold Internal.isAbsChars
            split
            · next h => cases h; simp at hEqS
            · rfl
          simp [this] at hI
      subst hC0
      have hTarget : "/loop_dst".toList = '/' :: "loop_dst".toList := by decide
      rw [hCl, hTarget, List.append_assoc] at hEq
      simp only [List.cons_append, List.cons.injEq, true_and] at hEq
      have hMem : '/' ∈ "loop_dst".toList := by
        rw [← hEq]; simp
      have hNotMem : '/' ∉ "loop_dst".toList := by decide
      exact hNotMem hMem
  · exact Bool.eq_false_iff.mpr hPref


private theorem lstat_root_child_none (s₀ : VfsState) (m : Nat) (seg : String)
    (hRoot : s₀.nodes "/" = some (.dir m))
    (hExec : ((m / 64) % 2 == 0) = false)
    (hSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd ("/" ++ seg)) = [seg])
    (hChild : vfsChildPath "/" seg = "/" ++ seg)
    (hFail : ((vfsApi.lstat ("/" ++ seg)).run s₀).1.isOk = false) :
    s₀.nodes ("/" ++ seg) = none := by
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hFail
  rw [hSegs] at hFail
  cases hN : s₀.nodes ("/" ++ seg) with
  | none => rfl
  | some nd =>
    have hStep : vfsResolveSegs s₀.nodes "/" [seg] false 1024 = .ok ("/" ++ seg, nd) := by
      unfold vfsResolveSegs
      rw [hRoot]
      dsimp only
      rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, hChild]
      unfold vfsResolveSegs
      rw [hN]
      cases nd <;> rfl
    rw [hStep] at hFail
    simp [Except.isOk, Except.toBool] at hFail


private theorem copyTree_pre_checks_ok {S : Type} (ops : RawFsOpsM (StateM S))
    (src dst : String) (dirsExistOk : Bool) (s₀ : S) (stSrc : FileStat) (c dstCanon : String)
    (hStat : (ops.stat true src).run s₀ = (.ok stSrc, s₀))
    (hKind : stSrc.kind = .dir)
    (hRp : (ops.realPath src).run s₀ = (.ok c, s₀))
    (hAbsDst : Internal.isAbsolute dst = true)
    (hNormDst : Internal.normPath dst = dst)
    (hApprox : (Internal.resolveApproxGoM ops dst [] (dst.toList.length + 1)).run s₀ = (dstCanon, s₀))
    (hGuard : (dstCanon == c || c == "/" || (c.toList ++ ['/']).isPrefixOf dstCanon.toList) = false) :
    (Internal.copyTreeImplM ops src dst dirsExistOk).run s₀ =
      (Internal.copyTreeGoM ops src dst dirsExistOk [] 4096).run s₀ := by
  dsimp only [Internal.copyTreeImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  rw [show ops.stat true src s₀ = (ops.stat true src).run s₀ from rfl, hStat]
  have hNotDirF : (stSrc.kind != .dir) = false := by rw [hKind]; decide
  simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
  dsimp only [Bind.bind, StateT.bind, StateT.pure]
  rw [show ops.realPath src s₀ = (ops.realPath src).run s₀ from rfl, hRp]
  simp only [hAbsDst, ↓reduceIte, hNormDst]
  dsimp only [Bind.bind, StateT.bind, Pure.pure, pure, StateT.pure]
  dsimp only [StateT.run] at hApprox
  rw [hApprox]
  simp [hGuard]


/-- Proof of `test_fs_vfs_copyTree_createsMissingParents` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_createsMissingParents :
    AllPass (test_fs_vfs_copyTree_createsMissingParents vfsApi) := by
  intro s₀ src ⟨stRoot, hStatRoot, hRootKind, hRootW, hRootX, hResRoot⟩
    ⟨stSrc, hStatSrc, hSrcKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hCNeNP, hCNeCopy⟩
    hListSrc hLstatNP hStatNP hLstatCopy
  have hRootNode : s₀.nodes "/" = some (.dir stRoot.mode) :=
    vfsResolveSegs_abs_root_realPath s₀ stRoot hStatRoot hRootKind hResRoot
  have hExec : ((stRoot.mode / 64) % 2 == 0) = false := by
    have : (stRoot.mode / 64) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hWrite : ((stRoot.mode / 128) % 2 == 0) = false := by
    have : (stRoot.mode / 128) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hSegsNP : vfsSplitSegs (vfsAbsNorm s₀.cwd "/new_parent") = ["new_parent"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hNPNone : s₀.nodes "/new_parent" = none :=
    lstat_root_child_none s₀ stRoot.mode "new_parent" hRootNode hExec hSegsNP (by decide) hLstatNP
  have hCopyNone : s₀.nodes "/new_parent/copy" = none :=
    vfsTree_noOrphan_child s₀.tree hNPNone
  have hRpNPBad : vfsRealPathPure s₀ "/new_parent" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsNP]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hSegsCopy : vfsSplitSegs (vfsAbsNorm s₀.cwd "/new_parent/copy") = ["new_parent", "copy"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hStatCopyBad : vfsStatPure s₀ false "/new_parent/copy" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsStatPure]
    rw [hSegsCopy]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hRpCopyBad : vfsRealPathPure s₀ "/new_parent/copy" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsCopy]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hParCopy : Internal.parent "/new_parent/copy" = some "/new_parent" := by decide
  have hNameCopy : Internal.name "/new_parent/copy" = some "copy" := by decide
  have hParNP : Internal.parent "/new_parent" = some "/" := by decide
  have hNameNP : Internal.name "/new_parent" = some "new_parent" := by decide
  have hApprox : (Internal.resolveApproxGoM vfsOps "/new_parent/copy" [] ("/new_parent/copy".toList.length + 1)).run s₀ =
      ("/new_parent/copy", s₀) := by
    rw [show ("/new_parent/copy".toList.length + 1) = 17 from by decide]
    unfold Internal.resolveApproxGoM
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/new_parent/copy" s₀ = (vfsRealPathPure s₀ "/new_parent/copy", s₀) from rfl, hRpCopyBad]
    dsimp only; rw [hParCopy, hNameCopy]; dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/new_parent" s₀ = (vfsRealPathPure s₀ "/new_parent", s₀) from rfl, hRpNPBad]
    dsimp only; rw [hParNP, hNameNP]; dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hRpR : vfsRealPathPure s₀ "/" = .ok "/" := hResRoot
    rw [show vfsOps.realPath "/" s₀ = (vfsRealPathPure s₀ "/", s₀) from rfl, hRpR]
    simp only [List.foldl_cons, List.foldl_nil]
    rfl
  have hGuard : ("/new_parent/copy" == c || c == "/" || (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList) = false := by
    have h1 : ("/new_parent/copy" == c) = false := beq_false_of_ne (Ne.symm hCNeCopy)
    have h2 : (c == "/") = false := beq_false_of_ne hCNeRoot
    have h3 := not_prefix_new_parent_copy c hCAbs hCNeNP
    simp only [h1, h2, h3, Bool.or_false]
  have hStatS0 : (vfsOps.stat true src).run s₀ = (.ok stSrc, s₀) := by
    change (vfsStatPure s₀ true src, s₀) = (.ok stSrc, s₀)
    rw [show vfsStatPure s₀ true src = .ok stSrc from hStatSrc]
  have hRpS0 : (vfsOps.realPath src).run s₀ = (.ok c, s₀) := by
    change (vfsRealPathPure s₀ src, s₀) = (.ok c, s₀)
    rw [show vfsRealPathPure s₀ src = .ok c from hResSrc]
  have hPre := copyTree_pre_checks_ok vfsOps src "/new_parent/copy" false s₀ stSrc c "/new_parent/copy"
    hStatS0 hSrcKind hRpS0 (by decide) (by decide) hApprox hGuard
  let st₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree ["new_parent"] (some (vfsEmptyDir 0o755))
      keys := "/new_parent" :: s₀.keys }
  let st₂ : VfsState :=
    { st₁ with
      tree := vfsTreeSet st₁.tree ["new_parent", "copy"] (some (vfsEmptyDir 0o755))
      keys := "/new_parent/copy" :: st₁.keys }
  have hSt1Nodes : st₁.nodes = fun k => if k == "/new_parent" then some (.dir 0o755) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" "new_parent")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeSet_emptyDir_nodes_root_child s₀.tree "new_parent" ⟨stRoot.mode, hRootNode⟩ (by decide) hNPNone
  have hSt1Root : st₁.nodes "/" = some (.dir stRoot.mode) := by
    rw [hSt1Nodes]; simp [hRootNode]
  have hSt1NP : st₁.nodes "/new_parent" = some (.dir 0o755) := by
    rw [hSt1Nodes]; simp
  have hSt1CopyNone : st₁.nodes "/new_parent/copy" = none := by
    rw [hSt1Nodes]; simp [hCopyNone]
  have hSt2Nodes : st₂.nodes = fun k => if k == "/new_parent/copy" then some (.dir 0o755) else st₁.nodes k := by
    change vfsTreeNodes (vfsTreeSet st₁.tree (vfsSplitSegs (vfsChildPath "/new_parent" "copy")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeNodes_insert_dir st₁.tree "/new_parent" "copy" (by decide) (by decide) ⟨0o755, hSt1NP⟩ hSt1CopyNone
  have hCreNP : vfsCreateDirPure s₀ "/new_parent" = (.ok (), st₁) := by
    have hAbs : vfsAbsNorm s₀.cwd "/new_parent" = "/new_parent" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["new_parent"] [] = some ([], "new_parent") := by decide
    have hPreNP : vfsResolveSegs s₀.nodes "/" ["new_parent"] false 1024 =
        .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hNPNone]; rfl
    have hParRoot : vfsResolveSegs s₀.nodes "/" [] true 512 = .ok ("/", .dir stRoot.mode) := by
      unfold vfsResolveSegs; rw [hRootNode]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide, hPreNP]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParRoot]; dsimp only
    rw [show (stRoot.mode / 128 % 2 == 0 || stRoot.mode / 64 % 2 == 0) = false from by simp [hWrite, hExec]]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    rw [hNPNone]
    simp [st₁, show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
  have hCreCopy : vfsCreateDirPure st₁ "/new_parent/copy" = (.ok (), st₂) := by
    have hAbs : vfsAbsNorm st₁.cwd "/new_parent/copy" = "/new_parent/copy" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["new_parent", "copy"] [] = some (["new_parent"], "copy") := by decide
    have hPreC : vfsResolveSegs st₁.nodes "/" ["new_parent", "copy"] false 1024 =
        .error { kind := .notFound, path := some "/new_parent/copy", message := "no such file or directory: /new_parent/copy" } := by
      unfold vfsResolveSegs; rw [hSt1Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt1NP]; dsimp only
      rw [show (0o755 / 64 % 2 == 0) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/new_parent" "copy" = "/new_parent/copy" from by decide]
      unfold vfsResolveSegs; rw [hSt1CopyNone]; rfl
    have hParNP' : vfsResolveSegs st₁.nodes "/" ["new_parent"] true 512 = .ok ("/new_parent", .dir 0o755) := by
      unfold vfsResolveSegs; rw [hSt1Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt1NP]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreC]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParNP']; dsimp only
    rw [show (0o755 / 128 % 2 == 0 || 0o755 / 64 % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/new_parent" "copy" = "/new_parent/copy" from by decide]
    rw [hSt1CopyNone]
    simp [st₂, show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide]
  have hMkDst : Internal.mkdirImplM vfsOps "/new_parent/copy" true false s₀ = (.ok (), st₂) := by
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/new_parent/copy" s₀ = (vfsStatPure s₀ false "/new_parent/copy", s₀) from rfl, hStatCopyBad]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [show Internal.ancestorChain "/new_parent/copy" "/new_parent/copy".toList.length = ["/new_parent"] from by decide]
    have hStatNPBad : vfsStatPure s₀ true "/new_parent" =
        .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      dsimp only [vfsStatPure]
      rw [hSegsNP]
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hNPNone]; rfl
    have hAnc : Internal.ensureAncestorsM vfsOps ["/new_parent"] s₀ = (.ok (), st₁) := by
      dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.stat true "/new_parent" s₀ = (vfsStatPure s₀ true "/new_parent", s₀) from rfl, hStatNPBad]
      dsimp only
      rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, StateT.bind, StateT.pure]
      rw [show vfsOps.createDir "/new_parent" s₀ = vfsCreateDirPure s₀ "/new_parent" from rfl, hCreNP]
      rfl
    have hBindAnc :
        StateT.bind (Internal.ensureAncestorsM vfsOps ["/new_parent"])
          (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/new_parent/copy") s₀ =
        vfsOps.createDir "/new_parent/copy" st₁ := by
      dsimp only [Bind.bind, StateT.bind]
      rw [hAnc]
    change (StateT.bind (Internal.ensureAncestorsM vfsOps ["/new_parent"])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/new_parent/copy") s₀) = (.ok (), st₂)
    rw [hBindAnc]
    exact hCreCopy
  have hCopyExec : (Internal.copyTreeImplM vfsOps src "/new_parent/copy" false).run s₀ = (.ok (), st₂) := by
    rw [hPre]
    unfold Internal.copyTreeGoM
    dsimp only [StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    have hVfsStatSrc : vfsStatPure s₀ true src = .ok stSrc := hStatSrc
    rw [hVfsStatSrc]
    have hNotDirF : (stSrc.kind != .dir) = false := by rw [hSrcKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hVfsRpSrc : vfsRealPathPure s₀ src = .ok c := hResSrc
    rw [hVfsRpSrc]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    have hListEq : Internal.listDirSortedM vfsOps src s₀ = (.ok #[], s₀) := by
      dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hListSrc ⊢
      cases hRd : vfsReadDirPure s₀ src with
      | error _ =>
        simp [hRd, StateT.pure] at hListSrc
      | ok arr =>
        simp only [hRd] at hListSrc
        dsimp only [StateT.pure, Pure.pure, pure] at hListSrc ⊢
        simp only [Except.ok.injEq] at hListSrc
        rw [hListSrc]
    rw [hListEq]
    dsimp only [StateT.bind]
    rw [hMkDst]
    dsimp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  have hIsDirNP : ((vfsApi.isDir "/new_parent").run st₂).1 = .ok true := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
    have hResNP : vfsResolveSegs st₂.nodes "/" (vfsSplitSegs (vfsAbsNorm st₂.cwd "/new_parent")) true 1024 =
        .ok ("/new_parent", .dir 0o755) := by
      have hSegs : vfsSplitSegs (vfsAbsNorm st₂.cwd "/new_parent") = ["new_parent"] := by
        rw [vfsAbsNorm_abs _ _ (by decide)]; decide
      rw [hSegs]
      unfold vfsResolveSegs
      have hSt2Root : st₂.nodes "/" = some (.dir stRoot.mode) := by
        rw [hSt2Nodes]; simp [hSt1Root]
      have hSt2NP : st₂.nodes "/new_parent" = some (.dir 0o755) := by
        rw [hSt2Nodes]; simp [hSt1NP]
      rw [hSt2Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt2NP]
    rw [hResNP]; rfl
  have hIsDirCopy : ((vfsApi.isDir "/new_parent/copy").run st₂).1 = .ok true := by
    change ((vfsApi.isDir "/new_parent/copy").run st₂).1 = .ok true
    exact vfsCreateDir_sets_isDir "/new_parent/copy" st₁ st₂ hCreCopy
  dsimp only [vfsApi, Internal.mkApiM]
  rw [hCopyExec]
  exact ⟨⟨rfl, hIsDirNP, hIsDirCopy⟩, trivial⟩


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_createsMissingParents`. -/
theorem reach_fs_vfs_copyTree_createsMissingParents :
    CanReach (test_fs_vfs_copyTree_createsMissingParents vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #[] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  have hLstatNP : ((vfsApi.lstat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent" = "/new_parent" := by decide
    have hS : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hStatNP : ((vfsApi.stat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent" = "/new_parent" := by decide
    have hS : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hLstatCopy : ((vfsApi.lstat "/new_parent/copy").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent/copy" = "/new_parent/copy" := by decide
    have hS : vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  exact ⟨st, "/src",
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩,
    hListSrc, hLstatNP, hStatNP, hLstatCopy,
    proof_fs_vfs_copyTree_createsMissingParents st "/src"
      ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩
      hListSrc hLstatNP hStatNP hLstatCopy⟩


/-- Proof of `test_fs_vfs_copyTree_loopRejected` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_loopRejected :
    AllPass (test_fs_vfs_copyTree_loopRejected vfsApi) := by
  intro s₀ src ⟨stRoot, hStatRoot, hRootKind, hRootW, hRootX, hResRoot⟩
    ⟨stSrc, hStatSrc, hSrcKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hCNeLoop, hResSelf⟩
    hListSrc ⟨stSelf, hStatSelf, hSelfKind⟩ hLstatLoop
  have hRootNode : s₀.nodes "/" = some (.dir stRoot.mode) :=
    vfsResolveSegs_abs_root_realPath s₀ stRoot hStatRoot hRootKind hResRoot
  have hExec : ((stRoot.mode / 64) % 2 == 0) = false := by
    have : (stRoot.mode / 64) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hWrite : ((stRoot.mode / 128) % 2 == 0) = false := by
    have : (stRoot.mode / 128) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hSegsLoop : vfsSplitSegs (vfsAbsNorm s₀.cwd "/loop_dst") = ["loop_dst"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hLoopNone : s₀.nodes "/loop_dst" = none :=
    lstat_root_child_none s₀ stRoot.mode "loop_dst" hRootNode hExec hSegsLoop (by decide) hLstatLoop
  have hRpLoopBad : vfsRealPathPure s₀ "/loop_dst" =
      .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsLoop]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [hLoopNone]; rfl
  have hStatLoopBad : vfsStatPure s₀ false "/loop_dst" =
      .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
    dsimp only [vfsStatPure]
    rw [hSegsLoop]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [hLoopNone]; rfl
  have hApprox : (Internal.resolveApproxGoM vfsOps "/loop_dst" [] ("/loop_dst".toList.length + 1)).run s₀ =
      ("/loop_dst", s₀) := by
    rw [show ("/loop_dst".toList.length + 1) = 10 from by decide]
    unfold Internal.resolveApproxGoM
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/loop_dst" s₀ = (vfsRealPathPure s₀ "/loop_dst", s₀) from rfl, hRpLoopBad]
    dsimp only
    rw [show Internal.parent "/loop_dst" = some "/" from by decide,
        show Internal.name "/loop_dst" = some "loop_dst" from by decide]
    dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hRpR : vfsRealPathPure s₀ "/" = .ok "/" := hResRoot
    rw [show vfsOps.realPath "/" s₀ = (vfsRealPathPure s₀ "/", s₀) from rfl, hRpR]
    simp only [List.foldl_cons, List.foldl_nil]
    rfl
  have hGuard : ("/loop_dst" == c || c == "/" || (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList) = false := by
    have h1 : ("/loop_dst" == c) = false := beq_false_of_ne (Ne.symm hCNeLoop)
    have h2 : (c == "/") = false := beq_false_of_ne hCNeRoot
    have h3 := not_prefix_loop_dst c hCAbs
    simp only [h1, h2, h3, Bool.or_false]
  have hStatS0 : (vfsOps.stat true src).run s₀ = (.ok stSrc, s₀) := by
    change (vfsStatPure s₀ true src, s₀) = (.ok stSrc, s₀)
    rw [show vfsStatPure s₀ true src = .ok stSrc from hStatSrc]
  have hRpS0 : (vfsOps.realPath src).run s₀ = (.ok c, s₀) := by
    change (vfsRealPathPure s₀ src, s₀) = (.ok c, s₀)
    rw [show vfsRealPathPure s₀ src = .ok c from hResSrc]
  have hPre := copyTree_pre_checks_ok vfsOps src "/loop_dst" false s₀ stSrc c "/loop_dst"
    hStatS0 hSrcKind hRpS0 (by decide) (by decide) hApprox hGuard
  have hListEq : (Internal.listDirSortedM vfsOps src).run s₀ = (.ok #["self"], s₀) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hListSrc ⊢
    cases hRd : vfsReadDirPure s₀ src with
    | error _ =>
      simp [hRd, StateT.pure] at hListSrc
    | ok arr =>
      simp only [hRd] at hListSrc
      dsimp only [StateT.pure, Pure.pure, pure] at hListSrc ⊢
      simp only [Except.ok.injEq] at hListSrc
      rw [hListSrc]
  dsimp only [StateT.run] at hListEq
  let st₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree ["loop_dst"] (some (vfsEmptyDir 0o755))
      keys := "/loop_dst" :: s₀.keys }
  have hSt1Nodes : st₁.nodes = fun k => if k == "/loop_dst" then some (.dir 0o755) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" "loop_dst")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeSet_emptyDir_nodes_root_child s₀.tree "loop_dst" ⟨stRoot.mode, hRootNode⟩ (by decide) hLoopNone
  have hCreLoop : vfsCreateDirPure s₀ "/loop_dst" = (.ok (), st₁) := by
    have hAbs : vfsAbsNorm s₀.cwd "/loop_dst" = "/loop_dst" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["loop_dst"] [] = some ([], "loop_dst") := by decide
    have hPreL : vfsResolveSegs s₀.nodes "/" ["loop_dst"] false 1024 =
        .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
      unfold vfsResolveSegs; rw [hLoopNone]; rfl
    have hParRoot : vfsResolveSegs s₀.nodes "/" [] true 512 = .ok ("/", .dir stRoot.mode) := by
      unfold vfsResolveSegs; rw [hRootNode]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/loop_dst" = ["loop_dst"] from by decide, hPreL]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParRoot]; dsimp only
    rw [show (stRoot.mode / 128 % 2 == 0 || stRoot.mode / 64 % 2 == 0) = false from by simp [hWrite, hExec]]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    rw [hLoopNone]
    simp [st₁, show vfsSplitSegs "/loop_dst" = ["loop_dst"] from by decide]
  have hMkLoop : Internal.mkdirImplM vfsOps "/loop_dst" true false s₀ = (.ok (), st₁) := by
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/loop_dst" s₀ = (vfsStatPure s₀ false "/loop_dst", s₀) from rfl, hStatLoopBad]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [show Internal.ancestorChain "/loop_dst" "/loop_dst".toList.length = [] from by decide]
    change StateT.bind (Internal.ensureAncestorsM vfsOps [])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/loop_dst") s₀ = (.ok (), st₁)
    have hAncNil : Internal.ensureAncestorsM vfsOps [] s₀ = (.ok (), s₀) := rfl
    simp [StateT.bind, hAncNil]
    exact hCreLoop
  have hSelfStatSt1 : vfsStatPure st₁ true (Internal.join src "self") = .ok stSelf := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStatSelf ⊢
    cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true 1024 with
    | error _ => simp [hR] at hStatSelf
    | ok p =>
      have hPres := vfsResolveSegs_insert_fresh s₀.nodes "/loop_dst" (.dir 0o755) hLoopNone
        1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true p hR
      dsimp only [st₁]
      rw [hSt1Nodes, hPres]
      simpa [hR] using hStatSelf
  have hSelfRpSt1 : vfsRealPathPure st₁ (Internal.join src "self") = .ok c := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hResSelf ⊢
    cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true 1024 with
    | error _ => simp [hR] at hResSelf
    | ok p =>
      have hPres := vfsResolveSegs_insert_fresh s₀.nodes "/loop_dst" (.dir 0o755) hLoopNone
        1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true p hR
      dsimp only [st₁]
      rw [hSt1Nodes, hPres]
      simpa [hR] using hResSelf
  have hCopyExec : (Internal.copyTreeImplM vfsOps src "/loop_dst" false).run s₀ =
      (.error { kind := .invalidInput, path := some (Internal.join src "self"), message := s!"symlink directory loop: {Internal.join src "self"}" }, st₁) := by
    rw [hPre]
    unfold Internal.copyTreeGoM
    dsimp only [StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    have hVfsStatSrc : vfsStatPure s₀ true src = .ok stSrc := hStatSrc
    rw [hVfsStatSrc]
    have hNotDirF : (stSrc.kind != .dir) = false := by rw [hSrcKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hVfsRpSrc : vfsRealPathPure s₀ src = .ok c := hResSrc
    rw [hVfsRpSrc]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [hListEq]
    dsimp only [StateT.bind]
    rw [hMkLoop]
    dsimp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true (Internal.join src "self") st₁ = (vfsStatPure st₁ true (Internal.join src "self"), st₁) from rfl,
        hSelfStatSt1]
    dsimp only
    have hSelfNotDirF : (stSelf.kind != .dir) = false := by rw [hSelfKind]; decide
    rw [show (stSelf.kind == .dir) = true from by rw [hSelfKind]; decide]
    simp only [↓reduceIte]
    unfold Internal.copyTreeGoM
    dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true (Internal.join src "self") st₁ = (vfsStatPure st₁ true (Internal.join src "self"), st₁) from rfl,
        hSelfStatSt1]
    simp only [hSelfNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath (Internal.join src "self") st₁ = (vfsRealPathPure st₁ (Internal.join src "self"), st₁) from rfl,
        hSelfRpSt1]
    simp only [List.mem_singleton, ↓reduceIte]
    rfl
  dsimp only [vfsApi, Internal.mkApiM]
  rw [hCopyExec]
  exact ⟨⟨_, rfl, rfl⟩, trivial⟩


/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_loopRejected`. -/
theorem reach_fs_vfs_copyTree_loopRejected :
    CanReach (test_fs_vfs_copyTree_loopRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s =>
        if s == "src" then
          some (.dir 0o755 (fun s2 => if s2 == "self" then some (.symlink "/src" 0o777) else none))
        else none)
      keys := ["/", "/src", "/src/self"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hSelfResolve : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (vfsApi.join "/src" "self"))) true 1024 =
      .ok ("/src", .dir 0o755) := by
    have hJ : vfsApi.join "/src" "self" = "/src/self" := by decide
    have hA : vfsAbsNorm st.cwd "/src/self" = "/src/self" := by decide
    have hS : vfsSplitSegs "/src/self" = ["src", "self"] := by decide
    have hS_src : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hJ, hA, hS]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/src" "self" = "/src/self" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src/self" = some (.symlink "/src" 0o777) from rfl]; dsimp only
    rw [show ((Internal.parent "/src/self").getD "/") = "/src" from by decide,
        show Internal.isAbsolute "/src" = true from by decide]
    simp only [↓reduceIte, show Internal.normPath "/src" = "/src" from by decide, hS_src]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSelf : ((vfsApi.resolve (vfsApi.join "/src" "self")).run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hStatSelf : ((vfsApi.stat (vfsApi.join "/src" "self")).run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #["self"] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src", "/src/self"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hN2 : (st.nodes "/src/self").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    have hPre2 : "/src/".toList.isPrefixOf "/src/self".toList = true := by decide
    have hDrop2 : "/src/self".toList.drop "/src/".toList.length = "self".toList := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, hN2, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src/self" != "/src") = true from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, hPre2, hDrop2,
      show (!"self".toList.isEmpty && !('/' ∈ "self".toList)) = true from by decide,
      show String.ofList "self".toList = "self" from by decide,
      Bool.true_and, Bool.false_and, List.mergeSort_singleton]
  have hLstatLoop : ((vfsApi.lstat "/loop_dst").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/loop_dst" = "/loop_dst" := by decide
    have hS : vfsSplitSegs "/loop_dst" = ["loop_dst"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/loop_dst" = none from rfl]; rfl
  exact ⟨st, "/src",
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩,
    hListSrc, ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩, hLstatLoop,
    proof_fs_vfs_copyTree_loopRejected st "/src"
      ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩
      hListSrc ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩ hLstatLoop⟩


private def buggyMkdirR1I01 (path : String) (parents existOk : Bool) : StateM VfsState (Except FsError Unit) := do
  if !parents then
    Internal.mkdirImplM vfsOps path parents existOk
  else
    let ancs := Internal.ancestorChain path path.toList.length
    match ← Internal.ensureAncestorsM vfsOps ancs with
    | .error ae => return .error ae
    | .ok () =>
      match ← vfsOps.createDir path with
      | .ok () => return .ok ()
      | .error e => if e.kind == .alreadyExists then return .ok () else return .error e


example : ¬ AllPass (test_fs_vfs_mkdir_existingFails { vfsApi with mkdir := buggyMkdirR1I01 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/broken" true vfsLstat_broken_symlink
  simp only [buggyMkdirR1I01, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind,
    pure, Pure.pure] at hFail
  have hChain : Internal.ancestorChain "/broken" "/broken".toList.length = [] := by decide
  rw [hChain] at hFail
  have hCre : vfsCreateDirPure st "/broken" =
      (.error { kind := .alreadyExists, path := some "/broken", message := "already exists: /broken" }, st) := by
    have hAbs : vfsAbsNorm "/" "/broken" = "/broken" := by decide
    have hSegs : vfsSplitSegs "/broken" = ["broken"] := by decide
    have hRes : vfsResolveSegs st.nodes "/" ["broken"] false 1024 = .ok ("/broken", .symlink "/nope" 0o777) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/" "broken" = "/broken" from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/broken" = some (.symlink "/nope" 0o777) from rfl]; rfl
    dsimp only [vfsCreateDirPure]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs, hRes]
    rfl
  change (match ((do
    let x ← Internal.ensureAncestorsM vfsOps []
    match x with
    | .error ae => return .error ae
    | .ok () =>
      match ← vfsOps.createDir "/broken" with
      | .ok () => return .ok ()
      | .error (e : FsError) =>
        if e.kind == .alreadyExists then return .ok () else return .error e :
          StateM VfsState (Except FsError Unit)).run st) with
    | (res, _) => _) at hFail
  have hAnc : Internal.ensureAncestorsM vfsOps [] st = (.ok (), st) := rfl
  simp only [StateT.run, bind, StateT.bind, pure, hAnc,
    show vfsOps.createDir "/broken" st = vfsCreateDirPure st "/broken" from rfl, hCre, assert] at hFail
  rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he


private def buggyCopyTreeR1I02 (src dst : String) (dirsExistOk : Bool) : StateM VfsState (Except FsError Unit) := do
  match ← vfsOps.stat true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
    Internal.mkdirImplM vfsOps dst false dirsExistOk


example : ¬ AllPass (test_fs_vfs_copyTree_createsMissingParents { vfsApi with copyTree := buggyCopyTreeR1I02 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/" = "/" from by decide,
        show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/" = "/" from by decide,
        show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #[] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  have hLstatNP : ((vfsApi.lstat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent" = "/new_parent" from by decide,
        show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hStatNP : ((vfsApi.stat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent" = "/new_parent" from by decide,
        show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hLstatCopy : ((vfsApi.lstat "/new_parent/copy").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hFail := h st "/src"
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
    ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩
    hListSrc hLstatNP hStatNP hLstatCopy
  have hPreCopy : vfsResolveSegs st.nodes "/" ["new_parent", "copy"] false 1024 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hParNP : vfsResolveSegs st.nodes "/" ["new_parent"] true 512 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hCreFail : (vfsCreateDirPure st "/new_parent/copy").1 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsCreateDirPure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreCopy]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show Internal.splitLastAux ["new_parent", "copy"] [] = some (["new_parent"], "copy") from by decide]
    dsimp only
    rw [hParNP]
  dsimp only [buggyCopyTreeR1I02, Internal.mkdirImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hFail
  have hVS : vfsOps.stat true "/src" st = (.ok (vfsToStat (.dir 0o755)), st) := by
    change (vfsStatPure st true "/src", st) = _
    rw [show vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) from hStatSrc]
  rw [hVS] at hFail
  dsimp only at hFail
  rw [show ((vfsToStat (.dir 0o755)).kind != .dir) = false from by decide] at hFail
  simp only [Bool.false_eq_true, ↓reduceIte] at hFail
  dsimp only [Bind.bind, StateT.bind, StateT.pure] at hFail
  have hStCopy : vfsOps.stat false "/new_parent/copy" st =
      (.error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" }, st) := by
    dsimp only [vfsOps, vfsStatPure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreCopy]
  rw [hStCopy] at hFail
  dsimp only at hFail
  rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide] at hFail
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hFail
  change (match (vfsCreateDirPure st "/new_parent/copy") with | (res, s₁) => _) at hFail
  dsimp only [vfsOps] at hFail
  cases hC : vfsCreateDirPure st "/new_parent/copy" with
  | mk res _ =>
    rw [hC] at hFail
    have hEq : res = .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      simpa [hC] using hCreFail
    simp [hEq, assert] at hFail


private def buggyTouchR1I03 (path : String) (existOk : Bool) : StateM VfsState (Except FsError Unit) := do
  match ← vfsOps.stat true path with
  | .ok st =>
    if !existOk then
      return .error { kind := .alreadyExists, path := some path, message := s!"file already exists: {path}" }
    else if st.kind == .dir then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else
      vfsOps.appendText path ""
  | .error e =>
    if e.kind == .notFound then
      vfsOps.writeBytes path ByteArray.empty
    else
      return .error e


example : ¬ AllPass (test_fs_vfs_touch_existingFails { vfsApi with touch := buggyTouchR1I03 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/broken" vfsLstat_broken_symlink
  have hFollowRes : vfsResolveSegs st.nodes "/" ["broken"] true 1024 =
      .error { kind := .notFound, path := some "/nope", message := "no such file or directory: /nope" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "broken" = "/broken" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/broken" = some (.symlink "/nope" 0o777) from rfl]; dsimp only
    rw [show ((Internal.parent "/broken").getD "/") = "/" from by decide,
        show Internal.isAbsolute "/nope" = true from by decide]
    simp only [↓reduceIte, show Internal.normPath "/nope" = "/nope" from by decide,
      show vfsSplitSegs "/nope" = ["nope"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "nope" = "/nope" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/nope" = none from rfl]; rfl
  have hStatFollow : vfsStatPure st true "/broken" =
      .error { kind := .notFound, path := some "/nope", message := "no such file or directory: /nope" } := by
    dsimp only [vfsStatPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/broken" = "/broken" from by decide,
        show vfsSplitSegs "/broken" = ["broken"] from by decide,
        hFollowRes]
  have hWb : (vfsWriteBytesPure st "/broken" ByteArray.empty).1 = .ok () := by
    dsimp only [vfsWriteBytesPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/broken" = "/broken" from by decide,
        show vfsSplitSegs "/broken" = ["broken"] from by decide,
        show Internal.splitLastAux ["broken"] [] = some ([], "broken") from by decide]
    dsimp only
    have hRootR : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
    rw [hRootR]; dsimp only
    rw [show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte,
      show vfsChildPath "/" "broken" = "/broken" from by decide, hFollowRes]
  dsimp only [vfsApi, Internal.mkApiM, buggyTouchR1I03, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at hFail
  rw [show vfsOps.stat true "/broken" st = (vfsStatPure st true "/broken", st) from rfl, hStatFollow] at hFail
  dsimp only at hFail
  rw [show (Raw.FsErrorKind.notFound == Raw.FsErrorKind.notFound) = true from by decide] at hFail
  simp only [↓reduceIte] at hFail
  rw [show vfsOps.writeBytes "/broken" ByteArray.empty st = vfsWriteBytesPure st "/broken" ByteArray.empty from rfl] at hFail
  cases hW : vfsWriteBytesPure st "/broken" ByteArray.empty with
  | mk res _ =>
    rw [hW] at hFail
    have hOkW : res = .ok () := by simpa [hW] using hWb
    rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
    rw [hOkW] at he
    cases he


private def buggyCopyTreeGoNoLoopM (src dst : String) (dirsExistOk : Bool) : Nat → StateM VfsState (Except FsError Unit)
  | 0 => return .error { kind := .ioError, path := some src, message := s!"maximum directory depth exceeded: {src}" }
  | fuel + 1 => do
    match ← vfsOps.stat true src with
    | .error e => return .error e
    | .ok st =>
      if st.kind != .dir then
        return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
      match ← vfsOps.realPath src with
      | .error e => return .error e
      | .ok _ =>
        match ← Internal.listDirSortedM vfsOps src with
        | .error e => return .error e
        | .ok names =>
          match ← Internal.mkdirImplM vfsOps dst true dirsExistOk with
          | .error e => return .error e
          | .ok () =>
            Internal.forEachChildM (fun n => do
              let sChild := Internal.join src n
              let dChild := Internal.join dst n
              match ← vfsOps.stat true sChild with
              | .error e => return .error e
              | .ok childSt =>
                if childSt.kind == .dir then
                  buggyCopyTreeGoNoLoopM sChild dChild dirsExistOk fuel
                else
                  match ← vfsOps.readBytes sChild with
                  | .error e => return .error e
                  | .ok bs => vfsOps.writeBytes dChild bs) names.toList


private theorem vfsResolveSegs_never_invalidInput (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow e, vfsResolveSegs nodes cur segs follow fuel = .error e → e.kind ≠ .invalidInput := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h; cases h; intro hk; cases hk
  | succ fuel ih =>
    intro cur segs follow e h
    simp only [vfsResolveSegs] at h
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at h; cases h; intro hk; cases hk
      | some nd =>
        simp only [hNd] at h
        cases nd with
        | file _ _ => simp at h
        | dir _ => simp at h
        | symlink _ _ => cases follow <;> simp at h; exact ih _ _ _ _ h
    | cons _ _ =>
      cases hNd : nodes cur with
      | none => simp [hNd] at h; cases h; intro hk; cases hk
      | some nd =>
        simp only [hNd] at h
        cases nd with
        | file _ _ => simp at h; cases h; intro hk; cases hk
        | symlink _ _ => exact ih _ _ _ _ h
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at h; cases h; intro hk; cases hk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at h
            exact ih _ _ _ _ h


private theorem vfsOps_mkdir_never_invalidInput (path : String) (parents existOk : Bool) (st : VfsState) (e : FsError)
    (hErr : (Internal.mkdirImplM vfsOps path parents existOk st).1 = .error e) : e.kind ≠ .invalidInput := by
  have hStatNe : ∀ f p s err, (vfsOps.stat f p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro f p s err hs
    dsimp only [vfsOps, vfsStatPure] at hs
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) f 1024 with
    | ok _ => simp [hR] at hs
    | error err' => simp [hR] at hs; cases hs; exact vfsResolveSegs_never_invalidInput s.nodes 1024 _ _ _ _ hR
  have hCreNe : ∀ p s err, (vfsOps.createDir p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hc
    dsimp only [vfsOps, vfsCreateDirPure] at hc
    cases hPre : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) false 1024 with
    | ok _ => simp [hPre] at hc; cases hc; intro hk; cases hk
    | error e0 =>
      simp only [hPre] at hc
      by_cases hNf : (e0.kind != .notFound) = true
      · simp [hNf] at hc; cases hc; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hPre
      · have hNfF : (e0.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hc
        cases hSp : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s.cwd p)) [] with
        | none => simp [hSp] at hc; cases hc; intro hk; cases hk
        | some pair =>
          rcases pair with ⟨parSegs, lastSeg⟩
          simp only [hSp] at hc
          cases hPar : vfsResolveSegs s.nodes "/" parSegs true 512 with
          | error pe => simp [hPar] at hc; cases hc; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hPar
          | ok pNode =>
            rcases pNode with ⟨parCanon, nd⟩
            cases nd with
            | file _ _ => simp [hPar] at hc; cases hc; intro hk; cases hk
            | symlink _ _ => simp [hPar] at hc; cases hc; intro hk; cases hk
            | dir pm =>
              simp only [hPar] at hc
              by_cases hPm : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
              · simp [hPm] at hc; cases hc; intro hk; cases hk
              · have hPmF : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hPm
                simp only [hPmF, Bool.false_eq_true, ↓reduceIte] at hc
                cases hEx : s.nodes (vfsChildPath parCanon lastSeg) with
                | some _ => simp [hEx] at hc; cases hc; intro hk; cases hk
                | none => simp [hEx] at hc
  have hEnsureNe : ∀ p s err, (Internal.ensureDirM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hd
    dsimp only [Internal.ensureDirM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hd
    cases hSt : vfsOps.stat true p s with
    | mk res1 s1 =>
      rw [hSt] at hd
      cases res1 with
      | ok st1 =>
        simp only at hd
        by_cases hD : (st1.kind == .dir) = true
        · simp only [hD, ↓reduceIte] at hd
          dsimp only [StateT.pure, Pure.pure, pure] at hd
          cases hd
        · have hDF : (st1.kind == .dir) = false := Bool.eq_false_iff.mpr hD
          simp only [hDF, Bool.false_eq_true, ↓reduceIte] at hd
          dsimp only [StateT.pure, Pure.pure, pure] at hd
          simp only [Except.error.injEq] at hd; rw [← hd]; intro hk; cases hk
      | error e1 =>
        have hStE1 := hStatNe true p s e1 (congrArg Prod.fst hSt)
        simp only at hd
        by_cases hNf : (e1.kind != .notFound) = true
        · simp [hNf, StateT.pure] at hd; cases hd; exact hStE1
        · have hNfF : (e1.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
          simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hd
          dsimp only [Bind.bind, StateT.bind, StateT.pure] at hd
          cases hCre : vfsOps.createDir p s1 with
          | mk rc sc =>
            rw [hCre] at hd
            cases rc with
            | ok _ =>
              dsimp only [StateT.pure, Pure.pure, pure] at hd
              cases hd
            | error ce =>
              have hCreE := hCreNe p s1 ce (congrArg Prod.fst hCre)
              simp only at hd
              by_cases hAe : (ce.kind == .alreadyExists) = true
              · simp only [hAe, ↓reduceIte] at hd
                cases hSt2 : vfsOps.stat true p sc with
                | mk rs2 _ =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hd
                  rw [hSt2] at hd
                  cases rs2 with
                  | error _ =>
                    dsimp only at hd
                    cases hd; intro hk; cases hk
                  | ok st2 =>
                    dsimp only at hd
                    by_cases hD2 : (st2.kind == .dir) = true
                    · simp only [hD2, ↓reduceIte] at hd
                      dsimp only [StateT.pure, Pure.pure, pure] at hd
                      cases hd
                    · have hD2F : (st2.kind == .dir) = false := Bool.eq_false_iff.mpr hD2
                      simp only [hD2F, Bool.false_eq_true, ↓reduceIte] at hd
                      dsimp only [StateT.pure, Pure.pure, pure] at hd
                      simp only [Except.error.injEq] at hd; rw [← hd]; intro hk; cases hk
              · simp [hAe, StateT.pure] at hd; cases hd; exact hCreE
  have hAncNe : ∀ ancs s err, (Internal.ensureAncestorsM vfsOps ancs s).1 = .error err → err.kind ≠ .invalidInput := by
    intro ancs; induction ancs with
    | nil => intro _ _ h; simp [Internal.ensureAncestorsM, pure, StateT.pure] at h
    | cons a rest ih =>
      intro s err ha
      simp only [Internal.ensureAncestorsM, Bind.bind, bind, StateT.bind, Pure.pure, pure] at ha
      cases hE : Internal.ensureDirM vfsOps a s with
      | mk r s' =>
        rw [hE] at ha
        cases r with
        | error e' =>
          dsimp only [StateT.pure, Pure.pure, pure] at ha
          cases ha; exact hEnsureNe a s err (congrArg Prod.fst hE)
        | ok _ => exact ih s' err ha
  have hCreExistNe : ∀ p s err, (Internal.createDirExistOkM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hce
    dsimp only [Internal.createDirExistOkM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hce
    cases hC : vfsOps.createDir p s with
    | mk rc sc =>
      rw [hC] at hce
      cases rc with
      | ok _ =>
        dsimp only [StateT.pure, Pure.pure, pure] at hce
        cases hce
      | error ce =>
        have hCeNe := hCreNe p s ce (congrArg Prod.fst hC)
        dsimp only at hce
        by_cases hAe : (ce.kind != .alreadyExists) = true
        · simp [hAe, StateT.pure] at hce; cases hce; exact hCeNe
        · have hAeF : (ce.kind != .alreadyExists) = false := Bool.eq_false_iff.mpr hAe
          simp only [hAeF, Bool.false_eq_true, ↓reduceIte] at hce
          dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hce
          cases hSt2 : vfsOps.stat true p sc with
          | mk rs2 s2 =>
            rw [hSt2] at hce
            cases rs2 with
            | error _ => simp [StateT.pure] at hce; cases hce; exact hCeNe
            | ok st2 =>
              dsimp only at hce
              by_cases hD2 : (st2.kind == .dir) = true
              · simp [hD2, StateT.pure] at hce
              · simp [hD2, StateT.pure] at hce; cases hce; exact hCeNe
  dsimp only [Internal.mkdirImplM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hErr
  cases hSt : vfsOps.stat false path st with
  | mk resPre sPre =>
    rw [hSt] at hErr
    cases resPre with
    | ok stPre =>
      simp only at hErr
      by_cases h1 : (existOk && stPre.kind == .dir) = true
      · simp [h1, StateT.pure] at hErr
      · have h1F : (existOk && stPre.kind == .dir) = false := Bool.eq_false_iff.mpr h1
        simp only [h1F, Bool.false_eq_true, ↓reduceIte] at hErr
        by_cases h2 : (existOk && stPre.kind == .symlink) = true
        · simp only [h2, ↓reduceIte] at hErr
          cases hSt2 : vfsOps.stat true path sPre with
          | mk r2 _ =>
            dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hErr
            rw [hSt2] at hErr
            cases r2 with
            | error _ =>
              dsimp only at hErr
              cases hErr; intro hk; cases hk
            | ok ts =>
              dsimp only at hErr
              by_cases hD : (ts.kind == .dir) = true
              · simp only [hD, ↓reduceIte] at hErr
                dsimp only [StateT.pure, Pure.pure, pure] at hErr
                cases hErr
              · have hDF : (ts.kind == .dir) = false := Bool.eq_false_iff.mpr hD
                simp only [hDF, Bool.false_eq_true, ↓reduceIte] at hErr
                dsimp only [StateT.pure, Pure.pure, pure] at hErr
                simp only [Except.error.injEq] at hErr; rw [← hErr]; intro hk; cases hk
        · simp [h2, StateT.pure] at hErr; cases hErr; intro hk; cases hk
    | error e0 =>
      have hStE0 := hStatNe false path st e0 (congrArg Prod.fst hSt)
      simp only at hErr
      by_cases hNf : (e0.kind != .notFound) = true
      · simp [hNf, StateT.pure] at hErr; cases hErr; exact hStE0
      · have hNfF : (e0.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hErr
        by_cases hP : (!parents) = true
        · simp only [hP, ↓reduceIte] at hErr
          cases existOk with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hErr; exact hCreNe path sPre e hErr
          | true => simp only [↓reduceIte] at hErr; exact hCreExistNe path sPre e hErr
        · have hPF : (!parents) = false := Bool.eq_false_iff.mpr hP
          simp only [hPF, Bool.false_eq_true, ↓reduceIte] at hErr
          dsimp only [Bind.bind, StateT.bind, StateT.pure] at hErr
          cases hAnc : Internal.ensureAncestorsM vfsOps (Internal.ancestorChain path path.toList.length) sPre with
          | mk ra sa =>
            rw [hAnc] at hErr
            cases ra with
            | error ae =>
              dsimp only [StateT.pure, Pure.pure, pure] at hErr
              cases hErr; exact hAncNe _ sPre e (congrArg Prod.fst hAnc)
            | ok _ =>
              dsimp only at hErr
              cases existOk with
              | false => simp only [Bool.false_eq_true, ↓reduceIte] at hErr; exact hCreNe path sa e hErr
              | true => simp only [↓reduceIte] at hErr; exact hCreExistNe path sa e hErr


private theorem forEachChildM_never_invalidInput (f : String → StateM VfsState (Except FsError Unit))
    (hf : ∀ x st e, (f x st).1 = .error e → e.kind ≠ .invalidInput) :
    ∀ xs st e, (Internal.forEachChildM f xs st).1 = .error e → e.kind ≠ .invalidInput := by
  intro xs; induction xs with
  | nil => intro _ _ h; simp [Internal.forEachChildM, pure, StateT.pure] at h
  | cons x rest ih =>
    intro st e h
    simp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind] at h
    cases hx : f x st with
    | mk r s' =>
      rw [hx] at h
      cases r with
      | error e' =>
        dsimp only [StateT.pure, Pure.pure, pure] at h
        cases h; exact hf x st e (congrArg Prod.fst hx)
      | ok _ => exact ih s' e h


private theorem forEachChildM_invariant (P : VfsState → Prop)
    (f : String → StateM VfsState (Except FsError Unit))
    (hf : ∀ x st, P st → P (f x st).2 ∧ (∀ e, (f x st).1 = .error e → e.kind ≠ .invalidInput)) :
    ∀ xs st, P st →
      P (Internal.forEachChildM f xs st).2 ∧
      (∀ e, (Internal.forEachChildM f xs st).1 = .error e → e.kind ≠ .invalidInput) := by
  intro xs; induction xs with
  | nil =>
    intro st hP
    simp only [Internal.forEachChildM, pure, StateT.pure]
    exact ⟨hP, fun _ h => by cases h⟩
  | cons x rest ih =>
    intro st hP
    simp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind]
    cases hx : f x st with
    | mk r s' =>
      have hStep := hf x st hP
      rw [hx] at hStep
      cases r with
      | error e' =>
        dsimp only [StateT.pure, Pure.pure, pure]
        exact ⟨hStep.1, fun e h => by cases h; exact hStep.2 e' rfl⟩
      | ok _ => exact ih s' hStep.1


private def NoFileTree (t : VfsTree) : Prop :=
  ∀ segs bs m, vfsTreeGet t segs ≠ some (.file bs m)


private theorem vfsTreeNodes_noFile (t : VfsTree) (k : String) (bs : ByteArray) (m : Nat)
    (hc : vfsTreeNodes t k = some (.file bs m)) (ht : NoFileTree t) : False := by
  unfold vfsTreeNodes at hc
  by_cases hC : isCanonPath k = true
  · simp only [hC, ↓reduceIte] at hc
    cases hg : vfsTreeGet t (vfsSplitSegs k) with
    | none => simp [hg] at hc
    | some sub =>
      simp only [hg, Option.map_some, Option.some.injEq] at hc
      cases sub with
      | file _ _ => exact ht (vfsSplitSegs k) _ _ hg
      | dir _ _ => simp [vfsTreeTopNode] at hc
      | symlink _ _ => simp [vfsTreeTopNode] at hc
  · simp [hC] at hc


private theorem vfsResolveSegs_true_noFile_isDir (t : VfsTree) (ht : NoFileTree t) :
    ∀ fuel cur segs canon nd,
      vfsResolveSegs (vfsTreeNodes t) cur segs true fuel = .ok (canon, nd) →
      ∃ m, nd = .dir m := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs canon nd h
    cases segs with
    | nil =>
      simp only [vfsResolveSegs] at h
      cases hc : vfsTreeNodes t cur with
      | none => simp [hc] at h
      | some n0 =>
        cases n0 with
        | file bs m => exact (vfsTreeNodes_noFile t cur bs m hc ht).elim
        | dir m => simp [hc] at h; rcases h with ⟨_, rfl⟩; exact ⟨m, rfl⟩
        | symlink _ _ => simp [hc] at h; exact ih _ _ _ _ h
    | cons seg rest =>
      simp only [vfsResolveSegs] at h
      cases hc : vfsTreeNodes t cur with
      | none => simp [hc] at h
      | some n0 =>
        cases n0 with
        | file bs m => exact (vfsTreeNodes_noFile t cur bs m hc ht).elim
        | symlink _ _ => simp [hc] at h; exact ih _ _ _ _ h
        | dir m =>
          simp only [hc] at h
          by_cases hp : ((m / 64) % 2 == 0) = true
          · simp [hp] at h
          · simp [hp] at h; exact ih _ _ _ _ h


private theorem vfsTreeSet_emptyDir_noFileTree (m : Nat) :
    ∀ path t, NoFileTree t → NoFileTree (vfsTreeSet t path (some (vfsEmptyDir m))) := by
  intro path; induction path with
  | nil =>
    intro t _ segs bs m' h
    cases segs <;> simp [vfsTreeSet, vfsEmptyDir, vfsTreeGet] at h
  | cons seg rest ih =>
    intro t ht segs bs m' h
    cases rest with
    | nil =>
      cases t with
      | file _ _ => exact ht segs _ _ h
      | symlink _ _ => exact ht segs _ _ (by simpa [vfsTreeSet] using h)
      | dir dm ch =>
        cases segs with
        | nil => simp [vfsTreeSet, vfsTreeGet] at h
        | cons s srest =>
          simp only [vfsTreeSet, vfsTreeGet] at h
          by_cases hs : (s == seg) = true
          · simp only [hs, ↓reduceIte] at h
            cases srest <;> simp [vfsEmptyDir, vfsTreeGet] at h
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
            cases hc : ch s with
            | none => simp [hc] at h
            | some sub =>
              simp only [hc] at h
              exact ht (s :: srest) bs m' (by simp only [vfsTreeGet, hc]; exact h)
    | cons seg2 rest2 =>
      cases t with
      | file _ _ => exact ht segs _ _ h
      | symlink _ _ => exact ht segs _ _ (by simpa [vfsTreeSet] using h)
      | dir dm ch =>
        cases segs with
        | nil => simp [vfsTreeSet, vfsTreeGet] at h
        | cons s srest =>
          simp only [vfsTreeSet, vfsTreeGet] at h
          by_cases hs : (s == seg) = true
          · simp only [hs, ↓reduceIte] at h
            cases hc : ch seg with
            | none => simp [hc] at h
            | some sub =>
              have hsEq : s = seg := beq_iff_eq.mp hs
              subst hsEq
              simp only [hc] at h
              have htSub : NoFileTree sub := fun xs bs' m'' hx =>
                ht (s :: xs) bs' m'' (by simp only [vfsTreeGet, hc]; exact hx)
              exact ih sub htSub srest bs m' h
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
            cases hc : ch s with
            | none => simp [hc] at h
            | some sub =>
              simp only [hc] at h
              exact ht (s :: srest) bs m' (by simp only [vfsTreeGet, hc]; exact h)


private theorem vfsCreateDirPure_noFileTree (st : VfsState) (p : String) (ht : NoFileTree st.tree) :
    NoFileTree (vfsCreateDirPure st p).2.tree := by
  unfold vfsCreateDirPure
  dsimp only
  cases vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd p)) false 1024 with
  | ok _ => exact ht
  | error e =>
    dsimp only
    by_cases hNf : (e.kind != .notFound) = true
    · simp only [hNf, ↓reduceIte]; exact ht
    · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
      cases Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd p)) [] with
      | none => exact ht
      | some pair =>
        rcases pair with ⟨parSegs, lastSeg⟩
        dsimp only
        cases vfsResolveSegs st.nodes "/" parSegs true 512 with
        | error _ => exact ht
        | ok pNode =>
          rcases pNode with ⟨parCanon, nd⟩
          cases nd with
          | file _ _ => exact ht
          | symlink _ _ => exact ht
          | dir pm =>
            dsimp only
            by_cases hPm : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
            · simp only [hPm, ↓reduceIte]; exact ht
            · simp only [hPm, Bool.false_eq_true, ↓reduceIte]
              cases st.nodes (vfsChildPath parCanon lastSeg) with
              | some _ => exact ht
              | none => exact vfsTreeSet_emptyDir_noFileTree 0o755 (vfsSplitSegs (vfsChildPath parCanon lastSeg)) st.tree ht


private theorem vfsEnsureDirM_noFileTree (anc : String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.ensureDirM vfsOps anc st).2.tree := by
  unfold Internal.ensureDirM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hSt : vfsOps.stat true anc st with
  | mk rSt s1 =>
    have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
    cases rSt with
    | ok st0 =>
      dsimp only
      by_cases hD : (st0.kind == .dir) = true <;> simp only [hD, ↓reduceIte, Bool.false_eq_true] <;> subst hs1 <;> exact ht
    | error e =>
      dsimp only
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte]; subst hs1; exact ht
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
        cases hCr : vfsOps.createDir anc s1 with
        | mk rc s2 =>
          have ht2 : NoFileTree s2.tree := by
            have hS2Eq : s2 = (vfsCreateDirPure s1 anc).2 := (congrArg Prod.snd hCr).symm
            rw [hS2Eq]; exact vfsCreateDirPure_noFileTree s1 anc (by subst hs1; exact ht)
          cases rc with
          | ok _ => exact ht2
          | error ce =>
            dsimp only
            by_cases hAe : (ce.kind == .alreadyExists) = true
            · simp only [hAe, ↓reduceIte, Bind.bind, bind, StateT.bind]
              cases hSt2 : vfsOps.stat true anc s2 with
              | mk rSt2 s3 =>
                have hs3 : s3 = s2 := (congrArg Prod.snd hSt2).symm
                cases rSt2 with
                | error _ => subst hs3; exact ht2
                | ok st2 =>
                  dsimp only
                  by_cases hD2 : (st2.kind == .dir) = true <;>
                    simp only [hD2, ↓reduceIte, Bool.false_eq_true] <;> subst hs3 <;> exact ht2
            · simp only [hAe, Bool.false_eq_true, ↓reduceIte]; exact ht2


private theorem vfsEnsureAncestorsM_noFileTree (ps : List String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.ensureAncestorsM vfsOps ps st).2.tree := by
  induction ps generalizing st with
  | nil => exact ht
  | cons p rest ih =>
    simp only [Internal.ensureAncestorsM, Bind.bind, bind, StateT.bind]
    cases hEd : Internal.ensureDirM vfsOps p st with
    | mk rd s1 =>
      have ht1 : NoFileTree s1.tree := by
        have hS1Eq : s1 = (Internal.ensureDirM vfsOps p st).2 := (congrArg Prod.snd hEd).symm
        rw [hS1Eq]; exact vfsEnsureDirM_noFileTree p st ht
      cases rd with
      | error _ => exact ht1
      | ok _ => exact ih s1 ht1


private theorem vfsCreateDirExistOkM_noFileTree (p : String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.createDirExistOkM vfsOps p st).2.tree := by
  unfold Internal.createDirExistOkM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hC : vfsOps.createDir p st with
  | mk rc sc =>
    have htc : NoFileTree sc.tree := by
      have hEq : sc = (vfsCreateDirPure st p).2 := (congrArg Prod.snd hC).symm
      rw [hEq]; exact vfsCreateDirPure_noFileTree st p ht
    cases rc with
    | ok _ => exact htc
    | error ce =>
      dsimp only
      by_cases hAe : (ce.kind != .alreadyExists) = true
      · simp only [hAe, ↓reduceIte]; exact htc
      · have hAeF : (ce.kind != .alreadyExists) = false := Bool.eq_false_iff.mpr hAe
        simp only [hAeF, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
        cases hSt2 : vfsOps.stat true p sc with
        | mk rs2 s2 =>
          have hs2 : s2 = sc := (congrArg Prod.snd hSt2).symm
          cases rs2 with
          | error _ => subst hs2; exact htc
          | ok st2 =>
            by_cases hD2 : (st2.kind == .dir) = true <;>
              simp only [hD2, ↓reduceIte, Bool.false_eq_true] <;> subst hs2 <;> exact htc


private theorem vfsMkdirImplM_noFileTree (p : String) (parents existOk : Bool) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.mkdirImplM vfsOps p parents existOk st).2.tree := by
  unfold Internal.mkdirImplM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hSt : vfsOps.stat false p st with
  | mk rSt s1 =>
    have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
    cases rSt with
    | ok ts =>
      dsimp only
      by_cases hD : (existOk && ts.kind == .dir) = true
      · simp only [hD, ↓reduceIte]; subst hs1; exact ht
      · simp only [hD, Bool.false_eq_true, ↓reduceIte]
        by_cases hS : (existOk && ts.kind == .symlink) = true
        · simp only [hS, ↓reduceIte, Bind.bind, bind, StateT.bind]
          cases hSt2 : vfsOps.stat true p s1 with
          | mk rSt2 s2 =>
            have hs2 : s2 = s1 := (congrArg Prod.snd hSt2).symm
            cases rSt2 with
            | error _ => subst hs2; subst hs1; exact ht
            | ok tgtSt =>
              dsimp only
              by_cases hTD : (tgtSt.kind == .dir) = true <;>
                simp only [hTD, ↓reduceIte, Bool.false_eq_true] <;> subst hs2 <;> subst hs1 <;> exact ht
        · simp only [hS, Bool.false_eq_true, ↓reduceIte]; subst hs1; exact ht
    | error e =>
      dsimp only
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte]; subst hs1; exact ht
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
        by_cases hP : (!parents) = true
        · simp only [hP, ↓reduceIte]
          cases existOk with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact vfsCreateDirPure_noFileTree s1 p (by subst hs1; exact ht)
          | true =>
            simp only [↓reduceIte]
            exact vfsCreateDirExistOkM_noFileTree p s1 (by subst hs1; exact ht)
        · have hPF : (!parents) = false := Bool.eq_false_iff.mpr hP
          simp only [hPF, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
          cases hAnc : Internal.ensureAncestorsM vfsOps (Internal.ancestorChain p p.toList.length) s1 with
          | mk ra sa =>
            have hta : NoFileTree sa.tree := by
              have hSaEq : sa = (Internal.ensureAncestorsM vfsOps (Internal.ancestorChain p p.toList.length) s1).2 :=
                (congrArg Prod.snd hAnc).symm
              rw [hSaEq]; exact vfsEnsureAncestorsM_noFileTree (Internal.ancestorChain p p.toList.length) s1 (by subst hs1; exact ht)
            cases ra with
            | error _ => exact hta
            | ok _ =>
              cases existOk with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact vfsCreateDirPure_noFileTree sa p hta
              | true =>
                simp only [↓reduceIte]
                exact vfsCreateDirExistOkM_noFileTree p sa hta


private theorem buggyCopyTreeGoNoLoopM_never_invalidInput :
    ∀ fuel src dst dirsExistOk st, NoFileTree st.tree →
      NoFileTree (buggyCopyTreeGoNoLoopM src dst dirsExistOk fuel st).2.tree ∧
      (∀ e, (buggyCopyTreeGoNoLoopM src dst dirsExistOk fuel st).1 = .error e → e.kind ≠ .invalidInput) := by
  have hStatNe : ∀ f p s err, (vfsOps.stat f p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro f p s err hs; dsimp only [vfsOps, vfsStatPure] at hs
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) f 1024 with
    | ok _ => simp [hR] at hs
    | error err' => simp [hR] at hs; cases hs; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
  have hRpNe : ∀ p s err, (vfsOps.realPath p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hr; dsimp only [vfsOps, vfsRealPathPure] at hr
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
    | ok _ => simp [hR] at hr
    | error err' => simp [hR] at hr; cases hr; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
  have hListNe : ∀ p s err, (Internal.listDirSortedM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hl
    dsimp only [Internal.listDirSortedM, vfsOps, vfsReadDirPure, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hl
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
    | error err' => simp [hR] at hl; cases hl; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
    | ok pNode =>
      rcases pNode with ⟨_, nd⟩
      cases nd with
      | dir m =>
        by_cases hm : ((m / 256) % 2 == 0) = true
        · simp [hR, hm, StateT.pure] at hl; cases hl; intro hk; cases hk
        · have hmF : ((m / 256) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
          simp [hR, hmF, StateT.pure] at hl
      | file _ _ => simp [hR] at hl; cases hl; intro hk; cases hk
      | symlink _ _ => simp [hR] at hl; cases hl; intro hk; cases hk
  intro fuel; induction fuel with
  | zero =>
    intro _ _ _ st ht
    simp only [buggyCopyTreeGoNoLoopM, pure, StateT.pure]
    exact ⟨ht, fun _ h => by cases h; intro hk; cases hk⟩
  | succ fuel ih =>
    intro src dst dirsExistOk st ht
    simp only [buggyCopyTreeGoNoLoopM, Bind.bind, bind, StateT.bind, Pure.pure, pure]
    cases hSt : vfsOps.stat true src st with
    | mk rs s1 =>
      have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
      cases rs with
      | error e1 =>
        dsimp only [StateT.pure]
        exact ⟨by subst hs1; exact ht, fun eOut h => by cases h; exact hStatNe true src st _ (congrArg Prod.fst hSt)⟩
      | ok st1 =>
        dsimp only
        by_cases hND : (st1.kind != .dir) = true
        · simp only [hND, ↓reduceIte, StateT.pure]
          exact ⟨by subst hs1; exact ht, fun eOut h => by cases h; intro hk; cases hk⟩
        · have hNDF : (st1.kind != .dir) = false := Bool.eq_false_iff.mpr hND
          simp only [hNDF, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind]
          cases hRp : vfsOps.realPath src s1 with
          | mk rr s2 =>
            have hs2 : s2 = s1 := (congrArg Prod.snd hRp).symm
            cases rr with
            | error e2 =>
              exact ⟨by subst hs2; subst hs1; exact ht, fun eOut h => by cases h; exact hRpNe src s1 _ (congrArg Prod.fst hRp)⟩
            | ok _ =>
              dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
              cases hLs : Internal.listDirSortedM vfsOps src s2 with
              | mk rl s3 =>
                have hs3 : s3 = s2 := by
                  have hSnd : s3 = (Internal.listDirSortedM vfsOps src s2).2 := (congrArg Prod.snd hLs).symm
                  rw [hSnd]
                  dsimp only [Internal.listDirSortedM, vfsOps, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  cases vfsReadDirPure s2 src <;> rfl
                cases rl with
                | error e3 =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  exact ⟨by subst hs3; subst hs2; subst hs1; exact ht, fun eOut h => by cases h; exact hListNe src s2 _ (congrArg Prod.fst hLs)⟩
                | ok names =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  cases hMk : Internal.mkdirImplM vfsOps dst true dirsExistOk s3 with
                  | mk rm s4 =>
                    have ht4 : NoFileTree s4.tree := by
                      have hEq : s4 = (Internal.mkdirImplM vfsOps dst true dirsExistOk s3).2 := (congrArg Prod.snd hMk).symm
                      rw [hEq]; apply vfsMkdirImplM_noFileTree
                      subst hs3; subst hs2; subst hs1; exact ht
                    cases rm with
                    | error e4 =>
                      dsimp only [StateT.pure, Pure.pure, pure]
                      exact ⟨ht4, fun eOut h => by cases h; exact vfsOps_mkdir_never_invalidInput dst true dirsExistOk s3 _ (congrArg Prod.fst hMk)⟩
                    | ok _ =>
                      apply forEachChildM_invariant (fun s => NoFileTree s.tree) _ _ names.toList s4 ht4
                      intro n sChildSt hChildHt
                      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                      cases hSc : vfsOps.stat true (Internal.join src n) sChildSt with
                      | mk rsc sc2 =>
                        have hsc2 : sc2 = sChildSt := (congrArg Prod.snd hSc).symm
                        cases rsc with
                        | error e5 =>
                          dsimp only [StateT.pure, Pure.pure, pure]
                          exact ⟨by subst hsc2; exact hChildHt, fun eOut h => by cases h; exact hStatNe true _ sChildSt _ (congrArg Prod.fst hSc)⟩
                        | ok cst =>
                          have hSc1 : vfsStatPure sChildSt true (Internal.join src n) = .ok cst := congrArg Prod.fst hSc
                          have hResTrue : ∃ nd, vfsResolveSegs sChildSt.nodes "/"
                              (vfsSplitSegs (vfsAbsNorm sChildSt.cwd (Internal.join src n))) true 1024 = .ok nd ∧
                              vfsToStat nd.2 = cst := by
                            unfold vfsStatPure at hSc1
                            cases hR : vfsResolveSegs sChildSt.nodes "/"
                                (vfsSplitSegs (vfsAbsNorm sChildSt.cwd (Internal.join src n))) true 1024 with
                            | error _ => simp [hR] at hSc1
                            | ok nd =>
                              simp only [hR, Except.ok.injEq] at hSc1
                              exact ⟨nd, rfl, hSc1⟩
                          rcases hResTrue with ⟨⟨_, nd⟩, hR, hStEq⟩
                          have ⟨m, hNd⟩ := vfsResolveSegs_true_noFile_isDir sChildSt.tree hChildHt 1024 "/" _ _ _ hR
                          subst hNd
                          have hCstDir : cst.kind = .dir := by rw [← hStEq]; rfl
                          have hD : (cst.kind == .dir) = true := by rw [hCstDir]; rfl
                          dsimp only
                          simp only [hD, ↓reduceIte]
                          exact ih _ _ dirsExistOk sc2 (by subst hsc2; exact hChildHt)


private theorem reach_fs_vfs_copyTree_loopRejected_noFile :
    ∃ (st : VfsState) (src : String), NoFileTree st.tree ∧
      (∃ stRoot, ((vfsApi.stat "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
        (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 ∧
        ((vfsApi.resolve "/").run st).1 = .ok "/") ∧
      (∃ stSrc, ((vfsApi.stat src).run st).1 = .ok stSrc ∧ stSrc.kind = .dir) ∧
      (∃ c, ((vfsApi.resolve src).run st).1 = .ok c ∧ vfsApi.isAbsolute c ∧ c ≠ "/" ∧
        c ≠ "/loop_dst" ∧ ((vfsApi.resolve (vfsApi.join src "self")).run st).1 = .ok c) ∧
      ((vfsApi.listDir src).run st).1 = .ok #["self"] ∧
      (∃ stSelf, ((vfsApi.stat (vfsApi.join src "self")).run st).1 = .ok stSelf ∧ stSelf.kind = .dir) ∧
      ((vfsApi.lstat "/loop_dst").run st).1.isOk = false := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s =>
        if s == "src" then
          some (.dir 0o755 (fun s2 => if s2 == "self" then some (.symlink "/src" 0o777) else none))
        else none)
      keys := ["/", "/src", "/src/self"]
      cwd := "/"
      nonce := 0 }
  have hNoFile : NoFileTree st.tree := by
    intro segs bs m hGet
    cases segs with
    | nil => simp [st, vfsTreeGet] at hGet
    | cons s rest =>
      simp only [st, vfsTreeGet] at hGet
      by_cases hS : (s == "src") = true
      · simp only [hS, ↓reduceIte] at hGet
        cases rest with
        | nil => simp [vfsTreeGet] at hGet
        | cons s2 rest2 =>
          simp only [vfsTreeGet] at hGet
          by_cases hS2 : (s2 == "self") = true
          · simp only [hS2, ↓reduceIte] at hGet
            cases rest2 <;> simp [vfsTreeGet] at hGet
          · simp [hS2] at hGet
      · simp [hS] at hGet
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hSelfResolve : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (vfsApi.join "/src" "self"))) true 1024 =
      .ok ("/src", .dir 0o755) := by
    have hJ : vfsApi.join "/src" "self" = "/src/self" := by decide
    have hA : vfsAbsNorm st.cwd "/src/self" = "/src/self" := by decide
    have hS : vfsSplitSegs "/src/self" = ["src", "self"] := by decide
    have hS_src : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hJ, hA, hS]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/src" "self" = "/src/self" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src/self" = some (.symlink "/src" 0o777) from rfl]; dsimp only
    rw [show ((Internal.parent "/src/self").getD "/") = "/src" from by decide,
        show Internal.isAbsolute "/src" = true from by decide]
    simp only [↓reduceIte, show Internal.normPath "/src" = "/src" from by decide, hS_src]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSelf : ((vfsApi.resolve (vfsApi.join "/src" "self")).run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hStatSelf : ((vfsApi.stat (vfsApi.join "/src" "self")).run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #["self"] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src", "/src/self"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hN2 : (st.nodes "/src/self").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    have hPre2 : "/src/".toList.isPrefixOf "/src/self".toList = true := by decide
    have hDrop2 : "/src/self".toList.drop "/src/".toList.length = "self".toList := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, hN2, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src/self" != "/src") = true from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, hPre2, hDrop2,
      show (!"self".toList.isEmpty && !('/' ∈ "self".toList)) = true from by decide,
      show String.ofList "self".toList = "self" from by decide,
      Bool.true_and, Bool.false_and, List.mergeSort_singleton]
  have hLstatLoop : ((vfsApi.lstat "/loop_dst").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/loop_dst" = "/loop_dst" := by decide
    have hS : vfsSplitSegs "/loop_dst" = ["loop_dst"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/loop_dst" = none from rfl]; rfl
  exact ⟨st, "/src", hNoFile,
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩,
    hListSrc, ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩, hLstatLoop⟩


example : ¬ AllPass (test_fs_vfs_copyTree_loopRejected
    { vfsApi with copyTree := fun src dst ok => buggyCopyTreeGoNoLoopM src dst ok 4096 }) := by
  intro h
  rcases reach_fs_vfs_copyTree_loopRejected_noFile with
    ⟨st, src, hNoFile, hRoot, hSrc, hCan, hList, hSelf, hLstat⟩
  have hFail := h st src hRoot hSrc hCan hList hSelf hLstat
  dsimp only [StateT.run, assert] at hFail
  rcases hFail with ⟨⟨e, hErr, hKind⟩, _⟩
  exact (buggyCopyTreeGoNoLoopM_never_invalidInput 4096 src "/loop_dst" false st hNoFile).2 e hErr hKind


private def buggyWalkR2I01 (root : String) : StateM VfsState (Except FsError (Array WalkEntry)) := do
  match ← vfsOps.stat true root with
  | .ok _ => Internal.walkImplM vfsOps root
  | .error _ => return .error { kind := .notFound, path := some root, message := s!"not found: {root}" }


example : ¬ AllPass (test_fs_vfs_walk_preservesStatError { vfsApi with walk := buggyWalkR2I01 }) := by
  intro h
  let st : VfsState :=
    { tree := vfsEmptyDir 0o000
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/locked"
  have hStatPerm : vfsStatPure st true "/locked" =
      .error { kind := .permissionDenied, path := some "/", message := "permission denied: /" } := by
    dsimp only [vfsStatPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/locked" = "/locked" from by decide,
        show vfsSplitSegs "/locked" = ["locked"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o000) from rfl]; rfl
  dsimp only [vfsApi, Internal.mkApiM, buggyWalkR2I01, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at hFail
  rw [show vfsOps.stat true "/locked" st = (vfsStatPure st true "/locked", st) from rfl, hStatPerm] at hFail
  simp only at hFail
  rcases hFail with ⟨⟨⟨e, he, hk⟩, _⟩, _⟩
  cases he
  simp at hk


private def buggySuffixesR3I01 (path : String) : Array String :=
  match Internal.name path with
  | none => #[]
  | some n =>
    match n.toList.reverse with
    | '.' :: _ => #[]
    | _ =>
      let stripped := n.toList.dropWhile (· == '.')
      match Internal.splitCharList '.' stripped with
      | [] | [_] => #[]
      | _ :: exts => ((exts.filter (!·.isEmpty)).map fun cs => "." ++ String.ofList cs).toArray


example : ¬ AllPass (test_fs_suffixes_doubleDot { defaultApi with suffixes := buggySuffixesR3I01 }) := by
  intro h
  have hFail := h "a" (by decide) (by decide) (by decide)
  have hVal : buggySuffixesR3I01 "a..ext" = #[".ext"] := by decide
  dsimp only [assert] at hFail
  have hCat : ("a" ++ "..ext") = "a..ext" := by decide
  rw [hCat, hVal] at hFail
  exact absurd hFail.1 (by decide)


private def buggyCopyTreeR3I02 (src dst : String) (dirsExistOk : Bool) : StateM VfsState (Except FsError Unit) :=
  Internal.copyTreeGoM vfsOps src dst dirsExistOk [] 4096


example : ¬ AllPass (test_fs_vfs_copyTree_selfCopyRejected { vfsApi with copyTree := buggyCopyTreeR3I02 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResDstBad : ((vfsApi.resolve "/src/sub").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src/sub" = "/src/sub" from by decide,
        show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src/sub" = none from rfl]; rfl
  have hFail := h st "/src" "/src/sub"
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
    ⟨"/src", hResSrc, by decide, by decide, hResSrc,
      Or.inr ⟨"sub", by decide, by decide, by decide, by decide, rfl, hResDstBad⟩⟩
  have hSubNone : st.nodes "/src/sub" = none := rfl
  have hListSrc : (Internal.listDirSortedM vfsOps "/src").run st = (.ok #[], st) := by
    dsimp only [Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  let stSub : VfsState :=
    { st with
      tree := vfsTreeSet st.tree ["src", "sub"] (some (vfsEmptyDir 0o755))
      keys := "/src/sub" :: st.keys }
  have hMkSub : Internal.mkdirImplM vfsOps "/src/sub" true false st = (.ok (), stSub) := by
    have hPreSub : vfsStatPure st false "/src/sub" =
        .error { kind := .notFound, path := some "/src/sub", message := "no such file or directory: /src/sub" } := by
      dsimp only [vfsStatPure]
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src/sub" = "/src/sub" from by decide,
          show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/" "src" = "/src" from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
      unfold vfsResolveSegs; rw [hSubNone]; rfl
    have hStSrcOk : vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) := hStatSrc
    have hAnc : Internal.ensureAncestorsM vfsOps ["/src"] st = (.ok (), st) := by
      dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, bind, StateT.bind, pure, StateT.pure]
      rw [show vfsOps.stat true "/src" st = (vfsStatPure st true "/src", st) from rfl, hStSrcOk]
      rfl
    have hCre : vfsCreateDirPure st "/src/sub" = (.ok (), stSub) := by
      have hParSub : Internal.splitLastAux ["src", "sub"] [] = some (["src"], "sub") := by decide
      have hParSrc : vfsResolveSegs st.nodes "/" ["src"] true 512 = .ok ("/src", .dir 0o755) := by
        unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/" "src" = "/src" from by decide]
        unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
      have hPreSub' : vfsResolveSegs st.nodes "/" ["src", "sub"] false 1024 =
          .error { kind := .notFound, path := some "/src/sub", message := "no such file or directory: /src/sub" } := by
        unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/" "src" = "/src" from by decide]
        unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
        unfold vfsResolveSegs; rw [hSubNone]; rfl
      dsimp only [vfsCreateDirPure]
      rw [show vfsAbsNorm st.cwd "/src/sub" = "/src/sub" from by decide,
          show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide, hPreSub']
      dsimp only
      rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, hParSub]
      rw [hParSrc]; dsimp only
      rw [show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/src" "sub" = "/src/sub" from by decide, hSubNone]
      simp [stSub, show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/src/sub" st = (vfsStatPure st false "/src/sub", st) from rfl, hPreSub]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        show Internal.ancestorChain "/src/sub" "/src/sub".toList.length = ["/src"] from by decide]
    have hBindSub :
        StateT.bind (Internal.ensureAncestorsM vfsOps ["/src"])
          (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/src/sub") st =
        vfsOps.createDir "/src/sub" st := by
      dsimp only [Bind.bind, StateT.bind]
      rw [hAnc]
    change StateT.bind (Internal.ensureAncestorsM vfsOps ["/src"])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/src/sub") st = (.ok (), stSub)
    rw [hBindSub]
    exact hCre
  have hBuggy : buggyCopyTreeR3I02 "/src" "/src/sub" false st = (.ok (), stSub) := by
    unfold buggyCopyTreeR3I02 Internal.copyTreeGoM
    dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true "/src" st = (vfsStatPure st true "/src", st) from rfl]
    have hStS : vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) := hStatSrc
    rw [hStS]
    dsimp only
    rw [show ((vfsToStat (.dir 0o755)).kind != .dir) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath "/src" st = (vfsRealPathPure st "/src", st) from rfl]
    have hRpS : vfsRealPathPure st "/src" = .ok "/src" := hResSrc
    rw [hRpS]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    dsimp only [StateT.run] at hListSrc
    rw [hListSrc]
    dsimp only [StateT.bind]
    rw [hMkSub]
    simp [Internal.forEachChildM, pure]
    rfl
  dsimp only [StateT.run, assert] at hFail
  rw [hBuggy] at hFail
  rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he


end LeanSwe.Fs.Proofs

import LeanSweProofs.Fs.Proofs.PurePathProofs
import LeanSweProofs.Fs.Proofs.VfsShared

namespace LeanSwe.Fs.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs
open LeanSwe.Fs.Model (LockHandle RawFsOpsM RawFsOps RawDirOpsM RawDirOps
  VfsNode VfsTree VfsState vfsTreeTopNode vfsEmptyDir vfsTreeGet nodeAt vfsTreeSet
  vfsAbsNorm vfsSplitSegs isCanonPath vfsTreeNodes vfsChildPath vfsResolveSegs
  vfsToStat vfsStatPure vfsRealPathPure vfsCreateDirPure vfsReadDirPure
  vfsWriteBytesPure hasLockConflict vfsAcquireLockPure vfsReleaseLockPure
  isValidRawPath vfsReadBytesPure vfsCreateFileNewPure vfsRenamePure vfsOps)
open LeanSwe.Fs.ProofsInternal

private theorem maxLockId_ge :
    ∀ (locks : List (Nat × String × LockMode)) (i : Nat) (p : String) (m : LockMode),
      (i, p, m) ∈ locks → i ≤ maxLockId locks
  | (hdId, _, _) :: rest, i, p, m, h => by
    simp only [List.mem_cons] at h
    rcases h with heq | hmem
    · cases heq
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (maxLockId_ge rest i p m hmem) (Nat.le_max_right _ _)

private theorem freshLockId_not_mem (st : VfsState) (p : String) (m : LockMode) :
    (freshLockId st, p, m) ∉ st.locks := by
  intro hmem
  have hle := maxLockId_ge st.locks (freshLockId st) p m hmem
  have hgt : maxLockId st.locks < freshLockId st := by
    unfold freshLockId
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  omega

private theorem filter_ne_fresh_eq :
    ∀ (l : List (Nat × String × LockMode)) (k : Nat),
      (∀ p m, (k, p, m) ∉ l) →
      l.filter (fun (id, _, _) => id != k) = l
  | [], _, _ => rfl
  | (i, p, m) :: rest, k, hk => by
    have hne : i ≠ k := fun heq => hk p m (heq ▸ List.mem_cons_self)
    have hbeq : (i != k) = true := bne_iff_ne.mpr hne
    have hrest : ∀ p' m', (k, p', m') ∉ rest := fun p' m' hm => hk p' m' (List.mem_cons_of_mem _ hm)
    simp [List.filter, hbeq, filter_ne_fresh_eq rest k hrest]

private theorem vfsTreeGet_set_file (bs : ByteArray) (m' : Nat) :
    ∀ (segs : List String) (lastSeg : String) (t : VfsTree) (q : List String),
      (∃ dm dch, vfsTreeGet t segs = some (.dir dm dch)) →
      vfsTreeGet t (segs ++ [lastSeg]) = none →
      (vfsTreeGet (vfsTreeSet t (segs ++ [lastSeg]) (some (.file bs m'))) q).map vfsTreeTopNode =
        if q == (segs ++ [lastSeg]) then some (.file bs m') else (vfsTreeGet t q).map vfsTreeTopNode := by
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
          | nil => simp [vfsTreeGet, vfsTreeTopNode]
          | cons rh rt =>
            simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte]
            simp [hChNone]
        · have hNe : (qh == lastSeg) = false := beq_false_of_ne hEq
          have hListNe : ((qh :: qt) == [lastSeg]) = false := by simp [hEq]
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
        have hSubDir : ∃ dm dch, vfsTreeGet sub rest = some (.dir dm dch) :=
          ⟨dm, dch, by simpa [vfsTreeGet, hCh] using hGet⟩
        have hSubNone : vfsTreeGet sub (rest ++ [lastSeg]) = none := by
          simpa [vfsTreeGet, hCh] using hNone
        have hNonEmpty : rest ++ [lastSeg] ≠ [] := by simp
        cases hRest : rest ++ [lastSeg] with
        | nil => exact absurd hRest hNonEmpty
        | cons rhd rtl =>
          have hSetEq : vfsTreeSet (.dir mode ch) ((seg :: rest) ++ [lastSeg]) (some (.file bs m')) =
              .dir mode (fun s => if s == seg then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) else ch s) := by
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
                    if s == qh then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) else ch s) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) qt).map vfsTreeTopNode := by
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

private theorem vfsTreeNodes_insert_file (t : VfsTree) (parCanon lastSeg : String)
    (bs : ByteArray) (m' : Nat)
    (hParCanon : isCanonPath parCanon = true)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hParDir : ∃ dm, vfsTreeNodes t parCanon = some (.dir dm))
    (hNewNone : vfsTreeNodes t (vfsChildPath parCanon lastSeg) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file bs m'))) =
      fun k => if k == vfsChildPath parCanon lastSeg then some (.file bs m') else vfsTreeNodes t k := by
  have ⟨hChildCanon, hChildSp⟩ := vfsChildPath_valid parCanon lastSeg hParCanon hLastValid
  have hParTreeDir : ∃ dm dch, vfsTreeGet t (vfsSplitSegs parCanon) = some (.dir dm dch) := by
    rcases hParDir with ⟨dm, hPar⟩
    simp only [vfsTreeNodes, nodeAt, hParCanon, ↓reduceIte] at hPar
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon) with
    | none => simp [hGet] at hPar
    | some sub =>
      cases sub with
      | dir dm' dch => exact ⟨dm', dch, rfl⟩
      | file _ _ => simp [hGet, vfsTreeTopNode] at hPar
      | symlink _ _ => simp [hGet, vfsTreeTopNode] at hPar
  have hNewTreeNone : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) = none := by
    have hNn := hNewNone
    simp only [vfsTreeNodes, nodeAt, hChildCanon, ↓reduceIte, hChildSp] at hNn
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) with
    | none => rfl
    | some _ => simp [hGet] at hNn
  funext k
  by_cases hKCanon : isCanonPath k = true
  · simp only [vfsTreeNodes, nodeAt, hKCanon, ↓reduceIte, hChildSp]
    rw [vfsTreeGet_set_file bs m' (vfsSplitSegs parCanon) lastSeg t (vfsSplitSegs k) hParTreeDir hNewTreeNone]
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

private theorem vfsResolveSegs_dir_child_nofollow (nodes : String → Option VfsNode)
    (lastSeg parCanon : String) (parMode : Nat) (hExec : ((parMode / 64) % 2 == 0) = false)
    (nd : VfsNode) (hChild : nodes (vfsChildPath parCanon lastSeg) = some nd) :
    ∀ fuel cur parSegs,
      vfsResolveSegs nodes cur parSegs true fuel = .ok (parCanon, .dir parMode) →
      vfsResolveSegs nodes cur (parSegs ++ [lastSeg]) false (fuel + 1) =
        .ok (vfsChildPath parCanon lastSeg, nd) := by
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
      | some nd' =>
        simp only [hNode] at hOk
        cases nd' with
        | file _ _ => simp at hOk
        | dir m =>
          simp only [Prod.mk.injEq, Except.ok.injEq, VfsNode.dir.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          simp only [List.nil_append, vfsResolveSegs, hNode, hExec, Bool.false_eq_true, ↓reduceIte, hChild]
          cases nd with
          | file _ _ => rfl
          | dir _ => rfl
          | symlink _ _ => rfl
        | symlink target m =>
          simp only [List.nil_append, vfsResolveSegs, hNode]
          exact ih "/" (vfsSplitSegs (Model.normPath
            (if Model.isAbsolute target then target else Model.join ((Model.parent cur).getD "/") target))) hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd' =>
        simp only [hNode] at hOk
        cases nd' with
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
          have hAssoc : vfsSplitSegs (Model.normPath
              (if Model.isAbsolute target then target else Model.join ((Model.parent cur).getD "/") target)) ++
              seg :: (rest ++ [lastSeg]) =
            (vfsSplitSegs (Model.normPath
              (if Model.isAbsolute target then target else Model.join ((Model.parent cur).getD "/") target)) ++
              seg :: rest) ++ [lastSeg] := by
            simp [List.append_assoc]
          rw [hAssoc]
          exact ih "/" _ hOk

private theorem vfsResolveSegs_true_ok_implies_false_ok (nodes : String → Option VfsNode) :
    ∀ fuel cur segs res,
      vfsResolveSegs nodes cur segs true fuel = .ok res →
      ∃ res', vfsResolveSegs nodes cur segs false fuel = .ok res' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [vfsResolveSegs] at h
  | succ f ih =>
    intro cur segs res hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        cases nd with
        | file bs m => exact ⟨(cur, .file bs m), by simp [vfsResolveSegs, hNode]⟩
        | dir m => exact ⟨(cur, .dir m), by simp [vfsResolveSegs, hNode]⟩
        | symlink t m => exact ⟨(cur, .symlink t m), by simp [vfsResolveSegs, hNode]⟩
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
            rcases ih (vfsChildPath cur seg) rest res hOk with ⟨r', hr'⟩
            exact ⟨r', by simp [vfsResolveSegs, hNode, hef, hr']⟩
        | symlink target m =>
          rcases ih "/" _ res hOk with ⟨r', hr'⟩
          exact ⟨r', by simp [vfsResolveSegs, hNode, hr']⟩

private theorem hasLockConflict_exclusive_false (locks : List (Nat × String × LockMode))
    (canon : String) (mode : LockMode) :
    hasLockConflict locks canon .exclusive = false →
    hasLockConflict locks canon mode = false := by
  intro h
  simp only [hasLockConflict, List.any_eq_false] at h ⊢
  intro x hx hMatch
  apply h x hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hMatch ⊢
  exact ⟨hMatch.1, Or.inl rfl⟩

private theorem hasLockConflict_cons_self_mode (id : Nat) (canon : String)
    (outerMode innerMode : LockMode) (locks : List (Nat × String × LockMode))
    (hEx : outerMode = .exclusive ∨ innerMode = .exclusive) :
    hasLockConflict ((id, canon, outerMode) :: locks) canon innerMode = true := by
  have hSelf : (LockMode.exclusive == LockMode.exclusive) = true := rfl
  rcases hEx with rfl | rfl <;> simp [hasLockConflict, hSelf]

private theorem vfsReleaseLockPure_fresh (st st1 : VfsState) (key path : String) (mode : LockMode)
    (hTrees : st1 = { st with locks := (freshLockId st, key, mode) :: st.locks, nextLockId := freshLockId st } ∨
      ∃ newTree newKeys, st1 = { st with tree := newTree, keys := newKeys, locks := (freshLockId st, key, mode) :: st.locks, nextLockId := freshLockId st }) :
    vfsReleaseLockPure st1 { handleId := freshLockId st, path := path, mode := mode } =
      (.ok (), { st1 with locks := st.locks }) := by
  have hNeZero : (freshLockId st == 0) = false := beq_false_of_ne (Nat.succ_ne_zero _)
  have hFilter := filter_ne_fresh_eq st.locks (freshLockId st) (freshLockId_not_mem st)
  rcases hTrees with rfl | ⟨_, _, rfl⟩ <;>
    simp [vfsReleaseLockPure, hNeZero, hFilter]

private theorem vfsAcquireLock_ok_step (st : VfsState) (path : String) (mode : LockMode)
    (createIfMissing nb : Bool) (h : LockHandle) (st1 : VfsState)
    (hAcq : vfsAcquireLockPure st path mode createIfMissing nb = (.ok h, st1)) :
    (h = { handleId := freshLockId st, path := path, mode := mode }) ∧
    ((∃ canon,
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .ok (canon, .file ByteArray.empty 0) ∧ False) ∨
      (∃ canon bs m,
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .ok (canon, .file bs m) ∧
        hasLockConflict st.locks canon mode = false ∧
        st1 = { st with locks := (freshLockId st, canon, mode) :: st.locks, nextLockId := freshLockId st }) ∨
      (∃ parSegs lastSeg parCanon parMode e,
        createIfMissing = true ∧
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .error e ∧
        e.kind = .notFound ∧
        Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] = some (parSegs, lastSeg) ∧
        vfsResolveSegs st.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode) ∧
        ((parMode / 128) % 2 == 0) = false ∧
        ((parMode / 64) % 2 == 0) = false ∧
        st.nodes (vfsChildPath parCanon lastSeg) = none ∧
        hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = false ∧
        st1 = { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: st.keys
          locks := (freshLockId st, vfsChildPath parCanon lastSeg, mode) :: st.locks
          nextLockId := freshLockId st })) := by
  rw [vfsAcquireLockPure_unfold] at hAcq
  split at hAcq
  · simp at hAcq
  · cases hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 with
    | ok pair =>
      rcases pair with ⟨canon, nd⟩
      simp only [hRes] at hAcq
      cases nd with
      | dir _ => simp at hAcq
      | symlink _ _ => simp at hAcq
      | file bs m =>
        by_cases hConf : hasLockConflict st.locks canon mode = true
        · simp [hConf] at hAcq
        · have hConfF : hasLockConflict st.locks canon mode = false := Bool.eq_false_iff.mpr hConf
          simp only [hConfF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hAcq
          rcases hAcq with ⟨rfl, rfl⟩
          exact ⟨rfl, Or.inr (Or.inl ⟨canon, bs, m, rfl, hConfF, rfl⟩)⟩
    | error e =>
      simp only [hRes] at hAcq
      by_cases hNf : (e.kind != .notFound) = true
      · simp [hNf] at hAcq
      · have hNfEq : e.kind = .notFound := by
          cases hk : e.kind <;> rw [hk] at hNf
          all_goals first | rfl | exact absurd hNf (by decide)
        have hNfF : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hAcq
        cases hCre : createIfMissing
        · simp [hCre] at hAcq
        · simp only [hCre, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAcq
          cases hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] with
          | none => simp [hSplit] at hAcq
          | some sp =>
            rcases sp with ⟨parSegs, lastSeg⟩
            simp only [hSplit] at hAcq
            cases hPar : vfsResolveSegs st.nodes "/" parSegs true 512 with
            | error pe => simp [hPar] at hAcq
            | ok parPair =>
              rcases parPair with ⟨parCanon, parNd⟩
              simp only [hPar] at hAcq
              cases parNd with
              | file _ _ => simp at hAcq
              | symlink _ _ => simp at hAcq
              | dir parMode =>
                by_cases hPerm : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = true
                · simp [hPerm] at hAcq
                · have hPermF : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false :=
                    Bool.eq_false_iff.mpr hPerm
                  have hW : ((parMode / 128) % 2 == 0) = false := by
                    cases h1 : ((parMode / 128) % 2 == 0) <;> simp_all
                  have hX : ((parMode / 64) % 2 == 0) = false := by
                    cases h2 : ((parMode / 64) % 2 == 0) <;> simp_all
                  simp only [hPermF, Bool.false_eq_true, ↓reduceIte] at hAcq
                  by_cases hConf : hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = true
                  · simp [hConf] at hAcq
                  · have hConfF : hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = false :=
                      Bool.eq_false_iff.mpr hConf
                    simp only [hConfF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hAcq
                    rcases hAcq with ⟨rfl, rfl⟩
                    have hNone : st.nodes (vfsChildPath parCanon lastSeg) = none := by
                      cases hCur : st.nodes (vfsChildPath parCanon lastSeg) with
                      | none => rfl
                      | some nd =>
                        exfalso
                        have hAllSegs : vfsSplitSegs (vfsAbsNorm st.cwd path) = parSegs ++ [lastSeg] := by
                          simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] parSegs lastSeg hSplit
                        have hStep := vfsResolveSegs_dir_child_nofollow st.nodes lastSeg parCanon parMode hX nd hCur 512 "/" parSegs hPar
                        have h1024 := vfsResolveSegs_fuel_mono st.nodes 513 1024 "/" (parSegs ++ [lastSeg]) false
                          (vfsChildPath parCanon lastSeg, nd) (by omega) hStep
                        rw [← hAllSegs, hRes] at h1024
                        cases h1024
                    exact ⟨rfl, Or.inr (Or.inr ⟨parSegs, lastSeg, parCanon, parMode, e, rfl, rfl, hNfEq, rfl, hPar, hW, hX, hNone, hConfF, rfl⟩)⟩

private theorem vfsWithFileLock_action_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (action : StateM VfsState (Except FsError α)) :
    (vfsApi.withFileLock path mode createIfMissing action).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing false with
      | (.error e, st') => (.error e, st')
      | (.ok h, st1) =>
        let (r, st2) := action.run st1
        let (relRes, s₁) := vfsReleaseLockPure st2 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok a, s₁)
          | .error re => (.error re, s₁) := by
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, Internal.withFileLockImplM, Internal.bracketLockM,
    vfsOps, StateT.run, StateT.tryFinally, Id.finally,
    tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
  cases hA : vfsAcquireLockPure s₀ path mode createIfMissing false with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok h =>
      dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      cases hAct : action.run st1 with
      | mk r st2 =>
        dsimp only [StateT.run] at hAct
        rw [hAct]
        dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
        cases vfsReleaseLockPure st2 h with
        | mk relRes s₁ =>
          cases r with
          | error e => rfl
          | ok a => cases relRes <;> rfl

private theorem vfsWithFileLock_pure_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (r : Except FsError α) :
    (vfsApi.withFileLock path mode createIfMissing (pure r)).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing false with
      | (.error e, st') => (.error e, st')
      | (.ok h, st1) =>
        let (relRes, s₁) := vfsReleaseLockPure st1 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok a, s₁)
          | .error re => (.error re, s₁) :=
  vfsWithFileLock_action_step s₀ path mode createIfMissing (pure r)

private theorem vfsTryWithFileLock_pure_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (r : Except FsError α) :
    (vfsApi.tryWithFileLock path mode createIfMissing (pure r)).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing true with
      | (.error e, st') =>
        if e.kind == .wouldBlock then (.ok none, st') else (.error e, st')
      | (.ok h, st1) =>
        let (relRes, s₁) := vfsReleaseLockPure st1 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok (some a), s₁)
          | .error re => (.error re, s₁) := by
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, Internal.tryWithFileLockImplM, Internal.bracketLockM,
    vfsOps, StateT.run, StateT.tryFinally, Id.finally,
    tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
  cases hA : vfsAcquireLockPure s₀ path mode createIfMissing true with
  | mk res st1 =>
    cases res with
    | error e =>
      dsimp only
      by_cases hw : (e.kind == .wouldBlock) = true <;> simp [hw] <;> rfl
    | ok h =>
      dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      cases vfsReleaseLockPure st1 h with
      | mk relRes s₁ =>
        cases r with
        | error e => rfl
        | ok a => cases relRes <;> rfl

private theorem vfsAcquireLock_after_exclusive_probe (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool)
    (hProbe : ((vfsApi.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ())) :
    isValidLockPath path = true ∧
    ((∃ canon bs m,
        vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 = .ok (canon, .file bs m) ∧
        hasLockConflict s₀.locks canon .exclusive = false ∧
        (∀ nb, vfsAcquireLockPure s₀ path mode createIfMissing nb =
          (.ok { handleId := freshLockId s₀, path := path, mode := mode },
            { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }))) ∨
      (∃ parSegs lastSeg parCanon parMode,
        createIfMissing = true ∧
        Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg) ∧
        vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode) ∧
        ((parMode / 128) % 2 == 0) = false ∧
        ((parMode / 64) % 2 == 0) = false ∧
        s₀.nodes (vfsChildPath parCanon lastSeg) = none ∧
        hasLockConflict s₀.locks (vfsChildPath parCanon lastSeg) .exclusive = false ∧
        (∀ nb, vfsAcquireLockPure s₀ path mode true nb =
          (.ok { handleId := freshLockId s₀, path := path, mode := mode },
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
              nextLockId := freshLockId s₀ })))) := by
  rw [vfsTryWithFileLock_pure_step] at hProbe
  cases hA : vfsAcquireLockPure s₀ path .exclusive createIfMissing true with
  | mk res st' =>
    rw [hA] at hProbe
    cases res with
    | error e =>
      by_cases hw : (e.kind == .wouldBlock) = true <;> simp [hw] at hProbe
    | ok hEx =>
      have ⟨rfl, hCases⟩ := vfsAcquireLock_ok_step s₀ path .exclusive createIfMissing true hEx st' hA
      have hValid : isValidLockPath path = true := by
        rw [vfsAcquireLockPure_unfold] at hA
        cases hv : isValidLockPath path <;> simp_all
      refine ⟨hValid, ?_⟩
      rcases hCases with ⟨_, _, hFalse⟩ | ⟨canon, bs, m, hRes, hConfEx, _⟩ |
          ⟨parSegs, lastSeg, parCanon, parMode, e, hCre, hRes, hNf, hSplit, hPar, hW, hX, hNone, hConfEx, _⟩
      · exact hFalse.elim
      · refine Or.inl ⟨canon, bs, m, hRes, hConfEx, fun nb => ?_⟩
        have hConfMode := hasLockConflict_exclusive_false s₀.locks canon mode hConfEx
        simp [vfsAcquireLockPure_unfold, hValid, hRes, hConfMode]
      · refine Or.inr ⟨parSegs, lastSeg, parCanon, parMode, hCre, hSplit, hPar, hW, hX, hNone, hConfEx, fun nb => ?_⟩
        have hConfMode := hasLockConflict_exclusive_false s₀.locks (vfsChildPath parCanon lastSeg) mode hConfEx
        have hPermF : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false := by simp [hW, hX]
        have hNfBool : (e.kind != .notFound) = false := by rw [hNf]; decide
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [hRes]
        dsimp only
        simp [hNfBool, hSplit, hPar, hPermF, hConfMode]

private theorem vfsResolveSegs_after_create (s₀ : VfsState) (path parCanon lastSeg : String)
    (parSegs : List String) (parMode : Nat)
    (hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg))
    (hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode))
    (hX : ((parMode / 64) % 2 == 0) = false)
    (hNone : s₀.nodes (vfsChildPath parCanon lastSeg) = none) :
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
      .ok (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644) := by
  intro s₁
  have hAllSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd path) = parSegs ++ [lastSeg] := by
    simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] parSegs lastSeg hSplit
  have hAllValid : ∀ s ∈ vfsSplitSegs (vfsAbsNorm s₀.cwd path), Internal.validFileName s = true := by
    unfold vfsAbsNorm
    rw [model_normPath_eq_internal]
    exact vfsSplitSegs_normPath_valid _
  have hParValid : ∀ s ∈ parSegs, Internal.validFileName s = true := fun s hs =>
    hAllValid s (by rw [hAllSegs]; simp [hs])
  have hLastValid : Internal.validFileName lastSeg = true :=
    hAllValid lastSeg (by rw [hAllSegs]; simp)
  have hParCanon : isCanonPath parCanon = true :=
    vfsResolveSegs_isCanon s₀.nodes 512 "/" parSegs true (parCanon, .dir parMode) (by decide) hParValid hPar
  have hParLookup : s₀.nodes parCanon = some (.dir parMode) :=
    vfsResolveSegs_ok_node s₀.nodes 512 "/" parSegs true parCanon (.dir parMode) hPar
  have hNodesEq :
      s₁.nodes = fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))) = _
    exact vfsTreeNodes_insert_file s₀.tree parCanon lastSeg ByteArray.empty 0o644 hParCanon hLastValid ⟨parMode, hParLookup⟩ hNone
  have hParNew := vfsResolveSegs_insert_fresh s₀.nodes (vfsChildPath parCanon lastSeg)
    (.file ByteArray.empty 0o644) hNone 512 "/" parSegs true (parCanon, .dir parMode) hPar
  have hChildNew :
      (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
        (vfsChildPath parCanon lastSeg) = some (.file ByteArray.empty 0o644) := by simp
  have hStep := vfsResolveSegs_dir_child_nofollow
    (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
    lastSeg parCanon parMode hX (.file ByteArray.empty 0o644) hChildNew 512 "/" parSegs hParNew
  have h1024 := vfsResolveSegs_fuel_mono
    (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
    513 1024 "/" (parSegs ++ [lastSeg]) false (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644)
    (by omega) hStep
  rw [← hAllSegs] at h1024
  change vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 = _
  rw [hNodesEq, h1024]

private theorem vfsProbe_after_release_created (s₀ : VfsState) (path parCanon lastSeg : String)
    (parSegs : List String) (parMode : Nat)
    (hValid : isValidLockPath path = true)
    (hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg))
    (hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode))
    (hX : ((parMode / 64) % 2 == 0) = false)
    (hNone : s₀.nodes (vfsChildPath parCanon lastSeg) = none)
    (hConfEx : hasLockConflict s₀.locks (vfsChildPath parCanon lastSeg) .exclusive = false) :
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
      .ok (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644) ∧
    ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
  intro s₁
  have hResS1 := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
  refine ⟨hResS1, ?_⟩
  rw [vfsTryWithFileLock_pure_step]
  have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
      (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
        { s₁ with locks := (freshLockId s₁, vfsChildPath parCanon lastSeg, .exclusive) :: s₁.locks,
                  nextLockId := freshLockId s₁ }) := by
    simp [vfsAcquireLockPure_unfold, hValid, hResS1, s₁, hConfEx]
  rw [hAcqS1]
  have hRelS1 := vfsReleaseLockPure_fresh s₁
    { s₁ with locks := (freshLockId s₁, vfsChildPath parCanon lastSeg, .exclusive) :: s₁.locks,
              nextLockId := freshLockId s₁ }
    (vfsChildPath parCanon lastSeg) path .exclusive (Or.inl rfl)
  simp [hRelS1]

/-- Proof of `test_fs_vfs_withFileLock_releasesOnOk` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_releasesOnOk :
    AllPass (test_fs_vfs_withFileLock_releasesOnOk (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode createIfMissing val hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  dsimp only [assert]
  rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
      ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
  · let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
    let s₁ : VfsState := { st1 with locks := s₀.locks }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 canon path mode (Or.inl rfl)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode createIfMissing (pure (.ok val))).run s₀ = (.ok val, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hResS1 : vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
        .ok (canon, .file bs m) := hRes
    have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
        (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
          { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [hValid]
      dsimp only
      rw [hResS1]
      dsimp only
      simp [s₁, st1, hConfEx]
    have hRelS1 := vfsReleaseLockPure_fresh s₁
      { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
      canon path .exclusive (Or.inl rfl)
    have hP : ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
      rw [vfsTryWithFileLock_pure_step, hAcqS1]
      simp [hRelS1]
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩
  · let st1 : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
        nextLockId := freshLockId s₀ }
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode true (pure (.ok val))).run s₀ = (.ok val, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hP := (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_releasesOnOk` using a `0o444` read-only file with `createIfMissing = true`. -/
theorem reach_fs_vfs_withFileLock_releasesOnOk :
    CanReach (test_fs_vfs_withFileLock_releasesOnOk (Internal.mkApiM vfsOps)) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "ro.lock" then some (.file (ByteArray.mk #[42]) 0o444) else none)
      keys := ["/ro.lock"]
      cwd := "/"
      nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/ro.lock")) false 1024 =
      .ok ("/ro.lock", .file (ByteArray.mk #[42]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/ro.lock" = "/ro.lock" from by decide,
        show vfsSplitSegs "/ro.lock" = ["ro.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "ro.lock" = "/ro.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/ro.lock" = some (.file (ByteArray.mk #[42]) 0o444) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/ro.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/ro.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/ro.lock", mode := .exclusive },
          { st with locks := (freshLockId st, "/ro.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/ro.lock" = true from by decide]
      dsimp only
      rw [hRes]
      simp [st, hasLockConflict]
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with locks := (freshLockId st, "/ro.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
      "/ro.lock" "/ro.lock" .exclusive (Or.inl rfl)
    simp [hRel]
  exact ⟨st, "/ro.lock", .shared, true, 7, hProbe,
    proof_fs_vfs_withFileLock_releasesOnOk st "/ro.lock" .shared true 7 hProbe⟩

/-- Proof of `test_fs_vfs_withFileLock_releasesOnError` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_releasesOnError :
    AllPass (test_fs_vfs_withFileLock_releasesOnError (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode createIfMissing err hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  dsimp only [assert]
  rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
      ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
  · let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
    let s₁ : VfsState := { st1 with locks := s₀.locks }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 canon path mode (Or.inl rfl)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode createIfMissing (pure (.error err : Except FsError Unit))).run s₀ =
        (.error err, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hResS1 : vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
        .ok (canon, .file bs m) := hRes
    have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
        (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
          { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [hValid]
      dsimp only
      rw [hResS1]
      dsimp only
      simp [s₁, st1, hConfEx]
    have hRelS1 := vfsReleaseLockPure_fresh s₁
      { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
      canon path .exclusive (Or.inl rfl)
    have hP : ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
      rw [vfsTryWithFileLock_pure_step, hAcqS1]
      simp [hRelS1]
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩
  · let st1 : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
        nextLockId := freshLockId s₀ }
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode true (pure (.error err : Except FsError Unit))).run s₀ =
        (.error err, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hP := (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_releasesOnError`. -/
theorem reach_fs_vfs_withFileLock_releasesOnError :
    CanReach (test_fs_vfs_withFileLock_releasesOnError (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .permissionDenied, message := "boom" }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/err.lock")) false 1024 =
      .error { kind := .notFound, path := some "/err.lock", message := "no such file or directory: /err.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/err.lock" = "/err.lock" from by decide,
        show vfsSplitSegs "/err.lock" = ["err.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "err.lock" = "/err.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/err.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/err.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/err.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/err.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "err.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "err.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "err.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/err.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/err.lock" = "/err.lock" from by decide,
          show vfsSplitSegs "/err.lock" = ["err.lock"] from by decide,
          show Internal.splitLastAux ["err.lock"] [] = some ([], "err.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "err.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "err.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "err.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "err.lock") "/err.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/err.lock", .exclusive, true, err, hProbe,
    proof_fs_vfs_withFileLock_releasesOnError st "/err.lock" .exclusive true err hProbe⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_sharedCoexists` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_tryWithFileLock_sharedCoexists :
    AllPass (test_fs_vfs_tryWithFileLock_sharedCoexists (Internal.mkApiM vfsOps)) := by
  intro s₀ path val hIsOk
  change ((vfsApi.withFileLock path .shared true
      (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀).1.isOk = true at hIsOk
  change (((vfsApi.withFileLock path .shared true
      (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀).1 = .ok (some val)) ∧ True
  rw [vfsWithFileLock_action_step] at hIsOk ⊢
  cases hOuter : vfsAcquireLockPure s₀ path .shared true false with
  | mk rO stO =>
    cases rO with
    | error e => rw [hOuter] at hIsOk; cases hIsOk
    | ok hO =>
      dsimp only at hIsOk ⊢
      rcases vfsAcquireLock_ok_step s₀ path .shared true false hO stO hOuter with ⟨rfl, hCases⟩
      have hValid : isValidLockPath path = true := by
        rw [vfsAcquireLockPure_unfold] at hOuter
        cases hv : isValidLockPath path <;> simp_all
      have hSharedNe : (LockMode.shared == LockMode.exclusive) = false := rfl
      have hInner : (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val))).run stO =
          (.ok (some val), { stO with nextLockId := freshLockId stO }) := by
        rw [vfsTryWithFileLock_pure_step]
        rcases hCases with ⟨_, _, hF⟩ | ⟨canon, bs, m, hRes, hConf, rfl⟩ |
            ⟨parSegs, lastSeg, parCanon, parMode, _, _, hRes, _, hSplit, hPar, _, hX, hNone, hConf, rfl⟩
        · exact hF.elim
        · have hConfIn : hasLockConflict ((freshLockId s₀, canon, .shared) :: s₀.locks) canon .shared = false := by
            simp only [hasLockConflict, hSharedNe]
            simpa [hasLockConflict, hSharedNe] using hConf
          let stO' : VfsState := { s₀ with locks := (freshLockId s₀, canon, .shared) :: s₀.locks, nextLockId := freshLockId s₀ }
          have hAcqIn : vfsAcquireLockPure stO' path .shared false true =
              (.ok { handleId := freshLockId stO', path := path, mode := .shared },
                { stO' with locks := (freshLockId stO', canon, .shared) :: stO'.locks, nextLockId := freshLockId stO' }) := by
            rw [vfsAcquireLockPure_unfold]
            rw [hValid]
            dsimp only
            rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
            dsimp only
            simp [stO', hConfIn]
          rw [hAcqIn]
          have hRelIn := vfsReleaseLockPure_fresh stO'
            { stO' with locks := (freshLockId stO', canon, .shared) :: stO'.locks, nextLockId := freshLockId stO' }
            canon path .shared (Or.inl rfl)
          dsimp only [stO'] at hRelIn ⊢
          simp [hRelIn]
        · let newTree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          let stO' : VfsState :=
            { s₀ with
              tree := newTree
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
              nextLockId := freshLockId s₀ }
          have hResStO' := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
          have hConfIn : hasLockConflict stO'.locks (vfsChildPath parCanon lastSeg) .shared = false := by
            simp only [stO', hasLockConflict, hSharedNe]
            simpa [hasLockConflict, hSharedNe] using hConf
          have hAcqIn : vfsAcquireLockPure stO' path .shared false true =
              (.ok { handleId := freshLockId stO', path := path, mode := .shared },
                { stO' with
                  locks := (freshLockId stO', vfsChildPath parCanon lastSeg, .shared) :: stO'.locks
                  nextLockId := freshLockId stO' }) := by
            rw [vfsAcquireLockPure_unfold]
            rw [hValid]
            dsimp only
            rw [show stO'.nodes = ({ s₀ with tree := newTree, keys := vfsChildPath parCanon lastSeg :: s₀.keys, nextLockId := freshLockId s₀ } : VfsState).nodes from rfl,
                show stO'.cwd = ({ s₀ with tree := newTree, keys := vfsChildPath parCanon lastSeg :: s₀.keys, nextLockId := freshLockId s₀ } : VfsState).cwd from rfl,
                hResStO']
            dsimp only
            simp [stO', hConfIn]
          rw [hAcqIn]
          have hRelIn := vfsReleaseLockPure_fresh stO'
            { stO' with
              locks := (freshLockId stO', vfsChildPath parCanon lastSeg, .shared) :: stO'.locks
              nextLockId := freshLockId stO' }
            (vfsChildPath parCanon lastSeg) path .shared (Or.inl rfl)
          dsimp only [stO', newTree] at hRelIn ⊢
          simp [hRelIn]
      rw [hInner]
      dsimp only [assert]
      rcases hCases with ⟨_, _, hF⟩ | ⟨canon, _, _, _, _, rfl⟩ |
          ⟨_, lastSeg, parCanon, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      · exact hF.elim
      · have hRelOk : (vfsReleaseLockPure
            { s₀ with
              locks := (freshLockId s₀, canon, .shared) :: s₀.locks
              nextLockId := freshLockId { s₀ with locks := (freshLockId s₀, canon, .shared) :: s₀.locks, nextLockId := freshLockId s₀ } }
            { handleId := freshLockId s₀, path := path, mode := .shared }).1 = .ok () := by
          simp [vfsReleaseLockPure, freshLockId]
        rw [hRelOk]
        exact ⟨rfl, trivial⟩
      · have hRelOk : (vfsReleaseLockPure
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
              nextLockId := freshLockId { s₀ with
                tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
                keys := vfsChildPath parCanon lastSeg :: s₀.keys
                locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
                nextLockId := freshLockId s₀ } }
            { handleId := freshLockId s₀, path := path, mode := .shared }).1 = .ok () := by
          simp [vfsReleaseLockPure, freshLockId]
        rw [hRelOk]
        exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_sharedCoexists`. -/
theorem reach_fs_vfs_tryWithFileLock_sharedCoexists :
    CanReach (test_fs_vfs_tryWithFileLock_sharedCoexists (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/sh.lock")) false 1024 =
      .error { kind := .notFound, path := some "/sh.lock", message := "no such file or directory: /sh.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
        show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "sh.lock" = "/sh.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/sh.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hOuter : ((vfsApi.withFileLock "/sh.lock" .shared true (vfsApi.tryWithFileLock "/sh.lock" .shared false (pure (Except.ok 42)))).run st).1.isOk = true := by
    rw [vfsWithFileLock_action_step]
    let stO :=
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "sh.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
        nextLockId := freshLockId st }
    have hAcqO : vfsAcquireLockPure st "/sh.lock" .shared true false =
        (.ok { handleId := freshLockId st, path := "/sh.lock", mode := .shared }, stO) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/sh.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
          show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide,
          show Internal.splitLastAux ["sh.lock"] [] = some ([], "sh.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict, stO]
      decide
    have hParNew := vfsResolveSegs_insert_fresh st.nodes (vfsChildPath "/" "sh.lock")
      (.file ByteArray.empty 0o644) (show st.nodes "/sh.lock" = none from rfl) 512 "/" [] true ("/", .dir 0o755) hPar
    have hNodesEq : stO.nodes = fun k =>
        if k == vfsChildPath "/" "sh.lock" then some (.file ByteArray.empty 0o644) else st.nodes k := by
      change vfsTreeNodes (vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))) = _
      exact vfsTreeNodes_insert_file st.tree "/" "sh.lock" ByteArray.empty 0o644 (by decide) (by decide)
        ⟨0o755, show st.nodes "/" = some (.dir 0o755) from rfl⟩ (show st.nodes "/sh.lock" = none from rfl)
    have hStep := vfsResolveSegs_dir_child_nofollow stO.nodes "sh.lock" "/" 0o755 (by decide)
      (.file ByteArray.empty 0o644) (by rw [hNodesEq]; simp) 512 "/" [] (by rw [hNodesEq]; exact hParNew)
    have hResO : vfsResolveSegs stO.nodes "/" (vfsSplitSegs (vfsAbsNorm stO.cwd "/sh.lock")) false 1024 =
        .ok ("/sh.lock", .file ByteArray.empty 0o644) := by
      change vfsResolveSegs stO.nodes "/" (vfsSplitSegs (vfsAbsNorm "/" "/sh.lock")) false 1024 = _
      rw [show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
          show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide]
      exact vfsResolveSegs_fuel_mono stO.nodes 513 1024 "/" ["sh.lock"] false _ (by omega) hStep
    have hConfO : hasLockConflict stO.locks "/sh.lock" .shared = false := by
      dsimp [stO, st, hasLockConflict]
      decide
    have hIn : (vfsApi.tryWithFileLock "/sh.lock" .shared false (pure (Except.ok 42))).run stO =
        (.ok (some 42), { stO with nextLockId := freshLockId stO }) := by
      rw [vfsTryWithFileLock_pure_step]
      have hAcqI : vfsAcquireLockPure stO "/sh.lock" .shared false true =
          (.ok { handleId := freshLockId stO, path := "/sh.lock", mode := .shared },
            { stO with locks := (freshLockId stO, "/sh.lock", .shared) :: stO.locks, nextLockId := freshLockId stO }) := by
        rw [vfsAcquireLockPure_unfold]
        rw [show isValidLockPath "/sh.lock" = true from by decide]
        dsimp only
        rw [hResO]
        dsimp only
        simp [stO, hConfO]
      rw [hAcqI]
      have hRelI := vfsReleaseLockPure_fresh stO
        { stO with locks := (freshLockId stO, "/sh.lock", .shared) :: stO.locks, nextLockId := freshLockId stO }
        "/sh.lock" "/sh.lock" .shared (Or.inl rfl)
      simp [hRelI]
    have hRelO' : (vfsReleaseLockPure { stO with nextLockId := freshLockId stO }
        { handleId := freshLockId st, path := "/sh.lock", mode := .shared }).1 = .ok () := by
      dsimp [vfsReleaseLockPure, stO, st, freshLockId]
    dsimp only [stO] at hAcqO hIn hRelO'
    rw [hAcqO]
    dsimp only
    rw [hIn]
    dsimp only
    cases hRel : vfsReleaseLockPure
        { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath "/" "sh.lock" :: st.keys
          locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
          nextLockId := freshLockId { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "sh.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
            nextLockId := freshLockId st } }
        { handleId := freshLockId st, path := "/sh.lock", mode := .shared } with
    | mk relRes sFinal =>
      have hRelEq : relRes = .ok () := by
        simpa [hRel] using hRelO'
      rw [hRelEq]
      rfl
  exact ⟨st, "/sh.lock", 42, hOuter,
    proof_fs_vfs_tryWithFileLock_sharedCoexists st "/sh.lock" 42 hOuter⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_exclusiveRejects` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_tryWithFileLock_exclusiveRejects :
    AllPass (test_fs_vfs_tryWithFileLock_exclusiveRejects (Internal.mkApiM vfsOps)) := by
  change AllPass (test_fs_vfs_tryWithFileLock_exclusiveRejects vfsApi)
  intro s₀ path markerPath outerMode innerMode hModes _ hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run] at hMarkerNone
  rw [vfsWithFileLock_action_step]
  cases hOuter : vfsAcquireLockPure s₀ path outerMode false false with
  | mk rO stO =>
    cases rO with
    | error e =>
      dsimp only
      intro hFalse
      exact hFalse.elim
    | ok hO =>
      dsimp only
      rcases vfsAcquireLock_ok_step s₀ path outerMode false false hO stO hOuter with ⟨rfl, hCases⟩
      have hValid : isValidLockPath path = true := by
        rw [vfsAcquireLockPure_unfold] at hOuter
        cases hv : isValidLockPath path <;> simp_all
      rcases hCases with ⟨_, _, hF⟩ | ⟨canon, bs, m, hRes, _, rfl⟩ | ⟨_, _, _, _, _, hCre, _⟩
      · exact hF.elim
      · have hConf1 := hasLockConflict_cons_self_mode (freshLockId s₀) canon outerMode innerMode s₀.locks hModes
        have hConf2 := hasLockConflict_cons_self_mode (freshLockId s₀) canon outerMode .exclusive s₀.locks (Or.inr rfl)
        let stO' : VfsState := { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }
        have hAcq1 : vfsAcquireLockPure stO' path innerMode false true =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, stO') := by
          rw [vfsAcquireLockPure_unfold]
          rw [hValid]
          dsimp only
          rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
          dsimp only
          simp [stO', hConf1]
        have hR1 :
            (vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")).run stO' =
              (.ok none, stO') := by
          dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, Internal.tryWithFileLockImplM, vfsOps, StateT.run, bind, StateT.bind, pure]
          rw [hAcq1]
          rfl
        have hAcq2 : vfsAcquireLockPure stO' path .exclusive false true =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, stO') := by
          rw [vfsAcquireLockPure_unfold]
          rw [hValid]
          dsimp only
          rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
          dsimp only
          simp [stO', hConf2]
        have hR2 :
            (vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run stO' =
              (.ok none, stO') := by
          rw [vfsTryWithFileLock_pure_step, hAcq2]
          rfl
        have hMarkerFalse : ((vfsApi.lstat markerPath).run s₀).1.isOk = false := hMarkerNone
        have hRelO := vfsReleaseLockPure_fresh s₀ stO' canon path outerMode (Or.inl rfl)
        dsimp only [stO'] at hRelO hR1 hR2
        have hAct :
            (do
              let r1 ← vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")
              let mAfter ← vfsApi.lstat markerPath
              let r2 ← vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))
              pure (Except.ok (r1, mAfter.isOk, r2)) :
                StateM VfsState (Except FsError (Except FsError (Option Unit) × Bool × Except FsError (Option Unit)))).run
              { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ } =
              (.ok (.ok none, false, .ok none),
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }) := by
          dsimp only [StateT.run, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
          change match (vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")).run _ with
            | (r1, s1) =>
              match (vfsApi.lstat markerPath).run s1 with
              | (mAfter, s2) =>
                match (vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run s2 with
                | (r2, s3) => (Except.ok (r1, mAfter.isOk, r2), s3) = _
          rw [hR1]
          dsimp only
          have hLstatM :
              (vfsApi.lstat markerPath).run
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ } =
              (((vfsApi.lstat markerPath).run s₀).1,
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }) := rfl
          rw [hLstatM]
          dsimp only
          rw [hR2]
          dsimp only
          rw [hMarkerFalse]
        rw [hAct]
        dsimp only
        rw [hRelO]
        dsimp only [assert]
        exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩
      · cases hCre

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_exclusiveRejects`. -/
theorem reach_fs_vfs_tryWithFileLock_exclusiveRejects :
    CanReach (test_fs_vfs_tryWithFileLock_exclusiveRejects (Internal.mkApiM vfsOps)) := by
  change CanReach (test_fs_vfs_tryWithFileLock_exclusiveRejects vfsApi)
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "a.lock" then some (.file ByteArray.empty 0o644) else none)
      keys := ["/a.lock"]
      cwd := "/"
      nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/a.lock")) false 1024 =
      .ok ("/a.lock", .file ByteArray.empty 0o644) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/a.lock" = "/a.lock" from by decide,
        show vfsSplitSegs "/a.lock" = ["a.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "a.lock" = "/a.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/a.lock" = some (.file ByteArray.empty 0o644) from rfl]
  have hLstatA : ((vfsApi.lstat "/a.lock").run st).1.isOk = true := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [hRes]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  let stO' : VfsState := { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
  have hAcqO : vfsAcquireLockPure st "/a.lock" .exclusive false false =
      (.ok { handleId := freshLockId st, path := "/a.lock", mode := .exclusive }, stO') := by
    rw [vfsAcquireLockPure_unfold]; rw [show isValidLockPath "/a.lock" = true from by decide]; dsimp only; rw [hRes]; dsimp only
    simp [st, hasLockConflict, stO']
  have hConf1 : hasLockConflict stO'.locks "/a.lock" .exclusive = true := by
    dsimp [stO', hasLockConflict]
    decide
  have hAcq1 : vfsAcquireLockPure stO' "/a.lock" .exclusive false true =
      (.error { kind := .wouldBlock, path := some "/a.lock", message := "resource temporarily unavailable" }, stO') := by
    rw [vfsAcquireLockPure_unfold]; rw [show isValidLockPath "/a.lock" = true from by decide]; dsimp only
    rw [show stO'.nodes = st.nodes from rfl, show stO'.cwd = st.cwd from rfl, hRes]; dsimp only; simp [stO', hConf1]
  have hR1 : (vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")).run stO' =
      (.ok none, stO') := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, Internal.tryWithFileLockImplM, vfsOps, StateT.run, bind, StateT.bind, pure]
    rw [hAcq1]; rfl
  have hR2 : (vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))).run stO' =
      (.ok none, stO') := by
    rw [vfsTryWithFileLock_pure_step, hAcq1]; rfl
  have hRelO := vfsReleaseLockPure_fresh st stO' "/a.lock" "/a.lock" .exclusive (Or.inl rfl)
  dsimp only [stO'] at hAcqO hR1 hR2 hRelO
  refine ⟨st, "/a.lock", "/marker", .exclusive, .exclusive, Or.inl rfl, hLstatA, hMarker, ?_⟩
  dsimp only [test_fs_vfs_tryWithFileLock_exclusiveRejects]
  rw [vfsWithFileLock_action_step, hAcqO]
  dsimp only
  have hAct :
      (do
        let r1 ← vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")
        let mAfter ← vfsApi.lstat "/marker"
        let r2 ← vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))
        pure (Except.ok (r1, mAfter.isOk, r2)) :
          StateM VfsState (Except FsError (Except FsError (Option Unit) × Bool × Except FsError (Option Unit)))).run
        { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st } =
        (.ok (.ok none, false, .ok none),
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := by
    dsimp only [StateT.run, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
    change match (vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")).run _ with
      | (r1, s1) =>
        match (vfsApi.lstat "/marker").run s1 with
        | (mAfter, s2) =>
          match (vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))).run s2 with
          | (r2, s3) => (Except.ok (r1, mAfter.isOk, r2), s3) = _
    rw [hR1]
    dsimp only
    have hLstatM :
        (vfsApi.lstat "/marker").run
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st } =
        (((vfsApi.lstat "/marker").run st).1,
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := rfl
    rw [hLstatM]
    dsimp only
    rw [hR2]
    dsimp only
    rw [hMarker]
  rw [hAct]
  dsimp only
  rw [hRelO]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩

private theorem isValidLockPath_of_not_empty_no_trailing_slash (path : String)
    (hNeEmpty : path.toList ≠ [])
    (hNoSlash : path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/') :
    isValidLockPath path = true := by
  unfold isValidLockPath
  cases hc : path.toList with
  | nil => exact absurd hc hNeEmpty
  | cons c rest =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and]
    rcases hNoSlash with hLen | hLast
    · have hLen1 : (c :: rest).length = 1 := by simpa [hc] using hLen
      simp [hLen1]
    · have hLast' : (c :: rest).getLast? ≠ some '/' := by simpa [hc] using hLast
      have hBeq : ((c :: rest).getLast? == some '/') = false := by
        cases hgl : (c :: rest).getLast? with
        | none => rfl
        | some ch =>
          simp only [hgl] at hLast'
          exact beq_false_of_ne (fun h => hLast' (by cases h; rfl))
      simp [hBeq]

/-- Proof of `test_fs_vfs_withFileLock_missingNotCreated` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_missingNotCreated :
    AllPass (test_fs_vfs_withFileLock_missingNotCreated (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode hNeEmpty hNoSlash hLstat
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run] at hLstat
  rcases hLstat with ⟨e, hStat, hNf⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    have hAcq : vfsAcquireLockPure s₀ path mode false false = (.error e', s₀) := by
      rw [vfsAcquireLockPure_unfold]
      rw [hValid]
      dsimp only
      rw [hRes]
      dsimp only
      simp [hNf]
    have hW : (vfsApi.withFileLock path mode false (pure (.ok ()))).run s₀ = (.error e', s₀) := by
      rw [vfsWithFileLock_pure_step, hAcq]
    dsimp only [assert]
    exact ⟨⟨⟨e', congrArg Prod.fst hW, hNf⟩, congrArg Prod.snd hW⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_missingNotCreated`. -/
theorem reach_fs_vfs_withFileLock_missingNotCreated :
    CanReach (test_fs_vfs_withFileLock_missingNotCreated (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hStat : ((vfsApi.lstat "/missing.lock").run st).1 =
      .error { kind := .notFound, path := some "/missing.lock", message := "no such file or directory: /missing.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/missing.lock" = "/missing.lock" from by decide,
        show vfsSplitSegs "/missing.lock" = ["missing.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "missing.lock" = "/missing.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/missing.lock" = none from rfl]; rfl
  exact ⟨st, "/missing.lock", .exclusive, by decide, Or.inr (by decide),
    ⟨_, hStat, rfl⟩,
    proof_fs_vfs_withFileLock_missingNotCreated st "/missing.lock" .exclusive (by decide) (Or.inr (by decide)) ⟨_, hStat, rfl⟩⟩

/-- Proof of `test_fs_vfs_withFileLock_symlinkRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_symlinkRejected :
    AllPass (test_fs_vfs_withFileLock_symlinkRejected (Internal.mkApiM vfsOps)) := by
  intro s₀ path markerPath mode createIfMissing hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨st, hStat, hSym⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes] at hStat
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    simp only [hRes, Except.ok.injEq] at hStat
    subst hStat
    cases nd with
    | file _ _ => simp [vfsToStat] at hSym
    | dir _ => simp [vfsToStat] at hSym
    | symlink tgt m =>
      dsimp only [Internal.withFileLockImplM, Internal.bracketLockM,
        StateT.tryFinally, Id.finally,
        tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, s₀) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [hRes]
        rfl
      rw [hAcq]
      exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_symlinkRejected`. -/
theorem reach_fs_vfs_withFileLock_symlinkRejected :
    CanReach (test_fs_vfs_withFileLock_symlinkRejected (Internal.mkApiM vfsOps)) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "sym.lock" then some (.symlink "/target" 0o777) else none)
      keys := ["/sym.lock"]
      cwd := "/"
      nonce := 0 }
  have hSym : ((vfsApi.lstat "/sym.lock").run st).1 = .ok (vfsToStat (.symlink "/target" 0o777)) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sym.lock" = "/sym.lock" from by decide,
        show vfsSplitSegs "/sym.lock" = ["sym.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "sym.lock" = "/sym.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/sym.lock" = some (.symlink "/target" 0o777) from rfl]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/sym.lock", "/marker", .exclusive, true, by decide, Or.inr (by decide),
    ⟨vfsToStat (.symlink "/target" 0o777), hSym, rfl⟩, hMarker,
    proof_fs_vfs_withFileLock_symlinkRejected st "/sym.lock" "/marker" .exclusive true (by decide) (Or.inr (by decide))
      ⟨vfsToStat (.symlink "/target" 0o777), hSym, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_withFileLock_dirRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_dirRejected :
    AllPass (test_fs_vfs_withFileLock_dirRejected (Internal.mkApiM vfsOps)) := by
  intro s₀ path markerPath mode createIfMissing hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨st, hStat, hDir⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes] at hStat
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    simp only [hRes, Except.ok.injEq] at hStat
    subst hStat
    cases nd with
    | file _ _ => simp [vfsToStat] at hDir
    | symlink _ _ => simp [vfsToStat] at hDir
    | dir m =>
      dsimp only [Internal.withFileLockImplM, Internal.bracketLockM,
        StateT.tryFinally, Id.finally,
        tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, s₀) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [hRes]
        rfl
      rw [hAcq]
      exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_dirRejected`. -/
theorem reach_fs_vfs_withFileLock_dirRejected :
    CanReach (test_fs_vfs_withFileLock_dirRejected (Internal.mkApiM vfsOps)) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "dir" then some (.dir 0o755 fun _ => none) else none)
      keys := ["/dir"]
      cwd := "/"
      nonce := 0 }
  have hDir : ((vfsApi.lstat "/dir").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/dir" = "/dir" from by decide,
        show vfsSplitSegs "/dir" = ["dir"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "dir" = "/dir" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/dir" = some (.dir 0o755) from rfl]
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/dir", "/marker", .exclusive, true, by decide, Or.inr (by decide),
    ⟨vfsToStat (.dir 0o755), hDir, rfl⟩, hMarker,
    proof_fs_vfs_withFileLock_dirRejected st "/dir" "/marker" .exclusive true (by decide) (Or.inr (by decide))
      ⟨vfsToStat (.dir 0o755), hDir, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_withFileLock_createsMissingFile` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_createsMissingFile :
    AllPass (test_fs_vfs_withFileLock_createsMissingFile (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode hNeEmpty hNoSlash hLstat hResOk
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run] at hLstat
  rcases hLstat with ⟨e, hStat, hNf⟩
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    change ((vfsApi.withFileLock path mode true (pure (.ok ()))).run s₀).1 = .ok () at hResOk
    change (∃ st, ((vfsApi.lstat path).run ((vfsApi.withFileLock path mode true (pure (.ok ()))).run s₀).2).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = 0) ∧ True
    rw [vfsWithFileLock_pure_step] at hResOk ⊢
    cases hA : vfsAcquireLockPure s₀ path mode true false with
    | mk r st1 =>
      rw [hA] at hResOk
      cases r with
      | error err => simp at hResOk
      | ok h =>
        have hValid : isValidLockPath path = true := by
          rw [vfsAcquireLockPure_unfold] at hA
          cases hv : isValidLockPath path <;> simp_all
        rcases vfsAcquireLock_ok_step s₀ path mode true false h st1 hA with ⟨rfl, hCases⟩
        rcases hCases with ⟨_, _, hF⟩ | ⟨_, _, _, hResOk', _⟩ |
            ⟨parSegs, lastSeg, parCanon, parMode, _, _, hResErr, _, hSplit, hPar, _, hX, hNone, hConf, rfl⟩
        · exact hF.elim
        · rw [hRes] at hResOk'; cases hResOk'
        · have hRel := vfsReleaseLockPure_fresh s₀
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
              nextLockId := freshLockId s₀ }
            (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
          have hCreated := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
          dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run, assert]
          rw [hRel]
          dsimp only
          unfold vfsStatPure
          rw [hCreated]
          refine ⟨⟨vfsToStat (.file ByteArray.empty 0o644), rfl, rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_createsMissingFile` using a missing path. -/
theorem reach_fs_vfs_withFileLock_createsMissingFile :
    CanReach (test_fs_vfs_withFileLock_createsMissingFile (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/new.lock")) false 1024 =
      .error { kind := .notFound, path := some "/new.lock", message := "no such file or directory: /new.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new.lock" = "/new.lock" from by decide,
        show vfsSplitSegs "/new.lock" = ["new.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new.lock" = "/new.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStat : ((vfsApi.lstat "/new.lock").run st).1 =
      .error { kind := .notFound, path := some "/new.lock", message := "no such file or directory: /new.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [hRes]
  have hOk : ((vfsApi.withFileLock "/new.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok () := by
    rw [vfsWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/new.lock" .exclusive true false =
        (.ok { handleId := freshLockId st, path := "/new.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "new.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "new.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "new.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/new.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new.lock" = "/new.lock" from by decide,
          show vfsSplitSegs "/new.lock" = ["new.lock"] from by decide,
          show Internal.splitLastAux ["new.lock"] [] = some ([], "new.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "new.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "new.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "new.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "new.lock") "/new.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/new.lock", .exclusive, by decide, Or.inr (by decide), ⟨_, hStat, rfl⟩, hOk,
    proof_fs_vfs_withFileLock_createsMissingFile st "/new.lock" .exclusive (by decide) (Or.inr (by decide)) ⟨_, hStat, rfl⟩ hOk⟩

/-- Proof of `test_fs_vfs_withFileLock_preservesExistingBytes` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_preservesExistingBytes :
    AllPass (test_fs_vfs_withFileLock_preservesExistingBytes (Internal.mkApiM vfsOps)) := by
  change AllPass (test_fs_vfs_withFileLock_preservesExistingBytes vfsApi)
  intro s₀ path mode createIfMissing hNeEmpty hNoSlash
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  dsimp only [test_fs_vfs_withFileLock_preservesExistingBytes]
  cases hRb : ((vfsApi.readBytes path).run s₀).1 with
  | error e => intro hF; exact hF.elim
  | ok bs₀ =>
    have ⟨hRaw, hRead⟩ : isValidRawPath path = true ∧
        ∃ canon m₀, vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 =
          .ok (canon, .file bs₀ m₀) := by
      dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run, vfsReadBytesPure] at hRb
      by_cases hV : isValidRawPath path = true
      · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRb
        cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 with
        | error _ => simp [hR] at hRb
        | ok pair =>
          rcases pair with ⟨canon, nd⟩
          cases nd with
          | dir _ => simp [hR] at hRb
          | symlink _ _ => simp [hR] at hRb
          | file bs m₀ =>
            simp only [hR, Except.ok.injEq] at hRb
            subst hRb
            exact ⟨hV, canon, m₀, rfl⟩
      · have hVF : isValidRawPath path = false := Bool.eq_false_iff.mpr hV
        simp [hVF] at hRb
    rcases hRead with ⟨canon, m₀, hRead⟩
    dsimp only
    intro hResIsOk
    change ((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).1.isOk = true at hResIsOk
    change (((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).1 = .ok bs₀ ∧
      ((vfsApi.readBytes path).run ((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).2).1 = .ok bs₀) ∧ True
    rw [vfsWithFileLock_action_step] at hResIsOk ⊢
    have ⟨res', hNoFollowOk⟩ :=
      vfsResolveSegs_true_ok_implies_false_ok s₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) (canon, .file bs₀ m₀) hRead
    rcases res' with ⟨canon', nd'⟩
    cases nd' with
    | dir _ =>
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, s₀) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [hNoFollowOk]
        rfl
      rw [hAcq] at hResIsOk
      cases hResIsOk
    | symlink _ _ =>
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, s₀) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [hNoFollowOk]
        rfl
      rw [hAcq] at hResIsOk
      cases hResIsOk
    | file bs' m' =>
      by_cases hConf : hasLockConflict s₀.locks canon' mode = true
      · have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, s₀) := by
          rw [vfsAcquireLockPure_unfold]
          rw [hValid]
          dsimp only
          rw [hNoFollowOk]
          dsimp only
          simp [hConf]
        rw [hAcq] at hResIsOk
        cases hResIsOk
      · have hConfF : hasLockConflict s₀.locks canon' mode = false := Bool.eq_false_iff.mpr hConf
        let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon', mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
            (.ok { handleId := freshLockId s₀, path := path, mode := mode }, st1) := by
          rw [vfsAcquireLockPure_unfold]
          rw [hValid]
          dsimp only
          rw [hNoFollowOk]
          dsimp only
          simp [hConfF, st1]
        rw [hAcq] at hResIsOk ⊢
        dsimp only [assert]
        have hReadSt1 : (vfsApi.readBytes path).run st1 = (.ok bs₀, st1) := by
          dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run]
          unfold vfsReadBytesPure
          simp only [hRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [show st1.nodes = s₀.nodes from rfl, show st1.cwd = s₀.cwd from rfl, hRead]
        rw [hReadSt1]
        dsimp only
        have hRel := vfsReleaseLockPure_fresh s₀ st1 canon' path mode (Or.inl rfl)
        dsimp only [st1] at hRel
        rw [hRel]
        dsimp only
        have hReadS2 : ((vfsApi.readBytes path).run { st1 with locks := s₀.locks }).1 = .ok bs₀ := by
          dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run]
          unfold vfsReadBytesPure
          simp only [hRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [show ({ st1 with locks := s₀.locks } : VfsState).nodes = s₀.nodes from rfl,
              show ({ st1 with locks := s₀.locks } : VfsState).cwd = s₀.cwd from rfl, hRead]
        exact ⟨⟨rfl, hReadS2⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_preservesExistingBytes` using a `0o444` read-only existing file. -/
theorem reach_fs_vfs_withFileLock_preservesExistingBytes :
    CanReach (test_fs_vfs_withFileLock_preservesExistingBytes (Internal.mkApiM vfsOps)) := by
  change CanReach (test_fs_vfs_withFileLock_preservesExistingBytes vfsApi)
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "data.lock" then some (.file (ByteArray.mk #[1, 2, 3]) 0o444) else none)
      keys := ["/data.lock"]
      cwd := "/"
      nonce := 0 }
  have hResTrue : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/data.lock")) true 1024 =
      .ok ("/data.lock", .file (ByteArray.mk #[1, 2, 3]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/data.lock" = "/data.lock" from by decide,
        show vfsSplitSegs "/data.lock" = ["data.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "data.lock" = "/data.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/data.lock" = some (.file (ByteArray.mk #[1, 2, 3]) 0o444) from rfl]
  have hResFalse : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/data.lock")) false 1024 =
      .ok ("/data.lock", .file (ByteArray.mk #[1, 2, 3]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/data.lock" = "/data.lock" from by decide,
        show vfsSplitSegs "/data.lock" = ["data.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "data.lock" = "/data.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/data.lock" = some (.file (ByteArray.mk #[1, 2, 3]) 0o444) from rfl]
  have hReadSt : ((vfsApi.readBytes "/data.lock").run st).1 = .ok (ByteArray.mk #[1, 2, 3]) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run]
    unfold vfsReadBytesPure
    simp only [show isValidRawPath "/data.lock" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hResTrue]
  let st1 : VfsState := { st with locks := (freshLockId st, "/data.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
  have hAcq : vfsAcquireLockPure st "/data.lock" .exclusive true false =
      (.ok { handleId := freshLockId st, path := "/data.lock", mode := .exclusive }, st1) := by
    rw [vfsAcquireLockPure_unfold]
    rw [show isValidLockPath "/data.lock" = true from by decide]
    dsimp only
    rw [hResFalse]
    dsimp only
    simp [st, hasLockConflict, st1]
  have hReadSt1 : (vfsApi.readBytes "/data.lock").run st1 = (.ok (ByteArray.mk #[1, 2, 3]), st1) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, StateT.run]
    unfold vfsReadBytesPure
    simp only [show isValidRawPath "/data.lock" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show st1.cwd = "/" from rfl, show st1.nodes = st.nodes from rfl, hResTrue]
  have hRel := vfsReleaseLockPure_fresh st st1 "/data.lock" "/data.lock" .exclusive (Or.inl rfl)
  dsimp only [st1] at hAcq hReadSt1 hRel
  have hResOk : ((vfsApi.withFileLock "/data.lock" .exclusive true (vfsApi.readBytes "/data.lock")).run st).1.isOk = true := by
    rw [vfsWithFileLock_action_step, hAcq]
    dsimp only
    rw [hReadSt1]
    dsimp only
    rw [hRel]
    rfl
  have hAllBase : AllPass (test_fs_vfs_withFileLock_preservesExistingBytes vfsApi) :=
    proof_fs_vfs_withFileLock_preservesExistingBytes
  have hAll := hAllBase st "/data.lock" .exclusive true (by decide) (Or.inr (by decide))
  rw [hReadSt] at hAll
  dsimp only at hAll
  refine ⟨st, "/data.lock", .exclusive, true, by decide, Or.inr (by decide), ?_⟩
  dsimp only [test_fs_vfs_withFileLock_preservesExistingBytes]
  rw [hReadSt]
  exact ⟨hResOk, hAll hResOk⟩

/-- Proof of `test_fs_vfs_withFileLock_invalidPathRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_withFileLock_invalidPathRejected :
    AllPass (test_fs_vfs_withFileLock_invalidPathRejected (Internal.mkApiM vfsOps)) := by
  intro s₀ path markerPath mode createIfMissing hBadPath hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, Internal.withFileLockImplM, vfsOps, StateT.run, bind, StateT.bind,
    pure, StateT.pure, assert] at hMarkerNone ⊢
  have hInvalid : isValidLockPath path = false := by
    unfold isValidLockPath
    rcases hBadPath with hEmpty | ⟨hGt, hSlash⟩
    · simp [hEmpty]
    · cases hc : path.toList with
      | nil => simp
      | cons c rest =>
        have hGt' : (c :: rest).length > 1 := by simpa [hc] using hGt
        have hSlash' : (c :: rest).getLast? = some '/' := by simpa [hc] using hSlash
        have hPos : 0 < rest.length := by simp at hGt'; omega
        simp [hPos, hSlash']
  have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
      (.error { kind := .invalidInput, path := some path, message := "invalid lock path" }, s₀) := by
    rw [vfsAcquireLockPure_unfold]
    rw [hInvalid]
    rfl
  rw [hAcq]
  exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_invalidPathRejected`. -/
theorem reach_fs_vfs_withFileLock_invalidPathRejected :
    CanReach (test_fs_vfs_withFileLock_invalidPathRejected (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "", "/marker", .exclusive, true, Or.inl rfl, hMarker,
    proof_fs_vfs_withFileLock_invalidPathRejected st "" "/marker" .exclusive true (Or.inl rfl) hMarker⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_releasesOnOk` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_tryWithFileLock_releasesOnOk :
    AllPass (test_fs_vfs_tryWithFileLock_releasesOnOk (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode createIfMissing val hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  have hBoth :
      ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.ok val))).run s₀).1 = .ok (some val) ∧
      ((vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run
        ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.ok val))).run s₀).2).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
        ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        canon path mode (Or.inl rfl)
      simp only [hRel, true_and]
      rw [vfsTryWithFileLock_pure_step]
      let s₁ : VfsState := { s₀ with nextLockId := freshLockId s₀ }
      have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
          (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
            { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [show s₁.nodes = s₀.nodes from rfl, show s₁.cwd = s₀.cwd from rfl, hRes]
        dsimp only
        simp [s₁, hConfEx]
      rw [hAcqS1]
      have hRelS1 := vfsReleaseLockPure_fresh s₁
        { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
        canon path .exclusive (Or.inl rfl)
      simp [hRelS1]
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with
          tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: s₀.keys
          locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
          nextLockId := freshLockId s₀ }
        (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
      simp only [hRel, true_and]
      exact (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
  dsimp only [assert]
  exact ⟨hBoth, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_releasesOnOk`. -/
theorem reach_fs_vfs_tryWithFileLock_releasesOnOk :
    CanReach (test_fs_vfs_tryWithFileLock_releasesOnOk (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/try.lock")) false 1024 =
      .error { kind := .notFound, path := some "/try.lock", message := "no such file or directory: /try.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/try.lock" = "/try.lock" from by decide,
        show vfsSplitSegs "/try.lock" = ["try.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "try.lock" = "/try.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/try.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/try.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/try.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/try.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "try.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "try.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "try.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/try.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/try.lock" = "/try.lock" from by decide,
          show vfsSplitSegs "/try.lock" = ["try.lock"] from by decide,
          show Internal.splitLastAux ["try.lock"] [] = some ([], "try.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "try.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "try.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "try.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "try.lock") "/try.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/try.lock", .shared, true, 9, hProbe,
    proof_fs_vfs_tryWithFileLock_releasesOnOk st "/try.lock" .shared true 9 hProbe⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_missingNotSwallowed` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_tryWithFileLock_missingNotSwallowed :
    AllPass (test_fs_vfs_tryWithFileLock_missingNotSwallowed (Internal.mkApiM vfsOps)) := by
  intro s₀ path markerPath mode hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨e, hStat, hNf⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    dsimp only [Internal.tryWithFileLockImplM, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
    have hAcq : vfsAcquireLockPure s₀ path mode false true = (.error e', s₀) := by
      rw [vfsAcquireLockPure_unfold]
      rw [hValid]
      dsimp only
      rw [hRes]
      dsimp only
      simp [hNf]
    rw [hAcq]
    have hNotWb : (e'.kind == .wouldBlock) = false := by rw [hNf]; decide
    simp only [hNotWb, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨⟨_, rfl, hNf⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_missingNotSwallowed`. -/
theorem reach_fs_vfs_tryWithFileLock_missingNotSwallowed :
    CanReach (test_fs_vfs_tryWithFileLock_missingNotSwallowed (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hStat : ((vfsApi.lstat "/missing.lock").run st).1 =
      .error { kind := .notFound, path := some "/missing.lock", message := "no such file or directory: /missing.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/missing.lock" = "/missing.lock" from by decide,
        show vfsSplitSegs "/missing.lock" = ["missing.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "missing.lock" = "/missing.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/missing.lock" = none from rfl]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkApiFromScopedRawM, Internal.toScopedRawFsOpsM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/missing.lock", "/marker", .exclusive, by decide, Or.inr (by decide),
    ⟨_, hStat, rfl⟩, hMarker,
    proof_fs_vfs_tryWithFileLock_missingNotSwallowed st "/missing.lock" "/marker" .exclusive (by decide) (Or.inr (by decide))
      ⟨_, hStat, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_releasesOnActionError` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_tryWithFileLock_releasesOnActionError :
    AllPass (test_fs_vfs_tryWithFileLock_releasesOnActionError (Internal.mkApiM vfsOps)) := by
  intro s₀ path mode createIfMissing err hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  have hBoth :
      ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀).1 =
        .error err ∧
      ((vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run
        ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀).2).1 =
        .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
        ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        canon path mode (Or.inl rfl)
      simp only [hRel, true_and]
      rw [vfsTryWithFileLock_pure_step]
      let s₁ : VfsState := { s₀ with nextLockId := freshLockId s₀ }
      have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
          (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
            { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
        rw [vfsAcquireLockPure_unfold]
        rw [hValid]
        dsimp only
        rw [show s₁.nodes = s₀.nodes from rfl, show s₁.cwd = s₀.cwd from rfl, hRes]
        dsimp only
        simp [s₁, hConfEx]
      rw [hAcqS1]
      have hRelS1 := vfsReleaseLockPure_fresh s₁
        { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
        canon path .exclusive (Or.inl rfl)
      simp [hRelS1]
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with
          tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: s₀.keys
          locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
          nextLockId := freshLockId s₀ }
        (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
      simp only [hRel, true_and]
      exact (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
  dsimp only [assert]
  exact ⟨hBoth, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_releasesOnActionError`. -/
theorem reach_fs_vfs_tryWithFileLock_releasesOnActionError :
    CanReach (test_fs_vfs_tryWithFileLock_releasesOnActionError (Internal.mkApiM vfsOps)) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .permissionDenied, message := "boom" }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/tryerr.lock")) false 1024 =
      .error { kind := .notFound, path := some "/tryerr.lock", message := "no such file or directory: /tryerr.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/tryerr.lock" = "/tryerr.lock" from by decide,
        show vfsSplitSegs "/tryerr.lock" = ["tryerr.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "tryerr.lock" = "/tryerr.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/tryerr.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/tryerr.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/tryerr.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/tryerr.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "tryerr.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "tryerr.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "tryerr.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      rw [vfsAcquireLockPure_unfold]
      rw [show isValidLockPath "/tryerr.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/tryerr.lock" = "/tryerr.lock" from by decide,
          show vfsSplitSegs "/tryerr.lock" = ["tryerr.lock"] from by decide,
          show Internal.splitLastAux ["tryerr.lock"] [] = some ([], "tryerr.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "tryerr.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "tryerr.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "tryerr.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "tryerr.lock") "/tryerr.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/tryerr.lock", .shared, true, err, hProbe,
    proof_fs_vfs_tryWithFileLock_releasesOnActionError st "/tryerr.lock" .shared true err hProbe⟩

end LeanSwe.Fs.Proofs

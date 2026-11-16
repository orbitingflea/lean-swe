import LeanSwe.Fs.Proofs.SubtreeCore

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs
open LeanSwe.Fs.Raw
open LeanSwe.Fs.Model

/-- State transition relation for an interleaved subtree step confined inside `pos` without leaking open handles or locks. -/
def InsideStep (pos : List String) (s0 s1 : VfsState) : Prop :=
  SameOutside pos s0 s1 ∧ s1.openDirs = s0.openDirs ∧ s1.locks = s0.locks

/-- Reflexivity of `InsideStep`. -/
theorem InsideStep_refl (pos : List String) (s : VfsState) : InsideStep pos s s :=
  ⟨SameOutside_refl pos s, rfl, rfl⟩

/-- Transitivity of `InsideStep`. -/
theorem InsideStep_trans {pos : List String} {s0 s1 s2 : VfsState}
    (h01 : InsideStep pos s0 s1) (h12 : InsideStep pos s1 s2) : InsideStep pos s0 s2 :=
  ⟨SameOutside_trans h01.1 h12.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

/-- Monotonicity of `InsideStep` under prefix widening. -/
theorem InsideStep_mono {a b : List String} {s0 s1 : VfsState}
    (hPre : a <+: b) (h : InsideStep b s0 s1) : InsideStep a s0 s1 :=
  ⟨SameOutside_mono hPre h.1, h.2.1, h.2.2⟩

private theorem insideStep_env {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (s : VfsState) : InsideStep pos s (env s) :=
  ⟨(hEnv s).1, (hEnv s).2.2.2.1, (hEnv s).2.2.2.2⟩

private theorem tryFinally_stateM_run {α β : Type} (act : StateM VfsState α)
    (fin : Option α → StateM VfsState β) (s : VfsState) :
    tryFinally' act fin s =
      let (a, s1) := act s
      let (b, s2) := fin (some a) s1
      ((a, b), s2) :=
  rfl

private theorem splitLastAux_append_singleton_entry {xs acc : List EntryName} {leaf : EntryName} :
    Internal.splitLastAux (xs ++ [leaf]) acc = some (acc.reverse ++ xs, leaf) := by
  induction xs generalizing acc with
  | nil => simp [Internal.splitLastAux]
  | cons x rest ih =>
    simp only [List.cons_append]
    cases rest with
    | nil => simp [Internal.splitLastAux]
    | cons y ys =>
      simpa [Internal.splitLastAux, List.append_assoc] using ih (acc := x :: acc)

private theorem splitLastAux_split_ge_pre {pre rest : List EntryName} (hRest : rest ≠ [])
    {walkPre : List EntryName} {leaf : EntryName}
    (hSp : Internal.splitLastAux (pre ++ rest) [] = some (walkPre, leaf)) :
    ∃ mid : List EntryName, walkPre = pre ++ mid := by
  have hLen : ∃ init : List EntryName, rest = init ++ [leaf] ∧ walkPre = pre ++ init := by
    have hJoin : ∀ {xs acc init : List EntryName} {l : EntryName},
        Internal.splitLastAux xs acc = some (init, l) → acc.reverse ++ xs = init ++ [l] := by
      intro xs
      induction xs with
      | nil => intro acc init l h; simp [Internal.splitLastAux] at h
      | cons x xt ih =>
        intro acc init l h
        cases xt with
        | nil =>
          simp only [Internal.splitLastAux, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp
        | cons y yt =>
          simp only [Internal.splitLastAux] at h
          simpa [List.append_assoc] using ih h
    have hEq := hJoin hSp
    simp only [List.reverse_nil, List.nil_append] at hEq
    cases hRRev : rest.reverse with
    | nil => exact absurd (congrArg List.reverse hRRev) (by simpa using hRest)
    | cons lastRev initRev =>
      have hRestEq : rest = initRev.reverse ++ [lastRev] := by
        simpa using congrArg List.reverse hRRev
      rw [hRestEq, ← List.append_assoc] at hEq
      have hLast : lastRev = leaf := by
        have hLastOpt := congrArg List.getLast? hEq
        simpa using hLastOpt
      subst hLast
      have hPreInit : pre ++ initRev.reverse = walkPre := by
        have hPop2 := congrArg List.dropLast hEq
        simpa using hPop2
      exact ⟨initRev.reverse, hRestEq, hPreInit.symm⟩
  rcases hLen with ⟨init, _, hW⟩
  exact ⟨init, hW⟩

private theorem foldl_maxDirId_ge (xs : List (Nat × List String)) (q : Nat × List String) (hq : q ∈ xs) :
    q.1 ≤ mMaxDirId xs := by
  induction xs with
  | nil => cases hq
  | cons a tl ih =>
    rcases List.mem_cons.mp hq with rfl | htl
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

private theorem lookupDir_mem_openDirs {st : VfsState} {dh : DirHandle} {pos : List String}
    (h : lookupDir st dh = some pos) : (dh.handleId, pos) ∈ st.openDirs ∧ dh.handleId ≠ 0 := by
  unfold lookupDir at h
  by_cases hz : (dh.handleId == 0) = true
  · simp [hz] at h
  · have hzF : (dh.handleId == 0) = false := Bool.eq_false_iff.mpr hz
    simp only [hzF, Bool.false_eq_true, ↓reduceIte] at h
    cases hf : st.openDirs.find? (fun p => p.1 == dh.handleId) with
    | none => simp [hf] at h
    | some pair =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      have hMem := List.mem_of_find?_eq_some hf
      have hPred : (fun p : Nat × List String => p.1 == dh.handleId) pair = true :=
        List.find?_some (p := fun p : Nat × List String => p.1 == dh.handleId) hf
      dsimp only at hPred
      have hIdEq : pair.1 = dh.handleId := beq_iff_eq.mp hPred
      have hPair : pair = (dh.handleId, pos) := Prod.ext hIdEq h
      exact ⟨hPair ▸ hMem, fun h0 => hz (beq_iff_eq.mpr h0)⟩

private theorem lookupDir_cons_ne {st : VfsState} {dh : DirHandle} {id : Nat} {pos : List String}
    (hNe : id ≠ dh.handleId) :
    lookupDir { st with openDirs := (id, pos) :: st.openDirs } dh = lookupDir st dh := by
  unfold lookupDir
  by_cases hz : (dh.handleId == 0) = true
  · simp [hz]
  · simp [hz, beq_false_of_ne hNe]

private theorem interleave_fstatDir_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (s : VfsState) :
    InsideStep pos s ((interleave env vfsDirOps).fstatDir dh s).2 :=
  insideStep_env hEnv s

private theorem interleave_lstatAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (name : EntryName) (s : VfsState) :
    InsideStep pos s ((interleave env vfsDirOps).lstatAt dh name s).2 :=
  insideStep_env hEnv s

private theorem interleave_readDirAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (s : VfsState) :
    InsideStep pos s ((interleave env vfsDirOps).readDirAt dh s).2 :=
  insideStep_env hEnv s

private theorem interleave_readRegularAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (name : EntryName) (s : VfsState) :
    InsideStep pos s ((interleave env vfsDirOps).readRegularAt dh name s).2 :=
  insideStep_env hEnv s

private theorem interleave_freshTempName_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (s : VfsState) :
    InsideStep pos s ((interleave env vfsDirOps).freshTempName s).2 := by
  have he := insideStep_env hEnv s
  rcases vfsDirOps_freshTempName_def (env s) with ⟨_, hSt⟩
  change InsideStep pos s (vfsDirOps.freshTempName (env s)).2
  rw [hSt]
  exact ⟨he.1, he.2.1, he.2.2⟩

private theorem interleave_createDirAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (name : EntryName) (s : VfsState)
    (hConfined : ∀ dhPos, lookupDir s dh = some dhPos → pos <+: dhPos) :
    InsideStep pos s ((interleave env vfsDirOps).createDirAt dh name s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep pos s (vfsDirOps.createDirAt dh name (env s)).2
  rw [vfsDirOps_createDirAt_def]
  have hLdEq : lookupDir (env s) dh = lookupDir s dh := by simp [lookupDir, (hEnv s).2.2.2.1]
  cases hLd : lookupDir s dh with
  | none => simp [hLdEq, hLd, he]
  | some dhPos =>
    have hPre := hConfined dhPos hLd
    simp only [hLdEq, hLd]
    cases hP : nodeAt (env s).tree dhPos with
    | none => exact he
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => exact he
      | dir parMode =>
        dsimp only
        split
        · exact he
        · cases hC : nodeAt (env s).tree (dhPos ++ [name.val]) with
          | some _ => exact he
          | none =>
            rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
            exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet hPre ⟨parMode, ch, hDir⟩ rfl), he.2.1, he.2.2⟩

private theorem interleave_createFileAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (name : EntryName) (bytes : ByteArray) (s : VfsState)
    (hConfined : ∀ dhPos, lookupDir s dh = some dhPos → pos <+: dhPos) :
    InsideStep pos s ((interleave env vfsDirOps).createFileAt dh name bytes s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep pos s (vfsDirOps.createFileAt dh name bytes (env s)).2
  rw [vfsDirOps_createFileAt_def]
  have hLdEq : lookupDir (env s) dh = lookupDir s dh := by simp [lookupDir, (hEnv s).2.2.2.1]
  cases hLd : lookupDir s dh with
  | none => simp [hLdEq, hLd, he]
  | some dhPos =>
    have hPre := hConfined dhPos hLd
    simp only [hLdEq, hLd]
    cases hP : nodeAt (env s).tree dhPos with
    | none => exact he
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => exact he
      | dir parMode =>
        dsimp only
        split
        · exact he
        · cases hC : nodeAt (env s).tree (dhPos ++ [name.val]) with
          | some _ => exact he
          | none =>
            rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
            exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet hPre ⟨parMode, ch, hDir⟩ rfl), he.2.1, he.2.2⟩

private theorem interleave_unlinkAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (name : EntryName) (isDir : Bool) (s : VfsState)
    (hConfined : ∀ dhPos, lookupDir s dh = some dhPos → pos <+: dhPos) :
    InsideStep pos s ((interleave env vfsDirOps).unlinkAt dh name isDir s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep pos s (vfsDirOps.unlinkAt dh name isDir (env s)).2
  rw [vfsDirOps_unlinkAt_def]
  have hLdEq : lookupDir (env s) dh = lookupDir s dh := by simp [lookupDir, (hEnv s).2.2.2.1]
  cases hLd : lookupDir s dh with
  | none => simp [hLdEq, hLd, he]
  | some dhPos =>
    have hPre := hConfined dhPos hLd
    simp only [hLdEq, hLd]
    cases hP : nodeAt (env s).tree dhPos with
    | none => exact he
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => exact he
      | dir parMode =>
        dsimp only
        split
        · exact he
        · cases hC : nodeAt (env s).tree (dhPos ++ [name.val]) with
          | none => exact he
          | some cnode =>
            rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
            cases cnode with
            | dir _ =>
              dsimp only
              split
              · exact he
              · split
                · exact he
                · exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet hPre ⟨parMode, ch, hDir⟩ rfl),
                    he.2.1, he.2.2⟩
            | file _ _ | symlink _ _ =>
              dsimp only
              split
              · exact he
              · exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet hPre ⟨parMode, ch, hDir⟩ rfl),
                  he.2.1, he.2.2⟩

private theorem interleave_symlinkAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (target : String) (dh : DirHandle) (name : EntryName) (s : VfsState)
    (hConfined : ∀ dhPos, lookupDir s dh = some dhPos → pos <+: dhPos) :
    InsideStep pos s ((interleave env vfsDirOps).symlinkAt target dh name s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep pos s (vfsDirOps.symlinkAt target dh name (env s)).2
  rw [vfsDirOps_symlinkAt_def]
  dsimp only
  split
  · exact he
  · have hLdEq : lookupDir (env s) dh = lookupDir s dh := by simp [lookupDir, (hEnv s).2.2.2.1]
    cases hLd : lookupDir s dh with
    | none => simp [hLdEq, hLd, he]
    | some dhPos =>
      have hPre := hConfined dhPos hLd
      simp only [hLdEq, hLd]
      cases hP : nodeAt (env s).tree dhPos with
      | none => exact he
      | some node =>
        cases node with
        | file _ _ | symlink _ _ => exact he
        | dir parMode =>
          dsimp only
          split
          · exact he
          · cases hC : nodeAt (env s).tree (dhPos ++ [name.val]) with
            | some _ => exact he
            | none =>
              rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
              exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet hPre ⟨parMode, ch, hDir⟩ rfl),
                he.2.1, he.2.2⟩

private theorem interleave_renameAt_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (srcDh : DirHandle) (srcName : EntryName)
    (dstDh : DirHandle) (dstName : EntryName) (s : VfsState)
    (hSrc : ∀ sp, lookupDir s srcDh = some sp → pos <+: sp)
    (hDst : ∀ dp, lookupDir s dstDh = some dp → pos <+: dp) :
    InsideStep pos s ((interleave env vfsDirOps).renameAt srcDh srcName dstDh dstName s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep pos s (vfsDirOps.renameAt srcDh srcName dstDh dstName (env s)).2
  rw [vfsDirOps_renameAt_def]
  have hLdS : lookupDir (env s) srcDh = lookupDir s srcDh := by simp [lookupDir, (hEnv s).2.2.2.1]
  have hLdD : lookupDir (env s) dstDh = lookupDir s dstDh := by simp [lookupDir, (hEnv s).2.2.2.1]
  cases hs : lookupDir s srcDh with
  | none => simp [hLdS, hs, he]
  | some srcPos =>
    cases hd : lookupDir s dstDh with
    | none => simp [hLdS, hLdD, hs, hd, he]
    | some dstPos =>
      have hPreS := hSrc srcPos hs
      have hPreD := hDst dstPos hd
      simp only [hLdS, hLdD, hs, hd]
      cases hPs : nodeAt (env s).tree srcPos with
      | none => exact he
      | some sNode =>
        cases sNode with
        | file _ _ | symlink _ _ => cases nodeAt (env s).tree dstPos <;> exact he
        | dir srcMode =>
          cases hPd : nodeAt (env s).tree dstPos with
          | none => exact he
          | some dNode =>
            cases dNode with
            | file _ _ | symlink _ _ => exact he
            | dir dstMode =>
              dsimp only
              split
              · exact he
              · split
                · exact he
                · cases hGet : vfsTreeGet (env s).tree (srcPos ++ [srcName.val]) with
                  | none => exact he
                  | some srcSub =>
                    dsimp only
                    split
                    · exact he
                    · split
                      · exact he
                      · next hNotPre =>
                        have hNotPreProp : ¬ (srcPos ++ [srcName.val]) <+: dstPos := by
                          intro hp
                          exact hNotPre (List.isPrefixOf_iff_prefix.mpr hp)
                        rcases vfsTreeGet_dir_of_nodeAt hPs with ⟨sch, hSDir⟩
                        rcases vfsTreeGet_dir_of_nodeAt hPd with ⟨dch, hDDir⟩
                        let tr1 := vfsTreeSet (env s).tree (srcPos ++ [srcName.val]) none
                        have hOut1 : SameOutside pos (env s) { env s with tree := tr1 } :=
                          SameOutside_of_vfsTreeSet hPreS ⟨srcMode, sch, hSDir⟩ rfl
                        have hPd1 : nodeAt tr1 dstPos = some (.dir dstMode) := by
                          rw [nodeAt_vfsTreeSet_outside _ srcPos srcName.val none dstPos ⟨srcMode, sch, hSDir⟩ hNotPreProp]
                          exact hPd
                        rcases vfsTreeGet_dir_of_nodeAt hPd1 with ⟨dch1, hDDir1⟩
                        have hOut2 : SameOutside pos { env s with tree := tr1 }
                            { env s with
                              tree := vfsTreeSet tr1 (dstPos ++ [dstName.val]) (some srcSub)
                              keys := pathOfSegs (dstPos ++ [dstName.val]) :: mRemapKeysAfterRename (env s).keys (srcPos ++ [srcName.val]) (dstPos ++ [dstName.val]) } :=
                          SameOutside_of_vfsTreeSet hPreD ⟨dstMode, dch1, hDDir1⟩ rfl
                        have hOutBoth := SameOutside_trans he.1 (SameOutside_trans hOut1 hOut2)
                        have hStep : InsideStep pos s { env s with
                              tree := vfsTreeSet tr1 (dstPos ++ [dstName.val]) (some srcSub)
                              keys := pathOfSegs (dstPos ++ [dstName.val]) :: mRemapKeysAfterRename (env s).keys (srcPos ++ [srcName.val]) (dstPos ++ [dstName.val]) } :=
                          ⟨hOutBoth, he.2.1, he.2.2⟩
                        split <;> first
                          | exact he
                          | exact hStep
                          | (split <;> first | exact he | exact hStep)

private theorem SameOutside_of_vfsTreeSet_target {st st' : VfsState} {pos base : List String}
    {leaf : String} {v : Option VfsTree} (hPre : pos <+: base ++ [leaf])
    (hDir : ∃ dm ch, vfsTreeGet st.tree base = some (.dir dm ch))
    (hTr : st'.tree = vfsTreeSet st.tree (base ++ [leaf]) v) :
    SameOutside pos st st' := by
  intro p hp
  simp only [VfsState.nodes, vfsTreeNodes]
  cases hc : isCanonPath p
  · rfl
  · simp only [↓reduceIte, hTr]
    have hNot : ¬ base ++ [leaf] <+: vfsSplitSegs p := fun h => hp (List.IsPrefix.trans hPre h)
    rw [nodeAt_vfsTreeSet_outside st.tree base leaf v (vfsSplitSegs p) hDir hNot]

private def OwnedHandle (baseDirs : List (Nat × List String))
    (isRoot : Bool) (cur : DirHandle) (curPos : List String) (s : VfsState) : Prop :=
  if isRoot then
    s.openDirs = baseDirs ∧ lookupDir s cur = some curPos
  else
    0 < cur.handleId ∧ (∀ q ∈ baseDirs, q.1 < cur.handleId) ∧ s.openDirs = (cur.handleId, curPos) :: baseDirs

private theorem ownedHandle_lookup {baseDirs : List (Nat × List String)}
    {isRoot : Bool} {cur : DirHandle} {curPos : List String} {s : VfsState}
    (h : OwnedHandle baseDirs isRoot cur curPos s) :
    lookupDir s cur = some curPos := by
  cases isRoot
  · simp only [OwnedHandle, Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨hPos, _, hDirs⟩
    unfold lookupDir
    rw [hDirs, beq_false_of_ne (Nat.ne_of_gt hPos)]
    simp
  · simp only [OwnedHandle, ↓reduceIte] at h
    exact h.2

private theorem interleave_closeDir_owned {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (cur : DirHandle) (curPos : List String)
    (baseDirs : List (Nat × List String))
    (hPos : 0 < cur.handleId) (hLt : ∀ q ∈ baseDirs, q.1 < cur.handleId)
    {s : VfsState} (hDirs : s.openDirs = (cur.handleId, curPos) :: baseDirs) :
    let (_, s') := (interleave env vfsDirOps).closeDir cur s
    SameOutside pos s s' ∧ s'.openDirs = baseDirs ∧ s'.locks = s.locks := by
  have he := insideStep_env hEnv s
  change let (_, s') := vfsDirOps.closeDir cur (env s); SameOutside pos s s' ∧ s'.openDirs = baseDirs ∧ s'.locks = s.locks
  rw [vfsDirOps_closeDir_def]
  have hEnvDirs : (env s).openDirs = (cur.handleId, curPos) :: baseDirs := he.2.1.trans hDirs
  have hNe0 : (cur.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  have hAny : (env s).openDirs.any (fun p => p.1 == cur.handleId) = true := by
    rw [hEnvDirs]
    simp
  simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hAny]
  have hFilter : (env s).openDirs.filter (fun p => p.1 != cur.handleId) = baseDirs := by
    rw [hEnvDirs, List.filter_cons, bne_self_eq_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.mpr fun q hq => bne_iff_ne.mpr (Nat.ne_of_lt (hLt q hq))
  exact ⟨he.1, hFilter, he.2.2⟩

private theorem bracketCloseDirM_owned {α : Type} {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (cur : DirHandle) (curPos : List String)
    (baseDirs : List (Nat × List String))
    (hPos : 0 < cur.handleId) (hLt : ∀ q ∈ baseDirs, q.1 < cur.handleId)
    (act : StateM VfsState α) {s0 : VfsState}
    (hDirs0 : s0.openDirs = (cur.handleId, curPos) :: baseDirs)
    (hAct : match act s0 with | (_, s1) => SameOutside pos s0 s1 ∧ s1.openDirs = s0.openDirs ∧ s1.locks = s0.locks) :
    match (Internal.bracketCloseDirM (interleave env vfsDirOps) cur act) s0 with
    | (res, s2) => res = (act s0).1 ∧ SameOutside pos s0 s2 ∧ s2.openDirs = baseDirs ∧ s2.locks = s0.locks := by
  dsimp only [Internal.bracketCloseDirM, bind, StateT.bind, pure, StateT.pure]
  rw [tryFinally_stateM_run]
  cases hA : act s0 with
  | mk a s1 =>
    rw [hA] at hAct
    dsimp only at hAct ⊢
    have hClose := interleave_closeDir_owned hEnv cur curPos baseDirs hPos hLt (hAct.2.1.trans hDirs0)
    cases hCl : (interleave env vfsDirOps).closeDir cur s1 with
    | mk _ s2 =>
      rw [hCl] at hClose
      dsimp only at hClose
      exact ⟨rfl, SameOutside_trans hAct.1 hClose.1, hClose.2.1, hClose.2.2.trans hAct.2.2⟩

private theorem step_openDirAt_owned {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (baseDirs : List (Nat × List String))
    (isRoot : Bool) (cur : DirHandle) (curPos : List String) (seg : EntryName) (s0 : VfsState)
    (hOwn : OwnedHandle baseDirs isRoot cur curPos s0)
    (step : StateM VfsState (Except FsError DirHandle))
    (hStepErr : ∀ e s1, step s0 = (.error e, s1) → InsideStep pos s0 s1)
    (hStepOk : ∀ nextDh s1, step s0 = (.ok nextDh, s1) →
      0 < nextDh.handleId ∧
      (∀ q ∈ s0.openDirs, q.1 < nextDh.handleId) ∧
      SameOutside pos s0 s1 ∧
      s1.openDirs = (nextDh.handleId, curPos ++ [seg.val]) :: s0.openDirs ∧
      s1.locks = s0.locks) :
    match (if isRoot then step else Internal.bracketCloseDirM (interleave env vfsDirOps) cur step) s0 with
    | (.error _, s2) => SameOutside pos s0 s2 ∧ s2.openDirs = baseDirs ∧ s2.locks = s0.locks
    | (.ok nextDh, s2) =>
        SameOutside pos s0 s2 ∧
        s2.locks = s0.locks ∧
        OwnedHandle baseDirs false nextDh (curPos ++ [seg.val]) s2 := by
  cases isRoot
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hOwn with ⟨hPos, hLt, hDirs⟩
    dsimp only [Internal.bracketCloseDirM, bind, StateT.bind, pure, StateT.pure]
    rw [tryFinally_stateM_run]
    cases hs : step s0 with
    | mk r s1 =>
      cases r with
      | error e =>
        dsimp only at hs ⊢
        have hErr := hStepErr e s1 hs
        have hClose := interleave_closeDir_owned hEnv cur curPos baseDirs hPos hLt (hErr.2.1.trans hDirs)
        cases hCl : (interleave env vfsDirOps).closeDir cur s1 with
        | mk _ s2 =>
          rw [hCl] at hClose
          exact ⟨SameOutside_trans hErr.1 hClose.1, hClose.2.1, hClose.2.2.trans hErr.2.2⟩
      | ok nextDh =>
        dsimp only at hs ⊢
        rcases hStepOk nextDh s1 hs with ⟨hNextPos, hNextGt, hOut1, hDirs1, hLocks1⟩
        have he := insideStep_env hEnv s1
        have hEnvDirs : (env s1).openDirs = (nextDh.handleId, curPos ++ [seg.val]) :: (cur.handleId, curPos) :: baseDirs := by
          rw [he.2.1, hDirs1, hDirs]
        have hNe0 : (cur.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
        have hAny : (env s1).openDirs.any (fun p => p.1 == cur.handleId) = true := by
          rw [hEnvDirs]
          simp
        have hCurLtNext : cur.handleId < nextDh.handleId := hNextGt (cur.handleId, curPos) (by rw [hDirs]; simp)
        have hFilter : (env s1).openDirs.filter (fun p => p.1 != cur.handleId) = (nextDh.handleId, curPos ++ [seg.val]) :: baseDirs := by
          rw [hEnvDirs, List.filter_cons, bne_iff_ne.mpr (Nat.ne_of_gt hCurLtNext),
            List.filter_cons, bne_self_eq_false]
          simp only [↓reduceIte, Bool.false_eq_true, List.cons.injEq, true_and]
          exact List.filter_eq_self.mpr fun q hq => bne_iff_ne.mpr (Nat.ne_of_lt (hLt q hq))
        have hCl : (interleave env vfsDirOps).closeDir cur s1 =
            (.ok (), { env s1 with openDirs := (nextDh.handleId, curPos ++ [seg.val]) :: baseDirs }) := by
          change vfsDirOps.closeDir cur (env s1) = _
          rw [vfsDirOps_closeDir_def, hNe0]
          simp [hAny, hFilter]
        rw [hCl]
        dsimp only
        have hGtBase : ∀ q ∈ baseDirs, q.1 < nextDh.handleId := fun q hq =>
          hNextGt q (by rw [hDirs]; exact List.mem_cons_of_mem _ hq)
        exact ⟨SameOutside_trans hOut1 he.1, he.2.2.trans hLocks1, hNextPos, hGtBase, rfl⟩
  · simp only [↓reduceIte]
    rcases hOwn with ⟨hDirs, _⟩
    cases hs : step s0 with
    | mk r s1 =>
      cases r with
      | error e =>
        have hErr := hStepErr e s1 hs
        exact ⟨hErr.1, hErr.2.1.trans hDirs, hErr.2.2⟩
      | ok nextDh =>
        rcases hStepOk nextDh s1 hs with ⟨hNextPos, hNextGt, hOut1, hDirs1, hLocks1⟩
        have hGtBase : ∀ q ∈ baseDirs, q.1 < nextDh.handleId := fun q hq => hNextGt q (hDirs ▸ hq)
        exact ⟨hOut1, hLocks1, hNextPos, hGtBase, hDirs1.trans (congrArg _ hDirs)⟩

private theorem walkDescendAuxM_owned {α : Type} {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (baseDirs : List (Nat × List String))
    (segs : List EntryName) (act : DirHandle → StateM VfsState (Except FsError α))
    (isRoot : Bool) (cur : DirHandle) (curPos : List String) (s0 : VfsState)
    (hOwn : OwnedHandle baseDirs isRoot cur curPos s0)
    (hAct : ∀ isR c cp s, OwnedHandle baseDirs isR c cp s →
      cp = curPos ++ segs.map (·.val) → InsideStep pos s (act c s).2) :
    match (Internal.walkDescendAuxM (interleave env vfsDirOps) isRoot cur segs act) s0 with
    | (_, sOut) => SameOutside pos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = s0.locks := by
  revert hOwn hAct
  induction segs generalizing isRoot cur curPos s0 with
  | nil =>
    intro hOwn hAct
    dsimp only [Internal.walkDescendAuxM]
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hStep := hAct false cur curPos s0 hOwn (by simp)
      rcases hOwn with ⟨hPos, hLt, hDirs⟩
      have hBr := bracketCloseDirM_owned hEnv cur curPos baseDirs hPos hLt (act cur) hDirs hStep
      cases hRes : (Internal.bracketCloseDirM (interleave env vfsDirOps) cur (act cur)) s0 with
      | mk _ _ =>
        rw [hRes] at hBr
        exact hBr.2
    · simp only [↓reduceIte]
      have hStep := hAct true cur curPos s0 hOwn (by simp)
      rcases hOwn with ⟨hDirs, _⟩
      exact ⟨hStep.1, hStep.2.1.trans hDirs, hStep.2.2⟩
  | cons seg rest ih =>
    intro hOwn hAct
    have hOpen := step_openDirAt_owned hEnv baseDirs isRoot cur curPos seg s0 hOwn
      ((interleave env vfsDirOps).openDirAt cur seg)
      (fun e s1 hErr => by
        change (vfsDirOps.openDirAt cur seg (env s0)) = (.error e, s1) at hErr
        rw [vfsDirOps_openDirAt_err cur seg (env s0) e s1 hErr]
        exact insideStep_env hEnv s0)
      (fun nextDh s1 hOk => by
        change (vfsDirOps.openDirAt cur seg (env s0)) = (.ok nextDh, s1) at hOk
        rcases vfsDirOps_openDirAt_ok cur seg (env s0) nextDh s1 hOk with
          ⟨hNextPos, _, hNextGt, _, _, _, hLd, _, _, _, _, _, hSt1⟩
        have he := insideStep_env hEnv s0
        have hLdEq : lookupDir (env s0) cur = lookupDir s0 cur := by simp [lookupDir, he.2.1]
        rw [hLdEq, ownedHandle_lookup hOwn] at hLd
        cases hLd
        rw [hSt1]
        exact ⟨hNextPos, fun q hq => hNextGt q (he.2.1 ▸ hq), he.1, by simp [he.2.1], he.2.2⟩)
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte] at hOpen
      unfold Internal.walkDescendAuxM
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hStep : (Internal.bracketCloseDirM (interleave env vfsDirOps) cur ((interleave env vfsDirOps).openDirAt cur seg)) s0 with
      | mk r s1 =>
        rw [hStep] at hOpen
        dsimp only
        cases r with
        | error e => exact hOpen
        | ok nextDh =>
          dsimp only
          rcases hOpen with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hOwn1
            (fun isR c cp s hOw hCp => hAct isR c cp s hOw (by simpa [List.append_assoc] using hCp))
          cases hWalk : (Internal.walkDescendAuxM (interleave env vfsDirOps) false nextDh rest act) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩
    · simp only [↓reduceIte] at hOpen
      unfold Internal.walkDescendAuxM
      simp only [↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hStep : ((interleave env vfsDirOps).openDirAt cur seg) s0 with
      | mk r s1 =>
        rw [hStep] at hOpen
        dsimp only
        cases r with
        | error e => exact hOpen
        | ok nextDh =>
          dsimp only
          rcases hOpen with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hOwn1
            (fun isR c cp s hOw hCp => hAct isR c cp s hOw (by simpa [List.append_assoc] using hCp))
          cases hWalk : (Internal.walkDescendAuxM (interleave env vfsDirOps) false nextDh rest act) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩

private theorem walkDescendM_inside {α : Type} {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (dhPos : List String)
    (segs : List EntryName) (act : DirHandle → StateM VfsState (Except FsError α))
    (s0 : VfsState) (hLd : lookupDir s0 dh = some dhPos)
    (hAct : ∀ isR c cp s, OwnedHandle s0.openDirs isR c cp s →
      cp = dhPos ++ segs.map (·.val) → InsideStep pos s (act c s).2) :
    InsideStep pos s0 ((Internal.walkDescendM (interleave env vfsDirOps) dh segs act) s0).2 :=
  walkDescendAuxM_owned hEnv s0.openDirs segs act true dh dhPos s0 ⟨rfl, hLd⟩ hAct

private theorem insideStep_walkDescend_eq {α : Type} {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (dhPos : List String)
    (segs : List EntryName) (act : DirHandle → StateM VfsState (Except FsError α))
    (s0 : VfsState) (r : Except FsError α) (s1 : VfsState)
    (hEq : Internal.walkDescendM (interleave env vfsDirOps) dh segs act s0 = (r, s1))
    (hLd : lookupDir s0 dh = some dhPos)
    (hAct : ∀ isR c cp s, OwnedHandle s0.openDirs isR c cp s →
      cp = dhPos ++ segs.map (·.val) → InsideStep pos s (act c s).2) :
    InsideStep pos s0 s1 := by
  have h := walkDescendM_inside hEnv dh dhPos segs act s0 hLd hAct
  rw [hEq] at h
  exact h

private theorem interleave_unlinkAt_inside_child {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (dh : DirHandle) (name : EntryName) (isDir : Bool) (s : VfsState)
    (hConfined : ∀ dhPos, lookupDir s dh = some dhPos → outerPos <+: dhPos ++ [name.val]) :
    InsideStep outerPos s ((interleave env vfsDirOps).unlinkAt dh name isDir s).2 := by
  have he := insideStep_env hEnv s
  change InsideStep outerPos s (vfsDirOps.unlinkAt dh name isDir (env s)).2
  rw [vfsDirOps_unlinkAt_def]
  have hLdEq : lookupDir (env s) dh = lookupDir s dh := by simp [lookupDir, he.2.1]
  cases hLd : lookupDir s dh with
  | none => simp [hLdEq, hLd, he]
  | some dhPos =>
    have hPre := hConfined dhPos hLd
    simp only [hLdEq, hLd]
    cases hP : nodeAt (env s).tree dhPos with
    | none => exact he
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => exact he
      | dir parMode =>
        dsimp only
        split
        · exact he
        · cases hC : nodeAt (env s).tree (dhPos ++ [name.val]) with
          | none => exact he
          | some cnode =>
            rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
            cases cnode with
            | dir _ =>
              dsimp only
              split
              · exact he
              · split
                · exact he
                · exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet_target hPre ⟨parMode, ch, hDir⟩ rfl),
                    he.2.1, he.2.2⟩
            | file _ _ | symlink _ _ =>
              dsimp only
              split
              · exact he
              · exact ⟨SameOutside_trans he.1 (SameOutside_of_vfsTreeSet_target hPre ⟨parMode, ch, hDir⟩ rfl),
                  he.2.1, he.2.2⟩

private theorem mkdirWalkM_owned {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (baseDirs : List (Nat × List String))
    (segs : List EntryName) (leafAct : DirHandle → StateM VfsState (Except FsError Unit))
    (isRoot : Bool) (cur : DirHandle) (curPos : List String) (s0 : VfsState)
    (hPreCur : pos <+: curPos) (hOwn : OwnedHandle baseDirs isRoot cur curPos s0)
    (hAct : ∀ isR c cp s, OwnedHandle baseDirs isR c cp s → pos <+: cp → InsideStep pos s (leafAct c s).2) :
    match (Internal.mkdirWalkM (interleave env vfsDirOps) isRoot cur segs leafAct) s0 with
    | (_, sOut) => SameOutside pos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = s0.locks := by
  revert hPreCur hOwn hAct
  induction segs generalizing isRoot cur curPos s0 with
  | nil =>
    intro hPreCur hOwn hAct
    dsimp only [Internal.mkdirWalkM]
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hStep := hAct false cur curPos s0 hOwn hPreCur
      rcases hOwn with ⟨hPos, hLt, hDirs⟩
      have hBr := bracketCloseDirM_owned hEnv cur curPos baseDirs hPos hLt (leafAct cur) hDirs hStep
      cases hRes : (Internal.bracketCloseDirM (interleave env vfsDirOps) cur (leafAct cur)) s0 with
      | mk _ _ =>
        rw [hRes] at hBr
        exact hBr.2
    · simp only [↓reduceIte]
      have hStep := hAct true cur curPos s0 hOwn hPreCur
      rcases hOwn with ⟨hDirs, _⟩
      exact ⟨hStep.1, hStep.2.1.trans hDirs, hStep.2.2⟩
  | cons seg rest ih =>
    intro hPreCur hOwn hAct
    let ops := interleave env vfsDirOps
    let step : StateM VfsState (Except FsError DirHandle) := do
      match ← ops.openDirAt cur seg with
      | .ok nextDh => pure (.ok nextDh)
      | .error e =>
        if e.kind == .notFound then
          match ← ops.createDirAt cur seg with
          | .ok () => ops.openDirAt cur seg
          | .error ce =>
            if ce.kind == .alreadyExists then ops.openDirAt cur seg
            else pure (.error ce)
        else
          pure (.error e)
    have hOpenErr : ∀ sX (e : FsError) (s1 : VfsState),
        InsideStep pos s0 sX → sX.openDirs = s0.openDirs →
        ops.openDirAt cur seg sX = (.error e, s1) →
        InsideStep pos s0 s1 := by
      intro sX e s1 hIX _ hErr
      change vfsDirOps.openDirAt cur seg (env sX) = (.error e, s1) at hErr
      rw [vfsDirOps_openDirAt_err cur seg (env sX) e s1 hErr]
      exact InsideStep_trans hIX (insideStep_env hEnv sX)
    have hOpenOk : ∀ sX (nextDh : DirHandle) (s1 : VfsState),
        InsideStep pos s0 sX → sX.openDirs = s0.openDirs → lookupDir sX cur = some curPos →
        ops.openDirAt cur seg sX = (.ok nextDh, s1) →
        0 < nextDh.handleId ∧
          (∀ q ∈ s0.openDirs, q.1 < nextDh.handleId) ∧
          SameOutside pos s0 s1 ∧ s1.openDirs = (nextDh.handleId, curPos ++ [seg.val]) :: s0.openDirs ∧ s1.locks = s0.locks := by
      intro sX nextDh s1 hIX _ hLdX hOk
      change vfsDirOps.openDirAt cur seg (env sX) = (.ok nextDh, s1) at hOk
      rcases vfsDirOps_openDirAt_ok cur seg (env sX) nextDh s1 hOk with
        ⟨hNextPos, _, hNextGt, _, _, _, hLd, _, _, _, _, _, hSt1⟩
      have heX := insideStep_env hEnv sX
      have hLdEq : lookupDir (env sX) cur = lookupDir sX cur := by simp [lookupDir, heX.2.1]
      rw [hLdEq, hLdX] at hLd
      cases hLd
      rw [hSt1]
      have hIXE := InsideStep_trans hIX heX
      exact ⟨hNextPos, fun q hq => hNextGt q (hIXE.2.1 ▸ hq), hIXE.1, by simp [hIXE.2.1], hIXE.2.2⟩
    have hStepProof := step_openDirAt_owned hEnv baseDirs isRoot cur curPos seg s0 hOwn step
      (fun e s1 hs => by
        dsimp only [step, bind, StateT.bind, pure, StateT.pure] at hs
        cases hO1 : ops.openDirAt cur seg s0 with
        | mk r1 s1' =>
          rw [hO1] at hs
          dsimp only at hs
          cases r1 with
          | ok _ => cases hs
          | error e1 =>
            have hI1 := hOpenErr s0 e1 s1' (InsideStep_refl pos s0) rfl hO1
            by_cases hNf : (e1.kind == .notFound) = true
            · simp only [hNf, ↓reduceIte, StateT.bind] at hs
              have hC := interleave_createDirAt_inside hEnv cur seg s1' fun p hp => by
                have hEq : lookupDir s1' cur = lookupDir s0 cur := by simp [lookupDir, hI1.2.1]
                rw [hEq, ownedHandle_lookup hOwn] at hp
                cases hp
                exact hPreCur
              cases hCr : ops.createDirAt cur seg s1' with
              | mk rC sC =>
                rw [hCr] at hC hs
                dsimp only at hC hs
                have hI2 := InsideStep_trans hI1 hC
                cases rC with
                | ok _ => exact hOpenErr sC e s1 hI2 hI2.2.1 hs
                | error ce =>
                  dsimp only [bind, StateT.bind, Bind.bind, pure, StateT.pure, Pure.pure] at hs
                  by_cases hAe : (ce.kind == .alreadyExists) = true
                  · simp only [hAe, ↓reduceIte] at hs
                    exact hOpenErr sC e s1 hI2 hI2.2.1 hs
                  · simp only [hAe, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hs
                    cases hs
                    exact hI2
            · simp only [hNf, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hs
              cases hs
              exact hI1)
      (fun nextDh s1 hs => by
        dsimp only [step, bind, StateT.bind, pure, StateT.pure] at hs
        cases hO1 : ops.openDirAt cur seg s0 with
        | mk r1 s1' =>
          rw [hO1] at hs
          dsimp only at hs
          cases r1 with
          | ok _ =>
            cases hs
            exact hOpenOk s0 nextDh s1 (InsideStep_refl pos s0) rfl (ownedHandle_lookup hOwn) hO1
          | error e1 =>
            have hI1 := hOpenErr s0 e1 s1' (InsideStep_refl pos s0) rfl hO1
            by_cases hNf : (e1.kind == .notFound) = true
            · simp only [hNf, ↓reduceIte, StateT.bind] at hs
              have hC := interleave_createDirAt_inside hEnv cur seg s1' fun p hp => by
                have hEq : lookupDir s1' cur = lookupDir s0 cur := by simp [lookupDir, hI1.2.1]
                rw [hEq, ownedHandle_lookup hOwn] at hp
                cases hp
                exact hPreCur
              cases hCr : ops.createDirAt cur seg s1' with
              | mk rC sC =>
                rw [hCr] at hC hs
                dsimp only at hC hs
                have hI2 := InsideStep_trans hI1 hC
                have hLdC : lookupDir sC cur = some curPos := by
                  have hEq : lookupDir sC cur = lookupDir s0 cur := by simp [lookupDir, hI2.2.1]
                  exact hEq.trans (ownedHandle_lookup hOwn)
                cases rC with
                | ok _ => exact hOpenOk sC nextDh s1 hI2 hI2.2.1 hLdC hs
                | error ce =>
                  dsimp only [bind, StateT.bind, Bind.bind, pure, StateT.pure, Pure.pure] at hs
                  by_cases hAe : (ce.kind == .alreadyExists) = true
                  · simp only [hAe, ↓reduceIte] at hs
                    exact hOpenOk sC nextDh s1 hI2 hI2.2.1 hLdC hs
                  · simp only [hAe, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hs
                    cases hs
            · simp only [hNf, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hs
              cases hs)
    have hNextPre : pos <+: curPos ++ [seg.val] := List.IsPrefix.trans hPreCur (List.prefix_append _ _)
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte] at hStepProof
      dsimp only [Internal.mkdirWalkM, bind, StateT.bind, pure, StateT.pure, Bool.false_eq_true, ↓reduceIte]
      change match ((Internal.bracketCloseDirM ops cur step >>= fun r =>
          match r with | .error e => StateT.pure (.error e) | .ok nextDh => Internal.mkdirWalkM ops false nextDh rest leafAct) s0) with
        | (_, sOut) => SameOutside pos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = s0.locks
      dsimp only [bind, StateT.bind]
      cases hRun : (Internal.bracketCloseDirM ops cur step) s0 with
      | mk r s1 =>
        rw [hRun] at hStepProof
        dsimp only at hStepProof ⊢
        cases r with
        | error _ => exact hStepProof
        | ok nextDh =>
          rcases hStepProof with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hNextPre hOwn1 hAct
          dsimp only [ops]
          cases hWalk : (Internal.mkdirWalkM (interleave env vfsDirOps) false nextDh rest leafAct) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩
    · simp only [↓reduceIte] at hStepProof
      dsimp only [Internal.mkdirWalkM, bind, StateT.bind, pure, StateT.pure, ↓reduceIte]
      change match ((step >>= fun r =>
          match r with | .error e => StateT.pure (.error e) | .ok nextDh => Internal.mkdirWalkM ops false nextDh rest leafAct) s0) with
        | (_, sOut) => SameOutside pos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = s0.locks
      dsimp only [bind, StateT.bind]
      cases hRun : step s0 with
      | mk r s1 =>
        rw [hRun] at hStepProof
        dsimp only at hStepProof ⊢
        cases r with
        | error _ => exact hStepProof
        | ok nextDh =>
          rcases hStepProof with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hNextPre hOwn1 hAct
          dsimp only [ops]
          cases hWalk : (Internal.mkdirWalkM (interleave env vfsDirOps) false nextDh rest leafAct) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩

private theorem mkdirWalkM_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (dhPos : List String)
    (segs : List EntryName) (leafAct : DirHandle → StateM VfsState (Except FsError Unit))
    (s0 : VfsState) (hPre : pos <+: dhPos) (hLd : lookupDir s0 dh = some dhPos)
    (hAct : ∀ isR c cp s, OwnedHandle s0.openDirs isR c cp s → pos <+: cp → InsideStep pos s (leafAct c s).2) :
    InsideStep pos s0 ((Internal.mkdirWalkM (interleave env vfsDirOps) true dh segs leafAct) s0).2 :=
  mkdirWalkM_owned hEnv s0.openDirs segs leafAct true dh dhPos s0 hPre ⟨rfl, hLd⟩ hAct

private theorem atomicWriteAtAuxM_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (parDh : DirHandle) (leaf : EntryName) (bytes : ByteArray)
    (attempts : Nat) (s0 : VfsState)
    (hConfined : ∀ p, lookupDir s0 parDh = some p → pos <+: p) :
    InsideStep pos s0 ((Internal.atomicWriteAtAuxM (interleave env vfsDirOps) parDh leaf bytes attempts) s0).2 := by
  induction attempts generalizing s0 with
  | zero => exact InsideStep_refl pos s0
  | succ k ih =>
    dsimp only [Internal.atomicWriteAtAuxM, bind, StateT.bind, pure, StateT.pure]
    have hFr := interleave_freshTempName_inside hEnv s0
    cases hF : (interleave env vfsDirOps).freshTempName s0 with
    | mk tmp s1 =>
      rw [hF] at hFr
      dsimp only at hFr ⊢
      have hConf1 : ∀ p, lookupDir s1 parDh = some p → pos <+: p := fun p hp => by
        have hEq : lookupDir s1 parDh = lookupDir s0 parDh := by simp [lookupDir, hFr.2.1]
        exact hConfined p (hEq ▸ hp)
      have hCr := interleave_createFileAt_inside hEnv parDh tmp bytes s1 hConf1
      cases hC : (interleave env vfsDirOps).createFileAt parDh tmp bytes s1 with
      | mk rC s2 =>
        rw [hC] at hCr
        dsimp only at hCr ⊢
        have hI2 := InsideStep_trans hFr hCr
        have hConf2 : ∀ p, lookupDir s2 parDh = some p → pos <+: p := fun p hp => by
          have hEq : lookupDir s2 parDh = lookupDir s0 parDh := by simp [lookupDir, hI2.2.1]
          exact hConfined p (hEq ▸ hp)
        cases rC with
        | ok _ =>
          dsimp only [StateT.bind]
          have hRn := interleave_renameAt_inside hEnv parDh tmp parDh leaf s2 hConf2 hConf2
          cases hR : (interleave env vfsDirOps).renameAt parDh tmp parDh leaf s2 with
          | mk rR s3 =>
            rw [hR] at hRn
            dsimp only at hRn ⊢
            have hI3 := InsideStep_trans hI2 hRn
            cases rR with
            | ok _ => exact hI3
            | error _ =>
              have hConf3 : ∀ p, lookupDir s3 parDh = some p → pos <+: p := fun p hp => by
                have hEq : lookupDir s3 parDh = lookupDir s0 parDh := by simp [lookupDir, hI3.2.1]
                exact hConfined p (hEq ▸ hp)
              exact InsideStep_trans hI3 (interleave_unlinkAt_inside hEnv parDh tmp false s3 hConf3)
        | error e =>
          dsimp only
          split
          · exact InsideStep_trans hI2 (ih s2 hConf2)
          · exact hI2

private theorem classifyChildrenM_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dirDh : DirHandle) (items dirsAcc : List EntryName)
    (filesAcc : List String) (s0 : VfsState) :
    InsideStep pos s0 ((Internal.classifyChildrenM (interleave env vfsDirOps) dirDh items dirsAcc filesAcc) s0).2 := by
  induction items generalizing dirsAcc filesAcc s0 with
  | nil => exact InsideStep_refl pos s0
  | cons n rest ih =>
    dsimp only [Internal.classifyChildrenM, bind, StateT.bind, pure, StateT.pure]
    have hL := interleave_lstatAt_inside hEnv dirDh n s0
    cases hLs : (interleave env vfsDirOps).lstatAt dirDh n s0 with
    | mk r s1 =>
      rw [hLs] at hL
      dsimp only at hL ⊢
      cases r with
      | error _ => exact hL
      | ok info =>
        dsimp only
        split
        · exact InsideStep_trans hL (ih (n :: dirsAcc) filesAcc s1)
        · exact InsideStep_trans hL (ih dirsAcc (n.val :: filesAcc) s1)

private theorem walkRecM_and_children_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (rootDh : DirHandle) (fuel : Nat) :
    (∀ (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (s0 : VfsState) (dhPos : List String),
      lookupDir s0 rootDh = some dhPos →
      InsideStep pos s0 ((Internal.walkRecM (interleave env vfsDirOps) rootDh relSegs relLabel acc fuel) s0).2) ∧
    (∀ (dirs : List EntryName) (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (s0 : VfsState) (dhPos : List String),
      lookupDir s0 rootDh = some dhPos →
      InsideStep pos s0 ((Internal.walkChildrenM (interleave env vfsDirOps) rootDh relSegs relLabel fuel acc dirs) s0).2) := by
  induction fuel with
  | zero =>
    refine ⟨fun _ _ _ s0 _ _ => ?_, ?_⟩
    · unfold Internal.walkRecM
      exact InsideStep_refl pos s0
    · intro dirs
      induction dirs with
      | nil =>
        intro _ _ _ s0 _ _
        unfold Internal.walkChildrenM
        exact InsideStep_refl pos s0
      | cons d rest _ =>
        intro relSegs relLabel acc s0 dhPos _
        unfold Internal.walkChildrenM
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        unfold Internal.walkRecM
        exact InsideStep_refl pos s0
  | succ f ih =>
    have hRec : ∀ (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (s0 : VfsState) (dhPos : List String),
        lookupDir s0 rootDh = some dhPos →
        InsideStep pos s0 ((Internal.walkRecM (interleave env vfsDirOps) rootDh relSegs relLabel acc (f + 1)) s0).2 := by
      intro relSegs relLabel acc s0 dhPos hLd
      unfold Internal.walkRecM
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hW : (Internal.walkDescendM (interleave env vfsDirOps) rootDh relSegs _) s0 with
      | mk rW s1 =>
        have hRead : InsideStep pos s0 s1 := insideStep_walkDescend_eq hEnv rootDh dhPos relSegs _ s0 rW s1 hW hLd
          (fun _ dirDh _ sX _ _ => by
            dsimp only [bind, StateT.bind, pure, StateT.pure]
            have hR := interleave_readDirAt_inside hEnv dirDh sX
            cases hRd : (interleave env vfsDirOps).readDirAt dirDh sX with
            | mk r1 s1' =>
              rw [hRd] at hR
              dsimp only at hR ⊢
              cases r1 with
              | error _ => exact hR
              | ok raw => exact InsideStep_trans hR (classifyChildrenM_inside hEnv dirDh (Internal.sortEntryNames raw) [] [] s1'))
        dsimp only
        cases rW with
        | error _ => exact hRead
        | ok pair =>
          dsimp only
          have hLd1 : lookupDir s1 rootDh = some dhPos := by
            have hEq : lookupDir s1 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hRead.2.1]
            exact hEq.trans hLd
          cases hCh : (Internal.walkChildrenM (interleave env vfsDirOps) rootDh relSegs relLabel f
              (acc.push { root := relLabel, dirs := (pair.1.map (·.val)).toArray, files := pair.2.toArray }) pair.1) s1 with
          | mk _ s2 =>
            exact InsideStep_trans hRead (by
              have hStep := ih.2 pair.1 relSegs relLabel
                (acc.push { root := relLabel, dirs := (pair.1.map (·.val)).toArray, files := pair.2.toArray }) s1 dhPos hLd1
              rw [hCh] at hStep
              exact hStep)
    refine ⟨hRec, ?_⟩
    intro dirs
    induction dirs with
    | nil =>
      intro _ _ _ s0 _ _
      unfold Internal.walkChildrenM
      exact InsideStep_refl pos s0
    | cons d rest ihD =>
      intro relSegs relLabel acc s0 dhPos hLd
      unfold Internal.walkChildrenM
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      have hStep := hRec (relSegs ++ [d]) (if relLabel == "." then d.val else relLabel ++ "/" ++ d.val) acc s0 dhPos hLd
      cases hW : (Internal.walkRecM (interleave env vfsDirOps) rootDh (relSegs ++ [d])
          (if relLabel == "." then d.val else relLabel ++ "/" ++ d.val) acc (f + 1)) s0 with
      | mk rW s1 =>
        rw [hW] at hStep
        dsimp only at hStep ⊢
        cases rW with
        | error _ => exact hStep
        | ok acc' =>
          dsimp only
          have hLd1 : lookupDir s1 rootDh = some dhPos := by
            have hEq : lookupDir s1 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hStep.2.1]
            exact hEq.trans hLd
          cases hTail : (Internal.walkChildrenM (interleave env vfsDirOps) rootDh relSegs relLabel (f + 1) acc' rest) s1 with
          | mk _ s2 =>
            have hRest := ihD relSegs relLabel acc' s1 dhPos hLd1
            rw [hTail] at hRest
            exact InsideStep_trans hStep hRest

private theorem rmtreeNonDirPrefixM_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dirDh : DirHandle) (items : List EntryName) (s0 : VfsState)
    (hConfined : ∀ p, lookupDir s0 dirDh = some p → pos <+: p) :
    InsideStep pos s0 ((Internal.rmtreeNonDirPrefixM (interleave env vfsDirOps) dirDh items) s0).2 := by
  induction items generalizing s0 with
  | nil => exact InsideStep_refl pos s0
  | cons c rest ih =>
    dsimp only [Internal.rmtreeNonDirPrefixM, bind, StateT.bind, pure, StateT.pure]
    have hL := interleave_lstatAt_inside hEnv dirDh c s0
    cases hLs : (interleave env vfsDirOps).lstatAt dirDh c s0 with
    | mk r s1 =>
      rw [hLs] at hL
      dsimp only at hL ⊢
      have hConf1 : ∀ p, lookupDir s1 dirDh = some p → pos <+: p := fun p hp => by
        have hEq : lookupDir s1 dirDh = lookupDir s0 dirDh := by simp [lookupDir, hL.2.1]
        exact hConfined p (hEq ▸ hp)
      cases r with
      | error e =>
        dsimp only
        split
        · exact InsideStep_trans hL (ih s1 hConf1)
        · exact hL
      | ok info =>
        dsimp only
        split
        · exact hL
        · dsimp only [StateT.bind]
          have hU := interleave_unlinkAt_inside hEnv dirDh c false s1 hConf1
          cases hUl : (interleave env vfsDirOps).unlinkAt dirDh c false s1 with
          | mk rU s2 =>
            rw [hUl] at hU
            dsimp only at hU ⊢
            have hI2 := InsideStep_trans hL hU
            have hConf2 : ∀ p, lookupDir s2 dirDh = some p → pos <+: p := fun p hp => by
              have hEq : lookupDir s2 dirDh = lookupDir s0 dirDh := by simp [lookupDir, hI2.2.1]
              exact hConfined p (hEq ▸ hp)
            cases rU with
            | ok _ => exact InsideStep_trans hI2 (ih s2 hConf2)
            | error e =>
              dsimp only [bind, StateT.bind]
              split
              · exact InsideStep_trans hI2 (ih s2 hConf2)
              · exact hI2

private theorem rmtreeProcessM_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (rootDh : DirHandle) (dirSegs : List EntryName)
    (subDirFn : EntryName → StateM VfsState (Except FsError Unit))
    (hSubFn : ∀ subDir s, (∃ p, lookupDir s rootDh = some p ∧ pos <+: p ++ dirSegs.map (·.val)) → InsideStep pos s (subDirFn subDir s).2)
    (steps : Nat) (items : List EntryName) (s0 : VfsState) (dhPos : List String)
    (hPre : pos <+: dhPos ++ dirSegs.map (·.val)) (hLd : lookupDir s0 rootDh = some dhPos) :
    InsideStep pos s0 ((Internal.rmtreeProcessM (interleave env vfsDirOps) rootDh dirSegs subDirFn steps items) s0).2 := by
  induction steps generalizing items s0 with
  | zero => cases items <;> exact InsideStep_refl pos s0
  | succ k ih =>
    cases items with
    | nil => exact InsideStep_refl pos s0
    | cons c rest =>
      dsimp only [Internal.rmtreeProcessM, bind, StateT.bind, pure, StateT.pure]
      let batchAct : DirHandle → StateM VfsState (Except FsError (Option (EntryName × List EntryName))) :=
        fun dirDh => Internal.rmtreeNonDirPrefixM (interleave env vfsDirOps) dirDh (c :: rest)
      have hBatch := walkDescendM_inside hEnv rootDh dhPos dirSegs batchAct
        s0 hLd (fun _ dirDh cp sX hOwn hCp =>
          rmtreeNonDirPrefixM_inside hEnv dirDh (c :: rest) sX fun p hp => by
            rw [ownedHandle_lookup hOwn] at hp
            cases hp
            exact hCp ▸ hPre)
      cases hB : (Internal.walkDescendM (interleave env vfsDirOps) rootDh dirSegs batchAct) s0 with
      | mk rB s1 =>
        rw [hB] at hBatch
        dsimp only at hBatch ⊢
        cases rB with
        | error _ => exact hBatch
        | ok opt =>
          cases opt with
          | none => exact hBatch
          | some pair =>
            dsimp only [StateT.bind]
            have hLd1 : lookupDir s1 rootDh = some dhPos := by
              have hEq : lookupDir s1 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hBatch.2.1]
              exact hEq.trans hLd
            have hSub := hSubFn pair.1 s1 ⟨dhPos, hLd1, hPre⟩
            cases hS : subDirFn pair.1 s1 with
            | mk rS s2 =>
              rw [hS] at hSub
              dsimp only at hSub ⊢
              have hI2 := InsideStep_trans hBatch hSub
              cases rS with
              | error _ => exact hI2
              | ok _ =>
                have hLd2 : lookupDir s2 rootDh = some dhPos := by
                  have hEq : lookupDir s2 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hI2.2.1]
                  exact hEq.trans hLd
                exact InsideStep_trans hI2 (ih pair.2 s2 hLd2)

private theorem rmtreeDirAtM_inside {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (rootDh : DirHandle) (fuel : Nat) :
    ∀ (parSegs : List EntryName) (leaf : EntryName) (s0 : VfsState) (dhPos : List String),
      outerPos <+: dhPos ++ parSegs.map (·.val) ++ [leaf.val] →
      lookupDir s0 rootDh = some dhPos →
      InsideStep outerPos s0 ((Internal.rmtreeDirAtM (interleave env vfsDirOps) rootDh parSegs leaf fuel) s0).2 := by
  induction fuel with
  | zero => intro _ _ s0 _ _ _; exact InsideStep_refl outerPos s0
  | succ f ih =>
    intro parSegs leaf s0 dhPos hPre hLd
    dsimp only [Internal.rmtreeDirAtM, bind, StateT.bind, pure, StateT.pure]
    have hPreDir : outerPos <+: dhPos ++ (parSegs ++ [leaf]).map (·.val) := by
      simpa [List.map_append, List.append_assoc] using hPre
    let readAct : DirHandle → StateM VfsState (Except FsError (Array EntryName)) :=
      fun dirDh => (interleave env vfsDirOps).readDirAt dirDh
    have hRead := walkDescendM_inside hEnv rootDh dhPos (parSegs ++ [leaf]) readAct
      s0 hLd (fun _ dirDh _ sX _ _ => interleave_readDirAt_inside hEnv dirDh sX)
    cases hR : (Internal.walkDescendM (interleave env vfsDirOps) rootDh (parSegs ++ [leaf]) readAct) s0 with
    | mk rRead s1 =>
      rw [hR] at hRead
      dsimp only at hRead ⊢
      cases rRead with
      | error _ => exact hRead
      | ok rawNames =>
        dsimp only [StateT.bind]
        have hLd1 : lookupDir s1 rootDh = some dhPos := by
          have hEq : lookupDir s1 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hRead.2.1]
          exact hEq.trans hLd
        have hProc := rmtreeProcessM_inside hEnv rootDh (parSegs ++ [leaf])
          (fun subDir => Internal.rmtreeDirAtM (interleave env vfsDirOps) rootDh (parSegs ++ [leaf]) subDir f)
          (fun subDir sX ⟨p, hLdX, hPreX⟩ => ih (parSegs ++ [leaf]) subDir sX p
            (List.IsPrefix.trans hPreX (List.prefix_append _ _)) hLdX)
          (Internal.sortEntryNames rawNames).length (Internal.sortEntryNames rawNames) s1 dhPos hPreDir hLd1
        cases hP : (Internal.rmtreeProcessM (interleave env vfsDirOps) rootDh (parSegs ++ [leaf])
            (fun subDir => Internal.rmtreeDirAtM (interleave env vfsDirOps) rootDh (parSegs ++ [leaf]) subDir f)
            (Internal.sortEntryNames rawNames).length (Internal.sortEntryNames rawNames)) s1 with
        | mk rProc s2 =>
          rw [hP] at hProc
          dsimp only at hProc ⊢
          have hI2 := InsideStep_trans hRead hProc
          cases rProc with
          | error _ => exact hI2
          | ok _ =>
            have hLd2 : lookupDir s2 rootDh = some dhPos := by
              have hEq : lookupDir s2 rootDh = lookupDir s0 rootDh := by simp [lookupDir, hI2.2.1]
              exact hEq.trans hLd
            let unlAct : DirHandle → StateM VfsState (Except FsError Unit) :=
              fun parDh => (interleave env vfsDirOps).unlinkAt parDh leaf true
            have hUnl := walkDescendM_inside hEnv rootDh dhPos parSegs unlAct
              s2 hLd2 (fun _ parDh cp sX hOwn hCpEq =>
                interleave_unlinkAt_inside_child hEnv parDh leaf true sX fun p hp => by
                  rw [ownedHandle_lookup hOwn] at hp
                  cases hp
                  simpa [hCpEq] using hPre)
            exact InsideStep_trans hI2 hUnl

private noncomputable def openDirTpl (st : VfsState) (root : String) (d : Nat) :
    Except FsError DirHandle × VfsState :=
  if !isValidRawPath root then
    (.error { kind := .invalidInput, path := some root, message := s!"invalid path: {root}" }, st)
  else
    let abs := vfsAbsNorm st.cwd root
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => (.error e, st)
    | .ok (canon, .dir mode) =>
      if (mode / 256) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" }, st)
      else
        let id := max d st.nextDirId + 1
        (.ok { handleId := id, rootPath := root },
          { st with openDirs := (id, vfsSplitSegs canon) :: st.openDirs, nextDirId := id + 1 })
    | .ok (_, _) =>
      (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st)

/-- On error, `vfsDirOps.openDir` leaves `VfsState` unchanged. -/
theorem vfsDirOps_openDir_err (root : String) (st : VfsState) (e : FsError) (st' : VfsState)
    (h : vfsDirOps.openDir root st = (.error e, st')) : st' = st := by
  have hPair : ∃ d, vfsDirOps.openDir root st = openDirTpl st root d := ⟨_, rfl⟩
  rcases hPair with ⟨d, hEq⟩
  rw [hEq] at h
  dsimp only [openDirTpl] at h
  repeat (first | split at h | cases h) <;> try rfl

private theorem openDirTpl_ok_aux (st : VfsState) (root : String) (d : Nat) (dh : DirHandle) (st' : VfsState)
    (hValid : isValidRawPath root = true)
    (res : Except FsError (String × VfsNode))
    (hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd root)) true 1024 = res)
    (h : (match res with
      | .error e => ((.error e : Except FsError DirHandle), st)
      | .ok (canon, .dir mode) =>
        if (mode / 256) % 2 == 0 then
          ((.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" } : Except FsError DirHandle), st)
        else
          let id := max d st.nextDirId + 1
          ((.ok { handleId := id, rootPath := root } : Except FsError DirHandle),
            { st with openDirs := (id, vfsSplitSegs canon) :: st.openDirs, nextDirId := id + 1 })
      | .ok (_, _) =>
        ((.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" } : Except FsError DirHandle), st)) = (.ok dh, st')) :
    ∃ canon m,
      vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd root)) true 1024 = .ok (canon, .dir m) ∧
      (m / 256) % 2 ≠ 0 ∧
      dh.handleId = max d st.nextDirId + 1 ∧
      st' = { st with openDirs := (dh.handleId, vfsSplitSegs canon) :: st.openDirs, nextDirId := dh.handleId + 1 } := by
  have _ := hValid
  cases res with
  | error _ => cases h
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    cases nd with
    | file _ _ | symlink _ _ => cases h
    | dir m =>
      dsimp only at h
      by_cases hm : (m / 256) % 2 == 0
      · simp only [hm, ↓reduceIte] at h; cases h
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        cases h
        exact ⟨canon, m, hRes, fun hZ => hm (beq_iff_eq.mpr hZ), rfl, rfl⟩

/-- Successful `vfsDirOps.openDir` exposes the resolved directory path and fresh handle metadata. -/
theorem vfsDirOps_openDir_ok_resolved (root : String) (st : VfsState) (dh : DirHandle) (st' : VfsState)
    (h : vfsDirOps.openDir root st = (.ok dh, st')) :
    0 < dh.handleId ∧
      st.nextDirId < dh.handleId ∧
      (∀ p ∈ st.openDirs, p.1 < dh.handleId) ∧
      ∃ canon m,
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd root)) true 1024 = .ok (canon, .dir m) ∧
        (m / 256) % 2 ≠ 0 ∧
        st' = { st with openDirs := (dh.handleId, vfsSplitSegs canon) :: st.openDirs, nextDirId := dh.handleId + 1 } := by
  have hOk := vfsDirOps_openDir_ok root st dh st' h
  have hPair : ∃ d, vfsDirOps.openDir root st = openDirTpl st root d := ⟨_, rfl⟩
  rcases hPair with ⟨d, hEq⟩
  rw [hEq] at h
  dsimp only [openDirTpl] at h
  by_cases hv : isValidRawPath root = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rcases openDirTpl_ok_aux st root d dh st' hv _ rfl h with ⟨canon, m, hRes, hm, _, hSt⟩
    exact ⟨hOk.1, hOk.2.1, hOk.2.2.1, canon, m, hRes, hm, hSt⟩
  · have hNot : (!isValidRawPath root) = true := by simp [hv]
    simp only [hNot, ↓reduceIte] at h
    cases h

private noncomputable def acqLockTpl (dh : DirHandle) (name : EntryName) (mode : LockMode)
    (createIfMissing _nonBlocking : Bool) (st : VfsState) (d : Nat) :
    Except FsError LockHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (mInvalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let leafPos := pos ++ [name.val]
        let lockPath := pathOfSegs leafPos
        let allocOk (stCur : VfsState) : Except FsError LockHandle × VfsState :=
          let id := max d stCur.nextLockId + 1
          let handle : LockHandle := { handleId := id, path := lockPath, mode := mode }
          (.ok handle, { stCur with locks := (id, lockPath, mode) :: stCur.locks, nextLockId := id })
        match nodeAt st.tree leafPos with
        | some (.file _ _) =>
          if hasLockConflict st.locks lockPath mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            allocOk st
        | some (.dir _) => (.error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }, st)
        | some (.symlink _ _) => (.error { kind := .invalidInput, path := some name.val, message := s!"symlink rejected for lock: {name.val}" }, st)
        | none =>
          if !createIfMissing then
            (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
          else if (parMode / 128) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else if hasLockConflict st.locks lockPath mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            let st1 := { st with
              tree := vfsTreeSet st.tree leafPos (some (.file ByteArray.empty 0o644))
              keys := lockPath :: st.keys }
            allocOk st1
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- On error, `vfsDirOps.acquireLockAt` leaves `VfsState` unchanged. -/
theorem vfsDirOps_acquireLockAt_err (dh : DirHandle) (name : EntryName)
    (mode : LockMode) (createIfMissing nonBlocking : Bool) (st : VfsState)
    (e : FsError) (st' : VfsState)
    (h : vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st = (.error e, st')) :
    st' = st := by
  have hPair : ∃ d, vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st =
      acqLockTpl dh name mode createIfMissing nonBlocking st d := ⟨_, rfl⟩
  rcases hPair with ⟨d, hEq⟩
  rw [hEq] at h
  dsimp only [acqLockTpl] at h
  repeat (first | split at h | cases h) <;> try rfl

private noncomputable def openDirAtTpl (dh : DirHandle) (name : EntryName) (st : VfsState) (d : Nat) :
    Except FsError DirHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (mInvalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | none => (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.symlink _ _) => (.error { kind := .invalidInput, path := some name.val, message := s!"symlink refused in subtree traversal: {name.val}" }, st)
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let id := max d st.nextDirId + 1
            let childPath := pathOfSegs childPos
            (.ok { handleId := id, rootPath := childPath },
              { st with openDirs := (id, childPos) :: st.openDirs, nextDirId := id + 1 })
        | some _ => (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- When `lookupDir st dh = none`, `vfsDirOps.openDirAt` refuses immediately with `mInvalidDirHandleErr dh`. -/
theorem vfsDirOps_openDirAt_none (st : VfsState) (dh : DirHandle) (name : EntryName)
    (hNone : lookupDir st dh = none) :
    vfsDirOps.openDirAt dh name st = (.error (mInvalidDirHandleErr dh), st) := by
  have hPair : ∃ d, vfsDirOps.openDirAt dh name st = openDirAtTpl dh name st d := ⟨_, rfl⟩
  rcases hPair with ⟨d, hEq⟩
  rw [hEq]
  simp [openDirAtTpl, hNone]

private theorem walkDescendAuxM_acquireLock {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (baseDirs : List (Nat × List String))
    (segs : List EntryName) (leaf : EntryName) (mode : LockMode) (createIfMissing nonBlock : Bool)
    (isRoot : Bool) (cur : DirHandle) (curPos : List String) (s0 : VfsState)
    (hOwn : OwnedHandle baseDirs isRoot cur curPos s0)
    (hPreLeaf : outerPos <+: curPos ++ segs.map (·.val) ++ [leaf.val]) :
    match (Internal.walkDescendAuxM (interleave env vfsDirOps) isRoot cur segs
        (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh leaf mode createIfMissing nonBlock)) s0 with
    | (.error _, sOut) => SameOutside outerPos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = s0.locks
    | (.ok lh, sOut) =>
      0 < lh.handleId ∧ (∀ l ∈ s0.locks, l.1 < lh.handleId) ∧
        SameOutside outerPos s0 sOut ∧ sOut.openDirs = baseDirs ∧ sOut.locks = (lh.handleId, lh.path, mode) :: s0.locks := by
  revert isRoot cur curPos s0
  induction segs with
  | nil =>
    intro isRoot cur curPos s0 hOwn hPreLeaf
    dsimp only [Internal.walkDescendAuxM]
    have he := insideStep_env hEnv s0
    cases hAcq : vfsDirOps.acquireLockAt cur leaf mode createIfMissing nonBlock (env s0) with
    | mk rAcq s1 =>
      have hAcqI : (interleave env vfsDirOps).acquireLockAt cur leaf mode createIfMissing nonBlock s0 = (rAcq, s1) := hAcq
      have hCurLd := ownedHandle_lookup hOwn
      cases isRoot
      · simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [Internal.bracketCloseDirM, bind, StateT.bind, pure, StateT.pure]
        rw [tryFinally_stateM_run, hAcqI]
        dsimp only
        rcases hOwn with ⟨hPos, hLt, hDirs⟩
        cases rAcq with
        | error e =>
          have hS1 := vfsDirOps_acquireLockAt_err cur leaf mode createIfMissing nonBlock (env s0) e s1 hAcq
          rw [hS1]
          have hClose := interleave_closeDir_owned hEnv cur curPos baseDirs hPos hLt (he.2.1.trans hDirs)
          cases hCl : (interleave env vfsDirOps).closeDir cur (env s0) with
          | mk _ s2 =>
            rw [hCl] at hClose
            exact ⟨SameOutside_trans he.1 hClose.1, hClose.2.1, hClose.2.2.trans he.2.2⟩
        | ok lh =>
          rcases vfsDirOps_acquireLockAt_ok cur leaf mode createIfMissing nonBlock (env s0) lh s1 hAcq with
            ⟨hLhPos, _, hLhLt, pAcq, hLdAcq, hOutNodes, hDirs1, hLocks1⟩
          have hLdEq : lookupDir (env s0) cur = lookupDir s0 cur := by simp [lookupDir, he.2.1]
          rw [hLdEq, hCurLd] at hLdAcq
          cases hLdAcq
          have hOut1 : SameOutside outerPos (env s0) s1 := fun p hp =>
            hOutNodes p (fun h => hp (List.IsPrefix.trans (by simpa using hPreLeaf) h))
          have hClose := interleave_closeDir_owned hEnv cur curPos baseDirs hPos hLt ((hDirs1.trans he.2.1).trans hDirs)
          cases hCl : (interleave env vfsDirOps).closeDir cur s1 with
          | mk _ s2 =>
            rw [hCl] at hClose
            exact ⟨hLhPos, fun l hl => hLhLt l (he.2.2 ▸ hl),
              SameOutside_trans (SameOutside_trans he.1 hOut1) hClose.1,
              hClose.2.1, hClose.2.2.trans (hLocks1.trans (congrArg _ he.2.2))⟩
      · simp only [↓reduceIte]
        rw [hAcqI]
        rcases hOwn with ⟨hDirs, _⟩
        cases rAcq with
        | error e =>
          have hS1 := vfsDirOps_acquireLockAt_err cur leaf mode createIfMissing nonBlock (env s0) e s1 hAcq
          rw [hS1]
          exact ⟨he.1, he.2.1.trans hDirs, he.2.2⟩
        | ok lh =>
          rcases vfsDirOps_acquireLockAt_ok cur leaf mode createIfMissing nonBlock (env s0) lh s1 hAcq with
            ⟨hLhPos, _, hLhLt, pAcq, hLdAcq, hOutNodes, hDirs1, hLocks1⟩
          have hLdEq : lookupDir (env s0) cur = lookupDir s0 cur := by simp [lookupDir, he.2.1]
          rw [hLdEq, hCurLd] at hLdAcq
          cases hLdAcq
          have hOut1 : SameOutside outerPos (env s0) s1 := fun p hp =>
            hOutNodes p (fun h => hp (List.IsPrefix.trans (by simpa using hPreLeaf) h))
          exact ⟨hLhPos, fun l hl => hLhLt l (he.2.2 ▸ hl),
            SameOutside_trans he.1 hOut1, (hDirs1.trans he.2.1).trans hDirs,
            hLocks1.trans (congrArg _ he.2.2)⟩
  | cons seg rest ih =>
    intro isRoot cur curPos s0 hOwn hPreLeaf
    have hOpen := step_openDirAt_owned hEnv baseDirs isRoot cur curPos seg s0 hOwn
      ((interleave env vfsDirOps).openDirAt cur seg)
      (fun e s1 hErr => by
        change (vfsDirOps.openDirAt cur seg (env s0)) = (.error e, s1) at hErr
        rw [vfsDirOps_openDirAt_err cur seg (env s0) e s1 hErr]
        exact insideStep_env hEnv s0)
      (fun nextDh s1 hOk => by
        change (vfsDirOps.openDirAt cur seg (env s0)) = (.ok nextDh, s1) at hOk
        rcases vfsDirOps_openDirAt_ok cur seg (env s0) nextDh s1 hOk with
          ⟨hNextPos, _, hNextGt, _, _, _, hLd, _, _, _, _, _, hSt1⟩
        have he := insideStep_env hEnv s0
        have hLdEq : lookupDir (env s0) cur = lookupDir s0 cur := by simp [lookupDir, he.2.1]
        rw [hLdEq, ownedHandle_lookup hOwn] at hLd
        cases hLd
        rw [hSt1]
        exact ⟨hNextPos, fun q hq => hNextGt q (he.2.1 ▸ hq), he.1, by simp [he.2.1], he.2.2⟩)
    cases isRoot
    · simp only [Bool.false_eq_true, ↓reduceIte] at hOpen
      unfold Internal.walkDescendAuxM
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hStep : (Internal.bracketCloseDirM (interleave env vfsDirOps) cur ((interleave env vfsDirOps).openDirAt cur seg)) s0 with
      | mk r s1 =>
        rw [hStep] at hOpen
        cases r with
        | error e => exact hOpen
        | ok nextDh =>
          dsimp only
          rcases hOpen with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hOwn1
            (by simpa [List.append_assoc] using hPreLeaf)
          cases hWalk : (Internal.walkDescendAuxM (interleave env vfsDirOps) false nextDh rest
              (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh leaf mode createIfMissing nonBlock)) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            cases r2 with
            | error _ => exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩
            | ok lh =>
              exact ⟨ihOut.1, fun l hl => ihOut.2.1 l (hLocks1 ▸ hl),
                SameOutside_trans hOut1 ihOut.2.2.1, ihOut.2.2.2.1,
                ihOut.2.2.2.2.trans (congrArg _ hLocks1)⟩
    · simp only [↓reduceIte] at hOpen
      unfold Internal.walkDescendAuxM
      simp only [↓reduceIte]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hStep : ((interleave env vfsDirOps).openDirAt cur seg) s0 with
      | mk r s1 =>
        rw [hStep] at hOpen
        cases r with
        | error e => exact hOpen
        | ok nextDh =>
          dsimp only
          rcases hOpen with ⟨hOut1, hLocks1, hOwn1⟩
          have ihOut := ih false nextDh (curPos ++ [seg.val]) s1 hOwn1
            (by simpa [List.append_assoc] using hPreLeaf)
          cases hWalk : (Internal.walkDescendAuxM (interleave env vfsDirOps) false nextDh rest
              (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh leaf mode createIfMissing nonBlock)) s1 with
          | mk r2 s2 =>
            rw [hWalk] at ihOut
            cases r2 with
            | error _ => exact ⟨SameOutside_trans hOut1 ihOut.1, ihOut.2.1, ihOut.2.2.trans hLocks1⟩
            | ok lh =>
              exact ⟨ihOut.1, fun l hl => ihOut.2.1 l (hLocks1 ▸ hl),
                SameOutside_trans hOut1 ihOut.2.2.1, ihOut.2.2.2.1,
                ihOut.2.2.2.2.trans (congrArg _ hLocks1)⟩

private theorem bracketDirLockM_inside {α : Type} {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (lh : LockHandle) (lp : String) (lm : LockMode)
    (baseLocks : List (Nat × String × LockMode)) (s0 : VfsState)
    (action : StateM VfsState (Except FsError α))
    (hPos : 0 < lh.handleId) (hLt : ∀ l ∈ baseLocks, l.1 < lh.handleId)
    (hLocks0 : s0.locks = (lh.handleId, lp, lm) :: baseLocks)
    (hAct : InsideStep outerPos s0 (action s0).2) :
    match (Internal.bracketDirLockM (interleave env vfsDirOps) lh action) s0 with
    | (_, sOut) => SameOutside outerPos s0 sOut ∧ sOut.openDirs = s0.openDirs ∧ sOut.locks = baseLocks := by
  dsimp only [Internal.bracketDirLockM, bind, StateT.bind, pure, StateT.pure]
  rw [tryFinally_stateM_run]
  cases hA : action s0 with
  | mk actRes s1 =>
    rw [hA] at hAct
    dsimp only at hAct ⊢
    have he := insideStep_env hEnv s1
    have hEnvLocks : (env s1).locks = (lh.handleId, lp, lm) :: baseLocks := he.2.2.trans (hAct.2.2.trans hLocks0)
    have hNe0 : (lh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
    have hAny : (env s1).locks.any (fun p => p.1 == lh.handleId) = true := by
      rw [hEnvLocks]; simp
    have hFilter : (env s1).locks.filter (fun p => p.1 != lh.handleId) = baseLocks := by
      rw [hEnvLocks, List.filter_cons, bne_self_eq_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun l hl => bne_iff_ne.mpr (Nat.ne_of_lt (hLt l hl))
    have hRel : (interleave env vfsDirOps).releaseLock lh s1 = (.ok (), { env s1 with locks := baseLocks }) := by
      change vfsDirOps.releaseLock lh (env s1) = _
      rw [vfsDirOps_releaseLock_def, hNe0]
      simp [hAny, hFilter]
    rw [hRel]
    dsimp only
    cases actRes <;> exact ⟨SameOutside_trans hAct.1 he.1, he.2.1.trans hAct.2.1, rfl⟩

private theorem withFileLock_inside {α : Type} {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (dh : DirHandle) (dhPos : List String)
    (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
    (action : StateM VfsState (Except FsError α)) (s0 : VfsState)
    (hPre : outerPos <+: dhPos) (hLd : lookupDir s0 dh = some dhPos)
    (hAct : ∀ s, lookupDir s dh = some dhPos → InsideStep outerPos s (action s).2) :
    InsideStep outerPos s0 ((Internal.subtreeOpsM (interleave env vfsDirOps) dh).withFileLock rel mode createIfMissing action s0).2 := by
  dsimp only [Internal.subtreeOpsM]
  cases hSp : Internal.splitLastAux rel.segments [] with
  | none => exact InsideStep_refl outerPos s0
  | some pair =>
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hAcq := walkDescendAuxM_acquireLock hEnv s0.openDirs pair.1 pair.2 mode createIfMissing false
      true dh dhPos s0 ⟨rfl, hLd⟩ (by simpa [List.append_assoc] using List.IsPrefix.trans hPre (List.prefix_append _ _))
    cases hW : Internal.walkDescendM (interleave env vfsDirOps) dh pair.1
        (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh pair.2 mode createIfMissing false) s0 with
    | mk rLock s1 =>
      change (Internal.walkDescendAuxM (interleave env vfsDirOps) true dh pair.1
          (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh pair.2 mode createIfMissing false)) s0 = (rLock, s1) at hW
      rw [hW] at hAcq
      dsimp only
      cases rLock with
      | error e => exact hAcq
      | ok lh =>
        dsimp only
        rcases hAcq with ⟨hLhPos, hLhLt, hOut1, hDirs1, hLocks1⟩
        have hLd1 : lookupDir s1 dh = some dhPos := by
          have hEq : lookupDir s1 dh = lookupDir s0 dh := by simp [lookupDir, hDirs1]
          exact hEq.trans hLd
        have hBr := bracketDirLockM_inside hEnv lh lh.path mode s0.locks s1 action hLhPos hLhLt hLocks1 (hAct s1 hLd1)
        cases hB : Internal.bracketDirLockM (interleave env vfsDirOps) lh action s1 with
        | mk _ s2 =>
          rw [hB] at hBr
          exact ⟨SameOutside_trans hOut1 hBr.1, hBr.2.1.trans hDirs1, hBr.2.2⟩

private theorem tryWithFileLock_inside {α : Type} {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (dh : DirHandle) (dhPos : List String)
    (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
    (action : StateM VfsState (Except FsError α)) (s0 : VfsState)
    (hPre : outerPos <+: dhPos) (hLd : lookupDir s0 dh = some dhPos)
    (hAct : ∀ s, lookupDir s dh = some dhPos → InsideStep outerPos s (action s).2) :
    InsideStep outerPos s0 ((Internal.subtreeOpsM (interleave env vfsDirOps) dh).tryWithFileLock rel mode createIfMissing action s0).2 := by
  dsimp only [Internal.subtreeOpsM]
  cases hSp : Internal.splitLastAux rel.segments [] with
  | none => exact InsideStep_refl outerPos s0
  | some pair =>
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hAcq := walkDescendAuxM_acquireLock hEnv s0.openDirs pair.1 pair.2 mode createIfMissing true
      true dh dhPos s0 ⟨rfl, hLd⟩ (by simpa [List.append_assoc] using List.IsPrefix.trans hPre (List.prefix_append _ _))
    cases hW : Internal.walkDescendM (interleave env vfsDirOps) dh pair.1
        (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh pair.2 mode createIfMissing true) s0 with
    | mk rLock s1 =>
      change (Internal.walkDescendAuxM (interleave env vfsDirOps) true dh pair.1
          (fun parDh => (interleave env vfsDirOps).acquireLockAt parDh pair.2 mode createIfMissing true)) s0 = (rLock, s1) at hW
      rw [hW] at hAcq
      dsimp only
      cases rLock with
      | error e =>
        dsimp only
        split <;> exact hAcq
      | ok lh =>
        dsimp only
        rcases hAcq with ⟨hLhPos, hLhLt, hOut1, hDirs1, hLocks1⟩
        have hLd1 : lookupDir s1 dh = some dhPos := by
          have hEq : lookupDir s1 dh = lookupDir s0 dh := by simp [lookupDir, hDirs1]
          exact hEq.trans hLd
        let wrap : StateM VfsState (Except FsError (Option α)) := do
          match ← action with
          | .ok a => pure (.ok (some a))
          | .error e => pure (.error e)
        have hWrap : InsideStep outerPos s1 (wrap s1).2 := by
          have hA := hAct s1 hLd1
          dsimp only [wrap, bind, StateT.bind, pure, StateT.pure]
          cases hActRun : action s1 with
          | mk rA sA =>
            rw [hActRun] at hA
            cases rA <;> exact hA
        have hBr := bracketDirLockM_inside hEnv lh lh.path mode s0.locks s1 wrap hLhPos hLhLt hLocks1 hWrap
        change InsideStep outerPos s0 (Internal.bracketDirLockM (interleave env vfsDirOps) lh wrap s1).2
        exact ⟨SameOutside_trans hOut1 hBr.1, hBr.2.1.trans hDirs1, hBr.2.2⟩

private theorem splitLastAux_some_append {xs acc pre : List EntryName} {leaf : EntryName}
    (h : Internal.splitLastAux xs acc = some (pre, leaf)) :
    acc.reverse ++ xs = pre ++ [leaf] := by
  induction xs generalizing acc with
  | nil => simp [Internal.splitLastAux] at h
  | cons x xt ih =>
    cases xt with
    | nil =>
      simp only [Internal.splitLastAux, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp
    | cons y yt =>
      simpa [Internal.splitLastAux, List.append_assoc] using ih h

private theorem rmtree_inside {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (dh : DirHandle) (dhPos : List String)
    (rel : RelPath) (ignoreMissing : Bool) (s0 : VfsState)
    (hPre : outerPos <+: dhPos ++ rel.segments.map (·.val)) (hLd : lookupDir s0 dh = some dhPos) :
    InsideStep outerPos s0 ((Internal.subtreeOpsM (interleave env vfsDirOps) dh).rmtree rel ignoreMissing s0).2 := by
  dsimp only [Internal.subtreeOpsM]
  cases hSp : Internal.splitLastAux rel.segments [] with
  | none => exact InsideStep_refl outerPos s0
  | some pair =>
    have hSegs : rel.segments = pair.1 ++ [pair.2] := by
      simpa using splitLastAux_some_append hSp
    have hPrePair : outerPos <+: dhPos ++ pair.1.map (·.val) ++ [pair.2.val] := by
      simpa [hSegs, List.map_append, List.append_assoc] using hPre
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    cases hW : Internal.walkDescendM (interleave env vfsDirOps) dh pair.1
        (fun parDh => (interleave env vfsDirOps).lstatAt parDh pair.2) s0 with
    | mk rLeaf s1 =>
      have hRead := insideStep_walkDescend_eq hEnv dh dhPos pair.1 _ s0 rLeaf s1 hW hLd
        (fun _ parDh _ sX _ _ => interleave_lstatAt_inside hEnv parDh pair.2 sX)
      dsimp only
      cases rLeaf with
      | error e =>
        dsimp only
        split <;> exact hRead
      | ok info =>
        dsimp only
        split
        · exact hRead
        · have hLd1 : lookupDir s1 dh = some dhPos := by
            have hEq : lookupDir s1 dh = lookupDir s0 dh := by simp [lookupDir, hRead.2.1]
            exact hEq.trans hLd
          exact InsideStep_trans hRead (rmtreeDirAtM_inside hEnv dh 4096 pair.1 pair.2 s1 dhPos hPrePair hLd1)

private theorem subtreeOpsM_basic_inside {pos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside pos env) (dh : DirHandle) (dhPos : List String)
    (rel : RelPath) (bytes : ByteArray) (b1 b2 : Bool) (target : String) (s0 : VfsState)
    (hPre : pos <+: dhPos) (hLd : lookupDir s0 dh = some dhPos) :
    let sub := Internal.subtreeOpsM (interleave env vfsDirOps) dh
    InsideStep pos s0 (sub.lstat rel s0).2 ∧
    InsideStep pos s0 (sub.readRegular rel s0).2 ∧
    InsideStep pos s0 (sub.atomicWriteBytes rel bytes s0).2 ∧
    InsideStep pos s0 (sub.mkdir rel b1 b2 s0).2 ∧
    InsideStep pos s0 (sub.unlink rel b1 s0).2 ∧
    InsideStep pos s0 (sub.rmdir rel s0).2 ∧
    InsideStep pos s0 (sub.symlink target rel s0).2 ∧
    InsideStep pos s0 (sub.listDir rel s0).2 ∧
    InsideStep pos s0 (sub.walk rel s0).2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none => exact interleave_fstatDir_inside hEnv dh s0
    | some pair =>
      exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
        (fun _ parDh _ sX _ _ => interleave_lstatAt_inside hEnv parDh pair.2 sX)
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none =>
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      have hF := interleave_fstatDir_inside hEnv dh s0
      cases hFRun : (interleave env vfsDirOps).fstatDir dh s0 with
      | mk r s1 =>
        rw [hFRun] at hF
        dsimp only at hF ⊢
        cases r with
        | error _ => exact hF
        | ok _ => dsimp only; split <;> exact hF
    | some pair =>
      exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
        (fun _ parDh _ sX _ _ => interleave_readRegularAt_inside hEnv parDh pair.2 sX)
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none => exact InsideStep_refl pos s0
    | some pair =>
      exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
        (fun _ parDh cp sX hOwn hEq =>
          atomicWriteAtAuxM_inside hEnv parDh pair.2 bytes 16 sX (fun p hp => by
            rw [ownedHandle_lookup hOwn] at hp
            cases hp
            rw [hEq]
            exact List.IsPrefix.trans hPre (List.prefix_append _ _)))
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none =>
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      have hF := interleave_fstatDir_inside hEnv dh s0
      cases hFRun : (interleave env vfsDirOps).fstatDir dh s0 with
      | mk r s1 =>
        rw [hFRun] at hF
        dsimp only at hF ⊢
        cases r with
        | error _ => exact hF
        | ok _ =>
          dsimp only
          split <;> try exact hF
          split <;> exact hF
    | some pair =>
      dsimp only
      have hLeaf : ∀ isR parDh cp sX, OwnedHandle s0.openDirs isR parDh cp sX → pos <+: cp →
          InsideStep pos sX ((do
            match ← (interleave env vfsDirOps).createDirAt parDh pair.2 with
            | .ok () => pure (.ok ())
            | .error e =>
              if b2 && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
                match ← (interleave env vfsDirOps).lstatAt parDh pair.2 with
                | .error _ => pure (.error e)
                | .ok info =>
                  if info.kind == .dir then pure (.ok ())
                  else if e.kind == .alreadyExists then pure (.error e)
                  else pure (.error { kind := .alreadyExists, path := some pair.2.val, message := s!"already exists: {pair.2.val}" })
              else pure (.error e) : StateM VfsState (Except FsError Unit)) sX).2 := by
        intro _ parDh cp sX hOwn hCp
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        have hC := interleave_createDirAt_inside hEnv parDh pair.2 sX fun p hp => by
          rw [ownedHandle_lookup hOwn] at hp; cases hp; exact hCp
        cases hCRun : (interleave env vfsDirOps).createDirAt parDh pair.2 sX with
        | mk rC s1 =>
          rw [hCRun] at hC
          dsimp only at hC ⊢
          cases rC with
          | ok _ => exact hC
          | error e =>
            dsimp only
            split
            · dsimp only [StateT.bind]
              have hL := interleave_lstatAt_inside hEnv parDh pair.2 s1
              cases hLRun : (interleave env vfsDirOps).lstatAt parDh pair.2 s1 with
              | mk rL s2 =>
                rw [hLRun] at hL
                dsimp only at hL ⊢
                have hI := InsideStep_trans hC hL
                cases rL with
                | error _ => exact hI
                | ok info =>
                  dsimp only [bind, StateT.bind, Bind.bind, pure, StateT.pure, Pure.pure]
                  split
                  · exact hI
                  · split <;> exact hI
            · exact hC
      split
      · exact mkdirWalkM_inside hEnv dh dhPos pair.1 _ s0 hPre hLd hLeaf
      · exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
          (fun isR c cp sX hOwn hEq => hLeaf isR c cp sX hOwn (hEq ▸ List.IsPrefix.trans hPre (List.prefix_append _ _)))
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none => exact InsideStep_refl pos s0
    | some pair =>
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      have hW := walkDescendM_inside hEnv dh dhPos pair.1
        (fun parDh => (interleave env vfsDirOps).unlinkAt parDh pair.2 false) s0 hLd
        (fun _ parDh cp sX hOwn hEq =>
          interleave_unlinkAt_inside hEnv parDh pair.2 false sX fun p hp => by
            rw [ownedHandle_lookup hOwn] at hp
            cases hp
            exact hEq ▸ List.IsPrefix.trans hPre (List.prefix_append _ _))
      cases hRun : Internal.walkDescendM (interleave env vfsDirOps) dh pair.1
          (fun parDh => (interleave env vfsDirOps).unlinkAt parDh pair.2 false) s0 with
      | mk r s1 =>
        rw [hRun] at hW
        dsimp only at hW ⊢
        cases r with
        | ok _ => exact hW
        | error e => dsimp only; split <;> exact hW
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none => exact InsideStep_refl pos s0
    | some pair =>
      exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
        (fun _ parDh cp sX hOwn hEq =>
          interleave_unlinkAt_inside hEnv parDh pair.2 true sX fun p hp => by
            rw [ownedHandle_lookup hOwn] at hp
            cases hp
            exact hEq ▸ List.IsPrefix.trans hPre (List.prefix_append _ _))
  · dsimp only [Internal.subtreeOpsM]
    cases Internal.splitLastAux rel.segments [] with
    | none => exact InsideStep_refl pos s0
    | some pair =>
      dsimp only
      split
      · exact InsideStep_refl pos s0
      · exact walkDescendM_inside hEnv dh dhPos pair.1 _ s0 hLd
          (fun _ parDh cp sX hOwn hEq =>
            interleave_symlinkAt_inside hEnv target parDh pair.2 sX fun p hp => by
              rw [ownedHandle_lookup hOwn] at hp
              cases hp
              exact hEq ▸ List.IsPrefix.trans hPre (List.prefix_append _ _))
  · dsimp only [Internal.subtreeOpsM]
    exact walkDescendM_inside hEnv dh dhPos rel.segments _ s0 hLd
      (fun _ dirDh _ sX _ _ => by
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        have hR := interleave_readDirAt_inside hEnv dirDh sX
        cases hRd : (interleave env vfsDirOps).readDirAt dirDh sX with
        | mk r s1 =>
          rw [hRd] at hR
          dsimp only at hR ⊢
          cases r <;> exact hR)
  · dsimp only [Internal.subtreeOpsM]
    exact (walkRecM_and_children_inside hEnv dh 4096).1 rel.segments "." #[] s0 dhPos hLd

private theorem evalSubtreeProg_insideStep {α : Type} {outerPos : List String} {env : VfsState → VfsState}
    (hEnv : EnvInside outerPos env) (dh : DirHandle) (dhPos : List String)
    (hPre : outerPos <+: dhPos) (prog : SubtreeProg α) :
    ∀ s0, lookupDir s0 dh = some dhPos →
      InsideStep outerPos s0 (evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) prog s0).2 := by
  induction prog with
  | pure _ =>
    intro s0 _
    simp only [evalSubtreeProg]
    exact InsideStep_refl outerPos s0
  | lstat rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false "" s0 hPre hLd).1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).lstat rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | readRegular rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false "" s0 hPre hLd).2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).readRegular rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | atomicWriteBytes rel bytes cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel bytes false false "" s0 hPre hLd).2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).atomicWriteBytes rel bytes s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | mkdir rel parents existOk cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty parents existOk "" s0 hPre hLd).2.2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).mkdir rel parents existOk s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | unlink rel missingOk cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty missingOk false "" s0 hPre hLd).2.2.2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).unlink rel missingOk s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | rmdir rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false "" s0 hPre hLd).2.2.2.2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).rmdir rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | rmtree rel ignoreMissing cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := rmtree_inside hEnv dh dhPos rel ignoreMissing s0 (List.IsPrefix.trans hPre (List.prefix_append _ _)) hLd
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).rmtree rel ignoreMissing s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | symlink target rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false target s0 hPre hLd).2.2.2.2.2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).symlink target rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | listDir rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false "" s0 hPre hLd).2.2.2.2.2.2.2.1
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).listDir rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | walk rel cont ih =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := (subtreeOpsM_basic_inside hEnv dh dhPos rel ByteArray.empty false false "" s0 hPre hLd).2.2.2.2.2.2.2.2
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).walk rel s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ih r s1 hLd1)
  | withFileLock rel mode cim body cont ihBody ihCont =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := withFileLock_inside hEnv dh dhPos rel mode cim
      (evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) body) s0 hPre hLd ihBody
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).withFileLock rel mode cim
        (evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) body) s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ihCont r s1 hLd1)
  | tryWithFileLock rel mode cim body cont ihBody ihCont =>
    intro s0 hLd
    simp only [evalSubtreeProg, bind, StateT.bind]
    have hOp := tryWithFileLock_inside hEnv dh dhPos rel mode cim
      (evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) body) s0 hPre hLd ihBody
    cases hRun : (Internal.subtreeOpsM (interleave env vfsDirOps) dh).tryWithFileLock rel mode cim
        (evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) body) s0 with
    | mk r s1 =>
      rw [hRun] at hOp
      dsimp only at hOp
      have hLd1 : lookupDir s1 dh = some dhPos := (by simp [lookupDir, hOp.2.1] : lookupDir s1 dh = lookupDir s0 dh).trans hLd
      exact InsideStep_trans hOp (ihCont r s1 hLd1)

private theorem envInside_id (pos : List String) : EnvInside pos id :=
  fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- Every operation in `Internal.subtreeOpsM` satisfies `SpecSubtreeSameOutside`. -/
theorem spec_subtreeSameOutside : SpecSubtreeSameOutside Internal.subtreeOpsM := by
  intro st dh pos rel bytes b1 b2 target lockMode α pureRes hLd _
  have hB := subtreeOpsM_basic_inside (envInside_id pos) dh pos rel bytes b1 b2 target st (List.prefix_refl pos) hLd
  have hRm := rmtree_inside (envInside_id (pos ++ rel.segments.map (·.val))) dh pos rel b1 st (List.prefix_refl _) hLd
  have hWfl := withFileLock_inside (envInside_id pos) dh pos rel lockMode b1 (pure pureRes) st
    (List.prefix_refl pos) hLd (fun s _ => InsideStep_refl pos s)
  have hTwfl := tryWithFileLock_inside (envInside_id pos) dh pos rel lockMode b1 (pure pureRes) st
    (List.prefix_refl pos) hLd (fun s _ => InsideStep_refl pos s)
  exact ⟨hB.1.1, hB.2.1.1, hB.2.2.1.1, hB.2.2.2.1.1, hB.2.2.2.2.1.1, hB.2.2.2.2.2.1.1,
    hRm.1, hB.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.2.1, hWfl.1, hTwfl.1⟩

/-- Every interleaved subtree program executed through `Internal.mkSubtreeOpenerM` preserves `SameOutside pos`, `openDirs`, and `locks`. -/
theorem spec_subtreeProgramSameOutsideInterleaved :
    SpecSubtreeProgramSameOutsideInterleaved Internal.mkSubtreeOpenerM := by
  intro α env root st pos m prog hPosValid hEnv _ _ _ hResAny
  dsimp only [Internal.mkSubtreeOpenerM, Internal.withSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  have he := insideStep_env hEnv st
  cases hOp : (interleave env vfsDirOps).openDir root st with
  | mk rOp s1 =>
    change vfsDirOps.openDir root (env st) = (rOp, s1) at hOp
    cases rOp with
    | error e =>
      dsimp only
      have hS1 := vfsDirOps_openDir_err root (env st) e s1 hOp
      rw [hS1]
      exact ⟨he.1, he.2.1, he.2.2⟩
    | ok dh =>
      dsimp only
      rcases vfsDirOps_openDir_ok_resolved root (env st) dh s1 hOp with
        ⟨hDhPos, _, hDhGt, canon, cm, hResCanon, _, hSt1⟩
      have hEnvData := hEnv st
      have hCanonEq : canon = pathOfSegs pos :=
        hResAny (env st) hEnvData.1 hEnvData.2.2.1 hEnvData.2.1 (canon, .dir cm) hResCanon
      have hSplitCanon : vfsSplitSegs canon = pos := by
        rw [hCanonEq]
        exact vfsSplitSegs_pathOfSegs pos hPosValid
      have hS1Dirs : s1.openDirs = (dh.handleId, pos) :: st.openDirs := by
        rw [hSt1, hSplitCanon, hEnvData.2.2.2.1]
      have hS1Locks : s1.locks = st.locks := by
        rw [hSt1, hEnvData.2.2.2.2]
      have hDhGtSt : ∀ q ∈ st.openDirs, q.1 < dh.handleId := fun q hq => hDhGt q (hEnvData.2.2.2.1 ▸ hq)
      have hLd1 : lookupDir s1 dh = some pos := by
        unfold lookupDir
        rw [hS1Dirs, beq_false_of_ne (Nat.ne_of_gt hDhPos)]
        simp
      let body : StateM VfsState (Except FsError α) := do
        match ← (interleave env vfsDirOps).fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind != .dir then pure (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" })
          else if info.mode / 256 % 2 == 0 || info.mode / 64 % 2 == 0 then
            pure (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" })
          else evalSubtreeProg (Internal.subtreeOpsM (interleave env vfsDirOps) dh) prog
      have hBody : InsideStep pos s1 (body s1).2 := by
        dsimp only [body, bind, StateT.bind, pure, StateT.pure]
        have hF := interleave_fstatDir_inside hEnv dh s1
        cases hFRun : (interleave env vfsDirOps).fstatDir dh s1 with
        | mk rF s2 =>
          rw [hFRun] at hF
          dsimp only at hF ⊢
          cases rF with
          | error _ => exact hF
          | ok info =>
            dsimp only
            split
            · exact hF
            · split
              · exact hF
              · have hLd2 : lookupDir s2 dh = some pos := by
                  have hEq : lookupDir s2 dh = lookupDir s1 dh := by simp [lookupDir, hF.2.1]
                  exact hEq.trans hLd1
                exact InsideStep_trans hF (evalSubtreeProg_insideStep hEnv dh pos (List.prefix_refl pos) prog s2 hLd2)
      have hBr := bracketCloseDirM_owned hEnv dh pos st.openDirs hDhPos hDhGtSt body hS1Dirs hBody
      have hOutOp : SameOutside pos (env st) s1 := by rw [hSt1]; exact fun _ _ => rfl
      change InsideStep pos st (Internal.bracketCloseDirM (interleave env vfsDirOps) dh body s1).2
      exact ⟨SameOutside_trans (SameOutside_trans he.1 hOutOp) hBr.2.1,
        hBr.2.2.1, hBr.2.2.2.trans hS1Locks⟩

private theorem vfsDirOps_simple_openDirs (dh : DirHandle) (name : EntryName) (bytes : ByteArray)
    (target : String) (b : Bool) (st : VfsState) :
    (vfsDirOps.fstatDir dh st).2.openDirs = st.openDirs ∧
    (vfsDirOps.lstatAt dh name st).2.openDirs = st.openDirs ∧
    (vfsDirOps.readDirAt dh st).2.openDirs = st.openDirs ∧
    (vfsDirOps.createDirAt dh name st).2.openDirs = st.openDirs ∧
    (vfsDirOps.readRegularAt dh name st).2.openDirs = st.openDirs ∧
    (vfsDirOps.createFileAt dh name bytes st).2.openDirs = st.openDirs ∧
    (vfsDirOps.renameAt dh name dh name st).2.openDirs = st.openDirs ∧
    (vfsDirOps.unlinkAt dh name b st).2.openDirs = st.openDirs ∧
    (vfsDirOps.symlinkAt target dh name st).2.openDirs = st.openDirs ∧
    (vfsDirOps.freshTempName st).2.openDirs = st.openDirs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vfsDirOps_fstatDir_def]
  · rw [vfsDirOps_lstatAt_def]
  · rw [vfsDirOps_readDirAt_def]
  · rw [vfsDirOps_createDirAt_def]; repeat (first | dsimp only | split | rfl)
  · rw [vfsDirOps_readRegularAt_def]
  · rw [vfsDirOps_createFileAt_def]; repeat (first | dsimp only | split | rfl)
  · rw [vfsDirOps_renameAt_def]; repeat (first | dsimp only | split | rfl)
  · rw [vfsDirOps_unlinkAt_def]; repeat (first | dsimp only | split | rfl)
  · rw [vfsDirOps_symlinkAt_def]; repeat (first | dsimp only | split | rfl)
  · rcases vfsDirOps_freshTempName_def st with ⟨_, hSt⟩; rw [hSt]

private theorem walkDescendM_none_eq {α : Type} (dh : DirHandle) (segs : List EntryName)
    (act : DirHandle → StateM VfsState (Except FsError α)) (st : VfsState)
    (hNone : lookupDir st dh = none) :
    match segs with
    | [] => Internal.walkDescendM vfsDirOps dh [] act st = act dh st
    | _ :: _ => Internal.walkDescendM vfsDirOps dh segs act st = (.error (mInvalidDirHandleErr dh), st) := by
  cases segs with
  | nil => rfl
  | cons seg rest =>
    dsimp only [Internal.walkDescendM]
    unfold Internal.walkDescendAuxM
    simp only [↓reduceIte]
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    rw [vfsDirOps_openDirAt_none st dh seg hNone]
    rfl

/-- Both `Internal.mkSubtreeOpenerM` and `Internal.subtreeOpsM` conserve `st.openDirs` for all valid or invalid handles. -/
theorem spec_descriptorConservation :
    SpecDescriptorConservation Internal.mkSubtreeOpenerM Internal.subtreeOpsM := by
  refine ⟨?_, ?_⟩
  · intro st dh rel bytes b1 b2 target lockMode α pureRes _
    cases hLd : lookupDir st dh with
    | some pos =>
      have hB := subtreeOpsM_basic_inside (envInside_id pos) dh pos rel bytes b1 b2 target st (List.prefix_refl pos) hLd
      have hRm := rmtree_inside (envInside_id pos) dh pos rel b1 st (List.IsPrefix.trans (List.prefix_refl pos) (List.prefix_append _ _)) hLd
      have hWfl := withFileLock_inside (envInside_id pos) dh pos rel lockMode b1 (pure pureRes) st
        (List.prefix_refl pos) hLd (fun s _ => InsideStep_refl pos s)
      have hTwfl := tryWithFileLock_inside (envInside_id pos) dh pos rel lockMode b1 (pure pureRes) st
        (List.prefix_refl pos) hLd (fun s _ => InsideStep_refl pos s)
      exact ⟨hB.1.2.1, hB.2.1.2.1, hB.2.2.1.2.1, hB.2.2.2.1.2.1, hB.2.2.2.2.1.2.1, hB.2.2.2.2.2.1.2.1,
        hRm.2.1, hB.2.2.2.2.2.2.1.2.1, hB.2.2.2.2.2.2.2.1.2.1, hB.2.2.2.2.2.2.2.2.2.1, hWfl.2.1, hTwfl.2.1⟩
    | none =>
      have walkNone : ∀ {β : Type} (segs : List EntryName) (act : DirHandle → StateM VfsState (Except FsError β)),
          (∀ s, (act dh s).2.openDirs = s.openDirs) →
          (Internal.walkDescendM vfsDirOps dh segs act st).2.openDirs = st.openDirs := by
        intro β segs act hAct
        have hW := walkDescendM_none_eq dh segs act st hLd
        cases segs with
        | nil => rw [hW]; exact hAct st
        | cons _ _ => rw [hW]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => exact (vfsDirOps_simple_openDirs dh ⟨"x", by decide⟩ bytes target b1 st).1
        | some pair => exact walkNone pair.1 _ (fun s => (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s).2.1)
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          rw [vfsDirOps_fstatDir_def, hLd]
          rfl
        | some pair => exact walkNone pair.1 _ (fun s => (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s).2.2.2.2.1)
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          apply walkNone pair.1 _
          intro s
          suffices ∀ k s0, (Internal.atomicWriteAtAuxM vfsDirOps dh pair.2 bytes k s0).2.openDirs = s0.openDirs from this 16 s
          intro k
          induction k with
          | zero => intro s0; rfl
          | succ k' ihk =>
            intro s0
            dsimp only [Internal.atomicWriteAtAuxM, bind, StateT.bind, pure, StateT.pure]
            have h0 := (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s0).2.2.2.2.2.2.2.2.2
            cases hF : vfsDirOps.freshTempName s0 with
            | mk tmp s1 =>
              rw [hF] at h0
              dsimp only at h0 ⊢
              have h1 := (vfsDirOps_simple_openDirs dh tmp bytes target b1 s1).2.2.2.2.2.1
              cases hC : vfsDirOps.createFileAt dh tmp bytes s1 with
              | mk rC s2 =>
                rw [hC] at h1
                dsimp only at h1 ⊢
                cases rC with
                | ok _ =>
                  dsimp only [StateT.bind]
                  have hRn : (vfsDirOps.renameAt dh tmp dh pair.2 s2).2.openDirs = s2.openDirs := by
                    rw [vfsDirOps_renameAt_def]; repeat (first | dsimp only | split | rfl)
                  cases hR : vfsDirOps.renameAt dh tmp dh pair.2 s2 with
                  | mk rR s3 =>
                    rw [hR] at hRn
                    dsimp only at hRn ⊢
                    cases rR with
                    | ok _ => exact hRn.trans (h1.trans h0)
                    | error _ =>
                      have h3 := (vfsDirOps_simple_openDirs dh tmp bytes target false s3).2.2.2.2.2.2.2.1
                      exact h3.trans (hRn.trans (h1.trans h0))
                | error _ =>
                  dsimp only
                  split
                  · exact (ihk s2).trans (h1.trans h0)
                  · exact h1.trans h0
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          rw [vfsDirOps_fstatDir_def, hLd]
          rfl
        | some pair =>
          dsimp only
          have hLeaf : ∀ s, ((do
              match ← vfsDirOps.createDirAt dh pair.2 with
              | .ok () => pure (.ok ())
              | .error e =>
                if b2 && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
                  match ← vfsDirOps.lstatAt dh pair.2 with
                  | .error _ => pure (.error e)
                  | .ok info =>
                    if info.kind == .dir then pure (.ok ())
                    else if e.kind == .alreadyExists then pure (.error e)
                    else pure (.error { kind := .alreadyExists, path := some pair.2.val, message := s!"already exists: {pair.2.val}" })
                else pure (.error e) : StateM VfsState (Except FsError Unit)) s).2.openDirs = s.openDirs := by
            intro s
            dsimp only [bind, StateT.bind, pure, StateT.pure]
            have hc := (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s).2.2.2.1
            cases hCr : vfsDirOps.createDirAt dh pair.2 s with
            | mk rC s1 =>
              rw [hCr] at hc
              dsimp only at hc ⊢
              cases rC with
              | ok _ => exact hc
              | error e =>
                dsimp only
                split
                · dsimp only [bind, StateT.bind, Bind.bind, pure, StateT.pure, Pure.pure]
                  have hl := (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s1).2.1
                  cases hLs : vfsDirOps.lstatAt dh pair.2 s1 with
                  | mk rL s2 =>
                    rw [hLs] at hl
                    dsimp only at hl ⊢
                    cases rL with
                    | error _ => exact hl.trans hc
                    | ok info =>
                      dsimp only [bind, StateT.bind, Bind.bind, pure, StateT.pure, Pure.pure]
                      split
                      · exact hl.trans hc
                      · split <;> exact hl.trans hc
                · exact hc
          split
          · cases hP : pair.1 with
            | nil =>
              unfold Internal.mkdirWalkM
              simp only [↓reduceIte]
              exact hLeaf st
            | cons seg _ =>
              unfold Internal.mkdirWalkM
              simp only [↓reduceIte]
              dsimp only [bind, StateT.bind, pure, StateT.pure]
              rw [vfsDirOps_openDirAt_none st dh seg hLd]
              simp only [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl,
                Bool.false_eq_true, ↓reduceIte]
              rfl
          · exact walkNone pair.1 _ hLeaf
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hW := walkNone pair.1 (fun parDh => vfsDirOps.unlinkAt parDh pair.2 false)
            (fun s => (vfsDirOps_simple_openDirs dh pair.2 bytes target false s).2.2.2.2.2.2.2.1)
          cases hRun : Internal.walkDescendM vfsDirOps dh pair.1
              (fun parDh => vfsDirOps.unlinkAt parDh pair.2 false) st with
          | mk r s1 =>
            rw [hRun] at hW
            dsimp only at hW ⊢
            cases r with
            | ok _ => exact hW
            | error e => dsimp only; split <;> exact hW
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair => exact walkNone pair.1 _ (fun s => (vfsDirOps_simple_openDirs dh pair.2 bytes target true s).2.2.2.2.2.2.2.1)
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hStep : ∃ e, Internal.walkDescendM vfsDirOps dh pair.1 (fun parDh => vfsDirOps.lstatAt parDh pair.2) st = (.error e, st) := by
            cases pair.1 with
            | nil =>
              dsimp only [Internal.walkDescendM]
              unfold Internal.walkDescendAuxM
              simp only [↓reduceIte]
              rw [vfsDirOps_lstatAt_def]
              have hN : lookupDir st dh = none := hLd
              simp [hN]
              exact ⟨_, rfl⟩
            | cons seg rest =>
              rw [walkDescendM_none_eq dh (seg :: rest) _ st hLd]
              exact ⟨_, rfl⟩
          rcases hStep with ⟨e, hEq⟩
          rw [hEq]
          dsimp only
          split <;> rfl
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          dsimp only
          split
          · rfl
          · exact walkNone pair.1 _ (fun s => (vfsDirOps_simple_openDirs dh pair.2 bytes target b1 s).2.2.2.2.2.2.2.2.1)
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        apply walkNone rel.segments _
        intro s
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        have hr := (vfsDirOps_simple_openDirs dh ⟨"x", by decide⟩ bytes target b1 s).2.2.1
        cases hR : vfsDirOps.readDirAt dh s with
        | mk r s1 => rw [hR] at hr; dsimp only at hr ⊢; cases r <;> exact hr
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        unfold Internal.walkRecM
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        cases rel.segments with
        | nil =>
          dsimp only [Internal.walkDescendM]
          unfold Internal.walkDescendAuxM
          simp only [↓reduceIte]
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          rw [vfsDirOps_readDirAt_def, hLd]
          rfl
        | cons seg rest =>
          rw [walkDescendM_none_eq dh (seg :: rest) _ st hLd]
          rfl
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hAcqNone : ∃ e, (Internal.walkDescendM vfsDirOps dh pair.1
              (fun parDh => vfsDirOps.acquireLockAt parDh pair.2 lockMode b1 false) st) = (.error e, st) := by
            cases pair.1 with
            | nil =>
              dsimp only [Internal.walkDescendM]
              unfold Internal.walkDescendAuxM
              simp only [↓reduceIte]
              rw [vfsDirOps_acquireLockAt_none st dh pair.2 lockMode b1 false hLd]
              exact ⟨_, rfl⟩
            | cons seg rest =>
              rw [walkDescendM_none_eq dh (seg :: rest) _ st hLd]
              exact ⟨_, rfl⟩
          rcases hAcqNone with ⟨e, hEq⟩
          rw [hEq]
          rfl
      · dsimp only [Internal.subtreeOpsM, StateT.run]
        cases Internal.splitLastAux rel.segments [] with
        | none => rfl
        | some pair =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hAcqNone : ∃ e, (Internal.walkDescendM vfsDirOps dh pair.1
              (fun parDh => vfsDirOps.acquireLockAt parDh pair.2 lockMode b1 true) st) = (.error e, st) := by
            cases pair.1 with
            | nil =>
              dsimp only [Internal.walkDescendM]
              unfold Internal.walkDescendAuxM
              simp only [↓reduceIte]
              rw [vfsDirOps_acquireLockAt_none st dh pair.2 lockMode b1 true hLd]
              exact ⟨_, rfl⟩
            | cons seg rest =>
              rw [walkDescendM_none_eq dh (seg :: rest) _ st hLd]
              exact ⟨_, rfl⟩
          rcases hAcqNone with ⟨e, hEq⟩
          rw [hEq]
          dsimp only
          split <;> rfl
  · intro α root st pureRes _
    dsimp only [Internal.mkSubtreeOpenerM, Internal.withSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    cases hOp : vfsDirOps.openDir root st with
    | mk rOp s1 =>
      dsimp only
      cases rOp with
      | error e => exact congrArg VfsState.openDirs (vfsDirOps_openDir_err root st e s1 hOp)
      | ok dh =>
        rcases vfsDirOps_openDir_ok root st dh s1 hOp with ⟨hDhPos, _, hDhGt, pos, hSt1⟩
        have hS1Dirs : s1.openDirs = (dh.handleId, pos) :: st.openDirs := by rw [hSt1]
        let body : StateM VfsState (Except FsError α) := do
          match ← (interleave id vfsDirOps).fstatDir dh with
          | .error e => pure (.error e)
          | .ok info =>
            if info.kind != .dir then pure (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" })
            else if info.mode / 256 % 2 == 0 || info.mode / 64 % 2 == 0 then
              pure (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" })
            else pure pureRes
        have hBody : InsideStep pos s1 (body s1).2 := by
          dsimp only [body, bind, StateT.bind, pure, StateT.pure]
          have hF := interleave_fstatDir_inside (envInside_id pos) dh s1
          cases hFRun : (interleave id vfsDirOps).fstatDir dh s1 with
          | mk rF s2 =>
            rw [hFRun] at hF
            dsimp only at hF ⊢
            cases rF with
            | error _ => exact hF
            | ok info =>
              dsimp only
              split
              · exact hF
              · split <;> exact hF
        have hBr := bracketCloseDirM_owned (envInside_id pos) dh pos st.openDirs hDhPos hDhGt body hS1Dirs hBody
        change (Internal.bracketCloseDirM (interleave id vfsDirOps) dh body s1).2.openDirs = st.openDirs
        exact hBr.2.2.1

end LeanSwe.Fs.Proofs
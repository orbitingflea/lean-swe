import LeanSwe.Fs.Proofs.FsRefinesHelpers2

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

private theorem list_forIn_state_const {W α β : Type}
    (step : α → β → StateM W (ForInStep β))
    (hConst : ∀ a b s, ((step a b).run s).2 = s)
    (xs : List α) (b : β) (s : W) : ((forIn xs b step).run s).2 = s := by
  induction xs generalizing b with
  | nil => rfl
  | cons a rest ih =>
    rw [List.forIn_cons]
    have h1 := hConst a b s
    cases hR : (step a b s) with
    | mk st s1 =>
      rw [StateT.run] at h1; rw [hR] at h1; dsimp only at h1; subst h1
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases st with
      | done _ => rfl
      | yield b' => exact ih b'

private theorem array_forIn_state_const {W α β : Type}
    (step : α → β → StateM W (ForInStep β))
    (hConst : ∀ a b s, ((step a b).run s).2 = s)
    (arr : Array α) (b : β) (s : W) : ((forIn arr b step).run s).2 = s := by
  rw [← Array.forIn_toList]
  exact list_forIn_state_const step hConst arr.toList b s

private theorem pairwise_push_str {arr : Array String} {x : String}
    (hPw : List.Pairwise (· ≤ ·) arr.toList) (hAll : ∀ a ∈ arr.toList, a ≤ x) :
    List.Pairwise (· ≤ ·) (arr.push x).toList := by
  rw [Array.toList_push, List.pairwise_append]
  exact ⟨hPw, List.pairwise_singleton _ _, fun a ha b hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact hAll a ha⟩

/-- Trace specification for `Internal.walkGoM`. -/
theorem walkGoM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (fuel : Nat) (root relRoot : String) (acc : Array WalkEntry)
    (hAcc : ∀ e ∈ acc.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.walkGoM ops.toNonLockFsOpsM root relRoot acc fuel).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      exceptPred r.1
        (fun es =>
          (∀ e ∈ es.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
          es.size > 0 ∧
          let fullDir := if relRoot == "." then root else Internal.join root relRoot
          ∃ h eof, (.openat none fullDir.toUTF8 dirOpenFlags 0, .opened h) ∈ tr ∧
            (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0)
        (fun e => nonLockErrOk e) := by
  induction fuel generalizing relRoot acc s with
  | zero =>
    simp only [Internal.walkGoM, Pure.pure, StateT.pure, StateT.run, exceptPred]
    exact ⟨[], fsWorldTrace_nil hWf, nonEmpty_append_left (by decide), by intro h; cases h⟩
  | succ k ih =>
    unfold Internal.walkGoM
    let fullDir := if relRoot == "." then root else Internal.join root relRoot
    have hL := listDirSortedM_trace hOps fullDir hWf
    cases hEl : (Internal.listDirSortedM ops.toNonLockFsOpsM fullDir s) with
    | mk rL s1 =>
      rw [StateT.run] at hL; rw [hEl] at hL; dsimp only at hL
      obtain ⟨tr0, hTr0, _, hOut0⟩ := hL
      dsimp only [fullDir] at hEl
      simp only [Bind.bind, StateT.bind, StateT.run, hEl]
      cases rL with
      | error e => simp only [Pure.pure, StateT.pure, exceptPred]; exact ⟨tr0, hTr0, hOut0.1⟩
      | ok names =>
        obtain ⟨hPwNames, _, hFd, eof, trO, trB, trC, hTr0Eq, hMemO, hMemE, hEz, _, _⟩ := hOut0
        have hMemO0 : (.openat none fullDir.toUTF8 dirOpenFlags 0, .opened hFd) ∈ tr0 := by
          rw [hTr0Eq]; exact List.mem_append_left _ (List.mem_append_left _ hMemO)
        have hMemE0 : (.getdents64 hFd 8192, .bytes eof) ∈ tr0 := by
          rw [hTr0Eq]; exact List.mem_append_left _ (List.mem_append_right _ hMemE)
        let inv1 : (Array String × Array String) → List String → Prop := fun p rest =>
          List.Pairwise (· ≤ ·) rest ∧
          List.Pairwise (· ≤ ·) p.1.toList ∧ List.Pairwise (· ≤ ·) p.2.toList ∧
          (∀ a ∈ p.1.toList, ∀ b ∈ rest, a ≤ b) ∧ (∀ a ∈ p.2.toList, ∀ b ∈ rest, a ≤ b)
        let step1 : String → (Array String × Array String) → StateM W (ForInStep (Array String × Array String)) :=
          fun n p => do
            let childFull := Internal.join fullDir n
            let isSubDir ← match ← ops.stat false childFull with
              | .ok st => pure (st.kind == .dir)
              | .error _ => pure false
            if isSubDir then pure (.yield (p.1.push n, p.2))
            else pure (.yield (p.1, p.2.push n))
        have hLoop1 := array_forIn_state_inv inv1 step1
          (fun a rest p sX hWX hI => by
            obtain ⟨hPwR, hPw1, hPw2, hLe1, hLe2⟩ := hI
            have hCons := List.pairwise_cons.mp hPwR
            dsimp only [step1]
            have hS := scoped_stat hOps false (Internal.join fullDir a) hWX
            cases hEs : (ops.stat false (Internal.join fullDir a) sX) with
            | mk rS sY =>
              rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
              obtain ⟨trS, hTrS, _, _⟩ := hS
              simp only [Bind.bind, StateT.bind, StateT.run, hEs, Pure.pure]
              have hPush1 : inv1 (p.1.push a, p.2) rest := by
                refine ⟨hCons.2, pairwise_push_str hPw1 (fun x hx => hLe1 x hx a (List.mem_cons_self ..)), hPw2, ?_, ?_⟩
                · intro x hx b hb
                  rw [Array.toList_push, List.mem_append] at hx
                  rcases hx with hx1 | hx2
                  · exact hLe1 x hx1 b (List.mem_cons_of_mem a hb)
                  · simp only [List.mem_singleton] at hx2; subst hx2; exact hCons.1 b hb
                · intro x hx b hb; exact hLe2 x hx b (List.mem_cons_of_mem a hb)
              have hPush2 : inv1 (p.1, p.2.push a) rest := by
                refine ⟨hCons.2, hPw1, pairwise_push_str hPw2 (fun x hx => hLe2 x hx a (List.mem_cons_self ..)), ?_, ?_⟩
                · intro x hx b hb; exact hLe1 x hx b (List.mem_cons_of_mem a hb)
                · intro x hx b hb
                  rw [Array.toList_push, List.mem_append] at hx
                  rcases hx with hx1 | hx2
                  · exact hLe2 x hx1 b (List.mem_cons_of_mem a hb)
                  · simp only [List.mem_singleton] at hx2; subst hx2; exact hCons.1 b hb
              cases rS with
              | error _ => exact ⟨trS, hTrS, hPush2⟩
              | ok st =>
                by_cases hD : (st.kind == .dir) = true
                · simp only [hD]; exact ⟨trS, hTrS, hPush1⟩
                · simp only [hD]; exact ⟨trS, hTrS, hPush2⟩)
          names (#[], #[]) hTr0.1 ⟨hPwNames, by simp, by simp, fun _ h => by simp at h, fun _ h => by simp at h⟩
        cases hL1 : (forIn names (#[], #[]) step1 s1) with
        | mk df s2 =>
          rw [StateT.run] at hLoop1; rw [hL1] at hLoop1; dsimp only at hLoop1
          obtain ⟨tr1, hTr1, _, hPwDirs, hPwFiles, _, _⟩ := hLoop1
          let out0 := acc.push { root := relRoot, dirs := df.1, files := df.2 }
          have hOut0Inv : (∀ e ∈ out0.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧ out0.size > 0 := by
            refine ⟨fun e he => ?_, by simp [out0]⟩
            rw [Array.toList_push, List.mem_append] at he
            rcases he with h1 | h2
            · exact hAcc e h1
            · simp only [List.mem_singleton] at h2; subst h2; exact ⟨hPwDirs, hPwFiles⟩
          let inv2 : (Option (Except FsError (Array WalkEntry)) × Array WalkEntry) → List String → Prop :=
            fun st rest => match st.1 with
              | none => (∀ e ∈ st.2.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧ st.2.size > 0
              | some (.error e) => rest = [] ∧ nonLockErrOk e
              | some (.ok _) => False
          let step2 : String → (Option (Except FsError (Array WalkEntry)) × Array WalkEntry) →
              StateM W (ForInStep (Option (Except FsError (Array WalkEntry)) × Array WalkEntry)) :=
            fun d st => do
              let nextRel := if relRoot == "." then d else Internal.join relRoot d
              match ← Internal.walkGoM ops.toNonLockFsOpsM root nextRel st.2 k with
              | .error e => pure (.done (some (.error e), st.2))
              | .ok out' => pure (.yield (none, out'))
          have hLoop2 := array_forIn_state_inv inv2 step2
            (fun d rest st sX hWX hI => by
              dsimp only [step2]
              dsimp only [inv2] at hI
              cases hOpt : st.1 with
              | some r =>
                rw [hOpt] at hI
                cases r with
                | ok _ => exact False.elim hI
                | error _ => exact False.elim (List.cons_ne_nil d rest hI.1)
              | none =>
                rw [hOpt] at hI
                have hSub := ih (if relRoot == "." then d else Internal.join relRoot d) st.2 hI.1 hWX
                cases hEr : (Internal.walkGoM ops.toNonLockFsOpsM root (if relRoot == "." then d else Internal.join relRoot d) st.2 k sX) with
                | mk rSub sY =>
                  rw [StateT.run] at hSub; rw [hEr] at hSub; dsimp only at hSub
                  obtain ⟨trSub, hTrSub, hOutSub⟩ := hSub
                  simp only [Bind.bind, StateT.bind, StateT.run, hEr, Pure.pure]
                  cases rSub with
                  | error e => exact ⟨trSub, hTrSub, rfl, hOutSub⟩
                  | ok out' => exact ⟨trSub, hTrSub, hOutSub.1, hOutSub.2.1⟩)
            df.1 (none, out0) hTr1.1 hOut0Inv
          cases hL2 : (forIn df.1 (none, out0) step2 s2) with
          | mk fin s3 =>
            rw [StateT.run] at hLoop2; rw [hL2] at hLoop2; dsimp only at hLoop2
            obtain ⟨tr2, hTr2, hInv2⟩ := hLoop2
            let bodyM : StateM W (Except FsError (Array WalkEntry)) := do
              let __s ← forIn names (#[], #[]) step1
              let out := acc.push { root := relRoot, dirs := __s.1, files := __s.2 }
              let __s2 ← forIn __s.1 (none, out) step2
              match __s2.1 with
              | some r => pure r
              | none => pure (.ok __s2.2)
            refine fsTrace_pair_subst
              (fun r tr => exceptPred r
                (fun es =>
                  (∀ e ∈ es.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
                  es.size > 0 ∧
                  ∃ h eof, (.openat none fullDir.toUTF8 dirOpenFlags 0, .opened h) ∈ tr ∧
                    (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0)
                (fun e => nonLockErrOk e))
              (r2 := (bodyM s1).1) (s2 := (bodyM s1).2) ?_ ?_
            · dsimp only [bodyM, Bind.bind]
              let restCont : (Array String × Array String) → StateM W (Except FsError (Array WalkEntry)) :=
                fun __s =>
                  StateT.bind (forIn __s.1 (none, acc.push { root := relRoot, dirs := __s.1, files := __s.2 }) step2) fun __s2 =>
                    match __s2.1 with
                    | some r => pure r
                    | none => pure (.ok __s2.2)
              have hEqState : ∀ (m1 m2 : StateM W (Array String × Array String))
                  (k1 k2 : (Array String × Array String) → StateM W (Except FsError (Array WalkEntry))),
                  m1 = m2 → k1 = k2 →
                  ((StateT.bind m1 k1 s1).1, (StateT.bind m1 k1 s1).2) =
                  ((StateT.bind m2 k2 s1).1, (StateT.bind m2 k2 s1).2) := by
                rintro _ _ _ _ rfl rfl; rfl
              refine hEqState _ (forIn names (#[], #[]) step1) _ restCont (by congr 1) ?_
              · funext __s
                dsimp only [restCont]
                congr 1
                funext __s2 sX; cases __s2.1 <;> rfl
            · have hBodyRun : bodyM s1 = (match fin.1 with | some r => r | none => .ok fin.2, s3) := by
                dsimp only [out0] at hL2
                simp only [bodyM, Bind.bind, StateT.bind, hL1, hL2]
                cases fin.1 <;> rfl
              rw [hBodyRun]; dsimp only
              dsimp only [inv2] at hInv2
              have hTrAll := fsWorldTrace_append (fsWorldTrace_append hTr0 hTr1) hTr2
              refine ⟨(tr0 ++ tr1) ++ tr2, hTrAll, ?_⟩
              cases hOpt : fin.1 with
              | none =>
                rw [hOpt] at hInv2
                exact ⟨hInv2.1, hInv2.2, hFd, eof,
                  List.mem_append_left _ (List.mem_append_left _ hMemO0),
                  List.mem_append_left _ (List.mem_append_left _ hMemE0), hEz⟩
              | some r =>
                rw [hOpt] at hInv2
                cases r with
                | ok _ => exact False.elim hInv2
                | error e => exact hInv2.2

/-- Trace specification for `Internal.walkImplM`. -/
theorem walkImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (root : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.walkImplM ops.toNonLockFsOpsM root).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok entries =>
        (∀ e ∈ entries.toList, List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList) ∧
        entries.size > 0 ∧ WalkRootTrace root tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.walkImplM
  have hS := scoped_stat hOps true root hWf
  cases hEs : (ops.stat true root s) with
  | mk rS s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    simp only [Bind.bind, StateT.bind, StateT.run, hEs]
    cases rS with
    | error e =>
      have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
      simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1, hNe1⟩
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      by_cases hNd : (st.kind != .dir) = true
      · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨rawSt, hmS, hEqSt⟩ := hOut1
        have hDir : rawSt.kind = .dir := rawKind_dir_of_toFileStat hEqSt (by
          cases hK : st.kind <;> rw [hK] at hNd <;> first | rfl | exact absurd (by decide) hNd)
        have hW := walkGoM_trace hOps 4096 root "." #[] (fun _ h => nomatch h) hTr1.1
        cases hEw : (Internal.walkGoM ops.toNonLockFsOpsM root "." #[] 4096 s1) with
        | mk rW s2 =>
          rw [StateT.run] at hW; rw [hEw] at hW; dsimp only at hW
          obtain ⟨tr2, hTr2, hOut2⟩ := hW
          refine ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, ?_⟩
          cases rW with
          | error e => exact ⟨hOut2, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩
          | ok es =>
            obtain ⟨hPw, hSz, hFd, eof, hMemO, hMemE, hEz⟩ := hOut2
            exact ⟨hPw, hSz, ⟨rawSt, List.mem_append_left _ hmS, hDir⟩,
              ⟨hFd, eof, List.mem_append_right _ hMemO, List.mem_append_right _ hMemE, hEz⟩⟩

/-- Trace specification for `Internal.globImplM`. -/
theorem globImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (root pattern : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.globImplM ops.toNonLockFsOpsM root pattern).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      exceptPred r.1
        (fun xs => List.Pairwise (· ≤ ·) xs.toList ∧ WalkRootTrace root tr)
        (fun e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput)) := by
  unfold Internal.globImplM
  have hMapGlob : ∀ (ge : LeanSwe.Glob.GlobError),
      nonLockErrOk (Internal.mapGlobError pattern ge) ∧ (Internal.mapGlobError pattern ge).kind = .invalidInput := by
    intro ge; simp only [Internal.mapGlobError, Internal.nonEmptyMsg, nonLockErrOk]
    refine ⟨⟨?_, by decide⟩, trivial⟩
    by_cases hE : ge.message.isEmpty = true
    · simp [hE]
    · simp only [hE, Bool.false_eq_true, ↓reduceIte]; intro h; rw [h] at hE; exact hE rfl
  cases hV : LeanSwe.Glob.validate pattern with
  | error ge =>
    simp only [Pure.pure, StateT.pure, StateT.run, exceptPred]
    have hM := hMapGlob ge; exact ⟨[], fsWorldTrace_nil hWf, hM.1, Or.inr hM.2⟩
  | ok u =>
    cases u
    have hW := walkImplM_trace hOps root hWf
    cases hEw : (Internal.walkImplM ops.toNonLockFsOpsM root s) with
    | mk rW s1 =>
      rw [StateT.run] at hW; rw [hEw] at hW; dsimp only at hW
      obtain ⟨tr1, hTr1, hOut1⟩ := hW
      simp only [Bind.bind, StateT.bind, StateT.run, hEw]
      cases rW with
      | error e => simp only [Pure.pure, StateT.pure, exceptPred]; exact ⟨tr1, hTr1, hOut1.1, Or.inl hOut1.2⟩
      | ok entries =>
        dsimp only
        let candStep : WalkEntry → Array String → StateM W (ForInStep (Array String)) :=
          fun entry candidates => do
            let candidates ← forIn entry.dirs candidates fun d candidates =>
              pure (ForInStep.yield (candidates.push (if entry.root == "." then d else Internal.join entry.root d)))
            let candidates ← forIn entry.files candidates fun f candidates =>
              pure (ForInStep.yield (candidates.push (if entry.root == "." then f else Internal.join entry.root f)))
            pure (ForInStep.yield candidates)
        have hCandConst : ((forIn entries (#[] : Array String) candStep).run s1).2 = s1 := by
          refine array_forIn_state_const candStep (fun entry cands sX => ?_) entries #[] s1
          dsimp only [candStep]
          let sDir : String → Array String → StateM W (ForInStep (Array String)) :=
            fun d c => pure (ForInStep.yield (c.push (if entry.root == "." then d else Internal.join entry.root d)))
          let sFile : String → Array String → StateM W (ForInStep (Array String)) :=
            fun f c => pure (ForInStep.yield (c.push (if entry.root == "." then f else Internal.join entry.root f)))
          have hC1 := array_forIn_state_const sDir (fun _ _ _ => rfl) entry.dirs cands sX
          cases h1 : (forIn entry.dirs cands sDir sX) with
          | mk c1 sA =>
            rw [StateT.run] at hC1; rw [h1] at hC1; dsimp only at hC1; subst hC1
            have hC2 := array_forIn_state_const sFile (fun _ _ _ => rfl) entry.files c1 sA
            simp only [Bind.bind, StateT.bind, StateT.run]
            have h1' : forIn entry.dirs cands sDir sA = (c1, sA) := h1
            dsimp only [sDir] at h1'; rw [h1']; dsimp only
            cases h2 : (forIn entry.files c1 sFile sA) with
            | mk c2 sB =>
              rw [StateT.run] at hC2; rw [h2] at hC2; dsimp only at hC2
              exact hC2
        cases hCand : (forIn entries (#[] : Array String) candStep s1) with
        | mk cands sC =>
          rw [StateT.run] at hCandConst; rw [hCand] at hCandConst; dsimp only at hCandConst; subst hCandConst
          let globCont : Array String → StateM W (Except FsError (Array String)) := fun c =>
            match LeanSwe.Glob.filter pattern c with
            | .error e => pure (.error (Internal.mapGlobError pattern e))
            | .ok matched => pure (.ok (matched.toList.mergeSort (· ≤ ·)).toArray)
          refine fsTrace_pair_subst
            (fun r tr => exceptPred r
              (fun xs => List.Pairwise (· ≤ ·) xs.toList ∧ WalkRootTrace root tr)
              (fun e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput)))
            (r2 := (StateT.bind (forIn entries (#[] : Array String) candStep) globCont sC).1)
            (s2 := (StateT.bind (forIn entries (#[] : Array String) candStep) globCont sC).2) ?_ ?_
          · congr 1
          · simp only [Bind.bind, StateT.bind, hCand, globCont]
            cases hFlt : LeanSwe.Glob.filter pattern cands with
            | error ge =>
              simp only [Pure.pure, exceptPred]
              have hM := hMapGlob ge; exact ⟨tr1, hTr1, hM.1, Or.inr hM.2⟩
            | ok matched =>
              simp only [Pure.pure, exceptPred]
              exact ⟨tr1, hTr1, by simpa using list_mergeSort_str_le matched.toList, hOut1.2.2⟩

/-- Trace specification for `Internal.touchImplM`. -/
theorem touchImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (existOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.touchImplM ops.toNonLockFsOpsM path existOk).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () =>
        (existOk = true ∧ ∃ tr1 tr2, tr = tr1 ++ tr2 ∧ WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 ByteArray.empty tr2) ∨
        (∃ tr1 tr2, tr = tr1 ++ tr2 ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ tr1 ∧
          WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 ByteArray.empty tr2)
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.touchImplM
  have hS := scoped_stat hOps false path hWf
  cases hEs : (ops.stat false path s) with
  | mk rS s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    simp only [Bind.bind, StateT.bind, StateT.run, hEs]
    cases rS with
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      cases existOk with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hApp : ∀ {sX : W} {trP : List KernelStep}, FsWorldTrace (proj s) trP (proj sX) → trP ≠ [] →
            let q := (ops.appendText path "").run sX
            ∃ tr, FsWorldTrace (proj s) tr (proj q.2) ∧
              match q.1 with
              | .ok () =>
                (True ∧ ∃ trA trB, tr = trA ++ trB ∧ WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 ByteArray.empty trB) ∨
                (∃ trA trB, tr = trA ++ trB ∧ (.fstatat none path.toUTF8 { symlinkNofollow := true }, .err Errno.ENOENT) ∈ trA ∧
                  WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 ByteArray.empty trB)
              | .error e => nonLockErrOk e ∧ tr ≠ [] := by
          intro sX trP hTrP hNeP
          have hAp := scoped_appendText hOps path "" hTrP.1
          cases hEap : (ops.appendText path "" sX) with
          | mk rAp sY =>
            rw [StateT.run] at hAp; rw [hEap] at hAp; dsimp only at hAp
            obtain ⟨trAp, hTrAp, _, hOutAp⟩ := hAp
            simp only [StateT.run, hEap]
            refine ⟨trP ++ trAp, fsWorldTrace_append hTrP hTrAp, ?_⟩
            cases rAp with
            | error e => exact ⟨hOutAp.1, fun h => hNeP (List.append_eq_nil_iff.mp h).1⟩
            | ok u => cases u; exact Or.inl ⟨trivial, trP, trAp, rfl, hOutAp⟩
        by_cases hD : (st.kind == .dir) = true
        · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
        · by_cases hSym : (st.kind == .symlink) = true
          · simp only [hD, Bool.false_eq_true, ↓reduceIte, hSym]
            have hS2 := scoped_stat hOps true path hTr1.1
            cases hEs2 : (ops.stat true path s1) with
            | mk rS2 s2 =>
              rw [StateT.run] at hS2; rw [hEs2] at hS2; dsimp only at hS2
              obtain ⟨tr2, hTr2, _, _⟩ := hS2
              simp only [Bind.bind, StateT.bind, hEs2]
              have hTr12 := fsWorldTrace_append hTr1 hTr2
              have hNe12 : tr1 ++ tr2 ≠ [] := fun h => hNe1 (List.append_eq_nil_iff.mp h).1
              cases rS2 with
              | error _ => exact hApp hTr12 hNe12
              | ok tgtSt =>
                by_cases hTd : (tgtSt.kind == .dir) = true
                · simp only [hTd, ↓reduceIte, Pure.pure, StateT.pure]
                  exact ⟨tr1 ++ tr2, hTr12, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe12⟩
                · simp only [hTd, Bool.false_eq_true, ↓reduceIte]; exact hApp hTr12 hNe12
          · simp only [hD, Bool.false_eq_true, ↓reduceIte, hSym]; exact hApp hTr1 hNe1
    | error e =>
      obtain ⟨hNl1, err, hmErr, hNfImp⟩ := hOut1
      have hNe1 : tr1 ≠ [] := fun hN => by rw [hN] at hmErr; cases hmErr
      by_cases hNf : (e.kind == .notFound) = true
      · simp only [hNf, ↓reduceIte]
        have hErrEq : err = Errno.ENOENT := hNfImp ((fsErrorKind_beq_iff_eq _ _).mp hNf)
        subst hErrEq
        have hW := scoped_writeBytes hOps path ByteArray.empty hTr1.1
        cases hEw : (ops.writeBytes path ByteArray.empty s1) with
        | mk rW s2 =>
          rw [StateT.run] at hW; rw [hEw] at hW; dsimp only at hW
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hW
          refine ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, ?_⟩
          cases rW with
          | error we => exact ⟨hOut2.1, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩
          | ok u => cases u; exact Or.inr ⟨tr1, tr2, rfl, hmErr, hOut2⟩
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨tr1, hTr1, hNl1, hNe1⟩

end LeanSwe.Fs.Proofs

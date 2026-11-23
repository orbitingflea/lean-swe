import LeanSwe.Fs.Proofs.FsRefinesHelpers1

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Trace specification for `Internal.forEachChildM`. -/
theorem forEachChildM_trace {W : Type} {proj : W → FsWorld}
    (f : String → StateM W (Except FsError Unit))
    (hf : ∀ n {s : W}, fsWorldWf (proj s) = true →
      let r := (f n).run s
      ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ match r.1 with | .ok () => True | .error e => nonLockErrOk e)
    (xs : List String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.forEachChildM f xs).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ match r.1 with | .ok () => True | .error e => nonLockErrOk e := by
  induction xs generalizing s with
  | nil =>
    simp only [Internal.forEachChildM, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, trivial⟩
  | cons n rest ih =>
    unfold Internal.forEachChildM
    have h1 := hf n hWf
    cases hEq : (f n s) with
    | mk r1 s1 =>
      rw [StateT.run] at h1; rw [hEq] at h1; dsimp only at h1
      obtain ⟨tr1, hTr1, hOut1⟩ := h1
      simp only [Bind.bind, StateT.bind, StateT.run, hEq]
      cases r1 with
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1⟩
      | ok u =>
        cases u; dsimp only
        have h2 := ih hTr1.1
        cases hEq2 : (Internal.forEachChildM f rest s1) with
        | mk r2 s2 =>
          rw [StateT.run] at h2; rw [hEq2] at h2; dsimp only at h2
          obtain ⟨tr2, hTr2, hOut2⟩ := h2
          dsimp only
          exact ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, hOut2⟩

/-- Trace specification for `Internal.rmtreeGoM`. -/
theorem rmtreeGoM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.RefinesStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (fuel : Nat) (dir : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.rmtreeGoM ops.toNonLockFsOpsM dir fuel).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      exceptPred r.1 (fun _ => UnlinkTrace none dir.toUTF8 true tr) (fun e => nonLockErrOk e) := by
  induction fuel generalizing dir s with
  | zero =>
    simp only [Internal.rmtreeGoM, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, nonEmpty_append_left (by decide), by intro h; cases h⟩
  | succ k ih =>
    unfold Internal.rmtreeGoM
    have hL := listDirSortedM_trace hOps dir hWf
    cases hEl : (Internal.listDirSortedM ops.toNonLockFsOpsM dir s) with
    | mk rL s1 =>
      rw [StateT.run] at hL; rw [hEl] at hL; dsimp only at hL
      obtain ⟨tr1, hTr1, _, hOut1⟩ := hL
      simp only [Bind.bind, StateT.bind, StateT.run, hEl]
      cases rL with
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1⟩
      | ok names =>
        dsimp only
        let childFn : String → StateM W (Except FsError Unit) := fun n => do
          let child := join dir n
          match ← ops.stat false child with
          | .error e => return .error e
          | .ok st =>
            if st.kind == .dir then Internal.rmtreeGoM ops.toNonLockFsOpsM child k
            else ops.unlinkFile child
        have hF := forEachChildM_trace childFn
          (fun n sX hWX => by
            dsimp only [childFn]
            have hS := scoped_stat hOps false (join dir n) hWX
            cases hEs : (ops.stat false (join dir n) sX) with
            | mk rS sY =>
              rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
              obtain ⟨trS, hTrS, _, hOutS⟩ := hS
              simp only [Bind.bind, StateT.bind, StateT.run, hEs]
              cases rS with
              | error e => simp only [Pure.pure, StateT.pure]; exact ⟨trS, hTrS, hOutS.1⟩
              | ok st =>
                by_cases hD : (st.kind == .dir) = true
                · simp only [hD, ↓reduceIte]
                  have hSub := ih (join dir n) hTrS.1
                  cases hEr : (Internal.rmtreeGoM ops.toNonLockFsOpsM (join dir n) k sY) with
                  | mk rSub sZ =>
                    rw [StateT.run] at hSub; rw [hEr] at hSub; dsimp only at hSub
                    obtain ⟨trSub, hTrSub, hOutSub⟩ := hSub
                    dsimp only
                    exact ⟨trS ++ trSub, fsWorldTrace_append hTrS hTrSub, by cases rSub with | ok u => cases u; trivial | error e => exact hOutSub⟩
                · simp only [hD, Bool.false_eq_true, ↓reduceIte]
                  have hU := scoped_unlinkFile hOps (join dir n) hTrS.1
                  cases hEu : (ops.unlinkFile (join dir n) sY) with
                  | mk rU sZ =>
                    rw [StateT.run] at hU; rw [hEu] at hU; dsimp only at hU
                    obtain ⟨trU, hTrU, _, hOutU⟩ := hU
                    dsimp only
                    exact ⟨trS ++ trU, fsWorldTrace_append hTrS hTrU, by cases rU with | ok u => cases u; trivial | error e => exact hOutU.1⟩)
          names.toList hTr1.1
        cases hEf : (Internal.forEachChildM childFn names.toList s1) with
        | mk rF s2 =>
          rw [StateT.run] at hF; rw [hEf] at hF; dsimp only at hF
          obtain ⟨tr2, hTr2, hOut2⟩ := hF
          let contFn : Except FsError Unit → StateM W (Except FsError Unit) := fun x =>
            match x with | .error e => pure (.error e) | .ok () => ops.removeDir dir
          refine fsTrace_pair_subst
            (fun r tr => exceptPred r (fun _ => UnlinkTrace none dir.toUTF8 true tr) (fun e => nonLockErrOk e))
            (r2 := (StateT.bind (Internal.forEachChildM childFn names.toList) contFn s1).1)
            (s2 := (StateT.bind (Internal.forEachChildM childFn names.toList) contFn s1).2) ?_ ?_
          · congr 1
          · simp only [Bind.bind, StateT.bind, hEf, contFn]
            have hTr12 := fsWorldTrace_append hTr1 hTr2
            cases rF with
            | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, hTr12, hOut2⟩
            | ok u =>
              cases u; dsimp only
              have hRm := scoped_removeDir hOps dir hTr2.1
              cases hErm : (ops.removeDir dir s2) with
              | mk rRm s3 =>
                rw [StateT.run] at hRm; rw [hErm] at hRm; dsimp only at hRm
                obtain ⟨tr3, hTr3, _, hOut3⟩ := hRm
                dsimp only
                refine ⟨(tr1 ++ tr2) ++ tr3, fsWorldTrace_append hTr12 hTr3, ?_⟩
                cases rRm with
                | ok u2 => cases u2; exact unlinkTrace_append_right hOut3
                | error e => exact hOut3.1

/-- Trace specification for `Internal.resolveApproxGoM`. -/
theorem resolveApproxGoM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.RefinesStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (fuel : Nat) (cur : String) (tail : List String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.resolveApproxGoM ops.toNonLockFsOpsM cur tail fuel).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) := by
  induction fuel generalizing cur tail s with
  | zero =>
    simp only [Internal.resolveApproxGoM, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf⟩
  | succ k ih =>
    unfold Internal.resolveApproxGoM
    have hR := scoped_realPath hOps cur hWf
    cases hEr : (ops.realPath cur s) with
    | mk rR s1 =>
      rw [StateT.run] at hR; rw [hEr] at hR; dsimp only at hR
      obtain ⟨tr1, hTr1, _, _⟩ := hR
      simp only [Bind.bind, StateT.bind, StateT.run, hEr]
      cases rR with
      | ok _ => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1⟩
      | error _ =>
        cases Model.parent cur with
        | none => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1⟩
        | some par =>
          cases Model.name cur with
          | none => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1⟩
          | some seg =>
            dsimp only
            have h2 := ih par (seg :: tail) hTr1.1
            cases hEr2 : (Internal.resolveApproxGoM ops.toNonLockFsOpsM par (seg :: tail) k s1) with
            | mk r2 s2 =>
              rw [StateT.run] at h2; rw [hEr2] at h2; dsimp only at h2
              obtain ⟨tr2, hTr2⟩ := h2
              exact ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2⟩

/-- Trace specification for `Internal.copyFileImplM`. -/
theorem copyFileImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.RefinesStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (src dst : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.copyFileImplM ops.toNonLockFsOpsM src dst).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () =>
        ∃ bs tr1 tr2 tr3, tr = tr1 ++ tr2 ++ tr3 ∧
          ReadRegularTrace none src.toUTF8 readOpenFlags bs tr2 ∧
          WriteFileTrace none dst.toUTF8 writeOpenFlags 0o666 bs tr3
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.copyFileImplM
  have hS := scoped_stat hOps true src hWf
  cases hEs : (ops.stat true src s) with
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
      by_cases hD : (st.kind == .dir) = true
      · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      · simp only [hD, Bool.false_eq_true, ↓reduceIte]
        have hR := scoped_readBytes hOps src hTr1.1
        cases hEr : (ops.readBytes src s1) with
        | mk rR s2 =>
          rw [StateT.run] at hR; rw [hEr] at hR; dsimp only at hR
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hR
          simp only [Bind.bind, StateT.bind, hEr]
          have hTr12 := fsWorldTrace_append hTr1 hTr2
          have hNe12 : tr1 ++ tr2 ≠ [] := fun h => hNe1 (List.append_eq_nil_iff.mp h).1
          cases rR with
          | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, hTr12, hOut2.1, hNe12⟩
          | ok bs =>
            dsimp only
            have hW := scoped_writeBytes hOps dst bs hTr2.1
            cases hEw : (ops.writeBytes dst bs s2) with
            | mk rW s3 =>
              rw [StateT.run] at hW; rw [hEw] at hW; dsimp only at hW
              obtain ⟨tr3, hTr3, _, hOut3⟩ := hW
              dsimp only
              refine ⟨(tr1 ++ tr2) ++ tr3, fsWorldTrace_append hTr12 hTr3, ?_⟩
              cases rW with
              | ok u => cases u; exact ⟨bs, tr1, tr2, tr3, rfl, hOut2, hOut3⟩
              | error e => exact ⟨hOut3.1, fun h => hNe12 (List.append_eq_nil_iff.mp h).1⟩

/-- Trace specification for `Internal.copyTreeGoM`. -/
theorem copyTreeGoM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.RefinesStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (fuel : Nat) (src dst : String) (dirsExistOk : Bool) (visited : List String)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.copyTreeGoM ops.toNonLockFsOpsM src dst dirsExistOk visited fuel).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () =>
        (∃ rawSt, (.fstatat none src.toUTF8 { symlinkNofollow := false }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir) ∧
        MkdirOkTrace dst dirsExistOk tr
      | .error e => nonLockErrOk e := by
  induction fuel generalizing src dst visited s with
  | zero =>
    simp only [Internal.copyTreeGoM, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, nonEmpty_append_left (by decide), by intro h; cases h⟩
  | succ k ih =>
    unfold Internal.copyTreeGoM
    have hS := scoped_stat hOps true src hWf
    cases hEs : (ops.stat true src s) with
    | mk rS s1 =>
      rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
      obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
      simp only [Bind.bind, StateT.bind, StateT.run, hEs]
      cases rS with
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1⟩
      | ok st =>
        by_cases hNd : (st.kind != .dir) = true
        · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨tr1, hTr1, nonEmpty_append_left (by decide), by intro h; cases h⟩
        · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨rawSt, hmS, hEqSt⟩ := hOut1
          have hDir : rawSt.kind = .dir := rawKind_dir_of_toFileStat hEqSt (by
            cases hK : st.kind <;> rw [hK] at hNd <;> first | rfl | exact absurd (by decide) hNd)
          have hRp := scoped_realPath hOps src hTr1.1
          cases hErp : (ops.realPath src s1) with
          | mk rRp s2 =>
            rw [StateT.run] at hRp; rw [hErp] at hRp; dsimp only at hRp
            obtain ⟨tr2, hTr2, _, hOut2⟩ := hRp
            simp only [Bind.bind, StateT.bind, hErp]
            have hTr12 := fsWorldTrace_append hTr1 hTr2
            cases rRp with
            | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, hTr12, hOut2.1⟩
            | ok canon =>
              by_cases hVis : canon ∈ visited
              · simp only [hVis, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨tr1 ++ tr2, hTr12, nonEmpty_append_left (by decide), by intro h; cases h⟩
              · simp only [hVis, ↓reduceIte]
                have hL := listDirSortedM_trace hOps src hTr2.1
                cases hEl : (Internal.listDirSortedM ops.toNonLockFsOpsM src s2) with
                | mk rL s3 =>
                  rw [StateT.run] at hL; rw [hEl] at hL; dsimp only at hL
                  obtain ⟨tr3, hTr3, _, hOut3⟩ := hL
                  simp only [Bind.bind, StateT.bind, hEl]
                  have hTr123 := fsWorldTrace_append hTr12 hTr3
                  cases rL with
                  | error e => simp only [Pure.pure, StateT.pure]; exact ⟨(tr1 ++ tr2) ++ tr3, hTr123, hOut3.1⟩
                  | ok names =>
                    have hMk := mkdirImplM_trace hOps dst true dirsExistOk hTr3.1
                    cases hEmk : (Internal.mkdirImplM ops.toNonLockFsOpsM dst true dirsExistOk s3) with
                    | mk rMk s4 =>
                      rw [StateT.run] at hMk; rw [hEmk] at hMk; dsimp only at hMk
                      obtain ⟨tr4, hTr4, hOut4⟩ := hMk
                      simp only [Bind.bind, StateT.bind, hEmk]
                      have hTr1234 := fsWorldTrace_append hTr123 hTr4
                      cases rMk with
                      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨((tr1 ++ tr2) ++ tr3) ++ tr4, hTr1234, hOut4.1⟩
                      | ok u =>
                        cases u; dsimp only
                        let childFn : String → StateM W (Except FsError Unit) := fun n => do
                          let sChild := Model.join src n
                          let dChild := Model.join dst n
                          match ← ops.stat true sChild with
                          | .error e => return .error e
                          | .ok childSt =>
                            if childSt.kind == .dir then
                              Internal.copyTreeGoM ops.toNonLockFsOpsM sChild dChild dirsExistOk (canon :: visited) k
                            else
                              Internal.copyFileImplM ops.toNonLockFsOpsM sChild dChild
                        have hFc := forEachChildM_trace childFn
                          (fun n sX hWX => by
                            dsimp only [childFn]
                            have hSc := scoped_stat hOps true (Model.join src n) hWX
                            cases hEsc : (ops.stat true (Model.join src n) sX) with
                            | mk rSc sY =>
                              rw [StateT.run] at hSc; rw [hEsc] at hSc; dsimp only at hSc
                              obtain ⟨trSc, hTrSc, _, hOutSc⟩ := hSc
                              simp only [Bind.bind, StateT.bind, StateT.run, hEsc]
                              cases rSc with
                              | error e => simp only [Pure.pure, StateT.pure]; exact ⟨trSc, hTrSc, hOutSc.1⟩
                              | ok childSt =>
                                by_cases hCd : (childSt.kind == .dir) = true
                                · simp only [hCd, ↓reduceIte]
                                  have hSub := ih (Model.join src n) (Model.join dst n) (canon :: visited) hTrSc.1
                                  cases hEsub : (Internal.copyTreeGoM ops.toNonLockFsOpsM (Model.join src n) (Model.join dst n) dirsExistOk (canon :: visited) k sY) with
                                  | mk rSub sZ =>
                                    rw [StateT.run] at hSub; rw [hEsub] at hSub; dsimp only at hSub
                                    obtain ⟨trSub, hTrSub, hOutSub⟩ := hSub
                                    dsimp only
                                    exact ⟨trSc ++ trSub, fsWorldTrace_append hTrSc hTrSub, by cases rSub with | ok u => cases u; trivial | error e => exact hOutSub⟩
                                · simp only [hCd, Bool.false_eq_true, ↓reduceIte]
                                  have hCf := copyFileImplM_trace hOps (Model.join src n) (Model.join dst n) hTrSc.1
                                  cases hEcf : (Internal.copyFileImplM ops.toNonLockFsOpsM (Model.join src n) (Model.join dst n) sY) with
                                  | mk rCf sZ =>
                                    rw [StateT.run] at hCf; rw [hEcf] at hCf; dsimp only at hCf
                                    obtain ⟨trCf, hTrCf, hOutCf⟩ := hCf
                                    dsimp only
                                    exact ⟨trSc ++ trCf, fsWorldTrace_append hTrSc hTrCf, by cases rCf with | ok u => cases u; trivial | error e => exact hOutCf.1⟩)
                          names.toList hTr4.1
                        cases hEfc : (Internal.forEachChildM childFn names.toList s4) with
                        | mk rFc s5 =>
                          rw [StateT.run] at hFc; rw [hEfc] at hFc; dsimp only at hFc
                          obtain ⟨tr5, hTr5, hOut5⟩ := hFc
                          refine ⟨(((tr1 ++ tr2) ++ tr3) ++ tr4) ++ tr5, fsWorldTrace_append hTr1234 hTr5, ?_⟩
                          cases rFc with
                          | error e => exact hOut5
                          | ok u2 =>
                            cases u2
                            refine ⟨⟨rawSt, ?_, hDir⟩, mkdirOkTrace_append_left (mkdirOkTrace_append_right hOut4)⟩
                            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmS)))

/-- General invariant-preserving trace lemma for `forIn` over `List` in `StateM W`. -/
theorem list_forIn_state_inv {W α β : Type} {proj : W → FsWorld}
    (inv : β → List α → Prop)
    (step : α → β → StateM W (ForInStep β))
    (hStep : ∀ a rest b s, fsWorldWf (proj s) = true → inv b (a :: rest) →
      let r := (step a b).run s
      ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
        match r.1 with
        | .done b' => inv b' []
        | .yield b' => inv b' rest)
    (xs : List α) (b : β) {s : W} (hWf : fsWorldWf (proj s) = true) (hInv : inv b xs) :
    let r := (forIn xs b step).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ inv r.1 [] := by
  induction xs generalizing b s with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, hInv⟩
  | cons a rest ih =>
    rw [List.forIn_cons]
    have h1 := hStep a rest b s hWf hInv
    cases hR : (step a b s) with
    | mk st s1 =>
      rw [StateT.run] at h1; rw [hR] at h1; dsimp only at h1
      obtain ⟨tr1, hTr1, hInv1⟩ := h1
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases st with
      | done b' => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hInv1⟩
      | yield b' =>
        dsimp only
        have h2 := ih b' hTr1.1 hInv1
        cases hR2 : (forIn rest b' step s1) with
        | mk b2 s2 =>
          rw [StateT.run] at h2; rw [hR2] at h2; dsimp only at h2
          obtain ⟨tr2, hTr2, hInv2⟩ := h2
          dsimp only
          exact ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, hInv2⟩

/-- General invariant-preserving trace lemma for `forIn` over `Array` in `StateM W`. -/
theorem array_forIn_state_inv {W α β : Type} {proj : W → FsWorld}
    (inv : β → List α → Prop)
    (step : α → β → StateM W (ForInStep β))
    (hStep : ∀ a rest b s, fsWorldWf (proj s) = true → inv b (a :: rest) →
      let r := (step a b).run s
      ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
        match r.1 with
        | .done b' => inv b' []
        | .yield b' => inv b' rest)
    (arr : Array α) (b : β) {s : W} (hWf : fsWorldWf (proj s) = true) (hInv : inv b arr.toList) :
    let r := (forIn arr b step).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ inv r.1 [] := by
  rw [← Array.forIn_toList]
  exact list_forIn_state_inv inv step hStep arr.toList b hWf hInv

end LeanSwe.Fs.Proofs

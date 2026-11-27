import LeanSweProofs.Fs.Proofs.FsRefinesAtomic
import LeanSweProofs.Fs.Proofs.FsRefinesPure
import LeanSweProofs.Fs.Proofs.SysBridgeCaps

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

private theorem readText_step {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execFsStep (Internal.mkApiFromScopedRawM ops) (.readText path)).run s
    allowedFsStep (proj s) (.readText path) r.1 (proj r.2) := by
  simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.readTextImplM,
    Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind]
  have hR := scoped_readBytes hOps path hWf
  cases hEr : (ops.readBytes path s) with
  | mk rR s1 =>
    rw [StateT.run] at hR; rw [hEr] at hR; dsimp only at hR
    obtain ⟨tr, hTr, _, hOut⟩ := hR
    cases rR with
    | error e =>
      simp only [Pure.pure, StateT.pure, allowedFsStep]
      exact ⟨tr, hTr, hOut⟩
    | ok bs =>
      dsimp only
      cases hU : String.fromUTF8? bs with
      | some str =>
        simp only [Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr, hTr, bs, hU, hOut⟩
      | none =>
        simp only [Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr, hTr, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inl (readRegularTrace_nonEmpty hOut)⟩

private theorem unlink_step {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (missingOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execFsStep (Internal.mkApiFromScopedRawM ops) (.unlink path missingOk)).run s
    allowedFsStep (proj s) (.unlink path missingOk) r.1 (proj r.2) := by
  simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.unlinkImplM,
    Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind]
  have hS := scoped_stat hOps false path hWf
  cases hEs : (ops.stat false path s) with
  | mk rS s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    cases rS with
    | error e =>
      obtain ⟨hNl1, err, hmErr, hNfImp⟩ := hOut1
      have hNe1 : tr1 ≠ [] := fun hN => by rw [hN] at hmErr; cases hmErr
      by_cases hM : ((e.kind == .notFound) && missingOk) = true
      · simp only [hM, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        have ⟨hNf, hMk⟩ := (Bool.and_eq_true _ _).mp hM
        have hErrEq : err = Errno.ENOENT := hNfImp ((fsErrorKind_beq_iff_eq _ _).mp hNf)
        subst hErrEq
        exact ⟨tr1, hTr1, Or.inr ⟨hMk, hmErr⟩⟩
      · simp only [hM, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr1, hTr1, hNl1, hNe1⟩
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      by_cases hD : (st.kind == .dir) = true
      · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      · simp only [hD, Bool.false_eq_true, ↓reduceIte]
        have hU := scoped_unlinkFile hOps path hTr1.1
        cases hEu : (ops.unlinkFile path s1) with
        | mk rU s2 =>
          rw [StateT.run] at hU; rw [hEu] at hU; dsimp only at hU
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hU
          simp only [Pure.pure, allowedFsStep]
          refine ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, ?_⟩
          cases rU with
          | ok u => cases u; exact Or.inl (unlinkTrace_append_right hOut2)
          | error e => exact ⟨hOut2.1, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩

private theorem rmtree_step {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (ignoreMissing : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execFsStep (Internal.mkApiFromScopedRawM ops) (.rmtree path ignoreMissing)).run s
    allowedFsStep (proj s) (.rmtree path ignoreMissing) r.1 (proj r.2) := by
  simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.rmtreeImplM,
    Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind]
  have hS := scoped_stat hOps false path hWf
  cases hEs : (ops.stat false path s) with
  | mk rS s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    cases rS with
    | error e =>
      obtain ⟨hNl1, err, hmErr, hNfImp⟩ := hOut1
      have hNe1 : tr1 ≠ [] := fun hN => by rw [hN] at hmErr; cases hmErr
      by_cases hM : ((e.kind == .notFound) && ignoreMissing) = true
      · simp only [hM, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        have ⟨hNf, hIg⟩ := (Bool.and_eq_true _ _).mp hM
        have hErrEq : err = Errno.ENOENT := hNfImp ((fsErrorKind_beq_iff_eq _ _).mp hNf)
        subst hErrEq
        exact ⟨tr1, hTr1, Or.inr ⟨hIg, hmErr⟩⟩
      · simp only [hM, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr1, hTr1, hNl1, hNe1⟩
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      by_cases hNd : (st.kind != .dir) = true
      · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
        have hGo := rmtreeGoM_trace hOps 4096 path hTr1.1
        cases hEg : (Internal.rmtreeGoM ops.toNonLockFsOpsM path 4096 s1) with
        | mk rG s2 =>
          rw [StateT.run] at hGo; rw [hEg] at hGo; dsimp only at hGo
          obtain ⟨tr2, hTr2, hOut2⟩ := hGo
          simp only [Pure.pure, allowedFsStep]
          refine ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, ?_⟩
          cases rG with
          | ok u => cases u; exact Or.inl (unlinkTrace_append_right hOut2)
          | error e => exact ⟨hOut2, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩

private theorem copyTree_step {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (src dst : String) (dirsExistOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execFsStep (Internal.mkApiFromScopedRawM ops) (.copyTree src dst dirsExistOk)).run s
    allowedFsStep (proj s) (.copyTree src dst dirsExistOk) r.1 (proj r.2) := by
  simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.copyTreeImplM,
    Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind]
  have hS := scoped_stat hOps true src hWf
  cases hEs : (ops.stat true src s) with
  | mk rS s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    cases rS with
    | error e =>
      have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
      simp only [Pure.pure, StateT.pure, allowedFsStep]; exact ⟨tr1, hTr1, hOut1.1, hNe1⟩
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      by_cases hNd : (st.kind != .dir) = true
      · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
      · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
        have hRp := scoped_realPath hOps src hTr1.1
        cases hErp : (ops.realPath src s1) with
        | mk rRp s2 =>
          rw [StateT.run] at hRp; rw [hErp] at hRp; dsimp only at hRp
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hRp
          have hTr12 := fsWorldTrace_append hTr1 hTr2
          have hNe12 : tr1 ++ tr2 ≠ [] := fun h => hNe1 (List.append_eq_nil_iff.mp h).1
          simp only [StateT.bind, hErp]
          cases rRp with
          | error e =>
            simp only [Pure.pure, allowedFsStep]; exact ⟨tr1 ++ tr2, hTr12, hOut2.1, hNe12⟩
          | ok srcCanon =>
            have hAfterAbs : ∀ (dstAbs : String) {s3 : W} {trP : List KernelStep},
                FsWorldTrace (proj s) trP (proj s3) → trP ≠ [] →
                let q := (FsStepOut.unit <$> ((do
                  let dstCanon ← Internal.resolveApproxGoM ops.toNonLockFsOpsM dstAbs [] (dstAbs.toList.length + 1)
                  if dstCanon == srcCanon || srcCanon == "/" || (srcCanon.toList ++ ['/']).isPrefixOf dstCanon.toList then
                    return (.error { kind := .invalidInput, path := some dst, message := s!"cannot copy directory into itself: {dst}" } : Except FsError Unit)
                  Internal.copyTreeGoM ops.toNonLockFsOpsM src dst dirsExistOk [] 4096) : StateM W (Except FsError Unit))).run s3
                allowedFsStep (proj s) (.copyTree src dst dirsExistOk) q.1 (proj q.2) := by
              intro dstAbs s3 trP hTrP hNeP
              have hRa := resolveApproxGoM_trace hOps (dstAbs.toList.length + 1) dstAbs [] hTrP.1
              cases hEra : (Internal.resolveApproxGoM ops.toNonLockFsOpsM dstAbs [] (dstAbs.toList.length + 1) s3) with
              | mk dstCanon s4 =>
                rw [StateT.run] at hRa; rw [hEra] at hRa; dsimp only at hRa
                obtain ⟨trA, hTrA⟩ := hRa
                simp only [Functor.map, StateT.map, Bind.bind, StateT.bind, StateT.run, hEra]
                have hTrPA := fsWorldTrace_append hTrP hTrA
                have hNePA : trP ++ trA ≠ [] := fun h => hNeP (List.append_eq_nil_iff.mp h).1
                by_cases hSelf : (dstCanon == srcCanon || srcCanon == "/" || (srcCanon.toList ++ ['/']).isPrefixOf dstCanon.toList) = true
                · simp only [hSelf, ↓reduceIte, Pure.pure, StateT.pure, allowedFsStep]
                  exact ⟨trP ++ trA, hTrPA, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNePA⟩
                · simp only [hSelf, Bool.false_eq_true, ↓reduceIte]
                  have hGo := copyTreeGoM_trace hOps 4096 src dst dirsExistOk [] hTrA.1
                  cases hEg : (Internal.copyTreeGoM ops.toNonLockFsOpsM src dst dirsExistOk [] 4096 s4) with
                  | mk rGo s5 =>
                    rw [StateT.run] at hGo; rw [hEg] at hGo; dsimp only at hGo
                    obtain ⟨trGo, hTrGo, hOutGo⟩ := hGo
                    simp only [Pure.pure, allowedFsStep]
                    refine ⟨(trP ++ trA) ++ trGo, fsWorldTrace_append hTrPA hTrGo, ?_⟩
                    cases rGo with
                    | error e => exact ⟨hOutGo, fun h => hNePA (List.append_eq_nil_iff.mp h).1⟩
                    | ok u =>
                      cases u; obtain ⟨⟨rawSt, hmS, hDir⟩, hMk⟩ := hOutGo
                      exact ⟨⟨rawSt, List.mem_append_right _ hmS, hDir⟩, mkdirOkTrace_append_right hMk⟩
            by_cases hAbs : Internal.isAbsolute dst = true
            · simp only [hAbs, ↓reduceIte]
              simpa [Functor.map, StateT.map, Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure] using
                hAfterAbs (Internal.normPath dst) hTr12 hNe12
            · simp only [hAbs, Bool.false_eq_true, ↓reduceIte]
              have hC := scoped_cwd hOps hTr2.1
              cases hEc : (ops.cwd s2) with
              | mk rC s3 =>
                rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
                obtain ⟨tr3, hTr3, _, _⟩ := hC
                have hTr123 := fsWorldTrace_append hTr12 hTr3
                have hNe123 : (tr1 ++ tr2) ++ tr3 ≠ [] := fun h => hNe12 (List.append_eq_nil_iff.mp h).1
                cases rC with
                | error _ =>
                  simpa [Functor.map, StateT.map, Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure, hEc] using
                    hAfterAbs (Internal.normPath dst) hTr123 hNe123
                | ok d =>
                  simpa [Functor.map, StateT.map, Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure, hEc] using
                    hAfterAbs (Internal.normPath (Internal.join d dst)) hTr123 hNe123

/-- Compositional single-step refinement lifting `ScopedRawFsOpsM` to `Internal.mkApiFromScopedRawM` across all 32 effectful `FsApiM` operations. -/
theorem refinesStepFromFinally_mkApiFromScopedRawM :
    Core.ObeysStepFromFinally
      (RawS := FsWorld) (PkgS := FsWorld)
      (RawOps := ScopedRawFsOpsM) (PkgApi := FsApiM)
      (RawReq := ScopedRawFsStepReq) (RawOut := ScopedRawFsStepOut)
      (PkgReq := FsStepReq) (PkgOut := FsStepOut)
      id fsWorldWf execScopedRawFsStep allowedScopedRawFsStep
      fsWorldWf Internal.mkApiFromScopedRawM execFsStep allowedFsStep := by
  intro W proj ops hOps s req hWf
  cases req with
  | readText path => exact readText_step hOps path hWf
  | writeText path content =>
    have h := scoped_writeBytes hOps path content.toUTF8 hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.writeBytes path content.toUTF8 s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | appendText path content =>
    have h := scoped_appendText hOps path content hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.appendText path content s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | readBytes path =>
    have h := scoped_readBytes hOps path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.readBytes path s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, hOut⟩
  | writeBytes path data =>
    have h := scoped_writeBytes hOps path data hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.writeBytes path data s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | atomicWriteBytes path data =>
    have h := atomicWriteBytesImplM_trace hOps path data hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.atomicWriteBytesImplM ops.toNonLockFsOpsM path data s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | atomicWriteText path content =>
    have h := atomicWriteBytesImplM_trace hOps path content.toUTF8 hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.atomicWriteTextImplM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.atomicWriteBytesImplM ops.toNonLockFsOpsM path content.toUTF8 s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | touch path existOk =>
    have h := touchImplM_trace hOps path existOk hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.touchImplM ops.toNonLockFsOpsM path existOk s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | mkdir path parents existOk =>
    have h := mkdirImplM_trace hOps path parents existOk hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.mkdirImplM ops.toNonLockFsOpsM path parents existOk s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | unlink path missingOk => exact unlink_step hOps path missingOk hWf
  | rmdir path =>
    have h := scoped_removeDir hOps path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.removeDir path s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | rmtree path ignoreMissing => exact rmtree_step hOps path ignoreMissing hWf
  | rename src dst =>
    have h := scoped_rename hOps src dst hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.rename src dst s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | copyFile src dst =>
    have h := copyFileImplM_trace hOps src dst hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.copyFileImplM ops.toNonLockFsOpsM src dst s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | copyTree src dst dirsExistOk => exact copyTree_step hOps src dst dirsExistOk hWf
  | pathExists path =>
    have h := scoped_stat hOps true path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind, Pure.pure]
    cases hEq : (ops.stat true path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      cases r with
      | ok st => obtain ⟨rawSt, hm, _⟩ := hOut; exact ⟨tr, hTr, Or.inl ⟨rfl, rawSt, hm⟩⟩
      | error e => obtain ⟨_, err, hm, _⟩ := hOut; exact ⟨tr, hTr, Or.inr ⟨rfl, err, hm⟩⟩
  | isFile path =>
    have h := scoped_stat hOps true path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind, Pure.pure]
    cases hEq : (ops.stat true path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      cases r with
      | ok st => obtain ⟨rawSt, hm, hSt⟩ := hOut; exact ⟨tr, hTr, Or.inl ⟨rawSt, hm, by rw [hSt]; exact toFileStat_kind_file rawSt⟩⟩
      | error e => obtain ⟨_, err, hm, _⟩ := hOut; exact ⟨tr, hTr, Or.inr ⟨rfl, err, hm⟩⟩
  | isDir path =>
    have h := scoped_stat hOps true path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind, Pure.pure]
    cases hEq : (ops.stat true path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      cases r with
      | ok st => obtain ⟨rawSt, hm, hSt⟩ := hOut; exact ⟨tr, hTr, Or.inl ⟨rawSt, hm, by rw [hSt]; exact toFileStat_kind_dir_beq rawSt⟩⟩
      | error e => obtain ⟨_, err, hm, _⟩ := hOut; exact ⟨tr, hTr, Or.inr ⟨rfl, err, hm⟩⟩
  | isSymlink path =>
    have h := scoped_stat hOps false path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, StateT.bind, Pure.pure]
    cases hEq : (ops.stat false path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      cases r with
      | ok st => obtain ⟨rawSt, hm, hSt⟩ := hOut; exact ⟨tr, hTr, Or.inl ⟨rawSt, hm, by rw [hSt]; exact toFileStat_kind_symlink_beq rawSt⟩⟩
      | error e => obtain ⟨_, err, hm, _⟩ := hOut; exact ⟨tr, hTr, Or.inr ⟨rfl, err, hm⟩⟩
  | stat path =>
    have h := scoped_stat hOps true path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.stat true path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      refine ⟨tr, hTr, ?_⟩
      cases r with | ok st => exact hOut | error e => exact ⟨hOut.1, let ⟨err, hm, _⟩ := hOut.2; ⟨err, hm⟩⟩
  | lstat path =>
    have h := scoped_stat hOps false path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.stat false path s) with
    | mk r _ =>
      rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h
      refine ⟨tr, hTr, ?_⟩
      cases r with | ok st => exact hOut | error e => exact ⟨hOut.1, let ⟨err, hm, _⟩ := hOut.2; ⟨err, hm⟩⟩
  | chmod path mode =>
    have h := hOps s (.chmod path mode) hWf
    simp only [execScopedRawFsStep, execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep, allowedFsStep] at h ⊢
    cases hEq : (ops.chmod path mode s) with
    | mk r _ => rw [hEq] at h; dsimp only at h ⊢; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | symlink target linkPath =>
    have h := hOps s (.symlink target linkPath) hWf
    simp only [execScopedRawFsStep, execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep, allowedFsStep] at h ⊢
    cases hEq : (ops.symlink target linkPath s) with
    | mk r _ => rw [hEq] at h; dsimp only at h ⊢; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | readLink path =>
    have h := hOps s (.readLink path) hWf
    simp only [execScopedRawFsStep, execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep, allowedFsStep] at h ⊢
    cases hEq : (ops.readLink path s) with
    | mk r _ => rw [hEq] at h; dsimp only at h ⊢; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | resolve path =>
    have h := scoped_realPath hOps path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.realPath path s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | cwd =>
    have h := scoped_cwd hOps hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (ops.cwd s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | listDir path =>
    have h := listDirSortedM_trace hOps path hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.listDirSortedM ops.toNonLockFsOpsM path s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | walk root =>
    have h := walkImplM_trace hOps root hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.walkImplM ops.toNonLockFsOpsM root s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | glob root pattern =>
    have h := globImplM_trace hOps root pattern hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.globImplM ops.toNonLockFsOpsM root pattern s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | rglob root pattern =>
    let fullPat := if pattern == "**" || pattern.startsWith "**/" then pattern else "**/" ++ pattern
    have h := globImplM_trace hOps root fullPat hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawM, Internal.rglobImplM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.globImplM ops.toNonLockFsOpsM root fullPat s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r <;> exact hOut⟩
  | withFileLock path mode createIfMissing actRes =>
    have h := hOps s (.withFileLock path mode createIfMissing actRes) hWf
    simp only [execScopedRawFsStep, execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep, allowedFsStep] at h ⊢
    cases hEq : (ops.withFileLock path mode createIfMissing (StateT.pure actRes) s) with
    | mk r _ => rw [hEq] at h; dsimp only at h ⊢; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, hOut⟩
  | tryWithFileLock path mode createIfMissing actRes =>
    have h := hOps s (.tryWithFileLock path mode createIfMissing actRes) hWf
    simp only [execScopedRawFsStep, execFsStep, Internal.mkApiFromScopedRawM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep, allowedFsStep] at h ⊢
    cases hEq : (ops.tryWithFileLock path mode createIfMissing (StateT.pure actRes) s) with
    | mk r _ => rw [hEq] at h; dsimp only at h ⊢; obtain ⟨tr, hTr, _, hOut⟩ := h; exact ⟨tr, hTr, hOut⟩

/-- Compositional single-step refinement lifting `ScopedRawFsOpsM` to `Internal.mkApiFromScopedRawRetryM` across all 32 effectful `FsApiM` operations. -/
theorem refinesStepFromFinally_mkApiFromScopedRawRetryM :
    Core.ObeysStepFromFinally
      (RawS := FsWorld) (PkgS := FsWorld)
      (RawOps := ScopedRawFsOpsM) (PkgApi := FsApiM)
      (RawReq := ScopedRawFsStepReq) (RawOut := ScopedRawFsStepOut)
      (PkgReq := FsStepReq) (PkgOut := FsStepOut)
      id fsWorldWf execScopedRawFsStep allowedScopedRawFsStep
      fsWorldWf Internal.mkApiFromScopedRawRetryM execFsStep allowedFsStep := by
  intro W proj ops hOps s req hWf
  cases req with
  | atomicWriteBytes path data =>
    have h := atomicWriteBytesRetryM_trace hOps path data 16 hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawRetryM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.atomicWriteBytesRetryM ops.toNonLockFsOpsM path data 16 s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | atomicWriteText path content =>
    have h := atomicWriteBytesRetryM_trace hOps path content.toUTF8 16 hWf
    simp only [execFsStep, Internal.mkApiFromScopedRawRetryM, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedFsStep]
    cases hEq : (Internal.atomicWriteBytesRetryM ops.toNonLockFsOpsM path content.toUTF8 16 s) with
    | mk r _ => rw [StateT.run] at h; rw [hEq] at h; obtain ⟨tr, hTr, hOut⟩ := h; exact ⟨tr, hTr, by cases r with | ok u => cases u; exact hOut | error e => exact hOut⟩
  | _ =>
    exact refinesStepFromFinally_mkApiFromScopedRawM proj ops hOps s _ hWf

/-- End-to-end compositional single-step refinement lifting `FsSysCapsM` (`LinuxSyscall.Files` + `LinuxSyscall.TimeRand`) to `Internal.mkApiFromCapsM`. -/
theorem refinesStepFromFinally_mkApiFromCapsM :
    Core.ObeysStepFromFinally
      fsDepsWorldToFsWorld fsDepsWorldWf
      execFsSysCapStep allowedFsSysCapStep
      fsWorldWf Internal.mkApiFromCapsM
      execFsStep allowedFsStep := by
  intro W proj caps hCaps s req hPkgWf
  have hDepsWf : fsDepsWorldWf (proj s) = true :=
    (fsWorldWf_fsDepsWorldToFsWorld_iff (proj s)).mp hPkgWf
  have hWfSplit := (Bool.and_eq_true _ _).mp hDepsWf
  let hidOf := (proj s).toHid
  have hEq0 : pinToHidProj proj hidOf s = (proj s).fs := pinToHidProj_eq_of_inv rfl hWfSplit.2
  have hMap0 : fsDepsWorldToFsWorld (proj s) = (proj s).fs := fsDepsWorldToFsWorld_eq_of_wf hWfSplit.2
  have hPinWf : fsWorldWf (pinToHidProj proj hidOf s) = true := hEq0 ▸ hWfSplit.1
  have hApi := refinesStepFromFinally_mkApiFromScopedRawRetryM (pinToHidProj proj hidOf)
    (Internal.toScopedRawFsOpsM (SysBridge.mkRawFsOpsM caps.files (SysBridge.nextTimeRandNonce caps.timeRand)))
    (refinesScopedRawFs_of_refinesFilesFixed (refinesFsFilesFixed_of_fsSysCaps hCaps hidOf))
    s req hPinWf
  have hWf1 := allowedFsStep_wf hApi
  obtain ⟨hHid1, hTwf1, _, _⟩ := pinToHidProj_wf_inv hWf1
  have hEq1 : pinToHidProj proj hidOf ((execFsStep (Internal.mkApiFromCapsM caps) req).run s).2 =
      (proj ((execFsStep (Internal.mkApiFromCapsM caps) req).run s).2).fs :=
    pinToHidProj_eq_of_inv hHid1 hTwf1
  have hMap1 : fsDepsWorldToFsWorld (proj ((execFsStep (Internal.mkApiFromCapsM caps) req).run s).2) =
      (proj ((execFsStep (Internal.mkApiFromCapsM caps) req).run s).2).fs :=
    fsDepsWorldToFsWorld_eq_of_wf hTwf1
  dsimp only [Function.comp, id, Internal.mkApiFromCapsM] at hApi hEq1 hMap1 ⊢
  rw [hEq0, hEq1] at hApi
  rw [hMap0, hMap1]
  exact hApi

end LeanSwe.Fs.Proofs

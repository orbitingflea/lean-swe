import LeanSwe.Fs.Proofs.FsRefinesHelpers3

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Trace specification for `Internal.atomicWriteSiblingM`. -/
theorem atomicWriteSiblingM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (bytes : ByteArray) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.atomicWriteSiblingM ops.toNonLockFsOpsM path bytes).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () =>
        ∃ nonce : Nat,
          let tmpPath := Model.join ((Model.parent path).getD ".") s!".{(Model.name path).getD "tmp"}.tmp.{nonce}"
          ∃ tr2 tr3, tr = tr2 ++ tr3 ∧
            WriteFileTrace none tmpPath.toUTF8 createNewOpenFlags 0o644 bytes tr2 ∧
            RenameTrace none tmpPath.toUTF8 none path.toUTF8 tr3
      | .error e => nonLockErrOk e := by
  unfold Internal.atomicWriteSiblingM
  have hN := scoped_monotonicNonce hOps hWf
  cases hEn : (ops.monotonicNonce s) with
  | mk nonce s1 =>
    rw [StateT.run] at hN; rw [hEn] at hN; dsimp only at hN
    obtain ⟨hTrN, _⟩ := hN
    simp only [Bind.bind, StateT.bind, StateT.run, hEn]
    let tmpPath := Model.join ((Model.parent path).getD ".") s!".{(Model.name path).getD "tmp"}.tmp.{nonce}"
    have hC := scoped_createFileNew hOps tmpPath bytes hTrN.1
    cases hEc : (ops.createFileNew tmpPath bytes s1) with
    | mk rC s2 =>
      rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
      obtain ⟨tr2, hTr2, _, hOut2⟩ := hC
      have hTrN2 : FsWorldTrace (proj s) tr2 (proj s2) := by
        simpa using fsWorldTrace_append hTrN hTr2
      cases rC with
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr2, hTrN2, hOut2.1⟩
      | ok u =>
        cases u
        have hRn := scoped_rename hOps tmpPath path hTr2.1
        cases hErn : (ops.rename tmpPath path s2) with
        | mk rRn s3 =>
          rw [StateT.run] at hRn; rw [hErn] at hRn; dsimp only at hRn
          obtain ⟨tr3, hTr3, _, hOut3⟩ := hRn
          dsimp only [tmpPath] at hErn
          simp only [Bind.bind, StateT.bind, hErn]
          cases rRn with
          | ok u2 =>
            cases u2; simp only [Pure.pure, StateT.pure]
            exact ⟨tr2 ++ tr3, fsWorldTrace_append hTrN2 hTr3, nonce, tr2, tr3, rfl, hOut2, hOut3⟩
          | error e =>
            have hU := scoped_unlinkFile hOps tmpPath hTr3.1
            cases hEu : (ops.unlinkFile tmpPath s3) with
            | mk rU s4 =>
              rw [StateT.run] at hU; rw [hEu] at hU; dsimp only at hU
              obtain ⟨tr4, hTr4, _, _⟩ := hU
              dsimp only [tmpPath] at hEu
              simp only [Bind.bind, StateT.bind, hEu, Pure.pure, StateT.pure]
              exact ⟨(tr2 ++ tr3) ++ tr4, fsWorldTrace_append (fsWorldTrace_append hTrN2 hTr3) hTr4, hOut3.1⟩

/-- Trace specification for `Internal.atomicWriteBytesImplM`. -/
theorem atomicWriteBytesImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (bytes : ByteArray) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.atomicWriteBytesImplM ops.toNonLockFsOpsM path bytes).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => AtomicWriteTrace path bytes tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/")) := by
  unfold Internal.atomicWriteBytesImplM
  by_cases hVal : (!Internal.isValidAtomicTargetPath path) = true
  · simp only [hVal, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inr (Or.inl trivial)⟩
  · by_cases hRoot : (path == "/") = true
    · simp only [hVal, Bool.false_eq_true, ↓reduceIte, hRoot, Pure.pure, StateT.pure, StateT.run]
      exact ⟨[], fsWorldTrace_nil hWf, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inr (Or.inr ⟨trivial, beq_iff_eq.mp hRoot⟩)⟩
    · simp only [hVal, Bool.false_eq_true, ↓reduceIte, hRoot]
      have hS := scoped_stat hOps false path hWf
      cases hEs : (ops.stat false path s) with
      | mk rS s1 =>
        rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
        obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
        simp only [Bind.bind, StateT.bind, StateT.run, hEs]
        have hSib : ∀ (hNe1 : tr1 ≠ []),
            let q := (Internal.atomicWriteSiblingM ops.toNonLockFsOpsM path bytes).run s1
            ∃ tr, FsWorldTrace (proj s) tr (proj q.2) ∧
              match q.1 with
              | .ok () => AtomicWriteTrace path bytes tr
              | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/")) := by
          intro hNe1
          have hA := atomicWriteSiblingM_trace hOps path bytes hTr1.1
          cases hEa : (Internal.atomicWriteSiblingM ops.toNonLockFsOpsM path bytes s1) with
          | mk rA s2 =>
            rw [StateT.run] at hA; rw [hEa] at hA; dsimp only at hA
            obtain ⟨trA, hTrA, hOutA⟩ := hA
            simp only [StateT.run, hEa]
            refine ⟨tr1 ++ trA, fsWorldTrace_append hTr1 hTrA, ?_⟩
            cases rA with
            | error e => exact ⟨hOutA, Or.inl (fun h => hNe1 (List.append_eq_nil_iff.mp h).1)⟩
            | ok u =>
              cases u; obtain ⟨nonce, tr2, tr3, rfl, hWr, hRn⟩ := hOutA
              exact ⟨nonce, tr1, tr2, tr3, by simp [List.append_assoc], hWr, hRn⟩
        cases rS with
        | error e =>
          have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
          by_cases hNf : (e.kind != .notFound) = true
          · simp only [hNf, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1, Or.inl hNe1⟩
          · simp only [hNf, Bool.false_eq_true, ↓reduceIte]; exact hSib hNe1
        | ok st =>
          have hNe1 := statTrace_nonEmpty hOut1
          by_cases hD : (st.kind == .dir) = true
          · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inl hNe1⟩
          · simp only [hD, Bool.false_eq_true, ↓reduceIte]; exact hSib hNe1

/-- Trace specification for `Internal.atomicWriteSiblingRetryM`. -/
theorem atomicWriteSiblingRetryM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (bytes : ByteArray) (attempts : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.atomicWriteSiblingRetryM ops.toNonLockFsOpsM path bytes attempts).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () =>
        ∃ nonce : Nat,
          let tmpPath := Model.join ((Model.parent path).getD ".") s!".{(Model.name path).getD "tmp"}.tmp.{nonce}"
          ∃ trPre tr2 tr3, tr = trPre ++ tr2 ++ tr3 ∧
            WriteFileTrace none tmpPath.toUTF8 createNewOpenFlags 0o644 bytes tr2 ∧
            RenameTrace none tmpPath.toUTF8 none path.toUTF8 tr3
      | .error e => nonLockErrOk e := by
  induction attempts generalizing s with
  | zero =>
    unfold Internal.atomicWriteSiblingRetryM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, ⟨by dsimp only; decide, by dsimp only; decide⟩⟩
  | succ a ih =>
    unfold Internal.atomicWriteSiblingRetryM
    have hN := scoped_monotonicNonce hOps hWf
    cases hEn : (ops.monotonicNonce s) with
    | mk nonce s1 =>
      rw [StateT.run] at hN; rw [hEn] at hN; dsimp only at hN
      obtain ⟨hTrN, _⟩ := hN
      simp only [Bind.bind, StateT.bind, StateT.run, hEn]
      let tmpPath := Model.join ((Model.parent path).getD ".") s!".{(Model.name path).getD "tmp"}.tmp.{nonce}"
      have hC := scoped_createFileNew hOps tmpPath bytes hTrN.1
      cases hEc : (ops.createFileNew tmpPath bytes s1) with
      | mk rC s2 =>
        rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
        obtain ⟨tr2, hTr2, _, hOut2⟩ := hC
        have hTrN2 : FsWorldTrace (proj s) tr2 (proj s2) := by
          simpa using fsWorldTrace_append hTrN hTr2
        cases rC with
        | ok u =>
          cases u
          have hRn := scoped_rename hOps tmpPath path hTr2.1
          cases hErn : (ops.rename tmpPath path s2) with
          | mk rRn s3 =>
            rw [StateT.run] at hRn; rw [hErn] at hRn; dsimp only at hRn
            obtain ⟨tr3, hTr3, _, hOut3⟩ := hRn
            dsimp only [tmpPath] at hErn
            simp only [Bind.bind, StateT.bind, hErn]
            cases rRn with
            | ok u2 =>
              cases u2; simp only [Pure.pure, StateT.pure]
              exact ⟨tr2 ++ tr3, fsWorldTrace_append hTrN2 hTr3, nonce, [], tr2, tr3, rfl, hOut2, hOut3⟩
            | error e =>
              have hU := scoped_unlinkFile hOps tmpPath hTr3.1
              cases hEu : (ops.unlinkFile tmpPath s3) with
              | mk rU s4 =>
                rw [StateT.run] at hU; rw [hEu] at hU; dsimp only at hU
                obtain ⟨tr4, hTr4, _, _⟩ := hU
                dsimp only [tmpPath] at hEu
                simp only [Bind.bind, StateT.bind, hEu, Pure.pure, StateT.pure]
                exact ⟨(tr2 ++ tr3) ++ tr4, fsWorldTrace_append (fsWorldTrace_append hTrN2 hTr3) hTr4, hOut3.1⟩
        | error ce =>
          by_cases hRetry : (ce.kind == .alreadyExists && decide (a > 0)) = true
          · simp only [hRetry, ↓reduceIte]
            have hIh := ih hTr2.1
            cases hO : (Internal.atomicWriteSiblingRetryM ops.toNonLockFsOpsM path bytes a s2) with
            | mk r3 s3 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨tr3, hTr3, hOut3⟩ := hIh
              refine ⟨tr2 ++ tr3, fsWorldTrace_append hTrN2 hTr3, ?_⟩
              cases r3 with
              | error e => exact hOut3
              | ok u =>
                cases u
                obtain ⟨nonce', trPre, sub2, sub3, rfl, hWr, hRn⟩ := hOut3
                exact ⟨nonce', tr2 ++ trPre, sub2, sub3, by simp [List.append_assoc], hWr, hRn⟩
          · simp only [hRetry, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨tr2, hTrN2, hOut2.1⟩

/-- Trace specification for `Internal.atomicWriteBytesRetryM`. -/
theorem atomicWriteBytesRetryM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (bytes : ByteArray) (attempts : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.atomicWriteBytesRetryM ops.toNonLockFsOpsM path bytes attempts).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => AtomicWriteTrace path bytes tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/")) := by
  unfold Internal.atomicWriteBytesRetryM
  by_cases hVal : (!Internal.isValidAtomicTargetPath path) = true
  · simp only [hVal, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inr (Or.inl trivial)⟩
  · by_cases hRoot : (path == "/") = true
    · simp only [hVal, Bool.false_eq_true, ↓reduceIte, hRoot, Pure.pure, StateT.pure, StateT.run]
      exact ⟨[], fsWorldTrace_nil hWf, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inr (Or.inr ⟨trivial, beq_iff_eq.mp hRoot⟩)⟩
    · simp only [hVal, Bool.false_eq_true, ↓reduceIte, hRoot]
      have hS := scoped_stat hOps false path hWf
      cases hEs : (ops.stat false path s) with
      | mk rS s1 =>
        rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
        obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
        simp only [Bind.bind, StateT.bind, StateT.run, hEs]
        have hSib : ∀ (hNe1 : tr1 ≠ []),
            let q := (Internal.atomicWriteSiblingRetryM ops.toNonLockFsOpsM path bytes attempts).run s1
            ∃ tr, FsWorldTrace (proj s) tr (proj q.2) ∧
              match q.1 with
              | .ok () => AtomicWriteTrace path bytes tr
              | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ e.kind = .invalidInput ∨ (e.kind = .isADirectory ∧ path = "/")) := by
          intro hNe1
          have hA := atomicWriteSiblingRetryM_trace hOps path bytes attempts hTr1.1
          cases hEa : (Internal.atomicWriteSiblingRetryM ops.toNonLockFsOpsM path bytes attempts s1) with
          | mk rA s2 =>
            rw [StateT.run] at hA; rw [hEa] at hA; dsimp only at hA
            obtain ⟨trA, hTrA, hOutA⟩ := hA
            simp only [StateT.run, hEa]
            refine ⟨tr1 ++ trA, fsWorldTrace_append hTr1 hTrA, ?_⟩
            cases rA with
            | error e => exact ⟨hOutA, Or.inl (fun h => hNe1 (List.append_eq_nil_iff.mp h).1)⟩
            | ok u =>
              cases u; obtain ⟨nonce, trPre, tr2, tr3, rfl, hWr, hRn⟩ := hOutA
              exact ⟨nonce, tr1 ++ trPre, tr2, tr3, by simp [List.append_assoc], hWr, hRn⟩
        cases rS with
        | error e =>
          have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
          by_cases hNf : (e.kind != .notFound) = true
          · simp only [hNf, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1, Or.inl hNe1⟩
          · simp only [hNf, Bool.false_eq_true, ↓reduceIte]; exact hSib hNe1
        | ok st =>
          have hNe1 := statTrace_nonEmpty hOut1
          by_cases hD : (st.kind == .dir) = true
          · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, Or.inl hNe1⟩
          · simp only [hD, Bool.false_eq_true, ↓reduceIte]; exact hSib hNe1

end LeanSwe.Fs.Proofs

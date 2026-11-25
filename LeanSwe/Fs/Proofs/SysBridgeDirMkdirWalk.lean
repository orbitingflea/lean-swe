import LeanSwe.Fs.Proofs.SysBridgeDirWalk

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined trace specification for `Internal.mkdirWalkM`. -/
theorem mkdirWalkM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (post : HandleId → List KernelStep → Prop)
    (leafAct : fd → StateM W (Except FsError Unit))
    (hLeaf : ∀ (dirDh : fd) (held : List HandleId) {s : W}, fsWorldWf (proj s) = true →
      let p := (leafAct dirDh).run s
      fsWorldWf (proj p.2) = true ∧
      (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds held tr held ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match p.1 with
        | .ok () => post (hidOf dirDh) tr
        | .error e => nonLockErrOk e)
    (isRoot : Bool) (cur : fd) (tailHeld : List HandleId) (segs : List EntryName)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let held0 := if isRoot then tailHeld else hidOf cur :: tailHeld
    let p := (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) isRoot cur segs leafAct).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held0 tr tailHeld ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => ∃ d sub, Subtrace sub tr ∧ post d sub
      | .error e => nonLockErrOk e := by
  induction segs generalizing isRoot cur s with
  | nil =>
    unfold Internal.mkdirWalkM
    cases isRoot with
    | true =>
      simp only [↓reduceIte]
      have hL := hLeaf cur tailHeld hWf
      cases hRl : leafAct cur s with
      | mk res s1 =>
        simp only [StateT.run, hRl] at hL ⊢
        obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hL
        refine ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, ?_⟩
        cases res with
        | ok u => cases u; exact ⟨hidOf cur, tr, subtrace_refl tr, hOut⟩
        | error e => exact hOut
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sysBracketCloseDirM_run]
      have hL := hLeaf cur (hidOf cur :: tailHeld) hWf
      cases hRl : leafAct cur s with
      | mk res s1 =>
        rw [StateT.run] at hL; rw [hRl] at hL; dsimp only at hL
        obtain ⟨hWf1, hTmp1, trL, hStL, hFdL, hConfL, hOutL⟩ := hL
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hCloseEq : (SysBridge.mkRawDirOpsM files nextNonce).closeDir cur s1 = (cRes, s2) := hRc
          simp only [StateT.run, hRl, hCloseEq]
          refine ⟨hWf2, by omega, trL ++ [(.close (hidOf cur), co)],
            healthyFilesSteps_append hStL hStC, traceFds_append hFdL hFdC,
            confined_append hConfL (confined_single (s := (.close (hidOf cur), co)) trivial), ?_⟩
          cases res with
          | ok u => cases u; exact ⟨hidOf cur, trL, subtrace_append_left _ (subtrace_refl trL), hOutL⟩
          | error e => exact hOutL
  | cons seg rest ih =>
    let stepM : StateM W (Except FsError fd) := do
      match ← (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg with
      | .ok nextDh => pure (.ok nextDh)
      | .error e =>
        if e.kind == .notFound then
          match ← (SysBridge.mkRawDirOpsM files nextNonce).createDirAt cur seg with
          | .ok () => (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg
          | .error ce =>
            if ce.kind == .alreadyExists then (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg
            else pure (.error ce)
        else
          pure (.error e)
    have hStepSpec : ∀ (hld : List HandleId),
        let q := stepM.run s
        fsWorldWf (proj q.2) = true ∧
        (proj q.2).tempSeq = (proj s).tempSeq ∧
        ∃ tr,
          HealthyFilesSteps (proj s).env tr (proj q.2).env ∧
          (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
          match q.1 with
          | .ok nextDh => TraceFds hld tr (hidOf nextDh :: hld)
          | .error e => TraceFds hld tr hld ∧ nonLockErrOk e := by
      intro hld
      dsimp only [stepM]
      have hOp1 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf
      cases hR1 : (SysBridge.openDirAtPure files cur seg DEFAULT_EINTR_FUEL s) with
      | mk r1 s1 =>
        rw [StateT.run] at hOp1; rw [hR1] at hOp1; dsimp only at hOp1
        obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hOp1
        have hR1' : (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg s = (r1, s1) := hR1
        simp only [Bind.bind, StateT.bind, StateT.run, hR1']
        cases r1 with
        | ok nextDh =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩
        | error e =>
          by_cases hNf : (e.kind == .notFound) = true
          · simp only [hNf, ↓reduceIte]
            have hCr := dirOps_createDirAt_trace hCap cur seg hld hWf1
            cases hRc : ((SysBridge.mkRawDirOpsM files nextNonce).createDirAt cur seg s1) with
            | mk crRes s2 =>
              rw [StateT.run] at hCr; rw [hRc] at hCr; dsimp only at hCr
              obtain ⟨hWf2, hTmp2, trC, hStC, hFdC, hConfC, hOutC⟩ := hCr
              simp only [Bind.bind, StateT.bind, hRc]
              cases crRes with
              | ok u =>
                cases u
                dsimp only
                have hOp2 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf2
                cases hR2 : (SysBridge.openDirAtPure files cur seg DEFAULT_EINTR_FUEL s2) with
                | mk r2 s3 =>
                  rw [StateT.run] at hOp2; rw [hR2] at hOp2; dsimp only at hOp2
                  obtain ⟨hWf3, hTmp3, tr2, hSt2, hConf2, hOut2⟩ := hOp2
                  have hR2' : (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg s2 = (r2, s3) := hR2
                  rw [hR2']; dsimp only
                  refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trC) ++ tr2,
                    healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStC) hSt2,
                    confined_append (confined_append hConf1 hConfC) hConf2, ?_⟩
                  cases r2 with
                  | ok nextDh => exact traceFds_append (traceFds_append hOut1.1 hFdC) hOut2
                  | error e2 => exact ⟨traceFds_append (traceFds_append hOut1.1 hFdC) hOut2.1, hOut2.2.1⟩
              | error ce =>
                dsimp only
                by_cases hEx : (ce.kind == .alreadyExists) = true
                · simp only [hEx, ↓reduceIte]
                  have hOp2 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf2
                  cases hR2 : (SysBridge.openDirAtPure files cur seg DEFAULT_EINTR_FUEL s2) with
                  | mk r2 s3 =>
                    rw [StateT.run] at hOp2; rw [hR2] at hOp2; dsimp only at hOp2
                    obtain ⟨hWf3, hTmp3, tr2, hSt2, hConf2, hOut2⟩ := hOp2
                    have hR2' : (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg s2 = (r2, s3) := hR2
                    rw [hR2']; dsimp only
                    refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trC) ++ tr2,
                      healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStC) hSt2,
                      confined_append (confined_append hConf1 hConfC) hConf2, ?_⟩
                    cases r2 with
                    | ok nextDh => exact traceFds_append (traceFds_append hOut1.1 hFdC) hOut2
                    | error e2 => exact ⟨traceFds_append (traceFds_append hOut1.1 hFdC) hOut2.1, hOut2.2.1⟩
                · simp only [hEx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                  exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ trC, healthyFilesSteps_append hSt1 hStC,
                    confined_append hConf1 hConfC, traceFds_append hOut1.1 hFdC, hOutC⟩
          · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1.1, hOut1.2.1⟩
    cases isRoot with
    | true =>
      have hSt := hStepSpec tailHeld
      cases hRs : stepM s with
      | mk rNext s1 =>
        rw [StateT.run] at hSt; rw [hRs] at hSt; dsimp only at hSt
        obtain ⟨hWf1, hTmp1, trS, hStS, hConfS, hOutS⟩ := hSt
        have hEq : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) true cur (seg :: rest) leafAct).run s =
            (match rNext with
             | .error e => (Except.error e, s1)
             | .ok nextDh => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct).run s1) := by
          conv => lhs; unfold Internal.mkdirWalkM
          simp only [↓reduceIte]
          refine Eq.trans ?_ (show (stepM >>= fun r => match r with
            | .error e => pure (Except.error e)
            | .ok nextDh => Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct).run s = _ from by
            simp only [Bind.bind, StateT.bind, StateT.run, hRs]; cases rNext <;> rfl)
          have hF : ∀ (a b : StateM W (Except FsError fd))
              (g1 g2 : Except FsError fd → StateM W (Except FsError Unit)),
              a = b → g1 = g2 → (a >>= g1).run s = (b >>= g2).run s := by rintro _ _ _ _ rfl rfl; rfl
          refine hF _ _ _ _ (funext fun s0 => ?_) (funext fun r => by cases r <;> rfl)
          simp only [stepM, Bind.bind, StateT.bind]
          cases (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg s0 with
          | mk r0 sA =>
            cases r0 with
            | ok _ => rfl
            | error e =>
              by_cases hNf : (e.kind == .notFound) = true
              · simp only [hNf, ↓reduceIte]
                cases (SysBridge.mkRawDirOpsM files nextNonce).createDirAt cur seg sA with
                | mk rC _ => cases rC with | ok u => cases u; rfl | error _ => rfl
              · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
        dsimp only; rw [hEq]
        cases rNext with
        | error e =>
          dsimp only
          exact ⟨hWf1, by omega, trS, hStS, hOutS.1, hConfS, hOutS.2⟩
        | ok nextDh =>
          have hIh := ih false nextDh hWf1
          cases hRec : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            refine ⟨hWf2, by omega, trS ++ tr2, healthyFilesSteps_append hStS hSt2,
              traceFds_append hOutS hFd2, confined_append hConfS hConf2, ?_⟩
            cases r2 with
            | error e => exact hOut2
            | ok u => cases u; obtain ⟨d, sub, hSub, hPost⟩ := hOut2; exact ⟨d, sub, subtrace_append_right trS hSub, hPost⟩
    | false =>
      have hSt := hStepSpec (hidOf cur :: tailHeld)
      cases hRs : stepM s with
      | mk rNext s1 =>
        rw [StateT.run] at hSt; rw [hRs] at hSt; dsimp only at hSt
        obtain ⟨hWf1, hTmp1, trS, hStS, hConfS, hOutS⟩ := hSt
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hBr : (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM files nextNonce) cur stepM) s = (rNext, s2) := by
            have h1 := sysBracketCloseDirM_run (SysBridge.mkRawDirOpsM files nextNonce) cur stepM s
            have hRc' : (SysBridge.mkRawDirOpsM files nextNonce).closeDir cur s1 = (cRes, s2) := hRc
            simp only [StateT.run, hRs, hRc'] at h1; exact h1
          have hEq : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false cur (seg :: rest) leafAct).run s =
              (match rNext with
               | .error e => (Except.error e, s2)
               | .ok nextDh => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct).run s2) := by
            conv => lhs; unfold Internal.mkdirWalkM
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine Eq.trans ?_ (show ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM files nextNonce) cur stepM) >>= fun r =>
              match r with
              | .error e => pure (Except.error e)
              | .ok nextDh => Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct).run s = _ from by
              simp only [Bind.bind, StateT.bind, StateT.run, hBr]; cases rNext <;> rfl)
            have hF : ∀ (a b : StateM W (Except FsError fd))
                (g1 g2 : Except FsError fd → StateM W (Except FsError Unit)),
                a = b → g1 = g2 →
                ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM files nextNonce) cur a) >>= g1).run s =
                ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM files nextNonce) cur b) >>= g2).run s := by
              rintro _ _ _ _ rfl rfl; rfl
            refine hF _ _ _ _ (funext fun s0 => ?_) (funext fun r => by cases r <;> rfl)
            simp only [stepM, Bind.bind, StateT.bind]
            cases (SysBridge.mkRawDirOpsM files nextNonce).openDirAt cur seg s0 with
            | mk r0 sA =>
              cases r0 with
              | ok _ => rfl
              | error e =>
                by_cases hNf : (e.kind == .notFound) = true
                · simp only [hNf, ↓reduceIte]
                  cases (SysBridge.mkRawDirOpsM files nextNonce).createDirAt cur seg sA with
                  | mk rC _ => cases rC with | ok u => cases u; rfl | error _ => rfl
                · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
          dsimp only; rw [hEq]
          have hStSC := healthyFilesSteps_append hStS hStC
          have hConfSC := confined_append hConfS (confined_single (s := (.close (hidOf cur), co)) trivial)
          cases rNext with
          | error e =>
            dsimp only
            exact ⟨hWf2, by omega, trS ++ [(.close (hidOf cur), co)], hStSC,
              traceFds_append hOutS.1 hFdC, hConfSC, hOutS.2⟩
          | ok nextDh =>
            have hFdSC : TraceFds (hidOf cur :: tailHeld) (trS ++ [(.close (hidOf cur), co)]) (hidOf nextDh :: tailHeld) :=
              traceFds_append hOutS traceFds_close_second
            have hIh := ih false nextDh hWf2
            cases hRec : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) false nextDh rest leafAct s2) with
            | mk r3 s3 =>
              simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
              obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
              refine ⟨hWf3, by omega, (trS ++ [(.close (hidOf cur), co)]) ++ tr3,
                healthyFilesSteps_append hStSC hSt3, traceFds_append hFdSC hFd3,
                confined_append hConfSC hConf3, ?_⟩
              cases r3 with
              | error e => exact hOut3
              | ok u => cases u; obtain ⟨d, sub, hSub, hPost⟩ := hOut3; exact ⟨d, sub, subtrace_append_right _ hSub, hPost⟩

end LeanSwe.Fs.Proofs

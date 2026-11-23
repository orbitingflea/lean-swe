import LeanSwe.Fs.Impl
import LeanSwe.Fs.Proofs.SysBridgeLoops

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

private theorem append_ne_empty_l {a b : String} (h : a ≠ "") : a ++ b ≠ "" := by
  intro heq
  apply h
  have hl : (a ++ b).toList = [] := by rw [heq]; rfl
  rw [String.toList_append] at hl
  exact String.ext (by simpa using (List.append_eq_nil_iff.mp hl).1)

/-- Trace specification for `SysBridge.readLinkLoop`. -/
theorem readLinkLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (path : String) (capSz : UInt32) (eintrFuel fuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readLinkLoop cap.files path capSz eintrFuel fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok tgt => ReadLinkTrace path.toUTF8 tgt tr ∧ tr ≠ []
      | .error e => nonLockErrOk e ∧ (fuel > 0 → tr ≠ []) := by
  induction fuel generalizing capSz s with
  | zero =>
    unfold SysBridge.readLinkLoop
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, fun h => by omega⟩
  | succ f ih =>
    unfold SysBridge.readLinkLoop
    have hRl := retryEintr_single_req (cap.files.readlinkat none path.toUTF8 capSz)
      (.readlinkat none path.toUTF8 capSz) outcomeOfBytes
      (fun s' hW => cap_method_step hCap (.readlinkat none path.toUTF8 capSz)
        (cap.files.readlinkat none path.toUTF8 capSz) outcomeOfBytes rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR : (retryEintr (cap.files.readlinkat none path.toUTF8 capSz) eintrFuel s) with
    | mk res s1 =>
      rw [StateT.run] at hRl; rw [hR] at hRl; dsimp only at hRl
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hRl
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.readlinkat none path.toUTF8 capSz, outcomeOfBytes res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      have hNe1 : trR ++ [(.readlinkat none path.toUTF8 capSz, outcomeOfBytes res)] ≠ [] := by simp
      cases res with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => hNe1⟩
      | ok bs =>
        by_cases hLt : bs.size < capSz.toNat
        · simp only [hLt, ↓reduceIte]
          cases hUtf : String.fromUTF8? bs with
          | some tgt =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, _, hTr1, ⟨⟨capSz, bs, by simp [outcomeOfBytes], hLt, hUtf⟩, hNe1⟩⟩
          | none =>
            simp only [Pure.pure, StateT.pure]
            refine ⟨hWf1, hTmp1, _, hTr1, ⟨?_, fun hc => by cases hc⟩, fun _ => hNe1⟩
            dsimp only
            exact append_ne_empty_l (append_ne_empty_l (by decide))
        · simp only [hLt, ↓reduceIte]
          by_cases hCapGe : capSz ≥ SysBridge.MAX_PATH_BUF_CAP
          · simp only [hCapGe, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => hNe1⟩
          · simp only [hCapGe, ↓reduceIte]
            have hIh := ih (min (capSz * 2) SysBridge.MAX_PATH_BUF_CAP) hWf1
            cases hO : (SysBridge.readLinkLoop cap.files path (min (capSz * 2) SysBridge.MAX_PATH_BUF_CAP) eintrFuel f s1) with
            | mk r2 s2 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hIh
              refine ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTr1 hTr2, ?_⟩
              cases r2 with
              | ok tgt =>
                obtain ⟨⟨c, b, hm, hl, hu⟩, _⟩ := hOut2
                exact ⟨⟨c, b, List.mem_append_right _ hm, hl, hu⟩, by simp⟩
              | error e => exact ⟨hOut2.1, fun _ => by simp⟩

/-- Trace specification for `SysBridge.getcwdLoop`. -/
theorem getcwdLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (capSz : UInt32) (eintrFuel fuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.getcwdLoop cap.files capSz eintrFuel fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok cwdStr => GetcwdTrace cwdStr tr ∧ tr ≠ []
      | .error e => nonLockErrOk e ∧ (fuel > 0 → tr ≠ []) := by
  induction fuel generalizing capSz s with
  | zero =>
    unfold SysBridge.getcwdLoop
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, fun h => by omega⟩
  | succ f ih =>
    unfold SysBridge.getcwdLoop
    have hGc := retryEintr_single_req (cap.files.getcwd capSz) (.getcwd capSz) outcomeOfBytes
      (fun s' hW => cap_method_step hCap (.getcwd capSz) (cap.files.getcwd capSz) outcomeOfBytes rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR : (retryEintr (cap.files.getcwd capSz) eintrFuel s) with
    | mk res s1 =>
      rw [StateT.run] at hGc; rw [hR] at hGc; dsimp only at hGc
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hGc
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.getcwd capSz, outcomeOfBytes res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok bs =>
        dsimp only
        cases hUtf : String.fromUTF8? bs with
        | some cwdStr =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hTr1, ⟨⟨capSz, bs, by simp [outcomeOfBytes], hUtf⟩, by simp⟩⟩
        | none =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hTr1, ⟨by decide, fun hc => by cases hc⟩, fun _ => by simp⟩
      | error e =>
        by_cases hRng : (e == Errno.ERANGE && decide (capSz < SysBridge.MAX_PATH_BUF_CAP)) = true
        · simp only [hRng, ↓reduceIte]
          have hIh := ih (min (capSz * 2) SysBridge.MAX_PATH_BUF_CAP) hWf1
          cases hO : (SysBridge.getcwdLoop cap.files (min (capSz * 2) SysBridge.MAX_PATH_BUF_CAP) eintrFuel f s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hIh
            refine ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTr1 hTr2, ?_⟩
            cases r2 with
            | ok cwdStr =>
              obtain ⟨⟨c, b, hm, hu⟩, _⟩ := hOut2
              exact ⟨⟨c, b, List.mem_append_right _ hm, hu⟩, by simp⟩
            | error err => exact ⟨hOut2.1, fun _ => by simp⟩
        · simp only [hRng, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩

/-- Trace specification for `SysBridge.realPathLoop`. -/
theorem realPathLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (origPath : String) (eintrFuel : Nat)
    (resolvedRev queue : List String) (trailingSlash : Bool) (symLeft fuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.realPathLoop cap.files origPath eintrFuel resolvedRev queue trailingSlash symLeft fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok rp => RealPathTrace rp tr
      | .error e => nonLockErrOk e ∧ (fuel > queue.length → tr ≠ []) := by
  induction fuel generalizing resolvedRev queue trailingSlash symLeft s with
  | zero =>
    unfold SysBridge.realPathLoop
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, fun h => by omega⟩
  | succ f ih =>
    unfold SysBridge.realPathLoop
    cases queue with
    | nil =>
      have hFs := retryEintr_single_req (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true })
        (.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) outcomeOfStatted
        (fun s' hW => cap_method_step hCap (.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true })
          (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) outcomeOfStatted rfl hW)
        (fun _ => rfl) eintrFuel hWf
      cases hR : (retryEintr (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) eintrFuel s) with
      | mk res s1 =>
        rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
        obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hFs
        simp only [Bind.bind, StateT.bind, StateT.run, hR]
        have hTr1 : FsWorldTrace (proj s) (trR ++ [(.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }, outcomeOfStatted res)]) (proj s1) :=
          ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
            (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
        cases res with
        | error e =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
        | ok st =>
          by_cases hBad : (trailingSlash && st.kind != .dir) = true
          · simp only [hBad, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
          · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, _, hTr1, renderAbsRev_isAbsolute resolvedRev, st, by simp [outcomeOfStatted]⟩
    | cons seg rest =>
      by_cases hDot : (seg == ".") = true
      · simp only [hDot, ↓reduceIte]
        have hIh := ih resolvedRev rest trailingSlash symLeft hWf
        cases hO : (SysBridge.realPathLoop cap.files origPath eintrFuel resolvedRev rest trailingSlash symLeft f s) with
        | mk r2 s2 =>
          simp only [StateT.run, hO] at hIh ⊢
          obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hIh
          refine ⟨hWf2, hTmp2, tr2, hTr2, ?_⟩
          cases r2 with
          | ok rp => exact hOut2
          | error e => exact ⟨hOut2.1, fun hGt => hOut2.2 (by simp at hGt; omega)⟩
      · by_cases hDotDot : (seg == "..") = true
        · simp only [hDot, Bool.false_eq_true, ↓reduceIte, hDotDot]
          have hFs := retryEintr_single_req (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true })
            (.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) outcomeOfStatted
            (fun s' hW => cap_method_step hCap (.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true })
              (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) outcomeOfStatted rfl hW)
            (fun _ => rfl) eintrFuel hWf
          cases hR : (retryEintr (cap.files.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }) eintrFuel s) with
          | mk res s1 =>
            rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
            obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hFs
            simp only [Bind.bind, StateT.bind, StateT.run, hR]
            have hTr1 : FsWorldTrace (proj s) (trR ++ [(.fstatat none (SysBridge.renderAbsRev resolvedRev).toUTF8 { symlinkNofollow := true }, outcomeOfStatted res)]) (proj s1) :=
              ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
                (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
            cases res with
            | error e =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
            | ok st =>
              by_cases hNd : (st.kind != .dir) = true
              · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
              · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
                have hPopStep : ∀ (rev' : List String),
                    let p := (SysBridge.realPathLoop cap.files origPath eintrFuel rev' rest trailingSlash symLeft f).run s1
                    fsWorldWf (proj p.2) = true ∧ (proj p.2).tempSeq = (proj s).tempSeq ∧
                    ∃ tr, FsWorldTrace (proj s) tr (proj p.2) ∧
                      match p.1 with
                      | .ok rp => RealPathTrace rp tr
                      | .error e => nonLockErrOk e ∧ (f + 1 > (seg :: rest).length → tr ≠ []) := by
                  intro rev'
                  have hIh := ih rev' rest trailingSlash symLeft hWf1
                  cases hO : (SysBridge.realPathLoop cap.files origPath eintrFuel rev' rest trailingSlash symLeft f s1) with
                  | mk r2 s2 =>
                    simp only [StateT.run, hO] at hIh ⊢
                    obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hIh
                    refine ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTr1 hTr2, ?_⟩
                    cases r2 with
                    | ok rp => exact ⟨hOut2.1, let ⟨rs, hm⟩ := hOut2.2; ⟨rs, List.mem_append_right _ hm⟩⟩
                    | error e => exact ⟨hOut2.1, fun _ => by simp⟩
                cases resolvedRev with
                | nil => exact hPopStep []
                | cons _ tl => exact hPopStep tl
        · simp only [hDot, Bool.false_eq_true, ↓reduceIte, hDotDot]
          have hFs := retryEintr_single_req (cap.files.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true })
            (.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true }) outcomeOfStatted
            (fun s' hW => cap_method_step hCap (.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true })
              (cap.files.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true }) outcomeOfStatted rfl hW)
            (fun _ => rfl) eintrFuel hWf
          cases hR : (retryEintr (cap.files.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true }) eintrFuel s) with
          | mk res s1 =>
            rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
            obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hFs
            simp only [Bind.bind, StateT.bind, StateT.run, hR]
            have hTr1 : FsWorldTrace (proj s) (trR ++ [(.fstatat none (SysBridge.renderAbsRev (seg :: resolvedRev)).toUTF8 { symlinkNofollow := true }, outcomeOfStatted res)]) (proj s1) :=
              ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
                (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
            cases res with
            | error e =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
            | ok st =>
              by_cases hSym : (st.kind == .symlink) = true
              · simp only [hSym, ↓reduceIte]
                by_cases hS0 : (symLeft == 0) = true
                · simp only [hS0, ↓reduceIte, Pure.pure, StateT.pure]
                  exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
                · simp only [hS0, Bool.false_eq_true, ↓reduceIte]
                  have hRl := readLinkLoop_trace hCap (SysBridge.renderAbsRev (seg :: resolvedRev)) 256 eintrFuel 13 hWf1
                  cases hRlR : (SysBridge.readLinkLoop cap.files (SysBridge.renderAbsRev (seg :: resolvedRev)) 256 eintrFuel 13 s1) with
                  | mk rlRes s2 =>
                    simp only [StateT.run, hRlR] at hRl ⊢
                    obtain ⟨hWf2, hTmp2, trL, hTrL, hOutL⟩ := hRl
                    simp only [Bind.bind, StateT.bind, hRlR]
                    cases rlRes with
                    | error e =>
                      simp only [Pure.pure, StateT.pure]
                      exact ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTr1 hTrL,
                        hOutL.1, fun _ => by simp⟩
                    | ok target =>
                      dsimp only
                      have hIh := ih (if target.startsWith "/" = true then [] else resolvedRev)
                        (SysBridge.splitNonEmptySegs target ++ rest)
                        (if rest.isEmpty = true then (trailingSlash || (decide (target.length > 1) && target.endsWith "/")) else trailingSlash)
                        (symLeft - 1) hWf2
                      cases hO : (SysBridge.realPathLoop cap.files origPath eintrFuel
                          (if target.startsWith "/" = true then [] else resolvedRev)
                          (SysBridge.splitNonEmptySegs target ++ rest)
                          (if rest.isEmpty = true then (trailingSlash || (decide (target.length > 1) && target.endsWith "/")) else trailingSlash)
                          (symLeft - 1) f s2) with
                      | mk r3 s3 =>
                        simp only [StateT.run, hO] at hIh ⊢
                        obtain ⟨hWf3, hTmp3, tr3, hTr3, hOut3⟩ := hIh
                        refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _,
                          fsWorldTrace_append (fsWorldTrace_append hTr1 hTrL) hTr3, ?_⟩
                        cases r3 with
                        | ok rp => exact ⟨hOut3.1, let ⟨rs, hm⟩ := hOut3.2; ⟨rs, List.mem_append_right _ hm⟩⟩
                        | error e => exact ⟨hOut3.1, fun _ => by simp⟩
              · by_cases hDir : (st.kind == .dir) = true
                · simp only [hSym, Bool.false_eq_true, ↓reduceIte, hDir]
                  have hIh := ih (seg :: resolvedRev) rest trailingSlash symLeft hWf1
                  cases hO : (SysBridge.realPathLoop cap.files origPath eintrFuel (seg :: resolvedRev) rest trailingSlash symLeft f s1) with
                  | mk r2 s2 =>
                    simp only [StateT.run, hO] at hIh ⊢
                    obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hIh
                    refine ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTr1 hTr2, ?_⟩
                    cases r2 with
                    | ok rp => exact ⟨hOut2.1, let ⟨rs, hm⟩ := hOut2.2; ⟨rs, List.mem_append_right _ hm⟩⟩
                    | error e => exact ⟨hOut2.1, fun _ => by simp⟩
                · by_cases hMore : (!rest.isEmpty || trailingSlash) = true
                  · simp only [hSym, Bool.false_eq_true, ↓reduceIte, hDir, hMore]
                    simp only [Pure.pure, StateT.pure]
                    exact ⟨hWf1, hTmp1, _, hTr1, nonLockErrOk_mapErrno _ _ _, fun _ => by simp⟩
                  · simp only [hSym, Bool.false_eq_true, ↓reduceIte, hDir, hMore, Pure.pure, StateT.pure]
                    exact ⟨hWf1, hTmp1, _, hTr1, renderAbsRev_isAbsolute (seg :: resolvedRev), st, by simp [outcomeOfStatted]⟩

/-- Trace specification for `SysBridge.realPathPure`. -/
theorem realPathPure_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (path : String) (eintrFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.realPathPure cap.files path eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok rp => RealPathTrace rp tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput) := by
  unfold SysBridge.realPathPure
  by_cases hEmp : path.isEmpty = true
  · simp only [hEmp, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    have hEqEmpty : path = "" := String.isEmpty_iff.mp hEmp
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, Or.inr (Or.inl ⟨hEqEmpty, rfl⟩)⟩
  · by_cases hNul : path.toList.contains (Char.ofNat 0) = true
    · simp only [hEmp, Bool.false_eq_true, ↓reduceIte, hNul, Pure.pure, StateT.pure, StateT.run]
      exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, Or.inr (Or.inr rfl)⟩
    · simp only [hEmp, Bool.false_eq_true, ↓reduceIte, hNul]
      by_cases hAbs : path.startsWith "/" = true
      · simp only [hAbs, ↓reduceIte, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
        have hLp := realPathLoop_trace hCap path eintrFuel [] (SysBridge.splitNonEmptySegs path)
          (decide (path.length > 1) && path.endsWith "/") SysBridge.MAX_SYMLINK_DEPTH
          ((SysBridge.splitNonEmptySegs path).length + 4096) hWf
        cases hO : (SysBridge.realPathLoop cap.files path eintrFuel [] (SysBridge.splitNonEmptySegs path)
            (decide (path.length > 1) && path.endsWith "/") SysBridge.MAX_SYMLINK_DEPTH
            ((SysBridge.splitNonEmptySegs path).length + 4096) s) with
        | mk r s1 =>
          simp only [StateT.run, hO] at hLp ⊢
          obtain ⟨hWf1, hTmp1, tr, hTr, hOut⟩ := hLp
          refine ⟨hWf1, hTmp1, tr, hTr, ?_⟩
          cases r with
          | ok rp => exact hOut
          | error e => exact ⟨hOut.1, Or.inl (hOut.2 (by omega))⟩
      · simp only [hAbs, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind, StateT.run]
        have hGc := getcwdLoop_trace hCap 4096 eintrFuel 9 hWf
        cases hG : (SysBridge.getcwdLoop cap.files 4096 eintrFuel 9 s) with
        | mk gRes s1 =>
          rw [StateT.run] at hGc; rw [hG] at hGc; dsimp only at hGc
          obtain ⟨hWf1, hTmp1, trG, hTrG, hOutG⟩ := hGc
          dsimp only
          cases gRes with
          | error e =>
            simp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
            exact ⟨hWf1, hTmp1, trG, hTrG, hOutG.1, Or.inl (hOutG.2 (by omega))⟩
          | ok cwdStr =>
            simp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
            have hLp := realPathLoop_trace hCap path eintrFuel (SysBridge.splitNonEmptySegs cwdStr).reverse
              (SysBridge.splitNonEmptySegs path) (decide (path.length > 1) && path.endsWith "/")
              SysBridge.MAX_SYMLINK_DEPTH ((SysBridge.splitNonEmptySegs path).length + 4096) hWf1
            cases hO : (SysBridge.realPathLoop cap.files path eintrFuel (SysBridge.splitNonEmptySegs cwdStr).reverse
                (SysBridge.splitNonEmptySegs path) (decide (path.length > 1) && path.endsWith "/")
                SysBridge.MAX_SYMLINK_DEPTH ((SysBridge.splitNonEmptySegs path).length + 4096) s1) with
            | mk r s2 =>
              simp only [StateT.run, hO] at hLp ⊢
              obtain ⟨hWf2, hTmp2, tr2, hTr2, hOut2⟩ := hLp
              refine ⟨hWf2, hTmp2.trans hTmp1, trG ++ tr2, fsWorldTrace_append hTrG hTr2, ?_⟩
              cases r with
              | ok rp => exact ⟨hOut2.1, let ⟨rs, hm⟩ := hOut2.2; ⟨rs, List.mem_append_right _ hm⟩⟩
              | error e => exact ⟨hOut2.1, Or.inl (by intro hNil; exact hOutG.2 (List.append_eq_nil_iff.mp hNil).1)⟩

/-- Trace specification for `SysBridge.removeDirAtOpt`. -/
theorem removeDirAtOpt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dir : Option HandleId) (path : String) (held : List HandleId) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.removeDirAtOpt cap.files dir path eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      tr ≠ [] ∧
      (∀ step ∈ tr, ∃ o, step = (.unlinkat dir path.toUTF8 true, o)) ∧
      match p.1 with
      | .ok () => UnlinkTrace dir path.toUTF8 true tr
      | .error e => nonLockErrOk e ∧ (e.kind = .notFound → (.unlinkat dir path.toUTF8 true, .err Errno.ENOENT) ∈ tr) := by
  unfold SysBridge.removeDirAtOpt
  have hUn := retryEintr_single_req (cap.files.unlinkat dir path.toUTF8 true)
    (.unlinkat dir path.toUTF8 true) outcomeOfUnit
    (fun s' hW => cap_method_step hCap (.unlinkat dir path.toUTF8 true)
      (cap.files.unlinkat dir path.toUTF8 true) outcomeOfUnit rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (cap.files.unlinkat dir path.toUTF8 true) eintrFuel s) with
  | mk res s1 =>
    rw [StateT.run] at hUn; rw [hR] at hUn; dsimp only at hUn
    obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hUn
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hFd1 : TraceFds held (trR ++ [(.unlinkat dir path.toUTF8 true, outcomeOfUnit res)]) held :=
      traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
        (traceFds_nonFd_step (by cases res <;> rfl) rfl)
    have hAllStep : ∀ step ∈ trR ++ [(.unlinkat dir path.toUTF8 true, outcomeOfUnit res)],
        ∃ o, step = (.unlinkat dir path.toUTF8 true, o) := fun step hm => by
      rcases List.mem_append.mp hm with h1 | h2
      · exact ⟨.err Errno.EINTR, hAll1 step h1⟩
      · exact ⟨outcomeOfUnit res, List.mem_singleton.mp h2⟩
    cases res with
    | ok u =>
      cases u
      simp only [Pure.pure, StateT.pure]
      exact ⟨hWf1, hTmp1, _, hSt1, hFd1, by simp, hAllStep, by simp [UnlinkTrace, outcomeOfUnit]⟩
    | error e =>
      by_cases hEx : (e == Errno.EEXIST) = true
      · simp only [hEx, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hSt1, hFd1, by simp, hAllStep, nonLockErrOk_mapErrno _ _ _,
          fun hNf => absurd (mapErrno_kind_notFound_eq _ _ _ hNf) (by decide)⟩
      · simp only [hEx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
        refine ⟨hWf1, hTmp1, _, hSt1, hFd1, by simp, hAllStep, nonLockErrOk_mapErrno _ _ _, fun hNf => ?_⟩
        have hEq := mapErrno_kind_notFound_eq _ _ _ hNf
        subst hEq
        simp [outcomeOfUnit]

/-- Trace specification for `SysBridge.readBytesPure`. -/
theorem readBytesPure_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (path : String) (eintrFuel streamFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readBytesPure cap.files path eintrFuel streamFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPathModel path = false ∧ e.kind = .invalidInput)) := by
  unfold SysBridge.readBytesPure
  by_cases hVal : SysBridge.isValidRawPath path = true
  · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hOp := retryEintr_single_req (cap.files.openat none path.toUTF8 readOpenFlags 0)
      (.openat none path.toUTF8 readOpenFlags 0) outcomeOfOpened
      (fun s' hW => cap_method_step hCap (.openat none path.toUTF8 readOpenFlags 0)
        (cap.files.openat none path.toUTF8 readOpenFlags 0) outcomeOfOpened rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR : (retryEintr (cap.files.openat none path.toUTF8 readOpenFlags 0) eintrFuel s) with
    | mk oRes s1 =>
      rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
      obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
      dsimp only [readOpenFlags] at hR
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
      cases oRes with
      | ok h =>
        have hFdO : TraceFds [] (trR ++ [(.openat none path.toUTF8 readOpenFlags 0, .opened h)]) [h] :=
          traceFds_append hFdR (traceFds_open_step rfl rfl)
        have hRd := readRegularFd_trace hCap h path [] streamFuel hWf1
        cases hRf : (SysBridge.readRegularFd cap.files h path streamFuel s1) with
        | mk rRes s2 =>
          simp only [StateT.run, hRf] at hRd ⊢
          obtain ⟨hWf2, hTmp2, trB, trC, hStBC, hFdB, hFdC, _, hCeq, hOut⟩ := hRd
          let trOpen := trR ++ [(.openat none path.toUTF8 readOpenFlags 0, .opened h)]
          have hTrAll : FsWorldTrace (proj s) (trOpen ++ trB ++ trC) (proj s2) :=
            ⟨hWf2, by rw [List.append_assoc]; exact healthyFilesSteps_append hStO hStBC,
             by rw [List.append_assoc]; exact traceFds_append hFdO (traceFds_append hFdB hFdC), by omega⟩
          refine ⟨hWf2, hTmp2.trans hTmp1, trOpen ++ trB ++ trC, hTrAll, ?_⟩
          cases rRes with
          | error e =>
            obtain ⟨co, rfl⟩ := hCeq
            exact ⟨hOut, Or.inl (by simp [trOpen])⟩
          | ok bs =>
            obtain ⟨⟨rawSt, hFsM, hReg⟩, ⟨eof, hEofM, hEz⟩, hBytes⟩ := hOut
            obtain ⟨co, rfl⟩ := hCeq
            exact ⟨h, rawSt, eof, trOpen, trB, [(.close h, co)], rfl,
              by simp [trOpen], hFsM, hReg, hEofM, hEz, hBytes, co, by simp⟩
      | error e =>
        have hTrO : FsWorldTrace (proj s) (trR ++ [(.openat none path.toUTF8 readOpenFlags 0, .err e)]) (proj s1) :=
          ⟨hWf1, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl), by omega⟩
        by_cases hNx : (e == Errno.ENXIO) = true
        · simp only [hNx, ↓reduceIte]
          have hS1 := retryEintr_single_req (cap.files.fstatat none path.toUTF8 {})
            (.fstatat none path.toUTF8 {}) outcomeOfStatted
            (fun s' hW => cap_method_step hCap (.fstatat none path.toUTF8 {})
              (cap.files.fstatat none path.toUTF8 {}) outcomeOfStatted rfl hW)
            (fun _ => rfl) eintrFuel hWf1
          cases hRs1 : (retryEintr (cap.files.fstatat none path.toUTF8 {}) eintrFuel s1) with
          | mk sRes1 s2 =>
            rw [StateT.run] at hS1; rw [hRs1] at hS1; dsimp only at hS1
            obtain ⟨hWf2, hTmp2, trR1, hSt1, hAll1⟩ := hS1
            simp only [Bind.bind, StateT.bind, hRs1]
            have hTr1 : FsWorldTrace (proj s1) (trR1 ++ [(.fstatat none path.toUTF8 {}, outcomeOfStatted sRes1)]) (proj s2) :=
              ⟨hWf2, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
                (traceFds_nonFd_step (by cases sRes1 <;> rfl) rfl), by omega⟩
            cases sRes1 with
            | ok st =>
              by_cases hD : (st.kind == .dir) = true <;>
                simp only [hD, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              · exact ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTrO hTr1,
                  nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
              · exact ⟨hWf2, hTmp2.trans hTmp1, _, fsWorldTrace_append hTrO hTr1,
                  nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
            | error _ =>
              have hS2 := retryEintr_single_req (cap.files.fstatat none path.toUTF8 { symlinkNofollow := true })
                (.fstatat none path.toUTF8 { symlinkNofollow := true }) outcomeOfStatted
                (fun s' hW => cap_method_step hCap (.fstatat none path.toUTF8 { symlinkNofollow := true })
                  (cap.files.fstatat none path.toUTF8 { symlinkNofollow := true }) outcomeOfStatted rfl hW)
                (fun _ => rfl) eintrFuel hWf2
              cases hRs2 : (retryEintr (cap.files.fstatat none path.toUTF8 { symlinkNofollow := true }) eintrFuel s2) with
              | mk sRes2 s3 =>
                rw [StateT.run] at hS2; rw [hRs2] at hS2; dsimp only at hS2
                obtain ⟨hWf3, hTmp3, trR2, hSt2, hAll2⟩ := hS2
                simp only [Bind.bind, StateT.bind, hRs2]
                have hTr2 : FsWorldTrace (proj s2) (trR2 ++ [(.fstatat none path.toUTF8 { symlinkNofollow := true }, outcomeOfStatted sRes2)]) (proj s3) :=
                  ⟨hWf3, hSt2, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll2)
                    (traceFds_nonFd_step (by cases sRes2 <;> rfl) rfl), by omega⟩
                cases sRes2 with
                | ok st =>
                  by_cases hD : (st.kind == .dir) = true <;>
                    simp only [hD, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                  · exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _,
                      fsWorldTrace_append (fsWorldTrace_append hTrO hTr1) hTr2,
                      nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
                  · exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _,
                      fsWorldTrace_append (fsWorldTrace_append hTrO hTr1) hTr2,
                      nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
                | error _ =>
                  simp only [Pure.pure, StateT.pure]
                  exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _,
                    fsWorldTrace_append (fsWorldTrace_append hTrO hTr1) hTr2,
                    nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
        · simp only [hNx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hTrO, nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
  · have hValF : isValidRawPathModel path = false := Bool.eq_false_iff.mpr hVal
    have hValF' : SysBridge.isValidRawPath path = false := hValF
    simp only [hValF', Bool.not_false, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, Or.inr ⟨hValF, rfl⟩⟩

end LeanSwe.Fs.Proofs

import LeanSwe.Fs.Proofs.SysBridgeFsOps

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Closing the second descriptor in `x :: h :: held` yields `x :: held` unconditionally. -/
theorem traceFds_close_second {x h : HandleId} {held : List HandleId} {co : FilesOutcome} :
    TraceFds (x :: h :: held) [(.close h, co)] (x :: held) := by
  refine TraceFds.step ?_ (TraceFds.nil _)
  have hOp : stepOpenedFd (.close h, co) = none := by cases co <;> rfl
  rw [hOp]
  refine ⟨by simp, ?_⟩
  simp only [List.erase]
  by_cases hEq : (x == h) = true
  · have hXh : x = h := beq_iff_eq.mp hEq
    simp [hXh]
  · simp [hEq]

/-- Prepending a non-empty string preserves non-emptiness. -/
theorem nonEmpty_append_left {a b : String} (ha : a ≠ "") : a ++ b ≠ "" := by
  intro h
  have hEq := congrArg String.toList h
  simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at hEq
  exact ha (by have := congrArg String.ofList hEq.1; simpa using this)

/-- Decidable equality characterization for `FsErrorKind` boolean equality. -/
theorem fsErrorKind_beq_iff_eq (a b : FsErrorKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Trace specification for `SysBridge.openDirPure`. -/
theorem openDirPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (eintrFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.openDirPure files rootPath eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trOpen,
      HealthyFilesSteps (proj s).env trOpen (proj p.2).env ∧
      (∀ step ∈ trOpen, ∃ o, step = (.openat none rootPath.toUTF8 dirOpenFlags 0, o)) ∧
      match p.1 with
      | .ok h =>
        TraceFds [] trOpen [hidOf h] ∧
        (.openat none rootPath.toUTF8 dirOpenFlags 0, .opened (hidOf h)) ∈ trOpen
      | .error e =>
        TraceFds [] trOpen [] ∧
        nonLockErrOk e ∧
        ((trOpen = [] ∧ isValidRawPath rootPath = false ∧ e.kind = .invalidInput) ∨ trOpen ≠ []) := by
  unfold SysBridge.openDirPure
  by_cases hVal : isValidRawPath rootPath = true
  · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hOp := retryEintr_single_req (files.openat none rootPath.toUTF8 dirOpenFlags 0)
      (.openat none rootPath.toUTF8 dirOpenFlags 0) (outcomeOfOpenedFd hidOf)
      (fun s' hW => cap_opened_step hCap (.openat none rootPath.toUTF8 dirOpenFlags 0)
        (files.openat none rootPath.toUTF8 dirOpenFlags 0) rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR : (retryEintr (files.openat none rootPath.toUTF8 dirOpenFlags 0) eintrFuel s) with
    | mk oRes s1 =>
      rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
      obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
      dsimp only [dirOpenFlags] at hR
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
      have hAllSteps : ∀ step ∈ trR ++ [(.openat none rootPath.toUTF8 dirOpenFlags 0, outcomeOfOpenedFd hidOf oRes)],
          ∃ o, step = (.openat none rootPath.toUTF8 dirOpenFlags 0, o) := fun step hm => by
        rcases List.mem_append.mp hm with h1 | h2
        · exact ⟨.err Errno.EINTR, hAllO step h1⟩
        · exact ⟨outcomeOfOpenedFd hidOf oRes, List.mem_singleton.mp h2⟩
      cases oRes with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hStO, hAllSteps,
          traceFds_append hFdR (traceFds_nonFd_step rfl rfl),
          nonLockErrOk_mapErrno _ _ _, Or.inr (by simp)⟩
      | ok h =>
        simp only [Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hStO, hAllSteps,
          traceFds_append hFdR (traceFds_open_step rfl rfl), by simp [outcomeOfOpenedFd]⟩
  · have hValF : isValidRawPath rootPath = false := Bool.eq_false_iff.mpr hVal
    simp only [hValF, Bool.not_false, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], HealthyFilesSteps.nil _, (fun _ hm => nomatch hm),
      TraceFds.nil [], nonLockErrOk_mapErrno _ _ _, Or.inl ⟨rfl, trivial, rfl⟩⟩

/-- Confined trace specification for `SysBridge.openDirAtPure`. -/
theorem openDirAtPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (dirFd : fd) (name : EntryName) (held : List HandleId) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.openDirAtPure files dirFd name eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok h => TraceFds held tr (hidOf h :: held)
      | .error e =>
        TraceFds held tr held ∧
        nonLockErrOk e ∧
        (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr) := by
  unfold SysBridge.openDirAtPure
  let fl : OpenFlags := { access := .rdonly, directory := true, nofollow := true, cloexec := true }
  have hOp := retryEintr_single_req (files.openat (some dirFd) name.val.toUTF8 fl 0)
    (.openat (some (hidOf dirFd)) name.val.toUTF8 fl 0) (outcomeOfOpenedFd hidOf)
    (fun s' hW => cap_opened_step hCap (.openat (some dirFd) name.val.toUTF8 fl 0)
      (files.openat (some dirFd) name.val.toUTF8 fl 0) rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (files.openat (some dirFd) name.val.toUTF8 fl 0) eintrFuel s) with
  | mk oRes s1 =>
    rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
    obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
    have hR' : retryEintr (files.openat (some dirFd) name.val.toUTF8
        { access := .rdonly, directory := true, nofollow := true, cloexec := true } 0) eintrFuel s =
        (oRes, s1) := hR
    simp only [Bind.bind, StateT.bind, StateT.run, hR']
    have hFdR : TraceFds held trR held := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
    have hConfStep : SubtreeConfinedReq (.openat (some (hidOf dirFd)) name.val.toUTF8 fl 0) := ⟨rfl, ⟨name, rfl⟩⟩
    have hConfO : ∀ step ∈ trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 fl 0, outcomeOfOpenedFd hidOf oRes)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAllO step hm]; exact hConfStep) (confined_single hConfStep)
    cases oRes with
    | ok h =>
      simp only [Pure.pure, StateT.pure]
      exact ⟨hWf1, hTmp1, _, hStO, hConfO, traceFds_append hFdR (traceFds_open_step rfl rfl)⟩
    | error e =>
      have hFdO : TraceFds held (trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 fl 0, .err e)]) held :=
        traceFds_append hFdR (traceFds_nonFd_step rfl rfl)
      by_cases hEl : (e == Errno.ELOOP) = true
      · simp only [hEl, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hStO, hConfO, hFdO, nonLockErrOk_mapErrno _ _ _,
          fun hNf => absurd (mapErrno_kind_notFound_eq _ _ _ hNf) (by decide)⟩
      · by_cases hNd : (e == Errno.ENOTDIR) = true
        · simp only [hEl, Bool.false_eq_true, ↓reduceIte, hNd]
          have hFs := retryEintr_single_req (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
            (.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }) outcomeOfStatted
            (fun s' hW => cap_statted_step hCap (.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
              (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) rfl hW)
            (fun _ => rfl) eintrFuel hWf1
          cases hRf : (retryEintr (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) eintrFuel s1) with
          | mk fRes s2 =>
            rw [StateT.run] at hFs; rw [hRf] at hFs; dsimp only at hFs
            obtain ⟨hWf2, hTmp2, trRf, hStF, hAllF⟩ := hFs
            simp only [Bind.bind, StateT.bind, hRf]
            have hConfF : ∀ step ∈ trRf ++ [(.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted fRes)],
                SubtreeConfinedReq step.1 :=
              confined_append (fun step hm => by rw [hAllF step hm]; exact ⟨rfl, ⟨name, rfl⟩⟩)
                (confined_single ⟨rfl, ⟨name, rfl⟩⟩)
            have hFdF : TraceFds held (trRf ++ [(.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted fRes)]) held :=
              traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAllF)
                (traceFds_nonFd_step (by cases fRes <;> rfl) rfl)
            have hStAll := healthyFilesSteps_append hStO hStF
            have hConfAll := confined_append hConfO hConfF
            have hFdAll := traceFds_append hFdO hFdF
            cases fRes with
            | error _ =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hConfAll, hFdAll, nonLockErrOk_mapErrno _ _ _,
                fun hNf => absurd (mapErrno_kind_notFound_eq _ _ _ hNf) (by decide)⟩
            | ok st =>
              by_cases hSym : (st.kind == .symlink) = true
              · simp only [hSym, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hConfAll, hFdAll, nonLockErrOk_mapErrno _ _ _,
                  fun hNf => absurd (mapErrno_kind_notFound_eq _ _ _ hNf) (by decide)⟩
              · simp only [hSym, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hConfAll, hFdAll, nonLockErrOk_mapErrno _ _ _,
                  fun hNf => absurd (mapErrno_kind_notFound_eq _ _ _ hNf) (by decide)⟩
        · simp only [hEl, Bool.false_eq_true, ↓reduceIte, hNd, Pure.pure, StateT.pure]
          refine ⟨hWf1, hTmp1, _, hStO, hConfO, hFdO, nonLockErrOk_mapErrno _ _ _, fun hNf => ?_⟩
          have hEq := mapErrno_kind_notFound_eq _ _ _ hNf
          subst hEq
          exact ⟨.openat (some (hidOf dirFd)) name.val.toUTF8 fl 0, by simp [outcomeOfOpenedFd]⟩

/-- Confined trace specification for `SysBridge.readDirAtPure`. -/
theorem readDirAtPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (dirFd : fd) (held : List HandleId) (eintrFuel streamFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readDirAtPure files dirFd eintrFuel streamFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok xs =>
        ∃ h eof,
          (.getdents64 h 8192, .bytes eof) ∈ tr ∧
          eof.size = 0 ∧
          (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ tr ∧ buf.size > 0)
      | .error e => nonLockErrOk e := by
  unfold SysBridge.readDirAtPure
  have hRe := retryEintr_single_req (files.reopenReadOnly dirFd)
    (.reopenReadOnly (hidOf dirFd)) (outcomeOfOpenedFd hidOf)
    (fun s' hW => cap_opened_step hCap (.reopenReadOnly dirFd)
      (files.reopenReadOnly dirFd) rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (files.reopenReadOnly dirFd) eintrFuel s) with
  | mk reRes s1 =>
    rw [StateT.run] at hRe; rw [hR] at hRe; dsimp only at hRe
    obtain ⟨hWf1, hTmp1, trRe, hStRe, hAllRe⟩ := hRe
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hFdRe0 : TraceFds held trRe held := traceFds_eintr_retries (fun _ hc => by cases hc) hAllRe
    have hConfRe : ∀ step ∈ trRe ++ [(.reopenReadOnly (hidOf dirFd), outcomeOfOpenedFd hidOf reRes)], SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAllRe step hm]; trivial) (confined_single trivial)
    cases reRes with
    | ok dupFd =>
      have hFdDup : TraceFds held (trRe ++ [(.reopenReadOnly (hidOf dirFd), .opened (hidOf dupFd))]) (hidOf dupFd :: held) :=
        traceFds_append hFdRe0 (traceFds_open_step rfl rfl)
      have hLp := readDirStreamLoop_trace hCap dupFd "." (hidOf dupFd :: held) #[] streamFuel (fun _ hm => by cases hm) hWf1
      cases hRl : (SysBridge.readDirStreamLoop files dupFd "." #[] streamFuel s1) with
      | mk lRes s2 =>
        rw [StateT.run] at hLp; rw [hRl] at hLp; dsimp only at hLp
        obtain ⟨hWf2, hTmp2, trL, hStL, hFdL, hConfL, hOutL⟩ := hLp
        simp only [Bind.bind, StateT.bind, hRl]
        cases lRes with
        | error err =>
          have hQ := closeQuiet_trace hCap dupFd held hWf2
          cases hRq : (SysBridge.closeQuiet files dupFd s2) with
          | mk u s3 =>
            rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
            obtain ⟨hWf3, hTmp3, co, hStC, hFdC, _⟩ := hQ
            simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
            exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _,
              healthyFilesSteps_append (healthyFilesSteps_append hStRe hStL) hStC,
              traceFds_append (traceFds_append hFdDup hFdL) hFdC,
              confined_append (confined_append hConfRe hConfL) (confined_single trivial), hOutL⟩
        | ok raw =>
          have hCc := closeCheck_trace hCap dupFd (some ".") held hWf2
          cases hRc : (SysBridge.closeCheck files dupFd (some ".") s2) with
          | mk cRes s3 =>
            rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
            obtain ⟨hWf3, hTmp3, hErrC, co, hStC, hFdC, _⟩ := hCc
            simp only [Bind.bind, StateT.bind, hRc]
            have hStAll := healthyFilesSteps_append (healthyFilesSteps_append hStRe hStL) hStC
            have hFdAll := traceFds_append (traceFds_append hFdDup hFdL) hFdC
            have hConfAll := confined_append (confined_append hConfRe hConfL) (confined_single (s := (.close (hidOf dupFd), co)) trivial)
            cases cRes with
            | error ce =>
              simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
              exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll, hErrC⟩
            | ok u =>
              cases u
              simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
              have hP := parseUniqueEntryNames_props raw
              cases hPr : SysBridge.parseUniqueEntryNames raw with
              | error pe =>
                rw [hPr] at hP
                exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll, hP⟩
              | ok xs =>
                rw [hPr] at hP
                obtain ⟨_, ⟨eof, hMemE, hEz⟩, hNonEmp⟩ := hOutL
                refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll,
                  hidOf dupFd, eof, by simp [hMemE], hEz, fun hGt => ?_⟩
                obtain ⟨buf, hMemB, hBp⟩ := hNonEmp (by simpa using hP hGt)
                exact ⟨buf, by simp [hMemB], hBp⟩
    | error errRe =>
      have hFdReErr : TraceFds held (trRe ++ [(.reopenReadOnly (hidOf dirFd), outcomeOfOpenedFd hidOf (.error errRe))]) held :=
        traceFds_append hFdRe0 (traceFds_nonFd_step rfl rfl)
      have hLs := retryEintr_single_req (files.lseek dirFd 0 .seekSet)
        (.lseek (hidOf dirFd) 0 .seekSet) outcomeOfU64
        (fun s' hW => cap_u64_step hCap (.lseek dirFd 0 .seekSet)
          (files.lseek dirFd 0 .seekSet) rfl hW)
        (fun _ => rfl) eintrFuel hWf1
      cases hRs : (retryEintr (files.lseek dirFd 0 .seekSet) eintrFuel s1) with
      | mk sRes s2 =>
        rw [StateT.run] at hLs; rw [hRs] at hLs; dsimp only at hLs
        obtain ⟨hWf2, hTmp2, trS, hStS, hAllS⟩ := hLs
        simp only [Bind.bind, StateT.bind, hRs]
        have hFdS : TraceFds held (trS ++ [(.lseek (hidOf dirFd) 0 .seekSet, outcomeOfU64 sRes)]) held :=
          traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAllS)
            (traceFds_nonFd_step (by cases sRes <;> rfl) rfl)
        have hConfS : ∀ step ∈ trS ++ [(.lseek (hidOf dirFd) 0 .seekSet, outcomeOfU64 sRes)], SubtreeConfinedReq step.1 :=
          confined_append (fun step hm => by rw [hAllS step hm]; trivial) (confined_single trivial)
        cases sRes with
        | error se =>
          simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
          exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hStRe hStS,
            traceFds_append hFdReErr hFdS, confined_append hConfRe hConfS,
            nonLockErrOk_mapErrno _ _ _⟩
        | ok _ =>
          have hLp := readDirStreamLoop_trace hCap dirFd "." held #[] streamFuel (fun _ hm => by cases hm) hWf2
          cases hRl : (SysBridge.readDirStreamLoop files dirFd "." #[] streamFuel s2) with
          | mk lRes s3 =>
            rw [StateT.run] at hLp; rw [hRl] at hLp; dsimp only at hLp
            obtain ⟨hWf3, hTmp3, trL, hStL, hFdL, hConfL, hOutL⟩ := hLp
            simp only [Bind.bind, StateT.bind, hRl]
            have hStAll := healthyFilesSteps_append (healthyFilesSteps_append hStRe hStS) hStL
            have hFdAll := traceFds_append (traceFds_append hFdReErr hFdS) hFdL
            have hConfAll := confined_append (confined_append hConfRe hConfS) hConfL
            cases lRes with
            | error err =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll, hOutL⟩
            | ok raw =>
              simp only [Pure.pure, StateT.pure]
              have hP := parseUniqueEntryNames_props raw
              cases hPr : SysBridge.parseUniqueEntryNames raw with
              | error pe =>
                rw [hPr] at hP
                exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll, hP⟩
              | ok xs =>
                rw [hPr] at hP
                obtain ⟨_, ⟨eof, hMemE, hEz⟩, hNonEmp⟩ := hOutL
                refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hStAll, hFdAll, hConfAll,
                  hidOf dirFd, eof, by simp [hMemE], hEz, fun hGt => ?_⟩
                obtain ⟨buf, hMemB, hBp⟩ := hNonEmp (by simpa using hP hGt)
                exact ⟨buf, by simp [hMemB], hBp⟩

/-- Confined trace specification for `SysBridge.readRegularAtPure`. -/
theorem readRegularAtPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (dirFd : fd) (name : EntryName) (held : List HandleId) (eintrFuel streamFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readRegularAtPure files dirFd name eintrFuel streamFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok bs => ReadRegularTrace (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags bs tr
      | .error e => nonLockErrOk e := by
  unfold SysBridge.readRegularAtPure
  have hOp := retryEintr_single_req (files.openat (some dirFd) name.val.toUTF8 readAtOpenFlags 0)
    (.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0) (outcomeOfOpenedFd hidOf)
    (fun s' hW => cap_opened_step hCap (.openat (some dirFd) name.val.toUTF8 readAtOpenFlags 0)
      (files.openat (some dirFd) name.val.toUTF8 readAtOpenFlags 0) rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (files.openat (some dirFd) name.val.toUTF8 readAtOpenFlags 0) eintrFuel s) with
  | mk oRes s1 =>
    rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
    obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
    dsimp only [readAtOpenFlags] at hR
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hFdR : TraceFds held trR held := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
    have hConfStep : SubtreeConfinedReq (.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0) := ⟨rfl, ⟨name, rfl⟩⟩
    have hConfO : ∀ step ∈ trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0, outcomeOfOpenedFd hidOf oRes)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAllO step hm]; exact hConfStep) (confined_single hConfStep)
    cases oRes with
    | ok h =>
      have hFdO : TraceFds held (trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0, .opened (hidOf h))]) (hidOf h :: held) :=
        traceFds_append hFdR (traceFds_open_step rfl rfl)
      have hRd := readRegularFd_trace hCap h name.val held streamFuel hWf1
      cases hRr : (SysBridge.readRegularFd files h name.val streamFuel s1) with
      | mk rRes s2 =>
        rw [StateT.run] at hRd; rw [hRr] at hRd; dsimp only at hRd
        obtain ⟨hWf2, hTmp2, trB, trC, hStB, hFdB, hFdC, hConfB, ⟨co, hCeq⟩, hOutB⟩ := hRd
        subst hCeq
        simp only [hRr]
        have hStAll := healthyFilesSteps_append hStO hStB
        have hFdAll := traceFds_append hFdO (traceFds_append hFdB hFdC)
        have hConfAll := confined_append hConfO hConfB
        cases rRes with
        | error err => exact ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hFdAll, hConfAll, hOutB⟩
        | ok bs =>
          obtain ⟨⟨rawSt, hFs, hReg⟩, ⟨eof, hMemE, hEz⟩, hReadEq⟩ := hOutB
          exact ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hFdAll, hConfAll,
            hidOf h, rawSt, eof, trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0, .opened (hidOf h))],
            trB, [(.close (hidOf h), co)], by simp [List.append_assoc, outcomeOfOpenedFd], by simp, hFs, hReg, hMemE, hEz, hReadEq, co, by simp⟩
    | error e =>
      have hFdO : TraceFds held (trR ++ [(.openat (some (hidOf dirFd)) name.val.toUTF8 readAtOpenFlags 0, .err e)]) held :=
        traceFds_append hFdR (traceFds_nonFd_step rfl rfl)
      by_cases hEl : (e == Errno.ELOOP) = true
      · simp only [hEl, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, _, hStO, hFdO, hConfO, nonLockErrOk_mapErrno _ _ _⟩
      · by_cases hNx : (e == Errno.ENXIO) = true
        · simp only [hEl, Bool.false_eq_true, ↓reduceIte, hNx]
          have hFs := retryEintr_single_req (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
            (.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }) outcomeOfStatted
            (fun s' hW => cap_statted_step hCap (.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
              (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) rfl hW)
            (fun _ => rfl) eintrFuel hWf1
          cases hRf : (retryEintr (files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) eintrFuel s1) with
          | mk fRes s2 =>
            rw [StateT.run] at hFs; rw [hRf] at hFs; dsimp only at hFs
            obtain ⟨hWf2, hTmp2, trRf, hStF, hAllF⟩ := hFs
            simp only [Bind.bind, StateT.bind, hRf]
            have hConfF : ∀ step ∈ trRf ++ [(.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted fRes)],
                SubtreeConfinedReq step.1 :=
              confined_append (fun step hm => by rw [hAllF step hm]; exact ⟨rfl, ⟨name, rfl⟩⟩)
                (confined_single ⟨rfl, ⟨name, rfl⟩⟩)
            have hFdF : TraceFds held (trRf ++ [(.fstatat (some (hidOf dirFd)) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted fRes)]) held :=
              traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAllF)
                (traceFds_nonFd_step (by cases fRes <;> rfl) rfl)
            cases fRes with
            | error _ =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hStO hStF,
                traceFds_append hFdO hFdF, confined_append hConfO hConfF, nonLockErrOk_mapErrno _ _ _⟩
            | ok st =>
              by_cases hDir : (st.kind == .dir) = true
              · simp only [hDir, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hStO hStF,
                  traceFds_append hFdO hFdF, confined_append hConfO hConfF, nonLockErrOk_mapErrno _ _ _⟩
              · simp only [hDir, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hStO hStF,
                  traceFds_append hFdO hFdF, confined_append hConfO hConfF, nonLockErrOk_mapErrno _ _ _⟩
        · simp only [hEl, Bool.false_eq_true, ↓reduceIte, hNx, Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, _, hStO, hFdO, hConfO, nonLockErrOk_mapErrno _ _ _⟩

end LeanSwe.Fs.Proofs

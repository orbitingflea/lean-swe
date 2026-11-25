import LeanSwe.Fs.SysBridge
import LeanSwe.Fs.Proofs.HealthyFilesBase

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- `SysBridge.statInfoToFileStat` agrees definitionally with `Model.toFileStat`. -/
theorem sysBridge_statInfoToFileStat_eq (st : StatInfo) :
    SysBridge.statInfoToFileStat st = Model.toFileStat st := rfl

private theorem str_ne_empty_of_toList_ne (s : String) (h : s.toList ≠ []) : s ≠ "" := by
  intro heq
  apply h
  rw [heq]
  rfl

private theorem append_ne_empty_left (a b : String) (h : a ≠ "") : a ++ b ≠ "" := by
  intro heq
  apply h
  have hl : (a ++ b).toList = [] := by rw [heq]; rfl
  rw [String.toList_append] at hl
  have ha : a.toList = [] := (List.append_eq_nil_iff.mp hl).1
  exact String.ext (by simpa using ha)

private theorem append_ne_empty_right (a b : String) (h : b ≠ "") : a ++ b ≠ "" := by
  intro heq
  apply h
  have hl : (a ++ b).toList = [] := by rw [heq]; rfl
  rw [String.toList_append] at hl
  have hb : b.toList = [] := (List.append_eq_nil_iff.mp hl).2
  exact String.ext (by simpa using hb)

/-- `SysBridge.mapErrno` always yields a non-empty message and never returns `.wouldBlock`. -/
theorem nonLockErrOk_mapErrno (path? : Option String) (ctx : String) (e : Errno) :
    nonLockErrOk (SysBridge.mapErrno path? ctx e) := by
  unfold nonLockErrOk SysBridge.mapErrno
  constructor
  · dsimp only
    exact append_ne_empty_left _ _ (append_ne_empty_right _ _ (by decide))
  · dsimp only
    repeat (split; · intro hc; cases hc)
    intro hc; cases hc

/-- `SysBridge.mapErrno` maps an errno to `.notFound` if and only if the errno is `Errno.ENOENT`. -/
theorem mapErrno_kind_notFound_eq (path? : Option String) (ctx : String) (e : Errno)
    (h : (SysBridge.mapErrno path? ctx e).kind = .notFound) :
    e = Errno.ENOENT := by
  unfold SysBridge.mapErrno at h
  dsimp only at h
  by_cases h1 : (e == Errno.ENOENT) = true
  · exact beq_iff_eq.mp h1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    repeat (split at h; · cases h)
    cases h

/-- Empty trace vacuously satisfies `SubtreeConfinedReq`. -/
theorem confined_nil : ∀ step ∈ ([] : List KernelStep), SubtreeConfinedReq step.1 :=
  fun _ hm => by cases hm

/-- Singleton trace satisfies `SubtreeConfinedReq` iff its step does. -/
theorem confined_single {s : KernelStep} (h : SubtreeConfinedReq s.1) :
    ∀ step ∈ [s], SubtreeConfinedReq step.1 := fun _ hm => by
  rw [List.mem_singleton.mp hm]; exact h

/-- Cons preserves `SubtreeConfinedReq`. -/
theorem confined_cons {s : KernelStep} {tr : List KernelStep}
    (h1 : SubtreeConfinedReq s.1) (h2 : ∀ step ∈ tr, SubtreeConfinedReq step.1) :
    ∀ step ∈ s :: tr, SubtreeConfinedReq step.1 := fun step hm => by
  rcases List.mem_cons.mp hm with rfl | htl
  · exact h1
  · exact h2 step htl

/-- Append preserves `SubtreeConfinedReq`. -/
theorem confined_append {tr1 tr2 : List KernelStep}
    (h1 : ∀ step ∈ tr1, SubtreeConfinedReq step.1)
    (h2 : ∀ step ∈ tr2, SubtreeConfinedReq step.1) :
    ∀ step ∈ tr1 ++ tr2, SubtreeConfinedReq step.1 := fun step hm => by
  rcases List.mem_append.mp hm with m1 | m2
  · exact h1 step m1
  · exact h2 step m2

/-- `SysBridge.parseDirents64Aux` never inserts `.` or `..` and preserves non-emptiness monotonicity. -/
theorem parseDirents64Aux_props (bs : ByteArray) (pos : Nat) (acc : Array String) (path : String)
    (fuel : Nat) (hAcc : ∀ nm ∈ acc.toList, nm ≠ "." ∧ nm ≠ "..") :
    match SysBridge.parseDirents64Aux bs pos acc path fuel with
    | .ok acc' =>
      (∀ nm ∈ acc'.toList, nm ≠ "." ∧ nm ≠ "..") ∧
      (acc'.size > acc.size → bs.size > 0)
    | .error e => nonLockErrOk e := by
  induction fuel generalizing pos acc with
  | zero =>
    unfold SysBridge.parseDirents64Aux
    exact nonLockErrOk_mapErrno _ _ _
  | succ f ih =>
    unfold SysBridge.parseDirents64Aux
    by_cases hEnd : (pos == bs.size) = true
    · simp only [hEnd, ↓reduceIte]
      exact ⟨hAcc, fun hGt => by omega⟩
    · simp only [hEnd, Bool.false_eq_true, ↓reduceIte]
      cases hOne : SysBridge.parseDirent64One bs pos with
      | none => exact nonLockErrOk_mapErrno _ _ _
      | some p =>
        rcases p with ⟨nameBytes, nextPos⟩
        dsimp only
        have hBsPos : bs.size > 0 := by
          unfold SysBridge.parseDirent64One at hOne
          split at hOne
          · cases hOne
          · omega
        cases hUtf : String.fromUTF8? nameBytes with
        | none =>
          dsimp only [nonLockErrOk]
          refine ⟨?_, fun hc => by cases hc⟩
          change ("invalid UTF-8 directory entry in '" ++ toString path ++ "'") ≠ ""
          exact append_ne_empty_left _ _ (append_ne_empty_left _ _ (by decide))
        | some nm =>
          dsimp only
          have hAcc' : ∀ x ∈ (if (nm == "." || nm == "..") = true then acc else acc.push nm).toList,
              x ≠ "." ∧ x ≠ ".." := by
            by_cases hDot : (nm == "." || nm == "..") = true
            · simp only [hDot, ↓reduceIte]; exact hAcc
            · simp only [hDot, Bool.false_eq_true, ↓reduceIte, Array.toList_push, List.mem_append,
                List.mem_singleton]
              intro x hx
              rcases hx with hOld | rfl
              · exact hAcc x hOld
              · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hDot
                exact hDot
          have hSub := ih nextPos (if (nm == "." || nm == "..") = true then acc else acc.push nm) hAcc'
          cases hRec : SysBridge.parseDirents64Aux bs nextPos
              (if (nm == "." || nm == "..") = true then acc else acc.push nm) path f with
          | error e => rw [hRec] at hSub; exact hSub
          | ok acc' =>
            rw [hRec] at hSub
            exact ⟨hSub.1, fun _ => hBsPos⟩

/-- `SysBridge.parseUniqueEntryNames` preserves `nonLockErrOk` on error and requires non-empty input for non-empty output. -/
theorem parseUniqueEntryNames_props (raw : Array String) :
    match SysBridge.parseUniqueEntryNames raw with
    | .ok xs => xs.size > 0 → raw.size > 0
    | .error e => nonLockErrOk e := by
  by_cases hEmpty : raw.size = 0
  · have hEq : raw = #[] := Array.eq_empty_of_size_eq_zero hEmpty
    subst hEq
    change (match Except.ok (#[] : Array EntryName) with
      | Except.ok xs => xs.size > 0 → (#[] : Array String).size > 0
      | Except.error e => nonLockErrOk e)
    intro hGt; simp at hGt
  · cases hRes : SysBridge.parseUniqueEntryNames raw with
    | ok xs => intro _; omega
    | error e =>
      unfold SysBridge.parseUniqueEntryNames at hRes
      have hInv : ∀ (xs : List String) (acc : Array EntryName),
          (forIn (m := Except FsError) xs acc fun s out => do
            let name ← EntryName.parse s
            if !out.contains name then pure (.yield (out.push name)) else pure (.yield out)) =
              Except.error e →
          nonLockErrOk e := by
        intro xs
        induction xs with
        | nil => intro acc h; simp [Pure.pure, Except.pure] at h
        | cons x rest ih =>
          intro acc h
          rw [List.forIn_cons] at h
          cases hP : EntryName.parse x with
          | error pe =>
            simp only [Bind.bind, Except.bind, hP] at h
            cases h
            unfold EntryName.parse at hP
            split at hP
            · cases hP
            · cases hP
              refine ⟨?_, fun hc => by cases hc⟩
              dsimp only
              exact append_ne_empty_left _ _ (append_ne_empty_left _ _ (by decide))
          | ok nm =>
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hP] at h
            by_cases hC : (!acc.contains nm) = true
            · simp only [hC, ↓reduceIte] at h; exact ih (acc.push nm) h
            · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h; exact ih acc h
      have hFor : (forIn (m := Except FsError) raw #[] fun s out => do
          let name ← EntryName.parse s
          if !out.contains name then pure (.yield (out.push name)) else pure (.yield out)) =
            Except.error e := by
        have hId : ∀ (x : Except FsError (Array EntryName)), (x >>= pure) = x := fun x => by
          cases x <;> rfl
        rw [hId] at hRes
        exact hRes
      rw [← Array.forIn_toList] at hFor
      exact hInv raw.toList #[] hFor

/-- `SysBridge.renderAbsRev` always produces an absolute path (`isAbsolute = true`). -/
theorem renderAbsRev_isAbsolute (rev : List String) :
    isAbsolute (SysBridge.renderAbsRev rev) = true := by
  unfold SysBridge.renderAbsRev isAbsolute
  cases hE : rev.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append]
    rfl
  · simp only [↓reduceIte]
    rfl

/-- Helper to unpack any single `FilesOpsM` method call from `Core.ObeysStep` over `HealthyFilesCapM`. -/
theorem cap_method_step {W α : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (req : FilesReq) (act : StateM W (Except Errno α)) (toOut : Except Errno α → FilesOutcome)
    (hExec : execFilesReq cap.files req = toOut <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env req (toOut p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq := by
  have h := cap_fileReq_raw hCap req hWf
  rw [hExec] at h
  simpa [Functor.map, StateT.map, StateT.run] using h

/-- `SysBridge.closeQuiet` always executes `.close h`, popping `h` from `h :: held`, and stays confined. -/
theorem closeQuiet_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.closeQuiet cap.files h).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ co,
      HealthyFilesSteps (proj s).env [(.close h, co)] (proj p.2).env ∧
      TraceFds (h :: held) [(.close h, co)] held ∧
      SubtreeConfinedReq (.close h) := by
  have hC := cap_method_step hCap (.close h) (cap.files.close h) outcomeOfUnit rfl hWf
  cases hR : cap.files.close h s with
  | mk res s1 =>
    have hC' : fsWorldWf (proj s1) = true ∧
        healthyStep (proj s).env (.close h) (outcomeOfUnit res) = some (proj s1).env ∧
        (proj s1).tempSeq = (proj s).tempSeq := by
      simpa [StateT.run, hR] using hC
    unfold SysBridge.closeQuiet
    simp only [Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure, hR]
    refine ⟨hC'.1, hC'.2.2, outcomeOfUnit res, healthyFilesSteps_single hC'.2.1, ?_, trivial⟩
    exact traceFds_close_head (by cases res <;> rfl) rfl

/-- `SysBridge.closeCheck` always executes `.close h`, popping `h` from `h :: held`, and yields `nonLockErrOk` on error. -/
theorem closeCheck_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path? : Option String) (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.closeCheck cap.files h path?).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    (match p.1 with | .ok () => True | .error e => nonLockErrOk e) ∧
    ∃ co,
      HealthyFilesSteps (proj s).env [(.close h, co)] (proj p.2).env ∧
      TraceFds (h :: held) [(.close h, co)] held ∧
      SubtreeConfinedReq (.close h) := by
  have hC := cap_method_step hCap (.close h) (cap.files.close h) outcomeOfUnit rfl hWf
  cases hR : cap.files.close h s with
  | mk res s1 =>
    have hC' : fsWorldWf (proj s1) = true ∧
        healthyStep (proj s).env (.close h) (outcomeOfUnit res) = some (proj s1).env ∧
        (proj s1).tempSeq = (proj s).tempSeq := by
      simpa [StateT.run, hR] using hC
    unfold SysBridge.closeCheck
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hPost : ∃ co,
        HealthyFilesSteps (proj s).env [(.close h, co)] (proj s1).env ∧
        TraceFds (h :: held) [(.close h, co)] held ∧
        SubtreeConfinedReq (.close h) :=
      ⟨outcomeOfUnit res, healthyFilesSteps_single hC'.2.1,
       traceFds_close_head (by cases res <;> rfl) rfl, trivial⟩
    cases res with
    | ok u =>
      cases u
      simp only [Pure.pure, StateT.pure]
      exact ⟨hC'.1, hC'.2.2, trivial, hPost⟩
    | error e =>
      by_cases hEin : (e == Errno.EINTR) = true
      · simp only [hEin, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨hC'.1, hC'.2.2, trivial, hPost⟩
      · simp only [hEin, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨hC'.1, hC'.2.2, nonLockErrOk_mapErrno _ _ _, hPost⟩

/-- Trace specification for `SysBridge.readAllChunksLoop`: reads exact `readBytesOn h trRead` to 0-byte EOF and always closes `h`. -/
theorem readAllChunksLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (held : List HandleId)
    (chunks : Array ByteArray) (total fuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readAllChunksLoop cap.files h path chunks total fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trRead trClose,
      HealthyFilesSteps (proj s).env (trRead ++ trClose) (proj p.2).env ∧
      TraceFds (h :: held) trRead (h :: held) ∧
      TraceFds (h :: held) trClose held ∧
      (∀ step ∈ trRead ++ trClose, SubtreeConfinedReq step.1) ∧
      (∃ co, trClose = [(.close h, co)]) ∧
      match p.1 with
      | .ok bs =>
        (∃ eof, (.read h 65536, .bytes eof) ∈ trRead ∧ eof.size = 0) ∧
        chunks.toList.foldl (· ++ ·) ByteArray.empty ++ readBytesOn h trRead = bs
      | .error e => nonLockErrOk e := by
  induction fuel generalizing chunks total s with
  | zero =>
    unfold SysBridge.readAllChunksLoop
    have hQ := closeQuiet_trace hCap h held hWf
    cases hR : (SysBridge.closeQuiet cap.files h s) with
    | mk u s1 =>
      rw [StateT.run] at hQ; rw [hR] at hQ; dsimp only at hQ
      obtain ⟨hWf1, hTmp1, co, hSt, hFd, hConf⟩ := hQ
      simp only [Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure, hR]
      exact ⟨hWf1, hTmp1, [], [(.close h, co)], hSt, TraceFds.nil _, hFd,
        confined_single hConf, ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
  | succ f ih =>
    unfold SysBridge.readAllChunksLoop
    have hRd := cap_method_step hCap (.read h SysBridge.READ_CHUNK_SIZE)
      (cap.files.read h SysBridge.READ_CHUNK_SIZE) outcomeOfBytes rfl hWf
    cases hR : cap.files.read h SysBridge.READ_CHUNK_SIZE s with
    | mk res s1 =>
      have hRd' : fsWorldWf (proj s1) = true ∧
          healthyStep (proj s).env (.read h 65536) (outcomeOfBytes res) = some (proj s1).env ∧
          (proj s1).tempSeq = (proj s).tempSeq := by
        rw [StateT.run] at hRd; rw [hR] at hRd; simpa [SysBridge.READ_CHUNK_SIZE] using hRd
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases res with
      | error e =>
        by_cases hRetry : (e == Errno.EINTR || e == Errno.EAGAIN) = true
        · simp only [hRetry, ↓reduceIte]
          have hIh := ih chunks total hRd'.1
          cases hO : (SysBridge.readAllChunksLoop cap.files h path chunks total f s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, trR, trC, hSt2, hFdR, hFdC, hConf2, hCeq, hOut2⟩ := hIh
            refine ⟨hWf2, hTmp2.trans hRd'.2.2, (.read h 65536, .err e) :: trR, trC,
              HealthyFilesSteps.cons _ _ _ hRd'.2.1 hSt2,
              TraceFds.step (by rfl) hFdR, hFdC, confined_cons trivial hConf2, hCeq, ?_⟩
            cases r2 with
            | error err => exact hOut2
            | ok bs =>
              obtain ⟨⟨eof, hMem, hZ⟩, hEq⟩ := hOut2
              refine ⟨⟨eof, List.mem_cons_of_mem _ hMem, hZ⟩, ?_⟩
              have hStepMiss : readBytesOn h [(.read h 65536, .err e)] = ByteArray.empty :=
                readBytesOn_step_miss h _ (fun _ _ hc => by cases hc)
              have hApp : readBytesOn h ((.read h 65536, .err e) :: trR) = readBytesOn h trR := by
                change readBytesOn h ([(.read h 65536, .err e)] ++ trR) = _
                rw [readBytesOn_append, hStepMiss, byteArray_empty_append]
              rw [hApp]; exact hEq
        · simp only [hRetry, Bool.false_eq_true, ↓reduceIte]
          have hQ := closeQuiet_trace hCap h held hRd'.1
          cases hRq : (SysBridge.closeQuiet cap.files h s1) with
          | mk u s2 =>
            rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
            obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
            simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
            exact ⟨hWf2, hTmp2.trans hRd'.2.2, [(.read h 65536, .err e)], [(.close h, co)],
              HealthyFilesSteps.cons _ _ _ hRd'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
              confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
      | ok chunk =>
        by_cases hZ : (chunk.size == 0) = true
        · simp only [hZ, ↓reduceIte]
          have hZ0 : chunk.size = 0 := beq_iff_eq.mp hZ
          have hChunkEmp : chunk = ByteArray.empty := by
            apply ByteArray.ext
            exact Array.eq_empty_of_size_eq_zero hZ0
          have hCc := closeCheck_trace hCap h (some path) held hRd'.1
          cases hRc : (SysBridge.closeCheck cap.files h (some path) s1) with
          | mk cres s2 =>
            rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
            obtain ⟨hWf2, hTmp2, hErrOk, co, hStC, hFdC, _⟩ := hCc
            simp only [Bind.bind, StateT.bind, hRc]
            have hSteps : HealthyFilesSteps (proj s).env ([(.read h 65536, .bytes chunk)] ++ [(.close h, co)]) (proj s2).env :=
              HealthyFilesSteps.cons _ _ _ hRd'.2.1 hStC
            have hConf := confined_cons (s := (.read h 65536, .bytes chunk)) trivial (confined_single (s := (.close h, co)) trivial)
            cases cres with
            | error ce =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf2, hTmp2.trans hRd'.2.2, [(.read h 65536, .bytes chunk)], [(.close h, co)],
                hSteps, traceFds_nonFd_step rfl rfl, hFdC, hConf, ⟨co, rfl⟩, hErrOk⟩
            | ok u =>
              cases u
              simp only [Pure.pure, StateT.pure]
              refine ⟨hWf2, hTmp2.trans hRd'.2.2, [(.read h 65536, .bytes chunk)], [(.close h, co)],
                hSteps, traceFds_nonFd_step rfl rfl, hFdC, hConf, ⟨co, rfl⟩,
                ⟨chunk, List.mem_singleton.mpr rfl, hZ0⟩, ?_⟩
              rw [readBytesOn_read_hit, hChunkEmp, byteArray_append_empty, concatChunks_eq_foldl]
        · simp only [hZ, Bool.false_eq_true, ↓reduceIte]
          have hIh := ih (chunks.push chunk) (total + chunk.size) hRd'.1
          cases hO : (SysBridge.readAllChunksLoop cap.files h path (chunks.push chunk) (total + chunk.size) f s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, trR, trC, hSt2, hFdR, hFdC, hConf2, hCeq, hOut2⟩ := hIh
            refine ⟨hWf2, hTmp2.trans hRd'.2.2, (.read h 65536, .bytes chunk) :: trR, trC,
              HealthyFilesSteps.cons _ _ _ hRd'.2.1 hSt2,
              TraceFds.step (by rfl) hFdR, hFdC, confined_cons trivial hConf2, hCeq, ?_⟩
            cases r2 with
            | error err => exact hOut2
            | ok bs =>
              obtain ⟨⟨eof, hMem, hEz⟩, hEq⟩ := hOut2
              refine ⟨⟨eof, List.mem_cons_of_mem _ hMem, hEz⟩, ?_⟩
              have hApp : readBytesOn h ((.read h 65536, .bytes chunk) :: trR) = chunk ++ readBytesOn h trR := by
                change readBytesOn h ([(.read h 65536, .bytes chunk)] ++ trR) = _
                rw [readBytesOn_append, readBytesOn_read_hit]
              rw [hApp, ← byteArray_append_assoc]
              simpa [Array.toList_push, List.foldl_append] using hEq

/-- Trace specification for `SysBridge.readRegularFd`: validates `.reg` via `fstat`, clears `O_NONBLOCK`, reads exact payload to EOF, and closes `h`. -/
theorem readRegularFd_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (held : List HandleId) (streamFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readRegularFd cap.files h path streamFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trBody trClose,
      HealthyFilesSteps (proj s).env (trBody ++ trClose) (proj p.2).env ∧
      TraceFds (h :: held) trBody (h :: held) ∧
      TraceFds (h :: held) trClose held ∧
      (∀ step ∈ trBody ++ trClose, SubtreeConfinedReq step.1) ∧
      (∃ co, trClose = [(.close h, co)]) ∧
      match p.1 with
      | .ok bs =>
        (∃ rawSt, (.fstat h, .statted rawSt) ∈ trBody ∧ rawSt.kind = .reg) ∧
        (∃ eof, (.read h 65536, .bytes eof) ∈ trBody ∧ eof.size = 0) ∧
        readBytesOn h trBody = bs
      | .error e => nonLockErrOk e := by
  unfold SysBridge.readRegularFd
  have hFs := cap_method_step hCap (.fstat h) (cap.files.fstat h) outcomeOfStatted rfl hWf
  cases hR : cap.files.fstat h s with
  | mk res s1 =>
    have hFs' : fsWorldWf (proj s1) = true ∧
        healthyStep (proj s).env (.fstat h) (outcomeOfStatted res) = some (proj s1).env ∧
        (proj s1).tempSeq = (proj s).tempSeq := by
      simpa [StateT.run, hR] using hFs
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    cases res with
    | error e =>
      have hQ := closeQuiet_trace hCap h held hFs'.1
      cases hRq : (SysBridge.closeQuiet cap.files h s1) with
      | mk u s2 =>
        rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
        obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
        simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
        exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .err e)], [(.close h, co)],
          HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
          confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
    | ok st =>
      by_cases hDir : (st.kind == .dir) = true
      · simp only [hDir, ↓reduceIte]
        have hQ := closeQuiet_trace hCap h held hFs'.1
        cases hRq : (SysBridge.closeQuiet cap.files h s1) with
        | mk u s2 =>
          rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
          obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
          simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
          exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .statted st)], [(.close h, co)],
            HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
            confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
      · by_cases hNReg : (st.kind != .reg) = true
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hNReg]
          have hQ := closeQuiet_trace hCap h held hFs'.1
          cases hRq : (SysBridge.closeQuiet cap.files h s1) with
          | mk u s2 =>
            rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
            obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
            simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
            exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .statted st)], [(.close h, co)],
              HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
              confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hNReg]
          have hKindReg : st.kind = .reg := by
            cases hK : st.kind <;> rw [hK] at hNReg <;> first | rfl | exact absurd (by decide) hNReg
          have hFc := cap_method_step hCap (.fcntl h .getFl) (cap.files.fcntl h .getFl) outcomeOfU32 rfl hFs'.1
          cases hRf : cap.files.fcntl h .getFl s1 with
          | mk fres s2 =>
            have hFc' : fsWorldWf (proj s2) = true ∧
                healthyStep (proj s1).env (.fcntl h .getFl) (outcomeOfU32 fres) = some (proj s2).env ∧
                (proj s2).tempSeq = (proj s1).tempSeq := by
              simpa [StateT.run, hRf] using hFc
            simp only [Bind.bind, StateT.bind, hRf]
            cases fres with
            | error fe =>
              have hQ := closeQuiet_trace hCap h held hFc'.1
              cases hRq : (SysBridge.closeQuiet cap.files h s2) with
              | mk u s3 =>
                rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
                obtain ⟨hWf3, hTmp3, co, hStC, hFdC, _⟩ := hQ
                simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
                exact ⟨hWf3, hTmp3.trans (hFc'.2.2.trans hFs'.2.2),
                  [(.fstat h, .statted st), (.fcntl h .getFl, .err fe)], [(.close h, co)],
                  HealthyFilesSteps.cons _ _ _ hFs'.2.1 (HealthyFilesSteps.cons _ _ _ hFc'.2.1 hStC),
                  TraceFds.step (by rfl) (traceFds_nonFd_step rfl rfl), hFdC,
                  confined_cons trivial (confined_cons trivial (confined_single trivial)),
                  ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
            | ok fl =>
              dsimp only
              have hFinish : ∀ {sX : W} {pre : List KernelStep},
                  fsWorldWf (proj sX) = true →
                  (proj sX).tempSeq = (proj s).tempSeq →
                  HealthyFilesSteps (proj s).env pre (proj sX).env →
                  TraceFds (h :: held) pre (h :: held) →
                  (∀ step ∈ pre, SubtreeConfinedReq step.1) →
                  (.fstat h, .statted st) ∈ pre →
                  readBytesOn h pre = ByteArray.empty →
                  let p := (SysBridge.readAllChunksLoop cap.files h path #[] 0 streamFuel).run sX
                  fsWorldWf (proj p.2) = true ∧ (proj p.2).tempSeq = (proj s).tempSeq ∧
                  ∃ trBody trClose,
                    HealthyFilesSteps (proj s).env (trBody ++ trClose) (proj p.2).env ∧
                    TraceFds (h :: held) trBody (h :: held) ∧
                    TraceFds (h :: held) trClose held ∧
                    (∀ step ∈ trBody ++ trClose, SubtreeConfinedReq step.1) ∧
                    (∃ co, trClose = [(.close h, co)]) ∧
                    match p.1 with
                    | .ok bs =>
                      (∃ rawSt, (.fstat h, .statted rawSt) ∈ trBody ∧ rawSt.kind = .reg) ∧
                      (∃ eof, (.read h 65536, .bytes eof) ∈ trBody ∧ eof.size = 0) ∧
                      readBytesOn h trBody = bs
                    | .error e => nonLockErrOk e := by
                intro sX pre hWfX hTmpX hStX hFdX hConfX hMemFs hEmptyPre
                have hRdLoop := readAllChunksLoop_trace hCap h path held #[] 0 streamFuel hWfX
                cases hO : (SysBridge.readAllChunksLoop cap.files h path #[] 0 streamFuel sX) with
                | mk rF sF =>
                  simp only [StateT.run, hO] at hRdLoop ⊢
                  obtain ⟨hWfF, hTmpF, trR, trC, hStF, hFdR, hFdC, hConfF, hCeq, hOutF⟩ := hRdLoop
                  refine ⟨hWfF, hTmpF.trans hTmpX, pre ++ trR, trC,
                    by rw [List.append_assoc]; exact healthyFilesSteps_append hStX hStF,
                    traceFds_append hFdX hFdR, hFdC,
                    by rw [List.append_assoc]; exact confined_append hConfX hConfF, hCeq, ?_⟩
                  cases rF with
                  | error e => exact hOutF
                  | ok bs =>
                    obtain ⟨⟨eof, hMemE, hEz⟩, hEq⟩ := hOutF
                    refine ⟨⟨st, List.mem_append_left _ hMemFs, hKindReg⟩,
                      ⟨eof, List.mem_append_right _ hMemE, hEz⟩, ?_⟩
                    rw [readBytesOn_append, hEmptyPre, byteArray_empty_append]
                    simpa [byteArray_empty_append] using hEq
              have hPre2 : HealthyFilesSteps (proj s).env [(.fstat h, .statted st), (.fcntl h .getFl, .u32 fl)] (proj s2).env :=
                HealthyFilesSteps.cons _ _ _ hFs'.2.1 (healthyFilesSteps_single hFc'.2.1)
              have hFd2 : TraceFds (h :: held) [(.fstat h, .statted st), (.fcntl h .getFl, .u32 fl)] (h :: held) :=
                TraceFds.step (by rfl) (traceFds_nonFd_step rfl rfl)
              have hConf2 := confined_cons (s := (.fstat h, .statted st)) trivial
                (confined_single (s := (.fcntl h .getFl, .u32 fl)) trivial)
              have hRdEmpty2 : readBytesOn h [(.fstat h, .statted st), (.fcntl h .getFl, .u32 fl)] = ByteArray.empty := rfl
              by_cases hNb : ((fl &&& ((1 : UInt32) <<< 8)) != 0) = true
              · simp only [hNb, ↓reduceIte]
                have hSet := cap_method_step hCap (.fcntl h (.setFl false ((fl &&& ((1 : UInt32) <<< 5)) != 0)))
                  (cap.files.fcntl h (.setFl false ((fl &&& ((1 : UInt32) <<< 5)) != 0))) outcomeOfU32 rfl hFc'.1
                cases hRs : cap.files.fcntl h (.setFl false ((fl &&& ((1 : UInt32) <<< 5)) != 0)) s2 with
                | mk sres s3 =>
                  have hSet' : fsWorldWf (proj s3) = true ∧
                      healthyStep (proj s2).env (.fcntl h (.setFl false ((fl &&& ((1 : UInt32) <<< 5)) != 0))) (outcomeOfU32 sres) = some (proj s3).env ∧
                      (proj s3).tempSeq = (proj s2).tempSeq := by
                    rw [StateT.run] at hSet; rw [hRs] at hSet; exact hSet
                  simp only [Bind.bind, StateT.bind, hRs]
                  cases sres with
                  | error se =>
                    have hQ := closeQuiet_trace hCap h held hSet'.1
                    cases hRq : (SysBridge.closeQuiet cap.files h s3) with
                    | mk u s4 =>
                      rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
                      obtain ⟨hWf4, hTmp4, co, hStC, hFdC, _⟩ := hQ
                      simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
                      exact ⟨hWf4, hTmp4.trans (hSet'.2.2.trans (hFc'.2.2.trans hFs'.2.2)),
                        [(.fstat h, .statted st), (.fcntl h .getFl, .u32 fl),
                         (.fcntl h (.setFl false ((fl &&& ((1 : UInt32) <<< 5)) != 0)), .err se)], [(.close h, co)],
                        HealthyFilesSteps.cons _ _ _ hFs'.2.1 (HealthyFilesSteps.cons _ _ _ hFc'.2.1
                          (HealthyFilesSteps.cons _ _ _ hSet'.2.1 hStC)),
                        TraceFds.step (by rfl) (TraceFds.step (by rfl) (traceFds_nonFd_step rfl rfl)),
                        hFdC, confined_cons trivial (confined_cons trivial (confined_cons trivial (confined_single trivial))),
                        ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
                  | ok fl2 =>
                    exact hFinish hSet'.1 (hSet'.2.2.trans (hFc'.2.2.trans hFs'.2.2))
                      (healthyFilesSteps_append hPre2 (healthyFilesSteps_single hSet'.2.1))
                      (traceFds_append hFd2 (traceFds_nonFd_step rfl rfl))
                      (confined_append hConf2 (confined_single trivial))
                      (by simp)
                      (by rw [readBytesOn_append, hRdEmpty2]; rfl)
              · simp only [hNb, Bool.false_eq_true, ↓reduceIte]
                exact hFinish hFc'.1 (hFc'.2.2.trans hFs'.2.2) hPre2 hFd2 hConf2 (by simp) hRdEmpty2

end LeanSwe.Fs.Proofs

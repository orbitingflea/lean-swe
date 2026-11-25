import LeanSwe.Fs.Proofs.SysBridgeScopedRefines
import LeanSwe.Fs.Proofs.SysBridgeDirRefines

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Substitute an equal `(result, state)` pair into an `FsWorldTrace` postcondition. -/
theorem fsTrace_pair_subst {W α : Type} {proj : W → FsWorld} {s0 : W}
    (P : α → List KernelStep → Prop)
    {r1 r2 : α} {s1 s2 : W} (hEq : (r1, s1) = (r2, s2))
    (h : ∃ tr, FsWorldTrace (proj s0) tr (proj s2) ∧ P r2 tr) :
    ∃ tr, FsWorldTrace (proj s0) tr (proj s1) ∧ P r1 tr := by
  cases hEq; exact h

/-- `StatTrace` always has a non-empty kernel trace. -/
theorem statTrace_nonEmpty {d : Option HandleId} {p : ByteArray} {f : Bool} {st : FileStat} {tr : List KernelStep}
    (h : StatTrace d p f st tr) : tr ≠ [] := by
  obtain ⟨rawSt, hm, _⟩ := h
  intro hNil; rw [hNil] at hm; cases hm

/-- `ReadRegularTrace` always has a non-empty kernel trace. -/
theorem readRegularTrace_nonEmpty {d : Option HandleId} {p : ByteArray} {fl : OpenFlags} {bs : ByteArray} {tr : List KernelStep}
    (h : ReadRegularTrace d p fl bs tr) : tr ≠ [] := by
  obtain ⟨hFd, _, _, trO, trB, trC, rfl, hMemO, _⟩ := h
  intro hNil
  have hm : (.openat d p fl 0, .opened hFd) ∈ trO ++ trB ++ trC :=
    List.mem_append_left _ (List.mem_append_left _ hMemO)
  rw [hNil] at hm; cases hm

/-- `ReadDirTrace` always has a non-empty kernel trace. -/
theorem readDirTrace_nonEmpty {p : ByteArray} {xs : Array String} {tr : List KernelStep}
    (h : ReadDirTrace p xs tr) : tr ≠ [] := by
  obtain ⟨_, hFd, _, trO, trB, trC, rfl, hMemO, _⟩ := h
  intro hNil
  have hm : (.openat none p dirOpenFlags 0, .opened hFd) ∈ trO ++ trB ++ trC :=
    List.mem_append_left _ (List.mem_append_left _ hMemO)
  rw [hNil] at hm; cases hm

/-- `UnlinkTrace` is preserved when appending traces on the left. -/
theorem unlinkTrace_append_right {d : Option HandleId} {p : ByteArray} {rd : Bool} {tr1 tr2 : List KernelStep}
    (h : UnlinkTrace d p rd tr2) : UnlinkTrace d p rd (tr1 ++ tr2) :=
  List.mem_append_right tr1 h

/-- `MkdirOkTrace` is preserved when appending a trace on the left. -/
theorem mkdirOkTrace_append_right {p : String} {ex : Bool} {tr1 tr2 : List KernelStep}
    (h : MkdirOkTrace p ex tr2) : MkdirOkTrace p ex (tr1 ++ tr2) := by
  rcases h with hMk | ⟨hEx, rawSt, nf, hm, hd⟩
  · exact Or.inl (List.mem_append_right tr1 hMk)
  · exact Or.inr ⟨hEx, rawSt, nf, List.mem_append_right tr1 hm, hd⟩

/-- `MkdirOkTrace` is preserved when appending a trace on the right. -/
theorem mkdirOkTrace_append_left {p : String} {ex : Bool} {tr1 tr2 : List KernelStep}
    (h : MkdirOkTrace p ex tr1) : MkdirOkTrace p ex (tr1 ++ tr2) := by
  rcases h with hMk | ⟨hEx, rawSt, nf, hm, hd⟩
  · exact Or.inl (List.mem_append_left tr2 hMk)
  · exact Or.inr ⟨hEx, rawSt, nf, List.mem_append_left tr2 hm, hd⟩

/-- Extract `rawSt.kind = .dir` from `(toFileStat rawSt).kind == .dir`. -/
theorem rawKind_dir_of_toFileStat {rawSt : StatInfo} {st : FileStat}
    (hEq : st = toFileStat rawSt) (hDir : (st.kind == .dir) = true) : rawSt.kind = .dir := by
  rw [hEq] at hDir; dsimp only [toFileStat] at hDir
  cases hK : rawSt.kind <;> rw [hK] at hDir <;> first | rfl | exact absurd hDir (by decide)

/-- `toFileStat` maps `.file` equality to `.reg` equality. -/
theorem toFileStat_kind_file (rawSt : StatInfo) : ((toFileStat rawSt).kind == .file) = (rawSt.kind == .reg) := by
  dsimp only [toFileStat]; cases rawSt.kind <;> rfl

/-- `toFileStat` maps `.dir` equality directly. -/
theorem toFileStat_kind_dir_beq (rawSt : StatInfo) : ((toFileStat rawSt).kind == .dir) = (rawSt.kind == .dir) := by
  dsimp only [toFileStat]; cases rawSt.kind <;> rfl

/-- `toFileStat` maps `.symlink` equality directly. -/
theorem toFileStat_kind_symlink_beq (rawSt : StatInfo) : ((toFileStat rawSt).kind == .symlink) = (rawSt.kind == .symlink) := by
  dsimp only [toFileStat]; cases rawSt.kind <;> rfl

/-- Unpack `stat` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_stat {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (follow : Bool) (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.stat follow path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok st => StatTrace none path.toUTF8 follow st tr
      | .error e =>
        nonLockErrOk e ∧ ∃ err, (.fstatat none path.toUTF8 { symlinkNofollow := !follow }, .err err) ∈ tr ∧
          (e.kind = .notFound → err = Errno.ENOENT) := by
  have h := hOps s (.stat follow path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.stat follow path s); rw [hEq] at h; exact h

/-- Unpack `readDir` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_readDir {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.readDir path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok xs => ReadDirTrace path.toUTF8 xs tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.readDir path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.readDir path s); rw [hEq] at h; exact h

/-- Unpack `createDir` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_createDir {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.createDir path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => MkdirTrace none path.toUTF8 0o777 tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.createDir path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.createDir path s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `removeDir` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_removeDir {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.removeDir path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => UnlinkTrace none path.toUTF8 true tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.removeDir path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.removeDir path s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `unlinkFile` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_unlinkFile {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.unlinkFile path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => UnlinkTrace none path.toUTF8 false tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.unlinkFile path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.unlinkFile path s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `readBytes` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_readBytes {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.readBytes path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok bs => ReadRegularTrace none path.toUTF8 readOpenFlags bs tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput)) := by
  have h := hOps s (.readBytes path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.readBytes path s); rw [hEq] at h; exact h

/-- Unpack `writeBytes` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_writeBytes {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (data : ByteArray) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.writeBytes path data).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => WriteFileTrace none path.toUTF8 writeOpenFlags 0o666 data tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.writeBytes path data) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.writeBytes path data s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `createFileNew` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_createFileNew {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (data : ByteArray) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.createFileNew path data).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => WriteFileTrace none path.toUTF8 createNewOpenFlags 0o644 data tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput)) := by
  have h := hOps s (.createFileNew path data) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.createFileNew path data s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `appendText` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_appendText {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path content : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.appendText path content).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => WriteFileTrace none path.toUTF8 appendOpenFlags 0o666 content.toUTF8 tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.appendText path content) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.appendText path content s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `rename` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_rename {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (src dst : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.rename src dst).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok () => RenameTrace none src.toUTF8 none dst.toUTF8 tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s (.rename src dst) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.rename src dst s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r with | ok u => cases u; exact h | error _ => exact h

/-- Unpack `realPath` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_realPath {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (ops.realPath path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok sOut => RealPathTrace sOut tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (path = "" ∧ e.kind = .notFound) ∨ e.kind = .invalidInput) := by
  have h := hOps s (.realPath path) hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.realPath path s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r <;> exact h

/-- Unpack `cwd` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_cwd {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := ops.cwd.run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok sOut => GetcwdTrace sOut tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  have h := hOps s .cwd hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.cwd s) with | mk r _ => rw [hEq] at h; dsimp only at h ⊢; cases r <;> exact h

/-- Unpack `monotonicNonce` from `RefinesStep` on `ScopedRawFsOpsM`. -/
theorem scoped_monotonicNonce {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := ops.monotonicNonce.run s
    FsWorldTrace (proj s) [] (proj r.2) ∧ (proj r.2).env = (proj s).env ∧
    r.1 = (proj s).tempSeq ∧ (proj r.2).tempSeq = (proj s).tempSeq + 1 := by
  have h := hOps s .monotonicNonce hWf
  simp only [execScopedRawFsStep, Functor.map, StateT.map, StateT.run, Bind.bind, Pure.pure, allowedScopedRawFsStep] at h ⊢
  cases hEq : (ops.monotonicNonce s); rw [hEq] at h; exact h

/-- Trace specification for `Internal.listDirSortedM`. -/
theorem listDirSortedM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.listDirSortedM ops.toNonLockFsOpsM path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧ (proj r.2).tempSeq = (proj s).tempSeq ∧
      match r.1 with
      | .ok xs => List.Pairwise (· ≤ ·) xs.toList ∧ ReadDirTrace path.toUTF8 xs tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.listDirSortedM
  have hR := scoped_readDir hOps path hWf
  cases hEq : (ops.readDir path s) with
  | mk res s1 =>
    rw [StateT.run] at hR; rw [hEq] at hR; dsimp only at hR
    obtain ⟨tr, hTr, hSeq, hOut⟩ := hR
    simp only [Bind.bind, StateT.bind, StateT.run, hEq]
    cases res with
    | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr, hTr, hSeq, hOut⟩
    | ok names =>
      simp only [Pure.pure, StateT.pure]
      obtain ⟨hNoDot, hFd, eof, trO, trB, trC, hTrEq, hMemO, hMemE, hEz, hPos, hC⟩ := hOut
      refine ⟨tr, hTr, hSeq, ?_, ?_, hFd, eof, trO, trB, trC, hTrEq, hMemO, hMemE, hEz, ?_, hC⟩
      · simpa using list_mergeSort_str_le names.toList
      · intro nm hMem
        have hMem' : nm ∈ names.toList.mergeSort (· ≤ ·) := by simpa using hMem
        exact hNoDot nm ((List.mergeSort_perm names.toList (· ≤ ·)).mem_iff.mp hMem')
      · intro hGt
        have hLen : (names.toList.mergeSort (· ≤ ·)).toArray.size = names.size := by
          rw [List.size_toArray, List.length_mergeSort, Array.length_toList]
        rw [hLen] at hGt
        exact hPos hGt

/-- Trace specification for `Internal.ensureDirM`. -/
theorem ensureDirM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (anc : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.ensureDirM ops.toNonLockFsOpsM anc).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => True
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.ensureDirM
  have hS := scoped_stat hOps true anc hWf
  cases hEq : (ops.stat true anc s) with
  | mk res s1 =>
    rw [StateT.run] at hS; rw [hEq] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    simp only [Bind.bind, StateT.bind, StateT.run, hEq]
    cases res with
    | ok st =>
      by_cases hD : (st.kind == .dir) = true
      · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, trivial⟩
      · simp only [hD, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
        exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, statTrace_nonEmpty hOut1⟩
    | error e =>
      have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1, hNe1⟩
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
        have hC := scoped_createDir hOps anc hTr1.1
        cases hEc : (ops.createDir anc s1) with
        | mk rC s2 =>
          rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hC
          simp only [Bind.bind, StateT.bind, hEc]
          cases rC with
          | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, trivial⟩
          | error ce =>
            by_cases hAe : (ce.kind == .alreadyExists) = true
            · simp only [hAe, ↓reduceIte]
              have hS2 := scoped_stat hOps true anc hTr2.1
              cases hEs2 : (ops.stat true anc s2) with
              | mk rS2 s3 =>
                rw [StateT.run] at hS2; rw [hEs2] at hS2; dsimp only at hS2
                obtain ⟨tr3, hTr3, _, _⟩ := hS2
                simp only [Bind.bind, StateT.bind, hEs2]
                have hTr123 := fsWorldTrace_append (fsWorldTrace_append hTr1 hTr2) hTr3
                have hNe123 : (tr1 ++ tr2) ++ tr3 ≠ [] := fun h => hNe1 (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
                cases rS2 with
                | error _ => simp only [Pure.pure, StateT.pure]; exact ⟨(tr1 ++ tr2) ++ tr3, hTr123, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe123⟩
                | ok st2 =>
                  by_cases hD2 : (st2.kind == .dir) = true
                  · simp only [hD2, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨(tr1 ++ tr2) ++ tr3, hTr123, trivial⟩
                  · simp only [hD2, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                    exact ⟨(tr1 ++ tr2) ++ tr3, hTr123, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe123⟩
            · simp only [hAe, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, hOut2.1, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩

/-- Trace specification for `Internal.ensureAncestorsM`. -/
theorem ensureAncestorsM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (ancs : List String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.ensureAncestorsM ops.toNonLockFsOpsM ancs).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => True
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  induction ancs generalizing s with
  | nil =>
    simp only [Internal.ensureAncestorsM, Pure.pure, StateT.pure, StateT.run]
    exact ⟨[], fsWorldTrace_nil hWf, trivial⟩
  | cons anc rest ih =>
    unfold Internal.ensureAncestorsM
    have hE := ensureDirM_trace hOps anc hWf
    cases hEq : (Internal.ensureDirM ops.toNonLockFsOpsM anc s) with
    | mk res s1 =>
      rw [StateT.run] at hE; rw [hEq] at hE; dsimp only at hE
      obtain ⟨tr1, hTr1, hOut1⟩ := hE
      simp only [Bind.bind, StateT.bind, StateT.run, hEq]
      cases res with
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1⟩
      | ok u =>
        cases u; dsimp only
        have hR := ih hTr1.1
        cases hEq2 : (Internal.ensureAncestorsM ops.toNonLockFsOpsM rest s1) with
        | mk res2 s2 =>
          rw [StateT.run] at hR; rw [hEq2] at hR; dsimp only at hR
          obtain ⟨tr2, hTr2, hOut2⟩ := hR
          dsimp only
          refine ⟨tr1 ++ tr2, fsWorldTrace_append hTr1 hTr2, ?_⟩
          cases res2 with
          | ok u2 => cases u2; trivial
          | error e => exact ⟨hOut2.1, fun h => hOut2.2 (List.append_eq_nil_iff.mp h).2⟩

/-- Trace specification for `Internal.createDirExistOkM`. -/
theorem createDirExistOkM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.createDirExistOkM ops.toNonLockFsOpsM path).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => MkdirOkTrace path true tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.createDirExistOkM
  have hC := scoped_createDir hOps path hWf
  cases hEc : (ops.createDir path s) with
  | mk res s1 =>
    rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hC
    simp only [Bind.bind, StateT.bind, StateT.run, hEc]
    cases res with
    | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, Or.inl hOut1⟩
    | error ce =>
      by_cases hAe : (ce.kind != .alreadyExists) = true
      · simp only [hAe, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1⟩
      · simp only [hAe, Bool.false_eq_true, ↓reduceIte]
        have hS := scoped_stat hOps true path hTr1.1
        cases hEs : (ops.stat true path s1) with
        | mk rS s2 =>
          rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
          obtain ⟨tr2, hTr2, _, hOut2⟩ := hS
          simp only [Bind.bind, StateT.bind, hEs]
          have hTr12 := fsWorldTrace_append hTr1 hTr2
          have hNe12 : tr1 ++ tr2 ≠ [] := fun h => hOut1.2 (List.append_eq_nil_iff.mp h).1
          cases rS with
          | error _ => simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, hTr12, hOut1.1, hNe12⟩
          | ok st =>
            by_cases hD : (st.kind == .dir) = true
            · simp only [hD, ↓reduceIte, Pure.pure, StateT.pure]
              obtain ⟨rawSt, hm, hEqSt⟩ := hOut2
              exact ⟨tr1 ++ tr2, hTr12, Or.inr ⟨rfl, rawSt, false, List.mem_append_right tr1 hm, rawKind_dir_of_toFileStat hEqSt hD⟩⟩
            · simp only [hD, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨tr1 ++ tr2, hTr12, hOut1.1, hNe12⟩

/-- Trace specification for `Internal.mkdirImplM`. -/
theorem mkdirImplM_trace {W : Type} {proj : W → FsWorld} {ops : ScopedRawFsOpsM (StateM W)}
    (hOps : Core.ObeysStep proj fsWorldWf (execScopedRawFsStep ops) allowedScopedRawFsStep)
    (path : String) (parents existOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (Internal.mkdirImplM ops.toNonLockFsOpsM path parents existOk).run s
    ∃ tr, FsWorldTrace (proj s) tr (proj r.2) ∧
      match r.1 with
      | .ok () => MkdirOkTrace path existOk tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold Internal.mkdirImplM
  have hS := scoped_stat hOps false path hWf
  cases hEs : (ops.stat false path s) with
  | mk res s1 =>
    rw [StateT.run] at hS; rw [hEs] at hS; dsimp only at hS
    obtain ⟨tr1, hTr1, _, hOut1⟩ := hS
    simp only [Bind.bind, StateT.bind, StateT.run, hEs]
    cases res with
    | ok st =>
      have hNe1 := statTrace_nonEmpty hOut1
      by_cases hEd : (existOk && (st.kind == .dir)) = true
      · simp only [hEd, ↓reduceIte, Pure.pure, StateT.pure]
        have ⟨hExT, hDirT⟩ := (Bool.and_eq_true _ _).mp hEd
        obtain ⟨rawSt, hm, hEqSt⟩ := hOut1
        exact ⟨tr1, hTr1, Or.inr ⟨hExT, rawSt, true, hm, rawKind_dir_of_toFileStat hEqSt hDirT⟩⟩
      · by_cases hEsym : (existOk && (st.kind == .symlink)) = true
        · simp only [hEd, Bool.false_eq_true, ↓reduceIte, hEsym]
          have hExT := ((Bool.and_eq_true _ _).mp hEsym).1
          have hS2 := scoped_stat hOps true path hTr1.1
          cases hEs2 : (ops.stat true path s1) with
          | mk rS2 s2 =>
            rw [StateT.run] at hS2; rw [hEs2] at hS2; dsimp only at hS2
            obtain ⟨tr2, hTr2, _, hOut2⟩ := hS2
            simp only [Bind.bind, StateT.bind, hEs2]
            have hTr12 := fsWorldTrace_append hTr1 hTr2
            have hNe12 : tr1 ++ tr2 ≠ [] := fun h => hNe1 (List.append_eq_nil_iff.mp h).1
            cases rS2 with
            | error _ => simp only [Pure.pure, StateT.pure]; exact ⟨tr1 ++ tr2, hTr12, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe12⟩
            | ok tgtSt =>
              by_cases hTd : (tgtSt.kind == .dir) = true
              · simp only [hTd, ↓reduceIte, Pure.pure, StateT.pure]
                obtain ⟨rawSt, hm, hEqSt⟩ := hOut2
                exact ⟨tr1 ++ tr2, hTr12, Or.inr ⟨hExT, rawSt, false, List.mem_append_right tr1 hm, rawKind_dir_of_toFileStat hEqSt hTd⟩⟩
              · simp only [hTd, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨tr1 ++ tr2, hTr12, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe12⟩
        · simp only [hEd, Bool.false_eq_true, ↓reduceIte, hEsym, Pure.pure, StateT.pure]
          exact ⟨tr1, hTr1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩, hNe1⟩
    | error e =>
      have hNe1 : tr1 ≠ [] := by obtain ⟨_, err, hm, _⟩ := hOut1; intro hN; rw [hN] at hm; cases hm
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨tr1, hTr1, hOut1.1, hNe1⟩
      · have hLeaf : ∀ (sX : W), fsWorldWf (proj sX) = true →
            let q := ((if existOk then Internal.createDirExistOkM ops.toNonLockFsOpsM path else ops.createDir path) : StateM W (Except FsError Unit)).run sX
            ∃ tr, FsWorldTrace (proj sX) tr (proj q.2) ∧
              match q.1 with
              | .ok () => MkdirOkTrace path existOk tr
              | .error e => nonLockErrOk e ∧ tr ≠ [] := by
          intro sX hWX
          cases existOk with
          | true => simpa using createDirExistOkM_trace hOps path hWX
          | false =>
            have hC := scoped_createDir hOps path hWX
            cases hEc : (ops.createDir path sX) with
            | mk rC sY =>
              rw [StateT.run] at hC; rw [hEc] at hC; dsimp only at hC
              obtain ⟨trC, hTrC, _, hOutC⟩ := hC
              simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, hEc]
              exact ⟨trC, hTrC, by cases rC with | ok u => cases u; exact Or.inl hOutC | error ce => exact hOutC⟩
        cases parents with
        | false =>
          simp only [hNf, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          have hL := hLeaf s1 hTr1.1
          cases hEl : ((if existOk then Internal.createDirExistOkM ops.toNonLockFsOpsM path else ops.createDir path) s1) with
          | mk rL s2 =>
            rw [StateT.run] at hL; rw [hEl] at hL; dsimp only at hL
            obtain ⟨trL, hTrL, hOutL⟩ := hL
            dsimp only
            refine ⟨tr1 ++ trL, fsWorldTrace_append hTr1 hTrL, ?_⟩
            cases rL with
            | ok u => cases u; exact mkdirOkTrace_append_right hOutL
            | error ce => exact ⟨hOutL.1, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩
        | true =>
          simp only [hNf, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
          have hA := ensureAncestorsM_trace hOps (Internal.ancestorChain path path.toList.length) hTr1.1
          cases hEa : (Internal.ensureAncestorsM ops.toNonLockFsOpsM (Internal.ancestorChain path path.toList.length) s1) with
          | mk rA s2 =>
            rw [StateT.run] at hA; rw [hEa] at hA; dsimp only at hA
            obtain ⟨trA, hTrA, hOutA⟩ := hA
            simp only [Bind.bind, StateT.bind, hEa]
            have hTr1A := fsWorldTrace_append hTr1 hTrA
            cases rA with
            | error ae =>
              simp only [Pure.pure, StateT.pure]
              exact ⟨tr1 ++ trA, hTr1A, hOutA.1, fun h => hNe1 (List.append_eq_nil_iff.mp h).1⟩
            | ok u =>
              cases u; dsimp only
              have hL := hLeaf s2 hTrA.1
              cases hEl : ((if existOk then Internal.createDirExistOkM ops.toNonLockFsOpsM path else ops.createDir path) s2) with
              | mk rL s3 =>
                rw [StateT.run] at hL; rw [hEl] at hL; dsimp only at hL
                obtain ⟨trL, hTrL, hOutL⟩ := hL
                dsimp only
                refine ⟨(tr1 ++ trA) ++ trL, fsWorldTrace_append hTr1A hTrL, ?_⟩
                cases rL with
                | ok u2 => cases u2; exact mkdirOkTrace_append_right hOutL
                | error ce => exact ⟨hOutL.1, fun h => hNe1 (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1⟩

end LeanSwe.Fs.Proofs

import LeanSweProofs.LinuxSyscall.Files.SpecTests
import LeanSweProofs.LinuxSyscall.Files.SpecMutants.Extra

namespace LeanSwe.LinuxSyscall.Files

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def stubStat (kind : FileKind := .reg) (size : Nat := 0) (mode : Mode := 0o644) (nlink : Nat := 1) : StatInfo :=
  { kind, size, mode, ino := 1, dev := 1, nlink,
    mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }

private def stubUnitOps : FilesOpsM (StateM Unit) Nat :=
  { openat := fun _ _ _ _ => pure (.ok 0)
    openat2 := fun _ _ _ => pure (.ok 0)
    close := fun _ => pure (.ok ())
    read := fun _ _ => pure (.ok (ByteArray.mk #[]))
    write := fun _ data => pure (.ok (UInt32.ofNat data.data.size))
    fstat := fun _ => pure (.ok (stubStat))
    fstatat := fun _ _ _ => pure (.ok (stubStat))
    faccessat := fun _ _ _ _ => pure (.ok ())
    mkdirat := fun _ _ _ => pure (.ok ())
    unlinkat := fun _ _ _ => pure (.ok ())
    renameat2 := fun _ _ _ _ _ => pure (.ok ())
    symlinkat := fun _ _ _ => pure (.ok ())
    readlinkat := fun _ _ _ => pure (.ok (ByteArray.mk #[]))
    getdents64 := fun _ _ => pure (.ok (ByteArray.mk #[]))
    fchmodat := fun _ _ _ => pure (.ok ())
    fchmod := fun _ _ => pure (.ok ())
    flock := fun _ _ => pure (.ok ())
    fcntl := fun _ _ => pure (.ok 0)
    fsync := fun _ => pure (.ok ())
    getcwd := fun _ => pure (.ok (asciiBytes ['/']))
    lseek := fun _ _ _ => pure (.ok 0)
    reopenReadOnly := fun _ => pure (.ok 0)
    dupStdio := fun _ => pure (.ok 0) }

example : ¬ Core.AllPass (test_files_errno_classificationAndTransient
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    FilesErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_files_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EBADF then .invalidArg else FilesErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.EBADF
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_encodersInjective
    (encOpen := fun f => { f with directory := false }.toBits)) := by
  intro h
  have h0 := h { directory := false } { directory := true }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_encodersInjective
    (encResolve := fun r => { r with beneath := false }.toBits)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2 { beneath := false } { beneath := true }
  exact absurd h1.1 (by decide)

example : ¬ Core.AllPass (test_files_statInfo_ofRawTuple_decodesAllKindsAndMasksMode
    (fun t => { StatInfo.ofRawTuple t with mode := t.2.2.1 })) := by
  intro h
  have h0 := h 0 0o100644 1 1 1 0 0 0 0
  exact absurd h0.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_files_statInfo_ofRawTuple_decodesAllKindsAndMasksMode
    (fun t => { StatInfo.ofRawTuple t with kind := .reg })) := by
  intro h
  have h0 := h 0 0o755 1 1 2 0 0 0 0
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_files_ops_embeddedNulRejectedWithEinval stubUnitOps) := by
  intro h
  have h0 := h () none {} {} {} {} 0 false {} 16 (ByteArray.mk #[97, 0, 98]) (by decide)
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_files_ops_embeddedNulRejectedWithEinval
    { stubUnitOps with
      openat := fun _ _ _ _ => pure (.error Errno.EINVAL)
      openat2 := fun _ _ _ => pure (.error Errno.EINVAL)
      fstatat := fun _ _ _ => pure (.error Errno.EINVAL)
      faccessat := fun _ _ _ _ => pure (.error Errno.EINVAL)
      mkdirat := fun _ _ _ => pure (.error Errno.EINVAL)
      unlinkat := fun _ _ _ => pure (.error Errno.EINVAL)
      renameat2 := fun _ _ _ _ _ => pure (.error Errno.EINVAL)
      symlinkat := fun _ _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () none {} {} {} {} 0 false {} 16 (ByteArray.mk #[97, 0, 98]) (by decide)
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_files_ops_openWriteReadStatCloseAndUseAfterClose stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_openWriteReadStatCloseAndUseAfterClose,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_files_ops_openWriteReadStatCloseAndUseAfterClose
    { stubUnitOps with
      openat := fun _ _ flags _ =>
        if flags.excl then pure (.ok 0) else pure (.ok 1)
      fstat := fun _ => pure (.ok (stubStat .reg 11 0o644))
      read := fun _ _ => pure (.ok (ByteArray.mk #[])) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_openWriteReadStatCloseAndUseAfterClose,
    stubUnitOps, stubStat, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_files_ops_openat2_resolveConstraints stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_openat2_resolveConstraints,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_files_ops_openat2_resolveConstraints
    { stubUnitOps with
      openat2 := fun _ _ how =>
        if !how.flags.creat && how.mode != 0 then pure (.error Errno.EINVAL)
        else pure (.ok 0) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_openat2_resolveConstraints,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1.1

example : ¬ Core.AllPass (test_files_ops_openat2_resolveConstraints
    { stubUnitOps with
      openat2 := fun _ _ how =>
        if (!how.flags.creat && how.mode != 0) || (how.flags.creat && how.mode > 0o7777) then
          pure (.error Errno.EINVAL)
        else pure (.ok 0) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_openat2_resolveConstraints,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.1.1

example : ¬ Core.AllPass (test_files_ops_dirLifecycleAndRenameat2 stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_dirLifecycleAndRenameat2,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1.1

example : ¬ Core.AllPass (test_files_ops_dirLifecycleAndRenameat2
    { stubUnitOps with
      mkdirat := fun _ _ _ => pure (.ok ())
      unlinkat := fun _ _ _ => pure (.error Errno.EISDIR)
      getdents64 := fun _ _ => pure (.ok (ByteArray.mk (List.replicate 24 0).toArray)) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_dirLifecycleAndRenameat2,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.1

example : ¬ Core.AllPass (test_files_ops_symlinkReadlinkAndFstatat stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_symlinkReadlinkAndFstatat,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_files_ops_symlinkReadlinkAndFstatat
    { stubUnitOps with
      fstatat := fun _ _ flags =>
        if flags.eaccess then pure (.error Errno.EINVAL)
        else pure (.ok (stubStat (if flags.symlinkNofollow then .symlink else .reg) 8))
      readlinkat := fun _ path cap =>
        if bytesEq path (asciiBytes ['s', 'y', 'm']) then
          pure (.ok (sliceBytes (asciiBytes ['d', 'e', 's', 't', '.', 't', 'x', 't']) 0 cap.toNat))
        else pure (.error Errno.EINVAL) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_symlinkReadlinkAndFstatat,
    stubUnitOps, stubStat, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.2.2.2.2.1.1

example : ¬ Core.AllPass (test_files_ops_chmodAccessFlockFcntlFsyncGetcwd stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_chmodAccessFlockFcntlFsyncGetcwd,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  rcases h.1 with hL | hR
  · cases hL
  · cases hR

example : ¬ Core.AllPass (test_files_ops_chmodAccessFlockFcntlFsyncGetcwd
    { stubUnitOps with
      getcwd := fun cap => if cap == 0 then pure (.error Errno.EINVAL) else pure (.ok (asciiBytes ['/']))
      fstat := fun _ => pure (.ok (stubStat .reg 0 0o600))
      faccessat := fun _ _ mask _ => if mask.exec && !mask.read then pure (.error Errno.EACCES) else pure (.ok ())
      flock := fun _ _ => pure (.ok ()) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_chmodAccessFlockFcntlFsyncGetcwd,
    stubUnitOps, stubStat, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.2.2.2.2.2.2.1.1

example : ¬ Core.AllPass (test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.1

example : ¬ Core.AllPass (test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir
    { stubUnitOps with
      fstatat := fun _ _ _ => pure (.error Errno.ENOENT)
      fstat := fun _ => pure (.ok (stubStat .reg 4 0o644 0))
      read := fun _ _ => pure (.ok (asciiBytes ['k', 'e', 'e', 'p']))
      getdents64 := fun _ _ => pure (.ok (ByteArray.mk #[])) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir,
    stubUnitOps, stubStat, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_files_ops_appendTruncAndCreatEdgeCases stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_appendTruncAndCreatEdgeCases,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  rcases h.1.1 with h1 | h2 | h3
  · cases h1
  · cases h2
  · cases h3

example : ¬ Core.AllPass (test_files_ops_appendTruncAndCreatEdgeCases
    { stubUnitOps with
      openat := fun _ _ flags _ =>
        if flags.creat && flags.directory then pure (.error Errno.EINVAL)
        else pure (.ok 0) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_files_ops_appendTruncAndCreatEdgeCases,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1.1

private theorem splitPathBytesLoop_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    ∀ k i, i + k = path.size →
      splitPathBytesLoop path i 0 [] k = [path]
  | 0, i, hk => by
    have hEq : i = path.size := by omega
    subst hEq
    unfold splitPathBytesLoop
    simp [hPos]
  | k + 1, i, hk => by
    have hi : i < path.size := by omega
    unfold splitPathBytesLoop
    simp only [hi, ↓reduceDIte]
    have hNe : (path[i] == slashByte) = false := by
      have h1 := hNo i hi
      simpa [bne] using h1
    rw [hNe]
    exact splitPathBytesLoop_noSlash path hPos hNo k (i + 1) (by omega)

private theorem splitPathBytes_of_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    splitPathBytes path = (false, [path], false) := by
  unfold splitPathBytes
  have h0 : (path[0] == slashByte) = false := by
    have := hNo 0 hPos
    simpa [bne] using this
  have hLast : (path[path.size - 1] == slashByte) = false := by
    have := hNo (path.size - 1) (Nat.sub_lt hPos Nat.zero_lt_one)
    simpa [bne] using this
  simp only [hPos, ↓reduceDIte, h0, hLast]
  exact congrArg (fun x => (false, x, false))
    (splitPathBytesLoop_noSlash path hPos hNo path.size 0 (Nat.zero_add _))

private def mkRepPath (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (97 : UInt8)).toArray

private theorem hasEmbeddedNulLoop_mkRepPath (n : Nat) :
    ∀ k i : Nat, hasEmbeddedNulLoop (mkRepPath n) i k = false
  | 0, _ => rfl
  | k + 1, i => by
    unfold hasEmbeddedNulLoop
    split
    · rename_i hlt
      have hElem : (mkRepPath n)[i] = (97 : UInt8) := by
        show (mkRepPath n).data[i] = (97 : UInt8)
        unfold mkRepPath
        exact List.getElem_replicate ..
      rw [hElem]
      exact hasEmbeddedNulLoop_mkRepPath n k (i + 1)
    · rfl

private theorem mkRepPath_size (n : Nat) : (mkRepPath n).data.size = n := by
  unfold mkRepPath
  rw [List.size_toArray, List.length_replicate]

private theorem mkRepPath_noSlash (n : Nat) (j : Nat) (hj : j < (mkRepPath n).size) :
    (mkRepPath n)[j] != slashByte := by
  have hElem : (mkRepPath n)[j] = (97 : UInt8) := by
    show (mkRepPath n).data[j] = (97 : UInt8)
    unfold mkRepPath
    exact List.getElem_replicate ..
  rw [hElem]
  rfl

private theorem exists_longSeg :
    ∃ p : ByteArray, hasEmbeddedNul p = false ∧ p.data.size < PATH_MAX ∧
      p.data.size > NAME_MAX ∧ (splitPathBytes p).2.1 = [p] :=
  ⟨mkRepPath 256,
    hasEmbeddedNulLoop_mkRepPath 256 (mkRepPath 256).size 0,
    by rw [mkRepPath_size]; decide,
    by rw [mkRepPath_size]; decide,
    by
      have hPos : 0 < (mkRepPath 256).size := by
        show 0 < (mkRepPath 256).data.size
        rw [mkRepPath_size]
        decide
      rw [splitPathBytes_of_noSlash (mkRepPath 256) hPos (mkRepPath_noSlash 256)]⟩

private theorem exists_maxPath :
    ∃ p : ByteArray, hasEmbeddedNul p = false ∧ p.data.size ≥ PATH_MAX :=
  ⟨mkRepPath 4096,
    hasEmbeddedNulLoop_mkRepPath 4096 (mkRepPath 4096).size 0,
    by rw [mkRepPath_size]; decide⟩

example : ¬ Core.AllPass (test_files_ops_symlinkLoopAndNameTooLong stubUnitOps ()) := by
  intro h
  rcases exists_longSeg with ⟨p1, hp1⟩
  rcases exists_maxPath with ⟨p2, hp2⟩
  have h0 := h p1 hp1 p2 hp2
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_files_ops_symlinkLoopAndNameTooLong
    { stubUnitOps with
      openat := fun _ path _ _ =>
        if path.data.size > NAME_MAX then pure (.error Errno.ENAMETOOLONG)
        else pure (.ok 0)
      fstatat := fun _ path _ =>
        if path.data.size >= PATH_MAX then pure (.error Errno.ENAMETOOLONG)
        else pure (.ok (stubStat .symlink))
      symlinkat := fun target _ _ =>
        if target.data.size >= PATH_MAX then pure (.error Errno.ENAMETOOLONG)
        else pure (.ok ()) } ()) := by
  intro h
  rcases exists_longSeg with ⟨p1, hp1⟩
  rcases exists_maxPath with ⟨p2, hp2⟩
  have h0 := h p1 hp1 p2 hp2
  dsimp only [stubUnitOps, stubStat, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  have hLoop := h0.2.2.2.2.1.1
  change (Except.ok (0 : Nat) : Except Errno Nat) = Except.error Errno.ELOOP at hLoop
  cases hLoop

example : ¬ Core.AllPass (test_files_ops_lseekReopenDupStdioAndOpath stubUnitOps ()) := by
  intro h
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.1

end LeanSwe.LinuxSyscall.Files

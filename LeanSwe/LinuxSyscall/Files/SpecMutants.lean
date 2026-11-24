import LeanSwe.LinuxSyscall.Files.SpecTests
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Files.Proofs.ExecCases

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

private def mkRepPath (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (97 : UInt8)).toArray

private theorem hasEmbeddedNul_replicate_97 :
    ∀ n, (List.replicate n (97 : UInt8)).any (· == (0 : UInt8)) = false
  | 0 => rfl
  | n + 1 => hasEmbeddedNul_replicate_97 n

private theorem witness_longSeg (n : Nat) (h1 : n > 0) (h2 : n < PATH_MAX) (h3 : n > NAME_MAX) :
    hasEmbeddedNul (mkRepPath n) = false ∧ (mkRepPath n).data.size < PATH_MAX ∧
    (mkRepPath n).data.size > NAME_MAX ∧ (splitPathBytes (mkRepPath n)).2.1 = [mkRepPath n] := by
  have hNul : hasEmbeddedNul (mkRepPath n) = false := by
    rw [hasEmbeddedNul_eq_toList_any]
    unfold mkRepPath
    rw [List.toList_toArray]
    exact hasEmbeddedNul_replicate_97 n
  have hSz : (mkRepPath n).data.size = n := by
    unfold mkRepPath
    rw [List.size_toArray, List.length_replicate]
  have hSplit : (splitPathBytes (mkRepPath n)).2.1 = [mkRepPath n] := by
    have hPos : 0 < (mkRepPath n).size := by
      show 0 < (mkRepPath n).data.size
      omega
    have hNo : ∀ j, (hj : j < (mkRepPath n).size) → (mkRepPath n)[j] != slashByte := by
      intro j hj
      have hElem : (mkRepPath n)[j] = (97 : UInt8) := by
        show (mkRepPath n).data[j] = (97 : UInt8)
        unfold mkRepPath
        exact List.getElem_replicate ..
      rw [hElem]
      decide
    rw [splitPathBytes_of_noSlash (mkRepPath n) hPos hNo]
  rw [hSz]
  exact ⟨hNul, h2, h3, hSplit⟩

private theorem witness_maxPath (n : Nat) (h : n ≥ PATH_MAX) :
    hasEmbeddedNul (mkRepPath n) = false ∧ (mkRepPath n).data.size ≥ PATH_MAX := by
  refine ⟨?_, ?_⟩
  · rw [hasEmbeddedNul_eq_toList_any]
    unfold mkRepPath
    rw [List.toList_toArray]
    exact hasEmbeddedNul_replicate_97 n
  · unfold mkRepPath
    rw [List.size_toArray, List.length_replicate]
    exact h

private theorem exists_longSeg :
    ∃ p : ByteArray, hasEmbeddedNul p = false ∧ p.data.size < PATH_MAX ∧
      p.data.size > NAME_MAX ∧ (splitPathBytes p).2.1 = [p] :=
  ⟨mkRepPath 256, witness_longSeg 256 (by decide) (by decide) (by decide)⟩

private theorem exists_maxPath :
    ∃ p : ByteArray, hasEmbeddedNul p = false ∧ p.data.size ≥ PATH_MAX :=
  ⟨mkRepPath 4096, witness_maxPath 4096 (by decide)⟩

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

example : ¬ Core.AllPass (test_files_model_allowedStep_partialReadAndInvariants
    (fun s req out =>
      match req, out with
      | .close _, .unit => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_allowedStep_partialReadAndInvariants
    (fun s req out =>
      match req, out with
      | .getcwd _, .bytes _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_hardenedInvariants
    (fun s req out =>
      match req, out with
      | .openat _ _ _ _, .err e => if e == Errno.EISDIR then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_hardenedInvariants
    (fun s req out =>
      match req, out with
      | .fsync _, .err e => if e == Errno.EINVAL then some s else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_hardenedInvariants
    (fun s req out =>
      match req, out with
      | .getdents64 _ _, .bytes _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_envGeneralizationInvariants
    (fun s req out =>
      match req, out with
      | .openat _ _ _ _, .opened _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_ops_lseekReopenDupStdioAndOpath stubUnitOps ()) := by
  intro h
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.2.2.1

example : ¬ Core.AllPass (test_files_errno_classificationAndTransient
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EROFS then .invalidArg else FilesErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.EROFS
  exact absurd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encOpen := fun f => { f with path := false }.toBits)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.1.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encResolve := fun r => { r with cached := false }.toBits)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.1.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encAt := fun a => { a with eaccess := false }.toBits)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.1.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encAcc := fun m => { m with exec := false }.toBits)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.1.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encRen := fun rn => { rn with whiteout := false }.toBits)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.2.1.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encFlock := fun _ => 0)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encFcntl := fun _ => (0, 0))) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.2.2.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encWhence := fun w => match w with | .seekSet => 2 | .seekCur => 1 | .seekEnd => 0)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_files_flags_exactWireValues
    (encStdio := fun s => match s with | .stdin => 2 | .stdout => 1 | .stderr => 0)) := by
  intro h
  have h0 := h {} {} {} {} {} 0
  exact absurd h0.2.2.2.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with openat := fun d p f m => raw.openat d p f.toBits m })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  cases h0.1

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with close := raw.fsync })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  cases h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with
      lseek := fun fd off w => raw.lseek fd (Int64.ofInt off.toInt32.toInt) w.toRaw })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl (0x100000005 : Int64) .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  exact absurd (congrArg Prod.snd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with
      symlinkat := fun t _ lp =>
        if hasEmbeddedNul t || hasEmbeddedNul lp then pure (.error Errno.EINVAL)
        else raw.symlinkat t none lp })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl (some 7) none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  exact absurd (congrArg Prod.snd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with
      symlinkat := fun t d lp =>
        if hasEmbeddedNul t || hasEmbeddedNul lp then pure (.error Errno.EINVAL)
        else raw.symlinkat lp d t })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  exact absurd (congrArg Prod.snd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with
      renameat2 := fun od op nd np f =>
        if hasEmbeddedNul op || hasEmbeddedNul np then pure (.error Errno.EINVAL)
        else raw.renameat2 nd np od op f.toBits })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl (some 3) (some 4) {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  exact absurd (congrArg Prod.snd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { Internal.mkFilesOpsM raw with
      write := fun fd data => raw.write fd (replicateZeroBytes data.size) })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Internal.mkFilesOpsM] at h0
  exact absurd (congrArg Prod.snd h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide)

example : ¬ Core.AllPass (test_files_interface_wrappersAndDefaults
    { defaultOps with close := fun _ => pure (.ok ()) }
    (fun d p f m => openat d p f m) (fun d p f => openat d p f) openat2
    (fun _ => pure (.error Errno.EBADF)) read write fstat
    (fun d p fl => fstatat d p fl) (fun d p => fstatat d p)
    (fun d p m fl => faccessat d p m fl) (fun d p => faccessat d p)
    (fun d p m => mkdirat d p m) (fun d p => mkdirat d p)
    (fun d p rm => unlinkat d p rm) (fun d p => unlinkat d p)
    (fun od op nd np rf => renameat2 od op nd np rf) (fun od op nd np => renameat2 od op nd np)
    symlinkat (fun d p c => readlinkat d p c) (fun d p => readlinkat d p)
    (fun fd c => getdents64 fd c) (fun fd => getdents64 fd)
    fchmodat fchmod flock fcntl fsync (fun c => getcwd c) getcwd
    (fun fd off wh => lseek fd off wh) (fun fd off => lseek fd off)
    reopenReadOnly dupStdio) := by
  intro h
  have h0 := h none none (ByteArray.mk #[]) (ByteArray.mk #[]) (Classical.choice (inferInstance : Nonempty RawFd)) {} {} 0 {} {} false {} 0 .unlock .getFl 0 .seekSet .stdin
  have hc := congrFun h0.2.2.2.1 (Classical.choice inferInstance)
  cases hc

example : ¬ Core.AllPass (test_files_model_dynamicFifoStdioInvariants (fun _ _ _ => none) evalModel) := by
  intro h
  cases h.1

example : ¬ Core.AllPass (test_files_model_dynamicFifoStdioInvariants allowedStep (fun s _ => (.err Errno.EBADF, s))) := by
  intro h
  rcases h.2.1 with ⟨_, _, _, _, hExt, _⟩
  cases hExt

example : ¬ Core.AllPass (test_files_model_allowedStep_partialReadAndInvariants
    (fun s req out =>
      match req, out with
      | .fstat _, .statted _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_allowedStep_partialReadAndInvariants
    (fun s req out =>
      match req, out with
      | .fcntl 1 .getFd, .u32 _ => none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_files_model_stateRefinementAndUserns (fun _ _ _ => none) evalModel) := by
  intro h
  cases h.2.2.1

example : ¬ Core.AllPass (test_files_model_stateRefinementAndUserns allowedStep (fun s _ => (.u32 0, s))) := by
  intro h
  cases h.1.2.1

end LeanSwe.LinuxSyscall.Files

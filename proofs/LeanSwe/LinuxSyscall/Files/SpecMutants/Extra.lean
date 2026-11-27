import LeanSwe.LinuxSyscall.Files.SpecTests

/-! Additional compile-time negative specification mutants for `LeanSwe.LinuxSyscall.Files`. -/

namespace LeanSwe.LinuxSyscall.Files

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

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

private def refMkFilesOpsM {m : Type → Type} [Monad m] {fd : Type}
    (raw : Internal.PosixFilesOpsM m fd) : FilesOpsM m fd :=
  { openat := fun dir path flags mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.openat dir path flags.toBits mode
    openat2 := fun dir path how =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.openat2 dir path how.flags.toBits how.mode how.resolve.toBits
    close := raw.close
    read := raw.read
    write := raw.write
    fstat := fun fd => do
      match ← raw.fstat fd with
      | .ok t => return .ok (StatInfo.ofRawTuple t)
      | .error e => return .error e
    fstatat := fun dir path flags =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else if flags.eaccess then pure (.error Errno.EINVAL)
      else do
        match ← raw.fstatat dir path flags.toBits with
        | .ok t => return .ok (StatInfo.ofRawTuple t)
        | .error e => return .error e
    faccessat := fun dir path mask flags =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.faccessat dir path mask.toBits flags.toBits
    mkdirat := fun dir path mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.mkdirat dir path mode
    unlinkat := fun dir path removeDir =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.unlinkat dir path (if removeDir then 1 else 0)
    renameat2 := fun oldDir oldPath newDir newPath flags =>
      if hasEmbeddedNul oldPath || hasEmbeddedNul newPath then pure (.error Errno.EINVAL)
      else raw.renameat2 oldDir oldPath newDir newPath flags.toBits
    symlinkat := fun target dir linkPath =>
      if hasEmbeddedNul target || hasEmbeddedNul linkPath then pure (.error Errno.EINVAL)
      else raw.symlinkat target dir linkPath
    readlinkat := fun dir path cap =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.readlinkat dir path cap
    getdents64 := raw.getdents64
    fchmodat := fun dir path mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.fchmodat dir path mode
    fchmod := raw.fchmod
    flock := fun fd op => raw.flock fd op.toBits
    fcntl := fun fd cmd =>
      let (tag, arg) := cmd.toRaw
      raw.fcntl fd tag arg
    fsync := raw.fsync
    getcwd := raw.getcwd
    lseek := fun fd off w => raw.lseek fd off w.toRaw
    reopenReadOnly := raw.reopenReadOnly
    dupStdio := fun slot => raw.dupStdio slot.toRaw }

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with openat := fun d p f m => raw.openat d p f.toBits m })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  cases hTarget

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with close := raw.fsync })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with
      lseek := fun fd off w => raw.lseek fd (Int64.ofInt off.toInt32.toInt) w.toRaw })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl (0x100000005 : Int64) .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with
      symlinkat := fun t _ lp =>
        if hasEmbeddedNul t || hasEmbeddedNul lp then pure (.error Errno.EINVAL)
        else raw.symlinkat t none lp })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl (some 7) none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with
      symlinkat := fun t d lp =>
        if hasEmbeddedNul t || hasEmbeddedNul lp then pure (.error Errno.EINVAL)
        else raw.symlinkat lp d t })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with
      renameat2 := fun od op nd np f =>
        if hasEmbeddedNul op || hasEmbeddedNul np then pure (.error Errno.EINVAL)
        else raw.renameat2 nd np od op f.toBits })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl (some 3) (some 4) {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

example : ¬ Core.AllPass (test_files_impl_mkFilesOpsM
    (fun raw => { refMkFilesOpsM raw with
      write := fun fd data => raw.write fd (replicateZeroBytes data.size) })) := by
  intro h
  have h0 := h (ByteArray.mk #[0]) rfl none none {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h0
  have hTarget := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [refMkFilesOpsM, StateT.run, StateT.bind, StateT.pure, Bind.bind, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hTarget
  exact absurd (congrArg Prod.snd hTarget) (by decide)

private def refRawIoFilesOps : Internal.PosixFilesOps :=
  { openat := fun _ _ _ _ => pure (Except.error Errno.ENOSYS)
    openat2 := fun _ _ _ _ _ => pure (Except.error Errno.ENOSYS)
    close := fun _ => pure (Except.ok ())
    read := fun _ _ => pure (Except.error Errno.ENOSYS)
    write := fun _ _ => pure (Except.error Errno.ENOSYS)
    fstat := fun _ => pure (Except.error Errno.ENOSYS)
    fstatat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    faccessat := fun _ _ _ _ => pure (Except.error Errno.ENOSYS)
    mkdirat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    unlinkat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    renameat2 := fun _ _ _ _ _ => pure (Except.error Errno.ENOSYS)
    symlinkat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    readlinkat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    getdents64 := fun _ _ => pure (Except.error Errno.ENOSYS)
    fchmodat := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    fchmod := fun _ _ => pure (Except.error Errno.ENOSYS)
    flock := fun _ _ => pure (Except.error Errno.ENOSYS)
    fcntl := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    fsync := fun _ => pure (Except.error Errno.ENOSYS)
    getcwd := fun _ => pure (Except.error Errno.ENOSYS)
    lseek := fun _ _ _ => pure (Except.error Errno.ENOSYS)
    reopenReadOnly := fun _ => pure (Except.error Errno.ENOSYS)
    dupStdio := fun _ => pure (Except.error Errno.ENOSYS) }

private def refIoFilesOps : FilesOps :=
  refMkFilesOpsM refRawIoFilesOps

example : ¬ Core.AllPass (test_files_interface_wrappersAndDefaults
    refIoFilesOps
    refIoFilesOps.openat (fun d p f => refIoFilesOps.openat d p f 0o644) refIoFilesOps.openat2
    (fun _ => pure (.error Errno.EBADF)) refIoFilesOps.read refIoFilesOps.write refIoFilesOps.fstat
    refIoFilesOps.fstatat (fun d p => refIoFilesOps.fstatat d p {})
    refIoFilesOps.faccessat (fun d p => refIoFilesOps.faccessat d p {} {})
    refIoFilesOps.mkdirat (fun d p => refIoFilesOps.mkdirat d p 0o755)
    refIoFilesOps.unlinkat (fun d p => refIoFilesOps.unlinkat d p false)
    refIoFilesOps.renameat2 (fun od op nd np => refIoFilesOps.renameat2 od op nd np {})
    refIoFilesOps.symlinkat refIoFilesOps.readlinkat (fun d p => refIoFilesOps.readlinkat d p 4096)
    refIoFilesOps.getdents64 (fun fd => refIoFilesOps.getdents64 fd 8192)
    refIoFilesOps.fchmodat refIoFilesOps.fchmod refIoFilesOps.flock refIoFilesOps.fcntl refIoFilesOps.fsync
    refIoFilesOps.getcwd (refIoFilesOps.getcwd 4096)
    refIoFilesOps.lseek (fun fd off => refIoFilesOps.lseek fd off .seekSet)
    refIoFilesOps.reopenReadOnly refIoFilesOps.dupStdio) := by
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

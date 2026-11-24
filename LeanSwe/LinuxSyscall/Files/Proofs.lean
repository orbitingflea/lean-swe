import LeanSwe.LinuxSyscall.Files.SpecTests
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Files.Proofs.Bitflags
import LeanSwe.LinuxSyscall.Files.Proofs.ExecCases
import LeanSwe.LinuxSyscall.Files.Proofs.Soundness
import LeanSwe.LinuxSyscall.Files.Proofs.HealthyStep

namespace LeanSwe.LinuxSyscall.Files

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `Errno.isTransientOsErrno` and `FilesErrorKind.ofErrno` satisfy their full classification specification. -/
theorem files_errno_classificationAndTransient_allPass :
    AllPass (test_files_errno_classificationAndTransient Errno.isTransientOsErrno FilesErrorKind.ofErrno) := by
  intro e
  dsimp only [Bind.bind, assert, pure]
  refine ⟨by decide, rfl, ?_⟩
  decide

/-- Exact C-ABI wire bitmasks and tag values decoded by `files_shim.c` hold for all 9 symbolic encoders. -/
theorem files_flags_exactWireValues_allPass :
    AllPass (test_files_flags_exactWireValues OpenFlags.toBits ResolveFlags.toBits
      AtFlags.toBits AccessModeMask.toBits RenameFlags.toBits FlockOp.toBits FcntlCmd.toRaw
      SeekWhence.toRaw StdioFd.toRaw) := by
  intro o r a m rn s
  dsimp only [Bind.bind, assert, pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, trivial⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    unfold OpenFlags.toBits
    cases o.access <;> rfl
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rfl
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rfl
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rfl
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All symbolic flag encoders in `LeanSwe.LinuxSyscall.Files` are injective. -/
theorem files_flags_encodersInjective_allPass :
    AllPass (test_files_flags_encodersInjective OpenFlags.toBits ResolveFlags.toBits
      AtFlags.toBits AccessModeMask.toBits RenameFlags.toBits FlockOp.toBits FcntlCmd.toRaw
      SeekWhence.toRaw StdioFd.toRaw) :=
  files_flags_encodersInjective_proof

/-- `StatInfo.ofRawTuple` decodes all 8 `FileKind` tags, masks `mode` to `0o7777`, and preserves all fields. -/
theorem files_statInfo_ofRawTuple_decodesAllKindsAndMasksMode_allPass :
    AllPass (test_files_statInfo_ofRawTuple_decodesAllKindsAndMasksMode StatInfo.ofRawTuple) := by
  intro sz rawMode ino dev nlink mSec mNsec aSec aNsec
  dsimp only [Bind.bind, assert, pure, StatInfo.ofRawTuple]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` rejects every embedded-NUL path with `Errno.EINVAL` and leaves `FilesState` unchanged. -/
theorem files_ops_embeddedNulRejectedWithEinval_allPass :
    AllPass (test_files_ops_embeddedNulRejectedWithEinval modelOps) :=
  files_ops_embeddedNulRejectedWithEinval_proof

/-- Concrete witness demonstrating reachability of `test_files_ops_embeddedNulRejectedWithEinval` on `modelOps`. -/
theorem files_ops_embeddedNulRejectedWithEinval_canReach :
    CanReach (test_files_ops_embeddedNulRejectedWithEinval modelOps) := by
  refine ⟨FilesState.initial, none, {}, {}, {}, {}, 0, false, {}, 16, ByteArray.mk #[97, 0, 98], ?_, ?_⟩
  · rfl
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `modelOps` satisfies open, write, read, `fstat`, `close`, and use-after-close `EBADF` checks. -/
theorem files_ops_openWriteReadStatCloseAndUseAfterClose_allPass :
    AllPass (test_files_ops_openWriteReadStatCloseAndUseAfterClose modelOps FilesState.initial) := by
  refine ⟨⟨rfl, rfl⟩, ⟨by decide, by decide⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨by decide, by decide, rfl⟩, ⟨rfl, rfl⟩, rfl, trivial⟩

/-- `modelOps` satisfies all `openat2` validation, `RESOLVE_BENEATH`, and `RESOLVE_NO_SYMLINKS` checks. -/
theorem files_ops_openat2_resolveConstraints_allPass :
    AllPass (test_files_ops_openat2_resolveConstraints modelOps FilesState.initial) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, trivial⟩

private def segOf (p : ByteArray) : ByteArray :=
  match (splitPathBytes p).2.1 with
  | [s] => s
  | [_, s] => s
  | _ => ByteArray.empty

private def dl_s1 :=
  (modelOps.mkdirat none (asciiBytes ['s', 'u', 'b']) 0o755).run FilesState.initial
private def dl_s2 :=
  (modelOps.openat none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
    { access := .wronly, creat := true } 0o644).run dl_s1.2
private def dl_s3 := (modelOps.close 0).run dl_s2.2
private def dl_s3_norm : FilesState :=
  { FilesState.initial with
    inodes :=
      [(0, { data := .dir { children := [(segOf (asciiBytes ['s', 'u', 'b']), 1)], parentIno := 0, lifecycle := .live }, mode := 0o755, nlink := 3 }),
       (1, { data := .dir { children := [(segOf (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r']), 2)], parentIno := 0, lifecycle := .live }, mode := 0o755, modeExact := true, nlink := 2 }),
       (2, { data := .reg {}, mode := 0o644, modeExact := true, nlink := 1 })]
    nextIno := 3
    nextHid := 1 }
private theorem dl_s3_eq : dl_s3.2 = dl_s3_norm := rfl
private def dl_sDo :=
  (modelOps.openat none (asciiBytes ['s', 'u', 'b']) { access := .rdonly, directory := true } 0).run dl_s3_norm
private def dl_sGs := (modelOps.getdents64 1 8).run dl_sDo.2
private def dl_sGo := (modelOps.getdents64 1 4096).run dl_sGs.2
private def dl_s3p := (modelOps.close 1).run dl_sGo.2
private def dl_s3p_norm : FilesState := { dl_s3_norm with nextHid := 2 }
private theorem dl_s3p_eq : dl_s3p.2 = dl_s3p_norm := rfl
private def dl_s4 :=
  (modelOps.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
    none (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd']) { noreplace := true }).run dl_s3p_norm
private def dl_s5 :=
  (modelOps.openat none (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y'])
    { access := .wronly, creat := true } 0o644).run dl_s4.2
private def dl_s6 := (modelOps.close 2).run dl_s5.2
private def dl_s6_norm : FilesState :=
  { FilesState.initial with
    inodes :=
      [(0, { data := .dir { children := [(segOf (asciiBytes ['s', 'u', 'b']), 1)], parentIno := 0, lifecycle := .live }, mode := 0o755, nlink := 3 }),
       (1, { data := .dir { children := [(segOf (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd']), 2),
                                         (segOf (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y']), 3)],
                            parentIno := 0, lifecycle := .live }, mode := 0o755, modeExact := true, nlink := 2 }),
       (2, { data := .reg {}, mode := 0o644, modeExact := true, nlink := 1 }),
       (3, { data := .reg {}, mode := 0o644, modeExact := true, nlink := 1 })]
    nextIno := 4
    nextHid := 3 }
private theorem dl_s6_eq : dl_s6.2 = dl_s6_norm := rfl

private theorem dl_s2_fst : dl_s2.1 = .ok 0 := rfl
private theorem dl_sDo_fst : dl_sDo.1 = .ok 1 := rfl
private theorem dl_sGo_ok : ∃ bs, dl_sGo.1 = .ok bs ∧ bs.size ≥ 24 :=
  ⟨mkTypedDirentStub [(dotBytes, 4, 2), (dotDotBytes, 4, 1), (asciiBytes ['i', 'n', 'n', 'e', 'r'], 8, 3)],
   rfl, by decide⟩
private theorem dl_s5_fst : dl_s5.1 = .ok 2 := rfl

/-- `modelOps` satisfies directory lifecycle (`mkdirat`, `getdents64`, `unlinkat`, `renameat2`) invariants. -/
theorem files_ops_dirLifecycleAndRenameat2_allPass :
    AllPass (test_files_ops_dirLifecycleAndRenameat2 modelOps FilesState.initial) := by
  dsimp only [test_files_ops_dirLifecycleAndRenameat2, Bind.bind, assert, pure]
  have h1 : (modelOps.mkdirat none (asciiBytes ['s', 'u', 'b']) 0o755).run FilesState.initial = (dl_s1.1, dl_s1.2) := rfl
  rw [h1]; dsimp only
  have h2 : (modelOps.openat none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
      { access := .wronly, creat := true } 0o644).run dl_s1.2 = (.ok 0, dl_s2.2) := Prod.ext dl_s2_fst rfl
  rw [h2]; dsimp only
  have h3 : (modelOps.close 0).run dl_s2.2 = (dl_s3.1, dl_s3_norm) := Prod.ext rfl dl_s3_eq
  rw [h3]; dsimp only
  have hDo : (modelOps.openat none (asciiBytes ['s', 'u', 'b'])
      { access := .rdonly, directory := true } 0).run dl_s3_norm = (.ok 1, dl_sDo.2) := Prod.ext dl_sDo_fst rfl
  rw [hDo]; dsimp only
  have hGs : (modelOps.getdents64 1 8).run dl_sDo.2 = (dl_sGs.1, dl_sGs.2) := rfl
  rw [hGs]; dsimp only
  have hGo : (modelOps.getdents64 1 4096).run dl_sGs.2 = (dl_sGo.1, dl_sGo.2) := rfl
  rw [hGo]; dsimp only
  have h3p : (modelOps.close 1).run dl_sGo.2 = (dl_s3p.1, dl_s3p_norm) := Prod.ext rfl dl_s3p_eq
  rw [h3p]; dsimp only
  have h4 : (modelOps.renameat2 none (asciiBytes ['s', 'u', 'b', '/', 'i', 'n', 'n', 'e', 'r'])
      none (asciiBytes ['s', 'u', 'b', '/', 'm', 'o', 'v', 'e', 'd']) { noreplace := true }).run dl_s3p_norm = (dl_s4.1, dl_s4.2) := rfl
  rw [h4]; dsimp only
  have h5 : (modelOps.openat none (asciiBytes ['s', 'u', 'b', '/', 's', 't', 'a', 'y'])
      { access := .wronly, creat := true } 0o644).run dl_s4.2 = (.ok 2, dl_s5.2) := Prod.ext dl_s5_fst rfl
  rw [h5]; dsimp only
  have h6 : (modelOps.close 2).run dl_s5.2 = (dl_s6.1, dl_s6_norm) := Prod.ext rfl dl_s6_eq
  rw [h6]; dsimp only
  exact ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl,
    dl_sGo_ok, ⟨Or.inl rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `symlinkat`, `readlinkat`, `fstatat`, and `O_NOFOLLOW` checks. -/
theorem files_ops_symlinkReadlinkAndFstatat_allPass :
    AllPass (test_files_ops_symlinkReadlinkAndFstatat modelOps FilesState.initial) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl,
    ⟨_, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `fchmod`, `fchmodat`, `faccessat`, `flock`, `fcntl`, `fsync`, and `getcwd` checks. -/
theorem files_ops_chmodAccessFlockFcntlFsyncGetcwd_allPass :
    AllPass (test_files_ops_chmodAccessFlockFcntlFsyncGetcwd modelOps FilesState.initial) := by
  refine ⟨Or.inl rfl, ⟨_, rfl, by decide, rfl, rfl⟩, rfl, ⟨_, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩,
    ⟨rfl, ⟨_, rfl, by decide, by decide⟩⟩, rfl, rfl, trivial⟩

/-- `modelOps` preserves open-file I/O and dead-directory `ENOENT` semantics after unlink. -/
theorem files_ops_unlinkWhileOpen_preservesIoAndDeadDir_allPass :
    AllPass (test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir modelOps FilesState.initial) :=
  files_ops_unlinkWhileOpen_preservesIoAndDeadDir_proof

/-- `modelOps` satisfies `O_APPEND`, `O_RDONLY | O_TRUNC`, `O_CREAT | O_DIRECTORY`, trailing slash, and dangling symlink creation checks. -/
theorem files_ops_appendTruncAndCreatEdgeCases_allPass :
    AllPass (test_files_ops_appendTruncAndCreatEdgeCases modelOps FilesState.initial) := by
  refine ⟨⟨Or.inl rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩

/-- `modelOps` enforces `NAME_MAX`, `PATH_MAX` (`ENAMETOOLONG`), and cyclic symlink `ELOOP` vs `AT_SYMLINK_NOFOLLOW`. -/
theorem files_ops_symlinkLoopAndNameTooLong_allPass :
    AllPass (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial) :=
  files_ops_symlinkLoopAndNameTooLong_proof

/-- Concrete witness demonstrating reachability of `test_files_ops_symlinkLoopAndNameTooLong` on `modelOps`. -/
theorem files_ops_symlinkLoopAndNameTooLong_canReach :
    CanReach (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial) :=
  files_ops_symlinkLoopAndNameTooLong_canReach_proof

/-- `allowedStep` satisfies all partial-read, `getcwd`, `/dev/shm` `F_GET_SEALS`, `StatInfo` nanosecond bounds, `.reopenExternalStdio` `FD_CLOEXEC`, and blocking `flock` invariants. -/
theorem files_model_allowedStep_partialReadAndInvariants_allPass :
    AllPass (test_files_model_allowedStep_partialReadAndInvariants allowedStep) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `allowedStep` satisfies all hardened model invariants. -/
theorem files_model_hardenedInvariants_allPass :
    AllPass (test_files_model_hardenedInvariants allowedStep) :=
  files_model_hardenedInvariants_proof

/-- `allowedStep` satisfies all environment-generalization invariants. -/
theorem files_model_envGeneralizationInvariants_allPass :
    AllPass (test_files_model_envGeneralizationInvariants allowedStep) :=
  files_model_envGeneralizationInvariants_proof

set_option maxRecDepth 4096 in
/-- Concrete witness demonstrating reachability of `test_files_model_envGeneralizationInvariants` on `allowedStep`. -/
theorem files_model_envGeneralizationInvariants_canReach :
    CanReach (test_files_model_envGeneralizationInvariants allowedStep) :=
  files_model_envGeneralizationInvariants_proof

/-- `modelOps` satisfies `O_PATH`, `lseek`, `reopenReadOnly`, and `dupStdio` invariants. -/
theorem files_ops_lseekReopenDupStdioAndOpath_allPass :
    AllPass (test_files_ops_lseekReopenDupStdioAndOpath modelOps
      { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2)] }, mode := 0o755, nlink := 3 }),
                   (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 })],
        fds := [], cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 5, nextHid := 0 }) :=
  files_ops_lseekReopenDupStdioAndOpath_proof

/-- Concrete witness demonstrating reachability of `test_files_ops_lseekReopenDupStdioAndOpath` on `modelOps`. -/
theorem files_ops_lseekReopenDupStdioAndOpath_canReach :
    CanReach (test_files_ops_lseekReopenDupStdioAndOpath modelOps
      { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2)] }, mode := 0o755, nlink := 3 }),
                   (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 })],
        fds := [], cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 5, nextHid := 0 }) :=
  files_ops_lseekReopenDupStdioAndOpath_proof

/-- Every `evalModel` transition `(out, s')` on a well-formed step is accepted by `verifyStep` with identical next state `some s'`. -/
theorem evalModel_state_refines_verifyStep (s : FilesState) (req : FilesReq)
    (hWf : WellFormedStep s req) :
    verifyStep s (evalReq s req) (evalModel s req).1 = some (evalModel s req).2 :=
  evalModel_state_refines_verifyStep_aux s req hWf

/-- Every `evalModel` outcome on a well-formed step is accepted by `verifyStep`. -/
theorem evalModel_refines_verifyStep (s : FilesState) (req : FilesReq)
    (hWf : WellFormedStep s req) :
    (verifyStep s (evalReq s req) (evalModel s req).1).isSome = true :=
  evalModel_refines_verifyStep_aux s req hWf

/-- `Internal.mkFilesOpsM` enforces all embedded-NUL and `AT_EACCESS` guards and forwards all 23 methods accurately. -/
theorem files_impl_mkFilesOpsM_allPass :
    AllPass (test_files_impl_mkFilesOpsM Internal.mkFilesOpsM) := by
  intro badPath hBad dir dir2 o r a m rn fl fc off w st rm
  dsimp only [Bind.bind, assert, pure, Internal.mkFilesOpsM, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, mkRecRawOps]
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  all_goals
    simp only [hBad, Bool.true_or, Bool.or_true, ↓reduceIte]
    rfl

/-- Reachability witness for `test_files_impl_mkFilesOpsM`. -/
theorem files_impl_mkFilesOpsM_canReach :
    CanReach (test_files_impl_mkFilesOpsM Internal.mkFilesOpsM) := by
  refine ⟨ByteArray.mk #[97, 0, 98], rfl, none, some 7, {}, {}, {}, {}, {}, .unlock, .getFl, 0, .seekSet, .stdin, false, ?_⟩
  have h := files_impl_mkFilesOpsM_allPass (ByteArray.mk #[97, 0, 98]) rfl none (some 7) {} {} {} {} {} .unlock .getFl 0 .seekSet .stdin false
  dsimp only [Bind.bind, assert, pure] at h ⊢
  exact h

/-- All 23 top-level `LeanSwe.LinuxSyscall.Files` wrappers and default arguments delegate directly to `defaultOps`. -/
theorem files_interface_wrappersAndDefaults_allPass :
    AllPass (test_files_interface_wrappersAndDefaults defaultOps (fun d p f m => openat d p f m)
      (fun d p f => openat d p f) openat2
      close read write fstat (fun d p fl => fstatat d p fl) (fun d p => fstatat d p)
      (fun d p m fl => faccessat d p m fl) (fun d p => faccessat d p)
      (fun d p m => mkdirat d p m) (fun d p => mkdirat d p)
      (fun d p rm => unlinkat d p rm) (fun d p => unlinkat d p)
      (fun od op nd np rf => renameat2 od op nd np rf) (fun od op nd np => renameat2 od op nd np)
      symlinkat (fun d p c => readlinkat d p c) (fun d p => readlinkat d p)
      (fun fd c => getdents64 fd c) (fun fd => getdents64 fd)
      fchmodat fchmod flock fcntl fsync (fun c => getcwd c) getcwd
      (fun fd off wh => lseek fd off wh) (fun fd off => lseek fd off) reopenReadOnly dupStdio) := by
  intro dir dir2 path path2 fd flags how mode atFlags mask rm renFlags cap flockOp cmd off whence slot
  dsimp only [Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `allowedStep` and `evalModel` satisfy all dynamic FIFO `ENXIO`, `.reopenExternalStdio` slot, and shared-OFD `.readDynamic` invariants. -/
theorem files_model_dynamicFifoStdioInvariants_allPass :
    AllPass (test_files_model_dynamicFifoStdioInvariants allowedStep evalModel) :=
  ⟨rfl, ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
    ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

private def sru_s0 : FilesState := { FilesState.initial with freeStdioSlots := [.stdin] }
private def sru_s1 := (evalModel sru_s0 (.openat none (asciiBytes ['.']) { access := .rdonly, directory := true, cloexec := false } 0)).2
private def sru_s2 := (evalModel sru_s1 (.dupStdio .stdin)).2
private def sru_gd := evalModel sru_s2 (.getdents64 0 4096)

private theorem sru_s2_wf : WellFormedStep sru_s2 (.getdents64 0 4096) := by
  have hInodes : sru_s2.inodes = FilesState.initial.inodes := rfl
  have hCwd : sru_s2.cwdPath = .unbound (ByteArray.mk #[47]) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro ino vn hIno
    rw [hInodes] at hIno
    simp [FilesState.initial, assocGet] at hIno
    rcases hIno with ⟨rfl, rfl⟩
    refine ⟨by decide, ?_⟩
    intro nm c hMem; cases hMem
  · intro fb hFb
    rw [hCwd] at hFb
    cases hFb
    decide
  · intro _ _ hReq; cases hReq

private theorem sru_gd_step : allowedStep sru_s2 (.getdents64 0 4096) sru_gd.1 = some sru_gd.2 := by
  have hRef : verifyStep sru_s2 (evalReq sru_s2 (.getdents64 0 4096)) sru_gd.1 = some sru_gd.2 :=
    evalModel_state_refines_verifyStep sru_s2 (.getdents64 0 4096) sru_s2_wf
  have hD : assocGet sru_s2.fds 0 = some { ino := 0, access := .rdonly, cloexec := false, pos := .dirStream 0 false, ofdId? := some 0 } := rfl
  unfold allowedStep directHid?
  dsimp only
  rw [hD]
  dsimp only
  have hOpen : (FdCloseState.open == FdCloseState.closeUncertain) = false := rfl
  rw [hOpen]
  simp only [Bool.false_eq_true, ↓reduceIte, verifyWithSeccomp, hRef]

/-- `allowedStep` and `evalModel` preserve per-FD state across shared-OFD `getdents64`, `ambientSeccomp` FIFO `EAGAIN` parity, and `!initUserNs` creation `EOVERFLOW` (`75`) allowance. -/
theorem files_model_stateRefinementAndUserns_allPass :
    AllPass (test_files_model_stateRefinementAndUserns allowedStep evalModel) := by
  have hFc0 : (evalModel sru_gd.2 (.fcntl 0 .getFd)).1 = .u32 0 := rfl
  have hFc1 : (evalModel sru_gd.2 (.fcntl 1 .getFd)).1 = .u32 1 := rfl
  exact ⟨⟨hFc0, hFc1, sru_gd_step⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, trivial⟩

end LeanSwe.LinuxSyscall.Files

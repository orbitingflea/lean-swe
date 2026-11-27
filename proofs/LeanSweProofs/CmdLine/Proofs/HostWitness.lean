import Core.Obeys
import LeanSwe.CmdLine.Interface
import LeanSweProofs.CmdLine.Proofs.HostBase

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.LinuxSyscall

private noncomputable def witnessRawFd : RawFd :=
  Classical.choice inferInstance

private def unimplHostFilesOp {α : Type} :
    ExceptT IO.Error (StateM Model.CmdLineHostState) (Except Errno α) :=
  ExceptT.mk fun s => (.ok (.error Errno.ENOSYS), s)

/-- Reference `CmdLineCapsM` witness over `ExceptT IO.Error (StateM Model.CmdLineHostState)` for `obeys_model_nonvacuous`. -/
noncomputable def modelHostCaps :
    Model.CmdLineCapsM (ExceptT IO.Error (StateM Model.CmdLineHostState)) :=
  { env :=
      { mapRawError := LeanSwe.EnvVars.Model.mapRawErrorModel
        getEnv := fun key => ExceptT.mk fun s => (.ok (LeanSwe.EnvVars.Model.getEnvModel s.env key), s)
        listEnv := ExceptT.mk fun s => (.ok (LeanSwe.EnvVars.Model.listEnvModel s.env), s)
        homeDir := ExceptT.mk fun s => (.ok (LeanSwe.EnvVars.Model.homeDirModel s.env), s)
        splitSearchPath := LeanSwe.EnvVars.Model.splitSearchPathModel }
    files :=
      { openat := fun _ _ _ _ => unimplHostFilesOp
        openat2 := fun _ _ _ => unimplHostFilesOp
        close := fun _ => ExceptT.mk fun s =>
          match s.openDups with
          | _ :: rest => (.ok (.ok ()), { s with openDups := rest })
          | [] => (.ok (.error Errno.EBADF), s)
        read := fun _ maxBytes => ExceptT.mk fun s =>
          match s.openDups with
          | .stdin :: _ =>
            match s.fault with
            | .ioThrow msg => (.error (IO.userError msg), s)
            | .ioErrno code => (.ok (.error code), s)
            | .none | .dupErrno _ =>
              if s.eintrCount > 0 then
                (.ok (.error Errno.EINTR), { s with eintrCount := s.eintrCount - 1 })
              else if maxBytes == 0 then
                (.ok (.ok ByteArray.empty), s)
              else
                match s.stdinBytes with
                | [] => (.ok (.ok ByteArray.empty), s)
                | b :: rest => (.ok (.ok (ByteArray.mk #[b])), { s with stdinBytes := rest })
          | _ => (.ok (.error Errno.EBADF), s)
        write := fun _ slice => ExceptT.mk fun s =>
          match s.openDups with
          | .stdout :: _ =>
            match s.fault with
            | .ioThrow msg => (.error (IO.userError msg), s)
            | .ioErrno code => (.ok (.error code), s)
            | .none | .dupErrno _ =>
              if s.eintrCount > 0 then
                (.ok (.error Errno.EINTR), { s with eintrCount := s.eintrCount - 1 })
              else
                let k := min slice.size 1048576
                (.ok (.ok (UInt32.ofNat k)), { s with stdoutBytes := s.stdoutBytes ++ slice.extract 0 k })
          | .stderr :: _ =>
            match s.fault with
            | .ioThrow msg => (.error (IO.userError msg), s)
            | .ioErrno code => (.ok (.error code), s)
            | .none | .dupErrno _ =>
              if s.eintrCount > 0 then
                (.ok (.error Errno.EINTR), { s with eintrCount := s.eintrCount - 1 })
              else
                let k := min slice.size 1048576
                (.ok (.ok (UInt32.ofNat k)), { s with stderrBytes := s.stderrBytes ++ slice.extract 0 k })
          | _ => (.ok (.error Errno.EBADF), s)
        fstat := fun _ => unimplHostFilesOp
        fstatat := fun _ _ _ => unimplHostFilesOp
        faccessat := fun _ _ _ _ => unimplHostFilesOp
        mkdirat := fun _ _ _ => unimplHostFilesOp
        unlinkat := fun _ _ _ => unimplHostFilesOp
        renameat2 := fun _ _ _ _ _ => unimplHostFilesOp
        symlinkat := fun _ _ _ => unimplHostFilesOp
        readlinkat := fun _ _ _ => unimplHostFilesOp
        getdents64 := fun _ _ => unimplHostFilesOp
        fchmodat := fun _ _ _ => unimplHostFilesOp
        fchmod := fun _ _ => unimplHostFilesOp
        flock := fun _ _ => unimplHostFilesOp
        fcntl := fun _ _ => unimplHostFilesOp
        fsync := fun _ => unimplHostFilesOp
        getcwd := fun _ => unimplHostFilesOp
        lseek := fun _ _ _ => unimplHostFilesOp
        reopenReadOnly := fun _ => unimplHostFilesOp
        dupStdio := fun slot => ExceptT.mk fun s =>
          match s.fault with
          | .dupErrno code => (.ok (.error code), s)
          | .none | .ioErrno _ | .ioThrow _ =>
            (.ok (.ok witnessRawFd), { s with openDups := slot :: s.openDups }) } }

/-- `modelHostCaps` satisfies `Model.allowedHostCapsStep` over `Model.CmdLineHostState`. -/
theorem modelHostCaps_obeys_allowedHostCapsStep :
    Core.ObeysStepExcept id Model.hostStepWf (Model.execCapsStep modelHostCaps) Model.allowedHostCapsStep := by
  intro s req _
  dsimp only [id, Model.execCapsStep, Model.allowedHostCapsStep, modelHostCaps]
  cases req with
  | envGet key =>
    rw [exceptT_run_map]
    dsimp only [ExceptT.run, ExceptT.mk, StateT.run, Except.map]
    exact ⟨rfl, rfl⟩
  | dupStdio slot =>
    rw [exceptT_run_map]
    dsimp only [ExceptT.run, ExceptT.mk, StateT.run]
    cases s.fault with
    | none => exact ⟨witnessRawFd, rfl, rfl⟩
    | dupErrno _ => exact ⟨rfl, rfl⟩
    | ioErrno _ => exact ⟨witnessRawFd, rfl, rfl⟩
    | ioThrow _ => exact ⟨witnessRawFd, rfl, rfl⟩
  | read fd maxBytes =>
    rw [exceptT_run_map]
    dsimp only [ExceptT.run, ExceptT.mk, StateT.run]
    cases s.openDups with
    | nil => exact ⟨rfl, rfl⟩
    | cons top rest =>
      cases top with
      | stdout | stderr => exact ⟨rfl, rfl⟩
      | stdin =>
        cases s.fault with
        | ioThrow _ | ioErrno _ => exact ⟨rfl, rfl⟩
        | none | dupErrno _ =>
          by_cases he : s.eintrCount > 0
          · simp [he, Except.map]
          · simp only [he, ↓reduceIte]
            by_cases hm : (maxBytes == 0) = true
            · simp [hm, Except.map]
            · simp only [hm, Bool.false_eq_true, ↓reduceIte]
              cases s.stdinBytes <;> exact ⟨rfl, rfl⟩
  | write fd slice =>
    rw [exceptT_run_map]
    dsimp only [ExceptT.run, ExceptT.mk, StateT.run]
    cases s.openDups with
    | nil => exact ⟨rfl, rfl⟩
    | cons top rest =>
      cases top with
      | stdin => exact ⟨rfl, rfl⟩
      | stdout | stderr =>
        cases s.fault with
        | ioThrow _ | ioErrno _ => exact ⟨rfl, rfl⟩
        | none | dupErrno _ =>
          by_cases he : s.eintrCount > 0 <;> simp [he, Except.map]
  | close fd =>
    rw [exceptT_run_map]
    dsimp only [ExceptT.run, ExceptT.mk, StateT.run]
    cases s.openDups <;> exact ⟨rfl, rfl⟩

end LeanSwe.CmdLine.Proofs

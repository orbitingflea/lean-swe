import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.PostFork.Interface
import LeanSwe.EnvVars.Interface
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSwe.Process.Impl
import LeanSwe.Process.SysBridge

namespace LeanSwe.Process

private initialize gProcTable : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd) ← IO.mkRef {}

/-- Default `ProcessApi` wired directly over `LinuxSyscall.{Process,Files,Poll,TimeRand}.defaultOps`, `PostFork.defaultOps`, `EnvVars.defaultApi`, `Core.ioConcOps`, and `Core.ioStateCell`. -/
def defaultApi : ProcessApi :=
  Internal.mkFullApiM
    { proc := LeanSwe.LinuxSyscall.Process.defaultOps
      files := LeanSwe.LinuxSyscall.Files.defaultOps
      poll := LeanSwe.LinuxSyscall.Poll.defaultOps
      timeRand := LeanSwe.LinuxSyscall.TimeRand.defaultOps
      postFork := LeanSwe.PostFork.defaultOps
      envRaw := LeanSwe.EnvVars.defaultApi }
    Core.ioConcOps
    (Core.ioStateCell gProcTable)

/-- Convert a raw OS error record into a normalized `ProcessError` with non-empty message. -/
@[inline] def mapRawError (err : ProcessRawError) : ProcessError :=
  defaultApi.mapRawError err

/-- Validate and normalize an `ExecRequest`. -/
@[inline] def validateRequest (req : ExecRequest) : Except ProcessError ExecRequest :=
  defaultApi.validateRequest req

/-- Construct a direct `execvp`-style `ExecRequest` with explicit argument array (no shell). -/
@[inline] def mkCommandRequest (program : String) (args : Array String := #[]) : ExecRequest :=
  defaultApi.mkCommandRequest program args

/-- Return a copy of `req` with UTF-8 encoded `stdin` text. -/
@[inline] def withTextInput (req : ExecRequest) (text : String) : ExecRequest :=
  defaultApi.withTextInput req text

/-- Validate `req` and spawn a child process directly in its own process group. -/
@[inline] def spawn (req : SpawnRequest) : IO (Except ProcessError ProcessHandle) :=
  defaultApi.spawn req

/-- Feed `stdin`, stream `stdout`/`stderr`, and wait for completion, timeout, or output cap. -/
@[inline] def awaitOutput
    (h : ProcessHandle)
    (stdin : ByteArray := ByteArray.empty)
    (timeoutMs : Option Nat := none)
    (maxOutputBytes : Option Nat := none) : IO (Except ProcessError ExecOutcome) :=
  defaultApi.awaitOutput h stdin timeoutMs maxOutputBytes

/-- Terminate the child process group (`SIGTERM` followed by `SIGKILL`). -/
@[inline] def killProcessGroup (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultApi.killProcessGroup h

/-- Wait for and release a spawned child handle. -/
@[inline] def reap (h : ProcessHandle) : IO (Except ProcessError Unit) :=
  defaultApi.reap h

/-- Execute a command directly in its own process group, returning `ExecResult` even for non-zero exit codes. -/
@[inline] def run (req : ExecRequest) : IO (Except ProcessError ExecResult) :=
  defaultApi.run req

/-- Execute a command like `run`, mapping any non-zero exit code to `.error` with `kind := .nonZeroExit`. -/
@[inline] def runChecked (req : ExecRequest) : IO (Except ProcessError ExecResult) :=
  defaultApi.runChecked req

/-- Execute `program` with explicit `args` via `run`. -/
@[inline] def runCommand (program : String) (args : Array String := #[]) :
    IO (Except ProcessError ExecResult) :=
  defaultApi.runCommand program args

/-- Execute `program` with explicit `args` via `runChecked`. -/
@[inline] def runCommandChecked (program : String) (args : Array String := #[]) :
    IO (Except ProcessError ExecResult) :=
  defaultApi.runCommandChecked program args

/-- Return count of currently active (un-reaped) spawned child process handles. -/
@[inline] def activeProcessCount : IO Nat :=
  defaultApi.activeProcessCount

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem ioConc_tryCatch_ok {α : Type} (act : IO α) (w : Void IO.RealWorld) :
    ∃ r w', Core.ioConcOps.tryCatchMsg act w = EST.Out.ok r w' := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]; unfold EST.tryCatch EST.bind EST.pure
  cases act w <;> exact ⟨_, _, rfl⟩

private theorem ioCell_get_ok {S : Type} (r : IO.Ref S) (w : Void IO.RealWorld) :
    ∃ s w', (Core.ioStateCell r).get w = EST.Out.ok s w' := by
  change ∃ s w', (r.get : BaseIO S).toEIO w = EST.Out.ok s w'
  unfold BaseIO.toEIO
  cases (r.get : BaseIO S) w with | mk a s => exact ⟨a, s, rfl⟩

private theorem ioCell_mod_ok {S α : Type} (r : IO.Ref S) (f : S → α × S) (w : Void IO.RealWorld) :
    ∃ a w', (Core.ioStateCell r).modifyGet f w = EST.Out.ok a w' := by
  change ∃ a w', (r.modifyGet f : BaseIO α).toEIO w = EST.Out.ok a w'
  unfold BaseIO.toEIO
  cases (r.modifyGet f : BaseIO α) w with | mk a s => exact ⟨a, s, rfl⟩

private theorem mkFullRaw_spawn_ok (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.spawnConc sys Core.ioConcOps (Core.ioStateCell r) ef req w = EST.Out.ok res w' := by
  unfold SysBridge.spawnConc
  rcases ioConc_tryCatch_ok _ w with ⟨tr, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases tr with
  | error _ => exact ⟨_, w1, rfl⟩
  | ok os => cases os with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok _ =>
      dsimp only; rcases ioCell_mod_ok r _ w1 with ⟨_, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; exact ⟨_, w2, rfl⟩

private theorem mkFullRaw_await_ok (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef iof : Nat) (h : ProcessHandle) (stdin : ByteArray) (to? max? : Option Nat)
    (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.awaitOutputConc sys Core.ioConcOps (Core.ioStateCell r) ef iof h stdin to? max? w = EST.Out.ok res w' := by
  unfold SysBridge.awaitOutputConc
  rcases ioCell_mod_ok r _ w with ⟨tk, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases tk with
  | none => exact ⟨_, w1, rfl⟩
  | some tup =>
    rcases tup with ⟨_, _, _, _⟩; dsimp only
    rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]
    cases tr with
    | error _ => exact ⟨_, w2, rfl⟩
    | ok os => cases os with
      | error _ => exact ⟨_, w2, rfl⟩
      | ok p =>
        rcases p with ⟨_, _⟩; dsimp only
        rcases ioCell_mod_ok r _ w2 with ⟨okF, w3, h3⟩; rw [io_bind_ok _ _ _ h3]
        cases okF <;> exact ⟨_, w3, rfl⟩

private theorem mkFullRaw_kill_ok (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.killProcessGroupConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold SysBridge.killProcessGroupConc
  rcases ioCell_get_ok r w with ⟨st, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases (SysBridge.findSlotPure h.handleId st.slots).map (·.pgid) with
  | none => exact ⟨_, w1, rfl⟩
  | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩

private theorem mkFullRaw_reap_ok (sys : Internal.ProcessSysCapsM IO)
    (r : IO.Ref (Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', SysBridge.reapConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold SysBridge.reapConc
  rcases ioCell_mod_ok r _ w with ⟨det, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases det with
  | none => exact ⟨_, w1, rfl⟩
  | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩

/-- `defaultApi.run` never throws an uncaught `IO.Error`. -/
theorem defaultApi_run_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', defaultApi.run req w = EST.Out.ok res w' := by
  unfold defaultApi Internal.mkFullApiM Internal.run SysBridge.mkFullRawOpsM
  dsimp only
  cases Internal.validateRequest req with
  | error e => exact ⟨Except.error e, w, rfl⟩
  | ok vreq =>
    dsimp only
    rcases mkFullRaw_spawn_ok _ _ _ vreq w with ⟨rSpawn, w1, hSpawn⟩; rw [io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok h =>
      dsimp only
      rcases mkFullRaw_await_ok _ _ _ _ h vreq.stdin vreq.timeoutMs vreq.maxOutputBytes w1 with ⟨rAwait, w2, hAwait⟩
      rw [io_bind_ok _ _ _ hAwait]
      rcases rAwait with _ | outcome
      · dsimp only
        rcases mkFullRaw_kill_ok _ _ _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
        rcases mkFullRaw_reap_ok _ _ _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
        exact ⟨_, w4, rfl⟩
      · cases outcome with
        | exited _ =>
          dsimp only
          rcases mkFullRaw_reap_ok _ _ _ h w2 with ⟨rReap, w3, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          cases rReap <;> exact ⟨_, w3, rfl⟩
        | signaled _ _ _ | timedOut _ _ | outputLimitExceeded _ _ =>
          dsimp only
          rcases mkFullRaw_kill_ok _ _ _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
          rcases mkFullRaw_reap_ok _ _ _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl⟩

end LeanSwe.Process

import Core.Assumptions
import Core.ConcOps
import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface

/-!
Shared `IO` totality and basic-error-kind invariants across `SysBridge` OS phases,
`Core.ioConcOps.tryCatchMsg`, and `Core.ioStateCell` for `LeanSwe.Process` error-impossibility proofs.
-/

namespace LeanSwe.Process.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

/-- Predicate asserting `e.kind` is one of the basic OS/validation kinds (never outcome/exit kinds). -/
def isBasicErrKind (e : ProcessError) : Prop :=
  e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧
    e.kind ≠ .terminatedBySignal ∧ e.kind ≠ .nonZeroExit

/-- Predicate asserting an `Except ProcessError α` is either `.ok` or has a basic error kind. -/
def basicErrOrOk {α : Type} : Except ProcessError α → Prop
  | .error e => isBasicErrKind e
  | .ok _ => True

/-- Predicate asserting `act` satisfies `P` whenever it returns `EST.Out.ok`. -/
def SatisfiesIO {α : Type} (P : α → Prop) (act : IO α) : Prop :=
  ∀ w : Void IO.RealWorld,
    match act w with
    | .ok a _ => P a
    | .error _ _ => True

theorem sat_pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    SatisfiesIO P (pure a) :=
  fun _ => h

theorem sat_any {α : Type} (x : IO α) : SatisfiesIO (fun _ => True) x := by
  intro w; cases x w <;> exact trivial

theorem sat_bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : IO α} {f : α → IO β}
    (hx : SatisfiesIO P x) (hf : ∀ a, P a → SatisfiesIO Q (f a)) :
    SatisfiesIO Q (x >>= f) := by
  intro w
  change match EST.bind x f w with | .ok b _ => Q b | .error _ _ => True
  unfold EST.bind
  have hxw := hx w
  cases h : x w with
  | error _ _ => exact trivial
  | ok a w' => rw [h] at hxw; exact hf a hxw w'

theorem sat_seq {α β : Type} {Q : β → Prop} {x : IO α} {f : α → IO β}
    (hf : ∀ a, SatisfiesIO Q (f a)) :
    SatisfiesIO Q (x >>= f) :=
  sat_bind (sat_any x) (fun a _ => hf a)

theorem sat_mono {α : Type} {P Q : α → Prop} {act : IO α}
    (h : SatisfiesIO P act) (himp : ∀ a, P a → Q a) : SatisfiesIO Q act := by
  intro w; have hw := h w
  cases hact : act w with
  | error _ _ => exact trivial
  | ok a _ => rw [hact] at hw; exact himp a hw

theorem basic_of_kind {e : ProcessError} (k : ProcessErrorKind)
    (heq : e.kind = k) (h1 : k ≠ .timedOut) (h2 : k ≠ .outputLimitExceeded)
    (h3 : k ≠ .terminatedBySignal) (h4 : k ≠ .nonZeroExit) : isBasicErrKind e := by
  rw [isBasicErrKind, heq]; exact ⟨h1, h2, h3, h4⟩

theorem basic_notFound {e : ProcessError} (h : e.kind = .notFound) : isBasicErrKind e :=
  basic_of_kind .notFound h (by decide) (by decide) (by decide) (by decide)

theorem basic_perm {e : ProcessError} (h : e.kind = .permissionDenied) : isBasicErrKind e :=
  basic_of_kind .permissionDenied h (by decide) (by decide) (by decide) (by decide)

theorem basic_invalid {e : ProcessError} (h : e.kind = .invalidInput) : isBasicErrKind e :=
  basic_of_kind .invalidInput h (by decide) (by decide) (by decide) (by decide)

theorem basic_io {e : ProcessError} (h : e.kind = .ioError) : isBasicErrKind e :=
  basic_of_kind .ioError h (by decide) (by decide) (by decide) (by decide)

theorem mapErrno_basic (prog? : Option String) (ctx : String) (e : LinuxSyscall.Errno) :
    isBasicErrKind (mapErrno prog? ctx e) := by
  unfold mapErrno; dsimp only
  split
  · exact basic_notFound rfl
  · split
    · exact basic_perm rfl
    · split
      · exact basic_invalid rfl
      · exact basic_io rfl

theorem mapCaughtMsg_basic (prog? : Option String) (msg : String) :
    isBasicErrKind (mapCaughtMsg prog? msg) :=
  basic_io rfl

theorem ensureNonEmptyMsg_basic (fb : String) {err : ProcessError}
    (h : isBasicErrKind err) : isBasicErrKind (Internal.ensureNonEmptyMsg fb err) := by
  unfold Internal.ensureNonEmptyMsg; split <;> exact h

theorem sysBridge_ensureNonEmptyMsg_basic (fb : String) {err : ProcessError}
    (h : isBasicErrKind err) : isBasicErrKind (SysBridge.ensureNonEmptyMsg fb err) := by
  unfold SysBridge.ensureNonEmptyMsg; split <;> exact h

theorem mapPostForkError_basic (req : ExecRequest) (pfErr : PostFork.PostForkError) :
    isBasicErrKind (mapPostForkError req pfErr) := by
  unfold mapPostForkError
  cases pfErr.childFailure with
  | some cf => exact mapErrno_basic _ _ cf.errno
  | none =>
    cases pfErr.kind with
    | invalidInput => exact basic_invalid rfl
    | _ =>
      cases pfErr.errno with
      | some e => exact mapErrno_basic _ _ e
      | none => exact basic_io rfl

/-- Lift `P` over `.ok` while requiring `isBasicErrKind` on `.error`. -/
def exceptBasicPred {α : Type} (P : α → Prop) : Except ProcessError α → Prop
  | .error e => isBasicErrKind e
  | .ok a => P a

theorem imp_io_bind_ok {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : x w = .ok a w') :
    (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  simp [EST.bind, h]

theorem ioConcOps_tryCatchMsg_sat {α : Type} {P : α → Prop}
    (act : IO (Except ProcessError α))
    (h : SatisfiesIO (exceptBasicPred P) act)
    (w : Void IO.RealWorld) :
    ∃ r w', Core.ioConcOps.tryCatchMsg act w = .ok r w' ∧
      match r with
      | .error _ => True
      | .ok inner => exceptBasicPred P inner := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]
  unfold EST.tryCatch EST.bind EST.pure
  have hw := h w
  cases hact : act w with
  | ok res w' =>
    rw [hact] at hw
    exact ⟨.ok res, w', rfl, hw⟩
  | error err w' =>
    exact ⟨.error (toString err), w', rfl, trivial⟩

theorem ioConcOps_tryCatchMsg_ok {α : Type} (act : IO α) (w : Void IO.RealWorld) :
    ∃ r w', Core.ioConcOps.tryCatchMsg act w = .ok r w' := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]
  unfold EST.tryCatch EST.bind EST.pure
  cases act w <;> exact ⟨_, _, rfl⟩

theorem ioStateCell_get_ok {S : Type} (r : IO.Ref S) (w : Void IO.RealWorld) :
    ∃ s w', (Core.ioStateCell r).get w = .ok s w' := by
  change ∃ s w', (r.get : BaseIO S).toEIO w = .ok s w'
  unfold BaseIO.toEIO
  cases (r.get : BaseIO S) w with
  | mk a s => exact ⟨a, s, rfl⟩

theorem ioStateCell_modifyGet_ok {S α : Type} (r : IO.Ref S)
    (f : S → α × S) (w : Void IO.RealWorld) :
    ∃ a w', (Core.ioStateCell r).modifyGet f w = .ok a w' := by
  change ∃ a w', (r.modifyGet f : BaseIO α).toEIO w = .ok a w'
  unfold BaseIO.toEIO
  cases (r.modifyGet f : BaseIO α) w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem validateWorkingDir_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (cwd? : Option String) (fuel : Nat) :
    SatisfiesIO basicErrOrOk (validateWorkingDir files cwd? fuel) := by
  unfold validateWorkingDir
  cases cwd? with
  | none => exact sat_pure trivial
  | some cwdDir =>
    dsimp only; split
    · exact sat_pure (mapErrno_basic _ _ _)
    · apply sat_seq; intro r1
      cases r1 with
      | error e => exact sat_pure (mapErrno_basic _ _ e)
      | ok _ =>
        dsimp only; split
        · exact sat_pure (mapErrno_basic _ _ _)
        · apply sat_seq; intro r2
          cases r2 with
          | error e => exact sat_pure (mapErrno_basic _ _ e)
          | ok _ => exact sat_pure trivial

private theorem searchPathDirs_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (program : String) (cwd? : Option String)
    (fuel : Nat) (sawPerm : Bool) (dirs : List String) :
    SatisfiesIO basicErrOrOk (searchPathDirs files program cwd? fuel sawPerm dirs) := by
  induction dirs generalizing sawPerm with
  | nil =>
    unfold searchPathDirs; split
    · exact sat_pure (basic_perm rfl)
    · exact sat_pure (basic_notFound rfl)
  | cons dir rest ih =>
    unfold searchPathDirs; apply sat_seq; intro r1
    cases r1 with
    | error e =>
      dsimp only; split
      · exact ih true
      · split
        · exact ih sawPerm
        · exact sat_pure (mapErrno_basic _ _ e)
    | ok _ =>
      dsimp only; split
      · exact ih true
      · apply sat_seq; intro r2
        cases r2 with
        | error e =>
          dsimp only; split
          · exact ih true
          · split
            · exact ih sawPerm
            · exact sat_pure (mapErrno_basic _ _ e)
        | ok _ => exact sat_pure trivial

private theorem resolveExecutablePath_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (program : String) (cwd? : Option String)
    (envBytes : Array ByteArray) (fuel : Nat) :
    SatisfiesIO basicErrOrOk (resolveExecutablePath files program cwd? envBytes fuel) := by
  unfold resolveExecutablePath; split
  · exact sat_pure trivial
  · exact searchPathDirs_sat files program cwd? fuel false _

private theorem readBaseEnv_caps_sat (sys : Internal.ProcessSysCapsM IO) (inheritEnv : Bool) :
    SatisfiesIO basicErrOrOk (readBaseEnv (sysDepsOfCaps sys) inheritEnv) := by
  unfold readBaseEnv; split
  · dsimp only [sysDepsOfCaps, Functor.map]
    change SatisfiesIO basicErrOrOk (sys.envRaw.listEnvironBytes >>= fun xs => pure (.ok xs))
    apply sat_seq; intro _; exact sat_pure trivial
  · exact sat_pure trivial

theorem spawnOsPhase_sat (sys : Internal.ProcessSysCapsM IO) (fuel : Nat) (req : ExecRequest) :
    SatisfiesIO (exceptBasicPred (fun _ => True)) (spawnOsPhase (sysDepsOfCaps sys) fuel req) := by
  unfold spawnOsPhase; split
  · exact sat_pure (basic_invalid rfl)
  · refine sat_bind (validateWorkingDir_sat (sysDepsOfCaps sys).files req.cwd fuel) fun r1 hr1 => ?_
    cases r1 with
    | error _ => exact sat_pure hr1
    | ok _ =>
      refine sat_bind (readBaseEnv_caps_sat sys req.inheritEnv) fun r2 hr2 => ?_
      cases r2 with
      | error _ => exact sat_pure (sysBridge_ensureNonEmptyMsg_basic _ hr2)
      | ok _ =>
        refine sat_bind (resolveExecutablePath_sat (sysDepsOfCaps sys).files req.program req.cwd _ fuel) fun r3 hr3 => ?_
        cases r3 with
        | error _ => exact sat_pure hr3
        | ok _ =>
          dsimp only; split
          · exact sat_pure (basic_invalid rfl)
          · apply sat_seq; intro r4
            cases r4 with
            | error e1 => exact sat_pure (mapErrno_basic _ _ e1)
            | ok _ =>
              apply sat_seq; intro r5
              cases r5 with
              | error e2 =>
                apply sat_seq; intro _; apply sat_seq; intro _
                exact sat_pure (mapErrno_basic _ _ e2)
              | ok _ =>
                apply sat_seq; intro r6
                cases r6 with
                | error e3 =>
                  apply sat_seq; intro _; apply sat_seq; intro _
                  apply sat_seq; intro _; apply sat_seq; intro _
                  exact sat_pure (mapErrno_basic _ _ e3)
                | ok _ =>
                  apply sat_seq; intro spawnRes
                  apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                  cases spawnRes with
                  | error pfErr =>
                    apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                    exact sat_pure (mapPostForkError_basic req pfErr)
                  | ok _ =>
                    dsimp only; split
                    · apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                      exact sat_pure (basic_io rfl)
                    · exact sat_pure trivial

private theorem checkTimedOut_sat (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (startMs : Nat) (timeoutMs? : Option Nat) :
    SatisfiesIO (fun r => match r with
      | .error _ => True
      | .ok (b, _) => timeoutMs? = none → b = false)
      (LinuxSyscall.TimeRand.checkTimedOut tr startMs timeoutMs?) := by
  cases timeoutMs? with
  | none => unfold LinuxSyscall.TimeRand.checkTimedOut; exact sat_pure (fun _ => rfl)
  | some _ =>
    unfold LinuxSyscall.TimeRand.checkTimedOut LinuxSyscall.TimeRand.monoNowMs
    apply sat_seq; intro r
    cases r with
    | error _ => exact sat_pure trivial
    | ok _ => dsimp only; split <;> exact sat_pure (fun h => by cases h)

theorem readStartMsOpt_sat (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (timeoutMs? : Option Nat) :
    SatisfiesIO basicErrOrOk (readStartMsOpt tr timeoutMs?) := by
  cases timeoutMs? with
  | none => exact sat_pure trivial
  | some _ =>
    unfold readStartMsOpt LinuxSyscall.TimeRand.monoNowMs
    apply sat_seq; intro r
    cases r with
    | ok _ => exact sat_pure trivial
    | error e => exact sat_pure (mapErrno_basic _ _ e)

private theorem writeStdinStep_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (inFd : fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (pos : Nat) (prog : Bool) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e
      | .ok (_, _, _, to) => timeoutMs? = none → to = false)
      (writeStdinStep files tr inFd stdin startMs timeoutMs? pos prog fuel) := by
  induction fuel generalizing pos prog with
  | zero =>
    unfold writeStdinStep; split
    · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
    · exact sat_pure (fun _ => rfl)
  | succ _ ih =>
    unfold writeStdinStep; split
    · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
    · refine sat_bind (checkTimedOut_sat tr startMs timeoutMs?) fun r1 hr1 => ?_
      cases r1 with
      | error e => apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)
      | ok pair =>
        rcases pair with ⟨b, _⟩
        cases b with
        | true => apply sat_seq; intro _; exact sat_pure hr1
        | false =>
          apply sat_seq; intro r2
          cases r2 with
          | ok _ =>
            dsimp only; split
            · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
            · split
              · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
              · exact ih _ true
          | error _ =>
            dsimp only; split
            · exact ih pos prog
            · split
              · exact sat_pure (fun _ => rfl)
              · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)

private theorem drainPipeStep_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (pipeFd : fd) (otherLen startMs : Nat) (timeoutMs? maxOut? : Option Nat)
    (chunks : Array ByteArray) (curLen iterBytes : Nat) (prog : Bool) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .ioErr e => isBasicErrKind e
      | .timedOut _ _ => timeoutMs? ≠ none
      | .limitExceeded _ _ => maxOut? ≠ none
      | .cont _ _ _ _ => True)
      (drainPipeStep files tr pipeFd otherLen startMs timeoutMs? maxOut?
        chunks curLen iterBytes prog fuel) := by
  induction fuel generalizing chunks curLen iterBytes prog with
  | zero => exact sat_pure trivial
  | succ _ ih =>
    unfold drainPipeStep; split
    · exact sat_pure trivial
    · refine sat_bind (checkTimedOut_sat tr startMs timeoutMs?) fun r1 hr1 => ?_
      cases r1 with
      | error e => apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)
      | ok pair =>
        rcases pair with ⟨b, _⟩
        cases b with
        | true => apply sat_seq; intro _; exact sat_pure (fun hnone => by cases hr1 hnone)
        | false =>
          apply sat_seq; intro r2
          cases r2 with
          | ok _ =>
            dsimp only; split
            · apply sat_seq; intro _; exact sat_pure trivial
            · cases maxOut? with
              | none => exact ih _ _ _ true
              | some _ =>
                dsimp only; split
                · apply sat_seq; intro _; exact sat_pure (fun h => by cases h)
                · exact ih _ _ _ true
          | error e =>
            dsimp only; split
            · exact ih chunks curLen iterBytes prog
            · split
              · exact sat_pure trivial
              · apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)

theorem streamPipesLoop_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd)
    (poll : LinuxSyscall.Poll.PollOpsM IO fd)
    (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (stdin : ByteArray) (startMs : Nat) (timeoutMs? maxOut? : Option Nat) (stepFuel : Nat)
    (st : StreamLoopState fd) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e
      | .ok (.timedOut _ _) => timeoutMs? ≠ none
      | .ok (.limitExceeded _ _) => maxOut? ≠ none
      | .ok (.eof _ _) => True)
      (streamPipesLoop files poll tr stdin startMs timeoutMs? maxOut? stepFuel st fuel) := by
  induction fuel generalizing st with
  | zero =>
    unfold streamPipesLoop; apply sat_seq; intro _; exact sat_pure (basic_io rfl)
  | succ _ ih =>
    unfold streamPipesLoop; split
    · exact sat_pure trivial
    · refine sat_bind (checkTimedOut_sat tr startMs timeoutMs?) fun r1 hr1 => ?_
      cases r1 with
      | error e => apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)
      | ok pair =>
        rcases pair with ⟨b, _⟩
        cases b with
        | true => apply sat_seq; intro _; exact sat_pure (fun hnone => by cases hr1 hnone)
        | false =>
          apply sat_seq; intro rPoll
          cases rPoll with
          | error e =>
            dsimp only; split
            · exact ih st
            · apply sat_seq; intro _; exact sat_pure (mapErrno_basic none "ppoll" e)
          | ok revents =>
            dsimp only; generalize decodeReadyFlags st revents = rf; rcases rf with ⟨inR, outR, errR⟩
            dsimp only; split
            · exact ih st
            · have hInSat : SatisfiesIO
                (fun r => match r with
                  | (_, _, _, to, some e) => isBasicErrKind e ∧ (timeoutMs? = none → to = false)
                  | (_, _, _, to, none) => timeoutMs? = none → to = false)
                (stepStdinIfReady inR files tr st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel) := by
                unfold stepStdinIfReady; split
                · unfold stepStdinOpt
                  cases st.inFd? with
                  | none => exact sat_pure (fun _ => rfl)
                  | some inFd =>
                    refine sat_bind (writeStdinStep_sat files tr inFd stdin startMs timeoutMs? st.stdinPos false stepFuel) fun r hr => ?_
                    cases r with | error _ => exact sat_pure ⟨hr, fun _ => rfl⟩ | ok _ => exact sat_pure hr
                · exact sat_pure (fun _ => rfl)
              refine sat_bind hInSat fun stup hstup => ?_
              rcases stup with ⟨inFdNext?, stdinPos', _, inTimedOut, inErr?⟩
              cases inErr? with
              | some _ => apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure hstup.1
              | none =>
                dsimp only; split
                · next hto =>
                  apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                  exact sat_pure (fun hnone => by have hf := hstup hnone; rw [hto] at hf; cases hf)
                · have hOutSat : SatisfiesIO
                    (fun r => match r with
                      | .ioErr e => isBasicErrKind e | .timedOut _ _ => timeoutMs? ≠ none
                      | .limitExceeded _ _ => maxOut? ≠ none | .cont _ _ _ _ => True)
                    (stepDrainIfReady outR files tr st.outFd? st.errLen startMs timeoutMs? maxOut? st.outChunks st.outLen stepFuel) := by
                    unfold stepDrainIfReady; split
                    · unfold stepDrainOpt
                      cases st.outFd? with
                      | none => exact sat_pure trivial
                      | some pfd => exact drainPipeStep_sat files tr pfd st.errLen startMs timeoutMs? maxOut? st.outChunks st.outLen 0 false stepFuel
                    · exact sat_pure trivial
                  refine sat_bind hOutSat fun outStep ho => ?_
                  cases outStep with
                  | ioErr _ | timedOut _ _ | limitExceeded _ _ =>
                    apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure ho
                  | cont outFdNext? outChunks' outLen' _ =>
                    have hErrSat : SatisfiesIO
                        (fun r => match r with
                          | .ioErr e => isBasicErrKind e | .timedOut _ _ => timeoutMs? ≠ none
                          | .limitExceeded _ _ => maxOut? ≠ none | .cont _ _ _ _ => True)
                        (stepDrainIfReady errR files tr st.errFd? outLen' startMs timeoutMs? maxOut? st.errChunks st.errLen stepFuel) := by
                      unfold stepDrainIfReady; split
                      · unfold stepDrainOpt
                        cases st.errFd? with
                        | none => exact sat_pure trivial
                        | some pfd => exact drainPipeStep_sat files tr pfd outLen' startMs timeoutMs? maxOut? st.errChunks st.errLen 0 false stepFuel
                      · exact sat_pure trivial
                    refine sat_bind hErrSat fun errStep he => ?_
                    cases errStep with
                    | ioErr _ | timedOut _ _ | limitExceeded _ _ =>
                      apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure he
                    | cont _ _ _ _ =>
                      dsimp only; split
                      · exact sat_pure trivial
                      · exact ih _

theorem waitBlockingLoop_sat {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM IO fd) (pid : Int32)
    (stdout stderr : ByteArray) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e | .ok (.timedOut _ _) => False
      | .ok (.outputLimitExceeded _ _) => False | .ok _ => True)
      (waitBlockingLoop proc pid stdout stderr fuel) := by
  induction fuel with
  | zero => exact sat_pure (basic_io rfl)
  | succ _ ih =>
    unfold waitBlockingLoop; apply sat_seq; intro r
    cases r with
    | ok wr => cases wr <;> exact sat_pure trivial
    | error e =>
      dsimp only; split
      · exact ih
      · split
        · exact sat_pure trivial
        · exact sat_pure (mapErrno_basic _ _ e)

theorem waitTimedLoop_sat {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e | .ok (_, .outputLimitExceeded _ _) => False | .ok _ => True)
      (waitTimedLoop proc tr pid startMs timeoutMs stdout stderr fuel) := by
  induction fuel with
  | zero => exact sat_pure (basic_io rfl)
  | succ _ ih =>
    unfold waitTimedLoop; apply sat_seq; intro r
    cases r with
    | ok wr =>
      cases wr with
      | stillRunning =>
        refine sat_bind (checkTimedOut_sat tr startMs (some timeoutMs)) fun rc _ => ?_
        cases rc with
        | error e => exact sat_pure (mapErrno_basic _ _ e)
        | ok pair =>
          rcases pair with ⟨b, _⟩
          cases b with
          | true => exact sat_pure trivial
          | false => apply sat_seq; intro _; exact ih
      | exited _ _ | signaled _ _ _ | stopped _ _ | continued _ => exact sat_pure trivial
    | error e =>
      dsimp only; split
      · exact ih
      · split
        · exact sat_pure trivial
        · exact sat_pure (mapErrno_basic _ _ e)

/-- Outcome limit predicate for `awaitOsPhase`. -/
def outcomePred (timeoutMs? maxOut? : Option Nat) : ExecOutcome → Prop
  | .timedOut _ _ => timeoutMs? ≠ none
  | .outputLimitExceeded _ _ => maxOut? ≠ none
  | _ => True

end LeanSwe.Process.Proofs

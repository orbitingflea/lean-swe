import Core.Assumptions
import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Impl
import LeanSwe.Process.Interface

namespace LeanSwe.Process.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.SysBridge

private def isBasicErrKind (e : ProcessError) : Prop :=
  e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧
    e.kind ≠ .terminatedBySignal ∧ e.kind ≠ .nonZeroExit

private def basicErrOrOk {α : Type} : Except ProcessError α → Prop
  | .error e => isBasicErrKind e
  | .ok _ => True

private def SatisfiesIO {α : Type} (P : α → Prop) (act : IO α) : Prop :=
  ∀ w : Void IO.RealWorld,
    match act w with
    | .ok a _ => P a
    | .error _ _ => True

private theorem sat_pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    SatisfiesIO P (pure a) :=
  fun _ => h

private theorem sat_any {α : Type} (x : IO α) : SatisfiesIO (fun _ => True) x := by
  intro w
  cases x w <;> exact trivial

private theorem sat_bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : IO α} {f : α → IO β}
    (hx : SatisfiesIO P x) (hf : ∀ a, P a → SatisfiesIO Q (f a)) :
    SatisfiesIO Q (x >>= f) := by
  intro w
  change match EST.bind x f w with | .ok b _ => Q b | .error _ _ => True
  unfold EST.bind
  have hxw := hx w
  cases h : x w with
  | error _ _ => exact trivial
  | ok a w' =>
    rw [h] at hxw
    exact hf a hxw w'

private theorem sat_seq {α β : Type} {Q : β → Prop} {x : IO α} {f : α → IO β}
    (hf : ∀ a, SatisfiesIO Q (f a)) :
    SatisfiesIO Q (x >>= f) :=
  sat_bind (sat_any x) (fun a _ => hf a)

private theorem basic_of_kind {e : ProcessError} (k : ProcessErrorKind)
    (heq : e.kind = k) (h1 : k ≠ .timedOut) (h2 : k ≠ .outputLimitExceeded)
    (h3 : k ≠ .terminatedBySignal) (h4 : k ≠ .nonZeroExit) : isBasicErrKind e := by
  rw [isBasicErrKind, heq]
  exact ⟨h1, h2, h3, h4⟩

private theorem basic_notFound {e : ProcessError} (h : e.kind = .notFound) : isBasicErrKind e :=
  basic_of_kind .notFound h (by decide) (by decide) (by decide) (by decide)

private theorem basic_perm {e : ProcessError} (h : e.kind = .permissionDenied) : isBasicErrKind e :=
  basic_of_kind .permissionDenied h (by decide) (by decide) (by decide) (by decide)

private theorem basic_invalid {e : ProcessError} (h : e.kind = .invalidInput) : isBasicErrKind e :=
  basic_of_kind .invalidInput h (by decide) (by decide) (by decide) (by decide)

private theorem basic_io {e : ProcessError} (h : e.kind = .ioError) : isBasicErrKind e :=
  basic_of_kind .ioError h (by decide) (by decide) (by decide) (by decide)

private theorem mapErrno_basic (prog? : Option String) (ctx : String) (e : LinuxSyscall.Errno) :
    isBasicErrKind (mapErrno prog? ctx e) := by
  unfold mapErrno
  dsimp only
  split
  · exact basic_notFound rfl
  · split
    · exact basic_perm rfl
    · split
      · exact basic_invalid rfl
      · exact basic_io rfl

private theorem mapIoError_basic (prog? : Option String) (err : IO.Error) :
    isBasicErrKind (mapIoError prog? err) := by
  unfold mapIoError
  cases err <;> dsimp only [ioErrorToRaw, mapRawError]
  all_goals first
    | exact basic_notFound rfl
    | exact basic_perm rfl
    | exact basic_invalid rfl
    | exact basic_io rfl

private theorem ensureNonEmptyMsg_basic (fb : String) {err : ProcessError}
    (h : isBasicErrKind err) : isBasicErrKind (Internal.ensureNonEmptyMsg fb err) := by
  unfold Internal.ensureNonEmptyMsg
  split <;> exact h

private theorem sysBridge_ensureNonEmptyMsg_basic (fb : String) {err : ProcessError}
    (h : isBasicErrKind err) : isBasicErrKind (SysBridge.ensureNonEmptyMsg fb err) := by
  unfold SysBridge.ensureNonEmptyMsg
  split <;> exact h

private theorem mapPostForkError_basic (req : ExecRequest) (pfErr : PostFork.PostForkError) :
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

private def exceptBasicPred {α : Type} (P : α → Prop) : Except ProcessError α → Prop
  | .error e => isBasicErrKind e
  | .ok a => P a

private theorem catchProc_sat {α : Type} {P : α → Prop} (prog? : Option String)
    (act : IO (Except ProcessError α))
    (h : SatisfiesIO (exceptBasicPred P) act)
    (w : Void IO.RealWorld) :
    ∃ r w', catchProc prog? act w = .ok r w' ∧ exceptBasicPred P r := by
  have heq : catchProc prog? act w =
      EST.tryCatch act (fun err => EST.pure (.error (mapIoError prog? err))) w := rfl
  rw [heq]
  have hw := h w
  cases hact : act w with
  | ok res w' =>
    rw [hact] at hw
    exact ⟨res, w', by simp [EST.tryCatch, hact], hw⟩
  | error err w' =>
    exact ⟨.error (mapIoError prog? err), w', by simp [EST.tryCatch, EST.pure, hact],
      mapIoError_basic prog? err⟩

private theorem catchProc_noThrow {α : Type} (prog? : Option String)
    (act : IO (Except ProcessError α)) (w : Void IO.RealWorld) :
    ∃ r w', catchProc prog? act w = .ok r w' := by
  have heq : catchProc prog? act w =
      EST.tryCatch act (fun err => EST.pure (.error (mapIoError prog? err))) w := rfl
  rw [heq]
  cases h : act w with
  | ok a w' => exact ⟨a, w', by simp [EST.tryCatch, h]⟩
  | error e w' => exact ⟨.error (mapIoError prog? e), w', by simp [EST.tryCatch, EST.pure, h]⟩

private theorem validateWorkingDir_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (cwd? : Option String) (fuel : Nat) :
    SatisfiesIO basicErrOrOk (validateWorkingDir files cwd? fuel) := by
  unfold validateWorkingDir
  cases cwd? with
  | none => exact sat_pure trivial
  | some cwdDir =>
    dsimp only
    split
    · exact sat_pure (mapErrno_basic _ _ _)
    · apply sat_seq; intro r1
      cases r1 with
      | error e => exact sat_pure (mapErrno_basic _ _ e)
      | ok st =>
        dsimp only
        split
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
    unfold searchPathDirs
    split
    · exact sat_pure (basic_perm rfl)
    · exact sat_pure (basic_notFound rfl)
  | cons dir rest ih =>
    unfold searchPathDirs
    apply sat_seq; intro r1
    cases r1 with
    | error e =>
      dsimp only
      split
      · exact ih true
      · split
        · exact ih sawPerm
        · exact sat_pure (mapErrno_basic _ _ e)
    | ok st =>
      dsimp only
      split
      · exact ih true
      · apply sat_seq; intro r2
        cases r2 with
        | error e =>
          dsimp only
          split
          · exact ih true
          · split
            · exact ih sawPerm
            · exact sat_pure (mapErrno_basic _ _ e)
        | ok _ => exact sat_pure trivial

private theorem resolveExecutablePath_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (program : String) (cwd? : Option String)
    (envBytes : Array ByteArray) (fuel : Nat) :
    SatisfiesIO basicErrOrOk (resolveExecutablePath files program cwd? envBytes fuel) := by
  unfold resolveExecutablePath
  split
  · exact sat_pure trivial
  · exact searchPathDirs_sat files program cwd? fuel false _

private theorem readBaseEnv_ioSysDeps_sat (inheritEnv : Bool) :
    SatisfiesIO basicErrOrOk (readBaseEnv ioSysDeps inheritEnv) := by
  unfold readBaseEnv
  split
  · dsimp only [ioSysDeps]
    apply sat_seq; intro _
    exact sat_pure trivial
  · exact sat_pure trivial

private theorem spawnPure_ioSysDeps_sat (tbl : ProcTableOpsM IO LinuxSyscall.RawFd)
    (fuel : Nat) (req : ExecRequest) :
    SatisfiesIO basicErrOrOk (spawnPure ioSysDeps tbl fuel req) := by
  unfold spawnPure
  split
  · exact sat_pure (basic_invalid rfl)
  · refine sat_bind (validateWorkingDir_sat ioSysDeps.files req.cwd fuel) fun r1 hr1 => ?_
    cases r1 with
    | error e => exact sat_pure hr1
    | ok _ =>
      refine sat_bind (readBaseEnv_ioSysDeps_sat req.inheritEnv) fun r2 hr2 => ?_
      cases r2 with
      | error e => exact sat_pure (sysBridge_ensureNonEmptyMsg_basic _ hr2)
      | ok baseEnv =>
        refine sat_bind (resolveExecutablePath_sat ioSysDeps.files req.program req.cwd _ fuel) fun r3 hr3 => ?_
        cases r3 with
        | error e => exact sat_pure hr3
        | ok resolvedPath =>
          dsimp only
          split
          · exact sat_pure (basic_invalid rfl)
          · apply sat_seq; intro r4
            cases r4 with
            | error e1 => exact sat_pure (mapErrno_basic _ _ e1)
            | ok p1 =>
              apply sat_seq; intro r5
              cases r5 with
              | error e2 =>
                apply sat_seq; intro _; apply sat_seq; intro _
                exact sat_pure (mapErrno_basic _ _ e2)
              | ok p2 =>
                apply sat_seq; intro r6
                cases r6 with
                | error e3 =>
                  apply sat_seq; intro _; apply sat_seq; intro _
                  apply sat_seq; intro _; apply sat_seq; intro _
                  exact sat_pure (mapErrno_basic _ _ e3)
                | ok p3 =>
                  apply sat_seq; intro spawnRes
                  apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                  cases spawnRes with
                  | error pfErr =>
                    apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                    exact sat_pure (mapPostForkError_basic req pfErr)
                  | ok child =>
                    dsimp only
                    split
                    · apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                      exact sat_pure (basic_io rfl)
                    · apply sat_seq; intro _
                      exact sat_pure trivial

private theorem checkTimedOut_sat (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (startMs : Nat) (timeoutMs? : Option Nat) :
    SatisfiesIO (fun r => match r with
      | .error _ => True
      | .ok (b, _) => timeoutMs? = none → b = false)
      (LinuxSyscall.TimeRand.checkTimedOut tr startMs timeoutMs?) := by
  cases timeoutMs? with
  | none =>
    unfold LinuxSyscall.TimeRand.checkTimedOut
    exact sat_pure (fun _ => rfl)
  | some timeoutMs =>
    unfold LinuxSyscall.TimeRand.checkTimedOut LinuxSyscall.TimeRand.monoNowMs
    apply sat_seq; intro r
    cases r with
    | error _ => exact sat_pure trivial
    | ok _ =>
      dsimp only
      split <;> exact sat_pure (fun h => by cases h)

private theorem readStartMsOpt_sat (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
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
    unfold writeStdinStep
    split
    · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
    · exact sat_pure (fun _ => rfl)
  | succ f ih =>
    unfold writeStdinStep
    split
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
          | ok n =>
            dsimp only
            split
            · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
            · split
              · apply sat_seq; intro _; exact sat_pure (fun _ => rfl)
              · exact ih _ true
          | error e =>
            dsimp only
            split
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
  | succ f ih =>
    unfold drainPipeStep
    split
    · exact sat_pure trivial
    · refine sat_bind (checkTimedOut_sat tr startMs timeoutMs?) fun r1 hr1 => ?_
      cases r1 with
      | error e => apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)
      | ok pair =>
        rcases pair with ⟨b, _⟩
        cases b with
        | true =>
          apply sat_seq; intro _
          exact sat_pure (fun hnone => by cases hr1 hnone)
        | false =>
          apply sat_seq; intro r2
          cases r2 with
          | ok chunk =>
            dsimp only
            split
            · apply sat_seq; intro _; exact sat_pure trivial
            · cases maxOut? with
              | none => exact ih _ _ _ true
              | some maxOut =>
                dsimp only
                split
                · apply sat_seq; intro _; exact sat_pure (fun h => by cases h)
                · exact ih _ _ _ true
          | error e =>
            dsimp only
            split
            · exact ih chunks curLen iterBytes prog
            · split
              · exact sat_pure trivial
              · apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)

private theorem stepStdinOpt_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (inFd? : Option fd) (stdin : ByteArray) (startMs : Nat) (timeoutMs? : Option Nat)
    (stdinPos stepFuel : Nat) :
    SatisfiesIO (fun r => match r with
      | (_, _, _, to, some e) => isBasicErrKind e ∧ (timeoutMs? = none → to = false)
      | (_, _, _, to, none) => timeoutMs? = none → to = false)
      (stepStdinOpt files tr inFd? stdin startMs timeoutMs? stdinPos stepFuel) := by
  unfold stepStdinOpt
  cases inFd? with
  | none => exact sat_pure (fun _ => rfl)
  | some inFd =>
    refine sat_bind (writeStdinStep_sat files tr inFd stdin startMs timeoutMs? stdinPos false stepFuel)
      fun r hr => ?_
    cases r with
    | error e => exact sat_pure ⟨hr, fun _ => rfl⟩
    | ok tup => exact sat_pure hr

private theorem stepDrainOpt_sat {fd : Type}
    (files : LinuxSyscall.Files.FilesOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (pipeFd? : Option fd) (otherLen startMs : Nat) (timeoutMs? maxOut? : Option Nat)
    (chunks : Array ByteArray) (curLen stepFuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .ioErr e => isBasicErrKind e
      | .timedOut _ _ => timeoutMs? ≠ none
      | .limitExceeded _ _ => maxOut? ≠ none
      | .cont _ _ _ _ => True)
      (stepDrainOpt files tr pipeFd? otherLen startMs timeoutMs? maxOut? chunks curLen stepFuel) := by
  unfold stepDrainOpt
  cases pipeFd? with
  | none => exact sat_pure trivial
  | some pipeFd =>
    exact drainPipeStep_sat files tr pipeFd otherLen startMs timeoutMs? maxOut?
      chunks curLen 0 false stepFuel

private theorem streamPipesLoop_sat {fd : Type}
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
    unfold streamPipesLoop
    apply sat_seq; intro _
    exact sat_pure (basic_io rfl)
  | succ f ih =>
    unfold streamPipesLoop
    split
    · exact sat_pure trivial
    · refine sat_bind (checkTimedOut_sat tr startMs timeoutMs?) fun r1 hr1 => ?_
      cases r1 with
      | error e => apply sat_seq; intro _; exact sat_pure (mapErrno_basic _ _ e)
      | ok pair =>
        rcases pair with ⟨b, remMs⟩
        cases b with
        | true => apply sat_seq; intro _; exact sat_pure (fun hnone => by cases hr1 hnone)
        | false =>
          apply sat_seq; intro rPoll
          cases rPoll with
          | error e =>
            dsimp only
            split
            · exact ih st
            · apply sat_seq; intro _
              exact sat_pure (mapErrno_basic none "ppoll" e)
          | ok revents =>
            dsimp only
            generalize decodeReadyFlags st revents = rf
            rcases rf with ⟨inR, outR, errR⟩
            dsimp only
            split
            · exact ih st
            · have hInSat : SatisfiesIO
                (fun r => match r with
                  | (_, _, _, to, some e) => isBasicErrKind e ∧ (timeoutMs? = none → to = false)
                  | (_, _, _, to, none) => timeoutMs? = none → to = false)
                (stepStdinIfReady inR files tr st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel) := by
                unfold stepStdinIfReady
                split
                · exact stepStdinOpt_sat files tr st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel
                · exact sat_pure (fun _ => rfl)
              refine sat_bind hInSat fun stup hstup => ?_
              rcases stup with ⟨inFdNext?, stdinPos', _, inTimedOut, inErr?⟩
              cases inErr? with
              | some e =>
                apply sat_seq; intro _; apply sat_seq; intro _
                exact sat_pure hstup.1
              | none =>
                dsimp only
                split
                · next hto =>
                  apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
                  exact sat_pure (fun hnone => by have hf := hstup hnone; rw [hto] at hf; cases hf)
                · have hOutSat : SatisfiesIO
                    (fun r => match r with
                      | .ioErr e => isBasicErrKind e
                      | .timedOut _ _ => timeoutMs? ≠ none
                      | .limitExceeded _ _ => maxOut? ≠ none
                      | .cont _ _ _ _ => True)
                    (stepDrainIfReady outR files tr st.outFd? st.errLen startMs timeoutMs? maxOut?
                      st.outChunks st.outLen stepFuel) := by
                    unfold stepDrainIfReady
                    split
                    · exact stepDrainOpt_sat files tr st.outFd? st.errLen startMs timeoutMs? maxOut?
                        st.outChunks st.outLen stepFuel
                    · exact sat_pure trivial
                  refine sat_bind hOutSat fun outStep ho => ?_
                  cases outStep with
                  | ioErr e =>
                    apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure ho
                  | timedOut _ _ =>
                    apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure ho
                  | limitExceeded _ _ =>
                    apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure ho
                  | cont outFdNext? outChunks' outLen' _ =>
                    have hErrSat : SatisfiesIO
                        (fun r => match r with
                          | .ioErr e => isBasicErrKind e
                          | .timedOut _ _ => timeoutMs? ≠ none
                          | .limitExceeded _ _ => maxOut? ≠ none
                          | .cont _ _ _ _ => True)
                        (stepDrainIfReady errR files tr st.errFd? outLen' startMs timeoutMs? maxOut?
                          st.errChunks st.errLen stepFuel) := by
                      unfold stepDrainIfReady
                      split
                      · exact stepDrainOpt_sat files tr st.errFd? outLen' startMs timeoutMs? maxOut?
                          st.errChunks st.errLen stepFuel
                      · exact sat_pure trivial
                    refine sat_bind hErrSat fun errStep he => ?_
                    cases errStep with
                    | ioErr e =>
                      apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure he
                    | timedOut _ _ =>
                      apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure he
                    | limitExceeded _ _ =>
                      apply sat_seq; intro _; apply sat_seq; intro _; exact sat_pure he
                    | cont errFdNext? errChunks' errLen' _ =>
                      dsimp only
                      split
                      · exact sat_pure trivial
                      · exact ih _

private theorem waitBlockingLoop_sat {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM IO fd) (pid : Int32)
    (stdout stderr : ByteArray) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e
      | .ok (.timedOut _ _) => False
      | .ok (.outputLimitExceeded _ _) => False
      | .ok _ => True)
      (waitBlockingLoop proc pid stdout stderr fuel) := by
  induction fuel with
  | zero => exact sat_pure (basic_io rfl)
  | succ f ih =>
    unfold waitBlockingLoop
    apply sat_seq; intro r
    cases r with
    | ok wr =>
      cases wr <;> exact sat_pure trivial
    | error e =>
      dsimp only
      split
      · exact ih
      · split
        · exact sat_pure trivial
        · exact sat_pure (mapErrno_basic _ _ e)

private theorem waitTimedLoop_sat {fd : Type}
    (proc : LinuxSyscall.Process.ProcessOpsM IO fd) (tr : LinuxSyscall.TimeRand.TimeRandOpsM IO)
    (pid : Int32) (startMs timeoutMs : Nat) (stdout stderr : ByteArray) (fuel : Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e
      | .ok (_, .outputLimitExceeded _ _) => False
      | .ok _ => True)
      (waitTimedLoop proc tr pid startMs timeoutMs stdout stderr fuel) := by
  induction fuel with
  | zero => exact sat_pure (basic_io rfl)
  | succ f ih =>
    unfold waitTimedLoop
    apply sat_seq; intro r
    cases r with
    | ok wr =>
      cases wr with
      | stillRunning =>
        refine sat_bind (checkTimedOut_sat tr startMs (some timeoutMs)) fun rc hrc => ?_
        cases rc with
        | error e => exact sat_pure (mapErrno_basic _ _ e)
        | ok pair =>
          rcases pair with ⟨b, remMs⟩
          cases b with
          | true => exact sat_pure trivial
          | false => apply sat_seq; intro _; exact ih
      | exited _ _ => exact sat_pure trivial
      | signaled _ _ _ => exact sat_pure trivial
      | stopped _ _ => exact sat_pure trivial
      | continued _ => exact sat_pure trivial
    | error e =>
      dsimp only
      split
      · exact ih
      · split
        · exact sat_pure trivial
        · exact sat_pure (mapErrno_basic _ _ e)

private theorem awaitOutputPure_sat {fd : Type}
    (deps : SysDepsM IO fd) (tbl : ProcTableOpsM IO fd) (eintrFuel ioFuel : Nat)
    (h : ProcessHandle) (stdin : ByteArray) (timeoutMs? maxOut? : Option Nat) :
    SatisfiesIO (fun r => match r with
      | .error e => isBasicErrKind e
      | .ok (.timedOut _ _) => timeoutMs? ≠ none
      | .ok (.outputLimitExceeded _ _) => maxOut? ≠ none
      | .ok _ => True)
      (awaitOutputPure deps tbl eintrFuel ioFuel h stdin timeoutMs? maxOut?) := by
  unfold awaitOutputPure
  apply sat_seq; intro opt
  cases opt with
  | none => exact sat_pure (basic_io rfl)
  | some tup =>
    rcases tup with ⟨pid, inFd0?, outFd0?, errFd0?⟩
    apply sat_seq; intro inFd?
    apply sat_seq; intro _
    apply sat_seq; intro _
    refine sat_bind (readStartMsOpt_sat deps.timeRand timeoutMs?) fun rs hrs => ?_
    cases rs with
    | error e =>
      apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
      exact sat_pure hrs
    | ok startMs =>
      refine sat_bind (streamPipesLoop_sat deps.files deps.poll deps.timeRand stdin startMs timeoutMs? maxOut? eintrFuel
        { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? } ioFuel) fun rsp hrsp => ?_
      cases rsp with
      | error e => exact sat_pure hrsp
      | ok spOut =>
        cases spOut with
        | timedOut out err =>
          apply sat_seq; intro okFlag
          split
          · exact sat_pure (basic_io rfl)
          · exact sat_pure hrsp
        | limitExceeded out err =>
          apply sat_seq; intro okFlag
          split
          · exact sat_pure (basic_io rfl)
          · exact sat_pure hrsp
        | eof out err =>
          cases timeoutMs? with
          | none =>
            refine sat_bind (waitBlockingLoop_sat deps.proc pid.toInt32 out err eintrFuel)
              fun rwb hrwb => ?_
            cases rwb with
            | error e => exact sat_pure hrwb
            | ok outcome =>
              apply sat_seq; intro okFlag
              split
              · exact sat_pure (basic_io rfl)
              · cases outcome with
                | exited _ => exact sat_pure trivial
                | signaled _ _ _ => exact sat_pure trivial
                | timedOut _ _ => exact False.elim hrwb
                | outputLimitExceeded _ _ => exact False.elim hrwb
          | some timeoutMs =>
            refine sat_bind (waitTimedLoop_sat deps.proc deps.timeRand pid.toInt32 startMs timeoutMs out err ioFuel)
              fun rwt hrwt => ?_
            cases rwt with
            | error e => exact sat_pure hrwt
            | ok pair =>
              rcases pair with ⟨waited, outcome⟩
              apply sat_seq; intro okFlag
              split
              · exact sat_pure (basic_io rfl)
              · cases outcome with
                | exited _ => exact sat_pure trivial
                | signaled _ _ _ => exact sat_pure trivial
                | timedOut _ _ => exact sat_pure (fun hc => by cases hc)
                | outputLimitExceeded _ _ => exact False.elim hrwt

private theorem reapPure_sat {fd : Type}
    (deps : SysDepsM IO fd) (tbl : ProcTableOpsM IO fd) (eintrFuel : Nat) (h : ProcessHandle) :
    SatisfiesIO basicErrOrOk (reapPure deps tbl eintrFuel h) := by
  unfold reapPure
  apply sat_seq; intro slot?
  cases slot? with
  | none => exact sat_pure trivial
  | some slot =>
    apply sat_seq; intro _; apply sat_seq; intro _; apply sat_seq; intro _
    split
    · apply sat_seq; intro r
      cases r with
      | ok _ => exact sat_pure trivial
      | error oe =>
        cases oe with
        | none => exact sat_pure (basic_io rfl)
        | some e => exact sat_pure (mapErrno_basic _ _ e)
    · exact sat_pure trivial

private theorem io_bind_ok {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : x w = .ok a w') :
    (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  simp [EST.bind, h]

private theorem validateRequest_err_is_invalidInput (req : ExecRequest) (err : ProcessError)
    (h : Internal.validateRequest req = .error err) : err.kind = .invalidInput := by
  unfold Internal.validateRequest at h
  repeat (first
    | (rw [Except.error.injEq] at h; subst h; rfl)
    | (rw [Except.ok.injEq] at h; cases h)
    | split at h
    | cases h)

private theorem validateRequest_ok_limits {req norm : ExecRequest}
    (h : Internal.validateRequest req = .ok norm) :
    norm.timeoutMs = req.timeoutMs ∧ norm.maxOutputBytes = req.maxOutputBytes := by
  unfold Internal.validateRequest at h
  repeat (first
    | (rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | split at h
    | cases h)

private def outcomePred (timeoutMs? maxOut? : Option Nat) : ExecOutcome → Prop
  | .timedOut _ _ => timeoutMs? ≠ none
  | .outputLimitExceeded _ _ => maxOut? ≠ none
  | _ => True

private theorem awaitOutputPure_sat_p {fd : Type}
    (deps : SysDepsM IO fd) (tbl : ProcTableOpsM IO fd) (eintrFuel ioFuel : Nat)
    (h : ProcessHandle) (stdin : ByteArray) (timeoutMs? maxOut? : Option Nat) :
    SatisfiesIO (exceptBasicPred (outcomePred timeoutMs? maxOut?))
      (awaitOutputPure deps tbl eintrFuel ioFuel h stdin timeoutMs? maxOut?) := by
  intro w0
  have h0 := awaitOutputPure_sat deps tbl eintrFuel ioFuel h stdin timeoutMs? maxOut? w0
  cases hr : awaitOutputPure deps tbl eintrFuel ioFuel h stdin timeoutMs? maxOut? w0 with
  | error _ _ => exact trivial
  | ok r _ =>
    rw [hr] at h0
    cases r with
    | error _ => exact h0
    | ok o => cases o <;> exact h0

private theorem basicErrOrOk_to_exceptBasic {α : Type} {act : IO (Except ProcessError α)}
    (h : SatisfiesIO basicErrOrOk act) :
    SatisfiesIO (exceptBasicPred (fun _ => True)) act := by
  intro w
  have hw := h w
  cases hr : act w with
  | error _ _ => exact trivial
  | ok r _ =>
    rw [hr] at hw
    cases r <;> exact hw

private theorem defaultOps_run_inv (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', Internal.run defaultOps req w = .ok r w' ∧
      match r with
      | .ok _ => True
      | .error e =>
        e.kind ≠ .nonZeroExit ∧
        (req.timeoutMs = none → e.kind ≠ .timedOut) ∧
        (req.maxOutputBytes = none → e.kind ≠ .outputLimitExceeded) := by
  unfold Internal.run
  cases hVal : Internal.validateRequest req with
  | error err =>
    have hk := validateRequest_err_is_invalidInput req err hVal
    refine ⟨.error err, w, rfl, ?_⟩
    dsimp only
    rw [hk]
    exact ⟨by decide, fun _ => by decide, fun _ => by decide⟩
  | ok norm =>
    have hlim := validateRequest_ok_limits hVal
    dsimp only
    rcases catchProc_sat (some norm.program)
        (spawnPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL norm)
        (basicErrOrOk_to_exceptBasic (spawnPure_ioSysDeps_sat ioProcTableOps DEFAULT_EINTR_FUEL norm)) w with
      ⟨rSpawn, w1, hSpawn, hSpawnInv⟩
    change defaultOps.spawn norm w = .ok rSpawn w1 at hSpawn
    rw [io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error err =>
      refine ⟨.error (Internal.ensureNonEmptyMsg "process spawn failed" err), w1, rfl, ?_⟩
      have hb := ensureNonEmptyMsg_basic "process spawn failed" hSpawnInv
      exact ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩
    | ok h =>
      dsimp only
      rcases catchProc_sat (P := outcomePred norm.timeoutMs norm.maxOutputBytes) none
          (awaitOutputPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
            h norm.stdin norm.timeoutMs norm.maxOutputBytes)
          (awaitOutputPure_sat_p ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
            h norm.stdin norm.timeoutMs norm.maxOutputBytes) w1 with
        ⟨rAwait, w2, hAwait, hAwaitInv⟩
      change defaultOps.awaitOutput h norm.stdin norm.timeoutMs norm.maxOutputBytes w1 = .ok rAwait w2 at hAwait
      rw [io_bind_ok _ _ _ hAwait]
      cases rAwait with
      | error err =>
        dsimp only
        rcases catchProc_noThrow none _ w2 with ⟨_, w3, hKill⟩
        change defaultOps.killProcessGroup h w2 = .ok _ w3 at hKill
        rw [io_bind_ok _ _ _ hKill]
        rcases catchProc_noThrow none _ w3 with ⟨_, w4, hReap⟩
        change defaultOps.reap h w3 = .ok _ w4 at hReap
        rw [io_bind_ok _ _ _ hReap]
        refine ⟨.error (Internal.ensureNonEmptyMsg "process I/O failed" err), w4, rfl, ?_⟩
        have hb := ensureNonEmptyMsg_basic "process I/O failed" hAwaitInv
        exact ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩
      | ok outcome =>
        cases outcome with
        | exited res =>
          dsimp only
          rcases catchProc_sat none
              (reapPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)
              (basicErrOrOk_to_exceptBasic (reapPure_sat ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)) w2 with
            ⟨rReap, w3, hReap, hReapInv⟩
          change defaultOps.reap h w2 = .ok rReap w3 at hReap
          rw [io_bind_ok _ _ _ hReap]
          cases rReap with
          | error err =>
            refine ⟨.error (Internal.ensureNonEmptyMsg "process reap failed" err), w3, rfl, ?_⟩
            have hb := ensureNonEmptyMsg_basic "process reap failed" hReapInv
            exact ⟨hb.2.2.2, fun _ => hb.1, fun _ => hb.2.1⟩
          | ok _ =>
            exact ⟨.ok res, w3, rfl, trivial⟩
        | signaled sig out err =>
          dsimp only
          rcases catchProc_noThrow none _ w2 with ⟨_, w3, hKill⟩
          change defaultOps.killProcessGroup h w2 = .ok _ w3 at hKill
          rw [io_bind_ok _ _ _ hKill]
          rcases catchProc_noThrow none _ w3 with ⟨_, w4, hReap⟩
          change defaultOps.reap h w3 = .ok _ w4 at hReap
          rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun _ hc => by cases hc), (fun _ hc => by cases hc)⟩⟩
        | timedOut out err =>
          dsimp only
          rcases catchProc_noThrow none _ w2 with ⟨_, w3, hKill⟩
          change defaultOps.killProcessGroup h w2 = .ok _ w3 at hKill
          rw [io_bind_ok _ _ _ hKill]
          rcases catchProc_noThrow none _ w3 with ⟨_, w4, hReap⟩
          change defaultOps.reap h w3 = .ok _ w4 at hReap
          rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun hnone => False.elim (hAwaitInv (hlim.1.trans hnone))), (fun _ hc => by cases hc)⟩⟩
        | outputLimitExceeded out err =>
          dsimp only
          rcases catchProc_noThrow none _ w2 with ⟨_, w3, hKill⟩
          change defaultOps.killProcessGroup h w2 = .ok _ w3 at hKill
          rw [io_bind_ok _ _ _ hKill]
          rcases catchProc_noThrow none _ w3 with ⟨_, w4, hReap⟩
          change defaultOps.reap h w3 = .ok _ w4 at hReap
          rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl, ⟨(fun hc => by cases hc), (fun _ hc => by cases hc), (fun hnone => False.elim (hAwaitInv (hlim.2.trans hnone)))⟩⟩

private theorem validateRequest_never_kind (kind : ProcessErrorKind) (hne : .invalidInput ≠ kind)
    (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind kind (LeanSwe.Process.validateRequest req) := by
  unfold Core.NeverErrorKindPure LeanSwe.Process.validateRequest defaultApi Internal.mkApiM
  dsimp only
  cases h : Internal.validateRequest req with
  | ok _ => exact trivial
  | error e =>
    dsimp only
    rw [validateRequest_err_is_invalidInput req e h]
    exact hne

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.notFound`. -/
theorem process_validateRequest_never_notFound (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .notFound (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .notFound (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.permissionDenied`. -/
theorem process_validateRequest_never_permissionDenied (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .permissionDenied (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .permissionDenied (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.timedOut`. -/
theorem process_validateRequest_never_timedOut (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .timedOut (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .timedOut (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.outputLimitExceeded`. -/
theorem process_validateRequest_never_outputLimitExceeded (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .outputLimitExceeded (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .outputLimitExceeded (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.terminatedBySignal`. -/
theorem process_validateRequest_never_terminatedBySignal (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .terminatedBySignal (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .terminatedBySignal (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.nonZeroExit`. -/
theorem process_validateRequest_never_nonZeroExit (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .nonZeroExit (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .nonZeroExit (by decide) req

/-- `Process.validateRequest` only returns `.invalidInput` on failure, never `.ioError`. -/
theorem process_validateRequest_never_ioError (req : ExecRequest) :
    Core.NeverErrorKindPure ProcessError.kind .ioError (LeanSwe.Process.validateRequest req) :=
  validateRequest_never_kind .ioError (by decide) req

/-- `Process.run` returns non-zero exit codes inside `ExecResult`, so it never fails with `.nonZeroExit`. -/
theorem process_run_never_nonZeroExit (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.run req) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.run defaultApi Internal.mkApiM
  dsimp only
  rcases defaultOps_run_inv req w with ⟨r, w', hrun, hinv⟩
  rw [hrun]
  cases r with
  | ok _ => exact trivial
  | error e => exact hinv.1

/-- `Process.runCommand` configures `timeoutMs := none`, so it never fails with `.timedOut`. -/
theorem process_runCommand_never_timedOut (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkApiM Internal.mkCommandRequest
  dsimp only
  rcases defaultOps_run_inv { program := program, args := args } w with ⟨r, w', hrun, hinv⟩
  rw [hrun]
  cases r with
  | ok _ => exact trivial
  | error e => exact hinv.2.1 rfl

/-- `Process.runCommand` configures `maxOutputBytes := none`, so it never fails with `.outputLimitExceeded`. -/
theorem process_runCommand_never_outputLimitExceeded (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkApiM Internal.mkCommandRequest
  dsimp only
  rcases defaultOps_run_inv { program := program, args := args } w with ⟨r, w', hrun, hinv⟩
  rw [hrun]
  cases r with
  | ok _ => exact trivial
  | error e => exact hinv.2.2 rfl

/-- `Process.runCommand` delegates to `Process.run`, so it never fails with `.nonZeroExit`. -/
theorem process_runCommand_never_nonZeroExit (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit
      (LeanSwe.Process.runCommand program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommand defaultApi Internal.mkApiM Internal.mkCommandRequest
  dsimp only
  rcases defaultOps_run_inv { program := program, args := args } w with ⟨r, w', hrun, hinv⟩
  rw [hrun]
  cases r with
  | ok _ => exact trivial
  | error e => exact hinv.1

/-- `Process.runCommandChecked` configures `timeoutMs := none`, so it never fails with `.timedOut`. -/
theorem process_runCommandChecked_never_timedOut (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut
      (LeanSwe.Process.runCommandChecked program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommandChecked defaultApi Internal.mkApiM
    Internal.mkCommandRequest Internal.runChecked
  dsimp only
  rcases defaultOps_run_inv { program := program, args := args } w with ⟨r, w', hrun, hinv⟩
  rw [io_bind_ok _ _ _ hrun]
  cases r with
  | error e => exact hinv.2.1 rfl
  | ok res =>
    dsimp only
    cases h0 : (res.exitCode == 0) with
    | true =>
      change match (pure (Except.ok res) : IO (Except ProcessError ExecResult)) w' with
        | .ok (.error e) _ => e.kind ≠ .timedOut | .ok (.ok _) _ => True | .error _ _ => False
      exact trivial
    | false =>
      show ProcessErrorKind.nonZeroExit ≠ ProcessErrorKind.timedOut
      decide

/-- `Process.runCommandChecked` configures `maxOutputBytes := none`, so it never fails with `.outputLimitExceeded`. -/
theorem process_runCommandChecked_never_outputLimitExceeded (program : String) (args : Array String)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.runCommandChecked program args) w := by
  unfold Core.NeverErrorKindIO LeanSwe.Process.runCommandChecked defaultApi Internal.mkApiM
    Internal.mkCommandRequest Internal.runChecked
  dsimp only
  rcases defaultOps_run_inv { program := program, args := args } w with ⟨r, w', hrun, hinv⟩
  rw [io_bind_ok _ _ _ hrun]
  cases r with
  | error e => exact hinv.2.2 rfl
  | ok res =>
    dsimp only
    cases h0 : (res.exitCode == 0) with
    | true => exact trivial
    | false =>
      show ProcessErrorKind.nonZeroExit ≠ ProcessErrorKind.outputLimitExceeded
      decide

private theorem killProcessGroupPure_sat {fd : Type}
    (deps : SysDepsM IO fd) (tbl : ProcTableOpsM IO fd) (eintrFuel : Nat) (h : ProcessHandle) :
    SatisfiesIO basicErrOrOk (killProcessGroupPure deps tbl eintrFuel h) := by
  unfold killProcessGroupPure
  apply sat_seq; intro pg?
  cases pg? with
  | none => exact sat_pure trivial
  | some pgid =>
    dsimp only
    split
    · exact sat_pure trivial
    · apply sat_seq; intro r1
      cases r1 with
      | error e =>
        dsimp only
        split
        · exact sat_pure trivial
        · exact sat_pure (mapErrno_basic _ _ e)
      | ok _ =>
        apply sat_seq; intro vanished
        split
        · exact sat_pure trivial
        · apply sat_seq; intro r2
          cases r2 with
          | error e =>
            dsimp only
            split
            · exact sat_pure trivial
            · exact sat_pure (mapErrno_basic _ _ e)
          | ok _ => exact sat_pure trivial

private theorem defaultOps_spawn_inv (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.spawn req w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.spawn defaultApi Internal.mkApiM Internal.spawn
  dsimp only
  cases hVal : Internal.validateRequest req with
  | error err =>
    exact ⟨.error err, w, rfl, basic_invalid (validateRequest_err_is_invalidInput req err hVal)⟩
  | ok norm =>
    dsimp only
    rcases catchProc_sat (some norm.program)
        (spawnPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL norm)
        (basicErrOrOk_to_exceptBasic (spawnPure_ioSysDeps_sat ioProcTableOps DEFAULT_EINTR_FUEL norm)) w with
      ⟨rSpawn, w1, hSpawn, hSpawnInv⟩
    change defaultOps.spawn norm w = .ok rSpawn w1 at hSpawn
    rw [io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error err => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process spawn failed" hSpawnInv⟩
    | ok h => exact ⟨.ok h, w1, rfl, trivial⟩

private theorem defaultOps_awaitOutput_inv (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.awaitOutput defaultApi Internal.mkApiM Internal.awaitOutput
  dsimp only
  split
  · exact ⟨_, w, rfl, basic_invalid rfl⟩
  · rcases catchProc_sat (P := outcomePred timeoutMs maxOutputBytes) none
        (awaitOutputPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
          h stdin timeoutMs maxOutputBytes)
        (awaitOutputPure_sat_p ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
          h stdin timeoutMs maxOutputBytes) w with
      ⟨rAw, w1, hAw, hAwInv⟩
    change defaultOps.awaitOutput h stdin timeoutMs maxOutputBytes w = .ok rAw w1 at hAw
    rw [io_bind_ok _ _ _ hAw]
    cases rAw with
    | error err => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process I/O failed" hAwInv⟩
    | ok out => exact ⟨.ok out, w1, rfl, trivial⟩

private theorem defaultOps_killProcessGroup_inv (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.killProcessGroup h w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.killProcessGroup defaultApi Internal.mkApiM Internal.killProcessGroup
  dsimp only
  rcases catchProc_sat none
      (killProcessGroupPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)
      (basicErrOrOk_to_exceptBasic (killProcessGroupPure_sat ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)) w with
    ⟨rKg, w1, hKg, hKgInv⟩
  change defaultOps.killProcessGroup h w = .ok rKg w1 at hKg
  rw [io_bind_ok _ _ _ hKg]
  cases rKg with
  | error err => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process group termination failed" hKgInv⟩
  | ok u => exact ⟨.ok u, w1, rfl, trivial⟩

private theorem defaultOps_reap_inv (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.reap h w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.reap defaultApi Internal.mkApiM Internal.reap
  dsimp only
  rcases catchProc_sat none
      (reapPure ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)
      (basicErrOrOk_to_exceptBasic (reapPure_sat ioSysDeps ioProcTableOps DEFAULT_EINTR_FUEL h)) w with
    ⟨rRp, w1, hRp, hRpInv⟩
  change defaultOps.reap h w = .ok rRp w1 at hRp
  rw [io_bind_ok _ _ _ hRp]
  cases rRp with
  | error err => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process reap failed" hRpInv⟩
  | ok u => exact ⟨.ok u, w1, rfl, trivial⟩

/-- `Process.spawn` never fails with `.timedOut`. -/
theorem process_spawn_never_timedOut (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_spawn_inv req w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.spawn` never fails with `.outputLimitExceeded`. -/
theorem process_spawn_never_outputLimitExceeded (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_spawn_inv req w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.spawn` never fails with `.terminatedBySignal`. -/
theorem process_spawn_never_terminatedBySignal (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_spawn_inv req w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.spawn` never fails with `.nonZeroExit`. -/
theorem process_spawn_never_nonZeroExit (req : ExecRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_spawn_inv req w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.awaitOutput` reports timeouts as `.ok (.timedOut ..)`, so it never fails with `.timedOut`. -/
theorem process_awaitOutput_never_timedOut (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.awaitOutput` reports output caps as `.ok (.outputLimitExceeded ..)`, so it never fails with `.outputLimitExceeded`. -/
theorem process_awaitOutput_never_outputLimitExceeded (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.awaitOutput` reports signals as `.ok (.signaled ..)`, so it never fails with `.terminatedBySignal`. -/
theorem process_awaitOutput_never_terminatedBySignal (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.awaitOutput` reports non-zero exit codes inside `.ok (.exited ..)`, so it never fails with `.nonZeroExit`. -/
theorem process_awaitOutput_never_nonZeroExit (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.killProcessGroup` never fails with `.timedOut`. -/
theorem process_killProcessGroup_never_timedOut (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_killProcessGroup_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.killProcessGroup` never fails with `.outputLimitExceeded`. -/
theorem process_killProcessGroup_never_outputLimitExceeded (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_killProcessGroup_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.killProcessGroup` never fails with `.terminatedBySignal`. -/
theorem process_killProcessGroup_never_terminatedBySignal (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_killProcessGroup_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.killProcessGroup` never fails with `.nonZeroExit`. -/
theorem process_killProcessGroup_never_nonZeroExit (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_killProcessGroup_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.reap` never fails with `.timedOut`. -/
theorem process_reap_never_timedOut (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_reap_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.reap` never fails with `.outputLimitExceeded`. -/
theorem process_reap_never_outputLimitExceeded (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_reap_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.reap` never fails with `.terminatedBySignal`. -/
theorem process_reap_never_terminatedBySignal (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_reap_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.reap` never fails with `.nonZeroExit`. -/
theorem process_reap_never_nonZeroExit (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultOps_reap_inv h w with ⟨r, w', hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

end LeanSwe.Process.Proofs

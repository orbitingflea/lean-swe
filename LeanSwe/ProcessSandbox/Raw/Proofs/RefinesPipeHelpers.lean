import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

private theorem sum_byteArray_foldl (xs : List ByteArray) (acc : ByteArray) :
    (xs.foldl (· ++ ·) acc).size = acc.size + (xs.map ByteArray.size).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, ByteArray.size_append]
    omega

/-- `concatChunks` produces a `ByteArray` whose size equals the sum of chunk sizes. -/
theorem concatChunks_size (chunks : Array ByteArray) (cap : Nat) :
    (concatChunks chunks cap).size = (chunks.toList.map ByteArray.size).sum := by
  unfold concatChunks
  rw [sum_byteArray_foldl]
  have hEmpty : (ByteArray.emptyWithCapacity cap).size = 0 := rfl
  rw [hEmpty]; omega

private theorem byteArray_extract_size_le (bs : ByteArray) (b e : Nat) :
    (bs.extract b e).size ≤ e - b := by
  simp only [ByteArray.size_extract]
  omega

/-- `Internal.mapRawError (.ioError none e msg)` always produces a non-empty message. -/
theorem mapRawError_ioError_ne_empty (e : Errno) (msg : String) :
    (Internal.mapRawError (.ioError none e msg)).message ≠ "" := by
  simp only [Internal.mapRawError, Model.Internal.mapRawError]
  cases h : msg.isEmpty with
  | true =>
    simp only [↓reduceIte]
    intro heq
    rw [String.append_eq_empty_iff] at heq
    exact absurd heq.1 (by decide)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact String.isEmpty_eq_false_iff.mp h

/-- `Internal.mapRawError (.unavailable e? msg)` always produces a non-empty message. -/
theorem mapRawError_unavail_ne_empty (e? : Option Errno) (msg : String) :
    (Internal.mapRawError (.unavailable e? msg)).message ≠ "" := by
  simp only [Internal.mapRawError, Model.Internal.mapRawError]
  cases h : msg.isEmpty with
  | true => simp only [↓reduceIte]; decide
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact String.isEmpty_eq_false_iff.mp h

/-- `classifyBoxStreamResult` preserves `stdout`/`stderr`, guarantees `outcomeNonNeg` on `.ok`, and guarantees non-empty error messages on `.error`. -/
theorem classifyBoxStreamResult_spec (program cwd : String) (to lim : Bool)
    (smsg? : Option InitStatusMsg) (stdout stderr : ByteArray) :
    match classifyBoxStreamResult program cwd to lim smsg? stdout stderr with
    | .ok res => res.stdout = stdout ∧ res.stderr = stderr ∧ outcomeNonNeg res.outcome
    | .error err => err.message ≠ "" := by
  unfold classifyBoxStreamResult
  cases smsg? with
  | none =>
    cases to with
    | true => exact ⟨rfl, rfl, trivial⟩
    | false =>
      cases lim with
      | true => exact ⟨rfl, rfl, trivial⟩
      | false => exact ⟨rfl, rfl, Int.natCast_nonneg 9⟩
  | some msg =>
    dsimp only
    cases hExec : (msg.kind == PS_STATUS_EXEC_ERR) with
    | true =>
      simp only [↓reduceIte]
      exact (HostBwrap.mapPathErrnoToSandboxError_classification _ _ _).2.2.1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hInit : (!to && !lim && msg.kind == PS_STATUS_INIT_ERR) with
      | true =>
        simp only [↓reduceIte]
        exact mapRawError_unavail_ne_empty _ _
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases to with
        | true => exact ⟨rfl, rfl, trivial⟩
        | false =>
          cases lim with
          | true => exact ⟨rfl, rfl, trivial⟩
          | false =>
            cases hEx : (msg.kind == PS_STATUS_EXITED) with
            | true => exact ⟨rfl, rfl, Int.natCast_nonneg _⟩
            | false =>
              cases hSig : (msg.kind == PS_STATUS_SIGNALED) with
              | true => exact ⟨rfl, rfl, Int.natCast_nonneg _⟩
              | false => exact ⟨rfl, rfl, Int.natCast_nonneg 9⟩

/-- `TimeRand.monoNowMs` preserves `proj`. -/
theorem preservesProj_monoNowMs {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) :
    PreservesProj proj (TimeRand.monoNowMs deps.timeRand) := by
  unfold TimeRand.monoNowMs
  refine preservesProj_bind (hDeps.timeRandClockGettime .monotonic) fun r => ?_
  cases r <;> exact preservesProj_pure _

/-- `TimeRand.checkTimedOut` preserves `proj`. -/
theorem preservesProj_checkTimedOut {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (startMs : Nat) (to? : Option Nat) :
    PreservesProj proj (TimeRand.checkTimedOut deps.timeRand startMs to?) := by
  unfold TimeRand.checkTimedOut
  cases to? with
  | none => exact preservesProj_pure _
  | some _ =>
    refine preservesProj_bind (preservesProj_monoNowMs hDeps) fun r => ?_
    cases r with
    | error _ => exact preservesProj_pure _
    | ok _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)

/-- `writeStdinStep` preserves `proj` and returns non-empty error messages on failure. -/
theorem writeStdinStep_spec {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (inFd : fd) (stdin : ByteArray) (startMs : Nat) (to? : Option Nat) :
    ∀ pos prog fuel,
      PreservesProj proj (writeStdinStep deps.files deps.timeRand inFd stdin startMs to? pos prog fuel) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        ∀ e, ((writeStdinStep deps.files deps.timeRand inFd stdin startMs to? pos prog fuel).run w).1 = .error e →
          e.message ≠ ""
  | pos, _, 0 => by
    unfold writeStdinStep
    constructor
    · exact preservesProj_ite
        (preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _))
        (preservesProj_pure _)
    · intro w _ e he
      by_cases hPos : pos ≥ stdin.size
      · simp only [hPos, ↓reduceIte, stateM_bind_run, stateM_pure_run] at he; cases he
      · simp only [hPos, ↓reduceIte, stateM_pure_run] at he; cases he
  | pos, prog, fuel + 1 => by
    unfold writeStdinStep
    constructor
    · refine preservesProj_ite
        (preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _)) ?_
      refine preservesProj_bind (preservesProj_checkTimedOut hDeps startMs to?) fun r => ?_
      cases r with
      | error _ => exact preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _)
      | ok pair =>
        rcases pair with ⟨b, rem⟩
        dsimp only
        cases b with
        | true => exact preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _)
        | false =>
          refine preservesProj_bind (hDeps.filesWrite inFd _) fun wr => ?_
          cases wr with
          | ok _ =>
            exact preservesProj_ite
              (preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _))
              (preservesProj_ite
                (preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _))
                (writeStdinStep_spec hDeps inFd stdin startMs to? _ true fuel).1)
          | error _ =>
            exact preservesProj_ite
              (writeStdinStep_spec hDeps inFd stdin startMs to? pos prog fuel).1
              (preservesProj_ite (preservesProj_pure _)
                (preservesProj_bind (preservesProj_closeOpt hDeps (some inFd)) (fun _ => preservesProj_pure _)))
    · intro w hWf e he
      by_cases hPos : pos ≥ stdin.size
      · simp only [hPos, ↓reduceIte, stateM_bind_run, stateM_pure_run] at he; cases he
      · simp only [hPos, ↓reduceIte, stateM_bind_run] at he
        have h1 := preservesProj_checkTimedOut hDeps startMs to? w hWf
        have hWf1 : rawHostWorldWf (proj ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).2) = true := by
          rw [h1]; exact hWf
        cases hTo : ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).1 with
        | error _ =>
          rw [hTo] at he
          simp only [stateM_bind_run, stateM_pure_run] at he
          cases he; exact mapRawError_ioError_ne_empty _ _
        | ok pair =>
          rw [hTo] at he
          rcases pair with ⟨b, rem⟩
          cases b with
          | true =>
            simp only [stateM_bind_run, stateM_pure_run] at he; cases he
          | false =>
            dsimp only at he
            simp only [stateM_bind_run] at he
            let w1 := ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).2
            let w2 := ((deps.files.write inFd (stdin.extract pos (Nat.min stdin.size (pos + STDIN_WRITE_CHUNK)))).run w1).2
            have h2 := hDeps.filesWrite inFd (stdin.extract pos (Nat.min stdin.size (pos + STDIN_WRITE_CHUNK))) w1 hWf1
            have hWf2 : rawHostWorldWf (proj w2) = true := by rw [h2]; exact hWf1
            cases hWr : ((deps.files.write inFd (stdin.extract pos (Nat.min stdin.size (pos + STDIN_WRITE_CHUNK)))).run w1).1 with
            | ok n =>
              rw [hWr] at he
              dsimp only at he
              cases hZ : (n == 0) with
              | true => simp only [hZ, ↓reduceIte, stateM_bind_run, stateM_pure_run] at he; cases he
              | false =>
                simp only [hZ, Bool.false_eq_true, ↓reduceIte] at he
                by_cases hDone : pos + n.toNat ≥ stdin.size
                · simp only [hDone, ↓reduceIte, stateM_bind_run, stateM_pure_run] at he; cases he
                · simp only [hDone, ↓reduceIte] at he
                  exact (writeStdinStep_spec hDeps inFd stdin startMs to? (pos + n.toNat) true fuel).2 _ hWf2 e he
            | error err =>
              rw [hWr] at he
              dsimp only at he
              cases hEi : (err == Errno.EINTR) with
              | true =>
                simp only [hEi, ↓reduceIte] at he
                exact (writeStdinStep_spec hDeps inFd stdin startMs to? pos prog fuel).2 _ hWf2 e he
              | false =>
                simp only [hEi, Bool.false_eq_true, ↓reduceIte] at he
                cases hEa : (err == Errno.EAGAIN) with
                | true => simp only [hEa, ↓reduceIte, stateM_pure_run] at he; cases he
                | false => simp only [hEa, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run] at he; cases he

/-- Loop invariant on `PipeStepResult`: tracks chunk-length sum and combined output cap `maxOut?`. -/
def PipeStepInv {fd : Type} (otherLen : Nat) (maxOut? : Option Nat) (r : PipeStepResult fd) : Prop :=
  match r with
  | .cont _ chunks len _ =>
    len = (chunks.toList.map ByteArray.size).sum ∧ (∀ m, maxOut? = some m → len + otherLen ≤ m)
  | .timedOut chunks len =>
    len = (chunks.toList.map ByteArray.size).sum ∧ (∀ m, maxOut? = some m → len + otherLen ≤ m)
  | .limitExceeded chunks len =>
    len = (chunks.toList.map ByteArray.size).sum ∧ (∀ m, maxOut? = some m → len + otherLen ≤ m)
  | .ioErr e => e.message ≠ ""

/-- `drainPipeStep` preserves `proj` and maintains `PipeStepInv`. -/
theorem drainPipeStep_spec {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (pipeFd : fd) (otherLen startMs : Nat) (to? maxOut? : Option Nat) :
    ∀ chunks curLen iterBytes prog fuel,
      curLen = (chunks.toList.map ByteArray.size).sum →
      (∀ m, maxOut? = some m → curLen + otherLen ≤ m) →
      PreservesProj proj (drainPipeStep deps.files deps.timeRand pipeFd otherLen startMs to? maxOut? chunks curLen iterBytes prog fuel) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        PipeStepInv otherLen maxOut? ((drainPipeStep deps.files deps.timeRand pipeFd otherLen startMs to? maxOut? chunks curLen iterBytes prog fuel).run w).1
  | _, _, _, _, 0, hSum, hBnd =>
    ⟨preservesProj_pure _, fun _ _ => ⟨hSum, hBnd⟩⟩
  | chunks, curLen, iterBytes, prog, fuel + 1, hSum, hBnd => by
    unfold drainPipeStep
    by_cases hFair : iterBytes ≥ STREAM_FAIRNESS_BYTES
    · simp only [hFair, ↓reduceIte]
      exact ⟨preservesProj_pure _, fun _ _ => ⟨hSum, hBnd⟩⟩
    · simp only [hFair, ↓reduceIte]
      have hTo := preservesProj_checkTimedOut hDeps startMs to?
      have hRd := hDeps.filesRead pipeFd PIPE_READ_CHUNK
      constructor
      · refine preservesProj_bind hTo fun r => ?_
        cases r with
        | error _ => exact preservesProj_bind (preservesProj_closeOpt hDeps (some pipeFd)) (fun _ => preservesProj_pure _)
        | ok pair =>
          rcases pair with ⟨b, rem⟩
          cases b with
          | true => exact preservesProj_bind (preservesProj_closeOpt hDeps (some pipeFd)) (fun _ => preservesProj_pure _)
          | false =>
            refine preservesProj_bind hRd fun rd => ?_
            cases rd with
            | error _ =>
              exact preservesProj_ite
                (drainPipeStep_spec hDeps pipeFd otherLen startMs to? maxOut? chunks curLen iterBytes prog fuel hSum hBnd).1
                (preservesProj_ite (preservesProj_pure _)
                  (preservesProj_bind (preservesProj_closeOpt hDeps (some pipeFd)) (fun _ => preservesProj_pure _)))
            | ok chunk =>
              refine preservesProj_ite
                (preservesProj_bind (preservesProj_closeOpt hDeps (some pipeFd)) (fun _ => preservesProj_pure _)) ?_
              cases maxOut? with
              | none =>
                have hSum' : curLen + chunk.size = ((chunks.push chunk).toList.map ByteArray.size).sum := by
                  simp [Array.toList_push, List.map_append, List.sum_append, hSum]
                exact (drainPipeStep_spec hDeps pipeFd otherLen startMs to? none (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel hSum' (fun _ h => by cases h)).1
              | some maxOut =>
                by_cases hGt : curLen + otherLen + chunk.size > maxOut
                · simp only [hGt, ↓reduceIte]
                  exact preservesProj_bind (preservesProj_closeOpt hDeps (some pipeFd)) (fun _ => preservesProj_pure _)
                · simp only [hGt, ↓reduceIte]
                  have hSum' : curLen + chunk.size = ((chunks.push chunk).toList.map ByteArray.size).sum := by
                    simp [Array.toList_push, List.map_append, List.sum_append, hSum]
                  have hBnd' : ∀ m, some maxOut = some m → curLen + chunk.size + otherLen ≤ m := by
                    intro m hm; cases hm; omega
                  exact (drainPipeStep_spec hDeps pipeFd otherLen startMs to? (some maxOut) (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel hSum' hBnd').1
      · intro w hWf
        simp only [stateM_bind_run]
        have h1 := hTo w hWf
        have hWf1 : rawHostWorldWf (proj ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).2) = true := by
          rw [h1]; exact hWf
        cases hTr : ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).1 with
        | error _ =>
          simp only [stateM_bind_run, stateM_pure_run, PipeStepInv]
          exact mapRawError_ioError_ne_empty _ _
        | ok pair =>
          rcases pair with ⟨b, rem⟩
          cases b with
          | true =>
            simp only [stateM_bind_run, stateM_pure_run, PipeStepInv]
            exact ⟨hSum, hBnd⟩
          | false =>
            dsimp only
            simp only [stateM_bind_run]
            let w1 := ((TimeRand.checkTimedOut deps.timeRand startMs to?).run w).2
            let w2 := ((deps.files.read pipeFd PIPE_READ_CHUNK).run w1).2
            have h2 := hRd w1 hWf1
            have hWf2 : rawHostWorldWf (proj w2) = true := by rw [h2]; exact hWf1
            cases hR : ((deps.files.read pipeFd PIPE_READ_CHUNK).run w1).1 with
            | error err =>
              dsimp only
              cases hEi : (err == Errno.EINTR) with
              | true =>
                simp only [↓reduceIte]
                exact (drainPipeStep_spec hDeps pipeFd otherLen startMs to? maxOut? chunks curLen iterBytes prog fuel hSum hBnd).2 _ hWf2
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases hEa : (err == Errno.EAGAIN) with
                | true =>
                  simp only [↓reduceIte, stateM_pure_run, PipeStepInv]
                  exact ⟨hSum, hBnd⟩
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run, PipeStepInv]
                  exact mapRawError_ioError_ne_empty _ _
            | ok chunk =>
              dsimp only
              cases hEof : (chunk.size == 0) with
              | true =>
                simp only [↓reduceIte, stateM_bind_run, stateM_pure_run, PipeStepInv]
                exact ⟨hSum, hBnd⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases maxOut? with
                | none =>
                  have hSum' : curLen + chunk.size = ((chunks.push chunk).toList.map ByteArray.size).sum := by
                    simp [Array.toList_push, List.map_append, List.sum_append, hSum]
                  exact (drainPipeStep_spec hDeps pipeFd otherLen startMs to? none (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel hSum' (fun _ h => by cases h)).2 _ hWf2
                | some maxOut =>
                  dsimp only
                  by_cases hGt : curLen + otherLen + chunk.size > maxOut
                  · simp only [hGt, ↓reduceIte, stateM_bind_run, stateM_pure_run, PipeStepInv]
                    by_cases hPos : maxOut - (curLen + otherLen) > 0
                    · simp only [hPos, ↓reduceIte]
                      refine ⟨by simp [Array.toList_push, List.map_append, List.sum_append, hSum], fun m hm => ?_⟩
                      cases hm
                      have hCurLe := hBnd maxOut rfl
                      have hExt := byteArray_extract_size_le chunk 0 (maxOut - (curLen + otherLen))
                      omega
                    · simp only [hPos, ↓reduceIte]
                      exact ⟨hSum, hBnd⟩
                  · simp only [hGt, ↓reduceIte]
                    have hSum' : curLen + chunk.size = ((chunks.push chunk).toList.map ByteArray.size).sum := by
                      simp [Array.toList_push, List.map_append, List.sum_append, hSum]
                    have hBnd' : ∀ m, some maxOut = some m → curLen + chunk.size + otherLen ≤ m := by
                      intro m hm; cases hm; omega
                    exact (drainPipeStep_spec hDeps pipeFd otherLen startMs to? (some maxOut) (chunks.push chunk) (curLen + chunk.size) (iterBytes + chunk.size) true fuel hSum' hBnd').2 _ hWf2

/-- Postcondition on `readBoxOutputCore`: non-negative outcome and `maxOut?` bound on `.ok`, non-empty message on `.error`. -/
def StreamResInv (maxOut? : Option Nat) (r : Except SandboxError SandboxResult) : Prop :=
  match r with
  | .ok res => outcomeNonNeg res.outcome ∧ (∀ m, maxOut? = some m → res.stdout.size + res.stderr.size ≤ m)
  | .error err => err.message ≠ ""

/-- `classifyBoxStreamResult` establishes `StreamResInv` from tracked chunk sums and combined cap. -/
theorem classify_streamResInv (program cwd : String) (to lim : Bool)
    (smsg? : Option InitStatusMsg) (outChunks errChunks : Array ByteArray) (outLen errLen : Nat)
    (maxOut? : Option Nat)
    (hOut : outLen = (outChunks.toList.map ByteArray.size).sum)
    (hErr : errLen = (errChunks.toList.map ByteArray.size).sum)
    (hBnd : ∀ m, maxOut? = some m → outLen + errLen ≤ m) :
    StreamResInv maxOut? (classifyBoxStreamResult program cwd to lim smsg?
      (concatChunks outChunks outLen) (concatChunks errChunks errLen)) := by
  have hCls := classifyBoxStreamResult_spec program cwd to lim smsg?
    (concatChunks outChunks outLen) (concatChunks errChunks errLen)
  unfold StreamResInv
  cases hR : classifyBoxStreamResult program cwd to lim smsg? (concatChunks outChunks outLen) (concatChunks errChunks errLen) with
  | error e => rw [hR] at hCls; exact hCls
  | ok res =>
    rw [hR] at hCls
    rcases hCls with ⟨ho, he, hnn⟩
    refine ⟨hnn, fun m hm => ?_⟩
    rw [ho, he, concatChunks_size, concatChunks_size, ← hOut, ← hErr]
    exact hBnd m hm

/-- `closeBoxStreamState` preserves `proj`. -/
theorem preservesProj_closeBoxStreamState {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (st : BoxStreamState fd) :
    PreservesProj proj (closeBoxStreamState deps.files st) := by
  unfold closeBoxStreamState
  exact preservesProj_bind (preservesProj_closeOpt hDeps st.inFd?) fun _ =>
    preservesProj_bind (preservesProj_closeOpt hDeps st.outFd?) fun _ =>
      preservesProj_bind (preservesProj_closeOpt hDeps st.errFd?) fun _ =>
        preservesProj_closeOpt hDeps st.statusFd?

end LeanSwe.ProcessSandbox.Raw.Proofs

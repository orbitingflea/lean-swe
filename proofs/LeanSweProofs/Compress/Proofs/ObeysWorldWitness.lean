import Core.Obeys
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSweProofs.Compress.Model.Refines
import LeanSweProofs.Compress.Proofs.SharedHelpers
import LeanSweProofs.Compress.Proofs.ObeysProcess

/-!
Standalone pure `ProcessApiM (StateM Model.CompressWorld)` capability witness (`worldProcessApi`)
proving `Model.allowedWorldProcessStep` is inhabited and non-vacuous
(`worldProcessApi_obeys_allowedWorldProcessStep`).
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

private theorem byteArray_get!_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have h1 : i < a.data.size := hi
  have h2 : i < (a ++ b).data.size := by
    simp [ByteArray.data_append, Array.size_append]
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  change (a ++ b).data[i]! = a.data[i]!
  rw [getElem!_pos (a ++ b).data i h2, getElem!_pos a.data i h1]
  simp [ByteArray.data_append, Array.getElem_append_left h1]

private theorem byteArray_extract_suffix (a b : ByteArray) :
    (a ++ b).extract a.size (a ++ b).size = b := by
  rw [ByteArray.size_append]
  exact ByteArray.extract_append_eq_right rfl rfl

private theorem mkSimFrame_size_le_bound (codec : Codec) (input : ByteArray) :
    (Model.mkSimFrame codec input).size ≤ Model.maxCompressedBound codec input.size := by
  unfold Model.mkSimFrame Model.maxCompressedBound
  cases codec with
  | gzip =>
    have h : Model.simGzipPrefix.size = 20 := rfl
    simp only [ByteArray.size_append, h]; omega
  | zstd =>
    have h : Model.simZstdPrefix.size = 9 := rfl
    simp only [ByteArray.size_append, h]; omega
  | xz =>
    have h1 : Model.simXzPrefix.size = 30 := rfl
    have h2 : Model.simXzSuffix.size = 2 := rfl
    simp only [ByteArray.size_append, h1, h2]; omega

private theorem mkSimFrame_canonicalFraming (codec : Codec) (input : ByteArray) :
    Model.hasCanonicalCompressedFraming codec (Model.mkSimFrame codec input) = true := by
  unfold Model.hasCanonicalCompressedFraming Model.mkSimFrame
  cases codec with
  | gzip =>
    have hp : Model.simGzipPrefix.size = 20 := rfl
    have hSz : (Model.simGzipPrefix ++ input).size ≥ 20 := by simp [ByteArray.size_append, hp]
    have hg (i : Nat) (hi : i < 20) : (Model.simGzipPrefix ++ input).get! i = Model.simGzipPrefix.get! i :=
      byteArray_get!_append_left (by rw [hp]; exact hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hSz, hg 0 (by omega)⟩, hg 1 (by omega)⟩, hg 2 (by omega)⟩,
      hg 3 (by omega)⟩, hg 4 (by omega)⟩, hg 5 (by omega)⟩, hg 6 (by omega)⟩, hg 7 (by omega)⟩
  | zstd =>
    have hp : Model.simZstdPrefix.size = 9 := rfl
    have hSz : (Model.simZstdPrefix ++ input).size ≥ 9 := by simp [ByteArray.size_append, hp]
    have hg (i : Nat) (hi : i < 9) : (Model.simZstdPrefix ++ input).get! i = Model.simZstdPrefix.get! i :=
      byteArray_get!_append_left (by rw [hp]; exact hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨hSz, hg 0 (by omega)⟩, hg 1 (by omega)⟩, hg 2 (by omega)⟩, hg 3 (by omega)⟩
  | xz =>
    have hp1 : Model.simXzPrefix.size = 30 := rfl
    have hp2 : Model.simXzSuffix.size = 2 := rfl
    have hSplit : Model.simXzPrefix =
        ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++
        ByteArray.mk #[0x4C, 0x53, 0x49, 0x4D, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
    have hSz : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).size ≥ 32 := by
      simp only [ByteArray.size_append, hp1, hp2]; omega
    have hPfx : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract 0 6 =
        ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] := by
      rw [hSplit]
      simp only [ByteArray.append_assoc]
      exact ByteArray.extract_append_eq_left rfl
    have hSfxSz : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).size - 2 =
        (Model.simXzPrefix ++ input).size := by
      simp only [ByteArray.size_append, hp2]; omega
    have hSfx : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract
        ((Model.simXzPrefix ++ input ++ Model.simXzSuffix).size - 2)
        (Model.simXzPrefix ++ input ++ Model.simXzSuffix).size =
        ByteArray.mk #[0x59, 0x5A] := by
      rw [hSfxSz]
      exact byteArray_extract_suffix (Model.simXzPrefix ++ input) Model.simXzSuffix
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨hSz, hPfx⟩, hSfx⟩

private theorem decodeSimFrame_mkSimFrame (codec : Codec) (input : ByteArray) :
    Model.decodeSimFrame? codec (Model.mkSimFrame codec input) = some input := by
  unfold Model.decodeSimFrame? Model.mkSimFrame
  cases codec with
  | gzip =>
    have hp : Model.simGzipPrefix.size = 20 := rfl
    have hSz : decide ((Model.simGzipPrefix ++ input).size ≥ 20) = true :=
      decide_eq_true (by simp [ByteArray.size_append, hp])
    have hL : (Model.simGzipPrefix ++ input).extract 0 20 = Model.simGzipPrefix := by
      change (Model.simGzipPrefix ++ input).extract 0 Model.simGzipPrefix.size = Model.simGzipPrefix
      exact ByteArray.extract_append_eq_left rfl
    have hR : (Model.simGzipPrefix ++ input).extract 20 (Model.simGzipPrefix ++ input).size = input :=
      byteArray_extract_suffix Model.simGzipPrefix input
    dsimp only
    rw [hSz, hL, hR]
    have hEqP : (Model.simGzipPrefix == Model.simGzipPrefix) = true := by decide
    rw [hEqP]
    rfl
  | zstd =>
    have hp : Model.simZstdPrefix.size = 9 := rfl
    have hSz : decide ((Model.simZstdPrefix ++ input).size ≥ 9) = true :=
      decide_eq_true (by simp [ByteArray.size_append, hp])
    have hL : (Model.simZstdPrefix ++ input).extract 0 9 = Model.simZstdPrefix := by
      change (Model.simZstdPrefix ++ input).extract 0 Model.simZstdPrefix.size = Model.simZstdPrefix
      exact ByteArray.extract_append_eq_left rfl
    have hR : (Model.simZstdPrefix ++ input).extract 9 (Model.simZstdPrefix ++ input).size = input :=
      byteArray_extract_suffix Model.simZstdPrefix input
    dsimp only
    rw [hSz, hL, hR]
    have hEqP : (Model.simZstdPrefix == Model.simZstdPrefix) = true := by decide
    rw [hEqP]
    rfl
  | xz =>
    have hp1 : Model.simXzPrefix.size = 30 := rfl
    have hp2 : Model.simXzSuffix.size = 2 := rfl
    have hSz : decide ((Model.simXzPrefix ++ input ++ Model.simXzSuffix).size ≥ 32) = true :=
      decide_eq_true (by simp only [ByteArray.size_append, hp1, hp2]; omega)
    have hL : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract 0 30 = Model.simXzPrefix := by
      rw [ByteArray.append_assoc]
      change (Model.simXzPrefix ++ (input ++ Model.simXzSuffix)).extract 0 Model.simXzPrefix.size = Model.simXzPrefix
      exact ByteArray.extract_append_eq_left rfl
    have hSfxPos : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).size - 2 =
        (Model.simXzPrefix ++ input).size := by
      simp only [ByteArray.size_append, hp2]; omega
    have hR : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract
        ((Model.simXzPrefix ++ input ++ Model.simXzSuffix).size - 2)
        (Model.simXzPrefix ++ input ++ Model.simXzSuffix).size = Model.simXzSuffix := by
      rw [hSfxPos]
      exact byteArray_extract_suffix (Model.simXzPrefix ++ input) Model.simXzSuffix
    have hMid : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract 30
        ((Model.simXzPrefix ++ input ++ Model.simXzSuffix).size - 2) = input := by
      rw [hSfxPos]
      have h1 : (Model.simXzPrefix ++ input ++ Model.simXzSuffix).extract 30 (Model.simXzPrefix ++ input).size =
          (Model.simXzPrefix ++ input).extract 30 (Model.simXzPrefix ++ input).size := by
        have hSub : ((Model.simXzPrefix ++ input) ++ Model.simXzSuffix).extract 0 (Model.simXzPrefix ++ input).size =
            Model.simXzPrefix ++ input := ByteArray.extract_append_eq_left rfl
        have hEx := congrArg (fun b : ByteArray => b.extract 30 (Model.simXzPrefix ++ input).size) hSub
        rw [ByteArray.extract_extract] at hEx
        have hMin : min (Model.simXzPrefix ++ input).size (0 + (Model.simXzPrefix ++ input).size) =
            (Model.simXzPrefix ++ input).size := by omega
        simpa [Nat.zero_add, hMin] using hEx
      rw [h1]
      exact byteArray_extract_suffix Model.simXzPrefix input
    dsimp only
    rw [hSz, hL, hR, hMid]
    have hEq1 : (Model.simXzPrefix == Model.simXzPrefix) = true := by decide
    have hEq2 : (Model.simXzSuffix == Model.simXzSuffix) = true := by decide
    rw [hEq1, hEq2]
    rfl

private theorem mkSimFrame_ConsistentEntry (codec : Codec) (input : ByteArray) :
    Model.isConsistentKnownEntry ((codec, Model.mkSimFrame codec input), input) = true := by
  unfold Model.isConsistentKnownEntry
  dsimp only
  rw [decodeSimFrame_mkSimFrame]
  dsimp only
  have hEq : (input == input) = true := by simp
  rw [hEq, Bool.and_true]
  cases codec with
  | zstd | xz => rfl
  | gzip =>
    change (false || Model.hasGzipHeader (Model.simGzipPrefix ++ input)) = true
    rw [Bool.false_or]
    have hCan := mkSimFrame_canonicalFraming .gzip input
    unfold Model.hasCanonicalCompressedFraming Model.mkSimFrame at hCan
    unfold Model.hasGzipHeader
    simp only [Bool.and_eq_true] at hCan ⊢
    exact ⟨⟨⟨hCan.1.1.1.1.1.1.1.1, hCan.1.1.1.1.1.1.1.2⟩, hCan.1.1.1.1.1.1.2⟩, hCan.1.1.1.1.1.2⟩

private theorem lookup_mem_of_some {st : Model.State} {codec : Codec} {comp prev : ByteArray}
    (h : st.lookup codec comp = some prev) :
    ∃ e ∈ st.known, e.1.1 = codec ∧ e.1.2 = comp ∧ e.2 = prev := by
  unfold Model.State.lookup at h
  cases hf : st.known.find? (fun entry => entry.1.1 == codec && entry.1.2 == comp) with
  | none => simp [hf] at h
  | some entry =>
    simp only [hf, Option.some.injEq] at h
    have hMem := List.mem_of_find?_eq_some hf
    have hPred := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hPred
    have hcEq : entry.1.1 = codec := by
      cases h1 : entry.1.1 <;> cases codec <;> rw [h1] at hPred <;>
        first | rfl | exact absurd hPred.1 (by decide)
    exact ⟨entry, hMem, hcEq, hPred.2, h⟩

private theorem lookup_mkSimFrame_consistent {st : Model.State}
    (hAll : st.known.all Model.isConsistentKnownEntry = true)
    (codec : Codec) (input prev : ByteArray)
    (hLk : st.lookup codec (Model.mkSimFrame codec input) = some prev) :
    (prev == input) = true := by
  rcases lookup_mem_of_some hLk with ⟨e, hMem, hC, hComp, hPrev⟩
  have hCon := (List.all_eq_true.mp hAll) e hMem
  unfold Model.isConsistentKnownEntry at hCon
  rcases (Bool.and_eq_true _ _).mp hCon with ⟨_, hDec⟩
  rw [hC, hComp, decodeSimFrame_mkSimFrame, hPrev] at hDec
  rw [beq_iff_eq] at hDec ⊢
  exact hDec.symm

private theorem lookup_gzip_consistent {st : Model.State}
    (hAll : st.known.all Model.isConsistentKnownEntry = true)
    (codec : Codec) (comp prev : ByteArray)
    (hLk : st.lookup codec comp = some prev) :
    (codec != .gzip || Model.hasGzipHeader comp) = true := by
  rcases lookup_mem_of_some hLk with ⟨e, hMem, hC, hComp, _⟩
  have hCon := (List.all_eq_true.mp hAll) e hMem
  unfold Model.isConsistentKnownEntry at hCon
  rcases (Bool.and_eq_true _ _).mp hCon with ⟨hGh, _⟩
  rwa [hC, hComp] at hGh

private theorem record_preserves_all_consistent {st : Model.State} {codec : Codec} {comp plain : ByteArray}
    (hAll : st.known.all Model.isConsistentKnownEntry = true)
    (hEntry : Model.isConsistentKnownEntry ((codec, comp), plain) = true) :
    (st.record codec comp plain).known.all Model.isConsistentKnownEntry = true := by
  unfold Model.State.record
  cases st.lookup codec comp with
  | some _ => exact hAll
  | none =>
    simp [List.all_cons, hEntry, hAll]

private def envToolProcessError (prog : String) : Model.ToolEnvStatus → Option ProcessError
  | .available => none
  | .missingOrNonExec => some { kind := .notFound, program := some prog, message := "tool not found" }
  | .pathSymlinkLoop => some { kind := .invalidInput, program := some prog, message := "symlink loop" }
  | .pathOrPipeIoError => some { kind := .ioError, program := some prog, message := "io error" }

private def fitsMaxOut (maxOutputBytes? : Option Nat) (sz : Nat) : Bool :=
  match maxOutputBytes? with
  | none => true
  | some lim => decide (sz ≤ lim)

private def simWorldRun (req : ExecRequest) (w : Model.CompressWorld) :
    Except ProcessError ExecResult × Model.CompressWorld :=
  match LeanSwe.Process.Model.validateRequestModel req with
  | .error verr => (.error verr, w)
  | .ok _ =>
    match Model.classifyCodecExecRequest? req with
    | none => (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, w)
    | some (.version codec) =>
      match envToolProcessError req.program (w.env.toolStatus codec) with
      | some pe => (.error pe, w)
      | none => (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, w)
    | some (.compress codec maxOut input) =>
      match envToolProcessError req.program (w.env.toolStatus codec) with
      | some pe => (.error pe, w)
      | none =>
        let frame := Model.mkSimFrame codec input
        if fitsMaxOut req.maxOutputBytes frame.size then
          let w' :=
            if frame.size ≤ maxOut then
              { w with codecState := w.codecState.record codec frame input }
            else
              w
          (.ok { exitCode := 0, stdout := frame, stderr := ByteArray.empty }, w')
        else
          (.error { kind := .outputLimitExceeded, program := some req.program, message := "output limit exceeded" }, w)
    | some (.decompress codec _maxOut input) =>
      match envToolProcessError req.program (w.env.toolStatus codec) with
      | some pe => (.error pe, w)
      | none =>
        match w.codecState.lookup codec input with
        | none => (.ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }, w)
        | some expected =>
          if fitsMaxOut req.maxOutputBytes expected.size then
            (.ok { exitCode := 0, stdout := expected, stderr := ByteArray.empty }, w)
          else
            (.error { kind := .outputLimitExceeded, program := some req.program, message := "output limit exceeded" }, w)

/-- Pure `ProcessApiM (StateM CompressWorld)` capability witness inhabiting `Model.allowedWorldProcessStep`. -/
def worldProcessApi : ProcessApiM (StateM Model.CompressWorld) :=
  let liftProc {α : Type} (act : StateM LeanSwe.Process.Model.ProcessModelState α) :
      StateM Model.CompressWorld α :=
    fun w =>
      let (a, p') := act.run w.proc
      (a, { w with proc := p' })
  { mapRawError := LeanSwe.Process.Model.mapRawErrorModel
    validateRequest := LeanSwe.Process.Model.validateRequestModel
    mkCommandRequest := LeanSwe.Process.Model.mkCommandRequestModel
    withTextInput := LeanSwe.Process.Model.withTextInputModel
    spawn := fun r => liftProc (modelProcessApi.spawn r)
    awaitOutput := fun h stdin t m => liftProc (modelProcessApi.awaitOutput h stdin t m)
    killProcessGroup := fun h => liftProc (modelProcessApi.killProcessGroup h)
    reap := fun h => liftProc (modelProcessApi.reap h)
    run := simWorldRun
    runChecked := fun r => liftProc (modelProcessApi.runChecked r)
    runCommand := fun prog args => liftProc (modelProcessApi.runCommand prog args)
    runCommandChecked := fun prog args => liftProc (modelProcessApi.runCommandChecked prog args)
    activeProcessCount := liftProc modelProcessApi.activeProcessCount }

@[simp] private theorem toolStatus_beq_self (t : Model.ToolEnvStatus) : (t == t) = true := by
  cases t <;> rfl

private theorem classifyCodec_maxOut_some {req : ExecRequest} {k : Model.CodecExecKind}
    (h : Model.classifyCodecExecRequest? req = some k) :
    (∀ c m i, k = .compress c m i → ∃ lim, req.maxOutputBytes = some lim ∧ lim ≥ 4096 ∧ m = lim - 4096) ∧
    (∀ c m i, k = .decompress c m i → ∃ lim, req.maxOutputBytes = some lim ∧ lim ≥ 4096 ∧ m = lim - 4096) := by
  unfold Model.classifyCodecExecRequest? at h
  cases hp : Model.parseCodecProgram? req.program with
  | none => rw [hp] at h; cases h
  | some c0 =>
    rw [hp] at h
    change (if req.args == #["--version"] then some (.version c0) else
      match req.args[0]?, req.maxOutputBytes with
      | some "-c", some lim => if lim ≥ 4096 then some (.compress c0 (lim - 4096) req.stdin) else none
      | some "-d", some lim => if lim ≥ 4096 then some (.decompress c0 (lim - 4096) req.stdin) else none
      | _, _ => none) = some k at h
    split at h
    · injection h with hk; subst hk
      exact ⟨(fun _ _ _ hc => nomatch hc), (fun _ _ _ hd => nomatch hd)⟩
    · split at h
      · next _ lim _ hLim =>
        split at h
        · next hge =>
          injection h with hk; subst hk
          exact ⟨(fun _ _ _ heq => by injection heq with _ hm _; exact ⟨lim, hLim, hge, hm.symm⟩),
            (fun _ _ _ hd => nomatch hd)⟩
        · cases h
      · next _ lim _ hLim =>
        split at h
        · next hge =>
          injection h with hk; subst hk
          exact ⟨(fun _ _ _ hc => nomatch hc),
            (fun _ _ _ heq => by injection heq with _ hm _; exact ⟨lim, hLim, hge, hm.symm⟩)⟩
        · cases h
      · cases h

private theorem emptyOk_allowedExecResult (code : Int) (req : ExecRequest) :
    LeanSwe.Process.Model.allowedExecResult false req
      (.ok { exitCode := code, stdout := ByteArray.empty, stderr := ByteArray.empty }) := by
  refine ⟨(fun h => nomatch h), fun lim _ => ?_⟩
  change 0 ≤ lim
  exact Nat.zero_le lim

private theorem envToolErr_allowedExecResult (req : ExecRequest) (pe : ProcessError)
    (ts : Model.ToolEnvStatus) (h : envToolProcessError req.program ts = some pe) :
    LeanSwe.Process.Model.allowedExecResult false req (.error pe) := by
  cases ts with
  | available => cases h
  | missingOrNonExec | pathSymlinkLoop | pathOrPipeIoError =>
    simp only [envToolProcessError, Option.some.injEq] at h
    subst h
    unfold LeanSwe.Process.Model.allowedExecResult
    dsimp only
    exact ⟨by decide, (fun hk => nomatch hk), (fun hk => nomatch hk),
      (fun hk => nomatch hk), (fun hk => nomatch hk)⟩

private theorem outLimitErr_allowedExecResult (req : ExecRequest) (lim : Nat)
    (hLim : req.maxOutputBytes = some lim) :
    LeanSwe.Process.Model.allowedExecResult false req
      (.error { kind := .outputLimitExceeded, program := some req.program, message := "output limit exceeded" }) := by
  unfold LeanSwe.Process.Model.allowedExecResult
  dsimp only
  refine ⟨by decide, (fun hk => nomatch hk), ?_, (fun hk => nomatch hk), (fun hk => nomatch hk)⟩
  intro _
  refine ⟨by rw [hLim]; rfl, rfl, fun l _ => ?_⟩
  change 0 ≤ l
  exact Nat.zero_le l

private theorem envToolErr_isNone_iff {prog : String} {ts : Model.ToolEnvStatus} :
    envToolProcessError prog ts = none ↔ ts = .available := by
  cases ts <;> simp [envToolProcessError]

private theorem envToolErr_version_conforms (env : Model.CompressEnv) (codec : Codec)
    (prog : String) (pe : ProcessError)
    (hPe : envToolProcessError prog (env.toolStatus codec) = some pe) :
    Model.rawVersionOutcomeConforms env codec (.error pe) = true := by
  unfold Model.rawVersionOutcomeConforms
  cases hTs : env.toolStatus codec with
  | available => rw [hTs] at hPe; cases hPe
  | missingOrNonExec | pathSymlinkLoop | pathOrPipeIoError => rfl

private theorem envToolErr_compress_conforms (env : Model.CompressEnv) (st : Model.State)
    (codec : Codec) (maxOut : Nat) (input : ByteArray) (prog : String) (pe : ProcessError)
    (hPe : envToolProcessError prog (env.toolStatus codec) = some pe) :
    Model.rawCompressOutcomeConforms env st codec maxOut input (.error pe) = true := by
  cases hTs : env.toolStatus codec with
  | available => rw [hTs] at hPe; cases hPe
  | missingOrNonExec | pathSymlinkLoop | pathOrPipeIoError =>
    rw [hTs] at hPe
    simp only [envToolProcessError, Option.some.injEq] at hPe
    subst hPe
    unfold Model.rawCompressOutcomeConforms Model.isResourceProcessErrorModel
    rw [hTs]
    dsimp only
    try simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    try simp only [show (Model.ToolEnvStatus.pathOrPipeIoError == .pathOrPipeIoError) = true from rfl, Bool.true_or]
    decide

private theorem envToolErr_decompress_conforms (env : Model.CompressEnv) (st : Model.State)
    (codec : Codec) (maxOut : Nat) (input : ByteArray) (prog : String) (pe : ProcessError)
    (hPe : envToolProcessError prog (env.toolStatus codec) = some pe) :
    Model.rawDecompressOutcomeConforms env st codec maxOut input (.error pe) = true := by
  cases hTs : env.toolStatus codec with
  | available => rw [hTs] at hPe; cases hPe
  | missingOrNonExec | pathSymlinkLoop | pathOrPipeIoError =>
    rw [hTs] at hPe
    simp only [envToolProcessError, Option.some.injEq] at hPe
    subst hPe
    unfold Model.rawDecompressOutcomeConforms Model.isResourceProcessErrorModel
    rw [hTs]
    dsimp only
    try simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    try simp only [show (Model.ToolEnvStatus.pathOrPipeIoError == .pathOrPipeIoError) = true from rfl, Bool.true_or]
    decide

/-- Non-vacuity theorem showing `worldProcessApi` obeys `Model.allowedWorldProcessStep`. -/
theorem worldProcessApi_obeys_allowedWorldProcessStep :
    Core.ObeysStep id Model.worldStepWf (Model.execProcessStep worldProcessApi) Model.allowedWorldProcessStep := by
  intro w req hWf
  have hWfBoth := (Bool.and_eq_true _ _).mp hWf
  have hProcWf : LeanSwe.Process.Model.processStateWf w.proc = true := hWfBoth.1
  have hKnownWf : w.codecState.known.all Model.isConsistentKnownEntry = true := hWfBoth.2
  have hBase := modelProcessApi_obeys_allowedProcessStep w.proc req hProcWf
  cases req with
  | spawn r =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | awaitOutput h stdin t m =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | killProcessGroup h =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | reap h =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | runChecked r =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | runCommand prog args =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | runCommandChecked prog args =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | activeProcessCount =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, worldProcessApi, Model.allowedWorldProcessStep, id] at hBase ⊢
    rw [stateT_map_run] at hBase ⊢; exact ⟨hWf, Bool.and_eq_true _ _ |>.mpr ⟨hBase.2.1, hKnownWf⟩, hBase, rfl, rfl⟩
  | run execReq =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      worldProcessApi, Model.allowedWorldProcessStep,
      LeanSwe.Process.Model.allowedPkgStep, LeanSwe.Process.Model.allowedPkgRun, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, simWorldRun]
    cases hVal : LeanSwe.Process.Model.validateRequestModel execReq with
    | error verr =>
      dsimp only
      exact ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, rfl⟩, rfl, rfl⟩
    | ok norm =>
      dsimp only
      cases hCls : Model.classifyCodecExecRequest? execReq with
      | none =>
        dsimp only
        exact ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, emptyOk_allowedExecResult 0 execReq⟩, rfl, rfl⟩
      | some k =>
        have hLimSpec := classifyCodec_maxOut_some hCls
        cases k with
        | version codec =>
          dsimp only
          cases hPe : envToolProcessError execReq.program (w.env.toolStatus codec) with
          | some pe =>
            dsimp only
            exact ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, envToolErr_allowedExecResult execReq pe _ hPe⟩,
              rfl, envToolErr_version_conforms w.env codec execReq.program pe hPe, rfl⟩
          | none =>
            have hTs : w.env.toolStatus codec = .available := envToolErr_isNone_iff.mp hPe
            dsimp only
            refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, emptyOk_allowedExecResult 0 execReq⟩, rfl, ?_, rfl⟩
            simp [Model.rawVersionOutcomeConforms, hTs]
        | compress codec maxOut input =>
          rcases hLimSpec.1 codec maxOut input rfl with ⟨lim, hLimEq, hLimGe, hMaxEq⟩
          dsimp only
          cases hPe : envToolProcessError execReq.program (w.env.toolStatus codec) with
          | some pe =>
            dsimp only
            exact ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, envToolErr_allowedExecResult execReq pe _ hPe⟩,
              rfl, envToolErr_compress_conforms w.env w.codecState codec maxOut input execReq.program pe hPe, rfl⟩
          | none =>
            have hTs : w.env.toolStatus codec = .available := envToolErr_isNone_iff.mp hPe
            dsimp only
            generalize hFr : Model.mkSimFrame codec input = frame
            have hBnd : frame.size ≤ Model.maxCompressedBound codec input.size := hFr ▸ mkSimFrame_size_le_bound codec input
            have hCan : Model.hasCanonicalCompressedFraming codec frame = true := hFr ▸ mkSimFrame_canonicalFraming codec input
            have hConE : Model.isConsistentKnownEntry ((codec, frame), input) = true := hFr ▸ mkSimFrame_ConsistentEntry codec input
            have hFitsEq : fitsMaxOut execReq.maxOutputBytes frame.size = decide (frame.size ≤ lim) := by
              simp [fitsMaxOut, hLimEq]
            by_cases hFit : frame.size ≤ lim
            · rw [hFitsEq, decide_eq_true hFit, ite_eq_left rfl]
              have hExecOk : LeanSwe.Process.Model.allowedExecResult false execReq
                  (.ok { exitCode := 0, stdout := frame, stderr := ByteArray.empty }) := by
                refine ⟨(fun h => nomatch h), fun l hl => ?_⟩
                rw [hLimEq] at hl; injection hl with hlEq; subst hlEq
                exact hFit
              by_cases hLeM : frame.size ≤ maxOut
              · have hNgt : ¬ (frame.size > maxOut) := by omega
                have hNewWf : Model.worldStepWf
                    { w with codecState := w.codecState.record codec frame input } = true :=
                  Bool.and_eq_true _ _ |>.mpr ⟨hProcWf, record_preserves_all_consistent hKnownWf hConE⟩
                have hLkOk : (match w.codecState.lookup codec frame with
                    | some prev => prev == input
                    | none => true) = true := by
                  cases hLk : w.codecState.lookup codec frame with
                  | none => rfl
                  | some prev => exact lookup_mkSimFrame_consistent hKnownWf codec input prev (hFr.symm ▸ hLk)
                rw [ite_eq_left hLeM]
                refine ⟨hWf, hNewWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, hExecOk⟩, rfl, ?_, ?_⟩
                · simp only [Model.rawCompressOutcomeConforms, hTs, toolStatus_beq_self, hNgt,
                     ↓reduceIte, hCan, Bool.true_and]
                  exact hLkOk
                · simp [hLeM]
              · have hGtM : frame.size > maxOut := by omega
                have hLtBnd : maxOut < Model.maxCompressedBound codec input.size := by omega
                rw [ite_eq_right hLeM]
                refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, hExecOk⟩, rfl, ?_, ?_⟩
                · simp [Model.rawCompressOutcomeConforms, hTs, hGtM, hLtBnd]
                · simp [hLeM]
            · have hLtBnd : maxOut < Model.maxCompressedBound codec input.size := by omega
              rw [hFitsEq, decide_eq_false hFit, ite_eq_right Bool.false_ne_true]
              refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, outLimitErr_allowedExecResult execReq lim hLimEq⟩,
                rfl, ?_, rfl⟩
              unfold Model.rawCompressOutcomeConforms
              rw [hTs]
              have hMsgNe : (!("output limit exceeded").isEmpty) = true := by decide
              simp only [hMsgNe, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨rfl, hLtBnd⟩
        | decompress codec maxOut input =>
          rcases hLimSpec.2 codec maxOut input rfl with ⟨lim, hLimEq, hLimGe, hMaxEq⟩
          dsimp only
          cases hPe : envToolProcessError execReq.program (w.env.toolStatus codec) with
          | some pe =>
            dsimp only
            exact ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, envToolErr_allowedExecResult execReq pe _ hPe⟩,
              rfl, envToolErr_decompress_conforms w.env w.codecState codec maxOut input execReq.program pe hPe, rfl⟩
          | none =>
            have hTs : w.env.toolStatus codec = .available := envToolErr_isNone_iff.mp hPe
            dsimp only
            cases hLk : w.codecState.lookup codec input with
            | none =>
              dsimp only
              refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, emptyOk_allowedExecResult 1 execReq⟩, rfl, ?_, ?_⟩
              · simp [Model.rawDecompressOutcomeConforms, hTs, hLk]
              · simp
            | some expected =>
              dsimp only
              have hGhOk := lookup_gzip_consistent hKnownWf codec input expected hLk
              have hFitsEq : fitsMaxOut execReq.maxOutputBytes expected.size = decide (expected.size ≤ lim) := by
                simp [fitsMaxOut, hLimEq]
              by_cases hFit : expected.size ≤ lim
              · rw [hFitsEq, decide_eq_true hFit, ite_eq_left rfl]
                have hExecOk : LeanSwe.Process.Model.allowedExecResult false execReq
                    (.ok { exitCode := 0, stdout := expected, stderr := ByteArray.empty }) := by
                  refine ⟨(fun h => nomatch h), fun l hl => ?_⟩
                  rw [hLimEq] at hl; injection hl with hlEq; subst hlEq
                  exact hFit
                by_cases hGtM : expected.size > maxOut
                · refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, hExecOk⟩, rfl, ?_, ?_⟩
                  · simp [Model.rawDecompressOutcomeConforms, hTs, hLk, hGtM, hGhOk]
                  · have hNle : ¬ (expected.size ≤ maxOut) := by omega
                    simp [hNle]
                · have hLeM : expected.size ≤ maxOut := by omega
                  have hRecIdem : w.codecState.record codec input expected = w.codecState := by
                    unfold Model.State.record; rw [hLk]
                  refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, hExecOk⟩, rfl, ?_, ?_⟩
                  · simp [Model.rawDecompressOutcomeConforms, hTs, hLk, hGtM, hLeM, hGhOk]
                  · simp [hLeM, hGhOk, hRecIdem]
              · have hGtM : expected.size > maxOut := by omega
                rw [hFitsEq, decide_eq_false hFit, ite_eq_right Bool.false_ne_true]
                refine ⟨hWf, hWf, ⟨hProcWf, hProcWf, rfl, Or.inl rfl, outLimitErr_allowedExecResult execReq lim hLimEq⟩,
                  rfl, ?_, rfl⟩
                unfold Model.rawDecompressOutcomeConforms
                rw [hTs, hLk]
                have hMsgNe : (!("output limit exceeded").isEmpty) = true := by decide
                simp only [hMsgNe, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨rfl, hGtM, hGhOk⟩

end LeanSwe.Compress.Proofs

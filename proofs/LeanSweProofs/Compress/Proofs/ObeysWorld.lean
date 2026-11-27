import Core.Obeys
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSweProofs.Compress.Model.Refines
import LeanSwe.Compress.Impl
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers
import LeanSweProofs.Compress.Proofs.BridgeProofs
import LeanSweProofs.Compress.Proofs.ObeysProcess

/-!
Compositional `Core.ObeysStepFrom` proof for `LeanSwe.Compress.Internal.mkApiM` over
`Model.CompressWorld` (`obeysStepFrom_world`).
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

private theorem parseCodecProgram_codecProgram (codec : Codec) :
    Model.parseCodecProgram? (Internal.codecProgram codec) = some codec := by
  cases codec <;> rfl

private theorem mkCompressArgs_get0 (codec : Codec) (opts : CompressOptions) :
    (Internal.mkCompressArgs codec opts)[0]? = some "-c" := by
  unfold Internal.mkCompressArgs
  cases codec <;> cases opts.level <;> cases opts.threads <;> rfl

private theorem mkCompressArgs_ne_version (codec : Codec) (opts : CompressOptions) :
    (Internal.mkCompressArgs codec opts == #["--version"]) = false := by
  cases h : (Internal.mkCompressArgs codec opts == #["--version"]) with
  | false => rfl
  | true =>
    have hEq : Internal.mkCompressArgs codec opts = #["--version"] := beq_iff_eq.mp h
    have h0 := mkCompressArgs_get0 codec opts
    rw [hEq] at h0
    injection h0 with hc
    exact absurd hc (by decide)

/-- `Model.classifyCodecExecRequest?` decodes `Internal.mkCompressRequest` to `.compress`. -/
theorem classifyCodecExecRequest_mkCompressRequest (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) :
    Model.classifyCodecExecRequest? (Internal.mkCompressRequest codec opts input) =
      some (.compress codec opts.maxOutputBytes input) := by
  unfold Model.classifyCodecExecRequest? Internal.mkCompressRequest Internal.stderrPipeSlack
  dsimp only
  rw [parseCodecProgram_codecProgram, mkCompressArgs_ne_version, mkCompressArgs_get0]
  have hGe : opts.maxOutputBytes + 4096 ≥ 4096 := Nat.le_add_left _ _
  simp [hGe]

/-- `Model.classifyCodecExecRequest?` decodes `Internal.mkDecompressRequest` to `.decompress`. -/
theorem classifyCodecExecRequest_mkDecompressRequest (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) :
    Model.classifyCodecExecRequest? (Internal.mkDecompressRequest codec opts input) =
      some (.decompress codec opts.maxOutputBytes input) := by
  unfold Model.classifyCodecExecRequest? Internal.mkDecompressRequest Internal.stderrPipeSlack
  have hGe : opts.maxOutputBytes + 4096 ≥ 4096 := Nat.le_add_left _ _
  cases codec <;> simp [Model.parseCodecProgram?, Internal.codecProgram,
    Internal.mkDecompressArgs, hGe]

/-- `Model.classifyCodecExecRequest?` decodes `Internal.mkToolVersionRequest` to `.version`. -/
theorem classifyCodecExecRequest_mkToolVersionRequest (codec : Codec) :
    Model.classifyCodecExecRequest? (Internal.mkToolVersionRequest codec) =
      some (.version codec) := by
  unfold Model.classifyCodecExecRequest? Internal.mkToolVersionRequest
  dsimp only
  rw [parseCodecProgram_codecProgram]
  simp

private theorem compressWith_state_match (st₀ : Model.State) (codec : Codec)
    (opts : CompressOptions) (input : ByteArray) (rawRes : Except ProcessError ExecResult)
    (hValid : isValidCompressInput codec opts input = true) :
    let res := (Internal.mkApiM (scriptedProcessApiId rawRes)).compressWith codec opts input
    (match rawRes with
     | .ok er =>
       if er.exitCode == 0 && er.stdout.size ≤ opts.maxOutputBytes then
         st₀.record codec er.stdout input
       else
         st₀
     | .error _ => st₀) =
    (match res with | .ok c => st₀.record codec c input | .error _ => st₀) := by
  rcases validateCompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, _⟩
  dsimp only [Internal.mkApiM, Internal.compressWith, scriptedProcessApiId, bind, pure, Id.run]
  rw [hVal]
  dsimp only
  cases rawRes with
  | error _ => rfl
  | ok er =>
    dsimp only [Internal.classifyExitResult]
    by_cases hZ : er.exitCode = 0
    · have hNz : (er.exitCode != 0) = false := by simp [hZ]
      have hBeq : (er.exitCode == 0) = true := by simp [hZ]
      simp only [hNz, hBeq, Bool.false_eq_true, Bool.true_and, ↓reduceIte, Bool.false_and]
      by_cases hGt : er.stdout.size > opts.maxOutputBytes
      · have hLe : ¬ (er.stdout.size ≤ opts.maxOutputBytes) := by omega
        simp [hGt, hLe]
      · have hLe : er.stdout.size ≤ opts.maxOutputBytes := by omega
        simp [hGt, hLe]
    · have hNz : (er.exitCode != 0) = true := bne_iff_ne.mpr hZ
      have hBeq : (er.exitCode == 0) = false := beq_false_of_ne hZ
      simp [hNz, hBeq]

private theorem decompressWith_state_match (st₀ : Model.State) (codec : Codec)
    (opts : DecompressOptions) (input : ByteArray) (rawRes : Except ProcessError ExecResult)
    (hValid : isValidDecompressInput opts input = true) :
    let res := (Internal.mkApiM (scriptedProcessApiId rawRes)).decompressWith codec opts input
    (match rawRes with
     | .ok er =>
       if er.exitCode == 0 && er.stdout.size ≤ opts.maxOutputBytes &&
           (codec != .gzip || Model.hasGzipHeader input) then
         st₀.record codec input er.stdout
       else
         st₀
     | .error _ => st₀) =
    (match res with | .ok o => st₀.record codec input o | .error _ => st₀) := by
  rcases validateDecompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, _⟩
  dsimp only [Internal.mkApiM, Internal.decompressWith, scriptedProcessApiId, bind, pure, Id.run]
  rw [hVal]
  dsimp only
  cases rawRes with
  | error pe =>
    dsimp only
    by_cases hBr : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
        codec == .gzip && !Internal.hasGzipHeader input) = true
    · simp [hBr]
    · simp [Bool.eq_false_iff.mpr hBr]
  | ok er =>
    dsimp only [Internal.classifyExitResult, Bool.true_and]
    by_cases hZ : er.exitCode = 0
    · have hNz : (er.exitCode != 0) = false := by simp [hZ]
      have hBeq : (er.exitCode == 0) = true := by simp [hZ]
      simp only [hNz, hBeq, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
      by_cases hGt : er.stdout.size > opts.maxOutputBytes
      · have hLe : decide (er.stdout.size ≤ opts.maxOutputBytes) = false :=
          decide_eq_false (by omega)
        simp only [hGt, hLe, Bool.false_and, ↓reduceIte]
        by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
        · simp [hGh]
        · simp [Bool.eq_false_iff.mpr hGh]
      · have hLe : decide (er.stdout.size ≤ opts.maxOutputBytes) = true :=
          decide_eq_true (by omega)
        simp only [hGt, hLe, Bool.true_and, ↓reduceIte]
        by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
        · have hNot : (codec != .gzip || Model.hasGzipHeader input) = false := by
            cases codec with
            | zstd | xz => cases hGh
            | gzip =>
              change (true && !Model.hasGzipHeader input) = true at hGh
              rw [Bool.true_and, Bool.not_eq_true'] at hGh
              change (false || Model.hasGzipHeader input) = false
              rw [Bool.false_or, hGh]
          simp [hGh, hNot]
        · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false :=
            Bool.eq_false_iff.mpr hGh
          have hOkGh := gzip_or_header_of_not_err hGhF
          simp [hGhF, hOkGh]
    · have hNz : (er.exitCode != 0) = true := bne_iff_ne.mpr hZ
      have hBeq : (er.exitCode == 0) = false := beq_false_of_ne hZ
      simp [hNz, hBeq]

private theorem compressWith_obeys_worldStep {W : Type}
    (proj : W → Model.CompressWorld) (proc : ProcessApiM (StateM W))
    (hWorld : Core.ObeysStep proj Model.worldStepWf (Model.execProcessStep proc) Model.allowedWorldProcessStep)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray) (w : W)
    (hWf : Model.worldStepWf (proj w) = true) :
    let r := (Internal.compressWith proc codec opts input).run w
    Model.worldStepWf (proj r.2) = true ∧
    (proj r.2).env = (proj w).env ∧
    Model.allowedCompressProcessStep (proj w).proc codec opts input r.1 (proj r.2).proc ∧
    Model.allowedCompressStep (proj w).env (proj w).codecState codec opts input r.1 (proj r.2).codecState = true := by
  have hProcWf : LeanSwe.Process.Model.processStateWf (proj w).proc = true :=
    (Bool.and_eq_true _ _).mp hWf |>.1
  by_cases hv : isValidCompressInput codec opts input = true
  · rcases validateCompressOptions_true_implies_ok codec opts input hv with ⟨hVal, hT⟩
    let req := Internal.mkCompressRequest codec opts input
    rcases validateRequestModel_mkCompressRequest codec opts input hT with ⟨norm, hReqOk⟩
    have hRaw := hWorld w (.run req) hWf
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedWorldProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run req).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      rcases hRaw with ⟨_, hWf1, hPkgStep, hEnvEq, hRest⟩
      dsimp only [req] at hWf1 hPkgStep hEnvEq hRest
      rw [hReqOk, classifyCodecExecRequest_mkCompressRequest] at hRest
      dsimp only at hRest
      rcases hRest with ⟨hConfM, hStEq⟩
      have hConf : rawCompressCallConforms (proj w).env (proj w).codecState codec opts input rawRes = true := hConfM
      have hSound := internalApi_compressWith_sound (proj w).env (proj w).codecState codec opts input rawRes hConf
      have hStMatch := compressWith_state_match (proj w).codecState codec opts input rawRes hv
      dsimp only at hSound hStMatch
      have hResEq : ((Internal.compressWith proc codec opts input).run w) =
          (((Internal.mkApiM (scriptedProcessApiId rawRes)).compressWith codec opts input), w1) := by
        unfold Internal.mkApiM
        unfold Internal.compressWith
        dsimp only [scriptedProcessApiId, Id.run]
        rw [hVal, stateT_bind_run, hRun]
        cases rawRes <;> rfl
      rw [hResEq]
      dsimp only
      have hFinalSt : (proj w1).codecState =
          (match (Internal.mkApiM (scriptedProcessApiId rawRes)).compressWith codec opts input with
           | .ok c => (proj w).codecState.record codec c input
           | .error _ => (proj w).codecState) := by
        rw [hStEq]
        cases rawRes <;> exact hStMatch
      rw [hFinalSt]
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hPkgStep
      have hProcPost : Model.allowedCompressProcessStep (proj w).proc codec opts input
          ((Internal.mkApiM (scriptedProcessApiId rawRes)).compressWith codec opts input) (proj w1).proc := by
        have hvM : Model.isValidCompressInput codec opts input = true := hv
        simp only [Model.allowedCompressProcessStep, hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        dsimp only [Internal.mkApiM, Internal.compressWith, scriptedProcessApiId, bind, pure, Id.run]
        rw [hVal]
        cases rawRes with
        | error pe =>
          exact ⟨hHdl, classifyProcessError_wellFormed codec pe, classifyProcessError_ne_corruptData codec pe⟩
        | ok er =>
          exact ⟨hHdl, classifyExitResult_compress_post codec opts.maxOutputBytes input er⟩
      exact ⟨hWf1, hEnvEq, hProcPost, hSound⟩
  · have hf : isValidCompressInput codec opts input = false := Bool.eq_false_iff.mpr hv
    rcases validateCompressOptions_false_implies_error codec opts input hf with
      ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
    have hfM : Model.isValidCompressInput codec opts input = false := hf
    have hErrWf : Model.isWellFormedCompressError codec e = true := by
      unfold Model.isWellFormedCompressError
      have hCod : (some codec == some codec) = true := by cases codec <;> rfl
      have hMsgE : e.message.isEmpty = false := string_ne_empty_iff_isEmpty_false e.message hMsg
      simp [hCodec, hCod, hMsgE, hErr, hKind, hExit]
    dsimp only [Internal.compressWith]
    rw [hVal, stateT_pure_run]
    dsimp only
    refine ⟨hWf, rfl, ?_, ?_⟩
    · unfold Model.allowedCompressProcessStep
      rw [hfM]
      dsimp only
      exact ⟨rfl, hProcWf, hKind, hErrWf⟩
    · unfold Model.allowedCompressStep
      rw [hfM]
      dsimp only
      rw [state_beq_self, hKind, kind_beq_self, hErrWf]
      rfl

private theorem decompressWith_obeys_worldStep {W : Type}
    (proj : W → Model.CompressWorld) (proc : ProcessApiM (StateM W))
    (hWorld : Core.ObeysStep proj Model.worldStepWf (Model.execProcessStep proc) Model.allowedWorldProcessStep)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray) (w : W)
    (hWf : Model.worldStepWf (proj w) = true) :
    let r := (Internal.decompressWith proc codec opts input).run w
    Model.worldStepWf (proj r.2) = true ∧
    (proj r.2).env = (proj w).env ∧
    Model.allowedDecompressProcessStep (proj w).proc codec opts input r.1 (proj r.2).proc ∧
    Model.allowedDecompressStep (proj w).env (proj w).codecState codec opts input r.1 (proj r.2).codecState = true := by
  have hProcWf : LeanSwe.Process.Model.processStateWf (proj w).proc = true :=
    (Bool.and_eq_true _ _).mp hWf |>.1
  by_cases hv : isValidDecompressInput opts input = true
  · rcases validateDecompressOptions_true_implies_ok codec opts input hv with ⟨hVal, hT⟩
    let req := Internal.mkDecompressRequest codec opts input
    rcases validateRequestModel_mkDecompressRequest codec opts input hT with ⟨norm, hReqOk⟩
    have hRaw := hWorld w (.run req) hWf
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedWorldProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run req).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      rcases hRaw with ⟨_, hWf1, hPkgStep, hEnvEq, hRest⟩
      dsimp only [req] at hWf1 hPkgStep hEnvEq hRest
      rw [hReqOk, classifyCodecExecRequest_mkDecompressRequest] at hRest
      dsimp only at hRest
      rcases hRest with ⟨hConfM, hStEq⟩
      have hConf : rawDecompressCallConforms (proj w).env (proj w).codecState codec opts input rawRes = true := hConfM
      have hSound := internalApi_decompressWith_sound (proj w).env (proj w).codecState codec opts input rawRes hConf
      have hStMatch := decompressWith_state_match (proj w).codecState codec opts input rawRes hv
      dsimp only at hSound hStMatch
      have hResEq : ((Internal.decompressWith proc codec opts input).run w) =
          (((Internal.mkApiM (scriptedProcessApiId rawRes)).decompressWith codec opts input), w1) := by
        unfold Internal.mkApiM
        unfold Internal.decompressWith
        dsimp only [scriptedProcessApiId, Id.run]
        rw [hVal, stateT_bind_run, hRun]
        cases rawRes with
        | error pe =>
          dsimp only [Bind.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad]
          by_cases hBr : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
              codec == .gzip && !Internal.hasGzipHeader input) = true
          · rw [ite_eq_left hBr, ite_eq_left hBr]; rfl
          · rw [ite_eq_right hBr, ite_eq_right hBr]; rfl
        | ok _ => rfl
      rw [hResEq]
      dsimp only
      have hFinalSt : (proj w1).codecState =
          (match (Internal.mkApiM (scriptedProcessApiId rawRes)).decompressWith codec opts input with
           | .ok o => (proj w).codecState.record codec input o
           | .error _ => (proj w).codecState) := by
        rw [hStEq]
        cases rawRes <;> exact hStMatch
      rw [hFinalSt]
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hPkgStep
      have hProcPost : Model.allowedDecompressProcessStep (proj w).proc codec opts input
          ((Internal.mkApiM (scriptedProcessApiId rawRes)).decompressWith codec opts input) (proj w1).proc := by
        have hvM : Model.isValidDecompressInput opts input = true := hv
        simp only [Model.allowedDecompressProcessStep, hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        dsimp only [Internal.mkApiM, Internal.decompressWith, scriptedProcessApiId, bind, pure, Id.run]
        rw [hVal]
        cases rawRes with
        | error pe =>
          dsimp only
          by_cases hBr : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
              codec == .gzip && !Internal.hasGzipHeader input) = true
          · simp only [hBr, ↓reduceIte]
            exact ⟨hHdl, framingErr_wellFormed codec pe.stderr⟩
          · simp only [Bool.eq_false_iff.mpr hBr, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hHdl, classifyProcessError_wellFormed codec pe⟩
        | ok er =>
          exact ⟨hHdl, classifyExitResult_decompress_post codec opts.maxOutputBytes input er⟩
      exact ⟨hWf1, hEnvEq, hProcPost, hSound⟩
  · have hf : isValidDecompressInput opts input = false := Bool.eq_false_iff.mpr hv
    rcases validateDecompressOptions_false_implies_error codec opts input hf with
      ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
    have hfM : Model.isValidDecompressInput opts input = false := hf
    have hErrWf : Model.isWellFormedCompressError codec e = true := by
      unfold Model.isWellFormedCompressError
      have hCod : (some codec == some codec) = true := by cases codec <;> rfl
      have hMsgE : e.message.isEmpty = false := string_ne_empty_iff_isEmpty_false e.message hMsg
      simp [hCodec, hCod, hMsgE, hErr, hKind, hExit]
    dsimp only [Internal.decompressWith]
    rw [hVal, stateT_pure_run]
    dsimp only
    refine ⟨hWf, rfl, ?_, ?_⟩
    · unfold Model.allowedDecompressProcessStep
      rw [hfM]
      dsimp only
      exact ⟨rfl, hProcWf, hKind, hErrWf⟩
    · unfold Model.allowedDecompressStep
      rw [hfM]
      dsimp only
      rw [state_beq_self, hKind, kind_beq_self, hErrWf]
      rfl

/-- Compositional `Core.ObeysStepFrom` lifting `Model.allowedWorldProcessStep` to `Internal.mkApiM`. -/
theorem obeysStepFrom_world :
    Core.ObeysStepFrom id Model.worldStepWf Model.execProcessStep Model.allowedWorldProcessStep
      Model.worldStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgWorldStep := by
  intro W proj proc hWorld w req hWf
  have hWfW : Model.worldStepWf (proj w) = true := hWf
  cases req with
  | compress codec input =>
    have h := compressWith_obeys_worldStep proj proc hWorld codec {} input w hWfW
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgWorldStep, Function.comp, id]
    rw [stateT_map_run]
    exact ⟨hWfW, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | decompress codec input =>
    have h := decompressWith_obeys_worldStep proj proc hWorld codec {} input w hWfW
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgWorldStep, Function.comp, id]
    rw [stateT_map_run]
    exact ⟨hWfW, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | compressWith codec opts input =>
    have h := compressWith_obeys_worldStep proj proc hWorld codec opts input w hWfW
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgWorldStep, Function.comp, id]
    rw [stateT_map_run]
    exact ⟨hWfW, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | decompressWith codec opts input =>
    have h := decompressWith_obeys_worldStep proj proc hWorld codec opts input w hWfW
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgWorldStep, Function.comp, id]
    rw [stateT_map_run]
    exact ⟨hWfW, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | isToolAvailable codec =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.isToolAvailable,
      Model.allowedPkgWorldStep, Function.comp, id]
    rw [stateT_map_run, stateT_bind_run]
    let vreq := Internal.mkToolVersionRequest codec
    rcases validateRequestModel_mkToolVersionRequest codec with ⟨norm, hReqOk⟩
    have hRaw := hWorld w (.run vreq) hWfW
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedWorldProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run vreq).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      dsimp only
      rcases hRaw with ⟨_, hWf1, hPkgStep, hEnvEq, hRest⟩
      dsimp only [vreq] at hWf1 hPkgStep hEnvEq hRest
      rw [hReqOk, classifyCodecExecRequest_mkToolVersionRequest] at hRest
      dsimp only at hRest
      rcases hRest with ⟨hConfM, hStEq⟩
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hPkgStep
      have hSound := internalApi_isToolAvailable_sound (proj w).env codec rawRes hConfM
      have hAvailEq : (match rawRes with | .ok res => res.exitCode == 0 | .error _ => false) =
          (Internal.mkApiM (scriptedProcessApiId rawRes)).isToolAvailable codec := by
        unfold Internal.mkApiM
        unfold Internal.isToolAvailable
        dsimp only [scriptedProcessApiId]
        cases rawRes <;> rfl
      cases rawRes <;>
        (rw [stateT_pure_run];
         exact ⟨hWfW, hWf1, hEnvEq, hHdl, hStEq, by simpa [← hAvailEq] using hSound⟩)

end LeanSwe.Compress.Proofs

import Core.Obeys
import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSweProofs.Compress.Model.Refines
import LeanSwe.Compress.Impl
import LeanSweProofs.Compress.Proofs.SharedHelpers

/-!
Compositional `Core.ObeysStepFrom` proof for `LeanSwe.Compress.Internal.mkApiM` directly over
`LeanSwe.Process.Model.ProcessModelState` (`obeysStepFrom_process`) together with a standalone
non-vacuity capability witness (`modelProcessApi_obeys_allowedProcessStep`).
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

/-- Unfold `StateM` pure on `.run`. -/
@[simp] theorem stateT_pure_run {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

/-- Unfold `StateM` bind on `.run`. -/
theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := by
  dsimp only [StateT.run, Bind.bind, StateT.bind]
  cases x s
  rfl

/-- Unfold `StateM` map (`<$>`) on `.run`. -/
theorem stateT_map_run {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := by
  dsimp only [Functor.map, StateT.map, StateT.run]
  cases x s
  rfl

private theorem list_contains_nul_false {cs : List Char} (h : ∀ c ∈ cs, c ≠ '\x00') :
    cs.contains '\x00' = false := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨beq_false_of_ne (Ne.symm (h x List.mem_cons_self)),
      ih (fun c hc => h c (List.mem_cons_of_mem x hc))⟩

private theorem list_contains_append_false {xs ys : List Char} (c : Char)
    (hx : xs.contains c = false) (hy : ys.contains c = false) :
    (xs ++ ys).contains c = false := by
  induction xs with
  | nil => exact hy
  | cons x rest ih =>
    simp only [List.cons_append, List.contains_cons, Bool.or_eq_false_iff] at hx ⊢
    exact ⟨hx.1, ih hx.2⟩

private theorem hasNulModel_append {a b : String}
    (ha : LeanSwe.Process.Model.hasNulModel a = false)
    (hb : LeanSwe.Process.Model.hasNulModel b = false) :
    LeanSwe.Process.Model.hasNulModel (a ++ b) = false := by
  unfold LeanSwe.Process.Model.hasNulModel at ha hb ⊢
  rw [String.toList_append]
  exact list_contains_append_false '\x00' ha hb

private theorem digitChar_ne_nul (d : Nat) : Nat.digitChar d ≠ '\x00' := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
  | n + 16 =>
    have hStar : Nat.digitChar (n + 16) = '*' := by
      unfold Nat.digitChar
      iterate 16 (rw [ite_eq_right (by omega)])
    rw [hStar]
    decide

private theorem toDigitsCore_no_nul (base fuel n : Nat) (ds : List Char)
    (hds : ∀ c ∈ ds, c ≠ '\x00') :
    ∀ c ∈ Nat.toDigitsCore base fuel n ds, c ≠ '\x00' := by
  induction fuel generalizing n ds with
  | zero => exact hds
  | succ f ih =>
    unfold Nat.toDigitsCore
    dsimp only
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact digitChar_ne_nul _
      · exact hds c hmem
    · apply ih
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact digitChar_ne_nul _
      · exact hds c hmem

private theorem hasNulModel_natRepr (n : Nat) :
    LeanSwe.Process.Model.hasNulModel (Nat.repr n) = false := by
  unfold LeanSwe.Process.Model.hasNulModel Nat.repr
  rw [String.toList_ofList]
  exact list_contains_nul_false (toDigitsCore_no_nul 10 (n + 1) n [] (fun _ h => nomatch h))

private theorem hasNulModel_levelArg (lvl : Nat) :
    LeanSwe.Process.Model.hasNulModel s!"-{lvl}" = false := by
  change LeanSwe.Process.Model.hasNulModel ("-" ++ Nat.repr lvl) = false
  exact hasNulModel_append rfl (hasNulModel_natRepr lvl)

private theorem hasNulModel_threadArg (t : Nat) :
    LeanSwe.Process.Model.hasNulModel s!"-T{t}" = false := by
  change LeanSwe.Process.Model.hasNulModel ("-T" ++ Nat.repr t) = false
  exact hasNulModel_append rfl (hasNulModel_natRepr t)

private theorem array_append_any_false {a b : Array String} {p : String → Bool}
    (ha : a.toList.any p = false) (hb : b.toList.any p = false) :
    (a ++ b).toList.any p = false := by
  rw [Array.toList_append, List.any_append, ha, hb]
  rfl

private theorem mkCompressArgs_any_hasNul_false (codec : Codec) (opts : CompressOptions) :
    (Internal.mkCompressArgs codec opts).toList.any LeanSwe.Process.Model.hasNulModel = false := by
  unfold Internal.mkCompressArgs
  dsimp only
  have hL : (match opts.level with | none => #[] | some lvl => #[s!"-{lvl}"]).toList.any
      LeanSwe.Process.Model.hasNulModel = false := by
    cases opts.level with
    | none => rfl
    | some lvl =>
      change (LeanSwe.Process.Model.hasNulModel s!"-{lvl}" || false) = false
      rw [Bool.or_false]
      exact hasNulModel_levelArg lvl
  have hT : (match opts.threads with | none => #[] | some t => #[s!"-T{t}"]).toList.any
      LeanSwe.Process.Model.hasNulModel = false := by
    cases opts.threads with
    | none => rfl
    | some t =>
      change (LeanSwe.Process.Model.hasNulModel s!"-T{t}" || false) = false
      rw [Bool.or_false]
      exact hasNulModel_threadArg t
  cases codec with
  | zstd => exact array_append_any_false (array_append_any_false rfl hL) hT
  | xz => exact array_append_any_false (array_append_any_false rfl hL) hT
  | gzip => exact array_append_any_false rfl hL

private theorem mkDecompressArgs_any_hasNul_false (codec : Codec) :
    (Internal.mkDecompressArgs codec).toList.any LeanSwe.Process.Model.hasNulModel = false := by
  cases codec <;> rfl

private theorem codecProgram_isEmpty_false (codec : Codec) :
    (Internal.codecProgram codec).isEmpty = false := by
  cases codec <;> rfl

private theorem codecProgram_hasNul_false (codec : Codec) :
    LeanSwe.Process.Model.hasNulModel (Internal.codecProgram codec) = false := by
  cases codec <;> rfl

private theorem codecSanitizedEnv_any_invalid_false :
    Internal.codecSanitizedEnv.toList.any LeanSwe.Process.Model.isInvalidEnvEntryModel = false := by
  decide

/-- Every valid `mkCompressRequest` passes `LeanSwe.Process.Model.validateRequestModel`. -/
theorem validateRequestModel_mkCompressRequest (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (hTimeout : opts.timeoutMs ≠ 0) :
    ∃ norm, LeanSwe.Process.Model.validateRequestModel
      (Internal.mkCompressRequest codec opts input) = .ok norm := by
  unfold LeanSwe.Process.Model.validateRequestModel
    LeanSwe.Process.Model.validateSpawnRequestModel Internal.mkCompressRequest
  have hT : (some opts.timeoutMs == some 0) = false := by
    cases htv : opts.timeoutMs with
    | zero => exact absurd htv hTimeout
    | succ _ => rfl
  simp only [codecProgram_isEmpty_false, codecProgram_hasNul_false,
    mkCompressArgs_any_hasNul_false, codecSanitizedEnv_any_invalid_false, hT,
    Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- Every valid `mkDecompressRequest` passes `LeanSwe.Process.Model.validateRequestModel`. -/
theorem validateRequestModel_mkDecompressRequest (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (hTimeout : opts.timeoutMs ≠ 0) :
    ∃ norm, LeanSwe.Process.Model.validateRequestModel
      (Internal.mkDecompressRequest codec opts input) = .ok norm := by
  unfold LeanSwe.Process.Model.validateRequestModel
    LeanSwe.Process.Model.validateSpawnRequestModel Internal.mkDecompressRequest
  have hT : (some opts.timeoutMs == some 0) = false := by
    cases htv : opts.timeoutMs with
    | zero => exact absurd htv hTimeout
    | succ _ => rfl
  simp only [codecProgram_isEmpty_false, codecProgram_hasNul_false,
    mkDecompressArgs_any_hasNul_false, codecSanitizedEnv_any_invalid_false, hT,
    Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- Every `mkToolVersionRequest` passes `LeanSwe.Process.Model.validateRequestModel`. -/
theorem validateRequestModel_mkToolVersionRequest (codec : Codec) :
    ∃ norm, LeanSwe.Process.Model.validateRequestModel
      (Internal.mkToolVersionRequest codec) = .ok norm := by
  unfold LeanSwe.Process.Model.validateRequestModel
    LeanSwe.Process.Model.validateSpawnRequestModel Internal.mkToolVersionRequest
  have hArgs : (#["--version"].toList.any LeanSwe.Process.Model.hasNulModel) = false := rfl
  simp only [codecProgram_isEmpty_false, codecProgram_hasNul_false, hArgs,
    codecSanitizedEnv_any_invalid_false, show (some 5000 == some 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- `Internal.classifyProcessError` never produces `.corruptData`. -/
theorem classifyProcessError_ne_corruptData (codec : Codec) (pe : ProcessError) :
    (Internal.classifyProcessError codec pe).kind ≠ .corruptData := by
  unfold Internal.classifyProcessError
  cases pe.kind with
  | invalidInput =>
    by_cases hRes : Internal.isResourceExhaustedProcessError pe <;> simp [hRes]
  | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError =>
    simp

/-- Postcondition of `Internal.classifyExitResult` for compression (`isDecompress = false`). -/
theorem classifyExitResult_compress_post (codec : Codec) (maxOut : Nat) (input : ByteArray)
    (res : ExecResult) :
    match Internal.classifyExitResult codec false maxOut input res with
    | .ok comp => comp.size ≤ maxOut
    | .error e => Model.isWellFormedCompressError codec e = true ∧ e.kind ≠ .corruptData := by
  by_cases hNz : (res.exitCode != 0) = true
  · have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec false maxOut input res = .error e ∧
        e.kind = .commandFailed := by
      unfold Internal.classifyExitResult; simp only [hNz, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
    have hWf := classifyExitResult_wellFormed_of_err codec false maxOut input res hEq
    rw [hEq]
    exact ⟨hWf, by rw [hk]; decide⟩
  · by_cases hOut : res.stdout.size > maxOut
    · have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec false maxOut input res = .error e ∧
          e.kind = .outputLimitExceeded := by
        unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.false_and]; exact ⟨_, rfl, rfl⟩
      have hWf := classifyExitResult_wellFormed_of_err codec false maxOut input res hEq
      rw [hEq]
      exact ⟨hWf, by rw [hk]; decide⟩
    · have hEq : Internal.classifyExitResult codec false maxOut input res = .ok res.stdout := by
        unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.false_and]
      rw [hEq]
      omega

/-- Postcondition of `Internal.classifyExitResult` for decompression (`isDecompress = true`). -/
theorem classifyExitResult_decompress_post (codec : Codec) (maxOut : Nat) (input : ByteArray)
    (res : ExecResult) :
    match Internal.classifyExitResult codec true maxOut input res with
    | .ok out => out.size ≤ maxOut ∧ (codec != .gzip || Model.hasGzipHeader input) = true
    | .error e => Model.isWellFormedCompressError codec e = true := by
  cases hCl : Internal.classifyExitResult codec true maxOut input res with
  | error e => exact classifyExitResult_wellFormed_of_err codec true maxOut input res hCl
  | ok out =>
    unfold Internal.classifyExitResult at hCl
    by_cases hNz : (res.exitCode != 0) = true
    · simp [hNz] at hCl
    · simp only [hNz, Bool.false_eq_true, ↓reduceIte] at hCl
      by_cases hOut : res.stdout.size > maxOut
      · simp only [hOut, ↓reduceIte, Bool.true_and] at hCl
        split at hCl <;> cases hCl
      · simp only [hOut, ↓reduceIte, Bool.true_and] at hCl
        by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
        · simp [hGh] at hCl
        · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false := Bool.eq_false_iff.mpr hGh
          simp only [hGhF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hCl
          subst hCl
          exact ⟨by omega, gzip_or_header_of_not_err hGhF⟩

/-- Extract `Model.allowedProcessHandleStep` from `LeanSwe.Process.Model.allowedPkgStep` on a valid `run` request. -/
theorem allowedProcessHandleStep_of_pkgRun {s s' : LeanSwe.Process.Model.ProcessModelState}
    {req norm : ExecRequest} {rawRes : Except ProcessError ExecResult}
    (hVal : LeanSwe.Process.Model.validateRequestModel req = .ok norm)
    (hStep : LeanSwe.Process.Model.allowedPkgStep s (.run req) (.execRes rawRes) s') :
    Model.allowedProcessHandleStep s s' := by
  rcases hStep with ⟨hWf, hWf', hRun⟩
  dsimp only [LeanSwe.Process.Model.allowedPkgRun] at hRun
  rw [hVal] at hRun
  exact ⟨hWf, hWf', hRun.1, hRun.2.1⟩

/-- Single-step `compressWith` refinement over `ProcessModelState`. -/
theorem compressWith_obeys_processStep {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (proc : ProcessApiM (StateM W))
    (hProc : Core.ObeysStep proj Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray) (w : W)
    (hWf : Model.processStepWf (proj w) = true) :
    let r := (Internal.compressWith proc codec opts input).run w
    Model.allowedCompressProcessStep (proj w) codec opts input r.1 (proj r.2) := by
  dsimp only [Model.allowedCompressProcessStep]
  by_cases hv : isValidCompressInput codec opts input = true
  · rcases validateCompressOptions_true_implies_ok codec opts input hv with ⟨hVal, hT⟩
    have hvM : Model.isValidCompressInput codec opts input = true := hv
    simp only [hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Internal.compressWith, hVal]
    rw [stateT_bind_run]
    let req := Internal.mkCompressRequest codec opts input
    rcases validateRequestModel_mkCompressRequest codec opts input hT with ⟨norm, hReqOk⟩
    have hRaw := hProc w (.run req) hWf
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, Model.allowedProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run req).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      dsimp only
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hRaw
      cases rawRes with
      | error pe =>
        exact ⟨hHdl, classifyProcessError_wellFormed codec pe, classifyProcessError_ne_corruptData codec pe⟩
      | ok er =>
        exact ⟨hHdl, classifyExitResult_compress_post codec opts.maxOutputBytes input er⟩
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
    rw [hfM, hVal, stateT_pure_run]
    dsimp only
    exact ⟨rfl, hWf, hKind, hErrWf⟩

/-- Single-step `decompressWith` refinement over `ProcessModelState`. -/
theorem decompressWith_obeys_processStep {W : Type}
    (proj : W → LeanSwe.Process.Model.ProcessModelState)
    (proc : ProcessApiM (StateM W))
    (hProc : Core.ObeysStep proj Model.processStepWf (Model.execProcessStep proc) Model.allowedProcessStep)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray) (w : W)
    (hWf : Model.processStepWf (proj w) = true) :
    let r := (Internal.decompressWith proc codec opts input).run w
    Model.allowedDecompressProcessStep (proj w) codec opts input r.1 (proj r.2) := by
  dsimp only [Model.allowedDecompressProcessStep]
  by_cases hv : isValidDecompressInput opts input = true
  · rcases validateDecompressOptions_true_implies_ok codec opts input hv with ⟨hVal, hT⟩
    have hvM : Model.isValidDecompressInput opts input = true := hv
    simp only [hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Internal.decompressWith, hVal]
    rw [stateT_bind_run]
    let req := Internal.mkDecompressRequest codec opts input
    rcases validateRequestModel_mkDecompressRequest codec opts input hT with ⟨norm, hReqOk⟩
    have hRaw := hProc w (.run req) hWf
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, Model.allowedProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run req).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      dsimp only
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hRaw
      cases rawRes with
      | error pe =>
        dsimp only
        by_cases hBr : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
            codec == .gzip && !Internal.hasGzipHeader input) = true
        · simp only [hBr, ↓reduceIte, stateT_pure_run]
          exact ⟨hHdl, framingErr_wellFormed codec pe.stderr⟩
        · simp only [Bool.eq_false_iff.mpr hBr, Bool.false_eq_true, ↓reduceIte, stateT_pure_run]
          exact ⟨hHdl, classifyProcessError_wellFormed codec pe⟩
      | ok er =>
        exact ⟨hHdl, classifyExitResult_decompress_post codec opts.maxOutputBytes input er⟩
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
    rw [hfM, hVal, stateT_pure_run]
    dsimp only
    exact ⟨rfl, hWf, hKind, hErrWf⟩

/-- Compositional `Core.ObeysStepFrom` lifting `LeanSwe.Process.Model.allowedPkgStep` to `Internal.mkApiM`. -/
theorem obeysStepFrom_process :
    Core.ObeysStepFrom id Model.processStepWf Model.execProcessStep Model.allowedProcessStep
      Model.processStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgProcessStep := by
  intro W proj proc hProc w req hWf
  have hWfP : Model.processStepWf (proj w) = true := hWf
  cases req with
  | compress codec input =>
    have h := compressWith_obeys_processStep proj proc hProc codec {} input w hWfP
    dsimp only [Model.execPkgStep, Internal.mkApiM, Function.comp, id]
    rw [stateT_map_run]
    exact h
  | decompress codec input =>
    have h := decompressWith_obeys_processStep proj proc hProc codec {} input w hWfP
    dsimp only [Model.execPkgStep, Internal.mkApiM, Function.comp, id]
    rw [stateT_map_run]
    exact h
  | compressWith codec opts input =>
    have h := compressWith_obeys_processStep proj proc hProc codec opts input w hWfP
    dsimp only [Model.execPkgStep, Internal.mkApiM, Function.comp, id]
    rw [stateT_map_run]
    exact h
  | decompressWith codec opts input =>
    have h := decompressWith_obeys_processStep proj proc hProc codec opts input w hWfP
    dsimp only [Model.execPkgStep, Internal.mkApiM, Function.comp, id]
    rw [stateT_map_run]
    exact h
  | isToolAvailable codec =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.isToolAvailable, Function.comp, id]
    rw [stateT_map_run, stateT_bind_run]
    let vreq := Internal.mkToolVersionRequest codec
    rcases validateRequestModel_mkToolVersionRequest codec with ⟨norm, hReqOk⟩
    have hRaw := hProc w (.run vreq) hWfP
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep, Model.allowedProcessStep] at hRaw
    rw [stateT_map_run] at hRaw
    cases hRun : (proc.run vreq).run w with
    | mk rawRes w1 =>
      rw [hRun] at hRaw
      dsimp only
      have hHdl := allowedProcessHandleStep_of_pkgRun hReqOk hRaw
      cases rawRes <;> exact hHdl

private theorem list_contains_map_filter_false {xs : List LeanSwe.Process.Model.ProcessHandleEntry}
    {p : LeanSwe.Process.Model.ProcessHandleEntry → Bool} {x : Nat}
    (h : (xs.map (·.handleId)).contains x = false) :
    ((xs.filter p).map (·.handleId)).contains x = false := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩
    · exact ih h.2

private theorem hasNoDupHandleIds_filter (xs : List LeanSwe.Process.Model.ProcessHandleEntry)
    (p : LeanSwe.Process.Model.ProcessHandleEntry → Bool)
    (h : LeanSwe.Process.Model.hasNoDupHandleIds (xs.map (·.handleId)) = true) :
    LeanSwe.Process.Model.hasNoDupHandleIds ((xs.filter p).map (·.handleId)) = true := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds,
      Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, LeanSwe.Process.Model.hasNoDupHandleIds,
        Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨list_contains_map_filter_false h.1, ih h.2⟩
    · exact ih h.2

/-- Filtering `activeHandles` preserves `LeanSwe.Process.Model.processStateWf`. -/
theorem processStateWf_filter (s : LeanSwe.Process.Model.ProcessModelState)
    (p : LeanSwe.Process.Model.ProcessHandleEntry → Bool)
    (hWf : LeanSwe.Process.Model.processStateWf s = true) :
    LeanSwe.Process.Model.processStateWf { s with activeHandles := s.activeHandles.filter p } = true := by
  unfold LeanSwe.Process.Model.processStateWf at hWf ⊢
  simp only [Bool.and_eq_true] at hWf ⊢
  refine ⟨⟨hWf.1.1, hasNoDupHandleIds_filter s.activeHandles p hWf.1.2⟩, ?_⟩
  rw [List.all_eq_true] at hWf ⊢
  intro e he
  exact hWf.2 e (List.mem_filter.mp he).1

private def simRunPure (req : ExecRequest) (s : LeanSwe.Process.Model.ProcessModelState) :
    Except ProcessError ExecResult × LeanSwe.Process.Model.ProcessModelState :=
  match LeanSwe.Process.Model.validateRequestModel req with
  | .error verr => (.error verr, s)
  | .ok _ => (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)

private theorem simRunPure_snd (req : ExecRequest) (s : LeanSwe.Process.Model.ProcessModelState) :
    (simRunPure req s).2 = s := by
  unfold simRunPure
  cases LeanSwe.Process.Model.validateRequestModel req <;> rfl

private theorem simRunPure_allowedPkgRun (checked : Bool) (req : ExecRequest)
    (s : LeanSwe.Process.Model.ProcessModelState) :
    LeanSwe.Process.Model.allowedPkgRun checked s req (simRunPure req s).1 (simRunPure req s).2 := by
  unfold simRunPure LeanSwe.Process.Model.allowedPkgRun
  cases LeanSwe.Process.Model.validateRequestModel req with
  | error _ => exact ⟨rfl, rfl⟩
  | ok _ =>
    refine ⟨rfl, Or.inl rfl, fun _ => rfl, fun lim _ => ?_⟩
    change 0 ≤ lim
    exact Nat.zero_le lim

/-- Pure `ProcessApiM (StateM ProcessModelState)` capability witness inhabiting `Model.allowedProcessStep`. -/
def modelProcessApi : ProcessApiM (StateM LeanSwe.Process.Model.ProcessModelState) :=
  { mapRawError := LeanSwe.Process.Model.mapRawErrorModel
    validateRequest := LeanSwe.Process.Model.validateRequestModel
    mkCommandRequest := LeanSwe.Process.Model.mkCommandRequestModel
    withTextInput := LeanSwe.Process.Model.withTextInputModel
    spawn := fun r s =>
      match LeanSwe.Process.Model.validateSpawnRequestModel r with
      | .error err => (.error err, s)
      | .ok _ => (.error { kind := .ioError, message := "mock spawn unavailable" }, s)
    awaitOutput := fun _ _ timeoutMs _ s =>
      if timeoutMs == some 0 then
        (.error { kind := .invalidInput, message := "timeoutMs must be greater than zero" }, s)
      else
        (.error { kind := .ioError, message := "mock await unavailable" }, s)
    killProcessGroup := fun _ s => (.ok (), s)
    reap := fun h s =>
      (.ok (), { s with activeHandles := s.activeHandles.filter (·.handleId != h.handleId) })
    run := simRunPure
    runChecked := simRunPure
    runCommand := fun prog args => simRunPure (LeanSwe.Process.Model.mkCommandRequestModel prog args)
    runCommandChecked := fun prog args => simRunPure (LeanSwe.Process.Model.mkCommandRequestModel prog args)
    activeProcessCount := fun s => (s.activeHandles.length, s) }

/-- Non-vacuity theorem showing `modelProcessApi` obeys `Model.allowedProcessStep`. -/
theorem modelProcessApi_obeys_allowedProcessStep :
    Core.ObeysStep id Model.processStepWf (Model.execProcessStep modelProcessApi) Model.allowedProcessStep := by
  intro s req hWf
  have hWfP : LeanSwe.Process.Model.processStateWf s = true := hWf
  cases req with
  | spawn r =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    cases LeanSwe.Process.Model.validateSpawnRequestModel r with
    | error _ => exact ⟨hWfP, hWfP, rfl, rfl⟩
    | ok _ =>
      refine ⟨hWfP, hWfP, rfl, ?_⟩
      dsimp only [LeanSwe.Process.Model.isNonOutcomeError]
      decide
  | awaitOutput h stdin timeoutMs maxOutputBytes =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    cases hT : (timeoutMs == some 0) with
    | true =>
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨hWfP, hWfP, rfl, rfl⟩
    | false =>
      rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
      dsimp only [LeanSwe.Process.Model.allowedAwaitCore, LeanSwe.Process.Model.isNonOutcomeError]
      exact ⟨hWfP, hWfP, hWfP, rfl, rfl, rfl, by decide⟩
  | killProcessGroup _ =>
    exact ⟨hWfP, hWfP, rfl, trivial⟩
  | reap h =>
    exact ⟨hWfP, processStateWf_filter s _ hWfP, rfl, rfl, trivial⟩
  | run r =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    refine ⟨hWfP, ?_, simRunPure_allowedPkgRun false r s⟩
    rw [simRunPure_snd]
    exact hWfP
  | runChecked r =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    refine ⟨hWfP, ?_, simRunPure_allowedPkgRun true r s⟩
    rw [simRunPure_snd]
    exact hWfP
  | runCommand prog args =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    refine ⟨hWfP, ?_, simRunPure_allowedPkgRun false (LeanSwe.Process.Model.mkCommandRequestModel prog args) s⟩
    rw [simRunPure_snd]
    exact hWfP
  | runCommandChecked prog args =>
    dsimp only [Model.execProcessStep, LeanSwe.Process.Model.execPkgStep,
      Model.allowedProcessStep, LeanSwe.Process.Model.allowedPkgStep, id]
    rw [stateT_map_run]
    dsimp only [StateT.run, modelProcessApi]
    refine ⟨hWfP, ?_, simRunPure_allowedPkgRun true (LeanSwe.Process.Model.mkCommandRequestModel prog args) s⟩
    rw [simRunPure_snd]
    exact hWfP
  | activeProcessCount =>
    exact ⟨hWfP, hWfP, rfl, rfl⟩

end LeanSwe.Compress.Proofs

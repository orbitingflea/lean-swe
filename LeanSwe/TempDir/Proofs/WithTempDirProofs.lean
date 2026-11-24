import LeanSwe.TempDir.Proofs.Shared
set_option Elab.async false
/-!
Verification of `LeanSwe.TempDir` `withTempDir`, validation, and root-resolution
specifications (Specs 1–7) and their `CanReach` witnesses.
-/
namespace LeanSwe.TempDir.Proofs
open Core Core.NondetTest LeanSwe.Time LeanSwe.Uuid LeanSwe.EnvVars
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
private theorem lookupNode_dir_after_writeText (sMk : TempDirMockState) (root child nm : String) (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (hnmNe : nm ≠ "") (hnmNoSlash : '/' ∉ nm.toList) (t : Int) (mode : Nat) (c : String) (hLook : lookupNode sMk.nodes (mockJoin root child) = some (.dir t mode)) :
    let dir := mockJoin root child; let p := mockJoin dir nm
    lookupNode ((normKey p, .file (freshInode sMk) c sMk.nowSec 0o644) :: sMk.nodes.filter (fun e => normKey e.1 != normKey p)) dir = some (.dir t mode) := by
  intro dir p; have hDirNorm := normKey_mockJoin root child hcNe hcNoSlash; have hNe := payload_ne_dir root child nm hrNe hcNe hcNoSlash hnmNe hnmNoSlash
  unfold lookupNode; rw [List.find?_cons]; dsimp only; rw [show (normKey (normKey p) == normKey dir) = false by rw [normKey_idem, hDirNorm, beq_false_of_ne hNe]]
  exact (lookupNode_filter_of_preserved sMk.nodes (fun e => normKey e.1 != normKey p) dir fun e _ he => by simp only [bne_iff_ne, ne_eq]; rw [he, hDirNorm]; exact ne_comm.mp hNe).trans hLook
private theorem allThree_of_validPrefix_false (s₀ : TempDirMockState) (root? : Option String) (dirPrefix : String) (hvp : Internal.validPrefix dirPrefix = false)
    {α : Type} (act : String → StateM TempDirMockState (Except TempDirError α)) :
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    (∃ e, (api.withTempDir root? dirPrefix act).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, (api.withLockedTempDir root? dirPrefix act).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, (api.cleanupStaleTempDirs root? dirPrefix 86400).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") := by
  let err : TempDirError := { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }
  have hCre : (Internal.createTempDir mockFs mockUuid mockEnv root? dirPrefix).run s₀ = (.error err, s₀) := by dsimp only [Internal.createTempDir, err]; simp only [hvp, Bool.not_false, ↓reduceIte, stateM_pure_run]
  refine ⟨⟨err, ?_, rfl, by decide⟩, ⟨err, ?_, rfl, by decide⟩, ⟨err, ?_, rfl, by decide⟩⟩
  · rw [mkApiM_withTempDir_eq, withTempDirM_create_err _ _ _ _ _ _ _ _ _ hCre]
  · rw [mkApiM_withLockedTempDir_eq]; exact withTempDirM_create_err mockFs mockUuid mockEnv s₀ s₀ root? dirPrefix _ _ hCre
  · rw [mkApiM_cleanupStaleTempDirs_eq]; dsimp only [Internal.cleanupStaleTempDirsM, err]; simp only [hvp, Bool.not_false, ↓reduceIte, stateM_pure_run]
private theorem allThree_of_resolveRoot_err (s₀ s₁ : TempDirMockState) (root? : Option String) (dirPrefix : String) (te : TempDirError)
    (hvp : Internal.validPrefix dirPrefix = true) (hRes : (Internal.resolveRoot mockFs mockEnv root?).run s₀ = (.error te, s₁))
    {α : Type} (act : String → StateM TempDirMockState (Except TempDirError α)) :
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    (api.withTempDir root? dirPrefix act).run s₀ = (.error te, s₁) ∧ (api.withLockedTempDir root? dirPrefix act).run s₀ = (.error te, s₁) ∧ (api.cleanupStaleTempDirs root? dirPrefix 86400).run s₀ = (.error te, s₁) := by
  have hCre : (Internal.createTempDir mockFs mockUuid mockEnv root? dirPrefix).run s₀ = (.error te, s₁) := by dsimp only [Internal.createTempDir]; simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hRes, stateM_pure_run]
  refine ⟨by rw [mkApiM_withTempDir_eq, withTempDirM_create_err _ _ _ _ _ _ _ _ _ hCre], by rw [mkApiM_withLockedTempDir_eq]; exact withTempDirM_create_err mockFs mockUuid mockEnv s₀ s₁ root? dirPrefix _ _ hCre,
    by rw [mkApiM_cleanupStaleTempDirs_eq]; dsimp only [Internal.cleanupStaleTempDirsM]; simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hRes, stateM_pure_run]⟩
private theorem withTempDir_failRm_run {α : Type} (s₀ : TempDirMockState) (root dirPrefix : String) (fe : String → FsError) (actRes : Except TempDirError α)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true) (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hNe : ((fe (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).kind == .notFound) = false) :
    let fsFail : FsApiM (StateM TempDirMockState) := { mockFs with rmtree := fun p _ => pure (.error (fe p)) }
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    let sMk : TempDirMockState := { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    ((Internal.mkApiM fsFail mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix fun _ => pure actRes).run s₀ = (Internal.combineCleanup actRes (.error (Internal.mapFsError (fe dir))), sMk) := by
  intro fsFail dir sMk
  have hOpsFail : CreateFsOps fsFail := ⟨rfl, fun _ s => mockFs_stat_run s _, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  have hResFail := resolveRoot_some_ok_run (fs := fsFail) (fun _ s => mockFs_stat_run s _) s₀ root hvr stRoot hRoot hRwx.1
  have hCreFail := createTempDir_ok_run hOpsFail s₀ (some root) root dirPrefix hResFail hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCreFail
  have hClnFail : (Internal.cleanupDirIgnoringNotFound fsFail dir).run sMk = (.error (Internal.mapFsError (fe dir)), sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsFail]; rw [stateM_bind_run, stateM_pure_run]; dsimp only; rw [hNe]; exact stateM_pure_run _ _
  rw [mkApiM_withTempDir_eq]; exact withTempDirM_run fsFail mockUuid mockEnv s₀ sMk sMk sMk (some root) dirPrefix dir _ _ _ hCreFail (stateM_pure_run _ _) hClnFail
/-- Spec 1: `withTempDir` creates `<root>/<dirPrefix><uuid>` with mode `0o700`, executes `action dir`, returns `.ok val`, and removes `dir` on exit. -/
theorem proof_tempdir_withTempDir_okCleansUpAndSetsMode :
    AllPass (test_tempdir_withTempDir_okCleansUpAndSetsMode (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_okCleansUpAndSetsMode, AllPass]; intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq, mockFs_lstat_run] at hNone
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  have hCre := createTempDir_ok_run createFsOps_mockFs s₀ (some root) root dirPrefix (resolveRoot_some_ok_run (fun _ s => mockFs_stat_run s _) s₀ root hvr stRoot hRoot hRwx.1) hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCre; obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCre; have hLookMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  let payload := mockJoin dir "payload.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (normKey payload, .file (freshInode sMk) "hello" sMk.nowSec 0o644) :: sMk.nodes.filter (fun e => normKey e.1 != normKey payload), nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hLookAct : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAct]; exact lookupNode_dir_after_writeText sMk root _ "payload.txt" hrNe hcNe hcNoSlash (by decide) (by decide) s₀.nowSec 0o700 "hello" hLookMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s = { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCln := cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookAct⟩; rw [← hsFin] at hCln; have hGone : lookupNode sFin.nodes dir = none := by rw [hsFin]; exact lookupNode_filter_underDir_eq _ _ hDirNorm
  rw [mkApiM_withTempDir_eq]; dsimp only [Internal.withTempDirM]; rw [mockFs_join_eq, mockUuid_toString_eq, stateM_bind_run, hCre]; dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, stateM_bind_run, mockFs_lstat_run]; unfold mockLstatPure; rw [hLookMk]; dsimp only [mockNodeStat]
  rw [show (EntryKind.dir != EntryKind.dir || (448 : Nat) != 0o700) = false by decide, Bool.false_or, bne_self_eq_false]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_writeText_run, ← hsAct]; dsimp only; simp only [stateM_pure_run]; rw [hCln]; dsimp only
  rw [allPass_assert, allPass_assert_end]; exact ⟨rfl, mockFs_lstat_isOk_false_of_lookup_none sFin dir hGone, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 1 (`test_tempdir_withTempDir_okCleansUpAndSetsMode`). -/
theorem reach_tempdir_withTempDir_okCleansUpAndSetsMode :
    CanReach (test_tempdir_withTempDir_okCleansUpAndSetsMode (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_okCleansUpAndSetsMode, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀; refine ⟨s₀, "/tmp", "tmp-", 42, ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]
  exact ⟨hNone, by have hp := proof_tempdir_withTempDir_okCleansUpAndSetsMode s₀ "/tmp" "tmp-" 42 ⟨rfl, rfl⟩ hRoot; dsimp only [test_tempdir_withTempDir_okCleansUpAndSetsMode, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; exact hp hNone⟩
/-- Spec 2: `withTempDir` cleans up `dir` and returns `action`'s `.error` with precedence over cleanup errors. -/
theorem proof_tempdir_withTempDir_errorCleansUpAndPreservesError :
    AllPass (test_tempdir_withTempDir_errorCleansUpAndPreservesError (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_errorCleansUpAndPreservesError, AllPass]; intro s₀ root dirPrefix actionErr ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq, mockFs_lstat_run] at hNone
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  have hCre := createTempDir_ok_run createFsOps_mockFs s₀ (some root) root dirPrefix (resolveRoot_some_ok_run (fun _ s => mockFs_stat_run s _) s₀ root hvr stRoot hRoot hRwx.1) hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCre
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCre; have hLookMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  let tmpPath := mockJoin dir "tmp.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (normKey tmpPath, .file (freshInode sMk) "data" sMk.nowSec 0o644) :: sMk.nodes.filter (fun e => normKey e.1 != normKey tmpPath), nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hLookAct : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAct]; exact lookupNode_dir_after_writeText sMk root _ "tmp.txt" hrNe hcNe hcNoSlash (by decide) (by decide) s₀.nowSec 0o700 "data" hLookMk
  have hAct : (do let _ ← mockFs.writeText (mockJoin dir "tmp.txt") "data"; return (Except.error actionErr : Except TempDirError Nat)).run sMk = (.error actionErr, sAct) := by rw [stateM_bind_run, mockFs_writeText_run, ← hsAct]; exact stateM_pure_run _ _
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s = { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCln := cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookAct⟩; rw [← hsFin] at hCln; have hGone : lookupNode sFin.nodes dir = none := by rw [hsFin]; exact lookupNode_filter_underDir_eq _ _ hDirNorm
  rw [mockFs_join_eq, mockUuid_toString_eq, mkApiM_withTempDir_eq]
  have hRun1 := withTempDirM_run mockFs mockUuid mockEnv s₀ sMk sAct sFin (some root) dirPrefix dir (fun d => do let _ ← mockFs.writeText (mockJoin d "tmp.txt") "data"; return (Except.error actionErr : Except TempDirError Nat)) (.error actionErr) (.ok ()) hCre hAct hCln
  have hRunFail := withTempDir_failRm_run s₀ root dirPrefix (fun _ => { kind := .permissionDenied, message := "cleanup failed" }) (Except.error actionErr : Except TempDirError Nat) hvr hvp stRoot hRoot hRwx hNone rfl
  rw [hRun1]; dsimp only at hRunFail ⊢; erw [hRunFail]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]; exact ⟨rfl, mockFs_lstat_isOk_false_of_lookup_none sFin dir hGone, rfl, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 2 (`test_tempdir_withTempDir_errorCleansUpAndPreservesError`). -/
theorem reach_tempdir_withTempDir_errorCleansUpAndPreservesError :
    CanReach (test_tempdir_withTempDir_errorCleansUpAndPreservesError (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_errorCleansUpAndPreservesError, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  let err : TempDirError := { kind := .ioError, message := "boom" }; have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  refine ⟨s₀, "/tmp", "tmp-", err, ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]
  exact ⟨hNone, by have hp := proof_tempdir_withTempDir_errorCleansUpAndPreservesError s₀ "/tmp" "tmp-" err ⟨rfl, rfl⟩ hRoot; dsimp only [test_tempdir_withTempDir_errorCleansUpAndPreservesError, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; exact hp hNone⟩
/-- Spec 3: When `action` returns `.ok` and `fs.rmtree` fails, `withTempDir` propagates the cleanup error rather than swallowing it. -/
theorem proof_tempdir_withTempDir_cleanupErrorReturnedOnOk :
    AllPass (test_tempdir_withTempDir_cleanupErrorReturnedOnOk (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, AllPass]; intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq, mockFs_lstat_run] at hNone
  have hRun := withTempDir_failRm_run s₀ root dirPrefix (fun p => { kind := .permissionDenied, path := some p, message := "rm failed" }) (.ok val) hvr hvp stRoot hRoot hRwx hNone rfl
  dsimp only at hRun; erw [hRun]; dsimp only; rw [allPass_assert_end]; exact ⟨⟨_, rfl, rfl, by simp [Internal.mapFsError]⟩, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 3 (`test_tempdir_withTempDir_cleanupErrorReturnedOnOk`). -/
theorem reach_tempdir_withTempDir_cleanupErrorReturnedOnOk :
    CanReach (test_tempdir_withTempDir_cleanupErrorReturnedOnOk (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀; refine ⟨s₀, "/tmp", "tmp-", 1, ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]
  exact ⟨hNone, by have hp := proof_tempdir_withTempDir_cleanupErrorReturnedOnOk s₀ "/tmp" "tmp-" 1 ⟨rfl, rfl⟩ hRoot; dsimp only [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; exact hp hNone⟩
/-- Spec 4: Exclusive creation rejects pre-existing directories or symlinks at `<root>/<dirPrefix><uuid>` with `.alreadyExists` without running `action` or deleting the existing entry. -/
theorem proof_tempdir_withTempDir_collisionRejected :
    AllPass (test_tempdir_withTempDir_collisionRejected (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_collisionRejected, AllPass]; intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarkerNone
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; rintro ⟨stExist, hExist, _⟩; rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hExist
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u); let sUuid : TempDirMockState := { s₀ with nextUuid := s₀.nextUuid + 1 }
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode sUuid.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem, sUuid] using hLookRoot
  obtain ⟨ndExist, hLookExist, _⟩ := lookupNode_of_lstat_ok sUuid dir stExist hExist; have hRes := resolveRoot_some_ok_run (fun _ s => mockFs_stat_run s _) s₀ root hvr stRoot hRoot hRwx.1
  have hMk : (mockFs.mkdir dir false false).run sUuid = (.error { kind := .alreadyExists, path := some dir, message := "exists" }, sUuid) := by
    dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash]; dsimp only; rw [hLookRootNorm]; dsimp only; rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte, hasWx_of_hasRwx stRoot hRwx, Bool.not_true, mockJoin_normKey]; rw [hLookExist]; cases ndExist <;> exact stateM_pure_run _ _
  have hCre : (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.error (Internal.mapFsError { kind := .alreadyExists, path := some dir, message := "exists" }), sUuid) := by
    dsimp only [Internal.createTempDir]; have hvp' : Internal.validPrefix dirPrefix = true := hvp; simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]; dsimp only; rw [stateM_bind_run, mockUuid_getUuid_run]; dsimp only; rw [mockFs_join_eq, mockUuid_toString_eq, stateM_bind_run, hMk, stateM_pure_run]
  rw [mkApiM_withTempDir_eq]; dsimp only [Internal.withTempDirM]; rw [stateM_bind_run, hCre]; dsimp only; rw [stateM_pure_run]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨⟨_, rfl, rfl⟩, by rw [mockFs_lstat_run] at hMarkerNone ⊢; exact hMarkerNone, by rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq, hExist]; rfl, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 4 (`test_tempdir_withTempDir_collisionRejected`). -/
theorem reach_tempdir_withTempDir_collisionRejected :
    CanReach (test_tempdir_withTempDir_collisionRejected (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_collisionRejected, CanReach]; let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = { nodes := [(dir, .dir 0 0o700), ("/tmp", .dir 0 0o755)] } := ⟨_, rfl⟩
  have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl; have hDirNeRoot : normKey dir ≠ normKey "/tmp" := mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [hs₀, mockFs_stat_run]; unfold mockStatPure mockLstatPure; rw [lookupNode_cons_ne dir _ _ "/tmp" hDirNeRoot]; rfl, rfl, rfl, rfl, rfl⟩
  have hM : ((mockFs.lstat "/").run s₀).1.isOk = false := by
    rw [hs₀, mockFs_lstat_run]; unfold mockLstatPure; rw [lookupNode_cons_ne _ _ _ _ (by rw [normKey_mockJoin "/tmp" _ hcNe hcNoSlash, show normKey "/" = "/" from rfl]; exact mockJoin_ne_slash "/tmp" _ (by decide) hcNe), lookupNode_cons_ne _ _ _ _ (by decide)]; rfl
  have hExist : ∃ stExist, ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run { s₀ with nextUuid := s₀.nextUuid + 1 }).1 = .ok stExist ∧ (stExist.kind = .dir ∨ stExist.kind = .symlink) :=
    ⟨mockNodeStat (.dir 0 0o700), by rw [hs₀, mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; unfold mockLstatPure; rw [lookupNode_cons_eq _ _ _ _ rfl], Or.inl rfl⟩
  refine ⟨s₀, "/tmp", "tmp-", "/", ⟨rfl, rfl⟩, hRoot, hM, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]
  exact ⟨hExist, by have hp := proof_tempdir_withTempDir_collisionRejected s₀ "/tmp" "tmp-" "/" ⟨rfl, rfl⟩ hRoot hM; dsimp only [test_tempdir_withTempDir_collisionRejected, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; exact hp hExist⟩
private theorem spec5_create_err (s₀ : TempDirMockState) (root dirPrefix : String) (fsBad : FsApiM (StateM TempDirMockState))
    (hJoin : fsBad.join = mockJoin) (hStat : ∀ p s, (fsBad.stat p).run s = (mockStatPure s p, s)) (hMkdir : fsBad.mkdir = mockFs.mkdir)
    (hChmod : ∀ p m, fsBad.chmod p m = pure (.error { kind := .permissionDenied, path := some p, message := "chmod denied" })) (hRm : fsBad.rmtree = mockRmtreePure)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true) (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNoneP : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    ∃ sFin : TempDirMockState, sFin.nodes = ({ nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } : TempDirMockState).nodes.filter (fun e => !underDir dir e.1) ∧
      (Internal.createTempDir fsBad mockUuid mockEnv (some root) dirPrefix).run s₀ = (.error (Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "chmod denied" }), sFin) := by
  intro dir; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s₀.nextUuid) hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by unfold mockLstatPure at hNoneP; cases hl : lookupNode s₀.nodes dir with | none => rfl | some _ => rw [hl] at hNoneP; simp [Except.isOk, Except.toBool] at hNoneP
  have hRes := resolveRoot_some_ok_run hStat s₀ root hvr stRoot hRoot hRwx.1
  obtain ⟨sMkdir, hsMkdir⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (fsBad.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (), sMkdir) := by dsimp only [dir] at hsMkdir ⊢; rw [hMkdir, hsMkdir]; exact mockFs_mkdir_fresh_run _ root _ hrNe hcNe hcNoSlash rootNode stRoot hLookRootNorm hStRoot hRwx hLookDirNone
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s = { sMkdir with nodes := sMkdir.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCln : (Internal.cleanupDirIgnoringNotFound fsBad dir).run sMkdir = (.ok (), sFin) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound]; rw [stateM_bind_run, hRm]; dsimp only [mockRmtreePure]; rw [stateM_bind_run, stateM_get_run]; dsimp only
    rw [hDirNorm, show lookupNode sMkdir.nodes dir = some (.dir s₀.nowSec 0o755) by rw [hsMkdir]; exact lookupNode_cons_eq _ _ _ _ rfl]; simp only [stateM_bind_run, stateM_set_run, stateM_pure_run, hsFin]; dsimp only [dir]
  refine ⟨sFin, by rw [hsFin, hsMkdir], ?_⟩; dsimp only [Internal.createTempDir]; simp only [show Internal.validPrefix dirPrefix = true from hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hRes]
  rw [mockUuid_getUuid_run]; dsimp only; rw [mockUuid_toString_eq, hJoin, stateM_bind_run]; dsimp only [dir] at hMk hCln ⊢; rw [hMk]; dsimp only; rw [stateM_bind_run, hChmod, stateM_pure_run]; dsimp only; rw [stateM_bind_run, hCln]; exact stateM_pure_run _ _
/-- Spec 5: If `fs.chmod dir 0o700` fails right after `fs.mkdir`, `withTempDir` rolls back `dir` without running `action`. -/
theorem proof_tempdir_withTempDir_chmodFailureRollsBack :
    AllPass (test_tempdir_withTempDir_chmodFailureRollsBack (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_chmodFailureRollsBack, AllPass]; intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarkerNone
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq, mockFs_lstat_run] at hNone
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u); have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  let fsBad : FsApiM (StateM TempDirMockState) := { mockFs with chmod := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "chmod denied" }) }
  obtain ⟨sFin, hsFinNodes, hCre⟩ := spec5_create_err s₀ root dirPrefix fsBad rfl (fun p s => mockFs_stat_run s p) rfl (fun _ _ => rfl) rfl hvr hvp stRoot hRoot hRwx hNone
  rw [mkApiM_withTempDir_eq, withTempDirM_create_err fsBad mockUuid mockEnv s₀ sFin (some root) dirPrefix _ _ hCre]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]
  have hGone : lookupNode sFin.nodes dir = none := by rw [hsFinNodes]; exact lookupNode_filter_underDir_eq _ _ hDirNorm
  have hMarkerNone' : lookupNode s₀.nodes markerPath = none := by rw [mockFs_lstat_run] at hMarkerNone; unfold mockLstatPure at hMarkerNone; cases hl : lookupNode s₀.nodes markerPath with | none => rfl | some _ => simp [hl, Except.isOk, Except.toBool] at hMarkerNone
  have hMarkerOut : ((mockFs.lstat markerPath).run sFin).1.isOk = false := by
    apply mockFs_lstat_isOk_false_of_lookup_none; by_cases hEq : normKey dir = normKey markerPath
    · unfold lookupNode at hGone ⊢; rw [← hEq, hDirNorm]; rw [hDirNorm] at hGone; exact hGone
    · rw [hsFinNodes]; apply lookupNode_filter_none_of_none; unfold lookupNode; rw [List.find?_cons]; dsimp only; rw [beq_false_of_ne hEq]; exact lookupNode_filter_none_of_none _ _ _ hMarkerNone'
  exact ⟨⟨_, rfl, rfl⟩, hMarkerOut, mockFs_lstat_isOk_false_of_lookup_none sFin dir hGone, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 5 (`test_tempdir_withTempDir_chmodFailureRollsBack`). -/
theorem reach_tempdir_withTempDir_chmodFailureRollsBack :
    CanReach (test_tempdir_withTempDir_chmodFailureRollsBack (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_chmodFailureRollsBack, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  have hM : ((mockFs.lstat "/").run s₀).1.isOk = false := by rw [hs₀, mockFs_lstat_run]; unfold mockLstatPure; rw [lookupNode_cons_ne _ _ _ _ (by decide)]; rfl
  refine ⟨s₀, "/tmp", "tmp-", "/", ⟨rfl, rfl⟩, hRoot, hM, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]
  exact ⟨hNone, by have hp := proof_tempdir_withTempDir_chmodFailureRollsBack s₀ "/tmp" "tmp-" "/" ⟨rfl, rfl⟩ hRoot hM; dsimp only [test_tempdir_withTempDir_chmodFailureRollsBack, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; exact hp hNone⟩
/-- Spec 6: All three operations reject invalid `dirPrefix` and invalid explicit `root?` with `.invalidInput` without modifying state. -/
theorem proof_tempdir_validation_rejectsInvalidInputs :
    AllPass (test_tempdir_validation_rejectsInvalidInputs (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_validation_rejectsInvalidInputs, AllPass]; intro s₀ root dirPrefix hInv
  by_cases hvp : Internal.validPrefix dirPrefix = true
  · have hvr : Internal.validRoot root = false := by rcases hInv with h | h <;> first | exact absurd hvp h | exact Bool.eq_false_iff.mpr fun ht => h ht
    have hRes : (Internal.resolveRoot mockFs mockEnv (some root)).run s₀ = (.error { kind := .invalidInput, path := some root, message := "invalid temporary root path" }, s₀) := by
      dsimp only [Internal.resolveRoot]; rw [stateM_bind_run, stateM_pure_run]; dsimp only; simp only [hvr, Bool.not_false, ↓reduceIte, stateM_pure_run]
    have ⟨h1, h2, h3⟩ := allThree_of_resolveRoot_err s₀ s₀ (some root) dirPrefix _ hvp hRes (fun _ => pure (.ok () : Except TempDirError Unit))
    rw [h1, h2, h3]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]; have hMsg : ("invalid temporary root path" : String) ≠ "" := by decide
    exact ⟨⟨_, rfl, rfl, hMsg⟩, ⟨_, rfl, rfl, hMsg⟩, ⟨_, rfl, rfl, hMsg⟩, ⟨rfl, rfl, rfl⟩, trivial⟩
  · obtain ⟨⟨e1, h1, hk1, hm1⟩, ⟨e2, h2, hk2, hm2⟩, ⟨e3, h3, hk3, hm3⟩⟩ := allThree_of_validPrefix_false s₀ (some root) dirPrefix (Bool.eq_false_iff.mpr hvp) (fun _ => pure (.ok () : Except TempDirError Unit))
    rw [h1, h2, h3]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]; exact ⟨⟨e1, rfl, hk1, hm1⟩, ⟨e2, rfl, hk2, hm2⟩, ⟨e3, rfl, hk3, hm3⟩, ⟨rfl, rfl, rfl⟩, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 6 (`test_tempdir_validation_rejectsInvalidInputs`). -/
theorem reach_tempdir_validation_rejectsInvalidInputs :
    CanReach (test_tempdir_validation_rejectsInvalidInputs (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) :=
  ⟨{}, "/tmp", "../bad", Or.inl (by decide), proof_tempdir_validation_rejectsInvalidInputs {} "/tmp" "../bad" (Or.inl (by decide))⟩
private theorem spec7_ok_allPass (s₀ : TempDirMockState) (r dirPrefix : String) (hR : r = match s₀.tmpdir with | some v => if v.isEmpty then "/tmp" else v | none => "/tmp")
    (hvr : (!r.isEmpty && !(Char.ofNat 0 ∈ r.toList)) = true) (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (st : FileStat) (hStat : mockStatPure s₀ r = .ok st) (hRwx : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1)
    (hNone : ((mockFs.lstat (mockFs.join r (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false) :
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv; let expectedDir := mockFs.join r (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid))
    (match (api.withTempDir none dirPrefix fun d => pure (Except.ok d)).run s₀ with | (r1, _) => match (api.withLockedTempDir none dirPrefix fun d => pure (Except.ok d)).run s₀ with
    | (r2, _) => match (api.cleanupStaleTempDirs none dirPrefix 86400).run s₀ with
    | (r3, _) => ((do NondetTest.assert (r1 = Except.ok expectedDir); NondetTest.assert (r2 = Except.ok expectedDir); NondetTest.assert (r3.isOk = true) : AllPassRun Unit) (fun _ => True))) := by
  intro api expectedDir; rw [mockFs_join_eq, mockUuid_toString_eq] at hNone
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin r (dirPrefix ++ mockUuidToString u)
  have hrNe := validRoot_ne_empty r hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin r _ hcNe hcNoSlash
  have hDirNe := mockJoin_ne_empty r _ hcNe; have hDirNeSlash := mockJoin_ne_slash r _ hrNe hcNe; have hRes := resolveRoot_none_ok_run (fun _ s => mockFs_stat_run s _) s₀ r hR hvr st hStat hRwx.1
  have hCre := createTempDir_ok_run createFsOps_mockFs s₀ none r dirPrefix hRes hvr hvp st hStat hRwx (by rw [mockFs_lstat_run] at hNone; exact hNone); dsimp only at hCre
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCre; have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFin1, hsFin1⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCln1 := cleanupDir_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩; rw [← hsFin1] at hCln1
  have hRun1 := withTempDirM_run mockFs mockUuid mockEnv s₀ sMk sMk sFin1 none dirPrefix dir (fun d => pure (Except.ok d)) (.ok dir) (.ok ()) hCre (stateM_pure_run _ _) hCln1
  let lockPath := mockJoin dir ".lock"; have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir := payload_ne_dir r _ ".lock" hrNe hcNe hcNoSlash (by decide) (by decide); have hUnderLock := underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by rw [hsMk]; exact lookupNode_lock_mk_none s₀.nodes dir _ hDirNorm hLockNeDir hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks), nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAfterLock, lookupNode_cons_lock_dir sMk.nodes dir _ hDirNorm hLockNeDir]; exact hLookDirMk
  have hCln2 := cleanupDir_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  have hRun2 : (Internal.withLockedTempDirM mockFs mockUuid mockEnv none dirPrefix fun d => pure (Except.ok d)).run s₀ = (.ok dir, { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM]; rw [stateM_bind_run, hCre]; dsimp only; rw [stateM_bind_run, stateM_tryFinally'_run, stateM_bind_run, mockFs_join_eq]
    rw [show mockJoin dir ".lock" = lockPath from rfl, mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]; dsimp only; simp only [stateM_bind_run, stateM_pure_run]
    rw [← hsAfterLock]; dsimp only [dir, u] at hCln2 ⊢; rw [hCln2]; exact stateM_pure_run _ _
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ r st hStat; have hLookRootNorm : lookupNode s₀.nodes (normKey r) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  let names := (Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey r) e.1)))).toArray
  have hList : (mockFs.listDir r).run s₀ = (.ok names, s₀) := by
    dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hLookRootNorm]; dsimp only; rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte, hasRx_of_hasRwx st hRwx, Bool.not_true, stateM_pure_run]; rfl
  dsimp only [expectedDir]; rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [show api = Internal.mkApiM mockFs mockTime mockUuid mockEnv from rfl, mkApiM_withTempDir_eq, mkApiM_withLockedTempDir_eq, mkApiM_cleanupStaleTempDirs_eq]
  rw [hRun1, hRun2]; dsimp only; simp only [allPass_assert, allPass_assert_end]
  cases hC : (Internal.cleanupStaleTempDirsM mockFs mockTime mockEnv none dirPrefix 86400).run s₀ with | mk r3 s3 =>
  refine ⟨rfl, rfl, ?_, trivial⟩
  have hResC : r3.isOk = true := by
    have hEq : r3 = ((Internal.cleanupStaleTempDirsM mockFs mockTime mockEnv none dirPrefix 86400).run s₀).1 := by rw [hC]
    rw [hEq]
    dsimp only [Internal.cleanupStaleTempDirsM]; simp only [show Internal.validPrefix dirPrefix = true from hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]; dsimp only; let nowTs := (mockTime.nowTimestamp.run s₀).1; have hTime : mockTime.nowTimestamp.run s₀ = (nowTs, s₀) := rfl
    rw [stateM_bind_run, hTime]; dsimp only; rw [stateM_bind_run, hList]; dsimp only; rw [stateM_bind_run]
    cases (Internal.sweepEntries mockFs r dirPrefix 86400 nowTs.toSecondsSinceUnixEpoch.val {} names.toList).run s₀ with | mk _ _ => rw [stateM_pure_run]; rfl
  exact hResC
/-- Spec 7: With `root? = none`, all three operations resolve non-empty `TMPDIR`, reject NUL `TMPDIR` with `.invalidInput`, reject missing/non-dir `TMPDIR` strictly, and fall back to `"/tmp"` when `TMPDIR` is unset or empty. -/
theorem proof_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing :
    AllPass (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing, AllPass]; intro s₀ dirPrefix hvp
  have hvp' : Internal.validPrefix dirPrefix = true := hvp; have hEnv : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := rfl
  rw [hEnv]; dsimp only; rw [mockUuid_getUuid_run s₀]; dsimp only
  cases ht : s₀.tmpdir with
  | none => dsimp only; rw [allPass_assume]; rintro ⟨stTmp, hStatTmp, hRwx⟩; rw [allPass_assume]; intro hNone; rw [mockFs_stat_run] at hStatTmp; exact spec7_ok_allPass s₀ "/tmp" dirPrefix (by rw [ht]) (by decide) hvp stTmp hStatTmp hRwx hNone
  | some tmpdir =>
    by_cases hEmpty : (!tmpdir.isEmpty) = true
    · simp only [hEmpty, ↓reduceIte]; have hEmptyF : tmpdir.isEmpty = false := by simpa using hEmpty
      by_cases hNul : Char.ofNat 0 ∈ tmpdir.toList
      · simp only [hNul, ↓reduceIte]
        have hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error { kind := .invalidInput, path := some tmpdir, message := "invalid temporary root path" }, s₀) := by
          dsimp only [Internal.resolveRoot]; rw [stateM_bind_run, hEnv, ht]; dsimp only; simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
          simp only [show Internal.validRoot tmpdir = false by simp [Internal.validRoot, hNul], Bool.not_false, ↓reduceIte]; rfl
        have ⟨h1, h2, h3⟩ := allThree_of_resolveRoot_err s₀ s₀ none dirPrefix _ hvp' hRes (fun _ => pure (.ok () : Except TempDirError Unit))
        rw [h1, h2, h3]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]; exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
      · simp only [hNul, ↓reduceIte]; have hvr : (!tmpdir.isEmpty && !(Char.ofNat 0 ∈ tmpdir.toList)) = true := by simp [hEmpty, hNul]
        have hResStart : ∀ mRes : Except FsError FileStat, mockStatPure s₀ tmpdir = mRes →
            (Internal.resolveRoot mockFs mockEnv none).run s₀ = (match mRes with | .error fe => .error (Internal.mapFsError fe) | .ok st => if st.kind != .dir then .error { kind := .notADirectory, path := some tmpdir, message := "temporary root is not a directory" } else .ok tmpdir, s₀) := by
          intro mRes hm; dsimp only [Internal.resolveRoot]; rw [stateM_bind_run, hEnv, ht]; dsimp only; simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
          simp only [show Internal.validRoot tmpdir = true from hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, mockFs_stat_run, hm]
          cases mRes with | error _ => rfl | ok st => dsimp only; by_cases hk : (st.kind != EntryKind.dir) = true <;> simp only [hk, Bool.false_eq_true, ↓reduceIte] <;> rfl
        rw [mockFs_stat_run, show mockStatPure { s₀ with tmpdir := some tmpdir, nextUuid := s₀.nextUuid + 1 } tmpdir = mockStatPure s₀ tmpdir from rfl]
        cases hStat : mockStatPure s₀ tmpdir with
        | error fe =>
          have hRes := hResStart (.error fe) hStat; dsimp only at hRes; have ⟨h1, h2, h3⟩ := allThree_of_resolveRoot_err s₀ s₀ none dirPrefix _ hvp' hRes (fun _ => pure (.ok () : Except TempDirError Unit))
          rw [h1, h2, h3]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]
          have hKind : fe.kind ≠ .notFound ∨ (Internal.mapFsError fe).kind = .notFound := if hk : fe.kind = .notFound then Or.inr (by simp [Internal.mapFsError, hk]) else Or.inl hk
          exact ⟨⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, trivial⟩
        | ok st =>
          by_cases hk : (st.kind != EntryKind.dir) = true
          · simp only [hk, ↓reduceIte]; have hRes := hResStart (.ok st) hStat; dsimp only at hRes; simp only [hk, ↓reduceIte] at hRes
            have ⟨h1, h2, h3⟩ := allThree_of_resolveRoot_err s₀ s₀ none dirPrefix _ hvp' hRes (fun _ => pure (.ok () : Except TempDirError Unit))
            rw [h1, h2, h3]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert_end]; exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, trivial⟩
          · simp only [hk, Bool.false_eq_true, ↓reduceIte]; rw [allPass_assume]; intro hRwx; rw [allPass_assume]; intro hNone; exact spec7_ok_allPass s₀ tmpdir dirPrefix (by rw [ht]; simp [hEmptyF]) hvr hvp st hStat hRwx hNone
    · simp only [hEmpty, Bool.false_eq_true, ↓reduceIte]; rw [allPass_assume]; rintro ⟨stTmp, hStatTmp, hRwx⟩; rw [allPass_assume]; intro hNone; rw [mockFs_stat_run] at hStatTmp
      exact spec7_ok_allPass s₀ "/tmp" dirPrefix (by rw [ht]; simp [show tmpdir.isEmpty = true by simpa using hEmpty]) (by decide) hvp stTmp hStatTmp hRwx hNone
/-- Non-vacuity `CanReach` witness for Spec 7 (`test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing`). -/
theorem reach_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing :
    CanReach (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hTmp := defaultRoot_afterUuid_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  refine ⟨s₀, "tmp-", rfl, ?_⟩; rw [show (mockEnv.getEnv "TMPDIR").run s₀ = (.ok none, s₀) from by rw [hs₀]; rfl]; dsimp only; rw [mockUuid_getUuid_run s₀]; dsimp only
  rw [canReach_assume]; refine ⟨hTmp, ?_⟩; rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hp := proof_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing s₀ "tmp-" rfl; dsimp only [test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing, AllPass] at hp
  rw [show (mockEnv.getEnv "TMPDIR").run s₀ = (.ok none, s₀) from by rw [hs₀]; rfl] at hp; dsimp only at hp; rw [mockUuid_getUuid_run s₀] at hp; dsimp only at hp
  rw [allPass_assume] at hp; have hp1 := hp hTmp; rw [allPass_assume] at hp1; exact hp1 hNone
end LeanSwe.TempDir.Proofs
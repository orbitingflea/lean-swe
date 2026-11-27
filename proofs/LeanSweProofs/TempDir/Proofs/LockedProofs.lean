import LeanSweProofs.TempDir.Proofs.Shared
import LeanSweProofs.TempDir.Proofs.WithTempDirProofs
set_option Elab.async false
/-!
Verification of `LeanSwe.TempDir` locked temporary directory and exception-safety
specifications (Specs 8–10) and their `CanReach` witnesses.
-/
namespace LeanSwe.TempDir.Proofs
open Core Core.NondetTest LeanSwe.Time LeanSwe.Uuid LeanSwe.EnvVars
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
private theorem foldl_max_ge_init (xs : List (Nat × LockMode)) (init : Nat) : init ≤ xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with | nil => exact Nat.le_refl init | cons y ys ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left init (y.1 + 1)) (ih _)
private theorem foldl_max_gt_mem (xs : List (Nat × LockMode)) (init : Nat) (x : Nat × LockMode) (hx : x ∈ xs) :
    x.1 < xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with | nil => simp at hx | cons y ys ih =>
    simp only [List.foldl_cons]; cases List.mem_cons.mp hx with
    | inl hxy => subst hxy; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) (Nat.le_max_right init (x.1 + 1))) (foldl_max_ge_init ys _)
    | inr hmem => exact ih (Nat.max init (y.1 + 1)) hmem
private theorem mockHasConflict_fresh (locks : List (Nat × LockMode)) (ino : Nat) (mode : LockMode) (hFresh : ∀ x ∈ locks, x.1 < ino) : mockHasConflict locks ino mode = false := by
  unfold mockHasConflict; rw [List.any_eq_false]; intro x hx hTrue; have hlt := hFresh x hx; have heq : x.1 = ino := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hTrue).1; omega
/-- Remove matching lock at the head of the lock list. -/
theorem mockRemoveFirstLock_head (ino : Nat) (m : LockMode) (locks : List (Nat × LockMode)) : mockRemoveFirstLock ino m ((ino, m) :: locks) = locks := by
  unfold mockRemoveFirstLock; have hm : (m == m) = true := by cases m <;> rfl
  have heq : ((ino, m) == (ino, m)) = true := by change (ino == ino && m == m) = true; rw [beq_self_eq_true, hm]; rfl
  rw [heq]; rfl
/-- Normalized child directory path is never under-equal to its parent root. -/
theorem underDir_mockJoin_root_false (root child : String) (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList) :
    underDir (mockJoin root child) root = false := not_underDir_mockJoin_root root child root hrNe hcNe hcNoSlash rfl
private theorem lookupNode_filter_not_underDir_eq (nodes : List (String × MockNode)) (d q : String) (hFalse : underDir d q = false) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) q = lookupNode nodes q := by
  induction nodes with | nil => rfl | cons x xs ih =>
    cases hb : (normKey x.1 == normKey q) with
    | true => have hux : underDir d x.1 = false := by simpa [underDir, beq_iff_eq.mp hb] using hFalse
              simp [lookupNode, hux, hb]
    | false => simp only [lookupNode, List.find?_cons, hb]; rw [List.filter_cons]; split <;> first | (simp only [List.find?_cons, hb]; exact ih) | exact ih
private theorem lookupNode_after_cleanup_root (nodes : List (String × MockNode)) (dir lockPath root : String) (ndL ndD : MockNode)
    (hNotUnder : underDir dir (normKey root) = false) (hb1 : (normKey lockPath == normKey (normKey root)) = false) (hb2 : (normKey dir == normKey (normKey root)) = false) :
    lookupNode ((lockPath, ndL) :: (dir, ndD) :: nodes.filter (fun e => !underDir dir e.1)) (normKey root) = lookupNode nodes (normKey root) := by
  unfold lookupNode; rw [List.find?_cons]; dsimp only; rw [hb1]; dsimp only; rw [List.find?_cons]; dsimp only; rw [hb2]; exact lookupNode_filter_not_underDir_eq nodes dir (normKey root) hNotUnder
/-- Re-creating `<root>/<child>` and acquiring `.exclusive` on `.lock` succeeds after cleanup. -/
theorem probe_exclusive_lock_after_cleanup_run (s : TempDirMockState) (root child : String) (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (rootNode : MockNode) (stRoot : FileStat) (hLookRoot : lookupNode s.nodes (normKey root) = some rootNode) (hStRoot : mockNodeStat rootNode = stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1) (hLookDir : lookupNode s.nodes (mockJoin root child) = none) :
    ((do let _ ← mockFs.mkdir (mockJoin root child) false false; mockFs.tryWithFileLock (mockJoin (mockJoin root child) ".lock") .exclusive true (pure (.ok ()))).run s).1 = .ok (some ()) := by
  let dir := mockJoin root child; let lockPath := mockJoin dir ".lock"; have hDirNorm := normKey_mockJoin root child hcNe hcNoSlash
  have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide); have hLockNeDir := payload_ne_dir root child ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock := underDir_mockJoin_self dir ".lock" (mockJoin_ne_empty root child hcNe) hDirNorm (mockJoin_ne_slash root child hrNe hcNe) (by decide) (by decide)
  obtain ⟨s1, hs1⟩ : ∃ s' : TempDirMockState, s' = { s with nodes := (dir, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (mockFs.mkdir dir false false).run s = (.ok (), s1) := by dsimp only [dir] at hs1 ⊢; rw [hs1]; exact mockFs_mkdir_fresh_run s root child hrNe hcNe hcNoSlash rootNode stRoot hLookRoot hStRoot hRwx hLookDir
  have hLookLock1 : lookupNode s1.nodes lockPath = none := by rw [hs1]; exact lookupNode_lock_mk_none s.nodes dir _ hDirNorm hLockNeDir hUnderLock
  rw [stateM_bind_run, hMk]; dsimp only; dsimp only [lockPath, dir] at hLockNorm hLookLock1; rw [mockFs_tryWithFileLock_create_run s1 _ .exclusive hLockNorm hLookLock1]; dsimp only; rw [stateM_pure_run]; rfl
private def spec8MkState (s₀ : TempDirMockState) (root dirPrefix : String) : TempDirMockState :=
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
private def spec8LockState (s₀ : TempDirMockState) (root dirPrefix : String) : TempDirMockState :=
  let sMk := spec8MkState s₀ root dirPrefix; let lockPath := mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock"
  { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := (freshInode sMk, .shared) :: sMk.locks, nextInode := freshInode sMk + 1 }
private theorem spec8_lockState_probes (s₀ : TempDirMockState) (root dirPrefix : String) (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)); let lockPath := mockJoin dir ".lock"; let sMk := spec8MkState s₀ root dirPrefix; let sLock := spec8LockState s₀ root dirPrefix
    ((mockFs.lstat dir).run sLock = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sLock)) ∧ ((mockFs.lstat lockPath).run sLock = (.ok (mockNodeStat (.file (freshInode sMk) "" sMk.nowSec 0o644)), sLock)) ∧
    ((mockFs.tryWithFileLock lockPath .shared false (pure (.ok ()))).run sLock = (.ok (some ()), sLock)) ∧ ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sLock = (.ok none, sLock)) := by
  intro dir lockPath sMk sLock; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s₀.nextUuid) hvp
  have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash; have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir := payload_ne_dir root _ ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    change lookupNode ((lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes) dir = _; rw [lookupNode_cons_lock_dir sMk.nodes dir _ hDirNorm hLockNeDir]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockLock : lookupNode sLock.nodes lockPath = some (.file (freshInode sMk) "" sMk.nowSec 0o644) := lookupNode_cons_eq _ _ _ _ rfl
  have hNoConfShared : mockHasConflict sLock.locks (freshInode sMk) .shared = false := by
    change mockHasConflict ((freshInode sMk, .shared) :: sMk.locks) (freshInode sMk) .shared = false
    unfold mockHasConflict; simp only [List.any_cons, beq_self_eq_true, show (LockMode.shared == LockMode.exclusive) = false from rfl, Bool.and_false, Bool.false_or]
    exact mockHasConflict_fresh sMk.locks (freshInode sMk) .shared fun x hx => foldl_max_gt_mem sMk.locks sMk.nextInode x hx
  have hConfEx : mockHasConflict sLock.locks (freshInode sMk) .exclusive = true := by
    change mockHasConflict ((freshInode sMk, .shared) :: sMk.locks) (freshInode sMk) .exclusive = true
    unfold mockHasConflict; simp only [List.any_cons, beq_self_eq_true, show (LockMode.exclusive == LockMode.exclusive) = true from rfl, Bool.true_or, Bool.and_self]
  refine ⟨by rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookDirLock], by rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockLock], ?_, ?_⟩
  · rw [mockFs_tryWithFileLock_existing_ok_run sLock lockPath .shared false (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hNoConfShared (pure (.ok ()))]; simp only [stateM_pure_run, mockRemoveFirstLock_head]; rfl
  · exact mockFs_tryWithFileLock_existing_conflict_run sLock lockPath .exclusive false (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hConfEx (pure (.ok ()))
private theorem root_preserved_after_cleanup (s₀ sFin : TempDirMockState) (dir lockPath root : String) (ndL ndD rootNode : MockNode)
    (hDirNorm : normKey dir = dir) (hUnderLock : underDir dir lockPath = true) (hRootNotUnder : underDir dir (normKey root) = false)
    (hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode) (hFinNodes : sFin.nodes = ((lockPath, ndL) :: (dir, ndD) :: s₀.nodes.filter (fun e => !underDir dir e.1)).filter (fun e => !underDir dir e.1)) :
    lookupNode sFin.nodes (normKey root) = some rootNode := by
  have hb1 : (normKey lockPath == normKey (normKey root)) = false := beq_false_of_ne fun hEq => by have h1 : underDir dir lockPath = underDir dir (normKey root) := (by unfold underDir; rw [hEq]); rw [hUnderLock, hRootNotUnder] at h1; exact Bool.noConfusion h1
  have hb2 : (normKey dir == normKey (normKey root)) = false := beq_false_of_ne fun hEq => by have h1 : underDir dir dir = underDir dir (normKey root) := (by unfold underDir; rw [hEq]); rw [underDir_refl dir hDirNorm, hRootNotUnder] at h1; exact Bool.noConfusion h1
  rw [hFinNodes, lookupNode_filter_not_underDir_eq _ dir (normKey root) hRootNotUnder]; exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root ndL ndD hRootNotUnder hb1 hb2).trans hLookRootNorm
private theorem withLockedTempDir_exec {α : Type} (s₀ : TempDirMockState) (root dirPrefix : String) (act : String → StateM TempDirMockState (Except TempDirError α))
    (res : Except TempDirError α) (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hAct : (act (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).run (spec8LockState s₀ root dirPrefix) = (res, spec8LockState s₀ root dirPrefix)) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)); let lockPath := mockJoin dir ".lock"
    ∃ sFin : TempDirMockState, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix act).run s₀ = (res, sFin) ∧
      ((mockFs.lstat dir).run sFin).1.isOk = false ∧ (∃ e, ((mockFs.lstat lockPath).run sFin).1 = .error e ∧ e.kind = .notFound) ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sFin).1 = .ok (some ()) := by
  intro dir lockPath; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s₀.nextUuid) hvp
  have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash; have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide); have hLockNeDir := payload_ne_dir root _ ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock := underDir_mockJoin_self dir ".lock" (mockJoin_ne_empty root _ hcNe) hDirNorm (mockJoin_ne_slash root _ hrNe hcNe) (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by simpa [underDir, normKey_idem] using underDir_mockJoin_root_false root _ hrNe hcNe hcNoSlash
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  have hRes := resolveRoot_some_ok_run (fun _ s => mockFs_stat_run s _) s₀ root hvr stRoot hRoot hRwx.1
  have hCreate := createTempDir_ok_run createFsOps_mockFs s₀ (some root) root dirPrefix hRes hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCreate
  let sMk := spec8MkState s₀ root dirPrefix; let sLock := spec8LockState s₀ root dirPrefix
  have hsMk : sMk = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := rfl
  rw [← hsMk] at hCreate; have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by rw [hsMk]; exact lookupNode_lock_mk_none s₀.nodes dir _ hDirNorm hLockNeDir hUnderLock
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by change lookupNode ((lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes) dir = _; rw [lookupNode_cons_lock_dir sMk.nodes dir _ hDirNorm hLockNeDir]; exact hLookDirMk
  obtain ⟨sAfter, hsAfter⟩ : ∃ s : TempDirMockState, s = { sLock with locks := mockRemoveFirstLock (freshInode sMk) .shared sLock.locks } := ⟨_, rfl⟩
  have hLookDirAfter : lookupNode sAfter.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAfter]; exact hLookDirLock
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s = { sAfter with nodes := sAfter.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean := cleanupDir_mock_run sAfter dir hDirNorm ⟨_, _, hLookDirAfter⟩; rw [← hsFin] at hClean
  have hWfl : (mockFs.withFileLock lockPath .shared true (act dir >>= fun r => pure (Except.ok r : Except FsError (Except TempDirError α)))).run sMk = (.ok res, sAfter) := by
    dsimp only [dir, lockPath] at hLockNorm hLookLockMk hAct ⊢; rw [mockFs_withFileLock_create_run sMk _ .shared hLockNorm hLookLockMk]; dsimp only
    change (let (r, s2) := (act (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) >>= fun r => pure (Except.ok r : Except FsError (Except TempDirError α))).run sLock; (r, { s2 with locks := mockRemoveFirstLock (freshInode sMk) .shared s2.locks })) = (.ok res, sAfter)
    rw [stateM_bind_run, hAct, stateM_pure_run]; dsimp only; rw [hsAfter]
  have hRun : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix act).run s₀ = (res, sFin) := by
    rw [mkApiM_withLockedTempDir_eq]; dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM]; rw [stateM_bind_run, hCreate]; dsimp only; rw [stateM_bind_run, stateM_tryFinally'_run, mockFs_join_eq]
    dsimp only [dir, lockPath] at hWfl hClean ⊢; rw [stateM_bind_run, hWfl]; dsimp only; simp only [stateM_pure_run]; rw [hClean]; dsimp only; cases res <;> rfl
  have hLookDirFin : lookupNode sFin.nodes dir = none := by rw [hsFin]; exact lookupNode_filter_none_of_underDir sAfter.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookLockFin : lookupNode sFin.nodes lockPath = none := by rw [hsFin]; exact lookupNode_filter_none_of_underDir sAfter.nodes dir lockPath hUnderLock
  have hsLock : sLock = { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := (freshInode sMk, .shared) :: sMk.locks, nextInode := freshInode sMk + 1 } := rfl
  have hLookRootFin := root_preserved_after_cleanup s₀ sFin dir lockPath root (.file (freshInode sMk) "" sMk.nowSec 0o644) (.dir s₀.nowSec 0o700) rootNode hDirNorm hUnderLock hRootUnderDirFalse hLookRootNorm (by rw [hsFin, hsAfter, hsLock, hsMk])
  refine ⟨sFin, hRun, mockFs_lstat_isOk_false_of_lookup_none sFin dir hLookDirFin, ⟨{ kind := .notFound, path := some lockPath, message := "not found" }, by rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockFin], rfl⟩,
    by dsimp only [dir, lockPath]; exact probe_exclusive_lock_after_cleanup_run sFin root _ hrNe hcNe hcNoSlash rootNode stRoot hLookRootFin hStRoot hRwx hLookDirFin⟩
private theorem withLockedTempDir_wfl_err_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat) (fs : FsApiM (StateM TempDirMockState)) (hOps : CreateFsOps fs)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true) (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hWfl : ∀ {β : Type} p m c (body : StateM TempDirMockState (Except FsError β)), fs.withFileLock p m c body = pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }))
    (sFin : TempDirMockState) (rc : Except TempDirError Unit) (hCln : (Internal.cleanupDirIgnoringNotFound fs (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).run (spec8MkState s₀ root dirPrefix) = (rc, sFin)) :
    ((Internal.mkApiM fs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix fun _ => pure (.ok val)).run s₀ =
      (.error (Internal.mapFsError ({ kind := .permissionDenied, path := some (mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock"), message := "lock denied" } : FsError)), sFin) := by
  have hRes := resolveRoot_some_ok_run hOps.hStat s₀ root hvr stRoot hRoot hRwx.1; have hCre := createTempDir_ok_run hOps s₀ (some root) root dirPrefix hRes hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCre
  rw [mkApiM_withLockedTempDir_eq]; dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM]; rw [stateM_bind_run, hCre]; dsimp only; let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  dsimp only [spec8MkState] at hCln; rw [stateM_bind_run, stateM_tryFinally'_run, hOps.hJoin, hWfl]; simp only [stateM_bind_run, stateM_pure_run]
  change (match (Internal.cleanupDirIgnoringNotFound fs dir).run { nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1), locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec, nextUuid := s₀.nextUuid + 1 } with | (b, s2) => _) = _
  dsimp only [dir] at hCln ⊢; rw [hCln]; exact stateM_pure_run _ _
private theorem spec8_fail_execs (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    let fs1 : FsApiM (StateM TempDirMockState) := { mockFs with withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }), rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
    let fs2 : FsApiM (StateM TempDirMockState) := { mockFs with withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
    ∃ s1 s2 : TempDirMockState,
      ((Internal.mkApiM fs1 mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix fun _ => pure (.ok val)).run s₀ =
        (.error (Internal.mapFsError ({ kind := .permissionDenied, path := some (mockJoin dir ".lock"), message := "lock denied" } : FsError)), s1) ∧
      ((Internal.mkApiM fs2 mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix fun _ => pure (.ok val)).run s₀ =
        (.error (Internal.mapFsError ({ kind := .permissionDenied, path := some (mockJoin dir ".lock"), message := "lock denied" } : FsError)), s2) ∧
      ((mockFs.lstat dir).run s2).1.isOk = false := by
  intro dir fs1 fs2; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s₀.nextUuid) hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  let sMk := spec8MkState s₀ root dirPrefix; let sLockClean := { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) }
  have hCln1 : (Internal.cleanupDirIgnoringNotFound fs1 dir).run sMk = (.error (Internal.mapFsError { kind := .ioError, path := some dir, message := "rm failed" }), sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fs1]; rw [stateM_bind_run, stateM_pure_run]; dsimp only; rw [show (FsErrorKind.ioError == FsErrorKind.notFound) = false from rfl]; exact stateM_pure_run _ _
  have hRunLockRm := withLockedTempDir_wfl_err_exec s₀ root dirPrefix val fs1 ⟨rfl, fun p s => mockFs_stat_run s p, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩ hvr hvp stRoot hRoot hRwx hNone (fun _ _ _ _ => rfl) sMk _ hCln1
  have hCln2 : (Internal.cleanupDirIgnoringNotFound fs2 dir).run sMk = (.ok (), sLockClean) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fs2]; rw [show mockFs.rmtree = mockRmtreePure from rfl]; dsimp only [mockRmtreePure]
    rw [stateM_bind_run, stateM_bind_run, stateM_get_run]; dsimp only [sMk, spec8MkState, sLockClean]
    rw [hDirNorm, lookupNode_cons_eq _ _ _ _ rfl, stateM_bind_run, stateM_set_run, stateM_pure_run]; rfl
  have hRunLockClean := withLockedTempDir_wfl_err_exec s₀ root dirPrefix val fs2 ⟨rfl, fun p s => mockFs_stat_run s p, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩ hvr hvp stRoot hRoot hRwx hNone (fun _ _ _ _ => rfl) sLockClean _ hCln2
  exact ⟨sMk, sLockClean, hRunLockRm, hRunLockClean, by rw [mockFs_lstat_run]; unfold mockLstatPure; dsimp only [sLockClean]; rw [lookupNode_filter_underDir_eq sMk.nodes dir hDirNorm]; rfl⟩
/-- Spec 8: `withLockedTempDir` holds a `.shared` lock on `<dir>/.lock` during `action`, releases it and deletes `dir` on `.ok`/`.error`, and cleans up even if locking fails. -/
theorem proof_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    AllPass (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, AllPass]
  intro s₀ root dirPrefix val err ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq] at hNone ⊢
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)); have ⟨hLDir, hLLock, hShared, hEx⟩ := spec8_lockState_probes s₀ root dirPrefix hvr hvp
  let act8 : String → StateM TempDirMockState (Except TempDirError Nat) := fun d => do
    let stDir ← mockFs.lstat d; let lst ← mockFs.lstat (mockJoin d ".lock")
    let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ())); let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
    match stDir, lst, sharedProbe, exProbe with
    | .ok info, .ok st, .ok (some ()), .ok none => if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then return .ok val else return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
    | .error _, _, _, _ => return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
    | _, .error _, _, _ => return .error { kind := .notFound, path := some d, message := "missing lock file" }
    | _, _, _, _ => return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
  have hAct : (act8 dir).run (spec8LockState s₀ root dirPrefix) = (.ok val, spec8LockState s₀ root dirPrefix) := by
    dsimp only [act8, dir]; rw [stateM_bind_run, hLDir]; dsimp only; rw [stateM_bind_run, hLLock]; dsimp only; rw [stateM_bind_run, hShared]; dsimp only; rw [stateM_bind_run, hEx]; dsimp only
    simp only [show ((mockNodeStat (.dir s₀.nowSec 0o700)).kind == EntryKind.dir) = true from rfl, show ((mockNodeStat (.dir s₀.nowSec 0o700)).mode == 0o700) = true from rfl, beq_self_eq_true,
      show ((mockNodeStat (.file (freshInode (spec8MkState s₀ root dirPrefix)) "" (spec8MkState s₀ root dirPrefix).nowSec 0o644)).kind == EntryKind.file) = true from rfl, Bool.and_self, ↓reduceIte, stateM_pure_run]
  obtain ⟨sOk, hRunOk, h1, h2, h3⟩ := withLockedTempDir_exec s₀ root dirPrefix act8 (.ok val) hvr hvp stRoot hRoot hRwx hNone hAct
  obtain ⟨sErr, hRunErr, h4, _, h5⟩ := withLockedTempDir_exec s₀ root dirPrefix (fun _ => pure (Except.error err : Except TempDirError Nat)) (.error err) hvr hvp stRoot hRoot hRwx hNone (stateM_pure_run _ _)
  dsimp only [act8, dir] at hRunOk
  (conv => arg 2; erw [hRunOk]); dsimp only; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact h1
  · exact h2
  · exact h3
  (conv => arg 2; erw [hRunErr]); dsimp only; rw [allPass_assert, allPass_assert, allPass_assert]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact h4
  · exact h5
  obtain ⟨s1, s2, hRunLockRm, hRunLockClean, hGoneClean⟩ := spec8_fail_execs s₀ root dirPrefix val hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hRunLockRm hRunLockClean; rw [mockFs_join_eq] at hRunLockRm hRunLockClean
  (conv => arg 2; erw [hRunLockRm]); dsimp only; rw [allPass_assert]
  (conv => arg 2; erw [hRunLockClean]); dsimp only; rw [allPass_assert, allPass_assert_end]; exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, hGoneClean, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 8 (`test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit`). -/
theorem reach_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    CanReach (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  refine ⟨s₀, "/tmp", "tmp-", 42, { kind := .ioError, message := "err" }, ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hp := proof_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit s₀ "/tmp" "tmp-" 42 { kind := .ioError, message := "err" } ⟨rfl, rfl⟩ hRoot
  dsimp only [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; dsimp only at hp; rw [allPass_assume] at hp; exact hp hNone
/-- Spec 9: `withLockedTempDir` ignores `.notFound` from `fs.rmtree` in its finalizer on concurrent cleanup. -/
theorem proof_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    AllPass (test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq] at hNone ⊢
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u); let lockPath := mockJoin dir ".lock"
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide); have hLockNeDir := payload_ne_dir root _ ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock := underDir_mockJoin_self dir ".lock" (mockJoin_ne_empty root _ hcNe) hDirNorm (mockJoin_ne_slash root _ hrNe hcNe) (by decide) (by decide)
  let fsSweep : FsApiM (StateM TempDirMockState) := { mockFs with rmtree := fun p ign => do let _ ← mockFs.rmtree p ign; pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
  have hOpsSweep : CreateFsOps fsSweep := ⟨rfl, fun p s => mockFs_stat_run s p, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  have hRes := resolveRoot_some_ok_run hOpsSweep.hStat s₀ root hvr stRoot hRoot hRwx.1
  have hCre := createTempDir_ok_run hOpsSweep s₀ (some root) root dirPrefix hRes hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCre
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCre; have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by rw [hsMk]; exact lookupNode_lock_mk_none s₀.nodes dir _ hDirNorm hLockNeDir hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks), nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAfterLock, lookupNode_cons_lock_dir sMk.nodes dir _ hDirNorm hLockNeDir]; exact hLookDirMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s = { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hRmInner : (mockFs.rmtree dir true).run sAfterLock = (.ok (), sFin) := by rw [hsFin]; dsimp only [mockFs, mockRmtreePure]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hDirNorm, hLookDirAfterLock]; simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]; rfl
  have hClean : (Internal.cleanupDirIgnoringNotFound fsSweep dir).run sAfterLock = (.ok (), sFin) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsSweep]; rw [stateM_bind_run, stateM_bind_run, hRmInner]; dsimp only; rw [stateM_pure_run]; dsimp only; rw [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl]; simp only [↓reduceIte]; exact stateM_pure_run _ _
  have hRun : ((Internal.mkApiM fsSweep mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (.ok val, sFin) := by
    rw [mkApiM_withLockedTempDir_eq]; dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM]; rw [stateM_bind_run, hCre]; dsimp only; rw [stateM_bind_run, stateM_tryFinally'_run, show fsSweep.join = mockJoin from rfl]
    rw [show (∀ {β : Type}, @fsSweep.withFileLock β = @mockFs.withFileLock β) from rfl]; dsimp only [dir, lockPath] at hLockNorm hLookLockMk hsAfterLock hClean ⊢
    rw [stateM_bind_run, mockFs_withFileLock_create_run sMk _ .shared hLockNorm hLookLockMk]; simp only [stateM_bind_run, stateM_pure_run]; rw [← hsAfterLock, hClean]; dsimp only; exact stateM_pure_run _ _
  dsimp only [fsSweep] at hRun; erw [hRun]; dsimp only; rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, mockFs_lstat_isOk_false_of_lookup_none sFin dir (by rw [hsFin]; exact lookupNode_filter_underDir_eq _ _ hDirNorm), trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 9 (`test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup`). -/
theorem reach_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    CanReach (test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  refine ⟨s₀, "/tmp", "tmp-", 7, ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hp := proof_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup s₀ "/tmp" "tmp-" 7 ⟨rfl, rfl⟩ hRoot
  dsimp only [test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; dsimp only at hp; rw [allPass_assume] at hp; exact hp hNone
private theorem createTempDir_ex_mock_steps (s₀ : TempDirMockState) (root dirPrefix : String) (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 } (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    let sMk := { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (ExceptT.run (Internal.createTempDir mockFsEx mockUuidEx mockEnvEx (some root) dirPrefix)).run s₀ = (.ok (.ok dir), sMk) := by
  intro dir sMk; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s₀.nextUuid) hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by unfold mockLstatPure at hNone; cases hl : lookupNode s₀.nodes dir with | none => rfl | some _ => rw [hl] at hNone; simp [Except.isOk, Except.toBool] at hNone
  let sMk0 : TempDirMockState := { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
  have hMk : (mockFs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (), sMk0) := by dsimp only [dir, sMk0]; exact mockFs_mkdir_fresh_run _ root _ hrNe hcNe hcNoSlash rootNode stRoot hLookRootNorm hStRoot hRwx hLookDirNone
  have hDisj : ∀ x ∈ s₀.nodes.filter (fun e => !underDir dir e.1), normKey x.1 ≠ dir := fun x hx he => by have hu : underDir dir x.1 = true := (by rw [underDir_eq_of_normKey_eq dir x.1 dir (he.trans hDirNorm.symm), underDir_refl dir hDirNorm]); have hf := (List.mem_filter.mp hx).2; simp [hu] at hf
  have hCh : (mockFs.chmod dir 0o700).run sMk0 = (.ok (), sMk) := mockFs_chmod_0o700_head_run sMk0 dir s₀.nowSec 0o755 _ hDirNorm rfl hDisj
  have hResEx : (ExceptT.run (Internal.resolveRoot mockFsEx mockEnvEx (some root))).run s₀ = (.ok (.ok root), s₀) := by
    dsimp only [Internal.resolveRoot]; rw [exceptT_stateM_bind_run, exceptT_pure_run]; dsimp only; simp only [show Internal.validRoot root = true from hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run]
    rw [show (ExceptT.run (mockFsEx.stat root)).run s₀ = (.ok (.ok stRoot), s₀) by dsimp only [mockFsEx]; rw [exceptT_liftM_run, mockFs_stat_run, hRoot]]; dsimp only; simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte, exceptT_pure_run]
  dsimp only [Internal.createTempDir]; simp only [show Internal.validPrefix dirPrefix = true from hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run]; rw [hResEx]; dsimp only; rw [exceptT_stateM_bind_run]
  rw [show (ExceptT.run mockUuidEx.getUuid).run s₀ = (.ok (.ok (mockUuidOfNat s₀.nextUuid)), { s₀ with nextUuid := s₀.nextUuid + 1 }) by dsimp only [mockUuidEx]; rw [exceptT_liftM_run, mockUuid_getUuid_run]]
  dsimp only; simp only [show mockFsEx.join root (dirPrefix ++ mockUuidEx.toString (mockUuidOfNat s₀.nextUuid)) = dir from rfl]
  rw [exceptT_stateM_bind_run, show (ExceptT.run (mockFsEx.mkdir dir false false)).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (.ok ()), sMk0) by dsimp only [mockFsEx]; rw [exceptT_liftM_run, hMk]]
  dsimp only; rw [exceptT_stateM_bind_run, show (ExceptT.run (mockFsEx.chmod dir 0o700)).run sMk0 = (.ok (.ok ()), sMk) by dsimp only [mockFsEx]; rw [exceptT_liftM_run, hCh]]; exact exceptT_pure_run _ _
private theorem cleanupDir_ex_mock_run (s : TempDirMockState) (dir : String) (hnorm : normKey dir = dir) (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run s = (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]; rw [exceptT_stateM_bind_run]; rcases hnode with ⟨m, mode, hLook⟩
  rw [show (ExceptT.run (mockFsEx.rmtree dir true)).run s = (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) by dsimp only [mockFsEx]; rw [exceptT_liftM_run]; dsimp only [mockFs, mockRmtreePure]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hnorm, hLook]; simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]]
  exact exceptT_pure_run _ _
/-- Spec 10: Over `ExceptT String (StateM TempDirMockState)`, throwing inside `withTempDir` or `withLockedTempDir` cleans up and releases the lock while propagating the exception. -/
theorem proof_tempdir_tryFinally_exceptionCleansUpAndReleasesLock :
    AllPass (test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock (S := TempDirMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, AllPass]; intro s₀ root dirPrefix ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  rw [mockFs_stat_run] at hRoot; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [allPass_assume]; intro hNone; rw [mockFs_join_eq, mockUuid_toString_eq] at hNone ⊢
  let u := mockUuidOfNat s₀.nextUuid; let dir := mockJoin root (dirPrefix ++ mockUuidToString u); let lockPath := mockJoin dir ".lock"
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp; have hDirNorm := normKey_mockJoin root _ hcNe hcNoSlash
  have hLockNorm := normKey_mockJoin dir ".lock" (by decide) (by decide); have hLockNeDir := payload_ne_dir root _ ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock := underDir_mockJoin_self dir ".lock" (mockJoin_ne_empty root _ hcNe) hDirNorm (mockJoin_ne_slash root _ hrNe hcNe) (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by simpa [underDir, normKey_idem] using underDir_mockJoin_root_false root _ hrNe hcNe hcNoSlash
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by simpa [lookupNode, normKey_idem] using hLookRoot
  have hCreate := createTempDir_ex_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone; dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s = { s₀ with nextUuid := s₀.nextUuid + 1, nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate; have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨s1Fin, hs1Fin⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sMk = (.ok (.ok ()), s1Fin) := by rw [hs1Fin]; exact cleanupDir_ex_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩
  have hRun1 : (ExceptT.run ((Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx).withTempDir (some root) dirPrefix fun _ => (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ = (.error "boom", s1Fin) := by
    rw [mkApiM_withTempDir_eq]; dsimp only [Internal.withTempDirM]; rw [exceptT_stateM_bind_run, hCreate]; dsimp only; rw [exceptT_stateM_bind_run]
    rw [exceptT_tryFinally'_error_run (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)) (fun _ => Internal.cleanupDirIgnoringNotFound mockFsEx dir) "boom" sMk sMk (exceptT_throw_run "boom" sMk) hClean1]
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by rw [hsMk]; exact lookupNode_lock_mk_none s₀.nodes dir _ hDirNorm hLockNeDir hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := sMk.locks, nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by rw [hsAfterLock, lookupNode_cons_lock_dir sMk.nodes dir _ hDirNorm hLockNeDir]; exact hLookDirMk
  obtain ⟨s2Fin, hs2Fin⟩ : ∃ s : TempDirMockState, s = { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean2 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sAfterLock = (.ok (.ok ()), s2Fin) := by rw [hs2Fin]; exact cleanupDir_ex_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  obtain ⟨sLock, hsLock⟩ : ∃ s : TempDirMockState, s = { sMk with nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := (freshInode sMk, .shared) :: sMk.locks, nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hWflThrow : ∀ (body : ExceptT String (StateM TempDirMockState) (Except FsError (Except TempDirError Unit))),
      (ExceptT.run body).run sLock = (.error "boom", sLock) → (ExceptT.run (mockFsEx.withFileLock lockPath .shared true body)).run sMk = (.error "boom", sAfterLock) := fun body hActThrow => by
    dsimp only [mockFsEx, mockLockCore]; rw [exceptT_stateM_bind_run, show (ExceptT.run (get : ExceptT String (StateM TempDirMockState) TempDirMockState)).run sMk = (.ok sMk, sMk) from rfl]; dsimp only
    rw [hLockNorm, hLookLockMk]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run, exceptT_pure_run]; dsimp only [lockPath] at hsLock; rw [← hsLock, show (ExceptT.run (set sLock : ExceptT String (StateM TempDirMockState) Unit)).run sMk = (.ok (), sLock) from rfl]; dsimp only
    have hModEx : (ExceptT.run (modify (fun s' : TempDirMockState => { s' with locks := mockRemoveFirstLock (freshInode sMk) .shared s'.locks }) : ExceptT String (StateM TempDirMockState) Unit)).run sLock = (.ok (), sAfterLock) := by
      rw [hsAfterLock, hsLock]; change (Except.ok (), { sMk with nodes := (mockJoin dir ".lock", .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes, locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks), nextInode := freshInode sMk + 1 }) = _; rw [mockRemoveFirstLock_head]
    rw [exceptT_tryFinally'_error_run body (fun _ => modify (fun s' : TempDirMockState => { s' with locks := mockRemoveFirstLock (freshInode sMk) .shared s'.locks })) "boom" sLock sLock hActThrow hModEx]
  have hRun2 : (ExceptT.run ((Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx).withLockedTempDir (some root) dirPrefix fun _ => (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ = (.error "boom", s2Fin) := by
    rw [mkApiM_withLockedTempDir_eq]; dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM]; rw [exceptT_stateM_bind_run, hCreate]; dsimp only; rw [exceptT_stateM_bind_run]; dsimp only [dir, u] at hClean2 hWflThrow ⊢
    rw [exceptT_tryFinally'_error_run _ (fun _ => Internal.cleanupDirIgnoringNotFound mockFsEx dir) "boom" sMk sAfterLock ?_ hClean2]
    · rw [exceptT_stateM_bind_run, show mockFsEx.join = mockJoin from rfl]; dsimp only [lockPath] at hWflThrow; rw [hWflThrow _ (by rw [exceptT_stateM_bind_run, exceptT_throw_run])]
  have hLookDir1 : lookupNode s1Fin.nodes dir = none := by rw [hs1Fin]; exact lookupNode_filter_underDir_eq _ _ hDirNorm
  have hLookDir2 : lookupNode s2Fin.nodes dir = none := by rw [hs2Fin]; exact lookupNode_filter_underDir_eq _ _ hDirNorm
  have hLookRoot2 := root_preserved_after_cleanup s₀ s2Fin dir lockPath root (.file (freshInode sMk) "" sMk.nowSec 0o644) (.dir s₀.nowSec 0o700) rootNode hDirNorm hUnderLock hRootUnderDirFalse hLookRootNorm (by rw [hs2Fin, hsAfterLock, hsMk])
  rw [hRun1, hRun2]; dsimp only; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨rfl, mockFs_lstat_isOk_false_of_lookup_none s1Fin dir hLookDir1, rfl, mockFs_lstat_isOk_false_of_lookup_none s2Fin dir hLookDir2,
    probe_exclusive_lock_after_cleanup_run s2Fin root _ hrNe hcNe hcNoSlash rootNode stRoot hLookRoot2 hStRoot hRwx hLookDir2, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 10 (`test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock`). -/
theorem reach_tempdir_tryFinally_exceptionCleansUpAndReleasesLock :
    CanReach (test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock (S := TempDirMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, CanReach]; obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  have hRoot := defaultRoot_ok s₀ hs₀; have hNone := defaultDir_lstat_none s₀ hs₀
  refine ⟨s₀, "/tmp", "tmp-", ⟨rfl, rfl⟩, hRoot, ?_⟩; rw [mockUuid_getUuid_run s₀]; dsimp only; rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hp := proof_tempdir_tryFinally_exceptionCleansUpAndReleasesLock s₀ "/tmp" "tmp-" ⟨rfl, rfl⟩ hRoot
  dsimp only [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, AllPass] at hp; rw [mockUuid_getUuid_run s₀] at hp; dsimp only at hp; rw [allPass_assume] at hp; exact hp hNone
end LeanSwe.TempDir.Proofs

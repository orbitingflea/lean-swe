import LeanSwe.TempDir.Proofs.CleanupBase
/-!
Verification of `LeanSwe.TempDir` stale-directory sweep specifications (Specs 11–15)
and their `CanReach` non-vacuity witnesses.
-/
namespace LeanSwe.TempDir.Proofs
open Core Core.NondetTest LeanSwe.Time LeanSwe.Uuid LeanSwe.EnvVars
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
/-- Spec 11: `cleanupStaleTempDirs` keeps any matching directory with an active lock regardless of age. -/
theorem proof_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    AllPass (test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, AllPass]; intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩
  rw [mockFs_stat_run] at hRoot; rw [mockFs_lstat_run] at hChild hLock; dsimp only at hChild hLock; rw [mockFs_join_eq] at hChild hLock ⊢
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt s₀.nowSec), s₀) from rfl]; dsimp only; rw [mockFs_lstat_run, hChild]; dsimp only; rw [allPass_assume]; intro _
  let child := mockJoin root childName; let lockPath := mockJoin child ".lock"; have hLockNorm := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨ndChild, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChild; obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLock
  cases ndLock with | dir _ _ | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile | file lockIno lockC lockT lockM =>
    by_cases hConf : mockHasConflict s₀.locks lockIno .shared = true
    · rw [mockFs_withFileLock_existing_conflict_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock hConf]; dsimp only; intro hFalse; cases hFalse
    · let sLock : TempDirMockState := { s₀ with locks := (lockIno, .shared) :: s₀.locks }
      obtain ⟨_, after, repBefore, sBefore, hBeforePres, hNotRmB, _, _, _, hExec⟩ := cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs sLock root dirPrefix childName maxAgeSec hvr hvp hcV stRoot hRoot hRwx ndChild hLookChild
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hLstatChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; exact Prod.ext hChild rfl
      have hLstatLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]; exact Prod.ext hLock rfl
      have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
      have hConfExclBefore : mockHasConflict sBefore.locks lockIno .exclusive = true := by rw [hBeforePres.2.1]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
      let nowSec := (mockTime.nowTimestamp.run sLock).1.toSecondsSinceUnixEpoch.val; let repMid : CleanupReport := { repBefore with keptLocked := repBefore.keptLocked.push child }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]; dsimp only [child, lockPath] at hLstatChildBefore hLstatLockBefore hLookLockBefore
        simp only [show (!dirPrefix.toList.isPrefixOf childName.toList) = false by simp [hPref], Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hLstatChildBefore, show (stChild.kind != EntryKind.dir) = false by rw [hcDir]; rfl, hLstatLockBefore, show (stLock.kind != EntryKind.file) = false by rw [hlFile]; rfl]
        rw [mockFs_tryWithFileLock_existing_conflict_run sBefore _ .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfExclBefore]; exact stateM_pure_run _ _
      cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore with | mk repAfter sFinal =>
        have hExec' := hExec repMid sBefore hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'
        obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, _, _, _, _⟩ := hExec'; have hTotPres := nodesFilteredPres_trans hBeforePres hAfterPres
        have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by rw [nodesFilteredPres_lookupNode hTotPres lockPath hPLock]; exact hLookLock
        have hConfExclFin : mockHasConflict sFinal.locks lockIno .exclusive = true := by rw [hTotPres.2.1]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
        have hProbeRun := mockFs_tryWithFileLock_existing_conflict_run sFinal lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockFin hConfExclFin (pure (.ok ()))
        have hLstatFin : (mockFs.lstat child).run sFinal = (.ok stChild, sFinal) := by rw [nodesFilteredPres_lstat hTotPres child hPChild, mockFs_lstat_run]; exact Prod.ext hChild rfl
        rw [mockFs_withFileLock_existing_ok_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock (Bool.eq_false_iff.mpr hConf)]
        dsimp only [sLock, lockPath, child, nowSec] at hProbeRun hLstatFin hCleanRun ⊢
        rw [stateM_bind_run, hCleanRun]; dsimp only; rw [stateM_bind_run]; erw [hProbeRun]; dsimp only; rw [stateM_bind_run]; erw [hLstatFin]; dsimp only; rw [stateM_pure_run]; dsimp only
        rw [allPass_assert, allPass_assert_end]; exact ⟨⟨hKLIff.mpr (by simp [repMid, child, Array.toList_push]), fun h => hNotRmB (hRmIff.mp h)⟩, ⟨rfl, rfl⟩, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 11 (`test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge`). -/
theorem reach_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    CanReach (test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, CanReach]
  let s₀ : TempDirMockState := { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.dir 0 0o755), rfl, rfl⟩, ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, ?_⟩
  rw [mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl, show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) from rfl]; dsimp only; rw [canReach_assume]; refine ⟨by decide, ?_⟩
  have hp := proof_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge s₀ "/tmp" "tmp-" "tmp-a" 10 ⟨by decide, by decide⟩ (by decide) (by decide) ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.dir 0 0o755), rfl, rfl⟩ ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩
  dsimp only [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, AllPass, mockTime] at hp
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run] at hp; dsimp only at hp; rw [mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl] at hp; dsimp only at hp; rw [allPass_assume] at hp; exact hp (by decide)
private theorem spec12_sweepEntry_deadLock (s₀ sBefore : TempDirMockState) (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int) (repBefore : CleanupReport)
    (stChild stLock : FileStat) (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat) (childNode : MockNode) (hcDir : pHasRwx stChild) (hlFile : stLock.kind = .file)
    (hvr : pValidRoot root = true) (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode) (hStChild : mockNodeStat childNode = stChild)
    (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM)) (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock)
    (hListZero : ((mockFs.listDir (mockJoin root childName)).run s₀).1 = .ok #[".lock"]) (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false)
    (hBeforePres : NodesFilteredPres (fun k => underDir (mockJoin root childName) k = true ∨ normKey k = normKey root) s₀ sBefore) :
    let child := mockJoin root childName; let lockPath := mockJoin child ".lock"
    ∃ sMid : TempDirMockState, (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = ({ repBefore with removed := repBefore.removed.push child }, sMid) ∧
      NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid ∧ lookupNode sMid.nodes child = none ∧ lookupNode sMid.nodes lockPath = none := by
  intro child lockPath; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe := mockJoin_ne_empty root childName hcNe; have hcFullNorm := normKey_mockJoin root childName hcNe hcSlash; have hLockNorm := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨hPChild, hPUnder, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : lookupNode sBefore.nodes child = some childNode := by rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]; exact hLookChild
  have hLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by rw [hBeforePres.2.1]; exact hConfF
  have hChildPure : mockLstatPure sBefore child = .ok stChild := by dsimp only [mockLstatPure]; rw [hChildBefore]; exact congrArg Except.ok hStChild
  have hLockPure : mockLstatPure sBefore lockPath = .ok stLock := by dsimp only [mockLstatPure]; rw [hLockBefore]; exact congrArg Except.ok hStLock
  have hLockNeChild := payload_ne_dir root childName ".lock" hrNe hcNe hcSlash (by decide) (by decide)
  have hRootUnderChild : underDir child (normKey root) = false := by simpa [underDir, normKey_idem] using underDir_mockJoin_root_false root childName hrNe hcNe hcSlash
  let sLock := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hListLock : (mockFs.listDir child).run sLock = (.ok #[".lock"], sLock) := by rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, (nodesFilteredPres_listDir hBeforePres child hcFullNe hPChild hPUnder).1, hListZero]
  let s1 := { sLock with nodes := sLock.nodes.filter (fun e => normKey e.1 != lockPath) }
  have hNeLockOfChild : ∀ e : String × MockNode, e ∈ sBefore.nodes → normKey e.1 = normKey child → (normKey e.1 != lockPath) = true := fun e _ h => bne_iff_ne.mpr (by dsimp only [lockPath]; rw [h, hcFullNorm, ← hLockNorm]; exact ne_comm.mp hLockNeChild)
  rcases (by cases childNode with | file _ _ _ _ | symlink _ _ => simp [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1 | dir tC mC => exact ⟨tC, mC, by change lookupNode (sBefore.nodes.filter (fun e => normKey e.1 != lockPath)) child = _; rw [lookupNode_filter_of_preserved sBefore.nodes _ child hNeLockOfChild]; exact hChildBefore⟩ : ∃ tC mC, lookupNode s1.nodes child = some (.dir tC mC)) with ⟨tC, mC, hLookChild1⟩
  let s2 := { s1 with nodes := s1.nodes.filter (fun e => normKey e.1 != child) }
  have hRemLocked : (Internal.removeLockedTempDir mockFs child lockPath).run sLock = (.ok (.ok ()), s2) := by
    dsimp only [Internal.removeLockedTempDir]; rw [stateM_bind_run, hListLock]; dsimp only [Array.toList]; rw [stateM_bind_run]; dsimp only [Internal.removeNonLockChildren]; simp only [beq_self_eq_true, ↓reduceIte]
    rw [stateM_pure_run]; dsimp only; rw [stateM_bind_run, mockFs_unlink_existing_run sLock lockPath true lockIno lockC lockT lockM hLockNorm hLockBefore]; dsimp only; rw [stateM_bind_run, mockFs_rmdir_dir_run s1 child tC mC hcFullNorm hLookChild1]; exact stateM_pure_run _ _
  let sMid := { s2 with locks := mockRemoveFirstLock lockIno .exclusive s2.locks }
  have hPresMid : NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid := by
    refine ⟨⟨fun k => (normKey k != lockPath) && (normKey k != child), fun k hk => ?_, list_filter_filter_and sBefore.nodes _ _⟩, mockRemoveFirstLock_head lockIno .exclusive sBefore.locks, rfl, rfl, rfl, rfl⟩
    have hn1 : normKey k ≠ lockPath := fun hEq => by have hu : underDir child (normKey root) = true := (by rw [← hk, underDir_eq_of_normKey_eq child (normKey k) lockPath (by simpa [normKey_idem] using hEq.trans hLockNorm.symm)]; exact underDir_mockJoin_self child ".lock" hcFullNe hcFullNorm (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)); rw [hRootUnderChild] at hu; cases hu
    have hn2 : normKey k ≠ child := fun hEq => by have hu : underDir child (normKey root) = true := (by rw [← hk, underDir_eq_of_normKey_eq child (normKey k) child (by simpa [normKey_idem] using hEq.trans hcFullNorm.symm)]; exact underDir_refl child hcFullNorm); rw [hRootUnderChild] at hu; cases hu
    simp [hn1, hn2]
  refine ⟨sMid, ?_, hPresMid, lookupNode_filter_ne_none s1.nodes child hcFullNorm, lookupNode_filter_none_of_none s1.nodes _ lockPath (lookupNode_filter_ne_none sLock.nodes lockPath hLockNorm)⟩
  dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]; dsimp only [child, lockPath] at hChildPure hLockPure
  simp only [show (!dirPrefix.toList.isPrefixOf childName.toList) = false by rw [hPref]; rfl, Bool.false_eq_true, ↓reduceIte, stateM_bind_run,
    mockFs_lstat_run, hChildPure, show (stChild.kind != .dir) = false by rw [hcDir.1]; rfl, hLockPure, show (stLock.kind != .file) = false by rw [hlFile]; rfl]
  rw [show mockJoin (mockJoin root childName) ".lock" = lockPath from rfl, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLockBefore hConfBefore]
  dsimp only; dsimp only [sLock] at hRemLocked; rw [hRemLocked]; exact stateM_pure_run _ _
/-- Spec 12: `cleanupStaleTempDirs` immediately removes a dead locked temp directory regardless of `maxAgeSec`, leaving zero locks held. -/
theorem proof_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately :
    AllPass (test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp, _⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩ hListZero hTryExcl
  have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV; let child := mockJoin root childName; let lockPath := mockJoin child ".lock"
  rw [mockFs_stat_run] at hRoot; rw [mockFs_lstat_run, mockFs_join_eq] at hChild hLock; dsimp only at hChild hLock; rw [mockFs_join_eq] at hListZero hTryExcl ⊢
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRoot; obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChild; obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLock
  cases ndLock with
  | dir _ _ | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | file lockIno lockC lockT lockM =>
    have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath (normKey_mockJoin child ".lock" (by decide) (by decide)) lockIno lockC lockT lockM hLookLock hTryExcl
    rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt s₀.nowSec), s₀) from rfl]; dsimp only; rw [mockFs_lstat_run, hChild]; dsimp only; rw [allPass_assume]; intro _
    obtain ⟨_, after, repBefore, sBefore, hBeforePres, _, hNotKLB, hNotKFB, _, hExec⟩ := cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec hvr hvp hcV stRoot hRoot hRwx childNode hLookChild
    obtain ⟨sMid, hSweepMid, hPresMid, hChildNoneMid, _⟩ := spec12_sweepEntry_deadLock s₀ sBefore root dirPrefix childName maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val)
        repBefore stChild stLock lockIno lockC lockT lockM childNode hcDir hlFile hvr hcV hPref hLookChild hStChild hLookLock hStLock hListZero hConfF hBeforePres
    cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) { repBefore with removed := repBefore.removed.push child } after).run sMid with
    | mk repAfter sFinal =>
      have hExec' := hExec { repBefore with removed := repBefore.removed.push child } sMid hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'
      obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, hKFIff, _, _, _⟩ := hExec'; obtain ⟨_, _, _, hPRoot⟩ := nodesFilteredPres_child_P (root := root) hcV
      rw [hCleanRun]; dsimp only [AllPass]; rw [allPass_assert, allPass_assert, allPass_assert_end]
      have hChildNoneFin := nodesFilteredPres_lookupNode_none hAfterPres child hChildNoneMid
      have hLookRootFin : lookupNode sFinal.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hAfterPres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk)),
          nodesFilteredPres_lookupNode hPresMid (normKey root) (fun k hk => by simpa [normKey_idem] using hk),
          nodesFilteredPres_lookupNode hBeforePres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk))]; simpa [lookupNode, normKey_idem] using hLookRoot
      exact ⟨⟨hRmIff.mpr (by simp [child, Array.toList_push]), fun h => hNotKLB (hKLIff.mp h), fun h => hNotKFB (hKFIff.mp h)⟩,
        mockFs_lstat_isOk_false_of_lookup_none sFinal child hChildNoneFin, probe_exclusive_lock_after_cleanup_run sFinal root childName hrNe hcNe hcSlash rootNode stRoot hLookRootFin hStRoot hRwx hChildNoneFin, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 12 (`test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately`). -/
theorem reach_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately :
    CanReach (test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, CanReach]
  let s₀ : TempDirMockState := { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)], nowSec := 5 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide, by decide⟩, by decide, by decide, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, rfl, rfl, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 5), s₀) from rfl, mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl]; dsimp only; rw [canReach_assume]; refine ⟨by decide, ?_⟩
  have hp := proof_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately s₀ "/tmp" "tmp-" "tmp-a" 10 ⟨by decide, by decide, by decide⟩ (by decide) (by decide) ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩ rfl rfl
  dsimp only [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, AllPass, mockTime] at hp
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run] at hp; dsimp only at hp; rw [mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl] at hp; dsimp only at hp; rw [allPass_assume] at hp; exact hp (by decide)
/-- Spec 13: for matching unlocked temp directories, `cleanupStaleTempDirs` keeps directories within `age ≤ maxAgeSec` and removes those with `age > maxAgeSec`. -/
theorem proof_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    AllPass (test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked, AllPass]; intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩ ⟨eNf, hLock, _⟩
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV; let child := mockJoin root childName; let lockPath := mockJoin child ".lock"
  rw [mockFs_stat_run] at hRoot; rw [mockFs_lstat_run, mockFs_join_eq] at hChild; dsimp only at hChild
  have hLockNone : lookupNode s₀.nodes lockPath = none := by rw [mockFs_join_eq] at hLock; exact mockFs_lstat_notFound_lookup_none s₀ lockPath eNf hLock
  rw [mockFs_join_eq]; obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChild
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt s₀.nowSec), s₀) from rfl]; dsimp only; rw [mockFs_lstat_run, hChild]; dsimp only
  let nowSec := (mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val; let ageSec := nowSec - stChild.modifiedSec
  obtain ⟨_, after, repBefore, sBefore, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ := cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec hvr hvp hcV stRoot hRoot hRwx childNode hLookChild
  obtain ⟨hPChild, _, _, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]
  have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.error { kind := .notFound, path := some lockPath, message := "not found" }, sBefore) := by
    rw [mockFs_lstat_run]; unfold mockLstatPure; rw [nodesFilteredPres_lookupNode_none hBeforePres lockPath hLockNone]
  have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
  have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
  by_cases hFresh : ageSec ≤ (maxAgeSec : Int)
  · let repMid : CleanupReport := { repBefore with keptFresh := repBefore.keptFresh.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sBefore) := by
      dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]; dsimp only [child, lockPath] at hChildBefore hLockBefore
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hChildBefore, hNotDir, hLockBefore, show (FsErrorKind.notFound != .notFound) = false from rfl]
      dsimp only [nowSec, ageSec] at hFresh ⊢; simp only [hFresh, ↓reduceIte]; exact stateM_pure_run _ _
    cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore with | mk repAfter sFinal =>
      have hExec' := hExec repMid sBefore hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'
      obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec'; rw [hCleanRun]; dsimp only [AllPass]; dsimp only [nowSec, ageSec] at hFresh
      rw [show (mockTime.nowTimestamp.run s₀).1 = _root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt s₀.nowSec) from rfl] at hFresh
      simp only [hFresh, ↓reduceIte]; rw [allPass_assert, allPass_assert_end]
      exact ⟨⟨hKFIff.mpr (by simp [repMid, child, Array.toList_push]), fun h => hNotRmB (hRmIff.mp h)⟩, by rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres) child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]; rfl, trivial⟩
  · have hRmUnder : (Internal.cleanupDirIgnoringNotFound mockFs child).run sBefore = (.ok (), { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }) := by
      have hLookChildBefore : lookupNode sBefore.nodes child = some childNode := by rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]; exact hLookChild
      cases childNode with | file _ _ _ _ | symlink _ _ => dsimp only [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1 | dir tC mC => exact cleanupDir_mock_run sBefore child (normKey_mockJoin root childName hcNe hcSlash) ⟨tC, mC, hLookChildBefore⟩
    let sMid := { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }; let repMid : CleanupReport := { repBefore with removed := repBefore.removed.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sMid) := by
      dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]; dsimp only [child, lockPath] at hChildBefore hLockBefore hRmUnder
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hChildBefore, hNotDir, hLockBefore, show (FsErrorKind.notFound != .notFound) = false from rfl]
      dsimp only [nowSec, ageSec] at hFresh ⊢; simp only [hFresh, ↓reduceIte, stateM_bind_run, hRmUnder]; exact stateM_pure_run _ _
    cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sMid with | mk repAfter sFinal =>
      have hExec' := hExec repMid sMid hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'
      obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec'; rw [hCleanRun]; dsimp only [AllPass]; dsimp only [nowSec, ageSec] at hFresh
      rw [show (mockTime.nowTimestamp.run s₀).1 = _root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt s₀.nowSec) from rfl] at hFresh
      simp only [hFresh, ↓reduceIte]; rw [allPass_assume]; intro _; rw [allPass_assert, allPass_assert_end]
      have hChildNoneMid : lookupNode sMid.nodes child = none := lookupNode_filter_none_of_underDir sBefore.nodes child child (underDir_refl child (normKey_mockJoin root childName hcNe hcSlash))
      exact ⟨⟨hRmIff.mpr (by simp [repMid, child, Array.toList_push]), fun h => hNotKFB (hKFIff.mp h)⟩, mockFs_lstat_isOk_false_of_lookup_none sFinal child (nodesFilteredPres_lookupNode_none hAfterPres child hChildNoneMid), trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 13 (`test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked`). -/
theorem reach_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    CanReach (test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked, CanReach]
  let s₀ : TempDirMockState := { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 95 0o755)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.dir 95 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨{ kind := .notFound, path := some "/tmp/tmp-a/.lock", message := "not found" }, rfl, rfl⟩, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) from rfl, mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 95 0o755)) from rfl]; dsimp only
  have hp := proof_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked s₀ "/tmp" "tmp-" "tmp-a" 10 ⟨by decide, by decide⟩ (by decide) (by decide) ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.dir 95 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨{ kind := .notFound, path := some "/tmp/tmp-a/.lock", message := "not found" }, rfl, rfl⟩
  dsimp only [test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked, AllPass, mockTime] at hp
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run] at hp; dsimp only at hp; rw [mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 95 0o755)) from rfl] at hp; dsimp only at hp
  have hCond : (_root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt 100)).toSecondsSinceUnixEpoch.val - (mockNodeStat (.dir 95 0o755)).modifiedSec ≤ (↑10 : Int) := of_decide_eq_true rfl
  split <;> first | exact hp | exact absurd hCond ‹_›
/-- Spec 14: `cleanupStaleTempDirs` skips non-matching names, files, and symlinks under `root` without removing them, and returns sorted arrays. -/
theorem proof_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    AllPass (test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety, AllPass]; intro s₀ root dirPrefix entryName maxAgeSec ⟨hvr, hvp⟩ hcV ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hSkipCond⟩
  let child := mockJoin root entryName; rw [mockFs_stat_run] at hRoot; rw [mockFs_lstat_run, mockFs_join_eq] at hChild; dsimp only at hChild; rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChild
  obtain ⟨_, after, repBefore, sBefore, hBeforePres, hNotRmB, _, _, _, hExec⟩ := cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix entryName maxAgeSec hvr hvp hcV stRoot hRoot hRwx childNode hLookChild
  obtain ⟨hPChild, _, _, _⟩ := nodesFilteredPres_child_P (root := root) hcV; let repMid : CleanupReport := { repBefore with skipped := repBefore.skipped.push child }
  have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore entryName).run sBefore = (repMid, sBefore) := by
    dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]
    rcases hSkipCond with hNotPref | hNotDir
    · simp only [show (!dirPrefix.toList.isPrefixOf entryName.toList) = true by cases hb : dirPrefix.toList.isPrefixOf entryName.toList <;> first | rfl | exact absurd hb hNotPref, ↓reduceIte]; exact stateM_pure_run _ _
    · by_cases hPref : (!dirPrefix.toList.isPrefixOf entryName.toList) = true
      · simp only [hPref, ↓reduceIte]; exact stateM_pure_run _ _
      · have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]
        dsimp only [child] at hChildBefore; simp only [Bool.eq_false_iff.mpr hPref, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hChildBefore, show (stChild.kind != .dir) = true by revert hNotDir; cases stChild.kind <;> decide, ↓reduceIte]; exact stateM_pure_run _ _
  cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore with | mk repAfter sFinal =>
    have hExec' := hExec repMid sBefore hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'; obtain ⟨hCleanRun, hAfterPres, hRmIff, _, _, hSkIff, _, _⟩ := hExec'
    rw [hCleanRun]; dsimp only [AllPass]; rw [allPass_assert, allPass_assert, allPass_assert_end]
    exact ⟨⟨hSkIff.mpr (by simp [repMid, child, Array.toList_push]), fun h => hNotRmB (hRmIff.mp h)⟩, by rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres) child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]; rfl, ⟨isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _⟩, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 14 (`test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety`). -/
theorem reach_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    CanReach (test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety, CanReach]; let s₀ : TempDirMockState := { nodes := [("/tmp", .dir 0 0o755), ("/tmp/keep-me", .dir 0 0o755)], nowSec := 100 }
  exact ⟨s₀, "/tmp", "tmp-", "keep-me", 10, ⟨by decide, by decide⟩, by decide, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.dir 0 0o755), rfl, Or.inl (by decide)⟩,
    proof_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety s₀ "/tmp" "tmp-" "keep-me" 10 ⟨by decide, by decide⟩ (by decide) ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.dir 0 0o755), rfl, Or.inl (by decide)⟩⟩
private theorem removeNonLockChildren_fail_with_lock_intact (child payload : String) (hcNe : child ≠ "") (hPayEq : payload = mockJoin child "locked_child.txt")
    (fs : FsApiM (StateM TempDirMockState)) (hLstat : fs.lstat = mockFs.lstat) (hJoin : fs.join = mockJoin) (hRm : fs.rmtree = mockFs.rmtree)
    (hUnl : ∀ p miss s, (fs.unlink p miss).run s = if p == payload then (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" }, s) else (mockFs.unlink p miss).run s)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNd : names.Nodup) (hPayMem : "locked_child.txt" ∈ names) (s : TempDirMockState)
    (hPayNode : ∃ ino c t m, lookupNode s.nodes payload = some (.file ino c t m)) :
    ∃ te s', (Internal.removeNonLockChildren fs child names).run s = (.error te, s') ∧ NodesFilteredPres (fun k => normKey k = normKey (mockJoin child ".lock")) s s' := by
  induction names generalizing s with
  | nil => cases hPayMem
  | cons nm rest ih =>
    have hnmV := hValid nm List.mem_cons_self; have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    have ⟨_, hRestNd⟩ := List.nodup_cons.mp hNd; dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : nm = ".lock"
    · subst hLock; exact ih hrestV hRestNd (by rcases List.mem_cons.mp hPayMem with h | h <;> first | exact absurd h (by decide) | exact h) s hPayNode
    · simp only [beq_false_of_ne hLock, Bool.false_eq_true, ↓reduceIte, hJoin, stateM_bind_run, hLstat, mockFs_lstat_run]
      by_cases hIsPay : nm = "locked_child.txt"
      · subst hIsPay; rw [← hPayEq]; rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
        rw [show mockLstatPure s payload = .ok (mockNodeStat (.file ino c t m)) by unfold mockLstatPure; rw [hLookPay]]; dsimp only
        simp only [show ((mockNodeStat (.file ino c t m)).kind == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]; rw [stateM_bind_run, hUnl payload true s]; simp only [beq_self_eq_true, ↓reduceIte]; exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
      · have hPayInRest : "locked_child.txt" ∈ rest := by rcases List.mem_cons.mp hPayMem with h | h <;> first | exact absurd h.symm hIsPay | exact h
        have hDisj : ∀ tgt, pValidEntryName tgt = true → nm ≠ tgt → ∀ k, normKey k = normKey (mockJoin child tgt) → underDir (mockJoin child nm) k = false ∧ normKey k ≠ normKey (mockJoin child nm) := fun tgt htV hNe k hk => by
          have ⟨hnmNe, _, _, hnmS⟩ := validEntryName_parts nm hnmV; have ⟨htNe, _, _, htS⟩ := validEntryName_parts tgt htV
          have hSub : ∀ hEq : underDir (mockJoin child nm) k = true, False := fun hEq => disjoint_underDir_mockJoin child nm tgt (mockJoin child tgt) hcNe hnmNe htNe hnmS htS hNe (by rwa [← underDir_eq_of_normKey_eq _ k (mockJoin child tgt) hk]) (underDir_refl _ (normKey_mockJoin child tgt htNe htS))
          exact ⟨by cases hb : underDir (mockJoin child nm) k with | false => rfl | true => exact absurd hb hSub, fun hEq => hSub (by rw [underDir_eq_of_normKey_eq _ k (mockJoin child nm) hEq]; exact underDir_refl _ (normKey_mockJoin child nm hnmNe hnmS))⟩
        have hDisjLock := hDisj ".lock" (by decide) hLock; have hDisjPay := hDisj "locked_child.txt" (by decide) hIsPay
        have hUnlOps : ∀ p miss s1, (fs.unlink p miss).run s1 = (mockFs.unlink p miss).run s1 ∨ ∃ fe, (fs.unlink p miss).run s1 = (.error fe, s1) := fun p miss s1 => by rw [hUnl]; split <;> first | exact Or.inr ⟨_, rfl⟩ | exact Or.inl rfl
        cases mockLstatPure s (mockJoin child nm) with
        | error fe =>
          dsimp only; by_cases hnf : (fe.kind == .notFound) = true
          · simp only [hnf, ↓reduceIte]; exact ih hrestV hRestNd hPayInRest s hPayNode
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
        | ok st =>
          dsimp only; by_cases hDir : (st.kind == .dir) = true
          · simp only [hDir, ↓reduceIte, stateM_bind_run]; have h1 := cleanupDirIgnoringNotFound_filteredPres fs hRm (mockJoin child nm) s
            cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin child nm)).run s with | mk rc sc =>
              rw [hc] at h1; dsimp only at h1; have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).1) h1; have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).1) h1
              cases rc with | error te => exact ⟨te, sc, stateM_pure_run _ _, hPresLock⟩ | ok _ => rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩; obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest sc ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩; exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩
          · simp only [Bool.eq_false_iff.mpr hDir, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]; have h1 := unlink_filteredPres fs hUnlOps (mockJoin child nm) true s
            cases hu : (fs.unlink (mockJoin child nm) true).run s with | mk ru su =>
              rw [hu] at h1; dsimp only at h1; have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).2) h1; have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).2) h1
              cases ru with | error _ => dsimp only; rw [stateM_bind_run, stateM_pure_run]; dsimp only; rw [stateM_pure_run]; exact ⟨_, su, stateM_pure_run _ _, hPresLock⟩ | ok _ => rw [stateM_bind_run, stateM_pure_run]; dsimp only; rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩; obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest su ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩; exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩
private theorem spec15_partialFail_exec (s₀ : TempDirMockState) (root dirPrefix childName : String) (maxAgeSec : Nat)
    (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true) (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (stRoot stChild stLock : FileStat) (hRootPure : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot) (childNode : MockNode)
    (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode) (hStChild : mockNodeStat childNode = stChild) (hcDir : pHasRwx stChild)
    (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat) (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM))
    (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock) (hlFile : stLock.kind = .file) (payIno : Nat) (payC : String) (payT : Int) (payM : Nat)
    (hLookPay : lookupNode s₀.nodes (mockJoin (mockJoin root childName) "locked_child.txt") = some (.file payIno payC payT payM)) (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false) :
    let child := mockJoin root childName; let lockPath := mockJoin child ".lock"; let payload := mockJoin child "locked_child.txt"
    let fsFailChild : FsApiM (StateM TempDirMockState) := { mockFs with unlink := fun p miss => if p == payload then pure (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" }) else mockFs.unlink p miss }
    ∃ rep s₁, ((Internal.mkApiM fsFailChild mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ = (.ok rep, s₁) ∧
      ¬ pHasPath rep.removed child = true ∧ ¬ pHasPath rep.keptFresh child = true ∧ (!rep.failed.isEmpty) = true ∧ ((mockFs.lstat lockPath).run s₁).1.isOk = true ∧ ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
  intro child lockPath payload fsFailChild; have hrNe := validRoot_ne_empty root hvr; have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe := mockJoin_ne_empty root childName hcNe; have hLockNorm := normKey_mockJoin child ".lock" (by decide) (by decide)
  have hOpsFail : SweepFsOps fsFailChild := ⟨rfl, rfl, rfl, rfl, fun {_} => rfl, rfl, rfl, fun p miss s => by dsimp only [fsFailChild]; split <;> first | exact Or.inr ⟨_, rfl⟩ | exact Or.inl rfl⟩
  obtain ⟨_, after, repBefore, sBefore, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ := cleanupStaleTempDirs_split_exec fsFailChild hOpsFail s₀ root dirPrefix childName maxAgeSec hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, hPUnder, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by rw [hBeforePres.2.1]; exact hConfF
  have hChildLstatBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only [mockLstatPure]; rw [hLookChild]; exact Prod.ext (congrArg Except.ok hStChild) rfl
  have hLockLstatBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]; dsimp only [mockLstatPure]; rw [hLookLock]; exact Prod.ext (congrArg Except.ok hStLock) rfl
  let sLockBefore := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hChildStatBefore : mockStatPure sBefore child = .ok stChild := by dsimp only [mockStatPure, mockLstatPure]; rw [nodesFilteredPres_lookupNode hBeforePres child hPChild, hLookChild]; exact congrArg Except.ok hStChild
  have ⟨hListChildBefore, hNdNames, hValidNames⟩ := mockFs_listDir_run_of_rwx sBefore child stChild hChildStatBefore hcDir
  have hPayUnder := underDir_mockJoin_self child "locked_child.txt" hcFullNe (normKey_mockJoin root childName hcNe hcSlash) (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)
  have hPayBefore : lookupNode sBefore.nodes payload = some (.file payIno payC payT payM) := by rw [nodesFilteredPres_lookupNode hBeforePres payload fun k hk => hPUnder k (by rw [underDir_eq_of_normKey_eq _ k payload hk]; exact hPayUnder)]; exact hLookPay
  have hPayMem := mockFs_listDir_mem_of_lookupNode sBefore child "locked_child.txt" hcFullNe (by decide) (.file payIno payC payT payM) hPayBefore
  let names := Internal.sortStrings (eraseDupStrings (sBefore.nodes.filterMap (fun e => mockParentChild (normKey child) e.1)))
  obtain ⟨te, sInner, hFailRun, hLockPresInner⟩ := removeNonLockChildren_fail_with_lock_intact child payload hcFullNe rfl fsFailChild rfl rfl rfl (fun p miss s => by dsimp only [fsFailChild]; split <;> rfl) names hValidNames hNdNames hPayMem sLockBefore ⟨payIno, payC, payT, payM, hPayBefore⟩
  have hListLock : (mockFs.listDir child).run sLockBefore = (.ok names.toArray, sLockBefore) := by rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, congrArg Prod.fst hListChildBefore]
  have hRemLocked : (Internal.removeLockedTempDir fsFailChild child lockPath).run sLockBefore = (.ok (.error te), sInner) := by dsimp only [Internal.removeLockedTempDir]; rw [hOpsFail.hListDir, stateM_bind_run, hListLock]; dsimp only [Array.toList]; rw [stateM_bind_run, hFailRun]; exact stateM_pure_run _ _
  let sMid := { sInner with locks := mockRemoveFirstLock lockIno .exclusive sInner.locks }; let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push te }
  have hSweepMid : (Internal.sweepEntry fsFailChild root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore = (repMid, sMid) := by
    dsimp only [Internal.sweepEntry]; rw [hOpsFail.hJoin]; dsimp only [child] at hChildLstatBefore hRemLocked; dsimp only [sLockBefore] at hRemLocked; rw [show mockJoin (mockJoin root childName) ".lock" = lockPath from rfl]
    simp only [show (!dirPrefix.toList.isPrefixOf childName.toList) = false by rw [hPref]; rfl, Bool.false_eq_true, ↓reduceIte, hOpsFail.hLstat, stateM_bind_run, hChildLstatBefore, show (stChild.kind != .dir) = false by rw [hcDir.1]; rfl, hLockLstatBefore, show (stLock.kind != .file) = false by rw [hlFile]; rfl, hOpsFail.hTryWfl, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfBefore, stateM_bind_run, hRemLocked, Except.map]; exact stateM_pure_run _ _
  cases hAfterRun : (Internal.sweepEntries fsFailChild root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sMid with | mk repAfter sFinal =>
    have hExec' := hExec repMid sMid hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'; obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, hFailNonEmpty, _⟩ := hExec'
    have hMidLockPres : NodesFilteredPres (fun k => normKey k = normKey lockPath) sBefore sMid := ⟨hLockPresInner.1, by dsimp only [sMid]; rw [hLockPresInner.2.1]; exact mockRemoveFirstLock_head _ _ _, hLockPresInner.2.2.1, hLockPresInner.2.2.2.1, hLockPresInner.2.2.2.2.1, hLockPresInner.2.2.2.2.2⟩
    have hPresLock0F := nodesFilteredPres_trans (nodesFilteredPres_mono hPLock hBeforePres) (nodesFilteredPres_trans hMidLockPres (nodesFilteredPres_mono hPLock hAfterPres))
    have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by rw [nodesFilteredPres_lookupNode hPresLock0F lockPath (fun _ hk => hk)]; exact hLookLock
    have hConfFin : mockHasConflict sFinal.locks lockIno .exclusive = false := by rw [hPresLock0F.2.1]; exact hConfF
    refine ⟨_, sFinal, hCleanRun, fun h => hNotRmB (hRmIff.mp h), fun h => hNotKFB (hKFIff.mp h), ?_, by rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockFin]; rfl, by rw [mockFs_tryWithFileLock_existing_ok_run sFinal lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockFin hConfFin]; rfl⟩
    rw [hFailNonEmpty (by simp only [repMid, Array.isEmpty, Array.size_push]; exact decide_eq_false (Nat.succ_ne_zero _))]; rfl
/-- Spec 15: `cleanupStaleTempDirs` rejects non-regular `.lock` files into `failed` and preserves `.lock` intact and unlocked if deleting a payload fails. -/
theorem proof_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    AllPass (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, AllPass]; intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩
  let child := mockJoin root childName; let lockPath := mockJoin child ".lock"
  rw [mockFs_stat_run] at hRoot; rw [mockFs_lstat_run, mockFs_join_eq] at hChild; dsimp only at hChild; rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChild; rw [mockFs_lstat_run]
  cases hlLock : mockLstatPure s₀ lockPath with | error _ => dsimp only; intro hFalse; cases hFalse | ok stLock =>
    dsimp only; by_cases hNotFile : (stLock.kind != .file) = true
    · simp only [hNotFile, ↓reduceIte]
      obtain ⟨_, after, repBefore, sBefore, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ := cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec hvr hvp hcV stRoot hRoot hRwx childNode hLookChild
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]
      have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]; dsimp only; rw [hlLock]
      let errExp : TempDirError := { kind := .invalidInput, path := some lockPath, message := "lock entry is not a regular file" }; let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push errExp }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore = (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]; rw [mockFs_join_eq]; dsimp only [child] at hChildBefore; rw [show mockJoin (mockJoin root childName) ".lock" = lockPath from rfl]
        simp only [show (!dirPrefix.toList.isPrefixOf childName.toList) = false by rw [hPref]; rfl, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hChildBefore, show (stChild.kind != .dir) = false by rw [hcDir.1]; rfl, hLockBefore, hNotFile]; exact stateM_pure_run _ _
      cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore with | mk repAfter sFinal =>
        have hExec' := hExec repMid sBefore hSweepMid; rw [hAfterRun] at hExec'; dsimp only at hExec'; obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, hFailMem⟩ := hExec'
        have hAnyErr : (repAfter.failed.any (fun e => e.kind == .invalidInput && e.path == some (mockJoin (mockJoin root childName) ".lock"))) = true := by
          rw [← Array.any_toList, List.any_eq_true]; exact ⟨errExp, hFailMem errExp (by simp [repMid, Array.toList_push]), by dsimp only [errExp, lockPath, child]; rw [Bool.and_eq_true]; exact ⟨by decide, beq_self_eq_true _⟩⟩
        rw [hCleanRun]; dsimp only [AllPass]; rw [allPass_assert, allPass_assert, allPass_assert_end]
        exact ⟨⟨fun h => hNotRmB (hRmIff.mp h), fun h => hNotKFB (hKFIff.mp h)⟩, hAnyErr, by rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres) child hPChild, mockFs_lstat_run]; dsimp only; rw [hChild]; rfl, trivial⟩
    · have hlFile : stLock.kind = .file := by revert hNotFile; cases stLock.kind <;> decide
      simp only [Bool.eq_false_iff.mpr hNotFile, Bool.false_eq_true, ↓reduceIte]; intro ⟨stP, hPay, hpFile⟩ hTryExcl; rw [mockFs_lstat_run] at hPay; dsimp only at hPay
      obtain ⟨ndPay, hLookPay, _⟩ := lookupNode_of_lstat_ok s₀ (mockJoin child "locked_child.txt") stP hPay; obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hlLock
      cases ndLock with | dir _ _ | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile | file lockIno lockC lockT lockM =>
        cases ndPay with | dir _ _ | symlink _ _ => dsimp only [child] at hLookPay; simp [mockLstatPure, hLookPay, mockNodeStat] at hPay; rw [← hPay] at hpFile; cases hpFile | file payIno payC payT payM =>
          have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath (normKey_mockJoin child ".lock" (by decide) (by decide)) lockIno lockC lockT lockM hLookLock hTryExcl
          obtain ⟨rep, s₁, hRun, h1, h2, h3, h4, h5⟩ := spec15_partialFail_exec s₀ root dirPrefix childName maxAgeSec hvr hvp hcV hPref stRoot stChild stLock hRoot hRwx childNode hLookChild hStChild hcDir lockIno lockC lockT lockM hLookLock hStLock hlFile payIno payC payT payM hLookPay hConfF
          rw [mkApiM_cleanupStaleTempDirs_eq] at hRun; dsimp only [StateT.run, mockTime] at hRun; rw [show mockFs.join = mockJoin from rfl] at hRun; dsimp only [Internal.mkApiM, Internal.mkApiFromCapsM, StateT.run, mockTime]; rw [hRun]
          dsimp only [AllPass]; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]; exact ⟨⟨h1, h2⟩, h3, h4, h5, trivial⟩
/-- Non-vacuity `CanReach` witness for Spec 15 (`test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety`). -/
theorem reach_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    CanReach (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, CanReach]
  let s₀ : TempDirMockState := { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .symlink "/etc/passwd" 0)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  have hp := proof_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety s₀ "/tmp" "tmp-" "tmp-a" 10 ⟨by decide, by decide⟩ (by decide) (by decide) ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  dsimp only [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, AllPass] at hp
  rw [mockFs_lstat_run, show mockLstatPure s₀ (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") = .ok (mockNodeStat (.symlink "/etc/passwd" 0)) from rfl] at hp ⊢
  dsimp only at hp ⊢; simp only [show ((mockNodeStat (.symlink "/etc/passwd" 0)).kind != .file) = true from rfl, ↓reduceIte] at hp ⊢; exact hp
end LeanSwe.TempDir.Proofs

import Core.Obeys
import LeanSwe.TempDir.Proofs.RefinesRaw
/-!
Package-level single-step refinement proofs relating `LeanSwe.TempDir.Internal.mkApiFromCapsM`
to the pure domain transitions (`specWithTempDir`, `specWithLockedTempDir`, `specCleanupStaleTempDirs`).
-/
namespace LeanSwe.TempDir.Proofs
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
private theorem resolveRoot_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root? : Option String) (w : W) :
    let r := (Internal.resolveRoot caps.fs caps.env root?).run w
    r.1 = specResolveRoot (proj w) root? ∧ proj r.2 = proj w := by
  have hStep : ∀ (rStr : String) (w1 : W) (hp : proj w1 = proj w),
      let res := (do
        if !Internal.validRoot rStr then return Except.error { kind := .invalidInput, path := some rStr, message := "invalid temporary root path" }
        match ← caps.fs.stat rStr with
        | .error fe => return Except.error (Internal.mapFsError fe)
        | .ok st =>
          if st.kind != .dir then return Except.error { kind := .notADirectory, path := some rStr, message := "temporary root is not a directory" }
          return Except.ok rStr : StateM W (Except TempDirError String)).run w1
      res.1 = (if !specValidRoot rStr then .error { kind := .invalidInput, path := some rStr, message := "invalid temporary root path" }
        else match lookupNode (proj w).nodes rStr with
          | none => .error { kind := .notFound, path := some rStr, message := "not found" }
          | some (.dir _ _) => .ok rStr
          | some _ => .error { kind := .notADirectory, path := some rStr, message := "temporary root is not a directory" }) ∧
        proj res.2 = proj w := by
    intro rStr w1 hp
    by_cases hVr : specValidRoot rStr = true
    · simp only [show Internal.validRoot rStr = true from hVr, hVr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run]; have hSt := raw_fsStat_eq proj caps hRaw w1 rStr
      cases hRun : (caps.fs.stat rStr).run w1 with
      | mk out w2 =>
        rw [hRun] at hSt; dsimp only [mockStatPure, mockLstatPure] at hSt; rw [hSt.1, hp]
        cases lookupNode (proj w).nodes rStr with
        | none => exact ⟨rfl, hSt.2.trans hp⟩
        | some nd => cases nd <;> exact ⟨rfl, hSt.2.trans hp⟩
    · have hVrF : specValidRoot rStr = false := Bool.eq_false_iff.mpr hVr
      simp only [show Internal.validRoot rStr = false from hVrF, hVrF, Bool.not_false, ↓reduceIte]; exact ⟨rfl, hp⟩
  dsimp only [Internal.resolveRoot, specResolveRoot]
  cases root? with
  | some rStr => rw [stateM_bind_run, stateM_pure_run]; exact hStep rStr w rfl
  | none =>
    rw [stateM_bind_run]
    have hEnv := raw_envGetEnv_eq proj caps hRaw w "TMPDIR"
    cases hERun : (caps.env.getEnv "TMPDIR").run w with
    | mk rE w1 =>
      rw [hERun] at hEnv; dsimp only at hEnv; rw [hEnv.1]; simp only [beq_self_eq_true, ↓reduceIte]
      cases (proj w).tmpdir with
      | none => exact hStep "/tmp" w1 hEnv.2
      | some v => exact hStep (if v.isEmpty then "/tmp" else v) w1 hEnv.2
private theorem specResolveRoot_ok_inv (s : TempDirMockState) (root? : Option String) (root : String)
    (hOk : specResolveRoot s root? = .ok root) : specValidRoot root = true ∧ ∃ t m, lookupNode s.nodes root = some (.dir t m) := by
  let r := match root? with | some r => r | none => match s.tmpdir with | some v => if v.isEmpty then "/tmp" else v | none => "/tmp"
  have hOk' : (if !specValidRoot r then (Except.error { kind := .invalidInput, path := some r, message := "invalid temporary root path" } : Except TempDirError String)
      else match lookupNode s.nodes r with
        | none => Except.error { kind := .notFound, path := some r, message := "not found" }
        | some (.dir _ _) => Except.ok r
        | some _ => Except.error { kind := .notADirectory, path := some r, message := "temporary root is not a directory" }) = Except.ok root := hOk
  by_cases hVr : specValidRoot r = true
  · simp only [hVr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk'
    cases hLk : lookupNode s.nodes r with
    | none => rw [hLk] at hOk'; cases hOk'
    | some nd => cases nd with
      | dir t m => rw [hLk] at hOk'; have hrEq : r = root := Except.ok.inj hOk'; exact ⟨hrEq ▸ hVr, t, m, hrEq ▸ hLk⟩
      | file _ _ _ _ | symlink _ _ => rw [hLk] at hOk'; cases hOk'
  · have hVrF : specValidRoot r = false := Bool.eq_false_iff.mpr hVr
    simp only [hVrF, Bool.not_false, ↓reduceIte] at hOk'; cases hOk'
private theorem specChmod_dir_head (s : TempDirMockState) (dir : String) (ti : Int) (m mode : Nat)
    (rest : List (String × MockNode)) (hNorm : normKey dir = dir) (hDisj : ∀ e ∈ rest, normKey e.1 ≠ dir) :
    specChmod { s with nodes := (dir, .dir ti m) :: rest } dir mode = (.ok (), { s with nodes := (dir, .dir ti mode) :: rest }) := by
  dsimp only [specChmod]; rw [hNorm, lookupNode_cons_eq _ _ _ _ rfl]
  simp only [List.map_cons, beq_iff_eq.mpr hNorm, ↓reduceIte]
  congr 2; congr 1; exact list_map_id_of_mem rest _ fun e he => by simp [beq_false_of_ne (hDisj e he)]
private theorem createTempDir_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root? : Option String) (dirPrefix : String) (w : W) :
    let r := (Internal.createTempDir caps.fs caps.uuid caps.env root? dirPrefix).run w
    let sp := specCreateTempDir (proj w) root? dirPrefix
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.createTempDir, specCreateTempDir]
  by_cases hVp : specValidPrefix dirPrefix = true
  · simp only [show Internal.validPrefix dirPrefix = true from hVp, hVp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run]; have hRes := resolveRoot_refines_spec proj caps hRaw root? w
    cases hRRun : (Internal.resolveRoot caps.fs caps.env root?).run w with
    | mk rRoot w1 =>
      rw [hRRun] at hRes; dsimp only at hRes; rw [hRes.1]
      cases hSp : specResolveRoot (proj w) root? with
      | error _ => exact ⟨rfl, hRes.2⟩
      | ok root =>
        obtain ⟨hVr, tRoot, mRoot, hLookRoot⟩ := specResolveRoot_ok_inv (proj w) root? root hSp
        have hLookRootNorm : lookupNode (proj w).nodes (normKey root) = some (.dir tRoot mRoot) := by rwa [lookupNode_normKey]
        have hrNe : root ≠ "" := validRoot_ne_empty root hVr
        rw [stateM_bind_run]; have hU := raw_uuidGet_eq proj caps hRaw w1
        cases hURun : caps.uuid.getUuid.run w1 with
        | mk rU w2 =>
          rw [hURun] at hU; dsimp only at hU; rw [hRes.2] at hU; rw [hU.1]; dsimp only
          have hToStr := raw_uuidToString_eq proj caps hRaw w2 (mockUuidOfNat (proj w).nextUuid)
          have hJoin := raw_fsJoin_eq proj caps hRaw w2 root (dirPrefix ++ mockUuidToString (mockUuidOfNat (proj w).nextUuid))
          rw [hToStr, hJoin]
          have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat (proj w).nextUuid) hVp
          let childNm := dirPrefix ++ mockUuidToString (mockUuidOfNat (proj w).nextUuid)
          let dir := mockJoin root childNm
          have hDirNorm : normKey dir = dir := normKey_mockJoin root childNm hcNe hcNoSlash
          rw [stateM_bind_run]
          have hMk := raw_fsMkdir_eq proj caps hRaw w2 dir false false
          cases hMRun : (caps.fs.mkdir dir false false).run w2 with
          | mk rMk w3 =>
            rw [hMRun] at hMk; dsimp only [specMkdir] at hMk
            rw [hU.2, splitParentChild_mockJoin root childNm hrNe hcNe hcNoSlash] at hMk
            dsimp only at hMk; rw [hLookRootNorm, mockJoin_normKey] at hMk; dsimp only at hMk; rw [hLookRoot]
            have hKindF : ((mockNodeStat (.dir tRoot mRoot)).kind != EntryKind.dir) = false := rfl
            have hWxEq : hasWx (mockNodeStat (.dir tRoot mRoot)) = ((mRoot / 128) % 2 == 1 && (mRoot / 64) % 2 == 1) := hasWx_dir_iff tRoot mRoot
            rw [hKindF, hWxEq] at hMk; simp only [Bool.false_eq_true, ↓reduceIte] at hMk
            by_cases hWx : ((mRoot / 128) % 2 == 1 && (mRoot / 64) % 2 == 1) = true
            · simp only [hWx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMk ⊢
              cases hD : lookupNode (proj w).nodes dir with
              | some nd => cases nd <;> (rw [hD] at hMk; dsimp only at hMk; rw [hMk.1]; exact ⟨rfl, hMk.2⟩)
              | none =>
                rw [hD] at hMk; dsimp only at hMk; rw [hMk.1]; dsimp only; rw [stateM_bind_run]
                have hCh := raw_fsChmod_eq proj caps hRaw w3 dir 0o700
                cases hCRun : (caps.fs.chmod dir 0o700).run w3 with
                | mk rCh w4 =>
                  rw [hCRun] at hCh; dsimp only at hCh; rw [hMk.2] at hCh
                  have hDisj : ∀ e ∈ (proj w).nodes.filter (fun e => !underDir dir e.1), normKey e.1 ≠ dir := fun e he hEq => by
                    have hu : underDir dir e.1 = true := by
                      rw [underDir_eq_of_normKey_eq dir e.1 dir (hEq.trans hDirNorm.symm), underDir_refl dir hDirNorm]
                    have hf := (List.mem_filter.mp he).2; simp [hu] at hf
                  rw [specChmod_dir_head { proj w with nextUuid := (proj w).nextUuid + 1 } dir (proj w).nowSec 0o755 0o700 _ hDirNorm hDisj] at hCh
                  rw [hCh.1]; exact ⟨rfl, hCh.2⟩
            · simp only [Bool.eq_false_iff.mpr hWx, Bool.not_false, ↓reduceIte] at hMk ⊢; rw [hMk.1]; exact ⟨rfl, hMk.2⟩
  · have hVpF : specValidPrefix dirPrefix = false := Bool.eq_false_iff.mpr hVp
    simp only [show Internal.validPrefix dirPrefix = false from hVpF, hVpF, Bool.not_false, ↓reduceIte]; exact ⟨rfl, rfl⟩
private theorem specCreateTempDir_ok_parts (s : TempDirMockState) (root? : Option String) (dirPrefix dir : String)
    (s1 : TempDirMockState) (hOk : specCreateTempDir s root? dirPrefix = (.ok dir, s1)) :
    ∃ root childNm, specValidRoot root = true ∧ childNm ≠ "" ∧ '/' ∉ childNm.toList ∧ dir = mockJoin root childNm ∧
      s1 = { s with nextUuid := s.nextUuid + 1, nodes := (dir, .dir s.nowSec 0o700) :: s.nodes.filter (fun e => !underDir dir e.1) } := by
  dsimp only [specCreateTempDir] at hOk
  by_cases hVp : specValidPrefix dirPrefix = true
  · simp only [hVp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hSp : specResolveRoot s root? with
    | error _ => simp [hSp] at hOk
    | ok root =>
      rw [hSp] at hOk
      obtain ⟨hVr, _, _, hLk⟩ := specResolveRoot_ok_inv s root? root hSp
      dsimp only at hOk; rw [hLk] at hOk; dsimp only at hOk; split at hOk; · cases hOk
      cases hD : lookupNode s.nodes (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s.nextUuid))) with
      | some _ => rw [hD] at hOk; cases hOk
      | none =>
        rw [hD] at hOk; simp only [Prod.mk.injEq, Except.ok.injEq] at hOk
        have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix (mockUuidOfNat s.nextUuid) hVp
        exact ⟨root, dirPrefix ++ mockUuidToString (mockUuidOfNat s.nextUuid), hVr, hcNe, hcNoSlash,
          hOk.1.symm, by rw [← hOk.2, ← hOk.1]⟩
  · simp [Bool.eq_false_iff.mpr hVp] at hOk
private theorem withTempDir_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root? : Option String)
    (dirPrefix : String) (act : StepAction) (w : W) :
    let r := (Internal.withTempDirM caps.fs caps.uuid caps.env root? dirPrefix (fun dir => pure (evalStepAction dir act))).run w
    let sp := specWithTempDir (proj w) root? dirPrefix act
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.withTempDirM, specWithTempDir]; rw [stateM_bind_run]
  have hCre := createTempDir_refines_spec proj caps hRaw root? dirPrefix w
  cases hCRun : (Internal.createTempDir caps.fs caps.uuid caps.env root? dirPrefix).run w with
  | mk rCre w1 =>
    rw [hCRun] at hCre; dsimp only at hCre
    cases hSp : specCreateTempDir (proj w) root? dirPrefix with
    | mk rSp s1 =>
      rw [hSp] at hCre; dsimp only at hCre; rw [hCre.1]
      cases rSp with
      | error _ => exact ⟨rfl, hCre.2⟩
      | ok dir =>
        obtain ⟨root, childNm, _, hcNe, hcNoSlash, hDirEq, hS1Eq⟩ := specCreateTempDir_ok_parts (proj w) root? dirPrefix dir s1 hSp
        have hDirNorm : normKey dir = dir := by rw [hDirEq]; exact normKey_mockJoin root childNm hcNe hcNoSlash
        dsimp only; rw [stateM_bind_run, stateM_tryFinally'_run]
        have hRm := raw_fsRmtree_eq proj caps hRaw w1 dir true
        cases hRRun : (caps.fs.rmtree dir true).run w1 with
        | mk rRm w2 =>
          rw [hRRun] at hRm; dsimp only [specRmtree] at hRm
          rw [hCre.2, hS1Eq, hDirNorm, lookupNode_cons_eq _ _ _ _ rfl] at hRm; dsimp only at hRm
          have hCln : (Internal.cleanupDirIgnoringNotFound caps.fs dir).run w1 = (.ok (), w2) := by
            dsimp only [Internal.cleanupDirIgnoringNotFound]; rw [stateM_bind_run, hRRun]; dsimp only; rw [hRm.1]; rfl
          have hP : (pure (evalStepAction dir act) : StateM W (Except TempDirError String)).run w1 = (evalStepAction dir act, w1) := rfl
          dsimp only [Internal.combineCleanup]
          rw [show (pure (evalStepAction dir act) : StateM W (Except TempDirError String)).run w1 = (evalStepAction dir act, w1) from hP]
          dsimp only; rw [hCln]; dsimp only
          have hFilt : ((dir, MockNode.dir (proj w).nowSec 0o700) :: (proj w).nodes.filter (fun e => !underDir dir e.1)).filter
              (fun e => !underDir dir e.1) = (proj w).nodes.filter (fun e => !underDir dir e.1) := by
            rw [List.filter_cons, underDir_refl dir hDirNorm]; simp
          refine ⟨?_, ?_⟩
          · rw [stateM_pure_run]; cases evalStepAction dir act <;> rfl
          · rw [stateM_pure_run, hRm.2, hFilt, hS1Eq]
private theorem withLockedTempDir_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root? : Option String)
    (dirPrefix : String) (act : StepAction) (w : W) :
    let r := (Internal.withLockedTempDirM caps.fs caps.uuid caps.env root? dirPrefix (fun dir => pure (evalStepAction dir act))).run w
    let sp := specWithLockedTempDir (proj w) root? dirPrefix act
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.withLockedTempDirM, Internal.withTempDirM, specWithLockedTempDir]; rw [stateM_bind_run]
  have hCre := createTempDir_refines_spec proj caps hRaw root? dirPrefix w
  cases hCRun : (Internal.createTempDir caps.fs caps.uuid caps.env root? dirPrefix).run w with
  | mk rCre w1 =>
    rw [hCRun] at hCre; dsimp only at hCre
    cases hSp : specCreateTempDir (proj w) root? dirPrefix with
    | mk rSp s1 =>
      rw [hSp] at hCre; dsimp only at hCre; rw [hCre.1]
      cases rSp with
      | error _ => exact ⟨rfl, hCre.2⟩
      | ok dir =>
        obtain ⟨root, childNm, hVr, hcNe, hcNoSlash, hDirEq, hS1Eq⟩ := specCreateTempDir_ok_parts (proj w) root? dirPrefix dir s1 hSp
        have hrNe : root ≠ "" := validRoot_ne_empty root hVr
        have hDirNorm : normKey dir = dir := by rw [hDirEq]; exact normKey_mockJoin root childNm hcNe hcNoSlash
        have hDirNe : dir ≠ "" := by rw [hDirEq]; exact mockJoin_ne_empty root childNm hcNe
        have hDirNeSlash : dir ≠ "/" := by rw [hDirEq]; exact mockJoin_ne_slash root childNm hrNe hcNe
        have hLockNorm : normKey (mockJoin dir ".lock") = mockJoin dir ".lock" := normKey_mockJoin dir ".lock" (by decide) (by decide)
        have hLockNe : normKey (mockJoin dir ".lock") ≠ dir := by
          rw [hDirEq]; exact payload_ne_dir root childNm ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
        have hLockUnder : underDir dir (mockJoin dir ".lock") = true :=
          underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
        have hJoin := raw_fsJoin_eq proj caps hRaw w1 dir ".lock"
        have hActEq : (do return Except.ok (← (pure (evalStepAction dir act) : StateM W (Except TempDirError String)))) =
            (pure (.ok (evalStepAction dir act)) : StateM W (Except FsError (Except TempDirError String))) := rfl
        rw [stateM_bind_run, stateM_tryFinally'_run]; dsimp only
        rw [stateM_bind_run, hJoin, hActEq]
        have hLk := raw_fsWithFileLockRet_eq proj caps hRaw w1 (mockJoin dir ".lock") .shared true (evalStepAction dir act)
        cases hLRun : (caps.fs.withFileLock (mockJoin dir ".lock") .shared true (pure (.ok (evalStepAction dir act)))).run w1 with
        | mk rLk w2 =>
          rw [hLRun] at hLk; dsimp only [specWithFileLockRet] at hLk
          have hNoneLk : lookupNode s1.nodes (normKey (mockJoin dir ".lock")) = none := by
            rw [hLockNorm, hS1Eq]; exact lookupNode_lock_mk_none (proj w).nodes dir (.dir (proj w).nowSec 0o700) hDirNorm hLockNe hLockUnder
          rw [hCre.2, hNoneLk] at hLk; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hLk
          rw [hLk.1]; dsimp only
          have hRm := raw_fsRmtree_eq proj caps hRaw w2 dir true
          cases hRRun : (caps.fs.rmtree dir true).run w2 with
          | mk rRm w3 =>
            rw [hRRun] at hRm; dsimp only [specRmtree] at hRm
            have hFreshEq : freshInode s1 = freshInode (proj w) := by rw [hS1Eq]; rfl
            rw [hLk.2, hFreshEq, hLockNorm, hS1Eq] at hRm
            have hLookDir : lookupNode ((mockJoin dir ".lock", MockNode.file (freshInode (proj w)) "" (proj w).nowSec 0o644) ::
                (dir, MockNode.dir (proj w).nowSec 0o700) :: (proj w).nodes.filter (fun e => !underDir dir e.1)) dir =
                some (.dir (proj w).nowSec 0o700) := by
              rw [lookupNode_cons_lock_dir _ dir _ hDirNorm hLockNe, lookupNode_cons_eq _ _ _ _ rfl]
            rw [hDirNorm, hLookDir] at hRm; dsimp only at hRm
            have hCln : (Internal.cleanupDirIgnoringNotFound caps.fs dir).run w2 = (.ok (), w3) := by
              dsimp only [Internal.cleanupDirIgnoringNotFound]; rw [stateM_bind_run, hRRun]; dsimp only; rw [hRm.1]; rfl
            rw [show (pure (evalStepAction dir act) : StateM W (Except TempDirError String)).run w2 = (evalStepAction dir act, w2) from rfl]; dsimp only; rw [hCln]; dsimp only
            have hFilt : ((mockJoin dir ".lock", MockNode.file (freshInode (proj w)) "" (proj w).nowSec 0o644) ::
                (dir, MockNode.dir (proj w).nowSec 0o700) :: (proj w).nodes.filter (fun e => !underDir dir e.1)).filter
                (fun e => !underDir dir e.1) = (proj w).nodes.filter (fun e => !underDir dir e.1) := by
              rw [List.filter_cons, hLockUnder, List.filter_cons, underDir_refl dir hDirNorm]; simp
            refine ⟨?_, ?_⟩
            · cases evalStepAction dir act <;> rfl
            · rw [stateM_pure_run, hRm.2, hFilt, hS1Eq]
private theorem sweepEntry_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep)
    (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int) (rep : CleanupReport) (entryName : String) (w : W) :
    let r := (Internal.sweepEntry caps.fs root dirPrefix maxAgeSec nowSec rep entryName).run w
    let sp := specSweepEntry (proj w) root dirPrefix maxAgeSec nowSec rep entryName
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.sweepEntry, specSweepEntry]; rw [raw_fsJoin_eq proj caps hRaw w root entryName]
  by_cases hPref : (!dirPrefix.toList.isPrefixOf entryName.toList) = true
  · simp only [hPref, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [Bool.eq_false_iff.mpr hPref, Bool.false_eq_true, ↓reduceIte]; rw [stateM_bind_run]
    have hLs := raw_fsLstat_eq proj caps hRaw w (mockJoin root entryName)
    cases hLRun : (caps.fs.lstat (mockJoin root entryName)).run w with
    | mk rChild w1 =>
      rw [hLRun] at hLs; dsimp only [mockLstatPure] at hLs; rw [hLs.1]
      cases hC : lookupNode (proj w).nodes (mockJoin root entryName) with
      | none => exact ⟨rfl, hLs.2⟩
      | some nd => cases nd with
        | file _ _ _ _ | symlink _ _ => exact ⟨rfl, hLs.2⟩
        | dir modSec _ =>
          simp only [mockNodeStat, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte,
            raw_fsJoin_eq proj caps hRaw w1]
          rw [stateM_bind_run]
          have hLk := raw_fsLstat_eq proj caps hRaw w1 (mockJoin (mockJoin root entryName) ".lock")
          cases hLkRun : (caps.fs.lstat (mockJoin (mockJoin root entryName) ".lock")).run w1 with
          | mk rLk w2 =>
            rw [hLkRun] at hLk; dsimp only [mockLstatPure] at hLk; rw [hLk.1, hLs.2]
            cases hLNd : lookupNode (proj w).nodes (mockJoin (mockJoin root entryName) ".lock") with
            | some ndL => cases ndL with
              | dir _ _ | symlink _ _ => exact ⟨rfl, hLk.2.trans hLs.2⟩
              | file ino _ _ _ =>
                simp only [mockNodeStat, show (EntryKind.file != EntryKind.file) = false from rfl, Bool.false_eq_true, ↓reduceIte]
                rw [stateM_bind_run]
                have hTry := raw_fsTryLockRemove_eq proj caps hRaw w2 (mockJoin root entryName) (mockJoin (mockJoin root entryName) ".lock")
                cases hTRun : (caps.fs.tryWithFileLock _ .exclusive false _).run w2 with
                | mk rT w3 =>
                  rw [hTRun] at hTry; dsimp only [specTryLockRemove] at hTry; rw [hLk.2, hLs.2, lookupNode_normKey, hLNd] at hTry
                  by_cases hConf : mockHasConflict (proj w).locks ino .exclusive = true
                  · simp only [hConf, ↓reduceIte] at hTry ⊢; rw [hTry.1]; exact ⟨rfl, hTry.2⟩
                  · simp only [Bool.eq_false_iff.mpr hConf, Bool.false_eq_true, ↓reduceIte] at hTry ⊢
                    cases hRem : specRemoveLockedDir (proj w) (mockJoin root entryName) (mockJoin (mockJoin root entryName) ".lock") with
                    | mk rRem sRem => rw [hRem] at hTry; rw [hTry.1]; cases rRem <;> exact ⟨rfl, hTry.2⟩
            | none =>
              simp only [show (FsErrorKind.notFound != FsErrorKind.notFound) = false from rfl, Bool.false_eq_true, ↓reduceIte]
              by_cases hFresh : nowSec - modSec ≤ (maxAgeSec : Int)
              · simp only [hFresh, ↓reduceIte]; exact ⟨rfl, hLk.2.trans hLs.2⟩
              · simp only [hFresh, ↓reduceIte, Internal.cleanupDirIgnoringNotFound]
                rw [stateM_bind_run, stateM_bind_run (x := caps.fs.rmtree (mockJoin root entryName) true)]
                have hRm := raw_fsRmtree_eq proj caps hRaw w2 (mockJoin root entryName) true
                cases hRRun : (caps.fs.rmtree (mockJoin root entryName) true).run w2 with
                | mk rRm w3 =>
                  rw [hRRun] at hRm; dsimp only [specRmtree] at hRm; rw [hLk.2, hLs.2, lookupNode_normKey, hC] at hRm
                  dsimp only at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩
private theorem sweepEntries_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root dirPrefix : String)
    (maxAgeSec : Nat) (nowSec : Int) (rep : CleanupReport) (names : List String) (w : W) :
    let r := (Internal.sweepEntries caps.fs root dirPrefix maxAgeSec nowSec rep names).run w
    let sp := specSweepEntries (proj w) root dirPrefix maxAgeSec nowSec rep names
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  induction names generalizing rep w with
  | nil => exact ⟨rfl, rfl⟩
  | cons name rest ih =>
    dsimp only [Internal.sweepEntries, specSweepEntries]; rw [stateM_bind_run]
    have h1 := sweepEntry_refines_spec proj caps hRaw root dirPrefix maxAgeSec nowSec rep name w
    cases hRun : (Internal.sweepEntry caps.fs root dirPrefix maxAgeSec nowSec rep name).run w with
    | mk rep1 w1 =>
      rw [hRun] at h1; dsimp only at h1
      cases hSp1 : specSweepEntry (proj w) root dirPrefix maxAgeSec nowSec rep name with
      | mk repS sS =>
        rw [hSp1] at h1; dsimp only at h1
        have hTail := ih rep1 w1; dsimp only at hTail
        have ⟨hRep, hSt⟩ := h1; subst hRep; rw [hSt] at hTail; exact hTail
private theorem cleanupStaleTempDirs_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (root? : Option String)
    (dirPrefix : String) (maxAgeSec : Nat) (w : W) :
    let r := (Internal.cleanupStaleTempDirsM caps.fs caps.time caps.env root? dirPrefix maxAgeSec).run w
    let sp := specCleanupStaleTempDirs (proj w) root? dirPrefix maxAgeSec
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.cleanupStaleTempDirsM, specCleanupStaleTempDirs]
  by_cases hVp : specValidPrefix dirPrefix = true
  · simp only [show Internal.validPrefix dirPrefix = true from hVp, hVp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run]; have hRes := resolveRoot_refines_spec proj caps hRaw root? w
    cases hRRun : (Internal.resolveRoot caps.fs caps.env root?).run w with
    | mk rRoot w1 =>
      rw [hRRun] at hRes; dsimp only at hRes; rw [hRes.1]
      cases hSpR : specResolveRoot (proj w) root? with
      | error _ => exact ⟨rfl, hRes.2⟩
      | ok root =>
        dsimp only; rw [stateM_bind_run]; have hTm := raw_timeNow_eq proj caps hRaw w1
        cases hTRun : caps.time.nowTimestamp.run w1 with
        | mk ts w2 =>
          rw [hTRun] at hTm; dsimp only at hTm; rw [hTm.1, hRes.2, timestamp_ofInt_toSec]
          dsimp only; rw [stateM_bind_run]; have hLs := raw_fsListDir_eq proj caps hRaw w2 root
          cases hLRun : (caps.fs.listDir root).run w2 with
          | mk rList w3 =>
            rw [hLRun] at hLs; dsimp only at hLs; rw [hLs.1, hTm.2, hRes.2]
            have hW3 : proj w3 = proj w := hLs.2.trans (hTm.2.trans hRes.2)
            cases hLd : specListDir (proj w) root with
            | error fe =>
              exact ⟨by dsimp only; exact congrArg Except.error (mapFsError_eq fe), hW3⟩
            | ok names =>
              dsimp only; rw [stateM_bind_run]
              have hSw := sweepEntries_refines_spec proj caps hRaw root dirPrefix maxAgeSec (proj w).nowSec {} names.toList w3
              cases hSRun : (Internal.sweepEntries caps.fs root dirPrefix maxAgeSec (proj w).nowSec {} names.toList).run w3 with
              | mk repFin w4 =>
                rw [hSRun] at hSw; dsimp only at hSw; rw [hW3] at hSw
                dsimp only; rw [hSw.1]; simp only [internal_sortStrings_eq]; exact ⟨rfl, hSw.2⟩
  · have hVpF : specValidPrefix dirPrefix = false := Bool.eq_false_iff.mpr hVp
    simp only [show Internal.validPrefix dirPrefix = false from hVpF, hVpF, Bool.not_false, ↓reduceIte]; exact ⟨rfl, rfl⟩
/-- Compositional single-step refinement lemma for `LeanSwe.TempDir.Internal.mkApiFromCapsM`. -/
theorem refinesStepFromFinally_mkApiFromCapsM :
    Core.ObeysStepFromFinally id tempDirStepWf execRawStep allowedRawStep
      tempDirStepWf Internal.mkApiFromCapsM execPkgStep allowedPkgStep := by
  intro W proj caps hRaw w req _
  cases req with
  | withTempDir root? dirPrefix act =>
    have h := withTempDir_refines_spec proj caps hRaw root? dirPrefix act w
    exact ⟨congrArg PkgStepOut.dirRes h.1, h.2⟩
  | withLockedTempDir root? dirPrefix act =>
    have h := withLockedTempDir_refines_spec proj caps hRaw root? dirPrefix act w
    exact ⟨congrArg PkgStepOut.dirRes h.1, h.2⟩
  | cleanupStaleTempDirs root? dirPrefix maxAgeSec =>
    have h := cleanupStaleTempDirs_refines_spec proj caps hRaw root? dirPrefix maxAgeSec w
    exact ⟨congrArg PkgStepOut.report h.1, h.2⟩
end LeanSwe.TempDir.Proofs

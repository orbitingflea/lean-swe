import LeanSwe.TempDir.Proofs.Shared

set_option Elab.async false

namespace LeanSwe.TempDir.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)

private theorem spec1_write_clean_step (s₀ sMk : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (hLookDirMk : lookupNode sMk.nodes (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = some (.dir s₀.nowSec 0o700)) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sAct sFin : TempDirMockState,
      (mockFs.writeText (mockJoin dir "payload.txt") "hello").run sMk = (.ok (), sAct) ∧
      (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) ∧
      ((mockFs.lstat dir).run sFin).1.isOk = false := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  let payload := mockJoin dir "payload.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempDirMockState, s =
      { sMk with
        nodes := (normKey payload, .file (freshInode sMk) "hello" sMk.nowSec 0o644) ::
          sMk.nodes.filter (fun e => normKey e.1 != normKey payload)
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hWrite : (mockFs.writeText (mockJoin dir "payload.txt") "hello").run sMk = (.ok (), sAct) := by
    rw [mockFs_writeText_run, ← hsAct]
  have hPayloadNeDir : normKey payload ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) "payload.txt" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hLookDirAfterWrite : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAct]
    unfold lookupNode
    dsimp only
    have hb : (normKey (normKey payload) == normKey dir) = false := by
      rw [normKey_idem, hDirNorm, beq_false_of_ne hPayloadNeDir]
    rw [List.find?_cons, hb]
    have hfu := lookupNode_filter_of_preserved sMk.nodes (fun e => normKey e.1 != normKey payload) dir
      (by
        intro e _ he
        simp only [bne_iff_ne, ne_eq]
        rw [he, hDirNorm]
        exact ne_comm.mp hPayloadNeDir)
    exact hfu.trans hLookDirMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s =
      { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) := by
    rw [hsFin]
    exact cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookDirAfterWrite⟩
  have hGone : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  exact ⟨sAct, sFin, hWrite, hClean, hGone⟩

/-- Spec 1: `withTempDir` creates `<root>/<dirPrefix><uuid>` with mode `0o700`, executes `action dir`, returns `.ok val`, and removes `dir` on exit. -/
theorem proof_tempdir_withTempDir_okCleansUpAndSetsMode :
    AllPass (test_tempdir_withTempDir_okCleansUpAndSetsMode
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_okCleansUpAndSetsMode, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨sMk, hCreate, hLstatDirMk, hLookDirMk⟩ :=
    spec1_mk_step s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨sAct, sFin, hWrite, hClean, hGone⟩ :=
    spec1_write_clean_step s₀ sMk root dirPrefix hvr hvp hLookDirMk
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [stateM_bind_run, hCreate]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hLstatDirMk]
  dsimp only [mockNodeStat]
  have hHead : (EntryKind.dir != EntryKind.dir || (448 : Nat) != 0o700) = false := by decide
  rw [hHead, Bool.false_or, bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hWrite]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, hGone, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 1 (`test_tempdir_withTempDir_okCleansUpAndSetsMode`). -/
theorem reach_tempdir_withTempDir_okCleansUpAndSetsMode :
    CanReach (test_tempdir_withTempDir_okCleansUpAndSetsMode
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_okCleansUpAndSetsMode, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨42, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨sMk, hCreate, hLstatDirMk, hLookDirMk⟩ :=
    spec1_mk_step s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨sAct, sFin, hWrite, hClean, hGone⟩ :=
    spec1_write_clean_step s₀ sMk "/tmp" "tmp-" rfl rfl hLookDirMk
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [stateM_bind_run, hCreate]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hLstatDirMk]
  dsimp only [mockNodeStat]
  have hHead : (EntryKind.dir != EntryKind.dir || (448 : Nat) != 0o700) = false := by decide
  rw [hHead, Bool.false_or, bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hWrite]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, hGone, trivial⟩

/-- Shared proof helper `lookupNode_filter_none_of_none`. -/
theorem lookupNode_filter_none_of_none (nodes : List (String × MockNode))
    (pred : (String × MockNode) → Bool) (p : String)
    (h : lookupNode nodes p = none) :
    lookupNode (nodes.filter pred) p = none := by
  unfold lookupNode at h ⊢
  dsimp only at h ⊢
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    cases hb : (normKey x.1 == normKey p) with
    | true => simp [hb] at h
    | false =>
      simp only [List.find?_cons, hb] at h
      rw [List.filter_cons]
      split
      · simp only [List.find?_cons, hb]
        exact ih h
      · exact ih h

private theorem lookupNode_none_of_lstat_isOk_false (s : TempDirMockState) (p : String)
    (h : ((mockFs.lstat p).run s).1.isOk = false) :
    lookupNode s.nodes p = none := by
  rw [mockFs_lstat_run] at h
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none => rfl
  | some nd => simp [hl, Except.isOk, Except.toBool] at h

private theorem mockJoin_tmp_ne_other (childName : String)
    (hcNe : childName ≠ "") (hcNoSlash : '/' ∉ childName.toList) :
    normKey (mockJoin "/tmp" childName) ≠ normKey "/other" := by
  rw [normKey_mockJoin "/tmp" childName hcNe hcNoSlash]
  intro hEq
  have hl := congrArg String.toList hEq
  have h1 := mockJoin_eq_append_of_ne_empty "/tmp" childName (by decide)
  have htmp : normKey "/tmp" = "/tmp" := by decide
  rw [h1, htmp] at hl
  rw [show ("/tmp" == "/") = false from by decide] at hl
  simp only [Bool.false_eq_true, ↓reduceIte] at hl
  have hdrop : (normKey "/other").toList = ['/','o','t','h','e','r'] := by decide
  have htmpList : ("/tmp" : String).toList = ['/','t','m','p'] := by decide
  rw [hdrop, htmpList] at hl
  simp at hl

private theorem createTempDir_mock_steps_custom_rm (s₀ : TempDirMockState) (root dirPrefix : String)
    (rm : String → Bool → StateM TempDirMockState (Except FsError Unit))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir { mockFs with rmtree := rm } mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) := by
  intro u dir sMk
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hSp : splitParentChild dir = some (normKey root, dirPrefix ++ mockUuidToString u) :=
    splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) (dirPrefix ++ mockUuidToString u) = dir :=
    mockJoin_normKey root (dirPrefix ++ mockUuidToString u)
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by
    unfold mockLstatPure at hNone
    cases hl : lookupNode s₀.nodes dir with
    | none => rfl
    | some dn =>
      rw [hl] at hNone
      simp [Except.toBool] at hNone
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hvp' : Internal.validPrefix dirPrefix = true := by simpa [Internal.validPrefix] using hvp
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  have hMk : ({ mockFs with rmtree := rm }.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.ok (), { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDirNone]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hCh : ({ mockFs with rmtree := rm }.chmod dir 0o700).run
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } =
      (.ok (), sMk) := by
    dsimp only [mockFs, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm]
    have hLook : lookupNode ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)) dir =
        some (MockNode.dir s₀.nowSec 0o755) :=
      lookupNode_cons_eq _ _ _ _ rfl
    rw [hLook]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
    have hMapId : (s₀.nodes.filter (fun e => !underDir dir e.1)).map
        (fun x => if normKey x.1 == dir then (x.1, match x.2 with
          | MockNode.dir t _ => MockNode.dir t 0o700
          | MockNode.file ino c t _ => MockNode.file ino c t 0o700
          | MockNode.symlink tgt t => MockNode.symlink tgt t) else x) =
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      apply list_map_id_of_mem
      intro x hx
      have hKeep := (List.mem_filter.mp hx).2
      have hne : (normKey x.1 == dir) = false := by
        rw [beq_false_of_ne]
        intro hEq
        simp only [underDir, hDirNorm, hEq, beq_self_eq_true, Bool.true_or, Bool.not_true] at hKeep
        exact Bool.noConfusion hKeep
      simp [hne]
    show (Except.ok (), {
      nodes := List.map (fun x => if (normKey x.1 == dir) = true then _ else x)
        ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)),
      locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec,
      nextUuid := s₀.nextUuid + 1 }) = (Except.ok (), sMk)
    simp only [List.map_cons, hDirNorm, beq_self_eq_true, ↓reduceIte]
    exact congrArg (fun ns => ((Except.ok (), ({
      nodes := (dir, MockNode.dir s₀.nowSec 0o700) :: ns,
      locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec,
      nextUuid := s₀.nextUuid + 1 } : TempDirMockState)) : Except FsError Unit × TempDirMockState)) hMapId
  have hResStep : (Internal.resolveRoot { mockFs with rmtree := rm } mockEnv (some root)).run s₀ = (.ok root, s₀) := by
    have h := resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
    exact h
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hResStep]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : mockFs.join root (dirPrefix ++ mockUuid.toString u) = dir := rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMk]
  rw [stateM_bind_run, hCh]
  rw [stateM_pure_run]

private theorem spec2_exec_parts (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let rmFail : String → Bool → StateM TempDirMockState (Except FsError Unit) :=
      fun _ _ => pure (.error { kind := .permissionDenied, message := "cleanup failed" })
    let fsFailClean : FsApiM (StateM TempDirMockState) := { mockFs with rmtree := rmFail }
    ∃ sMk sAct sFin : TempDirMockState,
      (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (mockFs.writeText (mockFs.join dir "tmp.txt") "data").run sMk = (.ok (), sAct) ∧
      (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) ∧
      ((mockFs.lstat dir).run sFin).1.isOk = false ∧
      (Internal.createTempDir fsFailClean mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk =
        (.error (Internal.mapFsError { kind := .permissionDenied, message := "cleanup failed" }), sMk) := by
  intro u dir rmFail fsFailClean
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreate1 := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate1
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate1
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  let tmpPath := mockJoin dir "tmp.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempDirMockState, s =
      { sMk with
        nodes := (normKey tmpPath, .file (freshInode sMk) "data" sMk.nowSec 0o644) ::
          sMk.nodes.filter (fun e => normKey e.1 != normKey tmpPath)
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hTmpNeDir : normKey tmpPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) "tmp.txt" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hLookDirAct : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAct]
    unfold lookupNode
    dsimp only
    have hb : (normKey (normKey tmpPath) == normKey dir) = false := by
      rw [normKey_idem, hDirNorm, beq_false_of_ne hTmpNeDir]
    rw [List.find?_cons, hb]
    have hfu := lookupNode_filter_of_preserved sMk.nodes (fun e => normKey e.1 != normKey tmpPath) dir
      (by
        intro e _ he
        simp only [bne_iff_ne, ne_eq]
        rw [he, hDirNorm]
        exact ne_comm.mp hTmpNeDir)
    exact hfu.trans hLookDirMk
  have hWrite1 : (mockFs.writeText (mockFs.join dir "tmp.txt") "data").run sMk = (.ok (), sAct) := by
    rw [mockFs_join_eq, mockFs_writeText_run, ← hsAct]
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s =
      { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) := by
    rw [hsFin]; exact cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookDirAct⟩
  have hGone1 : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  have hCreate2 := createTempDir_mock_steps_custom_rm s₀ root dirPrefix rmFail hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate2
  rw [← hsMk] at hCreate2
  have hClean2 : (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk =
      (.error (Internal.mapFsError { kind := .permissionDenied, message := "cleanup failed" }), sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsFailClean, rmFail]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.permissionDenied == FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
  exact ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩

/-- Spec 2: `withTempDir` cleans up `dir` and preserves `action`'s `.error` even when cleanup also fails. -/
theorem proof_tempdir_withTempDir_errorCleansUpAndPreservesError :
    AllPass (test_tempdir_withTempDir_errorCleansUpAndPreservesError
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_errorCleansUpAndPreservesError, AllPass]
  intro s₀ root dirPrefix actionErr ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩ :=
    spec2_exec_parts s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate1]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hWrite1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert]
  have hGone1' : ((mockFs.lstat (mockFs.join root (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      sFin).1.isOk = false := by
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact hGone1
  refine ⟨rfl, hGone1', ?_⟩
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate2]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
  dsimp only
  rw [hClean2]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert_end]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 2 (`test_tempdir_withTempDir_errorCleansUpAndPreservesError`). -/
theorem reach_tempdir_withTempDir_errorCleansUpAndPreservesError :
    CanReach (test_tempdir_withTempDir_errorCleansUpAndPreservesError
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_errorCleansUpAndPreservesError, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  let err : TempDirError := { kind := .ioError, path := none, message := "boom" }
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨err, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩ :=
    spec2_exec_parts s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate1]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hWrite1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert]
  have hGone1' : ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      sFin).1.isOk = false := by
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact hGone1
  refine ⟨rfl, hGone1', ?_⟩
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate2]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
  dsimp only
  rw [hClean2]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert_end]
  exact ⟨rfl, trivial⟩

private theorem spec3_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let fsFailClean : FsApiM (StateM TempDirMockState) :=
      { mockFs with rmtree := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "rm failed" }) }
    ∃ s₁ : TempDirMockState,
      ((Internal.mkApiM fsFailClean mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix fun _ =>
        pure (.ok val)).run s₀ =
        (.error (Internal.mapFsError { kind := .permissionDenied, path := some (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))), message := "rm failed" }), s₁) := by
  intro fsFailClean
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  have hCreate := createTempDir_mock_steps_custom_rm s₀ root dirPrefix
    (fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "rm failed" }))
    hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  let ce := Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "rm failed" }
  have hClean : (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk = (.error ce, sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsFailClean]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.permissionDenied == FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
  have hRun := withTempDir_mock_run_step fsFailClean mockTime mockUuid mockEnv s₀ sMk sMk sMk
    (some root) dirPrefix dir (fun _ => pure (.ok val)) (.ok val) (.error ce)
    hCreate (stateM_pure_run _ _) hClean
  exact ⟨sMk, hRun⟩

/-- Spec 3: `withTempDir` propagates cleanup error when `action` returns `.ok`. -/
theorem proof_tempdir_withTempDir_cleanupErrorReturnedOnOk :
    AllPass (test_tempdir_withTempDir_cleanupErrorReturnedOnOk
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨s₁, hRun⟩ := spec3_exec s₀ root dirPrefix val hvr hvp stRoot hRootPure hRwx hNonePure
  rw [hRun]
  dsimp only
  rw [allPass_assert_end]
  refine ⟨⟨_, rfl, rfl, ?_⟩, trivial⟩
  dsimp only [Internal.mapFsError]
  rw [show ("rm failed" : String).isEmpty = false from rfl]
  simp

/-- Non-vacuity `CanReach` witness for Spec 3 (`test_tempdir_withTempDir_cleanupErrorReturnedOnOk`). -/
theorem reach_tempdir_withTempDir_cleanupErrorReturnedOnOk :
    CanReach (test_tempdir_withTempDir_cleanupErrorReturnedOnOk
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_cleanupErrorReturnedOnOk, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨7, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s₁, hRun⟩ := spec3_exec s₀ "/tmp" "tmp-" 7 rfl rfl
    (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [hRun]
  dsimp only
  rw [canReach_assert_end]
  refine ⟨⟨_, rfl, rfl, ?_⟩, trivial⟩
  dsimp only [Internal.mapFsError]
  rw [show ("rm failed" : String).isEmpty = false from rfl]
  simp

private theorem createTempDir_mock_collision (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (stExist : FileStat)
    (hExist : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = .ok stExist) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let te := Internal.mapFsError { kind := .alreadyExists, path := some dir, message := "exists" }
    (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.error te, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
  intro u dir te
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hSp : splitParentChild dir = some (normKey root, dirPrefix ++ mockUuidToString u) :=
    splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) (dirPrefix ++ mockUuidToString u) = dir :=
    mockJoin_normKey root (dirPrefix ++ mockUuidToString u)
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookExist : ∃ existNode, lookupNode s₀.nodes dir = some existNode := by
    unfold mockLstatPure at hExist
    cases hl : lookupNode s₀.nodes dir with
    | none =>
      dsimp only [dir] at hl
      rw [hl] at hExist
      simp at hExist
    | some en => exact ⟨en, rfl⟩
  rcases hLookExist with ⟨existNode, hLookExist⟩
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hvp' : Internal.validPrefix dirPrefix = true := by simpa [Internal.validPrefix] using hvp
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  have hMkFail : (mockFs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.error { kind := .alreadyExists, path := some dir, message := "exists" },
       { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookExist]
    cases existNode <;> exact stateM_pure_run _ _
  have hResStep := resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hResStep]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : mockFs.join root (dirPrefix ++ mockUuid.toString u) = dir := rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMkFail]
  dsimp only
  rw [stateM_pure_run]

/-- Spec 4: Exclusive creation rejects pre-existing directories or symlinks with `.alreadyExists`. -/
theorem proof_tempdir_withTempDir_collisionRejected :
    AllPass (test_tempdir_withTempDir_collisionRejected
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_collisionRejected, AllPass]
  intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarker
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  rintro ⟨stExist, hExist, _⟩
  have hExistPure : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = .ok stExist := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hExist
    exact hExist
  have hCreErr := createTempDir_mock_collision s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx stExist hExistPure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  have hMarkerAfter : ((mockFs.lstat markerPath).run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false := by
    rw [mockFs_lstat_run] at hMarker ⊢
    exact hMarker
  have hDirAfter : ((mockFs.lstat (mockFs.join root (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = true := by
    rw [hExist]
    rfl
  exact ⟨⟨_, rfl, rfl⟩, hMarkerAfter, hDirAfter, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 4 (`test_tempdir_withTempDir_collisionRejected`). -/
theorem reach_tempdir_withTempDir_collisionRejected :
    CanReach (test_tempdir_withTempDir_collisionRejected
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_collisionRejected, CanReach]
  let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState,
      s = { nodes := [("/tmp", .dir 0 0o755), (dir, .dir 0 0o755)] } := ⟨_, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"/other", ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]
    unfold mockStatPure mockLstatPure
    rw [lookupNode_cons_eq "/tmp" (.dir 0 0o755) [(dir, .dir 0 0o755)] "/tmp" rfl]
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
  have hDirNeOther : normKey dir ≠ normKey "/other" := mockJoin_tmp_ne_other _ hcNe hcNoSlash
  have hMarker : ((mockFs.lstat "/other").run s₀).1.isOk = false := by
    rw [hs₀]
    apply mockFs_lstat_isOk_false_of_lookup_none
    rw [lookupNode_cons_ne "/tmp" _ _ "/other" (by decide)]
    rw [lookupNode_cons_ne dir _ [] "/other" hDirNeOther]
    rfl
  rw [canReach_assume]; refine ⟨hMarker, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hTmpNeDir : normKey "/tmp" ≠ normKey dir :=
    ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
  have hNextId : s₀.nextUuid = 1 := by rw [hs₀]
  have hExistPure : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) =
      .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hNextId, hs₀]
    unfold mockLstatPure
    dsimp only
    rw [lookupNode_cons_ne "/tmp" _ _ dir hTmpNeDir]
    rw [lookupNode_cons_eq dir (.dir 0 0o755) [] dir rfl]
  have hExist : ∃ stExist, ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1 = .ok stExist ∧ (stExist.kind = EntryKind.dir ∨ stExist.kind = EntryKind.symlink) :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hExistPure, Or.inl rfl⟩
  rw [canReach_assume]; refine ⟨hExist, ?_⟩
  have hCreErr := createTempDir_mock_collision s₀ "/tmp" "tmp-" rfl rfl
    (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ (mockNodeStat (.dir 0 0o755)) hExistPure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  have hMarkerAfter : ((mockFs.lstat "/other").run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false := by
    rw [mockFs_lstat_run] at hMarker ⊢
    exact hMarker
  have hDirAfter : ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = true := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq, hExistPure]
    rfl
  exact ⟨⟨_, rfl, rfl⟩, hMarkerAfter, hDirAfter, trivial⟩

private theorem spec5_exec (s₀ : TempDirMockState) (root dirPrefix markerPath : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hMarker : ((mockFs.lstat markerPath).run s₀).1.isOk = false)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let fsBadChmod : FsApiM (StateM TempDirMockState) :=
      { mockFs with chmod := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "chmod denied" }) }
    ∃ s₁ : TempDirMockState,
      (Internal.createTempDir fsBadChmod mockUuid mockEnv (some root) dirPrefix).run s₀ =
        (.error (Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "chmod denied" }), s₁) ∧
      ((mockFs.lstat markerPath).run s₁).1.isOk = false ∧
      ((mockFs.lstat dir).run s₁).1.isOk = false := by
  intro u dir fsBadChmod
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hSp : splitParentChild dir = some (normKey root, dirPrefix ++ mockUuidToString u) :=
    splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) (dirPrefix ++ mockUuidToString u) = dir :=
    mockJoin_normKey root (dirPrefix ++ mockUuidToString u)
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by
    unfold mockLstatPure at hNone
    cases hl : lookupNode s₀.nodes dir with
    | none => rfl
    | some dn =>
      rw [hl] at hNone
      simp [Except.toBool] at hNone
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hvp' : Internal.validPrefix dirPrefix = true := by simpa [Internal.validPrefix] using hvp
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (fsBadChmod.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (), sMk) := by
    rw [hsMk]
    dsimp only [fsBadChmod, mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDirNone]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o755) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean : (Internal.cleanupDirIgnoringNotFound fsBadChmod dir).run sMk = (.ok (), sFin) := by
    rw [hsFin]
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsBadChmod, mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm, hLookDirMk]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hResStep : (Internal.resolveRoot fsBadChmod mockEnv (some root)).run s₀ = (.ok root, s₀) :=
    resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  have hChFail : (fsBadChmod.chmod dir 0o700).run sMk =
      (.error { kind := .permissionDenied, path := some dir, message := "chmod denied" }, sMk) := by
    dsimp only [fsBadChmod]
    exact stateM_pure_run _ _
  have hCreErr : (Internal.createTempDir fsBadChmod mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.error (Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "chmod denied" }), sFin) := by
    dsimp only [Internal.createTempDir]
    simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hResStep]
    dsimp only
    rw [stateM_bind_run, hUuidStep]
    dsimp only
    have hDirEq : fsBadChmod.join root (dirPrefix ++ mockUuid.toString u) = dir := by
      dsimp only [fsBadChmod]
      rw [mockFs_join_eq, mockUuid_toString_eq]
    simp only [hDirEq]
    rw [stateM_bind_run, hMk]
    dsimp only
    rw [stateM_bind_run, hChFail]
    dsimp only
    rw [stateM_bind_run, hClean]
    dsimp only
    rw [stateM_pure_run]
  have hMarkerNone0 : lookupNode s₀.nodes markerPath = none :=
    lookupNode_none_of_lstat_isOk_false s₀ markerPath hMarker
  have hMarkerGone : ((mockFs.lstat markerPath).run sFin).1.isOk = false := by
    rw [hsFin, hsMk]
    apply mockFs_lstat_isOk_false_of_lookup_none
    dsimp only
    rw [List.filter_cons]
    have hSelf : (!underDir dir dir) = false := by simp [underDir_refl dir hDirNorm]
    rw [hSelf]
    apply lookupNode_filter_none_of_none
    exact lookupNode_filter_none_of_none s₀.nodes _ markerPath hMarkerNone0
  have hDirGone : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  exact ⟨sFin, hCreErr, hMarkerGone, hDirGone⟩

/-- Spec 5: If `fs.chmod dir 0o700` fails right after `fs.mkdir`, `withTempDir` rolls back `dir` without running `action`. -/
theorem proof_tempdir_withTempDir_chmodFailureRollsBack :
    AllPass (test_tempdir_withTempDir_chmodFailureRollsBack
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_chmodFailureRollsBack, AllPass]
  intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarker
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨s₁, hCreErr, hMarkerGone, hDirGone⟩ :=
    spec5_exec s₀ root dirPrefix markerPath hvr hvp stRoot hRootPure hRwx hMarker hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨⟨_, rfl, rfl⟩, hMarkerGone, hDirGone, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 5 (`test_tempdir_withTempDir_chmodFailureRollsBack`). -/
theorem reach_tempdir_withTempDir_chmodFailureRollsBack :
    CanReach (test_tempdir_withTempDir_chmodFailureRollsBack
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withTempDir_chmodFailureRollsBack, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"/other", ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  have hMarker : ((mockFs.lstat "/other").run s₀).1.isOk = false := by
    rw [hs₀]
    apply mockFs_lstat_isOk_false_of_lookup_none
    rw [lookupNode_cons_ne "/tmp" _ [] "/other" (by decide)]
    rfl
  rw [canReach_assume]; refine ⟨hMarker, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s₁, hCreErr, hMarkerGone, hDirGone⟩ :=
    spec5_exec s₀ "/tmp" "tmp-" "/other" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hMarker hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨⟨_, rfl, rfl⟩, hMarkerGone, hDirGone, trivial⟩

private theorem resolveRoot_some_invalid_run (s₀ : TempDirMockState) (root : String)
    (hInv : Internal.validRoot root = false) :
    ∃ te : TempDirError,
      (Internal.resolveRoot mockFs mockEnv (some root)).run s₀ = (.error te, s₀) ∧
      te.kind = .invalidInput ∧ te.message ≠ "" := by
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, stateM_pure_run]
  dsimp only
  simp only [hInv, Bool.not_false, ↓reduceIte, stateM_pure_run]
  exact ⟨_, rfl, rfl, by simp⟩

private theorem spec6_exec (s₀ : TempDirMockState) (root dirPrefix : String)
    (hInv : (¬ Internal.validPrefix dirPrefix) ∨ (¬ Internal.validRoot root)) :
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
      (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") := by
  by_cases hvp : Internal.validPrefix dirPrefix = true
  · have hvr : Internal.validRoot root = false := by
      rcases hInv with hnp | hnr
      · exact absurd hvp hnp
      · cases h : Internal.validRoot root with
        | false => rfl
        | true => exact absurd h hnr
    obtain ⟨te, hRes, hKind, hMsg⟩ := resolveRoot_some_invalid_run s₀ root hvr
    have hCre : (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.error te, s₀) := by
      dsimp only [Internal.createTempDir]
      simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hRes]
      exact stateM_pure_run _ _
    have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) := by
      rw [mkApiM_withTempDir_eq]
      dsimp only [Internal.withTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) := by
      rw [mkApiM_withLockedTempDir_eq]
      dsimp only [Internal.withLockedTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
        (.error te, s₀) := by
      rw [mkApiM_cleanupStaleTempDirs_eq]
      dsimp only [Internal.cleanupStaleTempDirsM]
      simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hRes]
      exact stateM_pure_run _ _
    exact ⟨⟨te, h1, hKind, hMsg⟩, ⟨te, h2, hKind, hMsg⟩, ⟨te, h3, hKind, hMsg⟩⟩
  · have hvpF : Internal.validPrefix dirPrefix = false := Bool.eq_false_iff.mpr hvp
    have hCre : (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      dsimp only [Internal.createTempDir]
      simp only [hvpF, Bool.not_false, ↓reduceIte, stateM_pure_run]
    have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_withTempDir_eq]
      dsimp only [Internal.withTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_withLockedTempDir_eq]
      dsimp only [Internal.withLockedTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_cleanupStaleTempDirs_eq]
      dsimp only [Internal.cleanupStaleTempDirsM]
      simp only [hvpF, Bool.not_false, ↓reduceIte, stateM_pure_run]
    exact ⟨⟨_, h1, rfl, by decide⟩, ⟨_, h2, rfl, by decide⟩, ⟨_, h3, rfl, by decide⟩⟩

/-- Spec 6: All three operations reject invalid `prefix` or `root` with `.invalidInput` and zero state mutations. -/
theorem proof_tempdir_validation_rejectsInvalidInputs :
    AllPass (test_tempdir_validation_rejectsInvalidInputs
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_validation_rejectsInvalidInputs, AllPass]
  intro s₀ root dirPrefix hInv
  have hInv' : (¬ Internal.validPrefix dirPrefix) ∨ (¬ Internal.validRoot root) := hInv
  obtain ⟨⟨e1, h1, hk1, hm1⟩, ⟨e2, h2, hk2, hm2⟩, ⟨e3, h3, hk3, hm3⟩⟩ := spec6_exec s₀ root dirPrefix hInv'
  rw [h1, h2, h3]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨⟨e1, rfl, hk1, hm1⟩, ⟨e2, rfl, hk2, hm2⟩, ⟨e3, rfl, hk3, hm3⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 6 (`test_tempdir_validation_rejectsInvalidInputs`). -/
theorem reach_tempdir_validation_rejectsInvalidInputs :
    CanReach (test_tempdir_validation_rejectsInvalidInputs
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_validation_rejectsInvalidInputs, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"", ?_⟩
  rw [canReach_nondet]; refine ⟨"bad/prefix", ?_⟩
  have hInv : ¬ Internal.validPrefix "bad/prefix" ∨ ¬ Internal.validRoot "" := Or.inr (by decide)
  rw [canReach_assume]; refine ⟨hInv, ?_⟩
  obtain ⟨⟨e1, h1, hk1, hm1⟩, ⟨e2, h2, hk2, hm2⟩, ⟨e3, h3, hk3, hm3⟩⟩ := spec6_exec s₀ "" "bad/prefix" hInv
  rw [h1, h2, h3]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨⟨e1, rfl, hk1, hm1⟩, ⟨e2, rfl, hk2, hm2⟩, ⟨e3, rfl, hk3, hm3⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- Shared proof helper `lookupNode_filter_none_of_underDir`. -/
theorem lookupNode_filter_none_of_underDir (nodes : List (String × MockNode)) (d p : String)
    (hu : underDir d p = true) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) p = none := by
  unfold lookupNode
  dsimp only
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    rw [List.filter_cons]
    cases hKeep : (!underDir d x.1) with
    | false => exact ih
    | true =>
      simp only [↓reduceIte]
      have hne : (normKey x.1 == normKey p) = false := by
        rw [beq_false_of_ne]
        intro heq
        have hu' : underDir d x.1 = true := by rw [underDir_eq_of_normKey_eq d x.1 p heq]; exact hu
        simp [hu'] at hKeep
      rw [List.find?_cons, hne]
      exact ih

private theorem resolveRoot_none_invalid_run (s₀ : TempDirMockState) (tmpdir : String)
    (hTmp : s₀.tmpdir = some tmpdir) (hNe : tmpdir.isEmpty = false)
    (hNul : Char.ofNat 0 ∈ tmpdir.toList) :
    ∃ te : TempDirError,
      (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error te, s₀) ∧
      te.kind = .invalidInput := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok (some tmpdir), s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run, hTmp]
  have hvrF : Internal.validRoot tmpdir = false := by
    simp [Internal.validRoot, hNe, hNul]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  dsimp only
  rw [hNe]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  simp only [hvrF, Bool.not_false, ↓reduceIte, stateM_pure_run]
  exact ⟨_, rfl, rfl⟩

private theorem resolveRoot_none_stat_err_run (s₀ : TempDirMockState) (r : String) (fe : FsError)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .error fe) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error (Internal.mapFsError fe), s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.error fe, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    exact stateM_pure_run _ _
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    exact stateM_pure_run _ _

private theorem resolveRoot_none_nonDir_run (s₀ : TempDirMockState) (r : String) (st : FileStat)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .ok st)
    (hNotDir : (st.kind != .dir) = true) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ =
      (.error { kind := .notADirectory, path := some r, message := "temporary root is not a directory" }, s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.ok st, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    dsimp only
    simp only [hNotDir, ↓reduceIte]
    exact stateM_pure_run _ _
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    dsimp only
    simp only [hNotDir, ↓reduceIte]
    exact stateM_pure_run _ _

private theorem resolveRoot_none_ok_run (s₀ : TempDirMockState) (r : String) (st : FileStat)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .ok st)
    (hDir : st.kind = .dir) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok r, s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.ok st, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    simp only [hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    simp only [hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]

/-- Shared proof helper `mockFs_withFileLock_create_run`. -/
theorem mockFs_withFileLock_create_run {α : Type}
    (s : TempDirMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : StateM TempDirMockState (Except FsError α)) :
    let ino := freshInode s
    let sLock := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := (ino, mode) :: s.locks
      nextInode := ino + 1 }
    (mockFs.withFileLock p mode true act).run s =
      ((act.run sLock).1, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
  intro ino sLock
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  have hSet : (set ({
      nodes := (p, MockNode.file (freshInode s) "" s.nowSec 420) :: s.nodes,
      locks := (freshInode s, mode) :: s.locks,
      nextInode := freshInode s + 1, tmpdir := s.tmpdir, nowSec := s.nowSec, nextUuid := s.nextUuid } : TempDirMockState) :
      StateM TempDirMockState Unit).run s = ((), sLock) := rfl
  rw [hSet]
  dsimp only
  cases hAct : act.run sLock with
  | mk r sA =>
    dsimp only
    have hMod : ((modify fun s' : TempDirMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
        StateM TempDirMockState Unit).run sA =
        ((), { sA with locks := mockRemoveFirstLock ino mode sA.locks }) := rfl
    rw [hMod]

private theorem createTempDir_none_mock_steps (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : Internal.validRoot root = true)
    (hvp : Internal.validPrefix dirPrefix = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok root, s₀))
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir mockFs mockUuid mockEnv none dirPrefix).run s₀ = (.ok dir, sMk) := by
  intro u dir sMk
  have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := by
    simpa [Internal.validRoot] using hvr
  have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := by
    simpa [Internal.validPrefix] using hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr'
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp'
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hSp : splitParentChild dir = some (normKey root, dirPrefix ++ mockUuidToString u) :=
    splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) (dirPrefix ++ mockUuidToString u) = dir :=
    mockJoin_normKey root (dirPrefix ++ mockUuidToString u)
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by
    unfold mockLstatPure at hNone
    cases hl : lookupNode s₀.nodes dir with
    | none => rfl
    | some dn =>
      rw [hl] at hNone
      simp [Except.toBool] at hNone
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  have hMk : (mockFs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.ok (), { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDirNone]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hCh : (mockFs.chmod dir 0o700).run
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } =
      (.ok (), sMk) := by
    dsimp only [mockFs, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm]
    have hLook : lookupNode ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)) dir =
        some (MockNode.dir s₀.nowSec 0o755) :=
      lookupNode_cons_eq _ _ _ _ rfl
    rw [hLook]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
    have hMapId : (s₀.nodes.filter (fun e => !underDir dir e.1)).map
        (fun x => if normKey x.1 == dir then (x.1, match x.2 with
          | MockNode.dir t _ => MockNode.dir t 0o700
          | MockNode.file ino c t _ => MockNode.file ino c t 0o700
          | MockNode.symlink tgt t => MockNode.symlink tgt t) else x) =
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      apply list_map_id_of_mem
      intro x hx
      have hKeep := (List.mem_filter.mp hx).2
      have hne : (normKey x.1 == dir) = false := by
        rw [beq_false_of_ne]
        intro hEq
        simp only [underDir, hDirNorm, hEq, beq_self_eq_true, Bool.true_or, Bool.not_true] at hKeep
        exact Bool.noConfusion hKeep
      simp [hne]
    show (Except.ok (), {
      nodes := List.map (fun x => if (normKey x.1 == dir) = true then _ else x)
        ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)),
      locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec,
      nextUuid := s₀.nextUuid + 1 }) = (Except.ok (), sMk)
    simp only [List.map_cons, hDirNorm, beq_self_eq_true, ↓reduceIte]
    exact congrArg (fun ns => ((Except.ok (), ({
      nodes := (dir, MockNode.dir s₀.nowSec 0o700) :: ns,
      locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec,
      nextUuid := s₀.nextUuid + 1 } : TempDirMockState)) : Except FsError Unit × TempDirMockState)) hMapId
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hRes]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : mockFs.join root (dirPrefix ++ mockUuid.toString u) = dir := rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMk]
  rw [stateM_bind_run, hCh]
  rw [stateM_pure_run]

private theorem spec7_err_all_three (s₀ : TempDirMockState) (dirPrefix : String) (te : TempDirError)
    (hvp : Internal.validPrefix dirPrefix = true)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error te, s₀)) :
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) ∧
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) ∧
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
      (.error te, s₀) := by
  have hCre : (Internal.createTempDir mockFs mockUuid mockEnv none dirPrefix).run s₀ = (.error te, s₀) := by
    dsimp only [Internal.createTempDir]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    exact stateM_pure_run _ _
  have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [stateM_bind_run, hCre]
    exact stateM_pure_run _ _
  have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempDirError Unit))).run s₀ = (.error te, s₀) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCre]
    exact stateM_pure_run _ _
  have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
      (.error te, s₀) := by
    rw [mkApiM_cleanupStaleTempDirs_eq]
    dsimp only [Internal.cleanupStaleTempDirsM]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    exact stateM_pure_run _ _
  exact ⟨h1, h2, h3⟩

private theorem spec7_ok_all_three (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : Internal.validRoot root = true)
    (hvp : Internal.validPrefix dirPrefix = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok root, s₀))
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    ∃ s1 s2 s3 rep3,
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun d => pure (.ok d))).run s₀ =
        (.ok dir, s1) ∧
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun d => pure (.ok d))).run s₀ =
        (.ok dir, s2) ∧
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
        (.ok rep3, s3) := by
  intro dir
  have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := by
    simpa [Internal.validRoot] using hvr
  have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := by
    simpa [Internal.validPrefix] using hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr'
  let u := mockUuidOfNat s₀.nextUuid
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp'
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hCreate := createTempDir_none_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hRes hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFin1, hsFin1⟩ : ∃ s : TempDirMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sMk = (.ok (), sFin1) := by
    rw [hsFin1]; exact cleanupDir_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩
  have h1 : (((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun d => pure (.ok d))).run s₀) =
      (.ok dir, sFin1) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
    dsimp only
    rw [hClean1]
    dsimp only
    rw [stateM_pure_run]
  let lockPath := mockJoin dir ".lock"
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s =
      { nodes := (lockPath, MockNode.file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks)
        nextInode := freshInode sMk + 1
        tmpdir := sMk.tmpdir
        nowSec := sMk.nowSec
        nextUuid := sMk.nextUuid } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sFin2, hsFin2⟩ : ∃ s : TempDirMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean2 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterLock = (.ok (), sFin2) := by
    rw [hsFin2]; exact cleanupDir_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  have h2 : (((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun d => pure (.ok d))).run s₀) =
      (.ok dir, sFin2) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run]
    rw [mockFs_join_eq]
    rw [mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterLock, hClean2]
    dsimp only
    rw [stateM_pure_run]
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hRx : hasRx stRoot = true := by
    simp [hasRx, hRwx.1, hRwx.2.1, hRwx.2.2.2]; decide
  have hList : (mockFs.listDir root).run s₀ =
      (.ok (Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1)))).toArray, s₀) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hRx, Bool.not_true]
    exact stateM_pure_run _ _
  have h3 : ∃ rep3 s3,
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
        (.ok rep3, s3) := by
    rw [mkApiM_cleanupStaleTempDirs_eq]
    dsimp only [Internal.cleanupStaleTempDirsM]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    dsimp only
    have hTimeStep : mockTime.nowTimestamp.run s₀ =
        (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt s₀.nowSec), s₀) := by
      simp [mockTime]; rfl
    rw [stateM_bind_run, hTimeStep]
    dsimp only
    rw [stateM_bind_run, hList]
    dsimp only
    cases hSw : (Internal.sweepEntries mockFs root dirPrefix 86400
        (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt s₀.nowSec)).toSecondsSinceUnixEpoch.val
        {} (Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1)))).toArray.toList).run s₀ with
    | mk repSw sSw =>
      let rep3 : CleanupReport :=
        { removed := (Internal.sortStrings repSw.removed.toList).toArray
          keptLocked := (Internal.sortStrings repSw.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repSw.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repSw.skipped.toList).toArray
          failed := repSw.failed }
      refine ⟨rep3, sSw, ?_⟩
      rw [stateM_bind_run, hSw]
      dsimp only
      exact stateM_pure_run _ _
  rcases h3 with ⟨rep3, s3, h3⟩
  exact ⟨sFin1, sFin2, s3, rep3, h1, h2, h3⟩

/-- Spec 7: With `root? = none`, all three operations resolve non-empty `TMPDIR`, reject NUL `TMPDIR` with `.invalidInput`, reject missing/non-dir `TMPDIR` strictly, and fall back to `"/tmp"` when `TMPDIR` is unset or empty. -/
theorem proof_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing :
    AllPass (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing, AllPass]
  intro s₀ dirPrefix hvp
  have hvp' : Internal.validPrefix dirPrefix = true := hvp
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  rw [hEnvStep]
  dsimp only
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  cases hTmp : s₀.tmpdir with
  | none =>
    dsimp only
    rw [allPass_assume]
    rintro ⟨stTmp, hStatTmp, hRwxTmp⟩
    have hStatTmpPure : mockStatPure s₀ "/tmp" = .ok stTmp := by
      rw [mockFs_stat_run] at hStatTmp; exact hStatTmp
    rw [allPass_assume]
    intro hNone
    have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
        (mockJoin "/tmp" (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
      rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
      exact hNone
    have hRes := resolveRoot_none_ok_run s₀ "/tmp" stTmp (by rw [hTmp]) rfl hStatTmpPure hRwxTmp.1
    obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
      spec7_ok_all_three s₀ "/tmp" dirPrefix rfl hvp' stTmp hStatTmpPure hRwxTmp hRes hNonePure
    rw [h1, h2, h3]
    dsimp only
    rw [allPass_assert, allPass_assert, allPass_assert_end]
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact ⟨rfl, rfl, rfl, trivial⟩
  | some tmpdir =>
    dsimp only
    by_cases hEmpty : tmpdir.isEmpty = true
    · simp only [hEmpty, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [allPass_assume]
      rintro ⟨stTmp, hStatTmp, hRwxTmp⟩
      have hStatTmpPure : mockStatPure s₀ "/tmp" = .ok stTmp := by
        rw [mockFs_stat_run] at hStatTmp; exact hStatTmp
      rw [allPass_assume]
      intro hNone
      have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
          (mockJoin "/tmp" (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
        rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
        exact hNone
      have hRes := resolveRoot_none_ok_run s₀ "/tmp" stTmp (by simp [hTmp, hEmpty]) rfl hStatTmpPure hRwxTmp.1
      obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
        spec7_ok_all_three s₀ "/tmp" dirPrefix rfl hvp' stTmp hStatTmpPure hRwxTmp hRes hNonePure
      rw [h1, h2, h3]
      dsimp only
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      rw [mockFs_join_eq, mockUuid_toString_eq]
      exact ⟨rfl, rfl, rfl, trivial⟩
    · have hNe : tmpdir.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
      simp only [hNe, Bool.not_false, ↓reduceIte]
      by_cases hNul : Char.ofNat 0 ∈ tmpdir.toList
      · simp only [hNul, ↓reduceIte]
        obtain ⟨te, hRes, hKind⟩ := resolveRoot_none_invalid_run s₀ tmpdir hTmp hNe hNul
        obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix te hvp' hRes
        rw [h1, h2, h3]
        dsimp only
        rw [allPass_assert, allPass_assert, allPass_assert_end]
        exact ⟨⟨⟨te, rfl, hKind⟩, rfl⟩, ⟨⟨te, rfl, hKind⟩, rfl⟩, ⟨⟨te, rfl, hKind⟩, rfl⟩, trivial⟩
      · simp only [hNul, ↓reduceIte]
        have hvr : Internal.validRoot tmpdir = true := by
          simp [Internal.validRoot, hNe, hNul]
        have hStatSame : ((mockFs.stat tmpdir).run { s₀ with tmpdir := some tmpdir, nextUuid := s₀.nextUuid + 1 }).1 =
            ((mockFs.stat tmpdir).run s₀).1 := by
          rw [mockFs_stat_run, mockFs_stat_run]; rfl
        rw [hStatSame]
        cases hStat : (mockFs.stat tmpdir).run s₀ |>.1 with
        | error fe =>
          dsimp only
          have hStatPure : mockStatPure s₀ tmpdir = .error fe := by
            rw [mockFs_stat_run] at hStat; exact hStat
          have hRes := resolveRoot_none_stat_err_run s₀ tmpdir fe (by simp [hTmp, hNe]) hvr hStatPure
          obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix (Internal.mapFsError fe) hvp' hRes
          rw [h1, h2, h3]
          dsimp only
          rw [allPass_assert, allPass_assert, allPass_assert_end]
          have hKind : fe.kind ≠ .notFound ∨ (Internal.mapFsError fe).kind = .notFound := by
            by_cases hnf : fe.kind = .notFound
            · right; simp [Internal.mapFsError, hnf]
            · left; exact hnf
          exact ⟨⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, trivial⟩
        | ok st =>
          dsimp only
          have hStatPure : mockStatPure s₀ tmpdir = .ok st := by
            rw [mockFs_stat_run] at hStat; exact hStat
          have notDirBranch (hNotDir : (st.kind != .dir) = true) :
              AllPass (do
                let (r1, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun _ => pure (.ok ())) |>.run s₀
                let (r2, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun _ => pure (.ok ())) |>.run s₀
                let (r3, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400 |>.run s₀
                NondetTest.assert (∃ te, r1 = .error te ∧ te.kind = .notADirectory)
                NondetTest.assert (∃ te, r2 = .error te ∧ te.kind = .notADirectory)
                NondetTest.assert (∃ te, r3 = .error te ∧ te.kind = .notADirectory)) := by
            have hRes := resolveRoot_none_nonDir_run s₀ tmpdir st (by simp [hTmp, hNe]) hvr hStatPure hNotDir
            obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix
              { kind := .notADirectory, path := some tmpdir, message := "temporary root is not a directory" } hvp' hRes
            dsimp only [AllPass]
            rw [h1, h2, h3]
            dsimp only
            rw [allPass_assert, allPass_assert, allPass_assert_end]
            exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, trivial⟩
          cases hk : st.kind with
          | dir =>
            simp only [show (EntryKind.dir != EntryKind.dir) = false from rfl,
              Bool.false_eq_true, ↓reduceIte]
            rw [allPass_assume]
            intro hRwx
            rw [allPass_assume]
            intro hNone
            have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
                (mockJoin tmpdir (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
              rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
              exact hNone
            have hRes := resolveRoot_none_ok_run s₀ tmpdir st (by simp [hTmp, hNe]) hvr hStatPure hk
            obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
              spec7_ok_all_three s₀ tmpdir dirPrefix hvr hvp' st hStatPure hRwx hRes hNonePure
            rw [h1, h2, h3]
            dsimp only
            rw [allPass_assert, allPass_assert, allPass_assert_end]
            rw [mockFs_join_eq, mockUuid_toString_eq]
            exact ⟨rfl, rfl, rfl, trivial⟩
          | file =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.file != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir
          | symlink =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.symlink != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir
          | other =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.other != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir

/-- Non-vacuity `CanReach` witness for Spec 7 (`test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing`). -/
theorem reach_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing :
    CanReach (test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_rootResolution_tmpdirAndFallbackAndStrictMissing, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = { tmpdir := some "/custom", nodes := [("/custom", .dir 0 0o755)] } :=
    ⟨_, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_assume]; refine ⟨rfl, ?_⟩
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok (some "/custom"), s₀) := by
    rw [hs₀]; rfl
  rw [hEnvStep]
  dsimp only
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hTmp : s₀.tmpdir = some "/custom" := by rw [hs₀]
  have hStatPure : mockStatPure s₀ "/custom" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hStatEq : ((mockFs.stat "/custom").run { s₀ with nextUuid := s₀.nextUuid + 1 }).1 =
      .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [mockFs_stat_run]; exact hStatPure
  rw [hStatEq]
  dsimp only
  simp only [show (!"/custom".isEmpty) = true from rfl, ↓reduceIte,
    show (Char.ofNat 0 ∈ ("/custom" : String).toList) = false from by decide, Bool.false_eq_true,
    show ((mockNodeStat (.dir 0 0o755)).kind != .dir) = false from rfl]
  rw [canReach_assume]; refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/custom" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/custom" ≠ normKey (mockJoin "/custom" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/custom" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/custom" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/custom" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hRes := resolveRoot_none_ok_run s₀ "/custom" (mockNodeStat (.dir 0 0o755)) (by rw [hTmp]; rfl) rfl hStatPure rfl
  obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ := spec7_ok_all_three s₀ "/custom" "tmp-" rfl rfl
    (mockNodeStat (.dir 0 0o755)) hStatPure ⟨rfl, rfl, rfl, rfl⟩ hRes hNonePure
  rw [h1, h2, h3]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨rfl, rfl, rfl, trivial⟩

end LeanSwe.TempDir.Proofs

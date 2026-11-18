import LeanSwe.TempDir.Proofs.Shared
import LeanSwe.TempDir.Proofs.WithTempDirProofs

set_option Elab.async false

namespace LeanSwe.TempDir.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)

private theorem foldl_max_ge_init (xs : List (Nat × LockMode)) (init : Nat) :
    init ≤ xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl init
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init (y.1 + 1)) (ih _)

private theorem foldl_max_gt_mem (xs : List (Nat × LockMode)) (init : Nat)
    (x : Nat × LockMode) (hx : x ∈ xs) :
    x.1 < xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl hxy =>
      subst hxy
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) (Nat.le_max_right init (x.1 + 1)))
        (foldl_max_ge_init ys _)
    | inr hmem =>
      exact ih (Nat.max init (y.1 + 1)) hmem

private theorem freshInode_gt_mem (s : TempDirMockState) (x : Nat × LockMode) (hx : x ∈ s.locks) :
    x.1 < freshInode s :=
  foldl_max_gt_mem s.locks s.nextInode x hx

private theorem mockHasConflict_fresh (locks : List (Nat × LockMode)) (ino : Nat) (mode : LockMode)
    (hFresh : ∀ x ∈ locks, x.1 < ino) :
    mockHasConflict locks ino mode = false := by
  unfold mockHasConflict
  rw [List.any_eq_false]
  intro x hx hTrue
  have hlt := hFresh x hx
  have hAnd : (x.1 == ino) = true := ((Bool.and_eq_true _ _).mp hTrue).1
  have heq : x.1 = ino := beq_iff_eq.mp hAnd
  omega

private theorem mockHasConflict_cons_shared_shared (locks : List (Nat × LockMode)) (ino : Nat)
    (hFresh : ∀ x ∈ locks, x.1 < ino) :
    mockHasConflict ((ino, .shared) :: locks) ino .shared = false := by
  unfold mockHasConflict
  simp only [List.any_cons, beq_self_eq_true, show (LockMode.shared == LockMode.exclusive) = false from rfl,
    Bool.and_false, Bool.false_or]
  exact mockHasConflict_fresh locks ino .shared hFresh

private theorem mockHasConflict_cons_shared_exclusive (locks : List (Nat × LockMode)) (ino : Nat) :
    mockHasConflict ((ino, .shared) :: locks) ino .exclusive = true := by
  unfold mockHasConflict
  simp only [List.any_cons, beq_self_eq_true, show (LockMode.exclusive == LockMode.exclusive) = true from rfl,
    Bool.true_or, Bool.and_self, Bool.true_or]

/-- Shared proof helper `mockRemoveFirstLock_head`. -/
theorem mockRemoveFirstLock_head (ino : Nat) (m : LockMode) (locks : List (Nat × LockMode)) :
    mockRemoveFirstLock ino m ((ino, m) :: locks) = locks := by
  unfold mockRemoveFirstLock
  have hm : (m == m) = true := by cases m <;> rfl
  have heq : ((ino, m) == (ino, m)) = true := by
    change (ino == ino && m == m) = true
    rw [beq_self_eq_true, hm]
    rfl
  rw [heq]
  rfl

/-- Shared proof helper `mockFs_tryWithFileLock_existing_ok_run`. -/
theorem mockFs_tryWithFileLock_existing_ok_run {α : Type}
    (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (mode0 : Nat)
    (hp : normKey p = p)
    (hNode : lookupNode s.nodes p = some (.file ino c t mode0))
    (hNoConflict : mockHasConflict s.locks ino mode = false)
    (act : StateM TempDirMockState (Except FsError α)) :
    let sLock := { s with locks := (ino, mode) :: s.locks }
    (mockFs.tryWithFileLock p mode createIfMissing act).run s =
      ((act.run sLock).1.map some, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
  intro sLock
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNode]
  dsimp only
  rw [hNoConflict]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  have hSet : (set ({ s with locks := (ino, mode) :: s.locks } : TempDirMockState) : StateM TempDirMockState Unit).run s =
      ((), sLock) := rfl
  rw [hSet]
  dsimp only
  cases hAct : act.run sLock with
  | mk r sA =>
    dsimp only
    have hMod : ((modify fun s' : TempDirMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
        StateM TempDirMockState Unit).run sA =
        ((), { sA with locks := mockRemoveFirstLock ino mode sA.locks }) := rfl
    rw [hMod]

/-- Shared proof helper `mockFs_tryWithFileLock_existing_conflict_run`. -/
theorem mockFs_tryWithFileLock_existing_conflict_run {α : Type}
    (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (mode0 : Nat)
    (hp : normKey p = p)
    (hNode : lookupNode s.nodes p = some (.file ino c t mode0))
    (hConflict : mockHasConflict s.locks ino mode = true)
    (act : StateM TempDirMockState (Except FsError α)) :
    (mockFs.tryWithFileLock p mode createIfMissing act).run s = (.ok none, s) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNode]
  dsimp only
  rw [hConflict]
  simp only [↓reduceIte, stateM_pure_run]

private theorem mockFs_tryWithFileLock_create_run {α : Type}
    (s : TempDirMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : StateM TempDirMockState (Except FsError α)) :
    let ino := freshInode s
    let sLock := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := (ino, mode) :: s.locks
      nextInode := ino + 1 }
    (mockFs.tryWithFileLock p mode true act).run s =
      ((act.run sLock).1.map some, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
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

/-- Shared proof helper `underDir_mockJoin_root_false`. -/
theorem underDir_mockJoin_root_false (root child : String)
    (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList) :
    underDir (mockJoin root child) root = false := by
  have hNormDir : normKey (mockJoin root child) = mockJoin root child :=
    normKey_mockJoin root child hcNe hcNoSlash
  have hDirNeSlash : mockJoin root child ≠ "/" := mockJoin_ne_slash root child hrNe hcNe
  have hJoin := mockJoin_eq_append_of_ne_empty root child hrNe
  have hcPos : 0 < child.length := string_length_pos_of_ne_empty child hcNe
  have hLenLt : (normKey root).length < (mockJoin root child).length := by
    rw [← @String.length_toList (normKey root), ← @String.length_toList (mockJoin root child), hJoin]
    split
    · next hEq =>
      have hRootEq : normKey root = "/" := beq_iff_eq.mp hEq
      rw [hRootEq]
      have hSlashLen : ("/" : String).length = 1 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, String.length_toList, hSlashLen]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil, String.length_toList]
      omega
  unfold underDir
  have hNeSlashB : (mockJoin root child == "/") = false := beq_false_of_ne hDirNeSlash
  have hNe : (normKey root == mockJoin root child) = false := by
    rw [beq_false_of_ne]
    intro hEq
    have hL := congrArg String.length hEq
    omega
  have hNotPref : (mockJoin root child ++ "/").toList.isPrefixOf (normKey root).toList = false := by
    cases hp : (mockJoin root child ++ "/").toList.isPrefixOf (normKey root).toList with
    | false => rfl
    | true =>
      exfalso
      have hLe := (List.isPrefixOf_iff_prefix.mp hp).length_le
      simp only [String.length_toList, String.length_append] at hLe
      have hOne : ("/" : String).length = 1 := rfl
      omega
  simp only [hNormDir, hNeSlashB, Bool.false_eq_true, ↓reduceIte, hNe, hNotPref, Bool.or_self]

private theorem lookupNode_filter_not_underDir_eq (nodes : List (String × MockNode)) (d q : String)
    (hFalse : underDir d q = false) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) q = lookupNode nodes q := by
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
    cases hb : (normKey x.1 == normKey q) with
    | true =>
      have hEq : normKey x.1 = normKey q := beq_iff_eq.mp hb
      have hux : underDir d x.1 = false := by simpa [underDir, hEq] using hFalse
      simp [lookupNode, hux, hb]
    | false =>
      simp only [lookupNode, List.find?_cons, hb]
      rw [List.filter_cons]
      split
      · simp only [List.find?_cons, hb]
        exact ih
      · exact ih

/-- Shared proof helper `probe_exclusive_lock_after_cleanup_run`. -/
theorem probe_exclusive_lock_after_cleanup_run
    (s : TempDirMockState) (root child : String)
    (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (rootNode : MockNode) (stRoot : FileStat)
    (hLookRoot : lookupNode s.nodes (normKey root) = some rootNode)
    (hStRoot : mockNodeStat rootNode = stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hLookDir : lookupNode s.nodes (mockJoin root child) = none) :
    ((do
      let _ ← mockFs.mkdir (mockJoin root child) false false
      mockFs.tryWithFileLock (mockJoin (mockJoin root child) ".lock") .exclusive true (pure (.ok ()))).run s).1 = .ok (some ()) := by
  let dir := mockJoin root child
  let lockPath := mockJoin dir ".lock"
  have hDirNorm : normKey dir = dir := normKey_mockJoin root child hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root child hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root child hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root child ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hSp : splitParentChild dir = some (normKey root, child) :=
    splitParentChild_mockJoin root child hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) child = dir :=
    mockJoin_normKey root child
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  obtain ⟨s1, hs1⟩ : ∃ s' : TempDirMockState, s' =
      { s with nodes := (dir, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (mockFs.mkdir dir false false).run s = (.ok (), s1) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRoot]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDir, hs1]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hLookLock1 : lookupNode s1.nodes lockPath = none := by
    rw [hs1]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s.nodes dir lockPath hUnderLock
  rw [stateM_bind_run, hMk]
  dsimp only
  rw [mockFs_tryWithFileLock_create_run s1 lockPath .exclusive hLockNorm hLookLock1]
  rw [stateM_pure_run]
  rfl

private theorem createTempDir_mock_steps_of_ops (s₀ : TempDirMockState) (root dirPrefix : String)
    (fs : FsApiM (StateM TempDirMockState))
    (hJoin : fs.join = mockJoin) (hStat : fs.stat = mockFs.stat)
    (hMkdir : fs.mkdir = mockFs.mkdir) (hChmod : fs.chmod = mockFs.chmod)
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
    (Internal.createTempDir fs mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.ok dir, sMk) := by
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
  have hResStep : (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
    dsimp only [Internal.resolveRoot]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStat, mockFs_stat_run, hRoot]
    dsimp only
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hResStep]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : fs.join root (dirPrefix ++ mockUuid.toString u) = dir := by
    rw [hJoin]; rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMkdir, hMk]
  dsimp only
  rw [stateM_bind_run, hChmod, hCh]
  dsimp only
  rw [stateM_pure_run]

private theorem withLockedTempDir_wfl_err_step {S α : Type}
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ sMk sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → StateM S (Except TempDirError α))
    (fe : FsError) (rc : Except TempDirError Unit)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.ok dir, sMk))
    (hWfl : (fs.withFileLock (fs.join dir ".lock") .shared true (do let r ← action dir; return .ok r)).run sMk = (.error fe, sMk))
    (hCln : (Internal.cleanupDirIgnoringNotFound fs dir).run sMk = (rc, sFin)) :
    ((Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action).run s₀ =
      (.error (Internal.mapFsError fe), sFin) := by
  rw [mkApiM_withLockedTempDir_eq]
  dsimp only [Internal.withLockedTempDirM]
  rw [stateM_bind_run, hCre]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, hWfl]
  dsimp only
  rw [hCln]
  dsimp only
  exact stateM_pure_run _ _

private theorem cleanupDir_mock_of_rmtree (s : TempDirMockState) (dir : String)
    (fs : FsApiM (StateM TempDirMockState)) (hRm : fs.rmtree = mockFs.rmtree)
    (hnorm : normKey dir = dir) (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (Internal.cleanupDirIgnoringNotFound fs dir).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [hRm]
  rcases hnode with ⟨m, mode, hLook⟩
  have h1 : (mockFs.rmtree dir true).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hnorm, hLook]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  rw [stateM_bind_run, h1]
  exact stateM_pure_run _ _

private theorem cleanupDir_mock_of_rmtree_err (s : TempDirMockState) (dir : String)
    (fs : FsApiM (StateM TempDirMockState)) (err : FsError)
    (hRm : (fs.rmtree dir true).run s = (.error err, s)) (hb : (err.kind == .notFound) = false) :
    (Internal.cleanupDirIgnoringNotFound fs dir).run s =
      (.error (Internal.mapFsError err), s) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [stateM_bind_run, hRm]
  dsimp only
  rw [hb]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact stateM_pure_run _ _

private def spec8MkState (s₀ : TempDirMockState) (root dirPrefix : String) : TempDirMockState :=
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  { s₀ with
    nextUuid := s₀.nextUuid + 1
    nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }

private def spec8LockState (s₀ : TempDirMockState) (root dirPrefix : String) : TempDirMockState :=
  let sMk := spec8MkState s₀ root dirPrefix
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let lockPath := mockJoin dir ".lock"
  { sMk with
    nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
    locks := (freshInode sMk, .shared) :: sMk.locks
    nextInode := freshInode sMk + 1 }

private theorem spec8_lockState_probes (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let sMk := spec8MkState s₀ root dirPrefix
    let sLock := spec8LockState s₀ root dirPrefix
    ((mockFs.lstat dir).run sLock = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sLock)) ∧
    ((mockFs.lstat lockPath).run sLock = (.ok (mockNodeStat (.file (freshInode sMk) "" sMk.nowSec 0o644)), sLock)) ∧
    ((mockFs.tryWithFileLock lockPath .shared false (pure (.ok ()))).run sLock = (.ok (some ()), sLock)) ∧
    ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sLock = (.ok none, sLock)) := by
  intro u dir lockPath sMk sLock
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) :=
    lookupNode_cons_eq _ _ _ _ rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    change lookupNode ((lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes) dir = _
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hLookLockLock : lookupNode sLock.nodes lockPath = some (.file (freshInode sMk) "" sMk.nowSec 0o644) :=
    lookupNode_cons_eq _ _ _ _ rfl
  have hFreshMk : ∀ x ∈ sMk.locks, x.1 < freshInode sMk := fun x hx => freshInode_gt_mem sMk x hx
  have hNoConfShared : mockHasConflict sLock.locks (freshInode sMk) .shared = false :=
    mockHasConflict_cons_shared_shared sMk.locks (freshInode sMk) hFreshMk
  have hConfEx : mockHasConflict sLock.locks (freshInode sMk) .exclusive = true :=
    mockHasConflict_cons_shared_exclusive sMk.locks (freshInode sMk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookDirLock]
  · rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockLock]
  · rw [mockFs_tryWithFileLock_existing_ok_run sLock lockPath .shared false
      (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hNoConfShared (pure (.ok ()))]
    simp only [stateM_pure_run, mockRemoveFirstLock_head]
    rfl
  · exact mockFs_tryWithFileLock_existing_conflict_run sLock lockPath .exclusive false
      (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hConfEx (pure (.ok ()))

private theorem lookupNode_after_cleanup_root
    (nodes : List (String × MockNode)) (dir lockPath root : String)
    (ndL ndD : MockNode)
    (hNotUnder : underDir dir (normKey root) = false)
    (hb1 : (normKey lockPath == normKey (normKey root)) = false)
    (hb2 : (normKey dir == normKey (normKey root)) = false) :
    lookupNode ((lockPath, ndL) :: (dir, ndD) :: nodes.filter (fun e => !underDir dir e.1)) (normKey root) =
      lookupNode nodes (normKey root) := by
  unfold lookupNode
  dsimp only
  rw [List.find?_cons, hb1]
  dsimp only
  rw [List.find?_cons, hb2]
  exact lookupNode_filter_not_underDir_eq nodes dir (normKey root) hNotUnder

private theorem spec8_ok_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (act : String → StateM TempDirMockState (Except TempDirError Nat))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hAct : (act (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).run
      (spec8LockState s₀ root dirPrefix) = (.ok val, spec8LockState s₀ root dirPrefix)) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    ∃ sOk : TempDirMockState,
      (api.withLockedTempDir (some root) dirPrefix act).run s₀ = (.ok val, sOk) ∧
      ((mockFs.lstat dir).run sOk).1.isOk = false ∧
      (∃ e, ((mockFs.lstat lockPath).run sOk).1 = .error e ∧ e.kind = .notFound) ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sOk).1 =
        .ok (some ()) := by
  intro u dir lockPath api
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  let sMk := spec8MkState s₀ root dirPrefix
  let sLock := spec8LockState s₀ root dirPrefix
  have hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := rfl
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hsLock : sLock =
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } := rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hActOk :
      (do let r ← act dir; return .ok r : StateM TempDirMockState (Except FsError (Except TempDirError Nat))).run sLock =
        (.ok (.ok val), sLock) := by
    rw [stateM_bind_run, hAct]
    exact stateM_pure_run _ _
  obtain ⟨sAfterOk, hsAfterOk⟩ : ∃ s : TempDirMockState, s =
      { sLock with locks := mockRemoveFirstLock (freshInode sMk) .shared sLock.locks } := ⟨_, rfl⟩
  have hLookDirAfterOk : lookupNode sAfterOk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterOk]; exact hLookDirLock
  obtain ⟨sOk, hsOk⟩ : ∃ s : TempDirMockState, s =
      { sAfterOk with nodes := sAfterOk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCleanOk : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterOk = (.ok (), sOk) := by
    rw [hsOk]; exact cleanupDir_mock_run sAfterOk dir hDirNorm ⟨_, _, hLookDirAfterOk⟩
  have hRunOk : (api.withLockedTempDir (some root) dirPrefix act).run s₀ = (.ok val, sOk) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, mockFs_join_eq]
    rw [mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [← hsLock, hActOk]
    dsimp only
    rw [← hsAfterOk, hCleanOk]
    exact stateM_pure_run _ _
  have hLookDirOk : lookupNode sOk.nodes dir = none := by
    rw [hsOk]; exact lookupNode_filter_none_of_underDir sAfterOk.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookLockOk : lookupNode sOk.nodes lockPath = none := by
    rw [hsOk]; exact lookupNode_filter_none_of_underDir sAfterOk.nodes dir lockPath hUnderLock
  have hLookRootOk : lookupNode sOk.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hsOk, lookupNode_filter_not_underDir_eq sAfterOk.nodes dir (normKey root) hRootUnderDirFalse]
    change lookupNode (sAfterOk.nodes) (normKey root) = some rootNode
    have hSA : sAfterOk.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterOk, hsLock, hsMk]
    rw [hSA]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeOk := probe_exclusive_lock_after_cleanup_run sOk root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRootOk hStRoot hRwx hLookDirOk
  refine ⟨sOk, hRunOk, mockFs_lstat_isOk_false_of_lookup_none sOk dir hLookDirOk, ?_, ?_⟩
  · refine ⟨{ kind := .notFound, path := some lockPath, message := "not found" }, ?_, rfl⟩
    rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockOk]
  · dsimp only [dir, lockPath]
    exact hProbeOk

private theorem spec8_err_exec (s₀ : TempDirMockState) (root dirPrefix : String) (err : TempDirError)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    ∃ sErr : TempDirMockState,
      (api.withLockedTempDir (some root) dirPrefix fun _ =>
        pure (Except.error err : Except TempDirError Nat)).run s₀ = (.error err, sErr) ∧
      ((mockFs.lstat dir).run sErr).1.isOk = false ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sErr).1 =
        .ok (some ()) := by
  intro u dir lockPath api
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  let sMk := spec8MkState s₀ root dirPrefix
  let sLock := spec8LockState s₀ root dirPrefix
  have hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := rfl
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hsLock : sLock =
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } := rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sAfterErr, hsAfterErr⟩ : ∃ s : TempDirMockState, s =
      { sLock with locks := mockRemoveFirstLock (freshInode sMk) .shared sLock.locks } := ⟨_, rfl⟩
  have hLookDirAfterErr : lookupNode sAfterErr.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterErr]; exact hLookDirLock
  obtain ⟨sErr, hsErr⟩ : ∃ s : TempDirMockState, s =
      { sAfterErr with nodes := sAfterErr.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCleanErr : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterErr = (.ok (), sErr) := by
    rw [hsErr]; exact cleanupDir_mock_run sAfterErr dir hDirNorm ⟨_, _, hLookDirAfterErr⟩
  have hRunErr : (api.withLockedTempDir (some root) dirPrefix fun _ =>
      pure (Except.error err : Except TempDirError Nat)).run s₀ = (.error err, sErr) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, mockFs_join_eq]
    have hLockEq : mockJoin dir ".lock" = lockPath := rfl
    rw [hLockEq, mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [← hsLock, stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterErr, hCleanErr]
    exact stateM_pure_run _ _
  have hLookDirErr : lookupNode sErr.nodes dir = none := by
    rw [hsErr]; exact lookupNode_filter_none_of_underDir sAfterErr.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookRootErr : lookupNode sErr.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hsErr, lookupNode_filter_not_underDir_eq sAfterErr.nodes dir (normKey root) hRootUnderDirFalse]
    have hSA : sAfterErr.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterErr, hsLock, hsMk]
    rw [hSA]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeErr := probe_exclusive_lock_after_cleanup_run sErr root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRootErr hStRoot hRwx hLookDirErr
  refine ⟨sErr, hRunErr, mockFs_lstat_isOk_false_of_lookup_none sErr dir hLookDirErr, ?_⟩
  dsimp only [dir, lockPath]
  exact hProbeErr

private theorem spec8_lockRm_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (fs1 : FsApiM (StateM TempDirMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin1 : fs1.join = mockJoin) (hStat1 : fs1.stat = mockFs.stat)
    (hMkdir1 : fs1.mkdir = mockFs.mkdir) (hChmod1 : fs1.chmod = mockFs.chmod)
    (hWfl1 : ∀ {β : Type} p m c (body : StateM TempDirMockState (Except FsError β)),
      fs1.withFileLock p m c body = pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }))
    (hRm1 : ∀ p ign, fs1.rmtree p ign = pure (.error { kind := .ioError, path := some p, message := "rm failed" })) :
    ∃ sLockRm : TempDirMockState, ∃ resLockRm : Except TempDirError Nat,
      ((Internal.mkApiM fs1 mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (resLockRm, sLockRm) ∧
      (∃ e, resLockRm = .error e ∧ e.kind = .permissionDenied) := by
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  let lockPath := mockJoin dir ".lock"
  have hCreateLockRm := createTempDir_mock_steps_of_ops s₀ root dirPrefix fs1 hJoin1 hStat1 hMkdir1 hChmod1 hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreateLockRm
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreateLockRm
  have hWflLockRm :
      (fs1.withFileLock (fs1.join dir ".lock") .shared true
        (do let r ← (fun _ => (pure (.ok val) : StateM TempDirMockState (Except TempDirError Nat))) dir; return .ok r)).run sMk =
        (.error { kind := .permissionDenied, path := some lockPath, message := "lock denied" }, sMk) := by
    rw [hJoin1, hWfl1]; exact stateM_pure_run _ _
  have hCleanLockRm :
      (Internal.cleanupDirIgnoringNotFound fs1 dir).run sMk =
        (.error (Internal.mapFsError { kind := .ioError, path := some dir, message := "rm failed" }), sMk) :=
    cleanupDir_mock_of_rmtree_err sMk dir fs1 { kind := .ioError, path := some dir, message := "rm failed" }
      (by rw [hRm1]; exact stateM_pure_run _ _) rfl
  have hRunLockRm := withLockedTempDir_wfl_err_step fs1 mockTime mockUuid mockEnv s₀ sMk sMk (some root) dirPrefix dir
    (fun _ => pure (.ok val)) { kind := .permissionDenied, path := some lockPath, message := "lock denied" } _
    hCreateLockRm hWflLockRm hCleanLockRm
  exact ⟨sMk, _, hRunLockRm, _, rfl, rfl⟩

private theorem spec8_lockClean_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (fs2 : FsApiM (StateM TempDirMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin2 : fs2.join = mockJoin) (hStat2 : fs2.stat = mockFs.stat)
    (hMkdir2 : fs2.mkdir = mockFs.mkdir) (hChmod2 : fs2.chmod = mockFs.chmod)
    (hWfl2 : ∀ {β : Type} p m c (body : StateM TempDirMockState (Except FsError β)),
      fs2.withFileLock p m c body = pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }))
    (hRm2 : fs2.rmtree = mockFs.rmtree) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sLockClean : TempDirMockState, ∃ resLockClean : Except TempDirError Nat,
      ((Internal.mkApiM fs2 mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (resLockClean, sLockClean) ∧
      (∃ e, resLockClean = .error e ∧ e.kind = .permissionDenied) ∧
      ((mockFs.lstat dir).run sLockClean).1.isOk = false := by
  intro u dir
  let lockPath := mockJoin dir ".lock"
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreateLockClean := createTempDir_mock_steps_of_ops s₀ root dirPrefix fs2 hJoin2 hStat2 hMkdir2 hChmod2 hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreateLockClean
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreateLockClean
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFinClean, hsFinClean⟩ : ∃ s : TempDirMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hWflLockClean :
      (fs2.withFileLock (fs2.join dir ".lock") .shared true
        (do let r ← (fun _ => (pure (.ok val) : StateM TempDirMockState (Except TempDirError Nat))) dir; return .ok r)).run sMk =
        (.error { kind := .permissionDenied, path := some lockPath, message := "lock denied" }, sMk) := by
    rw [hJoin2, hWfl2]; exact stateM_pure_run _ _
  have hCleanLockClean : (Internal.cleanupDirIgnoringNotFound fs2 dir).run sMk = (.ok (), sFinClean) := by
    rw [hsFinClean]
    exact cleanupDir_mock_of_rmtree sMk dir fs2 hRm2 hDirNorm ⟨_, _, hLookDirMk⟩
  have hRunLockClean := withLockedTempDir_wfl_err_step fs2 mockTime mockUuid mockEnv s₀ sMk sFinClean (some root) dirPrefix dir
    (fun _ => pure (.ok val)) { kind := .permissionDenied, path := some lockPath, message := "lock denied" } (.ok ())
    hCreateLockClean hWflLockClean hCleanLockClean
  have hLookDirClean : lookupNode sFinClean.nodes dir = none := by
    rw [hsFinClean]; exact lookupNode_filter_none_of_underDir sMk.nodes dir dir (underDir_refl dir hDirNorm)
  exact ⟨sFinClean, _, hRunLockClean, ⟨_, rfl, rfl⟩,
    mockFs_lstat_isOk_false_of_lookup_none sFinClean dir hLookDirClean⟩

/-- Spec 8: `withLockedTempDir` holds a `.shared` lock on `<dir>/.lock` during `action`, releases it and deletes `dir` on `.ok`/`.error`, and cleans up even if locking fails. -/
theorem proof_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    AllPass (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, AllPass]
  intro s₀ root dirPrefix val err ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  rw [mockFs_join_eq, mockUuid_toString_eq]
  have ⟨hLDir, hLLock, hShared, hEx⟩ := spec8_lockState_probes s₀ root dirPrefix hvr hvp
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let act8 : String → StateM TempDirMockState (Except TempDirError Nat) := fun d => do
    let stDir ← mockFs.lstat d
    let lst ← mockFs.lstat (mockJoin d ".lock")
    let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
    let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
    match stDir, lst, sharedProbe, exProbe with
    | .ok info, .ok st, .ok (some ()), .ok none =>
      if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
        return .ok val
      else
        return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
    | .error _, _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
    | _, .error _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "missing lock file" }
    | _, _, _, _ =>
      return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
  have hAct : (act8 dir).run (spec8LockState s₀ root dirPrefix) = (.ok val, spec8LockState s₀ root dirPrefix) := by
    dsimp only [act8, dir]
    rw [stateM_bind_run, hLDir]; dsimp only
    rw [stateM_bind_run, hLLock]; dsimp only
    rw [stateM_bind_run, hShared]; dsimp only
    rw [stateM_bind_run, hEx]; dsimp only
    have hModeDir : ((mockNodeStat (.dir s₀.nowSec 0o700)).kind == EntryKind.dir) = true := rfl
    have hModeVal : ((mockNodeStat (.dir s₀.nowSec 0o700)).mode == 0o700) = true := rfl
    have hKindFile : ((mockNodeStat (.file (freshInode (spec8MkState s₀ root dirPrefix)) "" (spec8MkState s₀ root dirPrefix).nowSec 0o644)).kind == EntryKind.file) = true := rfl
    simp only [hModeDir, hModeVal, beq_self_eq_true, hKindFile, Bool.and_self, ↓reduceIte, stateM_pure_run]
  let fs1 : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
      rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
  let fs2 : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
  obtain ⟨sOk, hRunOk, h1, h2, h3⟩ :=
    spec8_ok_exec s₀ root dirPrefix val act8 hvr hvp stRoot hRootPure hRwx hNonePure hAct
  obtain ⟨sErr, hRunErr, h4, h5⟩ :=
    spec8_err_exec s₀ root dirPrefix err hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨sLockRm, resLockRm, hRunLockRm, h6⟩ :=
    spec8_lockRm_exec s₀ root dirPrefix val fs1 hvr hvp stRoot hRootPure hRwx hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨sLockClean, resLockClean, hRunLockClean, h7, h8⟩ :=
    spec8_lockClean_exec s₀ root dirPrefix val fs2 hvr hvp stRoot hRootPure hRwx hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) rfl
  conv in ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunOk]
  dsimp only [fs1, fs2] at hRunLockRm hRunLockClean
  rw [hRunErr]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunLockRm]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert,
    allPass_assert, allPass_assert, allPass_assert]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunLockClean]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, h1, h2, h3, rfl, h4, h5, h6, h7, h8, trivial⟩

private theorem spec8_reach_tail (s₀ : TempDirMockState)
    (hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)))
    (hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    CanReach (do
      let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
      let act8 : String → StateM TempDirMockState (Except TempDirError Nat) := fun d => do
        let stDir ← mockFs.lstat d
        let lst ← mockFs.lstat (mockJoin d ".lock")
        let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
        let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
        match stDir, lst, sharedProbe, exProbe with
        | .ok info, .ok st, .ok (some ()), .ok none =>
          if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
            return .ok 42
          else
            return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
        | .error _, _, _, _ =>
          return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
        | _, .error _, _, _ =>
          return .error { kind := .notFound, path := some d, message := "missing lock file" }
        | _, _, _, _ =>
          return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
      let (resOk, sOk) := ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" act8).run s₀
      NondetTest.assert (resOk = .ok 42)
      NondetTest.assert (((mockFs.lstat dir).run sOk).1.isOk = false)
      NondetTest.assert (∃ e, ((mockFs.lstat (mockJoin dir ".lock")).run sOk).1 = .error e ∧ e.kind = .notFound)
      let probeOk := (do
        let _ ← mockFs.mkdir dir false false
        mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run sOk
      NondetTest.assert (probeOk.1 = .ok (some ()))
      let (resErr, sErr) := ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-"
        fun _ => pure (Except.error { kind := .ioError, message := "err" } : Except TempDirError Nat)).run s₀
      NondetTest.assert (resErr = .error { kind := .ioError, message := "err" })
      NondetTest.assert (((mockFs.lstat dir).run sErr).1.isOk = false)
      let probeErr := (do
        let _ ← mockFs.mkdir dir false false
        mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run sErr
      NondetTest.assert (probeErr.1 = .ok (some ()))
      let fsLockFailRm : FsApiM (StateM TempDirMockState) :=
        { mockFs with
          withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
          rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
      let (resLockRm, _) := ((Internal.mkApiM fsLockFailRm mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" fun _ => pure (.ok (42 : Nat))).run s₀
      NondetTest.assert (∃ e, resLockRm = .error e ∧ e.kind = .permissionDenied)
      let fsLockFailClean : FsApiM (StateM TempDirMockState) :=
        { mockFs with
          withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
      let (resLockClean, sLockClean) := ((Internal.mkApiM fsLockFailClean mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" fun _ => pure (.ok (42 : Nat))).run s₀
      NondetTest.assert (∃ e, resLockClean = .error e ∧ e.kind = .permissionDenied)
      NondetTest.assert (((mockFs.lstat dir).run sLockClean).1.isOk = false)) := by
  dsimp only [CanReach]
  have ⟨hLDir, hLLock, hShared, hEx⟩ := spec8_lockState_probes s₀ "/tmp" "tmp-" rfl rfl
  let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let act8 : String → StateM TempDirMockState (Except TempDirError Nat) := fun d => do
    let stDir ← mockFs.lstat d
    let lst ← mockFs.lstat (mockJoin d ".lock")
    let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
    let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
    match stDir, lst, sharedProbe, exProbe with
    | .ok info, .ok st, .ok (some ()), .ok none =>
      if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
        return .ok 42
      else
        return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
    | .error _, _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
    | _, .error _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "missing lock file" }
    | _, _, _, _ =>
      return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
  have hAct : (act8 dir).run (spec8LockState s₀ "/tmp" "tmp-") = (.ok 42, spec8LockState s₀ "/tmp" "tmp-") := by
    dsimp only [act8, dir]
    rw [stateM_bind_run, hLDir]; dsimp only
    rw [stateM_bind_run, hLLock]; dsimp only
    rw [stateM_bind_run, hShared]; dsimp only
    rw [stateM_bind_run, hEx]; dsimp only
    have hModeDir : ((mockNodeStat (.dir s₀.nowSec 0o700)).kind == EntryKind.dir) = true := rfl
    have hModeVal : ((mockNodeStat (.dir s₀.nowSec 0o700)).mode == 0o700) = true := rfl
    have hKindFile : ((mockNodeStat (.file (freshInode (spec8MkState s₀ "/tmp" "tmp-")) "" (spec8MkState s₀ "/tmp" "tmp-").nowSec 0o644)).kind == EntryKind.file) = true := rfl
    simp only [hModeDir, hModeVal, beq_self_eq_true, hKindFile, Bool.and_self, ↓reduceIte, stateM_pure_run]
  let fs1 : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
      rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
  let fs2 : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
  obtain ⟨sOk, hRunOk, h1, h2, h3⟩ :=
    spec8_ok_exec s₀ "/tmp" "tmp-" 42 act8
      rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure hAct
  obtain ⟨sErr, hRunErr, h4, h5⟩ :=
    spec8_err_exec s₀ "/tmp" "tmp-" { kind := .ioError, message := "err" }
      rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨sLockRm, resLockRm, hRunLockRm, h6⟩ :=
    spec8_lockRm_exec s₀ "/tmp" "tmp-" 42 fs1 rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨sLockClean, resLockClean, hRunLockClean, h7, h8⟩ :=
    spec8_lockClean_exec s₀ "/tmp" "tmp-" 42 fs2 rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) rfl
  conv in ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunOk]
  dsimp only [fs1, fs2] at hRunLockRm hRunLockClean
  rw [hRunErr]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunLockRm]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert, canReach_assert,
    canReach_assert, canReach_assert, canReach_assert]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunLockClean]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, h1, h2, h3, rfl, h4, h5, h6, h7, h8, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 8 (`test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit`). -/
theorem reach_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    CanReach (test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨42, ?_⟩
  rw [canReach_nondet]; refine ⟨{ kind := .ioError, message := "err" }, ?_⟩
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
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact spec8_reach_tail s₀ hRootPure hNonePure

private theorem spec9_exec (s₀ : TempDirMockState) (root dirPrefix : String) (val : Nat)
    (fsConcurrentSweep : FsApiM (StateM TempDirMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin : fsConcurrentSweep.join = mockJoin)
    (hStat : fsConcurrentSweep.stat = mockFs.stat)
    (hMkdir : fsConcurrentSweep.mkdir = mockFs.mkdir)
    (hChmod : fsConcurrentSweep.chmod = mockFs.chmod)
    (hWfl : ∀ {β : Type}, @fsConcurrentSweep.withFileLock β = @mockFs.withFileLock β)
    (hRm : ∀ p ign, fsConcurrentSweep.rmtree p ign = do
      let _ ← mockFs.rmtree p ign
      pure (.error { kind := .notFound, path := some p, message := "removed concurrently" })) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ s₁ : TempDirMockState,
      ((Internal.mkApiM fsConcurrentSweep mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (.ok val, s₁) ∧
      ((mockFs.lstat dir).run s₁).1.isOk = false := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey (mockJoin dir ".lock") = mockJoin dir ".lock" :=
    normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey (mockJoin dir ".lock") ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir (mockJoin dir ".lock") = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hCreate := createTempDir_mock_steps_of_ops s₀ root dirPrefix fsConcurrentSweep hJoin hStat hMkdir hChmod
    hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes (mockJoin dir ".lock") = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey (mockJoin dir ".lock")) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir (mockJoin dir ".lock") hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s =
      { nodes := (mockJoin dir ".lock", .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks)
        nextInode := freshInode sMk + 1
        tmpdir := sMk.tmpdir
        nowSec := sMk.nowSec
        nextUuid := sMk.nextUuid } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey (mockJoin dir ".lock") == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempDirMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hRmInner : (mockFs.rmtree dir true).run sAfterLock = (.ok (), sFin) := by
    rw [hsFin]
    dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm, hLookDirAfterLock]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hClean : (Internal.cleanupDirIgnoringNotFound fsConcurrentSweep dir).run sAfterLock = (.ok (), sFin) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound]
    rw [hRm, stateM_bind_run, stateM_bind_run, hRmInner]
    dsimp only
    rw [stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl]
    simp only [↓reduceIte]
    exact stateM_pure_run _ _
  have hRun : ((Internal.mkApiM fsConcurrentSweep mockTime mockUuid mockEnv).withLockedTempDir
      (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (.ok val, sFin) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, hJoin, hWfl]
    rw [mockFs_withFileLock_create_run sMk (mockJoin dir ".lock") .shared hLockNorm hLookLockMk]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterLock, hClean]
    dsimp only
    exact stateM_pure_run _ _
  have hLookDirFin : lookupNode sFin.nodes dir = none := by
    rw [hsFin]; exact lookupNode_filter_none_of_underDir sAfterLock.nodes dir dir (underDir_refl dir hDirNorm)
  exact ⟨sFin, hRun, mockFs_lstat_isOk_false_of_lookup_none sFin dir hLookDirFin⟩

/-- Spec 9: `withLockedTempDir` ignores `.notFound` from `fs.rmtree` in its finalizer on concurrent cleanup. -/
theorem proof_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    AllPass (test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  let fsConcurrentSweep : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      rmtree := fun p ign => do
        let _ ← mockFs.rmtree p ign
        pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
  obtain ⟨s₁, hRun, hDead⟩ := spec9_exec s₀ root dirPrefix val fsConcurrentSweep hvr hvp stRoot hRootPure hRwx hNonePure
    rfl rfl rfl rfl rfl (fun _ _ => rfl)
  rw [hRun]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, hDead, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 9 (`test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup`). -/
theorem reach_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    CanReach (test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, CanReach]
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
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  let fsConcurrentSweep : FsApiM (StateM TempDirMockState) :=
    { mockFs with
      rmtree := fun p ign => do
        let _ ← mockFs.rmtree p ign
        pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
  obtain ⟨s₁, hRun, hDead⟩ := spec9_exec s₀ "/tmp" "tmp-" 7 fsConcurrentSweep rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
    rfl rfl rfl rfl rfl (fun _ _ => rfl)
  rw [hRun]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, hDead, trivial⟩

private theorem exceptT_liftM_stateM_run {ε S α : Type} (x : StateM S α) (s : S) :
    (ExceptT.run (liftM x : ExceptT ε (StateM S) α)).run s = (.ok (x.run s).1, (x.run s).2) := by
  dsimp only [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, StateT.run, ExceptT.run]
  cases hx : x.run s with
  | mk a s' => rfl

private theorem exceptT_stateM_pure_run {ε S α : Type} (a : α) (s : S) :
    (ExceptT.run (pure a : ExceptT ε (StateM S) α)).run s = (.ok a, s) := rfl

private theorem exceptT_stateM_throw_run {ε S α : Type} (e : ε) (s : S) :
    (ExceptT.run (throw e : ExceptT ε (StateM S) α)).run s = (.error e, s) := rfl

private theorem createTempDir_ex_mock_steps (s₀ : TempDirMockState) (root dirPrefix : String)
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
    (ExceptT.run (Internal.createTempDir mockFsEx mockUuidEx mockEnvEx (some root) dirPrefix)).run s₀ =
      (.ok (.ok dir), sMk) := by
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
  have hResEx : (ExceptT.run (Internal.resolveRoot mockFsEx mockEnvEx (some root))).run s₀ = (.ok (.ok root), s₀) := by
    dsimp only [Internal.resolveRoot]
    rw [exceptT_stateM_bind_run, exceptT_stateM_pure_run]
    dsimp only
    simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run]
    have hStEx : (ExceptT.run (mockFsEx.stat root)).run s₀ = (.ok (.ok stRoot), s₀) := by
      dsimp only [mockFsEx]
      rw [exceptT_liftM_stateM_run, mockFs_stat_run, hRoot]
    rw [hStEx]
    dsimp only
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, exceptT_stateM_pure_run]
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
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
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run, hResEx]
  have hUuidEx : (ExceptT.run mockUuidEx.getUuid).run s₀ = (.ok (.ok u), { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    dsimp only [mockUuidEx]
    rw [exceptT_liftM_stateM_run, hUuidStep]
  rw [hUuidEx]
  dsimp only
  have hDirEq : mockFsEx.join root (dirPrefix ++ mockUuidEx.toString u) = dir := rfl
  simp only [hDirEq]
  have hMkEx : (ExceptT.run (mockFsEx.mkdir dir false false)).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.ok (.ok ()), { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run, hMk]
  rw [exceptT_stateM_bind_run, hMkEx]
  dsimp only
  have hChEx : (ExceptT.run (mockFsEx.chmod dir 0o700)).run
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } =
      (.ok (.ok ()), sMk) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run, hCh]
  rw [exceptT_stateM_bind_run, hChEx]
  exact exceptT_stateM_pure_run _ _

private theorem cleanupDir_ex_mock_run (s : TempDirMockState) (dir : String) (hnorm : normKey dir = dir)
    (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run s =
      (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [exceptT_stateM_bind_run]
  have hRmEx : (ExceptT.run (mockFsEx.rmtree dir true)).run s =
      (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run]
    rcases hnode with ⟨m, mode, hLook⟩
    have hRm : (mockFs.rmtree dir true).run s =
        (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
      dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
      rw [stateM_bind_run, stateM_get_run]
      dsimp only
      rw [hnorm, hLook]
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
    rw [hRm]
  rw [hRmEx]
  exact exceptT_stateM_pure_run _ _

private theorem mockFsEx_withFileLock_create_throw_run
    (s : TempDirMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : ExceptT String (StateM TempDirMockState) (Except FsError (Except TempDirError Unit))) (errStr : String)
    (hActThrow : (ExceptT.run act).run
      { s with
        nodes := (p, .file (freshInode s) "" s.nowSec 0o644) :: s.nodes
        locks := (freshInode s, mode) :: s.locks
        nextInode := freshInode s + 1 } =
      (.error errStr, { s with
        nodes := (p, .file (freshInode s) "" s.nowSec 0o644) :: s.nodes
        locks := (freshInode s, mode) :: s.locks
        nextInode := freshInode s + 1 })) :
    let ino := freshInode s
    let sAfter := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := mockRemoveFirstLock ino mode ((ino, mode) :: s.locks)
      nextInode := ino + 1 }
    (ExceptT.run (mockFsEx.withFileLock p mode true act)).run s = (.error errStr, sAfter) := by
  intro ino sAfter
  dsimp only [mockFsEx, resolveParentTarget]
  rw [exceptT_stateM_bind_run]
  have hGet : (ExceptT.run (get : ExceptT String (StateM TempDirMockState) TempDirMockState)).run s = (.ok s, s) := rfl
  rw [hGet]
  dsimp only
  rw [hp, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run, exceptT_stateM_pure_run]
  let sLock : TempDirMockState := { s with
    nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
    locks := (ino, mode) :: s.locks
    nextInode := ino + 1 }
  have hSetEx : (ExceptT.run (liftM (set ({
      nodes := (p, MockNode.file (freshInode s) "" s.nowSec 420) :: s.nodes,
      locks := (freshInode s, mode) :: s.locks,
      nextInode := freshInode s + 1, tmpdir := s.tmpdir, nowSec := s.nowSec, nextUuid := s.nextUuid } : TempDirMockState) :
      StateM TempDirMockState Unit) : ExceptT String (StateM TempDirMockState) Unit)).run s = (.ok (), sLock) := by
    rw [exceptT_liftM_stateM_run]; rfl
  rw [hSetEx]
  dsimp only
  let fin : Option (Except FsError (Except TempDirError Unit)) → ExceptT String (StateM TempDirMockState) Unit :=
    fun _ => liftM (modify (fun s' : TempDirMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
      StateM TempDirMockState Unit)
  have hModEx : (ExceptT.run (fin none)).run sLock = (.ok (), sAfter) := by
    dsimp only [fin]; rw [exceptT_liftM_stateM_run]; rfl
  rw [exceptT_tryFinally'_error_run act fin sLock sLock sAfter errStr () hActThrow hModEx]

private theorem spec10_part1_exec (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    ∃ s1 : TempDirMockState,
      (ExceptT.run (apiEx.withTempDir (some root) dirPrefix fun _ =>
        (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ =
        (.error "boom", s1) ∧
      ((mockFs.lstat dir).run s1).1.isOk = false := by
  intro u dir apiEx
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreate := createTempDir_ex_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨s1Fin, hs1Fin⟩ : ∃ s : TempDirMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sMk = (.ok (.ok ()), s1Fin) := by
    rw [hs1Fin]; exact cleanupDir_ex_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩
  have hRun1 : (ExceptT.run (apiEx.withTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ =
      (.error "boom", s1Fin) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [exceptT_stateM_bind_run, hCreate]
    dsimp only
    rw [exceptT_stateM_bind_run]
    rw [exceptT_tryFinally'_error_run (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit))
      (fun _ => Internal.cleanupDirIgnoringNotFound mockFsEx dir) sMk sMk s1Fin "boom" (.ok ())
      (exceptT_stateM_throw_run "boom" sMk) hClean1]
  have hLookDir1 : lookupNode s1Fin.nodes dir = none := by
    rw [hs1Fin]; exact lookupNode_filter_none_of_underDir _ dir dir (underDir_refl dir hDirNorm)
  exact ⟨s1Fin, hRun1, mockFs_lstat_isOk_false_of_lookup_none s1Fin dir hLookDir1⟩

private theorem withLockedTempDir_ex_throw_step {E S α : Type}
    (fs : FsApiM (ExceptT E (StateM S))) (time : TimeOpsM (ExceptT E (StateM S)))
    (uuid : UuidApiM (ExceptT E (StateM S))) (env : EnvVarsApiM (ExceptT E (StateM S)))
    (s₀ sMk sAfterLock sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → ExceptT E (StateM S) (Except TempDirError α))
    (err : E) (rc : Except TempDirError Unit)
    (hCre : (ExceptT.run (Internal.createTempDir fs uuid env root? dirPrefix)).run s₀ = (.ok (.ok dir), sMk))
    (hWfl : (ExceptT.run (fs.withFileLock (fs.join dir ".lock") .shared true
        (do let r ← action dir; return .ok r))).run sMk = (.error err, sAfterLock))
    (hCln : (ExceptT.run (Internal.cleanupDirIgnoringNotFound fs dir)).run sAfterLock = (.ok rc, sFin)) :
    (ExceptT.run ((Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action)).run s₀ =
      (.error err, sFin) := by
  rw [mkApiM_withLockedTempDir_eq]
  dsimp only [Internal.withLockedTempDirM]
  rw [exceptT_stateM_bind_run, hCre]
  dsimp only
  rw [exceptT_stateM_bind_run]
  rw [exceptT_tryFinally'_error_run
    (fs.withFileLock (fs.join dir ".lock") .shared true (do let r ← action dir; return .ok r))
    (fun _ => Internal.cleanupDirIgnoringNotFound fs dir)
    sMk sAfterLock sFin err rc hWfl hCln]

private theorem spec10_part2_run (s₀ : TempDirMockState) (root dirPrefix : String)
    (sMk sAfterLock s2Fin : TempDirMockState)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)), .dir s₀.nowSec 0o700) ::
          s₀.nodes.filter (fun e => !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) })
    (hsAfterLock : sAfterLock =
      { sMk with
        nodes := (mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock",
          .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 })
    (hs2Fin : s2Fin =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e =>
        !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) }) :
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ =
      (.error "boom", s2Fin) := by
  intro _
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  let lockPath := mockJoin dir ".lock"
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hCreate := createTempDir_ex_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hClean2 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sAfterLock =
      (.ok (.ok ()), s2Fin) := by
    rw [hs2Fin]; exact cleanupDir_ex_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  have hInnerThrow : (ExceptT.run (do
      let r ← (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit))
      return .ok r : ExceptT String (StateM TempDirMockState) (Except FsError (Except TempDirError Unit)))).run
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } =
      (.error "boom", { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 }) := by
    rw [exceptT_stateM_bind_run, exceptT_stateM_throw_run]
  have hWflThrow := mockFsEx_withFileLock_create_throw_run sMk lockPath .shared hLockNorm hLookLockMk _ "boom" hInnerThrow
  dsimp only at hWflThrow
  rw [mockRemoveFirstLock_head, ← hsAfterLock] at hWflThrow
  have hJoinEx : mockFsEx.join = mockJoin := rfl
  have hWflLock : (ExceptT.run (mockFsEx.withFileLock (mockFsEx.join dir ".lock") .shared true
      (do let r ← (fun _ => (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit))) dir; return .ok r))).run sMk =
      (.error "boom", sAfterLock) := by
    rw [hJoinEx]
    exact hWflThrow
  exact withLockedTempDir_ex_throw_step mockFsEx mockTimeEx mockUuidEx mockEnvEx
    s₀ sMk sAfterLock s2Fin (some root) dirPrefix dir
    (fun _ => (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))
    "boom" (.ok ()) hCreate hWflLock hClean2

private theorem spec10_part2_probe_exec (s₀ sMk sAfterLock s2Fin : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)), .dir s₀.nowSec 0o700) ::
          s₀.nodes.filter (fun e => !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) })
    (hsAfterLock : sAfterLock =
      { sMk with
        nodes := (mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock",
          .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 })
    (hs2Fin : s2Fin =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e =>
        !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) }) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ((mockFs.lstat dir).run s2Fin).1.isOk = false ∧
    ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run s2Fin).1 =
      .ok (some ()) := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  let lockPath := mockJoin dir ".lock"
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hLookDir2 : lookupNode s2Fin.nodes dir = none := by
    rw [hs2Fin]; exact lookupNode_filter_none_of_underDir sAfterLock.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookRoot2 : lookupNode s2Fin.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hs2Fin, lookupNode_filter_not_underDir_eq sAfterLock.nodes dir (normKey root) hRootUnderDirFalse]
    have hAL : sAfterLock.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterLock, hsMk]
    rw [hAL]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeS2 := probe_exclusive_lock_after_cleanup_run s2Fin root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRoot2 hStRoot hRwx hLookDir2
  refine ⟨mockFs_lstat_isOk_false_of_lookup_none s2Fin dir hLookDir2, ?_⟩
  dsimp only [dir]
  exact hProbeS2

private theorem spec10_part2_exec (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    ∃ s2 : TempDirMockState,
      (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
        (throw "boom" : ExceptT String (StateM TempDirMockState) (Except TempDirError Unit)))).run s₀ =
        (.error "boom", s2) ∧
      ((mockFs.lstat dir).run s2).1.isOk = false ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run s2).1 =
        .ok (some ()) := by
  intro u dir _
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempDirMockState, s =
      { sMk with
        nodes := (mockJoin dir ".lock", .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  obtain ⟨s2Fin, hs2Fin⟩ : ∃ s : TempDirMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hRun2 := spec10_part2_run s₀ root dirPrefix sMk sAfterLock s2Fin hvr hvp stRoot hRoot hRwx hNone
    hsMk hsAfterLock hs2Fin
  have ⟨hLstat2, hProbe2⟩ := spec10_part2_probe_exec s₀ sMk sAfterLock s2Fin root dirPrefix hvr hvp stRoot hRoot hRwx
    hsMk hsAfterLock hs2Fin
  dsimp only [u, dir] at hLstat2 hProbe2 ⊢
  dsimp only [Internal.mkApiM] at hRun2 ⊢
  exact ⟨s2Fin, hRun2, hLstat2, hProbe2⟩

/-- Spec 10: Over `ExceptT String (StateM TempDirMockState)`, throwing inside `withTempDir` or `withLockedTempDir` cleans up and releases the lock while propagating the exception. -/
theorem proof_tempdir_tryFinally_exceptionCleansUpAndReleasesLock :
    AllPass (test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock
      (S := TempDirMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, AllPass]
  intro s₀ root dirPrefix ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  obtain ⟨s1, hRun1, h1⟩ := spec10_part1_exec s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨s2, hRun2, h2, h3⟩ := spec10_part2_exec s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [hRun1, hRun2]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨rfl, h1, rfl, h2, h3, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 10 (`test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock`). -/
theorem reach_tempdir_tryFinally_exceptionCleansUpAndReleasesLock :
    CanReach (test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock
      (S := TempDirMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_tempdir_tryFinally_exceptionCleansUpAndReleasesLock, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempDirMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
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
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s1, hRun1, h1⟩ :=
    spec10_part1_exec s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨s2, hRun2, h2, h3⟩ :=
    spec10_part2_exec s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [hRun1, hRun2]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨rfl, h1, rfl, h2, h3, trivial⟩

end LeanSwe.TempDir.Proofs

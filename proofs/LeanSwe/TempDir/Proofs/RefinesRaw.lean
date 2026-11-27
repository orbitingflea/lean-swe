import Core.Obeys
import LeanSwe.TempDir.Proofs.Shared
import LeanSwe.TempDir.Proofs.LockedProofs
/-!
Primitive step-level refinement bridge (`mockFs_*`, `removeLockedTempDir_of_ops`,
`modelCaps_refines_allowedRawStep`, and `removeLockedTempDir_refines_spec`) for `LeanSwe.TempDir`.
-/
namespace LeanSwe.TempDir.Proofs
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
theorem mapFsError_eq (err : FsError) : Internal.mapFsError err = specMapFsError err := by
  cases hk : err.kind <;> simp [Internal.mapFsError, specMapFsError, hk]
theorem lookupNode_normKey (nodes : List (String × MockNode)) (p : String) :
    lookupNode nodes (normKey p) = lookupNode nodes p := by simp [lookupNode, normKey_idem]
theorem timestamp_ofInt_toSec (n : Int) :
    (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt n)).toSecondsSinceUnixEpoch.val = n := by
  simp [Std.Time.Timestamp.ofSecondsSinceUnixEpoch, Std.Time.Timestamp.toSecondsSinceUnixEpoch,
    Std.Time.Duration.ofSeconds, Std.Time.Second.Offset.ofInt]
theorem hasWx_dir_iff (t : Int) (m : Nat) :
    hasWx (mockNodeStat (.dir t m)) = ((m / 128) % 2 == 1 && (m / 64) % 2 == 1) := by
  simp [hasWx, mockNodeStat, show (EntryKind.dir == EntryKind.dir) = true from rfl]
theorem hasRx_dir_iff (t : Int) (m : Nat) :
    hasRx (mockNodeStat (.dir t m)) = ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) := by
  simp [hasRx, mockNodeStat, show (EntryKind.dir == EntryKind.dir) = true from rfl]
private theorem mockFs_lstat_eq (s : TempDirMockState) (p : String) :
    (mockFs.lstat p).run s = (mockLstatPure s p, s) := rfl
private theorem mockFs_listDir_eq (s : TempDirMockState) (p : String) :
    (mockFs.listDir p).run s = (specListDir s p, s) := by
  dsimp only [mockFs, specListDir]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with | none => rfl | some _ => dsimp only; split <;> first | rfl | (split <;> rfl)
private theorem mockFs_mkdir_eq (s : TempDirMockState) (p : String) (par existOk : Bool) :
    (mockFs.mkdir p par existOk).run s = specMkdir s p existOk := by
  dsimp only [mockFs, specMkdir]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases splitParentChild p with
  | none => rfl
  | some pb =>
    dsimp only; cases lookupNode s.nodes pb.1 with
    | none => rfl
    | some parNode =>
      dsimp only
      by_cases h1 : ((mockNodeStat parNode).kind != EntryKind.dir) = true
      · simp [h1]; rfl
      · simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (!hasWx (mockNodeStat parNode)) = true
        · simp [h2]; rfl
        · simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]
          cases lookupNode s.nodes (mockJoin pb.1 pb.2) with
          | none => rfl
          | some nd => cases nd with
            | dir _ _ => cases existOk <;> rfl
            | file _ _ _ _ | symlink _ _ => rfl
private theorem mockFs_chmod_eq (s : TempDirMockState) (p : String) (mode : Nat) :
    (mockFs.chmod p mode).run s = specChmod s p mode := by
  dsimp only [mockFs, specChmod]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) <;> rfl
private theorem mockFs_unlink_eq (s : TempDirMockState) (p : String) (miss : Bool) :
    (mockFs.unlink p miss).run s = specUnlink s p miss := by
  dsimp only [mockFs, specUnlink]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with | none => cases miss <;> rfl | some nd => cases nd <;> rfl
private theorem mockFs_rmdir_eq (s : TempDirMockState) (p : String) :
    (mockFs.rmdir p).run s = specRmdir s p := by
  dsimp only [mockFs, specRmdir]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with | none => rfl | some nd => cases nd <;> rfl
private theorem mockFs_rmtree_eq (s : TempDirMockState) (p : String) (ign : Bool) :
    (mockFs.rmtree p ign).run s = specRmtree s p ign := by
  dsimp only [mockFs, mockRmtreePure, specRmtree]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with | none => cases ign <;> rfl | some nd => cases nd <;> rfl
private theorem mockFs_withFileLockRet_eq (s : TempDirMockState) (p : String) (mode : LockMode)
    (createIfMissing : Bool) (res : Except TempDirError String) :
    (mockFs.withFileLock p mode createIfMissing (pure (.ok res))).run s =
      specWithFileLockRet s p mode createIfMissing res := by
  dsimp only [mockFs, mockLockCore, specWithFileLockRet]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with
  | some nd => cases nd with
    | dir _ _ | symlink _ _ => rfl
    | file ino _ _ _ =>
      dsimp only
      cases hConf : mockHasConflict s.locks ino mode with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run,
          stateM_tryFinally'_run, stateM_pure_run, stateM_modify_run, mockRemoveFirstLock_head]
        rfl
  | none =>
    cases createIfMissing with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run,
        stateM_tryFinally'_run, stateM_pure_run, stateM_modify_run, mockRemoveFirstLock_head]
      rfl
theorem removeNonLockChildren_eq_callback {W : Type} (fs : FsApiM (StateM W))
    (child : String) (names : List String) :
    Internal.removeNonLockChildren fs child names = tryLockRemoveChildren fs child names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    funext w
    change (Internal.removeNonLockChildren fs child (name :: rest)).run w =
      (tryLockRemoveChildren fs child (name :: rest)).run w
    dsimp only [Internal.removeNonLockChildren, tryLockRemoveChildren]
    by_cases hLock : (name == ".lock") = true
    · simp only [hLock, ↓reduceIte]; exact congrArg (fun f => f.run w) ih
    · simp only [Bool.eq_false_iff.mpr hLock, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, stateM_bind_run]
      cases (fs.lstat (fs.join child name)).run w with
      | mk rSt w1 =>
        cases rSt with
        | error fe =>
          dsimp only; by_cases hNf : (fe.kind == .notFound) = true
          · simp only [hNf, ↓reduceIte]; exact congrArg (fun f => f.run w1) ih
          · simp only [Bool.eq_false_iff.mpr hNf, Bool.false_eq_true, ↓reduceIte, mapFsError_eq]
        | ok st =>
          dsimp only; by_cases hDir : (st.kind == .dir) = true
          · simp only [hDir, ↓reduceIte, Internal.cleanupDirIgnoringNotFound]
            rw [stateM_bind_run, stateM_bind_run (x := fs.rmtree (fs.join child name) true),
              stateM_bind_run (x := fs.rmtree (fs.join child name) true)]
            cases (fs.rmtree (fs.join child name) true).run w1 with
            | mk rRm w2 =>
              cases rRm with
              | ok _ => simp only [stateM_bind_run, stateM_pure_run]; exact congrArg (fun f => f.run w2) ih
              | error fe =>
                dsimp only; by_cases hNf : (fe.kind == .notFound) = true
                · simp only [hNf, ↓reduceIte, stateM_bind_run, stateM_pure_run]; exact congrArg (fun f => f.run w2) ih
                · simp only [Bool.eq_false_iff.mpr hNf, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run, mapFsError_eq]
          · simp only [Bool.eq_false_iff.mpr hDir, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run, stateM_bind_run]
            cases (fs.unlink (fs.join child name) true).run w1 with
            | mk rUn w2 =>
              cases rUn with
              | ok _ => simp only [stateM_bind_run, stateM_pure_run]; exact congrArg (fun f => f.run w2) ih
              | error fe => simp only [stateM_bind_run, stateM_pure_run, mapFsError_eq]
theorem removeLockedTempDir_eq_callback {W : Type} (fs : FsApiM (StateM W))
    (child lockPath : String) :
    Internal.removeLockedTempDir fs child lockPath = tryLockRemoveCallback fs child lockPath := by
  funext w
  change (Internal.removeLockedTempDir fs child lockPath).run w =
    (tryLockRemoveCallback fs child lockPath).run w
  dsimp only [Internal.removeLockedTempDir, tryLockRemoveCallback]
  rw [stateM_bind_run, stateM_bind_run]
  cases (fs.listDir child).run w with
  | mk rList w1 =>
    cases rList with
    | error fe =>
      dsimp only; by_cases hNf : (fe.kind == .notFound) = true
      · simp only [hNf, ↓reduceIte]
      · simp only [Bool.eq_false_iff.mpr hNf, Bool.false_eq_true, ↓reduceIte, mapFsError_eq]
    | ok names =>
      dsimp only; rw [stateM_bind_run, stateM_bind_run, removeNonLockChildren_eq_callback]
      cases (tryLockRemoveChildren fs child names.toList).run w1 with
      | mk rCh w2 =>
        cases rCh with
        | error _ => rfl
        | ok _ =>
          dsimp only; rw [stateM_bind_run, stateM_bind_run]
          cases (fs.unlink lockPath true).run w2 with
          | mk rUn w3 =>
            cases rUn with
            | error fe => simp only [mapFsError_eq]
            | ok _ =>
              dsimp only; rw [stateM_bind_run, stateM_bind_run]
              cases (fs.rmdir child).run w3 with
              | mk rRm w4 =>
                cases rRm with
                | ok _ => rfl
                | error fe =>
                  dsimp only; by_cases hNf : (fe.kind == .notFound) = true
                  · simp only [hNf, ↓reduceIte]
                  · simp only [Bool.eq_false_iff.mpr hNf, Bool.false_eq_true, ↓reduceIte, mapFsError_eq]
private theorem removeNonLockChildren_of_ops {W : Type} (proj : W → TempDirMockState)
    (fs : FsApiM (StateM W)) (hJoin : ∀ a b, fs.join a b = mockJoin a b)
    (hLstat : ∀ p w, ((fs.lstat p).run w).1 = mockLstatPure (proj w) p ∧ proj ((fs.lstat p).run w).2 = proj w)
    (hRmtree : ∀ p ign w, ((fs.rmtree p ign).run w).1 = (specRmtree (proj w) p ign).1 ∧ proj ((fs.rmtree p ign).run w).2 = (specRmtree (proj w) p ign).2)
    (hUnlink : ∀ p miss w, ((fs.unlink p miss).run w).1 = (specUnlink (proj w) p miss).1 ∧ proj ((fs.unlink p miss).run w).2 = (specUnlink (proj w) p miss).2)
    (child : String) (names : List String) (w : W) :
    let r := (Internal.removeNonLockChildren fs child names).run w
    r.1 = .ok () ∧ proj r.2 = specRemoveNonLockChildren (proj w) child names := by
  induction names generalizing w with
  | nil => exact ⟨rfl, rfl⟩
  | cons name rest ih =>
    dsimp only [Internal.removeNonLockChildren, specRemoveNonLockChildren]
    by_cases hLock : (name == ".lock") = true
    · simp only [hLock, ↓reduceIte]; exact ih w
    · simp only [Bool.eq_false_iff.mpr hLock, Bool.false_eq_true, ↓reduceIte, hJoin]
      rw [stateM_bind_run]
      have hLs := hLstat (mockJoin child name) w
      cases hLRun : (fs.lstat (mockJoin child name)).run w with
      | mk rSt w1 =>
        rw [hLRun] at hLs; dsimp only at hLs; obtain ⟨hStEq, hProj1⟩ := hLs
        rw [hStEq]; dsimp only [mockLstatPure]
        cases hNd : lookupNode (proj w).nodes (mockJoin child name) with
        | none => have hRec := ih w1; rwa [hProj1] at hRec
        | some nd =>
          have hNd1 : lookupNode (proj w1).nodes (normKey (mockJoin child name)) = some nd := by
            rw [hProj1, lookupNode_normKey, hNd]
          cases nd with
          | dir t m =>
            simp only [mockNodeStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte,
              Internal.cleanupDirIgnoringNotFound]
            rw [stateM_bind_run, stateM_bind_run (x := fs.rmtree (mockJoin child name) true)]
            have hRm := hRmtree (mockJoin child name) true w1
            cases hRmRun : (fs.rmtree (mockJoin child name) true).run w1 with
            | mk rRm w2 =>
              rw [hRmRun] at hRm; dsimp only [specRmtree] at hRm; rw [hNd1] at hRm; dsimp only at hRm
              rw [hRm.1]; dsimp only; rw [stateM_pure_run]; dsimp only
              have hRec := ih w2; rwa [hRm.2, hProj1] at hRec
          | file ino c t m =>
            simp only [mockNodeStat, show (EntryKind.file == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run]
            have hUn := hUnlink (mockJoin child name) true w1
            cases hUnRun : (fs.unlink (mockJoin child name) true).run w1 with
            | mk rUn w2 =>
              rw [hUnRun] at hUn; dsimp only [specUnlink] at hUn; rw [hNd1] at hUn; dsimp only at hUn
              rw [hUn.1]; simp only [stateM_bind_run, stateM_pure_run]
              have hRec := ih w2; rwa [hUn.2, hProj1] at hRec
          | symlink tgt t =>
            simp only [mockNodeStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run]
            have hUn := hUnlink (mockJoin child name) true w1
            cases hUnRun : (fs.unlink (mockJoin child name) true).run w1 with
            | mk rUn w2 =>
              rw [hUnRun] at hUn; dsimp only [specUnlink] at hUn; rw [hNd1] at hUn; dsimp only at hUn
              rw [hUn.1]; simp only [stateM_bind_run, stateM_pure_run]
              have hRec := ih w2; rwa [hUn.2, hProj1] at hRec
private theorem removeLockedTempDir_of_ops {W : Type} (proj : W → TempDirMockState)
    (fs : FsApiM (StateM W)) (hJoin : ∀ a b, fs.join a b = mockJoin a b)
    (hLstat : ∀ p w, ((fs.lstat p).run w).1 = mockLstatPure (proj w) p ∧ proj ((fs.lstat p).run w).2 = proj w)
    (hRmtree : ∀ p ign w, ((fs.rmtree p ign).run w).1 = (specRmtree (proj w) p ign).1 ∧ proj ((fs.rmtree p ign).run w).2 = (specRmtree (proj w) p ign).2)
    (hUnlink : ∀ p miss w, ((fs.unlink p miss).run w).1 = (specUnlink (proj w) p miss).1 ∧ proj ((fs.unlink p miss).run w).2 = (specUnlink (proj w) p miss).2)
    (hListDir : ∀ p w, ((fs.listDir p).run w).1 = specListDir (proj w) p ∧ proj ((fs.listDir p).run w).2 = proj w)
    (hRmdir : ∀ p w, ((fs.rmdir p).run w).1 = (specRmdir (proj w) p).1 ∧ proj ((fs.rmdir p).run w).2 = (specRmdir (proj w) p).2)
    (child lockPath : String) (w : W) :
    let r := (Internal.removeLockedTempDir fs child lockPath).run w
    let sp := specRemoveLockedDir (proj w) child lockPath
    r.1 = .ok sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.removeLockedTempDir, specRemoveLockedDir]; rw [stateM_bind_run]
  have hLs := hListDir child w
  cases hLRun : (fs.listDir child).run w with
  | mk rList w1 =>
    rw [hLRun] at hLs; dsimp only [specListDir] at hLs; obtain ⟨hListEq, hProj1⟩ := hLs
    cases hChild : lookupNode (proj w).nodes (normKey child) with
    | none => rw [hChild] at hListEq; rw [hListEq]; exact ⟨rfl, hProj1⟩
    | some nd =>
      cases nd with
      | file _ _ _ _ | symlink _ _ =>
        rw [hChild] at hListEq; rw [hListEq]; exact ⟨rfl, hProj1⟩
      | dir t m =>
        rw [hChild] at hListEq; dsimp only at hListEq
        have hRxEq : hasRx (mockNodeStat (.dir t m)) = ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) := hasRx_dir_iff t m
        have hKindF : ((mockNodeStat (.dir t m)).kind != EntryKind.dir) = false := rfl
        rw [hKindF, hRxEq] at hListEq
        simp only [Bool.false_eq_true, ↓reduceIte] at hListEq
        by_cases hRx : ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) = true
        · simp only [hRx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hListEq ⊢
          rw [hListEq]; rw [stateM_bind_run]
          let names := sortStrings (eraseDupStrings ((proj w).nodes.filterMap (fun e => mockParentChild (normKey child) e.1)))
          have hCh := removeNonLockChildren_of_ops proj fs hJoin hLstat hRmtree hUnlink child names w1
          cases hChRun : (Internal.removeNonLockChildren fs child names).run w1 with
          | mk rCh w2 =>
            rw [hChRun] at hCh; dsimp only at hCh; rw [hCh.1]; dsimp only
            have hProj2 : proj w2 = specRemoveNonLockChildren (proj w) child names := by rw [hCh.2, hProj1]
            rw [stateM_bind_run]
            have hUn := hUnlink lockPath true w2
            cases hUnRun : (fs.unlink lockPath true).run w2 with
            | mk rUn w3 =>
              rw [hUnRun] at hUn; dsimp only [specUnlink] at hUn; rw [hProj2] at hUn
              cases hLk : lookupNode (specRemoveNonLockChildren (proj w) child names).nodes (normKey lockPath) with
              | some ndL => cases ndL with
                | dir _ _ => rw [hLk] at hUn; dsimp only at hUn; rw [hUn.1]; exact ⟨rfl, hUn.2⟩
                | file _ _ _ _ | symlink _ _ =>
                  rw [hLk] at hUn; dsimp only at hUn; rw [hUn.1]; dsimp only; rw [stateM_bind_run]
                  have hRm := hRmdir child w3
                  cases hRmRun : (fs.rmdir child).run w3 with
                  | mk rRm w4 =>
                    rw [hRmRun] at hRm; dsimp only [specRmdir] at hRm; rw [hUn.2] at hRm
                    cases hC2 : lookupNode ((specRemoveNonLockChildren (proj w) child names).nodes.filter (fun e => normKey e.1 != normKey lockPath)) (normKey child) with
                    | none => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩
                    | some nd2 => cases nd2 with | dir _ _ => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩ | file _ _ _ _ | symlink _ _ => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩
              | none =>
                rw [hLk] at hUn; simp only [↓reduceIte] at hUn; rw [hUn.1]; dsimp only; rw [stateM_bind_run]
                have hRm := hRmdir child w3
                cases hRmRun : (fs.rmdir child).run w3 with
                | mk rRm w4 =>
                  rw [hRmRun] at hRm; dsimp only [specRmdir] at hRm; rw [hUn.2] at hRm
                  cases hC2 : lookupNode (specRemoveNonLockChildren (proj w) child names).nodes (normKey child) with
                  | none => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩
                  | some nd2 => cases nd2 with | dir _ _ => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩ | file _ _ _ _ | symlink _ _ => rw [hC2] at hRm; rw [hRm.1]; exact ⟨rfl, hRm.2⟩
        · simp only [Bool.eq_false_iff.mpr hRx, Bool.not_false, ↓reduceIte] at hListEq ⊢
          rw [hListEq]; dsimp only [Internal.mapFsError]; exact ⟨rfl, hProj1⟩
private theorem specRemoveNonLockChildren_with_locks (s : TempDirMockState) (child : String)
    (names : List String) (l : List (Nat × LockMode)) :
    specRemoveNonLockChildren { s with locks := l } child names =
      { specRemoveNonLockChildren s child names with locks := l } := by
  induction names generalizing s with
  | nil => rfl
  | cons name rest ih =>
    dsimp only [specRemoveNonLockChildren]
    by_cases hLock : (name == ".lock") = true
    · simp only [hLock, ↓reduceIte]; exact ih s
    · simp only [Bool.eq_false_iff.mpr hLock, Bool.false_eq_true, ↓reduceIte]
      cases lookupNode s.nodes (mockJoin child name) with
      | none => exact ih s
      | some nd => cases nd with
        | dir _ _ => exact ih { s with nodes := s.nodes.filter (fun e => !underDir (normKey (mockJoin child name)) e.1) }
        | file _ _ _ _ | symlink _ _ => exact ih { s with nodes := s.nodes.filter (fun e => normKey e.1 != normKey (mockJoin child name)) }
private theorem specRemoveLockedDir_with_locks (s : TempDirMockState) (child lockPath : String) (l : List (Nat × LockMode)) :
    let sp := specRemoveLockedDir s child lockPath
    specRemoveLockedDir { s with locks := l } child lockPath = (sp.1, { sp.2 with locks := l }) := by
  dsimp only [specRemoveLockedDir]
  cases hC : lookupNode s.nodes (normKey child) with
  | none => rfl
  | some nd => cases nd with
    | file _ _ _ _ | symlink _ _ => rfl
    | dir t m =>
      by_cases hRx : ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) = true
      · simp only [hRx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [specRemoveNonLockChildren_with_locks s child _ l]
        generalize specRemoveNonLockChildren s child (sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey child) e.1)))) = s1
        cases hLk : lookupNode s1.nodes (normKey lockPath) with
        | none =>
          cases lookupNode s1.nodes (normKey child) with
          | none => rfl | some nd2 => cases nd2 <;> rfl
        | some ndL => cases ndL with
          | dir _ _ => rfl
          | file _ _ _ _ | symlink _ _ =>
            cases lookupNode (s1.nodes.filter (fun e => normKey e.1 != normKey lockPath)) (normKey child) with
            | none => rfl | some nd2 => cases nd2 <;> rfl
      · simp only [Bool.eq_false_iff.mpr hRx, Bool.not_false, ↓reduceIte]
private theorem specRemoveLockedDir_locks_eq (s : TempDirMockState) (child lockPath : String) :
    (specRemoveLockedDir s child lockPath).2.locks = s.locks := by
  have h := congrArg (fun p => p.2.locks) (specRemoveLockedDir_with_locks s child lockPath s.locks)
  simpa using h
private theorem mockFs_removeLockedTempDir_eq (child lockPath : String) (s : TempDirMockState) :
    ((Internal.removeLockedTempDir mockFs child lockPath).run s).1 = .ok (specRemoveLockedDir s child lockPath).1 ∧
      ((Internal.removeLockedTempDir mockFs child lockPath).run s).2 = (specRemoveLockedDir s child lockPath).2 :=
  removeLockedTempDir_of_ops id mockFs (fun _ _ => rfl)
    (fun p st => by rw [mockFs_lstat_eq]; exact ⟨rfl, rfl⟩)
    (fun p ign st => by rw [mockFs_rmtree_eq]; exact ⟨rfl, rfl⟩)
    (fun p miss st => by rw [mockFs_unlink_eq]; exact ⟨rfl, rfl⟩)
    (fun p st => by rw [mockFs_listDir_eq]; exact ⟨rfl, rfl⟩)
    (fun p st => by rw [mockFs_rmdir_eq]; exact ⟨rfl, rfl⟩)
    child lockPath s
/-- Non-vacuity witness: `Model.Internal.modelCaps` satisfies every single `RawStepReq` transition
in `allowedRawStep`, including `fsUnlink`, `fsRmdir`, and `fsTryWithFileLockRemoveLocked`. -/
theorem modelCaps_refines_allowedRawStep :
    Core.ObeysStep id tempDirStepWf (execRawStep modelCaps) allowedRawStep := by
  intro s req _
  cases req with
  | fsJoin _ _ | fsStat _ | fsLstat _ | timeNowTimestamp | uuidGetUuid | uuidToString _ => exact ⟨rfl, rfl⟩
  | fsMkdir p par existOk =>
    change RawStepOut.unitRes ((mockFs.mkdir p par existOk).run s).1 = RawStepOut.unitRes (specMkdir s p existOk).1 ∧
      ((mockFs.mkdir p par existOk).run s).2 = (specMkdir s p existOk).2
    rw [mockFs_mkdir_eq]; exact ⟨rfl, rfl⟩
  | fsChmod p mode =>
    change RawStepOut.unitRes ((mockFs.chmod p mode).run s).1 = RawStepOut.unitRes (specChmod s p mode).1 ∧
      ((mockFs.chmod p mode).run s).2 = (specChmod s p mode).2
    rw [mockFs_chmod_eq]; exact ⟨rfl, rfl⟩
  | fsUnlink p miss =>
    change RawStepOut.unitRes ((mockFs.unlink p miss).run s).1 = RawStepOut.unitRes (specUnlink s p miss).1 ∧
      ((mockFs.unlink p miss).run s).2 = (specUnlink s p miss).2
    rw [mockFs_unlink_eq]; exact ⟨rfl, rfl⟩
  | fsRmdir p =>
    change RawStepOut.unitRes ((mockFs.rmdir p).run s).1 = RawStepOut.unitRes (specRmdir s p).1 ∧
      ((mockFs.rmdir p).run s).2 = (specRmdir s p).2
    rw [mockFs_rmdir_eq]; exact ⟨rfl, rfl⟩
  | fsRmtree p ign =>
    change RawStepOut.unitRes ((mockFs.rmtree p ign).run s).1 = RawStepOut.unitRes (specRmtree s p ign).1 ∧
      ((mockFs.rmtree p ign).run s).2 = (specRmtree s p ign).2
    rw [mockFs_rmtree_eq]; exact ⟨rfl, rfl⟩
  | fsListDir p =>
    change RawStepOut.names ((mockFs.listDir p).run s).1 = RawStepOut.names (specListDir s p) ∧
      ((mockFs.listDir p).run s).2 = s
    rw [mockFs_listDir_eq]; exact ⟨rfl, rfl⟩
  | fsWithFileLockRet p mode createIfMissing res =>
    change RawStepOut.lockRet ((mockFs.withFileLock p mode createIfMissing (pure (.ok res))).run s).1 =
        RawStepOut.lockRet (specWithFileLockRet s p mode createIfMissing res).1 ∧
      ((mockFs.withFileLock p mode createIfMissing (pure (.ok res))).run s).2 =
        (specWithFileLockRet s p mode createIfMissing res).2
    rw [mockFs_withFileLockRet_eq]; exact ⟨rfl, rfl⟩
  | fsTryWithFileLockRemoveLocked child lockPath =>
    change RawStepOut.tryLockRemove ((mockFs.tryWithFileLock lockPath .exclusive false (tryLockRemoveCallback mockFs child lockPath)).run s).1 =
        RawStepOut.tryLockRemove (specTryLockRemove s child lockPath).1 ∧
      ((mockFs.tryWithFileLock lockPath .exclusive false (tryLockRemoveCallback mockFs child lockPath)).run s).2 =
        (specTryLockRemove s child lockPath).2
    rw [← removeLockedTempDir_eq_callback]
    have hRunLock : ∀ (act : StateM TempDirMockState (Except FsError (Except TempDirError Unit))),
        (mockFs.tryWithFileLock lockPath .exclusive false act).run s =
          match lookupNode s.nodes (normKey lockPath) with
          | some (.dir _ _) => (.error { kind := .isADirectory, path := some lockPath, message := "is dir" }, s)
          | some (.symlink _ _) => (.error { kind := .invalidInput, path := some lockPath, message := "symlink" }, s)
          | some (.file ino _ _ _) =>
            if mockHasConflict s.locks ino .exclusive then (.ok none, s)
            else
              let r := act.run { s with locks := (ino, .exclusive) :: s.locks }
              (r.1.map some, { r.2 with locks := mockRemoveFirstLock ino .exclusive r.2.locks })
          | none => (.error { kind := .notFound, path := some lockPath, message := "not found" }, s) := by
      intro act; dsimp only [mockFs, mockLockCore]; rw [stateM_bind_run, stateM_get_run]; dsimp only
      cases lookupNode s.nodes (normKey lockPath) with
      | none => rfl
      | some nd => cases nd with
        | dir _ _ | symlink _ _ => rfl
        | file ino _ _ _ =>
          dsimp only; cases hC : mockHasConflict s.locks ino .exclusive with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run,
              stateM_tryFinally'_run, stateM_modify_run, stateM_pure_run]
            cases act.run { s with locks := (ino, .exclusive) :: s.locks }; rfl
    rw [hRunLock]
    dsimp only [specTryLockRemove]
    cases lookupNode s.nodes (normKey lockPath) with
    | none => exact ⟨rfl, rfl⟩
    | some nd => cases nd with
      | dir _ _ | symlink _ _ => exact ⟨rfl, rfl⟩
      | file ino _ _ _ =>
        dsimp only; cases mockHasConflict s.locks ino .exclusive with
        | true => exact ⟨rfl, rfl⟩
        | false =>
          have hBody := mockFs_removeLockedTempDir_eq child lockPath { s with locks := (ino, .exclusive) :: s.locks }
          have hWl := specRemoveLockedDir_with_locks s child lockPath ((ino, .exclusive) :: s.locks)
          rw [hWl] at hBody; dsimp only at hBody
          rw [hBody.1, hBody.2]; dsimp only [Except.map]
          refine ⟨rfl, ?_⟩
          rw [mockRemoveFirstLock_head]
          have hEqL := specRemoveLockedDir_locks_eq s child lockPath
          cases hSp : specRemoveLockedDir s child lockPath with
          | mk rSp sSp => rw [hSp] at hEqL; dsimp only at hEqL; cases sSp; simpa using hEqL.symm
  | envGetEnv name =>
    change RawStepOut.env ((mockEnv.getEnv name).run s).1 = RawStepOut.env (.ok (if name == "TMPDIR" then s.tmpdir else none)) ∧
      ((mockEnv.getEnv name).run s).2 = s
    dsimp only [mockEnv]; cases (name == "TMPDIR") <;> exact ⟨rfl, rfl⟩
theorem raw_fsJoin_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (a b : String) :
    caps.fs.join a b = mockJoin a b := RawStepOut.str.inj (hRaw w (.fsJoin a b) rfl).1
theorem raw_fsStat_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) :
    ((caps.fs.stat p).run w).1 = mockStatPure (proj w) p ∧ proj ((caps.fs.stat p).run w).2 = proj w := by
  have h := hRaw w (.fsStat p) rfl; exact ⟨RawStepOut.stat.inj h.1, h.2⟩
theorem raw_fsLstat_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) :
    ((caps.fs.lstat p).run w).1 = mockLstatPure (proj w) p ∧ proj ((caps.fs.lstat p).run w).2 = proj w := by
  have h := hRaw w (.fsLstat p) rfl; exact ⟨RawStepOut.stat.inj h.1, h.2⟩
theorem raw_fsMkdir_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) (par existOk : Bool) :
    ((caps.fs.mkdir p par existOk).run w).1 = (specMkdir (proj w) p existOk).1 ∧
      proj ((caps.fs.mkdir p par existOk).run w).2 = (specMkdir (proj w) p existOk).2 := by
  have h := hRaw w (.fsMkdir p par existOk) rfl; exact ⟨RawStepOut.unitRes.inj h.1, h.2⟩
theorem raw_fsChmod_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) (mode : Nat) :
    ((caps.fs.chmod p mode).run w).1 = (specChmod (proj w) p mode).1 ∧
      proj ((caps.fs.chmod p mode).run w).2 = (specChmod (proj w) p mode).2 := by
  have h := hRaw w (.fsChmod p mode) rfl; exact ⟨RawStepOut.unitRes.inj h.1, h.2⟩
theorem raw_fsUnlink_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) (miss : Bool) :
    ((caps.fs.unlink p miss).run w).1 = (specUnlink (proj w) p miss).1 ∧
      proj ((caps.fs.unlink p miss).run w).2 = (specUnlink (proj w) p miss).2 := by
  have h := hRaw w (.fsUnlink p miss) rfl; exact ⟨RawStepOut.unitRes.inj h.1, h.2⟩
theorem raw_fsRmdir_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) :
    ((caps.fs.rmdir p).run w).1 = (specRmdir (proj w) p).1 ∧
      proj ((caps.fs.rmdir p).run w).2 = (specRmdir (proj w) p).2 := by
  have h := hRaw w (.fsRmdir p) rfl; exact ⟨RawStepOut.unitRes.inj h.1, h.2⟩
theorem raw_fsRmtree_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) (ign : Bool) :
    ((caps.fs.rmtree p ign).run w).1 = (specRmtree (proj w) p ign).1 ∧
      proj ((caps.fs.rmtree p ign).run w).2 = (specRmtree (proj w) p ign).2 := by
  have h := hRaw w (.fsRmtree p ign) rfl; exact ⟨RawStepOut.unitRes.inj h.1, h.2⟩
theorem raw_fsListDir_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (p : String) :
    ((caps.fs.listDir p).run w).1 = specListDir (proj w) p ∧ proj ((caps.fs.listDir p).run w).2 = proj w := by
  have h := hRaw w (.fsListDir p) rfl; exact ⟨RawStepOut.names.inj h.1, h.2⟩
theorem raw_fsWithFileLockRet_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W)
    (p : String) (mode : LockMode) (createIfMissing : Bool) (res : Except TempDirError String) :
    ((caps.fs.withFileLock p mode createIfMissing (pure (.ok res))).run w).1 = (specWithFileLockRet (proj w) p mode createIfMissing res).1 ∧
      proj ((caps.fs.withFileLock p mode createIfMissing (pure (.ok res))).run w).2 = (specWithFileLockRet (proj w) p mode createIfMissing res).2 := by
  have h := hRaw w (.fsWithFileLockRet p mode createIfMissing res) rfl; exact ⟨RawStepOut.lockRet.inj h.1, h.2⟩
theorem raw_fsTryLockRemove_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (child lockPath : String) :
    ((caps.fs.tryWithFileLock lockPath .exclusive false (Internal.removeLockedTempDir caps.fs child lockPath)).run w).1 =
        (specTryLockRemove (proj w) child lockPath).1 ∧
      proj ((caps.fs.tryWithFileLock lockPath .exclusive false (Internal.removeLockedTempDir caps.fs child lockPath)).run w).2 =
        (specTryLockRemove (proj w) child lockPath).2 := by
  rw [removeLockedTempDir_eq_callback]; have h := hRaw w (.fsTryWithFileLockRemoveLocked child lockPath) rfl
  exact ⟨RawStepOut.tryLockRemove.inj h.1, h.2⟩
theorem raw_timeNow_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) :
    (caps.time.nowTimestamp.run w).1 = Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (proj w).nowSec) ∧
      proj (caps.time.nowTimestamp.run w).2 = proj w := by
  have h := hRaw w .timeNowTimestamp rfl; exact ⟨RawStepOut.ts.inj h.1, h.2⟩
theorem raw_uuidGet_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) :
    (caps.uuid.getUuid.run w).1 = .ok (mockUuidOfNat (proj w).nextUuid) ∧
      proj (caps.uuid.getUuid.run w).2 = { proj w with nextUuid := (proj w).nextUuid + 1 } := by
  have h := hRaw w .uuidGetUuid rfl; exact ⟨RawStepOut.uuid.inj h.1, h.2⟩
theorem raw_uuidToString_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (u : Uuid) :
    caps.uuid.toString u = mockUuidToString u := RawStepOut.str.inj (hRaw w (.uuidToString u) rfl).1
theorem raw_envGetEnv_eq {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (w : W) (name : String) :
    ((caps.env.getEnv name).run w).1 = .ok (if name == "TMPDIR" then (proj w).tmpdir else none) ∧
      proj ((caps.env.getEnv name).run w).2 = proj w := by
  have h := hRaw w (.envGetEnv name) rfl; exact ⟨RawStepOut.env.inj h.1, h.2⟩
/-- Step-by-step refinement of `Internal.removeLockedTempDir` against pure `specRemoveLockedDir`
over `fsListDir`, `fsLstat`, `fsRmtree`, `fsUnlink`, and `fsRmdir`. -/
theorem removeLockedTempDir_refines_spec {W : Type} (proj : W → TempDirMockState) (caps : TempDirCaps (StateM W))
    (hRaw : Core.ObeysStep proj tempDirStepWf (execRawStep caps) allowedRawStep) (child lockPath : String) (w : W) :
    let r := (Internal.removeLockedTempDir caps.fs child lockPath).run w
    let sp := specRemoveLockedDir (proj w) child lockPath
    r.1 = .ok sp.1 ∧ proj r.2 = sp.2 :=
  removeLockedTempDir_of_ops proj caps.fs (fun a b => raw_fsJoin_eq proj caps hRaw w a b)
    (fun p w' => raw_fsLstat_eq proj caps hRaw w' p) (fun p ign w' => raw_fsRmtree_eq proj caps hRaw w' p ign)
    (fun p miss w' => raw_fsUnlink_eq proj caps hRaw w' p miss) (fun p w' => raw_fsListDir_eq proj caps hRaw w' p)
    (fun p w' => raw_fsRmdir_eq proj caps hRaw w' p) child lockPath w
end LeanSwe.TempDir.Proofs

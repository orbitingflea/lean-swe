import LeanSwe.LinuxSyscall.Files.SpecTests
import LeanSwe.LinuxSyscall.Files.Model

namespace LeanSwe.LinuxSyscall.Files

open Core (AllPass CanReach)
open Core.NondetTest

/-- Proof helper for `files_ops_embeddedNulRejectedWithEinval_allPass`. -/
theorem files_ops_embeddedNulRejectedWithEinval_proof :
    AllPass (test_files_ops_embeddedNulRejectedWithEinval modelOps) := by
  intro s₀ dir flags how atFlags mask mode rmDir renFlags cap badPath hNul
  dsimp only [Bind.bind, assert, pure, modelOps, StateT.run, StateT.bind, StateT.get,
    StateT.pure, get, getThe, MonadState.get, MonadStateOf.get, runOp, set, MonadStateOf.set]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    simp only [evalModel, evalReq, precheckNul, hNul, Bool.true_or, Bool.or_true, ↓reduceIte]
    rfl

private def uw_fname : ByteArray :=
  asciiBytes ['u', 'n', 'l', 'i', 'n', 'k', '.', 'b', 'i', 'n']

private def uw_data : ByteArray :=
  asciiBytes ['k', 'e', 'e', 'p']

private def uw_s1 :=
  (modelOps.openat none uw_fname { access := .rdwr, creat := true, excl := true } 0o644).run FilesState.initial

private def uw_s2 :=
  (modelOps.openat none uw_fname { access := .rdonly } 0).run uw_s1.2

private def uw_s3 :=
  (modelOps.write 0 uw_data).run uw_s2.2

private def uw_s4 :=
  (modelOps.unlinkat none uw_fname false).run uw_s3.2

private theorem uw_s4_lookup :
    ∃ d rd, assocGet uw_s4.2.fds 1 = some d ∧
      assocGet uw_s4.2.inodes d.ino = some { data := .reg rd, mode := 0o644, modeExact := true, nlink := 0 } ∧
      d.access = .rdonly ∧ d.isPathFd = false ∧ d.isExternalStdio = false ∧
      d.pos = .byteOffset 0 ∧ rd = RegData.ofBytes uw_data :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem uw_read_ok :
    ((modelOps.read 1 4).run
      ((modelOps.unlinkat none uw_fname false).run
        ((modelOps.write 0 uw_data).run
          ((modelOps.openat none uw_fname { access := .rdonly } 0).run
            ((modelOps.openat none uw_fname { access := .rdwr, creat := true, excl := true } 0o644).run
              FilesState.initial).2).2).2).2).1 = .ok uw_data := by
  change ((modelOps.read 1 4).run uw_s4.2).1 = .ok uw_data
  rcases uw_s4_lookup with ⟨d, rd, hF, hI, hAcc, hPathFd, hExt, hPos, hRd⟩
  dsimp only [modelOps, StateT.run, Bind.bind, StateT.bind, StateT.get, get, getThe,
    MonadState.get, MonadStateOf.get, set, MonadStateOf.set, StateT.set, StateT.pure, pure, runOp, evalModel, evalReq, precheckNul, evalRead]
  rw [hF]
  dsimp only
  rw [hPathFd, hAcc]
  simp only [Bool.false_or]
  rw [show (AccessMode.rdonly == AccessMode.wronly) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hExt]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hI]
  dsimp only
  rw [show VNode.isDynamic { data := .reg rd, mode := 0o644, modeExact := true, nlink := 0 } = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hPos]
  have hNoOv : ¬ (FilePos.byteOffset.offset + min (UInt32.toNat 4) MAX_READ_BYTES.toNat > 9223372036854775807) := by decide
  simp only [hNoOv, ↓reduceIte]
  dsimp only [runNondetDefault]
  rw [hPos, hRd]
  rfl

/-- Proof helper for `files_ops_unlinkWhileOpen_preservesIoAndDeadDir_allPass`. -/
theorem files_ops_unlinkWhileOpen_preservesIoAndDeadDir_proof :
    AllPass (test_files_ops_unlinkWhileOpen_preservesIoAndDeadDir modelOps FilesState.initial) := by
  refine ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl⟩, ?_,
    rfl, rfl, ⟨_, rfl, rfl, rfl⟩, rfl, rfl, rfl, trivial⟩
  change ((modelOps.read _ 4).run _).1 = .ok uw_data
  exact uw_read_ok

private theorem validatePathBytes_ok {p : ByteArray}
    (hNul : hasEmbeddedNul p = false) (hPath : p.data.size < PATH_MAX) :
    validatePathBytes p = .ok (splitPathBytes p) := by
  unfold validatePathBytes
  have hGe : ¬ (p.size ≥ PATH_MAX) := by
    change ¬ (p.data.size ≥ PATH_MAX)
    exact Nat.not_le_of_lt hPath
  simp only [hNul, Bool.false_eq_true, ↓reduceIte]
  split
  · next h => exact absurd h hGe
  · rfl

private theorem validatePathBytes_maxPath {p : ByteArray}
    (hNul : hasEmbeddedNul p = false) (hPath : p.data.size ≥ PATH_MAX) :
    validatePathBytes p = .error Errno.ENAMETOOLONG := by
  unfold validatePathBytes
  have hPath' : p.size ≥ PATH_MAX := hPath
  simp only [hNul, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · next h => exact absurd hPath' h

set_option maxRecDepth 4096 in
private theorem resolveOpenTarget_longSeg {p : ByteArray}
    (hNul : hasEmbeddedNul p = false) (hPath : p.data.size < PATH_MAX)
    (hName : p.data.size > NAME_MAX) (hSplit : (splitPathBytes p).2.1 = [p]) :
    resolveOpenTarget FilesState.initial none p true false {} = .error Errno.ENAMETOOLONG := by
  unfold resolveOpenTarget resolveOpenTargetWalk
  rw [validatePathBytes_ok hNul hPath]
  have hNonEmpty : (p.size == 0) = false := by
    have : p.size > 0 := Nat.lt_trans (by decide) hName
    exact beq_false_of_ne (Nat.ne_of_gt this)
  have hName' : p.size > NAME_MAX := hName
  rcases hSp : splitPathBytes p with ⟨isAbs, segs, trailing⟩
  have hSegs : segs = [p] := by
    have := hSplit
    rw [hSp] at this
    exact this
  subst hSegs
  have hNotDot : bytesEq p dotBytes = false := by
    unfold bytesEq
    rw [Bool.and_eq_false_iff]; left
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 : dotBytes.size = 1 := rfl
    have h3 : NAME_MAX = 255 := rfl
    change p.data.size = dotBytes.size at h
    omega
  have hNotDotDot : bytesEq p dotDotBytes = false := by
    unfold bytesEq
    rw [Bool.and_eq_false_iff]; left
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 : dotDotBytes.size = 2 := rfl
    have h3 : NAME_MAX = 255 := rfl
    change p.data.size = dotDotBytes.size at h
    omega
  have hFuel : [p].length + (MAX_SYMLINKS + 1) * PATH_MAX + 32 =
      Nat.succ ([p].length + (MAX_SYMLINKS + 1) * PATH_MAX + 31) := rfl
  have hGt' : (p.size > NAME_MAX) = True := eq_true hName'
  cases isAbs <;> cases trailing <;> (
    simp only [hNul, Bool.false_eq_true, ↓reduceIte]
    split
    · next hErr => change Except.ok PUnit.unit = Except.error _ at hErr; cases hErr
    · simp only [hNonEmpty, Bool.false_eq_true, Bool.false_and, Bool.true_and, Bool.and_false,
        Bool.not_false, ↓reduceIte, resolveStartDir, inodeMountId, FilesState.initial, assocGet]
      rw [hFuel, walkPath.eq_5]
      simp only [assocGet, hasVNodePermIn, hasVNodePerm, hasOwnerPerm, ProcessCred.capableWrtInode,
        DirLifecycle.isDead, hNotDot, hNotDotDot, hGt', Bool.false_eq_true, ↓reduceIte,
        Bool.and_false, Bool.and_true, Bool.not_false, Bool.true_and, List.isEmpty]
      rfl)

private theorem resolveLookupOrExt_maxPath (s : FilesState) {p : ByteArray}
    (hNul : hasEmbeddedNul p = false) (hPath : p.data.size ≥ PATH_MAX) :
    resolveLookupOrExt s none p true {} = .error Errno.ENAMETOOLONG := by
  unfold resolveLookupOrExt
  rw [validatePathBytes_maxPath hNul hPath]
  simp only [hNul, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem evalModel_symlinkat_maxPath (s : FilesState) {p : ByteArray}
    (hNul : hasEmbeddedNul p = false) (hPath : p.data.size ≥ PATH_MAX) :
    evalModel s (.symlinkat p none (asciiBytes ['s'])) = (.err Errno.ENAMETOOLONG, s) := by
  unfold evalModel evalReq precheckNul
  have hNulS : hasEmbeddedNul (asciiBytes ['s']) = false := rfl
  simp only [hNul, hNulS, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [show (if (decide (p.size > 0) && decide (p.size < PATH_MAX) && _) = true
      then StepResult.nondet NondetAction.externalStdioUnit
      else evalSymlink s p none (asciiBytes ['s'])) = evalSymlink s p none (asciiBytes ['s']) from by
    change (if (decide (p.size > 0) && decide (p.size < PATH_MAX) && false) = true then _ else _) = _
    simp]
  unfold evalSymlink
  have hp : (p.size ≥ PATH_MAX) = True := eq_true hPath
  simp only [hp, ↓reduceIte]
  rfl

private def loopStep1Result : Except Errno Unit × FilesState :=
  (modelOps.symlinkat (asciiBytes ['l', '2']) none (asciiBytes ['l', '1'])).run FilesState.initial

private def loopStep2Result : Except Errno Unit × FilesState :=
  (modelOps.symlinkat (asciiBytes ['l', '1']) none (asciiBytes ['l', '2'])).run loopStep1Result.2

private def loopOpenResult : Except Errno HandleId × FilesState :=
  (modelOps.openat none (asciiBytes ['l', '1']) { access := .rdonly } 0).run loopStep2Result.2

private def loopStatResult : Except Errno StatInfo × FilesState :=
  (modelOps.fstatat none (asciiBytes ['l', '1']) { symlinkNofollow := false }).run loopStep2Result.2

private def loopLstatResult : Except Errno StatInfo × FilesState :=
  (modelOps.fstatat none (asciiBytes ['l', '1']) { symlinkNofollow := true }).run loopStep2Result.2

private theorem loopStep1_ok : loopStep1Result.1 = .ok () := rfl
private theorem loopStep2_ok : loopStep2Result.1 = .ok () := rfl
set_option maxRecDepth 4096 in
private theorem loopOpen_eloop : loopOpenResult = (.error Errno.ELOOP, loopStep2Result.2) := by
  apply Prod.ext
  · exact Eq.refl _
  · exact Eq.refl _
set_option maxRecDepth 4096 in
private theorem loopStat_eloop : loopStatResult.1 = .error Errno.ELOOP := Eq.refl _
set_option maxRecDepth 4096 in
private theorem loopLstat_sym : ∃ st, loopLstatResult.1 = .ok st ∧ st.kind = .symlink :=
  ⟨(StatInfo.ofRawTuple (2, 2, 0o777, 1, 1, 1, 0, 0, 0, 0)), Eq.refl _, rfl⟩

set_option maxRecDepth 4096 in
/-- Proof helper for `files_ops_symlinkLoopAndNameTooLong_allPass`. -/
theorem files_ops_symlinkLoopAndNameTooLong_proof :
    AllPass (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial) := by
  intro longSeg ⟨hNul1, hLt, hGt, hSplit⟩ maxPath ⟨hNul2, hGe⟩
  dsimp only [Bind.bind, assert, pure, StateT.run, StateT.bind, StateT.get,
    StateT.pure, get, getThe, MonadState.get, MonadStateOf.get, runOp, set, MonadStateOf.set]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · refine ⟨?_, ?_⟩
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      unfold evalModel evalReq precheckNul evalOpen
      simp only [hNul1, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.and_false,
        Bool.not_false, Bool.and_true]
      have hr : (resolveOpenTargetWalk FilesState.initial none longSeg true false {} false).1 =
          .error Errno.ENAMETOOLONG := resolveOpenTarget_longSeg hNul1 hLt hGt hSplit
      rw [hr]
      rfl
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      unfold evalModel evalReq precheckNul evalOpen
      simp only [hNul1, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.and_false,
        Bool.not_false, Bool.and_true]
      have hr : (resolveOpenTargetWalk FilesState.initial none longSeg true false {} false).1 =
          .error Errno.ENAMETOOLONG := resolveOpenTarget_longSeg hNul1 hLt hGt hSplit
      rw [hr]
      rfl
  · refine ⟨?_, ?_⟩
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      unfold evalModel evalReq precheckNul evalStat
      simp only [hNul2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.not_false]
      rw [resolveLookupOrExt_maxPath FilesState.initial hNul2 hGe]
      rfl
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      unfold evalModel evalReq precheckNul evalStat
      simp only [hNul2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.not_false]
      rw [resolveLookupOrExt_maxPath FilesState.initial hNul2 hGe]
      rfl
  · refine ⟨?_, ?_⟩
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      rw [evalModel_symlinkat_maxPath FilesState.initial hNul2 hGe]
      rfl
    · dsimp only [modelOps, StateT.bind, StateT.get, StateT.pure, get, getThe,
        MonadState.get, MonadStateOf.get, Bind.bind, pure, runOp, set, MonadStateOf.set]
      rw [evalModel_symlinkat_maxPath FilesState.initial hNul2 hGe]
      rfl
  · exact ⟨loopStep1_ok, loopStep2_ok⟩
  · exact ⟨congrArg Prod.fst loopOpen_eloop, congrArg Prod.snd loopOpen_eloop⟩
  · exact loopStat_eloop
  · exact loopLstat_sym

private theorem splitPathBytesLoop_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    ∀ k i, i + k = path.size →
      splitPathBytesLoop path i 0 [] k = [path]
  | 0, i, hk => by
    have hEq : i = path.size := by omega
    subst hEq
    unfold splitPathBytesLoop
    simp [hPos]
  | k + 1, i, hk => by
    have hi : i < path.size := by omega
    unfold splitPathBytesLoop
    simp only [hi, ↓reduceDIte]
    have hNe : (path[i] == slashByte) = false := by
      have h1 := hNo i hi
      simpa [bne] using h1
    rw [hNe]
    exact splitPathBytesLoop_noSlash path hPos hNo k (i + 1) (by omega)

/-- Any non-empty path without `'/'` splits to `[path]`. -/
theorem splitPathBytes_of_noSlash (path : ByteArray) (hPos : 0 < path.size)
    (hNo : ∀ j, (hj : j < path.size) → path[j] != slashByte) :
    splitPathBytes path = (false, [path], false) := by
  unfold splitPathBytes
  have h0 : (path[0] == slashByte) = false := by
    have := hNo 0 hPos
    simpa [bne] using this
  have hLast : (path[path.size - 1] == slashByte) = false := by
    have := hNo (path.size - 1) (Nat.sub_lt hPos Nat.zero_lt_one)
    simpa [bne] using this
  simp only [hPos, ↓reduceDIte, h0, hLast]
  exact congrArg (fun x => (false, x, false))
    (splitPathBytesLoop_noSlash path hPos hNo path.size 0 (Nat.zero_add _))

private def mkRepPath (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (97 : UInt8)).toArray

private theorem hasEmbeddedNul_replicate_97 :
    ∀ n, (List.replicate n (97 : UInt8)).any (· == (0 : UInt8)) = false
  | 0 => rfl
  | n + 1 => hasEmbeddedNul_replicate_97 n

private theorem witness_longSeg_gen (n : Nat) (h1 : n > 0) (h2 : n < PATH_MAX) (h3 : n > NAME_MAX) :
    hasEmbeddedNul (mkRepPath n) = false ∧ (mkRepPath n).data.size < PATH_MAX ∧
    (mkRepPath n).data.size > NAME_MAX ∧ (splitPathBytes (mkRepPath n)).2.1 = [mkRepPath n] := by
  have hNul : hasEmbeddedNul (mkRepPath n) = false := by
    rw [hasEmbeddedNul_eq_toList_any]
    unfold mkRepPath
    rw [List.toList_toArray]
    exact hasEmbeddedNul_replicate_97 n
  have hSz : (mkRepPath n).data.size = n := by
    unfold mkRepPath
    rw [List.size_toArray, List.length_replicate]
  have hSplit : (splitPathBytes (mkRepPath n)).2.1 = [mkRepPath n] := by
    have hPos : 0 < (mkRepPath n).size := by
      show 0 < (mkRepPath n).data.size
      omega
    have hNo : ∀ j, (hj : j < (mkRepPath n).size) → (mkRepPath n)[j] != slashByte := by
      intro j hj
      have hElem : (mkRepPath n)[j] = (97 : UInt8) := by
        show (mkRepPath n).data[j] = (97 : UInt8)
        unfold mkRepPath
        exact List.getElem_replicate ..
      rw [hElem]
      decide
    rw [splitPathBytes_of_noSlash (mkRepPath n) hPos hNo]
  rw [hSz]
  exact ⟨hNul, h2, h3, hSplit⟩

private theorem witness_maxPath_gen (n : Nat) (h : n ≥ PATH_MAX) :
    hasEmbeddedNul (mkRepPath n) = false ∧ (mkRepPath n).data.size ≥ PATH_MAX := by
  refine ⟨?_, ?_⟩
  · rw [hasEmbeddedNul_eq_toList_any]
    unfold mkRepPath
    rw [List.toList_toArray]
    exact hasEmbeddedNul_replicate_97 n
  · unfold mkRepPath
    rw [List.size_toArray, List.length_replicate]
    exact h

private theorem test_symlinkLoop_of_witness
    (hAll : AllPass (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial))
    {p1 p2 : ByteArray}
    (hp1 : hasEmbeddedNul p1 = false ∧ p1.data.size < PATH_MAX ∧ p1.data.size > NAME_MAX ∧ (splitPathBytes p1).2.1 = [p1])
    (hp2 : hasEmbeddedNul p2 = false ∧ p2.data.size ≥ PATH_MAX) :
    CanReach (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial) :=
  ⟨p1, hp1, p2, hp2, hAll p1 hp1 p2 hp2⟩

/-- Proof helper for `files_ops_symlinkLoopAndNameTooLong_canReach`. -/
theorem files_ops_symlinkLoopAndNameTooLong_canReach_proof :
    CanReach (test_files_ops_symlinkLoopAndNameTooLong modelOps FilesState.initial) :=
  test_symlinkLoop_of_witness
    files_ops_symlinkLoopAndNameTooLong_proof
    (witness_longSeg_gen 256 (by decide) (by decide) (by decide))
    (witness_maxPath_gen 4096 (by decide))

set_option maxRecDepth 4096 in
/-- Proof helper for `files_model_envGeneralizationInvariants_allPass`. -/
theorem files_model_envGeneralizationInvariants_proof :
    AllPass (test_files_model_envGeneralizationInvariants allowedStep) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Proof helper for `files_ops_lseekReopenDupStdioAndOpath_allPass`. -/
def lroState : FilesState :=
  { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2)] }, mode := 0o755, nlink := 3 }),
               (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
               (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
               (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 })],
    fds := [], cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 5, nextHid := 0 }

private def lroRegBytes : ByteArray := ByteArray.mk #[114, 101, 103]
private def lroReg2Bytes : ByteArray := ByteArray.mk #[114, 101, 103, 50]
private def lroD400Bytes : ByteArray := ByteArray.mk #[100, 52, 48, 48]
private def lroPayBytes : ByteArray := ByteArray.mk #[97, 98, 99, 100, 101]

private def b2a_s7 := (modelOps.openat none lroRegBytes { access := .rdwr, creat := true, excl := true } 0o644).run lroState
private def b2a_s8 := (modelOps.write 0 lroPayBytes).run b2a_s7.2
private def b2a_s9 := (modelOps.lseek 0 (-1) .seekSet).run b2a_s8.2
private def b2a_s10 := (modelOps.lseek 0 2 .seekSet).run b2a_s9.2

private theorem b2a_s8_fst : b2a_s8.1 = .ok 5 := rfl
private theorem b2a_s9_fst : b2a_s9.1 = .error Errno.EINVAL := rfl
private theorem b2a_s10_fst : b2a_s10.1 = .ok 2 := rfl

private theorem b2a_s10_eq :
    b2a_s10.2 = { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2), (lroRegBytes, 5)] }, mode := 0o755, nlink := 3 }),
                             (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                             (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                             (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 }),
                             (5, { data := .reg (RegData.ofBytes lroPayBytes), mode := 0o644, modeExact := true, nlink := 1 })],
                  fds := [(0, { ino := 5, access := .rdwr, pos := .byteOffset 2,
                                dentry? := some (1, lroRegBytes), lastDentry? := some (1, lroRegBytes) })],
                  cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 6, nextHid := 1 } := rfl

private def rr_s1 := (modelOps.openat none lroReg2Bytes { access := .rdwr, creat := true, excl := true } 0o644).run lroState
private def rr_s2 := (modelOps.write 0 lroPayBytes).run rr_s1.2
private def rr_s3 := (modelOps.unlinkat none lroReg2Bytes false).run rr_s2.2

private theorem rr_s2_fst : rr_s2.1 = .ok 5 := rfl
private theorem rr_s3_fst : rr_s3.1 = .ok () := rfl

private theorem rr_s3_eq :
    rr_s3.2 = { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2)] }, mode := 0o755, nlink := 3 }),
                           (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                           (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                           (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 }),
                           (5, { data := .reg (RegData.ofBytes lroPayBytes), mode := 0o644, modeExact := true, nlink := 0 })],
                fds := [(0, { ino := 5, access := .rdwr, pos := .byteOffset 5,
                              dentry? := none, lastDentry? := some (1, lroReg2Bytes) })],
                cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 6, nextHid := 1 } := rfl

private def d19 := (modelOps.mkdirat none lroD400Bytes 0o400).run lroState
private def d20 := (modelOps.openat none lroD400Bytes { access := .rdonly, directory := true } 0).run d19.2
private def d21 := (modelOps.getdents64 0 4096).run d20.2
private def d22 := (modelOps.getdents64 0 4096).run d21.2
private def d23 := (modelOps.lseek 0 0 .seekSet).run d22.2

private theorem d20_eq :
    d20.2 = { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2), (lroD400Bytes, 5)] }, mode := 0o755, nlink := 4 }),
                         (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                         (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                         (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 }),
                         (5, { data := .dir { parentIno := 1, children := [] }, mode := 0o400, modeExact := true, nlink := 2 })],
              fds := [(0, { ino := 5, access := .rdonly, pos := .dirStream 0 false,
                            dentry? := some (1, lroD400Bytes), lastDentry? := some (1, lroD400Bytes) })],
              cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 6, nextHid := 1 } := rfl

private theorem d23_eq : d23.2 = d20.2 := by
  dsimp only [d23, d22, d21]
  rw [d20_eq]
  rfl

private theorem b2a_read_ok :
    ((modelOps.read 0 4).run b2a_s10.2).1 = .ok (ByteArray.mk #[99, 100, 101]) := by
  rw [b2a_s10_eq]; rfl

private theorem b2a_end_ok :
    ((modelOps.lseek 0 (-1) .seekEnd).run ((modelOps.read 0 4).run b2a_s10.2).2).1 = .ok 4 := by
  rw [b2a_s10_eq]; rfl

private theorem b2a_cur_ok :
    ((modelOps.lseek 0 (-2) .seekCur).run ((modelOps.lseek 0 (-1) .seekEnd).run ((modelOps.read 0 4).run b2a_s10.2).2).2).1 = .ok 2 := by
  rw [b2a_s10_eq]; rfl

private theorem rr_s4_eq :
    ((modelOps.reopenReadOnly 0).run rr_s3.2).2 =
      { inodes := [(1, { data := .dir { parentIno := 1, children := [("proc".toUTF8, 2)] }, mode := 0o755, nlink := 3 }),
                   (2, { data := .dir { parentIno := 1, children := [("self".toUTF8, 3)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (3, { data := .dir { parentIno := 2, children := [("fd".toUTF8, 4)] }, mode := 0o755, origin := .pseudoFs, nlink := 3 }),
                   (4, { data := .dir { parentIno := 3, children := [] }, mode := 0o755, origin := .pseudoFs, nlink := 2 }),
                   (5, { data := .reg (RegData.ofBytes lroPayBytes), mode := 0o644, modeExact := true, nlink := 0 })],
        fds := [(0, { ino := 5, access := .rdwr, pos := .byteOffset 5,
                      dentry? := none, lastDentry? := some (1, lroReg2Bytes) }),
                (1, { ino := 5, access := .rdonly, nonblock := true, cloexec := true, pos := .byteOffset 0,
                      dentry? := none, lastDentry? := some (1, lroReg2Bytes) })],
        cwdPath := .bound "/".toUTF8, rootIno := 1, cwdIno := 1, nextIno := 6, nextHid := 2 } := by
  rw [rr_s3_eq]; rfl

private theorem rr_read_ok :
    ((modelOps.read 1 8).run ((modelOps.reopenReadOnly 0).run rr_s3.2).2).1 = .ok lroPayBytes := by
  rw [rr_s4_eq]; rfl

private theorem d19_fst : d19.1 = .ok () := rfl
private theorem d21_fst : ∃ bs, d21.1 = .ok bs ∧ bs.data.size ≥ 24 := by
  dsimp only [d21]; rw [d20_eq]; exact ⟨_, rfl, by decide⟩
private theorem d22_fst : d22.1 = .ok (ByteArray.mk #[]) := by
  dsimp only [d22, d21]; rw [d20_eq]; rfl
private theorem d23_fst : d23.1 = .ok 0 := by
  dsimp only [d23, d22, d21]; rw [d20_eq]; rfl
private theorem d24_fst : ∃ bs, ((modelOps.getdents64 0 4096).run d23.2).1 = .ok bs ∧ bs.data.size ≥ 24 := by
  rw [d23_eq, d20_eq]; exact ⟨_, rfl, by decide⟩

set_option maxHeartbeats 800000 in
/-- Proof helper for `files_ops_lseekReopenDupStdioAndOpath_allPass`. -/
theorem files_ops_lseekReopenDupStdioAndOpath_proof :
    AllPass (test_files_ops_lseekReopenDupStdioAndOpath modelOps lroState) := by
  refine ⟨⟨_, rfl⟩, rfl, rfl, rfl, ⟨_, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩,
    b2a_s8_fst, b2a_s9_fst, b2a_s10_fst, b2a_read_ok, b2a_end_ok, b2a_cur_ok,
    rr_s2_fst, rr_s3_fst, rr_read_ok,
    d19_fst, d21_fst, d22_fst, d23_fst, d24_fst,
    rfl, rfl, rfl, trivial⟩

set_option maxRecDepth 4096 in
/-- Proof helper for `files_model_hardenedInvariants_allPass`. -/
theorem files_model_hardenedInvariants_proof :
    AllPass (test_files_model_hardenedInvariants allowedStep) := by
  repeat' (first | exact trivial | refine ⟨rfl, ?_⟩)

end LeanSwe.LinuxSyscall.Files

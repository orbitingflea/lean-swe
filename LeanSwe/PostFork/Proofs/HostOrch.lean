import Core.Assumptions
import LeanSwe.PostFork.Interface
import LeanSwe.PostFork.Impl
import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.Proofs.PureAndWire
import LeanSwe.PostFork.Proofs.HostOrchBase

/-!
Kernel proofs for `test_postfork_hostOps_validationBarrierEintrAndWire` (`Core.AllPass` + `Core.CanReach`)
and the `4` `Core.NeverErrorKindIO` impossibility theorems for `LeanSwe.PostFork`.
-/

namespace LeanSwe.PostFork.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Impl.Internal
open LeanSwe.PostFork.Impl

section HostOrchestrator

private theorem step_do_jp2 (c : Bool) (P1 P2 : Prop) (k : PUnit → Core.AllPassRun Unit) :
    (c = true → P1 ∧ P2) →
    k PUnit.unit (fun _ => True) →
    (if c = true then
      Core.NondetTest.assert P1 >>= fun _ => Core.NondetTest.assert P2 >>= k
    else
      Pure.pure () >>= k) (fun _ => True) := by
  intro ht hk
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    exact ⟨(ht hc).1, (ht hc).2, hk⟩
  · have hcf : c = false := Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
    exact hk

private theorem array_all_empty {α : Type} (p : α → Bool) :
    (#[] : Array α).all p = true := by
  rw [Array.all_eq_true]
  intro _ hi
  simp at hi

private theorem array_any_empty {α : Type} (p : α → Bool) :
    (#[] : Array α).any p = false := by
  rw [Bool.eq_false_iff, ne_eq, Array.any_eq_true]
  rintro ⟨_, hi, _⟩
  simp at hi

private theorem disjointFdRefArrays_empty {fd : Type} (eqFd : fd → fd → Bool)
    (keepFds : Array (FdRef fd)) (checkHandles : Bool := true) :
    disjointFdRefArrays eqFd #[] keepFds checkHandles = true := by
  unfold disjointFdRefArrays
  cases checkHandles <;> simp

private theorem spawn_invalid (spec : ChildSpecM Int32) (h : (!validateSpec spec) = true) :
    ((Impl.Internal.mkHostOps mockPosixHostOps).spawn spec).run {} =
      (.error (Impl.Internal.mkInvalidErr "invalid ChildSpecM"), {}) := by
  dsimp only [Impl.Internal.mkHostOps]
  simp only [validateSpecImpl_eq, h, ↓reduceIte]
  rfl

private theorem spawnWithBarrier_invalid (spec : ChildSpecM Int32) (h : (!validateSpec spec) = true) :
    ((Impl.Internal.mkHostOps mockPosixHostOps).spawnWithBarrier spec).run {} =
      (.error (Impl.Internal.mkInvalidErr "invalid ChildSpecM"), {}) := by
  dsimp only [Impl.Internal.mkHostOps]
  simp only [validateSpecImpl_eq, h, ↓reduceIte]
  rfl

private theorem spawn_largeArgs (extraArgCount : Nat) (fMode : ForkMode) (waitSt : ChildWaitStatus) :
    let largeArgs : Array (ArgToken Int32) :=
      #[ArgToken.lit "/bin/echo"] ++ (List.replicate extraArgCount (ArgToken.lit "a")).toArray
    ∃ stLarge : HostMockState,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawn
        { path := "/bin/echo", argv := largeArgs, forkMode := fMode }).run { waitResult := waitSt } =
        (.ok { pid := 4242, pgid := none }, stLarge) ∧
      stLarge.spawnedArgv.size = extraArgCount + 1 ∧
      stLarge.spawnedForkMode = fMode := by
  intro largeArgs
  let specLarge : ChildSpecM Int32 := { path := "/bin/echo", argv := largeArgs, forkMode := fMode }
  have hVal : validateSpec specLarge = true := by
    simp only [specLarge, validateSpec, validateSpecWith, disjointFdRefArrays_empty, largeArgs_valid extraArgCount,
      hasEmbeddedNulStr_echo, largeArgs, FdPolicy.keepFds, array_all_empty]
    decide
  dsimp only [specLarge] at hVal
  dsimp only [Impl.Internal.mkHostOps]
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeStdioPlan mockPosixHostOps .inherit).run { waitResult := waitSt } = (.ok (), _))]
  dsimp only
  rw [keepFdsImpl_eq, stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeRefList mockPosixHostOps (FdPolicy.keepFds .inheritNonCloexec).toList).run { waitResult := waitSt } = (.ok (), _))]
  dsimp only
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.filterOpenCloseList mockPosixHostOps (#[] : Array (FdRef Int32)).toList #[]).run { waitResult := waitSt } = (#[], _))]
  let s1 : HostMockState := { waitResult := waitSt, callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  have hPipe : (mockPosixHostOps.mkPipeCloexec).run { waitResult := waitSt } = (.ok (10, 11), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe]
  rw [stateT_bind_pure_val]
  dsimp only
  let s2 : HostMockState :=
    { s1 with
      callCount := 2
      hasSpawned := true
      spawnedFlags := flagsOfSpec specLarge false
      spawnedForkMode := fMode
      spawnedArgv := largeArgs.map renderMockArgToken
      spawnedEnv := formatEnvEntriesBytes specLarge.rawEnv specLarge.env
      spawnedCloseRefs := #[FdRef.handle 10] }
  have hFork : (Impl.Internal.performFork mockPosixHostOps specLarge none 11 #[] #[FdRef.handle 10] false).run s1 =
      (.ok 4242, s2) := rfl
  dsimp only [specLarge] at hFork
  rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
  dsimp only
  let s3 : HostMockState :=
    { s2 with
      callCount := 3
      closedHandles := [11]
      closedFds := [11] }
  have hCloseW : (mockPosixHostOps.closeFd 11).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseW]
  unfold Impl.Internal.awaitExecOrFailure
  have hRead := readAllRetry_empty 10 0 (by decide) s3 rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRead]
  dsimp only
  let s4 := { s3 with callCount := s3.callCount + 0 + 1, readEintrCount := 0 }
  have hCloseR : (mockPosixHostOps.closeFd 10).run s4 =
      (.ok (), { s4 with callCount := s4.callCount + 1, closedHandles := 10 :: s4.closedHandles, closedFds := 10 :: s4.closedFds }) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseR]
  have hDec : decodeChildFailure ByteArray.empty = none := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  refine ⟨_, rfl, ?_, rfl⟩
  dsimp only [s4, s3, s2, largeArgs]
  simp [Nat.add_comm]

private theorem spawn_tokFd (tokFd : Int32) :
    ∃ stTok : HostMockState,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawn
        { path := "/bin/echo"
          argv := #[ArgToken.ofLiteral "/bin/echo", ArgToken.ofHandle tokFd,
            ArgToken.procSelfFd tokFd, ArgToken.prefixedFd "--fd=" (.raw 5) "x"]
          env := #[("K", "V")]
          rawEnv := #[ByteArray.mk #[0x4B, 0x3D, 0x78], ByteArray.mk #[0x52, 0x3D, 0x80, 0xFF]]
          processGroup := .newGroup
          forkMode := .immortalThread }).run {} =
        (.ok { pid := 4242, pgid := some 4242 }, stTok) ∧
      stTok.setpgidCalls = [(4242, 4242)] ∧
      stTok.spawnedArgv = #["/bin/echo", s!"{tokFd}", s!"/proc/self/fd/{tokFd}", "--fd=5x"] ∧
      stTok.spawnedEnv = #[ByteArray.mk #[0x52, 0x3D, 0x80, 0xFF, 0], ("K=V".toUTF8.push 0)] ∧
      stTok.spawnedForkMode = .immortalThread ∧
      stTok.spawnedFlags = flagsOfSpec ({ path := "/bin/echo", argv := #[], processGroup := .newGroup } : ChildSpecM Int32) false := by
  let specTok : ChildSpecM Int32 :=
    { path := "/bin/echo"
      argv := #[ArgToken.ofLiteral "/bin/echo", ArgToken.ofHandle tokFd,
        ArgToken.procSelfFd tokFd, ArgToken.prefixedFd "--fd=" (.raw 5) "x"]
      env := #[("K", "V")]
      rawEnv := #[ByteArray.mk #[0x4B, 0x3D, 0x78], ByteArray.mk #[0x52, 0x3D, 0x80, 0xFF]]
      processGroup := .newGroup
      forkMode := .immortalThread }
  have hArgv :
      (#[ArgToken.ofLiteral "/bin/echo", ArgToken.ofHandle tokFd,
          ArgToken.procSelfFd tokFd, ArgToken.prefixedFd "--fd=" (.raw 5) "x"] :
        Array (ArgToken Int32)).all (ArgToken.isValid (fd := Int32)) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi4 : i < 4 := hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      simp [ArgToken.ofLiteral, ArgToken.ofHandle, ArgToken.procSelfFd, ArgToken.isValid,
        FdRef.isNonneg, hasEmbeddedNulStr_echo, hasEmbeddedNulStr_procSelfFd, hasEmbeddedNulStr_empty,
        hasEmbeddedNulStr_fdPrefix, hasEmbeddedNulStr_x]
  have hEnv : (#[("K", "V")] : Array (String × String)).all isValidEnvBinding = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi0 : i = 0 := by have : i < 1 := hi; omega
    subst hi0
    simp [isValidEnvBinding, hasEmbeddedNulStr_K, hasEmbeddedNulStr_V]
  have hRawEnv :
      (#[ByteArray.mk #[0x4B, 0x3D, 0x78], ByteArray.mk #[0x52, 0x3D, 0x80, 0xFF]] : Array ByteArray).all
        isValidRawEnvEntry = true := by
    decide +kernel
  have hVal : validateSpec specTok = true := by
    simp only [specTok, validateSpec, validateSpecWith, disjointFdRefArrays_empty, FdPolicy.keepFds,
      hasEmbeddedNulStr_echo, hArgv, hEnv, hRawEnv, array_all_empty]
    decide
  dsimp only [specTok] at hVal
  dsimp only [Impl.Internal.mkHostOps]
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeStdioPlan mockPosixHostOps .inherit).run {} = (.ok (), {}))]
  dsimp only
  rw [keepFdsImpl_eq, stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeRefList mockPosixHostOps (FdPolicy.keepFds .inheritNonCloexec).toList).run {} = (.ok (), {}))]
  dsimp only
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.filterOpenCloseList mockPosixHostOps (#[] : Array (FdRef Int32)).toList #[]).run {} = (#[], {}))]
  let s1 : HostMockState := { callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  have hPipe : (mockPosixHostOps.mkPipeCloexec).run {} = (.ok (10, 11), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe]
  rw [stateT_bind_pure_val]
  dsimp only
  let s2 : HostMockState :=
    { s1 with
      callCount := 3
      hasSpawned := true
      setpgidCalls := [(4242, 4242)]
      spawnedFlags := flagsOfSpec specTok false
      spawnedForkMode := .immortalThread
      spawnedArgv := specTok.argv.map renderMockArgToken
      spawnedEnv := formatEnvEntriesBytes specTok.rawEnv specTok.env
      spawnedCloseRefs := #[FdRef.handle 10] }
  have hFork : (Impl.Internal.performFork mockPosixHostOps specTok none 11 #[] #[FdRef.handle 10] false).run s1 =
      (.ok 4242, s2) := rfl
  dsimp only [specTok] at hFork
  rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
  dsimp only
  let s3 : HostMockState := { s2 with callCount := 4, closedHandles := [11], closedFds := [11] }
  have hCloseW : (mockPosixHostOps.closeFd 11).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseW]
  unfold Impl.Internal.awaitExecOrFailure
  have hRead := readAllRetry_empty 10 0 (by decide) s3 rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRead]
  dsimp only
  let s4 := { s3 with callCount := s3.callCount + 0 + 1, readEintrCount := 0 }
  have hCloseR : (mockPosixHostOps.closeFd 10).run s4 =
      (.ok (), { s4 with callCount := s4.callCount + 1, closedHandles := 10 :: s4.closedHandles, closedFds := 10 :: s4.closedFds }) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseR]
  have hDec : decodeChildFailure ByteArray.empty = none := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · dsimp only [s4, s3, s2, specTok]
    apply Array.ext_iff.mpr
    refine ⟨by simp, fun i hi1 _ => ?_⟩
    simp only [Array.size_map] at hi1
    have hi4 : i < 4 := hi1
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      · simp [renderMockArgToken, ArgToken.ofLiteral, ArgToken.ofHandle, ArgToken.procSelfFd]
        try decide
  · dsimp only [s4, s3, s2, specTok]
    decide +kernel

private theorem spawn_closedStdio99 :
    ∃ e st,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawn
        { path := "/bin/true", argv := #[], stdio := .redirect (.raw 99) (.raw 1) (.raw 2) true }).run
        { closedCallerFds := [99] } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EBADF := by
  dsimp only [Impl.Internal.mkHostOps]
  have hVal : validateSpec ({ path := "/bin/true", argv := #[], stdio := .redirect (.raw 99) (.raw 1) (.raw 2) true } : ChildSpecM Int32) = true := by
    simp only [validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_true, FdPolicy.keepFds,
      array_all_empty, array_any_empty]
    decide
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem spawnWithBarrier_closedKeep99 :
    ∃ e st,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawnWithBarrier
        { path := "/bin/true", argv := #[], fdPolicy := .closeAllAbove2Except #[.handle 99] }).run
        { closedCallerFds := [99] } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EBADF := by
  dsimp only [Impl.Internal.mkHostOps]
  have hKeep : (#[FdRef.handle 99] : Array (FdRef Int32)).all FdRef.isNonneg = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi0 : i = 0 := by have : i < 1 := hi; omega
    subst hi0
    rfl
  have hVal : validateSpec ({ path := "/bin/true", argv := #[], fdPolicy := .closeAllAbove2Except #[.handle 99] } : ChildSpecM Int32) = true := by
    simp only [validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_true, FdPolicy.keepFds,
      hKeep, array_all_empty]
    decide
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl, rfl, rfl⟩

private def barMidState (waitSt : ChildWaitStatus) : HostMockState :=
  { callCount := 6
    nextFd := 14
    closedHandles := [12, 11]
    failSetpgidErrno := some Errno.EPERM
    writeEintrCount := 2
    readEintrCount := 2
    waitEintrCount := 2
    allocSyncWriteFd := 13
    allocRepReadFd := 10
    waitResult := waitSt
    closedBeforeFork := []
    closedFds := [12, 11]
    setpgidCalls := [(4242, 4242)]
    spawnedFlags := flagsOfSpec ({ path := "/bin/true", argv := #[], processGroup := .newGroup } : ChildSpecM Int32) true
    spawnedForkMode := .direct
    spawnedArgv := #[]
    spawnedEnv := #[]
    spawnedCloseRefs := #[FdRef.handle 10, FdRef.handle 13]
    hasSpawned := true }

private theorem spawnWithBarrier_ok (waitSt : ChildWaitStatus) :
    let stBar : HostMockState :=
      { writeEintrCount := 2
        readEintrCount := 2
        waitEintrCount := 2
        failSetpgidErrno := some Errno.EPERM
        waitResult := waitSt }
    ((Impl.Internal.mkHostOps mockPosixHostOps).spawnWithBarrier
      { path := "/bin/true", argv := #[], processGroup := .newGroup }).run stBar =
      (.ok { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }, barMidState waitSt) := by
  intro stBar
  dsimp only [Impl.Internal.mkHostOps]
  have hVal : validateSpec ({ path := "/bin/true", argv := #[], processGroup := .newGroup } : ChildSpecM Int32) = true := by
    simp only [validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_true, FdPolicy.keepFds,
      array_all_empty]
    decide
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hP1 : (Impl.Internal.probeStdioPlan mockPosixHostOps .inherit).run stBar = (.ok (), stBar) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
  dsimp only
  have hP2 : (Impl.Internal.probeRefList mockPosixHostOps (FdPolicy.keepFds .inheritNonCloexec).toList).run stBar = (.ok (), stBar) := rfl
  rw [keepFdsImpl_eq, stateT_bind_pure_pair _ _ _ _ _ hP2]
  dsimp only
  have hFC : (Impl.Internal.filterOpenCloseList mockPosixHostOps (#[] : Array (FdRef Int32)).toList #[]).run stBar = (#[], stBar) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
  let s1 := { stBar with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  have hPipe1 : (mockPosixHostOps.mkPipeCloexec).run stBar = (.ok (10, 11), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe1]
  rw [stateT_bind_pure_val]
  dsimp only
  let s2 := { s1 with callCount := 2, nextFd := 14, allocSyncWriteFd := 13 }
  have hPipe2 : (mockPosixHostOps.mkPipeCloexec).run s1 = (.ok (12, 13), s2) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe2]
  rw [stateT_bind_pure_val]
  dsimp only
  let specB : ChildSpecM Int32 := { path := "/bin/true", argv := #[], processGroup := .newGroup }
  let s3 :=
    { s2 with
      callCount := 4
      hasSpawned := true
      setpgidCalls := [(4242, 4242)]
      spawnedFlags := flagsOfSpec specB true
      spawnedForkMode := .direct
      spawnedArgv := specB.argv.map renderMockArgToken
      spawnedEnv := formatEnvEntriesBytes specB.rawEnv specB.env
      spawnedCloseRefs := #[FdRef.handle 10, FdRef.handle 13] }
  have hFork : (Impl.Internal.performFork mockPosixHostOps specB (some 12) 11 #[] #[FdRef.handle 10, FdRef.handle 13] true).run s2 =
      (.ok 4242, s3) := rfl
  dsimp only [specB] at hFork
  rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
  dsimp only
  let s4 := { s3 with callCount := 6, closedHandles := [12, 11], closedFds := [12, 11] }
  have hClose : (Impl.Internal.closeListQuiet mockPosixHostOps [11, 12]).run s3 = ((), s4) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hClose]
  have hArg0 : (#[] : Array (ArgToken Int32)).map renderMockArgToken = #[] := by simp
  have hFmt0 : formatEnvEntriesBytes (#[] : Array ByteArray) (#[] : Array (String × String)) = #[] := by
    simp [formatEnvEntriesBytes]
  dsimp only [s4, s3, s2, s1, stBar, specB, barMidState, pure, StateT.pure]
  rw [hArg0, hFmt0]
  rfl

private theorem releaseBarrier_ok (waitSt : ChildWaitStatus) :
    let pend : PendingChildM Int32 := { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }
    ∃ stRelOut : HostMockState,
      ((Impl.Internal.mkHostOps mockPosixHostOps).releaseBarrier pend).run (barMidState waitSt) =
        (.ok { pid := 4242, pgid := some 4242 }, stRelOut) ∧
      stRelOut.syncWritten = ByteArray.mk #[1] ∧
      stRelOut.closedHandles.contains pend.syncWrite = true ∧
      stRelOut.closedHandles.contains pend.errRead = true := by
  intro pend
  dsimp only [Impl.Internal.mkHostOps]
  let s0 := { barMidState waitSt with callCount := (barMidState waitSt).callCount + 1 }
  have hPr : (mockPosixHostOps.probeHandleOpen 10).run (barMidState waitSt) = (.ok (), s0) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
  dsimp only
  have hWr := writeAllRetry_sync1_eintr2 13 s0 rfl rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
  dsimp only
  let s1 := { s0 with callCount := s0.callCount + 3, writeEintrCount := 0, syncWritten := ByteArray.mk #[1] }
  let s2 := { s1 with callCount := s1.callCount + 1, closedHandles := 13 :: s1.closedHandles, closedFds := 13 :: s1.closedFds }
  have hCl13 : (mockPosixHostOps.closeFd 13).run s1 = (.ok (), s2) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
  unfold Impl.Internal.awaitExecOrFailure
  have hRd := readAllRetry_empty 10 2 (by decide) s2 rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s3 := { s2 with callCount := s2.callCount + 2 + 1, readEintrCount := 0 }
  let s4 := { s3 with callCount := s3.callCount + 1, closedHandles := 10 :: s3.closedHandles, closedFds := 10 :: s3.closedFds }
  have hCl10 : (mockPosixHostOps.closeFd 10).run s3 = (.ok (), s4) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
  have hDec : decodeChildFailure ByteArray.empty = none := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only [pure, StateT.pure]
  dsimp only [pend]
  exact ⟨s4, rfl, rfl, rfl, rfl⟩

private theorem releaseBarrier_epipe (waitSt : ChildWaitStatus) :
    let pend : PendingChildM Int32 := { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }
    let stEpipe : HostMockState :=
      { barMidState waitSt with
        failWriteErrno := some Errno.EPIPE
        repWire := encodeFailureReport .execve Errno.ENOENT
        waitResult := .exited 127 }
    ∃ e cf stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).releaseBarrier pend).run stEpipe = (.error e, stOut) ∧
      e.kind = .childFailed ∧
      e.errno = some Errno.ENOENT ∧
      e.childFailure = some cf ∧
      cf = { stage := .execve, errno := Errno.ENOENT, waitStatus := some (.exited 127) } := by
  intro pend stEpipe
  dsimp only [pend]
  dsimp only [Impl.Internal.mkHostOps]
  let s0 := { stEpipe with callCount := stEpipe.callCount + 1 }
  have hPr : (mockPosixHostOps.probeHandleOpen 10).run stEpipe = (.ok (), s0) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
  dsimp only
  have hWr := writeAllRetry_epipe 13 s0 rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
  dsimp only
  have hEp : ((Impl.Internal.mkSysErr Errno.EPIPE "host write failed").errno == some Errno.EPIPE) = true := by decide
  simp only [hEp, ↓reduceIte]
  let s1 := { s0 with callCount := s0.callCount + 1 }
  let s2 := { s1 with callCount := s1.callCount + 1, closedHandles := 13 :: s1.closedHandles, closedFds := 13 :: s1.closedFds }
  have hCl13 : (mockPosixHostOps.closeFd 13).run s1 = (.ok (), s2) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
  unfold Impl.Internal.awaitExecOrFailure
  have hWire : s2.repWire = ByteArray.mk #[0x50, 0x01, 7, 0, 2, 0, 0, 0] := rfl
  have hRd := readAllRetry_wire8 10 2 (Or.inr rfl) 0x50 0x01 7 0 2 0 0 0 s2 rfl rfl rfl rfl hWire
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s3 := { s2 with callCount := s2.callCount + 2 + 4, readEintrCount := 0, repWire := ByteArray.empty }
  let s4 := { s3 with callCount := s3.callCount + 1, closedHandles := 10 :: s3.closedHandles, closedFds := 10 :: s3.closedFds }
  have hCl10 : (mockPosixHostOps.closeFd 10).run s3 = (.ok (), s4) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
  have hDec : decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 2, 0, 0, 0]) =
      some { stage := .execve, errno := Errno.ENOENT } := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only
  have hWt := waitRetry_ok 4242 s4 rfl (by dsimp only [s4, s3, s2, s1, s0, stEpipe, barMidState]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩

private theorem releaseBarrier_epipe_empty (waitSt : ChildWaitStatus) :
    let pend : PendingChildM Int32 := { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }
    let stEpipeEmpty : HostMockState :=
      { barMidState waitSt with
        failWriteErrno := some Errno.EPIPE
        repWire := ByteArray.empty
        waitResult := waitSt }
    ∃ e cf stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).releaseBarrier pend).run stEpipeEmpty = (.error e, stOut) ∧
      e.kind = .childFailed ∧
      e.errno = some Errno.EIO ∧
      e.childFailure = some cf ∧
      cf = { stage := .wireTruncated, errno := Errno.EIO, waitStatus := some waitSt } ∧
      stOut.closedHandles.contains pend.syncWrite = true ∧
      stOut.closedHandles.contains pend.errRead = true := by
  intro pend stEpipeEmpty
  dsimp only [pend]
  dsimp only [Impl.Internal.mkHostOps]
  let s0 := { stEpipeEmpty with callCount := stEpipeEmpty.callCount + 1 }
  have hPr : (mockPosixHostOps.probeHandleOpen 10).run stEpipeEmpty = (.ok (), s0) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
  dsimp only
  have hWr := writeAllRetry_epipe 13 s0 rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
  dsimp only
  have hEp : ((Impl.Internal.mkSysErr Errno.EPIPE "host write failed").errno == some Errno.EPIPE) = true := by decide
  simp only [hEp, ↓reduceIte]
  let s1 := { s0 with callCount := s0.callCount + 1 }
  let s2 := { s1 with callCount := s1.callCount + 1, closedHandles := 13 :: s1.closedHandles, closedFds := 13 :: s1.closedFds }
  have hCl13 : (mockPosixHostOps.closeFd 13).run s1 = (.ok (), s2) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
  unfold Impl.Internal.awaitExecOrFailure
  have hRd := readAllRetry_empty 10 2 (by decide) s2 rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s3 := { s2 with callCount := s2.callCount + 2 + 1, readEintrCount := 0 }
  let s4 := { s3 with callCount := s3.callCount + 1, closedHandles := 10 :: s3.closedHandles, closedFds := 10 :: s3.closedFds }
  have hCl10 : (mockPosixHostOps.closeFd 10).run s3 = (.ok (), s4) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
  have hDec : decodeChildFailure ByteArray.empty = none := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  simp only [↓reduceIte]
  have hWt := waitRetry_ok 4242 s4 rfl (by dsimp only [s4, s3, s2, s1, s0, stEpipeEmpty, barMidState]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem abortBarrier_clean (waitSt : ChildWaitStatus) :
    let pend : PendingChildM Int32 := { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }
    ∃ stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).abortBarrier pend).run
        { barMidState waitSt with repWire := ByteArray.empty, waitResult := .exited 125 } =
        (.ok (.aborted (.exited 125)), stOut) := by
  intro pend
  dsimp only [pend]
  dsimp only [Impl.Internal.mkHostOps]
  let st0 := { barMidState waitSt with repWire := ByteArray.empty, waitResult := .exited 125 }
  let s1 := { st0 with callCount := st0.callCount + 1, closedHandles := 13 :: st0.closedHandles, closedFds := 13 :: st0.closedFds }
  have hCl13 : (mockPosixHostOps.closeFd 13).run st0 = (.ok (), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
  dsimp only
  have hRd := readAllRetry_empty 10 2 (by decide) s1 rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s2 := { s1 with callCount := s1.callCount + 2 + 1, readEintrCount := 0 }
  let s3 := { s2 with callCount := s2.callCount + 1, closedHandles := 10 :: s2.closedHandles, closedFds := 10 :: s2.closedFds }
  have hCl10 : (mockPosixHostOps.closeFd 10).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
  have hWt := waitRetry_ok 4242 s3 rfl (by dsimp only [s3, s2, s1, st0, barMidState]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  exact ⟨_, rfl⟩

private theorem abortBarrier_failed (waitSt : ChildWaitStatus) :
    let pend : PendingChildM Int32 := { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 }
    ∃ stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).abortBarrier pend).run
        { barMidState waitSt with
          repWire := encodeFailureReport .fdSetup Errno.EBADF
          waitResult := .exited 127 } =
        (.ok (.failedBeforeBarrier
          { stage := .fdSetup, errno := Errno.EBADF, waitStatus := some (.exited 127) } (.exited 127)), stOut) := by
  intro pend
  dsimp only [pend]
  dsimp only [Impl.Internal.mkHostOps]
  let st0 := { barMidState waitSt with repWire := encodeFailureReport .fdSetup Errno.EBADF, waitResult := .exited 127 }
  let s1 := { st0 with callCount := st0.callCount + 1, closedHandles := 13 :: st0.closedHandles, closedFds := 13 :: st0.closedFds }
  have hCl13 : (mockPosixHostOps.closeFd 13).run st0 = (.ok (), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
  dsimp only
  have hWire : s1.repWire = ByteArray.mk #[0x50, 0x01, 4, 0, 9, 0, 0, 0] := rfl
  have hRd := readAllRetry_wire8 10 2 (Or.inr rfl) 0x50 0x01 4 0 9 0 0 0 s1 rfl rfl rfl rfl hWire
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s2 := { s1 with callCount := s1.callCount + 2 + 4, readEintrCount := 0, repWire := ByteArray.empty }
  let s3 := { s2 with callCount := s2.callCount + 1, closedHandles := 10 :: s2.closedHandles, closedFds := 10 :: s2.closedFds }
  have hCl10 : (mockPosixHostOps.closeFd 10).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
  have hWt := waitRetry_ok 4242 s3 rfl (by dsimp only [s3, s2, s1, st0, barMidState]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  have hDec : decodeChildFailure (ByteArray.mk #[0x50, 0x01, 4, 0, 9, 0, 0, 0]) =
      some { stage := .fdSetup, errno := Errno.EBADF } := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  exact ⟨_, rfl⟩

private theorem spawn_wireFail (stage : FailureStage) (errVal : UInt32)
    (hStage : stage ≠ .wireTruncated) (hLo : 1 ≤ errVal.toNat) (hHi : errVal.toNat ≤ 4095) :
    ∃ e stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawn { path := "/bin/false", argv := #[] }).run
        { readEintrCount := 1
          waitEintrCount := 1
          repWire := encodeFailureReport stage errVal
          waitResult := .exited 127 } = (.error e, stOut) ∧
      e.kind = .childFailed ∧
      e.errno = some errVal ∧
      e.childFailure = some { stage := stage, errno := errVal, waitStatus := some (.exited 127) } := by
  let specF : ChildSpecM Int32 := { path := "/bin/false", argv := #[] }
  let st0 : HostMockState :=
    { readEintrCount := 1
      waitEintrCount := 1
      repWire := encodeFailureReport stage errVal
      waitResult := .exited 127 }
  dsimp only [Impl.Internal.mkHostOps]
  have hVal : validateSpec specF = true := by
    simp only [specF, validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_false, FdPolicy.keepFds,
      array_all_empty]
    decide
  dsimp only [specF] at hVal
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeStdioPlan mockPosixHostOps .inherit).run st0 = (.ok (), st0))]
  dsimp only
  rw [keepFdsImpl_eq, stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeRefList mockPosixHostOps (FdPolicy.keepFds .inheritNonCloexec).toList).run st0 = (.ok (), st0))]
  dsimp only
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.filterOpenCloseList mockPosixHostOps (#[] : Array (FdRef Int32)).toList #[]).run st0 = (#[], st0))]
  let s1 := { st0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  have hPipe : (mockPosixHostOps.mkPipeCloexec).run st0 = (.ok (10, 11), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe]
  rw [stateT_bind_pure_val]
  dsimp only
  let s2 :=
    { s1 with
      callCount := 2
      hasSpawned := true
      spawnedFlags := flagsOfSpec specF false
      spawnedForkMode := .direct
      spawnedArgv := specF.argv.map renderMockArgToken
      spawnedEnv := formatEnvEntriesBytes specF.rawEnv specF.env
      spawnedCloseRefs := #[FdRef.handle 10] }
  have hFork : (Impl.Internal.performFork mockPosixHostOps specF none 11 #[] #[FdRef.handle 10] false).run s1 =
      (.ok 4242, s2) := rfl
  dsimp only [specF] at hFork
  rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
  dsimp only
  let s3 := { s2 with callCount := 3, closedHandles := [11], closedFds := [11] }
  have hCloseW : (mockPosixHostOps.closeFd 11).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseW]
  unfold Impl.Internal.awaitExecOrFailure
  let tag := (FailureStage.toTag? stage).getD STAGE_EXECVE
  let eNorm := normalizeWireErrno errVal
  let b4 := UInt8.ofNat (eNorm.toNat % 256)
  let b5 := UInt8.ofNat ((eNorm.toNat / 256) % 256)
  let b6 := UInt8.ofNat ((eNorm.toNat / 65536) % 256)
  let b7 := UInt8.ofNat ((eNorm.toNat / 16777216) % 256)
  have hWire : s3.repWire = ByteArray.mk #[WIRE_MAGIC, WIRE_VERSION, tag, 0, b4, b5, b6, b7] := rfl
  have hRd := readAllRetry_wire8 10 1 (Or.inl rfl) WIRE_MAGIC WIRE_VERSION tag 0 b4 b5 b6 b7 s3
    rfl rfl rfl rfl hWire
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s4 := { s3 with callCount := s3.callCount + 1 + 4, readEintrCount := 0, repWire := ByteArray.empty }
  let s5 := { s4 with callCount := s4.callCount + 1, closedHandles := 10 :: s4.closedHandles, closedFds := 10 :: s4.closedFds }
  have hCloseR : (mockPosixHostOps.closeFd 10).run s4 = (.ok (), s5) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseR]
  have hDec : decodeChildFailure (ByteArray.mk #[WIRE_MAGIC, WIRE_VERSION, tag, 0, b4, b5, b6, b7]) =
      some { stage := stage, errno := errVal } :=
    decodeChildFailure_encode_roundTrip stage errVal hStage hLo hHi
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only
  have hWt := waitRetry_ok 4242 s5 rfl (by dsimp only [s5, s4, s3, s2, s1, st0]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

private theorem spawn_wireTrunc :
    ∃ e stOut,
      ((Impl.Internal.mkHostOps mockPosixHostOps).spawn { path := "/bin/false", argv := #[] }).run
        { repWire := ByteArray.mk #[0x50, 0x01, 7, 0], waitResult := .exited 127 } = (.error e, stOut) ∧
      e.kind = .childFailed ∧
      e.errno = some Errno.EIO ∧
      e.childFailure = some { stage := .wireTruncated, errno := Errno.EIO, waitStatus := some (.exited 127) } := by
  let specF : ChildSpecM Int32 := { path := "/bin/false", argv := #[] }
  let st0 : HostMockState := { repWire := ByteArray.mk #[0x50, 0x01, 7, 0], waitResult := .exited 127 }
  dsimp only [Impl.Internal.mkHostOps]
  have hVal : validateSpec specF = true := by
    simp only [specF, validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_false, FdPolicy.keepFds,
      array_all_empty]
    decide
  dsimp only [specF] at hVal
  simp only [validateSpecImpl_eq, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeStdioPlan mockPosixHostOps .inherit).run st0 = (.ok (), st0))]
  dsimp only
  rw [keepFdsImpl_eq, stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.probeRefList mockPosixHostOps (FdPolicy.keepFds .inheritNonCloexec).toList).run st0 = (.ok (), st0))]
  dsimp only
  rw [stateT_bind_pure_pair _ _ _ _ _ (rfl : (Impl.Internal.filterOpenCloseList mockPosixHostOps (#[] : Array (FdRef Int32)).toList #[]).run st0 = (#[], st0))]
  let s1 := { st0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  have hPipe : (mockPosixHostOps.mkPipeCloexec).run st0 = (.ok (10, 11), s1) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hPipe]
  rw [stateT_bind_pure_val]
  dsimp only
  let s2 :=
    { s1 with
      callCount := 2
      hasSpawned := true
      spawnedFlags := flagsOfSpec specF false
      spawnedForkMode := .direct
      spawnedArgv := specF.argv.map renderMockArgToken
      spawnedEnv := formatEnvEntriesBytes specF.rawEnv specF.env
      spawnedCloseRefs := #[FdRef.handle 10] }
  have hFork : (Impl.Internal.performFork mockPosixHostOps specF none 11 #[] #[FdRef.handle 10] false).run s1 =
      (.ok 4242, s2) := rfl
  dsimp only [specF] at hFork
  rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
  dsimp only
  let s3 := { s2 with callCount := 3, closedHandles := [11], closedFds := [11] }
  have hCloseW : (mockPosixHostOps.closeFd 11).run s2 = (.ok (), s3) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseW]
  unfold Impl.Internal.awaitExecOrFailure
  have hRd := readAllRetry_wire4_e0 10 0x50 0x01 7 0 s3 rfl rfl rfl rfl rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
  dsimp only
  let s4 := { s3 with callCount := s3.callCount + 3, repWire := ByteArray.empty }
  let s5 := { s4 with callCount := s4.callCount + 1, closedHandles := 10 :: s4.closedHandles, closedFds := 10 :: s4.closedFds }
  have hCloseR : (mockPosixHostOps.closeFd 10).run s4 = (.ok (), s5) := rfl
  rw [stateT_bind_pure_pair _ _ _ _ _ hCloseR]
  have hDec : decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0]) =
      some { stage := .wireTruncated, errno := Errno.EIO } := rfl
  rw [decodeChildFailureImpl_eq, hDec]
  dsimp only
  have hWt := waitRetry_ok 4242 s5 rfl (by dsimp only [s5, s4, s3, s2, s1, st0]; omega)
  rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
  dsimp only [pure, StateT.pure]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- Kernel proof of `test_postfork_hostOps_validationBarrierEintrAndWire` on `Impl.Internal.mkHostOps`. -/
theorem test_postfork_hostOps_validationBarrierEintrAndWire_allPass :
    Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire Impl.Internal.mkHostOps) := by
  dsimp only [Core.AllPass, test_postfork_hostOps_validationBarrierEintrAndWire]
  intro spec stage errVal waitSt extraArgCount tokFd fMode
  dsimp (config := { zetaHave := true }) only
  refine step_do_jp2 (!validateSpec spec) _ _ _ ?_ ?_
  · intro hInv
    dsimp only [Impl.Internal.mkHostOps]
    simp only [validateSpecImpl_eq, hInv, ↓reduceIte, pure, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, ⟨⟨_, rfl, rfl⟩, trivial⟩⟩
  obtain ⟨stLarge, hLarge, hLargeSz, hLargeFm⟩ := spawn_largeArgs extraArgCount fMode waitSt
  rw [hLarge]
  dsimp only
  obtain ⟨stTok, hTok, hTokPgid, hTokArgv, hTokEnv, hTokFm, hTokFlags⟩ := spawn_tokFd tokFd
  rw [hTok]
  dsimp only
  obtain ⟨eCS, stCS, hCS, hCSKind, hCSErrno⟩ := spawn_closedStdio99
  rw [hCS]
  dsimp only
  obtain ⟨eCK, stCK, hCK, hCKKind, hCKErrno⟩ := spawnWithBarrier_closedKeep99
  rw [hCK]
  dsimp only
  rw [spawnWithBarrier_ok waitSt]
  dsimp only
  obtain ⟨stRelOut, hRelOk, hRelWr, hRelSw, hRelEr⟩ := releaseBarrier_ok waitSt
  rw [hRelOk]
  dsimp only
  obtain ⟨eEp, cfEp, stEp, hEp, hEpKind, hEpErrno, hEpCf, hEpCfEq⟩ := releaseBarrier_epipe waitSt
  rw [hEp]
  dsimp only
  obtain ⟨eEp0, cfEp0, stEp0, hEp0, hEp0Kind, hEp0Errno, hEp0Cf, hEp0CfEq, hEp0Sw, hEp0Er⟩ :=
    releaseBarrier_epipe_empty waitSt
  rw [hEp0]
  dsimp only
  obtain ⟨stAbClean, hAbClean⟩ := abortBarrier_clean waitSt
  rw [hAbClean]
  dsimp only
  obtain ⟨stAbFail, hAbFail⟩ := abortBarrier_failed waitSt
  rw [hAbFail]
  dsimp only
  obtain ⟨eTr, stTr, hTr, hTrKind, hTrErrno, hTrCf⟩ := spawn_wireTrunc
  rw [hTr]
  dsimp only
  refine ⟨⟨rfl, hLargeSz, hLargeFm⟩,
    ⟨rfl, hTokPgid, hTokArgv, hTokEnv, hTokFm, hTokFlags⟩,
    ⟨eCS, rfl, hCSKind, hCSErrno⟩,
    ⟨eCK, rfl, hCKKind, hCKErrno⟩,
    ⟨rfl, rfl⟩,
    ⟨rfl, hRelWr, hRelSw, hRelEr⟩,
    ⟨⟨eEp, cfEp, rfl, hEpKind, hEpErrno, hEpCf, hEpCfEq⟩,
      ⟨eEp0, cfEp0, rfl, hEp0Kind, hEp0Errno, hEp0Cf, hEp0CfEq, hEp0Sw, hEp0Er⟩⟩,
    rfl, rfl, ?_⟩
  rintro ⟨hStage, hLo, hHi⟩
  obtain ⟨eWf, stWf, hWf, hWfKind, hWfErrno, hWfCf⟩ := spawn_wireFail stage errVal hStage hLo hHi
  rw [hWf]
  exact ⟨⟨eWf, rfl, hWfKind, hWfErrno, hWfCf⟩, ⟨eTr, rfl, hTrKind, hTrErrno, hTrCf⟩, trivial⟩

/-- Witness reachability proof for `test_postfork_hostOps_validationBarrierEintrAndWire`. -/
theorem test_postfork_hostOps_validationBarrierEintrAndWire_canReach :
    Core.CanReach (test_postfork_hostOps_validationBarrierEintrAndWire Impl.Internal.mkHostOps) := by
  let spec0 : ChildSpecM Int32 := { path := "", argv := #[] }
  dsimp only [Core.CanReach, test_postfork_hostOps_validationBarrierEintrAndWire]
  have hInv : (!validateSpec spec0) = true := by
    simp [spec0, validateSpec, validateSpecWith, disjointFdRefArrays_empty, hasEmbeddedNulStr_empty]
  refine ⟨spec0, .execve, Errno.ENOENT, .exited 0, 1, (5 : Int32), .direct, ?_⟩
  dsimp (config := { zetaHave := true }) only
  dsimp only [Impl.Internal.mkHostOps]
  simp only [hInv, ↓reduceIte]
  obtain ⟨stLarge, hLarge, hLargeSz, hLargeFm⟩ := spawn_largeArgs 1 .direct (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hLarge
  rw [hLarge]
  dsimp only
  obtain ⟨stTok, hTok, hTokPgid, hTokArgv, hTokEnv, hTokFm, hTokFlags⟩ := spawn_tokFd (5 : Int32)
  dsimp only [Impl.Internal.mkHostOps] at hTok
  rw [hTok]
  dsimp only
  obtain ⟨eCS, stCS, hCS, hCSKind, hCSErrno⟩ := spawn_closedStdio99
  dsimp only [Impl.Internal.mkHostOps] at hCS
  rw [hCS]
  dsimp only
  obtain ⟨eCK, stCK, hCK, hCKKind, hCKErrno⟩ := spawnWithBarrier_closedKeep99
  dsimp only [Impl.Internal.mkHostOps] at hCK
  rw [hCK]
  dsimp only
  have hBar := spawnWithBarrier_ok (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hBar
  rw [hBar]
  dsimp only
  obtain ⟨stRelOut, hRelOk, hRelWr, hRelSw, hRelEr⟩ := releaseBarrier_ok (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hRelOk
  rw [hRelOk]
  dsimp only
  obtain ⟨eEp, cfEp, stEp, hEp, hEpKind, hEpErrno, hEpCf, hEpCfEq⟩ := releaseBarrier_epipe (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hEp
  rw [hEp]
  dsimp only
  obtain ⟨eEp0, cfEp0, stEp0, hEp0, hEp0Kind, hEp0Errno, hEp0Cf, hEp0CfEq, hEp0Sw, hEp0Er⟩ :=
    releaseBarrier_epipe_empty (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hEp0
  rw [hEp0]
  dsimp only
  obtain ⟨stAbClean, hAbClean⟩ := abortBarrier_clean (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hAbClean
  rw [hAbClean]
  dsimp only
  obtain ⟨stAbFail, hAbFail⟩ := abortBarrier_failed (.exited 0)
  dsimp only [Impl.Internal.mkHostOps] at hAbFail
  rw [hAbFail]
  dsimp only
  have hAss : FailureStage.execve ≠ .wireTruncated ∧ 1 ≤ Errno.ENOENT.toNat ∧ Errno.ENOENT.toNat ≤ 4095 :=
    ⟨by decide, by decide, by decide⟩
  obtain ⟨eWf, stWf, hWf, hWfKind, hWfErrno, hWfCf⟩ :=
    spawn_wireFail .execve Errno.ENOENT hAss.1 hAss.2.1 hAss.2.2
  dsimp only [Impl.Internal.mkHostOps] at hWf
  rw [hWf]
  dsimp only
  obtain ⟨eTr, stTr, hTr, hTrKind, hTrErrno, hTrCf⟩ := spawn_wireTrunc
  dsimp only [Impl.Internal.mkHostOps] at hTr
  rw [hTr]
  dsimp only
  exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩,
    ⟨rfl, hLargeSz, hLargeFm⟩,
    ⟨rfl, hTokPgid, hTokArgv, hTokEnv, hTokFm, hTokFlags⟩,
    ⟨eCS, rfl, hCSKind, hCSErrno⟩,
    ⟨eCK, rfl, hCKKind, hCKErrno⟩,
    ⟨rfl, rfl⟩,
    ⟨rfl, hRelWr, hRelSw, hRelEr⟩,
    ⟨⟨eEp, cfEp, rfl, hEpKind, hEpErrno, hEpCf, hEpCfEq⟩,
      ⟨eEp0, cfEp0, rfl, hEp0Kind, hEp0Errno, hEp0Cf, hEp0CfEq, hEp0Sw, hEp0Er⟩⟩,
    rfl, rfl, hAss,
    ⟨eWf, rfl, hWfKind, hWfErrno, hWfCf⟩,
    ⟨eTr, rfl, hTrKind, hTrErrno, hTrCf⟩, trivial⟩

end HostOrchestrator

section ErrorCoverageImpossible

private theorem neverErrorKindIO_of_ne {α : Type}
    (act : IO (Except PostForkError α)) (w : Void IO.RealWorld) (forbidden : PostForkErrorKind)
    (h : ∃ r w', act w = .ok r w' ∧ (∀ e, r = .error e → e.kind ≠ forbidden)) :
    Core.NeverErrorKindIO PostForkError.kind forbidden act w := by
  rcases h with ⟨r, w', hw, hs⟩
  unfold Core.NeverErrorKindIO
  rw [hw]
  cases r with
  | ok _ => trivial
  | error e => exact hs e rfl

/-- Proof that `LeanSwe.PostFork.spawnWithBarrier` never fails with `.childFailed`. -/
theorem spawnWithBarrier_never_childFailed (spec : ChildSpec) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO PostForkError.kind .childFailed (LeanSwe.PostFork.spawnWithBarrier spec) w := by
  rcases LeanSwe.PostFork.Proofs.defaultOps_exists_noThrow with ⟨raw, hDef, hRaw⟩
  apply neverErrorKindIO_of_ne _ w .childFailed
  unfold LeanSwe.PostFork.spawnWithBarrier
  rw [hDef]
  dsimp only [Impl.Internal.mkHostOps]
  by_cases hVal : (!validateSpec spec) = true
  · refine ⟨.error (Impl.Internal.mkInvalidErr "invalid ChildSpecM"), w, ?_, fun e he => by cases he; decide⟩
    simp [validateSpecImpl_eq, hVal, io_pure_eq]
  · have hValF : (!validateSpec spec) = false := Bool.eq_false_iff.mpr hVal
    simp only [validateSpecImpl_eq, hValF, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_eq]
    rcases probeStdioPlan_sysOnly raw hRaw spec.stdio w with ⟨r1, w1, hw1, hs1⟩
    rw [hw1]
    dsimp only
    cases r1 with
    | error err =>
      dsimp only
      exact ⟨.error err, w1, rfl, fun e he hK => by cases he; rw [hs1 err rfl] at hK; cases hK⟩
    | ok _ =>
      dsimp only
      rw [io_bind_eq]
      rcases probeRefList_sysOnly raw hRaw (FdPolicy.keepFds spec.fdPolicy).toList w1 with ⟨r2, w2, hw2, hs2⟩
      rw [keepFdsImpl_eq, hw2]
      dsimp only
      cases r2 with
      | error err =>
        dsimp only
        exact ⟨.error err, w2, rfl, fun e he hK => by cases he; rw [hs2 err rfl] at hK; cases hK⟩
      | ok _ =>
        dsimp only
        rw [io_bind_eq]
        rcases filterOpenCloseList_ok raw hRaw spec.closeFds.toList #[] w2 with ⟨openCloseFds, w2b, hw2b⟩
        rw [hw2b]
        dsimp only
        rw [io_bind_eq]
        rcases hRaw.mkPipeCloexec_ok w2b with ⟨r3, w3, hw3⟩
        rw [hw3]
        dsimp only
        cases r3 with
        | error err =>
          dsimp only
          exact ⟨.error _, w3, rfl, fun e he hK => by cases he; cases hK⟩
        | ok errPair =>
          dsimp only
          rcases errPair with ⟨errR, errW⟩
          rw [io_bind_eq, io_pure_eq]
          dsimp only
          rw [io_bind_eq]
          rcases hRaw.mkPipeCloexec_ok w3 with ⟨r4, w4, hw4⟩
          rw [hw4]
          dsimp only
          cases r4 with
          | error err =>
            dsimp only
            rw [io_bind_eq]
            rcases closeListQuiet_ok raw hRaw [errW, errR] w4 with ⟨_, w5, hw5⟩
            rw [hw5]
            exact ⟨.error _, w5, rfl, fun e he hK => by cases he; cases hK⟩
          | ok syncPair =>
            dsimp only
            rcases syncPair with ⟨syncR, syncW⟩
            rw [io_bind_eq, io_pure_eq]
            dsimp only
            rw [io_bind_eq]
            rcases performFork_sysOnly raw hRaw spec (some syncR) errW openCloseFds #[FdRef.handle errR, FdRef.handle syncW] true w4 with ⟨r5, w5, hw5, hs5⟩
            rw [hw5]
            dsimp only
            rw [io_bind_eq]
            rcases closeListQuiet_ok raw hRaw [errW, syncR] w5 with ⟨_, w6, hw6⟩
            rw [hw6]
            dsimp only
            cases r5 with
            | error err =>
              dsimp only
              rw [io_bind_eq]
              rcases closeListQuiet_ok raw hRaw [syncW, errR] w6 with ⟨_, w7, hw7⟩
              rw [hw7]
              exact ⟨.error err, w7, rfl, fun e he hK => by cases he; rw [hs5 err rfl] at hK; cases hK⟩
            | ok pid =>
              dsimp only
              exact ⟨.ok _, w6, rfl, fun e he => by cases he⟩

/-- Proof that `LeanSwe.PostFork.releaseBarrier` never fails with `.invalidInput`. -/
theorem releaseBarrier_never_invalidInput (p : PendingChild) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO PostForkError.kind .invalidInput (LeanSwe.PostFork.releaseBarrier p) w := by
  rcases LeanSwe.PostFork.Proofs.defaultOps_exists_noThrow with ⟨raw, hDef, hRaw⟩
  apply neverErrorKindIO_of_ne _ w .invalidInput
  unfold LeanSwe.PostFork.releaseBarrier
  rw [hDef]
  dsimp only [Impl.Internal.mkHostOps]
  rw [io_bind_eq]
  rcases hRaw.probeHandleOpen_ok p.errRead w with ⟨r0, w0, hw0⟩
  rw [hw0]
  dsimp only
  cases r0 with
  | error ep =>
    dsimp only
    exact ⟨.error _, w0, rfl, fun e he hK => by cases he; cases hK⟩
  | ok _ =>
    dsimp only
    rw [io_bind_eq]
    rcases writeAllRetryEintr_sysOnly raw hRaw p.syncWrite (ByteArray.mk #[1]) 0 18 w0 with ⟨r1, w1, hw1, hs1⟩
    rw [hw1]
    dsimp only
    cases r1 with
    | ok _ =>
      dsimp only
      rw [io_bind_eq]
      rcases hRaw.closeFd_ok p.syncWrite w1 with ⟨_, w2, hw2⟩
      rw [hw2]
      exact awaitExecOrFailure_never_invalidInput raw hRaw p.pid p.pgid p.errRead 18 w2
    | error err =>
      dsimp only
      by_cases hEp : err.errno == some Errno.EPIPE
      · simp only [hEp, ↓reduceIte]
        rw [io_bind_eq]
        rcases hRaw.closeFd_ok p.syncWrite w1 with ⟨_, w2, hw2⟩
        rw [hw2]
        exact awaitExecOrFailure_never_invalidInput raw hRaw p.pid p.pgid p.errRead 18 w2 true
      · simp only [hEp, Bool.false_eq_true, ↓reduceIte]
        by_cases hEb : Impl.Internal.isFastFailSyncWriteErr err.errno = true
        · simp only [hEb, ↓reduceIte, io_pure_eq]
          exact ⟨.error err, w1, rfl, fun e he hK => by cases he; rw [hs1 err rfl] at hK; cases hK⟩
        · have hEbF : Impl.Internal.isFastFailSyncWriteErr err.errno = false :=
            Bool.eq_false_iff.mpr hEb
          simp only [hEbF, Bool.false_eq_true, ↓reduceIte]
          have hCleanup : ∀ wt, ∃ r w',
              ((do
                let _ ← raw.closeFd p.errRead
                let _ ← Impl.Internal.waitRetryEintr raw p.pid 18
                return (.error err : Except PostForkError SpawnedChild)) :
                IO (Except PostForkError SpawnedChild)) wt = .ok r w' ∧
              (∀ e, r = .error e → e.kind ≠ .invalidInput) := by
            intro wt
            rw [io_bind_eq]
            rcases hRaw.closeFd_ok p.errRead wt with ⟨_, wa, hwa⟩
            rw [hwa]
            dsimp only
            rw [io_bind_eq]
            rcases waitRetryEintr_sysOnly raw hRaw p.pid 18 wa with ⟨_, wb, hwb, _⟩
            rw [hwb]
            exact ⟨.error err, wb, rfl, fun e he hK => by cases he; rw [hs1 err rfl] at hK; cases hK⟩
          rw [io_bind_eq]
          rcases hRaw.closeFd_ok p.syncWrite w1 with ⟨rcSw, w2, hw2⟩
          rw [hw2]
          dsimp only
          cases rcSw with
          | ok _ => dsimp only; exact hCleanup w2
          | error ce =>
            dsimp only
            by_cases hCe : (!Impl.Internal.isKernelCloseDetachNonBadf ce) = true
            · simp only [hCe, ↓reduceIte, io_pure_eq]
              exact ⟨.error err, w2, rfl, fun e he hK => by cases he; rw [hs1 err rfl] at hK; cases hK⟩
            · have hCeF : (!Impl.Internal.isKernelCloseDetachNonBadf ce) = false := Bool.eq_false_iff.mpr hCe
              simp only [hCeF, Bool.false_eq_true, ↓reduceIte]
              exact hCleanup w2

private theorem abortBarrier_sysOnly (p : PendingChild) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.PostFork.abortBarrier p w = .ok r w' ∧ (∀ e, r = .error e → e.kind = .sysError) := by
  rcases LeanSwe.PostFork.Proofs.defaultOps_exists_noThrow with ⟨raw, hDef, hRaw⟩
  unfold LeanSwe.PostFork.abortBarrier
  rw [hDef]
  dsimp only [Impl.Internal.mkHostOps]
  rw [io_bind_eq]
  rcases hRaw.closeFd_ok p.syncWrite w with ⟨r1, w1, hw1⟩
  rw [hw1]
  dsimp only
  have hRest : ∀ wt, ∃ (r : Except PostForkError AbortOutcome) (w' : Void IO.RealWorld),
      ((do
        let repRes ← Impl.Internal.readAllRetryEintr raw p.errRead 16 ByteArray.empty 18
        let _ ← raw.closeFd p.errRead
        match repRes with
        | .error err =>
          let _ ← Impl.Internal.waitRetryEintr raw p.pid 18
          return .error err
        | .ok repBytes =>
          let wst ← match ← Impl.Internal.waitRetryEintr raw p.pid 18 with
            | .ok s => pure s
            | .error err => return .error err
          match decodeChildFailure repBytes with
          | none => return .ok (.aborted wst)
          | some cf => return .ok (.failedBeforeBarrier { cf with waitStatus := some wst } wst)) :
        IO (Except PostForkError AbortOutcome)) wt = .ok r w' ∧
      (∀ (e : PostForkError), r = .error e → e.kind = PostForkErrorKind.sysError) := by
    intro wt
    rw [io_bind_eq]
    rcases readAllRetryEintr_sysOnly raw hRaw p.errRead 16 ByteArray.empty 18 wt with ⟨rr, wa, hwa, hsrr⟩
    rw [hwa]
    dsimp only
    rw [io_bind_eq]
    rcases hRaw.closeFd_ok p.errRead wa with ⟨_, wb, hwb⟩
    rw [hwb]
    dsimp only
    cases rr with
    | error err =>
      dsimp only
      rw [io_bind_eq]
      rcases waitRetryEintr_sysOnly raw hRaw p.pid 18 wb with ⟨_, wc, hwc, _⟩
      rw [hwc]
      exact ⟨.error err, wc, rfl, fun e he => by cases he; exact hsrr err rfl⟩
    | ok repBytes =>
      dsimp only
      rw [io_bind_eq]
      rcases waitRetryEintr_sysOnly raw hRaw p.pid 18 wb with ⟨rw, wc, hwc, hsrw⟩
      rw [hwc]
      dsimp only
      cases rw with
      | error err =>
        dsimp only
        exact ⟨.error err, wc, rfl, fun e he => by cases he; exact hsrw err rfl⟩
      | ok wst =>
        dsimp only
        cases decodeChildFailure repBytes with
        | none => dsimp only; exact ⟨.ok _, wc, rfl, fun e he => by cases he⟩
        | some cf => dsimp only; exact ⟨.ok _, wc, rfl, fun e he => by cases he⟩
  cases r1 with
  | ok _ => dsimp only; exact hRest w1
  | error e =>
    dsimp only
    by_cases hEb : (!Impl.Internal.isKernelCloseDetachNonBadf e) = true
    · simp only [hEb, ↓reduceIte, io_pure_eq]
      exact ⟨.error _, w1, rfl, fun err herr => by cases herr; rfl⟩
    · have hEbF : (!Impl.Internal.isKernelCloseDetachNonBadf e) = false := Bool.eq_false_iff.mpr hEb
      simp only [hEbF, Bool.false_eq_true, ↓reduceIte]
      exact hRest w1

/-- Proof that `LeanSwe.PostFork.abortBarrier` never fails with `.invalidInput`. -/
theorem abortBarrier_never_invalidInput (p : PendingChild) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO PostForkError.kind .invalidInput (LeanSwe.PostFork.abortBarrier p) w := by
  apply neverErrorKindIO_of_ne _ w .invalidInput
  rcases abortBarrier_sysOnly p w with ⟨r, w', hw, hs⟩
  exact ⟨r, w', hw, fun e he hK => by rw [hs e he] at hK; cases hK⟩

/-- Proof that `LeanSwe.PostFork.abortBarrier` never fails with `.childFailed`. -/
theorem abortBarrier_never_childFailed (p : PendingChild) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO PostForkError.kind .childFailed (LeanSwe.PostFork.abortBarrier p) w := by
  apply neverErrorKindIO_of_ne _ w .childFailed
  rcases abortBarrier_sysOnly p w with ⟨r, w', hw, hs⟩
  exact ⟨r, w', hw, fun e he hK => by rw [hs e he] at hK; cases hK⟩

end ErrorCoverageImpossible

end LeanSwe.PostFork.Proofs

import Core.NondetTest
import Core.Assumptions
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Api
import LeanSwe.PostFork.Aeneas.Bridge
import LeanSwe.PostFork.SpecTests

namespace LeanSwe.PostFork

open _root_.Aeneas _root_.Aeneas.Std Result
open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model

private theorem ok_inj {α : Type} {a b : α} (h : (ok a : Result α) = ok b) : a = b := by
  simpa using h

private def stubApi : PostForkAeneasApi :=
  { encodeFailureReport := fun st e =>
      let _ := e
      ok (Array.make 8#usize [80#u8, 1#u8, st, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8])
    validateChildArgs := fun _ _ _ => ok (.Ok ())
    clearCloexec := fun s _ => ok (.Ok (), s)
    setCloexec := fun s _ => ok (.Ok (), s)
    relocateRepAbove2 := fun s fd => ok (.Ok fd, s)
    setupStdio := fun s _ _ _ _ => ok (.Ok (), s)
    closeFdsAbove2Except := fun s _ _ => ok (.Ok (), s)
    parseDirentName := fun buf start stop => ok (expectedDirentParse buf start stop)
    readSyncByte := fun s _ => ok (true, s)
    writeAll := fun s _ _ => ok (.Ok (), s)
    runChild := fun s _ _ _ _ _ _ _ => ok { s with status := .exited 127#i32 } }

example : ¬ Core.AllPass (test_postfork_wireEncoder_uniformAndRoundTrip
    { stubApi with
      encodeFailureReport := fun st _ =>
        ok (Array.make 8#usize [0#u8, 1#u8, st, 0#u8, 2#u8, 0#u8, 0#u8, 0#u8]) }) := by
  intro h
  rcases (h 7#u8 2#i32 .execve Errno.ENOENT).1 with ⟨a, hOk, hEq⟩
  cases ok_inj hOk
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_postfork_cloexecAndRelocate_preserveFlagsAndBounds
    { stubApi with
      clearCloexec := fun s fd => ok (.Ok (), s.putSlot fd.val { desc := 1, cloexec := true }) }) := by
  intro h
  let s0 : ChildState :=
    { fds := [(3, { desc := 1, cloexec := true })]
      descs := [(1, .stream true true false [])] }
  have hAssume := (h s0 3#i32).2.2.2 ⟨rfl, rfl⟩
  rcases hAssume.1 with ⟨p, hOk, hPost⟩
  cases ok_inj hOk
  dsimp [CloexecTogglePost, s0, ChildState.getFd] at hPost
  have : ({ desc := 1, cloexec := true, extraFdFlags := 0#i32 } : FdEntry) =
      { desc := 1, cloexec := false, extraFdFlags := 0#i32 } := by
    have hp := hPost.2.1
    simp [ChildState.putSlot, eraseFdEntries, expectedExtraFlagsAfterSetfd] at hp
  exact absurd this (by decide)

example : ¬ Core.AllPass (test_postfork_setupStdio_clobberFreePermutationsAndCycles
    { stubApi with
      setupStdio := fun s _ _ _ _ => ok (.Ok (), s) }) := by
  intro h
  let s0 : ChildState :=
    { fdLimit := 16
      fds := [(0, { desc := 100, cloexec := true }), (1, { desc := 101, cloexec := false }), (2, { desc := 102, cloexec := false })] }
  have hBase := h s0 1#i32 0#i32 3#i32 true
  dsimp [test_postfork_setupStdio_clobberFreePermutationsAndCycles, s0] at hBase
  have hClosed := (hBase ⟨rfl, rfl⟩ ⟨by decide, by decide, by decide⟩).1
  rcases hClosed with ⟨p, hOk, hErr, _⟩
  cases ok_inj hOk
  cases hErr

example : ¬ Core.AllPass (test_postfork_parseDirentName_canonicalDecimalAndRoundTrip
    { stubApi with
      parseDirentName := fun _ _ _ => ok 3#i32 }) := by
  intro h
  let zeroBuf := Array.repeat 256#usize 0#u8
  have hDot := (h zeroBuf 0#usize 0#usize 0).2.1
  exact absurd (ok_inj hDot) (by decide)

example : ¬ Core.AllPass (test_postfork_closeFdsAbove2Except_closeRangeAndProcFallback
    { stubApi with
      closeFdsAbove2Except := fun s _ _ => ok (.Ok (), s) }) := by
  intro h
  let s0 : ChildState :=
    { fds := [(0, { desc := 10, cloexec := false }), (500, { desc := 50, cloexec := false })] }
  have hSub := (h s0 (-1)#i32 (mkSliceI32 0#usize [])).2.1
  rcases hSub with ⟨p, hOk, _, _, _, _, _, _, hClosed500, _⟩
  cases ok_inj hOk
  simp [ChildState.isOpen, ChildState.getFd] at hClosed500

example : ¬ Core.AllPass (test_postfork_readSyncByte_eintrRetryAndClose
    { stubApi with
      readSyncByte := fun s _ => ok (false, s) }) := by
  intro h
  have hSub := (h {} 5#i32).2.1
  rcases hSub with ⟨p, hOk, hGot, _⟩
  cases ok_inj hOk
  exact absurd hGot (by decide)

example : ¬ Core.AllPass (test_postfork_writeAll_eintrPartialWriteAndReassembly
    { stubApi with
      writeAll := fun s _ _ => ok (.Ok (), s) }) := by
  intro h
  have hSub := (h {} 4#i32 (mkSliceU8 0#usize [])).2.1
  rcases hSub with ⟨p, hOk, _, hApp⟩
  cases ok_inj hOk
  simp [appendedBytesForDesc, writtenBytesForDesc, mkSliceU8] at hApp

example : ¬ Core.AllPass (test_postfork_runChild_safetyAndExecPost
    { stubApi with
      runChild := fun s _ _ _ _ _ _ _ => ok { s with status := .exited 0#i32 } }) := by
  intro h
  have hBase := (h {} 0#u32 (-1)#i32 0#i32 1#i32 2#i32 3#i32
    (mkSliceI32 0#usize []) (mkSliceI32 0#usize []) none [] [] []).1
  rcases hBase with ⟨s', hOk, hSafe⟩
  cases ok_inj hOk
  rcases hSafe with h127 | ⟨_, h125, _⟩ | ⟨_, img, hExecd, _⟩
  · cases h127
  · cases h125
  · cases hExecd

example : ¬ Core.AllPass (test_postfork_runChild_validationStagesAndBarrier
    { stubApi with
      runChild := fun s _ _ _ _ _ _ _ => ok { s with status := .exited 0#i32 } }) := by
  intro h
  have hBase := h {} 0#u32 (-1)#i32 0#i32 1#i32 2#i32 (-1)#i32
    (mkSliceI32 0#usize []) (mkSliceI32 0#usize []) none [] [] [] ⟨rfl, rfl⟩
  dsimp only [test_postfork_runChild_validationStagesAndBarrier, stubApi] at hBase
  simp only [show decide ((-1)#i32 < 0#i32) = true from by decide] at hBase
  rcases hBase.1 with ⟨s', hOk, h127, _⟩
  cases ok_inj hOk
  cases h127

example : ¬ Core.AllPass (test_postfork_worldModel_linuxKernelEdgeInvariants
    { stubApi with
      writeAll := fun s _ _ => ok (.Err EPIPE, s) }) := by
  intro h
  let s0 : ChildState :=
    { fds := [(4, { desc := 5, cloexec := true })]
      descs := [(5, .stream false true true [])] }
  let pay := mkSliceU8 1#usize [1#u8]
  have hBase := h s0 4#i32 4#i32 0#i32 3#u32 3#u32 0#u32 2#i32 [97#u8] [97#u8] [] [] pay ⟨rfl, rfl⟩
  dsimp [s0, pay, mkSliceU8] at hBase
  rcases hBase.2.2.2.1 with ⟨p, hOk, _, hSig⟩
  cases ok_inj hOk
  exact absurd hSig (by decide)

private def badHostBuilder :
    LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 := fun raw =>
  { spawn := fun spec => do
      let _ ← raw.probeFdOpen 0
      if !LeanSwe.PostFork.Model.validateSpec spec then
        return .error { kind := .invalidInput, message := "bad" }
      return .ok { pid := 1, pgid := none }
    spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "bad" })
    releaseBarrier := fun _ => pure (.error { kind := .sysError, message := "bad" })
    abortBarrier := fun _ => pure (.error { kind := .sysError, message := "bad" }) }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire badHostBuilder) := by
  intro h
  have hBase := (h { path := "", argv := #[] } .validate 1 (.exited 0) 0 3 .direct).1
  dsimp [test_postfork_hostOps_validationBarrierEintrAndWire, badHostBuilder,
    LeanSwe.PostFork.Model.Internal.mockPosixHostOps] at hBase
  exact absurd hBase.2 (by decide)

private theorem mem_byteArray_toList_loop_mut (bs : ByteArray) (i : Nat) (r : List UInt8) (x : UInt8) :
    x ∈ ByteArray.toList.loop bs i r → x ∈ r ∨ ∃ j, j < bs.size ∧ x = bs.get! j := by
  induction hLen : bs.size - i generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop.eq_1]
    have hGe : ¬ (i < bs.size) := by omega
    simp only [hGe, ↓reduceIte, List.mem_reverse]
    intro hx; exact Or.inl hx
  | succ k ih =>
    rw [ByteArray.toList.loop.eq_1]
    have hLt : i < bs.size := by omega
    simp only [hLt, ↓reduceIte]
    intro hx
    rcases ih (i + 1) (bs.get! i :: r) (by omega) hx with h1 | ⟨j, hj, hEq⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact Or.inr ⟨i, hLt, rfl⟩
      · exact Or.inl h2
    · exact Or.inr ⟨j, hj, hEq⟩

private theorem hasEmbeddedNulStr_true_mut :
    LeanSwe.PostFork.Model.hasEmbeddedNulStr "/bin/true" = false := by
  unfold LeanSwe.PostFork.Model.hasEmbeddedNulStr
  rw [List.any_eq_false]
  intro x hx hEq
  have h0 : x = 0 := by simpa using hEq
  subst h0
  rcases mem_byteArray_toList_loop_mut "/bin/true".toUTF8 0 [] 0 hx with hEmpty | ⟨j, hj, hVal⟩
  · cases hEmpty
  · have hNe : ∀ k, k < "/bin/true".toUTF8.size → "/bin/true".toUTF8.get! k ≠ 0 := by decide
    exact hNe j hj hVal.symm

example : ¬ Core.AllPass (test_postfork_aeneasRefinement_flagsAndValidateChildArgs
    { stubApi with
      validateChildArgs := fun _ _ _ => ok (.Err EINVAL) }) := by
  intro h
  let spec0 : ChildSpecM Std.I32 := { path := "/bin/true", argv := #[] }
  let emptySl : Slice Std.I32 := mkSliceI32 0#usize []
  have hSub := (h spec0 false (-1)#i32 5#i32 emptySl emptySl).2.2.2.2.2.2.2.2
  have hPre :
      Bridge.specStringHygieneOk spec0 = true ∧
      Bridge.specHandlesValid spec0 = true ∧
      spec0.closeFds.all LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      (LeanSwe.PostFork.Model.FdPolicy.keepFds spec0.fdPolicy).all LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      emptySl.val = (spec0.closeFds.map Bridge.fdRefToStdI32).toList ∧
      emptySl.val = ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec0.fdPolicy).map Bridge.fdRefToStdI32).toList ∧
      Bridge.internalPipesDisjoint false false (-1)#i32 (-1)#i32 (-1)#i32 (-1)#i32 5#i32 emptySl.val emptySl.val = true := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [spec0, Bridge.specStringHygieneOk, hasEmbeddedNulStr_true_mut]
    · simp [spec0, Bridge.specHandlesValid, Bridge.allSpecFdRefs, LeanSwe.PostFork.Model.FdPolicy.keepFds]
    · simp [spec0]
    · simp [spec0, LeanSwe.PostFork.Model.FdPolicy.keepFds]
    · simp [spec0, emptySl, mkSliceI32, Array.to_slice, Array.make]
    · simp [spec0, emptySl, mkSliceI32, Array.to_slice, Array.make,
        LeanSwe.PostFork.Model.FdPolicy.keepFds]
    · simp [emptySl, mkSliceI32, Array.to_slice, Array.make, Bridge.internalPipesDisjoint,
        sliceContainsNonnegSpec]
  rcases (hSub hPre).1 with ⟨r, hOk, hEq⟩
  cases ok_inj hOk
  have hVal : LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec0 = true := by
    simp [spec0, LeanSwe.PostFork.Model.validateSpecWith, LeanSwe.PostFork.Model.disjointFdRefArrays,
      LeanSwe.PostFork.Model.FdPolicy.keepFds, hasEmbeddedNulStr_true_mut]
  rw [hVal] at hEq
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    (modeFn := fun _ => 0)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).1
  exact absurd hSub.2 (by decide)

private def leakSpawnForkErrBuilder :
    LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 := fun raw =>
  { (LeanSwe.PostFork.Impl.Internal.mkHostOps raw) with
    spawn := fun _ => do
      let (_, errW) ← match ← raw.mkPipeCloexec with
        | .ok p => pure p
        | .error e => return .error (LeanSwe.PostFork.Impl.Internal.mkSysErr e "pipe")
      let _ ← raw.closeFd errW
      return .error (LeanSwe.PostFork.Impl.Internal.mkSysErr Errno.EAGAIN "fork failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    (mkOps := leakSpawnForkErrBuilder)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.2.2.1
  rcases hSub.1 with ⟨_, st, hRun, _, hCl⟩
  have hEq : st.closedHandles = [11] :=
    congrArg (·.closedHandles) (congrArg Prod.snd hRun.symm)
  rw [hEq] at hCl
  exact absurd hCl (by decide)

private def deadlockBusyReleaseBuilder :
    LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 := fun raw =>
  { (LeanSwe.PostFork.Impl.Internal.mkHostOps raw) with
    releaseBarrier := fun pending => do
      let _ ← raw.writeOnce pending.syncWrite (ByteArray.mk #[1]) 0 1
      let _ ← raw.closeFd pending.syncWrite
      let _ ← raw.closeFd pending.errRead
      let _ ← raw.waitOnce pending.pid
      return .error (LeanSwe.PostFork.Impl.Internal.mkSysErr Errno.EIO "host write failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    (mkOps := deadlockBusyReleaseBuilder)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.2.2.1
  rcases hSub.2.2.2.2.2.2.1 with ⟨_, st, hRun, _, _, hCnt, _⟩
  have hEq : st.callCount = 4 :=
    congrArg (·.callCount) (congrArg Prod.snd hRun.symm)
  rw [hEq] at hCnt
  exact absurd hCnt (by decide)

private def badByteLaneFlatten
    (syncRead? : Option Int32) (errWrite : Int32)
    (stdioRefs closeRefs keepRefs : _root_.Array (FdRef Int32))
    (argv : _root_.Array (ArgToken Int32)) :
    LeanSwe.PostFork.Model.Internal.FlattenedForkArgsM Int32 :=
  let base := LeanSwe.PostFork.Impl.Internal.flattenForkArgs syncRead? errWrite stdioRefs closeRefs keepRefs argv
  { base with keepSlots := ByteArray.mk (List.replicate (keepRefs.size * 4) (0 : UInt8)).toArray }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    (flattenFn := badByteLaneFlatten)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.1
  exact absurd hSub.2.2.2.2.2.2.2 (by decide)

private def unprobedErrReadReleaseBuilder :
    LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 := fun raw =>
  { (LeanSwe.PostFork.Impl.Internal.mkHostOps raw) with
    releaseBarrier := fun pending => do
      let _ ← raw.writeOnce pending.syncWrite (ByteArray.mk #[1]) 0 1
      let _ ← raw.readOnce pending.errRead 16
      return .error (LeanSwe.PostFork.Impl.Internal.mkSysErr Errno.EBADF "host read failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    (mkOps := unprobedErrReadReleaseBuilder)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.2.2.1
  rcases hSub.2.2.2.2.2.2.2.2.1 with ⟨_, st, hRun, _, _, hSync, _⟩
  have hEq : st.syncWritten = ByteArray.mk #[1] :=
    congrArg (·.syncWritten) (congrArg Prod.snd hRun.symm)
  rw [hEq] at hSync
  exact absurd hSync (by decide)

private def epipeEmptyFalseOkBuilder :
    LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 := fun raw =>
  { spawn := fun _ => pure (.error { kind := .invalidInput, message := "bad" })
    spawnWithBarrier := fun _ => do
      modify fun s => { s with hasSpawned := true, allocSyncWriteFd := 13 }
      pure (.ok { pid := 4242, pgid := some 4242, syncWrite := 13, errRead := 10 })
    releaseBarrier := fun pending => do
      match ← raw.writeOnce pending.syncWrite (ByteArray.mk #[1]) 0 1 with
      | .ok _ => return .ok { pid := pending.pid, pgid := pending.pgid }
      | .error err =>
        if err == Errno.EPIPE then
          let _ ← raw.closeFd pending.syncWrite
          let _ ← raw.readOnce pending.errRead 16
          let _ ← raw.closeFd pending.errRead
          return .ok { pid := pending.pid, pgid := pending.pgid }
        else
          return .error (LeanSwe.PostFork.Impl.Internal.mkSysErr err "write failed")
    abortBarrier := fun _ => pure (.error { kind := .sysError, message := "bad" }) }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire epipeEmptyFalseOkBuilder) := by
  intro h
  have hSub := (h { path := "", argv := #[] } .validate 1 (.signaled 9) 0 3 .direct).2.2.2.2.2.2
  rcases hSub.2.2.1.2 with ⟨_, _, hErr, _⟩
  cases hErr

end LeanSwe.PostFork

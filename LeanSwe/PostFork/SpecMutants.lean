import Core.NondetTest
import Core.Assumptions
import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Types.Internal
import LeanSwe.PostFork.Model
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.SpecMutants.RefHost

namespace LeanSwe.PostFork

open _root_.Aeneas _root_.Aeneas.Std Result
open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model
open LeanSwe.PostFork.Aeneas.Internal
open LeanSwe.PostFork.Aeneas.Internal.World

private theorem ok_inj {α : Type} {a b : α} (h : (ok a : Result α) = ok b) : a = b := by
  simpa using h

private def stubApi : PostForkAeneasApi :=
  { wireMagic := 80#u8
    wireVersion := 1#u8
    stageValidate := 1#u8
    stageProcessGroup := 2#u8
    stageSignalReset := 3#u8
    stageFdSetup := 4#u8
    stageCloseUnkept := 5#u8
    stageChdir := 6#u8
    stageExecve := 7#u8
    encodeFailureReport := fun st e =>
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
    runChild := fun s _ _ _ _ => ok { s with status := .exited 127#i32 } }

example : ¬ Core.AllPass (test_postfork_wireEncoder_uniformAndRoundTrip
    { stubApi with
      encodeFailureReport := fun st _ =>
        ok (Array.make 8#usize [0#u8, 1#u8, st, 0#u8, 2#u8, 0#u8, 0#u8, 0#u8]) }) := by
  intro h
  rcases (h 7#u8 2#i32 .execve Errno.ENOENT).1 with ⟨a, hOk, hEq⟩
  cases ok_inj hOk
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_postfork_wireEncoder_uniformAndRoundTrip
    { stubApi with
      wireMagic := 81#u8 }) := by
  intro h
  have hAssume := (h 7#u8 2#i32 .execve Errno.ENOENT).2.2.2.2.2.2.2.2.2
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  exact absurd hAssume.2.1.1 (by decide)

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
      runChild := fun s _ _ _ _ => ok { s with status := .exited 0#i32 } }) := by
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
      runChild := fun s _ _ _ _ => ok { s with status := .exited 0#i32 } }) := by
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
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  { refMkHostOps raw with
    spawn := fun spec => do
      let _ ← raw.probeFdOpen 0
      if !LeanSwe.PostFork.Model.validateSpec spec then
        return .error { kind := .invalidInput, message := "bad" }
      return .ok { pid := 1, pgid := none } }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire badHostBuilder) := by
  intro h
  have hBase := (h { path := "", argv := #[] } .validate 1 (.exited 0) 0 3 .direct).1
  dsimp [test_postfork_hostOps_validationBarrierEintrAndWire, badHostBuilder,
    LeanSwe.PostFork.mockPosixHostOps] at hBase
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
    refFlattenForkArgs
    (fun _ => 0)
    (fun raw => refMkHostOps raw)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).1
  exact absurd hSub.2 (by decide)

private def leakSpawnForkErrBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  { refMkHostOps raw with
    spawn := fun _ => do
      let (_, errW) ← match ← raw.mkPipeCloexec with
        | .ok p => pure p
        | .error e => return .error (refMkSysErr e "pipe")
      let _ ← raw.closeFd errW
      return .error (refMkSysErr Errno.EAGAIN "fork failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    refFlattenForkArgs
    refForkModeToUInt32
    leakSpawnForkErrBuilder) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.2.2.1
  rcases hSub.1 with ⟨_, st, hRun, _, hCl⟩
  have hEq : st.closedHandles = [11] :=
    congrArg (·.closedHandles) (congrArg Prod.snd hRun.symm)
  rw [hEq] at hCl
  exact absurd hCl (by decide)

private def deadlockBusyReleaseBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  { refMkHostOps raw with
    releaseBarrier := fun pending => do
      let _ ← raw.writeOnce pending.syncWrite (ByteArray.mk #[1]) 0 1
      let _ ← raw.closeFd pending.syncWrite
      let _ ← raw.closeFd pending.errRead
      let _ ← raw.waitOnce pending.pid
      return .error (refMkSysErr Errno.EIO "host write failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    refFlattenForkArgs
    refForkModeToUInt32
    deadlockBusyReleaseBuilder) := by
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
    LeanSwe.PostFork.Impl.Internal.FlattenedForkArgsM Int32 :=
  let base := refFlattenForkArgs syncRead? errWrite stdioRefs closeRefs keepRefs argv
  { base with keepSlots := ByteArray.mk (List.replicate (keepRefs.size * 4) (0 : UInt8)).toArray }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    badByteLaneFlatten
    refForkModeToUInt32
    (fun raw => refMkHostOps raw)) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.1
  exact absurd hSub.2.2.2.2.2.2.2 (by decide)

private def unprobedErrReadReleaseBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  { refMkHostOps raw with
    releaseBarrier := fun pending => do
      let _ ← raw.writeOnce pending.syncWrite (ByteArray.mk #[1]) 0 1
      let _ ← raw.readOnce pending.errRead 16
      return .error (refMkSysErr Errno.EBADF "host read failed") }

example : ¬ Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter
    refFlattenForkArgs
    refForkModeToUInt32
    unprobedErrReadReleaseBuilder) := by
  intro h
  have hSub := (h none 3 #[] #[] #[] #[] { path := "", argv := #[] }).2.2.2.2.2.2.2.2.1
  rcases hSub.2.2.2.2.2.2.2.2.1 with ⟨_, st, hRun, _, _, hSync, _⟩
  have hEq : st.syncWritten = ByteArray.mk #[1] :=
    congrArg (·.syncWritten) (congrArg Prod.snd hRun.symm)
  rw [hEq] at hSync
  exact absurd hSync (by decide)

private def epipeEmptyFalseOkBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  { refMkHostOps raw with
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
          return .error (refMkSysErr err "write failed") }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire epipeEmptyFalseOkBuilder) := by
  intro h
  have hSub := (h { path := "", argv := #[] } .validate 1 (.signaled 9) 0 3 .direct).2.2.2.2.2.2
  have hVal : (!LeanSwe.PostFork.Model.validateSpec
      ({ path := "/bin/true", argv := #[], processGroup := .newGroup } : ChildSpecM Int32)) = false := by
    simp [LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      LeanSwe.PostFork.Model.disjointFdRefArrays, LeanSwe.PostFork.Model.FdPolicy.keepFds,
      hasEmbeddedNulStr_true_mut]
  simp only [epipeEmptyFalseOkBuilder, refMkHostOps, hVal, Bool.false_eq_true, ↓reduceIte,
    refProbeStdioPlan, refProbeList, refFilterOpenCloseList, refPerformFork, refStdioRefsArray,
    refCloseListQuiet, LeanSwe.PostFork.Model.FdPolicy.keepFds,
    LeanSwe.PostFork.Model.formatEnvEntriesBytes, LeanSwe.PostFork.mockPosixHostOps,
    StateT.run, Bind.bind, StateT.bind, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet] at hSub
  rcases hSub.2.2.1.2 with ⟨_, _, hErr, _⟩
  cases hErr

private def rawEnvDroppingBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  let base := refMkHostOps raw
  { base with
    spawn := fun spec => do
      let _ ← raw.forkRun 0 spec.forkMode none 11 #[] #[] #[] spec.cwd spec.path spec.argv
        (LeanSwe.PostFork.Model.formatEnvEntriesBytes #[] spec.env)
      return .ok { pid := 4242, pgid := some 4242 } }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire rawEnvDroppingBuilder) := by
  intro h
  have hSub := (h { path := "", argv := #[] } .validate 1 (.exited 0) 0 3 .direct).2.2.2.1
  have hSz := congrArg Array.size hSub.2.2.2.1
  change (LeanSwe.PostFork.Model.formatEnvEntriesBytes #[] #[("K", "V")]).size = 2 at hSz
  simp [LeanSwe.PostFork.Model.formatEnvEntriesBytes] at hSz

private def rawEnvUncheckedNulBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  let base := refMkHostOps raw
  { base with
    spawn := fun spec =>
      if spec.rawEnv.any (fun e => !LeanSwe.PostFork.Model.isValidRawEnvEntry e) then do
        let _ ← raw.mkPipeCloexec
        return .ok { pid := 4242, pgid := none }
      else base.spawn spec }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire rawEnvUncheckedNulBuilder) := by
  intro h
  let badSpec : ChildSpecM Int32 :=
    { path := "/bin/true", argv := #[], rawEnv := #[ByteArray.mk #[0x41, 0x3D, 0x00]] }
  have hBad : (!LeanSwe.PostFork.Model.validateSpec badSpec) = true := by
    have hNul : LeanSwe.PostFork.Model.isValidRawEnvEntry (ByteArray.mk #[0x41, 0x3D, 0x00]) = false := by
      decide +kernel
    simp [badSpec, LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      hNul, ← Array.all_toList]
  have hAll := h badSpec .validate 1 (.exited 0) 0 3 .direct
  dsimp [test_postfork_hostOps_validationBarrierEintrAndWire] at hAll
  simp only [hBad, ↓reduceIte] at hAll
  rcases hAll.1 with ⟨⟨_, hErr, _⟩, _⟩
  have hIsOk :
      ((rawEnvUncheckedNulBuilder LeanSwe.PostFork.mockPosixHostOps).1 badSpec {}).1 =
        .ok { pid := 4242, pgid := none } := by
    have hNul : LeanSwe.PostFork.Model.isValidRawEnvEntry (ByteArray.mk #[0x41, 0x3D, 0x00]) = false := by
      decide +kernel
    change ((((rawEnvUncheckedNulBuilder LeanSwe.PostFork.mockPosixHostOps).spawn badSpec).run {})).1 = _
    simp [rawEnvUncheckedNulBuilder, badSpec, hNul,
      LeanSwe.PostFork.mockPosixHostOps, ← Array.any_toList]
    rfl
  rw [hIsOk] at hErr
  cases hErr

private def naiveFormatEnvEntriesBytes (rawEnv : Array ByteArray) (env : Array (String × String)) :
    Array ByteArray :=
  rawEnv.map (fun b => b.push 0) ++ env.map (fun (k, v) => s!"{k}={v}".toUTF8.push 0)

private def rawEnvNoDedupBuilder :
    LeanSwe.PostFork.Impl.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 →
      PostForkOpsM (StateM LeanSwe.PostFork.HostMockState) Int32 := fun raw =>
  let base := refMkHostOps raw
  { base with
    spawn := fun spec => do
      let _ ← raw.forkRun 0 spec.forkMode none 11 #[] #[] #[] spec.cwd spec.path spec.argv
        (naiveFormatEnvEntriesBytes spec.rawEnv spec.env)
      return .ok { pid := 4242, pgid := some 4242 } }

example : ¬ Core.AllPass (test_postfork_hostOps_validationBarrierEintrAndWire rawEnvNoDedupBuilder) := by
  intro h
  have hSub := (h { path := "", argv := #[] } .validate 1 (.exited 0) 0 3 .direct).2.2.2.1
  have hSz := congrArg Array.size hSub.2.2.2.1
  change (naiveFormatEnvEntriesBytes
    #[ByteArray.mk #[0x4B, 0x3D, 0x78], ByteArray.mk #[0x52, 0x3D, 0x80, 0xFF]]
    #[("K", "V")]).size = 2 at hSz
  simp [naiveFormatEnvEntriesBytes] at hSz

end LeanSwe.PostFork

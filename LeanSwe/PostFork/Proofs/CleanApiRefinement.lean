import Core.PropCheck
import LeanSwe.PostFork.SpecTests
import LeanSwe.PostFork.Proofs.RunChildPre
import LeanSwe.PostFork.Proofs.HostOrchBase

/-!
Kernel proofs for `Aeneas` <-> `PostFork.Model` flag and validation
refinement, plus `PostFork` host marshaling, default-policy invariants,
negative `.raw` slot-clamp hygiene, `ForkMode` encoding, pipe cleanup, `EBUSY`
barrier fail-fast safety, and closed-`.raw` pipe-collision avoidance:
- `test_postfork_aeneasRefinement_flagsAndValidateChildArgs` (`Core.AllPass` + `Core.CanReach`),
- `test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter` (`Core.AllPass` + `Core.CanReach`).
-/

namespace LeanSwe.PostFork.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result
open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas
open LeanSwe.PostFork.Aeneas.Model
open LeanSwe.PostFork.Aeneas.Bridge

section HostMarshalingAndCloseFilter

private theorem pushI32Le_size (buf : ByteArray) (v : Int32) :
    (Impl.Internal.pushI32Le buf v).size = buf.size + 4 := by
  unfold Impl.Internal.pushI32Le
  simp only [ByteArray.size_push]

private theorem byteArray_emptyWithCapacity_size (c : Nat) :
    (ByteArray.emptyWithCapacity c).size = 0 :=
  rfl

private theorem array_mkEmpty_size {α : Type} (c : Nat) :
    (_root_.Array.mkEmpty c : _root_.Array α).size = 0 :=
  rfl

private theorem encodeRefList_size {fd : Type}
    (xs : List (FdRef fd)) (hs : _root_.Array fd) (buf : ByteArray) :
    ((xs.foldl
      (fun (hs, buf) r =>
        let (s, hs') := Impl.Internal.encodeFdRefSlot hs r
        (hs', Impl.Internal.pushI32Le buf s))
      (hs, buf)).2).size = buf.size + 4 * xs.length := by
  induction xs generalizing hs buf with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, pushI32Le_size]
    omega

private theorem encodeRefArray_size {fd : Type}
    (hs : _root_.Array fd) (refs : _root_.Array (FdRef fd)) :
    (Impl.Internal.encodeRefArray hs refs).1.size = 4 * refs.size := by
  unfold Impl.Internal.encodeRefArray
  rw [← _root_.Array.foldl_toList]
  have h := encodeRefList_size refs.toList hs (ByteArray.emptyWithCapacity (refs.size * 4))
  simp only [byteArray_emptyWithCapacity_size, Nat.zero_add, _root_.Array.length_toList] at h
  exact h

private theorem stepFlattenArgList_sizes {fd : Type}
    (xs : List (ArgToken fd))
    (hs : _root_.Array fd) (pfxs sfxs : _root_.Array String) (buf : ByteArray) :
    let r := xs.foldl Impl.Internal.stepFlattenArg (hs, pfxs, sfxs, buf)
    r.2.1.size = pfxs.size + xs.length ∧
    r.2.2.1.size = sfxs.size + xs.length ∧
    r.2.2.2.size = buf.size + 4 * xs.length := by
  induction xs generalizing hs pfxs sfxs buf with
  | nil => simp
  | cons tok rest ih =>
    cases tok with
    | lit s =>
      simp only [List.foldl_cons, Impl.Internal.stepFlattenArg, List.length_cons]
      obtain ⟨h1, h2, h3⟩ := ih hs (pfxs.push s) (sfxs.push "") (Impl.Internal.pushI32Le buf (-1))
      simp only [_root_.Array.size_push, pushI32Le_size] at h1 h2 h3
      exact ⟨by omega, by omega, by omega⟩
    | fdDecimal r =>
      simp only [List.foldl_cons, Impl.Internal.stepFlattenArg, List.length_cons]
      obtain ⟨h1, h2, h3⟩ :=
        ih (Impl.Internal.encodeFdRefSlot hs r).2 (pfxs.push "") (sfxs.push "")
          (Impl.Internal.pushI32Le buf (Impl.Internal.encodeFdRefSlot hs r).1)
      simp only [_root_.Array.size_push, pushI32Le_size] at h1 h2 h3
      exact ⟨by omega, by omega, by omega⟩
    | prefixedFd p r s =>
      simp only [List.foldl_cons, Impl.Internal.stepFlattenArg, List.length_cons]
      obtain ⟨h1, h2, h3⟩ :=
        ih (Impl.Internal.encodeFdRefSlot hs r).2 (pfxs.push p) (sfxs.push s)
          (Impl.Internal.pushI32Le buf (Impl.Internal.encodeFdRefSlot hs r).1)
      simp only [_root_.Array.size_push, pushI32Le_size] at h1 h2 h3
      exact ⟨by omega, by omega, by omega⟩

private theorem stepFlattenArgArray_sizes {fd : Type}
    (argv : _root_.Array (ArgToken fd)) (hs : _root_.Array fd) :
    let r := argv.foldl Impl.Internal.stepFlattenArg
      (hs, _root_.Array.mkEmpty argv.size, _root_.Array.mkEmpty argv.size,
        ByteArray.emptyWithCapacity (argv.size * 4))
    r.2.1.size = argv.size ∧
    r.2.2.1.size = argv.size ∧
    r.2.2.2.size = 4 * argv.size := by
  dsimp only
  rw [← _root_.Array.foldl_toList]
  obtain ⟨hp, hsx, hb⟩ :=
    stepFlattenArgList_sizes argv.toList hs
      (_root_.Array.mkEmpty argv.size)
      (_root_.Array.mkEmpty argv.size)
      (ByteArray.emptyWithCapacity (argv.size * 4))
  simp only [array_mkEmpty_size, byteArray_emptyWithCapacity_size, Nat.zero_add,
    _root_.Array.length_toList] at hp hsx hb
  exact ⟨hp, hsx, hb⟩

private theorem flattenForkArgs_sizes {fd : Type}
    (syncRead? : Option fd) (errWrite : fd)
    (stdioRefs closeRefs keepRefs : _root_.Array (FdRef fd))
    (argv : _root_.Array (ArgToken fd)) :
    let flat := Impl.Internal.flattenForkArgs syncRead? errWrite stdioRefs closeRefs keepRefs argv
    flat.metaSlots.size = 20 ∧
    flat.closeSlots.size = 4 * closeRefs.size ∧
    flat.keepSlots.size = 4 * keepRefs.size ∧
    flat.argPrefixes.size = argv.size ∧
    flat.argSuffixes.size = argv.size ∧
    flat.argSlots.size = 4 * argv.size := by
  dsimp only [Impl.Internal.flattenForkArgs]
  have hMeta (s0 s1 s2 s3 s4 : Int32) :
      (Impl.Internal.pushI32Le
        (Impl.Internal.pushI32Le
          (Impl.Internal.pushI32Le
            (Impl.Internal.pushI32Le
              (Impl.Internal.pushI32Le (ByteArray.emptyWithCapacity 20) s0) s1) s2) s3) s4).size = 20 := by
    simp only [pushI32Le_size, byteArray_emptyWithCapacity_size]
  obtain ⟨hp, hsx, hb⟩ := stepFlattenArgArray_sizes argv _
  exact ⟨hMeta _ _ _ _ _, encodeRefArray_size _ closeRefs, encodeRefArray_size _ keepRefs, hp, hsx, hb⟩

private theorem disjointFdRefArrays_false_eq_true {fd : Type}
    (closeFds keepFds : _root_.Array (FdRef fd)) :
    LeanSwe.PostFork.Model.disjointFdRefArrays (fun _ _ => false) closeFds keepFds false =
      LeanSwe.PostFork.Model.disjointFdRefArrays (fun _ _ => false) closeFds keepFds true := by
  unfold LeanSwe.PostFork.Model.disjointFdRefArrays
  dsimp (config := { zetaHave := true }) only
  by_cases hSmall : (decide (closeFds.size ≤ 8) || decide (keepFds.size ≤ 8)) = true
  · simp [hSmall]
  · simp only [hSmall, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
    congr 1
    have hAnyFalse (xs ys : List fd) :
        (xs.any fun _ => ys.any fun _ => false) = false := by
      induction xs with
      | nil => rfl
      | cons _ _ ih => simp [List.any_cons, ih]
    simp only [← _root_.Array.any_toList, _root_.Array.toList_filterMap, hAnyFalse, Bool.not_false]

private theorem validateSpec_eq_validateSpecWith_false {fd : Type} (spec : ChildSpecM fd) :
    LeanSwe.PostFork.Model.validateSpec spec =
      LeanSwe.PostFork.Model.validateSpecWith (fun _ _ => false) spec := by
  unfold LeanSwe.PostFork.Model.validateSpec LeanSwe.PostFork.Model.validateSpecWith
  dsimp (config := { zetaHave := true }) only
  rw [disjointFdRefArrays_false_eq_true]

private theorem subset_byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (x : UInt8)
    (hx : x ∈ r) : x ∈ ByteArray.toList.loop bs i r := by
  induction hLen : bs.size - i generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop.eq_1]
    have hGe : ¬ (i < bs.size) := by omega
    simp [hGe, hx]
  | succ k ih =>
    rw [ByteArray.toList.loop.eq_1]
    have hLt : i < bs.size := by omega
    simp only [hLt, ↓reduceIte]
    exact ih (i + 1) (bs.get! i :: r) (List.mem_cons_of_mem _ hx) (by omega)

private theorem get_mem_byteArray_toList_loop (bs : ByteArray) (i j : Nat) (r : List UInt8)
    (hij : i ≤ j) (hj : j < bs.size) :
    bs.get! j ∈ ByteArray.toList.loop bs i r := by
  induction hLen : bs.size - i generalizing i r with
  | zero => omega
  | succ k ih =>
    rw [ByteArray.toList.loop.eq_1]
    have hLt : i < bs.size := by omega
    simp only [hLt, ↓reduceIte]
    by_cases hEq : i = j
    · subst hEq
      exact subset_byteArray_toList_loop bs (i + 1) (bs.get! i :: r) (bs.get! i) List.mem_cons_self
    · exact ih (i + 1) (bs.get! i :: r) (by omega) (by omega)

private theorem hasEmbeddedNulStr_of_get_zero (s : String) (j : Nat)
    (hj : j < s.toUTF8.size) (hz : s.toUTF8.get! j = 0) :
    LeanSwe.PostFork.Model.hasEmbeddedNulStr s = true := by
  unfold LeanSwe.PostFork.Model.hasEmbeddedNulStr
  rw [List.any_eq_true]
  refine ⟨0, ?_, by decide⟩
  have hm := get_mem_byteArray_toList_loop s.toUTF8 0 j [] (Nat.zero_le j) hj
  rw [hz] at hm
  exact hm

private theorem validateSpec_hygiene_rejections :
    LeanSwe.PostFork.Model.validateSpec ({ path := "a\x00b", argv := #[] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], cwd := some "d\x00e" } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("", "1")] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("A=B", "1")] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("K\x00", "1")] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[], env := #[("K", "V\x00")] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.lit "x\x00"] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.fdDecimal (.raw (-1))] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p\x00" (.raw 3) "s"] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p" (.raw 3) "s\x00"] } : ChildSpecM Int32) = false ∧
    LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[.prefixedFd "p" (.raw (-1)) "s"] } : ChildSpecM Int32) = false := by
  have hNulAb : LeanSwe.PostFork.Model.hasEmbeddedNulStr "a\x00b" = true :=
    hasEmbeddedNulStr_of_get_zero "a\x00b" 1 (by decide) (by decide)
  have hNulDe : LeanSwe.PostFork.Model.hasEmbeddedNulStr "d\x00e" = true :=
    hasEmbeddedNulStr_of_get_zero "d\x00e" 1 (by decide) (by decide)
  have hNulK : LeanSwe.PostFork.Model.hasEmbeddedNulStr "K\x00" = true :=
    hasEmbeddedNulStr_of_get_zero "K\x00" 1 (by decide) (by decide)
  have hNulV : LeanSwe.PostFork.Model.hasEmbeddedNulStr "V\x00" = true :=
    hasEmbeddedNulStr_of_get_zero "V\x00" 1 (by decide) (by decide)
  have hNulX : LeanSwe.PostFork.Model.hasEmbeddedNulStr "x\x00" = true :=
    hasEmbeddedNulStr_of_get_zero "x\x00" 1 (by decide) (by decide)
  have hNulP : LeanSwe.PostFork.Model.hasEmbeddedNulStr "p\x00" = true :=
    hasEmbeddedNulStr_of_get_zero "p\x00" 1 (by decide) (by decide)
  have hNulS : LeanSwe.PostFork.Model.hasEmbeddedNulStr "s\x00" = true :=
    hasEmbeddedNulStr_of_get_zero "s\x00" 1 (by decide) (by decide)
  have hCleanP : LeanSwe.PostFork.Model.hasEmbeddedNulStr "p" = false :=
    hasEmbeddedNulStr_of_forall_ne "p" (by decide)
  have hCleanS : LeanSwe.PostFork.Model.hasEmbeddedNulStr "s" = false :=
    hasEmbeddedNulStr_of_forall_ne "s" (by decide)
  have hCleanK : LeanSwe.PostFork.Model.hasEmbeddedNulStr "K" = false :=
    hasEmbeddedNulStr_of_forall_ne "K" (by decide)
  have hEmpty : ("" : String).isEmpty = true := rfl
  have hEqChr : ("A=B" : String).contains '=' = true := by simp [String.contains_char_eq]
  have hNeg1 : LeanSwe.PostFork.Model.FdRef.isNonneg (FdRef.raw (-1) : FdRef Int32) = false := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      LeanSwe.PostFork.Model.isValidEnvBinding, LeanSwe.PostFork.Model.ArgToken.isValid,
      hasEmbeddedNulStr_true, hNulAb, hNulDe, hNulK, hNulV, hNulX, hNulP, hNulS,
      hCleanP, hCleanS, hCleanK, hEmpty, hEqChr, hNeg1,
      ← _root_.Array.all_toList, List.all_cons, List.all_nil,
      Bool.not_true, Bool.false_and, Bool.and_false]

private theorem spawn_closedRawCloseFilter_ok :
    ∃ stCol,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/true"
          argv := #[]
          closeFds := #[.raw 10, .raw 11, .raw 5, .handle 7] }).run { closedCallerFds := [10, 11] } =
        (.ok { pid := 4242, pgid := none }, stCol) ∧
      stCol.spawnedCloseRefs = #[.raw 5, .handle 7, .handle 10] := by
  let specC : ChildSpecM Int32 :=
    { path := "/bin/true", argv := #[], closeFds := #[.raw 10, .raw 11, .raw 5, .handle 7] }
  let st0 : LeanSwe.PostFork.Model.Internal.HostMockState := { closedCallerFds := [10, 11] }
  let stF := { st0 with callCount := 3 }
  let s1 := { stF with callCount := 4, nextFd := 12, allocRepReadFd := 10 }
  let s2 :=
    { s1 with
      callCount := 5
      hasSpawned := true
      spawnedFlags := LeanSwe.PostFork.Model.flagsOfSpec specC false
      spawnedForkMode := .direct
      spawnedArgv := specC.argv.map LeanSwe.PostFork.Model.Internal.renderMockArgToken
      spawnedEnv := LeanSwe.PostFork.Model.formatEnvEntries specC.env
      spawnedCloseRefs := #[.raw 5, .handle 7, .handle 10] }
  let s3 := { s2 with callCount := 6, closedHandles := [11], closedFds := [11] }
  let s4 := { s3 with callCount := s3.callCount + 0 + 1, readEintrCount := 0 }
  let s5 := { s4 with callCount := s4.callCount + 1, closedHandles := 10 :: s4.closedHandles, closedFds := 10 :: s3.closedFds }
  have hVal : LeanSwe.PostFork.Model.validateSpec specC = true := by
    simp only [specC, LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      hasEmbeddedNulStr_true, LeanSwe.PostFork.Model.FdPolicy.keepFds,
      LeanSwe.PostFork.Model.disjointFdRefArrays, ← _root_.Array.all_toList, ← _root_.Array.any_toList]
    decide
  have hColRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn specC).run st0 =
      (.ok { pid := 4242, pgid := none }, s5) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run st0 = (.ok (), st0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run st0 = (.ok (), st0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFilt :
        (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
          (#[FdRef.raw 10, .raw 11, .raw 5, .handle 7] : _root_.Array (FdRef Int32)).toList #[]).run st0 =
        (#[.raw 5, .handle 7], stF) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFilt]
    have hPipe : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run stF = (.ok (10, 11), s1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hPipe]
    rw [stateT_bind_pure_val]
    dsimp only
    have hFork :
        (Impl.Internal.performFork LeanSwe.PostFork.Model.Internal.mockPosixHostOps
          specC none 11 #[.raw 5, .handle 7] #[.handle 10] false).run s1 = (.ok 4242, s2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFork]
    dsimp only
    have hCloseW : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 11).run s2 = (.ok (), s3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCloseW]
    unfold Impl.Internal.awaitExecOrFailure
    have hRd := readAllRetry_empty 10 0 (by decide) s3 rfl rfl rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
    dsimp only
    have hCloseR : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 10).run s4 = (.ok (), s5) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCloseR]
    have hDec : LeanSwe.PostFork.Model.decodeChildFailure ByteArray.empty = none := rfl
    rw [hDec]
    rfl
  exact ⟨s5, hColRun, rfl⟩

private theorem pipeCleanup_and_busyAbort_ok :
    let busyRaw : LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 :=
      { LeanSwe.PostFork.Model.Internal.mockPosixHostOps with
        closeFd := fun _ => do
          modify fun st => { st with callCount := st.callCount + 1 }
          return .error Errno.EBUSY }
    let epermRaw : LeanSwe.PostFork.Model.Internal.PosixHostOpsM (StateM LeanSwe.PostFork.Model.Internal.HostMockState) Int32 :=
      { LeanSwe.PostFork.Model.Internal.mockPosixHostOps with
        closeFd := fun _ => do
          modify fun st => { st with callCount := st.callCount + 1 }
          return .error Errno.EPERM }
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/true", argv := #[] }).run { failForkErrno := some Errno.EAGAIN } = (.error e, st) ∧
      e.errno = some Errno.EAGAIN ∧ st.closedHandles = [10, 11]) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawnWithBarrier
        { path := "/bin/true", argv := #[] }).run { failNextPipeAt := some 1 } = (.error e, st) ∧
      e.errno = some Errno.EMFILE ∧ st.closedHandles = [10, 11]) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawnWithBarrier
        { path := "/bin/true", argv := #[] }).run { failForkErrno := some Errno.EAGAIN } = (.error e, st) ∧
      e.errno = some Errno.EAGAIN ∧ st.closedHandles = [10, 13, 12, 11]) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/true", argv := #[] }).run { failReadErrno := some Errno.EIO } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.closedHandles = [10, 11] ∧ st.callCount = 5) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/false", argv := #[] }).run
        { readEintrCount := 1
          repWire := LeanSwe.PostFork.Model.encodeFailureReport .execve Errno.ENOENT
          failWaitErrno := some Errno.ECHILD } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.ECHILD ∧ st.closedHandles = [10, 11]) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
        { failWriteErrno := some Errno.EIO, waitResult := .exited 125 } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.closedHandles = [10, 13] ∧ st.callCount = 5) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps busyRaw).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
        { failWriteErrno := some Errno.EIO } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.callCount = 3 ∧ st.closedHandles = []) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps busyRaw).abortBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EBUSY ∧ st.callCount = 1) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
        { allocSyncWriteFd := 13, closedHandles := [10] } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EBADF ∧ st.syncWritten = ByteArray.empty ∧ st.callCount = 1) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
        { failWriteErrno := some 75 } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some 75 ∧ st.callCount = 2 ∧ st.closedHandles = []) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps epermRaw).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run
        { failWriteErrno := some Errno.EIO } = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EIO ∧ st.callCount = 3 ∧ st.closedHandles = []) ∧
    (∃ e st,
      ((Impl.Internal.mkHostOps epermRaw).abortBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} = (.error e, st) ∧
      e.kind = .sysError ∧ e.errno = some Errno.EPERM ∧ st.callCount = 1) := by
  intro busyRaw epermRaw
  have hVal : LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/true", argv := #[] } : ChildSpecM Int32) = true := by
    simp only [LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      hasEmbeddedNulStr_true, LeanSwe.PostFork.Model.FdPolicy.keepFds,
      LeanSwe.PostFork.Model.disjointFdRefArrays, ← _root_.Array.all_toList, ← _root_.Array.any_toList]
    decide
  have hValF : LeanSwe.PostFork.Model.validateSpec ({ path := "/bin/false", argv := #[] } : ChildSpecM Int32) = true := by
    simp only [LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      hasEmbeddedNulStr_false, LeanSwe.PostFork.Model.FdPolicy.keepFds,
      LeanSwe.PostFork.Model.disjointFdRefArrays, ← _root_.Array.all_toList, ← _root_.Array.any_toList]
    decide
  let f0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failForkErrno := some Errno.EAGAIN }
  let f1 : LeanSwe.PostFork.Model.Internal.HostMockState := { f0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  let f2 : LeanSwe.PostFork.Model.Internal.HostMockState := { f1 with callCount := 2 }
  let f3 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { f2 with callCount := 3, closedHandles := [11], closedFds := [11], closedBeforeFork := [11] }
  let f4 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { f3 with callCount := 4, closedHandles := [10, 11], closedFds := [10, 11], closedBeforeFork := [10, 11] }
  have hSpawnForkRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/true", argv := #[] }).run f0 =
      (.error (Impl.Internal.mkSysErr Errno.EAGAIN "fork failed"), f4) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run f0 = (.ok (), f0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run f0 = (.ok (), f0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFC : (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (#[] : _root_.Array (FdRef Int32)).toList #[]).run f0 = (#[], f0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
    have hMp : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run f0 = (.ok (10, 11), f1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp]
    rw [stateT_bind_pure_val]
    dsimp only
    have hFk : (Impl.Internal.performFork LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      { path := "/bin/true", argv := #[] } none 11 #[] #[.handle 10] false).run f1 =
      (.error (Impl.Internal.mkSysErr Errno.EAGAIN "fork failed"), f2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFk]
    have hCl1 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 11).run f2 = (.ok (), f3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl1]
    dsimp only
    have hCl2 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 10).run f3 = (.ok (), f4) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl2]
    rfl
  let s0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failNextPipeAt := some 1 }
  let s1 : LeanSwe.PostFork.Model.Internal.HostMockState := { s0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  let s2 : LeanSwe.PostFork.Model.Internal.HostMockState := { s1 with callCount := 2 }
  let s3 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { s2 with callCount := 4, closedHandles := [10, 11], closedFds := [10, 11], closedBeforeFork := [10, 11] }
  have hPipe2Run :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawnWithBarrier
        { path := "/bin/true", argv := #[] }).run s0 =
      (.error (Impl.Internal.mkSysErr Errno.EMFILE "pipe2 sync-barrier failed"), s3) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run s0 = (.ok (), s0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run s0 = (.ok (), s0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFC : (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (#[] : _root_.Array (FdRef Int32)).toList #[]).run s0 = (#[], s0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
    have hMp1 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run s0 = (.ok (10, 11), s1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp1]
    rw [stateT_bind_pure_val]
    dsimp only
    have hMp2 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run s1 = (.error Errno.EMFILE, s2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp2]
    dsimp only
    have hCl : (Impl.Internal.closeListQuiet LeanSwe.PostFork.Model.Internal.mockPosixHostOps [11, 10]).run s2 = ((), s3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl]
    rfl
  let t0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failForkErrno := some Errno.EAGAIN }
  let t1 : LeanSwe.PostFork.Model.Internal.HostMockState := { t0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  let t2 : LeanSwe.PostFork.Model.Internal.HostMockState := { t1 with callCount := 2, nextFd := 14, allocSyncWriteFd := 13 }
  let t3 : LeanSwe.PostFork.Model.Internal.HostMockState := { t2 with callCount := 3 }
  let t4 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { t3 with callCount := 5, closedHandles := [12, 11], closedFds := [12, 11], closedBeforeFork := [12, 11] }
  let t5 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { t4 with callCount := 7, closedHandles := [10, 13, 12, 11], closedFds := [10, 13, 12, 11], closedBeforeFork := [10, 13, 12, 11] }
  have hForkRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawnWithBarrier
        { path := "/bin/true", argv := #[] }).run t0 =
      (.error (Impl.Internal.mkSysErr Errno.EAGAIN "fork failed"), t5) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run t0 = (.ok (), t0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run t0 = (.ok (), t0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFC : (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (#[] : _root_.Array (FdRef Int32)).toList #[]).run t0 = (#[], t0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
    have hMp1 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run t0 = (.ok (10, 11), t1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp1]
    rw [stateT_bind_pure_val]
    dsimp only
    have hMp2 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run t1 = (.ok (12, 13), t2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp2]
    rw [stateT_bind_pure_val]
    dsimp only
    have hFk : (Impl.Internal.performFork LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      { path := "/bin/true", argv := #[] } (some 12) 11 #[] #[.handle 10, .handle 13] true).run t2 =
      (.error (Impl.Internal.mkSysErr Errno.EAGAIN "fork failed"), t3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFk]
    have hCl1 : (Impl.Internal.closeListQuiet LeanSwe.PostFork.Model.Internal.mockPosixHostOps [11, 12]).run t3 = ((), t4) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl1]
    dsimp only
    have hCl2 : (Impl.Internal.closeListQuiet LeanSwe.PostFork.Model.Internal.mockPosixHostOps [13, 10]).run t4 = ((), t5) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl2]
    rfl
  let rd0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failReadErrno := some Errno.EIO }
  let rd1 : LeanSwe.PostFork.Model.Internal.HostMockState := { rd0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  let rd2 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { rd1 with
      callCount := 2
      hasSpawned := true
      spawnedFlags := LeanSwe.PostFork.Model.flagsOfSpec ({ path := "/bin/true", argv := #[] } : ChildSpecM Int32) false
      spawnedForkMode := .direct
      spawnedArgv := (#[] : _root_.Array (ArgToken Int32)).map LeanSwe.PostFork.Model.Internal.renderMockArgToken
      spawnedEnv := LeanSwe.PostFork.Model.formatEnvEntries #[]
      spawnedCloseRefs := #[.handle 10] }
  let rd3 : LeanSwe.PostFork.Model.Internal.HostMockState := { rd2 with callCount := 3, closedHandles := [11], closedFds := [11] }
  let rd4 : LeanSwe.PostFork.Model.Internal.HostMockState := { rd3 with callCount := 4 }
  let rd5 : LeanSwe.PostFork.Model.Internal.HostMockState := { rd4 with callCount := 5, closedHandles := [10, 11], closedFds := [10, 11] }
  have hReadErrRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/true", argv := #[] }).run rd0 =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host read failed"), rd5) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run rd0 = (.ok (), rd0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run rd0 = (.ok (), rd0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFC : (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (#[] : _root_.Array (FdRef Int32)).toList #[]).run rd0 = (#[], rd0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
    have hMp : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run rd0 = (.ok (10, 11), rd1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp]
    rw [stateT_bind_pure_val]
    dsimp only
    have hFk : (Impl.Internal.performFork LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      { path := "/bin/true", argv := #[] } none 11 #[] #[.handle 10] false).run rd1 = (.ok 4242, rd2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFk]
    dsimp only
    have hClW : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 11).run rd2 = (.ok (), rd3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClW]
    unfold Impl.Internal.awaitExecOrFailure
    have hRdE := readAllRetry_eio 10 rd3 rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hRdE]
    dsimp only
    have hClR : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 10).run rd4 = (.ok (), rd5) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClR]
    rfl
  let wt0 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { readEintrCount := 1
      repWire := LeanSwe.PostFork.Model.encodeFailureReport .execve Errno.ENOENT
      failWaitErrno := some Errno.ECHILD }
  let wt1 : LeanSwe.PostFork.Model.Internal.HostMockState := { wt0 with callCount := 1, nextFd := 12, allocRepReadFd := 10 }
  let wt2 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { wt1 with
      callCount := 2
      hasSpawned := true
      spawnedFlags := LeanSwe.PostFork.Model.flagsOfSpec ({ path := "/bin/false", argv := #[] } : ChildSpecM Int32) false
      spawnedForkMode := .direct
      spawnedArgv := (#[] : _root_.Array (ArgToken Int32)).map LeanSwe.PostFork.Model.Internal.renderMockArgToken
      spawnedEnv := LeanSwe.PostFork.Model.formatEnvEntries #[]
      spawnedCloseRefs := #[.handle 10] }
  let wt3 : LeanSwe.PostFork.Model.Internal.HostMockState := { wt2 with callCount := 3, closedHandles := [11], closedFds := [11] }
  let wt4 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { wt3 with callCount := wt3.callCount + 1 + 4, readEintrCount := 0, repWire := ByteArray.empty }
  let wt5 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { wt4 with callCount := wt4.callCount + 1, closedHandles := [10, 11], closedFds := [10, 11] }
  let wt6 : LeanSwe.PostFork.Model.Internal.HostMockState := { wt5 with callCount := wt5.callCount + 1 }
  have hWaitErrRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).spawn
        { path := "/bin/false", argv := #[] }).run wt0 =
      (.error (Impl.Internal.mkSysErr Errno.ECHILD "waitpid failed"), wt6) := by
    dsimp only [Impl.Internal.mkHostOps]
    simp only [hValF, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hP1 : (Impl.Internal.probeStdioPlan LeanSwe.PostFork.Model.Internal.mockPosixHostOps .inherit).run wt0 = (.ok (), wt0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP1]
    dsimp only
    have hP2 : (Impl.Internal.probeRefList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (LeanSwe.PostFork.Model.FdPolicy.keepFds .inheritNonCloexec).toList).run wt0 = (.ok (), wt0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hP2]
    dsimp only
    have hFC : (Impl.Internal.filterOpenCloseList LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      (#[] : _root_.Array (FdRef Int32)).toList #[]).run wt0 = (#[], wt0) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFC]
    have hMp : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.mkPipeCloexec).run wt0 = (.ok (10, 11), wt1) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hMp]
    rw [stateT_bind_pure_val]
    dsimp only
    have hFk : (Impl.Internal.performFork LeanSwe.PostFork.Model.Internal.mockPosixHostOps
      { path := "/bin/false", argv := #[] } none 11 #[] #[.handle 10] false).run wt1 = (.ok 4242, wt2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hFk]
    dsimp only
    have hClW : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 11).run wt2 = (.ok (), wt3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClW]
    unfold Impl.Internal.awaitExecOrFailure
    have hWire : wt3.repWire = ByteArray.mk #[0x50, 0x01, 7, 0, 2, 0, 0, 0] := rfl
    have hRd := readAllRetry_wire8 10 1 (Or.inl rfl) 0x50 0x01 7 0 2 0 0 0 wt3 rfl rfl rfl rfl hWire
    rw [stateT_bind_pure_pair _ _ _ _ _ hRd]
    dsimp only
    have hClR : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 10).run wt4 = (.ok (), wt5) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClR]
    have hDec : LeanSwe.PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 2, 0, 0, 0]) =
        some { stage := .execve, errno := Errno.ENOENT } := rfl
    rw [hDec]
    dsimp only
    have hWtE := waitRetry_echild 4242 wt5 rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hWtE]
    rfl
  let re0 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { failWriteErrno := some Errno.EIO, waitResult := .exited 125 }
  let reP : LeanSwe.PostFork.Model.Internal.HostMockState := { re0 with callCount := 1 }
  let re1 : LeanSwe.PostFork.Model.Internal.HostMockState := { reP with callCount := 2 }
  let re2 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { re1 with callCount := 3, closedHandles := [13], closedFds := [13], closedBeforeFork := [13] }
  let re3 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { re2 with callCount := 4, closedHandles := [10, 13], closedFds := [10, 13], closedBeforeFork := [10, 13] }
  let re4 : LeanSwe.PostFork.Model.Internal.HostMockState :=
    { re3 with callCount := 4 + 0 + 1, waitEintrCount := 0 }
  have hRelEioRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run re0 =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host write failed"), re4) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hPr : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.probeHandleOpen 10).run re0 = (.ok (), reP) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
    dsimp only
    have hWr := writeAllRetry_eio_raw LeanSwe.PostFork.Model.Internal.mockPosixHostOps rfl 13 reP rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
    dsimp only
    have hNotEp : ((Impl.Internal.mkSysErr Errno.EIO "host write failed").errno == some Errno.EPIPE) = false := by decide
    have hNotEb : Impl.Internal.isFastFailSyncWriteErr (Impl.Internal.mkSysErr Errno.EIO "host write failed").errno = false := by decide
    simp only [hNotEp, hNotEb, Bool.false_eq_true, ↓reduceIte]
    have hCl13 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 13).run re1 = (.ok (), re2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl13]
    dsimp only
    have hCl10 : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.closeFd 10).run re2 = (.ok (), re3) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hCl10]
    have hWt := waitRetry_ok 4242 re3 rfl (by decide)
    rw [stateT_bind_pure_pair _ _ _ _ _ hWt]
    rfl
  let br0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failWriteErrno := some Errno.EIO }
  let brP : LeanSwe.PostFork.Model.Internal.HostMockState := { br0 with callCount := 1 }
  let br1 : LeanSwe.PostFork.Model.Internal.HostMockState := { brP with callCount := 2 }
  let br2 : LeanSwe.PostFork.Model.Internal.HostMockState := { br1 with callCount := 3 }
  have hBusyRelRun :
      ((Impl.Internal.mkHostOps busyRaw).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run br0 =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host write failed"), br2) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hPr : (busyRaw.probeHandleOpen 10).run br0 = (.ok (), brP) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
    dsimp only
    have hWr := writeAllRetry_eio_raw busyRaw rfl 13 brP rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
    dsimp only
    have hNotEp : ((Impl.Internal.mkSysErr Errno.EIO "host write failed").errno == some Errno.EPIPE) = false := by decide
    have hNotEb : Impl.Internal.isFastFailSyncWriteErr (Impl.Internal.mkSysErr Errno.EIO "host write failed").errno = false := by decide
    simp only [hNotEp, hNotEb, Bool.false_eq_true, ↓reduceIte]
    have hClB : (busyRaw.closeFd 13).run br1 = (.error Errno.EBUSY, br2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClB]
    dsimp only
    have hCond : (!Impl.Internal.isKernelCloseDetachNonBadf Errno.EBUSY) = true := by decide
    rw [hCond]
    simp only [↓reduceIte]
    rfl
  have hBusyAbortRun :
      ((Impl.Internal.mkHostOps busyRaw).abortBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} =
      (.error (Impl.Internal.mkSysErr Errno.EBUSY "sync barrier handle already closed or busy"),
        { callCount := 1 }) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hClose : (busyRaw.closeFd 13).run {} = (.error Errno.EBUSY, { callCount := 1 }) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClose]
    dsimp only
    have hCond : (!Impl.Internal.isKernelCloseDetachNonBadf Errno.EBUSY) = true := by decide
    rw [hCond]
    simp only [↓reduceIte]
    rfl
  let ce0 : LeanSwe.PostFork.Model.Internal.HostMockState := { allocSyncWriteFd := 13, closedHandles := [10] }
  let ce1 : LeanSwe.PostFork.Model.Internal.HostMockState := { ce0 with callCount := 1 }
  have hClosedErrReadRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run ce0 =
      (.error (Impl.Internal.mkSysErr Errno.EBADF "failure report handle is not open"), ce1) := rfl
  let ov0 : LeanSwe.PostFork.Model.Internal.HostMockState := { failWriteErrno := some 75 }
  let ovP : LeanSwe.PostFork.Model.Internal.HostMockState := { ov0 with callCount := 1 }
  let ov1 : LeanSwe.PostFork.Model.Internal.HostMockState := { ovP with callCount := 2 }
  have hOvRelRun :
      ((Impl.Internal.mkHostOps LeanSwe.PostFork.Model.Internal.mockPosixHostOps).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run ov0 =
      (.error (Impl.Internal.mkSysErr 75 "host write failed"), ov1) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hPr : (LeanSwe.PostFork.Model.Internal.mockPosixHostOps.probeHandleOpen 10).run ov0 = (.ok (), ovP) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
    dsimp only
    have hWr := writeAllRetry_errno_ne4_raw LeanSwe.PostFork.Model.Internal.mockPosixHostOps rfl 75 (by decide) 13 ovP rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
    dsimp only
    have hNotEp : ((Impl.Internal.mkSysErr 75 "host write failed").errno == some Errno.EPIPE) = false := by decide
    have hFast : Impl.Internal.isFastFailSyncWriteErr (Impl.Internal.mkSysErr 75 "host write failed").errno = true := by decide
    simp only [hNotEp, hFast, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hEpermRelRun :
      ((Impl.Internal.mkHostOps epermRaw).releaseBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run br0 =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host write failed"), br2) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hPr : (epermRaw.probeHandleOpen 10).run br0 = (.ok (), brP) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hPr]
    dsimp only
    have hWr := writeAllRetry_eio_raw epermRaw rfl 13 brP rfl rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hWr]
    dsimp only
    have hNotEp : ((Impl.Internal.mkSysErr Errno.EIO "host write failed").errno == some Errno.EPIPE) = false := by decide
    have hNotEb : Impl.Internal.isFastFailSyncWriteErr (Impl.Internal.mkSysErr Errno.EIO "host write failed").errno = false := by decide
    simp only [hNotEp, hNotEb, Bool.false_eq_true, ↓reduceIte]
    have hClP : (epermRaw.closeFd 13).run br1 = (.error Errno.EPERM, br2) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClP]
    dsimp only
    have hCond : (!Impl.Internal.isKernelCloseDetachNonBadf Errno.EPERM) = true := by decide
    rw [hCond]
    simp only [↓reduceIte]
    rfl
  have hEpermAbortRun :
      ((Impl.Internal.mkHostOps epermRaw).abortBarrier
        { pid := 4242, pgid := none, syncWrite := 13, errRead := 10 }).run {} =
      (.error (Impl.Internal.mkSysErr Errno.EPERM "sync barrier handle already closed or busy"),
        { callCount := 1 }) := by
    dsimp only [Impl.Internal.mkHostOps]
    have hClose : (epermRaw.closeFd 13).run {} = (.error Errno.EPERM, { callCount := 1 }) := rfl
    rw [stateT_bind_pure_pair _ _ _ _ _ hClose]
    dsimp only
    have hCond : (!Impl.Internal.isKernelCloseDetachNonBadf Errno.EPERM) = true := by decide
    rw [hCond]
    simp only [↓reduceIte]
    rfl
  exact ⟨⟨_, f4, hSpawnForkRun, rfl, rfl⟩,
    ⟨_, s3, hPipe2Run, rfl, rfl⟩,
    ⟨_, t5, hForkRun, rfl, rfl⟩,
    ⟨_, rd5, hReadErrRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, wt6, hWaitErrRun, rfl, rfl, rfl⟩,
    ⟨_, re4, hRelEioRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, br2, hBusyRelRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, { callCount := 1 }, hBusyAbortRun, rfl, rfl, rfl⟩,
    ⟨_, ce1, hClosedErrReadRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, ov1, hOvRelRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, br2, hEpermRelRun, rfl, rfl, rfl, rfl⟩,
    ⟨_, { callCount := 1 }, hEpermAbortRun, rfl, rfl, rfl⟩⟩

/-- Kernel proof of `test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter`. -/
theorem test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter_allPass :
    Core.AllPass (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter) := by
  intro syncRead? errWrite stdioRefs closeRefs keepRefs argv specAny
  refine ⟨by decide, by simp [ChildSpecM.ofCommand], by decide,
    validateSpec_eq_validateSpecWith_false specAny,
    validateSpec_hygiene_rejections,
    flattenForkArgs_sizes syncRead? errWrite stdioRefs closeRefs keepRefs argv,
    by decide,
    spawn_closedRawCloseFilter_ok,
    pipeCleanup_and_busyAbort_ok,
    trivial⟩

/-- Witness reachability proof for `test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter`. -/
theorem test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter_canReach :
    Core.CanReach (test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter) := by
  let spec0 : ChildSpecM Int32 := { path := "", argv := #[] }
  have hAll := test_postfork_marshaling_flattenSlotsForkModeAndCloseFilter_allPass none 0 #[] #[] #[] #[] spec0
  exact ⟨none, 0, #[], #[], #[], #[], spec0, hAll⟩

end HostMarshalingAndCloseFilter

section AeneasValidationRefinement

private theorem list_any_congr_mem {α : Type} {xs : List α} {p q : α → Bool}
    (h : ∀ x ∈ xs, p x = q x) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem int32_eq_of_toBitVec_eq {a b : Int32} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a with
  | ofUInt32 u1 =>
    cases u1 with
    | ofBitVec bv1 =>
      cases b with
      | ofUInt32 u2 =>
        cases u2 with
        | ofBitVec bv2 =>
          change bv1 = bv2 at h
          subst h
          rfl

private theorem int32_eq_of_toInt_eq {a b : Int32} (h : a.toInt = b.toInt) : a = b :=
  int32_eq_of_toBitVec_eq (BitVec.eq_of_toInt_eq h)

private theorem specFlagsU32_bits {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) :
    flagSet (specFlagsU32 spec withBarrier) FLAG_SET_PGID = (spec.processGroup == .newGroup) ∧
    flagSet (specFlagsU32 spec withBarrier) FLAG_RESET_SIGPIPE = (spec.sigpipe == .resetDefault) ∧
    flagSet (specFlagsU32 spec withBarrier) FLAG_HAS_SYNC_BARRIER = withBarrier ∧
    flagSet (specFlagsU32 spec withBarrier) FLAG_REDIRECT_STDIO =
      (match spec.stdio with | .redirect .. => true | .inherit => false) ∧
    flagSet (specFlagsU32 spec withBarrier) FLAG_CLOSE_UNKEPT_ABOVE2 =
      (match spec.fdPolicy with | .closeAllAbove2Except _ => true | .inheritNonCloexec _ => false) ∧
    flagSet (specFlagsU32 spec withBarrier) FLAG_CLOSE_STDIO_SOURCES =
      (match spec.stdio, spec.fdPolicy with
       | .redirect _ _ _ true, .inheritNonCloexec _ => true
       | _, _ => false) := by
  dsimp only [specFlagsU32, mkU32, flagSet,
    LeanSwe.PostFork.Model.flagsOfSpec,
    LeanSwe.PostFork.Model.FLAG_SET_PGID,
    LeanSwe.PostFork.Model.FLAG_RESET_SIGPIPE,
    LeanSwe.PostFork.Model.FLAG_HAS_SYNC_BARRIER,
    LeanSwe.PostFork.Model.FLAG_REDIRECT_STDIO,
    LeanSwe.PostFork.Model.FLAG_CLOSE_UNKEPT_ABOVE2,
    LeanSwe.PostFork.Model.FLAG_CLOSE_STDIO_SOURCES,
    FLAG_SET_PGID, FLAG_RESET_SIGPIPE, FLAG_HAS_SYNC_BARRIER,
    FLAG_REDIRECT_STDIO, FLAG_CLOSE_UNKEPT_ABOVE2, FLAG_CLOSE_STDIO_SOURCES]
  cases spec.processGroup <;> cases spec.sigpipe <;> cases withBarrier <;>
    cases spec.stdio with
    | inherit =>
      cases spec.fdPolicy <;> (simp only; decide)
    | redirect _ _ _ closeSrcs =>
      cases closeSrcs <;> cases spec.fdPolicy <;> (simp only; decide)

private theorem rawKeep_foldl_contains_gen {fd : Type}
    (step : Std.HashSet Int32 → FdRef fd → Std.HashSet Int32)
    (hStepRaw : ∀ s m, step s (.raw m) = s.insert m)
    (hStepHdl : ∀ s h, step s (.handle h) = s)
    (xs : List (FdRef fd)) (acc : Std.HashSet Int32) (n : Int32) :
    (xs.foldl step acc).contains n =
      (acc.contains n || xs.any (fun r => match r with | .raw m => n == m | .handle _ => false)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    cases r with
    | raw m =>
      simp only [List.foldl_cons, hStepRaw, List.any_cons, ih, Std.HashSet.contains_insert]
      have hSym : (m == n) = (n == m) := by
        by_cases h : m = n
        · subst h; simp
        · have h' : n ≠ m := Ne.symm h
          simp [h, h']
      rw [hSym]
      cases acc.contains n <;> cases (n == m) <;> simp
    | handle h =>
      simp [List.foldl_cons, hStepHdl, List.any_cons, ih]

private theorem filterMap_handle_any_gen {fd : Type}
    (proj : FdRef fd → Option fd)
    (hProjHdl : ∀ h, proj (.handle h) = some h)
    (hProjRaw : ∀ m, proj (.raw m) = none)
    (xs : List (FdRef fd)) (p : fd → Bool) :
    (xs.filterMap proj).any p =
      xs.any (fun r => match r with | .handle h => p h | .raw _ => false) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    cases r <;> simp [hProjHdl, hProjRaw, List.any_cons, ih]

private theorem ite_false_congr {c1 c2 e1 e2 : Bool} (hc : c1 = c2) (he : e1 = e2) :
    (if c1 = true then false else e1) = (if c2 = true then false else e2) := by
  subst hc
  subst he
  rfl

private theorem disjointFdRefArrays_eq_not_any {fd : Type}
    (eqFd : fd → fd → Bool) (closeFds keepFds : _root_.Array (FdRef fd)) :
    LeanSwe.PostFork.Model.disjointFdRefArrays eqFd closeFds keepFds =
      !(closeFds.any (fun c => keepFds.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd c))) := by
  unfold LeanSwe.PostFork.Model.disjointFdRefArrays
  dsimp (config := { zetaHave := true }) only
  by_cases hSmall : (decide (closeFds.size ≤ 8) || decide (keepFds.size ≤ 8)) = true
  · simp [hSmall]
  · simp only [hSmall, Bool.false_eq_true, ↓reduceIte]
    rw [← _root_.Array.foldl_toList]
    simp only [← _root_.Array.any_toList, _root_.Array.toList_filterMap]
    have hSplit (xs : List (FdRef fd)) :
        (xs.any fun c => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd c)) =
          ((xs.any fun r =>
              match r with
              | .raw n => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw n))
              | .handle _ => false) ||
            (xs.any fun r =>
              match r with
              | .handle ch => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.handle ch))
              | .raw _ => false)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        rw [List.any_cons, List.any_cons, List.any_cons, ih]
        cases x with
        | raw n =>
          dsimp only
          cases (keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw n))) <;>
            cases (xs.any fun r => match r with | .raw m => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw m)) | .handle _ => false) <;>
            cases (xs.any fun r => match r with | .handle ch => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.handle ch)) | .raw _ => false) <;>
            rfl
        | handle ch =>
          dsimp only
          cases (keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.handle ch))) <;>
            cases (xs.any fun r => match r with | .raw m => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw m)) | .handle _ => false) <;>
            cases (xs.any fun r => match r with | .handle c => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.handle c)) | .raw _ => false) <;>
            rfl
    rw [hSplit closeFds.toList]
    refine Eq.trans (b :=
      if (closeFds.toList.any fun r =>
          match r with
          | .raw n => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw n))
          | .handle _ => false) = true then
        false
      else
        !(closeFds.toList.any fun r =>
          match r with
          | .handle ch => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.handle ch))
          | .raw _ => false)) ?_ ?_
    · refine ite_false_congr ?_ ?_
      · refine list_any_congr_mem fun r _ => ?_
        cases r with
        | raw n =>
          dsimp only
          rw [rawKeep_foldl_contains_gen _ (fun _ _ => rfl) (fun _ _ => rfl),
            Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
          refine list_any_congr_mem fun k _ => ?_
          cases k <;> rfl
        | handle _ => rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        congr 1
        rw [filterMap_handle_any_gen _ (fun _ => rfl) (fun _ => rfl)]
        refine list_any_congr_mem fun r _ => ?_
        cases r with
        | raw _ => rfl
        | handle ch =>
          dsimp only
          rw [filterMap_handle_any_gen _ (fun _ => rfl) (fun _ => rfl)]
          refine list_any_congr_mem fun k _ => ?_
          cases k <;> rfl
    · cases (closeFds.toList.any fun r =>
        match r with
        | .raw n => keepFds.toList.any (LeanSwe.PostFork.Model.FdRef.sameRef eqFd (.raw n))
        | .handle _ => false) <;> simp

private theorem specHandlesValid_props
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true) :
    (∀ h, FdRef.handle h ∈ allSpecFdRefs spec → 3 ≤ h.val) ∧
    (∀ h n, FdRef.handle h ∈ allSpecFdRefs spec → FdRef.raw n ∈ allSpecFdRefs spec →
      (h == (⟨n.toBitVec⟩ : I32)) = false) := by
  unfold specHandlesValid at hH
  rw [List.all_eq_true] at hH
  refine ⟨?_, ?_⟩
  · intro h hh
    have hm : h ∈ (allSpecFdRefs spec).filterMap (fun r => match r with | .handle x => some x | .raw _ => none) := by
      rw [List.mem_filterMap]
      exact ⟨.handle h, hh, rfl⟩
    have hp := hH h hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    have h3 : (3#i32).val ≤ h.val := hp.1
    simpa using h3
  · intro h n hh hn
    have hm : h ∈ (allSpecFdRefs spec).filterMap (fun r => match r with | .handle x => some x | .raw _ => none) := by
      rw [List.mem_filterMap]
      exact ⟨.handle h, hh, rfl⟩
    have hnMem : (⟨n.toBitVec⟩ : I32) ∈
        (allSpecFdRefs spec).filterMap (fun r => match r with | .raw m => some (⟨m.toBitVec⟩ : I32) | .handle _ => none) := by
      rw [List.mem_filterMap]
      exact ⟨.raw n, hn, rfl⟩
    have hp := hH h hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    have hAllFalse := List.any_eq_false.mp hp.2 (⟨n.toBitVec⟩ : I32) hnMem
    cases hEq : (h == (⟨n.toBitVec⟩ : I32))
    · rfl
    · simp only [beq_iff_eq] at hEq
      subst hEq
      simp at hAllFalse

private theorem fdRef_sameRef_eq_beq
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    {r1 r2 : FdRef I32}
    (hr1 : r1 ∈ allSpecFdRefs spec) (hr2 : r2 ∈ allSpecFdRefs spec) :
    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) r1 r2 =
      (fdRefToStdI32 r1 == fdRefToStdI32 r2) := by
  obtain ⟨_, hDisj⟩ := specHandlesValid_props hH
  cases r1 with
  | handle h1 =>
    cases r2 with
    | handle h2 => rfl
    | raw n2 =>
      simp only [LeanSwe.PostFork.Model.FdRef.sameRef, fdRefToStdI32]
      exact (hDisj h1 n2 hr1 hr2).symm
  | raw n1 =>
    cases r2 with
    | handle h2 =>
      simp only [LeanSwe.PostFork.Model.FdRef.sameRef, fdRefToStdI32]
      have h := hDisj h2 n1 hr2 hr1
      cases hEq : ((⟨n1.toBitVec⟩ : I32) == h2)
      · rfl
      · simp only [beq_iff_eq] at hEq
        rw [← hEq] at h
        simp at h
    | raw n2 =>
      simp only [LeanSwe.PostFork.Model.FdRef.sameRef, fdRefToStdI32]
      by_cases h : n1 = n2
      · subst h; simp
      · have hNe : (⟨n1.toBitVec⟩ : I32) ≠ ⟨n2.toBitVec⟩ := by
          intro hc
          apply h
          exact int32_eq_of_toBitVec_eq (congrArg IScalar.bv hc)
        simp [h, hNe]

private theorem raw_toBitVec_val (n : Int32) : ((⟨n.toBitVec⟩ : I32).val : Int) = n.toInt :=
  rfl

private theorem fdRef_isNonneg_eq_val
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    {r : FdRef I32} (hr : r ∈ allSpecFdRefs spec) :
    LeanSwe.PostFork.Model.FdRef.isNonneg r = decide (0 ≤ (fdRefToStdI32 r).val) := by
  obtain ⟨hGe3, _⟩ := specHandlesValid_props hH
  cases r with
  | handle h =>
    have h3 := hGe3 h hr
    simp only [LeanSwe.PostFork.Model.FdRef.isNonneg, fdRefToStdI32]
    exact (decide_eq_true (by omega)).symm
  | raw n =>
    simp only [LeanSwe.PostFork.Model.FdRef.isNonneg, fdRefToStdI32, raw_toBitVec_val]
    by_cases hn : 0 ≤ n.toInt <;> simp [hn]

private theorem fdRef_isNonneg_eq_i32Le
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    {r : FdRef I32} (hr : r ∈ allSpecFdRefs spec) :
    LeanSwe.PostFork.Model.FdRef.isNonneg r = decide (0#i32 ≤ fdRefToStdI32 r) := by
  rw [fdRef_isNonneg_eq_val hH hr]
  by_cases hv : 0 ≤ (fdRefToStdI32 r).val
  · have hi : 0#i32 ≤ fdRefToStdI32 r := by scalar_tac
    simp [hv, hi]
  · have hi : ¬ (0#i32 ≤ fdRefToStdI32 r) := by scalar_tac
    simp [hv, hi]

private theorem fdRef_isRawStdioSlot_eq
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    {r : FdRef I32} (hr : r ∈ allSpecFdRefs spec) :
    LeanSwe.PostFork.Model.FdRef.isRawStdioSlot r =
      (decide (0 ≤ (fdRefToStdI32 r).val) && decide ((fdRefToStdI32 r).val ≤ 2)) := by
  obtain ⟨hGe3, _⟩ := specHandlesValid_props hH
  cases r with
  | handle h =>
    have h3 := hGe3 h hr
    simp only [LeanSwe.PostFork.Model.FdRef.isRawStdioSlot, fdRefToStdI32]
    have hNle : ¬ ((h : Int) ≤ 2) := by omega
    simp [hNle]
  | raw n =>
    simp only [LeanSwe.PostFork.Model.FdRef.isRawStdioSlot, fdRefToStdI32, raw_toBitVec_val]
    have h0 : (n == 0) = decide (n.toInt = 0) := by
      by_cases h : n = 0
      · subst h; simp
      · have hne : n.toInt ≠ 0 := fun hc => h (int32_eq_of_toInt_eq hc)
        simp [h, hne]
    have h1 : (n == 1) = decide (n.toInt = 1) := by
      by_cases h : n = 1
      · subst h; simp
      · have hne : n.toInt ≠ 1 := fun hc => h (int32_eq_of_toInt_eq hc)
        simp [h, hne]
    have h2 : (n == 2) = decide (n.toInt = 2) := by
      by_cases h : n = 2
      · subst h; simp
      · have hne : n.toInt ≠ 2 := fun hc => h (int32_eq_of_toInt_eq hc)
        simp [h, hne]
    rw [h0, h1, h2]
    by_cases ha : 0 ≤ n.toInt ∧ n.toInt ≤ 2
    · rcases ha with ⟨_, _⟩
      have hCases : n.toInt = 0 ∨ n.toInt = 1 ∨ n.toInt = 2 := by omega
      rcases hCases with hc | hc | hc <;> simp [hc]
    · have hN0 : n.toInt ≠ 0 := by omega
      have hN1 : n.toInt ≠ 1 := by omega
      have hN2 : n.toInt ≠ 2 := by omega
      by_cases hb : 0 ≤ n.toInt
      · have hb2 : ¬ (n.toInt ≤ 2) := by omega
        simp [hN0, hN1, hN2, hb, hb2]
      · simp [hN0, hN1, hN2, hb]

private theorem mem_allSpecFdRefs_close {fd : Type} {spec : ChildSpecM fd} {r : FdRef fd}
    (hr : r ∈ spec.closeFds.toList) : r ∈ allSpecFdRefs spec := by
  unfold allSpecFdRefs
  exact List.mem_append_left _ (List.mem_append_right _ hr)

private theorem mem_allSpecFdRefs_keep {fd : Type} {spec : ChildSpecM fd} {r : FdRef fd}
    (hr : r ∈ (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList) :
    r ∈ allSpecFdRefs spec := by
  unfold allSpecFdRefs
  exact List.mem_append_right _ hr

private theorem i32_beq_iff_val_eq (a b : I32) : (a == b) = (a.val == b.val) := by
  by_cases h : a = b
  · subst h; simp
  · have hv : a.val ≠ b.val := fun hc => h (IScalar.eq_of_val_eq hc)
    simp [h, hv]

private theorem sliceContainsNonneg_map_eq
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    {arr : _root_.Array (FdRef I32)}
    (hSub : ∀ r ∈ arr.toList, r ∈ allSpecFdRefs spec)
    {target : FdRef I32} (hT : target ∈ allSpecFdRefs spec)
    (hNonneg : LeanSwe.PostFork.Model.FdRef.isNonneg target = true) :
    sliceContainsNonnegSpec (arr.map fdRefToStdI32).toList (fdRefToStdI32 target).val =
      arr.any (fun x => LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) x target) := by
  unfold sliceContainsNonnegSpec
  have hTVal := fdRef_isNonneg_eq_val hH hT
  rw [hNonneg] at hTVal
  rw [← hTVal, Bool.true_and, ← _root_.Array.any_toList, _root_.Array.toList_map, List.any_map]
  refine list_any_congr_mem fun x hx => ?_
  dsimp only [Function.comp]
  rw [← i32_beq_iff_val_eq, ← fdRef_sameRef_eq_beq hH (hSub x hx) hT]

private theorem slicesOverlapNonneg_eq_any
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    (hClosePos : spec.closeFds.all LeanSwe.PostFork.Model.FdRef.isNonneg = true) :
    slicesOverlapNonnegSpec
        (spec.closeFds.map fdRefToStdI32).toList
        ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).map fdRefToStdI32).toList =
      spec.closeFds.any (fun c =>
        (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
          (LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) c)) := by
  unfold slicesOverlapNonnegSpec
  rw [← _root_.Array.any_toList, _root_.Array.toList_map, List.any_map]
  rw [← _root_.Array.all_toList, List.all_eq_true] at hClosePos
  refine list_any_congr_mem fun c hc => ?_
  dsimp only [Function.comp]
  have hcMem := mem_allSpecFdRefs_close hc
  have hcPos := hClosePos c hc
  have hcVal := fdRef_isNonneg_eq_val hH hcMem
  rw [hcPos] at hcVal
  rw [← hcVal, Bool.true_and]
  rw [sliceContainsNonneg_map_eq hH (fun k hk => mem_allSpecFdRefs_keep hk) hcMem hcPos]
  simp only [← _root_.Array.any_toList]
  refine list_any_congr_mem fun k hk => ?_
  rw [fdRef_sameRef_eq_beq hH (mem_allSpecFdRefs_keep hk) hcMem,
    fdRef_sameRef_eq_beq hH hcMem (mem_allSpecFdRefs_keep hk)]
  by_cases hEq : fdRefToStdI32 k = fdRefToStdI32 c
  · rw [hEq]
  · have hNe : fdRefToStdI32 c ≠ fdRefToStdI32 k := Ne.symm hEq
    simp [hEq, hNe]

private theorem sliceHasStdioSlot_keep_eq
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true) :
    sliceHasStdioSlotSpec
        ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).map fdRefToStdI32).toList =
      (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
        LeanSwe.PostFork.Model.FdRef.isRawStdioSlot := by
  unfold sliceHasStdioSlotSpec
  rw [← _root_.Array.any_toList, _root_.Array.toList_map, List.any_map]
  refine list_any_congr_mem fun k hk => ?_
  dsimp only [Function.comp]
  exact (fdRef_isRawStdioSlot_eq hH (mem_allSpecFdRefs_keep hk)).symm

private theorem keep_gt2_check_eq
    {spec : ChildSpecM I32} (hH : specHandlesValid spec = true)
    (hNoStdioKeep :
      ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
        LeanSwe.PostFork.Model.FdRef.isRawStdioSlot) = false)
    {sRef : FdRef I32} (hsMem : sRef ∈ allSpecFdRefs spec)
    (hsPos : LeanSwe.PostFork.Model.FdRef.isNonneg sRef = true) :
    (!decide (fdRefToStdI32 sRef > 2#i32) ||
      !sliceContainsNonnegSpec
        ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).map fdRefToStdI32).toList
        (fdRefToStdI32 sRef).val) =
    !((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sRef)) := by
  rw [sliceContainsNonneg_map_eq hH (fun k hk => mem_allSpecFdRefs_keep hk) hsMem hsPos]
  simp only [← _root_.Array.any_toList] at hNoStdioKeep ⊢
  have hSimpl :
      ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList.any (fun k =>
        (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
        LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sRef)) =
      ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList.any (fun k =>
        LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sRef)) := by
    refine list_any_congr_mem fun k hk => ?_
    have hkF := List.any_eq_false.mp hNoStdioKeep k hk
    simp [hkF]
  rw [hSimpl]
  by_cases hGt : fdRefToStdI32 sRef > 2#i32
  · simp [hGt]
  · simp only [hGt, decide_false, Bool.not_false, Bool.true_or]
    suffices hNone :
        ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList.any (fun k =>
          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sRef)) = false by
      simp [hNone]
    rw [List.any_eq_false]
    intro k hk
    have hkF := List.any_eq_false.mp hNoStdioKeep k hk
    rw [fdRef_isRawStdioSlot_eq hH (mem_allSpecFdRefs_keep hk)] at hkF
    rw [fdRef_sameRef_eq_beq hH (mem_allSpecFdRefs_keep hk) hsMem]
    by_cases hEq : fdRefToStdI32 k = fdRefToStdI32 sRef
    · exfalso
      rw [hEq] at hkF
      have hsVal := fdRef_isNonneg_eq_val hH hsMem
      rw [hsPos] at hsVal
      have h0 : 0 ≤ (fdRefToStdI32 sRef).val := of_decide_eq_true hsVal.symm
      have hle2 : (fdRefToStdI32 sRef).val ≤ 2 := by scalar_tac
      simp [h0, hle2] at hkF
    · simp [hEq]

private def isOkUnit (r : core.result.Result Unit I32) : Bool :=
  match r with
  | .Ok () => true
  | .Err _ => false

/-- Kernel proof of `test_postfork_aeneasRefinement_flagsAndValidateChildArgs` for `rustAeneasApi`. -/
theorem test_postfork_aeneasRefinement_flagsAndValidateChildArgs_allPass :
    Core.AllPass (test_postfork_aeneasRefinement_flagsAndValidateChildArgs rustAeneasApi) := by
  dsimp only [Core.AllPass, test_postfork_aeneasRefinement_flagsAndValidateChildArgs]
  intro spec withBarrier syncR repW closeSlice keepSlice
  dsimp (config := { zetaHave := true }) only
  have hFlValid := flagsOfSpec_always_valid spec withBarrier
  obtain ⟨hB0, hB1, hB2, hB3, hB4, hB5⟩ := specFlagsU32_bits spec withBarrier
  have hBadSpec :
      LeanSwe.PostFork.Model.validateSpec
        ({ path := "/bin/true"
           argv := #[]
           stdio := .redirect (.raw 5) (.raw 1) (.raw 2) true
           fdPolicy := .inheritNonCloexec #[.raw 5] } : ChildSpecM Int32) = false := by
    simp only [LeanSwe.PostFork.Model.validateSpec, LeanSwe.PostFork.Model.validateSpecWith,
      hasEmbeddedNulStr_true, LeanSwe.PostFork.Model.FdPolicy.keepFds,
      LeanSwe.PostFork.Model.disjointFdRefArrays, ← _root_.Array.all_toList, ← _root_.Array.any_toList]
    decide
  have hB3Goal :
      (flagSet (specFlagsU32 spec withBarrier) FLAG_REDIRECT_STDIO =
        match spec.stdio with | .redirect .. => true | .inherit => false) := by
    cases hs : spec.stdio <;> simpa [hs] using hB3
  have hB4Goal :
      (flagSet (specFlagsU32 spec withBarrier) FLAG_CLOSE_UNKEPT_ABOVE2 =
        match spec.fdPolicy with | .closeAllAbove2Except _ => true | .inheritNonCloexec _ => false) := by
    cases hf : spec.fdPolicy <;> simpa [hf] using hB4
  have hB5Goal :
      (flagSet (specFlagsU32 spec withBarrier) FLAG_CLOSE_STDIO_SOURCES =
        match spec.stdio, spec.fdPolicy with
        | .redirect _ _ _ true, .inheritNonCloexec _ => true
        | _, _ => false) := by
    cases hs : spec.stdio with
    | inherit => cases hf : spec.fdPolicy <;> simpa [hs, hf] using hB5
    | redirect _ _ _ cs => cases cs <;> cases hf : spec.fdPolicy <;> simpa [hs, hf] using hB5
  refine ⟨hFlValid, hB0, hB1, hB2, hB3Goal, hB4Goal, hB5Goal, hBadSpec, ?_⟩
  rintro ⟨hStr, hHandles, hClosePos, hKeepPos, hCloseEq, hKeepEq, hPipes⟩
  have hStrParts := hStr
  unfold specStringHygieneOk at hStrParts
  dsimp (config := { zetaHave := true }) only at hStrParts
  simp only [Bool.and_eq_true] at hStrParts
  rcases hStrParts with ⟨⟨⟨⟨hPath1, hPath2⟩, hCwdOk⟩, hArgvOk⟩, hEnvOk⟩
  have hSpec :=
    validate_child_args_spec
      (specFlagsU32 spec withBarrier)
      syncR
      (stdioToStdI32Triple spec.stdio).1
      (stdioToStdI32Triple spec.stdio).2.1
      (stdioToStdI32Triple spec.stdio).2.2
      repW closeSlice keepSlice
  rcases hSpec with ⟨res, hResOk, hResPost⟩
  have hEqGoal :
      isOkUnit res = LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec := by
    simp only [hFlValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hResPost
    unfold internalPipesDisjoint at hPipes
    simp only [Bool.and_eq_true] at hPipes
    rcases hPipes with ⟨⟨⟨⟨_, hRepClose⟩, hRepKeep⟩, hSyncDisj⟩, hRedirPipes⟩
    have hSignSync :
        (!(flagSet (specFlagsU32 spec withBarrier) FLAG_HAS_SYNC_BARRIER) || decide (0#i32 ≤ syncR)) = true := by
      rw [hB2]
      cases withBarrier with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hSyncDisj ⊢
        exact hSyncDisj.1.1.1
    have hSyncOvl :
        (!(flagSet (specFlagsU32 spec withBarrier) FLAG_HAS_SYNC_BARRIER) ||
          (repW != syncR &&
            !sliceContainsNonnegSpec closeSlice.val syncR.val &&
            !sliceContainsNonnegSpec keepSlice.val syncR.val)) = true := by
      rw [hB2]
      cases withBarrier with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hSyncDisj ⊢
        exact ⟨⟨hSyncDisj.1.1.2, hSyncDisj.1.2⟩, hSyncDisj.2⟩
    have hDisjEq :
        (!slicesOverlapNonnegSpec closeSlice.val keepSlice.val) =
          LeanSwe.PostFork.Model.disjointFdRefArrays (· == ·)
            spec.closeFds (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy) := by
      rw [hCloseEq, hKeepEq, slicesOverlapNonneg_eq_any hHandles hClosePos, disjointFdRefArrays_eq_not_any]
    cases hStdio : spec.stdio with
    | inherit =>
      have hRedirF : flagSet (specFlagsU32 spec withBarrier) FLAG_REDIRECT_STDIO = false := by
        simpa [hStdio] using hB3
      have hSigns :
          validSignsSpec (specFlagsU32 spec withBarrier) syncR
            (stdioToStdI32Triple spec.stdio).1
            (stdioToStdI32Triple spec.stdio).2.1
            (stdioToStdI32Triple spec.stdio).2.2 = true := by
        unfold validSignsSpec
        rw [hSignSync, Bool.true_and, hRedirF]
        rfl
      simp only [hSigns, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hResPost
      have hNoOvl :
          validRunChildNoOverlap (specFlagsU32 spec withBarrier) syncR
            (stdioToStdI32Triple spec.stdio).1
            (stdioToStdI32Triple spec.stdio).2.1
            (stdioToStdI32Triple spec.stdio).2.2
            repW closeSlice.val keepSlice.val =
          (!slicesOverlapNonnegSpec closeSlice.val keepSlice.val) := by
        unfold validRunChildNoOverlap
        simp [hRepClose, hRepKeep, hSyncOvl, hRedirF]
      have hModelEq :
          LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec =
            LeanSwe.PostFork.Model.disjointFdRefArrays (· == ·)
              spec.closeFds (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy) := by
        unfold LeanSwe.PostFork.Model.validateSpecWith
        dsimp (config := { zetaHave := true }) only
        rw [hStdio]
        cases hc : spec.cwd with
        | none => simp [hPath1, hPath2, hArgvOk, hEnvOk, hClosePos, hKeepPos]
        | some dir =>
          have hcOk : (!LeanSwe.PostFork.Model.hasEmbeddedNulStr dir) = true := by
            simpa [hc] using hCwdOk
          simp [hPath1, hPath2, hcOk, hArgvOk, hEnvOk, hClosePos, hKeepPos]
      rw [hModelEq, ← hDisjEq, ← hNoOvl]
      cases hV : validRunChildNoOverlap (specFlagsU32 spec withBarrier) syncR
        (stdioToStdI32Triple spec.stdio).1
        (stdioToStdI32Triple spec.stdio).2.1
        (stdioToStdI32Triple spec.stdio).2.2
        repW closeSlice.val keepSlice.val
      · simp [hV] at hResPost
        rw [hResPost]; rfl
      · simp [hV] at hResPost
        rw [hResPost]; rfl
    | redirect sIn sOut sErr closeSrcs =>
      have hRedirT : flagSet (specFlagsU32 spec withBarrier) FLAG_REDIRECT_STDIO = true := by
        simpa [hStdio] using hB3
      have hsInMem : sIn ∈ allSpecFdRefs spec := by
        unfold allSpecFdRefs; simp [hStdio]
      have hsOutMem : sOut ∈ allSpecFdRefs spec := by
        unfold allSpecFdRefs; simp [hStdio]
      have hsErrMem : sErr ∈ allSpecFdRefs spec := by
        unfold allSpecFdRefs; simp [hStdio]
      have hTrEq :
          stdioToStdI32Triple spec.stdio =
            (fdRefToStdI32 sIn, fdRefToStdI32 sOut, fdRefToStdI32 sErr) := by
        simp [hStdio, stdioToStdI32Triple]
      rw [hTrEq] at hResPost
      dsimp only at hResPost
      have hSignsEq :
          validSignsSpec (specFlagsU32 spec withBarrier) syncR
            (fdRefToStdI32 sIn) (fdRefToStdI32 sOut) (fdRefToStdI32 sErr) =
          (LeanSwe.PostFork.Model.FdRef.isNonneg sIn &&
            LeanSwe.PostFork.Model.FdRef.isNonneg sOut &&
            LeanSwe.PostFork.Model.FdRef.isNonneg sErr) := by
        unfold validSignsSpec
        rw [hSignSync, Bool.true_and, hRedirT, Bool.not_true, Bool.false_or,
          ← fdRef_isNonneg_eq_i32Le hHandles hsInMem,
          ← fdRef_isNonneg_eq_i32Le hHandles hsOutMem,
          ← fdRef_isNonneg_eq_i32Le hHandles hsErrMem]
      by_cases hStdioPos :
          (LeanSwe.PostFork.Model.FdRef.isNonneg sIn &&
            LeanSwe.PostFork.Model.FdRef.isNonneg sOut &&
            LeanSwe.PostFork.Model.FdRef.isNonneg sErr) = true
      · rw [hSignsEq] at hResPost
        simp only [hStdioPos, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hResPost
        have hPosParts := hStdioPos
        simp only [Bool.and_eq_true] at hPosParts
        rcases hPosParts with ⟨⟨hsInPos, hsOutPos⟩, hsErrPos⟩
        simp only [hStdio, stdioToStdI32Triple, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hRedirPipes
        rcases hRedirPipes with ⟨hRepNotStdio, hSyncNotStdio⟩
        have hSyncStdioFlag :
            (!(flagSet (specFlagsU32 spec withBarrier) FLAG_HAS_SYNC_BARRIER) ||
              !fdInStdioSpec syncR (fdRefToStdI32 sIn) (fdRefToStdI32 sOut) (fdRefToStdI32 sErr)) = true := by
          rw [hB2]
          exact hSyncNotStdio
        have hKeepSlotEq := sliceHasStdioSlot_keep_eq hHandles
        rw [← hKeepEq] at hKeepSlotEq
        have hStdioInCloseEq :
            stdioInSliceSpec closeSlice.val
              (fdRefToStdI32 sIn) (fdRefToStdI32 sOut) (fdRefToStdI32 sErr) =
            spec.closeFds.any (fun c =>
              LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) c sIn ||
              LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) c sOut ||
              LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) c sErr) := by
          unfold stdioInSliceSpec
          rw [hCloseEq,
            sliceContainsNonneg_map_eq hHandles (fun c hc => mem_allSpecFdRefs_close hc) hsInMem hsInPos,
            sliceContainsNonneg_map_eq hHandles (fun c hc => mem_allSpecFdRefs_close hc) hsOutMem hsOutPos,
            sliceContainsNonneg_map_eq hHandles (fun c hc => mem_allSpecFdRefs_close hc) hsErrMem hsErrPos]
          simp only [← _root_.Array.any_toList]
          induction spec.closeFds.toList with
          | nil => rfl
          | cons x xs ih =>
            simp only [List.any_cons]
            rw [← ih]
            cases LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) x sIn <;>
              cases LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) x sOut <;>
              cases LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) x sErr <;>
              simp [Bool.or_assoc, Bool.or_comm]
        have hOvlEq :
            validRunChildNoOverlap (specFlagsU32 spec withBarrier) syncR
              (fdRefToStdI32 sIn) (fdRefToStdI32 sOut) (fdRefToStdI32 sErr)
              repW closeSlice.val keepSlice.val =
            LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec := by
          unfold validRunChildNoOverlap LeanSwe.PostFork.Model.validateSpecWith
          dsimp (config := { zetaHave := true }) only
          cases hc : spec.cwd with
          | none =>
            simp only [hPath1, hPath2, hArgvOk, hEnvOk, hClosePos, hKeepPos,
              hStdio, hsInPos, hsOutPos, hsErrPos,
              Bool.true_and, hRepClose, hRepKeep, hSyncOvl, hRedirT, Bool.not_true,
              Bool.false_or, hRepNotStdio, hSyncStdioFlag, hKeepSlotEq, hStdioInCloseEq, hDisjEq]
            by_cases hKeepHasStdio :
                ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
                  LeanSwe.PostFork.Model.FdRef.isRawStdioSlot) = true
            · simp [hKeepHasStdio]
            · have hKeepNoStdio :
                  ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
                    LeanSwe.PostFork.Model.FdRef.isRawStdioSlot) = false :=
                Bool.eq_false_iff.mpr hKeepHasStdio
              simp only [hKeepNoStdio, Bool.not_false, Bool.true_and]
              rw [hKeepEq,
                keep_gt2_check_eq hHandles hKeepNoStdio hsInMem hsInPos,
                keep_gt2_check_eq hHandles hKeepNoStdio hsOutMem hsOutPos,
                keep_gt2_check_eq hHandles hKeepNoStdio hsErrMem hsErrPos]
              have hJoinKeep :
                  (!(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) &&
                    !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) &&
                    !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) =
                  !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                    (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    (LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn ||
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut ||
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) := by
                simp only [← _root_.Array.any_toList]
                induction (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList with
                | nil => rfl
                | cons k ks ih =>
                  simp only [List.any_cons, Bool.not_or]
                  have hDist :
                      ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                        (LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn ||
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut ||
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) =
                      (((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) ||
                        ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) ||
                        ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) := by
                    cases (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) <;> simp
                  rw [hDist, Bool.not_or, Bool.not_or, ← ih]
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) <;>
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) <;>
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr) <;>
                  simp [Bool.and_assoc, Bool.and_comm]
              rw [hJoinKeep, hB5, hStdio]
              cases spec.fdPolicy <;> cases closeSrcs <;> dsimp only <;>
                cases (LeanSwe.PostFork.Model.disjointFdRefArrays (· == ·) spec.closeFds _) <;>
                cases (spec.closeFds.any _) <;>
                try (cases ((LeanSwe.PostFork.Model.FdPolicy.keepFds _).any _)) <;>
                rfl
          | some dir =>
            have hcOk : (!LeanSwe.PostFork.Model.hasEmbeddedNulStr dir) = true := by
              simpa [hc] using hCwdOk
            simp only [hcOk, hPath1, hPath2, hArgvOk, hEnvOk, hClosePos, hKeepPos,
              hStdio, hsInPos, hsOutPos, hsErrPos,
              Bool.true_and, hRepClose, hRepKeep, hSyncOvl, hRedirT, Bool.not_true,
              Bool.false_or, hRepNotStdio, hSyncStdioFlag, hKeepSlotEq, hStdioInCloseEq, hDisjEq]
            by_cases hKeepHasStdio :
                ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
                  LeanSwe.PostFork.Model.FdRef.isRawStdioSlot) = true
            · simp [hKeepHasStdio]
            · have hKeepNoStdio :
                  ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any
                    LeanSwe.PostFork.Model.FdRef.isRawStdioSlot) = false :=
                Bool.eq_false_iff.mpr hKeepHasStdio
              simp only [hKeepNoStdio, Bool.not_false, Bool.true_and]
              rw [hKeepEq,
                keep_gt2_check_eq hHandles hKeepNoStdio hsInMem hsInPos,
                keep_gt2_check_eq hHandles hKeepNoStdio hsOutMem hsOutPos,
                keep_gt2_check_eq hHandles hKeepNoStdio hsErrMem hsErrPos]
              have hJoinKeep :
                  (!(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) &&
                    !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) &&
                    !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                      (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) =
                  !(LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).any (fun k =>
                    (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    (LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn ||
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut ||
                      LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) := by
                simp only [← _root_.Array.any_toList]
                induction (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList with
                | nil => rfl
                | cons k ks ih =>
                  simp only [List.any_cons, Bool.not_or]
                  have hDist :
                      ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                        (LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn ||
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut ||
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) =
                      (((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) ||
                        ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) ||
                        ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                          LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr)) := by
                    cases (!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) <;> simp
                  rw [hDist, Bool.not_or, Bool.not_or, ← ih]
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sIn) <;>
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sOut) <;>
                  cases ((!LeanSwe.PostFork.Model.FdRef.isRawStdioSlot k) &&
                    LeanSwe.PostFork.Model.FdRef.sameRef (· == ·) k sErr) <;>
                  simp [Bool.and_assoc, Bool.and_comm]
              rw [hJoinKeep, hB5, hStdio]
              cases spec.fdPolicy <;> cases closeSrcs <;> dsimp only <;>
                cases (LeanSwe.PostFork.Model.disjointFdRefArrays (· == ·) spec.closeFds _) <;>
                cases (spec.closeFds.any _) <;>
                try (cases ((LeanSwe.PostFork.Model.FdPolicy.keepFds _).any _)) <;>
                rfl
        rw [← hOvlEq]
        cases hV : validRunChildNoOverlap (specFlagsU32 spec withBarrier) syncR
          (fdRefToStdI32 sIn) (fdRefToStdI32 sOut) (fdRefToStdI32 sErr)
          repW closeSlice.val keepSlice.val
        · simp [hV] at hResPost
          rw [hResPost]; rfl
        · simp [hV] at hResPost
          rw [hResPost]; rfl
      · have hStdioPosF :
            (LeanSwe.PostFork.Model.FdRef.isNonneg sIn &&
              LeanSwe.PostFork.Model.FdRef.isNonneg sOut &&
              LeanSwe.PostFork.Model.FdRef.isNonneg sErr) = false :=
          Bool.eq_false_iff.mpr hStdioPos
        rw [hSignsEq, hStdioPosF] at hResPost
        simp only [Bool.not_false, ↓reduceIte] at hResPost
        have hModelF : LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec = false := by
          unfold LeanSwe.PostFork.Model.validateSpecWith
          dsimp (config := { zetaHave := true }) only
          rw [hStdio]
          cases hsIn : LeanSwe.PostFork.Model.FdRef.isNonneg sIn <;>
            cases hsOut : LeanSwe.PostFork.Model.FdRef.isNonneg sOut <;>
            cases hsErr : LeanSwe.PostFork.Model.FdRef.isNonneg sErr
          all_goals simp_all
        rw [hResPost, hModelF]; rfl
  have hOkPost :
      OkPost
        (rustAeneasApi.validateChildArgs
          { flags := specFlagsU32 spec withBarrier
            sync_r := syncR
            stdin_fd := (stdioToStdI32Triple spec.stdio).1
            stdout_fd := (stdioToStdI32Triple spec.stdio).2.1
            stderr_fd := (stdioToStdI32Triple spec.stdio).2.2
            rep_w := repW }
          closeSlice keepSlice)
        (fun r =>
          (match r with | .Ok () => true | .Err _ => false) =
            LeanSwe.PostFork.Model.validateSpecWith (· == ·) spec) :=
    ⟨res, hResOk, hEqGoal⟩
  cases hs : spec.stdio <;>
    (simp only [hs, stdioToStdI32Triple] at hOkPost; exact ⟨hOkPost, trivial⟩)

/-- Witness reachability proof for `test_postfork_aeneasRefinement_flagsAndValidateChildArgs` exercising `withBarrier = true`, redirected `.handle` + `.raw` stdio, `closeFds`, and `keepFds`. -/
theorem test_postfork_aeneasRefinement_flagsAndValidateChildArgs_canReach :
    Core.CanReach (test_postfork_aeneasRefinement_flagsAndValidateChildArgs rustAeneasApi) := by
  let spec0 : ChildSpecM I32 :=
    { path := "/bin/true"
      argv := #[]
      stdio := .redirect (.handle 4#i32) (.raw 1) (.raw 2) true
      fdPolicy := .inheritNonCloexec #[.handle 8#i32]
      closeFds := #[.handle 6#i32]
      processGroup := .newGroup }
  let closeSl : Slice I32 := mkSliceI32 1#usize [6#i32]
  let keepSl : Slice I32 := mkSliceI32 1#usize [8#i32]
  have hAll :=
    test_postfork_aeneasRefinement_flagsAndValidateChildArgs_allPass
      spec0 true 9#i32 10#i32 closeSl keepSl
  dsimp only [Core.CanReach, test_postfork_aeneasRefinement_flagsAndValidateChildArgs]
  have hPre :
      specStringHygieneOk spec0 = true ∧
      specHandlesValid spec0 = true ∧
      spec0.closeFds.all LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      (LeanSwe.PostFork.Model.FdPolicy.keepFds spec0.fdPolicy).all
        LeanSwe.PostFork.Model.FdRef.isNonneg = true ∧
      closeSl.val = (spec0.closeFds.map fdRefToStdI32).toList ∧
      keepSl.val = ((LeanSwe.PostFork.Model.FdPolicy.keepFds spec0.fdPolicy).map fdRefToStdI32).toList ∧
      internalPipesDisjoint true true 9#i32 4#i32 (⟨(1 : Int32).toBitVec⟩ : I32)
        (⟨(2 : Int32).toBitVec⟩ : I32) 10#i32 closeSl.val keepSl.val = true := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [spec0, specStringHygieneOk, hasEmbeddedNulStr_true]
    · simp only [spec0, specHandlesValid, allSpecFdRefs, LeanSwe.PostFork.Model.FdPolicy.keepFds]
      decide
    · simp only [spec0, ← _root_.Array.all_toList]
      decide
    · simp only [spec0, LeanSwe.PostFork.Model.FdPolicy.keepFds, ← _root_.Array.all_toList]
      decide
    · simp [spec0, closeSl, mkSliceI32, Array.to_slice, Array.make, fdRefToStdI32]
    · simp [spec0, keepSl, mkSliceI32, Array.to_slice, Array.make,
        LeanSwe.PostFork.Model.FdPolicy.keepFds, fdRefToStdI32]
    · simp only [closeSl, keepSl, mkSliceI32, Array.to_slice, Array.make, internalPipesDisjoint,
        sliceContainsNonnegSpec, fdInStdioSpec]
      decide
  refine ⟨spec0, true, 9#i32, 10#i32, closeSl, keepSl,
    hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    hAll.2.2.2.2.2.1, hAll.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.1,
    hPre, hAll.2.2.2.2.2.2.2.2 hPre⟩

end AeneasValidationRefinement

end LeanSwe.PostFork.Proofs

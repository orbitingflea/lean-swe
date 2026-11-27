import LeanSwe.PostFork.Interface
import LeanSwe.PostFork.Impl
import LeanSweProofs.PostFork.SpecTests

/-!
Foundation lemmas for `LeanSwe.PostFork.Impl.Internal.mkHostOps` on
`LeanSwe.PostFork.mockPosixHostOps`, plus `NoThrowOps` / error-kind invariant
lemmas for `LeanSwe.PostFork` host operations.
-/

namespace LeanSwe.PostFork.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.Model
open LeanSwe.PostFork.Impl
open LeanSwe.PostFork.Impl.Internal

/-- Predicate stating that all operations of `raw` in `IO` terminate without throwing an `IO.Error`. -/
structure NoThrowOps (raw : PosixHostOpsM IO RawFd) : Prop where
  /-- `probeFdOpen` never throws an `IO.Error`. -/
  probeFdOpen_ok : ∀ n w, ∃ r w', raw.probeFdOpen n w = .ok r w'
  /-- `probeHandleOpen` never throws an `IO.Error`. -/
  probeHandleOpen_ok : ∀ h w, ∃ r w', raw.probeHandleOpen h w = .ok r w'
  /-- `mkPipeCloexec` never throws an `IO.Error`. -/
  mkPipeCloexec_ok : ∀ w, ∃ r w', raw.mkPipeCloexec w = .ok r w'
  /-- `closeFd` never throws an `IO.Error`. -/
  closeFd_ok : ∀ h w, ∃ r w', raw.closeFd h w = .ok r w'
  /-- `setpgidOnce` never throws an `IO.Error`. -/
  setpgidOnce_ok : ∀ p g w, ∃ r w', raw.setpgidOnce p g w = .ok r w'
  /-- `writeOnce` never throws an `IO.Error`. -/
  writeOnce_ok : ∀ h d o l w, ∃ r w', raw.writeOnce h d o l w = .ok r w'
  /-- `readOnce` never throws an `IO.Error`. -/
  readOnce_ok : ∀ h c w, ∃ r w', raw.readOnce h c w = .ok r w'
  /-- `waitOnce` never throws an `IO.Error`. -/
  waitOnce_ok : ∀ p w, ∃ r w', raw.waitOnce p w = .ok r w'
  /-- `forkRun` never throws an `IO.Error`. -/
  forkRun_ok : ∀ fl fm sr ew std cl kp cwd path argv env w,
    ∃ r w', raw.forkRun fl fm sr ew std cl kp cwd path argv env w = .ok r w'

section HostOrchestratorBase

/-- Pure iterative mirror of `Internal.loopPow2` over `StateM S`. -/
def runSteps {S σ α : Type} (step : σ → StateM S (Sum σ α)) : Nat → σ → S → Sum σ α × S
  | 0, s, st => (.inl s, st)
  | n + 1, s, st =>
    match (step s).run st with
    | (.inr a, st') => (.inr a, st')
    | (.inl s', st') => runSteps step n s' st'

theorem runSteps_add {S σ α : Type} (step : σ → StateM S (Sum σ α)) (m n : Nat) (s : σ) (st : S) :
    runSteps step (m + n) s st =
      match runSteps step m s st with
      | (.inr a, st') => (.inr a, st')
      | (.inl s', st') => runSteps step n s' st' := by
  induction m generalizing s st with
  | zero => simp [runSteps]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [runSteps]
    cases (step s).run st with
    | mk r st' =>
      cases r with
      | inl s' => exact ih s' st'
      | inr a => rfl

theorem loopPow2_run {S σ α : Type} (step : σ → StateM S (Sum σ α)) (d : Nat) (s : σ) (st : S) :
    (Impl.Internal.loopPow2 step d s).run st = runSteps step (2 ^ d) s st := by
  induction d generalizing s st with
  | zero =>
    simp only [Impl.Internal.loopPow2, Nat.pow_zero, runSteps]
    cases (step s).run st with
    | mk r st' => cases r <;> rfl
  | succ d ih =>
    rw [Impl.Internal.loopPow2, StateT.run_bind]
    simp only [Nat.pow_succ, Nat.mul_two, runSteps_add]
    rw [ih s st]
    cases runSteps step (2 ^ d) s st with
    | mk r st' =>
      cases r with
      | inl s' => exact ih s' st'
      | inr a => rfl

theorem runSteps_inr {S σ α : Type} (step : σ → StateM S (Sum σ α))
    {n : Nat} (hn : 0 < n) {s : σ} {st st' : S} {a : α}
    (h : (step s).run st = (.inr a, st')) :
    runSteps step n s st = (.inr a, st') := by
  cases n with
  | zero => omega
  | succ m => simp [runSteps, h]

theorem runSteps_inl {S σ α : Type} (step : σ → StateM S (Sum σ α))
    {n : Nat} (hn : 0 < n) {s s' : σ} {st st' : S}
    (h : (step s).run st = (.inl s', st')) :
    runSteps step n s st = runSteps step (n - 1) s' st' := by
  cases n with
  | zero => omega
  | succ m => simp [runSteps, h]

theorem runSteps_step_eq {S σ α : Type} (step1 step2 : σ → StateM S (Sum σ α))
    (h : step1 = step2) (n : Nat) (s : σ) (st : S) :
    runSteps step1 n s st = runSteps step2 n s st := by
  subst h; rfl

theorem stateT_bind_pure_pair {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S)
    (a : α) (s' : S) (hx : x.run s = (a, s')) :
    (x >>= f).run s = (f a).run s' := by
  simp [StateT.run_bind, hx]; rfl

theorem stateT_run_bind_id {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) :
    (x >>= f).run s = let p := x.run s; (f p.1).run p.2 := rfl

theorem stateT_bind_pure_val {S α β : Type} (a : α) (f : α → StateM S β) (s : S) :
    ((pure a : StateM S α) >>= f).run s = (f a).run s := rfl

theorem stateM_run_pure_any {S α : Type} (a : α) (s : S) :
    (pure a : StateM S α).run s = (a, s) := rfl

private theorem byteArray_ext {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a; cases b; congr

private theorem extract_eq_of_data {a : ByteArray} {b e : Nat} (hle : b ≤ e) :
    (a.extract b e).data = a.data.extract b e := by
  have hbe : b + (e - b) = e := by omega
  simp [ByteArray.extract, ByteArray.copySlice, hbe]

theorem appendBytes_empty_one :
    appendBytes ByteArray.empty (ByteArray.mk #[1]) = ByteArray.mk #[1] := rfl

theorem concatByteChunks_empty : Impl.Internal.concatByteChunks #[] = ByteArray.empty :=
  byteArray_ext rfl

theorem concatByteChunks_wire4 (a0 a1 a2 a3 : UInt8) :
    Impl.Internal.concatByteChunks ((#[].push (ByteArray.mk #[a0, a1, a2])).push (ByteArray.mk #[a3])) =
      ByteArray.mk #[a0, a1, a2, a3] := rfl

theorem concatByteChunks_wire8 (a0 a1 a2 a3 a4 a5 a6 a7 : UInt8) :
    Impl.Internal.concatByteChunks
        (((#[].push (ByteArray.mk #[a0, a1, a2])).push (ByteArray.mk #[a3, a4, a5])).push (ByteArray.mk #[a6, a7])) =
      ByteArray.mk #[a0, a1, a2, a3, a4, a5, a6, a7] := rfl

theorem mem_byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (x : UInt8) :
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

theorem hasEmbeddedNulStr_of_forall_ne (s : String)
    (h : ∀ i, i < s.toUTF8.size → s.toUTF8.get! i ≠ 0) :
    hasEmbeddedNulStr s = false := by
  unfold hasEmbeddedNulStr
  rw [List.any_eq_false]
  intro x hx hEq
  have h0 : x = 0 := by simpa using hEq
  subst h0
  rcases mem_byteArray_toList_loop s.toUTF8 0 [] 0 hx with hEmpty | ⟨j, hj, hVal⟩
  · cases hEmpty
  · exact h j hj hVal.symm

theorem hasEmbeddedNulStr_a : hasEmbeddedNulStr "a" = false :=
  hasEmbeddedNulStr_of_forall_ne "a" (by decide)

theorem hasEmbeddedNulStr_echo : hasEmbeddedNulStr "/bin/echo" = false :=
  hasEmbeddedNulStr_of_forall_ne "/bin/echo" (by decide)

theorem hasEmbeddedNulStr_true : hasEmbeddedNulStr "/bin/true" = false :=
  hasEmbeddedNulStr_of_forall_ne "/bin/true" (by decide)

theorem hasEmbeddedNulStr_false : hasEmbeddedNulStr "/bin/false" = false :=
  hasEmbeddedNulStr_of_forall_ne "/bin/false" (by decide)

theorem hasEmbeddedNulStr_fdPrefix : hasEmbeddedNulStr "--fd=" = false :=
  hasEmbeddedNulStr_of_forall_ne "--fd=" (by decide)

theorem hasEmbeddedNulStr_x : hasEmbeddedNulStr "x" = false :=
  hasEmbeddedNulStr_of_forall_ne "x" (by decide)

theorem hasEmbeddedNulStr_K : hasEmbeddedNulStr "K" = false :=
  hasEmbeddedNulStr_of_forall_ne "K" (by decide)

theorem hasEmbeddedNulStr_V : hasEmbeddedNulStr "V" = false :=
  hasEmbeddedNulStr_of_forall_ne "V" (by decide)

theorem hasEmbeddedNulStr_empty : hasEmbeddedNulStr "" = false :=
  hasEmbeddedNulStr_of_forall_ne "" (by decide)

theorem hasEmbeddedNulStr_procSelfFd : hasEmbeddedNulStr "/proc/self/fd/" = false :=
  hasEmbeddedNulStr_of_forall_ne "/proc/self/fd/" (by decide)

theorem largeArgs_valid (k : Nat) :
    ((#[ArgToken.lit "/bin/echo"] ++ (List.replicate k (ArgToken.lit "a")).toArray).all
      (ArgToken.isValid (fd := Int32))) = true := by
  rw [Array.all_eq_true]
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    simp [ArgToken.isValid, hasEmbeddedNulStr_echo]
  · have hGe : (#[ArgToken.lit "/bin/echo"] : Array (ArgToken Int32)).size ≤ i := by simp; omega
    rw [Array.getElem_append_right hGe]
    have hSub : i - (#[ArgToken.lit "/bin/echo"] : Array (ArgToken Int32)).size <
        (List.replicate k (ArgToken.lit "a" : ArgToken Int32)).toArray.size := by
      simp_all [Array.size_append]; omega
    have hMem := List.mem_toArray.mp (Array.getElem_mem hSub)
    rcases List.mem_replicate.mp hMem with ⟨_, hEq⟩
    rw [hEq]
    simp [ArgToken.isValid, hasEmbeddedNulStr_a]

theorem pow2_18_eq : 2 ^ (18 : Nat) = 262144 := by decide

/-- Single read step matching `Impl.Internal.readAllRetryEintr` on `mockPosixHostOps`. -/
def mockReadStep (fd : Int32) (cap : UInt64) (curChunks : Array ByteArray) :
    StateM HostMockState (Sum (Array ByteArray) (Except PostForkError ByteArray)) := do
  match ← mockPosixHostOps.readOnce fd cap with
  | .ok chunk =>
    if chunk.size == 0 then
      pure (.inr (.ok (Impl.Internal.concatByteChunks curChunks)))
    else
      pure (.inl (curChunks.push chunk))
  | .error e =>
    if e == 4 then
      pure (.inl curChunks)
    else
      pure (.inr (.error (Impl.Internal.mkSysErr e "host read failed")))

/-- Single wait step matching `Impl.Internal.waitRetryEintr` on `mockPosixHostOps`. -/
def mockWaitStep (pid : Pid) (_ : Unit) :
    StateM HostMockState (Sum Unit (Except PostForkError ChildWaitStatus)) := do
  match ← mockPosixHostOps.waitOnce pid with
  | .ok st => pure (.inr (.ok st))
  | .error e =>
    if e == 4 then
      pure (.inl ())
    else
      pure (.inr (.error (Impl.Internal.mkSysErr e "waitpid failed")))

/-- Single write step matching `Impl.Internal.writeAllRetryEintr` on `mockPosixHostOps`. -/
def mockWriteStep (fd : Int32) (data : ByteArray) (curOff : Nat) :
    StateM HostMockState (Sum Nat (Except PostForkError Unit)) :=
  if curOff ≥ data.size then
    pure (.inr (.ok ()))
  else do
    let rem := data.size - curOff
    match ← mockPosixHostOps.writeOnce fd data (UInt64.ofNat curOff) (UInt64.ofNat rem) with
    | .ok n =>
      if n == 0 then
        pure (.inr (.error (Impl.Internal.mkSysErr 5 "host write returned zero bytes")))
      else
        pure (.inl (curOff + n.toNat))
    | .error e =>
      if e == 4 then
        pure (.inl curOff)
      else
        pure (.inr (.error (Impl.Internal.mkSysErr e "host write failed")))

theorem readStep_eintr (fd : Int32) (cap : UInt64) (n : Nat) (hn : 0 < n)
    (chunks : Array ByteArray) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (hGt : st.readEintrCount > 0) :
    runSteps (mockReadStep fd cap) n chunks st =
      runSteps (mockReadStep fd cap) (n - 1) chunks
        { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 } := by
  refine runSteps_inl _ hn ?_
  have hRead : (mockPosixHostOps.readOnce fd cap).run st =
      (Except.error Errno.EINTR,
        { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }) := by
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hGt]
    rfl
  rw [mockReadStep, stateT_bind_pure_pair _ _ _ _ _ hRead]
  have h4 : (Errno.EINTR == 4) = true := by decide
  simp only [h4, ↓reduceIte]
  rfl

theorem readStep_eof_empty (fd : Int32) (cap : UInt64) (n : Nat) (hn : 0 < n)
    (chunks : Array ByteArray) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (h0 : st.readEintrCount = 0)
    (hEmpty : st.repWire = ByteArray.empty) :
    runSteps (mockReadStep fd cap) n chunks st =
      (.inr (.ok (Impl.Internal.concatByteChunks chunks)),
        { st with callCount := st.callCount + 1 }) := by
  refine runSteps_inr _ hn ?_
  have hEx : ByteArray.empty.extract 0 0 = ByteArray.empty := by
    apply byteArray_ext
    rw [extract_eq_of_data (by omega)]
    rfl
  have hRead : (mockPosixHostOps.readOnce fd cap).run st =
      (Except.ok ByteArray.empty, { st with callCount := st.callCount + 1 }) := by
    have hNotGt : ¬ (st.readEintrCount > 0) := by omega
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hNotGt, hEmpty, ite_self,
      ByteArray.size_empty, Nat.zero_min, hEx]
    rfl
  rw [mockReadStep, stateT_bind_pure_pair _ _ _ _ _ hRead]
  rfl

theorem readAllRetry_empty (fd : Int32) (eCnt : Nat) (he : eCnt ≤ 2) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (hE : st.readEintrCount = eCnt)
    (hEmpty : st.repWire = ByteArray.empty) :
    (Impl.Internal.readAllRetryEintr mockPosixHostOps fd 16 ByteArray.empty 18).run st =
      (.ok ByteArray.empty, { st with callCount := st.callCount + eCnt + 1, readEintrCount := 0 }) := by
  unfold Impl.Internal.readAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockReadStep fd 16)]; swap; rfl)
  rw [show (if (ByteArray.empty.size == 0) = true then (#[] : Array ByteArray) else #[ByteArray.empty]) = #[] from rfl]
  rw [pow2_18_eq]
  rcases Nat.lt_trichotomy eCnt 1 with h0 | h1 | h2
  · have hE0 : eCnt = 0 := by omega
    subst hE0
    rw [readStep_eof_empty fd 16 262144 (by decide) #[] st hClosed hFail hE hEmpty]
    dsimp only [StateT.run, pure, StateT.pure]
    rw [concatByteChunks_empty]
    simp only [hE, Nat.add_zero]
  · have hE1 : eCnt = 1 := by omega
    subst hE1
    rw [readStep_eintr fd 16 262144 (by decide) #[] st hClosed hFail (by omega)]
    let s1 : HostMockState := { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }
    have hE1' : s1.readEintrCount = 0 := by simp [s1, hE]
    rw [readStep_eof_empty fd 16 _ (by decide) #[] s1 hClosed hFail hE1' hEmpty]
    dsimp only [StateT.run, pure, StateT.pure]
    rw [concatByteChunks_empty]
    simp only [s1, hE, Nat.add_assoc]
  · have hE2 : eCnt = 2 := by omega
    subst hE2
    rw [readStep_eintr fd 16 262144 (by decide) #[] st hClosed hFail (by omega)]
    let s1 : HostMockState := { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }
    rw [readStep_eintr fd 16 _ (by decide) #[] s1 hClosed hFail (by simp [s1, hE])]
    let s2 : HostMockState := { s1 with callCount := s1.callCount + 1, readEintrCount := s1.readEintrCount - 1 }
    have hE2' : s2.readEintrCount = 0 := by simp [s2, s1, hE]
    rw [readStep_eof_empty fd 16 _ (by decide) #[] s2 hClosed hFail hE2' hEmpty]
    dsimp only [StateT.run, pure, StateT.pure]
    rw [concatByteChunks_empty]
    simp only [s2, s1, hE, Nat.add_assoc]

theorem readStep_chunk (fd : Int32) (cap : UInt64) (n : Nat) (hn : 0 < n)
    (chunks : Array ByteArray) (chunk rest : ByteArray) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (h0 : st.readEintrCount = 0)
    (hFd : fd = st.allocRepReadFd)
    (hChunk : st.repWire.extract 0 (Nat.min (Nat.min st.repWire.size cap.toNat) 3) = chunk)
    (hRest : st.repWire.extract (Nat.min (Nat.min st.repWire.size cap.toNat) 3) st.repWire.size = rest)
    (hChunkNe : (chunk.size == 0) = false) :
    runSteps (mockReadStep fd cap) n chunks st =
      runSteps (mockReadStep fd cap) (n - 1) (chunks.push chunk)
        { st with callCount := st.callCount + 1, repWire := rest } := by
  refine runSteps_inl _ hn ?_
  have hFdB : (fd == st.allocRepReadFd) = true := beq_iff_eq.mpr hFd
  have hRead : (mockPosixHostOps.readOnce fd cap).run st =
      (Except.ok chunk, { st with callCount := st.callCount + 1, repWire := rest }) := by
    have hNotGt : ¬ (st.readEintrCount > 0) := by omega
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hNotGt, hFdB, hChunk, hRest]
    rfl
  rw [mockReadStep, stateT_bind_pure_pair _ _ _ _ _ hRead]
  simp only [hChunkNe, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem readAllRetry_wire4_e0 (fd : Int32) (b0 b1 b2 b3 : UInt8) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (hE0 : st.readEintrCount = 0)
    (hFd : fd = st.allocRepReadFd)
    (hWire : st.repWire = ByteArray.mk #[b0, b1, b2, b3]) :
    (Impl.Internal.readAllRetryEintr mockPosixHostOps fd 16 ByteArray.empty 18).run st =
      (.ok (ByteArray.mk #[b0, b1, b2, b3]),
        { st with callCount := st.callCount + 3, repWire := ByteArray.empty }) := by
  unfold Impl.Internal.readAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockReadStep fd 16)]; swap; rfl)
  rw [show (if (ByteArray.empty.size == 0) = true then (#[] : Array ByteArray) else #[ByteArray.empty]) = #[] from rfl]
  rw [pow2_18_eq]
  have hC1 : (ByteArray.mk #[b0, b1, b2, b3]).extract 0 3 = ByteArray.mk #[b0, b1, b2] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hR1 : (ByteArray.mk #[b0, b1, b2, b3]).extract 3 4 = ByteArray.mk #[b3] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  rw [readStep_chunk fd 16 262144 (by decide) #[] (ByteArray.mk #[b0, b1, b2]) (ByteArray.mk #[b3])
    st hClosed hFail hE0 hFd (by rw [hWire]; exact hC1) (by rw [hWire]; exact hR1) rfl]
  let s1 : HostMockState := { st with callCount := st.callCount + 1, repWire := ByteArray.mk #[b3] }
  have hC2 : (ByteArray.mk #[b3]).extract 0 1 = ByteArray.mk #[b3] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hR2 : (ByteArray.mk #[b3]).extract 1 1 = ByteArray.empty :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  rw [readStep_chunk fd 16 _ (by decide) _ (ByteArray.mk #[b3]) ByteArray.empty
    s1 hClosed hFail hE0 hFd hC2 hR2 rfl]
  let s2 : HostMockState := { s1 with callCount := s1.callCount + 1, repWire := ByteArray.empty }
  rw [readStep_eof_empty fd 16 _ (by decide) _ s2 hClosed hFail hE0 rfl]
  dsimp only [StateT.run, pure, StateT.pure]
  have hCat := concatByteChunks_wire4 b0 b1 b2 b3
  rw [hCat]

theorem readAllRetry_wire8 (fd : Int32) (eCnt : Nat) (he : eCnt = 1 ∨ eCnt = 2)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = none)
    (hE : st.readEintrCount = eCnt)
    (hFd : fd = st.allocRepReadFd)
    (hWire : st.repWire = ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]) :
    (Impl.Internal.readAllRetryEintr mockPosixHostOps fd 16 ByteArray.empty 18).run st =
      (.ok (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]),
        { st with callCount := st.callCount + eCnt + 4, readEintrCount := 0, repWire := ByteArray.empty }) := by
  unfold Impl.Internal.readAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockReadStep fd 16)]; swap; rfl)
  rw [show (if (ByteArray.empty.size == 0) = true then (#[] : Array ByteArray) else #[ByteArray.empty]) = #[] from rfl]
  rw [pow2_18_eq]
  have hC1 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]).extract 0 3 = ByteArray.mk #[b0, b1, b2] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hR1 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]).extract 3 8 = ByteArray.mk #[b3, b4, b5, b6, b7] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hC2 : (ByteArray.mk #[b3, b4, b5, b6, b7]).extract 0 3 = ByteArray.mk #[b3, b4, b5] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hR2 : (ByteArray.mk #[b3, b4, b5, b6, b7]).extract 3 5 = ByteArray.mk #[b6, b7] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hC3 : (ByteArray.mk #[b6, b7]).extract 0 2 = ByteArray.mk #[b6, b7] :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hR3 : (ByteArray.mk #[b6, b7]).extract 2 2 = ByteArray.empty :=
    byteArray_ext (by rw [extract_eq_of_data (by omega)]; rfl)
  have hCat := concatByteChunks_wire8 b0 b1 b2 b3 b4 b5 b6 b7
  rcases he with rfl | rfl
  · rw [readStep_eintr fd 16 262144 (by decide) #[] st hClosed hFail (by omega)]
    let s0 : HostMockState := { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }
    have hE0 : s0.readEintrCount = 0 := by simp [s0, hE]
    rw [readStep_chunk fd 16 _ (by decide) #[] (ByteArray.mk #[b0, b1, b2]) (ByteArray.mk #[b3, b4, b5, b6, b7])
      s0 hClosed hFail hE0 hFd (by rw [show s0.repWire = _ from hWire]; exact hC1)
      (by rw [show s0.repWire = _ from hWire]; exact hR1) rfl]
    let s1 : HostMockState := { s0 with callCount := s0.callCount + 1, repWire := ByteArray.mk #[b3, b4, b5, b6, b7] }
    rw [readStep_chunk fd 16 _ (by decide) _ (ByteArray.mk #[b3, b4, b5]) (ByteArray.mk #[b6, b7])
      s1 hClosed hFail hE0 hFd hC2 hR2 rfl]
    let s2 : HostMockState := { s1 with callCount := s1.callCount + 1, repWire := ByteArray.mk #[b6, b7] }
    rw [readStep_chunk fd 16 _ (by decide) _ (ByteArray.mk #[b6, b7]) ByteArray.empty
      s2 hClosed hFail hE0 hFd hC3 hR3 rfl]
    let s3 : HostMockState := { s2 with callCount := s2.callCount + 1, repWire := ByteArray.empty }
    rw [readStep_eof_empty fd 16 _ (by decide) _ s3 hClosed hFail hE0 rfl]
    dsimp only [StateT.run, pure, StateT.pure]
    rw [hCat]
    simp only [s3, s2, s1, s0, hE]
  · rw [readStep_eintr fd 16 262144 (by decide) #[] st hClosed hFail (by omega)]
    let sa : HostMockState := { st with callCount := st.callCount + 1, readEintrCount := st.readEintrCount - 1 }
    rw [readStep_eintr fd 16 _ (by decide) #[] sa hClosed hFail (by simp [sa, hE])]
    let s0 : HostMockState := { sa with callCount := sa.callCount + 1, readEintrCount := sa.readEintrCount - 1 }
    have hE0 : s0.readEintrCount = 0 := by simp [s0, sa, hE]
    rw [readStep_chunk fd 16 _ (by decide) #[] (ByteArray.mk #[b0, b1, b2]) (ByteArray.mk #[b3, b4, b5, b6, b7])
      s0 hClosed hFail hE0 hFd (by rw [show s0.repWire = _ from hWire]; exact hC1)
      (by rw [show s0.repWire = _ from hWire]; exact hR1) rfl]
    let s1 : HostMockState := { s0 with callCount := s0.callCount + 1, repWire := ByteArray.mk #[b3, b4, b5, b6, b7] }
    rw [readStep_chunk fd 16 _ (by decide) _ (ByteArray.mk #[b3, b4, b5]) (ByteArray.mk #[b6, b7])
      s1 hClosed hFail hE0 hFd hC2 hR2 rfl]
    let s2 : HostMockState := { s1 with callCount := s1.callCount + 1, repWire := ByteArray.mk #[b6, b7] }
    rw [readStep_chunk fd 16 _ (by decide) _ (ByteArray.mk #[b6, b7]) ByteArray.empty
      s2 hClosed hFail hE0 hFd hC3 hR3 rfl]
    let s3 : HostMockState := { s2 with callCount := s2.callCount + 1, repWire := ByteArray.empty }
    rw [readStep_eof_empty fd 16 _ (by decide) _ s3 hClosed hFail hE0 rfl]
    dsimp only [StateT.run, pure, StateT.pure]
    rw [hCat]
    simp only [s3, s2, s1, s0, sa, hE]

theorem waitStep_loop (pid : Pid) (k n : Nat) (st : HostMockState)
    (hFail : st.failWaitErrno = none) (hk : st.waitEintrCount = k) (hn : k < n) :
    runSteps (mockWaitStep pid) n () st =
      (.inr (.ok st.waitResult), { st with callCount := st.callCount + k + 1, waitEintrCount := 0 }) := by
  induction k generalizing st n with
  | zero =>
    cases n with
    | zero => omega
    | succ m =>
      have hWait : (mockPosixHostOps.waitOnce pid).run st =
          (.ok st.waitResult, { st with callCount := st.callCount + 1 }) := by
        have hNotGt : ¬ (st.waitEintrCount > 0) := by omega
        dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
          set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
        simp only [hFail, hNotGt, ↓reduceIte]
        rfl
      rw [runSteps_inr _ (Nat.zero_lt_succ m)
        (by rw [mockWaitStep, stateT_bind_pure_pair _ _ _ _ _ hWait]; rfl)]
      simp only [hk, Nat.add_zero]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ m =>
      have hGt : st.waitEintrCount > 0 := by omega
      have hWait : (mockPosixHostOps.waitOnce pid).run st =
          (.error Errno.EINTR,
            { st with callCount := st.callCount + 1, waitEintrCount := st.waitEintrCount - 1 }) := by
        dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
          set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
        simp only [hFail, hGt, ↓reduceIte]
        rfl
      rw [runSteps_inl _ (Nat.zero_lt_succ m)
        (s' := ()) (st' := { st with callCount := st.callCount + 1, waitEintrCount := st.waitEintrCount - 1 }) ?_]
      · have ih1 := ih m { st with callCount := st.callCount + 1, waitEintrCount := st.waitEintrCount - 1 }
          hFail (by simp [hk]) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih1
      · rw [mockWaitStep, stateT_bind_pure_pair _ _ _ _ _ hWait]
        rfl

theorem waitRetry_ok (pid : Pid) (st : HostMockState)
    (hFail : st.failWaitErrno = none) (hLt : st.waitEintrCount < 100) :
    (Impl.Internal.waitRetryEintr mockPosixHostOps pid 18).run st =
      (.ok st.waitResult,
        { st with callCount := st.callCount + st.waitEintrCount + 1, waitEintrCount := 0 }) := by
  unfold Impl.Internal.waitRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockWaitStep pid)]; swap; rfl)
  rw [waitStep_loop pid st.waitEintrCount (2 ^ 18) st hFail rfl (by rw [pow2_18_eq]; omega)]
  rfl

theorem writeAllRetry_sync1_eintr2 (fd : Int32) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failWriteErrno = none)
    (hE : st.writeEintrCount = 2)
    (hFd : fd = st.allocSyncWriteFd)
    (hSync : st.syncWritten = ByteArray.empty) :
    (Impl.Internal.writeAllRetryEintr mockPosixHostOps fd (ByteArray.mk #[1]) 0 18).run st =
      (.ok (), { st with callCount := st.callCount + 3, writeEintrCount := 0, syncWritten := ByteArray.mk #[1] }) := by
  unfold Impl.Internal.writeAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockWriteStep fd (ByteArray.mk #[1]))]; swap; rfl)
  rw [pow2_18_eq]
  have hNotGe0 : ¬ (0 ≥ (ByteArray.mk #[1]).size) := by decide
  have hGe1 : (1 : Nat) ≥ (ByteArray.mk #[1]).size := by decide
  have hW1 : (mockPosixHostOps.writeOnce fd (ByteArray.mk #[1]) 0 1).run st =
      (.error Errno.EINTR, { st with callCount := st.callCount + 1, writeEintrCount := st.writeEintrCount - 1 }) := by
    have hGt : st.writeEintrCount > 0 := by omega
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hGt]
    rfl
  rw [runSteps_inl _ (by decide) (s' := 0)
    (st' := { st with callCount := st.callCount + 1, writeEintrCount := st.writeEintrCount - 1 })
    (by
      rw [mockWriteStep]; simp only [hNotGe0, ↓reduceIte]
      rw [show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
          show (UInt64.ofNat ((ByteArray.mk #[1]).size - 0) : UInt64) = 1 from rfl]
      rw [stateT_bind_pure_pair _ _ _ _ _ hW1]; rfl)]
  let s1 : HostMockState := { st with callCount := st.callCount + 1, writeEintrCount := st.writeEintrCount - 1 }
  have hE1 : s1.writeEintrCount = 1 := by simp [s1, hE]
  have hW2 : (mockPosixHostOps.writeOnce fd (ByteArray.mk #[1]) 0 1).run s1 =
      (.error Errno.EINTR, { s1 with callCount := s1.callCount + 1, writeEintrCount := s1.writeEintrCount - 1 }) := by
    have hGt1 : s1.writeEintrCount > 0 := by omega
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [s1, hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hGt1]
    rfl
  rw [runSteps_inl _ (by decide) (s' := 0)
    (st' := { s1 with callCount := s1.callCount + 1, writeEintrCount := s1.writeEintrCount - 1 })
    (by
      rw [mockWriteStep]; simp only [hNotGe0, ↓reduceIte]
      rw [show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
          show (UInt64.ofNat ((ByteArray.mk #[1]).size - 0) : UInt64) = 1 from rfl]
      rw [stateT_bind_pure_pair _ _ _ _ _ hW2]; rfl)]
  let s2 : HostMockState := { s1 with callCount := s1.callCount + 1, writeEintrCount := s1.writeEintrCount - 1 }
  have hE2 : s2.writeEintrCount = 0 := by simp [s2, hE1]
  have hExt1 : (ByteArray.mk #[1]).extract (0 : UInt64).toNat ((0 : UInt64).toNat + Nat.min (1 : UInt64).toNat 2) =
      ByteArray.mk #[1] :=
    byteArray_ext (by rw [extract_eq_of_data (by decide)]; rfl)
  have hFdB : (fd == s2.allocSyncWriteFd) = true := beq_iff_eq.mpr hFd
  have hW3 : (mockPosixHostOps.writeOnce fd (ByteArray.mk #[1]) 0 1).run s2 =
      (.ok (UInt64.ofNat 1),
        { s2 with callCount := s2.callCount + 1, syncWritten := appendBytes s2.syncWritten (ByteArray.mk #[1]) }) := by
    have hNotGt2 : ¬ (s2.writeEintrCount > 0) := by omega
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [s2, s1, hClosed, Bool.false_eq_true, ↓reduceIte, hFail, hNotGt2, hFdB]
    rw [hExt1]
    rfl
  rw [runSteps_inl _ (by decide) (s' := 1)
    (st' := { s2 with callCount := s2.callCount + 1, syncWritten := appendBytes s2.syncWritten (ByteArray.mk #[1]) })
    (by
      rw [mockWriteStep]; simp only [hNotGe0, ↓reduceIte]
      rw [show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
          show (UInt64.ofNat ((ByteArray.mk #[1]).size - 0) : UInt64) = 1 from rfl]
      rw [stateT_bind_pure_pair _ _ _ _ _ hW3]; rfl)]
  let s3 : HostMockState := { s2 with callCount := s2.callCount + 1, syncWritten := appendBytes s2.syncWritten (ByteArray.mk #[1]) }
  rw [runSteps_inr _ (by decide) (s := 1) (st := s3) (st' := s3) (a := .ok ())
    (by rw [mockWriteStep]; simp only [hGe1, ↓reduceIte]; rfl)]
  dsimp only [StateT.run, pure, StateT.pure]
  have hApp : appendBytes ByteArray.empty (ByteArray.mk #[1]) = ByteArray.mk #[1] :=
    appendBytes_empty_one
  simp only [s3, s2, s1, hSync, hApp, hE, Nat.add_assoc]

theorem writeAllRetry_epipe (fd : Int32) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failWriteErrno = some Errno.EPIPE) :
    (Impl.Internal.writeAllRetryEintr mockPosixHostOps fd (ByteArray.mk #[1]) 0 18).run st =
      (.error (Impl.Internal.mkSysErr Errno.EPIPE "host write failed"),
        { st with callCount := st.callCount + 1 }) := by
  unfold Impl.Internal.writeAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockWriteStep fd (ByteArray.mk #[1]))]; swap; rfl)
  rw [pow2_18_eq]
  have hNotGe0 : ¬ (0 ≥ (ByteArray.mk #[1]).size) := by decide
  have hW : (mockPosixHostOps.writeOnce fd (ByteArray.mk #[1]) 0 1).run st =
      (.error Errno.EPIPE, { st with callCount := st.callCount + 1 }) := by
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail]
    rfl
  rw [runSteps_inr _ (by decide)
    (by
      rw [mockWriteStep]; simp only [hNotGe0, ↓reduceIte]
      rw [show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
          show (UInt64.ofNat ((ByteArray.mk #[1]).size - 0) : UInt64) = 1 from rfl]
      rw [stateT_bind_pure_pair _ _ _ _ _ hW]; rfl)]
  dsimp only [StateT.run, pure, StateT.pure]

theorem writeAllRetry_errno_ne4_raw
    (raw : PosixHostOpsM (StateM HostMockState) Int32)
    (hRawW : raw.writeOnce = mockPosixHostOps.writeOnce)
    (e : Errno) (he4 : (e == 4) = false)
    (fd : Int32) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failWriteErrno = some e) :
    (Impl.Internal.writeAllRetryEintr raw fd (ByteArray.mk #[1]) 0 18).run st =
      (.error (Impl.Internal.mkSysErr e "host write failed"),
        { st with callCount := st.callCount + 1 }) := by
  unfold Impl.Internal.writeAllRetryEintr
  rw [hRawW, stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockWriteStep fd (ByteArray.mk #[1]))]; swap; rfl)
  rw [pow2_18_eq]
  have hNotGe0 : ¬ (0 ≥ (ByteArray.mk #[1]).size) := by decide
  have hW : (mockPosixHostOps.writeOnce fd (ByteArray.mk #[1]) 0 1).run st =
      (.error e, { st with callCount := st.callCount + 1 }) := by
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail]
    rfl
  rw [runSteps_inr _ (by decide)
    (by
      rw [mockWriteStep]; simp only [hNotGe0, ↓reduceIte]
      rw [show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
          show (UInt64.ofNat ((ByteArray.mk #[1]).size - 0) : UInt64) = 1 from rfl]
      rw [stateT_bind_pure_pair _ _ _ _ _ hW]
      simp only [he4, Bool.false_eq_true, ↓reduceIte]
      rfl)]
  dsimp only [StateT.run, pure, StateT.pure]

theorem writeAllRetry_eio_raw
    (raw : PosixHostOpsM (StateM HostMockState) Int32)
    (hRawW : raw.writeOnce = mockPosixHostOps.writeOnce)
    (fd : Int32) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failWriteErrno = some Errno.EIO) :
    (Impl.Internal.writeAllRetryEintr raw fd (ByteArray.mk #[1]) 0 18).run st =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host write failed"),
        { st with callCount := st.callCount + 1 }) :=
  writeAllRetry_errno_ne4_raw raw hRawW Errno.EIO (by decide) fd st hClosed hFail

theorem readAllRetry_eio (fd : Int32) (st : HostMockState)
    (hClosed : st.closedHandles.contains fd = false)
    (hFail : st.failReadErrno = some Errno.EIO) :
    (Impl.Internal.readAllRetryEintr mockPosixHostOps fd 16 ByteArray.empty 18).run st =
      (.error (Impl.Internal.mkSysErr Errno.EIO "host read failed"),
        { st with callCount := st.callCount + 1 }) := by
  unfold Impl.Internal.readAllRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockReadStep fd 16)]; swap; rfl)
  rw [show (if (ByteArray.empty.size == 0) = true then (#[] : Array ByteArray) else #[ByteArray.empty]) = #[] from rfl]
  rw [pow2_18_eq]
  have hR : (mockPosixHostOps.readOnce fd 16).run st =
      (.error Errno.EIO, { st with callCount := st.callCount + 1 }) := by
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hClosed, Bool.false_eq_true, ↓reduceIte, hFail]
    rfl
  rw [runSteps_inr _ (by decide) (by rw [mockReadStep, stateT_bind_pure_pair _ _ _ _ _ hR]; rfl)]
  dsimp only [StateT.run, pure, StateT.pure]

theorem waitRetry_echild (pid : Pid) (st : HostMockState)
    (hFail : st.failWaitErrno = some Errno.ECHILD) :
    (Impl.Internal.waitRetryEintr mockPosixHostOps pid 18).run st =
      (.error (Impl.Internal.mkSysErr Errno.ECHILD "waitpid failed"),
        { st with callCount := st.callCount + 1 }) := by
  unfold Impl.Internal.waitRetryEintr
  rw [stateT_run_bind_id, loopPow2_run]
  focus (rw [runSteps_step_eq _ (mockWaitStep pid)]; swap; rfl)
  rw [pow2_18_eq]
  have hW : (mockPosixHostOps.waitOnce pid).run st =
      (.error Errno.ECHILD, { st with callCount := st.callCount + 1 }) := by
    dsimp only [mockPosixHostOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, bind, StateT.bind, pure, StateT.pure, Id.run]
    simp only [hFail]
    rfl
  rw [runSteps_inr _ (by decide) (by rw [mockWaitStep, stateT_bind_pure_pair _ _ _ _ _ hW]; rfl)]
  dsimp only [StateT.run, pure, StateT.pure]

end HostOrchestratorBase

section HostIoInvariants

/-- Unfolding lemma for `IO.bind` at a world state. -/
theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w = match x w with | .ok a w' => f a w' | .error e w' => .error e w' := by
  change EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

/-- Unfolding lemma for `IO.pure` at a world state. -/
theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = .ok a w := rfl

private theorem loopPow2_io_ok {σ α : Type}
    (step : σ → IO (Sum σ α))
    (inv : σ → Prop)
    (post : α → Prop)
    (hStep : ∀ s w, inv s → ∃ r w', step s w = .ok r w' ∧
      (match r with | .inl s' => inv s' | .inr a => post a))
    (d : Nat) (s : σ) (hs : inv s) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.loopPow2 step d s w = .ok r w' ∧
      (match r with | .inl s' => inv s' | .inr a => post a) := by
  induction d generalizing s w with
  | zero => exact hStep s w hs
  | succ d ih =>
    unfold Impl.Internal.loopPow2
    rw [io_bind_eq]
    rcases ih s hs w with ⟨r1, w1, h1, hr1⟩
    rw [h1]
    dsimp only
    cases r1 with
    | inr done => exact ⟨.inr done, w1, rfl, hr1⟩
    | inl next => exact ih next hr1 w1

private theorem loopPow2_io_bind_ok {σ α β : Type}
    (step : σ → IO (Sum σ α))
    (inv : σ → Prop)
    (post : α → Prop)
    (d : Nat) (s : σ) (hs : inv s) (w : Void IO.RealWorld)
    (k : Sum σ α → IO β) (resPost : β → Prop)
    (hStep : ∀ s w, inv s → ∃ r w', step s w = .ok r w' ∧
      (match r with | .inl s' => inv s' | .inr a => post a))
    (hk : ∀ r w', (match r with | .inl s' => inv s' | .inr a => post a) →
      ∃ b w'', k r w' = .ok b w'' ∧ resPost b) :
    ∃ b w'', (Impl.Internal.loopPow2 step d s >>= k) w = .ok b w'' ∧ resPost b := by
  rw [io_bind_eq]
  rcases loopPow2_io_ok step inv post hStep d s hs w with ⟨r, w', h1, hr⟩
  rw [h1]
  exact hk r w' hr

theorem writeAllRetryEintr_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (h : RawFd) (data : ByteArray) (off depth : Nat) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.writeAllRetryEintr raw h data off depth w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  unfold Impl.Internal.writeAllRetryEintr
  refine loopPow2_io_bind_ok _ (fun _ => True)
    (fun (out : Except PostForkError Unit) => ∀ e, out = .error e → e.kind = .sysError)
    depth off trivial w _ _ (fun curOff w0 _ => by
      by_cases hc : curOff ≥ data.size
      · refine ⟨.inr (.ok ()), w0, ?_, fun e he => by cases he⟩
        simp [hc, io_pure_eq]
      · simp only [hc, ↓reduceIte]
        rw [io_bind_eq]
        rcases hRaw.writeOnce_ok h data (UInt64.ofNat curOff) (UInt64.ofNat (data.size - curOff)) w0 with ⟨rw, w1, hw⟩
        rw [hw]
        dsimp only
        cases rw with
        | ok n =>
          by_cases hn : n == 0
          · exact ⟨.inr (.error (Impl.Internal.mkSysErr 5 "host write returned zero bytes")), w1,
              by simp only [hn, ↓reduceIte, io_pure_eq], fun e he => by cases he; rfl⟩
          · exact ⟨.inl (curOff + n.toNat), w1, by simp only [hn, Bool.false_eq_true, ↓reduceIte, io_pure_eq], trivial⟩
        | error e =>
          by_cases he4 : e == 4
          · exact ⟨.inl curOff, w1, by simp only [he4, ↓reduceIte, io_pure_eq], trivial⟩
          · exact ⟨.inr (.error (Impl.Internal.mkSysErr e "host write failed")), w1,
              by simp only [he4, Bool.false_eq_true, ↓reduceIte, io_pure_eq], fun err herr => by cases herr; rfl⟩)
    (fun r1 w1 hr1 => by
      cases r1 with
      | inr out => exact ⟨out, w1, rfl, hr1⟩
      | inl finalOff =>
        by_cases hf : finalOff ≥ data.size
        · exact ⟨.ok (), w1, by simp only [hf, ↓reduceIte, io_pure_eq], fun e he => by cases he⟩
        · exact ⟨.error (Impl.Internal.mkSysErr 5 "host write exceeded retry fuel"), w1,
            by simp only [hf, ↓reduceIte, io_pure_eq], fun e he => by cases he; rfl⟩)

theorem readAllRetryEintr_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (h : RawFd) (cap : UInt64) (acc : ByteArray) (depth : Nat) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.readAllRetryEintr raw h cap acc depth w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  unfold Impl.Internal.readAllRetryEintr
  refine loopPow2_io_bind_ok _ (fun _ => True)
    (fun (out : Except PostForkError ByteArray) => ∀ e, out = .error e → e.kind = .sysError)
    depth (if acc.size == 0 then #[] else #[acc]) trivial w _ _ (fun curChunks w0 _ => by
      rw [io_bind_eq]
      rcases hRaw.readOnce_ok h cap w0 with ⟨rr, w1, hr⟩
      rw [hr]
      dsimp only
      cases rr with
      | ok chunk =>
        by_cases hs : chunk.size == 0
        · exact ⟨.inr (.ok (Impl.Internal.concatByteChunks curChunks)), w1,
            by simp only [hs, ↓reduceIte, io_pure_eq], fun e he => by cases he⟩
        · exact ⟨.inl (curChunks.push chunk), w1, by simp only [hs, Bool.false_eq_true, ↓reduceIte, io_pure_eq], trivial⟩
      | error e =>
        by_cases he4 : e == 4
        · exact ⟨.inl curChunks, w1, by simp only [he4, ↓reduceIte, io_pure_eq], trivial⟩
        · exact ⟨.inr (.error (Impl.Internal.mkSysErr e "host read failed")), w1,
            by simp only [he4, Bool.false_eq_true, ↓reduceIte, io_pure_eq], fun err herr => by cases herr; rfl⟩)
    (fun r1 w1 hr1 => by
      cases r1 with
      | inr out => exact ⟨out, w1, rfl, hr1⟩
      | inl _ => exact ⟨.error (Impl.Internal.mkSysErr 5 "host read exceeded retry fuel"), w1, rfl,
          fun e he => by cases he; rfl⟩)

theorem waitRetryEintr_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (pid : Pid) (depth : Nat) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.waitRetryEintr raw pid depth w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  unfold Impl.Internal.waitRetryEintr
  refine loopPow2_io_bind_ok _ (fun _ => True)
    (fun (out : Except PostForkError ChildWaitStatus) => ∀ e, out = .error e → e.kind = .sysError)
    depth () trivial w _ _ (fun _ w0 _ => by
      rw [io_bind_eq]
      rcases hRaw.waitOnce_ok pid w0 with ⟨rw, w1, hw⟩
      rw [hw]
      dsimp only
      cases rw with
      | ok st => exact ⟨.inr (.ok st), w1, rfl, fun e he => by cases he⟩
      | error e =>
        by_cases he4 : e == 4
        · exact ⟨.inl (), w1, by simp only [he4, ↓reduceIte, io_pure_eq], trivial⟩
        · exact ⟨.inr (.error (Impl.Internal.mkSysErr e "waitpid failed")), w1,
            by simp only [he4, Bool.false_eq_true, ↓reduceIte, io_pure_eq], fun err herr => by cases herr; rfl⟩)
    (fun r1 w1 hr1 => by
      cases r1 with
      | inr out => exact ⟨out, w1, rfl, hr1⟩
      | inl _ => exact ⟨.error (Impl.Internal.mkSysErr 4 "waitpid exceeded EINTR retry fuel"), w1, rfl,
          fun e he => by cases he; rfl⟩)

theorem closeListQuiet_ok (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (hs : List RawFd) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.closeListQuiet raw hs w = .ok r w' := by
  induction hs generalizing w with
  | nil => exact ⟨(), w, rfl⟩
  | cons h hs ih =>
    unfold Impl.Internal.closeListQuiet
    rw [io_bind_eq]
    rcases hRaw.closeFd_ok h w with ⟨_, w1, h1⟩
    rw [h1]
    exact ih w1

theorem probeRefList_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (rs : List (FdRef RawFd)) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.probeRefList raw rs w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  induction rs generalizing w with
  | nil => exact ⟨.ok (), w, rfl, fun e he => by cases he⟩
  | cons r rs ih =>
    unfold Impl.Internal.probeRefList Impl.Internal.probeRef
    cases r with
    | raw n =>
      dsimp only
      rw [io_bind_eq, io_bind_eq]
      rcases hRaw.probeFdOpen_ok n w with ⟨rp, w1, hp⟩
      rw [hp]
      dsimp only
      cases rp with
      | error e => exact ⟨.error _, w1, rfl, fun err herr => by cases herr; rfl⟩
      | ok _ => dsimp only; exact ih w1
    | handle h =>
      dsimp only
      rw [io_bind_eq, io_bind_eq]
      rcases hRaw.probeHandleOpen_ok h w with ⟨rp, w1, hp⟩
      rw [hp]
      dsimp only
      cases rp with
      | error e => exact ⟨.error _, w1, rfl, fun err herr => by cases herr; rfl⟩
      | ok _ => dsimp only; exact ih w1

theorem probeStdioPlan_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (st : StdioPlan RawFd) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.probeStdioPlan raw st w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  cases st with
  | inherit => exact ⟨.ok (), w, rfl, fun e he => by cases he⟩
  | redirect sIn sOut sErr _ => exact probeRefList_sysOnly raw hRaw [sIn, sOut, sErr] w

theorem filterOpenCloseList_ok (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (rs : List (FdRef RawFd)) (acc : Array (FdRef RawFd)) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.filterOpenCloseList raw rs acc w = .ok r w' := by
  induction rs generalizing acc w with
  | nil => exact ⟨acc, w, rfl⟩
  | cons r rs ih =>
    unfold Impl.Internal.filterOpenCloseList
    cases r with
    | handle h => exact ih (acc.push (.handle h)) w
    | raw n =>
      dsimp only
      rw [io_bind_eq]
      rcases hRaw.probeFdOpen_ok n w with ⟨rp, w1, hp⟩
      rw [hp]
      cases rp with
      | ok _ => exact ih (acc.push (.raw n)) w1
      | error _ => exact ih acc w1

theorem appendBytesImpl_eq (a b : ByteArray) :
    appendBytesImpl a b = appendBytes a b := rfl

theorem decodeChildFailureImpl_eq (bs : ByteArray) :
    decodeChildFailureImpl bs = decodeChildFailure bs := rfl

theorem flagsOfSpecImpl_eq {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) :
    flagsOfSpecImpl spec withBarrier = flagsOfSpec spec withBarrier := rfl

theorem keepFdsImpl_eq {fd : Type} (p : FdPolicy fd) :
    keepFdsImpl p = FdPolicy.keepFds p := rfl

theorem formatEnvEntriesBytesImpl_eq (rawEnv : Array ByteArray) (env : Array (String × String)) :
    formatEnvEntriesBytesImpl rawEnv env = formatEnvEntriesBytes rawEnv env := rfl

theorem validateSpecImpl_eq {fd : Type} (spec : ChildSpecM fd) :
    validateSpecImpl spec = validateSpec spec := rfl

theorem performFork_sysOnly (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (spec : ChildSpec) (syncRead? : Option RawFd) (errWrite : RawFd)
    (openCloseFds extraClose : Array (FdRef RawFd)) (withBarrier : Bool) (w : Void IO.RealWorld) :
    ∃ r w', Impl.Internal.performFork raw spec syncRead? errWrite openCloseFds extraClose withBarrier w = .ok r w' ∧
      (∀ e, r = .error e → e.kind = .sysError) := by
  unfold Impl.Internal.performFork
  rw [flagsOfSpecImpl_eq, keepFdsImpl_eq, formatEnvEntriesBytesImpl_eq]
  rw [io_bind_eq]
  rcases hRaw.forkRun_ok (flagsOfSpec spec withBarrier) spec.forkMode syncRead? errWrite
      (Impl.Internal.stdioRefsArray spec.stdio) (openCloseFds ++ extraClose)
      (FdPolicy.keepFds spec.fdPolicy) spec.cwd spec.path spec.argv (formatEnvEntriesBytes spec.rawEnv spec.env) w
    with ⟨rf, w1, hf⟩
  rw [hf]
  dsimp only
  cases rf with
  | error err =>
    dsimp only
    exact ⟨.error _, w1, rfl, fun e he => by cases he; rfl⟩
  | ok pid =>
    dsimp only
    cases hPg : spec.processGroup with
    | inherit =>
      dsimp only
      exact ⟨.ok pid, w1, rfl, fun e he => by cases he⟩
    | newGroup =>
      dsimp only
      rw [io_bind_eq]
      rcases hRaw.setpgidOnce_ok pid pid w1 with ⟨_, w2, hsg⟩
      rw [hsg]
      exact ⟨.ok pid, w2, rfl, fun e he => by cases he⟩

theorem awaitExecOrFailure_never_invalidInput (raw : PosixHostOpsM IO RawFd) (hRaw : NoThrowOps raw)
    (pid : Pid) (pgid? : Option Pid) (errRead : RawFd) (fuel : Nat) (w : Void IO.RealWorld)
    (barrierBroken : Bool := false) :
    ∃ r w', Impl.Internal.awaitExecOrFailure raw pid pgid? errRead fuel barrierBroken w = .ok r w' ∧
      (∀ e, r = .error e → e.kind ≠ .invalidInput) := by
  unfold Impl.Internal.awaitExecOrFailure
  rw [io_bind_eq]
  rcases readAllRetryEintr_sysOnly raw hRaw errRead 16 ByteArray.empty fuel w with ⟨rr, w1, hr, hrr⟩
  rw [hr]
  dsimp only
  rw [io_bind_eq]
  rcases hRaw.closeFd_ok errRead w1 with ⟨_, w2, hc⟩
  rw [hc]
  dsimp only
  cases rr with
  | error err =>
    dsimp only
    exact ⟨.error err, w2, rfl, fun e he hKind => by cases he; have hSys := hrr err rfl; rw [hSys] at hKind; cases hKind⟩
  | ok repBytes =>
    dsimp only
    rw [decodeChildFailureImpl_eq]
    cases hDec : decodeChildFailure repBytes with
    | none =>
      cases barrierBroken with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨.ok { pid := pid, pgid := pgid? }, w2, rfl, fun e he => by cases he⟩
      | true =>
        simp only [↓reduceIte]
        rw [io_bind_eq]
        rcases waitRetryEintr_sysOnly raw hRaw pid fuel w2 with ⟨rw, w3, hw, hrw⟩
        rw [hw]
        dsimp only
        cases rw with
        | error err =>
          exact ⟨.error err, w3, rfl, fun e he hKind => by cases he; have hSys := hrw err rfl; rw [hSys] at hKind; cases hKind⟩
        | ok wst =>
          exact ⟨.error _, w3, rfl, fun e he hKind => by cases he; cases hKind⟩
    | some cf =>
      dsimp only
      rw [io_bind_eq]
      rcases waitRetryEintr_sysOnly raw hRaw pid fuel w2 with ⟨rw, w3, hw, hrw⟩
      rw [hw]
      dsimp only
      cases rw with
      | error err =>
        exact ⟨.error err, w3, rfl, fun e he hKind => by cases he; have hSys := hrw err rfl; rw [hSys] at hKind; cases hKind⟩
      | ok wst =>
        exact ⟨.error _, w3, rfl, fun e he hKind => by cases he; cases hKind⟩

private theorem baseIO_lift_noThrow {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ r w', (liftM act : IO α) w = .ok r w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

/-- Pure `Prop` witness that `defaultOps` wraps a non-throwing `PosixHostOpsM IO RawFd` table (`Exists` cannot eliminate into `Type` or `IO`). -/
theorem defaultOps_exists_noThrow :
    ∃ raw : LeanSwe.PostFork.Impl.Internal.PosixHostOpsM IO RawFd,
      LeanSwe.PostFork.defaultOps = LeanSwe.PostFork.Impl.Internal.mkHostOps raw ∧
      NoThrowOps raw := by
  unfold LeanSwe.PostFork.defaultOps
  refine ⟨_, rfl, ?_⟩
  exact
    { probeFdOpen_ok := fun _ w => baseIO_lift_noThrow _ w
      probeHandleOpen_ok := fun _ w => baseIO_lift_noThrow _ w
      mkPipeCloexec_ok := fun w => baseIO_lift_noThrow _ w
      closeFd_ok := fun _ w => baseIO_lift_noThrow _ w
      setpgidOnce_ok := fun _ _ w => baseIO_lift_noThrow _ w
      writeOnce_ok := fun _ _ _ _ w => baseIO_lift_noThrow _ w
      readOnce_ok := fun _ _ w => baseIO_lift_noThrow _ w
      waitOnce_ok := fun _ w => baseIO_lift_noThrow _ w
      forkRun_ok := fun _ _ _ _ _ _ _ _ _ _ _ w => baseIO_lift_noThrow _ w }

end HostIoInvariants

end LeanSwe.PostFork.Proofs

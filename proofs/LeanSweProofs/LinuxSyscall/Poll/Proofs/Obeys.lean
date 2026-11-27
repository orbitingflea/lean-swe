import Core.Obeys
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSweProofs.LinuxSyscall.Poll.Model.Refines

/-!
# Capability-Parametric `Core.Obeys` Proofs for `LeanSwe.LinuxSyscall.Poll`

Proves `mkPollOpsM_obeysStepFrom`, `healthyModelOps_obeysStep`, and
`rawHealthyModelOps_obeysStep` for `LeanSwe.LinuxSyscall.Poll.Proofs.obeys_model`.
-/

namespace LeanSwe.LinuxSyscall.Poll.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Poll

@[simp] private theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

@[simp] private theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

@[simp] private theorem stateT_map_eq {W α β : Type} (g : α → β) (x : StateM W α) (w : W) :
    StateT.map g x w = (g (x w).1, (x w).2) := rfl

private theorem pollEvents_ofBits_toBits' (ev : PollEvents) : PollEvents.ofBits ev.toBits = ev := by
  rcases ev with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

private theorem pollEvents_toBits_lt' (ev : PollEvents) : ev.toBits < 32 := by
  rcases ev with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem pollEvents_beq_refl' (ev : PollEvents) : (ev == ev) = true := by
  rcases ev with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

local instance : LawfulBEq PollEvents where
  eq_of_beq {a b} h := by
    rcases a with ⟨a1, a2, a3, a4, a5⟩
    rcases b with ⟨b1, b2, b3, b4, b5⟩
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;>
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      first | rfl | exact absurd h (by decide)
  rfl {a} := pollEvents_beq_refl' a

private theorem ui8_ofNat_toUInt32_of_lt' {x : UInt32} (h : x < 32) :
    (UInt8.ofNat x.toNat).toUInt32 = x := by
  have hNat : x.toNat < 32 := h
  have hMod : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (Nat.lt_trans hNat (by decide))
  apply UInt32.toNat_inj.mp
  change x.toNat % 256 = x.toNat
  exact hMod

private theorem decodeRawEventFdFlags?_toBits (f : EventFdFlags) :
    Model.decodeRawEventFdFlags? f.toBits = some f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem decodeRawPollEventByte?_encode (ev : PollEvents) :
    Model.decodeRawPollEventByte? (UInt8.ofNat ev.toBits.toNat) = some ev := by
  unfold Model.decodeRawPollEventByte?
  rw [ui8_ofNat_toUInt32_of_lt' (pollEvents_toBits_lt' ev)]
  simp [pollEvents_toBits_lt' ev, pollEvents_ofBits_toBits' ev]

private theorem decodeRawPollEntriesList_encode :
    ∀ xs : List (HandleId × PollEvents),
      Model.decodeRawPollEntriesList
        (xs.map Prod.fst)
        (xs.map (fun (_, ev) => UInt8.ofNat ev.toBits.toNat)) = some xs
  | [] => rfl
  | (hid, ev) :: rest => by
    simp only [List.map_cons, Model.decodeRawPollEntriesList,
      decodeRawPollEventByte?_encode ev, decodeRawPollEntriesList_encode rest]

private theorem decodeRawPollEntries?_encode (entries : Array (HandleId × PollEvents)) :
    Model.decodeRawPollEntries? (encodePollRequests entries).1 (encodePollRequests entries).2 =
      some entries := by
  unfold Model.decodeRawPollEntries? encodePollRequests
  simp only [Array.toList_map, decodeRawPollEntriesList_encode entries.toList,
    Option.map_some, Array.toArray_toList]

private theorem decodeRawPollTimeout?_some (ts : Timespec) (hTs : ts.isValid = true) :
    Model.decodeRawPollTimeout? 1 ts.sec.toUInt64 ts.nsec = some (some ts) := by
  rcases ts with ⟨sec, nsec⟩
  have hSec : sec.toUInt64.toInt64 = sec := rfl
  unfold Model.decodeRawPollTimeout?
  have h0 : ((1 : UInt8) == 0) = false := by decide
  simp [h0, hSec, hTs]

private theorem healthyStep_ppoll_preErr {env : HealthyEnv}
    {entries : Array (HandleId × PollEvents)} {timeout : Option Timespec}
    (hWf : env.wf = true)
    (hPre : preCheckPoll (.ppoll entries timeout) = some Errno.EINVAL) :
    healthyStep env (.ppoll entries timeout) (.err Errno.EINVAL) = some env := by
  rcases env with ⟨st, budget⟩
  unfold healthyStep allowedStep
  have hNoCrit : isCriticalFault (.err Errno.EINVAL) = false := by decide
  have hNoEi : isEintrOutcome (.err Errno.EINVAL) = false := by decide
  simp [hWf, hNoCrit, hNoEi, stepPollCore, hPre]

/-- `Internal.mkPollOpsM` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem mkPollOpsM_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkPollOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | eventfd2 initval flags =>
    have hStep := hRaw w (.eventfd2 initval flags.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execPollReq,
      Internal.mkPollOpsM, Functor.map, Bind.bind, Pure.pure, StateT.run,
      stateT_map_eq, Model.allowedPkgStep, decodeRawEventFdFlags?_toBits] at hStep ⊢
    rcases hCall : raw.eventfd2 initval flags.toBits w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawOpened, outcomeOfOpened] using hStep
  | ppoll entries timeout =>
    cases timeout with
    | none =>
      by_cases hGt : entries.size > MAX_POLL_NFDS
      · simp only [Model.execPkgStep, execPollReq, Internal.mkPollOpsM,
          Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq,
          stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep, hGt, ↓reduceIte,
          outcomeOfPolled]
        have hPre : preCheckPoll (.ppoll entries none) = some Errno.EINVAL := by
          unfold preCheckPoll; simp [hGt]
        exact healthyStep_ppoll_preErr hWf hPre
      · have hLe : entries.size ≤ MAX_POLL_NFDS := Nat.le_of_not_gt hGt
        let enc := encodePollRequests entries
        have hStep := hRaw w (.ppoll enc.1 enc.2 0 0 0) hWf
        simp only [enc, Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execPollReq,
          Internal.mkPollOpsM, Functor.map, Bind.bind, Pure.pure, StateT.run,
          stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
          decodeRawPollEntries?_encode entries,
          show Model.decodeRawPollTimeout? 0 0 0 = some none from rfl,
          hLe, hGt, ↓reduceIte] at hStep ⊢
        rcases hCall : raw.ppoll (encodePollRequests entries).1 (encodePollRequests entries).2 0 0 0 w with ⟨res, w'⟩
        rw [hCall] at hStep
        cases res with
        | error e =>
          simpa [Model.outcomeOfRawPolled, outcomeOfPolled] using hStep
        | ok revBytes =>
          dsimp only [Model.outcomeOfRawPolled] at hStep
          rcases hStep with ⟨hSz, hPolled⟩
          have hNeF : (revBytes.size != entries.size) = false := by simp [hSz]
          simpa [hNeF, outcomeOfPolled] using hPolled
    | some ts =>
      cases hTs : ts.isValid with
      | false =>
        simp only [Model.execPkgStep, execPollReq, Internal.mkPollOpsM,
          Functor.map, Bind.bind, Pure.pure, StateT.run,
          stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
          hTs, Bool.not_false, ↓reduceIte, outcomeOfPolled]
        have hPre : preCheckPoll (.ppoll entries (some ts)) = some Errno.EINVAL := by
          unfold preCheckPoll; simp [hTs]
        exact healthyStep_ppoll_preErr hWf hPre
      | true =>
        by_cases hGt : entries.size > MAX_POLL_NFDS
        · simp only [Model.execPkgStep, execPollReq, Internal.mkPollOpsM,
            Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq,
            stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
            hTs, Bool.not_true, Bool.false_eq_true, hGt, ↓reduceIte, outcomeOfPolled]
          have hPre : preCheckPoll (.ppoll entries (some ts)) = some Errno.EINVAL := by
            unfold preCheckPoll; simp [hTs, hGt]
          exact healthyStep_ppoll_preErr hWf hPre
        · have hLe : entries.size ≤ MAX_POLL_NFDS := Nat.le_of_not_gt hGt
          let enc := encodePollRequests entries
          have hStep := hRaw w (.ppoll enc.1 enc.2 1 ts.sec.toUInt64 ts.nsec) hWf
          simp only [enc, Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execPollReq,
            Internal.mkPollOpsM, Functor.map, Bind.bind, Pure.pure, StateT.run,
            stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
            decodeRawPollEntries?_encode entries,
            decodeRawPollTimeout?_some ts hTs, hTs, Bool.not_true, Bool.false_eq_true,
            hLe, hGt, ↓reduceIte] at hStep ⊢
          rcases hCall : raw.ppoll (encodePollRequests entries).1 (encodePollRequests entries).2
            1 ts.sec.toUInt64 ts.nsec w with ⟨res, w'⟩
          rw [hCall] at hStep
          cases res with
          | error e =>
            simpa [Model.outcomeOfRawPolled, outcomeOfPolled] using hStep
          | ok revBytes =>
            dsimp only [Model.outcomeOfRawPolled] at hStep
            rcases hStep with ⟨hSz, hPolled⟩
            have hNeF : (revBytes.size != entries.size) = false := by simp [hSz]
            simpa [hNeF, outcomeOfPolled] using hPolled

private theorem freshPollHid_ge (fds : List (HandleId × PollDesc)) (n : HandleId) :
    n ≤ Model.freshPollHid fds n := by
  induction fds generalizing n with
  | nil => exact Nat.le_refl n
  | cons p rest ih =>
    unfold Model.freshPollHid
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left n (p.1 + 1)) (ih (max n (p.1 + 1)))

private theorem freshPollHid_gt_mem (fds : List (HandleId × PollDesc)) (n : HandleId) :
    ∀ p ∈ fds, p.1 < Model.freshPollHid fds n := by
  induction fds generalizing n with
  | nil => intro p hp; cases hp
  | cons hd rest ih =>
    intro p hp
    unfold Model.freshPollHid
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with hEq | hMem
    · subst hEq
      have h1 : p.1 + 1 ≤ max n (p.1 + 1) := Nat.le_max_right n (p.1 + 1)
      have h2 := freshPollHid_ge rest (max n (p.1 + 1))
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self p.1) (Nat.le_trans h1 h2)
    · exact ih (max n (hd.1 + 1)) p hMem

private theorem assocGet_none_of_lt (fds : List (HandleId × PollDesc)) (hid : HandleId)
    (hLt : ∀ p ∈ fds, p.1 < hid) :
    assocGet fds hid = none := by
  induction fds with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨k, d⟩
    have hk : k < hid := hLt (k, d) (List.mem_cons_self ..)
    have hNe : (k == hid) = false := beq_false_of_ne (Nat.ne_of_lt hk)
    simp only [assocGet, hNe, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun p hp => hLt p (List.mem_cons_of_mem _ hp))

private theorem preCheckPoll_eq_some_einval {req : PollReq} {e : Errno}
    (h : preCheckPoll req = some e) :
    e = Errno.EINVAL := by
  cases req with
  | eventfd2 _ _ => simp [preCheckPoll] at h
  | ppoll entries timeout =>
    unfold preCheckPoll at h
    split at h <;> simp_all

private theorem evalPollListAux_err_eq_ebadf (s : PollState) :
    ∀ (xs : List (HandleId × PollEvents)) (acc : List PollEvents) (e : Errno),
      evalPollListAux s xs acc = .error e → e = Errno.EBADF
  | [], _, _, h => by simp [evalPollListAux] at h
  | (hid, reqEv) :: rest, acc, e, h => by
    simp only [evalPollListAux] at h
    cases hGet : assocGet s.fds hid with
    | none =>
      simp only [hGet, Except.error.injEq] at h
      exact h.symm
    | some desc =>
      simp only [hGet] at h
      exact evalPollListAux_err_eq_ebadf s rest (computeDescRevents desc reqEv :: acc) e h

private theorem evalPollListAux_len (s : PollState) :
    ∀ (xs : List (HandleId × PollEvents)) (acc revList : List PollEvents),
      evalPollListAux s xs acc = .ok revList →
      revList.length = acc.length + xs.length
  | [], acc, revList, h => by
    simp only [evalPollListAux, Except.ok.injEq] at h
    subst h; simp
  | (hid, reqEv) :: rest, acc, revList, h => by
    simp only [evalPollListAux] at h
    cases hGet : assocGet s.fds hid with
    | none => simp [hGet] at h
    | some desc =>
      simp only [hGet] at h
      have ih := evalPollListAux_len s rest (computeDescRevents desc reqEv :: acc) revList h
      simp only [List.length_cons] at ih ⊢
      omega

private theorem healthyStep_of_coreSome {env : HealthyEnv} {req : PollReq}
    {out : PollOutcome} {s' : PollState}
    (hWf : env.wf = true)
    (hCore : (stepPollCore env.state req (some out)).map Prod.snd = some s')
    (hNoCrit : isCriticalFault out = false)
    (hNoEi : isEintrOutcome out = false) :
    healthyStep env req out = some { env with state := s' } := by
  rcases env with ⟨st, budget⟩
  unfold healthyStep allowedStep
  simp [hWf, hNoCrit, hNoEi, hCore]

/-- `Model.healthyModelOps` satisfies `Model.allowedPkgStep` from every well-formed `HealthyEnv`. -/
theorem healthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep := by
  intro env req hWf
  rcases env with ⟨⟨fds, nextHid, softNofile?, ambientSeccomp⟩, budget⟩
  let st : PollState := { fds := fds, nextHid := nextHid, softNofile? := softNofile?, ambientSeccomp := ambientSeccomp }
  dsimp only [id] at hWf ⊢
  cases req with
  | eventfd2 initval flags =>
    simp only [Model.execPkgStep, execPollReq, Model.healthyModelOps, Functor.map,
      Bind.bind, Pure.pure, get, getThe, MonadState.get, MonadStateOf.get, StateT.get,
      set, StateT.set, StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq,
      Model.allowedPkgStep, outcomeOfOpened]
    let hid := Model.freshPollHid fds nextHid
    have hNone : assocGet fds hid = none :=
      assocGet_none_of_lt fds hid (freshPollHid_gt_mem fds nextHid)
    have hGe : nextHid ≤ hid := freshPollHid_ge fds nextHid
    have hMax : max nextHid (hid + 1) = hid + 1 :=
      Nat.max_eq_right (Nat.le_succ_of_le hGe)
    apply healthyStep_of_coreSome hWf _ rfl rfl
    simp [hid, stepPollCore, hNone, hMax]
  | ppoll entries timeout =>
    simp only [Model.execPkgStep, execPollReq, Model.healthyModelOps, Functor.map,
      Bind.bind, Pure.pure, get, getThe, MonadState.get, MonadStateOf.get, StateT.get,
      StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedPkgStep]
    cases hPre : preCheckPoll (.ppoll entries timeout) with
    | some preErr =>
      simp only [stateT_pure_eq, outcomeOfPolled]
      have hEq := preCheckPoll_eq_some_einval hPre
      subst hEq
      exact healthyStep_ppoll_preErr hWf hPre
    | none =>
      dsimp only
      cases hPin : evalPollList st entries.toList with
      | error pinErr =>
        simp only [stateT_pure_eq, outcomeOfPolled]
        have hEq := evalPollListAux_err_eq_ebadf st entries.toList [] pinErr hPin
        subst hEq
        dsimp only [st] at hPin
        apply healthyStep_of_coreSome hWf _ (by decide) (by decide)
        dsimp only [stepPollCore]
        rw [hPre, hPin]
        simp
      | ok revList =>
        dsimp only
        have hLen : revList.length = entries.size := by
          simpa using evalPollListAux_len st entries.toList [] revList hPin
        dsimp only [st] at hPin
        cases softNofile? with
        | some lim =>
          by_cases hGt : entries.size > lim
          · simp only [hGt, decide_true, ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
            apply healthyStep_of_coreSome hWf _ (by decide) (by decide)
            dsimp only [stepPollCore]
            rw [hPre, hPin]
            simp [hGt]
          · simp only [hGt, decide_false, Bool.false_eq_true, ↓reduceIte]
            by_cases hAny : revList.any (fun ev => !ev.isEmpty) = true
            · simp only [hAny, Bool.not_true, Bool.false_and, Bool.false_eq_true,
                ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
              apply healthyStep_of_coreSome hWf _ rfl rfl
              dsimp only [stepPollCore]
              rw [hPre, hPin]
              simp [hGt, hAny, hLen]
            · have hAnyF : revList.any (fun ev => !ev.isEmpty) = false := Bool.eq_false_iff.mpr hAny
              cases timeout with
              | none =>
                simp only [hAnyF, Bool.not_false, Option.isNone_none, Bool.and_self,
                  ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
                apply healthyStep_of_coreSome hWf _ (by decide) (by decide)
                have hTr : Errno.EMFILE.isTransientOsErrno = true := by decide
                dsimp only [stepPollCore]
                rw [hPre, hPin]
                simp [hGt, hTr]
              | some ts =>
                simp only [hAnyF, Bool.not_false, Option.isNone_some, Bool.and_false,
                  Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
                apply healthyStep_of_coreSome hWf _ rfl rfl
                dsimp only [stepPollCore]
                rw [hPre, hPin]
                simp [hGt, hAnyF, hLen]
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hAny : revList.any (fun ev => !ev.isEmpty) = true
          · simp only [hAny, Bool.not_true, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
            apply healthyStep_of_coreSome hWf _ rfl rfl
            dsimp only [stepPollCore]
            rw [hPre, hPin]
            simp [hAny, hLen]
          · have hAnyF : revList.any (fun ev => !ev.isEmpty) = false := Bool.eq_false_iff.mpr hAny
            cases timeout with
            | none =>
              simp only [hAnyF, Bool.not_false, Option.isNone_none, Bool.and_self,
                ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
              apply healthyStep_of_coreSome hWf _ (by decide) (by decide)
              have hTr : Errno.EMFILE.isTransientOsErrno = true := by decide
              dsimp only [stepPollCore]
              rw [hPre, hPin]
              simp [hTr]
            | some ts =>
              simp only [hAnyF, Bool.not_false, Option.isNone_some, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, outcomeOfPolled]
              apply healthyStep_of_coreSome hWf _ rfl rfl
              dsimp only [stepPollCore]
              rw [hPre, hPin]
              simp [hAnyF, hLen]

private theorem byteArray_foldlM_id_loop (f : Array PollEvents → UInt8 → Array PollEvents)
    (raw : ByteArray) (hStop : raw.size ≤ raw.size) :
    ∀ (i j : Nat) (acc : Array PollEvents),
      i + j = raw.size →
      Id.run (ByteArray.foldlM.loop (m := Id) (fun a b => pure (f a b)) raw raw.size hStop i j acc) =
        (raw.data.toList.drop j).foldl f acc
  | 0, j, acc, hSum => by
    unfold ByteArray.foldlM.loop
    have hEq : j = raw.size := by omega
    subst hEq
    have hNotLt : ¬ (raw.size < raw.size) := Nat.lt_irrefl _
    have hDrop : raw.data.toList.drop raw.size = [] := by
      rw [List.drop_eq_nil_iff, Array.length_toList]
      exact Nat.le_refl _
    simp [hNotLt, hDrop, Pure.pure, Id.run]
  | i + 1, j, acc, hSum => by
    unfold ByteArray.foldlM.loop
    have hLt : j < raw.size := by omega
    have hLtList : j < raw.data.toList.length := by
      rw [Array.length_toList]; exact hLt
    have hGet : raw[j]'hLt = raw.data.toList[j]'hLtList := rfl
    simp only [hLt, ↓reduceDIte, Bind.bind, Pure.pure]
    rw [hGet, List.drop_eq_getElem_cons hLtList, List.foldl_cons]
    exact byteArray_foldlM_id_loop f raw hStop i (j + 1)
      (f acc (raw.data.toList[j]'hLtList)) (by omega)

private theorem list_foldl_push_decodePollEvents (xs : List PollEvents) (acc : Array PollEvents) :
    (xs.map (fun ev => UInt8.ofNat ev.toBits.toNat)).foldl
      (fun a b => a.push (PollEvents.ofBits b.toUInt32)) acc = acc ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => simp
  | cons ev rest ih =>
    simp only [List.map_cons, List.foldl_cons,
      ui8_ofNat_toUInt32_of_lt' (pollEvents_toBits_lt' ev),
      pollEvents_ofBits_toBits' ev, ih]
    apply Array.ext'
    simp

private theorem decodePollRevents_encode (revents : Array PollEvents) :
    decodePollRevents (ByteArray.mk (revents.map (fun ev => UInt8.ofNat ev.toBits.toNat))) =
      revents := by
  let raw := ByteArray.mk (revents.map (fun ev => UInt8.ofNat ev.toBits.toNat))
  change Id.run (ByteArray.foldlM (fun acc b => pure (acc.push (PollEvents.ofBits b.toUInt32))) #[] raw 0 raw.size) = revents
  unfold ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  rw [byteArray_foldlM_id_loop _ raw (Nat.le_refl raw.size) raw.size 0 #[] (Nat.add_zero _)]
  have hData : raw.data.toList.drop 0 = revents.toList.map (fun ev => UInt8.ofNat ev.toBits.toNat) := by
    simp [raw]
  rw [hData, list_foldl_push_decodePollEvents revents.toList #[]]
  simp

private theorem healthyStep_polled_size {env env' : HealthyEnv}
    {entries : Array (HandleId × PollEvents)} {timeout : Option Timespec}
    {revents : Array PollEvents}
    (h : healthyStep env (.ppoll entries timeout) (.polled revents) = some env') :
    revents.size = entries.size := by
  unfold healthyStep at h
  by_cases hG : (!env.wf || isCriticalFault (.polled revents)) = true
  · simp [hG] at h
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at h
    unfold allowedStep at h
    have hSec : env.state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hG
      cases hb : env.state.ambientSeccomp <;> simp_all [isCriticalFault]
    cases hCore : stepPollCore env.state (.ppoll entries timeout) (some (.polled revents)) with
    | none => simp [hCore, hSec] at h
    | some p =>
      dsimp only [stepPollCore] at hCore
      cases hPre : preCheckPoll (.ppoll entries timeout) with
      | some _ => rw [hPre] at hCore; simp at hCore
      | none =>
        rw [hPre] at hCore
        dsimp only at hCore
        cases hPin : evalPollList env.state entries.toList with
        | error _ => rw [hPin] at hCore; simp at hCore
        | ok revList =>
          rw [hPin] at hCore
          simp at hCore
          exact hCore.2.1

/-- `Model.rawHealthyModelOps` satisfies `Model.allowedRawStep` from every well-formed `HealthyEnv`. -/
theorem rawHealthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | eventfd2 initval flagsBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hFlg : Model.decodeRawEventFdFlags? flagsBits with
    | none => simp [Model.outcomeOfRawOpened]
    | some flags =>
      dsimp only
      have hStep := healthyModelOps_obeysStep env (.eventfd2 initval flags) hWf
      simp only [id, Model.execPkgStep, execPollReq, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.eventfd2 initval flags env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawOpened, outcomeOfOpened] using hStep
  | ppoll fds reqBytes hasTimeout secBits nsec =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hEnt : Model.decodeRawPollEntries? fds reqBytes with
    | none => simp [Model.outcomeOfRawPolled]
    | some entries =>
      cases hTo : Model.decodeRawPollTimeout? hasTimeout secBits nsec with
      | none => simp [Model.outcomeOfRawPolled]
      | some timeout =>
        dsimp only
        by_cases hLe : entries.size ≤ MAX_POLL_NFDS
        · simp only [hLe, ↓reduceIte, stateT_bind_eq]
          have hStep := healthyModelOps_obeysStep env (.ppoll entries timeout) hWf
          simp only [id, Model.execPkgStep, execPollReq, Functor.map,
            StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
          rcases hCall : Model.healthyModelOps.ppoll entries timeout env with ⟨res, env'⟩
          rw [hCall] at hStep
          cases res with
          | error e =>
            simpa [Model.outcomeOfRawPolled, outcomeOfPolled] using hStep
          | ok revents =>
            simp only [stateT_pure_eq, Model.outcomeOfRawPolled]
            dsimp only [outcomeOfPolled] at hStep
            have hSz : (ByteArray.mk (revents.map (fun ev => UInt8.ofNat ev.toBits.toNat))).size =
                entries.size := by
              change (revents.map (fun ev => UInt8.ofNat ev.toBits.toNat)).size = entries.size
              rw [Array.size_map]
              exact healthyStep_polled_size hStep
            rw [decodePollRevents_encode revents]
            exact ⟨hSz, hStep⟩
        · simp [hLe, Model.outcomeOfRawPolled]

end LeanSwe.LinuxSyscall.Poll.Proofs

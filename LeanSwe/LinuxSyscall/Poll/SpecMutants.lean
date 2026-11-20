import LeanSwe.LinuxSyscall.Poll.SpecTests

namespace LeanSwe.LinuxSyscall.Poll

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def stubPollOps : PollOpsM (StateM Unit) Nat :=
  { ppoll := fun entries _ => pure (.ok (entries.toList.map (fun _ => ({} : PollEvents))).toArray)
    eventfd2 := fun _ _ => pure (.ok 0) }

private theorem exists_hugePollEntries :
    ∃ arr : Array (Nat × PollEvents), arr.size > MAX_POLL_NFDS := by
  refine ⟨(List.replicate (MAX_POLL_NFDS + 1) ((0 : Nat), ({} : PollEvents))).toArray, ?_⟩
  rw [List.size_toArray, List.length_replicate]
  exact Nat.lt_succ_self MAX_POLL_NFDS

/-- Mutant treating `EFAULT` as a transient OS errno is rejected by `test_poll_errno_classification`. -/
theorem mutant_poll_efault_transient : ¬ Core.AllPass (test_poll_errno_classification
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    PollErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_poll_errno_classification
    Errno.isTransientOsErrno
    (fun e => if e == Errno.EINTR then .transientOrResource else PollErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.EINTR
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (encEv := fun ev => { ev with pollin := ev.pollout, pollout := ev.pollin }.toBits)
    (decEv := fun b =>
      let ev := PollEvents.ofBits b
      { ev with pollin := ev.pollout, pollout := ev.pollin })
    (encReq := fun entries =>
      encodePollRequests (entries.map (fun (fd, ev) => (fd, { ev with pollin := ev.pollout, pollout := ev.pollin }))))
    (decRev := fun raw =>
      (decodePollRevents raw).map (fun ev => { ev with pollin := ev.pollout, pollout := ev.pollin }))) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 {} {}
  exact absurd h1.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (encEv := fun ev => { ev with pollnval := false }.toBits)) := by
  intro h
  have h0 := h { pollnval := false } { pollnval := true }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (encEfd := fun f => { f with semaphore := false }.toBits)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 { semaphore := false } { semaphore := true }
  exact absurd h1.1 (by decide)

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (validTs := fun ts => ts.nsec < NANOS_PER_SEC)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 {} {}
  exact absurd h1.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval stubPollOps) := by
  intro h
  rcases exists_hugePollEntries with ⟨huge, hHuge⟩
  have h0 := h () #[] { sec := -1, nsec := 0 } (by decide) huge hHuge
  dsimp only [stubPollOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.1

example : ¬ Core.AllPass (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval
    { stubPollOps with
      ppoll := fun _ timeout =>
        match timeout with
        | some ts =>
          if !ts.isValid then pure (.error Errno.EINVAL)
          else pure (.ok #[])
        | none => pure (.ok #[]) }) := by
  intro h
  rcases exists_hugePollEntries with ⟨huge, hHuge⟩
  have h0 := h () #[] { sec := -1, nsec := 0 } (by decide) huge hHuge
  dsimp only [stubPollOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  have hBad := h0.2.2.1
  have hValid : (Timespec.mk 0 0).isValid = true := by decide
  rw [hValid] at hBad
  cases hBad

example : ¬ Core.AllPass (test_poll_ops_eventfdReadinessAndTimeouts stubPollOps ()) := by
  intro h
  have hEq := h.2.1.1
  dsimp only [stubPollOps, Bind.bind, StateT.run, pure, StateT.pure] at hEq
  injection hEq with hArr
  exact absurd hArr (by decide)

example : ¬ Core.AllPass (test_poll_ops_eventfdReadinessAndTimeouts
    { modelOps with
      ppoll := fun entries _ => do
        let s ← get
        match evalPollList s entries.toList with
        | .error e => return .error e
        | .ok revList => return .ok revList.toArray } PollState.initial) := by
  intro h
  have hBad := h.2.2.2.2.1
  change (Except.ok #[{}] : Except Errno (Array PollEvents)) = Except.error Errno.EINTR at hBad
  cases hBad

example : ¬ Core.AllPass (test_poll_state_counterSemaphoreCloseAndOutputFlags
    { modelOps with
      eventfd2 := fun initval flags =>
        modelOps.eventfd2 initval { flags with semaphore := false } }) := by
  intro h
  have hEq := h.2.2.2.2.2.2.2.1
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_poll_state_counterSemaphoreCloseAndOutputFlags
    { modelOps with
      ppoll := fun entries _ =>
        pure (.ok (entries.toList.map (fun _ => ({ pollout := true } : PollEvents))).toArray) }) := by
  intro h
  have hEq := h.2.2.2.1
  dsimp only [Bind.bind, StateT.run, pure, StateT.pure] at hEq
  injection hEq with hArr
  exact absurd hArr (by decide)

example : ¬ Core.AllPass (test_poll_model_allowedStep_invariants
    (fun s req out =>
      match req, out with
      | .ppoll entries _, .err e =>
        if entries.size > 0 && e == Errno.EINVAL then none
        else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_allowedStep_invariants
    (fun s req out =>
      match req, out with
      | .ppoll entries none, .polled got =>
        if got.size == entries.size then some s else none
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_allowedStep_invariants
    (fun s req out =>
      match req, out with
      | .ppoll _ _, .polled _ => some s
      | _, _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_softNofileAndAmbientSeccomp
    (fun s req out => allowedStep { s with softNofile? := none } req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_softNofileAndAmbientSeccomp
    (fun s req out => allowedStep { s with ambientSeccomp := false } req out)) := by
  intro h
  exact absurd h.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_softNofileAndAmbientSeccomp
    (fun s req out =>
      if s.ambientSeccomp then
        match out with
        | .err _ => some s
        | _ => allowedStep s req out
      else allowedStep s req out)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_poll_model_stepCoreSound (fun _ _ _ => none)) := by
  intro h
  have hStep : stepPollCore PollState.initial (.eventfd2 0 {}) none =
      some (.opened 0, { PollState.initial with fds := [(0, { kind := .eventfd 0 {} })], nextHid := 1 }) := rfl
  have h0 := h PollState.initial (.eventfd2 0 {}) (.opened 0)
    { PollState.initial with fds := [(0, { kind := .eventfd 0 {} })], nextHid := 1 } rfl hStep
  cases h0.1

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (defEfd := { nonblock := false, cloexec := false, semaphore := false })) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 {} {}
  exact absurd h1.2.2.2.2.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_poll_mkPollOps_encodesAndDelegates
    (fun raw =>
      { ppoll := fun _ _ => Except.error Errno.ENOSYS
        eventfd2 := fun _ _ => raw.eventfd2 0 0 })) := by
  intro h
  have hLe : (#[] : Array (Nat × PollEvents)).size ≤ MAX_POLL_NFDS := Nat.zero_le _
  have hTs : ({ sec := 0, nsec := 0 } : Timespec).isValid = true := by decide
  have h0 := (h (fun _ _ _ _ _ => Except.ok (ByteArray.mk #[])) (fun iv fl => Except.ok (iv.toNat + fl.toNat))
    #[] hLe { sec := 0, nsec := 0 } hTs 3 {}).1
  change (Except.ok 0 : Except Errno Nat) = Except.ok 5 at h0
  injection h0 with hNat
  exact absurd hNat (by decide)

example : ¬ Core.AllPass (test_poll_mkPollOps_encodesAndDelegates
    (fun raw =>
      { ppoll := fun entries _ =>
          let (fds, reqBytes) := encodePollRequests entries
          match raw.ppoll fds reqBytes 1 0 0 with
          | .error e => Except.error e
          | .ok revBytes => Except.ok (decodePollRevents revBytes)
        eventfd2 := fun initval flags => raw.eventfd2 initval flags.toBits })) := by
  intro h
  have hLe : (#[] : Array (Nat × PollEvents)).size ≤ MAX_POLL_NFDS := Nat.zero_le _
  have hTs : ({ sec := 0, nsec := 0 } : Timespec).isValid = true := by decide
  have h0 := (h (fun _ _ ht _ _ => if ht == 0 then Except.ok (ByteArray.mk #[]) else Except.error Errno.EINVAL)
    (fun _ _ => Except.ok 0) #[] hLe { sec := 0, nsec := 0 } hTs 0 {}).2.1
  have hOk := congrArg Except.isOk h0
  change false = true at hOk
  cases hOk

example : ¬ Core.AllPass (test_poll_interface_defaultOpsWiring (m := Id) (fd := Nat)
    (fun _ => { ppoll := fun _ _ => Except.error Errno.ENOSYS, eventfd2 := fun _ _ => Except.error Errno.ENOSYS })
    { ppoll := fun _ _ => Except.ok #[], eventfd2 := fun _ _ => Except.error Errno.ENOSYS }
    (fun _ _ => Except.ok #[])
    (fun _ => Except.ok #[])
    (fun _ _ => Except.error Errno.ENOSYS)
    (Except.error Errno.ENOSYS)) := by
  intro h
  rcases (h #[] none 0 {}).1 with ⟨_, hEq⟩
  have hApp := congrArg (fun o => o.ppoll #[] none) hEq
  change (Except.ok (#[] : Array PollEvents) : Except Errno (Array PollEvents)) = Except.error Errno.ENOSYS at hApp
  cases hApp

example : ¬ Core.AllPass (test_poll_interface_defaultOpsWiring (m := Id) (fd := Nat)
    (fun raw =>
      { ppoll := fun _ timeout =>
          match timeout with
          | none =>
            match raw.ppoll #[] (ByteArray.mk #[]) 0 0 0 with
            | _ => Except.error Errno.EINTR
          | some _ => Except.ok #[]
        eventfd2 := fun iv fl => raw.eventfd2 iv fl.toBits })
    { ppoll := fun _ timeout =>
        match timeout with
        | none => Except.error Errno.EINTR
        | some _ => Except.ok #[]
      eventfd2 := fun _ _ => Except.ok 0 }
    (fun _ timeout =>
      match timeout with
      | none => Except.error Errno.EINTR
      | some _ => Except.ok #[])
    (fun _ => Except.ok #[])
    (fun _ _ => Except.ok 0)
    (Except.ok 0)) := by
  intro h
  have hDef := (h #[] none 0 {}).2.2.1
  change (Except.ok (#[] : Array PollEvents) : Except Errno (Array PollEvents)) = Except.error Errno.EINTR at hDef
  cases hDef

example : ¬ Core.AllPass (test_poll_flags_and_codecs_roundtripAndInjective
    (decRev := fun raw => (decodePollRevents raw).extract 0 2)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 {} {}
  have h2 := h1.2.2.2.2.2.2.2.2.2.2.2.2 { pollin := true }
  have hEq : (decodePollRevents (encodePollRequests #[(10, {}), (20, {}), (30, { pollin := true })]).2).extract 0 2 =
      #[{}, {}, { pollin := true }] := h2.1.2.2.2.2.2
  have hLe : ((decodePollRevents (encodePollRequests #[(10, {}), (20, {}), (30, { pollin := true })]).2).extract 0 2).size ≤ 2 := by
    rw [Array.size_extract]; omega
  rw [hEq] at hLe
  exact absurd hLe (by decide)

example : ¬ Core.AllPass (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval
    { stubPollOps with
      ppoll := fun entries timeout =>
        match timeout with
        | some ts =>
          if !ts.isValid || entries.size > MAX_POLL_NFDS then pure (.error Errno.EINVAL)
          else pure (.ok #[])
        | none => pure (.ok #[]) }) := by
  intro h
  rcases exists_hugePollEntries with ⟨huge, hHuge⟩
  have h0 := h () #[] { sec := -1, nsec := 0 } (by decide) huge hHuge
  dsimp only [stubPollOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.2.2.2.1

end LeanSwe.LinuxSyscall.Poll

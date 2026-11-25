import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.Impl
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.Proofs.IpPolicyProofs
import LeanSwe.ConnectProxy.Proofs.ParserAndModelProofs
import LeanSwe.ConnectProxy.Proofs.RingBufHelpers

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

/-!
Relational `healthyStep` refinement and behavioral invariant proofs for `LeanSwe.ConnectProxy`
(`Relay`, `SysBridge`, `Impl`, and `Interface`) over `LeanSwe.LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}`.
-/

/-- Everyday network, signal, permission, and per-process resource errnos (`EINTR`, `EAGAIN`, `EMFILE`, `ENOSPC`, `EADDRINUSE`, `EACCES`, `EPERM`, `ECONNREFUSED`, `ETIMEDOUT`, `ENETUNREACH`, `EHOSTUNREACH`, `EPIPE`, `ECONNRESET`, `ENOTCONN`, `EINVAL`) are never classified as catastrophic OS faults, and `EMFILE`/`ENOSPC` are classified as everyday resource limits. -/
theorem everyday_errnos_not_critical :
    Errno.isResourceLimitErrno Errno.EMFILE = true ∧
    Errno.isResourceLimitErrno Errno.ENOSPC = true ∧
    Errno.isCriticalOsErrno Errno.EINTR = false ∧
    Errno.isCriticalOsErrno Errno.EAGAIN = false ∧
    Errno.isCriticalOsErrno Errno.EMFILE = false ∧
    Errno.isCriticalOsErrno Errno.ENOSPC = false ∧
    Errno.isCriticalOsErrno Errno.EADDRINUSE = false ∧
    Errno.isCriticalOsErrno Errno.EACCES = false ∧
    Errno.isCriticalOsErrno Errno.EPERM = false ∧
    Errno.isCriticalOsErrno Errno.ECONNREFUSED = false ∧
    Errno.isCriticalOsErrno Errno.ETIMEDOUT = false ∧
    Errno.isCriticalOsErrno Errno.ENETUNREACH = false ∧
    Errno.isCriticalOsErrno Errno.EHOSTUNREACH = false ∧
    Errno.isCriticalOsErrno Errno.EPIPE = false ∧
    Errno.isCriticalOsErrno Errno.ECONNRESET = false ∧
    Errno.isCriticalOsErrno Errno.ENOTCONN = false ∧
    Errno.isCriticalOsErrno Errno.EINVAL = false := by
  decide

/-- Compositional bundle-refinement bridge: independent subsystem implementations refining `Files.RefinesHealthyFiles` (`Files.RefinesHealthyFilesAt`), `Net.RefinesHealthyNet` (`Net.RefinesHealthyNetAt`), `Poll.RefinesHealthyPoll` (`Poll.RefinesHealthyPollAt`), `Dns.RefinesHealthyDns` (`Dns.RefinesHealthyDnsAt`), and `TimeRand.RefinesHealthyTimeRand` (`TimeRand.RefinesHealthyTimeRandAt`) lift cleanly onto `HealthySysWorld` to satisfy `RefinesHealthyCProxySys` (`RefinesHealthyCProxySysAt`). -/
theorem refinesHealthyBundles_implies_cproxySys
    (filesOps : Files.FilesOpsM (StateM Files.HealthyEnv) Files.HandleId)
    (netOps : Net.NetOpsM (StateM Net.HealthyEnv) Net.HandleId)
    (pollOps : Poll.PollOpsM (StateM Poll.HealthyEnv) Poll.HandleId)
    (dnsOps : Dns.DnsOpsM (StateM Dns.HealthyEnv))
    (timeOps : TimeRand.TimeRandOpsM (StateM TimeRand.HealthyEnv))
    (hFiles : Files.RefinesHealthyFiles filesOps)
    (hNet : Net.RefinesHealthyNet netOps)
    (hPoll : Poll.RefinesHealthyPoll pollOps)
    (hDns : Dns.RefinesHealthyDns dnsOps)
    (hTime : TimeRand.RefinesHealthyTimeRand timeOps)
    (hFilesWf : ∀ env req out env', Files.healthyStep env req out = some env' → env'.wf = true)
    (hNetWf : ∀ env req out env', Net.healthyStep env req out = some env' → env'.wf = true)
    (hPollWf : ∀ env req out env', Poll.healthyStep env req out = some env' → env'.wf = true)
    (hDnsWf : ∀ env req out env', Dns.healthyStep env req out = some env' → env'.wf = true)
    (hTimeWf : ∀ env req out env', TimeRand.healthyStep env req out = some env' → env'.wf = true) :
    Files.RefinesHealthyFilesAt id filesOps ∧
    Net.RefinesHealthyNetAt id netOps ∧
    Poll.RefinesHealthyPollAt id pollOps ∧
    Dns.RefinesHealthyDnsAt id dnsOps ∧
    TimeRand.RefinesHealthyTimeRandAt id timeOps ∧
    RefinesHealthyCProxySys
      { files :=
          { openat := fun d p fl m w => let (r, e') := (filesOps.openat d p fl m).run w.filesEnv; (r, { w with filesEnv := e' })
            openat2 := fun d p how w => let (r, e') := (filesOps.openat2 d p how).run w.filesEnv; (r, { w with filesEnv := e' })
            close := fun h w => let (r, e') := (filesOps.close h).run w.filesEnv; (r, { w with filesEnv := e' })
            read := fun h n w => let (r, e') := (filesOps.read h n).run w.filesEnv; (r, { w with filesEnv := e' })
            write := fun h bs w => let (r, e') := (filesOps.write h bs).run w.filesEnv; (r, { w with filesEnv := e' })
            fstat := fun h w => let (r, e') := (filesOps.fstat h).run w.filesEnv; (r, { w with filesEnv := e' })
            fstatat := fun d p fl w => let (r, e') := (filesOps.fstatat d p fl).run w.filesEnv; (r, { w with filesEnv := e' })
            faccessat := fun d p m fl w => let (r, e') := (filesOps.faccessat d p m fl).run w.filesEnv; (r, { w with filesEnv := e' })
            mkdirat := fun d p m w => let (r, e') := (filesOps.mkdirat d p m).run w.filesEnv; (r, { w with filesEnv := e' })
            unlinkat := fun d p rd w => let (r, e') := (filesOps.unlinkat d p rd).run w.filesEnv; (r, { w with filesEnv := e' })
            renameat2 := fun od op nd np fl w => let (r, e') := (filesOps.renameat2 od op nd np fl).run w.filesEnv; (r, { w with filesEnv := e' })
            symlinkat := fun t d lp w => let (r, e') := (filesOps.symlinkat t d lp).run w.filesEnv; (r, { w with filesEnv := e' })
            readlinkat := fun d p c w => let (r, e') := (filesOps.readlinkat d p c).run w.filesEnv; (r, { w with filesEnv := e' })
            getdents64 := fun h c w => let (r, e') := (filesOps.getdents64 h c).run w.filesEnv; (r, { w with filesEnv := e' })
            fchmodat := fun d p m w => let (r, e') := (filesOps.fchmodat d p m).run w.filesEnv; (r, { w with filesEnv := e' })
            fchmod := fun h m w => let (r, e') := (filesOps.fchmod h m).run w.filesEnv; (r, { w with filesEnv := e' })
            flock := fun h op w => let (r, e') := (filesOps.flock h op).run w.filesEnv; (r, { w with filesEnv := e' })
            fcntl := fun h cmd w => let (r, e') := (filesOps.fcntl h cmd).run w.filesEnv; (r, { w with filesEnv := e' })
            fsync := fun h w => let (r, e') := (filesOps.fsync h).run w.filesEnv; (r, { w with filesEnv := e' })
            getcwd := fun c w => let (r, e') := (filesOps.getcwd c).run w.filesEnv; (r, { w with filesEnv := e' })
            lseek := fun h off wh w => let (r, e') := (filesOps.lseek h off wh).run w.filesEnv; (r, { w with filesEnv := e' })
            reopenReadOnly := fun h w => let (r, e') := (filesOps.reopenReadOnly h).run w.filesEnv; (r, { w with filesEnv := e' })
            dupStdio := fun sl w => let (r, e') := (filesOps.dupStdio sl).run w.filesEnv; (r, { w with filesEnv := e' }) }
        net :=
          { socket := fun dom st fl p w => let (r, e') := (netOps.socket dom st fl p).run w.netEnv; (r, { w with netEnv := e' })
            socketpair := fun dom st fl w => let (r, e') := (netOps.socketpair dom st fl).run w.netEnv; (r, { w with netEnv := e' })
            bind := fun h sa w => let (r, e') := (netOps.bind h sa).run w.netEnv; (r, { w with netEnv := e' })
            listen := fun h bl w => let (r, e') := (netOps.listen h bl).run w.netEnv; (r, { w with netEnv := e' })
            accept4 := fun h fl w => let (r, e') := (netOps.accept4 h fl).run w.netEnv; (r, { w with netEnv := e' })
            connect := fun h sa w => let (r, e') := (netOps.connect h sa).run w.netEnv; (r, { w with netEnv := e' })
            getsockopt := fun h opt w => let (r, e') := (netOps.getsockopt h opt).run w.netEnv; (r, { w with netEnv := e' })
            setsockopt := fun h opt val w => let (r, e') := (netOps.setsockopt h opt val).run w.netEnv; (r, { w with netEnv := e' })
            getsockname := fun h w => let (r, e') := (netOps.getsockname h).run w.netEnv; (r, { w with netEnv := e' })
            recvfrom := fun h n fl w => let (r, e') := (netOps.recvfrom h n fl).run w.netEnv; (r, { w with netEnv := e' })
            sendto := fun h bs fl w => let (r, e') := (netOps.sendto h bs fl).run w.netEnv; (r, { w with netEnv := e' })
            shutdown := fun h how w => let (r, e') := (netOps.shutdown h how).run w.netEnv; (r, { w with netEnv := e' })
            sendmsg := fun h fds w => let (r, e') := (netOps.sendmsg h fds).run w.netEnv; (r, { w with netEnv := e' })
            recvmsg := fun h mf w => let (r, e') := (netOps.recvmsg h mf).run w.netEnv; (r, { w with netEnv := e' })
            ioctl := fun h op ifn w => let (r, e') := (netOps.ioctl h op ifn).run w.netEnv; (r, { w with netEnv := e' }) }
        poll :=
          { ppoll := fun fds to? w => let (r, e') := (pollOps.ppoll fds to?).run w.pollEnv; (r, { w with pollEnv := e' })
            eventfd2 := fun iv fl w => let (r, e') := (pollOps.eventfd2 iv fl).run w.pollEnv; (r, { w with pollEnv := e' }) }
        dns :=
          { getaddrinfo := fun host hints w => let (r, e') := (dnsOps.getaddrinfo host hints).run w.dnsEnv; (r, { w with dnsEnv := e' }) }
        timeRand :=
          { clock_gettime := fun clk w => let (r, e') := (timeOps.clock_gettime clk).run w.timeEnv; (r, { w with timeEnv := e' })
            clock_nanosleep := fun clk abs ts w => let (r, e') := (timeOps.clock_nanosleep clk abs ts).run w.timeEnv; (r, { w with timeEnv := e' })
            getrandom := fun n fl w => let (r, e') := (timeOps.getrandom n fl).run w.timeEnv; (r, { w with timeEnv := e' }) } } := by
  refine ⟨hFiles, hNet, hPoll, hDns, hTime, ?_⟩
  unfold RefinesHealthyCProxySys RefinesHealthyCProxySysAt
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => ⟨id, id⟩⟩
  · intro w h hWf
    have hStep := hFiles w.filesEnv (.close h) hWf.1
    dsimp only [Files.execFilesReq, Functor.map, StateT.map, StateT.run, Id.run] at hStep ⊢
    exact ⟨hStep, ⟨hFilesWf _ _ _ _ hStep, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl⟩
  · intro w req hWf
    have hStep := hNet w.netEnv req hWf.2.1
    cases req <;>
      (dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, Id.run] at hStep ⊢;
       exact ⟨hStep, ⟨hWf.1, hNetWf _ _ _ _ hStep, hWf.2.2.1, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl, id⟩)
  · intro w req hWf
    have hStep := hPoll w.pollEnv req hWf.2.2.1
    cases req <;>
      (dsimp only [Poll.execPollReq, Functor.map, StateT.map, StateT.run, Id.run] at hStep ⊢;
       exact ⟨hStep, ⟨hWf.1, hWf.2.1, hPollWf _ _ _ _ hStep, hWf.2.2.2.1, hWf.2.2.2.2⟩, rfl, id⟩)
  · intro w req hWf
    have hStep := hDns w.dnsEnv req hWf.2.2.2.1
    dsimp only [Dns.execDnsReq, StateT.run, Id.run] at hStep ⊢
    exact ⟨hStep, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hDnsWf _ _ _ _ hStep, hWf.2.2.2.2⟩, rfl, id⟩
  · intro w req hWf
    have hStep := hTime w.timeEnv req hWf.2.2.2.2
    cases req <;>
      (dsimp only [TimeRand.execTimeRandReq, Functor.map, StateT.map, StateT.run, Id.run] at hStep ⊢;
       exact ⟨hStep, ⟨hWf.1, hWf.2.1, hWf.2.2.1, hWf.2.2.2.1, hTimeWf _ _ _ _ hStep⟩, rfl, id⟩)

private theorem assocGet_append {α β : Type} [BEq α] (xs ys : List (α × β)) (j : α) :
    Files.assocGet (xs ++ ys) j =
      match Files.assocGet xs j with
      | some v => some v
      | none => Files.assocGet ys j := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.cons_append, Files.assocGet]
    by_cases h : (k == j) = true
    · simp [h]
    · simp [h, ih]

private theorem assocGet_none_of_not_mem_fst {β : Type} :
    ∀ (xs : List (Nat × β)) (j : Nat),
      j ∉ xs.map Prod.fst → Files.assocGet xs j = none
  | [], _, _ => rfl
  | (k, _) :: tl, j, hNotMem => by
    simp only [List.map_cons, List.mem_cons, not_or] at hNotMem
    have hNe : (k == j) = false := beq_false_of_ne (Ne.symm hNotMem.1)
    simp only [Files.assocGet, hNe, Bool.false_eq_true, ↓reduceIte]
    exact assocGet_none_of_not_mem_fst tl j hNotMem.2

private theorem assocErase_sublist_and_laws {β : Type} (k : Nat) :
    ∀ (xs acc : List (Nat × β)),
      (∀ x ∈ acc, x.1 ≠ k) →
      (Files.assocEraseAux xs k acc = acc.reverse ++ xs ∨
       ∃ l1 l2 v, acc.reverse ++ xs = l1 ++ (k, v) :: l2 ∧ Files.assocEraseAux xs k acc = l1 ++ l2)
  | [], acc, _ => Or.inl (by simp [Files.assocEraseAux])
  | (k', v') :: rest, acc, hAcc => by
    by_cases hEq : (k' == k) = true
    · have hk : k' = k := beq_iff_eq.mp hEq
      subst hk
      refine Or.inr ⟨acc.reverse, rest, v', by simp, ?_⟩
      simp [Files.assocEraseAux]
    · have hEqF : (k' == k) = false := Bool.eq_false_iff.mpr hEq
      have hNe : k' ≠ k := fun h => hEq (beq_iff_eq.mpr h)
      have hSub := assocErase_sublist_and_laws k rest ((k', v') :: acc) (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hTail
        · exact hNe
        · exact hAcc x hTail)
      simp only [Files.assocEraseAux, hEqF, Bool.false_eq_true, ↓reduceIte]
      simpa [List.reverse_cons, List.append_assoc] using hSub

private theorem assocErase_nodup_and_get_none {β : Type} (xs : List (Nat × β)) (k : Nat) :
    ((xs.map Prod.fst).Nodup →
      ((Files.assocErase xs k).map Prod.fst).Nodup ∧
      Files.assocGet (Files.assocErase xs k) k = none) ∧
    (∀ j, Files.assocGet xs j = none → Files.assocGet (Files.assocErase xs k) j = none) := by
  have hSpec := assocErase_sublist_and_laws k xs [] (fun _ h => nomatch h)
  simp only [List.reverse_nil, List.nil_append] at hSpec
  change ((xs.map Prod.fst).Nodup →
      ((Files.assocEraseAux xs k []).map Prod.fst).Nodup ∧
      Files.assocGet (Files.assocEraseAux xs k []) k = none) ∧
    (∀ j, Files.assocGet xs j = none → Files.assocGet (Files.assocEraseAux xs k []) j = none)
  have hGetNonePres : ∀ (a b : List (Nat × β)) (j : Nat),
      Files.assocGet (a ++ b) j = none → Files.assocGet a j = none ∧ Files.assocGet b j = none := by
    intro a b j hNone
    rw [assocGet_append] at hNone
    cases hGa : Files.assocGet a j with
    | some _ => rw [hGa] at hNone; cases hNone
    | none => rw [hGa] at hNone; exact ⟨rfl, hNone⟩
  rcases hSpec with hSame | ⟨l1, l2, v, hMid, hErased⟩
  · rw [hSame]
    refine ⟨fun hNd => ⟨hNd, ?_⟩, fun _ h => h⟩
    have hNoK : ∀ (ys acc : List (Nat × β)),
        (∀ x ∈ acc, x.1 ≠ k) →
        Files.assocEraseAux ys k acc = acc.reverse ++ ys →
        k ∉ (ys.map Prod.fst) := by
      intro ys
      induction ys with
      | nil => intro _ _ _; simp
      | cons hd tl ih =>
        rcases hd with ⟨k', v'⟩
        intro acc hAcc hEqAux
        by_cases hk : (k' == k) = true
        · have hkk : k' = k := beq_iff_eq.mp hk
          subst hkk
          simp only [Files.assocEraseAux, beq_self_eq_true, ↓reduceIte, List.reverseAux_eq] at hEqAux
          have hLen := congrArg List.length hEqAux
          simp at hLen
        · have hkF : (k' == k) = false := Bool.eq_false_iff.mpr hk
          have hNe : k' ≠ k := fun hc => hk (beq_iff_eq.mpr hc)
          simp only [Files.assocEraseAux, hkF, Bool.false_eq_true, ↓reduceIte] at hEqAux
          have hTailNot := ih ((k', v') :: acc) (by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | ht
            · exact hNe
            · exact hAcc x ht) (by simpa [List.reverse_cons, List.append_assoc] using hEqAux)
          simp [Ne.symm hNe, hTailNot]
    exact assocGet_none_of_not_mem_fst xs k (hNoK xs [] (fun _ h => nomatch h) hSame)
  · rw [hErased]
    refine ⟨fun hNd => ?_, fun j hNone => ?_⟩
    · rw [hMid, List.map_append, List.map_cons] at hNd
      have hSub : (l1.map Prod.fst ++ l2.map Prod.fst).Sublist (l1.map Prod.fst ++ k :: l2.map Prod.fst) :=
        List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self k _)
      have hNd2 : ((l1 ++ l2).map Prod.fst).Nodup := by
        rw [List.map_append]
        exact hSub.nodup hNd
      have hDisj := List.nodup_append.mp hNd
      have hNotInL2 : k ∉ l2.map Prod.fst := (List.nodup_cons.mp hDisj.2.1).1
      have hNotInL1 : k ∉ l1.map Prod.fst := fun hm => hDisj.2.2 k hm k (List.Mem.head _) rfl
      have hNotInBoth : k ∉ (l1 ++ l2).map Prod.fst := by
        rw [List.map_append, List.mem_append]
        exact fun h => h.elim hNotInL1 hNotInL2
      exact ⟨hNd2, assocGet_none_of_not_mem_fst (l1 ++ l2) k hNotInBoth⟩
    · rw [hMid] at hNone
      obtain ⟨hA, hRest⟩ := hGetNonePres l1 ((k, v) :: l2) j hNone
      have hB : Files.assocGet l2 j = none := by
        simp only [Files.assocGet] at hRest
        split at hRest
        · cases hRest
        · exact hRest
      rw [assocGet_append, hA, hB]

/-- Internal SysBridge helper lemma `wf_iff_parts`. -/
theorem wf_iff_parts (w : HealthySysWorld) :
    w.wf = true ↔
      (w.filesEnv.wf = true ∧ w.netEnv.wf = true ∧ w.pollEnv.wf = true ∧
       w.dnsEnv.wf = true ∧ w.timeEnv.wf = true) := by
  unfold HealthySysWorld.wf
  simp [Bool.and_eq_true, and_assoc]

/-- Internal SysBridge helper lemma `stateT_bind_run`. -/
theorem stateT_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    StateT.run (x >>= f) s = let (a, s') := StateT.run x s; StateT.run (f a) s' := rfl

/-- Internal SysBridge helper lemma `stateT_pure_run`. -/
theorem stateT_pure_run {σ α : Type} (a : α) (s : σ) :
    StateT.run (pure a : StateM σ α) s = (a, s) := rfl

/-- Internal SysBridge helper lemma `stateT_get_run`. -/
theorem stateT_get_run {σ : Type} (s : σ) :
    StateT.run (get : StateM σ σ) s = (s, s) := rfl

/-- Internal SysBridge helper lemma `stateT_set_run`. -/
theorem stateT_set_run {σ : Type} (s' s : σ) :
    StateT.run (set s' : StateM σ PUnit) s = ((), s') := rfl

/-- Internal SysBridge helper lemma `stateT_tryFinally_pure_run`. -/
theorem stateT_tryFinally_pure_run {σ α β : Type} (a : α) (fin : Option α → StateM σ β) (s : σ) :
    StateT.run (tryFinally' (pure a : StateM σ α) fin) s =
      let (b, s') := StateT.run (fin (some a)) s
      ((a, b), s') := rfl

/-- Internal SysBridge helper lemma `inst_net_socket`. -/
theorem inst_net_socket (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags) (p : UInt32)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.socket dom st fl p (w, tr) =
      let (r, w') := sys.net.socket dom st fl p w
      (r, (w', match r with | .ok h => { tr with openedFds := tr.openedFds.push h } | .error _ => tr)) := by
  unfold instrumentSysOps liftTraceOp
  dsimp only [StateT.run]
  rcases sys.net.socket dom st fl p w with ⟨r, _⟩
  cases r <;> rfl

/-- Internal SysBridge helper lemma `inst_net_socketpair`. -/
theorem inst_net_socketpair (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.socketpair dom st fl (w, tr) =
      let (r, w') := sys.net.socketpair dom st fl w
      (r, (w', match r with | .ok (h0, h1) => { tr with openedFds := (tr.openedFds.push h0).push h1 } | .error _ => tr)) := by
  unfold instrumentSysOps liftTraceOp
  dsimp only [StateT.run]
  rcases sys.net.socketpair dom st fl w with ⟨r, _⟩
  rcases r with _ | ⟨_, _⟩ <;> rfl

/-- Internal SysBridge helper lemma `inst_net_bind`. -/
theorem inst_net_bind (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (sa : Net.SockAddr) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.bind h sa (w, tr) =
      let (r, w') := sys.net.bind h sa w
      (r, (w', { tr with boundAddrs := tr.boundAddrs.push sa })) := rfl

/-- Internal SysBridge helper lemma `inst_net_listen`. -/
theorem inst_net_listen (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (bl : UInt32) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.listen h bl (w, tr) =
      let (r, w') := sys.net.listen h bl w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_net_accept4`. -/
theorem inst_net_accept4 (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (fl : Net.SockFlags) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.accept4 h fl (w, tr) =
      let (r, w') := sys.net.accept4 h fl w
      (r, (w', match r with
        | .ok (cfd, _) => { tr with openedFds := tr.openedFds.push cfd }
        | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e })) := by
  unfold instrumentSysOps liftTraceOp
  dsimp only [StateT.run]
  rcases sys.net.accept4 h fl w with ⟨r, _⟩
  rcases r with _ | ⟨_, _⟩ <;> rfl

/-- Internal SysBridge helper lemma `inst_net_connect`. -/
theorem inst_net_connect (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (sa : Net.SockAddr) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.connect h sa (w, tr) =
      let (r, w') := sys.net.connect h sa w
      (r, (w', { tr with dialedAddrs := tr.dialedAddrs.push sa })) := rfl

/-- Internal SysBridge helper lemma `inst_net_getsockopt`. -/
theorem inst_net_getsockopt (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (opt : Net.SockOpt) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.getsockopt h opt (w, tr) =
      let (r, w') := sys.net.getsockopt h opt w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_net_setsockopt`. -/
theorem inst_net_setsockopt (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (opt : Net.SetSockOpt) (val : UInt32) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.setsockopt h opt val (w, tr) =
      let (r, w') := sys.net.setsockopt h opt val w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_net_getsockname`. -/
theorem inst_net_getsockname (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.getsockname h (w, tr) =
      let (r, w') := sys.net.getsockname h w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_net_recvfrom`. -/
theorem inst_net_recvfrom (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (n : UInt32) (fl : Net.MsgFlags) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.recvfrom h n fl (w, tr) =
      let (r, w') := sys.net.recvfrom h n fl w
      (r, (w', match r with
        | .ok bs =>
          let k := Nat.min bs.size n.toNat
          let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
          { tr with recvBytes := tr.recvBytes ++ accepted }
        | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e })) := rfl

/-- Internal SysBridge helper lemma `inst_net_sendto`. -/
theorem inst_net_sendto (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (bs : ByteArray) (fl : Net.MsgFlags) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.sendto h bs fl (w, tr) =
      let (r, w') := sys.net.sendto h bs fl w
      (r, (w', match r with
        | .ok n =>
          let k := Nat.min n.toNat bs.size
          let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
          let zeroSend := tr.sawZeroSend || (n == 0 && bs.size > 0)
          { tr with sentBytes := tr.sentBytes ++ accepted, sawZeroSend := zeroSend }
        | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e })) := rfl

/-- Internal SysBridge helper lemma `inst_poll_ppoll`. -/
theorem inst_poll_ppoll (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (fds : Array (Nat × Poll.PollEvents)) (to? : Option Poll.Timespec)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).poll.ppoll fds to? (w, tr) =
      let (r, w') := sys.poll.ppoll fds to? w
      (r, (w', match r with
        | .ok _ => { tr with pollOutcomes := tr.pollOutcomes.push none }
        | .error e => { tr with pollOutcomes := tr.pollOutcomes.push (some e) })) := rfl

/-- Internal ConnectProxy proof helper `inst_net_shutdown`. -/
theorem inst_net_shutdown (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (h : Nat) (how : Net.ShutHow) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).net.shutdown h how (w, tr) =
      let (r, w') := sys.net.shutdown h how w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_dns_getaddrinfo`. -/
theorem inst_dns_getaddrinfo (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (host : String) (hints : Dns.ResolveHints) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).dns.getaddrinfo host hints (w, tr) =
      let (r, w') := sys.dns.getaddrinfo host hints w
      (r, (w', { tr with dnsQueries := tr.dnsQueries.push host })) := rfl

/-- Internal ConnectProxy proof helper `inst_time_gettime`. -/
theorem inst_time_gettime (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (clk : TimeRand.ClockId) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).timeRand.clock_gettime clk (w, tr) =
      let (r, w') := sys.timeRand.clock_gettime clk w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_time_nanosleep`. -/
theorem inst_time_nanosleep (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (clk : TimeRand.ClockId) (ab : Bool) (ts : TimeRand.Timespec)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).timeRand.clock_nanosleep clk ab ts (w, tr) =
      let (r, w') := sys.timeRand.clock_nanosleep clk ab ts w
      (r, (w', tr)) := rfl

/-- Internal SysBridge helper lemma `inst_files_close`. -/
theorem inst_files_close (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (d : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (instrumentSysOps sys).files.close d (w, tr) =
      let (r, w') := sys.files.close d w
      (r, (w', { tr with closedFds := tr.closedFds.push d })) := rfl

/-- Deterministic OS FD-table release under `RefinesHealthyCProxySys`: `closeFd` on `instrumentSysOps sys` executes in 1 `files.close` step (since healthy single-thread `close` excludes `EBUSY`), preserves `wf`, `Nodup`, and `proxyTable`, records `d` in `closedFds`, and erases `d` from `FilesState.fds`! -/
theorem healthy_closeFd_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w : HealthySysWorld)
    (tr : SysAuditTrace Nat)
    (d : Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := ((instrumentSysOps sys).closeFd d).run (w, tr)
    w'.wf = true ∧
    w'.proxyTable = w.proxyTable ∧
    tr' = { tr with closedFds := tr.closedFds.push d } ∧
    (∀ j, Files.assocGet w.filesEnv.state.fds j = none →
      Files.assocGet w'.filesEnv.state.fds j = none) ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup →
      (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
      Files.assocGet w'.filesEnv.state.fds d = none) := by
  have hCl := hRef.1 w d ((wf_iff_parts w).mp hWf)
  unfold CProxySysOpsM.closeFd closeSysFdAux
  dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run] at hCl ⊢
  rw [inst_files_close]
  rcases hRun : sys.files.close d w with ⟨r, w'⟩
  rw [hRun] at hCl
  dsimp only at hCl ⊢
  rcases hCl with ⟨hStep, hWf', hTbl⟩
  have hWfBool : w'.wf = true := (wf_iff_parts w').mpr hWf'
  have hNotBusy : ∀ e, r = .error e → (e == Errno.EBUSY) = false := by
    intro e hr
    subst hr
    apply Bool.eq_false_iff.mpr
    intro hB
    simp [Files.healthyStep, Files.outcomeOfUnit, Files.isCloseEbusy, hB] at hStep
  have hFdsRel :
      w'.filesEnv.state.fds = w.filesEnv.state.fds ∧ Files.assocGet w.filesEnv.state.fds d = none ∨
      w'.filesEnv.state.fds = Files.assocErase w.filesEnv.state.fds d := by
    unfold Files.healthyStep at hStep
    split at hStep
    · cases hStep
    · cases hAllow : Files.allowedStep w.filesEnv.state (.close d) (Files.outcomeOfUnit r) with
      | none => rw [hAllow] at hStep; cases hStep
      | some sMid =>
        rw [hAllow] at hStep
        dsimp only at hStep
        have hsEq : w'.filesEnv.state = sMid := by
          split at hStep
          · split at hStep
            · injection hStep with heq; exact (congrArg Files.HealthyEnv.state heq).symm
            · cases hStep
          · injection hStep with heq; exact (congrArg Files.HealthyEnv.state heq).symm
        rw [hsEq]
        unfold Files.allowedStep Files.allowedCloseStep at hAllow
        dsimp only at hAllow
        cases hGet : Files.assocGet w.filesEnv.state.fds d with
        | none =>
          rw [hGet] at hAllow
          dsimp only at hAllow
          unfold Files.verifyStep at hAllow
          dsimp only at hAllow
          split at hAllow
          · injection hAllow with hs; subst hs; exact Or.inl ⟨rfl, rfl⟩
          · cases hAllow
        | some desc =>
          rw [hGet] at hAllow
          dsimp only at hAllow
          have hNoSec : w.filesEnv.state.ambientSeccomp = false := by
            have hw0 := ((wf_iff_parts w).mp hWf).1
            unfold Files.HealthyEnv.wf at hw0
            simpa using hw0
          cases r with
          | ok _ =>
            dsimp only [Files.outcomeOfUnit] at hAllow
            injection hAllow with hs; subst hs
            exact Or.inr rfl
          | error e =>
            dsimp only [Files.outcomeOfUnit] at hAllow
            have hNb := hNotBusy e rfl
            simp only [hNb, Bool.false_eq_true, ↓reduceIte, hNoSec, Bool.false_and] at hAllow
            split at hAllow
            · split at hAllow
              · cases hAllow
              · injection hAllow with hs; subst hs; exact Or.inr rfl
            · cases hAllow
  have hPost :
      (∀ j, Files.assocGet w.filesEnv.state.fds j = none →
        Files.assocGet w'.filesEnv.state.fds j = none) ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup →
        (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
        Files.assocGet w'.filesEnv.state.fds d = none) := by
    rcases hFdsRel with ⟨hSame, hNoneD⟩ | hErase
    · rw [hSame]
      exact ⟨fun _ h => h, fun hNd => ⟨hNd, hNoneD⟩⟩
    · rw [hErase]
      have hLaws := assocErase_nodup_and_get_none w.filesEnv.state.fds d
      exact ⟨hLaws.2, hLaws.1⟩
  cases r with
  | ok _ =>
    exact ⟨hWfBool, hTbl, rfl, hPost.1, hPost.2⟩
  | error e =>
    have hNb := hNotBusy e rfl
    simp only [hNb, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hWfBool, hTbl, rfl, hPost.1, hPost.2⟩


end LeanSwe.ConnectProxy.Proofs

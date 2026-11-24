import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Net.Proofs.HealthyStep
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Poll.Proofs
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.Dns.Proofs
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.NetRelay.Proofs
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.Impl
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.Proofs.IpPolicyProofs
import LeanSwe.ConnectProxy.Proofs.ParserAndModelProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Proofs
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

/-- Internal SysBridge helper lemma `nat_min_eq_min`. -/
theorem nat_min_eq_min (a b : Nat) : Nat.min a b = min a b := rfl

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

private theorem inst_net_shutdown (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
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

private theorem inst_time_gettime (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
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

/-- Generic invariant and postcondition induction across bounded `EINTR` retry loops (`SysBridge.retryEintr`). -/
theorem retryEintr_preserves {W α : Type}
    (P : W → Prop)
    (Q : Except Errno α → W → Prop)
    (act : StateM W (Except Errno α))
    (hStep : ∀ w, P w →
      let (r, w') := act.run w
      P w' ∧ (r = .error Errno.EINTR ∨ Q r w')) :
    ∀ (fuel : Nat) (w : W), P w →
      let (r, w') := (retryEintr act fuel).run w
      P w' ∧ (r = .error Errno.EINTR ∨ Q r w')
  | 0, w, hw => hStep w hw
  | fuel + 1, w, hw => by
    have h0 := hStep w hw
    dsimp only [retryEintr, StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run] at h0 ⊢
    rcases hAct : act w with ⟨r0, w1⟩
    rw [hAct] at h0
    dsimp only at h0 ⊢
    rcases r0 with e | v
    · by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        exact retryEintr_preserves P Q act hStep fuel w1 h0.1
      · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
        simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
        refine ⟨h0.1, ?_⟩
        rcases h0.2 with hEq | hQ
        · injection hEq with he
          exact absurd (beq_iff_eq.mpr he) hEi
        · exact Or.inr hQ
    · exact ⟨h0.1, Or.inr (by
        rcases h0.2 with hBad | hQ
        · cases hBad
        · exact hQ)⟩

/-- Exact `eintrBudget` accounting across a single `Net.healthyStep`: `EINTR` requires `eintrBudget > 0` and decrements it by `1`; all other outcomes preserve `eintrBudget`. -/
theorem healthyNetStep_eintrBudget (env env' : Net.HealthyEnv) (req : Net.NetReq) (out : Net.NetOutcome)
    (h : Net.healthyStep env req out = some env') :
    (out = .err Errno.EINTR → env.eintrBudget > 0 ∧ env'.eintrBudget = env.eintrBudget - 1) ∧
    (out ≠ .err Errno.EINTR → env'.eintrBudget = env.eintrBudget) := by
  have ⟨_, _, _, _, _, hEi, hNe⟩ := Net.healthyStep_implies_allowedStep h
  refine ⟨fun hEq => hEi (by subst hEq; rfl), fun hNeOut => hNe ?_⟩
  cases out with
  | err e =>
    exact Bool.eq_false_iff.mpr fun hB =>
      hNeOut (congrArg Net.NetOutcome.err (beq_iff_eq.mp hB))
  | _ => rfl

/-- Generic `retryEintr` progress law with `eintrBudget` metric: when `budget w ≤ fuel`, `retryEintr fuel act` never returns `.error Errno.EINTR` and preserves `budget w' ≤ budget w`. -/
theorem retryEintr_budget_laws {W α : Type}
    (budget : W → Nat)
    (I : W → Prop)
    (Post : Except Errno α → W → Prop)
    (act : StateM W (Except Errno α))
    (hStep : ∀ w, I w →
      let (r, w') := act.run w
      (r = .error Errno.EINTR → I w' ∧ budget w > 0 ∧ budget w' = budget w - 1) ∧
      (r ≠ .error Errno.EINTR → budget w' ≤ budget w) ∧
      Post r w') :
    ∀ (fuel : Nat) (w : W), I w →
      let (r, w') := (retryEintr act fuel).run w
      Post r w' ∧ budget w' ≤ budget w ∧ (budget w ≤ fuel → r ≠ .error Errno.EINTR)
  | 0, w, hI => by
    have h0 := hStep w hI
    dsimp only [retryEintr, StateT.run] at h0 ⊢
    rcases hAct : act w with ⟨r0, w1⟩
    rw [hAct] at h0
    dsimp only at h0 ⊢
    refine ⟨h0.2.2, ?_, fun hBud0 hEi => ?_⟩
    · by_cases hEi : r0 = .error Errno.EINTR
      · have hb := h0.1 hEi; omega
      · exact h0.2.1 hEi
    · have hb := (h0.1 hEi).2.1
      omega
  | fuel + 1, w, hI => by
    have h0 := hStep w hI
    dsimp only [retryEintr, StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run] at h0 ⊢
    rcases hAct : act w with ⟨r0, w1⟩
    rw [hAct] at h0
    dsimp only at h0 ⊢
    rcases r0 with e | v
    · by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        have hEqEi : (Except.error e : Except Errno α) = .error Errno.EINTR :=
          congrArg Except.error (beq_iff_eq.mp hEi)
        obtain ⟨hI1, hPos, hDec⟩ := h0.1 hEqEi
        have hSub := retryEintr_budget_laws budget I Post act hStep fuel w1 hI1
        dsimp only [StateT.run] at hSub ⊢
        rcases hRec : retryEintr act fuel w1 with ⟨rFin, wFin⟩
        rw [hRec] at hSub
        dsimp only at hSub ⊢
        refine ⟨hSub.1, by omega, fun hBud => hSub.2.2 (by omega)⟩
      · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
        simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
        have hNe : (Except.error e : Except Errno α) ≠ .error Errno.EINTR := by
          intro hc; injection hc with he; exact hEi (beq_iff_eq.mpr he)
        exact ⟨h0.2.2, h0.2.1 hNe, fun _ => hNe⟩
    · have hNe : (Except.ok v : Except Errno α) ≠ .error Errno.EINTR := fun hc => nomatch hc
      exact ⟨h0.2.2, h0.2.1 hNe, fun _ => hNe⟩

private theorem sappend_nonempty_right (a b : String) (hb : b ≠ "") : a ++ b ≠ "" := by
  intro h
  exact hb (String.append_eq_empty_iff.mp h).2

/-- `Model.mapRawErrorPure` is total, preserves exact `(kind, errnoCode)`, and guarantees a non-empty message for all `ConnectProxyRawError` inputs. -/
theorem mapRawErrorPure_laws (raw : ConnectProxyRawError) :
    (Model.mapRawErrorPure raw).message ≠ "" ∧
    match raw with
    | .invalidArgument errno? _ =>
      (Model.mapRawErrorPure raw).kind = .invalidInput ∧ (Model.mapRawErrorPure raw).errnoCode = errno?
    | .addressInUse _ errno _ =>
      (Model.mapRawErrorPure raw).kind = .addressInUse ∧ (Model.mapRawErrorPure raw).errnoCode = some errno
    | .permissionDenied errno _ =>
      (Model.mapRawErrorPure raw).kind = .permissionDenied ∧ (Model.mapRawErrorPure raw).errnoCode = some errno
    | .resourceExhausted errno _ =>
      (Model.mapRawErrorPure raw).kind = .resourceExhausted ∧ (Model.mapRawErrorPure raw).errnoCode = some errno
    | .otherError errno _ =>
      (Model.mapRawErrorPure raw).kind = .ioError ∧ (Model.mapRawErrorPure raw).errnoCode = some errno
    | .userError _ =>
      (Model.mapRawErrorPure raw).kind = .ioError ∧ (Model.mapRawErrorPure raw).errnoCode = none := by
  cases raw with
  | invalidArgument errno? detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · decide
    · next h => intro he; subst he; simp [String.isEmpty] at h
  | addressInUse port errno detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · exact sappend_nonempty_right ("127.0.0.1:" ++ toString port) " is already in use" (by decide)
    · next h => intro he; subst he; simp [String.isEmpty] at h
  | permissionDenied errno detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · decide
    · next h => intro he; subst he; simp [String.isEmpty] at h
  | resourceExhausted errno detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · decide
    · next h => intro he; subst he; simp [String.isEmpty] at h
  | otherError errno detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · exact sappend_nonempty_right ("connect-proxy OS error (errno " ++ toString errno) ")" (by decide)
    · next h => intro he; subst he; simp [String.isEmpty] at h
  | userError detail =>
    refine ⟨?_, rfl, rfl⟩
    dsimp [Model.mapRawErrorPure]
    split
    · decide
    · next h => intro he; subst he; simp [String.isEmpty] at h

/-- `SysBridge.errnoToProxyError` maps everyday OS errnos (`EINVAL`, `EADDRINUSE`, `EACCES`/`EPERM`, `EMFILE`/`ENOBUFS`/`EAGAIN`) to their exact `ProxyErrorKind` with non-empty message. -/
theorem errnoToProxyError_laws (port : UInt16) (e : Errno) :
    (errnoToProxyError port e).message ≠ "" ∧
    (errnoToProxyError port e).errnoCode = some e ∧
    (e = Errno.EADDRINUSE → (errnoToProxyError port e).kind = .addressInUse) ∧
    (e = Errno.EACCES ∨ e = Errno.EPERM → (errnoToProxyError port e).kind = .permissionDenied) ∧
    (e = Errno.EMFILE ∨ e = Errno.EAGAIN ∨ e = Errno.ENOBUFS →
      (errnoToProxyError port e).kind = .resourceExhausted) := by
  have hMsg := (mapRawErrorPure_laws (classifyErrno port e)).1
  refine ⟨hMsg, ?_, ?_, ?_, ?_⟩
  · unfold errnoToProxyError classifyErrno
    repeat (first | split | rfl)
  · intro h; subst h; rfl
  · rintro (rfl | rfl) <;> rfl
  · rintro (rfl | rfl | rfl) <;> rfl

private theorem accepted_slice_toList (bs : ByteArray) (lim : Nat) :
    let k := Nat.min lim bs.size
    (if k == bs.size then bs.data else (bs.extract 0 k).data).toList =
      bs.data.toList.take lim := by
  simp only [nat_min_eq_min]
  by_cases hEq : (min lim bs.size == bs.size) = true
  · simp only [hEq, ↓reduceIte]
    have hGe : bs.size ≤ lim := by have := beq_iff_eq.mp hEq; omega
    exact (List.take_of_length_le (by simpa using hGe)).symm
  · have hEqF : (min lim bs.size == bs.size) = false := Bool.eq_false_iff.mpr hEq
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte, byteArray_extract_toList, List.drop_zero, Nat.sub_zero]
    have hLt : lim < bs.size := by
      have hNe : min lim bs.size ≠ bs.size := fun h => hEq (beq_iff_eq.mpr h)
      omega
    rw [Nat.min_eq_left (Nat.le_of_lt hLt)]

/-- Relational RX FIFO conservation and `EINTR` progress: over ANY `sys` refining `RefinesHealthyCProxySys`, `NetRelay.recvIntoRing` preserves `w'.wf`, rejects with `none` only on invalid-descriptor errors (`EBADF`/`EINVAL`/`ENOTSOCK`), preserves `rb.cap`, maintains `rb'.len ≤ rb.cap` and exact byte order `rb'.toList = rb.toList ++ rxDelta`, and progresses until full, `EOF`/peer-reset, or non-`EINTR` `netErrs` whenever `eintrBudget + (rb.cap - rb.len) ≤ fuel`. -/
theorem healthy_recvIntoRing_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      rb.len ≤ rb.cap →
      let (res, (w', tr')) := (NetRelay.recvIntoRing (instrumentSysOps sys).net fd fuel rb).run (w, tr)
      w'.wf = true ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      tr.netErrs.size ≤ tr'.netErrs.size ∧
      match res with
      | none =>
        ∃ e ∈ tr'.netErrs.toList,
          e ∈ tr.netErrs.toList ∨ (e = Errno.EBADF ∨ e = Errno.EINVAL ∨ e = Errno.ENOTSOCK)
      | some (rb', eof) =>
        rb'.len ≤ rb.cap ∧
        rb'.cap = rb.cap ∧
        (∃ rxDelta : List UInt8,
          tr'.recvBytes.toList = tr.recvBytes.toList ++ rxDelta ∧
          rb'.toList = rb.toList ++ rxDelta) ∧
        (w.netEnv.eintrBudget + (rb.cap - rb.len) ≤ fuel →
          rb'.writeAvail = 0 ∨ eof = true ∨ tr.netErrs.size < tr'.netErrs.size)
  | 0, rb, w, tr, hWf, hCap => by
    dsimp only [NetRelay.recvIntoRing, NetRelay.Internal.recvIntoRing, StateT.run, pure, StateT.pure]
    refine ⟨hWf, fun _ h => h, Nat.le_refl _, hCap, rfl, ⟨[], by simp, by simp⟩, fun hFuel => ?_⟩
    unfold RingBuf.writeAvail NetRelay.Internal.ringBufWriteAvail NetRelay.Internal.ringBufLen
    simp only [nat_min_eq_min]
    have hLenEq : rb.buf.size - rb.off = rb.len := rfl
    omega
  | fuel + 1, rb, w, tr, hWf, hCap => by
    unfold NetRelay.recvIntoRing NetRelay.Internal.recvIntoRing
    by_cases hAv0 : (NetRelay.Internal.ringBufWriteAvail rb == 0) = true
    · simp only [hAv0, ↓reduceIte]
      dsimp only [StateT.run, pure, StateT.pure]
      exact ⟨hWf, fun _ h => h, Nat.le_refl _, hCap, rfl, ⟨[], by simp, by simp⟩,
        fun _ => Or.inl (beq_iff_eq.mp hAv0)⟩
    · have hAvF : (NetRelay.Internal.ringBufWriteAvail rb == 0) = false := Bool.eq_false_iff.mpr hAv0
      simp only [hAvF, Bool.false_eq_true, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      let avail := NetRelay.Internal.ringBufWriteAvail rb
      let reqCap := Nat.min avail MAX_READ_BYTES.toNat
      let want := UInt32.ofNat reqCap
      have hAvailPos : avail > 0 := by
        have hNe : NetRelay.Internal.ringBufWriteAvail rb ≠ 0 := fun hc => hAv0 (beq_iff_eq.mpr hc)
        omega
      have hMaxVal : MAX_READ_BYTES.toNat = 16777216 := rfl
      have hReqCapPos : reqCap > 0 := by
        dsimp only [reqCap]; simp only [nat_min_eq_min]; omega
      have hReqCapLeAvail : reqCap ≤ avail := Nat.min_le_left _ _
      have hWantToNat : want.toNat = reqCap := by
        have hLt : reqCap < UInt32.size := by
          have : reqCap ≤ MAX_READ_BYTES.toNat := Nat.min_le_right _ _
          change reqCap < 4294967296; omega
        exact UInt32.toNat_ofNat_of_lt hLt
      have hTlLen : rb.toList.length = rb.len := ringBuf_toList_length_of_le_cap rb hCap
      have hAvailEq : avail = rb.cap - rb.toList.length := by
        unfold avail NetRelay.Internal.ringBufWriteAvail NetRelay.Internal.ringBufLen
        simp only [nat_min_eq_min]
        have hLenEq : rb.buf.size - rb.off = rb.len := rfl
        rw [hLenEq, Nat.min_eq_left hCap, hTlLen]
      have hLtCap : rb.len < rb.cap := by omega
      have hNet := hRef.2.1 w (.recvfrom fd want { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      rw [inst_net_recvfrom]
      rcases hRun : sys.net.recvfrom fd want { dontwait := true } w with ⟨r, w1⟩
      rw [hRun] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.recvfrom fd want { dontwait := true }) (Net.outcomeOfBytes r) hNet.1
      cases r with
      | ok bs =>
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget :=
          hBud.2 (fun hc => nomatch hc)
        by_cases hSz0 : (bs.size == 0) = true
        · simp only [hSz0, ↓reduceIte]
          dsimp only [StateT.run, pure, StateT.pure]
          have hSzEq : bs.size = 0 := beq_iff_eq.mp hSz0
          have hEmpty : bs.data.toList = [] :=
            List.eq_nil_of_length_eq_zero (by simpa using hSzEq)
          refine ⟨hWf1, fun _ h => h, Nat.le_refl _, hCap, rfl, ⟨[], ?_, by simp⟩, fun _ => Or.inr (Or.inl rfl)⟩
          simp [hSzEq, hEmpty]
        · have hSzF : (bs.size == 0) = false := Bool.eq_false_iff.mpr hSz0
          simp only [hSzF, Bool.false_eq_true, ↓reduceIte]
          have hBsPos : bs.size > 0 := by
            have hNe : bs.size ≠ 0 := fun hc => hSz0 (beq_iff_eq.mpr hc)
            omega
          let chunk := if bs.size ≤ reqCap then bs else bs.extract 0 reqCap
          have hChunkToList : chunk.data.toList = bs.data.toList.take reqCap := by
            dsimp only [chunk]
            by_cases hLe : bs.size ≤ reqCap
            · simp only [hLe, ↓reduceIte]
              exact (List.take_of_length_le (by simpa using hLe)).symm
            · simp only [hLe, ↓reduceIte, byteArray_extract_toList, List.drop_zero, Nat.sub_zero]
          have hChunkSz : chunk.size = min bs.size reqCap := by
            have h1 : chunk.data.toList.length = chunk.size := by simp
            rw [← h1, hChunkToList, List.length_take]
            have h2 : bs.data.toList.length = bs.size := by simp
            rw [h2, Nat.min_comm]
          have hChunkTake : chunk.data.toList.take (rb.cap - rb.toList.length) = chunk.data.toList := by
            apply List.take_of_length_le
            have h1 : chunk.data.toList.length = chunk.size := by simp
            omega
          let tr1 := { tr with recvBytes := tr.recvBytes ++
            (let k := Nat.min bs.size want.toNat; if k == bs.size then bs.data else (bs.extract 0 k).data) }
          have hPushCapEq : (rb.push chunk).cap = rb.cap := ringBuf_push_cap rb chunk
          have hPushCap : (rb.push chunk).len ≤ (rb.push chunk).cap := by
            rw [hPushCapEq]; exact ringBuf_push_len_le_cap rb chunk
          have hPushGt : (rb.push chunk).len > rb.len := by
            have hL1 := ringBuf_toList_length_of_le_cap (rb.push chunk) hPushCap
            have hL2 := congrArg List.length (ringBuf_push_toList rb chunk)
            rw [hL1, List.length_append, hChunkTake, hTlLen] at hL2
            have hLenChunk : chunk.data.toList.length = chunk.size := by simp
            omega
          have hSub := healthy_recvIntoRing_laws sys hRef fd fuel (rb.push chunk) w1 tr1 hWf1 hPushCap
          dsimp only [NetRelay.recvIntoRing, RingBuf.push, StateT.run] at hSub ⊢
          rcases hRes : NetRelay.Internal.recvIntoRing (instrumentSysOps sys).net fd fuel (NetRelay.Internal.ringBufPush rb chunk) (w1, tr1) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRes] at hSub
          dsimp only [tr1] at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, ?_⟩
          cases res2 with
          | none => exact hSub.2.2.2
          | some pair =>
            rcases pair with ⟨rb2, eof2⟩
            rcases hSub.2.2.2 with ⟨hCap2, hCapEq2, ⟨delta2, hTr2, hRb2⟩, hProg2⟩
            have hChunkEq :
                (let k := Nat.min bs.size want.toNat; if k == bs.size then bs.data else (bs.extract 0 k).data).toList =
                  chunk.data.toList := by
              have hAcc := accepted_slice_toList bs want.toNat
              dsimp only at hAcc ⊢
              have hMinComm : Nat.min bs.size want.toNat = Nat.min want.toNat bs.size := by
                simp only [nat_min_eq_min]; exact Nat.min_comm ..
              rw [hMinComm, hAcc, hWantToNat, hChunkToList]
            refine ⟨hPushCapEq ▸ hCap2, hCapEq2.trans hPushCapEq,
              ⟨chunk.data.toList ++ delta2, ?_, ?_⟩, fun hFuel => ?_⟩
            · rw [hTr2, Array.toList_append, hChunkEq, List.append_assoc]
            · change rb2.toList = rb.toList ++ (chunk.data.toList ++ delta2)
              have hP := ringBuf_push_toList rb chunk
              rw [hChunkTake] at hP
              calc rb2.toList
                _ = (rb.push chunk).toList ++ delta2 := hRb2
                _ = (rb.toList ++ chunk.data.toList) ++ delta2 := by rw [hP]
                _ = rb.toList ++ (chunk.data.toList ++ delta2) := List.append_assoc ..
            · exact hProg2 (by
                change w1.netEnv.eintrBudget + ((rb.push chunk).cap - (rb.push chunk).len) ≤ fuel
                rw [hPushCapEq]; omega)
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          have hEqEi : Net.outcomeOfBytes (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := healthy_recvIntoRing_laws sys hRef fd fuel rb w1 tr hWf1 hCap
          dsimp only [NetRelay.recvIntoRing, StateT.run] at hSub ⊢
          rcases hRes : NetRelay.Internal.recvIntoRing (instrumentSysOps sys).net fd fuel rb (w1, tr) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRes] at hSub
          dsimp only at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, ?_⟩
          cases res2 with
          | none => exact hSub.2.2.2
          | some pair =>
            rcases pair with ⟨rb2, eof2⟩
            exact ⟨hSub.2.2.2.1, hSub.2.2.2.2.1, hSub.2.2.2.2.2.1,
              fun hFuel => hSub.2.2.2.2.2.2 (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
          have hMono : ∀ x ∈ tr.netErrs.toList, x ∈ (tr.netErrs.push e).toList := by
            intro x hx; simp [Array.toList_push, hx]
          have hSzLt : tr.netErrs.size < (tr.netErrs.push e).size := by simp
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte]
            dsimp only [StateT.run, pure, StateT.pure]
            exact ⟨hWf1, hMono, Nat.le_of_lt hSzLt, hCap, rfl, ⟨[], by simp, by simp⟩,
              fun _ => Or.inr (Or.inr hSzLt)⟩
          · have hAgF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAg
            simp only [hAgF, Bool.false_eq_true, ↓reduceIte]
            by_cases hBadFd : (e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK) = true
            · simp only [hBadFd, ↓reduceIte]
              dsimp only [StateT.run, pure, StateT.pure]
              refine ⟨hWf1, hMono, Nat.le_of_lt hSzLt, e, by simp [Array.toList_push], Or.inr ?_⟩
              simp only [Bool.or_eq_true, beq_iff_eq] at hBadFd
              rcases hBadFd with (h1 | h2) | h3
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr h3)
            · have hBadFdF : (e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK) = false :=
                Bool.eq_false_iff.mpr hBadFd
              simp only [hBadFdF, Bool.false_eq_true, ↓reduceIte]
              dsimp only [StateT.run, pure, StateT.pure]
              exact ⟨hWf1, hMono, Nat.le_of_lt hSzLt, hCap, rfl, ⟨[], by simp, by simp⟩,
                fun _ => Or.inr (Or.inl rfl)⟩

/-- Relational TX FIFO conservation and `EINTR` progress: over ANY `sys` refining `RefinesHealthyCProxySys`, `NetRelay.flushRingNonblock` preserves `w'.wf`, returns `none` only on non-`EAGAIN` `netErrs`, preserves `rb.cap`, maintains `rb'.len ≤ rb.cap` and `txDelta ++ rb'.toList = rb.toList`, and progresses until empty, `EAGAIN`, or zero-send whenever `eintrBudget + rb.len ≤ fuel`. -/
theorem healthy_flushRingNonblock_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      rb.len ≤ rb.cap →
      let (res, (w', tr')) := (NetRelay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb).run (w, tr)
      w'.wf = true ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      (tr.sawZeroSend = true → tr'.sawZeroSend = true) ∧
      match res with
      | none =>
        ∃ e ∈ tr'.netErrs.toList, e ∈ tr.netErrs.toList ∨ e ≠ Errno.EAGAIN
      | some rb' =>
        rb'.len ≤ rb.cap ∧
        rb'.cap = rb.cap ∧
        (∃ txDelta : List UInt8,
          tr'.sentBytes.toList = tr.sentBytes.toList ++ txDelta ∧
          txDelta ++ rb'.toList = rb.toList) ∧
        (w.netEnv.eintrBudget + rb.len ≤ fuel →
          rb'.isEmpty = true ∨ Errno.EAGAIN ∈ tr'.netErrs.toList ∨ tr'.sawZeroSend = true)
  | 0, rb, w, tr, hWf, hCap => by
    dsimp only [NetRelay.flushRingNonblock, NetRelay.Internal.flushRingNonblock, StateT.run, pure, StateT.pure]
    refine ⟨hWf, fun _ h => h, id, hCap, rfl, ⟨[], by simp, by simp⟩, fun hFuel => ?_⟩
    have hLen0 : rb.len = 0 := by omega
    exact Or.inl (by unfold RingBuf.isEmpty NetRelay.Internal.ringBufIsEmpty; exact beq_iff_eq.mpr hLen0)
  | fuel + 1, rb, w, tr, hWf, hCap => by
    unfold NetRelay.flushRingNonblock NetRelay.Internal.flushRingNonblock
    by_cases hEmp : NetRelay.Internal.ringBufIsEmpty rb = true
    · simp only [hEmp, ↓reduceIte]
      dsimp only [StateT.run, pure, StateT.pure]
      exact ⟨hWf, fun _ h => h, id, hCap, rfl, ⟨[], by simp, by simp⟩, fun _ => Or.inl hEmp⟩
    · have hEmpF : NetRelay.Internal.ringBufIsEmpty rb = false := Bool.eq_false_iff.mpr hEmp
      simp only [hEmpF, Bool.false_eq_true, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      have hLenPos : rb.len > 0 := by
        unfold NetRelay.Internal.ringBufIsEmpty at hEmp
        have hNe : rb.len ≠ 0 := fun hc => hEmp (beq_iff_eq.mpr hc)
        omega
      let slice := NetRelay.Internal.ringBufFrontSlice rb
      have hSlicePos : slice.size > 0 := by
        have hEq1 : slice.data.toList.length = rb.toList.length :=
          congrArg List.length (ringBuf_frontSlice_toList rb)
        have hEq2 := ringBuf_toList_length_of_le_cap rb hCap
        have hSz : slice.data.toList.length = slice.size := by simp
        rw [← hSz, hEq1, hEq2]; exact hLenPos
      have hNet := hRef.2.1 w (.sendto fd slice { nosignal := true, dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      rw [inst_net_sendto]
      rcases hRun : sys.net.sendto fd slice { nosignal := true, dontwait := true } w with ⟨r, w1⟩
      rw [hRun] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.sendto fd slice { nosignal := true, dontwait := true }) (Net.outcomeOfU32 r) hNet.1
      cases r with
      | ok n =>
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget :=
          hBud.2 (fun hc => nomatch hc)
        let k := Nat.min n.toNat slice.size
        let accepted := if k == slice.size then slice.data else (slice.extract 0 k).data
        have hAccList : accepted.toList = rb.toList.take n.toNat := by
          have hAcc := accepted_slice_toList slice n.toNat
          have hFront : slice.data.toList = rb.toList := ringBuf_frontSlice_toList rb
          dsimp only [accepted, k]
          rw [hAcc, hFront]
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte, Bool.true_and]
          dsimp only [StateT.run, pure, StateT.pure]
          have hnZ : n.toNat = 0 := by have := beq_iff_eq.mp hn0; subst this; rfl
          have hZeroTrue : (tr.sawZeroSend || decide (slice.size > 0)) = true := by
            have hd : decide (slice.size > 0) = true := decide_eq_true hSlicePos
            rw [hd, Bool.or_true]
          refine ⟨hWf1, fun _ h => h, fun _ => hZeroTrue, hCap, rfl, ⟨[], ?_, by simp⟩,
            fun _ => Or.inr (Or.inr hZeroTrue)⟩
          rw [Array.toList_append, hAccList, hnZ]
          simp
        · have hnF : (n == 0) = false := Bool.eq_false_iff.mpr hn0
          simp only [hnF, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.or_false]
          have hnPos : n.toNat > 0 := by
            have hNe : n ≠ 0 := fun hc => hn0 (beq_iff_eq.mpr hc)
            exact Nat.pos_of_ne_zero (fun hz => hNe (by rw [← @UInt32.ofNat_toNat n, hz]; rfl))
          let tr1 := { tr with sentBytes := tr.sentBytes ++ accepted }
          have hConsCapEq : (rb.consume n.toNat).cap = rb.cap := ringBuf_consume_cap rb n.toNat
          have hConsCap : (rb.consume n.toNat).len ≤ (rb.consume n.toNat).cap := by
            rw [hConsCapEq]; exact ringBuf_consume_len_le_cap rb n.toNat hCap
          have hConsLt : (rb.consume n.toNat).len < rb.len := by
            have hL1 := ringBuf_toList_length_of_le_cap (rb.consume n.toNat) hConsCap
            have hL2 := congrArg List.length (ringBuf_consume_toList rb n.toNat hCap)
            have hL0 := ringBuf_toList_length_of_le_cap rb hCap
            rw [hL1, List.length_drop, hL0] at hL2
            omega
          have hSub := healthy_flushRingNonblock_laws sys hRef fd fuel (rb.consume n.toNat) w1 tr1 hWf1 hConsCap
          dsimp only [NetRelay.flushRingNonblock, RingBuf.consume, StateT.run, tr1] at hSub ⊢
          rcases hRes : NetRelay.Internal.flushRingNonblock (instrumentSysOps sys).net fd fuel (NetRelay.Internal.ringBufConsume rb n.toNat) (w1, tr1) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          dsimp only [tr1] at hRes
          rw [hRes] at hSub
          dsimp only at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, ?_⟩
          cases res2 with
          | none => exact hSub.2.2.2
          | some rb2 =>
            rcases hSub.2.2.2 with ⟨hCap2, hCapEq2, ⟨delta2, hTr2, hRb2⟩, hProg2⟩
            refine ⟨hConsCapEq ▸ hCap2, hCapEq2.trans hConsCapEq,
              ⟨rb.toList.take n.toNat ++ delta2, ?_, ?_⟩, fun hFuel => ?_⟩
            · rw [hTr2, Array.toList_append, hAccList, List.append_assoc]
            · have hC : (rb.consume n.toNat).toList = rb.toList.drop n.toNat :=
                ringBuf_consume_toList rb n.toNat hCap
              have hEq : delta2 ++ rb2.toList = (rb.consume n.toNat).toList := hRb2
              rw [List.append_assoc, hEq, hC]
              exact List.take_append_drop n.toNat rb.toList
            · exact hProg2 (by
                change w1.netEnv.eintrBudget + (rb.consume n.toNat).len ≤ fuel
                omega)
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          have hEqEi : Net.outcomeOfU32 (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := healthy_flushRingNonblock_laws sys hRef fd fuel rb w1 tr hWf1 hCap
          dsimp only [NetRelay.flushRingNonblock, StateT.run] at hSub ⊢
          rcases hRes : NetRelay.Internal.flushRingNonblock (instrumentSysOps sys).net fd fuel rb (w1, tr) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRes] at hSub
          dsimp only at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, ?_⟩
          cases res2 with
          | none => exact hSub.2.2.2
          | some rb2 =>
            exact ⟨hSub.2.2.2.1, hSub.2.2.2.2.1, hSub.2.2.2.2.2.1,
              fun hFuel => hSub.2.2.2.2.2.2 (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
          have hMono : ∀ x ∈ tr.netErrs.toList, x ∈ (tr.netErrs.push e).toList := by
            intro x hx; simp [Array.toList_push, hx]
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte]
            dsimp only [StateT.run, pure, StateT.pure]
            have hInAg : Errno.EAGAIN ∈ (tr.netErrs.push e).toList := by
              rw [beq_iff_eq.mp hAg]; simp [Array.toList_push]
            exact ⟨hWf1, hMono, id, hCap, rfl, ⟨[], by simp, by simp⟩,
              fun _ => Or.inr (Or.inl hInAg)⟩
          · have hAgF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAg
            simp only [hAgF, Bool.false_eq_true, ↓reduceIte]
            dsimp only [StateT.run, pure, StateT.pure]
            have hNeAg : e ≠ Errno.EAGAIN := fun hc => hAg (beq_iff_eq.mpr hc)
            exact ⟨hWf1, hMono, id, e, by simp [Array.toList_push], Or.inr hNeAg⟩

/-- `SysBridge.dnsAddrToIpAddr?` rejects every scoped IPv6 address (`scopeId != 0`), preventing link-local `%iface` confusion. -/
theorem dnsAddrToIpAddr_rejects_scoped (a : Dns.DnsAddr) (ip : IpAddr)
    (h : dnsAddrToIpAddr? a = some ip) :
    a.scopeId = 0 := by
  cases a with
  | ipv4 _ _ _ _ => rfl
  | ipv6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc =>
    by_cases hSc : sc = 0
    · exact hSc
    · have hBne : (sc != 0) = true := bne_iff_ne.mpr hSc
      simp [dnsAddrToIpAddr?, hBne] at h

/-- Every `IpAddr` retained by `SysBridge.filterUnscopedDnsAddrs` came from an unscoped (`scopeId = 0`) `DnsAddr` in `addrs`. -/
theorem filterUnscopedDnsAddrs_all_unscoped (addrs : List Dns.DnsAddr) (ip : IpAddr)
    (hMem : ip ∈ (filterUnscopedDnsAddrs addrs).toList) :
    ∃ a ∈ addrs, a.scopeId = 0 ∧ dnsAddrToIpAddr? a = some ip := by
  unfold filterUnscopedDnsAddrs at hMem
  rw [List.toList_toArray, List.mem_filterMap] at hMem
  rcases hMem with ⟨a, haMem, haEq⟩
  exact ⟨a, haMem, dnsAddrToIpAddr_rejects_scoped a ip haEq, haEq⟩

/-- `SysBridge.effectiveDialIp` preserves `Model.isGlobalIp` identically across IPv4, native IPv6, and unwrapped `::ffff:0:0/96` addresses. -/
theorem effectiveDialIp_isGlobalIp_eq (ip : IpAddr) :
    Model.isGlobalIp (effectiveDialIp ip) = Model.isGlobalIp ip := by
  cases ip with
  | v4 addr => rfl
  | v6 hi lo =>
    unfold effectiveDialIp isIpv4MappedV6
    by_cases hMap : (hi == 0 && (lo >>> 32) == 0x0000ffff) = true
    · simp [hMap, Model.isGlobalIp]
    · have hMapF : (hi == 0 && (lo >>> 32) == 0x0000ffff) = false := Bool.eq_false_iff.mpr hMap
      simp [hMapF]

/-- Unwrapping `::ffff:a.b.c.d` via `ipAddrToDialSockAddr` (`effectiveDialIp`) never bypasses `policy.extraBans`: any `ip` permitted by `Model.allowsIp policy` dials an unbanned target. -/
theorem dialSockAddr_never_banned (policy : IpPolicy) (ip : IpAddr)
    (hAllow : Model.allowsIp policy ip = true) :
    Model.isBannedByPrefixes policy.extraBans (effectiveDialIp ip) = false ∧
    (policy.extraAllows = #[] → Model.allowsIp policy (effectiveDialIp ip) = true) := by
  have hNotBanIp : Model.isBannedByPrefixes policy.extraBans ip = false := by
    unfold Model.allowsIp at hAllow
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hAllow
    exact hAllow.2
  have hNotBanEff : Model.isBannedByPrefixes policy.extraBans (effectiveDialIp ip) = false := by
    cases ip with
    | v4 addr => exact hNotBanIp
    | v6 hi lo =>
      unfold effectiveDialIp isIpv4MappedV6
      by_cases hMap : (hi == 0 && (lo >>> 32) == 0x0000ffff) = true
      · simp only [hMap, ↓reduceIte]
        apply Bool.eq_false_iff.mpr
        intro hBanV4
        unfold Model.isBannedByPrefixes at hBanV4
        rw [List.any_eq_true] at hBanV4
        rcases hBanV4 with ⟨ban, hBanMem, hMatchOr⟩
        simp only [embeddedIpv4Addrs, List.any_nil, Bool.or_false] at hMatchOr
        have hEmb : IpAddr.v4 lo.toUInt32 ∈ embeddedIpv4Addrs (.v6 hi lo) := by
          unfold embeddedIpv4Addrs
          simp [hMap]
        have hFalse := (specIpv4InIpv6NeverBypassesBan.1 policy (.v6 hi lo) (.v4 lo.toUInt32) ban
          hEmb hBanMem hMatchOr)
        rw [hAllow] at hFalse
        cases hFalse
      · have hMapF : (hi == 0 && (lo >>> 32) == 0x0000ffff) = false := Bool.eq_false_iff.mpr hMap
        simp [hMapF, hNotBanIp]
  refine ⟨hNotBanEff, ?_⟩
  intro hEmptyExtra
  unfold Model.allowsIp at hAllow ⊢
  rw [hEmptyExtra] at hAllow ⊢
  simp only [List.any_nil, Bool.or_false] at hAllow ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hAllow ⊢
  refine ⟨?_, hNotBanEff⟩
  cases hBase : policy.base with
  | publicOnly =>
    rw [hBase] at hAllow
    simpa [effectiveDialIp_isGlobalIp_eq] using hAllow.1
  | empty =>
    rw [hBase] at hAllow
    cases hAllow.1

/-- Internal SysBridge helper lemma `monoNowMs_instrumented_laws`. -/
theorem monoNowMs_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := (monoNowMs (instrumentSysOps sys)).run (w, tr)
    w'.wf = true ∧ tr' = tr := by
  unfold monoNowMs
  have hStep := retryEintr_preserves
    (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.wf = true ∧ wt.2 = tr)
    (fun _ _ => True)
    ((instrumentSysOps sys).timeRand.clock_gettime .monotonic)
    (fun (wx, trx) ⟨hwx, htrx⟩ => by
      have ht := hRef.2.2.2.2.1 wx (.clock_gettime .monotonic) ((wf_iff_parts wx).mp hwx)
      dsimp only [TimeRand.execTimeRandReq, Functor.map, StateT.map, StateT.run,
        bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run] at ht
      dsimp only [StateT.run]
      rw [inst_time_gettime]
      rcases hT : sys.timeRand.clock_gettime .monotonic wx with ⟨trRes, wx'⟩
      rw [hT] at ht
      dsimp only at ht ⊢
      exact ⟨⟨(wf_iff_parts _).mpr ht.2.1, htrx⟩, Or.inr trivial⟩)
    MAX_EINTR_RETRIES (w, tr) ⟨hWf, rfl⟩
  dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run] at hStep ⊢
  rcases hRun : retryEintr ((instrumentSysOps sys).timeRand.clock_gettime .monotonic) MAX_EINTR_RETRIES (w, tr) with ⟨r, wt1⟩
  rw [hRun] at hStep
  dsimp only at hStep ⊢
  cases r <;> exact hStep.1

/-- Relational TX slice conservation and `EINTR` progress for `NetRelay.flushBytesNonblock`. -/
theorem flushBytesNonblock_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) (bytes : ByteArray) :
    ∀ (fuel off : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (res, (w', tr')) := (NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off).run (w, tr)
      w'.wf = true ∧
      tr'.dnsQueries = tr.dnsQueries ∧
      tr'.dialedAddrs = tr.dialedAddrs ∧
      tr'.closedFds = tr.closedFds ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      (tr.sawZeroSend = true → tr'.sawZeroSend = true) ∧
      match res with
      | none => True
      | some nextOff =>
        (∃ txDelta : List UInt8,
          tr'.sentBytes.toList = tr.sentBytes.toList ++ txDelta ∧
          txDelta ++ bytes.data.toList.drop nextOff = bytes.data.toList.drop off) ∧
        (w.netEnv.eintrBudget + (bytes.size - off) ≤ fuel →
          nextOff ≥ bytes.size ∨ Errno.EAGAIN ∈ tr'.netErrs.toList ∨ tr'.sawZeroSend = true)
  | 0, off, w, tr, hWf => by
    dsimp only [NetRelay.flushBytesNonblock, NetRelay.Internal.flushBytesNonblock, StateT.run, pure, StateT.pure]
    exact ⟨hWf, rfl, rfl, rfl, id, fun _ h => h, id, ⟨[], by simp, by simp⟩, fun hFuel => Or.inl (by omega)⟩
  | fuel + 1, off, w, tr, hWf => by
    unfold NetRelay.flushBytesNonblock NetRelay.Internal.flushBytesNonblock
    by_cases hGe : off ≥ bytes.size
    · simp only [hGe, ↓reduceIte]
      dsimp only [StateT.run, pure, StateT.pure]
      exact ⟨hWf, rfl, rfl, rfl, id, fun _ h => h, id, ⟨[], by simp, by simp⟩, fun _ => Or.inl hGe⟩
    · simp only [hGe, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      let slice := if off == 0 then bytes else bytes.extract off bytes.size
      have hSliceList : slice.data.toList = bytes.data.toList.drop off := by
        dsimp only [slice]
        by_cases h0 : (off == 0) = true
        · simp [beq_iff_eq.mp h0]
        · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
          exact byteArray_extract_end_toList bytes off
      have hSliceSz : slice.size = bytes.size - off := by
        have h1 : slice.data.toList.length = slice.size := by simp
        have h2 : (bytes.data.toList.drop off).length = bytes.size - off := by simp
        rw [← h1, hSliceList, h2]
      have hSlicePos : slice.size > 0 := by omega
      have hNet := hRef.2.1 w (.sendto fd slice { nosignal := true, dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      rw [inst_net_sendto]
      rcases hRun : sys.net.sendto fd slice { nosignal := true, dontwait := true } w with ⟨r, w1⟩
      rw [hRun] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hNd1 : (w.filesEnv.state.fds.map Prod.fst).Nodup → (w1.filesEnv.state.fds.map Prod.fst).Nodup := hNet.2.2.2
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.sendto fd slice { nosignal := true, dontwait := true }) (Net.outcomeOfU32 r) hNet.1
      cases r with
      | ok n =>
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget := hBud.2 (fun hc => nomatch hc)
        let k := Nat.min n.toNat slice.size
        let accepted := if k == slice.size then slice.data else (slice.extract 0 k).data
        have hAccList : accepted.toList = (bytes.data.toList.drop off).take n.toNat := by
          have hAcc := accepted_slice_toList slice n.toNat
          dsimp only [accepted, k, slice] at hAcc ⊢
          rw [hAcc, hSliceList]
        by_cases hn0 : (n == 0) = true
        · simp only [hn0, ↓reduceIte, Bool.true_and]
          dsimp only [StateT.run, pure, StateT.pure]
          have hnZ : n.toNat = 0 := by have := beq_iff_eq.mp hn0; subst this; rfl
          have hZeroTrue : (tr.sawZeroSend || decide ((if off == 0 then bytes else bytes.extract off bytes.size).size > 0)) = true := by
            have hd : decide ((if off == 0 then bytes else bytes.extract off bytes.size).size > 0) = true := decide_eq_true hSlicePos
            rw [hd, Bool.or_true]
          refine ⟨hWf1, rfl, rfl, rfl, hNd1, fun _ h => h, fun _ => hZeroTrue,
            ⟨[], ?_, by simp⟩, fun _ => Or.inr (Or.inr hZeroTrue)⟩
          rw [Array.toList_append, hAccList, hnZ]; simp
        · have hnF : (n == 0) = false := Bool.eq_false_iff.mpr hn0
          simp only [hnF, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.or_false]
          have hnPos : n.toNat > 0 := by
            have hNe : n ≠ 0 := fun hc => hn0 (beq_iff_eq.mpr hc)
            exact Nat.pos_of_ne_zero (fun hz => hNe (by rw [← @UInt32.ofNat_toNat n, hz]; rfl))
          let step := Nat.min n.toNat slice.size
          have hStepPos : step > 0 := by
            dsimp only [step]; simp only [nat_min_eq_min]; omega
          have hDropEq : bytes.data.toList.drop (off + step) = (bytes.data.toList.drop off).drop n.toNat := by
            dsimp only [step]; simp only [nat_min_eq_min]
            by_cases hLe : n.toNat ≤ slice.size
            · rw [Nat.min_eq_left hLe, ← List.drop_drop]
            · rw [Nat.min_eq_right (by omega)]
              have hEqSz : off + slice.size = bytes.size := by omega
              rw [hEqSz]
              have hNil1 : bytes.data.toList.drop bytes.size = [] := by simp
              have hNil2 : (bytes.data.toList.drop off).drop n.toNat = [] :=
                List.drop_eq_nil_of_le (by simp; omega)
              rw [hNil1, hNil2]
          let tr1 := { tr with sentBytes := tr.sentBytes ++ accepted }
          have hSub := flushBytesNonblock_instrumented_laws sys hRef fd bytes fuel (off + step) w1 tr1 hWf1
          dsimp only [step, slice] at hStepPos
          dsimp only [NetRelay.flushBytesNonblock, StateT.run, tr1, step, accepted, k, slice] at hSub ⊢
          rcases hRes : NetRelay.Internal.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel (off + step) (w1, tr1) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          dsimp only [tr1, step, accepted, k, slice] at hRes
          rw [hRes] at hSub
          dsimp only at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, hSub.2.2.2.1, fun h0 => hSub.2.2.2.2.1 (hNd1 h0),
            hSub.2.2.2.2.2.1, hSub.2.2.2.2.2.2.1, ?_⟩
          cases res2 with
          | none => trivial
          | some nextOff =>
            rcases hSub.2.2.2.2.2.2.2 with ⟨⟨delta2, hTr2, hCons2⟩, hProg2⟩
            refine ⟨⟨(bytes.data.toList.drop off).take n.toNat ++ delta2, ?_, ?_⟩, fun hFuel => ?_⟩
            · rw [hTr2, Array.toList_append, hAccList, List.append_assoc]
            · rw [List.append_assoc, hCons2, hDropEq]
              exact List.take_append_drop n.toNat (bytes.data.toList.drop off)
            · exact hProg2 (by omega)
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          have hEqEi : Net.outcomeOfU32 (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := flushBytesNonblock_instrumented_laws sys hRef fd bytes fuel off w1 tr hWf1
          dsimp only [NetRelay.flushBytesNonblock, StateT.run] at hSub ⊢
          rcases hRes : NetRelay.Internal.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off (w1, tr) with ⟨res2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRes] at hSub
          dsimp only at hSub ⊢
          refine ⟨hSub.1, hSub.2.1, hSub.2.2.1, hSub.2.2.2.1, fun h0 => hSub.2.2.2.2.1 (hNd1 h0),
            hSub.2.2.2.2.2.1, hSub.2.2.2.2.2.2.1, ?_⟩
          cases res2 with
          | none => trivial
          | some nextOff =>
            exact ⟨hSub.2.2.2.2.2.2.2.1, fun hFuel => hSub.2.2.2.2.2.2.2.2 (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
          have hMono : ∀ x ∈ tr.netErrs.toList, x ∈ (tr.netErrs.push e).toList := by
            intro x hx; simp [Array.toList_push, hx]
          by_cases hC : (e == Errno.EAGAIN) = true
          · simp only [hC, ↓reduceIte]
            dsimp only [StateT.run, pure, StateT.pure]
            have hInAg : Errno.EAGAIN ∈ (tr.netErrs.push e).toList := by
              rw [beq_iff_eq.mp hC]; simp [Array.toList_push]
            exact ⟨hWf1, rfl, rfl, rfl, hNd1, hMono, id, ⟨[], by simp, by simp⟩,
              fun _ => Or.inr (Or.inl hInAg)⟩
          · simp only [Bool.eq_false_iff.mpr hC, Bool.false_eq_true, ↓reduceIte]
            dsimp only [StateT.run, pure, StateT.pure]
            exact ⟨hWf1, rfl, rfl, rfl, hNd1, hMono, id, trivial⟩

/-- Internal SysBridge helper lemma `shutdownWrClean_instrumented_laws`. -/
theorem shutdownWrClean_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) :
    ∀ (fuel : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (_, (w', tr')) := (NetRelay.shutdownWrClean (instrumentSysOps sys).net fd fuel).run (w, tr)
      w'.wf = true ∧ tr' = tr ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup)
  | 0, w, tr, hWf => ⟨hWf, rfl, id⟩
  | fuel + 1, w, tr, hWf => by
    unfold NetRelay.shutdownWrClean NetRelay.Internal.shutdownWrClean
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    have hNet := hRef.2.1 w (.shutdown fd .wr) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    rw [inst_net_shutdown]
    rcases hRun : sys.net.shutdown fd .wr w with ⟨r, w1⟩
    rw [hRun] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    have hNd1 := hNet.2.2.2
    cases r with
    | ok _ => exact ⟨hWf1, rfl, hNd1⟩
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        have hSub := shutdownWrClean_instrumented_laws sys hRef fd fuel w1 tr hWf1
        dsimp only [NetRelay.shutdownWrClean, StateT.run] at hSub ⊢
        rcases hRes : NetRelay.Internal.shutdownWrClean (instrumentSysOps sys).net fd fuel (w1, tr) with ⟨b2, wt2⟩
        rcases wt2 with ⟨w2, tr2⟩
        rw [hRes] at hSub
        exact ⟨hSub.1, hSub.2.1, fun h0 => hSub.2.2 (hNd1 h0)⟩
      · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
        simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
        by_cases hC : (e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE) = true
        · simp only [hC, ↓reduceIte]; exact ⟨hWf1, rfl, hNd1⟩
        · simp only [Bool.eq_false_iff.mpr hC, Bool.false_eq_true, ↓reduceIte]; exact ⟨hWf1, rfl, hNd1⟩

/-- Internal SysBridge helper lemma `stateT_bind_eq`. -/
theorem stateT_bind_eq {σ₁ σ₂ α β : Type}
    {x : StateM (σ₁ × σ₂) α} {k : α → StateM (σ₁ × σ₂) β}
    {w w' : σ₁} {tr tr' : σ₂} {res : β}
    (h : StateT.run (x >>= k) (w, tr) = (res, (w', tr'))) :
    ∃ a w1 tr1, StateT.run x (w, tr) = (a, (w1, tr1)) ∧
      StateT.run (k a) (w1, tr1) = (res, (w', tr')) := by
  rw [stateT_bind_run] at h
  rcases hx : StateT.run x (w, tr) with ⟨a, w1, tr1⟩
  rw [hx] at h
  exact ⟨a, w1, tr1, rfl, h⟩

/-- Internal SysBridge helper lemma `flushBytesNonblock_of_eq`. -/
theorem flushBytesNonblock_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd : Nat) (bytes : ByteArray) (fuel off : Nat)
    (w w1 : HealthySysWorld) (tr tr1 : SysAuditTrace Nat) (res : Option Nat)
    (hWf : w.wf = true)
    (hRun : StateT.run (NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off) (w, tr) = (res, (w1, tr1))) :
    w1.wf = true ∧ tr1.dnsQueries = tr.dnsQueries ∧ tr1.dialedAddrs = tr.dialedAddrs ∧
    tr1.closedFds = tr.closedFds ∧ (∀ e ∈ tr.netErrs.toList, e ∈ tr1.netErrs.toList) := by
  have h := flushBytesNonblock_instrumented_laws sys hRef fd bytes fuel off w tr hWf
  have hRun' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net fd bytes fuel off).run (w, tr) = (res, (w1, tr1)) := hRun
  rw [hRun'] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Internal SysBridge helper lemma `monoNowMs_of_eq`. -/
theorem monoNowMs_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w w1 : HealthySysWorld) (tr tr1 : SysAuditTrace Nat) (now : Nat)
    (hWf : w.wf = true)
    (hRun : StateT.run (monoNowMs (instrumentSysOps sys)) (w, tr) = (now, (w1, tr1))) :
    w1.wf = true ∧ tr1 = tr := by
  have h := monoNowMs_instrumented_laws sys hRef w tr hWf
  have hRun' : (monoNowMs (instrumentSysOps sys)).run (w, tr) = (now, (w1, tr1)) := hRun
  rw [hRun'] at h
  exact h

/-- Internal SysBridge helper lemma `shutdownWrClean_of_eq`. -/
theorem shutdownWrClean_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (fd fuel : Nat) (w w1 : HealthySysWorld) (tr tr1 : SysAuditTrace Nat) (okS : Bool)
    (hWf : w.wf = true)
    (hRun : StateT.run (NetRelay.shutdownWrClean (instrumentSysOps sys).net fd fuel) (w, tr) = (okS, (w1, tr1))) :
    w1.wf = true ∧ tr1 = tr := by
  have h := shutdownWrClean_instrumented_laws sys hRef fd fuel w tr hWf
  have hRun' : (NetRelay.shutdownWrClean (instrumentSysOps sys).net fd fuel).run (w, tr) = (okS, (w1, tr1)) := hRun
  rw [hRun'] at h
  exact ⟨h.1, h.2.1⟩

/-- Internal SysBridge helper lemma `closeFd_of_eq`. -/
theorem closeFd_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w w1 : HealthySysWorld) (tr tr1 : SysAuditTrace Nat) (fd : Nat) (u : Unit)
    (hWf : w.wf = true)
    (hRun : StateT.run ((instrumentSysOps sys).closeFd fd) (w, tr) = (u, (w1, tr1))) :
    w1.wf = true ∧ tr1.dnsQueries = tr.dnsQueries ∧ tr1.dialedAddrs = tr.dialedAddrs ∧
    tr1.netErrs = tr.netErrs ∧ (∀ x ∈ tr.closedFds.toList, x ∈ tr1.closedFds.toList) ∧
    fd ∈ tr1.closedFds.toList := by
  have h := healthy_closeFd_instrumented_laws sys hRef w tr fd hWf
  have hRun' : ((instrumentSysOps sys).closeFd fd).run (w, tr) = (u, (w1, tr1)) := hRun
  rw [hRun'] at h
  dsimp only at h
  refine ⟨h.1, by rw [h.2.2.1], by rw [h.2.2.1], by rw [h.2.2.1], ?_, ?_⟩
  · intro x hx; rw [h.2.2.1]; simp [Array.toList_push, hx]
  · rw [h.2.2.1]; simp [Array.toList_push]

/-- Internal SysBridge helper lemma `enterClosingReply_laws_of_eq`. -/
theorem enterClosingReply_laws_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (slot : ClientSlot Nat dnsJob) (cfd code : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true)
    (slot' : ClientSlot Nat dnsJob) (w' : HealthySysWorld) (tr' : SysAuditTrace Nat)
    (hRun : StateT.run (enterClosingReply (instrumentSysOps sys) limits slot cfd code) (w, tr) = (slot', (w', tr'))) :
    w'.wf = true ∧
    tr'.dnsQueries = tr.dnsQueries ∧
    tr'.dialedAddrs = tr.dialedAddrs ∧
    (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
    (∀ c b dl, slot'.phase ≠ .handshake c b dl) ∧
    (∀ st, slot'.phase ≠ .relay st) ∧
    (∀ c u h p cs ci le dl, slot'.phase ≠ .connecting c u h p cs ci le dl) := by
  unfold enterClosingReply at hRun
  dsimp only at hRun
  obtain ⟨now, w1, tr1, hM, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf1, hTr1⟩ := monoNowMs_of_eq sys hRef w w1 tr tr1 now hWf hM; clear hM
  obtain ⟨flRes, w2, tr2, hF, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf2, hDq2, hDa2, hCf2, hNe2⟩ := flushBytesNonblock_of_eq sys hRef cfd _ MAX_CLOSING_STEPS 0 w1 w2 tr1 tr2 flRes hWf1 hF; clear hF
  have hNe2' : ∀ e ∈ tr.netErrs.toList, e ∈ tr2.netErrs.toList := fun e he => hNe2 e (hTr1 ▸ he)
  have hCf2' : ∀ x ∈ tr.closedFds.toList, x ∈ tr2.closedFds.toList := fun x hx => hCf2 ▸ hTr1 ▸ hx
  cases flRes with
  | none =>
    dsimp only at hRun
    obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
    obtain ⟨hWf3, hDq3, hDa3, hNe3, hCf3, _⟩ := closeFd_of_eq sys hRef w2 w3 tr2 tr3 cfd u hWf2 hC; clear hC
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hS hWT; injection hWT with hW hT; subst hS; subst hW; subst hT
    refine ⟨hWf3, hDq3.trans (hDq2.trans (congrArg _ hTr1)), hDa3.trans (hDa2.trans (congrArg _ hTr1)),
      fun e he => hNe3 ▸ hNe2' e he, fun x hx => hCf3 x (hCf2' x hx), ?_, ?_, ?_⟩
    · intro _ _ _ h; cases h
    · intro _ h; cases h
    · intro _ _ _ _ _ _ _ _ h; cases h
  | some sentOff =>
    dsimp only at hRun
    by_cases hSent : sentOff ≥ (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes).size
    · simp only [hSent, ↓reduceIte] at hRun
      obtain ⟨okS, w3, tr3, hS, hRun⟩ := stateT_bind_eq hRun
      obtain ⟨hWf3, hTr3⟩ := shutdownWrClean_of_eq sys hRef cfd 16 w2 w3 tr2 tr3 okS hWf2 hS; clear hS
      cases okS with
      | true =>
        simp only [↓reduceIte, stateT_pure_run] at hRun
        injection hRun with hSl hWT; injection hWT with hW hT; subst hSl; subst hW; subst hT
        rw [hTr3]
        refine ⟨hWf3, hDq2.trans (congrArg _ hTr1), hDa2.trans (congrArg _ hTr1),
          hNe2', hCf2', ?_, ?_, ?_⟩
        · intro _ _ _ h; cases h
        · intro _ h; cases h
        · intro _ _ _ _ _ _ _ _ h; cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hRun
        obtain ⟨u, w4, tr4, hC, hRun⟩ := stateT_bind_eq hRun
        obtain ⟨hWf4, hDq4, hDa4, hNe4, hCf4, _⟩ := closeFd_of_eq sys hRef w3 w4 tr3 tr4 cfd u hWf3 hC; clear hC
        dsimp only [stateT_pure_run] at hRun
        injection hRun with hSl hWT; injection hWT with hW hT; subst hSl; subst hW; subst hT
        refine ⟨hWf4,
          hDq4.trans ((congrArg _ hTr3).trans (hDq2.trans (congrArg _ hTr1))),
          hDa4.trans ((congrArg _ hTr3).trans (hDa2.trans (congrArg _ hTr1))),
          fun e he => hNe4 ▸ hTr3 ▸ hNe2' e he,
          fun x hx => hCf4 x (hTr3 ▸ hCf2' x hx), ?_, ?_, ?_⟩
        · intro _ _ _ h; cases h
        · intro _ h; cases h
        · intro _ _ _ _ _ _ _ _ h; cases h
    · simp only [hSent, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with hSl hWT; injection hWT with hW hT; subst hSl; subst hW; subst hT
      refine ⟨hWf2, hDq2.trans (congrArg _ hTr1), hDa2.trans (congrArg _ hTr1),
        hNe2', hCf2', ?_, ?_, ?_⟩
      · intro _ _ _ h; cases h
      · intro _ h; cases h
      · intro _ _ _ _ _ _ _ _ h; cases h

/-- Internal SysBridge helper lemma `emitSlotEvent_fst_pipelined`. -/
theorem emitSlotEvent_fst_pipelined {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent) :
    (emitSlotEvent slot events ev).1.pipelined = slot.pipelined := by
  unfold emitSlotEvent; cases slot.eventEmitted <;> rfl

/-- Internal SysBridge helper lemma `reply200_init_u2c_toList`. -/
theorem reply200_init_u2c_toList :
    (({} : RingBuf).push Relay.reply200Bytes).toList = Relay.reply200Bytes.data.toList := by
  decide

/-- Internal SysBridge helper lemma `emitSlotEvent_snd_size`. -/
theorem emitSlotEvent_snd_size {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent) :
    (emitSlotEvent slot events ev).2.size = events.size + (if slot.eventEmitted then 0 else 1) := by
  unfold emitSlotEvent; cases slot.eventEmitted <;> simp


end LeanSwe.ConnectProxy.Proofs

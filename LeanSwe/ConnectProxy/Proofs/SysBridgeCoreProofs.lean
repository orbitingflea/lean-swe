import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreRelay

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

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

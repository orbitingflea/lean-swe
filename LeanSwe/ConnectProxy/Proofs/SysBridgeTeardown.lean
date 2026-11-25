import LeanSwe.ConnectProxy.Proofs.SysBridgeHandshake

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


private theorem healthy_stepHandshakeReadAux_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (deadlineMs : Nat) :
    ∀ (fuel : Nat) (headBuf : ByteArray)
      (w w' : HealthySysWorld) (tr tr' : SysAuditTrace Nat)
      (slot' : ClientSlot Nat Unit) (ev' : Array ConnectEvent),
      w.wf = true →
      headBuf.size ≤ cfg.limits.maxHeaderBytes →
      StateT.run (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd deadlineMs fuel headBuf) (w, tr) = ((slot', ev'), (w', tr')) →
      w'.wf = true ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      (∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' →
        ev' = events ∧
        slot'.eventEmitted = slot.eventEmitted ∧
        buf'.size ≤ cfg.limits.maxHeaderBytes ∧
        ((headBuf.size < cfg.limits.maxHeaderBytes ∨ fuel > 0) → buf'.size < cfg.limits.maxHeaderBytes) ∧
        (∃ rxDelta : List UInt8,
          tr'.recvBytes.toList = tr.recvBytes.toList ++ rxDelta ∧
          buf'.data.toList = headBuf.data.toList ++ rxDelta) ∧
        (w.netEnv.eintrBudget + (cfg.limits.maxHeaderBytes - headBuf.size) < fuel →
          Errno.EAGAIN ∈ tr'.netErrs.toList)) ∧
      ((∀ cfd' buf' dl', slot'.phase ≠ .handshake cfd' buf' dl') →
        (∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
        ev'.size = events.size + (if slot.eventEmitted then 0 else 1))
  | 0, headBuf, w, w', tr, tr', slot', ev', hWf, hLe, hRun => by
    dsimp only [stepHandshakeReadAux, stateT_pure_run] at hRun
    injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
    subst hs; subst he; subst hwe; subst hte
    refine ⟨hWf, fun _ h => h, fun _ buf' _ hPh => ?_, fun hNoHs => absurd rfl (hNoHs clientFd headBuf deadlineMs)⟩
    cases hPh
    exact ⟨rfl, rfl, hLe, fun hOr => by omega, ⟨[], by simp, by simp⟩, fun hLt => by omega⟩
  | fuel + 1, headBuf, w, w', tr, tr', slot', ev', hWf, hLe, hRun => by
    unfold stepHandshakeReadAux at hRun
    by_cases hMax : headBuf.size ≥ cfg.limits.maxHeaderBytes
    · simp only [hMax, ↓reduceIte] at hRun
      obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w w' tr tr' slot' ev' hWf hRun
      exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
    · simp only [hMax, ↓reduceIte] at hRun
      have hLtMax : headBuf.size < cfg.limits.maxHeaderBytes := by omega
      let rem := cfg.limits.maxHeaderBytes - headBuf.size
      let want := UInt32.ofNat (Nat.min rem HANDSHAKE_CHUNK_MAX)
      have hChunkBnd : 0 < HANDSHAKE_CHUNK_MAX ∧ HANDSHAKE_CHUNK_MAX < 4294967296 := by decide
      have hWantToNat : want.toNat = Nat.min rem HANDSHAKE_CHUNK_MAX := by
        have hSmall : Nat.min rem HANDSHAKE_CHUNK_MAX < UInt32.size := by
          simp only [nat_min_eq_min]
          change min rem HANDSHAKE_CHUNK_MAX < 4294967296
          omega
        exact UInt32.toNat_ofNat_of_lt hSmall
      have hWantLeRem : want.toNat ≤ rem := by
        rw [hWantToNat]; simp only [nat_min_eq_min]; omega
      have hWantPos : want.toNat > 0 := by
        rw [hWantToNat]; simp only [nat_min_eq_min]; omega
      obtain ⟨recvRes0, w10, tr10, hRecvRun, hRun⟩ := stateT_bind_eq hRun
      have hRecvRun' : (instrumentSysOps sys).net.recvfrom clientFd want { dontwait := true } (w, tr) = (recvRes0, (w10, tr10)) := hRecvRun
      clear hRecvRun
      rw [inst_net_recvfrom sys clientFd want { dontwait := true } w tr] at hRecvRun'
      have hNet := hRef.2.1 w (.recvfrom clientFd want { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
        pure, Pure.pure, StateT.pure, Id.run] at hNet
      rcases hRNet : sys.net.recvfrom clientFd want { dontwait := true } w with ⟨recvRes, w1⟩
      rw [hRNet] at hNet hRecvRun'
      dsimp only at hNet hRecvRun'
      injection hRecvRun' with hrr hwt; injection hwt with hwe hte
      subst hrr; subst hwe; subst hte
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.recvfrom clientFd want { dontwait := true }) (Net.outcomeOfBytes recvRes) hNet.1
      cases recvRes with
      | error e =>
        dsimp only at hRun
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte] at hRun
          have hEqEi : Net.outcomeOfBytes (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel headBuf w1 w' tr tr' slot' ev' hWf1 hLe hRun
          refine ⟨hSub.1, hSub.2.1, fun cfd' buf' dl' hPh => ?_, hSub.2.2.2⟩
          obtain ⟨hEvE, hEmE, hBLe, hBLt, hRx, hPr⟩ := hSub.2.2.1 cfd' buf' dl' hPh
          exact ⟨hEvE, hEmE, hBLe, fun _ => hBLt (Or.inl hLtMax), hRx, fun hFuel => hPr (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte] at hRun
          have hMono : ∀ x ∈ tr.netErrs.toList, x ∈ (tr.netErrs.push e).toList := by
            intro x hx; simp [Array.toList_push, hx]
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte, stateT_pure_run] at hRun
            injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
            subst hs; subst he; subst hwe; subst hte
            have hInAg : Errno.EAGAIN ∈ (tr.netErrs.push e).toList := by
              rw [beq_iff_eq.mp hAg]; simp [Array.toList_push]
            refine ⟨hWf1, hMono, fun _ buf' _ hPh => ?_, fun hNoHs => absurd rfl (hNoHs clientFd headBuf deadlineMs)⟩
            cases hPh
            exact ⟨rfl, rfl, hLe, fun _ => hLtMax, ⟨[], by simp, by simp⟩, fun _ => hInAg⟩
          · have hAgF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAg
            simp only [hAgF, Bool.false_eq_true, ↓reduceIte] at hRun
            let trErr := { tr with netErrs := tr.netErrs.push e }
            obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' trErr tr' slot' ev' hWf1 hRun
            exact ⟨hw, fun x hx => hne x (hMono x hx), fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
      | ok chunk =>
        dsimp only at hRun
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget := hBud.2 (fun hc => nomatch hc)
        let tr1 := { tr with recvBytes := tr.recvBytes ++
          (let k := Nat.min chunk.size want.toNat; if k == chunk.size then chunk.data else (chunk.extract 0 k).data) }
        by_cases hChunk0 : (chunk.size == 0) = true
        · simp only [hChunk0, ↓reduceIte] at hRun
          obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' tr1 tr' slot' ev' hWf1 hRun
          exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
        · have hChunkF : (chunk.size == 0) = false := Bool.eq_false_iff.mpr hChunk0
          simp only [hChunkF, Bool.false_eq_true, ↓reduceIte] at hRun
          have hChunkPos : chunk.size > 0 := by
            have hNe : chunk.size ≠ 0 := fun hc => hChunk0 (beq_iff_eq.mpr hc)
            omega
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          have hPartData : part.data = (let k := Nat.min chunk.size want.toNat; if k == chunk.size then chunk.data else (chunk.extract 0 k).data) := by
            dsimp only [part, takeN]
            split <;> rfl
          have hPartSz : part.size ≤ rem ∧ part.size > 0 := by
            dsimp only [part, takeN]
            simp only [nat_min_eq_min]
            split
            · rename_i hEq; have := beq_iff_eq.mp hEq; omega
            · simp only [ByteArray.size_extract]; omega
          have hNextSz : nextBuf.size ≤ cfg.limits.maxHeaderBytes ∧ nextBuf.size > headBuf.size := by
            dsimp only [nextBuf]
            by_cases hHb0 : (headBuf.size == 0) = true
            · simp only [hHb0, ↓reduceIte]
              have := beq_iff_eq.mp hHb0; omega
            · simp only [Bool.eq_false_iff.mpr hHb0, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append]
              omega
          have hNextList : nextBuf.data.toList = headBuf.data.toList ++ part.data.toList := by
            dsimp only [nextBuf]
            by_cases hHb0 : (headBuf.size == 0) = true
            · simp only [hHb0, ↓reduceIte]
              have hHbNil : headBuf.data.toList = [] :=
                List.eq_nil_of_length_eq_zero (by have := beq_iff_eq.mp hHb0; simpa using this)
              simp [hHbNil]
            · simp only [Bool.eq_false_iff.mpr hHb0, Bool.false_eq_true, ↓reduceIte]
              simp [ByteArray.data_append]
          cases hScan : findCrlfCrlf nextBuf (headBuf.size - 3) with
          | some pos =>
            rw [hScan] at hRun
            dsimp only at hRun
            let pipeBytes :=
              if pos + 4 ≥ nextBuf.size then ByteArray.empty else nextBuf.extract (pos + 4) nextBuf.size
            have hComp := healthy_handleCompleteHeadSync_of_eq sys hRef cfg slot events clientFd (nextBuf.extract 0 (pos + 4)) pipeBytes w1 w' tr1 tr' slot' ev' hWf1 hRun
            exact ⟨hComp.1, hComp.2.1, fun c b dl hPh => absurd hPh (hComp.2.2.1 c b dl), fun _ => hComp.2.2.2.2.2.1⟩
          | none =>
            rw [hScan] at hRun
            dsimp only at hRun
            by_cases hNextGe : nextBuf.size ≥ cfg.limits.maxHeaderBytes
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want, rem] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' tr1 tr' slot' ev' hWf1 hRun
              exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
            · have hNextLt : nextBuf.size < cfg.limits.maxHeaderBytes := by omega
              have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want, rem] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel nextBuf w1 w' tr1 tr' slot' ev' hWf1 hNextSz.1 hRun
              refine ⟨hSub.1, hSub.2.1, fun cfd' buf' dl' hPh => ?_, hSub.2.2.2⟩
              obtain ⟨hEvE, hEmE, hBLe, hBLt, ⟨rxDelta2, hTr2, hBuf2⟩, hProg2⟩ := hSub.2.2.1 cfd' buf' dl' hPh
              refine ⟨hEvE, hEmE, hBLe, fun _ => hBLt (Or.inl hNextLt), ⟨part.data.toList ++ rxDelta2, ?_, ?_⟩, fun hFuel => ?_⟩
              · rw [hTr2]; dsimp only [tr1]; rw [Array.toList_append, ← hPartData, List.append_assoc]
              · rw [hBuf2, hNextList, List.append_assoc]
              · exact hProg2 (by omega)

/-- `stepHandshakeReadAux` over ANY `sys` refining `RefinesHealthyCProxySys` preserves `wf` and enforces `headBuf.size ≤ maxHeaderBytes` across arbitrary short `recvfrom` chunks and `EINTR` retries. -/
theorem healthy_stepHandshakeReadAux_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (deadlineMs : Nat)
    (fuel : Nat) (headBuf : ByteArray) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : headBuf.size ≤ cfg.limits.maxHeaderBytes) :
    let ((slot', _), (w', _)) :=
      (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd deadlineMs fuel headBuf).run (w, tr)
    w'.wf = true ∧
    ∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' → buf'.size ≤ cfg.limits.maxHeaderBytes := by
  rcases hRun : (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd deadlineMs fuel headBuf).run (w, tr) with ⟨⟨slot', ev'⟩, w', tr'⟩
  have h := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel headBuf w w' tr tr' slot' ev' hWf hLe hRun
  exact ⟨h.1, fun c b d hp => (h.2.2.1 c b d hp).2.2.1⟩

/-- `stepHandshake` (with `startDnsSync`) over ANY `sys` refining `RefinesHealthyCProxySys` preserves `wf`, enforces `headBuf.size ≤ maxHeaderBytes` (strict `< maxHeaderBytes` after readable wakeups), conserves handshake bytes, retries `EINTR` until `EAGAIN` or transition, and emits a `ConnectEvent` unless entering `.connecting`. -/
theorem healthy_stepHandshakeSync_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (headBuf : ByteArray)
    (deadlineMs : Nat)
    (cRev : Poll.PollEvents)
    (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : headBuf.size ≤ cfg.limits.maxHeaderBytes)
    (hSlotPh : slot.phase = .handshake clientFd headBuf deadlineMs) :
    let ((slot', ev'), (w', tr')) :=
      (stepHandshake (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd headBuf deadlineMs cRev nowMs).run (w, tr)
    w'.wf = true ∧
    (∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' →
      buf'.size ≤ cfg.limits.maxHeaderBytes ∧
      ((cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true →
        buf'.size < cfg.limits.maxHeaderBytes) ∧
      (∃ rxDelta : List UInt8,
        tr'.recvBytes.toList = tr.recvBytes.toList ++ rxDelta ∧
        buf'.data.toList = headBuf.data.toList ++ rxDelta) ∧
      (cRev.pollin = true ∧
          w.netEnv.eintrBudget + (cfg.limits.maxHeaderBytes - headBuf.size) < MAX_HANDSHAKE_STEPS →
        Errno.EAGAIN ∈ tr'.netErrs.toList)) ∧
    ((∀ cfd' buf' dl', slot'.phase ≠ .handshake cfd' buf' dl') →
      (∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
      ev'.size = events.size + (if slot.eventEmitted then 0 else 1)) := by
  rcases hTop : (stepHandshake (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd headBuf deadlineMs cRev nowMs).run (w, tr) with ⟨⟨slot', ev'⟩, w', tr'⟩
  have hTop' : StateT.run (stepHandshake (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd headBuf deadlineMs cRev nowMs) (w, tr) = ((slot', ev'), (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold stepHandshake at hTop'
  by_cases hEv : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true
  · simp only [hEv, ↓reduceIte] at hTop'
    obtain ⟨⟨slot1, ev1⟩, w1, tr1, hStep1, hFin⟩ := stateT_bind_eq hTop'
    clear hTop'
    dsimp only at hFin
    obtain ⟨hWf1, _, hHs1, hEx1⟩ := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs MAX_HANDSHAKE_STEPS headBuf w w1 tr tr1 slot1 ev1 hWf hLe hStep1
    clear hStep1
    cases hPh : slot1.phase with
    | handshake cfd hb1 dl =>
      rw [hPh] at hFin; dsimp only at hFin
      by_cases hTo : nowMs ≥ dl
      · simp only [hTo, ↓reduceIte] at hFin
        obtain ⟨hEvEq, hEmEq, _⟩ := hHs1 cfd hb1 dl hPh
        obtain ⟨hw, _, _, _, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot1 ev1 _ cfd 403 w1 w' tr1 tr' slot' ev' hWf1 hFin
        rw [hEvEq, hEmEq] at hev
        exact ⟨hw, fun c b d hEq => absurd hEq (hph c b d), fun _ => Or.inr hev⟩
      · simp only [hTo, ↓reduceIte, stateT_pure_run] at hFin
        injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
        subst hS; subst hE; subst hW; subst hT
        refine ⟨hWf1, fun cfd' buf' dl' hEq => ?_, fun hNoHs => absurd hPh (hNoHs cfd hb1 dl)⟩
        obtain ⟨_, _, hBLe, hBLt, hRx, hPr⟩ := hHs1 cfd' buf' dl' hEq
        exact ⟨hBLe, fun _ => hBLt (Or.inr (by decide)), hRx, fun ⟨_, hF⟩ => hPr hF⟩
    | dns _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | relay _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | done =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
  · have hEvF : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = false := Bool.eq_false_iff.mpr hEv
    have hPollinF : cRev.pollin = false := by
      cases hp : cRev.pollin
      · rfl
      · simp [hp] at hEvF
    simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at hTop'
    obtain ⟨⟨slot1, ev1⟩, w1, tr1, hStep1, hFin⟩ := stateT_bind_eq hTop'
    clear hTop'
    dsimp only [stateT_pure_run] at hStep1
    injection hStep1 with hp hw; injection hp with hs he; injection hw with hwe hte
    subst hs; subst he; subst hwe; subst hte
    dsimp only at hFin
    rw [hSlotPh] at hFin
    dsimp only at hFin
    by_cases hTo : nowMs ≥ deadlineMs
    · simp only [hTo, ↓reduceIte] at hFin
      obtain ⟨hw, _, _, _, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w w' tr tr' slot' ev' hWf hFin
      exact ⟨hw, fun c b d hEq => absurd hEq (hph c b d), fun _ => Or.inr hev⟩
    · simp only [hTo, ↓reduceIte, stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      refine ⟨hWf, fun cfd' buf' dl' hEq => ?_, fun hNoHs => absurd hSlotPh (hNoHs clientFd headBuf deadlineMs)⟩
      rw [hSlotPh] at hEq
      cases hEq
      exact ⟨hLe, fun hBad => absurd hBad hEv, ⟨[], by simp, by simp⟩,
        fun ⟨hPin, _⟩ => by rw [hPollinF] at hPin; cases hPin⟩

/-- `emitSlotEvent` emits at most one `ConnectEvent` and permanently sets `eventEmitted = true`. -/
theorem emitSlotEvent_at_most_once {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent) :
    let (slot', events') := emitSlotEvent slot events ev
    slot'.eventEmitted = true ∧
    events'.size = events.size + (if slot.eventEmitted then 0 else 1) := by
  unfold emitSlotEvent
  dsimp only
  cases hEm : slot.eventEmitted <;> simp [hEm]

private theorem closeOptFd_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (optFd : Option Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := (NetRelay.closeOptFd (instrumentSysOps sys).closeFd optFd).run (w, tr)
    w'.wf = true ∧
    w'.proxyTable = w.proxyTable ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
    (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w'.filesEnv.state.fds j = none) ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup →
      (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
      ∀ d, optFd = some d → d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none) := by
  cases optFd with
  | none =>
    dsimp only [NetRelay.closeOptFd, StateT.run, pure, StateT.pure]
    exact ⟨hWf, rfl, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩
  | some d =>
    unfold NetRelay.closeOptFd NetRelay.Internal.closeOptFd
    have hCl := healthy_closeFd_instrumented_laws sys hRef w tr d hWf
    dsimp only [StateT.run] at hCl ⊢
    rcases hR : (instrumentSysOps sys).closeFd d (w, tr) with ⟨_, wt'⟩
    rcases wt' with ⟨w', tr'⟩
    rw [hR] at hCl
    dsimp only at hCl ⊢
    refine ⟨hCl.1, hCl.2.1, ?_, hCl.2.2.2.1, fun hNd => ⟨(hCl.2.2.2.2 hNd).1, fun d' hd' => ?_⟩⟩
    · intro x hx; rw [hCl.2.2.1]; simp [Array.toList_push, hx]
    · injection hd' with heq; subst heq
      refine ⟨?_, (hCl.2.2.2.2 hNd).2⟩
      rw [hCl.2.2.1]; simp [Array.toList_push]

private theorem healthy_teardownSlot_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (events1, (w1, tr1)) :=
      (teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr)
    w1.wf = true ∧
    w1.proxyTable = w.proxyTable ∧
    events1.size = events.size + (if slot.eventEmitted then 0 else 1) ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr1.closedFds.toList) ∧
    (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w1.filesEnv.state.fds j = none) ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup →
      (w1.filesEnv.state.fds.map Prod.fst).Nodup ∧
      ∀ fd ∈ slotOpenFds slot, fd ∈ tr1.closedFds.toList ∧ Files.assocGet w1.filesEnv.state.fds fd = none) := by
  have hEmitSz :
      (match slot.target? with
       | some (h, p) =>
         emitSlotEvent slot events { host := some h, port := some p, outcome := .failed, reason := some "proxy stopped" }
       | none =>
         emitSlotEvent slot events { outcome := .failed, reason := some "proxy stopped" }).2.size =
      events.size + (if slot.eventEmitted then 0 else 1) := by
    cases slot.target? with
    | some _ => exact (emitSlotEvent_at_most_once slot events _).2
    | none => exact (emitSlotEvent_at_most_once slot events _).2
  unfold teardownSlot slotOpenFds
  cases slot.phase with
  | handshake cfd _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr cfd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, ?_, h1.2.2.2.1, fun hNd => ⟨(h1.2.2.2.2 hNd).1, ?_⟩⟩
    · intro x hx; rw [h1.2.2.1]; simp [Array.toList_push, hx]
    · intro fd hMem; simp only [List.mem_singleton] at hMem; subst hMem
      refine ⟨?_, (h1.2.2.2.2 hNd).2⟩
      rw [h1.2.2.1]; simp [Array.toList_push]
  | dns cfd _ _ _ =>
    dsimp only
    rw [stateT_bind_run, stateT_pure_run]
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr cfd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, ?_, h1.2.2.2.1, fun hNd => ⟨(h1.2.2.2.2 hNd).1, ?_⟩⟩
    · intro x hx; rw [h1.2.2.1]; simp [Array.toList_push, hx]
    · intro fd hMem; simp only [List.mem_singleton] at hMem; subst hMem
      refine ⟨?_, (h1.2.2.2.2 hNd).2⟩
      rw [h1.2.2.1]; simp [Array.toList_push]
  | connecting cfd ufd _ _ _ _ _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr ufd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd ufd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only at h1 ⊢
    rw [stateT_bind_run]
    have h2 := healthy_closeFd_instrumented_laws sys hRef w1 tr1 cfd h1.1
    rcases hR2 : ((instrumentSysOps sys).closeFd cfd).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2
    dsimp only [stateT_pure_run] at h2 ⊢
    refine ⟨h2.1, h2.2.1.trans h1.2.1, hEmitSz, ?_, fun j hj => h2.2.2.2.1 j (h1.2.2.2.1 j hj), fun hNd => ?_⟩
    · intro x hx; rw [h2.2.2.1, h1.2.2.1]; simp [Array.toList_push, hx]
    · have hNd1 := (h1.2.2.2.2 hNd).1
      have hNd2 := (h2.2.2.2.2 hNd1).1
      refine ⟨hNd2, fun fd hMem => ?_⟩
      rcases List.mem_cons.mp hMem with rfl | hRest
      · refine ⟨?_, h2.2.2.2.1 fd (h1.2.2.2.2 hNd).2⟩
        rw [h2.2.2.1, h1.2.2.1]; simp [Array.toList_push]
      · simp only [List.mem_singleton] at hRest; subst hRest
        refine ⟨?_, (h2.2.2.2.2 hNd1).2⟩
        rw [h2.2.2.1]; simp [Array.toList_push]
  | relay st =>
    unfold Relay.closeRelayBoth
    dsimp only
    rw [stateT_bind_run, stateT_bind_run]
    have h1 := closeOptFd_instrumented_laws sys hRef st.clientFd? w tr hWf
    rcases hR1 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.clientFd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only at h1 ⊢
    rw [stateT_bind_run]
    have h2 := closeOptFd_instrumented_laws sys hRef st.upstreamFd? w1 tr1 h1.1
    rcases hR2 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.upstreamFd?).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2
    dsimp only [stateT_pure_run] at h2 ⊢
    refine ⟨h2.1, h2.2.1.trans h1.2.1, hEmitSz,
      fun x hx => h2.2.2.1 x (h1.2.2.1 x hx),
      fun j hj => h2.2.2.2.1 j (h1.2.2.2.1 j hj),
      fun hNd => ?_⟩
    obtain ⟨hNd1, hOpt1⟩ := h1.2.2.2.2 hNd
    obtain ⟨hNd2, hOpt2⟩ := h2.2.2.2.2 hNd1
    refine ⟨hNd2, fun fd hMem => ?_⟩
    rw [List.mem_append] at hMem
    rcases hMem with hC | hU
    · cases hc : st.clientFd? with
      | none => rw [hc] at hC; cases hC
      | some c =>
        rw [hc, List.mem_singleton] at hC; subst hC
        obtain ⟨hIn1, hNone1⟩ := hOpt1 fd hc
        exact ⟨h2.2.2.1 fd hIn1, h2.2.2.2.1 fd hNone1⟩
    · cases hu : st.upstreamFd? with
      | none => rw [hu] at hU; cases hU
      | some u =>
        rw [hu, List.mem_singleton] at hU; subst hU
        exact hOpt2 fd hu
  | closingReply cfd? _ _ _ _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := closeOptFd_instrumented_laws sys hRef cfd? w tr hWf
    rcases hR1 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd cfd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, h1.2.2.1, h1.2.2.2.1, fun hNd => ?_⟩
    obtain ⟨hNd1, hOpt1⟩ := h1.2.2.2.2 hNd
    refine ⟨hNd1, fun fd hMem => ?_⟩
    cases hc : cfd? with
    | none => rw [hc] at hMem; cases hMem
    | some c =>
      rw [hc, List.mem_singleton] at hMem; subst hMem
      exact hOpt1 fd hc
  | done =>
    dsimp only [stateT_bind_run, stateT_pure_run]
    exact ⟨hWf, rfl, hEmitSz, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩

/-- `teardownAllSlotsList` over ANY `sys` refining `RefinesHealthyCProxySys`: emits exact 1 `"proxy stopped"` event per undecided slot, preserves `wf`, `Nodup`, and `proxyTable`, and deterministically closes + erases every descriptor in `slotOpenFds`! -/
theorem healthy_teardownAllSlotsList_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) :
    ∀ (slots : List (ClientSlot Nat Unit)) (events : Array ConnectEvent)
      (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (events', (w', tr')) :=
        (teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) slots events).run (w, tr)
      w'.wf = true ∧
      w'.proxyTable = w.proxyTable ∧
      events'.size = events.size + (slots.filter (fun s => !s.eventEmitted)).length ∧
      (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
      (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w'.filesEnv.state.fds j = none) ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup →
        (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
        ∀ fd ∈ slots.flatMap slotOpenFds,
          fd ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds fd = none)
  | [], events, w, tr, hWf => by
    simp only [teardownAllSlotsList, List.filter_nil, List.length_nil, Nat.add_zero]
    exact ⟨hWf, rfl, rfl, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩
  | slot :: rest, events, w, tr, hWf => by
    unfold teardownAllSlotsList
    rw [stateT_bind_run]
    have hSlot := healthy_teardownSlot_laws sys hRef slot events w tr hWf
    rcases hSlotRun : (teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr) with ⟨events1, w1, tr1⟩
    rw [hSlotRun] at hSlot
    dsimp only at hSlot ⊢
    rcases hSlot with ⟨hWf1, hTbl1, hEmitSz, hClosed1, hGet1, hNdSlot⟩
    have hRest := healthy_teardownAllSlotsList_laws sys hRef rest events1 w1 tr1 hWf1
    rcases hRestRun : (teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) rest events1).run (w1, tr1) with ⟨ev2, w2, tr2⟩
    rw [hRestRun] at hRest
    dsimp only at hRest ⊢
    refine ⟨hRest.1, hRest.2.1.trans hTbl1, ?_,
      fun x hx => hRest.2.2.2.1 x (hClosed1 x hx),
      fun j hj => hRest.2.2.2.2.1 j (hGet1 j hj),
      fun hNd => ?_⟩
    · rw [hRest.2.2.1, hEmitSz]
      cases hEm : slot.eventEmitted <;> simp [List.filter, hEm] <;> omega
    · obtain ⟨hNd1, hSlotFds⟩ := hNdSlot hNd
      obtain ⟨hNd2, hRestFds⟩ := hRest.2.2.2.2.2 hNd1
      refine ⟨hNd2, fun fd hMem => ?_⟩
      simp only [List.flatMap_cons, List.mem_append] at hMem
      rcases hMem with hHead | hTail
      · obtain ⟨hIn1, hNone1⟩ := hSlotFds fd hHead
        exact ⟨hRest.2.2.2.1 fd hIn1, hRest.2.2.2.2.1 fd hNone1⟩
      · exact hRestFds fd hTail


end LeanSwe.ConnectProxy.Proofs

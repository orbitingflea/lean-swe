import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreBase

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

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
  unfold Net.healthyStep at h
  by_cases hBad : (!env.wf || Net.isCriticalFault out) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : Net.allowedStep env.state req out with
    | none => simp [hAl] at h
    | some s' =>
      rw [hAl] at h; dsimp only at h
      cases hEi : Net.isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨fun hEq => ?_, fun _ => rfl⟩
        subst hEq; cases hEi
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hPos : env.eintrBudget > 0
        · simp only [hPos, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨fun _ => ⟨hPos, rfl⟩, fun hNe => False.elim (hNe ?_)⟩
          cases out with
          | err e => exact congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          | _ => cases hEi
        · simp [hPos] at h
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

/-- Internal ConnectProxy proof helper `accepted_slice_toList`. -/
theorem accepted_slice_toList (bs : ByteArray) (lim : Nat) :
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


end LeanSwe.ConnectProxy.Proofs

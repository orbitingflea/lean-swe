import Core.NondetTest
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Net.SpecTests

namespace LeanSwe.LinuxSyscall.Net

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem foldl_max_ge (xs : List (HandleId × NetHandleEntry)) (init : Nat) :
    init ≤ xs.foldl (fun acc (h, e) => match e with | .open _ _ => max acc (h + 1) | .closed => acc) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    rcases hd with ⟨h, e⟩
    simp only [List.foldl_cons]
    cases e with
    | closed => exact ih init
    | «open» _ _ => exact Nat.le_trans (Nat.le_max_left init (h + 1)) (ih (max init (h + 1)))

private theorem assocGet_handles_lt_foldl (xs : List (HandleId × NetHandleEntry)) (init k fid : Nat) (clo : Bool)
    (hget : assocGet xs k = some (.open fid clo)) :
    k < xs.foldl (fun acc (h, e) => match e with | .open _ _ => max acc (h + 1) | .closed => acc) init := by
  induction xs generalizing init with
  | nil => simp [assocGet] at hget
  | cons hd tl ih =>
    rcases hd with ⟨h, e⟩
    simp only [assocGet] at hget
    simp only [List.foldl_cons]
    by_cases heq : (h == k) = true
    · rw [heq] at hget
      simp only [ite_true] at hget
      injection hget with he
      subst he
      have hk : h = k := beq_iff_eq.mp heq
      subst hk
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self h) (Nat.le_max_right init (h + 1)))
        (foldl_max_ge tl (max init (h + 1)))
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hget
      cases e with
      | closed => exact ih init hget
      | «open» _ _ => exact ih (max init (h + 1)) hget

private theorem isFreshHid_freshHidBase_add (s : NetState) (k : Nat) :
    isFreshHid s (freshHidBase s + k) = true := by
  unfold isFreshHid
  cases hget : assocGet s.handles (freshHidBase s + k) with
  | none => rfl
  | some e =>
    cases e with
    | closed => rfl
    | «open» fid clo =>
      exfalso
      have hlt : freshHidBase s + k < freshHidBase s :=
        assocGet_handles_lt_foldl s.handles s.nextHid (freshHidBase s + k) fid clo hget
      exact Nat.not_lt_of_le (Nat.le_add_right (freshHidBase s) k) hlt

private theorem isFreshHid_freshHidBase (s : NetState) :
    isFreshHid s (freshHidBase s) = true := by
  simpa using isFreshHid_freshHidBase_add s 0

private theorem assocGet_append {α β : Type} [BEq α] (xs ys : List (α × β)) (j : α) :
    assocGet (xs ++ ys) j = match assocGet xs j with | some v => some v | none => assocGet ys j := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, v⟩
    simp only [List.cons_append, assocGet]
    by_cases hxj : (x == j) = true
    · simp [hxj]
    · simp [hxj, ih]

private theorem assocGet_assocSetAux_ne {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (k j : α) (v : β) (acc : List (α × β)) (hne : k ≠ j) :
    assocGet (assocSetAux xs k v acc) j = assocGet (acc.reverse ++ xs) j := by
  induction xs generalizing acc with
  | nil =>
    rw [assocSetAux, List.reverseAux_eq, assocGet_append, assocGet_append]
    have hj : (k == j) = false := beq_false_of_ne hne
    simp [assocGet, hj]
  | cons hd tl ih =>
    rcases hd with ⟨x, old⟩
    simp only [assocSetAux]
    by_cases hkx : (x == k) = true
    · simp only [hkx, ↓reduceIte]
      rw [List.reverseAux_eq, assocGet_append, assocGet_append]
      have hxk : x = k := beq_iff_eq.mp hkx
      subst hxk
      have hkj : (x == j) = false := beq_false_of_ne hne
      simp [assocGet, hkj]
    · simp only [hkx, Bool.false_eq_true, ↓reduceIte]
      rw [ih ((x, old) :: acc)]
      simp [List.reverse_cons, List.append_assoc]

private theorem assocGet_assocSet_ne {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (k j : α) (v : β) (hne : k ≠ j) :
    assocGet (assocSet xs k v) j = assocGet xs j := by
  simpa [assocSet] using assocGet_assocSetAux_ne xs k j v [] hne

private theorem isFreshHid_set_lt (s : NetState) (h nextH : Nat) (fid : FileId) (clo : Bool) (hid : HandleId)
    (hlt : hid < h) (hf : isFreshHid s h = true) :
    isFreshHid { s with handles := assocSet s.handles hid (.open fid clo), nextHid := nextH } h = true := by
  unfold isFreshHid at hf ⊢
  have hne : hid ≠ h := Nat.ne_of_lt hlt
  simp only [assocGet_assocSet_ne s.handles hid h (.open fid clo) hne]
  exact hf

private theorem emitErr_none_sound {s : NetState} {canon : Errno}
    {alts : List Errno} {onErr : Errno → NetState} {allowTransient : Bool} {allowUnit? : Option NetState}
    {allowU32? : Option (UInt32 → Option NetState)} {allowBytes? : Option (ByteArray → Option NetState)}
    {out : NetOutcome} {s' : NetState}
    (h : emitErr none s canon alts onErr allowTransient allowUnit? allowU32? allowBytes? = some (out, s')) :
    emitErr (some out) s canon alts onErr allowTransient allowUnit? allowU32? allowBytes? = some (out, s') := by
  dsimp only [emitErr] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  simp

private theorem emitUnit_none_sound {s sOk : NetState}
    {altErrs : List Errno} {onAltErr : Errno → NetState} {allowTransient : Bool}
    {out : NetOutcome} {s' : NetState}
    (h : emitUnit none s sOk altErrs onAltErr allowTransient = some (out, s')) :
    emitUnit (some out) s sOk altErrs onAltErr allowTransient = some (out, s') := by
  dsimp only [emitUnit] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem emitU32_none_sound {s : NetState} {canon : UInt32} {sOk : NetState}
    {altErrs : List Errno} {allowZeroOk : Bool} {onAltErr : Errno → NetState} {allowTransient : Bool}
    {out : NetOutcome} {s' : NetState}
    (h : emitU32 none s canon sOk altErrs allowZeroOk onAltErr allowTransient = some (out, s')) :
    emitU32 (some out) s canon sOk altErrs allowZeroOk onAltErr allowTransient = some (out, s') := by
  dsimp only [emitU32] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  simp

private theorem emitAllocFd_none_sound {s : NetState} {desc : SockDesc} {cloexec : Bool}
    {altErrs : List Errno} {allowTransient : Bool} {out : NetOutcome} {s' : NetState}
    (h : emitAllocFd none s desc cloexec altErrs allowTransient = some (out, s')) :
    emitAllocFd (some out) s desc cloexec altErrs allowTransient = some (out, s') := by
  dsimp only [emitAllocFd] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  simp [isFreshHid_freshHidBase s]

private theorem emitAllocPair_none_sound {s : NetState} {d0 d1 : SockDesc} {cloexec : Bool}
    {altErrs : List Errno} {out : NetOutcome} {s' : NetState}
    (h : emitAllocPair none s d0 d1 cloexec altErrs = some (out, s')) :
    emitAllocPair (some out) s d0 d1 cloexec altErrs = some (out, s') := by
  dsimp only [emitAllocPair] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  have h0 := isFreshHid_freshHidBase_add s 0
  have h1' := isFreshHid_freshHidBase_add s 1
  simp only [Nat.add_zero] at h0
  simp [h0, h1']

private theorem emitAddr_none_sound {s : NetState} {canon : SockAddr} {validate : SockAddr → Option NetState}
    {out : NetOutcome} {s' : NetState}
    (h : emitAddr none s canon validate = some (out, s')) :
    emitAddr (some out) s canon validate = some (out, s') := by
  dsimp only [emitAddr] at h ⊢
  cases hv : validate canon with
  | none => simp [hv] at h
  | some sOk =>
    simp [hv] at h
    rcases h with ⟨rfl, rfl⟩
    simp [hv]

private theorem emitBytes_none_sound {s : NetState} {canon : ByteArray}
    {validate : ByteArray → Option NetState} {altErrs : List Errno} {out : NetOutcome} {s' : NetState}
    (h : emitBytes none s canon validate altErrs = some (out, s')) :
    emitBytes (some out) s canon validate altErrs = some (out, s') := by
  dsimp only [emitBytes] at h ⊢
  cases hv : validate canon with
  | none => simp [hv] at h
  | some sOk =>
    simp [hv] at h
    rcases h with ⟨rfl, rfl⟩
    simp [hv]

private theorem emitAccept_none_sound {s : NetState} {lFid : FileId} {ld : SockDesc}
    {aq : List AcceptEntry} {flags : SockFlags} {out : NetOutcome} {s' : NetState}
    (h : emitAccept none s lFid ld aq flags = some (out, s')) :
    emitAccept (some out) s lFid ld aq flags = some (out, s') := by
  dsimp only [emitAccept] at h ⊢
  cases aq with
  | nil => exact emitErr_none_sound h
  | cons accEntry restQ =>
    dsimp only at h ⊢
    by_cases hnb : ld.nonblock = true
    · simp only [hnb, ↓reduceIte] at h ⊢
      by_cases hm : matchesAcceptPeerAddr accEntry.peerAddr accEntry.peerAddr (!accEntry.peerPortPinned) accEntry.matchKind accEntry.peerRoutedV4 = true
      · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        rcases h with ⟨rfl, rfl⟩
        simp [isFreshHid_freshHidBase s, hm]
      · simp [hm] at h
    · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hm : matchesAcceptPeerAddr accEntry.peerAddr accEntry.peerAddr (!accEntry.peerPortPinned) accEntry.matchKind accEntry.peerRoutedV4 = true
      · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        rcases h with ⟨rfl, rfl⟩
        simp [isFreshHid_freshHidBase s, hm]
      · simp [hm] at h

private theorem streamBytesMatchesAux_refl (b mask : ByteArray) (rem i : Nat) :
    streamBytesMatchesAux b b mask rem i = true := by
  induction rem generalizing i with
  | zero => rfl
  | succ rem ih =>
    simp only [streamBytesMatchesAux, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact ih (i + 1)

private theorem streamBytesMatches_refl (b mask : ByteArray) :
    streamBytesMatches b b mask = true :=
  streamBytesMatchesAux_refl b mask b.size 0

private theorem cloneScmHandles_bind (rem : Nat) (nextH : HandleId) (batch : List FileId)
    (s : NetState) (acc : List HandleId)
    (hfresh : ∀ j, nextH ≤ j → isFreshHid s j = true) :
    let (sClone, got) := cloneScmHandles s rem nextH batch acc
    ∃ newTail, got.toList = acc.reverse ++ newTail ∧
      newTail.length = min rem batch.length ∧
      bindReceivedScmHandles s newTail (batch.take newTail.length) = some sClone := by
  induction rem generalizing s nextH batch acc with
  | zero =>
    cases batch <;> simp [cloneScmHandles, bindReceivedScmHandles]
  | succ rem ih =>
    cases batch with
    | nil => simp [cloneScmHandles, bindReceivedScmHandles]
    | cons srcFid rest =>
      simp only [cloneScmHandles]
      let s1 : NetState := { s with handles := assocSet s.handles nextH (.open srcFid true), nextHid := max s.nextHid (nextH + 1) }
      have hf1 : ∀ j, nextH + 1 ≤ j → isFreshHid s1 j = true := by
        intro j hj
        exact isFreshHid_set_lt s j (max s.nextHid (nextH + 1)) srcFid true nextH (Nat.lt_of_succ_le hj) (hfresh j (Nat.le_of_succ_le hj))
      have ihRes := ih (nextH + 1) rest s1 (nextH :: acc) hf1
      rcases hcl : cloneScmHandles s1 rem (nextH + 1) rest (nextH :: acc) with ⟨sClone, got⟩
      simp only [hcl] at ihRes
      rcases ihRes with ⟨newTail, hgot, hlen, hbind⟩
      refine ⟨nextH :: newTail, ?_, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using hgot
      · have hmin : min (rem + 1) (rest.length + 1) = min rem rest.length + 1 := by
          cases Nat.le_total rem rest.length with
          | inl hle => simp [Nat.min_eq_left, hle, Nat.succ_le_succ]
          | inr hle => simp [Nat.min_eq_right, hle, Nat.succ_le_succ]
        rw [List.length_cons, List.length_cons, hlen, hmin]
      · simp only [List.length_cons, List.take_succ_cons, bindReceivedScmHandles]
        have hf0 : isFreshHid s nextH = true := hfresh nextH (Nat.le_refl _)
        simp only [hf0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
        exact hbind

private theorem minU32_u32_toNat (n : Nat) (hne : n ≠ 0) :
    (UInt32.ofNat (min n 4294967295)).toNat = min n 4294967295 ∧
    1 ≤ min n 4294967295 := by
  have hlt : min n 4294967295 < UInt32.size := by change min n 4294967295 < 4294967296; omega
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  omega

private theorem stepBindInet_none_sound {s : NetState} {hid : HandleId} {selfFid : FileId}
    {d : SockDesc} {addr : SockAddr} {port : UInt16} {out : NetOutcome} {s' : NetState}
    (h : stepBindInet s hid selfFid d addr port none = some (out, s')) :
    stepBindInet s hid selfFid d addr port (some out) = some (out, s') := by
  unfold stepBindInet at h ⊢
  dsimp only at h ⊢
  by_cases hcb : (!canBindInet d) = true
  · simp only [hcb, ↓reduceIte] at h ⊢
    exact emitErr_none_sound h
  · simp only [hcb, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hinv : isInvalidV6LinkOrMulticast d.sockType addr d.boundDevIf = true
    · simp only [hinv, ↓reduceIte] at h ⊢
      exact emitErr_none_sound h
    · simp only [hinv, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hsc : ipv6ScopedIfindex? d.sockType addr <;> simp only [hsc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      · by_cases hdev : (!isIpv6WildcardAddr addr && d.boundDevIf != 0 && d.boundDevIf != 1) = true
        · simp only [hdev, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
        · simp only [hdev, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hloc : (!isLocalBindableAddr addr) = true
          · simp only [hloc, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
          · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hconf : (port != 0 && hasBindPortConflict s hid d.sockType d.reuseAddr (normalizeBindAddr addr d.boundDevIf)) = true
            · simp only [hconf, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
            · simp only [hconf, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitUnit_none_sound h
      · rename_i sc
        generalize hs1 : (if (sc != d.boundDevIf) = true then setFileSocket s selfFid { d with boundDevIf := sc } else s) = s1 at h ⊢
        by_cases hdev : (!isIpv6WildcardAddr addr && sc != 0 && sc != 1) = true
        · simp only [hdev, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
        · simp only [hdev, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hloc : (!isLocalBindableAddr addr) = true
          · simp only [hloc, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
          · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hconf : (port != 0 && hasBindPortConflict s1 hid ({ d with boundDevIf := sc }).sockType d.reuseAddr (normalizeBindAddr addr sc)) = true
            · simp only [hconf, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
            · simp only [hconf, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitUnit_none_sound h

private theorem stepBind_none_sound {s : NetState} {hid : HandleId} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepBind s hid addr none = some (out, s')) :
    stepBind s hid addr (some out) = some (out, s') := by
  unfold stepBind withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      (split at h <;> split <;> try contradiction)
      · exact emitErr_none_sound h
      · cases addr with
        | unix path =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · (split at h <;> split <;> try contradiction)
            · exact emitErr_none_sound h
            · exact emitErr_none_sound h
          · (split at h <;> split <;> try contradiction)
            · exact emitErr_none_sound h
            · exact emitUnit_none_sound h
        | ipv4 _ port => exact stepBindInet_none_sound h
        | ipv6 _ _ port _ _ => exact stepBindInet_none_sound h

private theorem stepListen_none_sound {s : NetState} {hid : HandleId} {backlog : UInt32}
    {out : NetOutcome} {s' : NetState}
    (h : stepListen s hid backlog none = some (out, s')) :
    stepListen s hid backlog (some out) = some (out, s') := by
  unfold stepListen withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hp : d.proto with
      | udp _ _ _ | unixDgram _ _ =>
        simp only [hp] at h ⊢
        exact emitErr_none_sound h
      | unixStream isSeq bp conn =>
        simp only [hp] at h ⊢
        cases conn with
        | listen _ aq => exact emitUnit_none_sound h
        | connected _ _ _ _ _ =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · exact emitUnit_none_sound h
        | idle =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · exact emitUnit_none_sound h
      | tcp fam bind sockState tcpState tainted =>
        simp only [hp] at h ⊢
        (split at h <;> split <;> try contradiction)
        · exact emitErr_none_sound h
        · cases tcpState with
          | listen _ aq => exact emitUnit_none_sound h
          | synSent _ | established _ _ | finWait _ _ | closeWait _ _ _ => exact emitErr_none_sound h
          | idle | closedAfterConn _ _ =>
            cases bind with
            | unbound => exact emitUnit_none_sound h
            | hashed _ _ _ _ =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitUnit_none_sound h
            | unhashed _ _ _ => exact emitUnit_none_sound h

private theorem stepAccept4_none_sound {s : NetState} {hid : HandleId} {flags : SockFlags}
    {out : NetOutcome} {s' : NetState}
    (h : stepAccept4 s hid flags none = some (out, s')) :
    stepAccept4 s hid flags (some out) = some (out, s') := by
  unfold stepAccept4 withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some lFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s lFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok ld =>
      simp only [hsock] at h ⊢
      cases hp : ld.proto with
      | udp _ _ _ | unixDgram _ _ =>
        simp only [hp] at h ⊢
        exact emitErr_none_sound h
      | tcp _ _ _ ts _ =>
        simp only [hp] at h ⊢
        cases ts with
        | listen _ aq => exact emitAccept_none_sound h
        | _ => exact emitErr_none_sound h
      | unixStream _ _ conn =>
        simp only [hp] at h ⊢
        cases conn with
        | listen _ aq =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · exact emitAccept_none_sound h
        | _ => exact emitErr_none_sound h

private theorem stepUnixDgramConnect_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {bp? : Option ByteArray} {oldPeer? : Option (FileId × SockAddr)} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepUnixDgramConnect s selfFid d bp? oldPeer? addr none = some (out, s')) :
    stepUnixDgramConnect s selfFid d bp? oldPeer? addr (some out) = some (out, s') := by
  unfold stepUnixDgramConnect at h ⊢
  cases addr with
  | ipv4 _ _ | ipv6 _ _ _ _ _ => exact emitErr_none_sound h
  | unix path =>
    dsimp only at h ⊢
    cases hfd : findBoundUnixSocket s .dgram path with
    | none => simp only [hfd] at h ⊢; exact emitErr_none_sound h
    | some p =>
      simp only [hfd] at h ⊢
      (split at h <;> split <;> try contradiction)
      · exact emitErr_none_sound h
      · (split at h <;> split <;> try contradiction)
        · exact emitErr_none_sound h
        · exact emitUnit_none_sound h

private theorem stepUdpConnect_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {fam : InetFamily} {bind : InetBind} {rawAddr : SockAddr} {out : NetOutcome} {s' : NetState}
    (h : stepUdpConnect s selfFid d fam bind rawAddr none = some (out, s')) :
    stepUdpConnect s selfFid d fam bind rawAddr (some out) = some (out, s') := by
  unfold stepUdpConnect at h ⊢
  generalize had : normalizeUdpTarget d.domain rawAddr bind.addr? = addr at h ⊢
  dsimp only at h ⊢
  by_cases hdom : (addr.domain != d.domain) = true
  · simp only [hdom, ↓reduceIte] at h ⊢
    exact emitErr_none_sound h
  · simp only [hdom, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hsc : ipv6ScopedIfindex? .dgram addr <;> simp only [hsc] at h ⊢
    · by_cases hinv : isInvalidV6LinkOrMulticast .dgram addr d.boundDevIf = true
      · simp only [hinv, Bool.false_or, ↓reduceIte] at h ⊢
        exact emitErr_none_sound h
      · simp only [hinv, Bool.false_or, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at h ⊢
        cases hmis : v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (loDownWasUp s.loState) with
        | some _ => simp only [hmis] at h ⊢; exact emitErr_none_sound h
        | none =>
          simp only [hmis] at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · (split at h <;> split <;> try contradiction)
            · exact emitErr_none_sound h
            · (split at h <;> split <;> try contradiction)
              · cases hlo : s.loState with
                | down _ b => simp only [hlo] at h ⊢; cases b <;> exact emitErr_none_sound h
                | unpinned _ | up _ => simp only [hlo] at h ⊢; exact emitUnit_none_sound h
              · exact emitUnit_none_sound h
    · rename_i sc
      by_cases hinv : ((d.boundDevIf != 0 && d.boundDevIf != sc) || isInvalidV6LinkOrMulticast .dgram addr d.boundDevIf) = true
      · simp only [hinv, ↓reduceIte] at h ⊢
        exact emitErr_none_sound h
      · simp only [hinv, Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize hs1 : (if (sc != d.boundDevIf) = true then setFileSocket s selfFid { d with boundDevIf := sc } else s) = s1 at h ⊢
        cases hmis : v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (loDownWasUp s1.loState) with
        | some _ => simp only [hmis] at h ⊢; exact emitErr_none_sound h
        | none =>
          simp only [hmis] at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · (split at h <;> split <;> try contradiction)
            · exact emitErr_none_sound h
            · (split at h <;> split <;> try contradiction)
              · cases hlo : s1.loState with
                | down _ b => simp only [hlo] at h ⊢; cases b <;> exact emitErr_none_sound h
                | unpinned _ | up _ => simp only [hlo] at h ⊢; exact emitUnit_none_sound h
              · exact emitUnit_none_sound h

private theorem stepUnixStreamConnect_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {isSeq : Bool} {bp? : Option ByteArray} {conn : UnixConnState} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepUnixStreamConnect s selfFid d isSeq bp? conn addr none = some (out, s')) :
    stepUnixStreamConnect s selfFid d isSeq bp? conn addr (some out) = some (out, s') := by
  unfold stepUnixStreamConnect at h ⊢
  dsimp only at h ⊢
  (split at h <;> split <;> try contradiction)
  · exact emitErr_none_sound h
  · cases hfd : findMatchingListener s selfFid .unix d.sockType addr with
    | none =>
      simp only [hfd] at h ⊢
      exact emitErr_none_sound h
    | some p =>
      simp only [hfd] at h ⊢
      rcases p with ⟨lFid, lDesc, mk⟩
      cases hlp : lDesc.proto with
      | unixStream lSeq lBp lConn =>
        simp only [hlp] at h ⊢
        cases lConn with
        | listen lBacklog aq =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · cases conn with
            | listen _ _ => exact emitErr_none_sound h
            | connected _ _ _ _ _ => exact emitErr_none_sound h
            | idle =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitUnit_none_sound h
        | _ => exact emitErr_none_sound h
      | _ =>
        simp only [hlp] at h ⊢
        exact emitErr_none_sound h

private theorem stepTcpSelfConnect_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {fam : InetFamily} {bind : InetBind} {tainted : Bool} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepTcpSelfConnect s selfFid d fam bind tainted addr none = some (out, s')) :
    stepTcpSelfConnect s selfFid d fam bind tainted addr (some out) = some (out, s') := by
  unfold stepTcpSelfConnect at h ⊢
  dsimp only at h ⊢
  (split at h <;> split <;> try contradiction)
  · rcases h with ⟨rfl, rfl⟩
    simp
  · (split at h <;> split <;> try contradiction)
    · exact emitErr_none_sound h
    · exact emitUnit_none_sound h

private theorem stepTcpConnectLookupListener_none_sound {s : NetState} {selfFid : FileId}
    {d : SockDesc} {fam : InetFamily} {bind : InetBind} {nextTainted : Bool}
    {ep nextP : UInt16} {addr : SockAddr} {out : NetOutcome} {s' : NetState}
    (h : stepTcpConnectLookupListener s selfFid d fam bind nextTainted ep nextP addr none = some (out, s')) :
    stepTcpConnectLookupListener s selfFid d fam bind nextTainted ep nextP addr (some out) = some (out, s') := by
  unfold stepTcpConnectLookupListener at h ⊢
  dsimp only at h ⊢
  (split at h <;> split <;> try contradiction)
  · exact emitErr_none_sound h
  · cases hlis : findMatchingListener s selfFid d.domain .stream
        (resolveTargetAddrForClient (some (tcpConnectLocalBind d.domain bind addr ep nextP s.nextPort false d.inetSaddrZero).1) addr) with
    | none =>
      simp only [hlis] at h ⊢
      by_cases hnb : d.nonblock = true
      · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
      · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
    | some l =>
      simp only [hlis] at h ⊢
      rcases l with ⟨lFid, lDesc, matchKind⟩
      cases hlp : lDesc.proto with
      | tcp lFam lBind lSs lTcp lTaint =>
        simp only [hlp] at h ⊢
        cases lTcp with
        | listen lBacklog aq =>
          by_cases hnb : d.nonblock = true
          · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
          · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hovf : aq.length > lBacklog.toNat
            · simp only [hovf, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
            · simp only [hovf, ↓reduceIte] at h ⊢; exact emitUnit_none_sound h
        | _ => exact emitErr_none_sound h
      | _ =>
        simp only [hlp] at h ⊢
        exact emitErr_none_sound h

private theorem stepTcpConnectNewCore_none_sound {s1 : NetState} {selfFid : FileId} {d1 : SockDesc}
    {fam : InetFamily} {bind : InetBind} {tainted : Bool} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepTcpConnectNewCore s1 selfFid d1 fam bind tainted addr none = some (out, s')) :
    stepTcpConnectNewCore s1 selfFid d1 fam bind tainted addr (some out) = some (out, s') := by
  unfold stepTcpConnectNewCore at h ⊢
  generalize hsa : (if sockAddrHasScope addr || d1.boundDevIf != 0 then [Errno.ENODEV] else []) = scopeAlts at h ⊢
  generalize hlda : (if isLoopbackTargetAddr addr && (match s1.loState with | .down _ _ => true | _ => false) then [Errno.EADDRNOTAVAIL] else []) = loDownLoopAlts at h ⊢
  generalize heff : resolveTargetAddrForClient bind.addr? addr = effAddr at h ⊢
  dsimp only at h ⊢
  cases hmis : v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (loDownWasUp s1.loState) with
  | some _ => simp only [hmis] at h ⊢; exact emitErr_none_sound h
  | none =>
    simp only [hmis] at h ⊢
    by_cases hTaint : (fam == .v6 && tainted && !isIpv4MappedV6Addr effAddr) = true
    · simp only [hTaint, ↓reduceIte] at h ⊢
      by_cases hnb : d1.nonblock = true
      · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
      · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
    · simp only [hTaint, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hMc : isMcastOrBcastTargetAddr effAddr = true
      · simp only [hMc, ↓reduceIte] at h ⊢
        cases hlo : s1.loState with
        | up _ => simp only [hlo, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
        | unpinned _ => simp only [hlo, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
        | down _ wasUp =>
          cases wasUp with
          | false => simp only [hlo, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
          | true =>
            simp only [hlo, Bool.and_true] at h ⊢
            by_cases hDir : isDirectedLoopBcastAddr effAddr = true
            · simp only [hDir, ↓reduceIte] at h ⊢
              by_cases hnb : d1.nonblock = true
              · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
              · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
            · simp only [hDir, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
      · simp only [hMc, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hBdi : (d1.boundDevIf != 0 && d1.boundDevIf != 1) = true
        · simp only [hBdi, ↓reduceIte] at h ⊢
          by_cases hnb : d1.nonblock = true
          · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
          · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
        · simp only [hBdi, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hlo : s1.loState with
          | up _ | unpinned _ =>
            simp only [hlo, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hSelf : isTcpSelfConnect d1 effAddr = true
            · simp only [hSelf, ↓reduceIte] at h ⊢; exact stepTcpSelfConnect_none_sound h
            · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact stepTcpConnectLookupListener_none_sound h
          | down _ wasUp =>
            cases wasUp with
            | false =>
              simp only [hlo, Bool.and_true, Bool.and_false] at h ⊢
              by_cases hLoop : isLoopbackTargetAddr effAddr = true
              · simp only [hLoop, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
              · simp only [hLoop, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hSelf : isTcpSelfConnect d1 effAddr = true
                · simp only [hSelf, ↓reduceIte] at h ⊢; exact stepTcpSelfConnect_none_sound h
                · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact stepTcpConnectLookupListener_none_sound h
            | true =>
              simp only [hlo, Bool.and_true] at h ⊢
              by_cases hLoop : isLoopbackTargetAddr effAddr = true
              · simp only [hLoop, Bool.and_true, ↓reduceIte] at h ⊢
                by_cases hnb : d1.nonblock = true
                · simp only [hnb, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
                · simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
              · simp only [hLoop, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hSelf : isTcpSelfConnect d1 effAddr = true
                · simp only [hSelf, ↓reduceIte] at h ⊢; exact stepTcpSelfConnect_none_sound h
                · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact stepTcpConnectLookupListener_none_sound h

private theorem stepTcpConnectNew_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {fam : InetFamily} {bind : InetBind} {tainted : Bool} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepTcpConnectNew s selfFid d fam bind tainted addr none = some (out, s')) :
    stepTcpConnectNew s selfFid d fam bind tainted addr (some out) = some (out, s') := by
  unfold stepTcpConnectNew at h ⊢
  dsimp only at h ⊢
  by_cases hDom : (addr.domain != d.domain) = true
  · simp only [hDom, ↓reduceIte] at h ⊢
    exact emitErr_none_sound h
  · simp only [hDom, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hsc : ipv6LinkLocalScope? addr <;> simp only [hsc] at h ⊢
    · by_cases hLl : (isIpv6LinkLocalNoScope addr && d.boundDevIf == 0) = true
      · simp only [hLl, Bool.or_false, ↓reduceIte] at h ⊢
        exact emitErr_none_sound h
      · simp only [hLl, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact stepTcpConnectNewCore_none_sound h
    · rename_i sc
      by_cases hLl : ((isIpv6LinkLocalNoScope addr && d.boundDevIf == 0) || (d.boundDevIf != 0 && d.boundDevIf != sc)) = true
      · simp only [hLl, ↓reduceIte] at h ⊢
        exact emitErr_none_sound h
      · simp only [hLl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact stepTcpConnectNewCore_none_sound h

private theorem stepConnectConnected_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {addr : SockAddr} {out : NetOutcome} {s' : NetState}
    (h : stepConnectConnected s selfFid d addr none = some (out, s')) :
    stepConnectConnected s selfFid d addr (some out) = some (out, s') := by
  unfold stepConnectConnected at h ⊢
  cases hsp : d.tcpSelfSynPending with
  | false =>
    rw [hsp] at h
    dsimp only at h ⊢
    exact emitErr_none_sound h
  | true =>
    rw [hsp] at h
    dsimp only at h ⊢
    rcases h with ⟨rfl, rfl⟩
    simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte]

private theorem stepConnectConnectingReady_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {fam : InetFamily} {bind : InetBind} {cf : Bool} {tcpState : TcpState} {tainted : Bool}
    {out : NetOutcome} {s' : NetState}
    (h : stepConnectConnectingReady s selfFid d fam bind cf tcpState tainted none = some (out, s')) :
    stepConnectConnectingReady s selfFid d fam bind cf tcpState tainted (some out) = some (out, s') := by
  unfold stepConnectConnectingReady at h ⊢
  dsimp only at h ⊢
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem stepConnectConnecting_none_sound {s : NetState} {selfFid : FileId} {d : SockDesc}
    {fam : InetFamily} {bind : InetBind} {cf : Bool} {tcpState : TcpState} {tainted : Bool}
    {out : NetOutcome} {s' : NetState}
    (h : stepConnectConnecting s selfFid d fam bind cf tcpState tainted none = some (out, s')) :
    stepConnectConnecting s selfFid d fam bind cf tcpState tainted (some out) = some (out, s') := by
  unfold stepConnectConnecting at h ⊢
  cases hso : consumePendingSoError d with
  | some p =>
    rw [hso] at h
    dsimp only at h ⊢
    rcases h with ⟨rfl, rfl⟩
    simp only [isAsyncConnectErrno, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  | none =>
    rw [hso] at h
    dsimp only at h ⊢
    cases tcpState with
    | established _ _ | finWait _ _ | closeWait _ _ _ =>
      dsimp only at h ⊢
      exact stepConnectConnectingReady_none_sound h
    | closedAfterConn _ _ =>
      dsimp only at h ⊢
      exact emitErr_none_sound h
    | synSent _ | idle | listen _ _ =>
      dsimp only at h ⊢
      exact emitErr_none_sound h

private theorem stepConnect_none_sound {s : NetState} {hid : HandleId} {addr : SockAddr}
    {out : NetOutcome} {s' : NetState}
    (h : stepConnect s hid addr none = some (out, s')) :
    stepConnect s hid addr (some out) = some (out, s') := by
  unfold stepConnect withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hp : d.proto with
      | unixDgram bp? oldPeer? =>
        simp only [hp] at h ⊢
        exact stepUnixDgramConnect_none_sound h
      | udp fam bind _ =>
        simp only [hp] at h ⊢
        exact stepUdpConnect_none_sound h
      | unixStream isSeq bp? conn =>
        simp only [hp] at h ⊢
        exact stepUnixStreamConnect_none_sound h
      | tcp fam bind sockState tcpState tainted =>
        simp only [hp] at h ⊢
        cases sockState with
        | connected => exact stepConnectConnected_none_sound h
        | disconnecting => exact emitErr_none_sound h
        | connecting cf => exact stepConnectConnecting_none_sound h
        | unconnected =>
          cases tcpState with
          | listen _ _ => exact emitErr_none_sound h
          | _ => exact stepTcpConnectNew_none_sound h

private theorem stepGetsockopt_none_sound {s : NetState} {hid : HandleId} {opt : SockOpt}
    {out : NetOutcome} {s' : NetState}
    (h : stepGetsockopt s hid opt none = some (out, s')) :
    stepGetsockopt s hid opt (some out) = some (out, s') := by
  unfold stepGetsockopt withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases opt with
      | reuseAddr => exact emitU32_none_sound h
      | error =>
        dsimp only at h ⊢
        cases hso : consumePendingSoError d with
        | some p =>
          simp only [hso] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          simp [isAsyncConnectErrno]
        | none =>
          simp only [hso] at h ⊢
          cases hp : d.proto with
          | unixStream isSeq bp conn =>
            simp only [hp] at h ⊢
            cases conn with
            | connected pf? psw pwb pwb2 prGc =>
              cases pwb2 with
              | true =>
                dsimp only at h ⊢
                rcases h with ⟨rfl, rfl⟩
                simp
              | false =>
                dsimp only at h ⊢
                rcases h with ⟨rfl, rfl⟩
                simp
            | _ =>
              dsimp only at h ⊢
              rcases h with ⟨rfl, rfl⟩
              simp
          | tcp fam bind ss ts taint =>
            simp only [hp] at h ⊢
            cases ts with
            | closedAfterConn pa reason =>
              cases reason with
              | selfShutRstPossible =>
                dsimp only at h ⊢
                rcases h with ⟨rfl, rfl⟩
                simp
              | _ =>
                dsimp only at h ⊢
                cases ss <;> (rcases h with ⟨rfl, rfl⟩; simp)
            | _ =>
              dsimp only at h ⊢
              cases ss <;> (rcases h with ⟨rfl, rfl⟩; simp)
          | _ =>
            simp only [hp] at h ⊢
            rcases h with ⟨rfl, rfl⟩
            simp

private theorem stepSetsockopt_none_sound {s : NetState} {hid : HandleId} {opt : SetSockOpt} {val : UInt32}
    {out : NetOutcome} {s' : NetState}
    (h : stepSetsockopt s hid opt val none = some (out, s')) :
    stepSetsockopt s hid opt val (some out) = some (out, s') := by
  unfold stepSetsockopt withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      exact emitUnit_none_sound h

private theorem stepGetsockname_none_sound {s : NetState} {hid : HandleId}
    {out : NetOutcome} {s' : NetState}
    (h : stepGetsockname s hid none = some (out, s')) :
    stepGetsockname s hid (some out) = some (out, s') := by
  unfold stepGetsockname withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hla : d.localAddr? with
      | none => simp only [hla] at h ⊢; exact emitAddr_none_sound h
      | some curSa => simp only [hla] at h ⊢; exact emitAddr_none_sound h

private theorem stepShutdown_none_sound {s : NetState} {hid : HandleId} {how : ShutHow}
    {out : NetOutcome} {s' : NetState}
    (h : stepShutdown s hid how none = some (out, s')) :
    stepShutdown s hid how (some out) = some (out, s') := by
  unfold stepShutdown withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hp : d.proto with
      | tcp fam bind sockState tcpState tainted =>
        simp only [hp] at h ⊢
        cases tcpState with
        | listen _ aq =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitUnit_none_sound h
          · exact emitUnit_none_sound h
        | idle | closedAfterConn _ _ => exact emitErr_none_sound h
        | synSent target => exact emitUnit_none_sound h
        | established pf? pa =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitUnit_none_sound h
          · (split at h <;> split <;> try contradiction)
            · exact emitUnit_none_sound h
            · exact emitUnit_none_sound h
        | finWait pf? pa => exact emitUnit_none_sound h
        | closeWait pf? pa pcc =>
          dsimp only at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitUnit_none_sound h
          · exact emitUnit_none_sound h
      | udp _ _ _ | unixDgram _ _ =>
        simp only [hp] at h ⊢
        (split at h <;> split <;> try contradiction)
        · (split at h <;> split <;> try contradiction)
          · exact emitUnit_none_sound h
          · exact emitErr_none_sound h
        · exact emitUnit_none_sound h
      | unixStream isSeq bp conn =>
        simp only [hp] at h ⊢
        cases conn with
        | listen bl aq => exact emitUnit_none_sound h
        | idle => exact emitUnit_none_sound h
        | connected _ _ _ _ _ => exact emitUnit_none_sound h

private theorem stepRecvfrom_body_none_sound (s : NetState) (selfFid : FileId) (d : SockDesc)
    (maxBytes : UInt32) (flags : MsgFlags) (out : NetOutcome) (s' : NetState)
    (h : stepRecvfromBody s selfFid d maxBytes flags none = some (out, s')) :
    stepRecvfromBody s selfFid d maxBytes flags (some out) = some (out, s') := by
  unfold stepRecvfromBody at h ⊢
  dsimp only at h ⊢
  by_cases hdg : (d.sockType == .dgram) = true
  · simp only [hdg, ↓reduceIte] at h ⊢
    cases hq : d.rxQueue with
    | cons u restQ =>
      simp only [hq] at h ⊢
      exact emitBytes_none_sound h
    | nil =>
      simp only [hq] at h ⊢
      (split at h <;> split <;> try contradiction)
      · exact emitBytes_none_sound h
      · exact emitErr_none_sound h
  · simp only [hdg, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hest : (!isEstablished d && d.rxQueue.isEmpty) = true
    · simp only [hest, ↓reduceIte] at h ⊢
      (split at h <;> split <;> try contradiction)
      · exact emitBytes_none_sound h
      · exact emitErr_none_sound h
    · simp only [hest, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hstr : (d.sockType == .stream) = true
      · simp only [hstr, ↓reduceIte] at h ⊢
        rcases hcr : collectStreamRead (if clampMaxReadU32 maxBytes == 0 then 1 else clampMaxReadU32 maxBytes) d.rxQueue with ⟨availBytes, dummyMask⟩
        simp only [hcr] at h ⊢
        by_cases hav : availBytes.size > 0
        · simp only [hav, ↓reduceIte] at h ⊢
          by_cases hcap : (clampMaxReadU32 maxBytes == 0) = true
          · simp only [hcap, ↓reduceIte] at h ⊢
            exact emitBytes_none_sound h
          · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rcases h with ⟨rfl, rfl⟩
            dsimp only
            have hspm : streamBytesMatches availBytes availBytes dummyMask = true :=
              streamBytesMatches_refl availBytes dummyMask
            have hcond : (availBytes.size >= 1 && availBytes.size <= availBytes.size &&
                streamBytesMatches availBytes availBytes dummyMask) = true := by
              simp [hspm]; omega
            simp only [hcond, ↓reduceIte]
        · simp only [hav, ↓reduceIte] at h ⊢
          cases hpr : d.proto with
          | unixStream isSeq bp conn =>
            simp only [hpr] at h ⊢
            cases conn with
            | connected pf? psw pwb pwb2 prGc =>
              cases pwb2 with
              | true =>
                simp only at h ⊢
                rcases h with ⟨rfl, rfl⟩
                simp
              | false =>
                simp only at h ⊢
                (split at h <;> split <;> try contradiction)
                · exact emitBytes_none_sound h
                · exact emitErr_none_sound h
            | _ =>
              simp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitBytes_none_sound h
              · exact emitErr_none_sound h
          | _ =>
            simp only [hpr] at h ⊢
            (split at h <;> split <;> try contradiction)
            · exact emitBytes_none_sound h
            · exact emitErr_none_sound h
      · simp only [hstr, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hrst : clearUnixSeqPeerReset? d with
        | some rp =>
          simp only [hrst] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          simp
        | none =>
          simp only [hrst] at h ⊢
          cases hq : d.rxQueue with
          | cons u restQ =>
            simp only [hq] at h ⊢
            exact emitBytes_none_sound h
          | nil =>
            simp only [hq] at h ⊢
            cases hpr : d.proto with
            | unixStream isSeq bp conn =>
              simp only [hpr] at h ⊢
              cases conn with
              | connected pf? psw pwb pwb2 prGc =>
                cases pwb2 with
                | true =>
                  simp only at h ⊢
                  rcases h with ⟨rfl, rfl⟩
                  simp
                | false =>
                  cases psw with
                  | true =>
                    simp only at h ⊢
                    exact emitBytes_none_sound h
                  | false =>
                    simp only at h ⊢
                    (split at h <;> split <;> try contradiction)
                    · exact emitBytes_none_sound h
                    · exact emitErr_none_sound h
              | _ =>
                simp only at h ⊢
                (split at h <;> split <;> try contradiction)
                · exact emitBytes_none_sound h
                · exact emitErr_none_sound h
            | _ =>
              simp only [hpr] at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitBytes_none_sound h
              · exact emitErr_none_sound h

private theorem emitBytes_none_ne_err {s : NetState} {canon : ByteArray}
    {validate : ByteArray → Option NetState} {altErrs : List Errno} {e : Errno} {s' : NetState} :
    emitBytes none s canon validate altErrs ≠ some (.err e, s') := by
  dsimp only [emitBytes]
  cases validate canon <;> intro h <;> cases h

private theorem emitErr_none_ne_err {s : NetState} {canon e : Errno}
    {alts : List Errno} {onErr : Errno → NetState} {allowTransient : Bool} {allowUnit? : Option NetState}
    {allowU32? : Option (UInt32 → Option NetState)} {allowBytes? : Option (ByteArray → Option NetState)}
    {s' : NetState} (hne : canon ≠ e) :
    emitErr none s canon alts onErr allowTransient allowUnit? allowU32? allowBytes? ≠ some (.err e, s') := by
  dsimp only [emitErr]
  intro h
  rcases h with ⟨rfl, _⟩
  exact hne rfl

private theorem tcpConsumeShutRdwrRecvRst_isTcp {s : NetState} {selfFid : FileId} {d : SockDesc} {sRst : NetState}
    (h : tcpConsumeShutRdwrRecvRst? s selfFid d = some sRst) :
    ∃ fam bind ss ts taint, d.proto = .tcp fam bind ss ts taint := by
  unfold tcpConsumeShutRdwrRecvRst? at h
  by_cases hr : d.tcpShutRdwrRst = true
  · simp only [hr, ↓reduceIte] at h
    cases hp : d.proto <;> simp [hp] at h
    exact ⟨_, _, _, _, _, rfl⟩
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
    cases hp : d.proto <;> simp [hp] at h
    exact ⟨_, _, _, _, _, rfl⟩

private theorem stepRecvfromBody_tcp_none_ne_econnreset {s : NetState} {selfFid : FileId} {d : SockDesc}
    {maxBytes : UInt32} {flags : MsgFlags} {s' : NetState}
    (htcp : ∃ fam bind ss ts taint, d.proto = .tcp fam bind ss ts taint) :
    stepRecvfromBody s selfFid d maxBytes flags none ≠ some (.err Errno.ECONNRESET, s') := by
  rcases htcp with ⟨fam, bind, ss, ts, taint, hpr⟩
  intro h
  unfold stepRecvfromBody at h
  have hdg : (d.sockType == .dgram) = false := by rw [SockDesc.sockType, hpr]; rfl
  have hstr : (d.sockType == .stream) = true := by rw [SockDesc.sockType, hpr]; rfl
  simp only [hdg, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hest : (!isEstablished d && d.rxQueue.isEmpty) = true
  · simp only [hest, ↓reduceIte] at h
    split at h
    · exact emitBytes_none_ne_err h
    · exact emitErr_none_ne_err (by decide) h
  · simp only [hest, Bool.false_eq_true, ↓reduceIte, hstr] at h
    rcases hcr : collectStreamRead (if clampMaxReadU32 maxBytes == 0 then 1 else clampMaxReadU32 maxBytes) d.rxQueue with ⟨availBytes, dummyMask⟩
    simp only [hcr] at h
    by_cases hav : availBytes.size > 0
    · simp only [hav, ↓reduceIte] at h
      split at h
      · exact emitBytes_none_ne_err h
      · cases h
    · simp only [hav, ↓reduceIte, hpr] at h
      split at h
      · exact emitBytes_none_ne_err h
      · split at h <;> exact emitErr_none_ne_err (by decide) h

private theorem stepRecvfrom_none_sound {s : NetState} {hid : HandleId} {maxBytes : UInt32} {flags : MsgFlags}
    {out : NetOutcome} {s' : NetState}
    (h : stepRecvfrom s hid maxBytes flags none = some (out, s')) :
    stepRecvfrom s hid maxBytes flags (some out) = some (out, s') := by
  unfold stepRecvfrom withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hpend : consumeRecvPendingSoError d with
      | some p =>
        simp only [hpend] at h ⊢
        by_cases hst : (d.sockType == .stream && !d.rxQueue.isEmpty) = true
        · simp only [hst, ↓reduceIte] at h ⊢
          have hb := stepRecvfrom_body_none_sound s selfFid d maxBytes flags out s' h
          cases out with
          | err _ => simp only [hb, Option.isSome_some, Bool.and_true, ↓reduceIte]
          | _ => simp only [Bool.or_true, ↓reduceIte, hb]
        · simp only [hst, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          simp [isAsyncConnectErrno]
      | none =>
        simp only [hpend] at h ⊢
        cases out with
        | err e =>
          by_cases he : (e == Errno.ECONNRESET) = true
          · have heq : e = Errno.ECONNRESET := beq_iff_eq.mp he
            subst heq
            cases htcp : tcpConsumeShutRdwrRecvRst? s selfFid d with
            | none =>
              simp only [ite_self]
              exact stepRecvfrom_body_none_sound s selfFid d maxBytes flags (.err Errno.ECONNRESET) s' h
            | some sRst =>
              exfalso
              exact stepRecvfromBody_tcp_none_ne_econnreset (tcpConsumeShutRdwrRecvRst_isTcp htcp) h
          · simp only [he, Bool.false_eq_true, ↓reduceIte]
            exact stepRecvfrom_body_none_sound s selfFid d maxBytes flags (.err e) s' h
        | _ => exact stepRecvfrom_body_none_sound s selfFid d maxBytes flags _ s' h

private theorem stepSendto_body_none_sound (s : NetState) (selfFid : FileId) (d : SockDesc)
    (data : ByteArray) (flags : MsgFlags) (out : NetOutcome) (s' : NetState)
    (h : stepSendtoBody s selfFid d data flags none = some (out, s')) :
    stepSendtoBody s selfFid d data flags (some out) = some (out, s') := by
  unfold stepSendtoBody at h ⊢
  dsimp only at h ⊢
  by_cases h1 : (d.sockType == .dgram && !isEstablished d) = true
  · simp only [h1, ↓reduceIte] at h ⊢
    exact emitErr_none_sound h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h2 : (!isEstablished d) = true
    · simp only [h2, ↓reduceIte] at h ⊢
      exact emitErr_none_sound h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hseq : (d.domain == .unix && d.sockType == .seqpacket) = true
      · simp only [hseq, ↓reduceIte] at h ⊢
        cases hpr : d.proto with
        | unixStream isSeq bp conn =>
          simp only [hpr] at h ⊢
          cases conn with
          | connected pf? psw pwb pwb2 prGc =>
            cases pwb2 with
            | true =>
              dsimp only at h ⊢
              exact emitErr_none_sound h
            | false =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · cases pwb with
                | true => dsimp only at h ⊢; exact emitErr_none_sound h
                | false =>
                  cases pf? with
                  | none => dsimp only at h ⊢; exact emitErr_none_sound h
                  | some _ => dsimp only at h ⊢; exact emitU32_none_sound h
          | _ =>
            dsimp only at h ⊢
            (split at h <;> split <;> try contradiction)
            · exact emitErr_none_sound h
            · exact emitErr_none_sound h
        | _ =>
          simp only [hpr] at h ⊢
          (split at h <;> split <;> try contradiction)
          · exact emitErr_none_sound h
          · exact emitErr_none_sound h
      · simp only [hseq, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases h3 : d.shut.wr = true
        · simp only [h3, ↓reduceIte] at h ⊢
          exact emitErr_none_sound h
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hdisc : disconnectUnixDgramIfPeerClosed s d with
          | some dDisc =>
            simp only [hdisc] at h ⊢
            exact emitErr_none_sound h
          | none =>
            simp only [hdisc] at h ⊢
            cases hpr : d.proto with
            | unixDgram _ peer? =>
              simp only [hpr] at h ⊢
              cases peer? with
              | none => exact emitErr_none_sound h
              | some p =>
                cases hl : lookupFileSocket s p.1 with
                | error _ => simp only [hl] at h ⊢; exact emitErr_none_sound h
                | ok pd =>
                  simp only [hl] at h ⊢
                  (split at h <;> split <;> try contradiction)
                  · exact emitErr_none_sound h
                  · (split at h <;> split <;> try contradiction)
                    · exact emitErr_none_sound h
                    · exact emitU32_none_sound h
            | unixStream _ _ conn =>
              simp only [hpr] at h ⊢
              cases conn with
              | connected peer? _ pwb _ _ =>
                cases peer? with
                | none => exact emitErr_none_sound h
                | some peerFid =>
                  dsimp only at h ⊢
                  (split at h <;> split <;> try contradiction)
                  · exact emitErr_none_sound h
                  · by_cases hz : (data.size == 0) = true
                    · simp only [hz, ↓reduceIte] at h ⊢
                      exact emitU32_none_sound h
                    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
                      have hne : data.size ≠ 0 := by intro h0; simp [h0] at hz
                      have ⟨htn, hge⟩ := minU32_u32_toNat data.size hne
                      rcases h with ⟨rfl, rfl⟩
                      have hcond : (min data.size 4294967295 >= 1 &&
                          min data.size 4294967295 <= min data.size 4294967295) = true := by
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        exact ⟨hge, Nat.le_refl _⟩
                      dsimp only
                      rw [htn]
                      simp only [hcond, ↓reduceIte]
              | _ => exact emitErr_none_sound h
            | tcp _ _ _ tcpState _ =>
              simp only [hpr] at h ⊢
              cases tcpState with
              | established pf? _ | finWait pf? _ =>
                dsimp only at h ⊢
                by_cases hz : (data.size == 0) = true
                · simp only [hz, ↓reduceIte] at h ⊢
                  exact emitU32_none_sound h
                · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  have hne : data.size ≠ 0 := by intro h0; simp [h0] at hz
                  have ⟨htn, hge⟩ := minU32_u32_toNat data.size hne
                  rcases h with ⟨rfl, rfl⟩
                  have hcond : (min data.size 4294967295 >= 1 &&
                      min data.size 4294967295 <= min data.size 4294967295) = true := by
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    exact ⟨hge, Nat.le_refl _⟩
                  dsimp only
                  rw [htn]
                  simp only [hcond, ↓reduceIte]
              | closeWait pf? pa pcc =>
                cases pcc with
                | false =>
                  dsimp only at h ⊢
                  by_cases hz : (data.size == 0) = true
                  · simp only [hz, ↓reduceIte] at h ⊢
                    exact emitU32_none_sound h
                  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    have hne : data.size ≠ 0 := by intro h0; simp [h0] at hz
                    have ⟨htn, hge⟩ := minU32_u32_toNat data.size hne
                    rcases h with ⟨rfl, rfl⟩
                    have hcond : (min data.size 4294967295 >= 1 &&
                        min data.size 4294967295 <= min data.size 4294967295) = true := by
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      exact ⟨hge, Nat.le_refl _⟩
                    dsimp only
                    rw [htn]
                    simp only [hcond, ↓reduceIte]
                | true =>
                  cases pf? with
                  | some _ => exact emitErr_none_sound h
                  | none =>
                    dsimp only at h ⊢
                    by_cases hz : (data.size == 0) = true
                    · simp only [hz, ↓reduceIte] at h ⊢
                      exact emitU32_none_sound h
                    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
                      have hne : data.size ≠ 0 := by intro h0; simp [h0] at hz
                      have ⟨htn, hge⟩ := minU32_u32_toNat data.size hne
                      rcases h with ⟨rfl, rfl⟩
                      have hcond : (min data.size 4294967295 >= 1 &&
                          min data.size 4294967295 <= min data.size 4294967295) = true := by
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        exact ⟨hge, Nat.le_refl _⟩
                      dsimp only
                      rw [htn]
                      simp only [hcond, ↓reduceIte]
              | _ => exact emitErr_none_sound h
            | udp fam _ target? =>
              simp only [hpr] at h ⊢
              cases target? with
              | none => exact emitErr_none_sound h
              | some targetAddr =>
                by_cases hv4p0 : (fam == .v6 && isIpv4MappedV6Addr targetAddr && targetAddr.port? == some 0) = true
                · simp only [hv4p0, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
                · simp only [hv4p0, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases hbdi : (d.boundDevIf != 0 && d.boundDevIf != 1) = true
                  · simp only [hbdi, ↓reduceIte] at h ⊢; exact emitErr_none_sound h
                  · simp only [hbdi, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hm : ipv4AllHostsMcastPort? targetAddr with
                    | some _ => simp only [hm] at h ⊢; exact emitU32_none_sound h
                    | none =>
                      simp only [hm] at h ⊢
                      cases hf : findBoundUdpPeer s d targetAddr with
                      | some _ => simp only [hf] at h ⊢; exact emitU32_none_sound h
                      | none => simp only [hf] at h ⊢; exact emitU32_none_sound h

private theorem stepSendto_none_sound {s : NetState} {hid : HandleId} {data : ByteArray} {flags : MsgFlags}
    {out : NetOutcome} {s' : NetState}
    (h : stepSendto s hid data flags none = some (out, s')) :
    stepSendto s hid data flags (some out) = some (out, s') := by
  unfold stepSendto withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hso : consumePendingSoError d with
      | some p =>
        simp only [hso] at h ⊢
        rcases h with ⟨rfl, rfl⟩
        simp [isAsyncConnectErrno]
      | none =>
        simp only [hso] at h ⊢
        exact stepSendto_body_none_sound s selfFid d data flags out s' h

private theorem stepSendmsg_none_sound {s : NetState} {hid : HandleId} {fds : Array HandleId}
    {out : NetOutcome} {s' : NetState}
    (h : stepSendmsg s hid fds none = some (out, s')) :
    stepSendmsg s hid fds (some out) = some (out, s') := by
  unfold stepSendmsg at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    by_cases hl : fds.toList.all (isLiveHandle s) = true
    · simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hsock : lookupFileSocket s selfFid with
      | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
      | ok d =>
        simp only [hsock] at h ⊢
        by_cases hdom : (d.domain != .unix) = true
        · simp only [hdom, ↓reduceIte] at h ⊢
          exact emitErr_none_sound h
        · simp only [hdom, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hso : consumePendingSoError d with
        | some p =>
          simp only [hso] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          simp [isAsyncConnectErrno]
        | none =>
          simp only [hso] at h ⊢
          by_cases hest : (!isEstablished d) = true
          · simp only [hest, ↓reduceIte] at h ⊢
            exact emitErr_none_sound h
          · simp only [hest, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hseq : (d.domain == .unix && d.sockType == .seqpacket) = true
            · simp only [hseq, ↓reduceIte] at h ⊢
              cases hpr : d.proto with
              | unixStream isSeq bp conn =>
                simp only [hpr] at h ⊢
                cases conn with
                | connected pf? psw pwb pwb2 prGc =>
                  cases pwb2 with
                  | true =>
                    dsimp only at h ⊢
                    exact emitErr_none_sound h
                  | false =>
                    dsimp only at h ⊢
                    (split at h <;> split <;> try contradiction)
                    · exact emitErr_none_sound h
                    · cases pwb with
                      | true => dsimp only at h ⊢; exact emitErr_none_sound h
                      | false =>
                        cases pf? with
                        | none => dsimp only at h ⊢; exact emitErr_none_sound h
                        | some _ => dsimp only at h ⊢; exact emitUnit_none_sound h
                | _ =>
                  dsimp only at h ⊢
                  (split at h <;> split <;> try contradiction)
                  · exact emitErr_none_sound h
                  · exact emitErr_none_sound h
              | _ =>
                simp only [hpr] at h ⊢
                (split at h <;> split <;> try contradiction)
                · exact emitErr_none_sound h
                · exact emitErr_none_sound h
            · simp only [hseq, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hwr : d.shut.wr = true
              · simp only [hwr, ↓reduceIte] at h ⊢
                exact emitErr_none_sound h
              · simp only [hwr, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases hdisc : disconnectUnixDgramIfPeerClosed s d with
                | some dDisc =>
                  simp only [hdisc] at h ⊢
                  exact emitErr_none_sound h
                | none =>
                  simp only [hdisc] at h ⊢
                  cases hpr : d.proto with
                  | unixDgram _ peer? =>
                    simp only [hpr] at h ⊢
                    cases peer? with
                    | none => exact emitErr_none_sound h
                    | some p =>
                      cases hlkp : lookupFileSocket s p.1 with
                      | error _ => simp only [hlkp] at h ⊢; exact emitErr_none_sound h
                      | ok _ =>
                        simp only [hlkp] at h ⊢
                        (split at h <;> split <;> try contradiction)
                        · exact emitErr_none_sound h
                        · (split at h <;> split <;> try contradiction)
                          · exact emitErr_none_sound h
                          · exact emitUnit_none_sound h
                  | unixStream _ _ conn =>
                    simp only [hpr] at h ⊢
                    cases conn with
                    | connected peer? _ pwb _ _ =>
                      cases peer? with
                      | none => exact emitErr_none_sound h
                      | some _ =>
                        dsimp only at h ⊢
                        (split at h <;> split <;> try contradiction)
                        · exact emitErr_none_sound h
                        · exact emitUnit_none_sound h
                    | _ => exact emitErr_none_sound h
                  | udp _ _ target? =>
                    simp only [hpr] at h ⊢
                    cases target? with
                    | none => exact emitErr_none_sound h
                    | some targetAddr =>
                      cases hbp : findBoundUdpPeer s d targetAddr with
                      | some _ => simp only [hbp] at h ⊢; exact emitUnit_none_sound h
                      | none => simp only [hbp] at h ⊢; exact emitUnit_none_sound h
                  | tcp _ _ _ tcpState _ =>
                    simp only [hpr] at h ⊢
                    cases tcpState with
                    | established _ _ | finWait _ _ =>
                      dsimp only at h ⊢
                      rcases h with ⟨rfl, rfl⟩
                      rfl
                    | closeWait pf? pa pcc =>
                      cases pcc with
                      | false =>
                        cases pf? <;> dsimp only at h ⊢ <;> rcases h with ⟨rfl, rfl⟩ <;> rfl
                      | true =>
                        cases pf? with
                        | some _ => exact emitErr_none_sound h
                        | none =>
                          dsimp only at h ⊢
                          rcases h with ⟨rfl, rfl⟩
                          rfl
                    | _ => exact emitErr_none_sound h
    · simp only [hl, Bool.not_false, ↓reduceIte] at h ⊢
      exact emitErr_none_sound h

private theorem releaseUnusedFiles_nil (s : NetState) : releaseUnusedFiles s [] = s := rfl

private theorem stepRecvmsg_body_none_sound (s : NetState) (selfFid : FileId) (d : SockDesc)
    (maxFds : UInt32) (out : NetOutcome) (s' : NetState)
    (h : stepRecvmsgBody s selfFid d maxFds none = some (out, s')) :
    stepRecvmsgBody s selfFid d maxFds (some out) = some (out, s') := by
  unfold stepRecvmsgBody at h ⊢
  dsimp only at h ⊢
  by_cases h1 : (d.sockType != .dgram && !isEstablished d && d.rxQueue.isEmpty) = true
  · simp only [h1, ↓reduceIte] at h ⊢
    (split at h <;> split <;> try contradiction)
    · rcases h with ⟨rfl, rfl⟩
      simp
    · exact emitErr_none_sound h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hrst : clearUnixSeqPeerReset? d with
    | some rp =>
      simp only [hrst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simp
    | none =>
      simp only [hrst] at h ⊢
      cases hpop : popRecvmsgUnit d.sockType d.rxQueue with
      | some p =>
        rcases p with ⟨batch, restQ⟩
        simp only [hpop] at h ⊢
        by_cases hgt : batch.length > maxFds.toNat
        · simp only [hgt, ↓reduceIte] at h ⊢
          exact emitErr_none_sound h
        · simp only [hgt, ↓reduceIte] at h ⊢
          let s1 := setFileSocket s selfFid { d with rxQueue := restQ }
          have hf : ∀ j, freshHidBase s1 ≤ j → isFreshHid s1 j = true := by
            intro j hj
            have hEq : j = freshHidBase s1 + (j - freshHidBase s1) := (Nat.add_sub_cancel' hj).symm
            rw [hEq]
            exact isFreshHid_freshHidBase_add s1 (j - freshHidBase s1)
          have hcb := cloneScmHandles_bind batch.length (freshHidBase s1) batch s1 [] hf
          rcases hcl : cloneScmHandles s1 batch.length (freshHidBase s1) batch [] with ⟨sClone, got⟩
          dsimp only [s1] at hcl hcb
          simp only [hcl] at hcb h ⊢
          rcases hcb with ⟨newTail, hgot, hlen, hbind⟩
          have hgl : got.toList = newTail := by simpa using hgot
          have hsz : got.size = newTail.length := by rw [← Array.length_toList, hgl]
          have hne : newTail.length = batch.length := by rw [hlen]; simp
          have htake : batch.take newTail.length = batch := List.take_of_length_le (by omega)
          have hdrop : batch.drop batch.length = [] := List.drop_of_length_le (Nat.le_refl _)
          rw [htake] at hbind
          rcases h with ⟨rfl, rfl⟩
          simp only [hgl, hsz, hne, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hbind]
          rw [hdrop, releaseUnusedFiles_nil]
      | none =>
        simp only [hpop] at h ⊢
        cases hpr : d.proto with
        | unixStream isSeq bp conn =>
          simp only [hpr] at h ⊢
          cases conn with
          | connected pf? psw pwb pwb2 prGc =>
            cases pwb2 with
            | true =>
              simp only at h ⊢
              rcases h with ⟨rfl, rfl⟩
              simp
            | false =>
              simp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · rcases h with ⟨rfl, rfl⟩
                simp
              · exact emitErr_none_sound h
          | _ =>
            simp only at h ⊢
            (split at h <;> split <;> try contradiction)
            · rcases h with ⟨rfl, rfl⟩
              simp
            · exact emitErr_none_sound h
        | _ =>
          simp only [hpr] at h ⊢
          (split at h <;> split <;> try contradiction)
          · rcases h with ⟨rfl, rfl⟩
            simp
          · exact emitErr_none_sound h

private theorem stepRecvmsgBody_tcp_none_ne_econnreset {s : NetState} {selfFid : FileId} {d : SockDesc}
    {maxFds : UInt32} {s' : NetState}
    (htcp : ∃ fam bind ss ts taint, d.proto = .tcp fam bind ss ts taint) :
    stepRecvmsgBody s selfFid d maxFds none ≠ some (.err Errno.ECONNRESET, s') := by
  rcases htcp with ⟨fam, bind, ss, ts, taint, hpr⟩
  intro h
  unfold stepRecvmsgBody at h
  by_cases h1 : (d.sockType != .dgram && !isEstablished d && d.rxQueue.isEmpty) = true
  · simp only [h1, ↓reduceIte] at h
    split at h
    · cases h
    · exact emitErr_none_ne_err (by decide) h
  · have hclr : clearUnixSeqPeerReset? d = none := by simp [clearUnixSeqPeerReset?, hpr]
    simp only [h1, Bool.false_eq_true, ↓reduceIte, hclr] at h
    cases hpop : popRecvmsgUnit d.sockType d.rxQueue with
    | some p =>
      rcases p with ⟨batch, restQ⟩
      simp only [hpop] at h
      split at h
      · exact emitErr_none_ne_err (by decide) h
      · rcases hcl : cloneScmHandles (setFileSocket s selfFid { d with rxQueue := restQ }) batch.length
          (freshHidBase (setFileSocket s selfFid { d with rxQueue := restQ })) batch [] with ⟨sClone, got⟩
        simp only [hcl] at h
        cases h
    | none =>
      simp only [hpop, hpr] at h
      split at h
      · cases h
      · exact emitErr_none_ne_err (by decide) h

private theorem stepRecvmsg_none_sound {s : NetState} {hid : HandleId} {maxFds : UInt32}
    {out : NetOutcome} {s' : NetState}
    (h : stepRecvmsg s hid maxFds none = some (out, s')) :
    stepRecvmsg s hid maxFds (some out) = some (out, s') := by
  unfold stepRecvmsg withSock at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error _ => simp only [hsock] at h ⊢; exact emitErr_none_sound h
    | ok d =>
      simp only [hsock] at h ⊢
      cases hpend : consumeRecvPendingSoError d with
      | some p =>
        simp only [hpend] at h ⊢
        by_cases hst : (d.sockType == .stream && !d.rxQueue.isEmpty) = true
        · simp only [hst, ↓reduceIte] at h ⊢
          have hb := stepRecvmsg_body_none_sound s selfFid d maxFds out s' h
          cases out with
          | err _ => simp only [hb, Option.isSome_some, Bool.and_true, ↓reduceIte]
          | _ => simp only [Bool.or_true, ↓reduceIte, hb]
        · simp only [hst, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          simp [isAsyncConnectErrno]
      | none =>
        simp only [hpend] at h ⊢
        cases out with
        | err e =>
          by_cases he : (e == Errno.ECONNRESET) = true
          · have heq : e = Errno.ECONNRESET := beq_iff_eq.mp he
            subst heq
            cases htcp : tcpConsumeShutRdwrRecvRst? s selfFid d with
            | none =>
              simp only [ite_self]
              exact stepRecvmsg_body_none_sound s selfFid d maxFds (.err Errno.ECONNRESET) s' h
            | some sRst =>
              exfalso
              exact stepRecvmsgBody_tcp_none_ne_econnreset (tcpConsumeShutRdwrRecvRst_isTcp htcp) h
          · simp only [he, Bool.false_eq_true, ↓reduceIte]
            exact stepRecvmsg_body_none_sound s selfFid d maxFds (.err e) s' h
        | _ => exact stepRecvmsg_body_none_sound s selfFid d maxFds _ s' h

private theorem stepIoctl_none_sound {s : NetState} {hid : HandleId} {op : NetIoctlOp} {ifname : ByteArray}
    {out : NetOutcome} {s' : NetState}
    (h : stepIoctl s hid op ifname none = some (out, s')) :
    stepIoctl s hid op ifname (some out) = some (out, s') := by
  unfold stepIoctl at h ⊢
  cases hfid : lookupHandleFileId s hid with
  | none => simp only [hfid] at h ⊢; exact emitErr_none_sound h
  | some selfFid =>
    simp only [hfid] at h ⊢
    cases hsock : lookupFileSocket s selfFid with
    | error fdErr =>
      simp only [hsock] at h ⊢
      (split at h <;> split <;> try contradiction)
      · exact emitErr_none_sound h
      · exact emitErr_none_sound h
    | ok _ =>
      simp only [hsock] at h ⊢
      by_cases h0 : (ifname.size == 0) = true
      · simp only [h0, ↓reduceIte] at h ⊢
        cases op <;> exact emitErr_none_sound h
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hlo : bytesEq ifname loIfname = true
        · simp only [hlo, ↓reduceIte] at h ⊢
          cases hst : s.loState with
          | up fl =>
            simp only [hst] at h ⊢
            cases op with
            | getIfFlags => exact emitU32_none_sound h
            | setIfFlags rawFl =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitU32_none_sound h
          | down fl wasUp =>
            simp only [hst] at h ⊢
            cases op with
            | getIfFlags => exact emitU32_none_sound h
            | setIfFlags rawFl =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitU32_none_sound h
          | unpinned defFl =>
            simp only [hst] at h ⊢
            cases op with
            | getIfFlags =>
              dsimp only at h ⊢
              split at h
              · rename_i hc
                rcases h with ⟨rfl, rfl⟩
                simp [hc]
              · cases h
            | setIfFlags rawFl =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitU32_none_sound h
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hba : bytesAssocGet s.otherIfaces ifname with
          | none =>
            simp only [hba] at h ⊢
            cases op with
            | getIfFlags =>
              dsimp only at h ⊢
              rcases h with ⟨rfl, rfl⟩
              simp
            | setIfFlags rawFl =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · rcases h with ⟨rfl, rfl⟩
                simp
          | some curFl =>
            simp only [hba] at h ⊢
            cases op with
            | getIfFlags => exact emitU32_none_sound h
            | setIfFlags rawFl =>
              dsimp only at h ⊢
              (split at h <;> split <;> try contradiction)
              · exact emitErr_none_sound h
              · exact emitU32_none_sound h

/-- Soundness of the deterministic `modelOps` transition relation: every step produced by `stepNetCore s req none` is accepted by `allowedStep s req out`. -/
theorem stepNetCore_none_sound (s : NetState) (req : NetReq) (out : NetOutcome) (s' : NetState)
    (h : stepNetCore s req none = some (out, s')) :
    allowedStep s req out = some s' := by
  have hSome : stepNetCore s req (some out) = some (out, s') := by
    unfold stepNetCore at h ⊢
    cases hp : preCheckNet req with
    | some err =>
      simp only [hp] at h ⊢
      exact emitErr_none_sound h
    | none =>
      simp only [hp] at h ⊢
      cases req with
      | socket => exact emitAllocFd_none_sound h
      | socketpair => exact emitAllocPair_none_sound h
      | bind => exact stepBind_none_sound h
      | listen => exact stepListen_none_sound h
      | accept4 => exact stepAccept4_none_sound h
      | connect => exact stepConnect_none_sound h
      | getsockopt => exact stepGetsockopt_none_sound h
      | setsockopt => exact stepSetsockopt_none_sound h
      | getsockname => exact stepGetsockname_none_sound h
      | recvfrom => exact stepRecvfrom_none_sound h
      | sendto => exact stepSendto_none_sound h
      | shutdown => exact stepShutdown_none_sound h
      | sendmsg => exact stepSendmsg_none_sound h
      | recvmsg => exact stepRecvmsg_none_sound h
      | ioctl => exact stepIoctl_none_sound h
  simp only [allowedStep, hSome, Option.map_some]

/-- `allowedStep` permits safe seccomp errnos under `ambientSeccomp = true` iff `reachesKernelSyscall` holds. -/
theorem net_model_ambientSeccomp_allPass :
    AllPass (test_net_model_ambientSeccomp allowedStep) := by
  dsimp only [AllPass, test_net_model_ambientSeccomp, Bind.bind, assert, pure]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, trivial⟩

/-- Witness showing `test_net_model_ambientSeccomp` reaches its terminal state on `allowedStep`. -/
theorem net_model_ambientSeccomp_canReach :
    CanReach (test_net_model_ambientSeccomp allowedStep) :=
  net_model_ambientSeccomp_allPass

/-- `allowedStep` satisfies kernel socket invariants for multicast/broadcast bind, dual-stack conflict, pre-listen `SHUT_RD`, listener shutdown, 4-way FIN close, and `AF_UNIX` bind FS errors. -/
theorem net_model_bindDualStackShutdownAndFinInvariants_allPass :
    AllPass (test_net_model_bindDualStackShutdownAndFinInvariants allowedStep) := by
  dsimp only [AllPass, test_net_model_bindDualStackShutdownAndFinInvariants, Bind.bind, assert, pure]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Witness showing `test_net_model_bindDualStackShutdownAndFinInvariants` reaches its terminal state on `allowedStep`. -/
theorem net_model_bindDualStackShutdownAndFinInvariants_canReach :
    CanReach (test_net_model_bindDualStackShutdownAndFinInvariants allowedStep) :=
  net_model_bindDualStackShutdownAndFinInvariants_allPass

/-- Every deterministic `stepNetCore s req none` step passes `allowedStep`. -/
theorem net_model_stepCoreSound_allPass :
    AllPass (test_net_model_stepCoreSound allowedStep) := by
  intro s req out s' h
  exact ⟨stepNetCore_none_sound s req out s' h, trivial⟩

/-- Concrete witness showing `test_net_model_stepCoreSound` is reachable on `allowedStep`. -/
theorem net_model_stepCoreSound_canReach :
    CanReach (test_net_model_stepCoreSound allowedStep) := by
  let s0 := NetState.initial false
  let req : NetReq := .socket .inet .stream {} 0
  have hs : ∃ out s', stepNetCore s0 req none = some (out, s') :=
    ⟨.opened 0, _, rfl⟩
  rcases hs with ⟨out, s', hstep⟩
  exact ⟨s0, req, out, s', hstep, net_model_stepCoreSound_allPass s0 req out s' hstep⟩

end LeanSwe.LinuxSyscall.Net

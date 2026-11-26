import Core.Assumptions
import LeanSwe.LinuxSyscall.Dns.Proofs.WireAndLiteralHelpers

namespace LeanSwe.LinuxSyscall.Dns.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

private theorem decodeRecordsList_sound_aux :
    ∀ (xs : List UInt8) (addrs : List DnsAddr),
      decodeRecordsList xs = .ok addrs →
      addrs.flatMap wireAddrBytes = xs
  | [], addrs, h => by
    simp [decodeRecordsList] at h
    subst h
    rfl
  | [_], _, h | [_, _], _, h | [_, _, _], _, h | [_, _, _, _], _, h | [_, _, _, _, _], _, h
  | [_, _, _, _, _, _], _, h | [_, _, _, _, _, _, _], _, h | [_, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _], _, h | [_, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _], _, h | [_, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, h | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, h => by
    simp [decodeRecordsList] at h
  | tag :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: s0 :: s1 :: s2 :: s3 :: rest, addrs, h => by
    unfold decodeRecordsList at h
    by_cases h4 : tag = DNS_FAMILY_V4
    · have ht4 : (tag == DNS_FAMILY_V4) = true := beq_iff_eq.mpr h4
      simp only [ht4, ↓reduceIte] at h
      split at h
      · next hpad =>
        split at h
        · next tail htail =>
          injection h with hEq
          subst hEq
          have hrest := decodeRecordsList_sound_aux rest tail htail
          simp only [Bool.and_eq_true, beq_iff_eq] at hpad
          rcases hpad with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb4, hb5⟩, hb6⟩, hb7⟩, hb8⟩, hb9⟩, hb10⟩, hb11⟩, hb12⟩, hb13⟩, hb14⟩, hb15⟩, hs0⟩, hs1⟩, hs2⟩, hs3⟩
          subst h4 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hs0 hs1 hs2 hs3
          simp [List.flatMap_cons, wireAddrBytes, DNS_FAMILY_V4, hrest]
        · contradiction
      · contradiction
    · have ht4 : (tag == DNS_FAMILY_V4) = false := beq_false_of_ne h4
      simp only [ht4, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h6 : tag = DNS_FAMILY_V6
      · have ht6 : (tag == DNS_FAMILY_V6) = true := beq_iff_eq.mpr h6
        simp only [ht6, ↓reduceIte] at h
        split at h
        · next tail htail =>
          injection h with hEq
          subst hEq
          have hrest := decodeRecordsList_sound_aux rest tail htail
          subst h6
          have hDec := encodeUInt32LEList_decodeUInt32LE s0 s1 s2 s3
          simp only [encodeUInt32LEList] at hDec
          simp only [List.flatMap_cons, wireAddrBytes, DNS_FAMILY_V6, List.cons_append, List.nil_append]
          have htail' := congrArg
            (fun l => (6 : UInt8) :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: l)
            (congrArg (· ++ rest) hDec)
          simpa [List.cons_append, List.append_assoc, hrest] using htail'
        · contradiction
      · have ht6 : (tag == DNS_FAMILY_V6) = false := beq_false_of_ne h6
        simp only [ht6, Bool.false_eq_true, ↓reduceIte] at h
        contradiction

/-- `decodeRecords` is right-inverse to `encodeRecords` on all accepted `ByteArray` payloads. -/
theorem decodeRecords_roundTrip_bytes (bs : ByteArray) (addrs : List DnsAddr)
    (h : decodeRecords bs = .ok addrs) :
    encodeRecords addrs = bs := by
  rw [decodeRecords_eq_list] at h
  have hxs := decodeRecordsList_sound_aux bs.data.toList addrs h
  apply ByteArray.ext
  apply Array.ext'
  rw [encodeWireRecords_data_toList, hxs]

private theorem decodeRecordsList_error_invariants :
    ∀ (xs : List UInt8) (err : DnsError),
      decodeRecordsList xs = .error err →
      err.kind = .otherGai ∧ err.gaiCode = EAI_OVERFLOW ∧ err.errno? = none ∧ !err.message.isEmpty = true
  | [], err, h => by simp [decodeRecordsList] at h
  | [_], err, h | [_, _], err, h | [_, _, _], err, h | [_, _, _, _], err, h
  | [_, _, _, _, _], err, h | [_, _, _, _, _, _], err, h | [_, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _], err, h | [_, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _], err, h | [_, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _], err, h | [_, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], err, h => by
    simp [decodeRecordsList] at h
    cases h
    refine ⟨rfl, rfl, rfl, by decide⟩
  | tag :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest, err, h => by
    unfold decodeRecordsList at h
    split at h
    · split at h
      · split at h
        · contradiction
        · next e he =>
          injection h with hEq
          subst hEq
          exact decodeRecordsList_error_invariants rest e he
      · cases h
        refine ⟨rfl, rfl, rfl, by decide⟩
    · split at h
      · split at h
        · contradiction
        · next e he =>
          injection h with hEq
          subst hEq
          exact decodeRecordsList_error_invariants rest e he
      · cases h
        refine ⟨rfl, rfl, rfl, ?_⟩
        simp [String.isEmpty]

/-- Every malformed-record `decodeRecords` failure satisfies `.otherGai` / `EAI_OVERFLOW` / `errno? = none` / non-empty `message`. -/
theorem decodeRecords_error_invariants (bs : ByteArray) (err : DnsError)
    (h : decodeRecords bs = .error err) :
    err.kind = .otherGai ∧ err.gaiCode = EAI_OVERFLOW ∧ err.errno? = none ∧ !err.message.isEmpty = true := by
  rw [decodeRecords_eq_list] at h
  exact decodeRecordsList_error_invariants bs.data.toList err h

private theorem decodeErrorMessage_nonEmpty (msg : ByteArray) :
    !(decodeErrorMessage msg).isEmpty = true := by
  unfold decodeErrorMessage
  cases String.fromUTF8? msg with
  | none =>
    simp [String.isEmpty]
  | some s =>
    by_cases hs : s = ""
    · simp [hs, String.isEmpty]
    · simp [String.isEmpty, hs]

theorem classifyGaiKind_ne_invalidHost (rc : Int32) :
    classifyGaiKind rc ≠ .invalidHost := by
  unfold classifyGaiKind
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem normalizeGaiCodeForHost_invariants (host : String) (hints : ResolveHints) (rc : Int32) :
    isValidGaiCode (normalizeGaiCodeForHost host hints rc) = true ∧
    (if normalizeGaiCodeForHost host hints rc == EAI_ADDRFAMILY then isNumericFamilyMismatch host hints else true) = true ∧
    (if isNumericFamilyMismatch host hints then
      normalizeGaiCodeForHost host hints rc != EAI_NONAME &&
      normalizeGaiCodeForHost host hints rc != EAI_NODATA
    else true) = true := by
  unfold normalizeGaiCodeForHost
  dsimp only
  let code0 := if isValidGaiCode rc then rc else EAI_FAIL
  change isValidGaiCode (if isNumericFamilyMismatch host hints then if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0 else if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0) = true ∧
    (if (if isNumericFamilyMismatch host hints then if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0 else if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0) == EAI_ADDRFAMILY then isNumericFamilyMismatch host hints else true) = true ∧
    (if isNumericFamilyMismatch host hints then
      (if isNumericFamilyMismatch host hints then if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0 else if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0) != EAI_NONAME &&
      (if isNumericFamilyMismatch host hints then if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0 else if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0) != EAI_NODATA
    else true) = true
  have hcode0 : isValidGaiCode code0 = true := by
    by_cases hok : isValidGaiCode rc = true
    · simp [code0, hok]
    · simp [code0, hok]; decide
  by_cases hMis : isNumericFamilyMismatch host hints = true
  · simp only [hMis, ↓reduceIte]
    by_cases hNo : (code0 == EAI_NONAME || code0 == EAI_NODATA) = true
    · simp only [hNo, ↓reduceIte]
      refine ⟨by decide, ?_, by decide⟩
      simp [EAI_ADDRFAMILY]
    · have hNoF : (code0 == EAI_NONAME || code0 == EAI_NODATA) = false :=
        Bool.eq_false_iff.mpr hNo
      have hne1 : code0 ≠ EAI_NONAME := by
        intro hEq
        have : (code0 == EAI_NONAME || code0 == EAI_NODATA) = true := by simp [hEq]
        rw [hNoF] at this; contradiction
      have hne2 : code0 ≠ EAI_NODATA := by
        intro hEq
        have : (code0 == EAI_NONAME || code0 == EAI_NODATA) = true := by simp [hEq]
        rw [hNoF] at this; contradiction
      refine ⟨?_, ?_, ?_⟩
      · simpa [hNoF] using hcode0
      · simp only [hNoF, Bool.false_eq_true, ↓reduceIte]
        cases hAF : (code0 == EAI_ADDRFAMILY) <;> simp
      · simp only [hNoF, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨hne1, hne2⟩
  · have hMisF : isNumericFamilyMismatch host hints = false := Bool.eq_false_iff.mpr hMis
    simp only [hMisF, Bool.false_eq_true, ↓reduceIte]
    by_cases hAF : (code0 == EAI_ADDRFAMILY) = true
    · simp only [hAF, ↓reduceIte]
      refine ⟨by decide, ?_, trivial⟩
      have hne : (EAI_NONAME == EAI_ADDRFAMILY) = false := by decide
      simp [hne]
    · have hAFF : (code0 == EAI_ADDRFAMILY) = false := Bool.eq_false_iff.mpr hAF
      simp only [hAFF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hcode0, by simp, trivial⟩

theorem dnsErrorKind_beq_refl (k : DnsErrorKind) : (k == k) = true := by
  cases k <;> decide

/-- Soundness of `(mkDnsOpsM (m := Id) raw).getaddrinfo host hints` when `raw` returns an arbitrary `(rc, eno, msgBytes)` error. -/
theorem mkDnsOpsM_id_error_sound (host : String) (hints : ResolveHints)
    (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) :
    allowedDnsOutcome host hints
      ((mkDnsOpsM (m := Id) { getaddrinfo := fun _ _ _ => .error (rc, eno, msgBytes) }).getaddrinfo host hints) = true := by
  unfold mkDnsOpsM
  dsimp only [Bind.bind, Pure.pure]
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte, classifyGaiError]
    unfold allowedDnsOutcome
    simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    rcases normalizeGaiCodeForHost_invariants host hints rc with ⟨hValid, hAF, hMis⟩
    have hKindNe := classifyGaiKind_ne_invalidHost (normalizeGaiCodeForHost host hints rc)
    have hKindBool : (classifyGaiKind (normalizeGaiCodeForHost host hints rc) != .invalidHost) = true := by
      cases hk : classifyGaiKind (normalizeGaiCodeForHost host hints rc) <;>
        first | exact absurd hk hKindNe | rfl
    refine ⟨⟨⟨⟨⟨⟨hKindBool, hValid⟩, dnsErrorKind_beq_refl _⟩, hAF⟩, hMis⟩, ?_⟩, decodeErrorMessage_nonEmpty msgBytes⟩
    split
    · rfl
    · rename_i eno' hEq
      split at hEq
      · rename_i hCond
        injection hEq with hEq'
        subst hEq'
        simp [hCond]
      · contradiction
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Exact `.error` characterization of `(mkDnsOpsM (m := Id) raw).getaddrinfo host hints` on valid hosts. -/
theorem mkDnsOpsM_id_error_eq (host : String) (hv : validateHost host = true) (hints : ResolveHints)
    (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) :
    ((mkDnsOpsM (m := Id) { getaddrinfo := fun _ _ _ => .error (rc, eno, msgBytes) }).getaddrinfo host hints) =
      .error
        { kind := classifyGaiKind (normalizeGaiCodeForHost host hints rc)
          gaiCode := normalizeGaiCodeForHost host hints rc
          errno? :=
            if normalizeGaiCodeForHost host hints rc == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then
              some eno
            else none
          message :=
            match String.fromUTF8? msgBytes with
            | some s => if s.isEmpty then "getaddrinfo failed" else s
            | none => s!"<non-utf8:{msgBytes.size}B>" } := by
  unfold mkDnsOpsM
  dsimp only [Bind.bind, Pure.pure]
  have hnv : (!validateHost host) = false := by simp [hv]
  simp only [hnv, Bool.false_eq_true, ↓reduceIte, classifyGaiError, decodeErrorMessage]
  cases String.fromUTF8? msgBytes <;> rfl

end LeanSwe.LinuxSyscall.Dns.Internal

namespace LeanSwe.LinuxSyscall.Dns.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- `Internal.encodeRecords addrs` has exact byte size `addrs.length * Internal.DNS_RECORD_SIZE` (`21` bytes per record). -/
theorem encodeRecords_size (addrs : List DnsAddr) :
    (Internal.encodeRecords addrs).size = addrs.length * Internal.DNS_RECORD_SIZE :=
  Internal.encodeRecords_size addrs

/-- `Internal.decodeRecords` cleanly round-trips `Internal.encodeRecords` for every `List DnsAddr`. -/
theorem decodeRecords_encodeRecords (addrs : List DnsAddr) :
    Internal.decodeRecords (Internal.encodeRecords addrs) = .ok addrs :=
  Internal.decodeRecords_encodeRecords addrs

/-- `Internal.decodeRecords` is right-inverse to `Internal.encodeRecords` on all accepted `ByteArray` payloads. -/
theorem decodeRecords_roundTrip_bytes (bs : ByteArray) (addrs : List DnsAddr)
    (h : Internal.decodeRecords bs = .ok addrs) :
    Internal.encodeRecords addrs = bs :=
  Internal.decodeRecords_roundTrip_bytes bs addrs h

private theorem decodeRecords_never_of_ne (bs : ByteArray) (k : DnsErrorKind)
    (hk : k ≠ .otherGai) :
    Core.NeverErrorKindPure DnsError.kind k (Internal.decodeRecords bs) := by
  unfold Core.NeverErrorKindPure
  cases h : Internal.decodeRecords bs with
  | ok _ => trivial
  | error err =>
    have hm := (Internal.decodeRecords_error_invariants bs err h).1
    exact fun hkind => hk (hkind.symm.trans hm)

/-- `Internal.decodeRecords` never produces `.invalidHost`. -/
theorem decodeRecords_never_invalidHost (bytes : ByteArray) :
    Core.NeverErrorKindPure DnsError.kind .invalidHost (Internal.decodeRecords bytes) :=
  decodeRecords_never_of_ne bytes .invalidHost (by decide)

/-- `Internal.decodeRecords` never produces `.nameNotFound`. -/
theorem decodeRecords_never_nameNotFound (bytes : ByteArray) :
    Core.NeverErrorKindPure DnsError.kind .nameNotFound (Internal.decodeRecords bytes) :=
  decodeRecords_never_of_ne bytes .nameNotFound (by decide)

/-- `Internal.decodeRecords` never produces `.temporaryFailure`. -/
theorem decodeRecords_never_temporaryFailure (bytes : ByteArray) :
    Core.NeverErrorKindPure DnsError.kind .temporaryFailure (Internal.decodeRecords bytes) :=
  decodeRecords_never_of_ne bytes .temporaryFailure (by decide)

/-- `Internal.decodeRecords` never produces `.systemError`. -/
theorem decodeRecords_never_systemError (bytes : ByteArray) :
    Core.NeverErrorKindPure DnsError.kind .systemError (Internal.decodeRecords bytes) :=
  decodeRecords_never_of_ne bytes .systemError (by decide)

theorem baseio_pure_fst {α : Type} (a : α) (s : Void IO.RealWorld) :
    ((Pure.pure (f := BaseIO) a) s).1 = a :=
  rfl

theorem mapAddrForHints_matchesHints (hints : ResolveHints) (a out : DnsAddr)
    (h : mapAddrForHints hints a = some out) :
    addrMatchesHints hints out = true := by
  cases hfam : hints.family with
  | any =>
    simp [mapAddrForHints, hfam] at h
    subst h
    simp [addrMatchesHints, hfam]
  | ipv4 =>
    cases a with
    | ipv4 b0 b1 b2 b3 =>
      simp [mapAddrForHints, hfam] at h
      subst h
      simp [addrMatchesHints, hfam, DnsAddr.isIpv4]
    | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
      simp only [mapAddrForHints, hfam] at h
      split at h
      · simp_all
      · simp only [Option.some.injEq] at h
        subst h
        dsimp [addrMatchesHints, DnsAddr.isIpv4]
        rw [hfam]
      · simp at h
  | ipv6 =>
    cases a with
    | ipv4 =>
      simp [mapAddrForHints, hfam] at h
    | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
      simp [mapAddrForHints, hfam] at h
      subst h
      simp [addrMatchesHints, hfam, DnsAddr.isIpv6]

theorem expandSockType_all_matchesHints (hints : ResolveHints) (xs : List DnsAddr)
    (h : xs.all (addrMatchesHints hints) = true) :
    (expandSockType hints xs).all (addrMatchesHints hints) = true := by
  cases hsock : hints.sockType with
  | stream => simp [expandSockType, hsock, h]
  | dgram => simp [expandSockType, hsock, h]
  | any =>
    simp only [expandSockType, hsock, List.all_eq_true, List.mem_flatMap] at h ⊢
    intro a ha
    rcases ha with ⟨b, hb, hmem⟩
    have hmb := h b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact hmb

private theorem dnsAddr_beq_refl (a : DnsAddr) : (a == a) = true := by
  cases a <;> simp [BEq.beq, instBEqDnsAddr.beq]

private theorem dnsAddr_eq_of_beq {a b : DnsAddr} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> simp [BEq.beq, instBEqDnsAddr.beq] at h
  · simp [h]
  · simp [h]

theorem list_dnsAddr_beq_refl (xs : List DnsAddr) : (xs == xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : instBEqDnsAddr.beq x x = true := dnsAddr_beq_refl x
    have hxs : xs.beq xs = true := ih
    simp [BEq.beq, List.beq, hx, hxs]

theorem list_dnsAddr_eq_of_beq {xs ys : List DnsAddr} (h : (xs == ys) = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp [BEq.beq, List.beq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [BEq.beq, List.beq] at h
    | cons y ys =>
      simp only [BEq.beq, List.beq, Bool.and_eq_true] at h
      have hxy : x = y := dnsAddr_eq_of_beq h.1
      have hxsys : xs = ys := ih h.2
      rw [hxy, hxsys]

theorem expandSockType_matchesSockTypeMultiplicity (hints : ResolveHints) (xs : List DnsAddr) :
    matchesSockTypeMultiplicity hints (expandSockType hints xs) = true := by
  cases hsock : hints.sockType with
  | stream => simp [matchesSockTypeMultiplicity, hsock]
  | dgram => simp [matchesSockTypeMultiplicity, hsock]
  | any =>
    unfold matchesSockTypeMultiplicity expandSockType
    simp only [hsock]
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      unfold checkSockTriples
      simp only [dnsAddr_beq_refl, Bool.true_and]
      exact ih

theorem filterMap_mapAddrForHints_all (hints : ResolveHints) (addrs : List DnsAddr) :
    (addrs.filterMap (mapAddrForHints hints)).all (addrMatchesHints hints) = true := by
  rw [List.all_eq_true]
  intro out hout
  rw [List.mem_filterMap] at hout
  rcases hout with ⟨a, _, ha⟩
  exact mapAddrForHints_matchesHints hints a out ha

theorem allowedDnsOutcome_of_error (host : String) (hv : validateHost host = true)
    (hints : ResolveHints) (err : DnsError)
    (hk : (err.kind != .invalidHost) = true)
    (hcode : isValidGaiCode err.gaiCode = true)
    (hcls : (err.kind == classifyGaiKind err.gaiCode) = true)
    (hAF : (if err.gaiCode == EAI_ADDRFAMILY then isNumericFamilyMismatch host hints else true) = true)
    (hMis : (if isNumericFamilyMismatch host hints then err.gaiCode != EAI_NONAME && err.gaiCode != EAI_NODATA else true) = true)
    (heno : (match err.errno? with
      | none => true
      | some eno => err.gaiCode == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT) = true)
    (hmsg : (!err.message.isEmpty) = true) :
    allowedDnsOutcome host hints (.error err) = true := by
  unfold allowedDnsOutcome
  have hnv : (!validateHost host) = false := by simp [hv]
  simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hk, hcode⟩, hcls⟩, hAF⟩, hMis⟩, heno⟩, hmsg⟩

theorem allowedDnsOutcome_emptyPayloadError (host : String) (hv : validateHost host = true)
    (hints : ResolveHints) :
    allowedDnsOutcome host hints (.error (emptyPayloadError host hints)) = true := by
  unfold emptyPayloadError
  by_cases hMis : isNumericFamilyMismatch host hints = true
  · simp only [hMis, ↓reduceIte]
    exact allowedDnsOutcome_of_error host hv hints _
      (by decide) (by decide) (by decide) (by simp [hMis]) (by simp [hMis]; decide) (by rfl) (by decide)
  · have hMisF : isNumericFamilyMismatch host hints = false := Bool.eq_false_iff.mpr hMis
    simp only [hMisF, Bool.false_eq_true, ↓reduceIte]
    by_cases hP : ((parsePureNumericAddr? host).isSome || (parseHybridScopedNumericZone? host).isSome) = true
    · simp only [hP, ↓reduceIte]
      exact allowedDnsOutcome_of_error host hv hints _
        (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)
    · have hPF : ((parsePureNumericAddr? host).isSome || (parseHybridScopedNumericZone? host).isSome) = false :=
        Bool.eq_false_iff.mpr hP
      simp only [hPF, Bool.false_eq_true, ↓reduceIte]
      by_cases hZ : (parseScopedNonNumericZone? host).isSome = true
      · simp only [hZ, ↓reduceIte]
        exact allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_NONAME, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)
      · have hZF : (parseScopedNonNumericZone? host).isSome = false := Bool.eq_false_iff.mpr hZ
        simp only [hZF, Bool.false_eq_true, ↓reduceIte]
        exact allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_NODATA, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)


end LeanSwe.LinuxSyscall.Dns.Proofs

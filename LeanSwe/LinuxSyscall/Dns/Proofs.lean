import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.Dns.SpecTests

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

private theorem dnsErrorKind_beq_refl (k : DnsErrorKind) : (k == k) = true := by
  cases k <;> decide

private theorem baseio_pure_fst {α : Type} (a : α) (s : Void IO.RealWorld) :
    ((Pure.pure (f := BaseIO) a) s).1 = a :=
  rfl

private theorem classifyGaiKind_ne_invalidHost (rc : Int32) :
    classifyGaiKind rc ≠ .invalidHost := by
  unfold classifyGaiKind
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem mapAddrForHints_matchesHints (hints : ResolveHints) (a out : DnsAddr)
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

private theorem expandSockType_all_matchesHints (hints : ResolveHints) (xs : List DnsAddr)
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

private theorem list_dnsAddr_beq_refl (xs : List DnsAddr) : (xs == xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : instBEqDnsAddr.beq x x = true := dnsAddr_beq_refl x
    have hxs : xs.beq xs = true := ih
    simp [BEq.beq, List.beq, hx, hxs]

private theorem list_dnsAddr_eq_of_beq {xs ys : List DnsAddr} (h : (xs == ys) = true) : xs = ys := by
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

private theorem expandSockType_matchesSockTypeMultiplicity (hints : ResolveHints) (xs : List DnsAddr) :
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

private theorem filterMap_mapAddrForHints_all (hints : ResolveHints) (addrs : List DnsAddr) :
    (addrs.filterMap (mapAddrForHints hints)).all (addrMatchesHints hints) = true := by
  rw [List.all_eq_true]
  intro out hout
  rw [List.mem_filterMap] at hout
  rcases hout with ⟨a, _, ha⟩
  exact mapAddrForHints_matchesHints hints a out ha

private theorem allowedDnsOutcome_of_error (host : String) (hv : validateHost host = true)
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

private theorem allowedDnsOutcome_emptyPayloadError (host : String) (hv : validateHost host = true)
    (hints : ResolveHints) :
    allowedDnsOutcome host hints (.error (emptyPayloadError host hints)) = true := by
  unfold emptyPayloadError
  by_cases hMis : isNumericFamilyMismatch host hints = true
  · simp only [hMis, ↓reduceIte]
    exact allowedDnsOutcome_of_error host hv hints _
      (by decide) (by decide) (by decide) (by simp [hMis]) (by simp [hMis]; decide) (by rfl) (by decide)
  · have hMisF : isNumericFamilyMismatch host hints = false := Bool.eq_false_iff.mpr hMis
    simp only [hMisF, Bool.false_eq_true, ↓reduceIte]
    by_cases hP : (parsePureNumericAddr? host).isSome = true
    · simp only [hP, ↓reduceIte]
      exact allowedDnsOutcome_of_error host hv hints _
        (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)
    · have hPF : (parsePureNumericAddr? host).isSome = false := Bool.eq_false_iff.mpr hP
      simp only [hPF, Bool.false_eq_true, ↓reduceIte]
      by_cases hZ : (parseScopedNonNumericZone? host).isSome = true
      · simp only [hZ, ↓reduceIte]
        exact allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_NONAME, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)
      · have hZF : (parseScopedNonNumericZone? host).isSome = false := Bool.eq_false_iff.mpr hZ
        simp only [hZF, Bool.false_eq_true, ↓reduceIte]
        exact allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_NODATA, EAI_ADDRFAMILY]) (by simp [hMisF]) (by rfl) (by decide)

private theorem normalizeGaiCodeForHost_bounds (host : String) (hints : ResolveHints) (rc : Int32) :
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

private theorem decode_post_sound (host : String) (hv : validateHost host = true)
    (hints : ResolveHints) (recBytes : ByteArray) :
    allowedDnsOutcome host hints
      (match Internal.decodeRecords recBytes with
      | .error e => .error e
      | .ok addrs =>
        if addrs.isEmpty || !addrs.all (addrMatchesHints hints) then
          .error (emptyPayloadError host hints)
        else if !matchesSockTypeMultiplicity hints addrs then
          .error { kind := .nameNotFound
                   gaiCode := EAI_FAIL
                   errno? := none
                   message := "Socket-type multiplicity mismatch" }
        else
          match parsePureNumericAddr? host with
          | some rawAddr =>
            match mapAddrForHints hints rawAddr with
            | none => .error (emptyPayloadError host hints)
            | some expAddr =>
              if addrs == expandSockType hints [expAddr] then
                .ok addrs
              else
                .error { kind := .nameNotFound
                         gaiCode := EAI_FAIL
                         errno? := none
                         message := "Numeric literal resolution mismatch" }
          | none =>
            match parseScopedNonNumericZone? host with
            | some (baseAddr, zoneCs) =>
              if canSymbolicScopedOk hints baseAddr zoneCs &&
                  matchesSymbolicScopedAddrs hints baseAddr addrs then
                .ok addrs
              else
                .error (emptyPayloadError host hints)
            | none => .ok addrs) = true := by
  cases hDec : Internal.decodeRecords recBytes with
  | error err =>
    have hinv := Internal.decodeRecords_error_invariants recBytes err hDec
    rcases hinv with ⟨hk, hcode, heno, hmsg⟩
    have hmsg' : (!err.message.isEmpty) = true := by simpa using hmsg
    refine allowedDnsOutcome_of_error host hv hints err ?_ ?_ ?_ ?_ ?_ ?_ hmsg'
    · rw [hk]; decide
    · rw [hcode]; decide
    · rw [hk, hcode]; decide
    · rw [hcode]; simp [EAI_OVERFLOW, EAI_ADDRFAMILY]
    · rw [hcode]
      split <;> decide
    · rw [heno]
  | ok addrs =>
    dsimp only
    by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
    · simp only [hBad, ↓reduceIte]
      exact allowedDnsOutcome_emptyPayloadError host hv hints
    · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
        Bool.eq_false_iff.mpr hBad
      have hempF : addrs.isEmpty = false := by
        cases h1 : addrs.isEmpty <;> simp_all
      have hall : addrs.all (addrMatchesHints hints) = true := by
        cases h2 : addrs.all (addrMatchesHints hints) <;> simp_all
      simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
      by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
      · simp only [hMultF, ↓reduceIte]
        refine allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) ?_ (by rfl) (by decide)
        split <;> decide
      · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
          Bool.eq_false_iff.mpr hMultF
        have hMult : matchesSockTypeMultiplicity hints addrs = true := by
          cases h3 : matchesSockTypeMultiplicity hints addrs <;> simp_all
        simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte]
        cases hParse : parsePureNumericAddr? host with
        | some rawAddr =>
          dsimp only
          cases hMap : mapAddrForHints hints rawAddr with
          | none =>
            dsimp only
            exact allowedDnsOutcome_emptyPayloadError host hv hints
          | some expAddr =>
            dsimp only
            by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
            · simp only [hEq, ↓reduceIte]
              unfold allowedDnsOutcome
              have hnv : (!validateHost host) = false := by simp [hv]
              simp [hnv, hempF, hall, hMult, hParse, hMap, hEq]
            · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
                Bool.eq_false_iff.mpr hEq
              simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
              refine allowedDnsOutcome_of_error host hv hints _
                (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) ?_ (by rfl) (by decide)
              split <;> decide
        | none =>
          dsimp only
          cases hScoped : parseScopedNonNumericZone? host with
          | none =>
            unfold allowedDnsOutcome
            have hnv : (!validateHost host) = false := by simp [hv]
            simp [hnv, hempF, hall, hMult, hParse, hScoped]
          | some p =>
            rcases p with ⟨baseAddr, zoneCs⟩
            dsimp only
            by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                matchesSymbolicScopedAddrs hints baseAddr addrs) = true
            · simp only [hScOk, ↓reduceIte]
              unfold allowedDnsOutcome
              have hnv : (!validateHost host) = false := by simp [hv]
              simp [hnv, hempF, hall, hMult, hParse, hScoped, hScOk]
            · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                  matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                Bool.eq_false_iff.mpr hScOk
              simp only [hScF, Bool.false_eq_true, ↓reduceIte]
              exact allowedDnsOutcome_emptyPayloadError host hv hints

private theorem baseio_bind_eq {α β : Type} (x : BaseIO α) (f : α → BaseIO β) (w : Void IO.RealWorld) :
    (x >>= f) w = f (x w).1 (x w).2 :=
  rfl

private theorem validateHost_eq (h : String) :
    validateHost h = (!h.toList.isEmpty && !h.toList.any (· == '\x00')) := by
  unfold validateHost
  have hEmpty : h.isEmpty = h.toList.isEmpty := by
    cases hl : h.toList with
    | nil =>
      have : h = "" := String.ext (by simp [hl])
      subst this; decide
    | cons _ _ =>
      have hne : h ≠ "" := by intro he; subst he; simp at hl
      simp [hne]
  simp [String.any, hEmpty]

private theorem eio_ofBaseIO_eq {α : Type} (x : BaseIO α) (w : Void IO.RealWorld) :
    (liftM x : IO α) w = EST.Out.ok (x w).1 (x w).2 :=
  rfl

private theorem io_bind_ok {α β : Type} (x : IO α) (f : α → IO β) (w w' : Void IO.RealWorld) (a : α)
    (hx : x w = EST.Out.ok a w') :
    (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  simp [EST.bind, hx]

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (Pure.pure (f := IO) a) w = EST.Out.ok a w :=
  rfl

private theorem io_pure_match {α : Type} (P : α → Bool) (a : α) (w : Void IO.RealWorld) (h : P a = true) :
    (match (Pure.pure (f := IO) a) w with | .ok res _ => P res = true | .error _ _ => False) := by
  rw [io_pure_eq]
  exact h

/-- `Internal.mkDnsOps` is definitionally `Internal.mkDnsOpsM` specialized to `IO`. -/
theorem mkDnsOps_eq_mkDnsOpsM (raw : Internal.PosixDnsOps) :
    Internal.mkDnsOps raw = Internal.mkDnsOpsM raw :=
  rfl

/-- `defaultOps.getaddrinfo` is definitionally `fun host hints => liftM (defaultOpsBase.getaddrinfo host hints)`. -/
theorem defaultOps_eq_liftM_defaultOpsBase :
    ∀ host hints, defaultOps.getaddrinfo host hints = liftM (defaultOpsBase.getaddrinfo host hints) :=
  fun _ _ => rfl

/-- `Dns.getaddrinfo` forwards `(host, hints)` directly to `defaultOps.getaddrinfo`. -/
theorem getaddrinfo_eq_defaultOps (host : String) (hints : ResolveHints) :
    Dns.getaddrinfo host hints = defaultOps.getaddrinfo host hints :=
  rfl

/-- Single-argument `Dns.getaddrinfo host` uses `{ family := .any, sockType := .stream }` (`{}`). -/
theorem getaddrinfo_default_hints_eq (host : String) :
    Dns.getaddrinfo host = defaultOps.getaddrinfo host { family := .any, sockType := .stream } :=
  rfl

/-- Pure `Id` soundness bridge for `Internal.mkDnsOpsM`. -/
theorem mkDnsOpsM_id_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOpsM Id) (host : String) (hints : ResolveHints) :
    allowedDnsOutcome host hints ((Internal.mkDnsOpsM raw).getaddrinfo host hints) = true := by
  unfold Internal.mkDnsOpsM
  dsimp only [Bind.bind, Pure.pure]
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    cases hRaw : raw.getaddrinfo host hints.family.toWire hints.sockType.toWire with
    | ok recBytes =>
      exact decode_post_sound host hv hints recBytes
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact hId
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Soundness bridge: every `BaseIO` call through `Internal.mkDnsOpsM raw` satisfies `Model.allowedDnsOutcome`. -/
theorem mkDnsOpsM_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints)
    (w : Void IO.RealWorld) :
    allowedDnsOutcome host hints ((Internal.mkDnsOpsM raw).getaddrinfo host hints w).1 = true := by
  unfold Internal.mkDnsOpsM
  dsimp only
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    rw [baseio_bind_eq]
    cases hRaw : (raw.getaddrinfo host hints.family.toWire hints.sockType.toWire w).1 with
    | ok recBytes =>
      have hPost := decode_post_sound host hv hints recBytes
      dsimp only
      cases hDec : Internal.decodeRecords recBytes with
      | error err =>
        rw [baseio_pure_fst]
        simpa [hDec] using hPost
      | ok addrs =>
        dsimp only
        simp only [hDec] at hPost
        by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
        · simp only [hBad, ↓reduceIte] at hPost ⊢
          rw [baseio_pure_fst]; exact hPost
        · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
            Bool.eq_false_iff.mpr hBad
          simp only [hBadF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
          by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
          · simp only [hMultF, ↓reduceIte] at hPost ⊢
            rw [baseio_pure_fst]; exact hPost
          · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
              Bool.eq_false_iff.mpr hMultF
            simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
            cases hP : parsePureNumericAddr? host with
            | some rawAddr =>
              cases hM : mapAddrForHints hints rawAddr with
              | none =>
                simp only [hP, hM] at hPost ⊢
                rw [baseio_pure_fst]; exact hPost
              | some expAddr =>
                simp only [hP, hM] at hPost ⊢
                by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
                · simp only [hEq, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
                · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
                    Bool.eq_false_iff.mpr hEq
                  simp only [hEqF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
            | none =>
              cases hZ : parseScopedNonNumericZone? host with
              | none =>
                simp only [hP, hZ] at hPost ⊢
                rw [baseio_pure_fst]; exact hPost
              | some p =>
                rcases p with ⟨baseAddr, zoneCs⟩
                simp only [hP, hZ] at hPost ⊢
                by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                    matchesSymbolicScopedAddrs hints baseAddr addrs) = true
                · simp only [hScOk, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
                · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                      matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                    Bool.eq_false_iff.mpr hScOk
                  simp only [hScF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      rw [baseio_pure_fst]
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact hId
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    rw [baseio_pure_fst]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Soundness bridge in `BaseIO` for `LeanSwe.LinuxSyscall.Dns.defaultOpsBase`. -/
theorem defaultOpsBase_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    allowedDnsOutcome host hints (defaultOpsBase.getaddrinfo host hints w).1 = true :=
  mkDnsOpsM_soundAgainstAllowedOutcome _ host hints w

/-- Soundness bridge in `IO`: whenever `raw.getaddrinfo` returns without throwing an `IO.Error`, `(Internal.mkDnsOps raw).getaddrinfo host hints` returns `.ok res` satisfying `allowedDnsOutcome host hints res`. -/
theorem mkDnsOps_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOps)
    (hNoThrow : ∀ h f s (w0 : Void IO.RealWorld),
      ∃ r w1, raw.getaddrinfo h f s w0 = EST.Out.ok r w1)
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match (Internal.mkDnsOps raw).getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False := by
  unfold Internal.mkDnsOps Internal.mkDnsOpsM
  dsimp only
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    rcases hNoThrow host hints.family.toWire hints.sockType.toWire w with
      ⟨rawOut, w1, hRaw⟩
    rw [io_bind_ok _ _ w w1 rawOut hRaw]
    cases rawOut with
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact io_pure_match (allowedDnsOutcome host hints) _ w1 hId
    | ok recBytes =>
      have hPost := decode_post_sound host hv hints recBytes
      dsimp only
      cases hDec : Internal.decodeRecords recBytes with
      | error err =>
        simp only [hDec] at hPost
        exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
      | ok addrs =>
        dsimp only
        simp only [hDec] at hPost
        by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
        · simp only [hBad, ↓reduceIte] at hPost ⊢
          exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
        · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
            Bool.eq_false_iff.mpr hBad
          simp only [hBadF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
          by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
          · simp only [hMultF, ↓reduceIte] at hPost ⊢
            exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
          · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
              Bool.eq_false_iff.mpr hMultF
            simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
            cases hP : parsePureNumericAddr? host with
            | some rawAddr =>
              cases hM : mapAddrForHints hints rawAddr with
              | none =>
                simp only [hP, hM] at hPost ⊢
                exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
              | some expAddr =>
                simp only [hP, hM] at hPost ⊢
                by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
                · simp only [hEq, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
                    Bool.eq_false_iff.mpr hEq
                  simp only [hEqF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
            | none =>
              cases hZ : parseScopedNonNumericZone? host with
              | none =>
                simp only [hP, hZ] at hPost ⊢
                exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
              | some p =>
                rcases p with ⟨baseAddr, zoneCs⟩
                simp only [hP, hZ] at hPost ⊢
                by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                    matchesSymbolicScopedAddrs hints baseAddr addrs) = true
                · simp only [hScOk, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                      matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                    Bool.eq_false_iff.mpr hScOk
                  simp only [hScF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    refine io_pure_match (allowedDnsOutcome host hints) _ w ?_
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- End-to-end `IO` soundness bridge for `LeanSwe.LinuxSyscall.Dns.defaultOps` (`Interface.lean`): never throws `IO.Error` and always returns an `allowedDnsOutcome`. -/
theorem defaultOps_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match defaultOps.getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False := by
  change match (liftM (defaultOpsBase.getaddrinfo host hints) : IO _) w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False
  rw [eio_ofBaseIO_eq]
  exact defaultOpsBase_soundAgainstAllowedOutcome host hints w

/-- End-to-end `IO` soundness bridge for public `LeanSwe.LinuxSyscall.Dns.getaddrinfo` (`Interface.lean`). -/
theorem getaddrinfo_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match Dns.getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False :=
  defaultOps_soundAgainstAllowedOutcome host hints w

/-- In `BaseIO`, `(Internal.mkDnsOpsM raw).getaddrinfo host hints` never emits `.invalidHost` once `validateHost host = true`. -/
theorem mkDnsOps_never_invalidHost_of_valid
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints)
    (hv : validateHost host = true) (w : Void IO.RealWorld) :
    Core.NeverErrorKindBaseIO DnsError.kind .invalidHost
      ((Internal.mkDnsOpsM raw).getaddrinfo host hints) w := by
  have hs := mkDnsOpsM_soundAgainstAllowedOutcome raw host hints w
  unfold Core.NeverErrorKindBaseIO
  unfold allowedDnsOutcome at hs
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
  cases hRes : (Internal.mkDnsOpsM raw).getaddrinfo host hints w with
  | mk val st =>
    cases hVal : val with
    | ok _ => trivial
    | error err =>
      have hFst : ((Internal.mkDnsOpsM raw).getaddrinfo host hints w).1 = .error err := by
        rw [hRes, hVal]
      rw [hFst] at hs
      simp only [Bool.and_eq_true] at hs
      have hne : (err.kind != .invalidHost) = true := hs.1.1.1.1.1.1
      dsimp only
      intro he
      rw [he] at hne
      revert hne
      decide

/-- When a `BaseIO` raw hook returns non-empty hint-matching encoded `addrs` on a valid host (matching any numeric/zoned literal and sockType multiplicity), `(Internal.mkDnsOpsM raw).getaddrinfo host hints` can never fail with any `DnsErrorKind`. -/
theorem mkDnsOps_never_error_when_encoded
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints) (addrs : List DnsAddr)
    (hv : validateHost host = true)
    (hne : addrs.isEmpty = false)
    (hm : addrs.all (addrMatchesHints hints) = true)
    (hMult : matchesSockTypeMultiplicity hints addrs = true)
    (hNum : ∀ rawAddr, parsePureNumericAddr? host = some rawAddr →
      ∃ expAddr, mapAddrForHints hints rawAddr = some expAddr ∧ addrs = expandSockType hints [expAddr])
    (hScoped : ∀ baseAddr zoneCs, parseScopedNonNumericZone? host = some (baseAddr, zoneCs) →
      canSymbolicScopedOk hints baseAddr zoneCs = true ∧
      matchesSymbolicScopedAddrs hints baseAddr addrs = true)
    (hRawOk : ∀ w0 : Void IO.RealWorld,
      (raw.getaddrinfo host hints.family.toWire hints.sockType.toWire w0).1 =
        Except.ok (Internal.encodeRecords addrs))
    (kind : DnsErrorKind) (w : Void IO.RealWorld) :
    Core.NeverErrorKindBaseIO DnsError.kind kind
      ((Internal.mkDnsOpsM raw).getaddrinfo host hints) w := by
  unfold Core.NeverErrorKindBaseIO Internal.mkDnsOpsM
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [baseio_bind_eq, hRawOk w]
  dsimp only
  simp only [decodeRecords_encodeRecords, hne, hm, hMult, Bool.false_eq_true, Bool.not_true, Bool.or_self, ↓reduceIte]
  cases hP : parsePureNumericAddr? host with
  | some rawAddr =>
    rcases hNum rawAddr hP with ⟨expAddr, hMap, hEq⟩
    dsimp only
    simp only [hMap, hEq, list_dnsAddr_beq_refl, ↓reduceIte]
    exact trivial
  | none =>
    cases hZ : parseScopedNonNumericZone? host with
    | none =>
      dsimp only
      trivial
    | some p =>
      rcases p with ⟨baseAddr, zoneCs⟩
      rcases hScoped baseAddr zoneCs hZ with ⟨hCan, hMatch⟩
      dsimp only
      simp only [hCan, hMatch, Bool.and_self, ↓reduceIte]
      exact trivial

/-- Proof of `test_dns_validateHost_semantics` for `validateHost`. -/
theorem test_dns_validateHost_semantics_ok :
    Core.AllPass (test_dns_validateHost_semantics validateHost) := by
  intro h
  simp only [Core.NondetTest.assert, Bind.bind, validateHost_eq]
  exact ⟨by decide, by decide, by decide, by decide, by decide, trivial, trivial⟩

/-- Proof of `test_dns_addrHelpers_semantics` for `DnsAddr.format` and `DnsAddr.isLoopback`. -/
theorem test_dns_addrHelpers_semantics_ok :
    Core.AllPass (test_dns_addrHelpers_semantics DnsAddr.format DnsAddr.isLoopback) := by
  dsimp [test_dns_addrHelpers_semantics]
  simp only [Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Proof of `test_dns_classifyGaiKind_semantics` for `classifyGaiKind`. -/
theorem test_dns_classifyGaiKind_semantics_ok :
    Core.AllPass (test_dns_classifyGaiKind_semantics classifyGaiKind) := by
  intro rc
  simp only [Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  have hne := classifyGaiKind_ne_invalidHost rc
  cases hk : classifyGaiKind rc <;>
    first | exact absurd hk hne | decide

/-- Proof of `test_dns_wireTags_semantics` for `AddrFamilyHint.toWire` and `SockTypeHint.toWire`. -/
theorem test_dns_wireTags_semantics_ok :
    Core.AllPass (test_dns_wireTags_semantics AddrFamilyHint.toWire SockTypeHint.toWire) := by
  intro f1 f2 s1 s2
  dsimp only [test_dns_wireTags_semantics, Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, trivial⟩
  · cases f1 <;> cases f2 <;> decide
  · cases s1 <;> cases s2 <;> decide

private theorem normalizeOracleOutcome_soundAgainstAllowedOutcome (host : String)
    (hints : ResolveHints) (rawOut : Except DnsError (List DnsAddr)) :
    allowedDnsOutcome host hints (normalizeOracleOutcome host hints rawOut) = true := by
  unfold normalizeOracleOutcome
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    cases hlook : rawOut with
    | ok addrs =>
      dsimp only
      have hAllFiltered := filterMap_mapAddrForHints_all hints addrs
      generalize hKept :
          (if !(addrs.filterMap (mapAddrForHints hints)).isEmpty &&
              matchesSockTypeMultiplicity hints (addrs.filterMap (mapAddrForHints hints)) then
            addrs.filterMap (mapAddrForHints hints)
          else
            expandSockType hints (addrs.filterMap (mapAddrForHints hints))) = kept
      have hMult : matchesSockTypeMultiplicity hints kept = true := by
        rw [← hKept]
        split
        · rename_i hBr
          simp only [Bool.and_eq_true] at hBr
          exact hBr.2
        · exact expandSockType_matchesSockTypeMultiplicity hints _
      have hAllKept : kept.all (addrMatchesHints hints) = true := by
        rw [← hKept]
        split
        · exact hAllFiltered
        · exact expandSockType_all_matchesHints hints _ hAllFiltered
      cases hP : parsePureNumericAddr? host with
      | some rawAddr =>
        dsimp only
        cases hM : mapAddrForHints hints rawAddr with
        | none =>
          dsimp only
          exact allowedDnsOutcome_emptyPayloadError host hv hints
        | some expAddr =>
          dsimp only
          by_cases hEq : (kept == expandSockType hints [expAddr]) = true
          · simp only [hEq, ↓reduceIte]
            unfold allowedDnsOutcome
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hP, hM, hEq, Bool.and_true]
            have hne : (expandSockType hints [expAddr]).isEmpty = false := by
              cases hsock : hints.sockType <;> simp [expandSockType, hsock]
            have hExpMatch : ([expAddr] : List DnsAddr).all (addrMatchesHints hints) = true := by
              simp [mapAddrForHints_matchesHints hints rawAddr expAddr hM]
            have hAll := expandSockType_all_matchesHints hints [expAddr] hExpMatch
            have hEq' : kept = expandSockType hints [expAddr] :=
              list_dnsAddr_eq_of_beq hEq
            have hne' : kept.isEmpty = false := by
              rw [hEq']; exact hne
            have hAll' : kept.all (addrMatchesHints hints) = true := by
              rw [hEq']; exact hAll
            simp [hne', hAll', hMult]
          · have hEqF : (kept == expandSockType hints [expAddr]) = false :=
              Bool.eq_false_iff.mpr hEq
            simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
            refine allowedDnsOutcome_of_error host hv hints _
              (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) ?_ (by rfl) (by decide)
            split <;> decide
      | none =>
        dsimp only
        cases hZ : parseScopedNonNumericZone? host with
        | some p =>
          rcases p with ⟨baseAddr, zoneCs⟩
          dsimp only
          by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
              !kept.isEmpty &&
              matchesSymbolicScopedAddrs hints baseAddr kept) = true
          · simp only [hScOk, ↓reduceIte]
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hScOk
            rcases hScOk with ⟨⟨hCan, hNemp⟩, hMatch⟩
            unfold allowedDnsOutcome
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hNemp, Bool.not_false, hAllKept, hMult,
              hP, hZ, hCan, hMatch, Bool.and_self]
          · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                !kept.isEmpty &&
                matchesSymbolicScopedAddrs hints baseAddr kept) = false :=
              Bool.eq_false_iff.mpr hScOk
            simp only [hScF, Bool.false_eq_true, ↓reduceIte]
            exact allowedDnsOutcome_emptyPayloadError host hv hints
        | none =>
          dsimp only
          by_cases hemp : kept.isEmpty = true
          · simp only [hemp, ↓reduceIte]
            exact allowedDnsOutcome_emptyPayloadError host hv hints
          · have hempF : kept.isEmpty = false := Bool.eq_false_iff.mpr hemp
            simp only [hempF, Bool.false_eq_true, ↓reduceIte]
            unfold allowedDnsOutcome
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hempF, Bool.not_false, hAllKept, hMult,
              hP, hZ, Bool.and_self]
    | error err =>
      dsimp only
      let code' := normalizeGaiCodeForHost host hints err.gaiCode
      let errno?' : Option Errno := match err.errno? with
        | some eno => if code' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
        | none => none
      let msg' := if err.message.isEmpty then "getaddrinfo failed" else err.message
      rcases normalizeGaiCodeForHost_bounds host hints err.gaiCode with ⟨hValid, hAF, hMis⟩
      refine allowedDnsOutcome_of_error host hv hints
        { kind := classifyGaiKind code', gaiCode := code', errno? := errno?', message := msg' }
        ?_ hValid (dnsErrorKind_beq_refl _) hAF hMis ?_ ?_
      · have hkindNe := classifyGaiKind_ne_invalidHost code'
        cases hk : classifyGaiKind code' <;>
          first | exact absurd hk hkindNe | rfl
      · dsimp only [errno?']
        cases hErrEno : err.errno? with
        | none => rfl
        | some e =>
          dsimp only
          by_cases hSys : (code' == EAI_SYSTEM && e != 0 && e != Errno.EFAULT) = true
          · simp only [hSys, ↓reduceIte]
          · have hSysF : (code' == EAI_SYSTEM && e != 0 && e != Errno.EFAULT) = false :=
              Bool.eq_false_iff.mpr hSys
            simp only [hSysF, Bool.false_eq_true, ↓reduceIte]
      · by_cases hm : err.message = ""
        · simp [msg', hm, String.isEmpty]
        · simp [msg', String.isEmpty, hm]
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

private theorem modelResolve_soundAgainstAllowedOutcome (oracle : DnsOracle) (host : String)
    (hints : ResolveHints) :
    allowedDnsOutcome host hints (modelResolve oracle host hints) = true := by
  unfold modelResolve
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    exact normalizeOracleOutcome_soundAgainstAllowedOutcome host hints (oracle.lookup host hints)
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Proof of `test_dns_modelOps_soundAgainstAllowedOutcome` for `modelOps`. -/
theorem test_dns_modelOps_soundAgainstAllowedOutcome_ok :
    Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome modelOps) := by
  intro oracle host hints rawOut
  dsimp only [test_dns_modelOps_soundAgainstAllowedOutcome, Core.NondetTest.assert, Bind.bind,
    modelOps, Pure.pure, StateT.run, StateT.bind, StateT.pure,
    get, MonadStateOf.get, getThe, StateT.get]
  have hv127 : validateHost "127.0.0.1" = true := by rw [validateHost_eq]; decide
  have hvEmpty : validateHost "" = false := by rw [validateHost_eq]; decide
  have hvNul : validateHost "a\x00b" = false := by rw [validateHost_eq]; decide
  have hvLocal : validateHost "localhost" = true := by rw [validateHost_eq]; decide
  have hvZ1 : validateHost "::1%lo" = true := by rw [validateHost_eq]; decide
  have hvZ2 : validateHost "fe80::1%lo" = true := by rw [validateHost_eq]; decide
  have hvZ3 : validateHost "fe80::1%" = true := by rw [validateHost_eq]; decide
  have hvBad : validateHost "bad host" = true := by rw [validateHost_eq]; decide
  have hvA : validateHost "::ffff:127.0.0.1" = true := by rw [validateHost_eq]; decide
  have hvMZ : validateHost "::ffff:127.0.0.1%lo" = true := by rw [validateHost_eq]; decide
  refine ⟨modelResolve_soundAgainstAllowedOutcome oracle host hints,
    normalizeOracleOutcome_soundAgainstAllowedOutcome host hints rawOut, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  · simp [allowedDnsOutcome, hv127]
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvZ1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_NONAME]
    intro _ _ _ hK; exact absurd hK (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_NONAME, EAI_SYSTEM]
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_SYSTEM, Errno.EFAULT]
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ _ hLe _; exact absurd hLe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hGe _; exact absurd hGe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hGe _; exact absurd hGe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hEq _; exact absurd hEq (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, EAI_BADFLAGS]
    intro _ _ hLe _; exact absurd hLe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, EAI_SERVICE]
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvZ3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvBad, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [modelResolve, defaultOfflineOracle, hvA, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · have hP127 : parsePureNumericAddr? "127.0.0.1" = some (.ipv4 127 0 0 1) := by rfl
    simp only [modelResolve, defaultOfflineOracle, hv127, hP127, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvMZ, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]
  · have hP127 : parsePureNumericAddr? "127.0.0.1" = some (.ipv4 127 0 0 1) := by rfl
    simp only [defaultOfflineOracle, hv127, hP127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [defaultOfflineOracle, hvZ2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp [normalizeOracleOutcome, hvEmpty]
  · simp [normalizeOracleOutcome, hvNul]

/-- Proof of `test_dns_mkRawOps_soundAgainstAllowedOutcome` for `Internal.mkDnsOpsM` (`Id`). -/
theorem test_dns_mkRawOps_soundAgainstAllowedOutcome_ok :
    Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
      (fun raw => Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw })) := by
  intro rawFn host hints expectedAddrs
  dsimp only [test_dns_mkRawOps_soundAgainstAllowedOutcome, Core.NondetTest.assert, Bind.bind]
  refine ⟨mkDnsOpsM_id_soundAgainstAllowedOutcome { getaddrinfo := rawFn } host hints, ?_, ?_, trivial⟩
  · rw [Bool.or_eq_true]
    cases hR : rawFn host hints.family.toWire hints.sockType.toWire with
    | error e =>
      left
      simp
    | ok bytes =>
      by_cases hv : validateHost host = true
      · by_cases hAllowed : allowedDnsOutcome host hints (.ok expectedAddrs) = true
        · by_cases hBytes : (bytes.data == (encodeWireRecords expectedAddrs).data) = true
          · right
            have hRaw : rawFn host hints.family.toWire hints.sockType.toWire =
                .ok (encodeWireRecords expectedAddrs) := by
              rw [hR, ByteArray.ext (eq_of_beq hBytes)]
            unfold allowedDnsOutcome at hAllowed
            have hnv : (!validateHost host) = false := by simp [hv]
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAllowed
            rcases hAllowed with ⟨⟨⟨hNemp, hAll⟩, hMult⟩, hTrail⟩
            have hemp : expectedAddrs.isEmpty = false := by
              cases h1 : expectedAddrs.isEmpty <;> simp_all
            unfold Internal.mkDnsOpsM
            dsimp only [Bind.bind, Pure.pure]
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hRaw, Internal.decodeRecords_encodeRecords,
              hemp, hAll, hMult, Bool.not_true, Bool.or_self, ↓reduceIte]
            cases hP : parsePureNumericAddr? host with
            | some rawAddr =>
              simp only [hP] at hTrail
              cases hM : mapAddrForHints hints rawAddr with
              | none => simp [hM] at hTrail
              | some expAddr =>
                simp only [hM] at hTrail ⊢
                simp only [hTrail, ↓reduceIte, list_dnsAddr_beq_refl]
            | none =>
              simp only [hP] at hTrail
              cases hZ : parseScopedNonNumericZone? host with
              | none =>
                simp only [list_dnsAddr_beq_refl]
              | some p =>
                rcases p with ⟨baseAddr, zoneCs⟩
                simp only [hZ, Bool.and_eq_true] at hTrail ⊢
                simp only [hTrail.1, hTrail.2, and_self, ↓reduceIte, list_dnsAddr_beq_refl]
          · left; simp [hv, hAllowed, hBytes]
        · left; simp [hv, hAllowed]
      · left; simp [hv]
  · cases hv : validateHost host with
    | false => trivial
    | true =>
      cases hR : rawFn host hints.family.toWire hints.sockType.toWire with
      | ok _ => trivial
      | error p =>
        rcases p with ⟨rc, eno, msgBytes⟩
        dsimp only
        have hEq := Internal.mkDnsOpsM_id_error_eq host hv hints rc eno msgBytes
        unfold Internal.mkDnsOpsM at hEq ⊢
        dsimp only [Bind.bind, Pure.pure] at hEq ⊢
        rw [hR]
        exact hEq

end LeanSwe.LinuxSyscall.Dns.Proofs

#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.encodeRecords_size
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_encodeRecords
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_roundTrip_bytes
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_never_invalidHost
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_never_nameNotFound
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_never_temporaryFailure
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.decodeRecords_never_systemError
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOpsM_id_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOpsM_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOps_eq_mkDnsOpsM
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.defaultOps_eq_liftM_defaultOpsBase
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.getaddrinfo_eq_defaultOps
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.getaddrinfo_default_hints_eq
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.defaultOpsBase_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOps_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.defaultOps_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.getaddrinfo_soundAgainstAllowedOutcome
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOps_never_invalidHost_of_valid
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.mkDnsOps_never_error_when_encoded
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_validateHost_semantics_ok
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_addrHelpers_semantics_ok
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_classifyGaiKind_semantics_ok
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_wireTags_semantics_ok
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_modelOps_soundAgainstAllowedOutcome_ok
#print axioms LeanSwe.LinuxSyscall.Dns.Proofs.test_dns_mkRawOps_soundAgainstAllowedOutcome_ok

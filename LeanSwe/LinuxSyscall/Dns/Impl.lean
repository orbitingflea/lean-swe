import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.Dns.Model

namespace LeanSwe.LinuxSyscall.Dns.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- Fixed byte width of each serialized address record emitted by `c/dns_shim.c`. -/
abbrev DNS_RECORD_SIZE : Nat := Dns.DNS_RECORD_SIZE

private def DNS_FAMILY_V4 : UInt8 := 4

private def DNS_FAMILY_V6 : UInt8 := 6

private def decodeErrorMessage (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s =>
    if s.isEmpty then "getaddrinfo failed" else s
  | none =>
    s!"<non-utf8:{bytes.size}B>"

private def classifyGaiError (host : String) (hints : ResolveHints)
    (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) : DnsError :=
  let rc' := normalizeGaiCodeForHost host hints rc
  let kind := classifyGaiKind rc'
  let errno? : Option Errno :=
    if rc' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
  { kind := kind
    gaiCode := rc'
    errno? := errno?
    message := decodeErrorMessage msgBytes }

private def decodeUInt32LE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)))

/-- Serialize a list of `DnsAddr` values into concatenated 21-byte `ByteArray` records (`Types.encodeWireRecords`). -/
abbrev encodeRecords (addrs : List DnsAddr) : ByteArray :=
  encodeWireRecords addrs

private def decodeRecordAt (bytes : ByteArray) (idx : Nat) (h : idx + DNS_RECORD_SIZE ≤ bytes.size) :
    Except DnsError DnsAddr :=
  let tag := bytes[idx]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b0 := bytes[idx + 1]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b1 := bytes[idx + 2]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b2 := bytes[idx + 3]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b3 := bytes[idx + 4]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b4 := bytes[idx + 5]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b5 := bytes[idx + 6]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b6 := bytes[idx + 7]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b7 := bytes[idx + 8]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b8 := bytes[idx + 9]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b9 := bytes[idx + 10]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b10 := bytes[idx + 11]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b11 := bytes[idx + 12]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b12 := bytes[idx + 13]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b13 := bytes[idx + 14]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b14 := bytes[idx + 15]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let b15 := bytes[idx + 16]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let s0 := bytes[idx + 17]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let s1 := bytes[idx + 18]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let s2 := bytes[idx + 19]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  let s3 := bytes[idx + 20]'(by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at h; omega)
  if tag == DNS_FAMILY_V4 then
    if b4 == 0 && b5 == 0 && b6 == 0 && b7 == 0 && b8 == 0 && b9 == 0 &&
        b10 == 0 && b11 == 0 && b12 == 0 && b13 == 0 && b14 == 0 && b15 == 0 &&
        s0 == 0 && s1 == 0 && s2 == 0 && s3 == 0 then
      .ok (.ipv4 b0 b1 b2 b3)
    else
      .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
               message := "non-zero padding or scope in IPv4 DNS record" }
  else if tag == DNS_FAMILY_V6 then
    .ok (.ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 (decodeUInt32LE s0 s1 s2 s3))
  else
    .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
             message := s!"invalid DNS record family tag {tag.toNat}" }

private def decodeRecordsLoop (bytes : ByteArray) (idx : Nat) (acc : List DnsAddr) :
    Except DnsError (List DnsAddr) :=
  if idx == bytes.size then
    .ok acc.reverse
  else if hFull : idx + DNS_RECORD_SIZE ≤ bytes.size then
    match decodeRecordAt bytes idx hFull with
    | .ok a => decodeRecordsLoop bytes (idx + DNS_RECORD_SIZE) (a :: acc)
    | .error e => .error e
  else
    .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
             message := "truncated DNS record payload" }
termination_by bytes.size - idx
decreasing_by
  simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at hFull ⊢
  omega

/-- Decode concatenated 21-byte `ByteArray` records from `dns_shim.c` into `List DnsAddr`. -/
def decodeRecords (bytes : ByteArray) : Except DnsError (List DnsAddr) :=
  decodeRecordsLoop bytes 0 []

/-- Low-level C-ABI DNS resolution hook signature parameterized by monad `m`. -/
structure PosixDnsOpsM (m : Type → Type) where
  /-- Call `leanswe_sys_getaddrinfo` returning raw 21-byte records or `(gaiCode, errno, msgBytes)`. -/
  getaddrinfo : String → UInt8 → UInt8 → m (Except (Int32 × UInt32 × ByteArray) ByteArray)

/-- Specialized `IO` signature for `PosixDnsOpsM`. -/
abbrev PosixDnsOps := PosixDnsOpsM IO

/-- Construct a `DnsOpsM m` capability bundle from low-level `PosixDnsOpsM m` hooks, validating `host` up front, forwarding wire hints, enforcing `allowedDnsOutcome` invariants over decoded records, and safely UTF-8-decoding error bytes. -/
def mkDnsOpsM {m : Type → Type} [Monad m] (raw : PosixDnsOpsM m) : DnsOpsM m :=
  { getaddrinfo := fun host hints => do
      if !validateHost host then
        return .error invalidHostError
      else
        match ← raw.getaddrinfo host hints.family.toWire hints.sockType.toWire with
        | .ok recBytes =>
          match decodeRecords recBytes with
          | .error e => return .error e
          | .ok addrs =>
            if addrs.isEmpty || !addrs.all (addrMatchesHints hints) then
              return .error (emptyPayloadError host hints)
            else if !matchesSockTypeMultiplicity hints addrs then
              return .error { kind := .nameNotFound
                              gaiCode := EAI_FAIL
                              errno? := none
                              message := "Socket-type multiplicity mismatch" }
            else
              match parsePureNumericAddr? host with
              | some rawAddr =>
                match mapAddrForHints hints rawAddr with
                | none =>
                  return .error (emptyPayloadError host hints)
                | some expAddr =>
                  if addrs == expandSockType hints [expAddr] then
                    return .ok addrs
                  else
                    return .error { kind := .nameNotFound
                                    gaiCode := EAI_FAIL
                                    errno? := none
                                    message := "Numeric literal resolution mismatch" }
              | none =>
                match parseHybridScopedNumericZone? host with
                | some (baseAddr, sc) =>
                  if matchesHybridScopedAddrs hints baseAddr sc addrs then
                    return .ok addrs
                  else
                    return .error (emptyPayloadError host hints)
                | none =>
                  match parseScopedNonNumericZone? host with
                  | some (baseAddr, zoneCs) =>
                    if canSymbolicScopedOk hints baseAddr zoneCs &&
                        matchesSymbolicScopedAddrs hints baseAddr addrs then
                      return .ok addrs
                    else
                      return .error (emptyPayloadError host hints)
                  | none => return .ok addrs
        | .error (rc, eno, msgBytes) => return .error (classifyGaiError host hints rc eno msgBytes) }

/-- Construct an `IO` `DnsOps` bundle from `PosixDnsOps` hooks. -/
def mkDnsOps (raw : PosixDnsOps) : DnsOps :=
  mkDnsOpsM raw

private def encodeUInt32LEList (v : UInt32) : List UInt8 :=
  let n := v.toNat
  [ UInt8.ofNat (n % 256)
  , UInt8.ofNat ((n / 256) % 256)
  , UInt8.ofNat ((n / 65536) % 256)
  , UInt8.ofNat ((n / 16777216) % 256) ]

private def decodeRecordsList : List UInt8 → Except DnsError (List DnsAddr)
  | [] => .ok []
  | tag :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: s0 :: s1 :: s2 :: s3 :: rest =>
    if tag == DNS_FAMILY_V4 then
      if b4 == 0 && b5 == 0 && b6 == 0 && b7 == 0 && b8 == 0 && b9 == 0 &&
          b10 == 0 && b11 == 0 && b12 == 0 && b13 == 0 && b14 == 0 && b15 == 0 &&
          s0 == 0 && s1 == 0 && s2 == 0 && s3 == 0 then
        match decodeRecordsList rest with
        | .ok tail => .ok (.ipv4 b0 b1 b2 b3 :: tail)
        | .error e => .error e
      else
        .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
                 message := "non-zero padding or scope in IPv4 DNS record" }
    else if tag == DNS_FAMILY_V6 then
      match decodeRecordsList rest with
      | .ok tail =>
        .ok (.ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 (decodeUInt32LE s0 s1 s2 s3) :: tail)
      | .error e => .error e
    else
      .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
               message := s!"invalid DNS record family tag {tag.toNat}" }
  | _ =>
    .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
             message := "truncated DNS record payload" }

private theorem decodeUInt32LE_encodeUInt32LE (v : UInt32) :
    decodeUInt32LE
      (UInt8.ofNat (v.toNat % 256))
      (UInt8.ofNat ((v.toNat / 256) % 256))
      (UInt8.ofNat ((v.toNat / 65536) % 256))
      (UInt8.ofNat ((v.toNat / 16777216) % 256)) = v := by
  have hv : v.toNat < 4294967296 := v.toBitVec.isLt
  have hnat :
      (v.toNat % 256) +
        256 * ((v.toNat / 256) % 256 +
          256 * ((v.toNat / 65536) % 256 +
            256 * ((v.toNat / 16777216) % 256))) = v.toNat := by
    omega
  unfold decodeUInt32LE
  simp only [UInt8.toNat_ofNat', Nat.mod_mod]
  rw [hnat, UInt32.ofNat_toNat]

private theorem encodeUInt32LEList_decodeUInt32LE (b0 b1 b2 b3 : UInt8) :
    encodeUInt32LEList (decodeUInt32LE b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have hb2 : b2.toNat < 256 := b2.toBitVec.isLt
  have hb3 : b3.toNat < 256 := b3.toBitVec.isLt
  have hsum : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) < 4294967296 := by
    omega
  have hto : (decodeUInt32LE b0 b1 b2 b3).toNat =
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
    unfold decodeUInt32LE
    exact Nat.mod_eq_of_lt hsum
  unfold encodeUInt32LEList
  rw [hto]
  have h0 : (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) % 256 = b0.toNat := by omega
  have h1 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 256) % 256 = b1.toNat := by omega
  have h2 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 65536) % 256 = b2.toNat := by omega
  have h3 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 16777216) % 256 = b3.toNat := by omega
  simp only [h0, h1, h2, h3, UInt8.ofNat_toNat]

private theorem wireAddrBytes_length (a : DnsAddr) :
    (wireAddrBytes a).length = DNS_RECORD_SIZE := by
  cases a <;> rfl

private theorem flatMap_wireAddrBytes_length (addrs : List DnsAddr) :
    (addrs.flatMap wireAddrBytes).length = addrs.length * DNS_RECORD_SIZE := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, wireAddrBytes_length, ih, List.length_cons,
      DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE]
    omega

/-- `encodeRecords addrs` has exact byte size `addrs.length * DNS_RECORD_SIZE` (`21` bytes per record). -/
theorem encodeRecords_size (addrs : List DnsAddr) :
    (encodeRecords addrs).size = addrs.length * DNS_RECORD_SIZE := by
  rw [ByteArray.size, ← Array.length_toList, encodeWireRecords_data_toList, flatMap_wireAddrBytes_length]

private theorem decodeRecordsList_short :
    ∀ (xs : List UInt8), xs ≠ [] → xs.length < 21 →
      decodeRecordsList xs = .error
        { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
          message := "truncated DNS record payload" }
  | [], hne, _ => absurd rfl hne
  | [_], _, _ | [_, _], _, _ | [_, _, _], _, _ | [_, _, _, _], _, _ | [_, _, _, _, _], _, _
  | [_, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, hlt => by
    simp at hlt
    omega

private theorem drop_21_eq (xs : List UInt8) (idx : Nat) (h : idx + 21 ≤ xs.length) :
    xs.drop idx =
      xs[idx] :: xs[idx + 1] :: xs[idx + 2] :: xs[idx + 3] :: xs[idx + 4] ::
      xs[idx + 5] :: xs[idx + 6] :: xs[idx + 7] :: xs[idx + 8] :: xs[idx + 9] ::
      xs[idx + 10] :: xs[idx + 11] :: xs[idx + 12] :: xs[idx + 13] :: xs[idx + 14] ::
      xs[idx + 15] :: xs[idx + 16] :: xs[idx + 17] :: xs[idx + 18] :: xs[idx + 19] ::
      xs[idx + 20] :: xs.drop (idx + 21) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]

private theorem byte_get_eq_toList (bytes : ByteArray) (i : Nat) (h : i < bytes.size) :
    bytes[i] = bytes.data.toList[i]'(by rw [Array.length_toList]; exact h) :=
  rfl

private theorem decodeRecordsLoop_eq_aux (bytes : ByteArray) :
    ∀ (n idx : Nat) (acc : List DnsAddr),
      idx ≤ bytes.size →
      bytes.size - idx = n →
      decodeRecordsLoop bytes idx acc =
        match decodeRecordsList (bytes.data.toList.drop idx) with
        | .ok xs => .ok (acc.reverse ++ xs)
        | .error e => .error e := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro idx acc hle hrem
    unfold decodeRecordsLoop
    by_cases hEnd : idx = bytes.size
    · have hbeq : (idx == bytes.size) = true := beq_iff_eq.mpr hEnd
      have hdrop : bytes.data.toList.drop idx = [] := by
        rw [List.drop_eq_nil_iff, Array.length_toList]
        simp only [ByteArray.size] at hEnd
        exact Nat.le_of_eq hEnd.symm
      simp [hbeq, hdrop, decodeRecordsList]
    · have hbeq : (idx == bytes.size) = false := beq_false_of_ne hEnd
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      by_cases hFull : idx + DNS_RECORD_SIZE ≤ bytes.size
      · simp only [hFull, ↓reduceDIte]
        have hlen21 : idx + 21 ≤ bytes.data.toList.length := by
          rw [Array.length_toList, ← ByteArray.size]
          simpa [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] using hFull
        have hdrop := drop_21_eq bytes.data.toList idx hlen21
        rw [hdrop]
        have hih := ih (bytes.size - (idx + DNS_RECORD_SIZE))
          (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) (idx + DNS_RECORD_SIZE)
        unfold decodeRecordAt decodeRecordsList
        simp only [byte_get_eq_toList]
        by_cases h4 : bytes.data.toList[idx]'(by omega) = DNS_FAMILY_V4
        · have ht4 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V4) = true := beq_iff_eq.mpr h4
          simp only [ht4, ↓reduceIte]
          by_cases hpad :
              ((bytes.data.toList[idx + 5]'(by omega) == 0 &&
                bytes.data.toList[idx + 6]'(by omega) == 0 &&
                bytes.data.toList[idx + 7]'(by omega) == 0 &&
                bytes.data.toList[idx + 8]'(by omega) == 0 &&
                bytes.data.toList[idx + 9]'(by omega) == 0 &&
                bytes.data.toList[idx + 10]'(by omega) == 0 &&
                bytes.data.toList[idx + 11]'(by omega) == 0 &&
                bytes.data.toList[idx + 12]'(by omega) == 0 &&
                bytes.data.toList[idx + 13]'(by omega) == 0 &&
                bytes.data.toList[idx + 14]'(by omega) == 0 &&
                bytes.data.toList[idx + 15]'(by omega) == 0 &&
                bytes.data.toList[idx + 16]'(by omega) == 0 &&
                bytes.data.toList[idx + 17]'(by omega) == 0 &&
                bytes.data.toList[idx + 18]'(by omega) == 0 &&
                bytes.data.toList[idx + 19]'(by omega) == 0 &&
                bytes.data.toList[idx + 20]'(by omega) == 0) = true)
          · simp only [hpad, ↓reduceIte]
            have hrec := hih (acc := DnsAddr.ipv4
              (bytes.data.toList[idx + 1]'(by omega))
              (bytes.data.toList[idx + 2]'(by omega))
              (bytes.data.toList[idx + 3]'(by omega))
              (bytes.data.toList[idx + 4]'(by omega)) :: acc)
              (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) rfl
            simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at hrec ⊢
            rw [hrec]
            cases decodeRecordsList (bytes.data.toList.drop (idx + 21)) with
            | ok tail => simp [List.reverse_cons, List.append_assoc]
            | error e => rfl
          · simp only [hpad, Bool.false_eq_true, ↓reduceIte]
        · have ht4 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V4) = false := beq_false_of_ne h4
          simp only [ht4, Bool.false_eq_true, ↓reduceIte]
          by_cases h6 : bytes.data.toList[idx]'(by omega) = DNS_FAMILY_V6
          · have ht6 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V6) = true := beq_iff_eq.mpr h6
            simp only [ht6, ↓reduceIte]
            have hrec := hih (acc := DnsAddr.ipv6
              (bytes.data.toList[idx + 1]'(by omega))
              (bytes.data.toList[idx + 2]'(by omega))
              (bytes.data.toList[idx + 3]'(by omega))
              (bytes.data.toList[idx + 4]'(by omega))
              (bytes.data.toList[idx + 5]'(by omega))
              (bytes.data.toList[idx + 6]'(by omega))
              (bytes.data.toList[idx + 7]'(by omega))
              (bytes.data.toList[idx + 8]'(by omega))
              (bytes.data.toList[idx + 9]'(by omega))
              (bytes.data.toList[idx + 10]'(by omega))
              (bytes.data.toList[idx + 11]'(by omega))
              (bytes.data.toList[idx + 12]'(by omega))
              (bytes.data.toList[idx + 13]'(by omega))
              (bytes.data.toList[idx + 14]'(by omega))
              (bytes.data.toList[idx + 15]'(by omega))
              (bytes.data.toList[idx + 16]'(by omega))
              (decodeUInt32LE
                (bytes.data.toList[idx + 17]'(by omega))
                (bytes.data.toList[idx + 18]'(by omega))
                (bytes.data.toList[idx + 19]'(by omega))
                (bytes.data.toList[idx + 20]'(by omega))) :: acc)
              (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) rfl
            simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at hrec ⊢
            rw [hrec]
            cases decodeRecordsList (bytes.data.toList.drop (idx + 21)) with
            | ok tail => simp [List.reverse_cons, List.append_assoc]
            | error e => rfl
          · have ht6 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V6) = false := beq_false_of_ne h6
            simp only [ht6, Bool.false_eq_true, ↓reduceIte]
      · simp only [hFull, ↓reduceDIte]
        have hltLen : (bytes.data.toList.drop idx).length < 21 := by
          rw [List.length_drop, Array.length_toList]
          simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE, ByteArray.size] at hFull ⊢
          omega
        have hneDrop : bytes.data.toList.drop idx ≠ [] := by
          intro he
          rw [List.drop_eq_nil_iff, Array.length_toList] at he
          simp only [ByteArray.size] at hle hEnd he
          omega
        rw [decodeRecordsList_short _ hneDrop hltLen]

private theorem decodeRecords_eq_list (bytes : ByteArray) :
    decodeRecords bytes = decodeRecordsList bytes.data.toList := by
  unfold decodeRecords
  rw [decodeRecordsLoop_eq_aux bytes (bytes.size - 0) 0 [] (Nat.zero_le _) rfl]
  simp only [List.drop_zero, List.reverse_nil, List.nil_append]
  cases decodeRecordsList bytes.data.toList <;> rfl

private theorem decodeRecordsList_wireAddrBytes_append (a : DnsAddr) (tailBytes : List UInt8) :
    decodeRecordsList (wireAddrBytes a ++ tailBytes) =
      match decodeRecordsList tailBytes with
      | .ok tail => .ok (a :: tail)
      | .error e => .error e := by
  cases a with
  | ipv4 b0 b1 b2 b3 => rfl
  | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    simp only [wireAddrBytes, List.cons_append, List.nil_append]
    conv => lhs; unfold decodeRecordsList
    have ht4 : ((6 : UInt8) == DNS_FAMILY_V4) = false := by decide
    have ht6 : ((6 : UInt8) == DNS_FAMILY_V6) = true := by decide
    simp only [ht4, Bool.false_eq_true, ↓reduceIte, ht6, decodeUInt32LE_encodeUInt32LE]

private theorem decodeRecordsList_flatMap_wireAddrBytes (addrs : List DnsAddr) :
    decodeRecordsList (addrs.flatMap wireAddrBytes) = .ok addrs := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp [List.flatMap_cons, decodeRecordsList_wireAddrBytes_append, ih]

/-- `decodeRecords` cleanly round-trips `encodeRecords` for every `List DnsAddr`. -/
theorem decodeRecords_encodeRecords (addrs : List DnsAddr) :
    decodeRecords (encodeRecords addrs) = .ok addrs := by
  rw [decodeRecords_eq_list, encodeWireRecords_data_toList, decodeRecordsList_flatMap_wireAddrBytes]

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

private theorem classifyGaiKind_ne_invalidHost (rc : Int32) :
    classifyGaiKind rc ≠ .invalidHost := by
  unfold classifyGaiKind
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem normalizeGaiCodeForHost_invariants (host : String) (hints : ResolveHints) (rc : Int32) :
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

private theorem dnsErrorKind_beq_refl (k : DnsErrorKind) : (k == k) = true := by
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
  simp [hnv, classifyGaiError, decodeErrorMessage]

end LeanSwe.LinuxSyscall.Dns.Internal

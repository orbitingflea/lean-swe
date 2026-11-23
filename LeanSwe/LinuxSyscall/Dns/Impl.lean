import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.Dns.Model

namespace LeanSwe.LinuxSyscall.Dns.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- Fixed byte width of each serialized address record emitted by `c/dns_shim.c`. -/
abbrev DNS_RECORD_SIZE : Nat := Dns.DNS_RECORD_SIZE

/-- Wire-format family tag for IPv4 address records emitted by `c/dns_shim.c`. -/
def DNS_FAMILY_V4 : UInt8 := 4

/-- Wire-format family tag for IPv6 address records emitted by `c/dns_shim.c`. -/
def DNS_FAMILY_V6 : UInt8 := 6

/-- Safely decode raw diagnostic error bytes from `getaddrinfo(3)` / `gai_strerror(3)`. -/
def decodeErrorMessage (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s =>
    if s.isEmpty then "getaddrinfo failed" else s
  | none =>
    s!"<non-utf8:{bytes.size}B>"

/-- Construct a normalized `DnsError` from raw `leanswe_sys_getaddrinfo` failure outputs. -/
def classifyGaiError (host : String) (hints : ResolveHints)
    (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) : DnsError :=
  let rc' := normalizeGaiCodeForHost host hints rc
  let kind := classifyGaiKind rc'
  let errno? : Option Errno :=
    if rc' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
  { kind := kind
    gaiCode := rc'
    errno? := errno?
    message := decodeErrorMessage msgBytes }

/-- Decode 4 little-endian wire bytes into a `UInt32` IPv6 scope ID. -/
def decodeUInt32LE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)))

/-- Serialize a list of `DnsAddr` values into concatenated 21-byte `ByteArray` records (`Types.encodeWireRecords`). -/
abbrev encodeRecords (addrs : List DnsAddr) : ByteArray :=
  encodeWireRecords addrs

/-- Decode one 21-byte wire record starting at byte offset `idx` in `bytes`. -/
def decodeRecordAt (bytes : ByteArray) (idx : Nat) (h : idx + DNS_RECORD_SIZE ≤ bytes.size) :
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

/-- Iteratively decode concatenated 21-byte wire records starting at offset `idx`. -/
def decodeRecordsLoop (bytes : ByteArray) (idx : Nat) (acc : List DnsAddr) :
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

end LeanSwe.LinuxSyscall.Dns.Internal

import LeanSweProofs.LinuxSyscall.Dns.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.Dns`

Defines raw C-ABI wire decoders (`decodeRawFamily?`, `decodeRawSockType?`,
`decodeRawHints?`, `decodeRawErrorMessage`, `rawGaiErrorToDnsError`), the raw
single-step contract (`RawDnsReq`, `RawDnsOut`, `execRawStep`, `allowedRawStep`,
`rawHealthyModelOps`), and package-level single-step entry points (`execPkgStep`,
`allowedPkgStep`) over `HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.Dns.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Decode a portable `AddrFamilyHint` wire byte (`0 = any`, `1 = ipv4`, `2 = ipv6`). -/
def decodeRawFamily? : UInt8 → Option AddrFamilyHint
  | 0 => some .any
  | 1 => some .ipv4
  | 2 => some .ipv6
  | _ => none

/-- Decode a portable `SockTypeHint` wire byte (`0 = any`, `1 = stream`, `2 = dgram`). -/
def decodeRawSockType? : UInt8 → Option SockTypeHint
  | 0 => some .any
  | 1 => some .stream
  | 2 => some .dgram
  | _ => none

/-- Decode raw `(familyWire, sockTypeWire)` bytes into `ResolveHints`. -/
def decodeRawHints? (famWire sockWire : UInt8) : Option ResolveHints :=
  match decodeRawFamily? famWire, decodeRawSockType? sockWire with
  | some fam, some st => some { family := fam, sockType := st }
  | _, _ => none

/-- Safely decode raw UTF-8 diagnostic bytes from `getaddrinfo(3)` / `gai_strerror(3)`. -/
def decodeRawErrorMessage (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s => if s.isEmpty then "getaddrinfo failed" else s
  | none => s!"<non-utf8:{bytes.size}B>"

/-- Normalize raw `(gaiCode, errno, msgBytes)` failure outputs into a structured `DnsError`. -/
def rawGaiErrorToDnsError (host : String) (hints : ResolveHints)
    (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) : DnsError :=
  let rc' := normalizeGaiCodeForHost host hints rc
  { kind := classifyGaiKind rc'
    gaiCode := rc'
    errno? := if rc' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
    message := decodeRawErrorMessage msgBytes }

/-- Single-step request record for `Internal.PosixDnsOpsM` C-ABI hooks. -/
structure RawDnsReq where
  /-- Hostname or IP literal passed to `leanswe_sys_getaddrinfo`. -/
  host : String := ""
  /-- Encoded `AddrFamilyHint` wire tag. -/
  familyWire : UInt8 := 0
  /-- Encoded `SockTypeHint` wire tag. -/
  sockTypeWire : UInt8 := 1
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Single-step output type for `Internal.PosixDnsOpsM` C-ABI hooks. -/
abbrev RawDnsOut : Type :=
  Except (Int32 × UInt32 × ByteArray) ByteArray

/-- Execute one `RawDnsReq` against an `Internal.PosixDnsOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : Internal.PosixDnsOpsM (StateM W)) (req : RawDnsReq) :
    StateM W RawDnsOut :=
  raw.getaddrinfo req.host req.familyWire req.sockTypeWire

/-- Allowed single-step relation for `Internal.PosixDnsOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawDnsReq) (out : RawDnsOut)
    (env' : HealthyEnv) : Prop :=
  if validateHost req.host then
    match decodeRawHints? req.familyWire req.sockTypeWire with
    | some hints =>
      match out with
      | .ok recBytes =>
        ∃ addrs : List DnsAddr,
          recBytes = encodeWireRecords addrs ∧
          healthyStep env { host := req.host, hints := hints } (.ok addrs) = some env'
      | .error (rc, eno, msgBytes) =>
        healthyStep env { host := req.host, hints := hints }
          (.error (rawGaiErrorToDnsError req.host hints rc eno msgBytes)) = some env'
    | none =>
      (∃ rc eno msgBytes, out = .error (rc, eno, msgBytes)) ∧ env' = env
  else
    (∃ rc eno msgBytes, out = .error (rc, eno, msgBytes)) ∧ env' = env

/-- Reference `Internal.PosixDnsOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : Internal.PosixDnsOpsM (StateM HealthyEnv) :=
  { getaddrinfo := fun host famWire sockWire =>
      if validateHost host then
        match decodeRawHints? famWire sockWire with
        | some hints => do
          match ← healthyModelOps.getaddrinfo host hints with
          | .ok addrs => return .ok (encodeWireRecords addrs)
          | .error err => return .error (err.gaiCode, err.errno?.getD 0, err.message.toUTF8)
        | none => pure (.error (EAI_FAIL, 0, "invalid raw dns hints".toUTF8))
      else
        pure (.error (EAI_NONAME, Errno.EINVAL, "invalid hostname".toUTF8)) }

/-- Execute one `DnsReq` against a `DnsOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : DnsOpsM (StateM W)) (req : DnsReq) :
    StateM W DnsOutcome :=
  execDnsReq ops req

/-- Allowed single-step relation for `DnsOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : DnsReq) (out : DnsOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

end LeanSwe.LinuxSyscall.Dns.Model

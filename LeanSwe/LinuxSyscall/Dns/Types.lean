import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Dns

open LeanSwe.LinuxSyscall

/-- Linux `<netdb.h>` `EAI_BADFLAGS` error code. -/
def EAI_BADFLAGS : Int32 := -1

/-- Linux `<netdb.h>` `EAI_NONAME` error code. -/
def EAI_NONAME : Int32 := -2

/-- Linux `<netdb.h>` `EAI_AGAIN` error code. -/
def EAI_AGAIN : Int32 := -3

/-- Linux `<netdb.h>` `EAI_FAIL` error code. -/
def EAI_FAIL : Int32 := -4

/-- Linux `<netdb.h>` `EAI_NODATA` error code. -/
def EAI_NODATA : Int32 := -5

/-- Linux `<netdb.h>` `EAI_FAMILY` error code. -/
def EAI_FAMILY : Int32 := -6

/-- Linux `<netdb.h>` `EAI_SOCKTYPE` error code. -/
def EAI_SOCKTYPE : Int32 := -7

/-- Linux `<netdb.h>` `EAI_SERVICE` error code. -/
def EAI_SERVICE : Int32 := -8

/-- Linux `<netdb.h>` `EAI_ADDRFAMILY` error code. -/
def EAI_ADDRFAMILY : Int32 := -9

/-- Linux `<netdb.h>` `EAI_MEMORY` error code. -/
def EAI_MEMORY : Int32 := -10

/-- Linux `<netdb.h>` `EAI_SYSTEM` error code. -/
def EAI_SYSTEM : Int32 := -11

/-- Linux `<netdb.h>` `EAI_OVERFLOW` error code. -/
def EAI_OVERFLOW : Int32 := -12

/-- Address family hint passed to `getaddrinfo(3)`. -/
inductive AddrFamilyHint where
  /-- Allow either IPv4 or IPv6 (`AF_UNSPEC`). -/
  | any
  /-- Restrict resolution to IPv4 (`AF_INET`). -/
  | ipv4
  /-- Restrict resolution to IPv6 (`AF_INET6`). -/
  | ipv6
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Socket type hint passed to `getaddrinfo(3)`. -/
inductive SockTypeHint where
  /-- Do not constrain socket type (`ai_socktype = 0`). -/
  | any
  /-- Stream sockets (`SOCK_STREAM`). -/
  | stream
  /-- Datagram sockets (`SOCK_DGRAM`). -/
  | dgram
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Hints controlling `getaddrinfo(3)` resolution (`AF_UNSPEC` and `SOCK_STREAM` by default). -/
structure ResolveHints where
  /-- Desired address family constraint. -/
  family : AddrFamilyHint := .any
  /-- Desired socket type constraint. -/
  sockType : SockTypeHint := .stream
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Encode `AddrFamilyHint` into its C-shim byte tag (`0 = AF_UNSPEC`, `1 = AF_INET`, `2 = AF_INET6`). -/
def AddrFamilyHint.toWire : AddrFamilyHint → UInt8
  | .any => 0
  | .ipv4 => 1
  | .ipv6 => 2

/-- Encode `SockTypeHint` into its C-shim byte tag (`0 = any`, `1 = SOCK_STREAM`, `2 = SOCK_DGRAM`). -/
def SockTypeHint.toWire : SockTypeHint → UInt8
  | .any => 0
  | .stream => 1
  | .dgram => 2

/-- Pure representation of a resolved IPv4 or IPv6 address (preserving `sin6_scope_id` for scoped IPv6). -/
inductive DnsAddr where
  /-- IPv4 address octets in network byte order (`b0.b1.b2.b3`). -/
  | ipv4 (b0 b1 b2 b3 : UInt8)
  /-- IPv6 address bytes in network byte order (`b0..b15`) and interface scope ID (`sin6_scope_id`). -/
  | ipv6 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) (scopeId : UInt32 := 0)
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Return the IPv6 scope ID (`0` for IPv4 or unscoped IPv6). -/
def DnsAddr.scopeId : DnsAddr → UInt32
  | .ipv4 _ _ _ _ => 0
  | .ipv6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc => sc

/-- Return `true` iff `a` has zero interface scope ID (`scopeId == 0`). -/
def DnsAddr.isUnscoped (a : DnsAddr) : Bool :=
  a.scopeId == 0

/-- Return `true` iff `a` is an IPv4 address. -/
def DnsAddr.isIpv4 : DnsAddr → Bool
  | .ipv4 _ _ _ _ => true
  | .ipv6 .. => false

/-- Return `true` iff `a` is an IPv6 address. -/
def DnsAddr.isIpv6 : DnsAddr → Bool
  | .ipv4 _ _ _ _ => false
  | .ipv6 .. => true

/-- Extract the 4 IPv4 network-order octets if `a` is `.ipv4`. -/
def DnsAddr.ipv4Bytes? : DnsAddr → Option (UInt8 × UInt8 × UInt8 × UInt8)
  | .ipv4 b0 b1 b2 b3 => some (b0, b1, b2, b3)
  | .ipv6 .. => none

/-- Extract the 16-byte network-order IPv6 address and `scopeId` if `a` is `.ipv6`. -/
def DnsAddr.ipv6Bytes? : DnsAddr → Option (ByteArray × UInt32)
  | .ipv4 _ _ _ _ => none
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    some (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], sc)

/-- Format a single `DnsAddr` in canonical dotted-quad (IPv4) or full hex-group (IPv6, with `%<scopeId>` when non-zero) notation. -/
def DnsAddr.format : DnsAddr → String
  | .ipv4 b0 b1 b2 b3 => s!"{b0.toNat}.{b1.toNat}.{b2.toNat}.{b3.toNat}"
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    let hexByte (x : UInt8) : String :=
      let hi := Nat.digitChar (x.toNat / 16)
      let lo := Nat.digitChar (x.toNat % 16)
      String.ofList [hi, lo]
    let seg (hi lo : UInt8) : String := hexByte hi ++ hexByte lo
    let base := String.intercalate ":"
      [ seg b0 b1, seg b2 b3, seg b4 b5, seg b6 b7
      , seg b8 b9, seg b10 b11, seg b12 b13, seg b14 b15 ]
    if sc == 0 then base else s!"{base}%{sc}"

/-- Return `true` iff `a` is an unscoped IPv4 (`127.0.0.0/8`) or IPv6 (`::1`) loopback address. -/
def DnsAddr.isLoopback : DnsAddr → Bool
  | .ipv4 b0 _ _ _ => b0 == 127
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    sc == 0 &&
    b0 == 0 && b1 == 0 && b2 == 0 && b3 == 0 &&
    b4 == 0 && b5 == 0 && b6 == 0 && b7 == 0 &&
    b8 == 0 && b9 == 0 && b10 == 0 && b11 == 0 &&
    b12 == 0 && b13 == 0 && b14 == 0 && b15 == 1

/-- Return `true` iff `a` satisfies the address-family constraint in `hints`. -/
def addrMatchesHints (hints : ResolveHints) (a : DnsAddr) : Bool :=
  match hints.family with
  | .any => true
  | .ipv4 => a.isIpv4
  | .ipv6 => a.isIpv6

/-- Return `true` iff `host` is non-empty and free of embedded NUL (`\x00`) bytes. -/
def validateHost (host : String) : Bool :=
  !host.isEmpty && !host.any (· == '\x00')

/-- Semantic error category for `LeanSwe.LinuxSyscall.Dns` operations. -/
inductive DnsErrorKind where
  /-- Empty hostname or hostname containing an embedded NUL byte. -/
  | invalidHost
  /-- Hostname is syntactically valid but did not resolve (`EAI_NONAME`, `EAI_NODATA`, `EAI_FAIL`). -/
  | nameNotFound
  /-- Transient resolution failure (`EAI_AGAIN`). -/
  | temporaryFailure
  /-- OS or memory failure (`EAI_SYSTEM`, `EAI_MEMORY`). -/
  | systemError
  /-- Other `getaddrinfo(3)` `EAI_*` failure code. -/
  | otherGai
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Map a `getaddrinfo(3)` `EAI_*` error code to its semantic `DnsErrorKind` (never `.invalidHost`). -/
def classifyGaiKind (rc : Int32) : DnsErrorKind :=
  if rc == EAI_NONAME || rc == EAI_NODATA || rc == EAI_FAIL then
    .nameNotFound
  else if rc == EAI_AGAIN then
    .temporaryFailure
  else if rc == EAI_SYSTEM || rc == EAI_MEMORY then
    .systemError
  else
    .otherGai

/-- Structured error returned by `LeanSwe.LinuxSyscall.Dns` operations. -/
structure DnsError where
  /-- Semantic error category. -/
  kind : DnsErrorKind
  /-- Raw `getaddrinfo(3)` `EAI_*` return code. -/
  gaiCode : Int32
  /-- Captured `Errno` (`Errno.EINVAL` for invalid host; `saved_errno` for `EAI_SYSTEM`). -/
  errno? : Option Errno
  /-- Safely UTF-8 decoded diagnostic message. -/
  message : String
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Canonical `DnsError` for rejected empty or NUL-containing hostnames (`EAI_NONAME` / `EINVAL`). -/
def invalidHostError : DnsError :=
  { kind := .invalidHost
    gaiCode := EAI_NONAME
    errno? := some Errno.EINVAL
    message := "invalid hostname: empty or contains NUL byte" }

/-- Public capability record for standalone DNS name resolution. -/
structure DnsOpsM (m : Type → Type) where
  /-- Resolve `host` under `hints` into IPv4/IPv6 addresses (`DnsAddr`) or a structured `DnsError`. -/
  getaddrinfo : String → (hints : ResolveHints := {}) → m (Except DnsError (List DnsAddr))

/-- Specialized `IO` signature for `DnsOpsM`. -/
abbrev DnsOps := DnsOpsM IO

/-- Fixed byte width of each serialized address record emitted by `c/dns_shim.c`. -/
def DNS_RECORD_SIZE : Nat := 21

private def WIRE_FAMILY_V4 : UInt8 := 4

private def WIRE_FAMILY_V6 : UInt8 := 6

private def pushWireUInt32LE (acc : ByteArray) (v : UInt32) : ByteArray :=
  let n := v.toNat
  acc
    |>.push (UInt8.ofNat (n % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 16777216) % 256))

private def pushWireAddr (acc : ByteArray) : DnsAddr → ByteArray
  | .ipv4 b0 b1 b2 b3 =>
    acc
      |>.push WIRE_FAMILY_V4 |>.push b0 |>.push b1 |>.push b2 |>.push b3
      |>.push 0 |>.push 0 |>.push 0 |>.push 0
      |>.push 0 |>.push 0 |>.push 0 |>.push 0
      |>.push 0 |>.push 0 |>.push 0 |>.push 0
      |>.push 0 |>.push 0 |>.push 0 |>.push 0
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    let base := acc
      |>.push WIRE_FAMILY_V6
      |>.push b0 |>.push b1 |>.push b2 |>.push b3
      |>.push b4 |>.push b5 |>.push b6 |>.push b7
      |>.push b8 |>.push b9 |>.push b10 |>.push b11
      |>.push b12 |>.push b13 |>.push b14 |>.push b15
    pushWireUInt32LE base sc

private def encodeWireRecordsLoop : List DnsAddr → ByteArray → ByteArray
  | [], acc => acc
  | a :: rest, acc => encodeWireRecordsLoop rest (pushWireAddr acc a)

/-- Serialize a list of `DnsAddr` values into concatenated 21-byte wire records (`c/dns_shim.c` layout). -/
def encodeWireRecords (addrs : List DnsAddr) : ByteArray :=
  encodeWireRecordsLoop addrs (ByteArray.emptyWithCapacity (addrs.length * DNS_RECORD_SIZE))

/-- Canonical 21-byte wire serialization for a single `DnsAddr` (`c/dns_shim.c` layout). -/
def wireAddrBytes : DnsAddr → List UInt8
  | .ipv4 b0 b1 b2 b3 =>
    [4, b0, b1, b2, b3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    let n := sc.toNat
    [6, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
     UInt8.ofNat ((n / 65536) % 256), UInt8.ofNat ((n / 16777216) % 256)]

private theorem push_wire_toList (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  simp [ByteArray.push]

private theorem pushWireAddr_data_toList (acc : ByteArray) (a : DnsAddr) :
    (pushWireAddr acc a).data.toList = acc.data.toList ++ wireAddrBytes a := by
  cases a with
  | ipv4 b0 b1 b2 b3 =>
    unfold pushWireAddr wireAddrBytes
    simp only [WIRE_FAMILY_V4, push_wire_toList, List.append_assoc, List.cons_append, List.nil_append]
  | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    unfold pushWireAddr pushWireUInt32LE wireAddrBytes
    simp only [WIRE_FAMILY_V6, push_wire_toList, List.append_assoc, List.cons_append, List.nil_append]

private theorem encodeWireRecordsLoop_data_toList (addrs : List DnsAddr) (acc : ByteArray) :
    (encodeWireRecordsLoop addrs acc).data.toList = acc.data.toList ++ addrs.flatMap wireAddrBytes := by
  induction addrs generalizing acc with
  | nil => simp [encodeWireRecordsLoop]
  | cons a rest ih =>
    simp [encodeWireRecordsLoop, ih, pushWireAddr_data_toList, List.flatMap_cons, List.append_assoc]

/-- Every `encodeWireRecords addrs` buffer equals `addrs.flatMap wireAddrBytes` byte-for-byte. -/
theorem encodeWireRecords_data_toList (addrs : List DnsAddr) :
    (encodeWireRecords addrs).data.toList = addrs.flatMap wireAddrBytes := by
  unfold encodeWireRecords
  rw [encodeWireRecordsLoop_data_toList]
  rfl

end LeanSwe.LinuxSyscall.Dns

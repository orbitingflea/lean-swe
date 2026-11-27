import LeanSwe.LinuxSyscall.Dns.Types

namespace LeanSwe.LinuxSyscall.Dns.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- Fixed byte width of each serialized address record emitted by `c/dns_shim.c`. -/
abbrev DNS_RECORD_SIZE : Nat := Dns.DNS_RECORD_SIZE

/-- Wire-format family tag for IPv4 address records emitted by `c/dns_shim.c`. -/
def DNS_FAMILY_V4 : UInt8 := 4

/-- Wire-format family tag for IPv6 address records emitted by `c/dns_shim.c`. -/
def DNS_FAMILY_V6 : UInt8 := 6

/-- Return `true` iff `rc` is a reachable Linux `<netdb.h>` `getaddrinfo(3)` error code for `ai_flags = 0` and `service = NULL`. -/
def isValidGaiCodeImpl (rc : Int32) : Bool :=
  EAI_OVERFLOW ≤ rc && rc ≤ EAI_NONAME && rc != EAI_SERVICE

/-- Decode a single ASCII hexadecimal digit into `0..15`. -/
def hexValImpl? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse unsigned integer digits in `base` bounded above by `maxVal`. -/
def parseUintDigitsImpl? (base : Nat) (maxVal : Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => do
    let d ← hexValImpl? c
    if d ≥ base then none
    let nxt := acc * base + d
    if nxt > maxVal then none
    parseUintDigitsImpl? base maxVal cs nxt

/-- Tail-recursive worker splitting a character list on `sep`. -/
def splitCharListAuxImpl (sep : Char) : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
    if c == sep then
      splitCharListAuxImpl sep cs [] (cur.reverse :: acc)
    else
      splitCharListAuxImpl sep cs (c :: cur) acc

/-- Split `cs` on separator character `sep`. -/
def splitCharListImpl (sep : Char) (cs : List Char) : List (List Char) :=
  splitCharListAuxImpl sep cs [] []

/-- Tail-recursive worker splitting a character list on `"::"`. -/
def splitDoubleColonAuxImpl : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | ':' :: ':' :: cs, cur, acc =>
    splitDoubleColonAuxImpl cs [] (cur.reverse :: acc)
  | c :: cs, cur, acc =>
    splitDoubleColonAuxImpl cs (c :: cur) acc

/-- Split `cs` on `"::"` runs. -/
def splitDoubleColonCharsImpl (cs : List Char) : List (List Char) :=
  splitDoubleColonAuxImpl cs [] []

/-- Parse one `inet_aton(3)` numeric IPv4 component (decimal, octal, or hexadecimal). -/
def parseIpv4AtonPartImpl? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | '0' :: 'x' :: ds | '0' :: 'X' :: ds =>
    if ds.isEmpty then none else parseUintDigitsImpl? 16 0xffffffff ds 0
  | '0' :: ds =>
    parseUintDigitsImpl? 8 0xffffffff ds 0
  | c :: ds =>
    if '1' ≤ c && c ≤ '9' then
      parseUintDigitsImpl? 10 0xffffffff (c :: ds) 0
    else
      none

/-- Parse a 1-to-4-part `inet_aton(3)` IPv4 literal into `DnsAddr`. -/
def parseIpv4AtonImpl? (host : String) : Option DnsAddr := do
  let parts := splitCharListImpl '.' host.toList
  if parts.any (·.isEmpty) then none
  match parts with
  | [aCs] =>
    let a ← parseIpv4AtonPartImpl? aCs
    some (.ipv4
      (UInt8.ofNat ((a >>> 24) &&& 0xff))
      (UInt8.ofNat ((a >>> 16) &&& 0xff))
      (UInt8.ofNat ((a >>> 8) &&& 0xff))
      (UInt8.ofNat (a &&& 0xff)))
  | [aCs, bCs] =>
    let a ← parseIpv4AtonPartImpl? aCs
    let b ← parseIpv4AtonPartImpl? bCs
    if a > 255 || b > 0xffffff then none
    some (.ipv4
      (UInt8.ofNat a)
      (UInt8.ofNat ((b >>> 16) &&& 0xff))
      (UInt8.ofNat ((b >>> 8) &&& 0xff))
      (UInt8.ofNat (b &&& 0xff)))
  | [aCs, bCs, cCs] =>
    let a ← parseIpv4AtonPartImpl? aCs
    let b ← parseIpv4AtonPartImpl? bCs
    let c ← parseIpv4AtonPartImpl? cCs
    if a > 255 || b > 255 || c > 0xffff then none
    some (.ipv4
      (UInt8.ofNat a)
      (UInt8.ofNat b)
      (UInt8.ofNat ((c >>> 8) &&& 0xff))
      (UInt8.ofNat (c &&& 0xff)))
  | [aCs, bCs, cCs, dCs] =>
    let a ← parseIpv4AtonPartImpl? aCs
    let b ← parseIpv4AtonPartImpl? bCs
    let c ← parseIpv4AtonPartImpl? cCs
    let d ← parseIpv4AtonPartImpl? dCs
    if a > 255 || b > 255 || c > 255 || d > 255 then none
    some (.ipv4 (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c) (UInt8.ofNat d))
  | _ => none

/-- Parse a strict decimal IPv4 octet (`0..255`, no leading zeros). -/
def parseStrictDecOctetImpl? (cs : List Char) : Option Nat := do
  if cs.isEmpty || cs.length > 3 then none
  if cs.length > 1 && cs.head? == some '0' then none
  parseUintDigitsImpl? 10 255 cs 0

/-- Parse a strict dotted-quad IPv4 tail into two 16-bit IPv6 hextets. -/
def parseStrictIpv4HextetsImpl? (cs : List Char) : Option (Nat × Nat) := do
  let parts := splitCharListImpl '.' cs
  match parts with
  | [aCs, bCs, cCs, dCs] =>
    let a ← parseStrictDecOctetImpl? aCs
    let b ← parseStrictDecOctetImpl? bCs
    let c ← parseStrictDecOctetImpl? cCs
    let d ← parseStrictDecOctetImpl? dCs
    some ((a <<< 8) ||| b, (c <<< 8) ||| d)
  | _ => none

/-- Parse a 1-to-4-digit hexadecimal IPv6 hextet (`0..0xffff`). -/
def parseHexGroupImpl? (cs : List Char) : Option Nat := do
  if cs.isEmpty || cs.length > 4 then none
  parseUintDigitsImpl? 16 0xffff cs 0

/-- Tail-recursive worker parsing colon-separated IPv6 hextet groups with optional IPv4 tail. -/
def parseIpv6PartsLoopImpl (allowV4Tail : Bool) : List (List Char) → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | [last], acc =>
    if allowV4Tail && last.contains '.' then do
      let (hi, lo) ← parseStrictIpv4HextetsImpl? last
      if acc.length + 2 > 8 then none else some (lo :: hi :: acc).reverse
    else do
      let v ← parseHexGroupImpl? last
      if acc.length ≥ 8 then none else some (v :: acc).reverse
  | p :: rest, acc =>
    if acc.length ≥ 8 then
      none
    else do
      let v ← parseHexGroupImpl? p
      parseIpv6PartsLoopImpl allowV4Tail rest (v :: acc)

/-- Parse colon-separated IPv6 hextet groups (empty input returns `some []`). -/
def parseIpv6PartsImpl? (allowV4Tail : Bool) (cs : List Char) : Option (List Nat) :=
  if cs.isEmpty then
    some []
  else
    let parts := splitCharListImpl ':' cs
    if parts.any (·.isEmpty) then
      none
    else
      parseIpv6PartsLoopImpl allowV4Tail parts []

/-- Parse a non-empty decimal `UInt32` IPv6 zone identifier. -/
def parseNumericZoneImpl? (zoneCs : List Char) : Option UInt32 := do
  if zoneCs.isEmpty then none
  let n ← parseUintDigitsImpl? 10 0xffffffff zoneCs 0
  some (UInt32.ofNat n)

/-- Return `true` iff `a` is an IPv4-mapped IPv6 address (`::ffff:0:0/96`). -/
def isIpv4MappedAddrImpl : DnsAddr → Bool
  | .ipv6 0 0 0 0 0 0 0 0 0 0 0xff 0xff _ _ _ _ _ => true
  | _ => false

/-- Tail-recursive worker splitting a host string at its first `'%'` zone separator. -/
def splitFirstZoneAuxImpl : List Char → List Char → List Char × Option (List Char)
  | [], acc => (acc.reverse, none)
  | '%' :: rest, acc => (acc.reverse, some rest)
  | c :: rest, acc => splitFirstZoneAuxImpl rest (c :: acc)

/-- Construct an `.ipv6` `DnsAddr` from 8 16-bit big-endian words and `scopeId`. -/
def wordsToIpv6AddrImpl (ws : List Nat) (sc : UInt32) : Option DnsAddr :=
  match ws with
  | [w0, w1, w2, w3, w4, w5, w6, w7] =>
    some (.ipv6
      (UInt8.ofNat ((w0 >>> 8) &&& 0xff)) (UInt8.ofNat (w0 &&& 0xff))
      (UInt8.ofNat ((w1 >>> 8) &&& 0xff)) (UInt8.ofNat (w1 &&& 0xff))
      (UInt8.ofNat ((w2 >>> 8) &&& 0xff)) (UInt8.ofNat (w2 &&& 0xff))
      (UInt8.ofNat ((w3 >>> 8) &&& 0xff)) (UInt8.ofNat (w3 &&& 0xff))
      (UInt8.ofNat ((w4 >>> 8) &&& 0xff)) (UInt8.ofNat (w4 &&& 0xff))
      (UInt8.ofNat ((w5 >>> 8) &&& 0xff)) (UInt8.ofNat (w5 &&& 0xff))
      (UInt8.ofNat ((w6 >>> 8) &&& 0xff)) (UInt8.ofNat (w6 &&& 0xff))
      (UInt8.ofNat ((w7 >>> 8) &&& 0xff)) (UInt8.ofNat (w7 &&& 0xff))
      sc)
  | _ => none

/-- Parse the address body of an IPv6 literal (without `%zone`) into a `scopeId → Option DnsAddr` builder. -/
def parseIpv6CoreImpl? (addrCs : List Char) : Option (UInt32 → Option DnsAddr) := do
  if addrCs.isEmpty || addrCs.length > 64 then none
  let halves := splitDoubleColonCharsImpl addrCs
  match halves with
  | [single] => do
    let ws ← parseIpv6PartsImpl? true single
    if ws.length != 8 then none
    some (wordsToIpv6AddrImpl ws)
  | [lhsCs, rhsCs] => do
    let lhs ← parseIpv6PartsImpl? false lhsCs
    let rhs ← parseIpv6PartsImpl? true rhsCs
    let used := lhs.length + rhs.length
    if used ≥ 8 then none
    let zeros := List.replicate (8 - used) 0
    some (wordsToIpv6AddrImpl (lhs ++ zeros ++ rhs))
  | _ => none

/-- Parse an IPv6 literal with an optional `%<zone>` suffix into its builder and raw zone chars. -/
def parseIpv6SplitZoneImpl? (host : String) : Option ((UInt32 → Option DnsAddr) × Option (List Char)) :=
  let (addrCs, zone?) := splitFirstZoneAuxImpl host.toList []
  match parseIpv6CoreImpl? addrCs with
  | none => none
  | some mk => some (mk, zone?)

/-- Return `true` iff `host.toList` is non-empty and free of embedded NUL (`\x00`) characters. -/
def isNonEmptyNoNulHostImpl (host : String) : Bool :=
  let cs := host.toList
  !cs.isEmpty && !cs.contains (Char.ofNat 0)

/-- Return `true` iff `a` is an IPv6 link-local or node/link-local multicast address eligible for symbolic `%<iface>` zones. -/
def allowsSymbolicIpv6ZoneImpl : DnsAddr → Bool
  | .ipv6 b0 b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    (b0 == 0xfe && (b1 &&& 0xc0) == 0x80) ||
    (b0 == 0xff && ((b1 &&& 0x0f) == 0x01 || (b1 &&& 0x0f) == 0x02))
  | .ipv4 .. => false

/-- Parse pure platform-independent numeric IPv4 or IPv6 literals. -/
def parsePureNumericAddrImpl? (host : String) : Option DnsAddr :=
  if !isNonEmptyNoNulHostImpl host then none
  else
    match parseIpv4AtonImpl? host with
    | some addr => some addr
    | none =>
      match parseIpv6SplitZoneImpl? host with
      | none => none
      | some (mk, none) => mk 0
      | some (mk, some zoneCs) =>
        match parseNumericZoneImpl? zoneCs with
        | some sc =>
          match mk sc with
          | some addr =>
            if allowsSymbolicIpv6ZoneImpl addr && zoneCs.length < 16 then none
            else some addr
          | none => none
        | none => none

/-- Parse a link/multicast-local IPv6 literal with a `1..15`-byte numeric `%<u32>` zone. -/
def parseHybridScopedNumericZoneImpl? (host : String) : Option (DnsAddr × UInt32) :=
  if !isNonEmptyNoNulHostImpl host then none
  else
    match parseIpv4AtonImpl? host with
    | some _ => none
    | none =>
      match parseIpv6SplitZoneImpl? host with
      | some (mk, some zoneCs) =>
        if zoneCs.length < 16 then
          match mk 0, parseNumericZoneImpl? zoneCs with
          | some baseAddr, some sc =>
            if allowsSymbolicIpv6ZoneImpl baseAddr then some (baseAddr, sc) else none
          | _, _ => none
        else none
      | _ => none

/-- Parse an IPv6 literal with an empty or non-`uint32` `%<zone>` suffix. -/
def parseScopedNonNumericZoneImpl? (host : String) : Option (DnsAddr × List Char) :=
  if !isNonEmptyNoNulHostImpl host then none
  else
    match parseIpv4AtonImpl? host with
    | some _ => none
    | none =>
      match parseIpv6SplitZoneImpl? host with
      | some (mk, some zoneCs) =>
        if (parseNumericZoneImpl? zoneCs).isSome then none
        else
          match mk 0 with
          | some baseAddr => some (baseAddr, zoneCs)
          | none => none
      | _ => none

/-- Transform `a` under `hints.family`, unwrapping IPv4-mapped IPv6 to `.ipv4` when `hints.family = .ipv4`. -/
def mapAddrForHintsImpl (hints : ResolveHints) (a : DnsAddr) : Option DnsAddr :=
  match hints.family with
  | .any => some a
  | .ipv4 =>
    match a with
    | .ipv4 .. => some a
    | .ipv6 0 0 0 0 0 0 0 0 0 0 0xff 0xff b0 b1 b2 b3 _ => some (.ipv4 b0 b1 b2 b3)
    | .ipv6 .. => none
  | .ipv6 =>
    match a with
    | .ipv4 .. => none
    | .ipv6 .. => some a

/-- Replicate resolved addresses according to `hints.sockType`. -/
def expandSockTypeImpl (hints : ResolveHints) (addrs : List DnsAddr) : List DnsAddr :=
  match hints.sockType with
  | .any => addrs.flatMap (fun a => [a, a, a])
  | .stream | .dgram => addrs

/-- Check that every consecutive 3-element group in `addrs` consists of equal addresses. -/
def checkSockTriplesImpl : List DnsAddr → Bool
  | [] => true
  | a :: b :: c :: rest => a == b && b == c && checkSockTriplesImpl rest
  | _ => false

/-- Return `true` iff `addrs` satisfies the `SockTypeHint.any` `3×` consecutive-triple multiplicity invariant. -/
def matchesSockTypeMultiplicityImpl (hints : ResolveHints) (addrs : List DnsAddr) : Bool :=
  match hints.sockType with
  | .stream | .dgram => true
  | .any => checkSockTriplesImpl addrs

/-- Replace the `scopeId` of an `.ipv6` address with `sc` (identity on `.ipv4`). -/
def withIpv6ScopeImpl (sc : UInt32) : DnsAddr → DnsAddr
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 _ =>
    .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc
  | a => a

/-- Return `true` iff `host`'s non-numeric `%zone` is eligible to resolve symbolically under `hints`. -/
def canSymbolicScopedOkImpl (hints : ResolveHints) (baseAddr : DnsAddr) (zoneCs : List Char) : Bool :=
  !zoneCs.isEmpty && allowsSymbolicIpv6ZoneImpl baseAddr && hints.family != .ipv4

/-- Return `true` iff `addrs` equals `expandSockTypeImpl hints [scopedAddr]` with non-zero `scopeId` matching `baseAddr`. -/
def matchesSymbolicScopedAddrsImpl (hints : ResolveHints) (baseAddr : DnsAddr) (addrs : List DnsAddr) : Bool :=
  match addrs.head? with
  | some first =>
    first.isIpv6 && !first.isUnscoped &&
    first == withIpv6ScopeImpl first.scopeId baseAddr &&
    addrs == expandSockTypeImpl hints [first]
  | none => false

/-- Return `true` iff `addrs` matches either fallback numeric `scopeId = sc` or a resolved symbolic non-zero `scopeId`. -/
def matchesHybridScopedAddrsImpl (hints : ResolveHints) (baseAddr : DnsAddr) (sc : UInt32)
    (addrs : List DnsAddr) : Bool :=
  hints.family != .ipv4 &&
    (addrs == expandSockTypeImpl hints [withIpv6ScopeImpl sc baseAddr] ||
     matchesSymbolicScopedAddrsImpl hints baseAddr addrs)

/-- Return `true` iff `host` is a numeric or non-v4-mapped zoned IP literal whose address family conflicts with `hints.family`. -/
def isNumericFamilyMismatchImpl (host : String) (hints : ResolveHints) : Bool :=
  match parsePureNumericAddrImpl? host with
  | some rawAddr => (mapAddrForHintsImpl hints rawAddr).isNone
  | none =>
    match parseHybridScopedNumericZoneImpl? host with
    | some _ => hints.family == .ipv4
    | none =>
      match parseScopedNonNumericZoneImpl? host with
      | some (baseAddr, _) => hints.family == .ipv4 && !isIpv4MappedAddrImpl baseAddr
      | none => false

/-- Normalize a raw `gaiCode` for `(host, hints)`. -/
def normalizeGaiCodeForHostImpl (host : String) (hints : ResolveHints) (rc : Int32) : Int32 :=
  let code0 := if isValidGaiCodeImpl rc then rc else EAI_FAIL
  if isNumericFamilyMismatchImpl host hints then
    if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0
  else
    if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0

/-- Canonical `DnsError` emitted when an underlying resolver returns empty, wrong-family, or unresolvable zoned records. -/
def emptyPayloadErrorImpl (host : String) (hints : ResolveHints) : DnsError :=
  if isNumericFamilyMismatchImpl host hints then
    { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
      message := "Address family for hostname not supported" }
  else if (parsePureNumericAddrImpl? host).isSome || (parseHybridScopedNumericZoneImpl? host).isSome then
    { kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none,
      message := "Numeric literal resolution mismatch" }
  else if (parseScopedNonNumericZoneImpl? host).isSome then
    { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none,
      message := "Name or service not known" }
  else
    { kind := .nameNotFound, gaiCode := EAI_NODATA, errno? := none,
      message := "No address associated with hostname" }

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
  let rc' := normalizeGaiCodeForHostImpl host hints rc
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
              return .error (emptyPayloadErrorImpl host hints)
            else if !matchesSockTypeMultiplicityImpl hints addrs then
              return .error { kind := .nameNotFound
                              gaiCode := EAI_FAIL
                              errno? := none
                              message := "Socket-type multiplicity mismatch" }
            else
              match parsePureNumericAddrImpl? host with
              | some rawAddr =>
                match mapAddrForHintsImpl hints rawAddr with
                | none =>
                  return .error (emptyPayloadErrorImpl host hints)
                | some expAddr =>
                  if addrs == expandSockTypeImpl hints [expAddr] then
                    return .ok addrs
                  else
                    return .error { kind := .nameNotFound
                                    gaiCode := EAI_FAIL
                                    errno? := none
                                    message := "Numeric literal resolution mismatch" }
              | none =>
                match parseHybridScopedNumericZoneImpl? host with
                | some (baseAddr, sc) =>
                  if matchesHybridScopedAddrsImpl hints baseAddr sc addrs then
                    return .ok addrs
                  else
                    return .error (emptyPayloadErrorImpl host hints)
                | none =>
                  match parseScopedNonNumericZoneImpl? host with
                  | some (baseAddr, zoneCs) =>
                    if canSymbolicScopedOkImpl hints baseAddr zoneCs &&
                        matchesSymbolicScopedAddrsImpl hints baseAddr addrs then
                      return .ok addrs
                    else
                      return .error (emptyPayloadErrorImpl host hints)
                  | none => return .ok addrs
        | .error (rc, eno, msgBytes) => return .error (classifyGaiError host hints rc eno msgBytes) }

/-- Construct an `IO` `DnsOps` bundle from `PosixDnsOps` hooks. -/
def mkDnsOps (raw : PosixDnsOps) : DnsOps :=
  mkDnsOpsM raw

end LeanSwe.LinuxSyscall.Dns.Internal

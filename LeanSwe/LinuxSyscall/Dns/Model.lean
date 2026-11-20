import LeanSwe.LinuxSyscall.Dns.Types

namespace LeanSwe.LinuxSyscall.Dns

open LeanSwe.LinuxSyscall

/-- Pure nondeterministic DNS resolution oracle returning `List DnsAddr` or `DnsError`. -/
structure DnsOracle where
  /-- Oracle lookup callback for syntactically valid hostnames and resolution hints. -/
  lookup : String → ResolveHints → Except DnsError (List DnsAddr)

/-- Return `true` iff `rc` is a reachable Linux `<netdb.h>` `getaddrinfo(3)` error code for `ai_flags = 0` and `service = NULL`. -/
def isValidGaiCode (rc : Int32) : Bool :=
  EAI_OVERFLOW ≤ rc && rc ≤ EAI_NONAME && rc != EAI_SERVICE

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseUintDigits? (base : Nat) (maxVal : Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => do
    let d ← hexVal? c
    if d ≥ base then none
    let nxt := acc * base + d
    if nxt > maxVal then none
    parseUintDigits? base maxVal cs nxt

private def splitCharListAux (sep : Char) : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
    if c == sep then
      splitCharListAux sep cs [] (cur.reverse :: acc)
    else
      splitCharListAux sep cs (c :: cur) acc

private def splitCharList (sep : Char) (cs : List Char) : List (List Char) :=
  splitCharListAux sep cs [] []

private def splitDoubleColonAux : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | ':' :: ':' :: cs, cur, acc =>
    splitDoubleColonAux cs [] (cur.reverse :: acc)
  | c :: cs, cur, acc =>
    splitDoubleColonAux cs (c :: cur) acc

private def splitDoubleColonChars (cs : List Char) : List (List Char) :=
  splitDoubleColonAux cs [] []

private def parseIpv4AtonPart? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | '0' :: 'x' :: ds | '0' :: 'X' :: ds =>
    if ds.isEmpty then none else parseUintDigits? 16 0xffffffff ds 0
  | '0' :: ds =>
    parseUintDigits? 8 0xffffffff ds 0
  | c :: ds =>
    if '1' ≤ c && c ≤ '9' then
      parseUintDigits? 10 0xffffffff (c :: ds) 0
    else
      none

private def parseIpv4Aton? (host : String) : Option DnsAddr := do
  let parts := splitCharList '.' host.toList
  if parts.any (·.isEmpty) then none
  match parts with
  | [aCs] =>
    let a ← parseIpv4AtonPart? aCs
    some (.ipv4
      (UInt8.ofNat ((a >>> 24) &&& 0xff))
      (UInt8.ofNat ((a >>> 16) &&& 0xff))
      (UInt8.ofNat ((a >>> 8) &&& 0xff))
      (UInt8.ofNat (a &&& 0xff)))
  | [aCs, bCs] =>
    let a ← parseIpv4AtonPart? aCs
    let b ← parseIpv4AtonPart? bCs
    if a > 255 || b > 0xffffff then none
    some (.ipv4
      (UInt8.ofNat a)
      (UInt8.ofNat ((b >>> 16) &&& 0xff))
      (UInt8.ofNat ((b >>> 8) &&& 0xff))
      (UInt8.ofNat (b &&& 0xff)))
  | [aCs, bCs, cCs] =>
    let a ← parseIpv4AtonPart? aCs
    let b ← parseIpv4AtonPart? bCs
    let c ← parseIpv4AtonPart? cCs
    if a > 255 || b > 255 || c > 0xffff then none
    some (.ipv4
      (UInt8.ofNat a)
      (UInt8.ofNat b)
      (UInt8.ofNat ((c >>> 8) &&& 0xff))
      (UInt8.ofNat (c &&& 0xff)))
  | [aCs, bCs, cCs, dCs] =>
    let a ← parseIpv4AtonPart? aCs
    let b ← parseIpv4AtonPart? bCs
    let c ← parseIpv4AtonPart? cCs
    let d ← parseIpv4AtonPart? dCs
    if a > 255 || b > 255 || c > 255 || d > 255 then none
    some (.ipv4 (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c) (UInt8.ofNat d))
  | _ => none

private def parseStrictDecOctet? (cs : List Char) : Option Nat := do
  if cs.isEmpty || cs.length > 3 then none
  if cs.length > 1 && cs.head? == some '0' then none
  parseUintDigits? 10 255 cs 0

private def parseStrictIpv4Hextets? (cs : List Char) : Option (Nat × Nat) := do
  let parts := splitCharList '.' cs
  match parts with
  | [aCs, bCs, cCs, dCs] =>
    let a ← parseStrictDecOctet? aCs
    let b ← parseStrictDecOctet? bCs
    let c ← parseStrictDecOctet? cCs
    let d ← parseStrictDecOctet? dCs
    some ((a <<< 8) ||| b, (c <<< 8) ||| d)
  | _ => none

private def parseHexGroup? (cs : List Char) : Option Nat := do
  if cs.isEmpty || cs.length > 4 then none
  parseUintDigits? 16 0xffff cs 0

private def parseIpv6PartsLoop (allowV4Tail : Bool) : List (List Char) → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | [last], acc =>
    if allowV4Tail && last.contains '.' then do
      let (hi, lo) ← parseStrictIpv4Hextets? last
      if acc.length + 2 > 8 then none else some (lo :: hi :: acc).reverse
    else do
      let v ← parseHexGroup? last
      if acc.length ≥ 8 then none else some (v :: acc).reverse
  | p :: rest, acc =>
    if acc.length ≥ 8 then
      none
    else do
      let v ← parseHexGroup? p
      parseIpv6PartsLoop allowV4Tail rest (v :: acc)

private def parseIpv6Parts? (allowV4Tail : Bool) (cs : List Char) : Option (List Nat) :=
  if cs.isEmpty then
    some []
  else
    let parts := splitCharList ':' cs
    if parts.any (·.isEmpty) then
      none
    else
      parseIpv6PartsLoop allowV4Tail parts []

private def wordsToIpv6Addr (ws : List Nat) (sc : UInt32) : Option DnsAddr :=
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

private def parseIpv6Core? (addrCs : List Char) : Option (UInt32 → Option DnsAddr) := do
  if addrCs.isEmpty || addrCs.length > 64 then none
  let halves := splitDoubleColonChars addrCs
  match halves with
  | [single] => do
    let ws ← parseIpv6Parts? true single
    if ws.length != 8 then none
    some (wordsToIpv6Addr ws)
  | [lhsCs, rhsCs] => do
    let lhs ← parseIpv6Parts? false lhsCs
    let rhs ← parseIpv6Parts? true rhsCs
    let used := lhs.length + rhs.length
    if used ≥ 8 then none
    let zeros := List.replicate (8 - used) 0
    some (wordsToIpv6Addr (lhs ++ zeros ++ rhs))
  | _ => none

private def parseNumericZone? (zoneCs : List Char) : Option UInt32 := do
  if zoneCs.isEmpty then none
  let n ← parseUintDigits? 10 0xffffffff zoneCs 0
  some (UInt32.ofNat n)

private def isIpv4MappedAddr : DnsAddr → Bool
  | .ipv6 0 0 0 0 0 0 0 0 0 0 0xff 0xff _ _ _ _ _ => true
  | _ => false

/-- Return `true` iff `a` is an IPv6 link-local (`fe80::/10`), multicast node-local (`ffx1::/16`), or multicast link-local (`ffx2::/16`) address eligible for symbolic `%<iface>` zones under RFC 4007 / `glibc`. -/
def allowsSymbolicIpv6Zone : DnsAddr → Bool
  | .ipv6 b0 b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    (b0 == 0xfe && (b1 &&& 0xc0) == 0x80) ||
    (b0 == 0xff && ((b1 &&& 0x0f) == 0x01 || (b1 &&& 0x0f) == 0x02))
  | .ipv4 .. => false

private def splitFirstZoneAux : List Char → List Char → List Char × Option (List Char)
  | [], acc => (acc.reverse, none)
  | '%' :: rest, acc => (acc.reverse, some rest)
  | c :: rest, acc => splitFirstZoneAux rest (c :: acc)

private def parseIpv6SplitZone? (host : String) : Option ((UInt32 → Option DnsAddr) × Option (List Char)) :=
  let (addrCs, zone?) := splitFirstZoneAux host.toList []
  match parseIpv6Core? addrCs with
  | none => none
  | some mk => some (mk, zone?)

private def isNonEmptyNoNulHost (host : String) : Bool :=
  let cs := host.toList
  !cs.isEmpty && !cs.contains (Char.ofNat 0)

/-- Parse pure platform- and namespace-independent numeric IPv4 (`inet_aton`) or IPv6 (unscoped, non-link/multicast-local `%<u32>`, or `>= 16`-byte `%<u32>` exceeding `IFNAMSIZ`) literals. -/
def parsePureNumericAddr? (host : String) : Option DnsAddr :=
  if !isNonEmptyNoNulHost host then none
  else
    match parseIpv4Aton? host with
    | some addr => some addr
    | none =>
      match parseIpv6SplitZone? host with
      | none => none
      | some (mk, none) => mk 0
      | some (mk, some zoneCs) =>
        match parseNumericZone? zoneCs with
        | some sc =>
          match mk sc with
          | some addr =>
            if allowsSymbolicIpv6Zone addr && zoneCs.length < 16 then none
            else some addr
          | none => none
        | none => none

/-- If `host` is a link- or node/link-local-multicast IPv6 literal (`allowsSymbolicIpv6Zone`) with a `1..15`-byte (`< IFNAMSIZ`) numeric `%<u32>` zone (where `glibc` checks `if_nametoindex` before falling back to numeric `strtoul`), return `(baseAddr, numericScopeId)`. -/
def parseHybridScopedNumericZone? (host : String) : Option (DnsAddr × UInt32) :=
  if !isNonEmptyNoNulHost host then none
  else
    match parseIpv4Aton? host with
    | some _ => none
    | none =>
      match parseIpv6SplitZone? host with
      | some (mk, some zoneCs) =>
        if zoneCs.length < 16 then
          match mk 0, parseNumericZone? zoneCs with
          | some baseAddr, some sc =>
            if allowsSymbolicIpv6Zone baseAddr then some (baseAddr, sc) else none
          | _, _ => none
        else none
      | _ => none

/-- If `host` is an IPv6 literal with an empty or non-`uint32` `%<zone>` suffix (`strchr('%')`), return its base address (`scopeId = 0`) and raw zone bytes. -/
def parseScopedNonNumericZone? (host : String) : Option (DnsAddr × List Char) :=
  if !isNonEmptyNoNulHost host then none
  else
    match parseIpv4Aton? host with
    | some _ => none
    | none =>
      match parseIpv6SplitZone? host with
      | some (mk, some zoneCs) =>
        if (parseNumericZone? zoneCs).isSome then none
        else
          match mk 0 with
          | some baseAddr => some (baseAddr, zoneCs)
          | none => none
      | _ => none

/-- Return `true` iff `host` is a numeric IPv4 or IPv6 literal (including IPv6 literals with a `%zone` suffix). -/
def isNumericHostLiteral (host : String) : Bool :=
  isNonEmptyNoNulHost host &&
    ((parseIpv4Aton? host).isSome || (parseIpv6SplitZone? host).isSome)

/-- Transform `a` under `hints.family`: unwraps IPv4-mapped IPv6 (`::ffff:a.b.c.d`) to `.ipv4` when `hints.family = .ipv4`. -/
def mapAddrForHints (hints : ResolveHints) (a : DnsAddr) : Option DnsAddr :=
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

/-- Replicate resolved addresses according to `hints.sockType` (`3×` for `SockTypeHint.any`, matching Linux `glibc` `[SOCK_STREAM, SOCK_DGRAM, SOCK_RAW]`). -/
def expandSockType (hints : ResolveHints) (addrs : List DnsAddr) : List DnsAddr :=
  match hints.sockType with
  | .any => addrs.flatMap (fun a => [a, a, a])
  | .stream | .dgram => addrs

/-- Check that every consecutive 3-element group in `addrs` consists of equal addresses. -/
def checkSockTriples : List DnsAddr → Bool
  | [] => true
  | a :: b :: c :: rest => a == b && b == c && checkSockTriples rest
  | _ => false

/-- Return `true` iff `addrs` satisfies the `SockTypeHint.any` `3×` consecutive-triple multiplicity invariant. -/
def matchesSockTypeMultiplicity (hints : ResolveHints) (addrs : List DnsAddr) : Bool :=
  match hints.sockType with
  | .stream | .dgram => true
  | .any => checkSockTriples addrs

/-- Replace the `scopeId` of an `.ipv6` address with `sc` (identity on `.ipv4`). -/
def withIpv6Scope (sc : UInt32) : DnsAddr → DnsAddr
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 _ =>
    .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc
  | a => a

/-- Return `true` iff `canSymbolicScopedOk`: `host`'s non-numeric `%zone` is non-empty, `baseAddr` permits symbolic zones, and `hints.family != .ipv4`. -/
def canSymbolicScopedOk (hints : ResolveHints) (baseAddr : DnsAddr) (zoneCs : List Char) : Bool :=
  !zoneCs.isEmpty && allowsSymbolicIpv6Zone baseAddr && hints.family != .ipv4

/-- Return `true` iff `addrs` equals `expandSockType hints [scopedAddr]` where `scopedAddr` shares `baseAddr`'s 16 bytes with non-zero `scopeId`. -/
def matchesSymbolicScopedAddrs (hints : ResolveHints) (baseAddr : DnsAddr) (addrs : List DnsAddr) : Bool :=
  match addrs.head? with
  | some first =>
    first.isIpv6 && !first.isUnscoped &&
    first == withIpv6Scope first.scopeId baseAddr &&
    addrs == expandSockType hints [first]
  | none => false

/-- Return `true` iff `addrs` matches either the fallback numeric `scopeId = sc` or a resolved symbolic `if_nametoindex` non-zero `scopeId` for a `< IFNAMSIZ` numeric-zoned link/multicast-local IPv6 literal under non-`.ipv4` hints. -/
def matchesHybridScopedAddrs (hints : ResolveHints) (baseAddr : DnsAddr) (sc : UInt32)
    (addrs : List DnsAddr) : Bool :=
  hints.family != .ipv4 &&
    (addrs == expandSockType hints [withIpv6Scope sc baseAddr] ||
     matchesSymbolicScopedAddrs hints baseAddr addrs)

/-- Return `true` iff `host` is a numeric or non-v4-mapped zoned IP literal whose address family conflicts with `hints.family` (`EAI_ADDRFAMILY`). -/
def isNumericFamilyMismatch (host : String) (hints : ResolveHints) : Bool :=
  match parsePureNumericAddr? host with
  | some rawAddr => (mapAddrForHints hints rawAddr).isNone
  | none =>
    match parseHybridScopedNumericZone? host with
    | some _ => hints.family == .ipv4
    | none =>
      match parseScopedNonNumericZone? host with
      | some (baseAddr, _) => hints.family == .ipv4 && !isIpv4MappedAddr baseAddr
      | none => false

private def isLocalhostAscii (host : String) : Bool :=
  let lowerCs := host.toList.map fun c =>
    if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  lowerCs == ['l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't']

/-- Normalize a raw `gaiCode` for `(host, hints)`: clamps invalid codes to `EAI_FAIL`, maps `EAI_NONAME`/`EAI_NODATA` to `EAI_ADDRFAMILY` on numeric family mismatches, and maps stray `EAI_ADDRFAMILY` to `EAI_NONAME` otherwise. -/
def normalizeGaiCodeForHost (host : String) (hints : ResolveHints) (rc : Int32) : Int32 :=
  let code0 := if isValidGaiCode rc then rc else EAI_FAIL
  if isNumericFamilyMismatch host hints then
    if code0 == EAI_NONAME || code0 == EAI_NODATA then EAI_ADDRFAMILY else code0
  else
    if code0 == EAI_ADDRFAMILY then EAI_NONAME else code0

/-- Canonical `DnsError` emitted when an underlying resolver returns empty, wrong-family, or unresolvable zoned records. -/
def emptyPayloadError (host : String) (hints : ResolveHints) : DnsError :=
  if isNumericFamilyMismatch host hints then
    { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
      message := "Address family for hostname not supported" }
  else if (parsePureNumericAddr? host).isSome || (parseHybridScopedNumericZone? host).isSome then
    { kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none,
      message := "Numeric literal resolution mismatch" }
  else if (parseScopedNonNumericZone? host).isSome then
    { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none,
      message := "Name or service not known" }
  else
    { kind := .nameNotFound, gaiCode := EAI_NODATA, errno? := none,
      message := "No address associated with hostname" }

/-- Pure relational specification of an allowed `getaddrinfo(host, hints)` outcome. -/
def allowedDnsOutcome (host : String) (hints : ResolveHints := {})
    (out : Except DnsError (List DnsAddr)) : Bool :=
  if !validateHost host then
    match out with
    | .error err =>
      err.kind == .invalidHost &&
      err.gaiCode == EAI_NONAME &&
      err.errno? == some Errno.EINVAL &&
      !err.message.isEmpty
    | .ok _ => false
  else
    match out with
    | .ok addrs =>
      !addrs.isEmpty &&
      addrs.all (addrMatchesHints hints) &&
      matchesSockTypeMultiplicity hints addrs &&
      (match parsePureNumericAddr? host with
       | some rawAddr =>
         match mapAddrForHints hints rawAddr with
         | some expAddr => addrs == expandSockType hints [expAddr]
         | none => false
       | none =>
         match parseHybridScopedNumericZone? host with
         | some (baseAddr, sc) =>
           matchesHybridScopedAddrs hints baseAddr sc addrs
         | none =>
           match parseScopedNonNumericZone? host with
           | some (baseAddr, zoneCs) =>
             canSymbolicScopedOk hints baseAddr zoneCs &&
             matchesSymbolicScopedAddrs hints baseAddr addrs
           | none => true)
    | .error err =>
      err.kind != .invalidHost &&
      isValidGaiCode err.gaiCode &&
      err.kind == classifyGaiKind err.gaiCode &&
      (if err.gaiCode == EAI_ADDRFAMILY then isNumericFamilyMismatch host hints else true) &&
      (if isNumericFamilyMismatch host hints then err.gaiCode != EAI_NONAME && err.gaiCode != EAI_NODATA else true) &&
      (match err.errno? with
       | none => true
       | some eno => err.gaiCode == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT) &&
      !err.message.isEmpty

/-- Normalize an oracle outcome so valid hostnames enforce family filtering, IPv4-mapped IPv6 unwrapping, `sockType` multiplicity, scoped-zone rules, numeric `EAI_ADDRFAMILY` vs non-numeric errors, `isValidGaiCode`, and `EFAULT`-free `DnsError` invariants. -/
def normalizeOracleOutcome (host : String) (hints : ResolveHints := {})
    (out : Except DnsError (List DnsAddr)) : Except DnsError (List DnsAddr) :=
  if !validateHost host then
    .error invalidHostError
  else
    match out with
    | .ok addrs =>
      let filtered := addrs.filterMap (mapAddrForHints hints)
      let kept :=
        if !filtered.isEmpty && matchesSockTypeMultiplicity hints filtered then
          filtered
        else
          expandSockType hints filtered
      match parsePureNumericAddr? host with
      | some rawAddr =>
        match mapAddrForHints hints rawAddr with
        | none => .error (emptyPayloadError host hints)
        | some expAddr =>
          if kept == expandSockType hints [expAddr] then
            .ok kept
          else
            .error { kind := .nameNotFound
                     gaiCode := EAI_FAIL
                     errno? := none
                     message := "Numeric literal resolution mismatch" }
      | none =>
        match parseHybridScopedNumericZone? host with
        | some (baseAddr, sc) =>
          if !kept.isEmpty && matchesHybridScopedAddrs hints baseAddr sc kept then
            .ok kept
          else
            .error (emptyPayloadError host hints)
        | none =>
          match parseScopedNonNumericZone? host with
          | some (baseAddr, zoneCs) =>
            if canSymbolicScopedOk hints baseAddr zoneCs && !kept.isEmpty &&
                matchesSymbolicScopedAddrs hints baseAddr kept then
              .ok kept
            else
              .error (emptyPayloadError host hints)
          | none =>
            if kept.isEmpty then
              .error (emptyPayloadError host hints)
            else
              .ok kept
    | .error err =>
      let code' := normalizeGaiCodeForHost host hints err.gaiCode
      let kind' := classifyGaiKind code'
      let errno?' := match err.errno? with
        | some eno => if code' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
        | none => none
      let msg' := if err.message.isEmpty then "getaddrinfo failed" else err.message
      .error { kind := kind', gaiCode := code', errno? := errno?', message := msg' }

/-- Pure reference DNS resolution against `oracle`, rejecting empty or NUL-containing hosts up front. -/
def modelResolve (oracle : DnsOracle) (host : String) (hints : ResolveHints := {}) :
    Except DnsError (List DnsAddr) :=
  if !validateHost host then
    .error invalidHostError
  else
    normalizeOracleOutcome host hints (oracle.lookup host hints)

/-- Pure `StateM DnsOracle` capability bundle implementing `DnsOpsM` against the oracle. -/
def modelOps : DnsOpsM (StateM DnsOracle) :=
  { getaddrinfo := fun host hints => do
      let oracle ← get
      return modelResolve oracle host hints }

/-- Built-in offline-safe `DnsOracle` resolving numeric IPv4 (`inet_aton` 1-4 parts), IPv6 (with numeric `%<u32>` or link/multicast-local `%lo` = `1`), `localhost` (`::1`/`127.0.0.1` matching `glibc` `files`), `::ffff:a.b.c.d` unwrapping under `.ipv4`, `SockTypeHint.any` `3×` multiplicity, and `.invalid` failures. -/
def defaultOfflineOracle : DnsOracle :=
  { lookup := fun host hints =>
      let filterByFamily (addrs : List DnsAddr) : Except DnsError (List DnsAddr) :=
        let kept := addrs.filterMap (mapAddrForHints hints)
        if kept.isEmpty then
          .error { kind := .otherGai
                   gaiCode := EAI_ADDRFAMILY
                   errno? := none
                   message := "Address family for hostname not supported" }
        else
          .ok (expandSockType hints kept)
      if !validateHost host then
        .error invalidHostError
      else
        match parsePureNumericAddr? host with
        | some addr => filterByFamily [addr]
        | none =>
          match parseHybridScopedNumericZone? host with
          | some (baseAddr, sc) =>
            if hints.family == .ipv4 then
              .error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
                       message := "Address family for hostname not supported" }
            else
              filterByFamily [withIpv6Scope sc baseAddr]
          | none =>
            match parseScopedNonNumericZone? host with
          | some (baseAddr, zoneCs) =>
            if zoneCs == ['l', 'o'] && allowsSymbolicIpv6Zone baseAddr then
              if hints.family == .ipv4 then
                .error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
                         message := "Address family for hostname not supported" }
              else
                match parseIpv6SplitZone? host with
                | some (mk, _) =>
                  match mk 1 with
                  | some scopedAddr => filterByFamily [scopedAddr]
                  | none =>
                    .error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none,
                             message := "Name or service not known" }
                | none =>
                  .error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none,
                           message := "Name or service not known" }
            else if hints.family == .ipv4 && !isIpv4MappedAddr baseAddr then
              .error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
                       message := "Address family for hostname not supported" }
            else
              .error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none,
                       message := "Name or service not known" }
          | none =>
            if isLocalhostAscii host then
              let loopbackV4 := DnsAddr.ipv4 127 0 0 1
              let loopbackV6 := DnsAddr.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
              match hints.family with
              | .ipv4 => .ok (expandSockType hints [loopbackV4, loopbackV4])
              | .ipv6 => .ok (expandSockType hints [loopbackV6])
              | .any => .ok (expandSockType hints [loopbackV6, loopbackV4])
            else
              .error { kind := .nameNotFound
                       gaiCode := EAI_NONAME
                       errno? := none
                       message := "Name or service not known" } }

/-- One DNS lookup request in a `Dns` world-model trace (`host` and `ResolveHints`). -/
structure DnsReq where
  /-- Hostname or numeric IP literal passed to `getaddrinfo`. -/
  host : String
  /-- Address-family and socket-type constraints. -/
  hints : ResolveHints := {}
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Outcome observed at the `Dns` world-model boundary. -/
abbrev DnsOutcome := Except DnsError (List DnsAddr)

/-- Execute one `DnsReq` against a `DnsOpsM m` capability bundle. -/
def execDnsReq {m : Type → Type} [Monad m]
    (ops : DnsOpsM m) (req : DnsReq) : m DnsOutcome :=
  ops.getaddrinfo req.host req.hints

/-- Return `true` iff `out` is a curated catastrophic OS or allocator fault (`EAI_MEMORY`, or `EAI_SYSTEM` carrying `Errno.isCriticalOsErrno`). -/
def isCriticalFault : DnsOutcome → Bool
  | .ok _ => false
  | .error err =>
    err.gaiCode == EAI_MEMORY ||
      (err.gaiCode == EAI_SYSTEM &&
        match err.errno? with
        | some eno => Errno.isCriticalOsErrno eno
        | none => false)

/-- Return `true` iff `out` is an interrupted syscall outcome (`EAI_SYSTEM` carrying `Errno.EINTR`). -/
def isEintrOutcome : DnsOutcome → Bool
  | .ok _ => false
  | .error err => err.gaiCode == EAI_SYSTEM && err.errno? == some Errno.EINTR

/-- Stateful DNS world model pairing a reference `DnsOracle` with optional ambient `seccomp` preemption. -/
structure DnsState where
  /-- Reference resolution oracle for non-numeric hostnames. -/
  oracle : DnsOracle := defaultOfflineOracle
  /-- Whether an ambient outer `seccomp` filter may preempt NSS or socket syscalls. -/
  ambientSeccomp : Bool := false
  deriving Inhabited

/-- Initial `DnsState` backed by `oracle` with `ambientSeccomp = false`. -/
def DnsState.initial (oracle : DnsOracle := defaultOfflineOracle) : DnsState :=
  { oracle := oracle, ambientSeccomp := false }

/-- Enable ambient outer `seccomp` preemption on a `DnsState`. -/
def DnsState.withOuterSeccomp (s : DnsState := DnsState.initial) : DnsState :=
  { s with ambientSeccomp := true }

/-- Relational OS-level step checker for `LeanSwe.LinuxSyscall.Dns`: enforces `allowedDnsOutcome` and, when `ambientSeccomp = false`, requires pure and hybrid numeric IP literals (`parsePureNumericAddr?`, `parseHybridScopedNumericZone?`) to succeed on family match or fail with `EAI_ADDRFAMILY` on family mismatch unless a critical OS fault (`isCriticalFault`) occurs. -/
def allowedStep (s : DnsState) (req : DnsReq) (out : DnsOutcome) : Option DnsState :=
  if !allowedDnsOutcome req.host req.hints out then
    none
  else if !validateHost req.host || s.ambientSeccomp then
    some s
  else
    match parsePureNumericAddr? req.host with
    | some rawAddr =>
      match mapAddrForHints req.hints rawAddr with
      | some _ =>
        match out with
        | .ok _ => some s
        | .error _ => if isCriticalFault out then some s else none
      | none =>
        match out with
        | .ok _ => none
        | .error err =>
          if (err.gaiCode == EAI_ADDRFAMILY && err.errno? == none) || isCriticalFault out then
            some s
          else
            none
    | none =>
      match parseHybridScopedNumericZone? req.host with
      | none => some s
      | some _ =>
        if req.hints.family != .ipv4 then
          match out with
          | .ok _ => some s
          | .error _ => if isCriticalFault out then some s else none
        else
          match out with
          | .ok _ => none
          | .error err =>
            if (err.gaiCode == EAI_ADDRFAMILY && err.errno? == none) || isCriticalFault out then
              some s
            else
              none

/-- Healthy execution environment wrapping `DnsState` with a finite `EINTR` interruption budget (`ambientSeccomp = false`). -/
structure HealthyEnv where
  /-- Underlying `DnsState` world state. -/
  state : DnsState := DnsState.initial
  /-- Remaining bound on `EINTR` signal interruptions. -/
  eintrBudget : Nat := 0
  deriving Inhabited

/-- Initial healthy `Dns` environment (`ambientSeccomp = false`, `eintrBudget`). -/
def HealthyEnv.initial (eintrBudget : Nat := 0) (oracle : DnsOracle := defaultOfflineOracle) :
    HealthyEnv :=
  { state := DnsState.initial oracle, eintrBudget := eintrBudget }

/-- Return `true` iff `env` has no ambient `seccomp` preemption. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Dns`, guaranteeing unconditional resolution of valid in-family numeric IP literals while allowing everyday DNS/NSS errors and bounded `EINTR` on hostnames and banning curated critical OS faults. -/
def healthyStep (env : HealthyEnv) (req : DnsReq) (out : DnsOutcome) : Option HealthyEnv :=
  if !env.wf || isCriticalFault out then
    none
  else
    match allowedStep env.state req out with
    | none => none
    | some s' =>
      if isEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Healthy reference DNS resolution resolving pure and hybrid numeric IP literals directly (matching `glibc` `gaih_inet` `if_nametoindex`-before-`strtoul` precedence) and normalizing non-numeric oracle outcomes to exclude critical faults and `EINTR`. -/
def healthyModelResolve (oracle : DnsOracle) (host : String) (hints : ResolveHints := {}) :
    DnsOutcome :=
  if !validateHost host then
    .error invalidHostError
  else
    match parsePureNumericAddr? host with
    | some rawAddr =>
      match mapAddrForHints hints rawAddr with
      | some expAddr => .ok (expandSockType hints [expAddr])
      | none => .error (emptyPayloadError host hints)
    | none =>
      match parseHybridScopedNumericZone? host with
      | some (baseAddr, sc) =>
        if hints.family == .ipv4 then
          .error (emptyPayloadError host hints)
        else
          match normalizeOracleOutcome host hints (oracle.lookup host hints) with
          | .ok addrs => .ok addrs
          | .error _ => .ok (expandSockType hints [withIpv6Scope sc baseAddr])
      | none =>
        let base := normalizeOracleOutcome host hints (oracle.lookup host hints)
        if isCriticalFault base || isEintrOutcome base then
          .error (emptyPayloadError host hints)
        else
          base

/-- Reference `DnsOpsM (StateM HealthyEnv)` refining `healthyStep` across all hostnames and hints. -/
def healthyModelOps : DnsOpsM (StateM HealthyEnv) :=
  { getaddrinfo := fun host hints => do
      let env ← get
      return healthyModelResolve env.state.oracle host hints }

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthyDnsAt {W : Type} (proj : W → HealthyEnv)
    (ops : DnsOpsM (StateM W)) : Prop :=
  ∀ (w : W) (req : DnsReq),
    (proj w).wf = true →
    let (out, w') := (execDnsReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Universal healthy-world refinement predicate specialized to `StateM HealthyEnv`. -/
abbrev RefinesHealthyDns (ops : DnsOpsM (StateM HealthyEnv)) : Prop :=
  RefinesHealthyDnsAt id ops

/-- Every host accepted by `parsePureNumericAddr?` is non-empty and free of embedded NUL bytes (`validateHost = true`). -/
theorem validateHost_of_parsePureNumericAddr {host : String} {addr : DnsAddr}
    (hP : parsePureNumericAddr? host = some addr) :
    validateHost host = true := by
  unfold parsePureNumericAddr? at hP
  by_cases hne : isNonEmptyNoNulHost host = true
  · unfold validateHost
    unfold isNonEmptyNoNulHost at hne
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hne ⊢
    refine ⟨?_, ?_⟩
    · cases hl : host.toList with
      | nil => simp [hl] at hne
      | cons _ _ =>
        cases he : host.isEmpty
        · rfl
        · have : host = "" := String.isEmpty_iff.mp he
          subst this; simp at hl
    · cases hAny : host.toList.any (· == '\x00') with
      | false => simp [String.any, hAny]
      | true =>
        rw [List.any_eq_true] at hAny
        rcases hAny with ⟨c, hcMem, hcEq⟩
        have hc0 : c = Char.ofNat 0 := eq_of_beq hcEq
        subst hc0
        have hCont : host.toList.contains (Char.ofNat 0) = true := List.contains_iff_mem.mpr hcMem
        rw [hne.2] at hCont
        contradiction
  · simp [hne] at hP

/-- Every host accepted by `parseHybridScopedNumericZone?` is non-empty and free of embedded NUL bytes (`validateHost = true`). -/
theorem validateHost_of_parseHybridScopedNumericZone {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hH : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    validateHost host = true := by
  unfold parseHybridScopedNumericZone? at hH
  by_cases hne : isNonEmptyNoNulHost host = true
  · unfold validateHost
    unfold isNonEmptyNoNulHost at hne
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hne ⊢
    refine ⟨?_, ?_⟩
    · cases hl : host.toList with
      | nil => simp [hl] at hne
      | cons _ _ =>
        cases he : host.isEmpty
        · rfl
        · have : host = "" := String.isEmpty_iff.mp he
          subst this; simp at hl
    · cases hAny : host.toList.any (· == '\x00') with
      | false => simp [String.any, hAny]
      | true =>
        rw [List.any_eq_true] at hAny
        rcases hAny with ⟨c, hcMem, hcEq⟩
        have hc0 : c = Char.ofNat 0 := eq_of_beq hcEq
        subst hc0
        have hCont : host.toList.contains (Char.ofNat 0) = true := List.contains_iff_mem.mpr hcMem
        rw [hne.2] at hCont
        contradiction
  · simp [hne] at hH

/-- Every `baseAddr` produced by `parseHybridScopedNumericZone?` satisfies `allowsSymbolicIpv6Zone baseAddr = true`. -/
theorem allowsSymbolicIpv6Zone_of_parseHybridScopedNumericZone {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hH : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    allowsSymbolicIpv6Zone baseAddr = true := by
  unfold parseHybridScopedNumericZone? at hH
  by_cases hne : isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hH
    cases h4 : parseIpv4Aton? host with
    | some _ => simp [h4] at hH
    | none =>
      simp only [h4] at hH
      cases h6 : parseIpv6SplitZone? host with
      | none => simp [h6] at hH
      | some p =>
        rcases p with ⟨mk, z?⟩
        cases z? with
        | none => simp [h6] at hH
        | some zoneCs =>
          simp only [h6] at hH
          by_cases hlen : zoneCs.length < 16
          · simp only [hlen, ↓reduceIte] at hH
            cases hm : mk 0 with
            | none => simp [hm] at hH
            | some bAddr =>
              cases hn : parseNumericZone? zoneCs with
              | none => simp [hm, hn] at hH
              | some scVal =>
                simp only [hm, hn] at hH
                by_cases hAl : allowsSymbolicIpv6Zone bAddr = true
                · simp only [hAl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hH
                  rw [← hH.1]
                  exact hAl
                · simp [hAl] at hH
          · simp [hlen] at hH
  · simp [hne] at hH

private theorem wordsToIpv6Addr_allowsSymbolic {ws : List Nat} {sc1 sc2 : UInt32} {a1 a2 : DnsAddr}
    (h1 : wordsToIpv6Addr ws sc1 = some a1) (h2 : wordsToIpv6Addr ws sc2 = some a2) :
    allowsSymbolicIpv6Zone a1 = allowsSymbolicIpv6Zone a2 := by
  cases ws with | nil => simp [wordsToIpv6Addr] at h1 | cons w0 ws1 =>
  cases ws1 with | nil => simp [wordsToIpv6Addr] at h1 | cons w1 ws2 =>
  cases ws2 with | nil => simp [wordsToIpv6Addr] at h1 | cons w2 ws3 =>
  cases ws3 with | nil => simp [wordsToIpv6Addr] at h1 | cons w3 ws4 =>
  cases ws4 with | nil => simp [wordsToIpv6Addr] at h1 | cons w4 ws5 =>
  cases ws5 with | nil => simp [wordsToIpv6Addr] at h1 | cons w5 ws6 =>
  cases ws6 with | nil => simp [wordsToIpv6Addr] at h1 | cons w6 ws7 =>
  cases ws7 with | nil => simp [wordsToIpv6Addr] at h1 | cons w7 ws8 =>
  cases ws8 with
  | cons _ _ => simp [wordsToIpv6Addr] at h1
  | nil =>
    simp only [wordsToIpv6Addr, Option.some.injEq] at h1 h2
    subst h1; subst h2
    rfl

private theorem parseIpv6Core_exists_words {addrCs : List Char} {mkFn : UInt32 → Option DnsAddr}
    (h : parseIpv6Core? addrCs = some mkFn) :
    ∃ ws : List Nat, mkFn = wordsToIpv6Addr ws := by
  unfold parseIpv6Core? at h
  by_cases hBad : (addrCs.isEmpty || decide (addrCs.length > 64)) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Bind.bind, Option.bind] at h
    cases hSplit : splitDoubleColonChars addrCs with
    | nil => simp [hSplit] at h
    | cons first rest =>
      cases rest with
      | nil =>
        simp only [hSplit] at h
        cases hP1 : parseIpv6Parts? true first with
        | none => simp [hP1] at h
        | some ws =>
          simp only [hP1] at h
          by_cases hne8 : (ws.length != 8) = true
          · simp [hne8] at h
          · simp only [hne8, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
            exact ⟨ws, h.symm⟩
      | cons second rest2 =>
        cases rest2 with
        | cons _ _ => simp [hSplit] at h
        | nil =>
          simp only [hSplit] at h
          cases hL : parseIpv6Parts? false first with
          | none => simp [hL] at h
          | some lhs =>
            simp only [hL] at h
            cases hR : parseIpv6Parts? true second with
            | none => simp [hR] at h
            | some rhs =>
              simp only [hR] at h
              by_cases hge : lhs.length + rhs.length ≥ 8
              · simp [hge] at h
              · simp only [hge, ↓reduceIte, Option.some.injEq] at h
                exact ⟨lhs ++ List.replicate (8 - (lhs.length + rhs.length)) 0 ++ rhs, h.symm⟩

/-- `parsePureNumericAddr?` and `parseHybridScopedNumericZone?` are mutually exclusive: every hybrid numeric-scoped literal yields `parsePureNumericAddr? host = none`. -/
theorem parsePureNumericAddr_none_of_parseHybridScopedNumericZone
    {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hHyb : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    parsePureNumericAddr? host = none := by
  unfold parseHybridScopedNumericZone? at hHyb
  unfold parsePureNumericAddr?
  by_cases hne : isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hHyb ⊢
    cases h4 : parseIpv4Aton? host with
    | some _ => simp [h4] at hHyb
    | none =>
      simp only [h4] at hHyb ⊢
      cases h6 : parseIpv6SplitZone? host with
      | none => simp [h6] at hHyb
      | some p =>
        rcases p with ⟨mk, z?⟩
        cases z? with
        | none => simp [h6] at hHyb
        | some zoneCs =>
          simp only [h6] at hHyb ⊢
          by_cases hlen : zoneCs.length < 16
          · simp only [hlen, ↓reduceIte] at hHyb
            cases hm0 : mk 0 with
            | none => simp [hm0] at hHyb
            | some bAddr =>
              cases hn : parseNumericZone? zoneCs with
              | none => simp [hm0, hn] at hHyb
              | some scVal =>
                simp only [hm0, hn] at hHyb ⊢
                by_cases hAl : allowsSymbolicIpv6Zone bAddr = true
                · simp only [hAl, ↓reduceIte] at hHyb
                  cases hms : mk scVal with
                  | none => rfl
                  | some addrSc =>
                    dsimp only
                    unfold parseIpv6SplitZone? at h6
                    cases hCore : parseIpv6Core? (splitFirstZoneAux host.toList []).1 with
                    | none => simp [hCore] at h6
                    | some mkFn =>
                      have hMkEq : mkFn = mk := by
                        simp only [hCore, Option.some.injEq, Prod.mk.injEq] at h6
                        exact h6.1
                      subst hMkEq
                      rcases parseIpv6Core_exists_words hCore with ⟨ws, hWs⟩
                      rw [hWs] at hm0 hms
                      have hEqAl := wordsToIpv6Addr_allowsSymbolic hm0 hms
                      rw [← hEqAl]
                      simp [hAl, hlen]
                · simp [hAl] at hHyb
          · simp [hlen] at hHyb
  · simp [hne] at hHyb

/-- Every non-numeric host (`isNumericHostLiteral host = false`) returns `none` under `parsePureNumericAddr?`. -/
theorem parsePureNumericAddr_none_of_not_numericLiteral {host : String}
    (hNonNum : isNumericHostLiteral host = false) :
    parsePureNumericAddr? host = none := by
  unfold isNumericHostLiteral at hNonNum
  unfold parsePureNumericAddr?
  by_cases hne : isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.true_and, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hNonNum
    simp [hne, hNonNum.1, hNonNum.2]
  · have hneF : isNonEmptyNoNulHost host = false := Bool.eq_false_iff.mpr hne
    simp [hneF]

/-- Every non-numeric host (`isNumericHostLiteral host = false`) returns `none` under `parseHybridScopedNumericZone?`. -/
theorem parseHybridScopedNumericZone_none_of_not_numericLiteral {host : String}
    (hNonNum : isNumericHostLiteral host = false) :
    parseHybridScopedNumericZone? host = none := by
  unfold isNumericHostLiteral at hNonNum
  unfold parseHybridScopedNumericZone?
  by_cases hne : isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.true_and, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hNonNum
    simp [hne, hNonNum.1, hNonNum.2]
  · have hneF : isNonEmptyNoNulHost host = false := Bool.eq_false_iff.mpr hne
    simp [hneF]

end LeanSwe.LinuxSyscall.Dns

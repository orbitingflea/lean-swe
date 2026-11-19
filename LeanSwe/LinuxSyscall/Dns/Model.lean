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

/-- Parse pure platform-independent numeric IPv4 (`inet_aton`) or IPv6 (no zone or numeric `%<u32>` scope ID) literals. -/
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
        | some sc => mk sc
        | none => none

/-- If `host` is an IPv6 literal with an empty or non-`uint32` `%<zone>` suffix (`strchr('%')`), return its base address (`scopeId = 0`) and raw zone bytes. -/
def parseScopedNonNumericZone? (host : String) : Option (DnsAddr × List Char) :=
  if !isNonEmptyNoNulHost host then none
  else
    match parsePureNumericAddr? host with
    | some _ => none
    | none =>
      match parseIpv6SplitZone? host with
      | some (mk, some zoneCs) =>
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

private def withIpv6Scope (sc : UInt32) : DnsAddr → DnsAddr
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

/-- Return `true` iff `host` is a numeric or non-v4-mapped zoned IP literal whose address family conflicts with `hints.family` (`EAI_ADDRFAMILY`). -/
def isNumericFamilyMismatch (host : String) (hints : ResolveHints) : Bool :=
  match parsePureNumericAddr? host with
  | some rawAddr => (mapAddrForHints hints rawAddr).isNone
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
  else if (parsePureNumericAddr? host).isSome then
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

end LeanSwe.LinuxSyscall.Dns

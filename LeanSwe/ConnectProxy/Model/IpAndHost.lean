import LeanSwe.ConnectProxy.Types

namespace LeanSwe.ConnectProxy.Model

open LeanSwe.ConnectProxy


/-- Compute a 32-bit network-order bitmask with `prefixLen` leading `1` bits (`0` when `prefixLen = 0`). -/
def ipv4Mask (prefixLen : Nat) : UInt32 :=
  if prefixLen == 0 then 0
  else if prefixLen ≥ 32 then 0xffffffff
  else (0xffffffff : UInt32) <<< UInt32.ofNat (32 - prefixLen)

/-- Compute a 64-bit network-order bitmask with `bits` leading `1` bits (`0` when `bits = 0`). -/
def u64TopMask (bits : Nat) : UInt64 :=
  if bits == 0 then 0
  else if bits ≥ 64 then 0xffffffffffffffff
  else (0xffffffffffffffff : UInt64) <<< UInt64.ofNat (64 - bits)

/-- Compute the `(hiMask, loMask)` 128-bit network-order bitmask pair for an IPv6 `prefixLen`. -/
def ipv6Masks (prefixLen : Nat) : UInt64 × UInt64 :=
  if prefixLen ≤ 64 then
    (u64TopMask prefixLen, 0)
  else
    (0xffffffffffffffff, u64TopMask (prefixLen - 64))

/-- Return `true` iff `pfx` has a valid CIDR prefix length (`≤ 32` for IPv4, `≤ 128` for IPv6). -/
def isValidIpPrefix : IpPrefix → Bool
  | .v4 _ len => len ≤ 32
  | .v6 _ _ len => len ≤ 128

/-- Return `true` iff `pfx` is valid and `ip` shares the masked prefix bits of `pfx` in the same IP family. -/
def prefixContains (pfx : IpPrefix) (ip : IpAddr) : Bool :=
  match pfx, ip with
  | .v4 net len, .v4 addr =>
    len ≤ 32 && (net &&& ipv4Mask len) == (addr &&& ipv4Mask len)
  | .v6 netHi netLo len, .v6 hi lo =>
    len ≤ 128 &&
      let (mHi, mLo) := ipv6Masks len
      (netHi &&& mHi) == (hi &&& mHi) && (netLo &&& mLo) == (lo &&& mLo)
  | _, _ => false

/-- Return `true` iff `c` is an ASCII decimal digit (`'0'`–`'9'`). -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Return `true` iff `c` is an ASCII letter (`'a'`–`'z'` or `'A'`–`'Z'`). -/
def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- Convert an uppercase ASCII letter to lowercase, leaving all other characters unchanged. -/
def toAsciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (c.toNat + 32)
  else
    c

/-- Decode a single hexadecimal character into `0..15`, or `none` if non-hex. -/
def hexCharVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c && c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else none

/-- Split `cs` on delimiter character `sep`, preserving empty segments. -/
def splitOnCharAux (sep : Char) (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: rest =>
    if c == sep then acc.reverse :: splitOnCharAux sep [] rest
    else splitOnCharAux sep (c :: acc) rest

/-- Split `cs` on delimiter character `sep`. -/
def splitOnChar (sep : Char) (cs : List Char) : List (List Char) :=
  splitOnCharAux sep [] cs

/-- Accumulate decimal digits into a `Nat`. -/
def parseDigitsAcc (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    if isAsciiDigit c then
      parseDigitsAcc (acc * 10 + (c.toNat - '0'.toNat)) cs
    else
      none

/-- Parse `1..maxLen` decimal digits with no leading zeros (`"0"` is valid, `"01"` is rejected). -/
def parseDecNoLeadingZero (cs : List Char) (maxLen : Nat) : Option Nat :=
  if cs.isEmpty || cs.length > maxLen then
    none
  else if cs.length > 1 && cs.head? == some '0' then
    none
  else
    parseDigitsAcc 0 cs

/-- Parse a strict 4-octet dotted-decimal IPv4 character list into a network-order `UInt32`. -/
def parseIpv4Chars (cs : List Char) : Option UInt32 :=
  match splitOnChar '.' cs with
  | [s0, s1, s2, s3] =>
    match parseDecNoLeadingZero s0 3, parseDecNoLeadingZero s1 3,
          parseDecNoLeadingZero s2 3, parseDecNoLeadingZero s3 3 with
    | some b0, some b1, some b2, some b3 =>
      if b0 ≤ 255 && b1 ≤ 255 && b2 ≤ 255 && b3 ≤ 255 then
        some ((UInt32.ofNat b0 <<< 24) ||| (UInt32.ofNat b1 <<< 16) |||
              (UInt32.ofNat b2 <<< 8) ||| UInt32.ofNat b3)
      else
        none
    | _, _, _, _ => none
  | _ => none

/-- Accumulate hexadecimal digits into a `Nat`. -/
def parseHexAcc (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    match hexCharVal? c with
    | some v => parseHexAcc (acc * 16 + v) cs
    | none => none

/-- Parse a 1-to-4-character hexadecimal IPv6 hextet into `UInt16`. -/
def parseHexGroup (cs : List Char) : Option UInt16 :=
  if cs.isEmpty || cs.length > 4 then
    none
  else
    match parseHexAcc 0 cs with
    | some v => some (UInt16.ofNat v)
    | none => none

/-- Return `true` iff `cs` contains two adjacent colons `"::"`. -/
def hasDoubleColon : List Char → Bool
  | ':' :: ':' :: _ => true
  | _ :: rest => hasDoubleColon rest
  | [] => false

/-- Locate at most one `"::"` compression marker in `cs`, rejecting `":::"` and multiple `"::"` runs. -/
def splitDoubleColonAux (acc : List Char) : List Char → Option (Option (List Char × List Char))
  | [] => some none
  | ':' :: ':' :: rest =>
    if rest.head? == some ':' || hasDoubleColon rest then
      none
    else
      some (some (acc.reverse, rest))
  | c :: rest => splitDoubleColonAux (c :: acc) rest

/-- Parse colon-separated IPv6 groups into `UInt16` hextets, optionally allowing a trailing IPv4 dotted-quad. -/
def parseHextetGroups (allowTrailingV4 : Bool) : List (List Char) → Option (List UInt16)
  | [] => none
  | [lastGrp] =>
    if allowTrailingV4 && lastGrp.contains '.' then
      match parseIpv4Chars lastGrp with
      | some v4 =>
        some [UInt16.ofNat (v4 >>> 16).toNat, UInt16.ofNat (v4 &&& 0xffff).toNat]
      | none => none
    else
      (parseHexGroup lastGrp).map (fun h => [h])
  | grp :: rest =>
    match parseHexGroup grp, parseHextetGroups allowTrailingV4 rest with
    | some h, some tail => some (h :: tail)
    | _, _ => none

/-- Parse one side of `"::"` (empty yields `some []`; non-empty parses colon-separated groups). -/
def parseHextetSide (allowTrailingV4 : Bool) (cs : List Char) : Option (List UInt16) :=
  if cs.isEmpty then
    some []
  else
    parseHextetGroups allowTrailingV4 (splitOnChar ':' cs)

/-- Pack exactly 8 `UInt16` hextets into `(hi, lo)` `UInt64` words. -/
def packHextets8 : List UInt16 → Option (UInt64 × UInt64)
  | [h0, h1, h2, h3, h4, h5, h6, h7] =>
    let hi :=
      (h0.toUInt64 <<< 48) ||| (h1.toUInt64 <<< 32) |||
      (h2.toUInt64 <<< 16) ||| h3.toUInt64
    let lo :=
      (h4.toUInt64 <<< 48) ||| (h5.toUInt64 <<< 32) |||
      (h6.toUInt64 <<< 16) ||| h7.toUInt64
    some (hi, lo)
  | _ => none

/-- Parse an RFC 4291 IPv6 literal (without brackets, zone ID, or CIDR `/prefix`) into `(hi, lo)`. -/
def parseIpv6Chars (cs : List Char) : Option (UInt64 × UInt64) :=
  if cs.isEmpty || cs.contains '*' || cs.contains '%' || cs.contains '/' then
    none
  else
    match splitDoubleColonAux [] cs with
    | none => none
    | some none =>
      match parseHextetGroups true (splitOnChar ':' cs) with
      | some hs => if hs.length == 8 then packHextets8 hs else none
      | none => none
    | some (some (leftCs, rightCs)) =>
      match parseHextetSide false leftCs, parseHextetSide true rightCs with
      | some lhs, some rhs =>
        if lhs.length + rhs.length < 8 then
          let pad := List.replicate (8 - (lhs.length + rhs.length)) (0 : UInt16)
          packHextets8 (lhs ++ pad ++ rhs)
        else
          none
      | _, _ => none

/-- Parse a strict IPv4 (`a.b.c.d`) or RFC 4291 IPv6 literal into `IpAddr`. -/
def parseIpAddr (s : String) : Except ProxyError IpAddr :=
  let cs := s.toList
  if cs.contains '*' then
    .error { kind := .invalidInput, message := s!"wildcard '*' is not permitted in IP address: '{s}'" }
  else if cs.contains ':' then
    match parseIpv6Chars cs with
    | some (hi, lo) => .ok (.v6 hi lo)
    | none => .error { kind := .invalidInput, message := s!"invalid IPv6 address: '{s}'" }
  else
    match parseIpv4Chars cs with
    | some v4 => .ok (.v4 v4)
    | none => .error { kind := .invalidInput, message := s!"invalid IPv4 address: '{s}'" }

/-- Parse a single IPv4/IPv6 literal or canonical CIDR `/prefix` block into `IpPrefix`. -/
def parseIpPrefix (s : String) : Except ProxyError IpPrefix :=
  let cs := s.toList
  if cs.contains '*' then
    .error { kind := .invalidInput, message := s!"wildcard '*' is not permitted in IP prefix: '{s}'" }
  else
    match splitOnChar '/' cs with
    | [addrCs] =>
      match parseIpAddr (String.ofList addrCs) with
      | .ok (.v4 a) => .ok (.v4 a 32)
      | .ok (.v6 hi lo) => .ok (.v6 hi lo 128)
      | .error e => .error e
    | [addrCs, lenCs] =>
      match parseIpAddr (String.ofList addrCs), parseDecNoLeadingZero lenCs 3 with
      | .ok (.v4 a), some len =>
        if len ≤ 32 then
          if (a &&& ipv4Mask len) == a then
            .ok (.v4 a len)
          else
            .error { kind := .invalidInput, message := s!"IPv4 CIDR prefix has non-zero host bits: '{s}'" }
        else
          .error { kind := .invalidInput, message := s!"IPv4 CIDR prefix length exceeds 32: '{s}'" }
      | .ok (.v6 hi lo), some len =>
        if len ≤ 128 then
          let (mHi, mLo) := ipv6Masks len
          if (hi &&& mHi) == hi && (lo &&& mLo) == lo then
            .ok (.v6 hi lo len)
          else
            .error { kind := .invalidInput, message := s!"IPv6 CIDR prefix has non-zero host bits: '{s}'" }
        else
          .error { kind := .invalidInput, message := s!"IPv6 CIDR prefix length exceeds 128: '{s}'" }
      | .error e, _ => .error e
      | _, none => .error { kind := .invalidInput, message := s!"invalid CIDR prefix length in '{s}'" }
    | _ =>
      .error { kind := .invalidInput, message := s!"invalid CIDR prefix syntax: '{s}'" }

/-- Official IANA RFC 6890 / RFC 5771 non-globally-routable IPv4 blocks (including CGNAT and multicast). -/
def ianaIpv4NonGlobalPrefixes : List IpPrefix :=
  [ .v4 0x00000000 8
  , .v4 0x0a000000 8
  , .v4 0x64400000 10
  , .v4 0x7f000000 8
  , .v4 0xa9fe0000 16
  , .v4 0xac100000 12
  , .v4 0xc0000000 24
  , .v4 0xc0000200 24
  , .v4 0xc0a80000 16
  , .v4 0xc6120000 15
  , .v4 0xc6336400 24
  , .v4 0xcb007100 24
  , .v4 0xe0000000 4
  , .v4 0xf0000000 4
  ]

/-- Official IANA RFC 6890 globally-routable `/32` exceptions inside `192.0.0.0/24` (RFC 7723 PCP & RFC 8155 TURN). -/
def ianaIpv4GlobalExceptions : List IpPrefix :=
  [ .v4 0xc0000009 32
  , .v4 0xc000000a 32
  ]

/-- Return `true` iff 32-bit IPv4 `addr` is globally-routable unicast per IANA RFC 6890 and RFC 5771. -/
def isGlobalIpv4 (addr : UInt32) : Bool :=
  let ip := IpAddr.v4 addr
  !(ianaIpv4NonGlobalPrefixes.any (fun p => prefixContains p ip)) ||
    ianaIpv4GlobalExceptions.any (fun p => prefixContains p ip)

/-- IANA RFC 4291 / RFC 3587 IPv6 Global Unicast allocation root (`2000::/3`). -/
def ianaIpv6GlobalUnicastPrefix : IpPrefix :=
  .v6 0x2000000000000000 0x0000000000000000 3

/-- Official IANA RFC 6890 / RFC 4291 / RFC 9602 / RFC 9637 non-globally-routable IPv6 blocks (excluding `::ffff:0:0/96` and `64:ff9b::/96`, which delegate to their embedded IPv4). -/
def ianaIpv6NonGlobalPrefixes : List IpPrefix :=
  [ .v6 0x0000000000000000 0x0000000000000000 128
  , .v6 0x0000000000000000 0x0000000000000001 128
  , .v6 0x0064ff9b00010000 0x0000000000000000 48
  , .v6 0x0100000000000000 0x0000000000000000 64
  , .v6 0x2001000000000000 0x0000000000000000 23
  , .v6 0x20010db800000000 0x0000000000000000 32
  , .v6 0x2002000000000000 0x0000000000000000 16
  , .v6 0x3fff000000000000 0x0000000000000000 20
  , .v6 0x5f00000000000000 0x0000000000000000 16
  , .v6 0xfc00000000000000 0x0000000000000000 7
  , .v6 0xfe80000000000000 0x0000000000000000 10
  , .v6 0xfec0000000000000 0x0000000000000000 10
  , .v6 0xff00000000000000 0x0000000000000000 8
  ]

/-- Official IANA globally-routable IPv6 sub-allocations inside `2001::/23` (PCP, TURN, AMT, AS112-v6, ORCHIDv2, DRID). -/
def ianaIpv6GlobalExceptions : List IpPrefix :=
  [ .v6 0x2001000100000000 0x0000000000000001 128
  , .v6 0x2001000100000000 0x0000000000000002 128
  , .v6 0x2001000300000000 0x0000000000000000 32
  , .v6 0x2001000401120000 0x0000000000000000 48
  , .v6 0x2001002000000000 0x0000000000000000 28
  , .v6 0x2001003000000000 0x0000000000000000 28
  ]

/-- Construct an IPv4-mapped IPv6 address `::ffff:a.b.c.d` (`::ffff:0:0/96`). -/
def mkIpv4MappedIpv6 (v4 : UInt32) : IpAddr :=
  .v6 0 ((0x0000ffff00000000 : UInt64) ||| v4.toUInt64)

/-- Construct a deprecated RFC 4291 §2.5.5.1 IPv4-compatible IPv6 address `::a.b.c.d` (`::/96`, for `v4 > 1`). -/
def mkIpv4CompatibleIpv6 (v4 : UInt32) : IpAddr :=
  .v6 0 v4.toUInt64

/-- Construct an RFC 2765 SIIT IPv4-translated IPv6 address `::ffff:0:a.b.c.d` (`::ffff:0:0:0/96`). -/
def mkSiitIpv6 (v4 : UInt32) : IpAddr :=
  .v6 0 ((0xffff000000000000 : UInt64) ||| v4.toUInt64)

/-- Construct a Well-Known NAT64 IPv6 address `64:ff9b::a.b.c.d` (`64:ff9b::/96`). -/
def mkNat64WellKnownIpv6 (v4 : UInt32) : IpAddr :=
  .v6 0x0064ff9b00000000 v4.toUInt64

/-- Construct a Local-Use NAT64 `/96` NSP IPv6 address `64:ff9b:1:subHi:subLo_hi:subLo_lo:a.b.c.d` (`64:ff9b:1::/48`). -/
def mkNat64LocalIpv6 (v4 : UInt32) (subHi : UInt16 := 0) (subLo : UInt32 := 0) : IpAddr :=
  .v6 ((0x0064ff9b00010000 : UInt64) ||| subHi.toUInt64)
      ((subLo.toUInt64 <<< 32) ||| v4.toUInt64)

/-- Construct a Local-Use NAT64 RFC 6052 `/48` NSP IPv6 address under `64:ff9b:1::/48` (`u = 0`). -/
def mkNat64Local48Ipv6 (v4 : UInt32) (suffix40 : UInt64 := 0) : IpAddr :=
  .v6 ((0x0064ff9b00010000 : UInt64) ||| (v4 >>> 16).toUInt64)
      ((((v4 &&& 0xffff).toUInt64) <<< 40) ||| (suffix40 &&& 0xffffffffff))

/-- Construct a Local-Use NAT64 RFC 6052 `/56` NSP IPv6 address under `64:ff9b:1::/48` (`u = 0`). -/
def mkNat64Local56Ipv6 (sub8 : UInt8) (v4 : UInt32) (suffix32 : UInt32 := 0) : IpAddr :=
  .v6 ((0x0064ff9b00010000 : UInt64) ||| (sub8.toUInt64 <<< 8) ||| (v4 >>> 24).toUInt64)
      ((((v4 &&& 0xffffff).toUInt64) <<< 32) ||| suffix32.toUInt64)

/-- Construct a Local-Use NAT64 RFC 6052 `/64` NSP IPv6 address under `64:ff9b:1::/48` (`u = 0`). -/
def mkNat64Local64Ipv6 (sub16 : UInt16) (v4 : UInt32) (suffix24 : UInt32 := 0) : IpAddr :=
  .v6 ((0x0064ff9b00010000 : UInt64) ||| sub16.toUInt64)
      ((v4.toUInt64 <<< 24) ||| (suffix24 &&& 0xffffff).toUInt64)

/-- Construct a 6to4 IPv6 address under `2002::/16` carrying `v4` in bits 16..47. -/
def mk6to4Ipv6 (v4 : UInt32) (sla : UInt16 := 0) (iface : UInt64 := 1) : IpAddr :=
  .v6 ((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) iface

/-- Construct a Teredo IPv6 address under `2001::/32` carrying `serverV4` (bits 32..63) and inverted `clientV4` (bits 96..127). -/
def mkTeredoIpv6 (serverV4 : UInt32) (flagsPort : UInt32 := 0) (clientV4 : UInt32) : IpAddr :=
  .v6 ((0x2001000000000000 : UInt64) ||| serverV4.toUInt64)
      ((flagsPort.toUInt64 <<< 32) ||| (clientV4 ^^^ 0xffffffff).toUInt64)

/-- Extract all embedded IPv4 addresses (`IpAddr.v4`) from an IPv6 transition/translation address (`::ffff:0:0/96`, `::/96` `lo > 1`, `::ffff:0:0:0/96`, `64:ff9b::/96`, `64:ff9b:1::/48` `/96`+`/48`+`/56`+`/64`, `2002::/16`, `2001::/32`). -/
def embeddedIpv4Addrs : IpAddr → List IpAddr
  | .v4 _ => []
  | .v6 hi lo =>
    if hi == 0 && (lo >>> 32) == 0x0000ffff then
      [.v4 lo.toUInt32]
    else if hi == 0 && (lo >>> 32) == 0 && lo > 1 then
      [.v4 lo.toUInt32]
    else if hi == 0 && (lo >>> 32) == 0xffff0000 then
      [.v4 lo.toUInt32]
    else if hi == 0x0064ff9b00000000 && (lo >>> 32) == 0 then
      [.v4 lo.toUInt32]
    else if (hi >>> 16) == 0x0064ff9b0001 then
      let low96 : List IpAddr := [.v4 lo.toUInt32]
      let rfc6052Layouts : List IpAddr :=
        if ((lo >>> 56) &&& 0xff) == 0 then
          let v4Pl48 := ((hi <<< 16) ||| ((lo >>> 40) &&& 0xffff)).toUInt32
          let v4Pl56 := (((hi &&& 0xff) <<< 24) ||| ((lo >>> 32) &&& 0xffffff)).toUInt32
          let v4Pl64 := (lo >>> 24).toUInt32
          [.v4 v4Pl48, .v4 v4Pl56, .v4 v4Pl64]
        else
          []
      low96 ++ rfc6052Layouts
    else if (hi >>> 48) == 0x2002 then
      [.v4 (hi >>> 16).toUInt32]
    else if (hi >>> 32) == 0x20010000 then
      let serverV4 := hi.toUInt32
      let clientV4 := lo.toUInt32 ^^^ 0xffffffff
      [.v4 serverV4, .v4 clientV4]
    else
      []

/-- Return `true` iff `ip` is globally-routable unicast per IANA RFC 6890 / `2000::/3` (and any embedded IPv4 in `::ffff:0:0/96` or `64:ff9b::/96` is globally-routable). -/
def isGlobalIp : IpAddr → Bool
  | .v4 addr => isGlobalIpv4 addr
  | .v6 hi lo =>
    if hi == 0 && (lo >>> 32) == 0x0000ffff then
      isGlobalIpv4 lo.toUInt32
    else if hi == 0x0064ff9b00000000 && (lo >>> 32) == 0 then
      isGlobalIpv4 lo.toUInt32
    else
      let ip := IpAddr.v6 hi lo
      prefixContains ianaIpv6GlobalUnicastPrefix ip &&
      (!(ianaIpv6NonGlobalPrefixes.any (fun p => prefixContains p ip)) ||
        ianaIpv6GlobalExceptions.any (fun p => prefixContains p ip))

/-- Return `true` iff `ip` or any unwrapped embedded IPv4 in `ip` matches a prefix in `bans`. -/
def isBannedByPrefixes (bans : Array IpPrefix) (ip : IpAddr) : Bool :=
  let banList := bans.toList
  let emb := embeddedIpv4Addrs ip
  banList.any (fun b => prefixContains b ip || emb.any (fun v4 => prefixContains b v4))

/-- Evaluate `policy` on `ip` as `(inBase ∨ inExtraAllows) ∧ ¬ inExtraBans` with IPv4-in-IPv6 ban unwrapping. -/
def allowsIp (policy : IpPolicy) (ip : IpAddr) : Bool :=
  let inBase :=
    match policy.base with
    | .publicOnly => isGlobalIp ip
    | .empty => false
  let inExtraAllows := policy.extraAllows.toList.any (fun p => prefixContains p ip)
  (inBase || inExtraAllows) && !isBannedByPrefixes policy.extraBans ip

/-- Format a natural number `< 16` as a single lowercase hex character. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Format a 16-bit IPv6 hextet in minimal lowercase hex without leading zeros. -/
def formatHextet (h : UInt16) : String :=
  let n := h.toNat
  if n == 0 then "0"
  else
    let d3 := (n / 4096) % 16
    let d2 := (n / 256) % 16
    let d1 := (n / 16) % 16
    let d0 := n % 16
    if d3 != 0 then String.ofList [lowerHexDigit d3, lowerHexDigit d2, lowerHexDigit d1, lowerHexDigit d0]
    else if d2 != 0 then String.ofList [lowerHexDigit d2, lowerHexDigit d1, lowerHexDigit d0]
    else if d1 != 0 then String.ofList [lowerHexDigit d1, lowerHexDigit d0]
    else String.ofList [lowerHexDigit d0]

/-- Count consecutive zero hextets from the head of `hs`. -/
def leadingZeroRunLen : List UInt16 → Nat
  | [] => 0
  | h :: rest => if h == 0 then 1 + leadingZeroRunLen rest else 0

/-- Find the `(startIdx, len)` of the first longest zero-hextet run of length `≥ 2` per RFC 5952. -/
def bestZeroRunAux (idx bestStart bestLen : Nat) : List UInt16 → Nat × Nat
  | [] => (bestStart, bestLen)
  | h :: rest =>
    let runLen := leadingZeroRunLen (h :: rest)
    if runLen ≥ 2 && runLen > bestLen then
      bestZeroRunAux (idx + 1) idx runLen rest
    else
      bestZeroRunAux (idx + 1) bestStart bestLen rest

/-- Join formatted hextet strings with `":"`. -/
def joinColonStrings : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ ":" ++ joinColonStrings xs

/-- Format `(hi, lo)` as an RFC 5952 canonical lowercase IPv6 string. -/
def formatIpv6Canonical (hi lo : UInt64) : String :=
  let hs : List UInt16 :=
    [ ((hi >>> 48) &&& 0xffff).toUInt16
    , ((hi >>> 32) &&& 0xffff).toUInt16
    , ((hi >>> 16) &&& 0xffff).toUInt16
    , (hi &&& 0xffff).toUInt16
    , ((lo >>> 48) &&& 0xffff).toUInt16
    , ((lo >>> 32) &&& 0xffff).toUInt16
    , ((lo >>> 16) &&& 0xffff).toUInt16
    , (lo &&& 0xffff).toUInt16
    ]
  let (bestStart, bestLen) := bestZeroRunAux 0 0 0 hs
  if bestLen < 2 then
    joinColonStrings (hs.map formatHextet)
  else
    let pre := (hs.take bestStart).map formatHextet
    let post := (hs.drop (bestStart + bestLen)).map formatHextet
    match pre.isEmpty, post.isEmpty with
    | true, true => "::"
    | true, false => "::" ++ joinColonStrings post
    | false, true => joinColonStrings pre ++ "::"
    | false, false => joinColonStrings pre ++ "::" ++ joinColonStrings post

/-- Format a natural number in decimal (`0` -> `"0"`). -/
def formatNatDecAux (fuel n : Nat) (acc : List Char) : List Char :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let d := Char.ofNat ('0'.toNat + (n % 10))
    if n < 10 then d :: acc
    else formatNatDecAux f (n / 10) (d :: acc)

/-- Format a 32-bit IPv4 address in canonical dotted-decimal form. -/
def formatIpv4Canonical (addr : UInt32) : String :=
  let b0 := String.ofList (formatNatDecAux 4 ((addr >>> 24) &&& 0xff).toNat [])
  let b1 := String.ofList (formatNatDecAux 4 ((addr >>> 16) &&& 0xff).toNat [])
  let b2 := String.ofList (formatNatDecAux 4 ((addr >>> 8) &&& 0xff).toNat [])
  let b3 := String.ofList (formatNatDecAux 4 (addr &&& 0xff).toNat [])
  b0 ++ "." ++ b1 ++ "." ++ b2 ++ "." ++ b3

/-- Return `true` iff lowercase label `lbl` is an `inet_aton` decimal/octal or `0x` hex number (WHATWG numeric-TLD check). -/
def isInetAtonNumericLabel (lbl : List Char) : Bool :=
  !lbl.isEmpty &&
    (lbl.all isAsciiDigit ||
      match lbl with
      | '0' :: 'x' :: hexRest => hexRest.all (fun c => (hexCharVal? c).isSome)
      | _ => false)

/-- Return `true` iff `lbl` is a valid lowercase RFC 1123 DNS label (`1..63` chars of `a-z`, `0-9`, `-`, not starting/ending with `-`). -/
def isValidDnsLabel (lbl : List Char) : Bool :=
  !lbl.isEmpty &&
  lbl.length ≤ 63 &&
  lbl.head? != some '-' &&
  lbl.getLast? != some '-' &&
  lbl.all (fun c => ('a' ≤ c && c ≤ 'z') || isAsciiDigit c || c == '-')

/-- Normalize and validate a target host (domain name, IPv4 literal, or bracketed `[IPv6]` literal), returning `(canonicalHost, literalIp?)`. -/
def normalizeTargetHost (raw : String) : Except ProxyError (String × Option IpAddr) :=
  let cs := raw.toList
  if cs.isEmpty then
    .error { kind := .invalidInput, message := "target host must not be empty" }
  else if cs.contains '*' then
    .error { kind := .invalidInput, message := s!"wildcard '*' is not permitted in target host: '{raw}'" }
  else if cs.head? == some '[' || cs.contains ':' || cs.contains ']' then
    match cs with
    | '[' :: innerAndClose =>
      if innerAndClose.getLast? == some ']' then
        let inner := innerAndClose.dropLast
        if inner.contains '[' || inner.contains ']' || !inner.contains ':' then
          .error { kind := .invalidInput, message := s!"invalid bracketed IPv6 host: '{raw}'" }
        else
          match parseIpv6Chars inner with
          | some (hi, lo) =>
            let canon := formatIpv6Canonical hi lo
            let finalInner :=
              if !canon.toList.contains '[' && !canon.toList.contains ']' &&
                 !canon.toList.contains '*' && canon.toList.contains ':' &&
                 parseIpv6Chars canon.toList == some (hi, lo) then
                canon
              else
                String.ofList inner
            .ok ("[" ++ finalInner ++ "]", some (.v6 hi lo))
          | none =>
            .error { kind := .invalidInput, message := s!"invalid bracketed IPv6 host: '{raw}'" }
      else
        .error { kind := .invalidInput, message := s!"unclosed bracketed IPv6 host: '{raw}'" }
    | _ =>
      .error { kind := .invalidInput, message := s!"invalid unbracketed colon or bracket in host: '{raw}'" }
  else
    match parseIpv4Chars cs with
    | some v4 =>
      .ok (String.ofList cs, some (.v4 v4))
    | none =>
      let lower := cs.map toAsciiLowerChar
      let labels := splitOnChar '.' lower
      let lastLbl := labels.getLastD []
      if lower.length ≤ 253 && labels.all isValidDnsLabel && !isInetAtonNumericLabel lastLbl then
        .ok (String.ofList lower, none)
      else
        .error { kind := .invalidInput, message := s!"invalid target host: '{raw}'" }

/-- Extract `some ip` if `host` is a canonical IPv4 or bracketed `[IPv6]` literal, or `none` for a DNS domain. -/
def literalIpOfHost? (host : String) : Option IpAddr :=
  match normalizeTargetHost host with
  | .ok (_, ip?) => ip?
  | .error _ => none

/-- Validate and normalize a `TargetRule` (normalizing `host` and rejecting `port = 0`). -/
def normalizeTargetRule (rule : TargetRule) : Except ProxyError TargetRule :=
  if rule.port == 0 then
    .error { kind := .invalidInput, message := "target port 0 is not permitted" }
  else
    match normalizeTargetHost rule.host with
    | .ok (normHost, _) => .ok { host := normHost, port := rule.port }
    | .error e => .error e


end LeanSwe.ConnectProxy.Model

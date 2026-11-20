import LeanSwe.LinuxSyscall.Net.Model.State

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

/-- Encoded `sockaddr_un` byte length produced by `encode_unix_sockaddr` in `net_shim.c`. -/
def unixEncodedLen (p : ByteArray) : Nat :=
  if (p.size > 0 && p.get! 0 == 0) || p.size >= 108 then p.size + 2 else p.size + 3

/-- Kernel `familyMismatchErrno` for `bind` and `connect` when `addr.domain != d.domain`. -/
def familyMismatchErrno (dom : SockDomain) (addr : SockAddr) : Errno :=
  match dom with
  | .unix => Errno.EINVAL
  | .inet =>
    match addr with
    | .ipv6 _ _ _ _ _ => Errno.EAFNOSUPPORT
    | .unix p => if unixEncodedLen p < 16 then Errno.EINVAL else Errno.EAFNOSUPPORT
    | .ipv4 _ _ => Errno.EINVAL
  | .inet6 =>
    match addr with
    | .ipv4 _ _ => Errno.EINVAL
    | .unix p => if unixEncodedLen p < 24 then Errno.EINVAL else Errno.EAFNOSUPPORT
    | .ipv6 _ _ _ _ _ => Errno.EINVAL

/-- Default unbound `SockAddr` returned by Linux `getsockname` prior to `bind`. -/
def defaultUnboundAddr : SockDomain → SockAddr
  | .inet => .ipv4 0 0
  | .inet6 => .ipv6 0 0 0 0 0
  | .unix => .unix (ByteArray.mk #[])

/-- Replace the port number of an IPv4/IPv6 `SockAddr`. -/
def SockAddr.withPort (sa : SockAddr) (p : UInt16) : SockAddr :=
  match sa with
  | .ipv4 ip _ => .ipv4 ip p
  | .ipv6 hi lo _ fl sc => .ipv6 hi lo p fl sc
  | .unix path => .unix path

/-- Extract the port number of an IPv4/IPv6 `SockAddr`, or `none` for `AF_UNIX`. -/
def SockAddr.port? : SockAddr → Option UInt16
  | .ipv4 _ p | .ipv6 _ _ p _ _ => some p
  | .unix _ => none

/-- Returns `true` iff `ip` is in the IPv4 `127.0.0.0/8` loopback unicast block (excluding `127.255.255.255`). -/
def isIpv4Loopback (ip : UInt32) : Bool :=
  (ip >>> 24) == 127 && ip != 0x7fffffff

/-- Returns `true` iff `ip` is IPv4 multicast (`224.0.0.0/4`) or broadcast (`255.255.255.255`, `127.255.255.255`). -/
def isIpv4McastOrBcast (ip : UInt32) : Bool :=
  (ip >>> 28) == 0xe || ip == 0xffffffff || ip == 0x7fffffff

/-- Returns `true` iff `ip` is IPv4 broadcast (`255.255.255.255` or `127.255.255.255`). -/
def isIpv4Bcast (ip : UInt32) : Bool :=
  ip == 0xffffffff || ip == 0x7fffffff

/-- Resolve an IPv4 connect destination (`0.0.0.0` routes to `127.0.0.1`; `127.x.y.z` stays `127.x.y.z`). -/
def resolveLoopbackTargetV4 (ip : UInt32) : UInt32 :=
  if ip == INADDR_ANY then INADDR_LOOPBACK else ip

/-- Encode an IPv4 address `ip` into the lower 64 bits of an IPv4-mapped IPv6 address `::ffff:a.b.c.d`. -/
def ipv4ToMappedV6Lo (ip : UInt32) : UInt64 :=
  0x0000ffff00000000 ||| ip.toUInt64

/-- Extract the embedded IPv4 address if `(hi, lo)` is `::ffff:a.b.c.d`. -/
def mappedV4Addr? (hi lo : UInt64) : Option UInt32 :=
  if hi == 0 && (lo &&& 0xffffffff00000000) == 0x0000ffff00000000 then
    some (UInt32.ofNat (lo &&& 0xffffffff).toNat)
  else none

/-- Returns `true` iff `sa` targets IPv4/mapped-IPv4 broadcast. -/
def isBcastTargetAddr : SockAddr → Bool
  | .ipv4 ip _ => isIpv4Bcast ip
  | .ipv6 hi lo _ _ _ => ((mappedV4Addr? hi lo).map isIpv4Bcast).getD false
  | .unix _ => false

/-- Returns `true` iff `sa` targets multicast or broadcast (`224.0.0.0/4`, `ff00::/8`, or broadcast). -/
def isMcastOrBcastTargetAddr : SockAddr → Bool
  | .ipv4 ip _ => isIpv4McastOrBcast ip
  | .ipv6 hi lo _ _ _ => (hi >>> 56) == 0xff || ((mappedV4Addr? hi lo).map isIpv4McastOrBcast).getD false
  | .unix _ => false

/-- Extract the embedded IPv4 `127.0.0.0/8` or `0.0.0.0` address if `(hi, lo)` is `::ffff:loopback/0`. -/
def mappedLoopbackV4? (hi lo : UInt64) : Option UInt32 :=
  match mappedV4Addr? hi lo with
  | some ip => if isIpv4Loopback ip || ip == INADDR_ANY then some ip else none
  | none => none

/-- Resolve an IPv4 connect destination using a bound client's loopback IP when `tip == 0.0.0.0`. -/
def resolveLoopbackTargetForClientV4 (cliSa? : Option SockAddr) (tip : UInt32) : UInt32 :=
  if tip == INADDR_ANY then
    match cliSa? with
    | some (.ipv4 cip _) => if isIpv4Loopback cip then cip else INADDR_LOOPBACK
    | some (.ipv6 chi clo _ _ _) =>
      match mappedLoopbackV4? chi clo with
      | some cip => if cip != INADDR_ANY then cip else INADDR_LOOPBACK
      | none => INADDR_LOOPBACK
    | _ => INADDR_LOOPBACK
  else resolveLoopbackTargetV4 tip

/-- Resolve wildcard `0.0.0.0`, `::ffff:0.0.0.0`, and `[::]` (when client local IP is `::ffff:*`) target addresses. -/
def resolveTargetAddrForClient (cliSa? : Option SockAddr) (targetAddr : SockAddr) : SockAddr :=
  match targetAddr with
  | .ipv4 tip tp => .ipv4 (resolveLoopbackTargetForClientV4 cliSa? tip) tp
  | .ipv6 thi tlo tp fl sc =>
    if thi == 0 && tlo == 0 then
      match cliSa? with
      | some (.ipv6 chi clo _ _ _) =>
        if (mappedV4Addr? chi clo).isSome then
          .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) tp fl sc
        else .ipv6 0 0 tp fl sc
      | _ => .ipv6 0 0 tp fl sc
    else
      match mappedV4Addr? thi tlo with
      | some tip => .ipv6 0 (ipv4ToMappedV6Lo (resolveLoopbackTargetForClientV4 cliSa? tip)) tp fl sc
      | none => .ipv6 thi tlo tp fl sc
  | .unix p => .unix p

/-- Returns `true` iff `sa` is IPv6 link-local `fe80::/10`. -/
def isIpv6LinkLocal : SockAddr → Bool
  | .ipv6 hi _ _ _ _ => (hi &&& 0xffc0000000000000) == 0xfe80000000000000
  | _ => false

/-- Returns `true` iff `sa` is interface-local (`ff01::/16`) or link-local (`ff02::/16`) IPv6 multicast. -/
def isIpv6ScopedMulticast : SockAddr → Bool
  | .ipv6 hi _ _ _ _ =>
    (hi >>> 56) == 0xff &&
      let mscope := (hi >>> 48) &&& 0xf
      mscope == 1 || mscope == 2
  | _ => false

/-- Returns `true` iff `sa` requires an IPv6 scope ID (`fe80::/10`, or UDP `ff01::/16` / `ff02::/16`). -/
def ipv6NeedsScopeId (sockType : SockType) (sa : SockAddr) : Bool :=
  isIpv6LinkLocal sa || (sockType == .dgram && isIpv6ScopedMulticast sa)

/-- Extract nonzero `scopeId` when `sa` binds `sk->sk_bound_dev_if` for `sockType`. -/
def ipv6ScopedIfindex? (sockType : SockType) (sa : SockAddr) : Option UInt32 :=
  match sa with
  | .ipv6 _ _ _ _ scope => if ipv6NeedsScopeId sockType sa && scope != 0 then some scope else none
  | _ => none

/-- Returns `true` iff `sa` is IPv6 link-local `fe80::/10` with missing `scopeId == 0`. -/
def isIpv6LinkLocalNoScope : SockAddr → Bool
  | .ipv6 hi _ _ _ scope => (hi &&& 0xffc0000000000000) == 0xfe80000000000000 && scope == 0
  | _ => false

/-- Extract nonzero `scopeId` when `sa` is an IPv6 link-local `fe80::/10` address (`tcp_v6_connect` binds `sk_bound_dev_if`). -/
def ipv6LinkLocalScope? : SockAddr → Option UInt32
  | .ipv6 hi _ _ _ scope =>
    if (hi &&& 0xffc0000000000000) == 0xfe80000000000000 && scope != 0 then some scope else none
  | _ => none

/-- Returns `true` iff `sa` is IPv6 multicast `ff00::/8`. -/
def isIpv6Multicast : SockAddr → Bool
  | .ipv6 hi _ _ _ _ => (hi >>> 56) == 0xff
  | _ => false

/-- Returns `true` iff `sa` is `::ffff:a.b.c.d`. -/
def isIpv4MappedV6Addr : SockAddr → Bool
  | .ipv6 hi lo _ _ _ => (mappedV4Addr? hi lo).isSome
  | _ => false

/-- Normalize IPv6 `flowinfo` (`0`) and scoped `scopeId` on `bind` per Linux `__inet6_bind`. -/
def normalizeBindAddr (sa : SockAddr) (fallbackScope : UInt32 := 0) : SockAddr :=
  match sa with
  | .ipv6 hi lo p _ sc =>
    let isLinkLocal := (hi &&& 0xffc0000000000000) == 0xfe80000000000000 ||
      ((hi >>> 56) == 0xff && (((hi >>> 48) &&& 0xf) == 1 || ((hi >>> 48) &&& 0xf) == 2))
    let effSc := if isLinkLocal then (if sc != 0 then sc else fallbackScope) else 0
    .ipv6 hi lo p 0 effSc
  | other => other

/-- Returns `true` iff IPv6 `bind`/`connect` rejects `sa` with `EINVAL` due to missing scope (with `boundDevIf == 0`) or non-UDP multicast. -/
def isInvalidV6LinkOrMulticast (sockType : SockType) (sa : SockAddr) (boundDevIf : UInt32 := 0) : Bool :=
  (isIpv6LinkLocalNoScope sa && boundDevIf == 0) ||
    match sa with
    | .ipv6 hi _ _ _ sc =>
      (hi >>> 56) == 0xff &&
        (sockType != .dgram ||
          let mscope := (hi >>> 48) &&& 0xf
          (mscope == 1 || mscope == 2) && sc == 0 && boundDevIf == 0)
    | _ => false

/-- Returns `true` iff `sa` locks an explicit non-wildcard local IP (`SOCK_BINDADDR_LOCK`). -/
def isBindAddrLockedSa : SockAddr → Bool
  | .ipv4 ip _ => ip != INADDR_ANY
  | .ipv6 hi lo _ _ _ => !(hi == 0 && lo == 0)
  | .unix _ => false

/-- Returns `true` iff `lo` is currently down after having been up at least once. -/
def loDownWasUp : LoState → Bool
  | .down _ true => true
  | _ => false

/-- Detect cross-type IPv6 mapped (`::ffff:...`) vs native (`::1`/multicast) mismatch on `connect`. -/
def v6MappedNativeMismatchErrno? (loc? : Option SockAddr) (target : SockAddr)
    (bindAddrLocked : Bool := true) (loDown127 : Bool := false) : Option Errno :=
  match loc?, target with
  | some (.ipv6 lhi llo _ _ _), .ipv6 thi tlo _ _ _ =>
    let locMapped := (mappedV4Addr? lhi llo).isSome
    let tgtMapped := (mappedV4Addr? thi tlo).isSome
    let locNonWildNative := !(lhi == 0 && llo == 0) && !locMapped
    let tgtNonWildNative := !(thi == 0 && tlo == 0) && !tgtMapped
    if locMapped && tgtNonWildNative then some Errno.EAFNOSUPPORT
    else if bindAddrLocked && locNonWildNative && tgtMapped then some Errno.ENETUNREACH
    else
      match mappedV4Addr? lhi llo with
      | some lip =>
        if bindAddrLocked && isIpv4McastOrBcast lip then
          if lip == 0x7fffffff then
            if loDown127 then none else some Errno.ENETUNREACH
          else some Errno.EINVAL
        else none
      | none => none
  | _, _ => none

/-- Returns `true` iff `sa` is locally bindable (wildcard, loopback, `AF_UNIX`, or multicast/broadcast `RTN_MULTICAST`/`RTN_BROADCAST`). -/
def isLocalBindableAddr : SockAddr → Bool
  | .ipv4 ip _ => ip == INADDR_ANY || isIpv4Loopback ip || isIpv4McastOrBcast ip
  | .ipv6 hi lo _ _ _ =>
    (hi == 0 && (lo == 0 || lo == 1)) ||
    (hi >>> 56) == 0xff ||
    (mappedLoopbackV4? hi lo).isSome ||
    ((mappedV4Addr? hi lo).map isIpv4McastOrBcast).getD false
  | .unix _ => true

/-- Returns `true` iff `sa` is non-wildcard local IPv6 (`::1` or `::ffff:127.x.y.z`), whose `lo`-down bind can return `EADDRNOTAVAIL`. -/
def isLocalNonWildcardV6 : SockAddr → Bool
  | .ipv6 hi lo _ _ _ =>
    (hi == 0 && lo == 1) ||
    match mappedLoopbackV4? hi lo with
    | some ip => ip != INADDR_ANY
    | none => false
  | _ => false

/-- Returns `true` iff `sa` targets an IPv4/IPv6 loopback destination. -/
def isLoopbackTargetAddr : SockAddr → Bool
  | .ipv4 ip _ => ip == INADDR_ANY || isIpv4Loopback ip
  | .ipv6 hi lo _ _ _ => (hi == 0 && (lo == 0 || lo == 1)) || (mappedLoopbackV4? hi lo).isSome
  | .unix _ => false

/-- Resolve wildcard local IP to loopback when a bound socket connects. -/
def concretizeClientLocalAddr (locSa : SockAddr) (targetAddr? : Option SockAddr := none) : SockAddr :=
  match locSa with
  | .ipv4 ip p => .ipv4 (if ip == INADDR_ANY then INADDR_LOOPBACK else ip) p
  | .ipv6 hi lo p fl sc =>
    if hi == 0 && lo == 0 then
      match targetAddr? with
      | some (.ipv6 thi tlo _ _ _) =>
        if (mappedV4Addr? thi tlo).isSome then
          .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p fl sc
        else .ipv6 0 1 p fl sc
      | _ => .ipv6 0 1 p fl sc
    else if mappedV4Addr? hi lo == some INADDR_ANY then
      .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p fl sc
    else .ipv6 hi lo p fl sc
  | .unix path => .unix path

/-- Returns `true` iff binding `sa` sets `SOCK_BINDADDR_LOCK` while leaving `inet->inet_saddr = 0` (`224.0.0.0/4`, `255.255.255.255`, or `::ffff:0.0.0.0` / `::ffff:<mcast/bcast>`). -/
def isAddrLockedZeroInetSaddr : SockAddr → Bool
  | .ipv4 ip _ => isIpv4McastOrBcast ip
  | .ipv6 hi lo _ _ _ =>
    match mappedV4Addr? hi lo with
    | some ip => ip == INADDR_ANY || isIpv4McastOrBcast ip
    | none => false
  | .unix _ => false

/-- Concretize a bound client local address on `connect`, updating `SOCK_STREAM` zero-`inet_saddr` sources (`224.0.0.0/4`, `255.255.255.255`, or fresh-netns `lo`-down IPv4 binds) to `127.0.0.1`. -/
def concretizeStreamOrClientLocalAddr (sockType : SockType) (locSa targetAddr : SockAddr)
    (inetSaddrZero : Bool := false) : SockAddr :=
  match locSa with
  | .ipv4 ip p =>
    if sockType == .stream && (isIpv4McastOrBcast ip || inetSaddrZero) then .ipv4 INADDR_LOOPBACK p
    else concretizeClientLocalAddr locSa (some targetAddr)
  | .ipv6 hi lo p fl sc =>
    match mappedV4Addr? hi lo with
    | some ip =>
      if sockType == .stream && isIpv4McastOrBcast ip then
        .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) p fl sc
      else concretizeClientLocalAddr locSa (some targetAddr)
    | none => concretizeClientLocalAddr locSa (some targetAddr)
  | _ => concretizeClientLocalAddr locSa (some targetAddr)

/-- Default auto-bound client `SockAddr` assigned when an unbound inet socket connects. -/
def defaultAutoClientAddr (domain : SockDomain) (targetAddr : SockAddr) (ep : UInt16) : SockAddr :=
  match domain, targetAddr with
  | .inet, _ => .ipv4 INADDR_LOOPBACK ep
  | .inet6, .ipv6 thi tlo _ _ _ =>
    if (mappedV4Addr? thi tlo).isSome then
      .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) ep 0 0
    else .ipv6 0 1 ep 0 0
  | .inet6, _ => .ipv6 0 1 ep 0 0
  | .unix, _ => .unix (ByteArray.mk #[])

/-- Concretize wildcard/multicast/zero-`inet_saddr` local IP to the target loopback IP upon TCP self-connect. -/
def concretizeSelfConnectLocal (locSa targetAddr : SockAddr) (inetSaddrZero : Bool := false) : SockAddr :=
  match locSa, targetAddr with
  | .ipv4 lip lp, .ipv4 tip _ =>
    .ipv4 (if lip == INADDR_ANY || isIpv4McastOrBcast lip || inetSaddrZero then resolveLoopbackTargetV4 tip else lip) lp
  | .ipv6 lhi llo lp fl sc, .ipv6 thi tlo _ _ _ =>
    if lhi == 0 && llo == 0 then
      match mappedV4Addr? thi tlo with
      | some tip => .ipv6 0 (ipv4ToMappedV6Lo (resolveLoopbackTargetV4 tip)) lp fl sc
      | none => .ipv6 0 1 lp fl sc
    else if mappedV4Addr? lhi llo == some INADDR_ANY ||
        ((mappedV4Addr? lhi llo).map isIpv4McastOrBcast).getD false then
      match mappedV4Addr? thi tlo with
      | some tip => .ipv6 0 (ipv4ToMappedV6Lo (resolveLoopbackTargetV4 tip)) lp fl sc
      | none => .ipv6 lhi llo lp fl sc
    else .ipv6 lhi llo lp fl sc
  | sa, _ => sa

/-- Check whether `gotSa` matches `baseSa` up to ephemeral port assignment and loopback/wildcard IP resolution. -/
def matchesEphemeralAddr (baseSa gotSa : SockAddr) : Bool :=
  match baseSa, gotSa with
  | .ipv4 ip1 _, .ipv4 ip2 p2 =>
    p2 != 0 && (ip1 == ip2 || (ip1 == INADDR_ANY && isIpv4Loopback ip2) ||
      (isIpv4Loopback ip1 && ip2 == INADDR_ANY))
  | .ipv6 hi1 lo1 _ fl1 sc1, .ipv6 hi2 lo2 p2 fl2 sc2 =>
    p2 != 0 && fl1 == fl2 && sc1 == sc2 &&
      ((hi1 == hi2 && lo1 == lo2) ||
       (hi1 == 0 && lo1 == 0 && hi2 == 0 && (lo2 == 1 || (mappedLoopbackV4? 0 lo2).isSome)) ||
       (hi2 == 0 && lo2 == 0 && hi1 == 0 && (lo1 == 1 || (mappedLoopbackV4? 0 lo1).isSome)) ||
       ((mappedLoopbackV4? hi1 lo1).isSome && (mappedLoopbackV4? hi2 lo2).isSome))
  | _, _ => false

/-- Check whether `gotSa` matches a socket's disconnected local address with unlocked wildcard reset. -/
def matchesResettableLocalAddr (baseSa gotSa : SockAddr) : Bool :=
  match baseSa, gotSa with
  | .ipv4 _ p1, .ipv4 ip2 p2 =>
    p1 != 0 && p1 == p2 && (ip2 == INADDR_ANY || matchesEphemeralAddr baseSa gotSa)
  | .ipv6 _ _ p1 fl1 _, .ipv6 hi2 lo2 p2 fl2 sc2 =>
    p1 != 0 && p1 == p2 &&
      ((hi2 == 0 && lo2 == 0 && fl1 == fl2 && sc2 == 0) || matchesEphemeralAddr baseSa gotSa)
  | _, _ => baseSa == gotSa

/-- Check whether two IPv4/IPv6 addresses overlap (including cross-family `[::]`/`::ffff:` vs IPv4) on the same non-zero port. -/
def ipAddrsConflict (a b : SockAddr) : Bool :=
  let v4VsV6Conflict (ip4 : UInt32) (p4 : UInt16) (hi6 lo6 : UInt64) (p6 : UInt16) : Bool :=
    p4 != 0 && p4 == p6 &&
      ((hi6 == 0 && lo6 == 0) ||
       match mappedV4Addr? hi6 lo6 with
       | some ip6 => ip4 == ip6 || ip4 == INADDR_ANY || ip6 == INADDR_ANY
       | none => false)
  match a, b with
  | .ipv4 ip1 p1, .ipv4 ip2 p2 =>
    p1 != 0 && p1 == p2 && (ip1 == ip2 || ip1 == INADDR_ANY || ip2 == INADDR_ANY)
  | .ipv6 hi1 lo1 p1 _ _, .ipv6 hi2 lo2 p2 _ _ =>
    p1 != 0 && p1 == p2 &&
      ((hi1 == hi2 && lo1 == lo2) ||
       (hi1 == 0 && lo1 == 0) || (hi2 == 0 && lo2 == 0) ||
       (mappedV4Addr? hi1 lo1 == some INADDR_ANY && (mappedV4Addr? hi2 lo2).isSome) ||
       (mappedV4Addr? hi2 lo2 == some INADDR_ANY && (mappedV4Addr? hi1 lo1).isSome))
  | .ipv4 ip4 p4, .ipv6 hi6 lo6 p6 _ _ => v4VsV6Conflict ip4 p4 hi6 lo6 p6
  | .ipv6 hi6 lo6 p6 _ _, .ipv4 ip4 p4 => v4VsV6Conflict ip4 p4 hi6 lo6 p6
  | _, _ => false

/-- Returns `true` iff IPv6 `(lhi, llo)` accepts traffic destined to IPv4 `dstIp`. -/
def v6MappedIpMatchesV4 (lhi llo : UInt64) (dstIp : UInt32) : Bool :=
  (lhi == 0 && llo == 0) ||
  match mappedV4Addr? lhi llo with
  | some lip => lip == dstIp || lip == INADDR_ANY
  | none => false

/-- Extract hashed `InetBind` address for conflict checking (ignoring `.unbound`, `.unhashed`, and pending ephemeral binds). -/
private def hashedBindAddr? (d : SockDesc) : Option SockAddr :=
  match d.proto with
  | .tcp _ (.hashed sa false _ _) _ _ _ => some sa
  | .udp _ (.hashed sa false _ _) _ => some sa
  | _ => none

/-- Check whether binding `selfHid` (`sockType`, `selfReuse`) to `targetAddr` conflicts across IPv4/IPv6 dual-stack sockets. -/
def hasBindPortConflict (s : NetState) (selfHid : HandleId) (sockType : SockType)
    (selfReuse : Bool) (targetAddr : SockAddr) : Bool :=
  let selfFid? := lookupHandleFileId s selfHid
  s.files.any fun (fid, entry) =>
    if some fid == selfFid? then false
    else
      match entry with
      | .socket other =>
        other.sockType == sockType &&
        match hashedBindAddr? other with
        | some osa =>
          if ipAddrsConflict targetAddr osa then
            if other.proto.isListening then true
            else !(selfReuse && other.reuseAddr)
          else false
        | none => false
      | .nonSocket => false

/-- Check whether binding `selfHid` conflicts with a socket that cannot have already unhashed via async `SHUT_RDWR` `RST`. -/
def hasDefiniteBindPortConflict (s : NetState) (selfHid : HandleId) (sockType : SockType)
    (selfReuse : Bool) (targetAddr : SockAddr) : Bool :=
  let selfFid? := lookupHandleFileId s selfHid
  s.files.any fun (fid, entry) =>
    if some fid == selfFid? then false
    else
      match entry with
      | .socket other =>
        let asyncUnhashPossible :=
          (other.tcpShutRdwrRst || other.tcpCloseWaitRst) &&
          match other.proto with
          | .tcp _ b _ _ _ => !b.isPortLocked
          | _ => false
        !asyncUnhashPossible &&
        other.sockType == sockType &&
        match hashedBindAddr? other with
        | some osa =>
          if ipAddrsConflict targetAddr osa then
            if other.proto.isListening then true
            else !(selfReuse && other.reuseAddr)
          else false
        | none => false
      | .nonSocket => false

/-- Check whether transitioning `selfHid` to `.listen` on `sa` conflicts across IPv4/IPv6 dual-stack listeners. -/
def hasListenConflict (s : NetState) (selfHid : HandleId) (sockType : SockType) (sa : SockAddr) : Bool :=
  let selfFid? := lookupHandleFileId s selfHid
  s.files.any fun (fid, entry) =>
    if some fid == selfFid? then false
    else
      match entry with
      | .socket other =>
        other.proto.isListening &&
        other.sockType == sockType &&
        match hashedBindAddr? other with
        | some osa => ipAddrsConflict sa osa
        | none => false
      | .nonSocket => false

private inductive CanonTcpEp where
  | v4 (ip : UInt32) (port : UInt16)
  | v6native (hi lo : UInt64) (port : UInt16)
  | other (sa : SockAddr)
  deriving DecidableEq, BEq

private def canonTcpEp : SockAddr → CanonTcpEp
  | .ipv4 ip p => .v4 ip p
  | .ipv6 hi lo p _ _ =>
    match mappedV4Addr? hi lo with
    | some ip => .v4 ip p
    | none => .v6native hi lo p
  | sa => .other sa

/-- Returns `true` iff connecting `(cliSa, resolvedAddr)` collides with an existing TCP socket's 4-tuple. -/
def hasTcpFourTupleConflict (s : NetState) (selfFid : FileId) (cliSa resolvedAddr : SockAddr) : Bool :=
  let cLoc := canonTcpEp cliSa
  let cRem := canonTcpEp resolvedAddr
  s.files.any fun (fid, entry) =>
    if fid == selfFid then false
    else
      match entry with
      | .socket other =>
        match other.proto with
        | .tcp _ otherBind _ otherTcp _ =>
          let peerOpt? :=
            match otherTcp with
            | .established _ pa | .finWait _ pa | .closeWait _ pa _ | .closedAfterConn pa .cleanFin => some pa
            | .synSent pa => if other.soError == 0 then some pa else none
            | _ => none
          match otherBind.addr?, peerOpt? with
          | some oLoc, some oPeer => canonTcpEp oLoc == cLoc && canonTcpEp oPeer == cRem
          | _, _ => false
        | _ => false
      | .nonSocket => false

/-- Returns `true` iff `path` uses the Linux abstract `AF_UNIX` namespace (`sun_path[0] == 0`). -/
def isAbstractUnixPath (path : ByteArray) : Bool :=
  path.size > 0 && path.get! 0 == 0

/-- Find an open bound `AF_UNIX` socket at `path`. -/
def findBoundUnixSocket (s : NetState) (sockType : SockType) (path : ByteArray) : Option (FileId × SockDesc) :=
  let isAbs := isAbstractUnixPath path
  let rec go : List (FileId × OpenFileEntry) → Option (FileId × SockDesc)
    | [] => none
    | (fid, entry) :: rest =>
      match entry with
      | .socket d =>
        if !d.unixAddrInherited && (!isAbs || d.sockType == sockType) then
          match d.localAddr? with
          | some (.unix lp) => if bytesEq lp path then some (fid, d) else go rest
          | _ => go rest
        else go rest
      | .nonSocket => go rest
  go s.files

/-- Check whether binding an `AF_UNIX` socket of `sockType` to `path` conflicts (`EADDRINUSE`). -/
def hasUnixBindConflict (s : NetState) (sockType : SockType) (path : ByteArray) : Bool :=
  if isAbstractUnixPath path then (findBoundUnixSocket s sockType path).isSome
  else bytesListContains s.boundUnixPaths path

/-- Find an active listening socket matching `(domain, sockType, targetAddr)`, supporting dual-stack `::ffff:`. -/
def findMatchingListener (s : NetState) (selfFid : FileId) (domain : SockDomain)
    (sockType : SockType) (targetAddr : SockAddr) : Option (FileId × SockDesc × LoopbackMatchKind) :=
  let rec goSame : List (FileId × OpenFileEntry) → Option (FileId × SockDesc × LoopbackMatchKind)
    | [] => none
    | (fid, entry) :: rest =>
      if fid == selfFid then goSame rest
      else
        match entry with
        | .socket d =>
          let loDevOk := d.domain == .unix || d.boundDevIf == 0 || d.boundDevIf == 1
          if loDevOk && d.proto.isListening && d.domain == domain && d.sockType == sockType then
            match d.localAddr?, targetAddr with
            | some (.unix lp), .unix tp =>
              if bytesEq lp tp then some (fid, d, .sameFamily) else goSame rest
            | some (.ipv4 lip lp), .ipv4 tip tp =>
              let dstIp := resolveLoopbackTargetV4 tip
              if tp != 0 && lp == tp && (isIpv4Loopback tip || tip == INADDR_ANY) &&
                  (lip == dstIp || lip == INADDR_ANY) then
                some (fid, d, .sameFamily)
              else goSame rest
            | some (.ipv6 lhi llo lp _ _), .ipv6 thi tlo tp _ _ =>
              if tp != 0 && lp == tp then
                if (thi == 0 && (tlo == 1 || tlo == 0)) && ((lhi == 0 && llo == 1) || (lhi == 0 && llo == 0)) then
                  some (fid, d, .sameFamily)
                else
                  match mappedLoopbackV4? thi tlo with
                  | some tip =>
                    if v6MappedIpMatchesV4 lhi llo (resolveLoopbackTargetV4 tip) then
                      some (fid, d, .sameFamily)
                    else goSame rest
                  | none => goSame rest
              else goSame rest
            | _, _ => goSame rest
          else goSame rest
        | .nonSocket => goSame rest
  let rec goV4ToV6 : List (FileId × OpenFileEntry) → Option (FileId × SockDesc × LoopbackMatchKind)
    | [] => none
    | (fid, entry) :: rest =>
      if fid == selfFid then goV4ToV6 rest
      else
        match entry with
        | .socket d =>
          if (d.boundDevIf == 0 || d.boundDevIf == 1) && d.proto.isListening && d.domain == .inet6 && d.sockType == sockType then
            match d.localAddr?, targetAddr with
            | some (.ipv6 lhi llo lp _ _), .ipv4 tip tp =>
              let dstIp := resolveLoopbackTargetV4 tip
              if tp != 0 && lp == tp && isIpv4Loopback dstIp && v6MappedIpMatchesV4 lhi llo dstIp then
                some (fid, d, .v4ToV6)
              else goV4ToV6 rest
            | _, _ => goV4ToV6 rest
          else goV4ToV6 rest
        | .nonSocket => goV4ToV6 rest
  let rec goV6ToV4 : List (FileId × OpenFileEntry) → Option (FileId × SockDesc × LoopbackMatchKind)
    | [] => none
    | (fid, entry) :: rest =>
      if fid == selfFid then goV6ToV4 rest
      else
        match entry with
        | .socket d =>
          if (d.boundDevIf == 0 || d.boundDevIf == 1) && d.proto.isListening && d.domain == .inet && d.sockType == sockType then
            match d.localAddr?, targetAddr with
            | some (.ipv4 lip lp), .ipv6 thi tlo tp _ _ =>
              match mappedLoopbackV4? thi tlo with
              | some tip =>
                let dstIp := resolveLoopbackTargetV4 tip
                if tp != 0 && lp == tp && (lip == dstIp || lip == INADDR_ANY) then
                  some (fid, d, .v6MappedToV4)
                else goV6ToV4 rest
              | none => goV6ToV4 rest
            | _, _ => goV6ToV4 rest
          else goV6ToV4 rest
        | .nonSocket => goV6ToV4 rest
  match goSame s.files with
  | some res => some res
  | none =>
    if domain == .inet then goV4ToV6 s.files
    else if domain == .inet6 then goV6ToV4 s.files
    else none

/-- Check whether an inbound UDP packet from `senderDesc` matches a connected receiver's `peerAddr`. -/
def udpConnectedPeerMatches (senderDesc : SockDesc) (targetAddr receiverPeer : SockAddr) : Bool :=
  let senderBind := match senderDesc.proto with | .udp _ b _ => b | _ => .unbound
  let rawSenderLoc :=
    match senderBind.addr? with
    | some l => concretizeClientLocalAddr l (some targetAddr)
    | none => defaultUnboundAddr senderDesc.domain
  let targetIsV4Wire :=
    match targetAddr with
    | .ipv4 _ _ => true
    | .ipv6 thi tlo _ _ _ => (mappedV4Addr? thi tlo).isSome
    | .unix _ => false
  let senderLoc : SockAddr :=
    match rawSenderLoc with
    | .ipv4 lip lp =>
      if isIpv4McastOrBcast lip || senderDesc.inetSaddrZero then .ipv4 INADDR_LOOPBACK lp else .ipv4 lip lp
    | .ipv6 0 1 lp fl sc =>
      if !senderBind.isAddrLocked && targetIsV4Wire then
        .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) lp fl sc
      else .ipv6 0 1 lp fl sc
    | .ipv6 lhi llo lp fl sc =>
      if (lhi >>> 56) == 0xff then .ipv6 0 1 lp fl 0 else .ipv6 lhi llo lp fl sc
    | other => other
  if (senderDesc.udpExtRoutedIp || senderDesc.tcpMcastRoutedIp) && isLoopbackTargetAddr receiverPeer then
    false
  else
  let portOk (p1 p2 : UInt16) : Bool := p2 != 0 && !senderBind.isEphemeral && p1 == p2
  match senderLoc, receiverPeer with
  | .ipv4 lip lp, .ipv4 pip pp =>
    let dstIp := resolveLoopbackTargetV4 pip
    portOk lp pp && (lip == INADDR_ANY || lip == dstIp)
  | .ipv6 lhi llo lp _ _, .ipv6 phi plo pp _ _ =>
    if !portOk lp pp then false
    else if (phi == 0 && (plo == 1 || plo == 0)) && ((lhi == 0 && llo == 1) || (lhi == 0 && llo == 0)) then true
    else
      match mappedLoopbackV4? phi plo with
      | some pip => v6MappedIpMatchesV4 lhi llo (resolveLoopbackTargetV4 pip)
      | none => false
  | .ipv4 lip lp, .ipv6 phi plo pp _ _ =>
    match mappedLoopbackV4? phi plo with
    | some pip =>
      let dstIp := resolveLoopbackTargetV4 pip
      portOk lp pp && (lip == INADDR_ANY || lip == dstIp)
    | none => false
  | .ipv6 lhi llo lp _ _, .ipv4 pip pp =>
    portOk lp pp && v6MappedIpMatchesV4 lhi llo (resolveLoopbackTargetV4 pip)
  | _, _ => false

/-- Find an open bound UDP peer socket matching `targetAddr` and sender's local endpoint. -/
def findBoundUdpPeer (s : NetState) (senderDesc : SockDesc) (targetAddr : SockAddr) : Option (FileId × SockDesc) :=
  let senderDom := senderDesc.domain
  let targetIsV4Wire : Bool :=
    match targetAddr with
    | .ipv4 _ _ => true
    | .ipv6 thi tlo _ _ _ => (mappedV4Addr? thi tlo).isSome
    | .unix _ => false
  let rec go (best : Option (Nat × Nat × FileId × SockDesc)) : List (FileId × OpenFileEntry) → Option (FileId × SockDesc)
    | [] => best.map (fun (_, _, fid, d) => (fid, d))
    | (fid, entry) :: rest =>
      match entry with
      | .socket d =>
        match d.proto with
        | .udp fam bind connPeer? =>
          let dDom : SockDomain := match fam with | .v4 => .inet | .v6 => .inet6
          let loDevOk : Bool := d.boundDevIf == 0 || d.boundDevIf == 1
          let addrMatches : Bool :=
            if !loDevOk then false
            else
              match bind.addr?, targetAddr with
              | some (.ipv4 lip lp), .ipv4 tip tp =>
                let dstIp := resolveLoopbackTargetV4 tip
                dDom == .inet && tp != 0 && lp == tp && (isIpv4Loopback tip || tip == INADDR_ANY) &&
                  (lip == dstIp || lip == INADDR_ANY)
              | some (.ipv6 lhi llo lp _ _), .ipv6 thi tlo tp _ _ =>
                if dDom == .inet6 && tp != 0 && lp == tp then
                  if (thi == 0 && (tlo == 1 || tlo == 0)) && ((lhi == 0 && llo == 1) || (lhi == 0 && llo == 0)) then true
                  else
                    match mappedLoopbackV4? thi tlo with
                    | some tip => v6MappedIpMatchesV4 lhi llo (resolveLoopbackTargetV4 tip)
                    | none => false
                else false
              | some (.ipv6 lhi llo lp _ _), .ipv4 tip tp =>
                let dstIp := resolveLoopbackTargetV4 tip
                senderDom == .inet && dDom == .inet6 && tp != 0 && lp == tp && isIpv4Loopback dstIp &&
                  v6MappedIpMatchesV4 lhi llo dstIp
              | some (.ipv4 lip lp), .ipv6 thi tlo tp _ _ =>
                if senderDom == .inet6 && dDom == .inet && tp != 0 && lp == tp then
                  match mappedLoopbackV4? thi tlo with
                  | some tip =>
                    let dstIp := resolveLoopbackTargetV4 tip
                    lip == dstIp || lip == INADDR_ANY
                  | none => false
                else false
              | _, _ => false
          let connOk : Bool :=
            if !addrMatches then false
            else
              match connPeer? with
              | some rp => udpConnectedPeerMatches senderDesc targetAddr rp
              | none => true
          if connOk then
            let connScore : Nat := if connPeer?.isSome then 4 else 0
            let exactIpScore : Nat :=
              match bind.addr? with
              | some (.ipv4 lip _) => if lip != INADDR_ANY then 2 else 0
              | some (.ipv6 lhi llo _ _ _) =>
                if !(lhi == 0 && llo == 0) && mappedV4Addr? lhi llo != some INADDR_ANY then 2 else 0
              | _ => 0
            let famScore : Nat :=
              if targetIsV4Wire then (if dDom == .inet then 1 else 0)
              else (if dDom == .inet6 then 1 else 0)
            let score := connScore + exactIpScore + famScore
            let seq := d.udpBindSeq
            let nextBest :=
              match best with
              | none => some (score, seq, fid, d)
              | some (bScore, bSeq, _, _) =>
                if score > bScore || (score == bScore && seq >= bSeq) then some (score, seq, fid, d)
                else best
            go nextBest rest
          else go best rest
        | _ => go best rest
      | .nonSocket => go best rest
  go none s.files

/-- Compute `(peerAddrForListener, srvConcreteLocalAddr)` for a loopback `connect` to `(lDesc, matchKind)`. -/
def computeLoopbackEndpoints (cliConcreteAddr targetAddr : SockAddr)
    (lDesc : SockDesc) (matchKind : LoopbackMatchKind) : SockAddr × SockAddr :=
  match matchKind with
  | .v4ToV6 =>
    let (cip, cp) := match cliConcreteAddr with
      | .ipv4 ip p => (ip, p)
      | _ => (INADDR_LOOPBACK, 49152)
    let (tip, tp) := match targetAddr with
      | .ipv4 ip p => (resolveLoopbackTargetV4 ip, p)
      | _ => (INADDR_LOOPBACK, 0)
    (.ipv6 0 (ipv4ToMappedV6Lo cip) cp 0 0, .ipv6 0 (ipv4ToMappedV6Lo tip) tp 0 0)
  | .v6MappedToV4 =>
    let (cip, cp) := match cliConcreteAddr with
      | .ipv6 hi lo p _ _ =>
        (resolveLoopbackTargetV4 ((mappedLoopbackV4? hi lo).getD INADDR_LOOPBACK), p)
      | _ => (INADDR_LOOPBACK, 49152)
    let (tip, tp) := match targetAddr with
      | .ipv6 thi tlo p _ _ =>
        (resolveLoopbackTargetV4 ((mappedLoopbackV4? thi tlo).getD INADDR_LOOPBACK), p)
      | _ => (INADDR_LOOPBACK, 0)
    (.ipv4 cip cp, .ipv4 tip tp)
  | .sameFamily =>
    let srvLocal :=
      match lDesc.localAddr?, targetAddr with
      | some (.ipv4 lip lp), .ipv4 tip _ =>
        .ipv4 (if lip == INADDR_ANY then resolveLoopbackTargetV4 tip else lip) lp
      | some (.ipv6 lhi llo lp fl sc), .ipv6 thi tlo _ _ _ =>
        if lhi == 0 && llo == 0 then
          match mappedLoopbackV4? thi tlo with
          | some tip => .ipv6 0 (ipv4ToMappedV6Lo (resolveLoopbackTargetV4 tip)) lp fl sc
          | none => .ipv6 0 1 lp fl sc
        else if mappedV4Addr? lhi llo == some INADDR_ANY then
          match mappedLoopbackV4? thi tlo with
          | some tip => .ipv6 0 (ipv4ToMappedV6Lo (resolveLoopbackTargetV4 tip)) lp fl sc
          | none => .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) lp fl sc
        else .ipv6 lhi llo lp fl sc
      | some sa, _ => sa
      | none, _ => defaultUnboundAddr lDesc.domain
    (cliConcreteAddr, srvLocal)

/-- Check whether `gotPeerAddr` matches `entry.peerAddr` (allowing ephemeral/wildcard or host-routed IPv4 resolution when unpinned). -/
def matchesAcceptPeerAddr (expectedPeer gotPeer : SockAddr) (cliEphPending : Bool)
    (matchKind : LoopbackMatchKind) (peerRoutedV4 : Bool := false) : Bool :=
  if gotPeer == expectedPeer then true
  else if peerRoutedV4 then
    match matchKind with
    | .sameFamily =>
      match expectedPeer, gotPeer with
      | .ipv4 _ expP, .ipv4 gotIp gotP =>
        gotIp != INADDR_ANY && gotP != 0 && (cliEphPending || expP == gotP)
      | .ipv6 0 expLo expP 0 0, .ipv6 0 gotLo gotP 0 0 =>
        (mappedV4Addr? 0 expLo).isSome &&
          match mappedV4Addr? 0 gotLo with
          | some gotIp => gotIp != INADDR_ANY && gotP != 0 && (cliEphPending || expP == gotP)
          | none => false
      | _, _ => false
    | .v4ToV6 =>
      match expectedPeer, gotPeer with
      | .ipv6 0 _ expP 0 0, .ipv6 0 gotLo gotP 0 0 =>
        match mappedV4Addr? 0 gotLo with
        | some gotIp => gotIp != INADDR_ANY && gotP != 0 && (cliEphPending || expP == gotP)
        | none => false
      | _, _ => false
    | .v6MappedToV4 =>
      match expectedPeer, gotPeer with
      | .ipv4 _ expP, .ipv4 gotIp gotP =>
        gotIp != INADDR_ANY && gotP != 0 && (cliEphPending || expP == gotP)
      | _, _ => false
  else if !cliEphPending then false
  else
    match matchKind with
    | .v4ToV6 =>
      match expectedPeer, gotPeer with
      | .ipv6 0 _ _ 0 0, .ipv6 0 gotLo gotP 0 0 =>
        gotP != 0 && (mappedLoopbackV4? 0 gotLo).isSome
      | _, _ => false
    | .v6MappedToV4 =>
      match expectedPeer, gotPeer with
      | .ipv4 _ _, .ipv4 gotIp gotP =>
        gotP != 0 && isIpv4Loopback gotIp
      | _, _ => false
    | .sameFamily =>
      matchesEphemeralAddr expectedPeer gotPeer

/-- Returns `true` iff `d` is an explicitly bound TCP socket connecting to its own local address. -/
def isTcpSelfConnect (d : SockDesc) (addr : SockAddr) : Bool :=
  match d.proto with
  | .tcp _ (.hashed localSa false _ _) _ _ _ =>
    match localSa, resolveTargetAddrForClient (some localSa) addr with
    | .ipv4 lip lp, .ipv4 tip tp =>
      let dstIp := resolveLoopbackTargetV4 tip
      lp != 0 && lp == tp && isIpv4Loopback dstIp &&
        (if d.inetSaddrZero then dstIp == INADDR_LOOPBACK
         else lip == dstIp || ((lip == INADDR_ANY || isIpv4McastOrBcast lip) && dstIp == INADDR_LOOPBACK))
    | .ipv6 lhi llo lp _ _, .ipv6 thi tlo tp _ _ =>
      if lp == 0 || lp != tp then false
      else if (thi == 0 && (tlo == 1 || tlo == 0)) && ((lhi == 0 && llo == 0) || (lhi == 0 && llo == 1)) then
        true
      else
        match mappedV4Addr? thi tlo with
        | some v4tip =>
          let dstIp := resolveLoopbackTargetV4 v4tip
          let locIsWildOrMcast :=
            (lhi == 0 && llo == 0) ||
            mappedV4Addr? lhi llo == some INADDR_ANY ||
            ((mappedV4Addr? lhi llo).map isIpv4McastOrBcast).getD false
          isIpv4Loopback dstIp &&
            (mappedV4Addr? lhi llo == some dstIp || (locIsWildOrMcast && dstIp == INADDR_LOOPBACK))
        | none => false
    | _, _ => false
  | _ => false

/-- Compute updated `ifr_flags` on `SIOCSIFFLAGS` (`dev_change_flags` volatile mask `0xf3a5`). -/
def applyIfFlags (curFlags newFlags : UInt32) : UInt32 :=
  let masked := newFlags &&& 0xf3a5
  if (curFlags &&& IFF_LOOPBACK) != 0 then
    let base := masked ||| IFF_LOOPBACK
    if (masked &&& IFF_UP) != 0 then base ||| IFF_RUNNING else base
  else
    masked

end LeanSwe.LinuxSyscall.Net

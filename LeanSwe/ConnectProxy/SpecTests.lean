import Core.NondetTest
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model

namespace LeanSwe.ConnectProxy

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ConnectProxy.Raw
open LeanSwe.ConnectProxy.Model

/-- Builder assembling a pure `ConnectProxyApiM m` from injected `RawConnectProxyOpsM m`. -/
abbrev ConnectProxyBuilder (m : Type → Type) :=
  RawConnectProxyOpsM m → ConnectProxyApiM m

/-- `api.parseIpAddr` agrees with `Model.parseIpAddr`, parses IPv4 and RFC 4291 IPv6 literals, and rejects `*` wildcards, octal leading zeros, shorthand integers, brackets, and CIDR suffixes with `.invalidInput` and non-empty message. -/
def test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let s ← nondet String
  NondetTest.assert (api.parseIpAddr s = Model.parseIpAddr s)
  match api.parseIpAddr s with
  | .ok _ => NondetTest.assert (!s.toList.contains '*')
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  NondetTest.assert (api.parseIpAddr "127.0.0.1" = .ok (.v4 0x7f000001))
  NondetTest.assert (api.parseIpAddr "::ffff:127.0.0.1" = .ok (.v6 0 0x0000ffff7f000001))
  NondetTest.assert ((api.parseIpAddr "10.1*").isOk = false)
  NondetTest.assert ((api.parseIpAddr "192.168.*").isOk = false)
  NondetTest.assert ((api.parseIpAddr "010.0.0.1").isOk = false)
  NondetTest.assert ((api.parseIpAddr "127.1").isOk = false)
  NondetTest.assert ((api.parseIpAddr "[::1]").isOk = false)

/-- `api.parseIpPrefix` agrees with `Model.parseIpPrefix`, promotes single IPs to `/32` and `/128`, evaluates exact `/prefix` bitmasks (`10.1.0.0/16` never matching `10.100.0.1`), and rejects `*` wildcards, non-zero host bits, and out-of-range prefix lengths. -/
def test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let s ← nondet String
  NondetTest.assert (api.parseIpPrefix s = Model.parseIpPrefix s)
  match api.parseIpPrefix s with
  | .ok pfx =>
    NondetTest.assert (!s.toList.contains '*' ∧ isValidIpPrefix pfx = true)
  | .error err =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  NondetTest.assert ((api.parseIpPrefix "10.1*").isOk = false)
  NondetTest.assert ((api.parseIpPrefix "192.168.*").isOk = false)
  NondetTest.assert ((api.parseIpPrefix "10.20.1.5/24").isOk = false)
  NondetTest.assert ((api.parseIpPrefix "10.0.0.0/33").isOk = false)
  NondetTest.assert ((api.parseIpPrefix "fe80::/129").isOk = false)
  match api.parseIpPrefix "10.1.0.0/16" with
  | .error _ => NondetTest.assert False
  | .ok p16 =>
    NondetTest.assert (prefixContains p16 (.v4 0x0a01ffff) = true)
    NondetTest.assert (prefixContains p16 (.v4 0x0a640001) = false)

/-- `api.isGlobalIp` agrees universally with `Model.isGlobalIp` and enforces the complete IANA RFC 6890 / `2000::/3` global-unicast table (including CGNAT, multicast, benchmarking, documentation, `::/96`, SIIT `::ffff:0:0:0/96`, ULA, link-local, IANA exceptions, and embedded IPv4-in-IPv6). -/
def test_cproxy_isGlobalIp_completeIanaRfc6890Table
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let ip ← nondet IpAddr
  NondetTest.assert (api.isGlobalIp ip = Model.isGlobalIp ip)
  NondetTest.assert (api.isGlobalIp (.v4 0x08080808) = true)
  NondetTest.assert (api.isGlobalIp (.v4 0x00000001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0x0a000001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0x64400001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0x7f000001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xa9fe0101) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xac100001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xc0000001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xc0000009) = true)
  NondetTest.assert (api.isGlobalIp (.v4 0xc000000a) = true)
  NondetTest.assert (api.isGlobalIp (.v4 0xc0000201) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xc0a80101) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xc6120001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xc6336401) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xcb007101) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xe0000001) = false)
  NondetTest.assert (api.isGlobalIp (.v4 0xf0000001) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x2606470047000000 0x1111) = true)
  NondetTest.assert (api.isGlobalIp (.v6 0 0) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0 1) = false)
  NondetTest.assert (api.isGlobalIp (mkIpv4CompatibleIpv6 0x7f000001) = false)
  NondetTest.assert (api.isGlobalIp (mkIpv4CompatibleIpv6 0x08080808) = false)
  NondetTest.assert (api.isGlobalIp (mkSiitIpv6 0x7f000001) = false)
  NondetTest.assert (api.isGlobalIp (mkSiitIpv6 0x08080808) = false)
  NondetTest.assert (api.isGlobalIp (mkIpv4MappedIpv6 0x08080808) = true)
  NondetTest.assert (api.isGlobalIp (mkIpv4MappedIpv6 0x7f000001) = false)
  NondetTest.assert (api.isGlobalIp (mkNat64WellKnownIpv6 0x08080808) = true)
  NondetTest.assert (api.isGlobalIp (mkNat64WellKnownIpv6 0x7f000001) = false)
  NondetTest.assert (api.isGlobalIp (mkNat64LocalIpv6 0x08080808) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x0100000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x2001000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x2001000100000000 1) = true)
  NondetTest.assert (api.isGlobalIp (.v6 0x2001000200000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x20010db800000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x2002080808080000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x3fff000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x4000000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0x5f00000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0xfc00000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0xfe80000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0xfec0000000000000 1) = false)
  NondetTest.assert (api.isGlobalIp (.v6 0xff00000000000000 1) = false)

/-- `api.allowsIp` evaluates `(base ∪ extraAllows) \ extraBans` so any matching `ban` in `extraBans` always overrides both `base` and `extraAllows`. -/
def test_cproxy_allowsIp_banAlwaysOverridesAllow
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let policy ← nondet IpPolicy
  let ip ← nondet IpAddr
  NondetTest.assert (api.allowsIp policy ip = Model.allowsIp policy ip)
  let conflictPolicy : IpPolicy :=
    { base := .empty
      extraAllows := #[.v4 0x0a140000 16]
      extraBans := #[.v4 0x0a140100 24] }
  NondetTest.assert (api.allowsIp conflictPolicy (.v4 0x0a140105) = false)
  NondetTest.assert (api.allowsIp conflictPolicy (.v4 0x0a140205) = true)
  let i ← nondet Nat
  assume (i < policy.extraBans.size)
  let ban := policy.extraBans[i]!
  assume (prefixContains ban ip = true)
  NondetTest.assert (api.allowsIp policy ip = false)

/-- `api.allowsIp` unwraps IPv4-in-IPv6 (`::ffff:0:0/96`, `::/96` `v4 > 1`, `::ffff:0:0:0/96`, `64:ff9b::/96`, `64:ff9b:1::/48` `/96` with arbitrary subnet plus RFC 6052 `/48`, `/56`, `/64`, `2002::/16`, `2001::/32` Teredo server & client) so wrapping a banned IPv4 in IPv6 never bypasses `extraBans`. -/
def test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let v4 ← nondet UInt32
  let sub8 ← nondet UInt8
  let subHi ← nondet UInt16
  let sla ← nondet UInt16
  let subLo ← nondet UInt32
  let otherV4 ← nondet UInt32
  let flagsPort ← nondet UInt32
  let suffix32 ← nondet UInt32
  let suffix24 ← nondet UInt32
  let iface ← nondet UInt64
  let suffix40 ← nondet UInt64
  let ban ← nondet IpPrefix
  assume (prefixContains ban (.v4 v4) = true)
  let wideAllowPolicy : IpPolicy :=
    { base := .publicOnly
      extraAllows := #[.v6 0 0 0]
      extraBans := #[ban] }
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkIpv4MappedIpv6 v4) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkSiitIpv6 v4) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkNat64WellKnownIpv6 v4) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkNat64LocalIpv6 v4 subHi subLo) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkNat64Local48Ipv6 v4 suffix40) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkNat64Local56Ipv6 sub8 v4 suffix32) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkNat64Local64Ipv6 subHi v4 suffix24) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mk6to4Ipv6 v4 sla iface) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkTeredoIpv6 v4 flagsPort otherV4) = false)
  NondetTest.assert (api.allowsIp wideAllowPolicy (mkTeredoIpv6 otherV4 flagsPort v4) = false)
  if v4 > 1 then
    NondetTest.assert (api.allowsIp wideAllowPolicy (mkIpv4CompatibleIpv6 v4) = false)
  else
    pure ()

/-- `api.parseConnectRequest` agrees with `Model.parseConnectRequest`, normalizes domain and bracketed `[IPv6]` hosts, and refuses `GET`/`POST`, `*` wildcards, schemes/paths/userinfo, numeric-TLD `inet_aton` shorthands, port `0`/`>65535`, bare LF, and smuggling headers. -/
def test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let raw ← nondet ByteArray
  NondetTest.assert (api.parseConnectRequest raw = Model.parseConnectRequest raw)
  match api.parseConnectRequest raw with
  | .ok rule => NondetTest.assert (rule.port ≠ 0 ∧ !rule.host.toList.contains '*')
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  NondetTest.assert (api.parseConnectRequest "CONNECT API.Anthropic.COM:443 HTTP/1.1\r\nHost: api.anthropic.com:443\r\n\r\n".toUTF8 =
    .ok { host := "api.anthropic.com", port := 443 })
  NondetTest.assert (api.parseConnectRequest "CONNECT [2001:DB8:0:0::1]:8443 HTTP/1.1\r\n\r\n".toUTF8 =
    .ok { host := "[2001:db8::1]", port := 8443 })
  NondetTest.assert ((api.parseConnectRequest "GET http://api.anthropic.com/ HTTP/1.1\r\nHost: api.anthropic.com\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "POST /v1/messages HTTP/1.1\r\nHost: api.anthropic.com\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT *.anthropic.com:443 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT https://api.anthropic.com:443 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT user@api.anthropic.com:443 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT 127.1:443 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT 0x7f000001:443 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT api.anthropic.com:0 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT api.anthropic.com:65536 HTTP/1.1\r\n\r\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT api.anthropic.com:443 HTTP/1.1\n\n".toUTF8).isOk = false)
  NondetTest.assert ((api.parseConnectRequest "CONNECT api.anthropic.com:443 HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n".toUTF8).isOk = false)

/-- `api.validateConfig` agrees with `Model.validateConfig`, accepts `listenPort = 0`, rejects `TargetRule.port = 0`, `*` hosts, invalid `IpPrefix` lengths, and any zero `ProxyLimits` field, and is idempotent. -/
def test_cproxy_validateConfig_limitsPortZeroAndIdempotence
    {runner} [NondetTest runner] (api : ConnectProxyApi) : runner Unit := do
  let cfg ← nondet ProxyConfig
  NondetTest.assert (api.validateConfig cfg = Model.validateConfig cfg)
  let ephemCfg : ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[{ host := "API.Anthropic.COM", port := 443 }] }
  NondetTest.assert (api.validateConfig ephemCfg =
    .ok { config := { ephemCfg with allowedTargets := #[{ host := "api.anthropic.com", port := 443 }] } })
  NondetTest.assert ((api.validateConfig { allowedTargets := #[{ host := "api.anthropic.com", port := 0 }] }).isOk = false)
  NondetTest.assert ((api.validateConfig { allowedTargets := #[{ host := "*.anthropic.com", port := 443 }] }).isOk = false)
  NondetTest.assert ((api.validateConfig { limits := { maxHeaderBytes := 0 } }).isOk = false)
  NondetTest.assert ((api.validateConfig { limits := { headerTimeoutMs := 0 } }).isOk = false)
  NondetTest.assert ((api.validateConfig { limits := { connectTimeoutMs := 0 } }).isOk = false)
  NondetTest.assert ((api.validateConfig { limits := { maxConcurrentTunnels := 0 } }).isOk = false)
  NondetTest.assert ((api.validateConfig { ipPolicy := { extraAllows := #[.v4 0 33] } }).isOk = false)
  match api.validateConfig cfg with
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  | .ok vcfg => NondetTest.assert (api.validateConfig vcfg.config = .ok vcfg)

/-- `authorizeConnect` enforces exact `(host, port)` matching (refusing subdomains, suffix/prefix lookalikes, port mismatches, `GET`/`POST`, and oversized headers) without invoking DNS on denied requests. -/
def test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal
    {runner} [NondetTest runner]
    (authFn : ProxyConfig → ByteArray → (String → Except String (Array IpAddr)) → ConnectAuthResult) :
    runner Unit := do
  let cfg : ProxyConfig :=
    { allowedTargets := #[{ host := "api.anthropic.com", port := 443 }]
      limits := { maxHeaderBytes := 64 } }
  let pubResolver (_h : String) : Except String (Array IpAddr) := .ok #[.v4 0x08080808]
  let failIfCalled (_h : String) : Except String (Array IpAddr) := .error "DNS SHOULD NOT BE QUERIED"
  let okRes := authFn cfg "CONNECT API.Anthropic.COM:443 HTTP/1.1\r\n\r\n".toUTF8 pubResolver
  let subRes := authFn cfg "CONNECT sub.api.anthropic.com:443 HTTP/1.1\r\n\r\n".toUTF8 failIfCalled
  let evilSufRes := authFn cfg "CONNECT api.anthropic.com.evil.com:443 HTTP/1.1\r\n\r\n".toUTF8 failIfCalled
  let evilPreRes := authFn cfg "CONNECT evilapi.anthropic.com:443 HTTP/1.1\r\n\r\n".toUTF8 failIfCalled
  let badPortRes := authFn cfg "CONNECT api.anthropic.com:8443 HTTP/1.1\r\n\r\n".toUTF8 failIfCalled
  let getRes := authFn cfg "GET http://api.anthropic.com/ HTTP/1.1\r\n\r\n".toUTF8 failIfCalled
  let bigHead := ("CONNECT api.anthropic.com:443 HTTP/1.1\r\nX-Pad: 012345678901234567890123456789\r\n\r\n").toUTF8
  let bigRes := authFn cfg bigHead failIfCalled
  NondetTest.assert (okRes = .dial { host := "api.anthropic.com", port := 443, primaryIp := .v4 0x08080808 })
  NondetTest.assert (∃ r, subRes = .deny (some "sub.api.anthropic.com") (some 443) r)
  NondetTest.assert (∃ r, evilSufRes = .deny (some "api.anthropic.com.evil.com") (some 443) r)
  NondetTest.assert (∃ r, evilPreRes = .deny (some "evilapi.anthropic.com") (some 443) r)
  NondetTest.assert (∃ r, badPortRes = .deny (some "api.anthropic.com") (some 8443) r)
  NondetTest.assert (∃ h p r, getRes = .deny h p r)
  NondetTest.assert (∃ h p r, bigRes = .deny h p r)

/-- `authorizeConnect` filters resolved IPs through `allowsIp`, selects the exact verified `IpAddr` to dial (preventing DNS-rebinding TOCTOU), returns `.deny` when all resolved IPs are blocked, and returns `.dnsFailed` on resolver errors. -/
def test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly
    {runner} [NondetTest runner]
    (authFn : ProxyConfig → ByteArray → (String → Except String (Array IpAddr)) → ConnectAuthResult) :
    runner Unit := do
  let cfg : ProxyConfig :=
    { allowedTargets := #[{ host := "api.example.com", port := 443 }]
      ipPolicy := { base := .publicOnly, extraBans := #[.v4 0x01010100 24] } }
  let head := "CONNECT api.example.com:443 HTTP/1.1\r\n\r\n".toUTF8
  let mixedRes := authFn cfg head (fun _ => .ok #[.v4 0x7f000001, .v4 0x01010101, .v4 0x5db8d822, .v4 0x08080808])
  let allBlockedRes := authFn cfg head (fun _ => .ok #[.v4 0x7f000001, mkIpv4MappedIpv6 0x01010101])
  let dnsErrRes := authFn cfg head (fun _ => .error "nxdomain")
  NondetTest.assert (mixedRes = .dial {
    host := "api.example.com"
    port := 443
    primaryIp := .v4 0x5db8d822
    fallbackIps := #[.v4 0x08080808]
  })
  NondetTest.assert (∃ r, allBlockedRes = .deny (some "api.example.com") (some 443) r)
  NondetTest.assert (dnsErrRes = .dnsFailed "api.example.com" 443 "nxdomain")

/-- Calling `withProxy` with an invalid `ProxyConfig` returns `.invalidInput` immediately without starting a proxy, running `action`, or mutating state. -/
def test_cproxy_withProxy_invalidConfig_hasZeroSideEffects
    {runner} [NondetTest runner]
    (mkApi : ConnectProxyBuilder (StateM MockProxySimState)) : runner Unit := do
  let s₀ ← nondet MockProxySimState
  let cfg ← nondet ProxyConfig
  let api := mkApi mockRawProxyOps
  match Model.validateConfig cfg with
  | .ok _ => assume False
  | .error _ =>
    let (res, s₁) := (api.withProxy cfg fun _ => do
      modify fun st => { st with startCalls := st.startCalls + 99 }
      return (.ok 42 : Except ProxyError Nat)).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- Across all `ProxyConfig` and `MockProxySimState` inputs, `withProxy` matches `Model.withProxyModel` (preserving explicit `listenPort`, normalizing `allowedTargets`, enforcing `IpPolicy` across arbitrary hosts, skipping `action`/`stopProxy` when `startProxy` fails, and propagating `stopProxy` errors on `.ok`). -/
def test_cproxy_withProxy_universalConfigAndLifecycleEquivalence
    {runner} [NondetTest runner]
    (mkApi : ConnectProxyBuilder (StateM MockProxySimState)) : runner Unit := do
  let s₀ ← nondet MockProxySimState
  let cfg ← nondet ProxyConfig
  let val ← nondet Nat
  let api := mkApi mockRawProxyOps
  let action (proxy : RunningProxy) : StateM MockProxySimState (Except ProxyError (Nat × UInt16)) :=
    pure (.ok (val, proxy.port))
  let (res, s₁) := (api.withProxy cfg action).run s₀
  let (expectedRes, expectedState) := (Model.withProxyModel mockRawProxyOps cfg action).run s₀
  NondetTest.assert (res = expectedRes ∧ s₁ = expectedState)
  match Model.validateConfig cfg with
  | .error _ =>
    NondetTest.assert (s₁ = s₀)
  | .ok _ =>
    match s₀.failStartWith with
    | some startErr =>
      NondetTest.assert (res = .error startErr ∧
        s₁.startCalls = s₀.startCalls + 1 ∧
        s₁.stopCalls = s₀.stopCalls ∧
        s₁.activeHandles = s₀.activeHandles)
    | none =>
      match s₀.failStopWith with
      | some stopErr =>
        NondetTest.assert (res = .error stopErr ∧
          s₁.startCalls = s₀.startCalls + 1 ∧
          s₁.stopCalls = s₀.stopCalls + 1 ∧
          s₁.activeHandles = s₀.activeHandles)
      | none =>
        NondetTest.assert (∃ boundPort evs,
          res = .ok ((val, boundPort), evs) ∧
          boundPort ≠ 0 ∧
          (cfg.listenPort = 0 ∨ boundPort = cfg.listenPort) ∧
          evs.size = s₀.scriptedAttempts.size ∧
          s₁.activeHandles = s₀.activeHandles)

/-- `withProxy` binds `listenPort = 0` to a non-zero port, skips DNS on denied/literal heads, steps sequentially through `primaryIp :: fallbackIps` when `primaryIp` fails `connect()`, emits `.failed` when all verified candidates fail, and emits 1 `ConnectEvent` per attempt including `"proxy stopped"`. -/
def test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory
    {runner} [NondetTest runner]
    (mkApi : ConnectProxyBuilder (StateM MockProxySimState)) : runner Unit := do
  let val ← nondet Nat
  let api := mkApi mockRawProxyOps
  let cfg : ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "API.Example.COM", port := 443 },
        { host := "down.example.com", port := 443 }
      ]
      ipPolicy := { base := .publicOnly, extraBans := #[.v4 0x0a000000 8] } }
  let s₀ : MockProxySimState :=
    { ephemeralPort := 51234
      dnsTable := [
        ("api.example.com", .resolved #[.v4 0x7f000001, mkNat64WellKnownIpv6 0x0a000001, .v4 0x5db8d822, .v4 0x08080808]),
        ("down.example.com", .resolved #[.v4 0x09090909])
      ]
      failConnectIps := [.v4 0x5db8d822, .v4 0x09090909]
      scriptedAttempts := #[
        .completedHead "GET http://api.example.com/ HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT evil.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT api.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT down.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .inFlightAtStop (some "api.example.com") (some 443)
      ] }
  let (res, s₁) := (api.withProxy cfg fun proxy => do
    if proxy.port == 51234 then
      return .ok val
    else
      return .error { kind := .ioError, message := "unexpected bound port" }).run s₀
  NondetTest.assert (s₁.activeHandles = [] ∧ s₁.startCalls = 1 ∧ s₁.stopCalls = 1)
  NondetTest.assert (s₁.dnsQueries = #["api.example.com", "down.example.com"])
  NondetTest.assert (s₁.dialedEndpoints = #[(.v4 0x5db8d822, 443), (.v4 0x08080808, 443), (.v4 0x09090909, 443)])
  match res with
  | .error _ => NondetTest.assert False
  | .ok (gotVal, events) =>
    NondetTest.assert (gotVal = val ∧ events.size = 5)
    NondetTest.assert (events[0]?.map (·.outcome) = some .denied ∧ events[0]?.bind (·.reason) ≠ none)
    NondetTest.assert (events[1]? = some {
      host := some "evil.example.com"
      port := some 443
      outcome := .denied
      reason := events[1]?.bind (·.reason)
    } ∧ events[1]?.bind (·.reason) ≠ none)
    NondetTest.assert (events[2]? = some {
      host := some "api.example.com"
      port := some 443
      outcome := .allowed
      reason := none
    })
    NondetTest.assert (events[3]? = some {
      host := some "down.example.com"
      port := some 443
      outcome := .failed
      reason := events[3]?.bind (·.reason)
    } ∧ events[3]?.bind (·.reason) ≠ none)
    NondetTest.assert (events[4]? = some {
      host := some "api.example.com"
      port := some 443
      outcome := .failed
      reason := some "proxy stopped"
    })

/-- When the caller callback returns `.error actionErr`, `withProxy` stops the running proxy (releasing active handles) and returns `.error actionErr` even if `stopProxy` also errors. -/
def test_cproxy_withProxy_callbackError_tearsDownAndPreservesError
    {runner} [NondetTest runner]
    (mkApi : ConnectProxyBuilder (StateM MockProxySimState)) : runner Unit := do
  let s₀ ← nondet MockProxySimState
  let actionErr ← nondet ProxyError
  assume (s₀.failStartWith = none)
  let cfg : ProxyConfig := { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] }
  let api := mkApi mockRawProxyOps
  let (res, s₁) := (api.withProxy cfg fun _ =>
    pure (Except.error actionErr : Except ProxyError Nat)).run s₀
  NondetTest.assert (res = .error actionErr)
  NondetTest.assert (s₁.startCalls = s₀.startCalls + 1 ∧ s₁.stopCalls = s₀.stopCalls + 1)
  NondetTest.assert (s₁.activeHandles.length = s₀.activeHandles.length)

/-- Over `ExceptT String (StateM MockProxySimState)`, an uncaught monadic exception or cancellation inside `action` triggers `MonadFinally` teardown (`stopProxy`) and propagates the exception without leaking handles. -/
def test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown
    {runner} [NondetTest runner]
    (mkExApi : ConnectProxyBuilder (ExceptT String (StateM MockProxySimState))) : runner Unit := do
  let s₀ ← nondet MockProxySimState
  assume (s₀.failStartWith = none ∧ s₀.failStopWith = none)
  let cfg : ProxyConfig := { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] }
  let apiEx := mkExApi mockRawProxyOpsEx
  let (res, s₁) := (ExceptT.run (apiEx.withProxy cfg fun _ =>
    (throw "cancelled" : ExceptT String (StateM MockProxySimState) (Except ProxyError Unit)))).run s₀
  NondetTest.assert (res = .error "cancelled")
  NondetTest.assert (s₁.startCalls = s₀.startCalls + 1 ∧ s₁.stopCalls = s₀.stopCalls + 1)
  NondetTest.assert (s₁.activeHandles = s₀.activeHandles)

/-- External runtime and differential-oracle assumptions grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- Differential equivalence against Python 3 `ipaddress`: for IPv4 `ip.is_global and not ip.is_multicast`, for `::ffff:0:0/96` and `64:ff9b::/96` `v4.is_global and not v4.is_multicast`, and for all other IPv6 `ip.is_global and not ip.is_multicast and not ip.is_site_local and not ip.is_reserved` (verified with 0 mismatches across all 65,536 `/16` prefixes). -/
  pythonIpaddressDifferentialEquivalence : Prop
  /-- Real loopback TCP upstream tunnel (`IpBase.empty` + `extraAllows := #[127.0.0.1/32]`) relays bidirectional bytes (including coalesced post-`\r\n\r\n` tunnel bytes and directional half-close) cleanly via `curl` and raw sockets, returning `(value, events)` in memory with zero temporary files. -/
  loopbackTunnelAndCurlIntegration : Prop
  /-- Real HTTP client probing confirms `403 Forbidden` (without `TCP RST` clobbering) on plain `GET`/`POST`, unlisted `(host, port)`, and banned/private IPs, `502 Bad Gateway` on unreachable upstream, multi-IP fallback when the first verified candidate fails `connect()`, header timeout/size rejection, decision/completion `ConnectEvent` order, and parallel collision-free `listenPort = 0` runs on `127.0.0.1`. -/
  httpStatusCodesLimitsFallbackAndParallelEphemeralPorts : Prop

end LeanSwe.ConnectProxy

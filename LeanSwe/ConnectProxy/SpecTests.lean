import Core.NondetTest
import Core.Assumptions
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.HealthySys

namespace LeanSwe.ConnectProxy

open Core (NondetTest ErrorObligation)
open Core.NondetTest
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

/-- Over any `sys` refining `RefinesHealthyCProxySys`, `createListener` binds strictly to `127.0.0.1` (`INADDR_LOOPBACK`), makes zero DNS or `connect` calls, preserves `proxyTable` and `wf`, resolves a non-zero loopback port (`listenPort = 0` or exact `listenPort`) on `.ok`, and deterministically closes every opened descriptor via `files.close` on `.error`. -/
def test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true ∧ (w₀.filesEnv.state.fds.map Prod.fst).Nodup)
  let vcfg ← nondet ValidProxyConfig
  let (res, (w₁, tr₁)) := (bridge.createListener (SysBridge.instrumentSysOps sys) vcfg).run (w₀, {})
  NondetTest.assert (w₁.wf = true ∧ w₁.proxyTable = w₀.proxyTable)
  NondetTest.assert (tr₁.dnsQueries = #[] ∧ tr₁.dialedAddrs = #[])
  NondetTest.assert (∀ sa ∈ tr₁.boundAddrs.toList,
    sa = .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK vcfg.config.listenPort)
  match res with
  | .ok (_, _, _, boundPort) =>
    NondetTest.assert (boundPort ≠ 0 ∧ (vcfg.config.listenPort = 0 ∨ boundPort = vcfg.config.listenPort))
  | .error err =>
    NondetTest.assert (err.message ≠ "" ∧
      (w₀.netEnv.eintrBudget ≤ SysBridge.MAX_EINTR_RETRIES → err.errnoCode ≠ some LinuxSyscall.Errno.EINTR))
    NondetTest.assert (∀ fd ∈ tr₁.openedFds.toList,
      fd ∈ tr₁.closedFds.toList ∧ LinuxSyscall.Files.assocGet w₁.filesEnv.state.fds fd = none)

/-- Over any `sys` refining `RefinesHealthyCProxySys`, Stage-1 `onHead` gates before DNS (`0` DNS and `0` `connect` calls on denied heads), literal IP targets make `0` DNS calls, domain targets make at most `1` DNS query (`#[host]`, no re-resolution), scoped IPv6 records (`scopeId != 0`) are excluded, every dialed `SockAddr` comes from an `allowsIp`-verified unbanned IP, and pipelined post-`\r\n\r\n` bytes plus `200 Connection Established` are conserved into `.connecting`/`.relay`. -/
def test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true)
  let cfg ← nondet ProxyConfig
  let headBytes ← nondet ByteArray
  let pipelined ← nondet ByteArray
  let cfd ← nondet Nat
  let events ← nondet (Array ConnectEvent)
  let initSlot : SysBridge.ClientSlot Nat Unit := { phase := .handshake cfd headBytes 1000 }
  let ((slot₁, events₁), (w₁, tr₁)) :=
    (bridge.handleCompleteHeadSync (SysBridge.instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      initSlot events cfd headBytes pipelined).run (w₀, {})
  NondetTest.assert (w₁.wf = true)
  NondetTest.assert (
    (∀ st, slot₁.phase = .relay st →
      st.pendingPrefix = pipelined ∧ st.pendingOff = 0 ∧ st.u2c.toList = Relay.reply200Bytes.data.toList) ∧
    (∀ c u h p cs ci le dl, slot₁.phase = .connecting c u h p cs ci le dl →
      slot₁.pipelined = pipelined))
  match Model.decideConnectHead cfg headBytes with
  | .deny _ _ _ =>
    NondetTest.assert (tr₁.dnsQueries = #[] ∧ tr₁.dialedAddrs = #[] ∧ events₁.size = events.size + 1)
  | .needResolve _ port (some litIp) =>
    NondetTest.assert (tr₁.dnsQueries = #[])
    NondetTest.assert (∀ sa ∈ tr₁.dialedAddrs.toList,
      sa = SysBridge.ipAddrToDialSockAddr litIp port ∧
      Model.allowsIp cfg.ipPolicy litIp = true ∧
      Model.isBannedByPrefixes cfg.ipPolicy.extraBans (SysBridge.effectiveDialIp litIp) = false)
  | .needResolve host port none =>
    NondetTest.assert (tr₁.dnsQueries = #[host])
    let (dnsRes, _) := (sys.dns.getaddrinfo host { family := .any, sockType := .stream }).run w₀
    match dnsRes with
    | .error _ =>
      NondetTest.assert (tr₁.dialedAddrs = #[])
    | .ok addrs =>
      NondetTest.assert (∀ sa ∈ tr₁.dialedAddrs.toList,
        ∃ ip, sa = SysBridge.ipAddrToDialSockAddr ip port ∧
          Model.allowsIp cfg.ipPolicy ip = true ∧
          Model.isBannedByPrefixes cfg.ipPolicy.extraBans (SysBridge.effectiveDialIp ip) = false ∧
          ∃ a ∈ addrs, a.scopeId = 0 ∧ SysBridge.dnsAddrToIpAddr? a = some ip)

/-- Over any `sys` refining `RefinesHealthyCProxySys`, listener `POLLIN` interest disables at `maxConcurrentTunnels`, `acceptNewClients` enforces `slots.size ≤ maxConcurrentTunnels` while retrying `EINTR` until cap or non-`EINTR` `accept4` error, and `stepHandshakeSync` enforces `headBuf.size ≤ maxHeaderBytes` (strict `< maxHeaderBytes` after readable wakeups), exact handshake byte conservation, `EINTR` retry progress, and refusal event emission on `maxHeaderBytes`/timeout/EOF. -/
def test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true)
  let cfg ← nondet ProxyConfig
  let lfd ← nondet Nat
  let cfd ← nondet Nat
  let nowMs ← nondet Nat
  let dlMs ← nondet Nat
  let slots ← nondet (Array (SysBridge.ClientSlot Nat Unit))
  let headBuf ← nondet ByteArray
  let cRev ← nondet LinuxSyscall.Poll.PollEvents
  let events ← nondet (Array ConnectEvent)
  assume (slots.size ≤ cfg.limits.maxConcurrentTunnels ∧ headBuf.size ≤ cfg.limits.maxHeaderBytes)
  NondetTest.assert (bridge.listenPollinEnabled slots.size cfg.limits.maxConcurrentTunnels =
    decide (slots.size < cfg.limits.maxConcurrentTunnels))
  let (slots', (w₁, tr₁)) :=
    (bridge.acceptNewClients (SysBridge.instrumentSysOps sys) cfg.limits lfd nowMs slots).run (w₀, {})
  NondetTest.assert (w₁.wf = true ∧ slots'.size ≤ cfg.limits.maxConcurrentTunnels ∧
    (w₀.netEnv.eintrBudget + (cfg.limits.maxConcurrentTunnels - slots.size) ≤ SysBridge.MAX_ACCEPT_BATCH →
      slots'.size = cfg.limits.maxConcurrentTunnels ∨ tr₁.netErrs.size > 0))
  let initSlot : SysBridge.ClientSlot Nat Unit := { phase := .handshake cfd headBuf dlMs }
  let ((slot', events'), (w₂, tr₂)) :=
    (bridge.stepHandshakeSync (SysBridge.instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      initSlot events cfd headBuf dlMs cRev nowMs).run (w₀, {})
  NondetTest.assert (w₂.wf = true ∧
    (∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' →
      buf'.size ≤ cfg.limits.maxHeaderBytes ∧
      ((cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true →
        buf'.size < cfg.limits.maxHeaderBytes) ∧
      buf'.data.toList = headBuf.data.toList ++ tr₂.recvBytes.toList ∧
      (cRev.pollin = true ∧
          w₀.netEnv.eintrBudget + (cfg.limits.maxHeaderBytes - headBuf.size) < SysBridge.MAX_HANDSHAKE_STEPS →
        LinuxSyscall.Errno.EAGAIN ∈ tr₂.netErrs.toList)) ∧
    ((∀ cfd' buf' dl', slot'.phase ≠ .handshake cfd' buf' dl') →
      (∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
      events'.size = events.size + 1))

/-- Over any `sys` refining `RefinesHealthyCProxySys`, `recvIntoRing`, `flushRingNonblock`, and `stepBidirectionalRelay` maintain `len ≤ RING_CAP` (`16 KiB`), exact FIFO byte conservation across short `recvfrom`/`sendto` chunks and `EINTR` retries, pipelined `pendingPrefix` ordering, and response preservation across peer `TCP RST` (`POLLIN | POLLERR | POLLHUP`). -/
def test_cproxy_healthy_relayByteConservationShortIoAndEintr
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true)
  let fd ← nondet Nat
  let ufd ← nondet Nat
  let fuel ← nondet Nat
  let rb ← nondet Relay.RingBuf
  let pipelined ← nondet ByteArray
  assume (rb.len ≤ Relay.RING_CAP)
  let (rxRes, (w₁, tr₁)) := (bridge.recvIntoRing (SysBridge.instrumentSysOps sys).net fd fuel rb).run (w₀, {})
  NondetTest.assert (w₁.wf = true)
  match rxRes with
  | none =>
    NondetTest.assert (∃ e ∈ tr₁.netErrs.toList,
      e = LinuxSyscall.Errno.EBADF ∨ e = LinuxSyscall.Errno.EINVAL ∨ e = LinuxSyscall.Errno.ENOTSOCK)
  | some (rb', eof) =>
    NondetTest.assert (rb'.len ≤ Relay.RING_CAP ∧ rb'.toList = rb.toList ++ tr₁.recvBytes.toList ∧
      (w₀.netEnv.eintrBudget + (Relay.RING_CAP - rb.len) ≤ fuel →
        rb'.writeAvail = 0 ∨ eof = true ∨ tr₁.netErrs.size > 0))
  let (txRes, (w₂, tr₂)) := (bridge.flushRingNonblock (SysBridge.instrumentSysOps sys).net fd fuel rb).run (w₀, {})
  NondetTest.assert (w₂.wf = true)
  match txRes with
  | none =>
    NondetTest.assert (∃ e ∈ tr₂.netErrs.toList, e ≠ LinuxSyscall.Errno.EAGAIN)
  | some rb' =>
    NondetTest.assert (rb'.len ≤ Relay.RING_CAP ∧ tr₂.sentBytes.toList ++ rb'.toList = rb.toList ∧
      (w₀.netEnv.eintrBudget + rb.len ≤ fuel →
        rb'.isEmpty = true ∨ LinuxSyscall.Errno.EAGAIN ∈ tr₂.netErrs.toList ∨ tr₂.sawZeroSend = true))
  let (stPipe, (w₃, tr₃)) :=
    (bridge.stepBidirectionalRelay (SysBridge.instrumentSysOps sys)
      (Relay.RelayState.init fd ufd pipelined) {} { pollout := true }).run (w₀, {})
  NondetTest.assert (w₃.wf = true ∧
    (stPipe.uWrClosed = false →
      tr₃.sentBytes.toList ++
        (stPipe.pendingPrefix.extract stPipe.pendingOff stPipe.pendingPrefix.size).data.toList =
        pipelined.data.toList ∧
      (w₀.netEnv.eintrBudget + pipelined.size ≤ Relay.MAX_RELAY_IO_STEPS →
        stPipe.prefixFlushed = true ∨ LinuxSyscall.Errno.EAGAIN ∈ tr₃.netErrs.toList ∨ tr₃.sawZeroSend = true)) ∧
    (stPipe.uWrClosed = true →
      stPipe.clientFd? = some fd ∧ stPipe.u2c.toList = Relay.reply200Bytes.data.toList))
  let (stRst, (w₄, tr₄)) :=
    (bridge.stepBidirectionalRelay (SysBridge.instrumentSysOps sys)
      (Relay.RelayState.init fd ufd ByteArray.empty)
      {} { pollin := true, pollerr := true, pollhup := true }).run (w₀, {})
  NondetTest.assert (w₄.wf = true ∧
    ((∃ e ∈ tr₄.netErrs.toList,
        e = LinuxSyscall.Errno.EBADF ∨ e = LinuxSyscall.Errno.EINVAL ∨ e = LinuxSyscall.Errno.ENOTSOCK) ∨
      (stRst.clientFd? = some fd ∧ stRst.u2c.toList = Relay.reply200Bytes.data.toList ++ tr₄.recvBytes.toList)))

/-- Over any `sys` refining `RefinesHealthyCProxySys`, `stopProxy` and `withProxy` deterministically close `listenFd`, `wakeR`, `wakeW`, and all active `slotOpenFds` via `files.close` (removing every closed handle from `FilesState.fds`), emit `"proxy stopped"` once per undecided slot, conserve `activeProxyCount`, and reject double `stopProxy` with `.invalidInput`. -/
def test_cproxy_healthy_withProxyAndStopClosesAllFds
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true ∧ (w₀.filesEnv.state.fds.map Prod.fst).Nodup)
  let cfg ← nondet ProxyConfig
  let vcfg ← nondet ValidProxyConfig
  let lfd ← nondet Nat
  let wakeR ← nondet Nat
  let wakeW ← nondet Nat
  let slots ← nondet (Array (SysBridge.ClientSlot Nat Unit))
  let events ← nondet (Array ConnectEvent)
  let rawOps := bridge.mkRawOps (SysBridge.instrumentSysOps sys)
  let hid := SysBridge.freshSyncHandleId w₀.proxyTable
  let activeEntry : SysBridge.SyncProxyEntry Nat :=
    { handleId := hid
      port := 8080
      vcfg := vcfg
      listenFd := lfd
      wakeR := wakeR
      wakeW := wakeW
      slots := slots
      events := events }
  let wActive : HealthySys.HealthySysWorld :=
    { w₀ with proxyTable := { nextHandleId := hid + 1, entries := activeEntry :: w₀.proxyTable.entries } }
  let proxy : RunningProxy := { handleId := hid, port := 8080 }
  let (stopRes, (w₁, tr₁)) := (rawOps.stopProxy proxy).run (wActive, {})
  NondetTest.assert (w₁.wf = true ∧ (rawOps.activeProxyCount.run (w₁, tr₁)).1 = w₀.proxyTable.entries.length)
  NondetTest.assert (∃ finalEvs,
    stopRes = .ok finalEvs ∧
    finalEvs.size = events.size + (slots.toList.filter (fun s => !s.eventEmitted)).length)
  NondetTest.assert (∀ fd ∈ ([lfd, wakeR, wakeW] ++ (slots.toList.flatMap HealthySys.slotOpenFds)),
    fd ∈ tr₁.closedFds.toList ∧ LinuxSyscall.Files.assocGet w₁.filesEnv.state.fds fd = none)
  let (dblRes, (w₁d, tr₁d)) := (rawOps.stopProxy proxy).run (w₁, tr₁)
  NondetTest.assert ((∃ err, dblRes = .error err ∧ err.kind = .invalidInput ∧ err.message ≠ "") ∧
    (rawOps.activeProxyCount.run (w₁d, tr₁d)).1 = w₀.proxyTable.entries.length)
  let (_, (w₂, tr₂)) := (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))).run (w₀, {})
  NondetTest.assert (w₂.wf = true ∧ (rawOps.activeProxyCount.run (w₂, tr₂)).1 = w₀.proxyTable.entries.length)
  NondetTest.assert (∀ fd ∈ tr₂.openedFds.toList,
    fd ∈ tr₂.closedFds.toList ∧ LinuxSyscall.Files.assocGet w₂.filesEnv.state.fds fd = none)

/-- Over any `sys` refining `RefinesHealthyCProxySys`, `buildPollBatchSync` constructs kernel-valid `ppoll` batches, `stepSlotSync` on `.connecting` and `.closingReply` enforces zero DNS re-resolution, verified-candidate-only fallback dialing, pipelined byte conservation on `SO_ERROR = 0`, and deterministic FD release on timeout/error/disconnect, and `pollAndStepTickSync` preserves `wf`, `maxConcurrentTunnels`, finished-slot pruning, and `EINTR` retry discipline. -/
def test_cproxy_healthy_pollAndStepTickAndFallbackConnect
    {runner} [NondetTest runner] (bridge : HealthySys.SysBridgeTarget) : runner Unit := do
  let sys ← nondet (SysBridge.CProxySysOpsM (StateM HealthySys.HealthySysWorld) Nat)
  assume (HealthySys.RefinesHealthyCProxySys sys)
  let w₀ ← nondet HealthySys.HealthySysWorld
  assume (w₀.wf = true ∧ (w₀.filesEnv.state.fds.map Prod.fst).Nodup)
  let cfg ← nondet ProxyConfig
  let wakeR ← nondet Nat
  let lfd ← nondet Nat
  let cfd ← nondet Nat
  let ufd ← nondet Nat
  let host ← nondet String
  let port ← nondet UInt16
  let candidates ← nondet (Array IpAddr)
  let candIdx ← nondet Nat
  let nowMs ← nondet Nat
  let dlMs ← nondet Nat
  let pipelined ← nondet ByteArray
  let replyBytes ← nondet ByteArray
  let cRev ← nondet LinuxSyscall.Poll.PollEvents
  let uRev ← nondet LinuxSyscall.Poll.PollEvents
  let stopFlag ← nondet Bool
  let slots ← nondet (Array (SysBridge.ClientSlot Nat Unit))
  let events ← nondet (Array ConnectEvent)
  assume (slots.size ≤ cfg.limits.maxConcurrentTunnels ∧
    ∀ ip ∈ candidates.toList, Model.allowsIp cfg.ipPolicy ip = true)
  let (reqs, indices, timeout?) :=
    bridge.buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels nowMs slots
  NondetTest.assert (reqs[0]? = some (wakeR, { pollin := true }) ∧
    reqs[1]? = some (lfd, { pollin := decide (slots.size < cfg.limits.maxConcurrentTunnels) }) ∧
    indices.size = slots.size ∧
    ∀ ts, timeout? = some ts → ts.isValid = true)
  let connSlot : SysBridge.ClientSlot Nat Unit :=
    { phase := .connecting cfd ufd host port candidates candIdx none dlMs
      pipelined := pipelined
      target? := some (host, port) }
  let ((connSlot', connEvs'), (wC, trC)) :=
    (bridge.stepSlotSync (SysBridge.instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      connSlot events cRev uRev nowMs).run (w₀, {})
  NondetTest.assert (wC.wf = true ∧ trC.dnsQueries = #[] ∧
    (∀ sa ∈ trC.dialedAddrs.toList,
      ∃ ip ∈ candidates.toList,
        sa = SysBridge.ipAddrToDialSockAddr ip port ∧
        Model.allowsIp cfg.ipPolicy ip = true ∧
        Model.isBannedByPrefixes cfg.ipPolicy.extraBans (SysBridge.effectiveDialIp ip) = false) ∧
    (∀ st, connSlot'.phase = .relay st →
      st.pendingPrefix = pipelined ∧ st.pendingOff = 0 ∧
      st.u2c.toList = Relay.reply200Bytes.data.toList ∧
      connEvs'.size = events.size + 1) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = true →
      ufd ∈ trC.closedFds.toList ∧ cfd ∈ trC.closedFds.toList ∧
      LinuxSyscall.Files.assocGet wC.filesEnv.state.fds ufd = none ∧
      LinuxSyscall.Files.assocGet wC.filesEnv.state.fds cfd = none) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = false ∧
        (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = false ∧
        nowMs ≥ dlMs →
      ufd ∈ trC.closedFds.toList))
  let closeSlot : SysBridge.ClientSlot Nat Unit :=
    { phase := .closingReply (some cfd) replyBytes 0 false 0 dlMs }
  let ((closeSlot', _), (wCl, trCl)) :=
    (bridge.stepSlotSync (SysBridge.instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      closeSlot events cRev uRev nowMs).run (w₀, {})
  NondetTest.assert (wCl.wf = true ∧
    (nowMs ≥ dlMs → closeSlot'.phase = .done) ∧
    (closeSlot'.phase = .done →
      cfd ∈ trCl.closedFds.toList ∧
      LinuxSyscall.Files.assocGet wCl.filesEnv.state.fds cfd = none))
  let (tickOut, (wT, trT)) :=
    (bridge.pollAndStepTickSync (SysBridge.instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      stopFlag wakeR lfd slots events).run (w₀, {})
  NondetTest.assert (wT.wf = true ∧
    (tickOut = .retryEintr ↔ trT.pollOutcomes = #[some LinuxSyscall.Errno.EINTR]) ∧
    (stopFlag = true → tickOut = .retryEintr ∨ tickOut = .stopOrFatal) ∧
    (stopFlag = false ∧ trT.pollOutcomes = #[none] →
      ∃ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs) ∧
    (∀ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs →
      stopFlag = false ∧
      nextSlots.size ≤ cfg.limits.maxConcurrentTunnels ∧
      ∀ s ∈ nextSlots.toList, s.isFinished = false))

/-- Declared error-coverage matrix for public fallible `LeanSwe.ConnectProxy` requests (`ProxyErrorKind`). -/
def errorCoverage : List (ErrorObligation ProxyErrorKind) :=
  [ { request := "LeanSwe.ConnectProxy.parseIpAddr"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseIpAddr_invalidInput" .real }
  , { request := "LeanSwe.ConnectProxy.parseIpAddr"
      errorKind := .addressInUse
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpAddr_never_addressInUse" }
  , { request := "LeanSwe.ConnectProxy.parseIpAddr"
      errorKind := .permissionDenied
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpAddr_never_permissionDenied" }
  , { request := "LeanSwe.ConnectProxy.parseIpAddr"
      errorKind := .resourceExhausted
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpAddr_never_resourceExhausted" }
  , { request := "LeanSwe.ConnectProxy.parseIpAddr"
      errorKind := .ioError
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpAddr_never_ioError" }
  , { request := "LeanSwe.ConnectProxy.parseIpPrefix"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseIpPrefix_invalidInput" .real }
  , { request := "LeanSwe.ConnectProxy.parseIpPrefix"
      errorKind := .addressInUse
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpPrefix_never_addressInUse" }
  , { request := "LeanSwe.ConnectProxy.parseIpPrefix"
      errorKind := .permissionDenied
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpPrefix_never_permissionDenied" }
  , { request := "LeanSwe.ConnectProxy.parseIpPrefix"
      errorKind := .resourceExhausted
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpPrefix_never_resourceExhausted" }
  , { request := "LeanSwe.ConnectProxy.parseIpPrefix"
      errorKind := .ioError
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseIpPrefix_never_ioError" }
  , { request := "LeanSwe.ConnectProxy.parseConnectRequest"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_parseConnectRequest_invalidInput" .real }
  , { request := "LeanSwe.ConnectProxy.parseConnectRequest"
      errorKind := .addressInUse
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseConnectRequest_never_addressInUse" }
  , { request := "LeanSwe.ConnectProxy.parseConnectRequest"
      errorKind := .permissionDenied
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseConnectRequest_never_permissionDenied" }
  , { request := "LeanSwe.ConnectProxy.parseConnectRequest"
      errorKind := .resourceExhausted
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseConnectRequest_never_resourceExhausted" }
  , { request := "LeanSwe.ConnectProxy.parseConnectRequest"
      errorKind := .ioError
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_parseConnectRequest_never_ioError" }
  , { request := "LeanSwe.ConnectProxy.validateConfig"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_validateConfig_invalidInput" .real }
  , { request := "LeanSwe.ConnectProxy.validateConfig"
      errorKind := .addressInUse
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_validateConfig_never_addressInUse" }
  , { request := "LeanSwe.ConnectProxy.validateConfig"
      errorKind := .permissionDenied
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_validateConfig_never_permissionDenied" }
  , { request := "LeanSwe.ConnectProxy.validateConfig"
      errorKind := .resourceExhausted
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_validateConfig_never_resourceExhausted" }
  , { request := "LeanSwe.ConnectProxy.validateConfig"
      errorKind := .ioError
      justification := .provedImpossible "LeanSwe.ConnectProxy.Proofs.cproxy_validateConfig_never_ioError" }
  , { request := "LeanSwe.ConnectProxy.withProxy"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_invalidInput" .real }
  , { request := "LeanSwe.ConnectProxy.withProxy"
      errorKind := .addressInUse
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_addressInUse" .real }
  , { request := "LeanSwe.ConnectProxy.withProxy"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_permissionDenied" .mocked }
  , { request := "LeanSwe.ConnectProxy.withProxy"
      errorKind := .resourceExhausted
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_resourceExhausted" .mocked }
  , { request := "LeanSwe.ConnectProxy.withProxy"
      errorKind := .ioError
      justification := .tested "LeanSwe.ConnectProxy.RuntimeTests.err_cproxy_withProxy_ioError" .real } ]

end LeanSwe.ConnectProxy

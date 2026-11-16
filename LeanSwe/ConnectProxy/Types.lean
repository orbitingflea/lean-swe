import LeanSwe.ConnectProxy.Raw.Types

namespace LeanSwe.ConnectProxy

export LeanSwe.ConnectProxy.Raw
  (ProxyErrorKind ProxyError ConnectProxyRawError IpAddr IpPrefix IpBase IpPolicy
   TargetRule ProxyLimits ProxyConfig ValidProxyConfig ConnectOutcome ConnectEvent
   RunningProxy HeadDecision ResolveDecision RawConnectProxyOpsM RawConnectProxyOps)

/-- Public HTTP `CONNECT` proxy operations exported by `LeanSwe.ConnectProxy`, parameterized over `m`. -/
structure ConnectProxyApiM (m : Type → Type) where
  /-- Parse a strict IPv4 (`a.b.c.d`) or RFC 4291 IPv6 literal, rejecting `*` wildcards, `/prefix` suffixes, and octal/shorthand forms. -/
  parseIpAddr : String → Except ProxyError IpAddr
  /-- Parse a single IPv4/IPv6 literal (`/32` or `/128`) or canonical CIDR `/prefix` block, rejecting `*` wildcards and non-zero host bits. -/
  parseIpPrefix : String → Except ProxyError IpPrefix
  /-- Return `true` iff `ip` is globally-routable unicast under the complete IANA RFC 6890 / RFC 4291 special-purpose registry. -/
  isGlobalIp : IpAddr → Bool
  /-- Evaluate `IpPolicy` as `(base ∪ extraAllows) \ extraBans`, unwrapping embedded IPv4-in-IPv6 addresses against bans and `.publicOnly`. -/
  allowsIp : IpPolicy → IpAddr → Bool
  /-- Parse and normalize an HTTP/1.x `CONNECT <authority> HTTP/1.<0|1>\r\n...\r\n\r\n` request head into a canonical `TargetRule`. -/
  parseConnectRequest : ByteArray → Except ProxyError TargetRule
  /-- Validate and normalize a `ProxyConfig` (`TargetRule` hosts/ports, `IpPrefix` lengths, and positive `ProxyLimits`). -/
  validateConfig : ProxyConfig → Except ProxyError ValidProxyConfig
  /-- Run `action` with a scoped `127.0.0.1` `CONNECT` proxy, guaranteeing listener/tunnel teardown via `MonadFinally` and returning `(val, events)`. -/
  withProxy :
    {α : Type} →
    ProxyConfig →
    (RunningProxy → m (Except ProxyError α)) →
    m (Except ProxyError (α × Array ConnectEvent))

/-- Concrete `IO` HTTP `CONNECT` proxy API bundle exported by `LeanSwe.ConnectProxy`. -/
abbrev ConnectProxyApi := ConnectProxyApiM IO

end LeanSwe.ConnectProxy

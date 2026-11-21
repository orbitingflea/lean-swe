import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Impl

namespace LeanSwe.ConnectProxy

/-- Default `IO` HTTP `CONNECT` proxy API backed by `LeanSwe.LinuxSyscall.{Net,Poll,Dns,TimeRand}`. -/
def defaultApi : ConnectProxyApi :=
  Internal.defaultIoApi

/-- Parse a strict IPv4 (`a.b.c.d`) or RFC 4291 IPv6 literal into `IpAddr`. -/
@[inline] def parseIpAddr (s : String) : Except ProxyError IpAddr :=
  defaultApi.parseIpAddr s

/-- Parse a single IPv4/IPv6 literal or canonical CIDR `/prefix` block into `IpPrefix`. -/
@[inline] def parseIpPrefix (s : String) : Except ProxyError IpPrefix :=
  defaultApi.parseIpPrefix s

/-- Return `true` iff `ip` is globally-routable unicast per the complete IANA RFC 6890 / RFC 4291 registry. -/
@[inline] def isGlobalIp (ip : IpAddr) : Bool :=
  defaultApi.isGlobalIp ip

/-- Evaluate `IpPolicy` as `(base ∪ extraAllows) \ extraBans` with IPv4-in-IPv6 unwrapping. -/
@[inline] def allowsIp (policy : IpPolicy) (ip : IpAddr) : Bool :=
  defaultApi.allowsIp policy ip

/-- Parse and normalize an HTTP/1.x `CONNECT` request head into a canonical `TargetRule`. -/
@[inline] def parseConnectRequest (raw : ByteArray) : Except ProxyError TargetRule :=
  defaultApi.parseConnectRequest raw

/-- Validate and normalize a `ProxyConfig` before starting a proxy. -/
@[inline] def validateConfig (cfg : ProxyConfig) : Except ProxyError ValidProxyConfig :=
  defaultApi.validateConfig cfg

/-- Run `action` with a scoped `127.0.0.1` `CONNECT` proxy, guaranteeing teardown via `MonadFinally` and returning `(val, events)`. -/
@[inline] def withProxy {α : Type} (cfg : ProxyConfig)
    (action : RunningProxy → IO (Except ProxyError α)) :
    IO (Except ProxyError (α × Array ConnectEvent)) :=
  defaultApi.withProxy cfg action

end LeanSwe.ConnectProxy

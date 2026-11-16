import LeanSwe.ConnectProxy.Raw.Types
import LeanSwe.ConnectProxy.Raw.Impl

namespace LeanSwe.ConnectProxy.Raw

@[extern "leanswe_cproxy_create"]
private opaque rawCreate :
  UInt16 → UInt64 → UInt64 → UInt64 → UInt64 →
  IO (UInt32 × UInt32 × String × UInt64 × UInt16)

@[extern "leanswe_cproxy_run_loop"]
private opaque rawRunLoop :
  UInt64 →
  @& (ByteArray → Internal.HeadRawResult) →
  @& (String → UInt16 → ByteArray → Internal.ResolveRawResult) →
  IO Unit

@[extern "leanswe_cproxy_stop"]
private opaque rawStop : UInt64 → IO (UInt32 × UInt32 × String × Array Internal.EventRawTuple)

@[extern "leanswe_cproxy_active_count"]
private opaque rawActiveCount : IO Nat

private def cproxyFfiOps : Internal.CProxyFfiOps :=
  { createProxy := rawCreate
    runLoop := rawRunLoop
    stopProxy := rawStop
    activeCount := rawActiveCount }

/-- Default loopback HTTP `CONNECT` raw proxy operations backed by `c/cproxy_shim.c`. -/
def defaultOps : RawConnectProxyOps :=
  Internal.mkRawOps cproxyFfiOps

/-- Normalize a raw OS socket/listener error into a `ProxyError` with a non-empty message. -/
@[inline] def mapRawError (err : ConnectProxyRawError) : ProxyError :=
  defaultOps.mapRawError err

/-- Bind `127.0.0.1` (`vcfg.config.listenPort`) and serve `CONNECT` tunnels gated by pure `onHead` and `onResolved` callbacks. -/
@[inline] def startProxy
    (vcfg : ValidProxyConfig)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision) :
    IO (Except ProxyError RunningProxy) :=
  defaultOps.startProxy vcfg onHead onResolved

/-- Stop accepting connections, close all active tunnels, wait for the server loop, and return recorded `ConnectEvent`s. -/
@[inline] def stopProxy (proxy : RunningProxy) : IO (Except ProxyError (Array ConnectEvent)) :=
  defaultOps.stopProxy proxy

/-- Return the number of currently active (started and not yet stopped) proxy instances. -/
@[inline] def activeProxyCount : IO Nat :=
  defaultOps.activeProxyCount

end LeanSwe.ConnectProxy.Raw

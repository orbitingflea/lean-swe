import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.SysBridge

namespace LeanSwe.ConnectProxy.Internal

open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

/-- Build a pure generic `ConnectProxyApiM m` bundle backed by an injected `RawConnectProxyOpsM m`. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawConnectProxyOpsM m) : ConnectProxyApiM m :=
  { parseIpAddr := Model.parseIpAddr
    parseIpPrefix := Model.parseIpPrefix
    isGlobalIp := Model.isGlobalIp
    allowsIp := Model.allowsIp
    parseConnectRequest := Model.parseConnectRequest
    validateConfig := Model.validateConfig
    withProxy := fun cfg action => Model.withProxyModel ops cfg action }

/-- Default `IO` `ConnectProxyApi` backed purely by `LeanSwe.LinuxSyscall.{Net,Poll,Dns,TimeRand}` via `SysBridge`. -/
def defaultIoApi : ConnectProxyApi :=
  { parseIpAddr := Model.parseIpAddr
    parseIpPrefix := Model.parseIpPrefix
    isGlobalIp := Model.isGlobalIp
    allowsIp := Model.allowsIp
    parseConnectRequest := Model.parseConnectRequest
    validateConfig := Model.validateConfig
    withProxy := fun cfg action => SysBridge.withProxyIo cfg action }

end LeanSwe.ConnectProxy.Internal

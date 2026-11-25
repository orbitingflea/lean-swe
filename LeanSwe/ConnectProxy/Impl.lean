import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.BridgeState
import LeanSwe.ConnectProxy.SysBridge.Driver

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

/-- Build a full `ConnectProxyApiM m` bundle unifying `Impl`, `SysBridge`, and `Relay` directly
    over `LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}` (`CProxySysOpsM m RawFd`) and `Core.ConcOpsM m`. -/
def mkFullApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (sys : Internal.SysBridge.CProxySysOpsM m LinuxSyscall.RawFd)
    (conc : Core.ConcOpsM m) : ConnectProxyApiM m :=
  { parseIpAddr := Model.parseIpAddr
    parseIpPrefix := Model.parseIpPrefix
    isGlobalIp := Model.isGlobalIp
    allowsIp := Model.allowsIp
    parseConnectRequest := Model.parseConnectRequest
    validateConfig := Model.validateConfig
    withProxy := fun cfg action =>
      match Model.validateConfig cfg with
      | .error err => pure (.error err)
      | .ok vcfg => SysBridge.Driver.withProxyM sys conc vcfg action }

end LeanSwe.ConnectProxy.Internal

import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model

namespace LeanSwe.ConnectProxy.Internal

open LeanSwe.ConnectProxy

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

end LeanSwe.ConnectProxy.Internal

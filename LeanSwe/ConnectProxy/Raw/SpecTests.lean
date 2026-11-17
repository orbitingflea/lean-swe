import Core.NondetTest
import LeanSwe.ConnectProxy.Raw.Types

namespace LeanSwe.ConnectProxy.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_cproxyRaw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawConnectProxyOps) : runner Unit := do
  let raw ← nondet ConnectProxyRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `ops.mapRawError` maps every `ConnectProxyRawError` variant to its exact `ProxyErrorKind` and `errnoCode`. -/
def test_cproxyRaw_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (ops : RawConnectProxyOps) : runner Unit := do
  let raw ← nondet ConnectProxyRawError
  let err := ops.mapRawError raw
  match raw with
  | .invalidArgument errno? _ =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.errnoCode = errno?)
  | .addressInUse _ errno _ =>
    NondetTest.assert (err.kind = .addressInUse ∧ err.errnoCode = some errno)
  | .permissionDenied errno _ =>
    NondetTest.assert (err.kind = .permissionDenied ∧ err.errnoCode = some errno)
  | .resourceExhausted errno _ =>
    NondetTest.assert (err.kind = .resourceExhausted ∧ err.errnoCode = some errno)
  | .otherError errno _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.errnoCode = some errno)
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.errnoCode = none)

/-- `ops.startProxy` rejects any `ValidProxyConfig` whose `ProxyLimits` has a zero field with `.invalidInput` without leaking handles. -/
def test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput
    {S : Type} {runner} [NondetTest runner] (ops : RawConnectProxyOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let vcfg ← nondet ValidProxyConfig
  let lim := vcfg.config.limits
  assume (lim.maxHeaderBytes = 0 ∨ lim.headerTimeoutMs = 0 ∨
    lim.connectTimeoutMs = 0 ∨ lim.maxConcurrentTunnels = 0)
  let onHead (bs : ByteArray) : HeadDecision := let _ := bs; .deny none none "rejected"
  let onResolved (h : String) (p : UInt16) (ips : Array IpAddr) : ResolveDecision :=
    let _ := (h, p, ips); .deny "rejected"
  let n₀ := (ops.activeProxyCount.run s₀).1
  let (res, s₁) := (ops.startProxy vcfg onHead onResolved).run s₀
  let n₁ := (ops.activeProxyCount.run s₁).1
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ n₁ = n₀)

/-- `ops.startProxy` binds a non-zero port (resolving `listenPort = 0` to an ephemeral port), increments `activeProxyCount`, restores `activeProxyCount` on `stopProxy`, and rejects double-stop with `.invalidInput`. -/
def test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount
    {S : Type} {runner} [NondetTest runner] (ops : RawConnectProxyOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let vcfg ← nondet ValidProxyConfig
  let onHead (bs : ByteArray) : HeadDecision := let _ := bs; .deny none none "denied"
  let onResolved (h : String) (p : UInt16) (ips : Array IpAddr) : ResolveDecision :=
    let _ := (h, p, ips); .deny "denied"
  let n₀ := (ops.activeProxyCount.run s₀).1
  let (startRes, s₁) := (ops.startProxy vcfg onHead onResolved).run s₀
  match startRes with
  | .error _ => assume False
  | .ok proxy =>
    let n₁ := (ops.activeProxyCount.run s₁).1
    NondetTest.assert (proxy.port ≠ 0 ∧
      (vcfg.config.listenPort = 0 ∨ proxy.port = vcfg.config.listenPort) ∧
      n₁ = n₀ + 1)
    let (stopRes, s₂) := (ops.stopProxy proxy).run s₁
    match stopRes with
    | .error _ => assume False
    | .ok _ =>
      let n₂ := (ops.activeProxyCount.run s₂).1
      NondetTest.assert (n₂ = n₀)
      let (doubleStopRes, s₃) := (ops.stopProxy proxy).run s₂
      let n₃ := (ops.activeProxyCount.run s₃).1
      NondetTest.assert ((∃ e, doubleStopRes = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ n₃ = n₀)

/-- External OS and socket trust boundary assumptions for `cproxy_shim.c` grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `cproxy_shim.c` binds strictly to `127.0.0.1` (`INADDR_LOOPBACK` with `SO_REUSEADDR`, never `0.0.0.0`, `::`, or `SO_REUSEPORT`), resolves `listenPort = 0` via `getsockname` to `RunningProxy.port ∈ 1..65535`, maps `EADDRINUSE` to `.addressInUse`, saturates `Nat` `ProxyLimits` to `UInt64`, clamps `poll()` `int` slices to `INT_MAX`, and grows slot and `head_buf` allocations on demand. -/
  loopbackOnlyBindEphemeralPortAndLimitBounds : Prop
  /-- Each accepted connection consumes handshake bytes into `slot->head_buf` via normal `recv` (no `MSG_PEEK` CPU spin), scans for `\r\n\r\n` before rejecting `head_len == maxHeaderBytes`, flushes any coalesced post-`\r\n\r\n` client bytes from `slot->head_buf` directly to `upstream_fd` via `POLLOUT` after queueing `200 Connection Established` at index `0` of the upstream-to-client buffer, and flushes `403`/`502` in a bounded `CLOSING_REPLY` state (`min(headerTimeoutMs, 250)` ms, `SHUT_WR` + `<= 64 KiB` drain) avoiding `sk_receive_queue` `TCP RST`. -/
  boundedHandshakeDrainAndCleanErrorReplies : Prop
  /-- `cproxy_shim.c` invokes pure `onHead` on the dedicated Lean server thread before DNS, skipping `getaddrinfo` on `.deny` (`403`) and on literal IP targets (`literalIp? = some ip`), and runs `getaddrinfo` off-thread on `256 KiB`-stack detached C helper pthreads holding `job->mu` across non-blocking `notify_wfd` writes (passing `#[]` to `onResolved` for `403` when `rc == 0` yields only skipped `sin6_scope_id != 0` entries). -/
  stage1HeadGateAndOffThreadRefcountedDns : Prop
  /-- `cproxy_shim.c` steps sequentially through verified `primaryIp :: fallbackIps` via direct `sockaddr_in` / `sockaddr_in6` (`AF_INET` for `::ffff:0:0/96`, treating `EINPROGRESS` and `EINTR` as `POLLOUT` waits with per-candidate `connectTimeoutMs`, aborting on client `POLLERR | POLLHUP | POLLNVAL` as `"client disconnected"`), never re-resolving `host`. -/
  directVerifiedSockaddrSequentialDial : Prop
  /-- `listen_fd` omits `POLLIN` at `active_slots >= maxConcurrentTunnels`, `poll()` relay uses `16 KiB` ring buffers with `MSG_NOSIGNAL`, clears `POLLIN` immediately on `EOF` while firing `shutdown(SHUT_WR)` immediately on empty buffer or final drained byte, closes both FDs on hard socket errors, emits 1 `ConnectEvent` in decision/completion order, and on `stopProxy` wakes immediately without blocking on stalled DNS and appends `"proxy stopped"` in `accept()` order for undecided slots only. -/
  concurrencyAdmissionHalfCloseRelayAndEventOrder : Prop

end LeanSwe.ConnectProxy.Raw

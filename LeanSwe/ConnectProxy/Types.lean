namespace LeanSwe.ConnectProxy

/-- Classification of errors produced by `LeanSwe.ConnectProxy`. -/
inductive ProxyErrorKind where
  /-- Malformed IP/CIDR literal, malformed `CONNECT` head, invalid `TargetRule`, invalid `ProxyLimits`, or stale handle. -/
  | invalidInput
  /-- Requested `127.0.0.1` `listenPort` is already bound (`EADDRINUSE`). -/
  | addressInUse
  /-- Insufficient permissions to create or bind a loopback socket (`EACCES` / `EPERM`). -/
  | permissionDenied
  /-- File descriptor, memory, or thread limit exhausted (`EMFILE` / `ENFILE` / `ENOMEM` / `EAGAIN`). -/
  | resourceExhausted
  /-- Other OS-level socket, listener, or teardown I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.ConnectProxy` operations. -/
structure ProxyError where
  /-- Machine-checkable error category. -/
  kind : ProxyErrorKind
  /-- Underlying OS `errno` code when produced by a system call. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Reducible IPv4 or IPv6 address in big-endian (network) bit order. -/
inductive IpAddr where
  /-- 32-bit IPv4 address (`(a <<< 24) ||| (b <<< 16) ||| (c <<< 8) ||| d`). -/
  | v4 (addr : UInt32)
  /-- 128-bit IPv6 address split into upper 64 bits (`hi`, bits 0..63) and lower 64 bits (`lo`, bits 64..127). -/
  | v6 (hi : UInt64) (lo : UInt64)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Reducible IPv4 or IPv6 CIDR prefix block evaluated via exact bitwise masks. -/
inductive IpPrefix where
  /-- IPv4 CIDR block with `prefixLen ≤ 32`. -/
  | v4 (addr : UInt32) (prefixLen : Nat)
  /-- IPv6 CIDR block with `prefixLen ≤ 128`. -/
  | v6 (hi : UInt64) (lo : UInt64) (prefixLen : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Base IP allowlist posture before applying `extraAllows` and `extraBans`. -/
inductive IpBase where
  /-- Permit all globally-routable unicast IPs per IANA RFC 6890 / RFC 4291 (`isGlobalIp`). -/
  | publicOnly
  /-- Start with all IPs disallowed unless matched by `extraAllows`. -/
  | empty
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Two-set IP policy evaluated as `(base ∪ extraAllows) \ extraBans` with IPv4-in-IPv6 unwrapping. -/
structure IpPolicy where
  /-- Base IP posture (defaults to `.publicOnly`). -/
  base : IpBase := .publicOnly
  /-- Additional allowed CIDR blocks unioned with `base`. -/
  extraAllows : Array IpPrefix := #[]
  /-- Explicitly banned CIDR blocks that always override both `base` and `extraAllows`. -/
  extraBans : Array IpPrefix := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Exact `(host, port)` destination rule (no wildcards). -/
structure TargetRule where
  /-- Target domain name, IPv4 literal, or bracketed `[IPv6]` literal (normalized to lowercase ASCII). -/
  host : String
  /-- Target TCP port (`1..65535`; `0` is rejected). -/
  port : UInt16 := 443
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Resource, header size, and timeout caps protecting the host proxy from stalls and FD floods. -/
structure ProxyLimits where
  /-- Maximum bytes permitted for the `CONNECT` HTTP request head including `\r\n\r\n` (`> 0`). -/
  maxHeaderBytes : Nat := 8192
  /-- Maximum time in milliseconds to receive a complete `\r\n\r\n` request head (`> 0`). -/
  headerTimeoutMs : Nat := 30_000
  /-- Maximum time in milliseconds per verified upstream `IpAddr` TCP `connect()` attempt (`> 0`). -/
  connectTimeoutMs : Nat := 30_000
  /-- Maximum simultaneous client connections/tunnels served concurrently (`> 0`). -/
  maxConcurrentTunnels : Nat := 128
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Caller configuration for `withProxy`. -/
structure ProxyConfig where
  /-- Loopback `127.0.0.1` TCP port to bind (`0` selects an OS-assigned ephemeral free port). -/
  listenPort : UInt16 := 0
  /-- Exact `(host, port)` destination allowlist. -/
  allowedTargets : Array TargetRule := #[]
  /-- Upstream resolved-IP filtering policy. -/
  ipPolicy : IpPolicy := {}
  /-- Header, timeout, and concurrency limits. -/
  limits : ProxyLimits := {}
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Normalized, boundary-validated `ProxyConfig` produced by `validateConfig`. -/
structure ValidProxyConfig where
  /-- Normalized `ProxyConfig` with lowercase canonical `TargetRule`s, valid `IpPrefix` lengths, and positive `ProxyLimits`. -/
  config : ProxyConfig
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Outcome classification recorded for each accepted client connection. -/
inductive ConnectOutcome where
  /-- Target and verified upstream IP were permitted and TCP `connect()` succeeded (`200 Connection Established`). -/
  | allowed
  /-- Refused by HTTP method/framing, `allowedTargets`, or `IpPolicy` (`403 Forbidden`). -/
  | denied
  /-- Permitted by policy, but DNS lookup or upstream `connect()` failed (`502 Bad Gateway`), or proxy stopped mid-handshake/dial. -/
  | failed
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single in-memory audit record emitted per accepted client connection (no wall-clock dependency). -/
structure ConnectEvent where
  /-- Normalized target host when parseable from a valid `CONNECT` request line. -/
  host : Option String := none
  /-- Target port when parseable from a valid `CONNECT` request line. -/
  port : Option UInt16 := none
  /-- Final disposition of the connection attempt. -/
  outcome : ConnectOutcome
  /-- Diagnostic reason (`none` when `outcome = .allowed`, `some ...` when `.denied` or `.failed`). -/
  reason : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Handle to a running loopback `127.0.0.1` `CONNECT` proxy instance. -/
structure RunningProxy where
  /-- Opaque handle identifier allocated for the running proxy instance. -/
  handleId : Nat
  /-- Bound loopback TCP port on `127.0.0.1` (`1..65535`, resolved via `getsockname` when `listenPort = 0`). -/
  port : UInt16
  deriving Repr, BEq, DecidableEq, Inhabited

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

/-- Pure representation of raw OS socket/listener error inputs for total error-mapping specs. -/
inductive ConnectProxyRawError where
  /-- Invalid argument, socket parameter, or proxy handle (`EINVAL`). -/
  | invalidArgument (errno? : Option UInt32) (detail : String)
  /-- Loopback `listenPort` is already in use (`EADDRINUSE`). -/
  | addressInUse (port : UInt16) (errno : UInt32) (detail : String)
  /-- Permission denied on socket creation or bind (`EACCES` / `EPERM`). -/
  | permissionDenied (errno : UInt32) (detail : String)
  /-- File descriptor, memory, or OS thread exhaustion (`EMFILE` / `ENFILE` / `ENOMEM` / `EAGAIN`). -/
  | resourceExhausted (errno : UInt32) (detail : String)
  /-- Generic numeric OS error. -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic fallback error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Stage-1 pure Lean decision on a raw HTTP request head prior to any DNS resolution. -/
inductive HeadDecision where
  /-- Request is a valid `CONNECT` matching `allowedTargets`; use `literalIp?` directly or resolve `host` via `getaddrinfo`. -/
  | needResolve (host : String) (port : UInt16) (literalIp? : Option IpAddr)
  /-- Request is refused before DNS resolution (`403 Forbidden`). -/
  | deny (host : Option String) (port : Option UInt16) (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Stage-2 pure Lean decision over resolved `IpAddr`s selecting the exact verified IP(s) to dial. -/
inductive ResolveDecision where
  /-- Dial `primaryIp` (falling back only within `fallbackIps`) directly by `sockaddr` without re-resolving DNS. -/
  | dial (primaryIp : IpAddr) (fallbackIps : Array IpAddr)
  /-- All candidate `IpAddr`s were rejected by `IpPolicy` (`403 Forbidden`). -/
  | deny (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Minimal callback-driven internal bridge for `LeanSwe.ConnectProxy`, keeping all parsing and IP policy in pure Lean. -/
structure RawConnectProxyOpsM (m : Type → Type) where
  /-- Normalize a raw OS socket/listener error into a `ProxyError` with a non-empty message. -/
  mapRawError : ConnectProxyRawError → ProxyError
  /-- Bind `127.0.0.1` (`vcfg.config.listenPort`) and serve `CONNECT` tunnels gated by pure `onHead` and `onResolved` callbacks. -/
  startProxy :
    ValidProxyConfig →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    m (Except ProxyError RunningProxy)
  /-- Stop accepting connections, close all active tunnels, join worker state, and return all recorded `ConnectEvent`s. -/
  stopProxy : RunningProxy → m (Except ProxyError (Array ConnectEvent))
  /-- Return the number of currently active (started and not yet stopped) proxy instances. -/
  activeProxyCount : m Nat

/-- Concrete `IO` internal bridge bundle for `LeanSwe.ConnectProxy`. -/
abbrev RawConnectProxyOps := RawConnectProxyOpsM IO

/-- Minimal monadic capability bundle for scoped `withProxy` execution after pure configuration validation. -/
structure ScopedProxyOpsM (m : Type → Type) where
  /-- Execute `action` against a started `RunningProxy` for a pre-validated `ValidProxyConfig`, returning `(val, events)`. -/
  withProxy :
    {α : Type} →
    ValidProxyConfig →
    (RunningProxy → m (Except ProxyError α)) →
    m (Except ProxyError (α × Array ConnectEvent))

end LeanSwe.ConnectProxy

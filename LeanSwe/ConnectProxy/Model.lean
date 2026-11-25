import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model.IpAndHost

namespace LeanSwe.ConnectProxy.Model

open LeanSwe.ConnectProxy

export LeanSwe.ConnectProxy
  (ConnectProxyRawError HeadDecision ResolveDecision RawConnectProxyOpsM RawConnectProxyOps)


/-- Split authority `cs` at its final `':'` into `(hostChars, portChars)`. -/
def splitLastColonAux (cur : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | ':' :: rest =>
    match splitLastColonAux (':' :: cur) rest with
    | some res => some res
    | none => some (cur.reverse, rest)
  | c :: rest => splitLastColonAux (c :: cur) rest

/-- Return `true` iff byte `b` is a valid RFC 9110 HTTP token character (`tchar`). -/
def isHttpTchar (b : UInt8) : Bool :=
  let n := b.toNat
  (0x30 ≤ n && n ≤ 0x39) ||
  (0x41 ≤ n && n ≤ 0x5a) ||
  (0x61 ≤ n && n ≤ 0x7a) ||
  n == 0x21 || n == 0x23 || n == 0x24 || n == 0x25 || n == 0x26 ||
  n == 0x27 || n == 0x2a || n == 0x2b || n == 0x2d || n == 0x2e ||
  n == 0x5e || n == 0x5f || n == 0x60 || n == 0x7c || n == 0x7e

/-- Return `true` iff byte `b` is allowed inside an HTTP header field value (HTAB, SP, VCHAR, or `obs-text`, no CTLs). -/
def isValidHeaderValByte (b : UInt8) : Bool :=
  let n := b.toNat
  n == 0x09 || (0x20 ≤ n && n ≤ 0x7e) || (0x80 ≤ n && n ≤ 0xff)

/-- Trim leading and trailing HTTP optional whitespace (`' '` and `'\t'`). -/
def trimOwsBytes (bs : List UInt8) : List UInt8 :=
  let isOws (b : UInt8) : Bool := b == 0x20 || b == 0x09
  (bs.dropWhile isOws).reverse.dropWhile isOws |>.reverse

/-- Split a `\r\n`-terminated byte stream into lines, rejecting bare `\r`, bare `\n`, and early empty lines before the final `\r\n\r\n`. -/
def splitCrlfHeaderLinesAux (cur : List UInt8) : List UInt8 → Option (List (List UInt8))
  | [] => none
  | [0x0d, 0x0a] =>
    if cur.isEmpty then some [] else none
  | 0x0d :: 0x0a :: rest =>
    if cur.isEmpty then
      none
    else
      (splitCrlfHeaderLinesAux [] rest).map (cur.reverse :: ·)
  | 0x0d :: _ => none
  | 0x0a :: _ => none
  | 0x00 :: _ => none
  | b :: rest => splitCrlfHeaderLinesAux (b :: cur) rest

/-- Validate a single HTTP header line (`Name: Value`), rejecting `obs-fold`, whitespace before `':'`, `Transfer-Encoding`, and non-zero `Content-Length`. -/
def validateConnectHeaderLine (line : List UInt8) : Bool :=
  match line with
  | [] => false
  | first :: _ =>
    if first == 0x20 || first == 0x09 then
      false
    else
      let nameBytes := line.takeWhile (· != 0x3a)
      let afterName := line.dropWhile (· != 0x3a)
      match afterName with
      | [] => false
      | _ :: valBytes =>
        !nameBytes.isEmpty &&
        nameBytes.all isHttpTchar &&
        valBytes.all isValidHeaderValByte &&
        (let lowerName := String.ofList (nameBytes.map (fun b => toAsciiLowerChar (Char.ofNat b.toNat)))
         let trimmedVal := trimOwsBytes valBytes
         lowerName != "transfer-encoding" &&
         (lowerName != "content-length" || trimmedVal == [0x30]))

/-- Parse an HTTP/1.x `CONNECT <authority> HTTP/1.<0|1>\r\n...headers...\r\n\r\n` head into a canonical `TargetRule`. -/
def parseConnectRequest (raw : ByteArray) : Except ProxyError TargetRule :=
  match splitCrlfHeaderLinesAux [] raw.data.toList with
  | none =>
    .error { kind := .invalidInput, message := "malformed HTTP request framing (expected CRLF-delimited head ending in CRLFCRLF)" }
  | some [] =>
    .error { kind := .invalidInput, message := "empty HTTP request line" }
  | some (reqLineBytes :: headerLines) =>
    if !reqLineBytes.all (fun b => 0x20 ≤ b.toNat && b.toNat ≤ 0x7e) then
      .error { kind := .invalidInput, message := "invalid non-ASCII or control byte in HTTP request line" }
    else if !headerLines.all validateConnectHeaderLine then
      .error { kind := .invalidInput, message := "invalid or disallowed HTTP header field in CONNECT request" }
    else
      let reqChars := reqLineBytes.map (fun b => Char.ofNat b.toNat)
      match splitOnChar ' ' reqChars with
      | [methodCs, authorityCs, versionCs] =>
        let method := String.ofList methodCs
        let version := String.ofList versionCs
        if method != "CONNECT" then
          .error { kind := .invalidInput, message := s!"unsupported HTTP method '{method}' (only CONNECT is permitted)" }
        else if version != "HTTP/1.1" && version != "HTTP/1.0" then
          .error { kind := .invalidInput, message := s!"unsupported HTTP version '{version}'" }
        else if authorityCs.contains '/' || authorityCs.contains '?' || authorityCs.contains '#' || authorityCs.contains '@' then
          .error { kind := .invalidInput, message := "CONNECT authority must be host:port without scheme, path, query, or userinfo" }
        else
          match splitLastColonAux [] authorityCs with
          | none =>
            .error { kind := .invalidInput, message := "CONNECT authority missing ':port'" }
          | some (hostCs, portCs) =>
            match parseDecNoLeadingZero portCs 5 with
            | none =>
              .error { kind := .invalidInput, message := "invalid port in CONNECT authority" }
            | some portNat =>
              if portNat == 0 || portNat > 65535 then
                .error { kind := .invalidInput, message := s!"CONNECT port {portNat} out of range 1..65535" }
              else
                match normalizeTargetHost (String.ofList hostCs) with
                | .ok (normHost, _) => .ok { host := normHost, port := UInt16.ofNat portNat }
                | .error e => .error e
      | _ =>
        .error { kind := .invalidInput, message := "malformed HTTP request line" }

/-- Validate all entries of a list with `f`, preserving order. -/
def mapExceptList {α β : Type} (f : α → Except ProxyError β) : List α → Except ProxyError (List β)
  | [] => .ok []
  | x :: xs => do
    let y ← f x
    let ys ← mapExceptList f xs
    .ok (y :: ys)

/-- Validate and normalize a `ProxyConfig` into a `ValidProxyConfig`. -/
def validateConfig (cfg : ProxyConfig) : Except ProxyError ValidProxyConfig := do
  if cfg.limits.maxHeaderBytes == 0 then
    .error { kind := .invalidInput, message := "ProxyLimits.maxHeaderBytes must be greater than 0" }
  else if cfg.limits.headerTimeoutMs == 0 then
    .error { kind := .invalidInput, message := "ProxyLimits.headerTimeoutMs must be greater than 0" }
  else if cfg.limits.connectTimeoutMs == 0 then
    .error { kind := .invalidInput, message := "ProxyLimits.connectTimeoutMs must be greater than 0" }
  else if cfg.limits.maxConcurrentTunnels == 0 then
    .error { kind := .invalidInput, message := "ProxyLimits.maxConcurrentTunnels must be greater than 0" }
  else if !cfg.ipPolicy.extraAllows.toList.all isValidIpPrefix then
    .error { kind := .invalidInput, message := "IpPolicy.extraAllows contains an out-of-range CIDR prefixLen" }
  else if !cfg.ipPolicy.extraBans.toList.all isValidIpPrefix then
    .error { kind := .invalidInput, message := "IpPolicy.extraBans contains an out-of-range CIDR prefixLen" }
  else do
    let normTargets ← mapExceptList normalizeTargetRule cfg.allowedTargets.toList
    .ok { config := { cfg with allowedTargets := normTargets.toArray } }

/-- Return `true` iff canonical `target` equals the normalization of at least one valid entry in `rules`. -/
def matchesAllowedTarget (rules : Array TargetRule) (target : TargetRule) : Bool :=
  rules.toList.any fun r =>
    match normalizeTargetRule r with
    | .ok norm => norm == target
    | .error _ => false

/-- Stage-1 pure head gate: enforce `maxHeaderBytes`, parse `CONNECT`, and verify exact `allowedTargets` membership before DNS. -/
def decideConnectHead (cfg : ProxyConfig) (head : ByteArray) : HeadDecision :=
  if head.size > cfg.limits.maxHeaderBytes then
    .deny none none "request head exceeds maxHeaderBytes"
  else
    match parseConnectRequest head with
    | .error err =>
      .deny none none err.message
    | .ok target =>
      if matchesAllowedTarget cfg.allowedTargets target then
        .needResolve target.host target.port (literalIpOfHost? target.host)
      else
        .deny (some target.host) (some target.port) "target (host, port) not in allowedTargets"

/-- Stage-2 pure IP gate: filter candidate `ips` through `allowsIp policy` and select the verified `IpAddr`(s) to dial. -/
def decideResolvedIps (policy : IpPolicy) (_host : String) (_port : UInt16) (ips : Array IpAddr) : ResolveDecision :=
  match ips.toList.filter (allowsIp policy) with
  | [] => .deny "no resolved IP address permitted by IpPolicy"
  | primary :: rest => .dial primary rest.toArray

/-- Verified upstream dial plan produced by `authorizeConnect`. -/
structure DialPlan where
  /-- Normalized target host recorded for audit logging only (never re-resolved at dial time). -/
  host : String
  /-- Verified destination TCP port (`1..65535`). -/
  port : UInt16
  /-- Primary verified `IpAddr` selected to dial directly via `sockaddr_in` / `sockaddr_in6`. -/
  primaryIp : IpAddr
  /-- Remaining verified `IpAddr`s (all satisfying `allowsIp`) in resolver order. -/
  fallbackIps : Array IpAddr := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure end-to-end authorization decision for a single `CONNECT` request head. -/
inductive ConnectAuthResult where
  /-- Authorized: dial `plan.primaryIp` (falling back only within `plan.fallbackIps`) at `plan.port`. -/
  | dial (plan : DialPlan)
  /-- Denied by method/framing, `allowedTargets`, or `IpPolicy` (`403 Forbidden`). -/
  | deny (host : Option String) (port : Option UInt16) (reason : String)
  /-- Target allowed by `allowedTargets`, but host DNS resolution failed (`502 Bad Gateway`). -/
  | dnsFailed (host : String) (port : UInt16) (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Authorize an incoming HTTP head in two phases, calling `resolveHost` only when target admission allows a non-literal domain. -/
def authorizeConnect
    (cfg : ProxyConfig)
    (head : ByteArray)
    (resolveHost : String → Except String (Array IpAddr)) : ConnectAuthResult :=
  match decideConnectHead cfg head with
  | .deny host? port? reason => .deny host? port? reason
  | .needResolve host port (some litIp) =>
    match decideResolvedIps cfg.ipPolicy host port #[litIp] with
    | .deny reason => .deny (some host) (some port) reason
    | .dial primary fallbacks =>
      .dial { host := host, port := port, primaryIp := primary, fallbackIps := fallbacks }
  | .needResolve host port none =>
    match resolveHost host with
    | .error dnsErr =>
      .dnsFailed host port (if dnsErr.isEmpty then "dns resolution failed" else dnsErr)
    | .ok resolved =>
      match decideResolvedIps cfg.ipPolicy host port resolved with
      | .deny reason => .deny (some host) (some port) reason
      | .dial primary fallbacks =>
        .dial { host := host, port := port, primaryIp := primary, fallbackIps := fallbacks }

/-- Map a `ConnectAuthResult` and optional upstream TCP `connect()` error into its exact single `ConnectEvent`. -/
def eventOfAuthResult (auth : ConnectAuthResult) (connectErr? : Option String := none) : ConnectEvent :=
  match auth with
  | .deny host? port? reason =>
    { host := host?, port := port?, outcome := .denied, reason := some reason }
  | .dnsFailed host port reason =>
    { host := some host, port := some port, outcome := .failed, reason := some reason }
  | .dial plan =>
    match connectErr? with
    | none =>
      { host := some plan.host, port := some plan.port, outcome := .allowed, reason := none }
    | some connErr =>
      let msg := if connErr.isEmpty then "upstream connect failed" else connErr
      { host := some plan.host, port := some plan.port, outcome := .failed, reason := some msg }

/-- Frozen security theorem statement: any `ban ∈ policy.extraBans` matching `ip` unconditionally overrides `base` and `extraAllows`. -/
def SpecBanOverridesAllow : Prop :=
  ∀ (policy : IpPolicy) (ip : IpAddr) (ban : IpPrefix),
    ban ∈ policy.extraBans.toList →
    prefixContains ban ip = true →
    allowsIp policy ip = false

/-- Frozen security theorem statement: wrapping a banned IPv4 address inside IPv6 (`::ffff:0:0/96`, `::/96` `v4 > 1`, `::ffff:0:0:0/96`, `64:ff9b::/96`, `64:ff9b:1::/48` `/96`+`/48`+`/56`+`/64`, `2002::/16`, `2001::/32` Teredo server/client) never bypasses `extraBans`. -/
def SpecIpv4InIpv6NeverBypassesBan : Prop :=
  (∀ (policy : IpPolicy) (ip : IpAddr) (v4 : IpAddr) (ban : IpPrefix),
    v4 ∈ embeddedIpv4Addrs ip →
    ban ∈ policy.extraBans.toList →
    prefixContains ban v4 = true →
    allowsIp policy ip = false) ∧
  (∀ (v4 : UInt32) (sub8 : UInt8) (subHi sla : UInt16) (subLo otherV4 flagsPort suffix32 suffix24 : UInt32)
     (iface suffix40 : UInt64),
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkIpv4MappedIpv6 v4) ∧
    (v4 > 1 → IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkIpv4CompatibleIpv6 v4)) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkSiitIpv6 v4) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkNat64WellKnownIpv6 v4) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkNat64LocalIpv6 v4 subHi subLo) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkNat64Local48Ipv6 v4 suffix40) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkNat64Local56Ipv6 sub8 v4 suffix32) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkNat64Local64Ipv6 subHi v4 suffix24) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mk6to4Ipv6 v4 sla iface) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkTeredoIpv6 v4 flagsPort otherV4) ∧
    IpAddr.v4 v4 ∈ embeddedIpv4Addrs (mkTeredoIpv6 otherV4 flagsPort v4))

/-- Frozen security theorem statement: `authorizeConnect` dials only when the request is a bounded valid `CONNECT` matching `allowedTargets`, and every dialed `IpAddr` comes from the literal/resolved IP snapshot and satisfies `allowsIp`. -/
def SpecOnlyAllowedTargetAndVerifiedIpDialed : Prop :=
  ∀ (cfg : ProxyConfig) (head : ByteArray)
    (resolveHost : String → Except String (Array IpAddr)) (plan : DialPlan),
    authorizeConnect cfg head resolveHost = .dial plan →
    head.size ≤ cfg.limits.maxHeaderBytes ∧
    parseConnectRequest head = .ok { host := plan.host, port := plan.port } ∧
    matchesAllowedTarget cfg.allowedTargets { host := plan.host, port := plan.port } = true ∧
    allowsIp cfg.ipPolicy plan.primaryIp = true ∧
    (∀ ip, ip ∈ plan.fallbackIps.toList → allowsIp cfg.ipPolicy ip = true) ∧
    (match literalIpOfHost? plan.host with
     | some litIp => plan.primaryIp = litIp ∧ plan.fallbackIps = #[]
     | none =>
       ∃ resolved, resolveHost plan.host = .ok resolved ∧
         plan.primaryIp ∈ resolved.toList ∧
         ∀ ip, ip ∈ plan.fallbackIps.toList → ip ∈ resolved.toList)

/-- Simulated DNS lookup result for a hostname in `MockProxySimState`. -/
inductive DnsSimResult where
  /-- Hostname resolved to `ips`. -/
  | resolved (ips : Array IpAddr)
  /-- Hostname lookup failed with `reason`. -/
  | failed (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Scripted client connection scenario for deterministic `RawConnectProxyOpsM` simulation. -/
inductive SimulatedClientAttempt where
  /-- Client sends `head` before proxy stop; `connectErr? = none` simulates TCP `connect()` success, `some msg` simulates failure. -/
  | completedHead (head : ByteArray) (connectErr? : Option String := none)
  /-- Client connection is still mid-handshake or mid-dial when `stopProxy` is called. -/
  | inFlightAtStop (host : Option String := none) (port : Option UInt16 := none)
  deriving BEq, DecidableEq, Inhabited

/-- Pure state for deterministic simulation of `RawConnectProxyOpsM` and `withProxy` lifecycle specs. -/
structure MockProxySimState where
  /-- Currently active (started and not yet stopped) proxy handle IDs. -/
  activeHandles : List Nat := []
  /-- Next fresh handle ID counter. -/
  nextHandleId : Nat := 1
  /-- Ephemeral port assigned when `listenPort = 0` (`49152` used if `0`). -/
  ephemeralPort : UInt16 := 49152
  /-- Simulated `getaddrinfo` lookup table (`host -> DnsSimResult`). -/
  dnsTable : List (String × DnsSimResult) := []
  /-- Verified upstream `IpAddr`s whose simulated TCP `connect()` fails before trying fallback IPs. -/
  failConnectIps : List IpAddr := []
  /-- Scripted client connection attempts processed while a proxy instance runs. -/
  scriptedAttempts : Array SimulatedClientAttempt := #[]
  /-- Optional injected error returned by `startProxy`. -/
  failStartWith : Option ProxyError := none
  /-- Optional injected error returned by `stopProxy` after releasing the handle. -/
  failStopWith : Option ProxyError := none
  /-- Count of `startProxy` invocations. -/
  startCalls : Nat := 0
  /-- Count of `stopProxy` invocations. -/
  stopCalls : Nat := 0
  /-- Hostnames passed to simulated DNS resolution in order. -/
  dnsQueries : Array String := #[]
  /-- Exact `(verifiedIp, port)` pairs dialed upstream in order. -/
  dialedEndpoints : Array (IpAddr × UInt16) := #[]
  /-- Recorded `ConnectEvent` batch from the most recently stopped proxy. -/
  lastStoppedEvents : Array ConnectEvent := #[]
  deriving BEq, DecidableEq, Inhabited

/-- Normalize a `ConnectProxyRawError` into a `ProxyError` with a guaranteed non-empty message. -/
def mapRawErrorPure : ConnectProxyRawError → ProxyError
  | .invalidArgument errno? detail =>
    { kind := .invalidInput
      errnoCode := errno?
      message := if detail.isEmpty then "invalid connect-proxy argument" else detail }
  | .addressInUse port errno detail =>
    { kind := .addressInUse
      errnoCode := some errno
      message := if detail.isEmpty then s!"127.0.0.1:{port} is already in use" else detail }
  | .permissionDenied errno detail =>
    { kind := .permissionDenied
      errnoCode := some errno
      message := if detail.isEmpty then "permission denied binding 127.0.0.1 socket" else detail }
  | .resourceExhausted errno detail =>
    { kind := .resourceExhausted
      errnoCode := some errno
      message := if detail.isEmpty then "proxy socket or thread resource limit exhausted" else detail }
  | .otherError errno detail =>
    { kind := .ioError
      errnoCode := some errno
      message := if detail.isEmpty then s!"connect-proxy OS error (errno {errno})" else detail }
  | .userError detail =>
    { kind := .ioError
      errnoCode := none
      message := if detail.isEmpty then "connect-proxy I/O error" else detail }

/-- Step sequentially across verified candidate `IpAddr`s (`primaryIp :: fallbackIps`), recording each attempted `(ip, port)` and stopping on the first candidate not in `failConnectIps`. -/
def stepDialCandidates
    (failConnectIps : List IpAddr)
    (port : UInt16)
    (connectErr? : Option String) :
    List IpAddr → Array (IpAddr × UInt16) → Option String × Array (IpAddr × UInt16)
  | [], dialed =>
    let msg :=
      match connectErr? with
      | some cerr => if cerr.isEmpty then "upstream connect failed" else cerr
      | none => "all verified upstream IPs failed connect"
    (some msg, dialed)
  | ip :: rest, dialed =>
    let dialed' := dialed.push (ip, port)
    if failConnectIps.contains ip then
      stepDialCandidates failConnectIps port connectErr? rest dialed'
    else
      match connectErr? with
      | none => (none, dialed')
      | some cerr =>
        let msg := if cerr.isEmpty then "upstream connect failed" else cerr
        (some msg, dialed')

/-- Simulate one `SimulatedClientAttempt` using the pure `onHead` and `onResolved` callbacks supplied to `startProxy`. -/
def stepSimulatedAttempt
    (dnsTable : List (String × DnsSimResult))
    (failConnectIps : List IpAddr)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (attempt : SimulatedClientAttempt)
    (dnsQueries : Array String)
    (dialed : Array (IpAddr × UInt16)) :
    ConnectEvent × Array String × Array (IpAddr × UInt16) :=
  match attempt with
  | .inFlightAtStop host? port? =>
    ({ host := host?, port := port?, outcome := .failed, reason := some "proxy stopped" }, dnsQueries, dialed)
  | .completedHead head connectErr? =>
    match onHead head with
    | .deny host? port? reason =>
      ({ host := host?, port := port?, outcome := .denied, reason := some reason }, dnsQueries, dialed)
    | .needResolve host port (some litIp) =>
      match onResolved host port #[litIp] with
      | .deny reason =>
        ({ host := some host, port := some port, outcome := .denied, reason := some reason }, dnsQueries, dialed)
      | .dial primaryIp fallbackIps =>
        let (dialErr?, dialed') :=
          stepDialCandidates failConnectIps port connectErr? (primaryIp :: fallbackIps.toList) dialed
        match dialErr? with
        | none =>
          ({ host := some host, port := some port, outcome := .allowed, reason := none }, dnsQueries, dialed')
        | some msg =>
          ({ host := some host, port := some port, outcome := .failed, reason := some msg }, dnsQueries, dialed')
    | .needResolve host port none =>
      let dnsQueries' := dnsQueries.push host
      let dnsRes :=
        match dnsTable.find? (fun p => p.1 == host) with
        | some (_, res) => res
        | none => .failed "name not found"
      match dnsRes with
      | .failed derr =>
        let msg := if derr.isEmpty then "dns resolution failed" else derr
        ({ host := some host, port := some port, outcome := .failed, reason := some msg }, dnsQueries', dialed)
      | .resolved ips =>
        match onResolved host port ips with
        | .deny reason =>
          ({ host := some host, port := some port, outcome := .denied, reason := some reason }, dnsQueries', dialed)
        | .dial primaryIp fallbackIps =>
          let (dialErr?, dialed') :=
            stepDialCandidates failConnectIps port connectErr? (primaryIp :: fallbackIps.toList) dialed
          match dialErr? with
          | none =>
            ({ host := some host, port := some port, outcome := .allowed, reason := none }, dnsQueries', dialed')
          | some msg =>
            ({ host := some host, port := some port, outcome := .failed, reason := some msg }, dnsQueries', dialed')

/-- Fold `stepSimulatedAttempt` over a list of `SimulatedClientAttempt`s in order. -/
def runSimulatedAttempts
    (dnsTable : List (String × DnsSimResult))
    (failConnectIps : List IpAddr)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision) :
    List SimulatedClientAttempt → Array ConnectEvent → Array String → Array (IpAddr × UInt16) →
    Array ConnectEvent × Array String × Array (IpAddr × UInt16)
  | [], evs, qs, ds => (evs, qs, ds)
  | a :: rest, evs, qs, ds =>
    let (ev, qs', ds') := stepSimulatedAttempt dnsTable failConnectIps onHead onResolved a qs ds
    runSimulatedAttempts dnsTable failConnectIps onHead onResolved rest (evs.push ev) qs' ds'

/-- Pure `RawConnectProxyOpsM (StateM MockProxySimState)` simulation adapter for spec and proof verification. -/
def mockRawProxyOps : RawConnectProxyOpsM (StateM MockProxySimState) :=
  { mapRawError := mapRawErrorPure
    startProxy := fun vcfg onHead onResolved s =>
      let lim := vcfg.config.limits
      if lim.maxHeaderBytes == 0 || lim.headerTimeoutMs == 0 ||
         lim.connectTimeoutMs == 0 || lim.maxConcurrentTunnels == 0 then
        (.error (mapRawErrorPure (.invalidArgument none "proxy limits must be positive")), s)
      else
        let sCount := { s with startCalls := s.startCalls + 1 }
        match s.failStartWith with
        | some err => (.error err, sCount)
        | none =>
          let hid := Nat.max s.nextHandleId ((s.activeHandles.foldl Nat.max 0) + 1)
          let boundPort : UInt16 :=
            if vcfg.config.listenPort == 0 then
              if s.ephemeralPort == 0 then 49152 else s.ephemeralPort
            else
              vcfg.config.listenPort
          let (evs, qs', ds') :=
            runSimulatedAttempts s.dnsTable s.failConnectIps onHead onResolved
              s.scriptedAttempts.toList #[] s.dnsQueries s.dialedEndpoints
          let s' :=
            { sCount with
              activeHandles := hid :: s.activeHandles
              nextHandleId := hid + 1
              dnsQueries := qs'
              dialedEndpoints := ds'
              lastStoppedEvents := evs }
          (.ok { handleId := hid, port := boundPort }, s')
    stopProxy := fun proxy s =>
      let sCount := { s with stopCalls := s.stopCalls + 1 }
      if !s.activeHandles.contains proxy.handleId then
        (.error (mapRawErrorPure (.invalidArgument none "proxy handle is not active")), sCount)
      else
        let sClean := { sCount with activeHandles := s.activeHandles.filter (· != proxy.handleId) }
        match s.failStopWith with
        | some err => (.error err, sClean)
        | none => (.ok s.lastStoppedEvents, sClean)
    activeProxyCount := fun s => (s.activeHandles.length, s) }

/-- Start, run `action`, and guarantee `stopProxy` teardown via `[MonadFinally m]` for an already-validated `ValidProxyConfig`. -/
def withValidProxyModel {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawConnectProxyOpsM m)
    (vcfg : ValidProxyConfig)
    (action : RunningProxy → m (Except ProxyError α)) :
    m (Except ProxyError (α × Array ConnectEvent)) := do
  let onHead := decideConnectHead vcfg.config
  let onResolved := decideResolvedIps vcfg.config.ipPolicy
  match ← ops.startProxy vcfg onHead onResolved with
  | .error err => return .error err
  | .ok proxy =>
    let (actRes, stopRes) ← tryFinally' (action proxy) (fun _ => ops.stopProxy proxy)
    match actRes, stopRes with
    | .error ae, _ => return .error ae
    | .ok _, .error se => return .error se
    | .ok a, .ok evs => return .ok (a, evs)

/-- Validate `cfg`, then run `withValidProxyModel ops vcfg action`. -/
def withProxyModel {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (ops : RawConnectProxyOpsM m)
    (cfg : ProxyConfig)
    (action : RunningProxy → m (Except ProxyError α)) :
    m (Except ProxyError (α × Array ConnectEvent)) := do
  match validateConfig cfg with
  | .error err => return .error err
  | .ok vcfg => withValidProxyModel ops vcfg action

/-- Lift `mockRawProxyOps` into `ExceptT String (StateM MockProxySimState)` for `MonadFinally` exception/cancellation specs. -/
def mockRawProxyOpsEx : RawConnectProxyOpsM (ExceptT String (StateM MockProxySimState)) :=
  { mapRawError := mockRawProxyOps.mapRawError
    startProxy := fun vcfg onHead onResolved =>
      ExceptT.mk (fun s =>
        let (r, s') := (mockRawProxyOps.startProxy vcfg onHead onResolved).run s
        (.ok r, s'))
    stopProxy := fun proxy =>
      ExceptT.mk (fun s =>
        let (r, s') := (mockRawProxyOps.stopProxy proxy).run s
        (.ok r, s'))
    activeProxyCount :=
      ExceptT.mk (fun s =>
        let (n, s') := mockRawProxyOps.activeProxyCount.run s
        (.ok n, s')) }

/-- Single-step `withProxy` request input for `Core.ObeysStepFromConc` capability refinement. -/
structure ProxyStepReq where
  /-- Candidate proxy configuration supplied to `withProxy`. -/
  cfg : ProxyConfig := {}
  /-- Caller callback port offset returned alongside recorded `ConnectEvent`s. -/
  tag : UInt16 := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pre-validated `withProxy` step input pairing a `ValidProxyConfig` with a port offset tag. -/
structure ProxyRawStepReq where
  /-- Validated proxy configuration supplied to `withProxy`. -/
  vcfg : ValidProxyConfig := { config := {} }
  /-- Caller callback port offset returned alongside recorded `ConnectEvent`s. -/
  tag : UInt16 := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Well-formedness guard on `MockProxySimState` requiring a non-zero fallback ephemeral port. -/
def proxyStepWf (s : MockProxySimState) : Bool :=
  decide (s.ephemeralPort != 0)

/-- Execute one scoped `withProxy` step through `ConnectProxyApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : ConnectProxyApiM (StateM W)) (req : ProxyStepReq) :
    StateM W (Except ProxyError (UInt16 × Array ConnectEvent)) :=
  api.withProxy req.cfg (fun p => pure (.ok (p.port + req.tag)))

/-- Relational postcondition for a validated `withProxy` step over `MockProxySimState`. -/
def allowedRawStep (s : MockProxySimState) (req : ProxyRawStepReq)
    (out : Except ProxyError (UInt16 × Array ConnectEvent)) (s' : MockProxySimState) : Prop :=
  s'.ephemeralPort = s.ephemeralPort ∧
  match out with
  | .error err => err.message ≠ ""
  | .ok (val, evs) =>
    ∃ boundPort : UInt16,
      boundPort ≠ 0 ∧
      (req.vcfg.config.listenPort ≠ 0 → boundPort = req.vcfg.config.listenPort) ∧
      val = boundPort + req.tag ∧
      ∀ ev ∈ evs.toList, (ev.outcome = .allowed → ev.reason = none)

/-- Relational postcondition for a `ConnectProxyApiM` `withProxy` step gated by a single `validateConfig`. -/
def allowedPkgStep (s : MockProxySimState) (req : ProxyStepReq)
    (out : Except ProxyError (UInt16 × Array ConnectEvent)) (s' : MockProxySimState) : Prop :=
  match validateConfig req.cfg with
  | .error err => out = .error err ∧ s' = s
  | .ok vcfg => allowedRawStep s { vcfg, tag := req.tag } out s'

end LeanSwe.ConnectProxy.Model

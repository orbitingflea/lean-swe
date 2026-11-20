import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.Dns.Model

namespace LeanSwe.LinuxSyscall.Dns

open Core (NondetTest ErrorObligation ErrorJustification ErrorTestMode AssumptionObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `validateHost` rejects empty strings and strings containing `\x00` while accepting loopback literals and `"localhost"`, matching `!h.toList.isEmpty && !h.toList.any (· == '\x00')`. -/
def test_dns_validateHost_semantics
    {runner} [NondetTest runner]
    (fn : String → Bool := validateHost) : runner Unit := do
  let h ← nondet String
  NondetTest.assert (fn "" = false)
  NondetTest.assert (fn "a\x00b" = false)
  NondetTest.assert (fn "127.0.0.1" = true)
  NondetTest.assert (fn "::1" = true)
  NondetTest.assert (fn "localhost" = true)
  NondetTest.assert (fn h = (!h.toList.isEmpty && !h.toList.any (· == '\x00')))

/-- Pure `DnsAddr` accessors, `isLoopback`, `addrMatchesHints`, and `format` preserve `scopeId`, unscoped checks, byte extraction, family filters, and `%<scopeId>` rendering. -/
def test_dns_addrHelpers_semantics
    {runner} [NondetTest runner]
    (fmt : DnsAddr → String := DnsAddr.format)
    (isLoop : DnsAddr → Bool := DnsAddr.isLoopback) : runner Unit := do
  let a4 := DnsAddr.ipv4 127 0 0 1
  let a4Other := DnsAddr.ipv4 8 8 8 8
  let a6u := DnsAddr.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
  let a6lScoped := DnsAddr.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7
  let a6s := DnsAddr.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7
  NondetTest.assert (a4.isUnscoped = true)
  NondetTest.assert (a6u.isUnscoped = true)
  NondetTest.assert (a6s.isUnscoped = false)
  NondetTest.assert (a4.scopeId = 0)
  NondetTest.assert (a6s.scopeId = 7)
  NondetTest.assert (a4.ipv4Bytes? = some (127, 0, 0, 1))
  NondetTest.assert (a6u.ipv4Bytes? = none)
  NondetTest.assert (a4.ipv6Bytes? = none)
  NondetTest.assert (a6s.ipv6Bytes? =
    some (ByteArray.mk #[0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 7))
  NondetTest.assert (isLoop a4 = true)
  NondetTest.assert (isLoop (.ipv4 127 255 0 9) = true)
  NondetTest.assert (isLoop a4Other = false)
  NondetTest.assert (isLoop a6u = true)
  NondetTest.assert (isLoop a6lScoped = false)
  NondetTest.assert (isLoop a6s = false)
  NondetTest.assert (addrMatchesHints { family := .ipv4 } a4 = true)
  NondetTest.assert (addrMatchesHints { family := .ipv6 } a4 = false)
  NondetTest.assert (fmt a4 = "127.0.0.1")
  NondetTest.assert (fmt a6u = "0000:0000:0000:0000:0000:0000:0000:0001")
  NondetTest.assert (fmt a6s = "fe80:0000:0000:0000:0000:0000:0000:0001%7")

/-- Linux `<netdb.h>` `EAI_*` constants match their C ABI values and `classifyGaiKind` maps codes into semantic buckets without ever emitting `.invalidHost`. -/
def test_dns_classifyGaiKind_semantics
    {runner} [NondetTest runner]
    (cls : Int32 → DnsErrorKind := classifyGaiKind) : runner Unit := do
  let rc ← nondet Int32
  NondetTest.assert (EAI_BADFLAGS = -1)
  NondetTest.assert (EAI_NONAME = -2)
  NondetTest.assert (EAI_AGAIN = -3)
  NondetTest.assert (EAI_FAIL = -4)
  NondetTest.assert (EAI_NODATA = -5)
  NondetTest.assert (EAI_FAMILY = -6)
  NondetTest.assert (EAI_SOCKTYPE = -7)
  NondetTest.assert (EAI_SERVICE = -8)
  NondetTest.assert (EAI_ADDRFAMILY = -9)
  NondetTest.assert (EAI_MEMORY = -10)
  NondetTest.assert (EAI_SYSTEM = -11)
  NondetTest.assert (EAI_OVERFLOW = -12)
  NondetTest.assert (cls EAI_NONAME = .nameNotFound)
  NondetTest.assert (cls EAI_NODATA = .nameNotFound)
  NondetTest.assert (cls EAI_FAIL = .nameNotFound)
  NondetTest.assert (cls EAI_AGAIN = .temporaryFailure)
  NondetTest.assert (cls EAI_SYSTEM = .systemError)
  NondetTest.assert (cls EAI_MEMORY = .systemError)
  NondetTest.assert (cls EAI_ADDRFAMILY = .otherGai)
  NondetTest.assert (cls EAI_BADFLAGS = .otherGai)
  NondetTest.assert (cls rc != .invalidHost)

/-- `AddrFamilyHint.toWire` and `SockTypeHint.toWire` map hints to `(0, 1, 2)` injectively. -/
def test_dns_wireTags_semantics
    {runner} [NondetTest runner]
    (famToWire : AddrFamilyHint → UInt8 := AddrFamilyHint.toWire)
    (sockToWire : SockTypeHint → UInt8 := SockTypeHint.toWire) : runner Unit := do
  let f1 ← nondet AddrFamilyHint
  let f2 ← nondet AddrFamilyHint
  let s1 ← nondet SockTypeHint
  let s2 ← nondet SockTypeHint
  NondetTest.assert (famToWire .any = 0)
  NondetTest.assert (famToWire .ipv4 = 1)
  NondetTest.assert (famToWire .ipv6 = 2)
  NondetTest.assert (sockToWire .any = 0)
  NondetTest.assert (sockToWire .stream = 1)
  NondetTest.assert (sockToWire .dgram = 2)
  NondetTest.assert ((famToWire f1 == famToWire f2) = (f1 == f2))
  NondetTest.assert ((sockToWire s1 == sockToWire s2) = (s1 == s2))
  NondetTest.assert (({} : ResolveHints) = { family := .any, sockType := .stream })

/-- Every resolution executed by `modelOps` against any `DnsOracle`, hostname, and `ResolveHints` is accepted by `allowedDnsOutcome`, which enforces `Errno.EFAULT` exclusion, `isValidGaiCode`, numeric-literal matching, `::ffff:a.b.c.d` unwrapping, scoped-zone rules, and `sockType = .any` multiplicity. -/
def test_dns_modelOps_soundAgainstAllowedOutcome
    {runner} [NondetTest runner]
    (ops : DnsOpsM (StateM DnsOracle) := modelOps) : runner Unit := do
  let oracle ← nondet DnsOracle
  let host ← nondet String
  let hints ← nondet ResolveHints
  let rawOut ← nondet (Except DnsError (List DnsAddr))
  let (res, _) := (ops.getaddrinfo host hints).run oracle
  NondetTest.assert (allowedDnsOutcome host hints res = true)
  NondetTest.assert (allowedDnsOutcome host hints (normalizeOracleOutcome host hints rawOut) = true)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints (.ok []) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" { family := .ipv6 }
    (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0]) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" { family := .ipv4, sockType := .any }
    (.ok [.ipv4 127 0 0 1]) = false)
  NondetTest.assert (allowedDnsOutcome "localhost" { family := .ipv4, sockType := .any }
    (.ok [.ipv4 127 0 0 1]) = false)
  NondetTest.assert (allowedDnsOutcome "::1%lo" { family := .any, sockType := .stream }
    (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1]) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := EAI_NONAME, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := some Errno.EINVAL, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EFAULT, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := 42, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := -13, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := -42, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := Int32.minValue, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := EAI_BADFLAGS, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" hints
    (.error { kind := .otherGai, gaiCode := EAI_SERVICE, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "127.0.0.1" { family := .ipv6, sockType := .stream }
    (.error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "fe80::1%" { family := .ipv4, sockType := .stream }
    (.error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "x" }) = false)
  NondetTest.assert (allowedDnsOutcome "bad host" { family := .any, sockType := .stream }
    (.error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none, message := "x" }) = false)
  NondetTest.assert (((ops.getaddrinfo "::ffff:127.0.0.1" { family := .ipv4, sockType := .stream }).run defaultOfflineOracle).1
    = .ok [.ipv4 127 0 0 1])
  NondetTest.assert (((ops.getaddrinfo "localhost" { family := .any, sockType := .stream }).run defaultOfflineOracle).1
    = .ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0, .ipv4 127 0 0 1])
  NondetTest.assert (((ops.getaddrinfo "localhost" { family := .ipv4, sockType := .any }).run defaultOfflineOracle).1
    = .ok [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])
  NondetTest.assert (((ops.getaddrinfo "127.0.0.1" { family := .ipv4, sockType := .any }).run defaultOfflineOracle).1
    = .ok [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])
  NondetTest.assert (((ops.getaddrinfo "::1%lo" { family := .any, sockType := .stream }).run defaultOfflineOracle).1
    = .error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "Name or service not known" })
  NondetTest.assert (((ops.getaddrinfo "fe80::1%lo" { family := .any, sockType := .stream }).run defaultOfflineOracle).1
    = .ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1])
  NondetTest.assert (((ops.getaddrinfo "fe80::1%" { family := .ipv4, sockType := .stream }).run defaultOfflineOracle).1
    = .error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none, message := "Address family for hostname not supported" })
  NondetTest.assert (((ops.getaddrinfo "::ffff:127.0.0.1%lo" { family := .ipv4, sockType := .stream }).run defaultOfflineOracle).1
    = .error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "Name or service not known" })
  NondetTest.assert (((ops.getaddrinfo "127.0.0.1").run defaultOfflineOracle).1
    = ((ops.getaddrinfo "127.0.0.1" { family := .any, sockType := .stream }).run defaultOfflineOracle).1)
  NondetTest.assert (defaultOfflineOracle.lookup "127.0.0.1" { family := .ipv4, sockType := .any }
    = .ok [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])
  NondetTest.assert (defaultOfflineOracle.lookup "fe80::1%lo" { family := .any, sockType := .any }
    = .ok [ .ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1
          , .ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1
          , .ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 ])
  NondetTest.assert (normalizeOracleOutcome "" hints (.ok [.ipv4 127 0 0 1]) = .error invalidHostError)
  NondetTest.assert (normalizeOracleOutcome "a\x00b" hints (.ok [.ipv4 127 0 0 1]) = .error invalidHostError)
  NondetTest.assert (isNumericHostLiteral "127.0.0.1" = true)
  NondetTest.assert (isNumericHostLiteral "0x7f000001" = true)
  NondetTest.assert (isNumericHostLiteral "::1" = true)
  NondetTest.assert (isNumericHostLiteral "fe80::1%lo" = true)
  NondetTest.assert (isNumericHostLiteral "::ffff:127.0.0.1%lo" = true)
  NondetTest.assert (isNumericHostLiteral "::ffff:127.0.0.1%" = true)
  NondetTest.assert (isNumericHostLiteral "fe80::1%lo\x00" = false)
  NondetTest.assert (isNumericHostLiteral "localhost" = false)
  NondetTest.assert (isNumericHostLiteral "" = false)

/-- Wrapper soundness and pass-through promise over arbitrary raw wire callbacks (`Id`): `mkOps rawFn` always satisfies `allowedDnsOutcome host hints`, forwards `(host, hints.family.toWire, hints.sockType.toWire)` faithfully without dropping valid `.ok` records, and preserves normalized `gaiCode`, `EAI_SYSTEM` `errno?`, and UTF-8/hex diagnostic messages on `.error`. -/
def test_dns_mkRawOps_soundAgainstAllowedOutcome
    {runner} [NondetTest runner]
    (mkOps : (String → UInt8 → UInt8 → Except (Int32 × UInt32 × ByteArray) ByteArray) → DnsOpsM Id) :
    runner Unit := do
  let rawFn ← nondet (String → UInt8 → UInt8 → Except (Int32 × UInt32 × ByteArray) ByteArray)
  let host ← nondet String
  let hints ← nondet ResolveHints
  let expectedAddrs ← nondet (List DnsAddr)
  let ops := mkOps rawFn
  NondetTest.assert (allowedDnsOutcome host hints (ops.getaddrinfo host hints) = true)
  NondetTest.assert (
    !(validateHost host &&
      allowedDnsOutcome host hints (.ok expectedAddrs) &&
      (match rawFn host hints.family.toWire hints.sockType.toWire with
       | .ok bytes => bytes.data == (encodeWireRecords expectedAddrs).data
       | .error _ => false)) ||
    (match ops.getaddrinfo host hints with
     | .ok got => got == expectedAddrs
     | .error _ => false))
  NondetTest.assert (
    match validateHost host, rawFn host hints.family.toWire hints.sockType.toWire with
    | true, .error (rc, eno, msgBytes) =>
      let expCode := normalizeGaiCodeForHost host hints rc
      let expErrno? : Option Errno :=
        if expCode == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
      let expMsg :=
        match String.fromUTF8? msgBytes with
        | some s => if s.isEmpty then "getaddrinfo failed" else s
        | none => s!"<non-utf8:{msgBytes.size}B>"
      ops.getaddrinfo host hints = .error
        { kind := classifyGaiKind expCode
          gaiCode := expCode
          errno? := expErrno?
          message := expMsg }
    | _, _ => True)

/-- `healthyStep` and `healthyModelOps` preserve `HealthyEnv.wf`, force in-family pure numeric IP literals (`"127.0.0.1"`) to resolve unconditionally without `EINTR` or `EAI_AGAIN`, preserve oracle outcomes on non-numeric hostnames (`"localhost"`, `"fe80::1%lo"`) whenever non-critical and non-`EINTR`, accept everyday hostname failures (`EAI_AGAIN`, `EAI_NONAME`, `EAI_SYSTEM`/`EMFILE`), reject curated critical faults (`EAI_MEMORY`, `EAI_SYSTEM` + `ENOMEM`/`EIO`/`ENFILE`) and ambient `seccomp`, and strictly decrement `eintrBudget` on `EAI_SYSTEM`/`EINTR`. -/
def test_dns_healthyStep_and_healthyModelOps
    {runner} [NondetTest runner]
    (ops : DnsOpsM (StateM HealthyEnv) := healthyModelOps)
    (step : HealthyEnv → DnsReq → DnsOutcome → Option HealthyEnv := healthyStep) :
    runner Unit := do
  let e1 := HealthyEnv.initial 1 defaultOfflineOracle
  let e0 := HealthyEnv.initial 0 defaultOfflineOracle
  NondetTest.assert (e1.wf = true ∧ e0.wf = true)
  NondetTest.assert (step { state := DnsState.initial.withOuterSeccomp, eintrBudget := 1 }
    { host := "127.0.0.1" } (.ok [.ipv4 127 0 0 1]) = none)
  NondetTest.assert ((ops.getaddrinfo "127.0.0.1" { family := .ipv4, sockType := .stream }).run e1 =
    (.ok [.ipv4 127 0 0 1], e1))
  NondetTest.assert ((ops.getaddrinfo "localhost" { family := .any, sockType := .stream }).run e1 =
    (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0, .ipv4 127 0 0 1], e1))
  NondetTest.assert ((ops.getaddrinfo "fe80::1%lo" { family := .any, sockType := .stream }).run e1 =
    (.ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1], e1))
  NondetTest.assert (step e1 { host := "127.0.0.1", hints := { family := .ipv4, sockType := .stream } }
    (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) = none ∧
    step e1 { host := "127.0.0.1", hints := { family := .ipv4, sockType := .stream } }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) = none ∧
    step e1 { host := "127.0.0.1", hints := { family := .ipv6, sockType := .stream } }
      (.error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none, message := "x" }) = some e1)
  NondetTest.assert (step e1 { host := "localhost" }
      (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) = some e1 ∧
    step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EMFILE, message := "x" }) = some e1)
  NondetTest.assert (step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_MEMORY, errno? := none, message := "x" }) = none ∧
    step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.ENOMEM, message := "x" }) = none ∧
    step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EIO, message := "x" }) = none ∧
    step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.ENFILE, message := "x" }) = none)
  NondetTest.assert (step e1 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) = some e0 ∧
    step e0 { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) = none)
  let env ← nondet HealthyEnv
  assume (env.wf = true)
  let host ← nondet String
  let hints ← nondet ResolveHints
  let (res, env') := (ops.getaddrinfo host hints).run env
  NondetTest.assert (step env { host := host, hints := hints } res = some env' ∧
    env'.wf = true ∧ env'.eintrBudget = env.eintrBudget)
  NondetTest.assert (((isNumericHostLiteral host = false ∧
      isCriticalFault (modelResolve env.state.oracle host hints) = false ∧
      isEintrOutcome (modelResolve env.state.oracle host hints) = false) →
      res = modelResolve env.state.oracle host hints) ∧
    (∀ baseAddr sc, parseHybridScopedNumericZone? host = some (baseAddr, sc) →
      (hints.family != .ipv4) = true →
      res = match modelResolve env.state.oracle host hints with
        | .ok addrs => .ok addrs
        | .error _ => .ok (expandSockType hints [withIpv6Scope sc baseAddr])))
  NondetTest.assert ((res, env') = (healthyModelResolve env.state.oracle host hints, env) ∧
    ((parsePureNumericAddr? host = none ∧ parseHybridScopedNumericZone? host = none) →
      res =
        if isCriticalFault (modelResolve env.state.oracle host hints) ||
            isEintrOutcome (modelResolve env.state.oracle host hints) then
          .error (emptyPayloadError host hints)
        else
          modelResolve env.state.oracle host hints))
  let anyEnv ← nondet HealthyEnv
  let anyReq ← nondet DnsReq
  let anyOut ← nondet DnsOutcome
  NondetTest.assert (step anyEnv anyReq anyOut =
    if !anyEnv.wf || isCriticalFault anyOut then
      none
    else
      match allowedStep anyEnv.state anyReq anyOut with
      | none => none
      | some s' =>
        if isEintrOutcome anyOut then
          if anyEnv.eintrBudget > 0 then
            some { state := s', eintrBudget := anyEnv.eintrBudget - 1 }
          else
            none
        else
          some { state := s', eintrBudget := anyEnv.eintrBudget })

/-- Thin C-wrapper boundary assumptions for `LeanSwe.LinuxSyscall.Dns` (`c/dns_shim.c`), verified offline at runtime with nonce logging. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.LinuxSyscall.Dns.assume_dns_getaddrinfo_offlineAndScoped"
      subject := "LeanSwe.LinuxSyscall.Dns.getaddrinfo"
      formalPred? := none }
  , { name := "LeanSwe.LinuxSyscall.Dns.assume_dns_getaddrinfo_hostGuardsAndHints"
      subject := "LeanSwe.LinuxSyscall.Dns.getaddrinfo"
      formalPred? := none } ]

/-- Complete `(request × DnsErrorKind)` error-coverage matrix for caller-facing `LeanSwe.LinuxSyscall.Dns` operations (`5` obligations). -/
def errorCoverage : List (ErrorObligation DnsErrorKind) :=
  [ { request := "LeanSwe.LinuxSyscall.Dns.getaddrinfo", errorKind := .invalidHost, justification := .tested "LeanSwe.LinuxSyscall.Dns.RuntimeTests.err_dns_getaddrinfo_invalidHost" .real }
  , { request := "LeanSwe.LinuxSyscall.Dns.getaddrinfo", errorKind := .nameNotFound, justification := .tested "LeanSwe.LinuxSyscall.Dns.RuntimeTests.err_dns_getaddrinfo_nameNotFound" .real }
  , { request := "LeanSwe.LinuxSyscall.Dns.getaddrinfo", errorKind := .temporaryFailure, justification := .tested "LeanSwe.LinuxSyscall.Dns.RuntimeTests.err_dns_getaddrinfo_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Dns.getaddrinfo", errorKind := .systemError, justification := .tested "LeanSwe.LinuxSyscall.Dns.RuntimeTests.err_dns_getaddrinfo_mocked" .mocked }
  , { request := "LeanSwe.LinuxSyscall.Dns.getaddrinfo", errorKind := .otherGai, justification := .tested "LeanSwe.LinuxSyscall.Dns.RuntimeTests.err_dns_getaddrinfo_mocked" .mocked } ]

end LeanSwe.LinuxSyscall.Dns

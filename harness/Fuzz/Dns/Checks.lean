import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.Dns.Model

namespace Fuzz.Dns.Checks

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

private def failWith {α : Type} (msg : String) : IO α :=
  throw (IO.userError s!"Dns.Checks: {msg}")

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    failWith s!"assertion failed: {label}"

private def expectOk {α : Type} (label : String) (res : Except DnsError α) : IO α := do
  match res with
  | .ok v => return v
  | .error e => failWith s!"{label}: unexpected error ({repr e})"

private def expectErrKind {α : Type} (label : String) (expected : DnsErrorKind) (res : Except DnsError α)
    (logMode? : Option String := some "real") : IO DnsError := do
  match res with
  | .ok _ => failWith s!"{label}: expected error kind {repr expected}, got ok"
  | .error e =>
    if e.kind != expected then
      failWith s!"{label}: expected {repr expected}, got {repr e}"
    if let some mode := logMode? then
      Fuzz.Common.logErrHit "LeanSwe.LinuxSyscall.Dns.getaddrinfo" (reprStr e.kind).trimAscii.toString mode
    return e

private def mkMockRawOps (fn : String → UInt8 → UInt8 → Except (Int32 × UInt32 × ByteArray) ByteArray) :
    Internal.PosixDnsOps :=
  { getaddrinfo := fun host fam sock => pure (fn host fam sock) }

/-- Runtime verification for `LeanSwe.LinuxSyscall.Dns.assume_dns_getaddrinfo_offlineAndScoped`. -/
private def assume_dns_getaddrinfo_offlineAndScoped : IO Unit := do
  let r4 ← expectOk "127.0.0.1" (← getaddrinfo "127.0.0.1")
  assertTrue "127.0.0.1 exact" (r4 == [.ipv4 127 0 0 1])
  assertTrue "127.0.0.1 allowed" (allowedDnsOutcome "127.0.0.1" {} (.ok r4))

  let rAny ← expectOk "127.0.0.1 sockType=any" (← getaddrinfo "127.0.0.1" { family := .any, sockType := .any })
  assertTrue "127.0.0.1 any non-empty" (!rAny.isEmpty && rAny.all (· == .ipv4 127 0 0 1))
  assertTrue "127.0.0.1 any allowed" (allowedDnsOutcome "127.0.0.1" { family := .any, sockType := .any } (.ok rAny))

  let r6 ← expectOk "::1" (← getaddrinfo "::1")
  assertTrue "::1 exact" (r6 == [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0])
  assertTrue "::1 allowed" (allowedDnsOutcome "::1" {} (.ok r6))

  let rScoped ← expectOk "fe80::1%lo" (← getaddrinfo "fe80::1%lo")
  assertTrue "fe80::1%lo non-empty" (!rScoped.isEmpty)
  assertTrue "fe80::1%lo preserves non-zero scopeId" (rScoped.all fun a => a.isIpv6 && !a.isUnscoped)

  let rNumScope ← expectOk "fe80::1%305419896" (← getaddrinfo "fe80::1%305419896")
  assertTrue "fe80::1%305419896 allowedDnsOutcome" (allowedDnsOutcome "fe80::1%305419896" {} (.ok rNumScope))
  assertTrue "fe80::1%305419896 preserves non-zero scopeId"
    (!rNumScope.isEmpty && rNumScope.all fun a => a.isIpv6 && !a.isUnscoped)
  let rGlobalNumScope ← expectOk "2001:db8::1%305419896" (← getaddrinfo "2001:db8::1%305419896")
  assertTrue "2001:db8::1%305419896 always preserves exact multi-byte scopeId"
    (rGlobalNumScope == [.ipv6 0x20 0x01 0x0d 0xb8 0 0 0 0 0 0 0 0 0 0 0 1 305419896])
  let rLongZoneScope ← expectOk "fe80::1%0000000305419896" (← getaddrinfo "fe80::1%0000000305419896")
  assertTrue "fe80::1%0000000305419896 (>= IFNAMSIZ) always preserves exact scopeId"
    (rLongZoneScope == [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 305419896])

  let rMapped ← expectOk "::ffff:127.0.0.1 ipv4" (← getaddrinfo "::ffff:127.0.0.1" { family := .ipv4, sockType := .stream })
  assertTrue "::ffff:127.0.0.1 ipv4 unwraps" (rMapped == [.ipv4 127 0 0 1])
  let rMappedAny ← expectOk "::ffff:127.0.0.1 ipv4 any" (← getaddrinfo "::ffff:127.0.0.1" { family := .ipv4, sockType := .any })
  assertTrue "::ffff:127.0.0.1 ipv4 any 3x" (rMappedAny == [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])

  let hostsExists ← System.FilePath.pathExists "/etc/hosts"
  let rLocalAny ← getaddrinfo "localhost" { family := .ipv4, sockType := .any }
  assertTrue "localhost ipv4 any allowedDnsOutcome" (allowedDnsOutcome "localhost" { family := .ipv4, sockType := .any } rLocalAny)
  match rLocalAny with
  | .ok addrs =>
    assertTrue "localhost ipv4 any 3x mult" (matchesSockTypeMultiplicity { family := .ipv4, sockType := .any } addrs && addrs.all DnsAddr.isIpv4)
  | .error _ =>
    assertTrue "localhost ipv4 any only fails when /etc/hosts is absent" (!hostsExists)

  let rNonLinkZone ← getaddrinfo "::1%lo"
  assertTrue "::1%lo allowedDnsOutcome" (allowedDnsOutcome "::1%lo" {} rNonLinkZone)
  let _ ← expectErrKind "::1%lo rejected" .nameNotFound rNonLinkZone

  let rEmptyZoneV4 ← getaddrinfo "fe80::1%" { family := .ipv4, sockType := .stream }
  assertTrue "fe80::1% ipv4 allowedDnsOutcome" (allowedDnsOutcome "fe80::1%" { family := .ipv4, sockType := .stream } rEmptyZoneV4)
  let eEmptyZoneV4 ← expectErrKind "fe80::1% ipv4 EAI_ADDRFAMILY" .otherGai rEmptyZoneV4
  assertTrue "fe80::1% ipv4 gaiCode EAI_ADDRFAMILY" (eEmptyZoneV4.gaiCode == EAI_ADDRFAMILY)

  let rMappedZone ← getaddrinfo "::ffff:127.0.0.1%lo" { family := .ipv4, sockType := .stream }
  assertTrue "::ffff:127.0.0.1%lo ipv4 allowedDnsOutcome" (allowedDnsOutcome "::ffff:127.0.0.1%lo" { family := .ipv4, sockType := .stream } rMappedZone)
  let eMappedZone ← expectErrKind "::ffff:127.0.0.1%lo ipv4 EAI_NONAME" .nameNotFound rMappedZone
  assertTrue "::ffff:127.0.0.1%lo ipv4 gaiCode EAI_NONAME" (eMappedZone.gaiCode == EAI_NONAME)

  let longMalformed := String.join (List.replicate 50000 "1:") ++ "1"
  let rLong ← getaddrinfo longMalformed
  assertTrue "50000-colon malformed allowedDnsOutcome" (allowedDnsOutcome longMalformed {} rLong)
  let _ ← expectErrKind "50000-colon malformed rejected" .nameNotFound rLong

  let rLocalRaw ← getaddrinfo "localhost"
  assertTrue "localhost allowedDnsOutcome" (allowedDnsOutcome "localhost" {} rLocalRaw)
  assertTrue "8.8.8.8 not loopback" (!(DnsAddr.ipv4 8 8 8 8).isLoopback)
  assertTrue "scoped ::1%7 not loopback" (!(DnsAddr.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7).isLoopback)
  match rLocalRaw with
  | .ok rLocal =>
    assertTrue "localhost non-empty" (!rLocal.isEmpty)
    assertTrue "localhost all loopback" (rLocal.all DnsAddr.isLoopback)
    let decLocal ← expectOk "localhost round-trip" (Internal.decodeRecords (Internal.encodeRecords rLocal))
    assertTrue "localhost round-trip exact" (decLocal == rLocal)
  | .error _ =>
    assertTrue "localhost only fails when /etc/hosts is absent" (!hostsExists)

/-- Runtime verification for `LeanSwe.LinuxSyscall.Dns.assume_dns_getaddrinfo_hostGuardsAndHints`. -/
private def assume_dns_getaddrinfo_hostGuardsAndHints : IO Unit := do
  let eEmpty ← expectErrKind "empty host" .invalidHost (← getaddrinfo "")
  assertTrue "empty gaiCode EAI_NONAME" (eEmpty.gaiCode == EAI_NONAME)
  assertTrue "empty errno EINVAL" (eEmpty.errno? == some Errno.EINVAL)

  let eNul ← expectErrKind "embedded NUL host" .invalidHost (← getaddrinfo "a\x00b")
  assertTrue "nul gaiCode EAI_NONAME" (eNul.gaiCode == EAI_NONAME)
  assertTrue "nul errno EINVAL" (eNul.errno? == some Errno.EINVAL)

  let h4 : ResolveHints := { family := .ipv4, sockType := .stream }
  let r4 ← expectOk "127.0.0.1 ipv4" (← getaddrinfo "127.0.0.1" h4)
  assertTrue "127.0.0.1 ipv4 all ipv4" (!r4.isEmpty && r4.all DnsAddr.isIpv4)
  assertTrue "127.0.0.1 ipv4 allowed" (allowedDnsOutcome "127.0.0.1" h4 (.ok r4))

  let h6d : ResolveHints := { family := .ipv6, sockType := .dgram }
  let r6 ← expectOk "::1 ipv6 dgram" (← getaddrinfo "::1" h6d)
  assertTrue "::1 ipv6 all ipv6" (!r6.isEmpty && r6.all DnsAddr.isIpv6)
  assertTrue "::1 ipv6 allowed" (allowedDnsOutcome "::1" h6d (.ok r6))

  let rMismatch ← getaddrinfo "127.0.0.1" h6d
  assertTrue "127.0.0.1 ipv6 hint allowed" (allowedDnsOutcome "127.0.0.1" h6d rMismatch)
  match rMismatch with
  | .error e =>
    assertTrue "127.0.0.1 ipv6 hint otherGai" (e.kind == .otherGai && e.gaiCode == EAI_ADDRFAMILY)
  | .ok _ => failWith "127.0.0.1 unexpectedly resolved under IPv6-only hint"

  let rBad ← getaddrinfo "bad host"
  assertTrue "bad host allowedDnsOutcome" (allowedDnsOutcome "bad host" {} rBad)
  match rBad with
  | .error e =>
    assertTrue "bad host non-empty message" (!e.message.isEmpty)
    assertTrue "bad host EAI_NONAME" (e.kind == .nameNotFound && e.gaiCode == EAI_NONAME)
  | .ok _ => failWith "bad host unexpectedly resolved"

/-- Real offline host test for `DnsErrorKind.invalidHost` on `getaddrinfo`. -/
private def err_dns_getaddrinfo_invalidHost : IO Unit := do
  let e1 ← expectErrKind "getaddrinfo empty" .invalidHost (← getaddrinfo "")
  assertTrue "empty errno=EINVAL" (e1.errno? == some Errno.EINVAL)
  let e2 ← expectErrKind "getaddrinfo embedded NUL" .invalidHost (← getaddrinfo "bad\x00host")
  assertTrue "nul errno=EINVAL" (e2.errno? == some Errno.EINVAL)

/-- Real offline-deterministic host test for `DnsErrorKind.nameNotFound` on `getaddrinfo` (zero DNS network dependency). -/
private def err_dns_getaddrinfo_nameNotFound : IO Unit := do
  let e ← expectErrKind "bad host" .nameNotFound (← getaddrinfo "bad host")
  assertTrue "gaiCode == EAI_NONAME" (e.gaiCode == EAI_NONAME)
  assertTrue "message non-empty" (!e.message.isEmpty)

/-- Mocked FFI boundary error-classification, family-mismatch, and malformed-payload tests for `getaddrinfo`. -/
private def err_dns_getaddrinfo_mocked : IO Unit := do
  let expectMock {α : Type} (label : String) (expected : DnsErrorKind) (res : Except DnsError α) : IO DnsError :=
    expectErrKind label expected res (logMode? := some "mocked")
  let msg := "mock error".toUTF8
  let nodataOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_NODATA, 0, msg))
  let _ ← expectMock "mock nodata" .nameNotFound (← nodataOps.getaddrinfo "example.invalid.")

  let failOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_FAIL, 0, msg))
  let _ ← expectMock "mock fail" .nameNotFound (← failOps.getaddrinfo "example.invalid.")

  let tempOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_AGAIN, 0, msg))
  let _ ← expectMock "mock temporaryFailure" .temporaryFailure (← tempOps.getaddrinfo "example.invalid.")

  let sysOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_SYSTEM, Errno.ENOMEM, msg))
  let eSys ← expectMock "mock systemError" .systemError (← sysOps.getaddrinfo "example.invalid.")
  assertTrue "mock systemError errno" (eSys.errno? == some Errno.ENOMEM && eSys.message == "mock error")

  let sysZeroOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_SYSTEM, 0, ByteArray.empty))
  let eSysZero ← expectMock "mock EAI_SYSTEM errno=0" .systemError (← sysZeroOps.getaddrinfo "example.invalid.")
  assertTrue "mock EAI_SYSTEM errno=0 -> none" (eSysZero.errno? == none && eSysZero.message == "getaddrinfo failed")

  let memOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_MEMORY, Errno.ENOMEM, msg))
  let eMem ← expectMock "mock EAI_MEMORY" .systemError (← memOps.getaddrinfo "example.invalid.")
  assertTrue "mock EAI_MEMORY errno? none" (eMem.errno? == none)

  let zeroRcOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (0, 0, msg))
  let eZero ← expectMock "mock rc=0" .nameNotFound (← zeroRcOps.getaddrinfo "example.invalid.")
  assertTrue "mock rc=0 mapped to EAI_FAIL" (eZero.gaiCode == EAI_FAIL)

  let otherOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_FAMILY, 0, msg))
  let eOther ← expectMock "mock otherGai" .otherGai (← otherOps.getaddrinfo "example.invalid.")
  assertTrue "otherGai gaiCode EAI_FAMILY" (eOther.gaiCode == EAI_FAMILY)

  let emptyOkNameOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .ok ByteArray.empty)
  let eEmptyOkName ← expectMock "mock empty ok non-numeric -> nameNotFound" .nameNotFound
    (← emptyOkNameOps.getaddrinfo "example.invalid.")
  assertTrue "mock empty ok non-numeric EAI_NODATA" (eEmptyOkName.gaiCode == EAI_NODATA)

  let eEmptyOkNum ← expectMock "mock empty ok numeric ipv6 -> otherGai" .otherGai
    (← emptyOkNameOps.getaddrinfo "127.0.0.1" { family := .ipv6 })
  assertTrue "mock empty ok numeric EAI_ADDRFAMILY" (eEmptyOkNum.gaiCode == EAI_ADDRFAMILY)
  let eEmptyOkNumAny ← expectMock "mock empty ok numeric any -> EAI_FAIL" .nameNotFound
    (← emptyOkNameOps.getaddrinfo "127.0.0.1")
  assertTrue "mock empty ok numeric any EAI_FAIL" (eEmptyOkNumAny.gaiCode == EAI_FAIL)

  let mismatchNameOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .ok (Internal.encodeRecords [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0]))
  let eMisName ← expectMock "mock family mismatch non-numeric -> nameNotFound" .nameNotFound
    (← mismatchNameOps.getaddrinfo "example.invalid." { family := .ipv4 })
  assertTrue "mock family mismatch non-numeric EAI_NODATA" (eMisName.gaiCode == EAI_NODATA)

  let eMisNum ← expectMock "mock family mismatch numeric -> otherGai" .otherGai
    (← mismatchNameOps.getaddrinfo "127.0.0.1" { family := .ipv6 })
  assertTrue "mock family mismatch numeric EAI_ADDRFAMILY" (eMisNum.gaiCode == EAI_ADDRFAMILY)

  let rc42Ops := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (42, 0, msg))
  let eRc42 ← expectMock "mock rc=42" .nameNotFound (← rc42Ops.getaddrinfo "example.invalid.")
  assertTrue "mock rc=42 mapped to EAI_FAIL" (eRc42.gaiCode == EAI_FAIL)

  let otherNonUtf8Ops := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_FAMILY, 0, ByteArray.mk #[0xff, 0xfe]))
  let eNonUtf8 ← expectMock "mock non-utf8 otherGai" .otherGai (← otherNonUtf8Ops.getaddrinfo "example.invalid.")
  assertTrue "non-utf8 message preserved" (eNonUtf8.message == "<non-utf8:2B>")

  let svcOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_SERVICE, 0, msg))
  let eSvc ← expectMock "mock EAI_SERVICE clamped" .nameNotFound (← svcOps.getaddrinfo "example.invalid.")
  assertTrue "mock EAI_SERVICE mapped to EAI_FAIL" (eSvc.gaiCode == EAI_FAIL)

  let badFlagsOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_BADFLAGS, 0, msg))
  let eBadFlags ← expectMock "mock EAI_BADFLAGS clamped" .nameNotFound (← badFlagsOps.getaddrinfo "example.invalid.")
  assertTrue "mock EAI_BADFLAGS mapped to EAI_FAIL" (eBadFlags.gaiCode == EAI_FAIL)

  let efaultOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .error (EAI_SYSTEM, Errno.EFAULT, msg))
  let eEfault ← expectMock "mock EAI_SYSTEM EFAULT" .systemError (← efaultOps.getaddrinfo "example.invalid.")
  assertTrue "mock EAI_SYSTEM EFAULT stripped" (eEfault.errno? == none)

  let mixedOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ =>
    .ok (Internal.encodeRecords [.ipv4 127 0 0 1, .ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0]))
  let eMixedName ← expectMock "mock mixed family rejected non-numeric" .nameNotFound
    (← mixedOps.getaddrinfo "example.invalid." { family := .ipv4 })
  assertTrue "mock mixed family rejected EAI_NODATA" (eMixedName.gaiCode == EAI_NODATA)
  let eMixedNum ← expectMock "mock mixed family rejected numeric" .nameNotFound
    (← mixedOps.getaddrinfo "127.0.0.1" { family := .ipv4 })
  assertTrue "mock mixed family rejected numeric EAI_FAIL" (eMixedNum.gaiCode == EAI_FAIL)

  let malOps := Internal.mkDnsOps (mkMockRawOps fun _ _ _ => .ok (ByteArray.mk #[99, 0, 0, 0, 0]))
  let eMal ← expectMock "mock malformed payload -> otherGai" .otherGai (← malOps.getaddrinfo "example.invalid.")
  assertTrue "mock malformed gaiCode=EAI_OVERFLOW" (eMal.gaiCode == EAI_OVERFLOW)

/-- Real decoder test for `.otherGai` (`EAI_OVERFLOW`) on malformed inputs and large tail-recursive round-trips. -/
private def err_dns_decodeRecords_malformed : IO Unit := do
  let eTrunc ← expectErrKind "truncated" .otherGai (Internal.decodeRecords (ByteArray.mk #[4, 127, 0])) none
  assertTrue "truncated EAI_OVERFLOW" (eTrunc.gaiCode == EAI_OVERFLOW)
  let _ ← expectErrKind "bad tag" .otherGai
    (Internal.decodeRecords (ByteArray.mk #[9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) none
  let _ ← expectErrKind "bad v4 padding" .otherGai
    (Internal.decodeRecords (ByteArray.mk #[4, 127, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])) none
  let bulk := List.replicate 5000 (DnsAddr.ipv4 127 0 0 1)
  let decBulk ← expectOk "5000-record tail-rec round-trip" (Internal.decodeRecords (Internal.encodeRecords bulk))
  assertTrue "5000-record count" (decBulk.length == 5000)

/-- Run all `Dns` real and mocked error-path regression checks. -/
def runChecks : IO Unit := do
  assume_dns_getaddrinfo_offlineAndScoped
  assume_dns_getaddrinfo_hostGuardsAndHints
  err_dns_getaddrinfo_invalidHost
  err_dns_getaddrinfo_nameNotFound
  err_dns_getaddrinfo_mocked
  err_dns_decodeRecords_malformed

end Fuzz.Dns.Checks

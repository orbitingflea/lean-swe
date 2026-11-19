import LeanSwe.LinuxSyscall.Dns.SpecTests
import LeanSwe.LinuxSyscall.Dns.Impl

/-! Compile-time negative specification mutants for `LeanSwe.LinuxSyscall.Dns`. -/

namespace LeanSwe.LinuxSyscall.Dns

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

example : ¬ Core.AllPass (test_dns_validateHost_semantics (fun h => !h.isEmpty)) := by
  intro h
  have h0 := h "a\x00b"
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics (fun _ => "127.0.0.1")) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics
    (fun a => s!"{a.format}%0")
    DnsAddr.isLoopback) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics
    DnsAddr.format
    (fun _ => true)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_classifyGaiKind_semantics (fun rc =>
    if rc == EAI_NONAME then .invalidHost else classifyGaiKind rc)) := by
  intro h
  have h0 := h EAI_NONAME
  exact absurd h0.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_wireTags_semantics
    (fun | .any => 1 | .ipv4 => 1 | .ipv6 => 2)
    SockTypeHint.toWire) := by
  intro h
  have h0 := h .any .ipv4 .any .any
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_dns_wireTags_semantics
    AddrFamilyHint.toWire
    (fun | .any => 1 | .stream => 1 | .dgram => 2)) := by
  intro h
  have h0 := h .any .any .any .stream
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ => pure (.ok []) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "::1%lo" then pure (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1])
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "::1%lo" {} (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "fe80::1%" && f.family == .ipv4 then
          pure (.error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "x" })
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "fe80::1%" { family := .ipv4, sockType := .stream } (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "localhost" && f.family == .ipv4 && f.sockType == .any then
          pure (.ok [.ipv4 127 0 0 1])
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "localhost" { family := .ipv4, sockType := .any } (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ =>
        pure (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EFAULT, message := "x" }) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ =>
        pure (.error { kind := .otherGai, gaiCode := -13, errno? := none, message := "x" }) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun _ => { getaddrinfo := fun _ _ => .ok [] })) := by
  intro h
  have h1 := (h (fun _ _ _ => .ok ByteArray.empty) "127.0.0.1" {} []).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun _ => { getaddrinfo := fun _ _ =>
      Except.error ({ kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none, message := "x" }) })) := by
  intro h
  let exp := [DnsAddr.ipv4 127 0 0 1]
  have h2 := (h (fun _ _ _ => .ok (encodeWireRecords exp)) "example.invalid." {} exp).2.1
  simp [allowedDnsOutcome, parsePureNumericAddr?, parseScopedNonNumericZone?,
    validateHost, String.any] at h2
  exact absurd h2 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match raw host hints.sockType.toWire hints.family.toWire with
          | .ok _ => .ok [.ipv4 127 0 0 1]
          | .error _ => Except.error ({ kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none, message := "x" }) })) := by
  intro h
  let exp := [DnsAddr.ipv4 127 0 0 1]
  have h2 := (h
    (fun _ fam sock =>
      if fam == 1 && sock == 2 then .ok (encodeWireRecords exp)
      else .error (EAI_FAIL, 0, ByteArray.empty))
    "127.0.0.1" { family := .ipv4, sockType := .dgram } exp).2.1
  simp [allowedDnsOutcome, parsePureNumericAddr?, validateHost, String.any] at h2
  exact absurd h2 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match (Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw }).getaddrinfo host hints with
          | .ok xs => .ok xs
          | .error e => .error { e with errno? := none } })) := by
  intro h
  have h3 := (h (fun _ _ _ => .error (EAI_SYSTEM, Errno.ENOMEM, "oom".toUTF8)) "127.0.0.1" {} []).2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h3
  have hv : validateHost "127.0.0.1" = true := by simp [validateHost, String.any]
  rw [hv] at h3
  dsimp at h3
  rw [Internal.mkDnsOpsM_id_error_eq "127.0.0.1" hv {} EAI_SYSTEM Errno.ENOMEM "oom".toUTF8] at h3
  injection h3 with hErr
  injection hErr with _ _ hEno _
  exact absurd hEno (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match (Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw }).getaddrinfo host hints with
          | .ok xs => .ok xs
          | .error e => .error { e with message := "x" } })) := by
  intro h
  have h3 := (h (fun _ _ _ => .error (EAI_AGAIN, 0, "temp err".toUTF8)) "127.0.0.1" {} []).2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h3
  have hv : validateHost "127.0.0.1" = true := by simp [validateHost, String.any]
  rw [hv] at h3
  dsimp at h3
  rw [Internal.mkDnsOpsM_id_error_eq "127.0.0.1" hv {} EAI_AGAIN 0 "temp err".toUTF8] at h3
  injection h3 with hErr
  injection hErr with _ _ _ hMsg
  have hUtf8 : String.fromUTF8? "temp err".toUTF8 = some "temp err" := by
    simp [String.fromUTF8?, String.toUTF8, "temp err".isValidUTF8]
  rw [hUtf8] at hMsg
  exact absurd hMsg (by decide)

end LeanSwe.LinuxSyscall.Dns

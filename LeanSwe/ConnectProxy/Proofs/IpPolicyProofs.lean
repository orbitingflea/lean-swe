import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.SpecTests

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

private def AllBelow (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | k + 1 => P k ∧ AllBelow P k

private theorem of_allBelow {P : Nat → Prop} : ∀ {n : Nat}, AllBelow P n → ∀ i < n, P i
  | 0, _, _, hi => nomatch hi
  | k + 1, ⟨hk, hrest⟩, i, hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact of_allBelow hrest i hlt
    · exact hk

local macro "prove_u64_bits" : tactic =>
  `(tactic| (
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    revert i hi
    apply of_allBelow
    simp [AllBelow]))

local macro "prove_u32_bits" : tactic =>
  `(tactic| (
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    revert i hi
    apply of_allBelow
    simp [AllBelow]))

private theorem u64_beq_false_of_rshift_ne {x y s : UInt64}
    (h : x >>> s ≠ y >>> s) : (x == y) = false := by
  apply beq_false_of_ne
  intro hEq
  exact h (congrArg (· >>> s) hEq)

private theorem nonEmpty_append_left {a b : String} (ha : a ≠ "") : a ++ b ≠ "" :=
  fun h => ha (String.append_eq_empty_iff.mp h).1

local macro "solve_invalid_input" : tactic =>
  `(tactic| exact ⟨rfl, by
    dsimp only [ToString.toString]
    repeat (first | apply nonEmpty_append_left | decide)⟩)

private theorem bool_not_of_ne_true {b : Bool} (h : ¬b = true) : (!b) = true := by
  cases b <;> simp_all

private theorem parseIpAddr_ok_no_star {s : String} {ip : IpAddr}
    (h : Model.parseIpAddr s = .ok ip) : (!s.toList.contains '*') = true := by
  unfold Model.parseIpAddr at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hStar
    exact bool_not_of_ne_true hStar

private theorem parseIpAddr_err_props {s : String} {err : ProxyError}
    (h : Model.parseIpAddr s = .error err) : err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.parseIpAddr at h
  dsimp only at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · split at h
      · cases h
      · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · cases h
      · injection h with hEq; subst hEq; solve_invalid_input

private theorem parseIpPrefix_ok_props {s : String} {pfx : IpPrefix}
    (h : Model.parseIpPrefix s = .ok pfx) :
    (!s.toList.contains '*') = true ∧ Model.isValidIpPrefix pfx = true := by
  unfold Model.parseIpPrefix at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hStar
    refine ⟨bool_not_of_ne_true hStar, ?_⟩
    split at h
    · split at h <;> try cases h
      · rfl
      · rfl
    · split at h <;> try cases h
      · split at h
        · rename_i hLen
          split at h <;> try cases h
          simp [Model.isValidIpPrefix, hLen]
        · cases h
      · split at h
        · rename_i hLen
          split at h <;> try cases h
          simp [Model.isValidIpPrefix, hLen]
        · cases h
    · cases h

private theorem parseIpPrefix_err_props {s : String} {err : ProxyError}
    (h : Model.parseIpPrefix s = .error err) : err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.parseIpPrefix at h
  dsimp only at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · split at h
      · cases h
      · cases h
      · rename_i hAddr
        injection h with hEq; subst hEq
        exact parseIpAddr_err_props hAddr
    · split at h
      · split at h
        · split at h
          · cases h
          · injection h with hEq; subst hEq; solve_invalid_input
        · injection h with hEq; subst hEq; solve_invalid_input
      · split at h
        · split at h
          · cases h
          · injection h with hEq; subst hEq; solve_invalid_input
        · injection h with hEq; subst hEq; solve_invalid_input
      · injection h with hEq; subst hEq; exact parseIpAddr_err_props ‹_›
      · injection h with hEq; subst hEq; solve_invalid_input
    · injection h with hEq; subst hEq; solve_invalid_input

/-- Any matching CIDR block in `policy.extraBans` overrides both `policy.base` and `policy.extraAllows`. -/
theorem specBanOverridesAllow : SpecBanOverridesAllow := by
  intro policy ip ban hMem hMatch
  unfold Model.allowsIp Model.isBannedByPrefixes
  have hAny : (policy.extraBans.toList.any fun b =>
      prefixContains b ip || (embeddedIpv4Addrs ip).any (fun v4 => prefixContains b v4)) = true := by
    rw [List.any_eq_true]
    exact ⟨ban, hMem, by simp [hMatch]⟩
  simp [hAny]

/-- Wrapping a banned IPv4 address in any supported IPv4-in-IPv6 embedding never bypasses `extraBans`. -/
theorem specIpv4InIpv6NeverBypassesBan : SpecIpv4InIpv6NeverBypassesBan := by
  refine ⟨?_, ?_⟩
  · intro policy ip v4 ban hEmb hBan hMatch
    unfold Model.allowsIp Model.isBannedByPrefixes
    have hAny : (policy.extraBans.toList.any fun b =>
        prefixContains b ip || (embeddedIpv4Addrs ip).any (fun x => prefixContains b x)) = true := by
      rw [List.any_eq_true]
      refine ⟨ban, hBan, ?_⟩
      have hEmbMatch : ((embeddedIpv4Addrs ip).any (fun x => prefixContains ban x)) = true := by
        rw [List.any_eq_true]
        exact ⟨v4, hEmb, hMatch⟩
      simp [hEmbMatch]
    simp [hAny]
  · intro v4 sub8 subHi sla subLo otherV4 flagsPort suffix32 suffix24 iface suffix40
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [mkIpv4MappedIpv6, embeddedIpv4Addrs]
      have h1 : (((0x0000ffff00000000 : UInt64) ||| v4.toUInt64) >>> 32) = 0x0000ffff := by prove_u64_bits
      have h2 : ((0x0000ffff00000000 : UInt64) ||| v4.toUInt64).toUInt32 = v4 := by prove_u32_bits
      rw [h1, h2]; simp
    · intro hv4
      dsimp [mkIpv4CompatibleIpv6, embeddedIpv4Addrs]
      have h1 : (v4.toUInt64 >>> 32) = 0 := by prove_u64_bits
      have h2 : v4.toUInt64.toUInt32 = v4 := by prove_u32_bits
      have hgt : v4.toUInt64 > 1 := by
        show (1 : UInt64).toNat < v4.toUInt64.toNat
        have hv : (1 : UInt32).toNat < v4.toNat := hv4
        simpa [UInt32.toNat_toUInt64] using hv
      rw [h1, h2]; simp [hgt]
    · dsimp [mkSiitIpv6, embeddedIpv4Addrs]
      have h1 : (((0xffff000000000000 : UInt64) ||| v4.toUInt64) >>> 32) = 0xffff0000 := by prove_u64_bits
      have h2 : ((0xffff000000000000 : UInt64) ||| v4.toUInt64).toUInt32 = v4 := by prove_u32_bits
      rw [h1, h2]; simp
    · dsimp [mkNat64WellKnownIpv6, embeddedIpv4Addrs]
      have h1 : (v4.toUInt64 >>> 32) = 0 := by prove_u64_bits
      have h2 : v4.toUInt64.toUInt32 = v4 := by prove_u32_bits
      rw [h1, h2]; simp
    · dsimp [mkNat64LocalIpv6, embeddedIpv4Addrs]
      have h1 : (((0x0064ff9b00010000 : UInt64) ||| subHi.toUInt64) >>> 16) = 0x0064ff9b0001 := by prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 16) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 16) (by rw [h1]; decide)
      have h2 : ((subLo.toUInt64 <<< 32) ||| v4.toUInt64).toUInt32 = v4 := by prove_u32_bits
      rw [h0a, h0b, h1, h2]; simp
    · dsimp [mkNat64Local48Ipv6, embeddedIpv4Addrs]
      have h1 : (((0x0064ff9b00010000 : UInt64) ||| (v4 >>> 16).toUInt64) >>> 16) = 0x0064ff9b0001 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 16) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 16) (by rw [h1]; decide)
      have hu : ((((((v4 &&& 0xffff).toUInt64 <<< 40) ||| (suffix40 &&& 0xffffffffff)) >>> 56) &&& 0xff) == 0) = true := by
        apply beq_iff_eq.mpr; prove_u64_bits
      have hv4 : ((((0x0064ff9b00010000 : UInt64) ||| (v4 >>> 16).toUInt64) <<< 16) |||
          (((((v4 &&& 0xffff).toUInt64 <<< 40) ||| (suffix40 &&& 0xffffffffff)) >>> 40) &&& 0xffff)).toUInt32 = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h1, hu, hv4]; simp
    · dsimp [mkNat64Local56Ipv6, embeddedIpv4Addrs]
      have h1 : (((0x0064ff9b00010000 : UInt64) ||| (sub8.toUInt64 <<< 8) ||| (v4 >>> 24).toUInt64) >>> 16) = 0x0064ff9b0001 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 16) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 16) (by rw [h1]; decide)
      have hu : ((((((v4 &&& 0xffffff).toUInt64 <<< 32) ||| suffix32.toUInt64) >>> 56) &&& 0xff) == 0) = true := by
        apply beq_iff_eq.mpr; prove_u64_bits
      have hv4 : (((((0x0064ff9b00010000 : UInt64) ||| (sub8.toUInt64 <<< 8) ||| (v4 >>> 24).toUInt64) &&& 0xff) <<< 24) |||
          (((((v4 &&& 0xffffff).toUInt64 <<< 32) ||| suffix32.toUInt64) >>> 32) &&& 0xffffff)).toUInt32 = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h1, hu, hv4]; simp
    · dsimp [mkNat64Local64Ipv6, embeddedIpv4Addrs]
      have h1 : (((0x0064ff9b00010000 : UInt64) ||| subHi.toUInt64) >>> 16) = 0x0064ff9b0001 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 16) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 16) (by rw [h1]; decide)
      have hu : (((((v4.toUInt64 <<< 24) ||| (suffix24 &&& 0xffffff).toUInt64) >>> 56) &&& 0xff) == 0) = true := by
        apply beq_iff_eq.mpr; prove_u64_bits
      have hv4 : (((v4.toUInt64 <<< 24) ||| (suffix24 &&& 0xffffff).toUInt64) >>> 24).toUInt32 = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h1, hu, hv4]; simp
    · dsimp [mk6to4Ipv6, embeddedIpv4Addrs]
      have h1 : (((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) >>> 48) = 0x2002 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 48) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 48) (by rw [h1]; decide)
      have h0c : ((((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) >>> 16) == 0x0064ff9b0001) = false := by
        have hShift : ((((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) >>> 16) >>> 32) =
            (((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) >>> 48) := by
          prove_u64_bits
        exact u64_beq_false_of_rshift_ne (s := 32) (by rw [hShift, h1]; decide)
      have hv4 : (((0x2002000000000000 : UInt64) ||| (v4.toUInt64 <<< 16) ||| sla.toUInt64) >>> 16).toUInt32 = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h0c, h1, hv4]; simp
    · dsimp [mkTeredoIpv6, embeddedIpv4Addrs]
      have h1 : (((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 32) = 0x20010000 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 32) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 32) (by rw [h1]; decide)
      have h0c : ((((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 16) == 0x0064ff9b0001) = false := by
        have hShift : ((((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 16) >>> 16) =
            (((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 32) := by
          prove_u64_bits
        exact u64_beq_false_of_rshift_ne (s := 16) (by rw [hShift, h1]; decide)
      have h0d : ((((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 48) == 0x2002) = false := by
        apply beq_false_of_ne
        have hShift : (((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 48) =
            ((((0x2001000000000000 : UInt64) ||| v4.toUInt64) >>> 32) >>> 16) := by
          prove_u64_bits
        rw [hShift, h1]; decide
      have hv4 : ((0x2001000000000000 : UInt64) ||| v4.toUInt64).toUInt32 = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h0c, h0d, h1, hv4]; simp
    · dsimp [mkTeredoIpv6, embeddedIpv4Addrs]
      have h1 : (((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 32) = 0x20010000 := by
        prove_u64_bits
      have h0a := u64_beq_false_of_rshift_ne (y := 0) (s := 32) (by rw [h1]; decide)
      have h0b := u64_beq_false_of_rshift_ne (y := 0x0064ff9b00000000) (s := 32) (by rw [h1]; decide)
      have h0c : ((((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 16) == 0x0064ff9b0001) = false := by
        have hShift : ((((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 16) >>> 16) =
            (((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 32) := by
          prove_u64_bits
        exact u64_beq_false_of_rshift_ne (s := 16) (by rw [hShift, h1]; decide)
      have h0d : ((((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 48) == 0x2002) = false := by
        apply beq_false_of_ne
        have hShift : (((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 48) =
            ((((0x2001000000000000 : UInt64) ||| otherV4.toUInt64) >>> 32) >>> 16) := by
          prove_u64_bits
        rw [hShift, h1]; decide
      have hv4 : (((flagsPort.toUInt64 <<< 32) ||| (v4 ^^^ 0xffffffff).toUInt64).toUInt32 ^^^ 0xffffffff) = v4 := by
        prove_u32_bits
      rw [h0a, h0b, h0c, h0d, h1, hv4]; simp

/-- `AllPass` proof of `test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid` on `defaultApi`. -/
theorem proof_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid :
    Core.AllPass (test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid defaultApi) := by
  intro s
  dsimp [test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assert]
  refine ⟨rfl, ?_⟩
  cases h : Model.parseIpAddr s with
  | ok _ => exact ⟨parseIpAddr_ok_no_star h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | error err => exact ⟨parseIpAddr_err_props h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `CanReach` witness for `test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid` on `defaultApi`. -/
theorem reach_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid :
    Core.CanReach (test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid defaultApi) :=
  ⟨"127.0.0.1", proof_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid "127.0.0.1"⟩

/-- `AllPass` proof of `test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards` on `defaultApi`. -/
theorem proof_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards :
    Core.AllPass (test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards defaultApi) := by
  intro s
  dsimp [test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assert]
  refine ⟨rfl, ?_⟩
  have hP16 : Model.parseIpPrefix "10.1.0.0/16" = .ok (.v4 0x0a010000 16) := rfl
  cases h : Model.parseIpPrefix s with
  | ok _ =>
    refine ⟨parseIpPrefix_ok_props h, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [hP16]
    exact ⟨by decide, by decide, trivial⟩
  | error err =>
    refine ⟨parseIpPrefix_err_props h, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [hP16]
    exact ⟨by decide, by decide, trivial⟩

/-- `CanReach` witness for `test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards` on `defaultApi`. -/
theorem reach_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards :
    Core.CanReach (test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards defaultApi) :=
  ⟨"10.1.0.0/16", proof_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards "10.1.0.0/16"⟩

/-- `AllPass` proof of `test_cproxy_isGlobalIp_completeIanaRfc6890Table` on `defaultApi`. -/
theorem proof_cproxy_isGlobalIp_completeIanaRfc6890Table :
    Core.AllPass (test_cproxy_isGlobalIp_completeIanaRfc6890Table defaultApi) := by
  intro ip
  dsimp [test_cproxy_isGlobalIp_completeIanaRfc6890Table, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assert]
  refine ⟨rfl, ?_⟩
  repeat refine ⟨by decide, ?_⟩
  exact trivial

/-- `CanReach` witness for `test_cproxy_isGlobalIp_completeIanaRfc6890Table` on `defaultApi`. -/
theorem reach_cproxy_isGlobalIp_completeIanaRfc6890Table :
    Core.CanReach (test_cproxy_isGlobalIp_completeIanaRfc6890Table defaultApi) :=
  ⟨.v4 0x08080808, proof_cproxy_isGlobalIp_completeIanaRfc6890Table (.v4 0x08080808)⟩

/-- `AllPass` proof of `test_cproxy_allowsIp_banAlwaysOverridesAllow` on `defaultApi`. -/
theorem proof_cproxy_allowsIp_banAlwaysOverridesAllow :
    Core.AllPass (test_cproxy_allowsIp_banAlwaysOverridesAllow defaultApi) := by
  intro policy ip
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assume, assert]
  refine ⟨rfl, by decide, by decide, ?_⟩
  intro i hi hMatch
  have hMem : policy.extraBans[i]! ∈ policy.extraBans.toList := by
    rw [getElem!_pos policy.extraBans i hi]
    exact Array.getElem_mem_toList hi
  exact ⟨specBanOverridesAllow policy ip policy.extraBans[i]! hMem hMatch, trivial⟩

/-- `CanReach` witness for `test_cproxy_allowsIp_banAlwaysOverridesAllow` on `defaultApi`. -/
theorem reach_cproxy_allowsIp_banAlwaysOverridesAllow :
    Core.CanReach (test_cproxy_allowsIp_banAlwaysOverridesAllow defaultApi) := by
  let policy : IpPolicy := { extraBans := #[.v4 0x7f000000 8] }
  let ip : IpAddr := .v4 0x7f000001
  have hi : 0 < policy.extraBans.size := by decide
  have hMatch : prefixContains policy.extraBans[0]! ip = true := by decide
  have hAll := proof_cproxy_allowsIp_banAlwaysOverridesAllow policy ip
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assume, assert] at hAll
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.defaultIoApi,
    Core.CanReach, bind, assume, assert]
  exact ⟨policy, ip, rfl, by decide, by decide, 0, hi, hMatch, (hAll.2.2.2 0 hi hMatch).1, trivial⟩

/-- `AllPass` proof of `test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan` on `defaultApi`. -/
theorem proof_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan :
    Core.AllPass (test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan defaultApi) := by
  intro v4 sub8 subHi sla subLo otherV4 flagsPort suffix32 suffix24 iface suffix40 ban hBan
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assume, assert]
  let wideAllowPolicy : IpPolicy :=
    { base := .publicOnly
      extraAllows := #[.v6 0 0 0]
      extraBans := #[ban] }
  have hBanMem : ban ∈ wideAllowPolicy.extraBans.toList := by simp [wideAllowPolicy]
  obtain ⟨hUnwrap, hEmbed⟩ := specIpv4InIpv6NeverBypassesBan
  obtain ⟨hM, hC, hS, hW, hL, h48, h56, h64, h6t4, hTs, hTc⟩ :=
    hEmbed v4 sub8 subHi sla subLo otherV4 flagsPort suffix32 suffix24 iface suffix40
  refine ⟨hUnwrap wideAllowPolicy _ (.v4 v4) ban hM hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban hS hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban hW hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban hL hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban h48 hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban h56 hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban h64 hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban h6t4 hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban hTs hBanMem hBan,
    hUnwrap wideAllowPolicy _ (.v4 v4) ban hTc hBanMem hBan, ?_⟩
  by_cases hv : v4 > 1
  · simp only [hv, ↓reduceIte]
    exact ⟨hUnwrap wideAllowPolicy _ (.v4 v4) ban (hC hv) hBanMem hBan, trivial⟩
  · simp [hv, pure]

/-- `CanReach` witness for `test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan` on `defaultApi`. -/
theorem reach_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan :
    Core.CanReach (test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan defaultApi) := by
  let v4 : UInt32 := 0x7f000001
  let ban : IpPrefix := .v4 0x7f000000 8
  have hBan : prefixContains ban (.v4 v4) = true := by decide
  have hAll := proof_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan
    v4 0 0 0 0 0 0 0 0 0 0 ban hBan
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.defaultIoApi,
    Core.AllPass, bind, assume, assert] at hAll
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.defaultIoApi,
    Core.CanReach, bind, assume, assert]
  exact ⟨v4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ban, hBan, hAll⟩

end LeanSwe.ConnectProxy.Proofs

import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSweProofs.LinuxSyscall.Dns.SpecTests

namespace LeanSwe.LinuxSyscall.Dns

open LeanSwe.LinuxSyscall

/-- Canonical 21-byte wire serialization for a single `DnsAddr` (`c/dns_shim.c` layout). -/
def wireAddrBytes : DnsAddr → List UInt8
  | .ipv4 b0 b1 b2 b3 =>
    [4, b0, b1, b2, b3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    let n := sc.toNat
    [6, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
     UInt8.ofNat ((n / 65536) % 256), UInt8.ofNat ((n / 16777216) % 256)]

private theorem push_wire_toList (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList = b.data.toList ++ [x] := by
  simp [ByteArray.push]

private theorem pushWireAddr_data_toList (acc : ByteArray) (a : DnsAddr) :
    (Internal.pushWireAddr acc a).data.toList = acc.data.toList ++ wireAddrBytes a := by
  cases a with
  | ipv4 b0 b1 b2 b3 =>
    unfold Internal.pushWireAddr wireAddrBytes
    simp only [push_wire_toList, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    unfold Internal.pushWireAddr Internal.pushWireUInt32LE wireAddrBytes
    simp only [push_wire_toList, List.append_assoc, List.cons_append, List.nil_append]
    rfl

private theorem encodeWireRecordsLoop_data_toList (addrs : List DnsAddr) (acc : ByteArray) :
    (Internal.encodeWireRecordsLoop addrs acc).data.toList = acc.data.toList ++ addrs.flatMap wireAddrBytes := by
  induction addrs generalizing acc with
  | nil => simp [Internal.encodeWireRecordsLoop]
  | cons a rest ih =>
    simp [Internal.encodeWireRecordsLoop, ih, pushWireAddr_data_toList, List.flatMap_cons, List.append_assoc]

/-- Every `encodeWireRecords addrs` buffer equals `addrs.flatMap wireAddrBytes` byte-for-byte. -/
theorem encodeWireRecords_data_toList (addrs : List DnsAddr) :
    (encodeWireRecords addrs).data.toList = addrs.flatMap wireAddrBytes := by
  unfold encodeWireRecords
  rw [encodeWireRecordsLoop_data_toList]
  rfl

/-- Every host accepted by `parsePureNumericAddr?` is non-empty and free of embedded NUL bytes (`validateHost = true`). -/
theorem validateHost_of_parsePureNumericAddr {host : String} {addr : DnsAddr}
    (hP : parsePureNumericAddr? host = some addr) :
    validateHost host = true := by
  unfold parsePureNumericAddr? at hP
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · unfold validateHost
    unfold Internal.isNonEmptyNoNulHost at hne
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hne ⊢
    refine ⟨?_, ?_⟩
    · cases hl : host.toList with
      | nil => simp [hl] at hne
      | cons _ _ =>
        cases he : host.isEmpty
        · rfl
        · have : host = "" := String.isEmpty_iff.mp he
          subst this; simp at hl
    · cases hAny : host.toList.any (· == '\x00') with
      | false => simp [String.any, hAny]
      | true =>
        rw [List.any_eq_true] at hAny
        rcases hAny with ⟨c, hcMem, hcEq⟩
        have hc0 : c = Char.ofNat 0 := eq_of_beq hcEq
        subst hc0
        have hCont : host.toList.contains (Char.ofNat 0) = true := List.contains_iff_mem.mpr hcMem
        rw [hne.2] at hCont
        contradiction
  · simp [hne] at hP

/-- Every host accepted by `parseHybridScopedNumericZone?` is non-empty and free of embedded NUL bytes (`validateHost = true`). -/
theorem validateHost_of_parseHybridScopedNumericZone {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hH : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    validateHost host = true := by
  unfold parseHybridScopedNumericZone? at hH
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · unfold validateHost
    unfold Internal.isNonEmptyNoNulHost at hne
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hne ⊢
    refine ⟨?_, ?_⟩
    · cases hl : host.toList with
      | nil => simp [hl] at hne
      | cons _ _ =>
        cases he : host.isEmpty
        · rfl
        · have : host = "" := String.isEmpty_iff.mp he
          subst this; simp at hl
    · cases hAny : host.toList.any (· == '\x00') with
      | false => simp [String.any, hAny]
      | true =>
        rw [List.any_eq_true] at hAny
        rcases hAny with ⟨c, hcMem, hcEq⟩
        have hc0 : c = Char.ofNat 0 := eq_of_beq hcEq
        subst hc0
        have hCont : host.toList.contains (Char.ofNat 0) = true := List.contains_iff_mem.mpr hcMem
        rw [hne.2] at hCont
        contradiction
  · simp [hne] at hH

/-- Every `baseAddr` produced by `parseHybridScopedNumericZone?` satisfies `allowsSymbolicIpv6Zone baseAddr = true`. -/
theorem allowsSymbolicIpv6Zone_of_parseHybridScopedNumericZone {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hH : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    allowsSymbolicIpv6Zone baseAddr = true := by
  unfold parseHybridScopedNumericZone? at hH
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hH
    split at hH
    · contradiction
    · cases h6 : Internal.parseIpv6SplitZone? host with
      | none => simp [h6] at hH
      | some p =>
        rcases p with ⟨mk, z?⟩
        cases z? with
        | none => simp [h6] at hH
        | some zoneCs =>
          simp only [h6] at hH
          by_cases hlen : zoneCs.length < 16
          · simp only [hlen, ↓reduceIte] at hH
            split at hH
            · rename_i bAddr scVal _ _
              by_cases hAl : allowsSymbolicIpv6Zone bAddr = true
              · simp only [hAl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hH
                rw [← hH.1]
                exact hAl
              · simp [hAl] at hH
            · contradiction
          · simp [hlen] at hH
  · simp [hne] at hH

private theorem wordsToIpv6Addr_allowsSymbolic {ws : List Nat} {sc1 sc2 : UInt32} {a1 a2 : DnsAddr}
    (h1 : Internal.wordsToIpv6Addr ws sc1 = some a1) (h2 : Internal.wordsToIpv6Addr ws sc2 = some a2) :
    allowsSymbolicIpv6Zone a1 = allowsSymbolicIpv6Zone a2 := by
  cases ws with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w0 ws1 =>
  cases ws1 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w1 ws2 =>
  cases ws2 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w2 ws3 =>
  cases ws3 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w3 ws4 =>
  cases ws4 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w4 ws5 =>
  cases ws5 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w5 ws6 =>
  cases ws6 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w6 ws7 =>
  cases ws7 with | nil => simp [Internal.wordsToIpv6Addr] at h1 | cons w7 ws8 =>
  cases ws8 with
  | cons _ _ => simp [Internal.wordsToIpv6Addr] at h1
  | nil =>
    simp only [Internal.wordsToIpv6Addr, Option.some.injEq] at h1 h2
    subst h1; subst h2
    rfl

private theorem parseIpv6Core_exists_words {addrCs : List Char} {mkFn : UInt32 → Option DnsAddr}
    (h : Internal.parseIpv6Core? addrCs = some mkFn) :
    ∃ ws : List Nat, mkFn = Internal.wordsToIpv6Addr ws := by
  unfold Internal.parseIpv6Core? at h
  by_cases hBad : (addrCs.isEmpty || decide (addrCs.length > 64)) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Bind.bind, Option.bind] at h
    split at h
    · split at h
      · contradiction
      · rename_i ws _
        by_cases hne8 : (ws.length != 8) = true
        · simp [hne8] at h
        · simp only [hne8, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
          exact ⟨ws, h.symm⟩
    · split at h
      · contradiction
      · rename_i lhs _
        dsimp only at h
        split at h
        · contradiction
        · rename_i rhs _
          dsimp only at h
          by_cases hge : lhs.length + rhs.length ≥ 8
          · simp [hge] at h
          · simp only [hge, ↓reduceIte, Option.some.injEq] at h
            exact ⟨lhs ++ List.replicate (8 - (lhs.length + rhs.length)) 0 ++ rhs, h.symm⟩
    · contradiction

/-- `parsePureNumericAddr?` and `parseHybridScopedNumericZone?` are mutually exclusive: every hybrid numeric-scoped literal yields `parsePureNumericAddr? host = none`. -/
theorem parsePureNumericAddr_none_of_parseHybridScopedNumericZone
    {host : String} {baseAddr : DnsAddr} {sc : UInt32}
    (hHyb : parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    parsePureNumericAddr? host = none := by
  unfold parseHybridScopedNumericZone? at hHyb
  unfold parsePureNumericAddr?
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hHyb ⊢
    split at hHyb
    · contradiction
    · cases h6 : Internal.parseIpv6SplitZone? host with
      | none => simp [h6] at hHyb
      | some p =>
        rcases p with ⟨mk, z?⟩
        cases z? with
        | none => simp [h6] at hHyb
        | some zoneCs =>
          simp only [h6] at hHyb ⊢
          by_cases hlen : zoneCs.length < 16
          · simp only [hlen, ↓reduceIte] at hHyb
            split at hHyb
            · rename_i bAddr scVal hm0 hn
              simp only [hn]
              by_cases hAl : allowsSymbolicIpv6Zone bAddr = true
              · simp only [hAl, ↓reduceIte] at hHyb
                cases hms : mk scVal with
                | none => rfl
                | some addrSc =>
                  dsimp only
                  unfold Internal.parseIpv6SplitZone? at h6
                  split at h6
                  split at h6
                  · contradiction
                  · rename_i mkFn hCore
                    have hMkEq : mkFn = mk := by
                      simp only [Option.some.injEq, Prod.mk.injEq] at h6
                      exact h6.1
                    subst hMkEq
                    rcases parseIpv6Core_exists_words hCore with ⟨ws, hWs⟩
                    rw [hWs] at hm0 hms
                    have hEqAl := wordsToIpv6Addr_allowsSymbolic hm0 hms
                    rw [← hEqAl]
                    simp [hAl, hlen]
              · simp [hAl] at hHyb
            · contradiction
          · simp [hlen] at hHyb
  · simp [hne] at hHyb

/-- Every non-numeric host (`isNumericHostLiteral host = false`) returns `none` under `parsePureNumericAddr?`. -/
theorem parsePureNumericAddr_none_of_not_numericLiteral {host : String}
    (hNonNum : isNumericHostLiteral host = false) :
    parsePureNumericAddr? host = none := by
  unfold isNumericHostLiteral at hNonNum
  unfold parsePureNumericAddr?
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.true_and, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hNonNum
    simp [hne, hNonNum.1, hNonNum.2]
  · have hneF : Internal.isNonEmptyNoNulHost host = false := Bool.eq_false_iff.mpr hne
    simp [hneF]

/-- Every non-numeric host (`isNumericHostLiteral host = false`) returns `none` under `parseHybridScopedNumericZone?`. -/
theorem parseHybridScopedNumericZone_none_of_not_numericLiteral {host : String}
    (hNonNum : isNumericHostLiteral host = false) :
    parseHybridScopedNumericZone? host = none := by
  unfold isNumericHostLiteral at hNonNum
  unfold parseHybridScopedNumericZone?
  by_cases hne : Internal.isNonEmptyNoNulHost host = true
  · simp only [hne, Bool.true_and, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hNonNum
    simp [hne, hNonNum.1, hNonNum.2]
  · have hneF : Internal.isNonEmptyNoNulHost host = false := Bool.eq_false_iff.mpr hne
    simp [hneF]

end LeanSwe.LinuxSyscall.Dns

namespace LeanSwe.LinuxSyscall.Dns.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- Little-endian 4-byte list encoding of a 32-bit unsigned integer `v`. -/
def encodeUInt32LEList (v : UInt32) : List UInt8 :=
  let n := v.toNat
  [ UInt8.ofNat (n % 256)
  , UInt8.ofNat ((n / 256) % 256)
  , UInt8.ofNat ((n / 65536) % 256)
  , UInt8.ofNat ((n / 16777216) % 256) ]

/-- Reference list-based decoder for concatenated 21-byte wire DNS records. -/
def decodeRecordsList : List UInt8 → Except DnsError (List DnsAddr)
  | [] => .ok []
  | tag :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: s0 :: s1 :: s2 :: s3 :: rest =>
    if tag == DNS_FAMILY_V4 then
      if b4 == 0 && b5 == 0 && b6 == 0 && b7 == 0 && b8 == 0 && b9 == 0 &&
          b10 == 0 && b11 == 0 && b12 == 0 && b13 == 0 && b14 == 0 && b15 == 0 &&
          s0 == 0 && s1 == 0 && s2 == 0 && s3 == 0 then
        match decodeRecordsList rest with
        | .ok tail => .ok (.ipv4 b0 b1 b2 b3 :: tail)
        | .error e => .error e
      else
        .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
                 message := "non-zero padding or scope in IPv4 DNS record" }
    else if tag == DNS_FAMILY_V6 then
      match decodeRecordsList rest with
      | .ok tail =>
        .ok (.ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 (decodeUInt32LE s0 s1 s2 s3) :: tail)
      | .error e => .error e
    else
      .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
               message := s!"invalid DNS record family tag {tag.toNat}" }
  | _ =>
    .error { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
             message := "truncated DNS record payload" }

private theorem decodeUInt32LE_encodeUInt32LE (v : UInt32) :
    decodeUInt32LE
      (UInt8.ofNat (v.toNat % 256))
      (UInt8.ofNat ((v.toNat / 256) % 256))
      (UInt8.ofNat ((v.toNat / 65536) % 256))
      (UInt8.ofNat ((v.toNat / 16777216) % 256)) = v := by
  have hv : v.toNat < 4294967296 := v.toBitVec.isLt
  have hnat :
      (v.toNat % 256) +
        256 * ((v.toNat / 256) % 256 +
          256 * ((v.toNat / 65536) % 256 +
            256 * ((v.toNat / 16777216) % 256))) = v.toNat := by
    omega
  unfold decodeUInt32LE
  simp only [UInt8.toNat_ofNat', Nat.mod_mod]
  rw [hnat, UInt32.ofNat_toNat]

theorem encodeUInt32LEList_decodeUInt32LE (b0 b1 b2 b3 : UInt8) :
    encodeUInt32LEList (decodeUInt32LE b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have hb2 : b2.toNat < 256 := b2.toBitVec.isLt
  have hb3 : b3.toNat < 256 := b3.toBitVec.isLt
  have hsum : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) < 4294967296 := by
    omega
  have hto : (decodeUInt32LE b0 b1 b2 b3).toNat =
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
    unfold decodeUInt32LE
    exact Nat.mod_eq_of_lt hsum
  unfold encodeUInt32LEList
  rw [hto]
  have h0 : (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) % 256 = b0.toNat := by omega
  have h1 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 256) % 256 = b1.toNat := by omega
  have h2 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 65536) % 256 = b2.toNat := by omega
  have h3 : ((b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) / 16777216) % 256 = b3.toNat := by omega
  simp only [h0, h1, h2, h3, UInt8.ofNat_toNat]

private theorem wireAddrBytes_length (a : DnsAddr) :
    (wireAddrBytes a).length = DNS_RECORD_SIZE := by
  cases a <;> rfl

private theorem flatMap_wireAddrBytes_length (addrs : List DnsAddr) :
    (addrs.flatMap wireAddrBytes).length = addrs.length * DNS_RECORD_SIZE := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, wireAddrBytes_length, ih, List.length_cons,
      DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE]
    omega

/-- `encodeRecords addrs` has exact byte size `addrs.length * DNS_RECORD_SIZE` (`21` bytes per record). -/
theorem encodeRecords_size (addrs : List DnsAddr) :
    (encodeRecords addrs).size = addrs.length * DNS_RECORD_SIZE := by
  rw [ByteArray.size, ← Array.length_toList, encodeWireRecords_data_toList, flatMap_wireAddrBytes_length]

private theorem decodeRecordsList_short :
    ∀ (xs : List UInt8), xs ≠ [] → xs.length < 21 →
      decodeRecordsList xs = .error
        { kind := .otherGai, gaiCode := EAI_OVERFLOW, errno? := none,
          message := "truncated DNS record payload" }
  | [], hne, _ => absurd rfl hne
  | [_], _, _ | [_, _], _, _ | [_, _, _], _, _ | [_, _, _, _], _, _ | [_, _, _, _, _], _, _
  | [_, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, hlt => by
    simp at hlt
    omega

private theorem drop_21_eq (xs : List UInt8) (idx : Nat) (h : idx + 21 ≤ xs.length) :
    xs.drop idx =
      xs[idx] :: xs[idx + 1] :: xs[idx + 2] :: xs[idx + 3] :: xs[idx + 4] ::
      xs[idx + 5] :: xs[idx + 6] :: xs[idx + 7] :: xs[idx + 8] :: xs[idx + 9] ::
      xs[idx + 10] :: xs[idx + 11] :: xs[idx + 12] :: xs[idx + 13] :: xs[idx + 14] ::
      xs[idx + 15] :: xs[idx + 16] :: xs[idx + 17] :: xs[idx + 18] :: xs[idx + 19] ::
      xs[idx + 20] :: xs.drop (idx + 21) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_getElem_cons (by omega)]

private theorem byte_get_eq_toList (bytes : ByteArray) (i : Nat) (h : i < bytes.size) :
    bytes[i] = bytes.data.toList[i]'(by rw [Array.length_toList]; exact h) :=
  rfl

private theorem decodeRecordsLoop_eq_aux (bytes : ByteArray) :
    ∀ (n idx : Nat) (acc : List DnsAddr),
      idx ≤ bytes.size →
      bytes.size - idx = n →
      decodeRecordsLoop bytes idx acc =
        match decodeRecordsList (bytes.data.toList.drop idx) with
        | .ok xs => .ok (acc.reverse ++ xs)
        | .error e => .error e := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro idx acc hle hrem
    unfold decodeRecordsLoop
    by_cases hEnd : idx = bytes.size
    · have hbeq : (idx == bytes.size) = true := beq_iff_eq.mpr hEnd
      have hdrop : bytes.data.toList.drop idx = [] := by
        rw [List.drop_eq_nil_iff, Array.length_toList]
        simp only [ByteArray.size] at hEnd
        exact Nat.le_of_eq hEnd.symm
      simp [hbeq, hdrop, decodeRecordsList]
    · have hbeq : (idx == bytes.size) = false := beq_false_of_ne hEnd
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      by_cases hFull : idx + DNS_RECORD_SIZE ≤ bytes.size
      · simp only [hFull, ↓reduceDIte]
        have hlen21 : idx + 21 ≤ bytes.data.toList.length := by
          rw [Array.length_toList, ← ByteArray.size]
          simpa [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] using hFull
        have hdrop := drop_21_eq bytes.data.toList idx hlen21
        rw [hdrop]
        have hih := ih (bytes.size - (idx + DNS_RECORD_SIZE))
          (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) (idx + DNS_RECORD_SIZE)
        unfold decodeRecordAt decodeRecordsList
        simp only [byte_get_eq_toList]
        by_cases h4 : bytes.data.toList[idx]'(by omega) = DNS_FAMILY_V4
        · have ht4 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V4) = true := beq_iff_eq.mpr h4
          simp only [ht4, ↓reduceIte]
          by_cases hpad :
              ((bytes.data.toList[idx + 5]'(by omega) == 0 &&
                bytes.data.toList[idx + 6]'(by omega) == 0 &&
                bytes.data.toList[idx + 7]'(by omega) == 0 &&
                bytes.data.toList[idx + 8]'(by omega) == 0 &&
                bytes.data.toList[idx + 9]'(by omega) == 0 &&
                bytes.data.toList[idx + 10]'(by omega) == 0 &&
                bytes.data.toList[idx + 11]'(by omega) == 0 &&
                bytes.data.toList[idx + 12]'(by omega) == 0 &&
                bytes.data.toList[idx + 13]'(by omega) == 0 &&
                bytes.data.toList[idx + 14]'(by omega) == 0 &&
                bytes.data.toList[idx + 15]'(by omega) == 0 &&
                bytes.data.toList[idx + 16]'(by omega) == 0 &&
                bytes.data.toList[idx + 17]'(by omega) == 0 &&
                bytes.data.toList[idx + 18]'(by omega) == 0 &&
                bytes.data.toList[idx + 19]'(by omega) == 0 &&
                bytes.data.toList[idx + 20]'(by omega) == 0) = true)
          · simp only [hpad, ↓reduceIte]
            have hrec := hih (acc := DnsAddr.ipv4
              (bytes.data.toList[idx + 1]'(by omega))
              (bytes.data.toList[idx + 2]'(by omega))
              (bytes.data.toList[idx + 3]'(by omega))
              (bytes.data.toList[idx + 4]'(by omega)) :: acc)
              (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) rfl
            simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at hrec ⊢
            rw [hrec]
            cases decodeRecordsList (bytes.data.toList.drop (idx + 21)) with
            | ok tail => simp [List.reverse_cons, List.append_assoc]
            | error e => rfl
          · simp only [hpad, Bool.false_eq_true, ↓reduceIte]
        · have ht4 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V4) = false := beq_false_of_ne h4
          simp only [ht4, Bool.false_eq_true, ↓reduceIte]
          by_cases h6 : bytes.data.toList[idx]'(by omega) = DNS_FAMILY_V6
          · have ht6 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V6) = true := beq_iff_eq.mpr h6
            simp only [ht6, ↓reduceIte]
            have hrec := hih (acc := DnsAddr.ipv6
              (bytes.data.toList[idx + 1]'(by omega))
              (bytes.data.toList[idx + 2]'(by omega))
              (bytes.data.toList[idx + 3]'(by omega))
              (bytes.data.toList[idx + 4]'(by omega))
              (bytes.data.toList[idx + 5]'(by omega))
              (bytes.data.toList[idx + 6]'(by omega))
              (bytes.data.toList[idx + 7]'(by omega))
              (bytes.data.toList[idx + 8]'(by omega))
              (bytes.data.toList[idx + 9]'(by omega))
              (bytes.data.toList[idx + 10]'(by omega))
              (bytes.data.toList[idx + 11]'(by omega))
              (bytes.data.toList[idx + 12]'(by omega))
              (bytes.data.toList[idx + 13]'(by omega))
              (bytes.data.toList[idx + 14]'(by omega))
              (bytes.data.toList[idx + 15]'(by omega))
              (bytes.data.toList[idx + 16]'(by omega))
              (decodeUInt32LE
                (bytes.data.toList[idx + 17]'(by omega))
                (bytes.data.toList[idx + 18]'(by omega))
                (bytes.data.toList[idx + 19]'(by omega))
                (bytes.data.toList[idx + 20]'(by omega))) :: acc)
              (by simp [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at *; omega) rfl
            simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE] at hrec ⊢
            rw [hrec]
            cases decodeRecordsList (bytes.data.toList.drop (idx + 21)) with
            | ok tail => simp [List.reverse_cons, List.append_assoc]
            | error e => rfl
          · have ht6 : (bytes.data.toList[idx]'(by omega) == DNS_FAMILY_V6) = false := beq_false_of_ne h6
            simp only [ht6, Bool.false_eq_true, ↓reduceIte]
      · simp only [hFull, ↓reduceDIte]
        have hltLen : (bytes.data.toList.drop idx).length < 21 := by
          rw [List.length_drop, Array.length_toList]
          simp only [DNS_RECORD_SIZE, Dns.DNS_RECORD_SIZE, ByteArray.size] at hFull ⊢
          omega
        have hneDrop : bytes.data.toList.drop idx ≠ [] := by
          intro he
          rw [List.drop_eq_nil_iff, Array.length_toList] at he
          simp only [ByteArray.size] at hle hEnd he
          omega
        rw [decodeRecordsList_short _ hneDrop hltLen]

theorem decodeRecords_eq_list (bytes : ByteArray) :
    decodeRecords bytes = decodeRecordsList bytes.data.toList := by
  unfold decodeRecords
  rw [decodeRecordsLoop_eq_aux bytes (bytes.size - 0) 0 [] (Nat.zero_le _) rfl]
  simp only [List.drop_zero, List.reverse_nil, List.nil_append]
  cases decodeRecordsList bytes.data.toList <;> rfl

private theorem decodeRecordsList_wireAddrBytes_append (a : DnsAddr) (tailBytes : List UInt8) :
    decodeRecordsList (wireAddrBytes a ++ tailBytes) =
      match decodeRecordsList tailBytes with
      | .ok tail => .ok (a :: tail)
      | .error e => .error e := by
  cases a with
  | ipv4 b0 b1 b2 b3 => rfl
  | ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    simp only [wireAddrBytes, List.cons_append, List.nil_append]
    conv => lhs; unfold decodeRecordsList
    have ht4 : ((6 : UInt8) == DNS_FAMILY_V4) = false := by decide
    have ht6 : ((6 : UInt8) == DNS_FAMILY_V6) = true := by decide
    simp only [ht4, Bool.false_eq_true, ↓reduceIte, ht6, decodeUInt32LE_encodeUInt32LE]

private theorem decodeRecordsList_flatMap_wireAddrBytes (addrs : List DnsAddr) :
    decodeRecordsList (addrs.flatMap wireAddrBytes) = .ok addrs := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp [List.flatMap_cons, decodeRecordsList_wireAddrBytes_append, ih]

/-- `decodeRecords` cleanly round-trips `encodeRecords` for every `List DnsAddr`. -/
theorem decodeRecords_encodeRecords (addrs : List DnsAddr) :
    decodeRecords (encodeRecords addrs) = .ok addrs := by
  rw [decodeRecords_eq_list, encodeWireRecords_data_toList, decodeRecordsList_flatMap_wireAddrBytes]


end LeanSwe.LinuxSyscall.Dns.Internal

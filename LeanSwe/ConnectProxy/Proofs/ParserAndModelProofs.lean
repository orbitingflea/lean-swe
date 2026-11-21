import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.SpecTests

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

private theorem nonEmpty_append_left {a b : String} (ha : a ≠ "") : a ++ b ≠ "" :=
  fun h => ha (String.append_eq_empty_iff.mp h).1

local macro "solve_invalid_input" : tactic =>
  `(tactic| exact ⟨rfl, by
    dsimp only [ToString.toString]
    repeat (first | apply nonEmpty_append_left | decide)⟩)

private theorem bool_not_of_ne_true {b : Bool} (h : ¬b = true) : (!b) = true := by
  cases b <;> simp_all

private theorem bool_false_of_not_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

private theorem bool_ne_true_of_not_true {b : Bool} (h : (!b) = true) : ¬b = true := by
  cases b <;> simp_all

private theorem not_contains_of_not_mem {xs : List Char} {c : Char} (h : c ∉ xs) :
    xs.contains c = false :=
  Bool.eq_false_iff.mpr fun hm => h (List.contains_iff_mem.mp hm)

private theorem not_mem_of_not_contains {xs : List Char} {c : Char} (h : ¬xs.contains c = true) :
    c ∉ xs :=
  fun hm => h (List.contains_iff_mem.mpr hm)

private theorem mem_of_mem_dropLast {α : Type} : ∀ {xs : List α} {x : α}, x ∈ xs.dropLast → x ∈ xs
  | [], _, h => nomatch h
  | [_], _, h => nomatch h
  | a :: b :: rest, x, h => by
    simp only [List.dropLast] at h
    rcases List.mem_cons.mp h with rfl | htl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_of_mem_dropLast htl)

private theorem list_map_eq_self_of_forall {α : Type} (f : α → α) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.map]
    rw [h x List.mem_cons_self, list_map_eq_self_of_forall f rest (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem exists_mem_splitOnCharAux_of_mem_acc (sep : Char) :
    ∀ (acc cs : List Char) {x : Char}, x ∈ acc →
      ∃ seg ∈ splitOnCharAux sep acc cs, x ∈ seg
  | acc, [], _, hx => ⟨acc.reverse, by simp [splitOnCharAux], List.mem_reverse.mpr hx⟩
  | acc, c :: rest, x, hx => by
    simp only [splitOnCharAux]
    by_cases hc : c == sep
    · simp only [hc, ↓reduceIte]
      exact ⟨acc.reverse, List.mem_cons_self, List.mem_reverse.mpr hx⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact exists_mem_splitOnCharAux_of_mem_acc sep (c :: acc) rest (List.mem_cons_of_mem c hx)

private theorem exists_mem_splitOnCharAux_of_mem (sep : Char) :
    ∀ (acc cs : List Char) {x : Char}, x ∈ cs → x ≠ sep →
      ∃ seg ∈ splitOnCharAux sep acc cs, x ∈ seg
  | _, [], _, hx, _ => nomatch hx
  | acc, c :: rest, x, hx, hne => by
    simp only [splitOnCharAux]
    rcases List.mem_cons.mp hx with rfl | hrest
    · have hfalse : (x == sep) = false := beq_false_of_ne hne
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      exact exists_mem_splitOnCharAux_of_mem_acc sep (x :: acc) rest List.mem_cons_self
    · by_cases hc : c == sep
      · simp only [hc, ↓reduceIte]
        rcases exists_mem_splitOnCharAux_of_mem sep [] rest hrest hne with ⟨seg, hseg, hmem⟩
        exact ⟨seg, List.mem_cons_of_mem _ hseg, hmem⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact exists_mem_splitOnCharAux_of_mem sep (c :: acc) rest hrest hne

private theorem mem_splitOnChar_of_mem {sep : Char} {cs : List Char} {x : Char}
    (hx : x ∈ cs) (hne : x ≠ sep) : ∃ seg ∈ splitOnChar sep cs, x ∈ seg :=
  exists_mem_splitOnCharAux_of_mem sep [] cs hx hne

private theorem char_le_iff_toNat {a b : Char} :
    decide (a ≤ b) = true ↔ a.val.toNat ≤ b.val.toNat := by
  rw [decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le]

private theorem toAsciiLowerChar_eq_self_of_dnsChar {c : Char}
    (h : (('a' ≤ c && c ≤ 'z') || isAsciiDigit c || c == '-') = true) :
    toAsciiLowerChar c = c := by
  unfold toAsciiLowerChar
  split
  · rename_i hAZ
    exfalso
    simp only [Bool.and_eq_true, Bool.or_eq_true, isAsciiDigit, beq_iff_eq, char_le_iff_toNat] at hAZ h
    have hA : 65 ≤ c.val.toNat := hAZ.1
    have hZ : c.val.toNat ≤ 90 := hAZ.2
    rcases h with (⟨ha, _⟩ | ⟨_, h9⟩) | rfl
    · have : 97 ≤ c.val.toNat := ha; omega
    · have : c.val.toNat ≤ 57 := h9; omega
    · exact absurd hA (by decide)
  · rfl

private theorem dnsChar_of_validLabels {cs : List Char}
    (hLabels : (splitOnChar '.' cs).all isValidDnsLabel = true)
    {c : Char} (hc : c ∈ cs) (hNotDot : c ≠ '.') :
    (('a' ≤ c && c ≤ 'z') || isAsciiDigit c || c == '-') = true := by
  rcases mem_splitOnChar_of_mem hc hNotDot with ⟨seg, hSegMem, hCMem⟩
  have hSegValid : isValidDnsLabel seg = true := List.all_eq_true.mp hLabels seg hSegMem
  unfold isValidDnsLabel at hSegValid
  simp only [Bool.and_eq_true] at hSegValid
  exact List.all_eq_true.mp hSegValid.2 c hCMem

private theorem parseDigitsAcc_all_digits (acc : Nat) :
    ∀ (cs : List Char) {n : Nat}, parseDigitsAcc acc cs = some n →
      cs.all isAsciiDigit = true
  | [], _, _ => rfl
  | c :: cs, _, h => by
    unfold parseDigitsAcc at h
    split at h
    · rename_i hc
      simp [hc, parseDigitsAcc_all_digits (acc * 10 + (c.toNat - '0'.toNat)) cs h]
    · cases h

private theorem parseDecNoLeadingZero_numeric {cs : List Char} {maxLen n : Nat}
    (h : parseDecNoLeadingZero cs maxLen = some n) :
    isInetAtonNumericLabel cs = true := by
  unfold parseDecNoLeadingZero at h
  split at h
  · cases h
  · rename_i hEmpty
    split at h
    · cases h
    · have hNotEmpty : cs.isEmpty = false := by
        cases he : cs.isEmpty
        · rfl
        · exact absurd (by simp [he]) hEmpty
      have hDigits := parseDigitsAcc_all_digits 0 cs h
      simp [isInetAtonNumericLabel, hNotEmpty, hDigits]

private theorem parseIpv4Chars_lastLabel_numeric {cs : List Char} {v4 : UInt32}
    (h : parseIpv4Chars cs = some v4) :
    isInetAtonNumericLabel ((splitOnChar '.' cs).getLastD []) = true := by
  unfold parseIpv4Chars at h
  split at h
  · rename_i s0 s1 s2 s3 hSplit
    rw [hSplit]
    split at h
    · rename_i _ _ _ b3 _ _ _ hb3
      exact parseDecNoLeadingZero_numeric hb3
    · cases h
  · cases h

private theorem normalizeTargetHost_err_props {raw : String} {err : ProxyError}
    (h : Model.normalizeTargetHost raw = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.normalizeTargetHost at h
  dsimp only at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · split at h
        · split at h
          · split at h
            · injection h with hEq; subst hEq; solve_invalid_input
            · split at h
              · cases h
              · injection h with hEq; subst hEq; solve_invalid_input
          · injection h with hEq; subst hEq; solve_invalid_input
        · injection h with hEq; subst hEq; solve_invalid_input
      · split at h
        · cases h
        · split at h
          · cases h
          · injection h with hEq; subst hEq; solve_invalid_input

private theorem normalizeTargetHost_ok_no_star {raw normHost : String} {ip? : Option IpAddr}
    (h : Model.normalizeTargetHost raw = .ok (normHost, ip?)) :
    (!normHost.toList.contains '*') = true := by
  unfold Model.normalizeTargetHost at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hNotStar
      have hStarCs : '*' ∉ raw.toList := not_mem_of_not_contains hNotStar
      split at h
      · split at h
        · rename_i innerAndClose hList
          rw [hList] at hStarCs
          split at h
          · split at h
            · cases h
            · split at h
              · injection h with hPair
                injection hPair with hHost _
                subst hHost
                apply bool_not_of_ne_true
                intro hMem
                have hIn := List.contains_iff_mem.mp hMem
                simp only [String.toList_append, List.mem_append] at hIn
                rcases hIn with ((hOpen | hInner) | hClose)
                · simp at hOpen
                · split at hInner
                  · rename_i hCond
                    simp only [Bool.and_eq_true] at hCond
                    exact not_mem_of_not_contains (bool_ne_true_of_not_true hCond.1.1.2) hInner
                  · rw [String.toList_ofList] at hInner
                    exact hStarCs (List.mem_cons_of_mem '[' (mem_of_mem_dropLast hInner))
                · simp at hClose
              · cases h
          · cases h
        · cases h
      · split at h
        · injection h with hPair
          injection hPair with hHost _
          subst hHost
          rw [String.toList_ofList]
          exact bool_not_of_ne_true hNotStar
        · split at h
          · rename_i hDns
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hDns
            injection h with hPair
            injection hPair with hHost _
            subst hHost
            rw [String.toList_ofList]
            apply bool_not_of_ne_true
            intro hMem
            have hValid := dnsChar_of_validLabels hDns.1.2 (List.contains_iff_mem.mp hMem) (by decide)
            revert hValid; decide
          · cases h

private theorem normalizeTargetHost_idempotent {raw normHost : String} {ip? : Option IpAddr}
    (h : Model.normalizeTargetHost raw = .ok (normHost, ip?)) :
    Model.normalizeTargetHost normHost = .ok (normHost, ip?) := by
  unfold Model.normalizeTargetHost at h
  dsimp only at h
  by_cases hEmpty : raw.toList.isEmpty = true
  · simp only [hEmpty, ↓reduceIte] at h; cases h
  · have hEmptyF : raw.toList.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
    simp only [hEmptyF, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hStar : raw.toList.contains '*' = true
    · simp only [hStar, ↓reduceIte] at h; cases h
    · have hStarF : raw.toList.contains '*' = false := Bool.eq_false_iff.mpr hStar
      simp only [hStarF, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hV6Brk : (raw.toList.head? == some '[' || raw.toList.contains ':' || raw.toList.contains ']') = true
      · simp only [hV6Brk, ↓reduceIte] at h
        split at h
        · rename_i innerAndClose hList
          by_cases hLast : (innerAndClose.getLast? == some ']') = true
          · simp only [hLast, ↓reduceIte] at h
            by_cases hBad : (innerAndClose.dropLast.contains '[' || innerAndClose.dropLast.contains ']' ||
                !innerAndClose.dropLast.contains ':') = true
            · simp only [hBad, ↓reduceIte] at h; cases h
            · have hBadF : (innerAndClose.dropLast.contains '[' || innerAndClose.dropLast.contains ']' ||
                  !innerAndClose.dropLast.contains ':') = false := Bool.eq_false_iff.mpr hBad
              simp only [hBadF, Bool.false_eq_true, ↓reduceIte] at h
              cases hV6 : parseIpv6Chars innerAndClose.dropLast with
              | none => simp only [hV6] at h; cases h
              | some pair =>
                rcases pair with ⟨hi, lo⟩
                simp only [hV6] at h
                injection h with hPair
                injection hPair with hHost hIp
                subst hHost; subst hIp
                let canon := formatIpv6Canonical hi lo
                let cond := !canon.toList.contains '[' && !canon.toList.contains ']' &&
                  !canon.toList.contains '*' && canon.toList.contains ':' &&
                  (parseIpv6Chars canon.toList == some (hi, lo))
                let finalInner := if cond then canon else String.ofList innerAndClose.dropLast
                have hProp : (!finalInner.toList.contains '[') = true ∧
                    (!finalInner.toList.contains ']') = true ∧
                    (!finalInner.toList.contains '*') = true ∧
                    finalInner.toList.contains ':' = true ∧
                    parseIpv6Chars finalInner.toList = some (hi, lo) := by
                  dsimp only [finalInner]
                  by_cases hc : cond = true
                  · simp only [hc, ↓reduceIte]
                    simp only [cond, Bool.and_eq_true, beq_iff_eq] at hc
                    exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
                  · have hcF : cond = false := Bool.eq_false_iff.mpr hc
                    simp only [hcF, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
                    simp only [Bool.or_eq_true, not_or] at hBad
                    refine ⟨bool_not_of_ne_true hBad.1.1, bool_not_of_ne_true hBad.1.2, ?_, ?_, hV6⟩
                    · apply bool_not_of_ne_true
                      intro hm
                      exact hStar (List.contains_iff_mem.mpr
                        (by rw [hList]; exact List.mem_cons_of_mem '[' (mem_of_mem_dropLast (List.contains_iff_mem.mp hm))))
                    · by_cases hcol : innerAndClose.dropLast.contains ':' = true
                      · exact hcol
                      · exact absurd (bool_not_of_ne_true hcol) hBad.2
                have hList2 : ("[" ++ finalInner ++ "]").toList = '[' :: (finalInner.toList ++ [']']) := by
                  simp [String.toList_append]
                have hFullNotStar : ("[" ++ finalInner ++ "]").toList.contains '*' = false := by
                  apply not_contains_of_not_mem
                  rw [hList2]
                  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                  rintro (h1 | h2 | h3)
                  · cases h1
                  · exact not_mem_of_not_contains (bool_ne_true_of_not_true hProp.2.2.1) h2
                  · cases h3
                have hNoBrkL : finalInner.toList.contains '[' = false := bool_false_of_not_true hProp.1
                have hNoBrkR : finalInner.toList.contains ']' = false := bool_false_of_not_true hProp.2.1
                have hHasCol : finalInner.toList.contains ':' = true := hProp.2.2.2.1
                have hParse2 : parseIpv6Chars finalInner.toList = some (hi, lo) := hProp.2.2.2.2
                have hFinalEq : ("[" ++ (if cond = true then canon else String.ofList innerAndClose.dropLast) ++ "]") =
                    ("[" ++ finalInner ++ "]") := rfl
                unfold Model.normalizeTargetHost
                dsimp only
                rw [hFinalEq]
                have hFullNonEmpty : ("[" ++ finalInner ++ "]").toList.isEmpty = false := by
                  rw [hList2]; rfl
                have hFullV6Brk : (("[" ++ finalInner ++ "]").toList.head? == some '[' ||
                    ("[" ++ finalInner ++ "]").toList.contains ':' ||
                    ("[" ++ finalInner ++ "]").toList.contains ']') = true := by
                  rw [hList2]; rfl
                rw [hFullNonEmpty, hFullNotStar, hFullV6Brk]
                simp only [Bool.false_eq_true, ↓reduceIte, hList2, List.getLast?_concat,
                  List.dropLast_concat, hNoBrkL, hNoBrkR, hHasCol, Bool.not_true,
                  Bool.or_self, hParse2, beq_self_eq_true]
                by_cases hc : cond = true
                · have hc' : (!canon.toList.contains '[' && !canon.toList.contains ']' &&
                      !canon.toList.contains '*' && canon.toList.contains ':' &&
                      (parseIpv6Chars canon.toList == some (hi, lo))) = true := hc
                  simp only [finalInner, hc, ↓reduceIte]
                  simp only [canon] at hc'
                  simp only [canon, hc', ↓reduceIte]
                · have hc' : (!canon.toList.contains '[' && !canon.toList.contains ']' &&
                      !canon.toList.contains '*' && canon.toList.contains ':' &&
                      (parseIpv6Chars canon.toList == some (hi, lo))) = false :=
                    Bool.eq_false_iff.mpr hc
                  simp only [finalInner, hc, ↓reduceIte, Bool.false_eq_true,
                    String.toList_ofList]
                  simp only [canon] at hc'
                  simp only [hc', Bool.false_eq_true, ↓reduceIte]
          · simp only [Bool.eq_false_iff.mpr hLast, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · cases h
      · have hV6BrkF : (raw.toList.head? == some '[' || raw.toList.contains ':' || raw.toList.contains ']') = false :=
          Bool.eq_false_iff.mpr hV6Brk
        simp only [hV6BrkF, Bool.false_eq_true, ↓reduceIte] at h
        cases hV4 : parseIpv4Chars raw.toList with
        | some v4 =>
          simp only [hV4] at h
          injection h with hPair
          injection hPair with hHost hIp
          subst hHost; subst hIp
          unfold Model.normalizeTargetHost
          dsimp only
          simp only [String.toList_ofList, hEmptyF, hStarF, hV6BrkF, hV4, Bool.false_eq_true, ↓reduceIte]
        | none =>
          simp only [hV4] at h
          by_cases hDns : ((raw.toList.map toAsciiLowerChar).length ≤ 253 &&
              (splitOnChar '.' (raw.toList.map toAsciiLowerChar)).all isValidDnsLabel &&
              !isInetAtonNumericLabel ((splitOnChar '.' (raw.toList.map toAsciiLowerChar)).getLastD [])) = true
          · simp only [hDns, ↓reduceIte] at h
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hDns
            injection h with hPair
            injection hPair with hHost hIp
            subst hHost; subst hIp
            let lower := raw.toList.map toAsciiLowerChar
            have hLowerNonEmpty : lower.isEmpty = false := by
              cases hL : raw.toList with
              | nil => simp [hL] at hEmpty
              | cons _ _ => simp [lower, hL]
            have hCharOk : ∀ c ∈ lower,
                (('a' ≤ c && c ≤ 'z') || isAsciiDigit c || c == '-' || c == '.') = true := by
              intro c hc
              by_cases hd : c == '.'
              · simp [hd]
              · have hD := dnsChar_of_validLabels hDns.1.2 hc (fun he => hd (beq_iff_eq.mpr he))
                simp [hD]
            have hNotContains : ∀ bad : Char,
                (('a' ≤ bad && bad ≤ 'z') || isAsciiDigit bad || bad == '-' || bad == '.') = false →
                lower.contains bad = false := by
              intro bad hBad
              apply not_contains_of_not_mem
              intro hm
              have ht := hCharOk bad hm
              rw [hBad] at ht
              cases ht
            have hNoStar : lower.contains '*' = false := hNotContains '*' (by decide)
            have hNoCol : lower.contains ':' = false := hNotContains ':' (by decide)
            have hNoRBrk : lower.contains ']' = false := hNotContains ']' (by decide)
            have hNotHeadLBrk : (lower.head? == some '[') = false := by
              cases hhd : lower with
              | nil => rfl
              | cons c rest =>
                by_cases hEq : c = '['
                · subst hEq
                  have hm : '[' ∈ lower := by rw [hhd]; exact List.mem_cons_self
                  exact absurd (hCharOk '[' hm) (by decide)
                · simp [beq_false_of_ne hEq]
            have hLowerMap : lower.map toAsciiLowerChar = lower := by
              apply list_map_eq_self_of_forall
              intro c hc
              by_cases hd : c == '.'
              · have hce : c = '.' := beq_iff_eq.mp hd
                subst hce; rfl
              · exact toAsciiLowerChar_eq_self_of_dnsChar
                  (dnsChar_of_validLabels hDns.1.2 hc (fun he => hd (beq_iff_eq.mpr he)))
            have hNoV4 : parseIpv4Chars lower = none := by
              cases hv : parseIpv4Chars lower with
              | none => rfl
              | some v4 =>
                exfalso
                have hNum := parseIpv4Chars_lastLabel_numeric hv
                rw [hNum] at hDns
                cases hDns.2
            dsimp only [lower] at hLowerNonEmpty hNoStar hNotHeadLBrk hNoCol hNoRBrk hNoV4 hLowerMap
            unfold Model.normalizeTargetHost
            dsimp only
            simp only [String.toList_ofList, hLowerNonEmpty, hNoStar, hNotHeadLBrk, hNoCol, hNoRBrk,
              Bool.or_self, Bool.false_eq_true, ↓reduceIte, hNoV4, hLowerMap, hDns.1.1, hDns.1.2, hDns.2,
              decide_true, Bool.not_false, Bool.and_self]
          · simp only [Bool.eq_false_iff.mpr hDns, Bool.false_eq_true, ↓reduceIte] at h; cases h

private theorem normalizeTargetRule_err_props {r : TargetRule} {err : ProxyError}
    (h : Model.normalizeTargetRule r = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.normalizeTargetRule at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · cases h
    · rename_i hHost
      injection h with hEq; subst hEq
      exact normalizeTargetHost_err_props hHost

private theorem normalizeTargetRule_idempotent {r y : TargetRule}
    (h : Model.normalizeTargetRule r = .ok y) :
    Model.normalizeTargetRule y = .ok y := by
  unfold Model.normalizeTargetRule at h
  split at h
  · cases h
  · rename_i hPort
    split at h
    · rename_i normHost _ hHost
      injection h with hEq; subst hEq
      unfold Model.normalizeTargetRule
      simp only [hPort, Bool.false_eq_true, ↓reduceIte, normalizeTargetHost_idempotent hHost]
    · cases h

private theorem mapExceptList_normalizeTargetRule_err_props :
    ∀ (rs : List TargetRule) {err : ProxyError},
      Model.mapExceptList Model.normalizeTargetRule rs = .error err →
      err.kind = .invalidInput ∧ err.message ≠ ""
  | [], _, h => nomatch h
  | r :: rest, _, h => by
    simp only [Model.mapExceptList, bind, Except.bind] at h
    cases hr : Model.normalizeTargetRule r with
    | error er =>
      rw [hr] at h
      injection h with hEq; subst hEq
      exact normalizeTargetRule_err_props hr
    | ok nr =>
      rw [hr] at h
      dsimp only at h
      cases hRest : Model.mapExceptList Model.normalizeTargetRule rest with
      | error er =>
        rw [hRest] at h
        injection h with hEq; subst hEq
        exact mapExceptList_normalizeTargetRule_err_props rest hRest
      | ok _ =>
        rw [hRest] at h
        cases h

private theorem mapExceptList_normalizeTargetRule_idempotent :
    ∀ (rs ys : List TargetRule),
      Model.mapExceptList Model.normalizeTargetRule rs = .ok ys →
      Model.mapExceptList Model.normalizeTargetRule ys = .ok ys
  | [], ys, h => by
    simp only [Model.mapExceptList] at h
    injection h with hEq; subst hEq
    rfl
  | r :: rest, ys, h => by
    simp only [Model.mapExceptList, bind, Except.bind] at h
    cases hr : Model.normalizeTargetRule r with
    | error er => rw [hr] at h; cases h
    | ok y =>
      rw [hr] at h
      dsimp only at h
      cases hRest : Model.mapExceptList Model.normalizeTargetRule rest with
      | error er => rw [hRest] at h; cases h
      | ok yrest =>
        rw [hRest] at h
        injection h with hEq; subst hEq
        simp only [Model.mapExceptList, bind, Except.bind,
          normalizeTargetRule_idempotent hr,
          mapExceptList_normalizeTargetRule_idempotent rest yrest hRest]

private theorem parseConnectRequest_ok_props {raw : ByteArray} {rule : TargetRule}
    (h : Model.parseConnectRequest raw = .ok rule) :
    rule.port ≠ 0 ∧ (!rule.host.toList.contains '*') = true := by
  unfold Model.parseConnectRequest at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  dsimp only at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  rename_i portNat _
  split at h
  · cases h
  · rename_i hRange
    split at h
    · rename_i normHost _ hHost
      injection h with hEq; subst hEq
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_gt_eq] at hRange
      refine ⟨?_, normalizeTargetHost_ok_no_star hHost⟩
      intro hZero
      have hNat : (UInt16.ofNat portNat).toNat = 0 := congrArg UInt16.toNat hZero
      have hMod : portNat % 65536 = 0 := by simpa [UInt16.toNat_ofNat] using hNat
      rw [Nat.mod_eq_of_lt (by omega)] at hMod
      exact hRange.1 hMod
    · cases h

/-- Every error returned by `Model.parseConnectRequest` has kind `.invalidInput` and a non-empty message. -/
theorem parseConnectRequest_err_props {raw : ByteArray} {err : ProxyError}
    (h : Model.parseConnectRequest raw = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.parseConnectRequest at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · injection h with hEq; subst hEq; solve_invalid_input
      · dsimp only at h
        split at h
        · split at h
          · injection h with hEq; subst hEq; solve_invalid_input
          · split at h
            · injection h with hEq; subst hEq; solve_invalid_input
            · split at h
              · injection h with hEq; subst hEq; solve_invalid_input
              · split at h
                · injection h with hEq; subst hEq; solve_invalid_input
                · split at h
                  · injection h with hEq; subst hEq; solve_invalid_input
                  · split at h
                    · injection h with hEq; subst hEq; solve_invalid_input
                    · split at h
                      · cases h
                      · rename_i hHost
                        injection h with hEq; subst hEq
                        exact normalizeTargetHost_err_props hHost
        · injection h with hEq; subst hEq; solve_invalid_input

/-- Every error returned by `Model.validateConfig` has kind `.invalidInput` and a non-empty message. -/
theorem validateConfig_err_props {cfg : ProxyConfig} {err : ProxyError}
    (h : Model.validateConfig cfg = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.validateConfig at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · injection h with hEq; subst hEq; solve_invalid_input
      · split at h
        · injection h with hEq; subst hEq; solve_invalid_input
        · split at h
          · injection h with hEq; subst hEq; solve_invalid_input
          · split at h
            · injection h with hEq; subst hEq; solve_invalid_input
            · simp only [bind, Except.bind] at h
              split at h
              · rename_i hMap
                injection h with hEq; subst hEq
                exact mapExceptList_normalizeTargetRule_err_props _ hMap
              · cases h

private theorem validateConfig_idempotent {cfg : ProxyConfig} {vcfg : ValidProxyConfig}
    (h : Model.validateConfig cfg = .ok vcfg) :
    Model.validateConfig vcfg.config = .ok vcfg := by
  unfold Model.validateConfig at h
  split at h <;> try cases h
  rename_i h1
  split at h <;> try cases h
  rename_i h2
  split at h <;> try cases h
  rename_i h3
  split at h <;> try cases h
  rename_i h4
  split at h <;> try cases h
  rename_i h5
  split at h <;> try cases h
  rename_i h6
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i normTargets hMap
    injection h with hEq; subst hEq
    unfold Model.validateConfig
    simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
      mapExceptList_normalizeTargetRule_idempotent _ _ hMap]

/-- Structural properties guaranteed whenever `Model.decideConnectHead` returns `.needResolve`. -/
theorem decideConnectHead_needResolve_props {cfg : ProxyConfig} {head : ByteArray}
    {host : String} {port : UInt16} {litIp? : Option IpAddr}
    (h : Model.decideConnectHead cfg head = .needResolve host port litIp?) :
    head.size ≤ cfg.limits.maxHeaderBytes ∧
    Model.parseConnectRequest head = .ok { host := host, port := port } ∧
    Model.matchesAllowedTarget cfg.allowedTargets { host := host, port := port } = true ∧
    Model.literalIpOfHost? host = litIp? := by
  unfold Model.decideConnectHead at h
  split at h
  · cases h
  · rename_i hNotOver
    have hSize : head.size ≤ cfg.limits.maxHeaderBytes := Nat.le_of_not_lt hNotOver
    split at h
    · cases h
    · rename_i target hParse
      split at h
      · rename_i hAllowed
        injection h with hHost hPort hLit
        subst hHost; subst hPort; subst hLit
        exact ⟨hSize, hParse, hAllowed, rfl⟩
      · cases h

/-- `authorizeConnect` only produces `.dial plan` for bounded valid `CONNECT` requests matching `allowedTargets`, dialing verified IPs from the literal or resolved snapshot. -/
theorem specOnlyAllowedTargetAndVerifiedIpDialed :
    SpecOnlyAllowedTargetAndVerifiedIpDialed := by
  intro cfg head resolveHost plan hAuth
  unfold Model.authorizeConnect at hAuth
  cases hHead : Model.decideConnectHead cfg head with
  | deny h p r =>
    rw [hHead] at hAuth; cases hAuth
  | needResolve host port litIp? =>
    rw [hHead] at hAuth
    obtain ⟨hSize, hParse, hAllowed, hLitEq⟩ := decideConnectHead_needResolve_props hHead
    cases litIp? with
    | some litIp =>
      cases hAllowLit : Model.allowsIp cfg.ipPolicy litIp with
      | false =>
        simp only [Model.decideResolvedIps, List.filter, hAllowLit] at hAuth
        cases hAuth
      | true =>
        simp only [Model.decideResolvedIps, List.filter, hAllowLit] at hAuth
        injection hAuth with hPlan
        subst hPlan
        refine ⟨hSize, hParse, hAllowed, hAllowLit, ?_, ?_⟩
        · intro ip hip; nomatch hip
        · rw [hLitEq]; exact ⟨rfl, rfl⟩
    | none =>
      dsimp only at hAuth
      cases hRes : resolveHost host with
      | error dnsErr =>
        rw [hRes] at hAuth; cases hAuth
      | ok resolved =>
        rw [hRes] at hAuth
        dsimp only at hAuth
        unfold Model.decideResolvedIps at hAuth
        cases hFiltEq : resolved.toList.filter (Model.allowsIp cfg.ipPolicy) with
        | nil =>
          rw [hFiltEq] at hAuth; cases hAuth
        | cons primary rest =>
          rw [hFiltEq] at hAuth
          dsimp only at hAuth
          injection hAuth with hPlan
          subst hPlan
          have hPrimMem : primary ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
            rw [hFiltEq]; exact List.Mem.head _
          obtain ⟨hPrimIn, hPrimAllow⟩ := List.mem_filter.mp hPrimMem
          refine ⟨hSize, hParse, hAllowed, hPrimAllow, ?_, ?_⟩
          · intro ip hip
            have hRest : ip ∈ rest := by simpa using hip
            have hInFilt : ip ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
              rw [hFiltEq]; exact List.Mem.tail _ hRest
            exact (List.mem_filter.mp hInFilt).2
          · rw [hLitEq]
            refine ⟨resolved, hRes, hPrimIn, ?_⟩
            intro ip hip
            have hRest : ip ∈ rest := by simpa using hip
            have hInFilt : ip ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
              rw [hFiltEq]; exact List.Mem.tail _ hRest
            exact (List.mem_filter.mp hInFilt).1

/-- `AllPass` proof of `test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority` on `defaultApi`. -/
theorem proof_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority :
    Core.AllPass (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority defaultApi) := by
  intro raw
  dsimp [test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority, defaultApi, Internal.mkScopedApiM,
    Core.AllPass, bind, assert]
  refine ⟨rfl, ?_⟩
  cases h : Model.parseConnectRequest raw with
  | ok _ => exact ⟨parseConnectRequest_ok_props h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | error err => exact ⟨parseConnectRequest_err_props h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `CanReach` witness for `test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority` on `defaultApi`. -/
theorem reach_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority :
    Core.CanReach (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority defaultApi) :=
  ⟨ByteArray.empty, proof_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority ByteArray.empty⟩

/-- `AllPass` proof of `test_cproxy_validateConfig_limitsPortZeroAndIdempotence` on `defaultApi`. -/
theorem proof_cproxy_validateConfig_limitsPortZeroAndIdempotence :
    Core.AllPass (test_cproxy_validateConfig_limitsPortZeroAndIdempotence defaultApi) := by
  intro cfg
  dsimp [test_cproxy_validateConfig_limitsPortZeroAndIdempotence, defaultApi, Internal.mkScopedApiM,
    Core.AllPass, bind, assert]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases h : Model.validateConfig cfg with
  | error err => exact ⟨validateConfig_err_props h, trivial⟩
  | ok vcfg => exact ⟨validateConfig_idempotent h, trivial⟩

/-- `CanReach` witness for `test_cproxy_validateConfig_limitsPortZeroAndIdempotence` on `defaultApi`. -/
theorem reach_cproxy_validateConfig_limitsPortZeroAndIdempotence :
    Core.CanReach (test_cproxy_validateConfig_limitsPortZeroAndIdempotence defaultApi) :=
  ⟨{}, proof_cproxy_validateConfig_limitsPortZeroAndIdempotence {}⟩

/-- `AllPass` proof of `test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal` on `Model.authorizeConnect`. -/
theorem proof_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal :
    Core.AllPass (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal Model.authorizeConnect) := by
  dsimp [test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal, Core.AllPass, bind, assert]
  refine ⟨rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, trivial⟩

/-- `CanReach` witness for `test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal` on `Model.authorizeConnect`. -/
theorem reach_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal :
    Core.CanReach (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal Model.authorizeConnect) :=
  proof_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal

/-- `AllPass` proof of `test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly` on `Model.authorizeConnect`. -/
theorem proof_cproxy_model_authorizeConnect_selectsVerifiedIpOnly :
    Core.AllPass (test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly Model.authorizeConnect) := by
  dsimp [test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly, Core.AllPass, bind, assert]
  refine ⟨rfl, ⟨_, rfl⟩, rfl, trivial⟩

/-- `CanReach` witness for `test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly` on `Model.authorizeConnect`. -/
theorem reach_cproxy_model_authorizeConnect_selectsVerifiedIpOnly :
    Core.CanReach (test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly Model.authorizeConnect) :=
  proof_cproxy_model_authorizeConnect_selectsVerifiedIpOnly

end LeanSwe.ConnectProxy.Proofs

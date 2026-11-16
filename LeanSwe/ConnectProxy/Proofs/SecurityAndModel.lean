import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.SpecTests

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Raw
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

private theorem parseConnectRequest_err_props {raw : ByteArray} {err : ProxyError}
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

private theorem validateConfig_err_props {cfg : ProxyConfig} {err : ProxyError}
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

private theorem decideConnectHead_needResolve_props {cfg : ProxyConfig} {head : ByteArray}
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

/-- `AllPass` proof of `test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid` on `defaultApi`. -/
theorem proof_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid :
    Core.AllPass (test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid defaultApi) := by
  intro s
  dsimp [test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_isGlobalIp_completeIanaRfc6890Table, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.mkApiM,
    Core.AllPass, bind, assume, assert] at hAll
  dsimp [test_cproxy_allowsIp_banAlwaysOverridesAllow, defaultApi, Internal.mkApiM,
    Core.CanReach, bind, assume, assert]
  exact ⟨policy, ip, rfl, by decide, by decide, 0, hi, hMatch, (hAll.2.2.2 0 hi hMatch).1, trivial⟩

/-- `AllPass` proof of `test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan` on `defaultApi`. -/
theorem proof_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan :
    Core.AllPass (test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan defaultApi) := by
  intro v4 sub8 subHi sla subLo otherV4 flagsPort suffix32 suffix24 iface suffix40 ban hBan
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.mkApiM,
    Core.AllPass, bind, assume, assert] at hAll
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, defaultApi, Internal.mkApiM,
    Core.CanReach, bind, assume, assert]
  exact ⟨v4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ban, hBan, hAll⟩

/-- `AllPass` proof of `test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority` on `defaultApi`. -/
theorem proof_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority :
    Core.AllPass (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority defaultApi) := by
  intro raw
  dsimp [test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority, defaultApi, Internal.mkApiM,
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
  dsimp [test_cproxy_validateConfig_limitsPortZeroAndIdempotence, defaultApi, Internal.mkApiM,
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

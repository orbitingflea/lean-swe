import LeanSwe.Time.Interface

namespace LeanSwe.Time.Proofs

open Std.Time

private theorem digitChar_isAsciiDigit (n : Nat) :
    Internal.isAsciiDigit (Internal.digitChar n) = true := by
  have hfin : ∀ k : Fin 10, Internal.isAsciiDigit (Internal.digitChar k.val) = true := by decide
  have hm := hfin ⟨n % 10, Nat.mod_lt n (by decide)⟩
  simpa [Internal.digitChar] using hm

private theorem digitChar_ne_dash (n : Nat) :
    (Internal.digitChar n == '-') = false := by
  have hfin : ∀ k : Fin 10, (Internal.digitChar k.val == '-') = false := by decide
  have hm := hfin ⟨n % 10, Nat.mod_lt n (by decide)⟩
  simpa [Internal.digitChar] using hm

private theorem digitVal_digitChar (n : Nat) :
    Internal.digitVal (Internal.digitChar n) = n % 10 := by
  have hfin : ∀ k : Fin 10, Internal.digitVal (Internal.digitChar k.val) = k.val := by decide
  have hm := hfin ⟨n % 10, Nat.mod_lt n (by decide)⟩
  simpa [Internal.digitChar] using hm

private theorem twoDigitsChars_length (n : Nat) :
    (Internal.twoDigitsChars n).length = 2 := rfl

private theorem fourDigitsChars_length (n : Nat) :
    (Internal.fourDigitsChars n).length = 4 := rfl

private theorem nineDigitsChars_length (n : Nat) :
    (Internal.nineDigitsChars n).length = 9 := rfl

/-- Calendar/formatting proof helper `popTwoDigitsNat?_twoDigitsChars`. -/
theorem popTwoDigitsNat?_twoDigitsChars (n : Nat) (hn : n < 100) (rest : List Char) :
    Internal.popTwoDigitsNat? (Internal.twoDigitsChars n ++ rest) = some (n, rest) := by
  simp only [Internal.twoDigitsChars, List.cons_append, List.nil_append,
    Internal.popTwoDigitsNat?, Internal.pop2?, Internal.twoDigitsNat?,
    digitChar_isAsciiDigit, Bool.and_self, ↓reduceIte, digitVal_digitChar]
  congr 2; omega

private theorem popFourDigitsNat?_fourDigitsChars (n : Nat) (hn : n < 10000) (rest : List Char) :
    Internal.popFourDigitsNat? (Internal.fourDigitsChars n ++ rest) = some (n, rest) := by
  simp only [Internal.fourDigitsChars, List.cons_append, List.nil_append,
    Internal.popFourDigitsNat?, Internal.pop2?, Internal.fourDigitsNat?,
    digitChar_isAsciiDigit, Bool.and_self, ↓reduceIte, digitVal_digitChar]
  congr 2; omega

/-- Calendar/formatting proof helper `splitLeadingDigits_nineDigitsChars`. -/
theorem splitLeadingDigits_nineDigitsChars (n : Nat) (tl : List Char)
    (htl : match tl with | [] => True | c :: _ => Internal.isAsciiDigit c = false) :
    Internal.splitLeadingDigits (Internal.nineDigitsChars n ++ tl) =
      (Internal.nineDigitsChars n, tl) := by
  have hhd : ∀ c tl', Internal.isAsciiDigit c = false →
      Internal.splitLeadingDigits (c :: tl') = ([], c :: tl') := by
    intro c tl' hc; simp [Internal.splitLeadingDigits, hc]
  have hbase : Internal.splitLeadingDigits tl = ([], tl) := by
    cases tl with
    | nil => rfl
    | cons c cs => exact hhd c cs htl
  dsimp [Internal.nineDigitsChars]
  simp only [Internal.splitLeadingDigits, digitChar_isAsciiDigit, ↓reduceIte, hbase]

/-- Calendar/formatting proof helper `fracDigitsToNanos9_nineDigitsChars`. -/
theorem fracDigitsToNanos9_nineDigitsChars (n : Nat) (hn : n < 1000000000) :
    Internal.fracDigitsToNanos9 9 0 (Internal.nineDigitsChars n) = n := by
  simp only [Internal.nineDigitsChars, Internal.fracDigitsToNanos9, digitVal_digitChar]
  omega

/-- Calendar/formatting proof helper `parseDateHead_formatUtcDateChars`. -/
theorem parseDateHead_formatUtcDateChars (d : PlainDate)
    (hy0 : 0 ≤ d.year.toInt) (hy1 : d.year.toInt ≤ 9999) (tl : List Char) :
    Internal.parseDateHead (Internal.formatUtcDateChars d ++ tl) = .ok (d, tl) := by
  have hfmt_y : Internal.formatYearChars d.year.toInt = Internal.fourDigitsChars d.year.toInt.toNat := by
    simp [Internal.formatYearChars, hy0, hy1]
  have hhead : Internal.parseDateHead (Internal.formatUtcDateChars d ++ tl) =
      Internal.parseDatePrefix false (Internal.formatUtcDateChars d ++ tl) := by
    dsimp [Internal.formatUtcDateChars]
    rw [hfmt_y]
    dsimp [Internal.fourDigitsChars]
    simp [Internal.parseDateHead, digitChar_ne_dash]
  rw [hhead]
  dsimp [Internal.formatUtcDateChars, Internal.parseDatePrefix]
  rw [hfmt_y]
  simp only [List.append_assoc, List.cons_append]
  rw [popFourDigitsNat?_fourDigitsChars d.year.toInt.toNat (by omega)]
  dsimp only [Internal.pop1?]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hm := d.month.property
  have hd := d.day.property
  rw [popTwoDigitsNat?_twoDigitsChars d.month.val.toNat (by omega)]
  dsimp only [Internal.pop1?]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [popTwoDigitsNat?_twoDigitsChars d.day.val.toNat (by omega)]
  have hm_nat : 1 ≤ d.month.val.toNat ∧ d.month.val.toNat ≤ 12 := by omega
  have hd_nat : 1 ≤ d.day.val.toNat ∧ d.day.val.toNat ≤ 31 := by omega
  dsimp only
  simp only [hm_nat, hd_nat, and_self, dite_true]
  have hy_eq : Year.Offset.ofInt (d.year.toInt.toNat : Int) = d.year := by
    change (d.year.toInt.toNat : Int) = d.year.toInt; omega
  have hm_eq : Month.Ordinal.ofNat d.month.val.toNat hm_nat = d.month := by
    apply Subtype.ext; change (d.month.val.toNat : Int) = d.month.val; omega
  have hd_eq : Day.Ordinal.ofNat d.day.val.toNat hd_nat = d.day := by
    apply Subtype.ext; change (d.day.val.toNat : Int) = d.day.val; omega
  rw [hy_eq, hm_eq, hd_eq]
  simp [PlainDate.ofYearMonthDay?, d.valid]

private theorem parseDatePrefix_err {neg : Bool} {cs : List Char} {e : TimeError}
    (h : Internal.parseDatePrefix neg cs = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" := by
  dsimp [Internal.parseDatePrefix] at h
  cases h4 : Internal.popFourDigitsNat? cs with
  | none => rw [h4] at h; cases h; exact ⟨rfl, by decide⟩
  | some v1 =>
    rcases v1 with ⟨yNat, r1⟩
    rw [h4] at h; dsimp at h
    cases hp1 : Internal.pop1? r1 with
    | none => rw [hp1] at h; cases h; exact ⟨rfl, by decide⟩
    | some v2 =>
      rcases v2 with ⟨s1, r2⟩
      rw [hp1] at h; dsimp at h
      by_cases hs1 : s1 != '-'
      · simp [hs1] at h; cases h; exact ⟨rfl, by decide⟩
      · simp only [hs1, Bool.false_eq_true, ↓reduceIte] at h
        cases hm : Internal.popTwoDigitsNat? r2 with
        | none => rw [hm] at h; cases h; exact ⟨rfl, by decide⟩
        | some v3 =>
          rcases v3 with ⟨mNat, r3⟩
          rw [hm] at h; dsimp at h
          cases hp2 : Internal.pop1? r3 with
          | none => rw [hp2] at h; cases h; exact ⟨rfl, by decide⟩
          | some v4 =>
            rcases v4 with ⟨s2, r4⟩
            rw [hp2] at h; dsimp at h
            by_cases hs2 : s2 != '-'
            · simp [hs2] at h; cases h; exact ⟨rfl, by decide⟩
            · simp only [hs2, Bool.false_eq_true, ↓reduceIte] at h
              cases hd : Internal.popTwoDigitsNat? r4 with
              | none => rw [hd] at h; cases h; exact ⟨rfl, by decide⟩
              | some v5 =>
                rcases v5 with ⟨dNat, r5⟩
                rw [hd] at h; dsimp at h
                by_cases hnz : neg && yNat == 0
                · simp [hnz] at h; cases h; exact ⟨rfl, by decide⟩
                · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at h
                  split at h
                  · split at h
                    · split at h
                      · cases h
                      · cases h; exact ⟨rfl, by decide⟩
                    · cases h; exact ⟨rfl, by decide⟩
                  · cases h; exact ⟨rfl, by decide⟩

private theorem parseDateHead_err {cs : List Char} {e : TimeError}
    (h : Internal.parseDateHead cs = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" := by
  dsimp [Internal.parseDateHead] at h
  cases cs with
  | nil => exact parseDatePrefix_err h
  | cons c rest =>
    dsimp at h
    by_cases hc : c == '-'
    · simp only [hc, ↓reduceIte] at h; exact parseDatePrefix_err h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact parseDatePrefix_err h

private theorem parseOffsetSeconds_err {cs : List Char} {e : TimeError}
    (h : Internal.parseOffsetSeconds cs = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" := by
  dsimp [Internal.parseOffsetSeconds] at h
  cases hp0 : Internal.pop1? cs with
  | none => rw [hp0] at h; cases h; exact ⟨rfl, by decide⟩
  | some v0 =>
    rcases v0 with ⟨z0, r0⟩
    rw [hp0] at h; dsimp at h
    by_cases he : r0.isEmpty
    · simp only [he, ↓reduceIte] at h
      by_cases hz : z0 == 'Z' || z0 == 'z'
      · simp [hz] at h
      · simp [hz] at h; cases h; exact ⟨rfl, by decide⟩
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hs : z0 != '+' && z0 != '-'
      · simp [hs] at h; cases h; exact ⟨rfl, by decide⟩
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
        cases hhh : Internal.popTwoDigitsNat? r0 with
        | none => rw [hhh] at h; cases h; exact ⟨rfl, by decide⟩
        | some v1 =>
          rcases v1 with ⟨oh, r1⟩
          rw [hhh] at h; dsimp at h
          cases hp1 : Internal.pop1? r1 with
          | none => rw [hp1] at h; cases h; exact ⟨rfl, by decide⟩
          | some v2 =>
            rcases v2 with ⟨sep1, r2⟩
            rw [hp1] at h; dsimp at h
            by_cases hc1 : sep1 != ':'
            · simp [hc1] at h; cases h; exact ⟨rfl, by decide⟩
            · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
              cases hmm : Internal.popTwoDigitsNat? r2 with
              | none => rw [hmm] at h; cases h; exact ⟨rfl, by decide⟩
              | some v3 =>
                rcases v3 with ⟨om, r3⟩
                rw [hmm] at h; dsimp at h
                cases h3 : r3 with
                | nil =>
                  rw [h3] at h; dsimp at h
                  by_cases hr : oh ≤ 23 && om ≤ 59
                  · simp [hr] at h
                  · simp [hr] at h; cases h; exact ⟨rfl, by decide⟩
                | cons sep2 r4 =>
                  rw [h3] at h; dsimp at h
                  by_cases hc2 : sep2 != ':'
                  · simp [hc2] at h; cases h; exact ⟨rfl, by decide⟩
                  · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
                    cases hss : Internal.popTwoDigitsNat? r4 with
                    | none => rw [hss] at h; cases h; exact ⟨rfl, by decide⟩
                    | some v4 =>
                      rcases v4 with ⟨os, r5⟩
                      rw [hss] at h
                      cases h4 : r5 with
                      | cons _ _ => rw [h4] at h; cases h; exact ⟨rfl, by decide⟩
                      | nil =>
                        rw [h4] at h; dsimp at h
                        by_cases hr : oh ≤ 23 && om ≤ 59 && os ≤ 59
                        · simp [hr] at h
                        · simp [hr] at h; cases h; exact ⟨rfl, by decide⟩

/-- Calendar/formatting proof helper `parseUtcDate_err`. -/
theorem parseUtcDate_err (raw : String) {e : TimeError}
    (h : Internal.parseUtcDate raw = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" := by
  dsimp [Internal.parseUtcDate, Bind.bind, Except.bind] at h
  cases h1 : Internal.parseDateHead raw.toList with
  | error err =>
    rw [h1] at h; cases h; exact parseDateHead_err h1
  | ok v =>
    rw [h1] at h
    rcases v with ⟨d, rest⟩
    dsimp at h
    cases rest with
    | nil => cases h
    | cons c cs => cases h; exact ⟨rfl, by decide⟩

/-- Calendar/formatting proof helper `parseUtcIso8601_err`. -/
theorem parseUtcIso8601_err (raw : String) {e : TimeError}
    (h : Internal.parseUtcIso8601 raw = .error e) :
    e.kind = .invalidFormat ∧ e.message ≠ "" := by
  dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind] at h
  cases h1 : Internal.parseDateHead raw.toList with
  | error err =>
    rw [h1] at h; cases h; exact parseDateHead_err h1
  | ok v =>
    rw [h1] at h
    rcases v with ⟨date, afterDate⟩
    dsimp at h
    cases hpop1 : Internal.pop1? afterDate with
    | none => rw [hpop1] at h; cases h; exact ⟨rfl, by decide⟩
    | some v0 =>
      rw [hpop1] at h; rcases v0 with ⟨sep, r0⟩; dsimp at h
      by_cases hsep : sep != 'T' && sep != 't'
      · simp [hsep] at h; cases h; exact ⟨rfl, by decide⟩
      · simp only [hsep, Bool.false_eq_true, ↓reduceIte] at h
        cases hpop2 : Internal.popTwoDigitsNat? r0 with
        | none => rw [hpop2] at h; cases h; exact ⟨rfl, by decide⟩
        | some v1 =>
          rw [hpop2] at h; rcases v1 with ⟨hh, r1⟩; dsimp at h
          cases hpop3 : Internal.pop1? r1 with
          | none => rw [hpop3] at h; cases h; exact ⟨rfl, by decide⟩
          | some v2 =>
            rw [hpop3] at h; rcases v2 with ⟨c1, r2⟩; dsimp at h
            by_cases hc1 : c1 != ':'
            · simp [hc1] at h; cases h; exact ⟨rfl, by decide⟩
            · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
              cases hpop4 : Internal.popTwoDigitsNat? r2 with
              | none => rw [hpop4] at h; cases h; exact ⟨rfl, by decide⟩
              | some v3 =>
                rw [hpop4] at h; rcases v3 with ⟨mm, r3⟩; dsimp at h
                cases hpop5 : Internal.pop1? r3 with
                | none => rw [hpop5] at h; cases h; exact ⟨rfl, by decide⟩
                | some v4 =>
                  rw [hpop5] at h; rcases v4 with ⟨c2, r4⟩; dsimp at h
                  by_cases hc2 : c2 != ':'
                  · simp [hc2] at h; cases h; exact ⟨rfl, by decide⟩
                  · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
                    cases hpop6 : Internal.popTwoDigitsNat? r4 with
                    | none => rw [hpop6] at h; cases h; exact ⟨rfl, by decide⟩
                    | some v5 =>
                      rw [hpop6] at h; rcases v5 with ⟨ss, afterSec⟩; dsimp at h
                      by_cases hrange : !(hh ≤ 23 && mm ≤ 59 && ss ≤ 59)
                      · simp [hrange] at h; cases h; exact ⟨rfl, by decide⟩
                      · simp only [hrange, Bool.false_eq_true, ↓reduceIte] at h
                        cases h_as : afterSec with
                        | nil =>
                          rw [h_as] at h; dsimp at h
                          cases hoff : Internal.parseOffsetSeconds [] with
                          | error err => rw [hoff] at h; cases h; exact parseOffsetSeconds_err hoff
                          | ok offSec => rw [hoff] at h; cases h
                        | cons dot fracStart =>
                          rw [h_as] at h; dsimp at h
                          by_cases hdot : dot == '.'
                          · simp only [hdot, ↓reduceIte] at h
                            by_cases hemp : (Internal.splitLeadingDigits fracStart).fst.isEmpty ||
                                (Internal.splitLeadingDigits fracStart).fst.length > 9
                            · simp only [hemp, ↓reduceIte] at h; cases h; exact ⟨rfl, by decide⟩
                            · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at h
                              cases hoff : Internal.parseOffsetSeconds (Internal.splitLeadingDigits fracStart).snd with
                              | error err => rw [hoff] at h; cases h; exact parseOffsetSeconds_err hoff
                              | ok offSec => rw [hoff] at h; cases h
                          · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h
                            cases hoff : Internal.parseOffsetSeconds (dot :: fracStart) with
                            | error err => rw [hoff] at h; cases h; exact parseOffsetSeconds_err hoff
                            | ok offSec => rw [hoff] at h; cases h

end LeanSwe.Time.Proofs

import LeanSwe.Toml.Proofs.ParseWitnessMlStr
import LeanSwe.Toml.Proofs.RenderInjectiveNum

/-!
# Datetime & Unquoted Scalar Parse-to-Render Completeness Witnesses

Constructs `ValueTape` witnesses for `parseDatePart`, `parseTimePart`, `parseOffsetPart`,
`parseDateTimeChars`, `takeUnquotedTokenChars`, and `classifyScalarChars`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem digit_eq_of_val {c1 c2 : Char}
    (h1 : isAsciiDigitModel c1 = true) (h2 : isAsciiDigitModel c2 = true)
    (heq : c1.toNat - '0'.toNat = c2.toNat - '0'.toNat) : c1 = c2 := by
  have b1 : 48 ≤ c1.toNat ∧ c1.toNat ≤ 57 := by
    have p : '0' ≤ c1 ∧ c1 ≤ '9' := by simpa [isAsciiDigitModel] using h1
    exact ⟨UInt32.le_iff_toNat_le.mp p.1, UInt32.le_iff_toNat_le.mp p.2⟩
  have b2 : 48 ≤ c2.toNat ∧ c2.toNat ≤ 57 := by
    have p : '0' ≤ c2 ∧ c2 ≤ '9' := by simpa [isAsciiDigitModel] using h2
    exact ⟨UInt32.le_iff_toNat_le.mp p.1, UInt32.le_iff_toNat_le.mp p.2⟩
  have hz : '0'.toNat = 48 := rfl
  have hc : c1.toNat = c2.toNat := by omega
  rw [← Char.ofNat_toNat c1, ← Char.ofNat_toNat c2, hc]

private theorem digit_lt10 (c : Char) (hc : isAsciiDigitModel c = true) : c.toNat - '0'.toNat < 10 := by
  have h : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigitModel] using hc
  have h9 : c.toNat ≤ 57 := UInt32.le_iff_toNat_le.mp h.2
  have hz : '0'.toNat = 48 := rfl
  omega

private theorem padNatZero_2_of_twoDigits {c1 c2 : Char} {n : Nat}
    (h : twoDigitsNat? c1 c2 = some n) : (padNatZero 2 n).toList = [c1, c2] := by
  unfold twoDigitsNat? at h; split at h <;> try (simp at h; done)
  rename_i hd; injection h with hn; simp only [Bool.and_eq_true] at hd
  have := digit_lt10 c1 hd.1; have := digit_lt10 c2 hd.2; unfold digitVal at hn
  obtain ⟨hp_d, hp_f, hp_l⟩ := padNatZero_props 2 n
  have hlen := hp_l (by decide) (by change n < 100; omega)
  rcases hpl : (padNatZero 2 n).toList with _ | ⟨p1, _ | ⟨p2, _ | _⟩⟩ <;> rw [hpl] at hlen <;> try simp at hlen
  rw [hpl] at hp_d hp_f
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add] at hp_d hp_f
  have := digit_lt10 p1 hp_d.1; have := digit_lt10 p2 hp_d.2
  rw [digit_eq_of_val hp_d.1 hd.1 (by omega), digit_eq_of_val hp_d.2 hd.2 (by omega)]

private theorem padNatZero_4_of_fourDigits {c1 c2 c3 c4 : Char} {y : Nat}
    (h : fourDigitsNat? c1 c2 c3 c4 = some y) : (padNatZero 4 y).toList = [c1, c2, c3, c4] := by
  unfold fourDigitsNat? at h; split at h <;> try (simp at h; done)
  rename_i hd; injection h with hy; simp only [Bool.and_eq_true] at hd
  have := digit_lt10 c1 hd.1.1.1; have := digit_lt10 c2 hd.1.1.2; have := digit_lt10 c3 hd.1.2; have := digit_lt10 c4 hd.2
  unfold digitVal at hy
  obtain ⟨hp_d, hp_f, hp_l⟩ := padNatZero_props 4 y
  have hlen := hp_l (by decide) (by change y < 10000; omega)
  rcases hpl : (padNatZero 4 y).toList with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | _⟩⟩⟩⟩ <;>
    rw [hpl] at hlen <;> try simp at hlen
  rw [hpl] at hp_d hp_f
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add] at hp_d hp_f
  have := digit_lt10 p1 hp_d.1; have := digit_lt10 p2 hp_d.2.1; have := digit_lt10 p3 hp_d.2.2.1; have := digit_lt10 p4 hp_d.2.2.2
  rw [digit_eq_of_val hp_d.1 hd.1.1.1 (by omega), digit_eq_of_val hp_d.2.1 hd.1.1.2 (by omega),
      digit_eq_of_val hp_d.2.2.1 hd.1.2 (by omega), digit_eq_of_val hp_d.2.2.2 hd.2 (by omega)]

theorem parseDatePart_witness {cs rest : List Char} {d : Std.Time.PlainDate}
    (h : parseDatePart cs = .ok (d, rest)) :
    ∃ ds, renderDate d = some ds ∧ cs = ds.toList ++ rest := by
  unfold parseDatePart at h
  split at h
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 rem
    cases hy : fourDigitsNat? y1 y2 y3 y4 <;> rw [hy] at h <;> try (simp at h; done)
    cases hm : twoDigitsNat? m1 m2 <;> rw [hm] at h <;> try (simp at h; done)
    cases hd : twoDigitsNat? d1 d2 <;> rw [hd] at h <;> try (simp at h; done)
    rename_i yv mv dv
    dsimp only at h
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    rename_i hm_ok hd_ok date hcal
    split at h <;> try (simp at h; done)
    rename_i hvd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hfields : date.year.toNat = yv ∧ date.month.val.toNat = mv ∧ date.day.val.toNat = dv := by
      unfold Std.Time.PlainDate.ofYearMonthDay? at hcal
      split at hcal <;> try (simp at hcal; done)
      injection hcal with heq; subst heq; exact ⟨rfl, rfl, rfl⟩
    refine ⟨padNatZero 4 date.year.toNat ++ "-" ++ padNatZero 2 date.month.val.toNat ++ "-" ++
        padNatZero 2 date.day.val.toNat,
      by simp [renderDate, hvd], ?_⟩
    simp [String.toList_append, hfields.1, hfields.2.1, hfields.2.2,
      padNatZero_4_of_fourDigits hy, padNatZero_2_of_twoDigits hm, padNatZero_2_of_twoDigits hd]
  · nomatch h

private theorem takeDigits_witness :
    ∀ (cs acc : List Char),
      ∃ dsTail,
        (takeDigits acc cs).1 = acc.reverse ++ dsTail ∧
        cs = dsTail ++ (takeDigits acc cs).2 ∧
        dsTail.all isAsciiDigitModel = true
  | [], acc => ⟨[], by simp [takeDigits], rfl, rfl⟩
  | c :: rest, acc => by
    unfold takeDigits
    by_cases hd : isAsciiDigit c = true
    · have hdm : isAsciiDigitModel c = true := hd
      simp only [hd, ↓reduceIte]
      obtain ⟨dsTail, h1, h2, h3⟩ := takeDigits_witness rest (c :: acc)
      exact ⟨c :: dsTail, by simpa [List.reverse_cons, List.append_assoc] using h1,
        congrArg (c :: ·) h2, by simp [hdm, h3]⟩
    · simp [hd]

private theorem fracAux_eq_model (k acc : Nat) (ds : List Char) :
    fracDigitsToNanosAux k acc ds = fracDigitsToNanosAuxModel k acc ds := by
  induction k generalizing acc ds with
  | zero => rfl
  | succ k ih =>
    cases ds with
    | nil => exact ih (acc * 10) []
    | cons c r => exact ih (acc * 10 + (c.toNat - '0'.toNat)) r

theorem parseTimePart_witness {cs rest : List Char} {tm : Std.Time.PlainTime}
    (h : parseTimePart cs = .ok (tm, rest)) :
    ∃ fl ts, renderTime tm fl = some ts ∧ cs = ts.toList ++ rest := by
  unfold parseTimePart at h
  split at h
  · rename_i h1 h2 m1 m2 s1 s2 rem
    cases hh : twoDigitsNat? h1 h2 <;> rw [hh] at h <;> try (simp at h; done)
    cases hm : twoDigitsNat? m1 m2 <;> rw [hm] at h <;> try (simp at h; done)
    cases hs : twoDigitsNat? s1 s2 <;> rw [hs] at h <;> try (simp at h; done)
    rename_i hv mv sv
    dsimp only at h
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    rename_i hh_ok mm_ok ss_ok
    cases rem with
    | nil =>
      dsimp only at h
      obtain ⟨htm, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hvt : validTomlTime tm = true := by rw [← htm]; simp [validTomlTime]; exact Int.ofNat_le.mpr ss_ok
      subst htm
      refine ⟨none, padNatZero 2 hv ++ ":" ++ padNatZero 2 mv ++ ":" ++ padNatZero 2 sv, ?_, ?_⟩
      · simp [renderTime, hvt,
          show (Std.Time.Hour.Ordinal.ofNat hv hh_ok).val.toNat = hv from rfl,
          show (Std.Time.Minute.Ordinal.ofNat mv mm_ok).val.toNat = mv from rfl,
          show (Std.Time.Second.Ordinal.ofNat sv _).val.toNat = sv from rfl]; rfl
      · simp [String.toList_append, padNatZero_2_of_twoDigits hh,
          padNatZero_2_of_twoDigits hm, padNatZero_2_of_twoDigits hs]
    | cons c3 r3 =>
      by_cases hdot : c3 = '.'
      · subst hdot
        split at h
        · rename_i r3' heq_dot; obtain ⟨_, rfl⟩ := List.cons.inj heq_dot
          obtain ⟨dsTail, hds_eq, hr3_eq, hall⟩ := takeDigits_witness r3 []
          rcases htk : takeDigits [] r3 with ⟨fracDs, afterFrac⟩
          rw [htk] at hds_eq hr3_eq h; dsimp only at hds_eq hr3_eq h
          simp only [List.reverse_nil, List.nil_append] at hds_eq; subst hds_eq
          split at h
          · nomatch h
          · rename_i hne_f
            obtain ⟨htm, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
            have hvt : validTomlTime tm = true := by rw [← htm]; simp [validTomlTime]; exact Int.ofNat_le.mpr ss_ok
            subst htm
            have hne_str : (!(String.ofList fracDs).isEmpty) = true := by
              cases fracDs with | nil => simp at hne_f | cons _ _ => simp [String.ext_iff]
            have hnano_m : fracDigitsToNanosModel fracDs = fracDigitsToNanos fracDs := by
              simp [fracDigitsToNanosModel, fracDigitsToNanos, fracAux_eq_model]
            refine ⟨some (String.ofList fracDs),
              padNatZero 2 hv ++ ":" ++ padNatZero 2 mv ++ ":" ++ padNatZero 2 sv ++ "." ++ String.ofList fracDs,
              ?_, ?_⟩
            · simp [renderTime, hvt, hne_str, String.toList_ofList, hall, hnano_m,
                show (Std.Time.Hour.Ordinal.ofNat hv hh_ok).val.toNat = hv from rfl,
                show (Std.Time.Minute.Ordinal.ofNat mv mm_ok).val.toNat = mv from rfl,
                show (Std.Time.Second.Ordinal.ofNat sv _).val.toNat = sv from rfl]; rfl
            · simp [String.toList_append, String.toList_ofList, hr3_eq,
                padNatZero_2_of_twoDigits hh, padNatZero_2_of_twoDigits hm, padNatZero_2_of_twoDigits hs]
        · rename_i hnot; exact False.elim (hnot r3 rfl)
      · split at h
        · rename_i fs heq; exact absurd (List.cons.inj heq).1 hdot
        · obtain ⟨htm, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          have hvt : validTomlTime tm = true := by rw [← htm]; simp [validTomlTime]; exact Int.ofNat_le.mpr ss_ok
          subst htm
          refine ⟨none, padNatZero 2 hv ++ ":" ++ padNatZero 2 mv ++ ":" ++ padNatZero 2 sv, ?_, ?_⟩
          · simp [renderTime, hvt,
              show (Std.Time.Hour.Ordinal.ofNat hv hh_ok).val.toNat = hv from rfl,
              show (Std.Time.Minute.Ordinal.ofNat mv mm_ok).val.toNat = mv from rfl,
              show (Std.Time.Second.Ordinal.ofNat sv _).val.toNat = sv from rfl]; rfl
          · simp [String.toList_append, padNatZero_2_of_twoDigits hh,
              padNatZero_2_of_twoDigits hm, padNatZero_2_of_twoDigits hs]
  · nomatch h

theorem parseOffsetPart_witness {cs : List Char} {off : Std.Time.TimeZone.Offset}
    (h : parseOffsetPart cs = .ok off) :
    ∃ st, renderOffset off st = some (String.ofList cs) := by
  unfold parseOffsetPart at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm; exact ⟨.upperZ, by decide⟩
  · obtain rfl := (Except.ok.inj h).symm; exact ⟨.lowerZ, by decide⟩
  · rename_i c1 h1 h2 m1 m2
    split at h <;> try (simp at h; done)
    rename_i hsgn
    cases hh : twoDigitsNat? h1 h2 <;> rw [hh] at h <;> try (simp at h; done)
    cases hm : twoDigitsNat? m1 m2 <;> rw [hm] at h <;> try (simp at h; done)
    rename_i hv mv
    dsimp only at h
    split at h <;> try (simp at h; done)
    rename_i hbounds; simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
    let rawOff := Std.Time.TimeZone.Offset.ofSeconds
      (Std.Time.Second.Offset.ofInt
        (if Int.ofNat (hv * 3600 + mv * 60) == 0 then 0
         else if c1 == '-' then -Int.ofNat (hv * 3600 + mv * 60)
         else Int.ofNat (hv * 3600 + mv * 60)))
    change (if validTomlOffset rawOff then Except.ok rawOff else _) = Except.ok off at h
    cases hvo : validTomlOffset rawOff <;> rw [hvo] at h
    · nomatch h
    · simp only [↓reduceIte, Except.ok.injEq] at h; subst h
      have hph := padNatZero_2_of_twoDigits hh
      have hpm := padNatZero_2_of_twoDigits hm
      by_cases hz : hv * 3600 + mv * 60 = 0
      · have hv0 : hv = 0 := by omega
        have mv0 : mv = 0 := by omega
        subst hv0 mv0
        have h00_h : [h1, h2] = ['0', '0'] := hph.symm
        have h00_m : [m1, m2] = ['0', '0'] := hpm.symm
        obtain ⟨rfl, eh2⟩ := List.cons.inj h00_h; obtain ⟨rfl, _⟩ := List.cons.inj eh2
        obtain ⟨rfl, em2⟩ := List.cons.inj h00_m; obtain ⟨rfl, _⟩ := List.cons.inj em2
        rcases Bool.or_eq_true_iff.mp hsgn with hp | hn
        · have hc1 := eq_of_beq hp; subst hc1; exact ⟨.numeric, by decide⟩
        · have hc1 := eq_of_beq hn; subst hc1; exact ⟨.negZero, by decide⟩
      · refine ⟨.upperZ, ?_⟩
        have htot_ne : Int.ofNat (hv * 3600 + mv * 60) ≠ 0 := by simp; omega
        have hsec_val : rawOff.second.val =
            if c1 == '-' then -Int.ofNat (hv * 3600 + mv * 60) else Int.ofNat (hv * 3600 + mv * 60) := by
          dsimp only [rawOff]
          rw [beq_false_of_ne htot_ne]; rfl
        have hsec_nz : rawOff.second.val ≠ 0 := by
          rw [hsec_val]; split <;> (simp; omega)
        have hnat_abs : rawOff.second.val.natAbs = hv * 3600 + mv * 60 := by
          rw [hsec_val]; split
          · rw [Int.natAbs_neg]; rfl
          · rfl
        simp only [renderOffset, hvo, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          beq_false_of_ne hsec_nz, hnat_abs,
          show (hv * 3600 + mv * 60) / 60 / 60 = hv by omega,
          show ((hv * 3600 + mv * 60) / 60) % 60 = mv by omega, Option.some.injEq]
        rw [hsec_val]
        rcases Bool.or_eq_true_iff.mp hsgn with hp | hn
        · rw [eq_of_beq hp]; simp only [show ('+' == '-') = false from rfl, Bool.false_eq_true, ↓reduceIte]
          have hpos : ¬(Int.ofNat (hv * 3600 + mv * 60) < 0) := by simp; omega
          simp only [hpos, ↓reduceIte]
          apply String.ext_iff.mpr; simp [String.toList_append, hph, hpm]
        · rw [eq_of_beq hn]; simp only [beq_self_eq_true, ↓reduceIte]
          have hneg : (-Int.ofNat (hv * 3600 + mv * 60) < 0) := by simp; omega
          simp only [hneg, ↓reduceIte]
          apply String.ext_iff.mpr; simp [String.toList_append, hph, hpm]
  · nomatch h

theorem parseDateTimeChars_witness {tok : List Char} {v : TomlValue}
    (h : parseDateTimeChars tok = some (.ok v)) :
    ∃ vt, renderValueInline v vt = some (String.ofList tok) := by
  unfold parseDateTimeChars at h
  by_cases hdp : hasDatePrefix tok = true
  · simp only [hdp, ↓reduceIte] at h
    cases hd : parseDatePart tok with
    | error _ => rw [hd] at h; nomatch h
    | ok drem =>
      rw [hd] at h; rcases drem with ⟨date, rem1⟩
      obtain ⟨ds, hds_r, htok_d⟩ := parseDatePart_witness hd
      cases rem1 with
      | nil =>
        simp only [Option.some.injEq, Except.ok.injEq] at h; subst h
        refine ⟨.localDate, ?_⟩
        simp [renderValueInline, hds_r, htok_d, String.ofList_toList]
      | cons sep timeCs =>
        dsimp only at h; split at h <;> try (simp at h; done)
        rename_i hsep
        let sepStyle : DateTimeSep := if sep == 'T' then .upperT else if sep == 't' then .lowerT else .space
        have hsep_l : (renderDateTimeSep sepStyle).toList = [sep] := by
          simp only [Bool.or_eq_true, beq_iff_eq] at hsep
          rcases hsep with (rfl | rfl) | rfl <;> simp [sepStyle, renderDateTimeSep]
        cases ht : parseTimePart timeCs with
        | error _ => rw [ht] at h; nomatch h
        | ok trem =>
          rw [ht] at h; rcases trem with ⟨tm, rem2⟩
          obtain ⟨fl, ts, hts_r, htime_eq⟩ := parseTimePart_witness ht
          cases rem2 with
          | nil =>
            simp only [Option.some.injEq, Except.ok.injEq] at h; subst h
            refine ⟨.localDateTime sepStyle fl, ?_⟩
            simp only [renderValueInline, hds_r, hts_r, Option.bind_eq_bind, Option.bind, Option.some.injEq]
            apply String.ext_iff.mpr
            simp [String.toList_append, hsep_l, htok_d, htime_eq]
          | cons oc ocs =>
            dsimp only at h
            cases ho : parseOffsetPart (oc :: ocs) with
            | error _ => rw [ho] at h; nomatch h
            | ok off =>
              rw [ho] at h; simp only [Option.some.injEq, Except.ok.injEq] at h; subst h
              obtain ⟨ost, host_r⟩ := parseOffsetPart_witness ho
              refine ⟨.offsetDateTime sepStyle ost fl, ?_⟩
              simp only [renderValueInline, hds_r, hts_r, host_r, Option.bind_eq_bind, Option.bind, Option.some.injEq]
              apply String.ext_iff.mpr
              simp [String.toList_append, String.toList_ofList, hsep_l, htok_d, htime_eq]
  · simp only [hdp, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases ht : parseTimePart tok with
      | error _ => rw [ht] at h; nomatch h
      | ok trem =>
        rw [ht] at h; rcases trem with ⟨tm, _ | _⟩
        · simp only [Option.some.injEq, Except.ok.injEq] at h; subst h
          obtain ⟨fl, ts, hts_r, htok_t⟩ := parseTimePart_witness ht
          refine ⟨.localTime fl, ?_⟩
          simp [renderValueInline, hts_r, htok_t, String.ofList_toList]
        · nomatch h
    · split at h <;> nomatch h

private theorem takeNonDelim_witness :
    ∀ (cs acc : List Char),
      ∃ tokTail,
        (takeNonDelim acc cs).1 = acc.reverse ++ tokTail ∧
        cs = tokTail ++ (takeNonDelim acc cs).2 ∧
        (tokTail.all fun c => !isUnquotedDelim c) = true
  | [], acc => ⟨[], by simp [takeNonDelim], rfl, rfl⟩
  | c :: rest, acc => by
    unfold takeNonDelim
    by_cases hdel : isUnquotedDelim c = true
    · simp [hdel]
    · simp only [hdel, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨tokTail, h1, h2, h3⟩ := takeNonDelim_witness rest (c :: acc)
      exact ⟨c :: tokTail, by simpa [List.reverse_cons, List.append_assoc] using h1,
        congrArg (c :: ·) h2, by simp [hdel, h3]⟩

theorem takeUnquotedTokenChars_split (cs : List Char) :
    cs = (takeUnquotedTokenChars cs).1 ++ (takeUnquotedTokenChars cs).2 := by
  have hnd (l : List Char) : l = (takeNonDelim [] l).1 ++ (takeNonDelim [] l).2 := by
    obtain ⟨tt, htt, hl, _⟩ := takeNonDelim_witness l []
    rcases ht : takeNonDelim [] l with ⟨t, a⟩
    rw [ht] at htt hl; dsimp only at htt hl ⊢
    simp only [List.reverse_nil, List.nil_append] at htt; subst htt; exact hl
  unfold takeUnquotedTokenChars
  split
  · split
    · rename_i rest _
      have hr := hnd rest
      rcases ht : takeNonDelim [] rest with ⟨tail, after⟩
      rw [ht] at hr; dsimp only at hr ⊢
      rw [hr]; simp
    · exact hnd _
  · exact hnd cs

private def isIntAllowedChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '_' || c == 'x' || c == 'X' || c == 'o' || c == 'O' || c == 'b' || c == 'B' ||
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private theorem digitVal_nonHex {b : NumBase} {c : Char} {d : Nat}
    (hbh : b ≠ .hex) (hdv : NumParse.Model.digitVal? b c = some d) :
    isIntAllowedChar c = true ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  cases b with
  | hex => exact absurd rfl hbh
  | bin =>
    simp only [NumParse.Model.digitVal?] at hdv
    split at hdv; · rename_i hk; rw [eq_of_beq hk]; decide
    split at hdv; · rename_i hk; rw [eq_of_beq hk]; decide
    nomatch hdv
  | oct =>
    simp only [NumParse.Model.digitVal?] at hdv; split at hdv <;> try (simp at hdv; done)
    rename_i hk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    have hle9 : c ≤ '9' := UInt32.le_trans hk.2 (show '7' ≤ '9' by decide)
    exact ⟨by simp [isIntAllowedChar, hk.1, hle9],
      fun e => by subst e; exact absurd hk (by decide), fun e => by subst e; exact absurd hk (by decide)⟩
  | dec =>
    simp only [NumParse.Model.digitVal?] at hdv; split at hdv <;> try (simp at hdv; done)
    rename_i hk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨by simp [isIntAllowedChar, hk.1, hk.2],
      fun e => by subst e; exact absurd hk (by decide), fun e => by subst e; exact absurd hk (by decide)⟩

private theorem digitVal_any {b : NumBase} {c : Char} {d : Nat}
    (hdv : NumParse.Model.digitVal? b c = some d) : isIntAllowedChar c = true := by
  by_cases hbh : b = .hex
  · subst hbh; simp only [NumParse.Model.digitVal?] at hdv
    split at hdv; · rename_i hk; simp [isIntAllowedChar, hk]
    split at hdv; · rename_i hk; simp [isIntAllowedChar, hk]
    split at hdv; · rename_i hk; simp [isIntAllowedChar, hk]
    nomatch hdv
  · exact (digitVal_nonHex hbh hdv).1

private theorem parseIntModelChars_alphabet {cs : List Char} {m : Int}
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∀ c ∈ cs, isIntAllowedChar c = true) ∧
    (hasUppercaseBasePrefixChars cs = false → (String.ofList cs).startsWith "0x" = false →
      'e' ∉ cs ∧ 'E' ∉ cs) := by
  have dec_char : ∀ b a l n, b ≠ .hex → NumParse.Model.consumeIntDigits b a l = .ok n →
      ∀ c ∈ l, isIntAllowedChar c = true ∧ c ≠ 'e' ∧ c ≠ 'E' := by
    intro b a l n hbh hc
    fun_induction NumParse.Model.consumeIntDigits b a l with
    | case1 => simp
    | case2 _ c rest d hdv ih =>
      exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨digitVal_nonHex hbh hdv, ih hc⟩⟩
    | case3 => nomatch hc
    | case4 => nomatch hc
    | case5 _ c rest _ _ d hdv ih =>
      exact List.forall_mem_cons.mpr ⟨digitVal_nonHex hbh hdv, ih hc⟩
    | case6 => nomatch hc
  have hex_char : ∀ a l n, NumParse.Model.consumeIntDigits .hex a l = .ok n →
      ∀ c ∈ l, isIntAllowedChar c = true := by
    intro a l n hc
    fun_induction NumParse.Model.consumeIntDigits .hex a l with
    | case1 => simp
    | case2 _ c rest d hdv ih =>
      exact List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨digitVal_any hdv, ih hc⟩⟩
    | case3 => nomatch hc
    | case4 => nomatch hc
    | case5 _ c rest _ _ d hdv ih =>
      exact List.forall_mem_cons.mpr ⟨digitVal_any hdv, ih hc⟩
    | case6 => nomatch hc
  have dec_body : ∀ neg l, NumParse.Model.parseDecAfterSign neg l = .ok m →
      ∀ c ∈ l, isIntAllowedChar c = true ∧ c ≠ 'e' ∧ c ≠ 'E' := by
    intro neg l hd
    unfold NumParse.Model.parseDecAfterSign at hd; split at hd <;> try (simp at hd; done)
    · split at hd
      · exact List.forall_mem_singleton.mpr (by decide)
      · repeat (split at hd; all_goals try (simp at hd; done))
    · rename_i c rest _ _; split at hd <;> try (simp at hd; done)
      rename_i d hdv; split at hd <;> try (simp at hd; done)
      rename_i n hn
      exact List.forall_mem_cons.mpr ⟨digitVal_nonHex (by decide) hdv, dec_char .dec d rest n (by decide) hn⟩
  have sign_wrap {s0 : Char} {r0 : List Char} (hs0 : isIntAllowedChar s0 = true ∧ s0 ≠ 'e' ∧ s0 ≠ 'E')
      (hb : ∀ c ∈ r0, isIntAllowedChar c = true ∧ c ≠ 'e' ∧ c ≠ 'E') :
      (∀ c ∈ s0 :: r0, isIntAllowedChar c = true) ∧
      (hasUppercaseBasePrefixChars (s0 :: r0) = false →
        (String.ofList (s0 :: r0)).startsWith "0x" = false → 'e' ∉ s0 :: r0 ∧ 'E' ∉ s0 :: r0) :=
    ⟨List.forall_mem_cons.mpr ⟨hs0.1, fun c hc => (hb c hc).1⟩, fun _ _ =>
      ⟨fun hm => (List.mem_cons.mp hm).elim (fun e => hs0.2.1 e.symm) (fun ht => (hb _ ht).2.1 rfl),
       fun hm => (List.mem_cons.mp hm).elim (fun e => hs0.2.2 e.symm) (fun ht => (hb _ ht).2.2 rfl)⟩⟩
  unfold NumParse.Model.parseIntModelChars at h; split at h
  · nomatch h
  · split at h <;> try (simp at h; done)
    exact sign_wrap (by decide) (dec_body false _ h)
  · split at h <;> try (simp at h; done)
    exact sign_wrap (by decide) (dec_body true _ h)
  · exact sign_wrap (by decide) (dec_body false _ h)
  · exact sign_wrap (by decide) (dec_body true _ h)
  · rename_i _ b rest
    cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h; have hb := dec_body false _ h
      exact ⟨fun c hc => (hb c hc).1, fun _ _ => ⟨fun hm => (hb _ hm).2.1 rfl, fun hm => (hb _ hm).2.2 rfl⟩⟩
    | some base =>
      rw [hbp] at h; dsimp only at h; split at h <;> try (simp at h; done)
      rename_i _ c1 cs1 _
      cases hdv : NumParse.Model.digitVal? base c1 <;> rw [hdv] at h <;> try (simp at h; done)
      rename_i d; dsimp only at h
      cases hn : NumParse.Model.consumeIntDigits base d cs1 <;> rw [hn] at h <;> try (simp at h; done)
      rename_i n
      have hb_al : isIntAllowedChar b = true := by
        unfold NumParse.Model.basePrefix? at hbp; split at hbp <;> first | decide | nomatch hbp
      refine ⟨List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨hb_al,
        List.forall_mem_cons.mpr ⟨digitVal_any hdv, ?_⟩⟩⟩, fun hup hno0x => ?_⟩
      · cases base with
        | hex => exact hex_char d cs1 n hn
        | bin => exact fun c hc => (dec_char .bin d cs1 n (by decide) hn c hc).1
        | oct => exact fun c hc => (dec_char .oct d cs1 n (by decide) hn c hc).1
        | dec => exact fun c hc => (dec_char .dec d cs1 n (by decide) hn c hc).1
      · have hnot_hex : base ≠ .hex := by
          rintro rfl
          have hb_x : b = 'x' ∨ b = 'X' := by unfold NumParse.Model.basePrefix? at hbp; split at hbp <;> simp_all
          rcases hb_x with rfl | rfl
          · have hsw : (String.ofList ('0' :: 'x' :: c1 :: cs1)).startsWith "0x" = true :=
              String.startsWith_string_iff.mpr ⟨c1 :: cs1, by simp [String.toList_ofList]⟩
            rw [hsw] at hno0x; cases hno0x
          · simp [hasUppercaseBasePrefixChars] at hup
        have hb_ne : b ≠ 'e' ∧ b ≠ 'E' := by
          unfold NumParse.Model.basePrefix? at hbp; split at hbp <;> first | decide | nomatch hbp
        have hc1_ne := (digitVal_nonHex hnot_hex hdv).2
        have hcs1 := dec_char base d cs1 n hnot_hex hn
        simp only [List.mem_cons, not_or]
        exact ⟨⟨by decide, hb_ne.1.symm, hc1_ne.1.symm, fun hm => (hcs1 'e' hm).2.1 rfl⟩,
               ⟨by decide, hb_ne.2.symm, hc1_ne.2.symm, fun hm => (hcs1 'E' hm).2.2 rfl⟩⟩
  · have hb := dec_body false _ h
    exact ⟨fun c hc => (hb c hc).1, fun _ _ => ⟨fun hm => (hb _ hm).2.1 rfl, fun hm => (hb _ hm).2.2 rfl⟩⟩

/-- `classifyScalarChars` produces a `ValueTape` rendering to `String.ofList tok`. -/
theorem classifyScalarChars_witness {numApi : NumParseApi} (hnum : ValidNumApi numApi)
    {tok : List Char} {v : TomlValue}
    (h : classifyScalarChars (toCharNumApi numApi) tok = .ok v) :
    ∃ vt, renderValueInline v vt = some (String.ofList tok) := by
  unfold classifyScalarChars at h
  split at h
  · nomatch h
  · obtain rfl := (Except.ok.inj h).symm; exact ⟨.bool, by simp [renderValueInline]⟩
  · obtain rfl := (Except.ok.inj h).symm; exact ⟨.bool, by simp [renderValueInline]⟩
  · cases hdt : parseDateTimeChars tok with
    | some res => rw [hdt] at h; exact parseDateTimeChars_witness (h ▸ hdt)
    | none =>
      rw [hdt] at h; dsimp only at h
      split at h
      · rename_i hflt
        cases hpf : (toCharNumApi numApi).parseFloatChars tok with
        | error _ => rw [hpf] at h; nomatch h
        | ok f =>
          rw [hpf] at h; obtain rfl := (Except.ok.inj h).symm
          let s := String.ofList tok
          have hspec := hnum.parseFloat s
          change numApi.parseFloat s = .ok f at hpf
          rw [hpf] at hspec
          cases hpm : parseFloatModel s with
          | error _ => rw [hpm] at hspec; exact False.elim hspec
          | ok g =>
            rw [hpm] at hspec
            have heqv := floatBitMatch_implies_floatEquiv hspec
            have heqv_b : ((g.isNaN && f.isNaN) || g == f) = true := by
              rcases heqv with ⟨h1, h2⟩ | hb
              · simp [h1, h2]
              · simp [(float_beq_props f g hb).1]
            obtain ⟨_, hfmc⟩ := parseFloatModelChars_propsM s.toList g (by simpa [parseFloatModel] using hpm)
            have hnoTerm : (s.toList.all fun c =>
                !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true :=
              List.all_eq_true.mpr fun c hc => (isFloatModelCharM_props c (hfmc c hc)).2.2.2.1
            have hmark : (s.contains '.' || s.contains 'e' || s.contains 'E' ||
                s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = true := by
              unfold isFloatTokenCandidateChars at hflt
              simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hflt
              rcases hflt with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | ⟨_, (h1 | h1) | h1⟩ <;>
                simp [s, String.contains_char_eq, String.toList_ofList, *]
            refine ⟨.float (some s), ?_⟩
            have hvfl : isValidFloatLex s f = true := by
              unfold isValidFloatLex; rw [hmark, hnoTerm, hpm]; simp [heqv_b]
            simp [renderValueInline, hvfl, s]
      · split at h
        · nomatch h
        · rename_i hno_up
          have hup_f : hasUppercaseBasePrefixChars tok = false := Bool.eq_false_iff.mpr hno_up
          cases hpi : (toCharNumApi numApi).parseInt64Chars tok with
          | error _ => rw [hpi] at h; nomatch h
          | ok n =>
            rw [hpi] at h; obtain rfl := (Except.ok.inj h).symm
            let s := String.ofList tok
            change numApi.parseInt64 s = .ok n at hpi
            have hspec := (hnum.parseInt64 s).1
            rw [hpi] at hspec
            have hp64 : parseInt64Model s = .ok n := by simpa [Except.mapError] using hspec.symm
            have hmi : ∃ mi, parseIntModelChars tok = .ok mi := by
              unfold parseInt64Model parseIntModel at hp64
              rw [String.toList_ofList] at hp64
              cases hc : parseIntModelChars tok with
              | error _ => rw [hc] at hp64; nomatch hp64
              | ok mi => exact ⟨mi, rfl⟩
            rcases hmi with ⟨mi, hmi⟩
            obtain ⟨halph, hno_exp_fn⟩ := parseIntModelChars_alphabet hmi
            have hnoTerm_c : ∀ c, isIntAllowedChar c = true →
                (!c.isWhitespace && c != '#' && c != ',' && c != ']' &&
                  c != '}' && c != '.' && !isDisallowedControl c) = true := by
              have hlt : ∀ x, isIntAllowedChar x = true → x.toNat < 128 := fun x hx => by
                simp only [isIntAllowedChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
                rcases hx with (((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) |
                    ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨_, h2⟩) <;>
                  first | decide | exact Nat.lt_of_le_of_lt (UInt32.le_iff_toNat_le.mp h2) (by decide)
              have hall : (List.range 128).all (fun k =>
                  let x := Char.ofNat k
                  !isIntAllowedChar x || (!x.isWhitespace && x != '#' && x != ',' &&
                    x != ']' && x != '}' && x != '.' && !isDisallowedControl x)) = true := by decide
              intro c hc
              simpa [Char.ofNat_toNat, hc] using List.all_eq_true.mp hall c.toNat (List.mem_range.mpr (hlt c hc))
            have hnoTerm : (s.toList.all fun c =>
                !c.isWhitespace && c != '#' && c != ',' && c != ']' &&
                  c != '}' && c != '.' && !isDisallowedControl c) = true := by
              simp only [s, String.toList_ofList]
              exact List.all_eq_true.mpr fun c hc => hnoTerm_c c (halph c hc)
            have hnoBad : (s.startsWith "0X" || s.startsWith "0O" || s.startsWith "0B" ||
                s.startsWith "+0X" || s.startsWith "+0O" || s.startsWith "+0B" ||
                s.startsWith "-0X" || s.startsWith "-0O" || s.startsWith "-0B") = false := by
              simp only [Bool.or_eq_false_iff]
              have ns (p : String) (hp : ∀ t, p.toList ++ t = tok → False) : s.startsWith p = false :=
                Bool.eq_false_iff.mpr fun hsw =>
                  let ⟨t, ht⟩ := String.startsWith_string_iff.mp hsw; hp t (by simpa [s, String.toList_ofList] using ht)
              exact ⟨⟨⟨⟨⟨⟨⟨⟨ns "0X" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f),
                ns "0O" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "0B" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "+0X" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "+0O" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "+0B" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "-0X" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "-0O" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩,
                ns "-0B" (fun t ht => by simp [← ht, hasUppercaseBasePrefixChars] at hup_f)⟩
            have hnoExp : (if s.startsWith "0x" then true else !(s.contains 'e' || s.contains 'E')) = true := by
              by_cases h0x : s.startsWith "0x" = true
              · simp [h0x]
              · have hne := hno_exp_fn hup_f (Bool.eq_false_iff.mpr h0x)
                simp [Bool.eq_false_iff.mpr h0x, String.contains_char_eq, s, String.toList_ofList, hne.1, hne.2]
            refine ⟨.int (some s), ?_⟩
            have hvil : isValidIntLex s n = true := by unfold isValidIntLex; rw [hnoBad, hnoTerm, hnoExp, hp64]; simp
            simp [renderValueInline, hvil, s]

end LeanSwe.Toml.Proofs

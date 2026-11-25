import LeanSwe.Toml.Proofs.RenderInjectiveScalar

/-!
# Integer & Float Model Lexeme Characterization (`Impl`-Independent)

Proves `Impl`-independent model properties for `isValidIntLex`, `formatInt64Canonical`,
`isValidFloatLex`, `canonicalFloat_isValidFloatLex`, and `floatFormatSpec_isValidFloatLex`,
shared by `RenderInjective`, `ScalarRoundTrip`, and `FormatBridge`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem forall_ascii_decideM (p q : Char → Bool) (hascii : ∀ c, p c = true → c.toNat < 128)
    (hdec : (List.range 128).all (fun n => !p (Char.ofNat n) || q (Char.ofNat n)) = true)
    (c : Char) (hp : p c = true) : q c = true := by
  simpa [Char.ofNat_toNat, hp] using List.all_eq_true.mp hdec c.toNat (List.mem_range.mpr (hascii c hp))

private theorem isAsciiDigitModel_lt128 (c : Char) (h : isAsciiDigitModel c = true) : c.toNat < 128 := by
  have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigitModel] using h
  have := UInt32.le_iff_toNat_le.mp h1.2
  have : '9'.val.toNat = 57 := rfl; have : c.toNat = c.val.toNat := rfl; omega

private def isIntModelCharM (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == '_'

private theorem isIntModelCharM_props (c : Char) (h : isIntModelCharM c = true) :
    c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-' := by
  have hlt : ∀ x, isIntModelCharM x = true → x.toNat < 128 := fun x hx => by
    simp only [isIntModelCharM, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
    rcases hx with (((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | rfl) <;>
      first | decide | (have : x.toNat ≤ 102 := Nat.le_trans h2 (by decide); omega)
  have hq := forall_ascii_decideM isIntModelCharM (fun x => x != ':' && x != '.' && x != '-') hlt (by decide) c h
  simp only [Bool.and_eq_true, bne_iff_ne] at hq
  exact ⟨hq.1.1, hq.1.2, hq.2⟩

private theorem digitVal?_isIntModelCharM (b : NumBase) (c : Char) (d : Nat)
    (h : NumParse.Model.digitVal? b c = some d) : isIntModelCharM c = true := by
  cases b <;> simp only [NumParse.Model.digitVal?] at h
  · repeat (split at h; · rename_i hc; simp only [beq_iff_eq] at hc; subst hc; rfl)
    cases h
  · split at h <;> first
      | (rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
         simp [isIntModelCharM, hc.1, show c ≤ '9' from Nat.le_trans hc.2 (by decide)]; done)
      | cases h
  · split at h <;> first | (rename_i hc; simp [isIntModelCharM, hc]; done) | cases h
  · repeat (split at h; · rename_i hc; simp [isIntModelCharM, hc])
    cases h

private theorem consumeIntDigits_charsM (b : NumBase) (acc : Nat) (cs : List Char) (n : Nat)
    (h : NumParse.Model.consumeIntDigits b acc cs = .ok n) : ∀ c ∈ cs, isIntModelCharM c = true := by
  fun_induction NumParse.Model.consumeIntDigits b acc cs <;> simp_all
  · exact ⟨rfl, digitVal?_isIntModelCharM b _ _ ‹_›⟩
  · exact digitVal?_isIntModelCharM b _ _ ‹_›

private theorem parseDecAfterSign_propsM (neg : Bool) (cs : List Char) (m : Int)
    (h : NumParse.Model.parseDecAfterSign neg cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ isAsciiDigitModel c0 = true) ∧
      (∀ c ∈ cs, c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-') := by
  unfold NumParse.Model.parseDecAfterSign at h; split at h <;> try cases h
  · split at h
    · exact ⟨⟨'0', [], rfl, rfl⟩, fun c hc => by rcases List.mem_singleton.mp hc with rfl; decide⟩
    · repeat (split at h; all_goals try cases h)
  · rename_i c rest _ _; split at h <;> try cases h
    rename_i d hdv; split at h <;> try cases h
    rename_i n hn
    have hd_c : isAsciiDigitModel c = true := by
      simp only [NumParse.Model.digitVal?] at hdv
      split at hdv <;> first | (rename_i hc; exact hc) | cases hdv
    exact ⟨⟨c, rest, rfl, hd_c⟩, fun ch hch => isIntModelCharM_props ch
      ((List.mem_cons.mp hch).elim (fun e => e ▸ digitVal?_isIntModelCharM .dec c d hdv)
        (consumeIntDigits_charsM .dec d rest n hn ch))⟩

/-- Character-level invariants for any token accepted by `NumParse.Model.parseIntModelChars`. -/
theorem parseIntModelChars_propsM (cs : List Char) (m : Int)
    (h : NumParse.Model.parseIntModelChars cs = .ok m) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigitModel c0 = true) ∧
      (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigitModel c1 = true)) ∧
    (∀ c ∈ cs, c ≠ ':' ∧ c ≠ '.') ∧ (∀ c0 r0, cs = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
  have hsigned (sgn : Char) (neg : Bool) (tail : List Char) (hsgn : sgn = '+' ∨ sgn = '-')
      (hp : NumParse.Model.parseDecAfterSign neg tail = .ok m) :
      (∃ c0 rest, sgn :: tail = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ isAsciiDigitModel c0 = true) ∧
        (∀ c1 r1, (c0 = '+' ∨ c0 = '-') → rest = c1 :: r1 → isAsciiDigitModel c1 = true)) ∧
      (∀ c ∈ sgn :: tail, c ≠ ':' ∧ c ≠ '.') ∧ (∀ c0 r0, sgn :: tail = c0 :: r0 → ∀ c ∈ r0, c ≠ '-') := by
    obtain ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩ := parseDecAfterSign_propsM neg tail m hp
    exact ⟨⟨sgn, tail, rfl, hsgn.elim Or.inl (Or.inr ∘ Or.inl),
        fun c1 r1 _ h1 => by rw [h1] at hdr; injection hdr with hc1 _; exact hc1 ▸ hd_dig⟩,
      List.forall_mem_cons.mpr ⟨by rcases hsgn with rfl | rfl <;> decide, fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩⟩,
      fun _ r0 hcr c hc => by injection hcr with _ hr; subst hr; exact (hchars c hc).2.2⟩
  unfold NumParse.Model.parseIntModelChars at h; split at h
  · cases h
  · split at h <;> first | cases h | exact hsigned '+' false _ (Or.inl rfl) h
  · split at h <;> first | cases h | exact hsigned '-' true _ (Or.inr rfl) h
  · exact hsigned '+' false _ (Or.inl rfl) h
  · exact hsigned '-' true _ (Or.inr rfl) h
  · rename_i _ b rest; cases hbp : NumParse.Model.basePrefix? b with
    | none =>
      rw [hbp] at h; dsimp only at h
      obtain ⟨_, hchars⟩ := parseDecAfterSign_propsM false ('0' :: b :: rest) m h
      exact ⟨⟨'0', b :: rest, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
        fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩,
        fun _ r0 hcr c hc => by injection hcr with _ hr; subst hr; exact (hchars c (List.mem_cons_of_mem _ hc)).2.2⟩
    | some base =>
      rw [hbp] at h; dsimp only at h; split at h <;> try cases h
      rename_i _ c1 cs1 _
      cases hdv : NumParse.Model.digitVal? base c1 with
      | none => simp [hdv] at h
      | some d =>
        rw [hdv] at h; dsimp only at h
        cases hn : NumParse.Model.consumeIntDigits base d cs1 with
        | error => simp [hn] at h
        | ok n =>
          have hb_ne : b ≠ ':' ∧ b ≠ '.' ∧ b ≠ '-' := by
            unfold NumParse.Model.basePrefix? at hbp; split at hbp <;> first | decide | cases hbp
          have hbody : ∀ c ∈ c1 :: cs1, c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-' := List.forall_mem_cons.mpr
            ⟨isIntModelCharM_props c1 (digitVal?_isIntModelCharM base c1 d hdv),
             fun c hc => isIntModelCharM_props c (consumeIntDigits_charsM base d cs1 n hn c hc)⟩
          exact ⟨⟨'0', b :: c1 :: cs1, rfl, Or.inr (Or.inr rfl), fun _ _ hs => by rcases hs with h1 | h1 <;> cases h1⟩,
            List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨⟨hb_ne.1, hb_ne.2.1⟩, fun c hc => ⟨(hbody c hc).1, (hbody c hc).2.1⟩⟩⟩,
            fun _ r0 hcr => by injection hcr with _ hr; subst hr; exact List.forall_mem_cons.mpr ⟨hb_ne.2.2, fun c hc => (hbody c hc).2.2⟩⟩
  · obtain ⟨⟨d0, dr, hdr, hd_dig⟩, hchars⟩ := parseDecAfterSign_propsM false cs m h
    have hne_sgn : d0 ≠ '+' ∧ d0 ≠ '-' :=
      ⟨fun he => by subst he; revert hd_dig; decide, fun he => by subst he; revert hd_dig; decide⟩
    exact ⟨⟨d0, dr, hdr, Or.inr (Or.inr hd_dig), fun _ _ hs _ => hs.elim (absurd · hne_sgn.1) (absurd · hne_sgn.2)⟩,
      fun c hc => ⟨(hchars c hc).1, (hchars c hc).2.1⟩,
      fun _ r0 hcr c hc => by rw [hcr] at hchars; exact (hchars c (List.mem_cons_of_mem _ hc)).2.2⟩

private theorem toString_pos_head (n : Nat) (hn : 0 < n) :
    ∃ d0 ds, (toString n).toList = d0 :: ds ∧ isAsciiDigitModel d0 = true ∧ d0 ≠ '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if h10 : n < 10 then
      have hinfo : (toString n).toList = [Nat.digitChar n] ∧ isAsciiDigitModel (Nat.digitChar n) = true ∧ Nat.digitChar n ≠ '0' := by
        match n with
        | 0 => omega
        | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
        | _ + 10 => omega
      exact ⟨Nat.digitChar n, [], hinfo.1, hinfo.2.1, hinfo.2.2⟩
    else
      obtain ⟨d0, ds, hd_l, hd_d, hd_ne0⟩ := ih (n / 10) (by omega) (by omega)
      have hsp : (toString ((n / 10) * 10 + n % 10)).toList = (toString (n / 10)).toList ++ [Nat.digitChar (n % 10)] := by
        change (Nat.repr ((n / 10) * 10 + n % 10)).toList = _
        simp only [Nat.repr, String.toList_ofList, Nat.toDigits]; rw [Nat.toDigitsCore]
        have hr := Nat.mod_lt n (by decide : 0 < 10)
        simp only [show ((n / 10) * 10 + n % 10) / 10 = n / 10 by omega,
          show ((n / 10) * 10 + n % 10) % 10 = n % 10 by omega, show n / 10 ≠ 0 by omega, ↓reduceIte]
        have hacc : ∀ f m (a : List Char), Nat.toDigitsCore 10 f m a = Nat.toDigitsCore 10 f m [] ++ a := by
          intro f; induction f with
          | zero => simp [Nat.toDigitsCore]
          | succ f ihf =>
            intro m a; rw [Nat.toDigitsCore, Nat.toDigitsCore]; split
            · simp
            · rw [ihf (m / 10) (_ :: a), ihf (m / 10) [_]]; simp [List.append_assoc]
        have hmono : ∀ f1 f2 m, m < f1 → m < f2 → Nat.toDigitsCore 10 f1 m [] = Nat.toDigitsCore 10 f2 m [] := by
          intro f1; induction f1 with
          | zero => omega
          | succ f1' ihf =>
            intro f2 m hf1 hf2; cases f2 with | zero => omega | succ f2' =>
            rw [Nat.toDigitsCore, Nat.toDigitsCore]
            if hdv : m / 10 = 0 then simp [hdv] else
              simp only [hdv, ↓reduceIte]; rw [hacc f1', hacc f2', ihf f2' (m / 10) (by omega) (by omega)]
        rw [hacc, hmono _ (n / 10 + 1) (n / 10) (by omega) (by omega)]
        simp [toString, Nat.repr, String.toList_ofList, Nat.toDigits]
      rw [show (n / 10) * 10 + n % 10 = n by omega, hd_l] at hsp
      exact ⟨d0, ds ++ [Nat.digitChar (n % 10)], hsp, hd_d, hd_ne0⟩

private theorem parseDecAfterSign_toStringM (neg : Bool) (n : Nat) :
    NumParse.Model.parseDecAfterSign neg (toString n).toList =
      .ok (if neg then -Int.ofNat n else Int.ofNat n) := by
  have hdig_val (c) (hc : isAsciiDigitModel c = true) :
      NumParse.Model.digitVal? .dec c = some (c.toNat - '0'.toNat) := by
    have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigitModel] using hc
    simp [NumParse.Model.digitVal?, h1.1, h1.2]
  have hcons_dec : ∀ (acc : Nat) (ds : List Char), ds.all isAsciiDigitModel = true →
      NumParse.Model.consumeIntDigits .dec acc ds = .ok (ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc) := by
    intro acc ds hds; induction ds generalizing acc with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hds
      have hnot_u : c ≠ '_' := by intro heq; subst heq; exact absurd hds.1 (by decide)
      unfold NumParse.Model.consumeIntDigits
      split <;> first | contradiction | (rename_i heq; injection heq with h1 _; exact absurd h1 hnot_u)
                      | (rename_i c1 cs1 _ _ heq; injection heq with h1 h2; subst h1 h2
                         simp only [hdig_val c hds.1, NumParse.Model.NumBase.radix, List.foldl_cons]
                         exact ih (acc * 10 + (c.toNat - '0'.toNat)) hds.2)
  if hn : n = 0 then
    subst hn; rw [show (toString (0 : Nat)).toList = ['0'] from rfl]; simp [NumParse.Model.parseDecAfterSign]
  else
    obtain ⟨d0, ds, hlist, hd0, hne0⟩ := toString_pos_head n (by omega)
    have hp0 := padNatZero_props 0 n
    simp only [padNatZero, Nat.zero_le, ↓reduceIte] at hp0
    obtain ⟨hall, hfold, _⟩ := hp0
    rw [hlist] at hall hfold ⊢
    simp only [List.all_cons, Bool.and_eq_true, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at hall hfold
    have hnot_u : d0 ≠ '_' := by intro heq; subst heq; exact absurd hd0 (by decide)
    unfold NumParse.Model.parseDecAfterSign
    split <;> first | contradiction | (rename_i heq; injection heq with h1 _; first | exact absurd h1 hnot_u | exact absurd h1 hne0)
                    | (rename_i c1 rest1 _ _ _ heq; injection heq with h1 h2; subst h1 h2
                       rw [hdig_val d0 hd0]; dsimp only
                       rw [hcons_dec (d0.toNat - '0'.toNat) ds hall.2, hfold])

/-- Canonical `Int64` decimal formatting satisfies `isValidIntLex`. -/
theorem formatInt64Canonical_isValidIntLex (n : Int64) :
    isValidIntLex (formatInt64Canonical n) n = true := by
  let isCanonChar (c : Char) : Bool := c == '-' || isAsciiDigitModel c
  have hcanon_props : ∀ c, isCanonChar c = true →
      (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && c != '.' &&
        !isDisallowedControl c && c != 'X' && c != 'O' && c != 'B' && c != 'e' && c != 'E') = true :=
    forall_ascii_decideM isCanonChar
      (fun x => !x.isWhitespace && x != '#' && x != ',' && x != ']' && x != '}' && x != '.' &&
        !isDisallowedControl x && x != 'X' && x != 'O' && x != 'B' && x != 'e' && x != 'E')
      (fun c hc => by simp only [isCanonChar, Bool.or_eq_true, beq_iff_eq] at hc; exact hc.elim (fun e => e ▸ by decide) (isAsciiDigitModel_lt128 c))
      (by decide)
  have hstr_neg (k) : (toString (Int.negSucc k)).toList = '-' :: (toString (k + 1)).toList := by
    change (("-" ++ (k + 1).repr) : String).toList = '-' :: (toString (k + 1)).toList; simp [String.toList_append, toString]
  have hd_nat (m : Nat) : (toString m).toList.all isAsciiDigitModel = true := by
    have hp := (padNatZero_props 0 m).1; simpa [padNatZero] using hp
  have honly : ∀ c ∈ (formatInt64Canonical n).toList, isCanonChar c = true := by
    intro c hc; simp only [formatInt64Canonical] at hc; cases hni : n.toInt with
    | ofNat m => rw [hni, show toString (Int.ofNat m) = toString m from rfl] at hc; simp [isCanonChar, List.all_eq_true.mp (hd_nat m) c hc]
    | negSucc k => rw [hni, hstr_neg k] at hc; exact (List.mem_cons.mp hc).elim (fun e => e ▸ rfl) fun hc' => by simp [isCanonChar, List.all_eq_true.mp (hd_nat (k + 1)) c hc']
  have hp_int : NumParse.Model.parseIntModel (formatInt64Canonical n) = .ok n.toInt := by
    simp only [formatInt64Canonical, NumParse.Model.parseIntModel]; cases hni : n.toInt with
    | ofNat m =>
      rw [show toString (Int.ofNat m) = toString m from rfl]; cases m with
      | zero => rw [show (toString (0 : Nat)).toList = ['0'] from rfl]; rfl
      | succ k =>
        obtain ⟨d0, ds, hlist, hd0, hne0⟩ := toString_pos_head (k + 1) (by omega)
        have hd := parseDecAfterSign_toStringM false (k + 1); rw [hlist] at hd ⊢; simp only [Bool.false_eq_true, ↓reduceIte] at hd
        have hnp : d0 ≠ '+' ∧ d0 ≠ '-' := ⟨fun h => by subst h; revert hd0; decide, fun h => by subst h; revert hd0; decide⟩
        unfold NumParse.Model.parseIntModelChars
        split <;> first | contradiction | (rename_i heq; injection heq with h1 _; first | exact absurd h1 hnp.1 | exact absurd h1 hnp.2 | exact absurd h1 hne0) | exact hd
    | negSucc k =>
      rw [hstr_neg k]; obtain ⟨d0, ds, hlist, _, hne0⟩ := toString_pos_head (k + 1) (by omega)
      have hd := parseDecAfterSign_toStringM true (k + 1); rw [hlist] at hd ⊢; simp only [↓reduceIte] at hd
      change NumParse.Model.parseIntModelChars ('-' :: d0 :: ds) = .ok (-Int.ofNat (k + 1)); unfold NumParse.Model.parseIntModelChars
      split <;> first | contradiction | (rename_i heq; cases heq; done) | (rename_i heq; injection heq with _ h2; injection h2 with h3 _; exact absurd h3 hne0)
                      | (rename_i _ _ _ heq; injection heq with _ h2; subst h2; exact hd) | (rename_i _ _ _ _ hne _; exact False.elim (hne (d0 :: ds) rfl))
  have hbounds : NumParse.Model.inInt64Range n.toInt = true := by
    have := Int64.le_toInt n; have := Int64.toInt_le n; have : Int64.maxValue.toInt = 9223372036854775807 := by decide
    rw [NumParse.Model.inInt64Range, decide_eq_true_eq]; simp only [NumParse.Model.int64MinInt, NumParse.Model.int64MaxInt]; omega
  have hp64 : NumParse.Model.parseInt64Model (formatInt64Canonical n) = .ok n := by
    simp [NumParse.Model.parseInt64Model, hp_int, hbounds, Int64.ofInt_toInt]
  have hclean : ((formatInt64Canonical n).toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && c != '.' && !isDisallowedControl c) = true :=
    List.all_eq_true.mpr fun c hc => by have hp := hcanon_props c (honly c hc); simp only [Bool.and_eq_true] at hp ⊢; exact hp.1.1.1.1.1
  have hnot_mem (ch) (hch : ch = 'X' ∨ ch = 'O' ∨ ch = 'B' ∨ ch = 'e' ∨ ch = 'E') : ch ∉ (formatInt64Canonical n).toList := fun hm => by
    have hp := hcanon_props ch (honly ch hm); simp only [Bool.and_eq_true, bne_iff_ne] at hp
    rcases hch with rfl | rfl | rfl | rfl | rfl <;> first | exact hp.1.1.1.1.2 rfl | exact hp.1.1.1.2 rfl | exact hp.1.1.2 rfl | exact hp.1.2 rfl | exact hp.2 rfl
  have hnot_sw (p : String) (ch) (hmem : ch ∈ p.toList) (hch : ch = 'X' ∨ ch = 'O' ∨ ch = 'B') : (formatInt64Canonical n).startsWith p = false := by
    rw [Bool.eq_false_iff]; intro hsw; rcases String.startsWith_string_iff.mp hsw with ⟨t, ht⟩
    exact hnot_mem ch (hch.elim Or.inl fun h => h.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inl)) (by rw [← ht]; exact List.mem_append_left t hmem)
  simp only [isValidIntLex, hp64, hclean, beq_self_eq_true, Bool.not_false, Bool.true_and, Bool.and_true, Bool.or_self,
    hnot_sw "0X" 'X' (by decide) (by decide), hnot_sw "0O" 'O' (by decide) (by decide), hnot_sw "0B" 'B' (by decide) (by decide),
    hnot_sw "+0X" 'X' (by decide) (by decide), hnot_sw "+0O" 'O' (by decide) (by decide), hnot_sw "+0B" 'B' (by decide) (by decide),
    hnot_sw "-0X" 'X' (by decide) (by decide), hnot_sw "-0O" 'O' (by decide) (by decide), hnot_sw "-0B" 'B' (by decide) (by decide)]
  split <;> first | rfl | simp [String.contains, hnot_mem 'e' (by decide), hnot_mem 'E' (by decide)]

/-- Character alphabet accepted by `NumParse.Model.parseFloatModelChars`. -/
def isFloatModelCharM (c : Char) : Bool :=
  c == '+' || c == '-' || c == '.' || c == 'e' || c == 'E' || c == '_' || c == 'i' || c == 'n' || c == 'f' || c == 'a' || isAsciiDigitModel c

theorem isFloatModelCharM_props (c : Char) (h : isFloatModelCharM c = true) :
    c ≠ ':' ∧ c ≠ 'x' ∧ c ≠ 'X' ∧
    (!c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true ∧
    (!isModelDelim c && c != '\r') = true := by
  have hlt : ∀ x, isFloatModelCharM x = true → x.toNat < 128 := fun x hx => by
    simp only [isFloatModelCharM, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hd)
    all_goals first | decide | exact isAsciiDigitModel_lt128 x hd
  have hq := forall_ascii_decideM isFloatModelCharM
    (fun x => x != ':' && x != 'x' && x != 'X' &&
      (!x.isWhitespace && x != '#' && x != ',' && x != ']' && x != '}' && !isDisallowedControl x) &&
      (!isModelDelim x && x != '\r')) hlt (by decide) c h
  rcases Bool.and_eq_true_iff.mp hq with ⟨hq1, hcl2⟩
  rcases Bool.and_eq_true_iff.mp hq1 with ⟨hq2, hcl1⟩
  simp only [Bool.and_eq_true, bne_iff_ne] at hq2
  exact ⟨hq2.1.1, hq2.1.2, hq2.2, hcl1, hcl2⟩

private theorem consumeDecFloatDigits_propsM (acc cnt : Nat) (cs : List Char)
    (m cnt' : Nat) (rest : List Char) (h : NumParse.Model.consumeDecFloatDigits acc cnt cs = .ok (m, cnt', rest)) :
    ∃ pfx, cs = pfx ++ rest ∧ (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigitModel ch = true) := by
  fun_induction NumParse.Model.consumeDecFloatDigits acc cnt cs with
  | case1 => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [← h.2.2], by simp⟩
  | case2 _ _ c cs hd ih => obtain ⟨pfx, hcs, hpfx⟩ := ih h; exact ⟨'_' :: c :: pfx, by simp [hcs], List.forall_mem_cons.mpr ⟨Or.inl rfl, List.forall_mem_cons.mpr ⟨Or.inr hd, hpfx⟩⟩⟩
  | case3 _ _ _ _ => simp at h
  | case4 => simp at h
  | case5 _ _ c cs _ _ hd ih => obtain ⟨pfx, hcs, hpfx⟩ := ih h; exact ⟨c :: pfx, by simp [hcs], List.forall_mem_cons.mpr ⟨Or.inr hd, hpfx⟩⟩
  | case6 _ _ _ _ _ _ _ => simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [← h.2.2], by simp⟩

private theorem parseFloatIntPart_propsM (cs : List Char) (m : Nat) (rest : List Char)
    (h : NumParse.Model.parseFloatIntPart cs = .ok (m, rest)) :
    ∃ pfx d0 ptail, cs = pfx ++ rest ∧ pfx = d0 :: ptail ∧ isAsciiDigitModel d0 = true ∧
      (∀ ch ∈ pfx, ch = '_' ∨ isAsciiDigitModel ch = true) := by
  unfold NumParse.Model.parseFloatIntPart at h; split at h <;> try cases h
  · split at h
    · split at h <;> try cases h
      split at h
      · repeat (split at h; all_goals try cases h)
      · cases h; exact ⟨['0'], '0', [], rfl, rfl, rfl, List.forall_mem_singleton.mpr (Or.inr rfl)⟩
    · cases h; exact ⟨['0'], '0', [], rfl, rfl, rfl, List.forall_mem_singleton.mpr (Or.inr rfl)⟩
  · rename_i c rest' _ _; split at h <;> try cases h
    rename_i hd0; split at h <;> try cases h
    rename_i _ _ rem hc; obtain ⟨pfx, hcs0, hpfx⟩ := consumeDecFloatDigits_propsM _ _ _ _ _ _ hc
    exact ⟨c :: pfx, c, pfx, by simp [hcs0], rfl, hd0, List.forall_mem_cons.mpr ⟨Or.inr hd0, hpfx⟩⟩

private theorem parseFloatExpSuffix_charsM (afterE : List Char) (g : Int → Float) (f : Float)
    (h : (match NumParse.Model.parseFloatExpPart afterE with
      | Except.error k => Except.error k
      | Except.ok (expVal, afterExp) => if afterExp.isEmpty then Except.ok (g expVal) else Except.error NumParseErrorKind.trailingChars) = Except.ok f) :
    ∀ c ∈ afterE, isFloatModelCharM c = true := by
  cases hexp : NumParse.Model.parseFloatExpPart afterE with
  | error => simp [hexp] at h
  | ok res =>
    rcases res with ⟨expVal, afterExp⟩; rw [hexp] at h; dsimp only at h
    cases afterExp with | cons _ _ => simp at h | nil =>
    simp only [NumParse.Model.parseFloatExpPart.eq_def] at hexp; split at hexp <;> try cases hexp
    rename_i c0 r0 _ heq; split at hexp <;> try cases hexp
    rename_i hd0; split at hexp <;> try cases hexp
    rename_i _ _ _ hc; obtain ⟨pfx, hr0, hpfx⟩ := consumeDecFloatDigits_propsM _ _ _ _ _ _ hc
    rw [List.append_nil] at hr0; subst pfx
    have hbody : ∀ ch ∈ c0 :: r0, isFloatModelCharM ch = true := List.forall_mem_cons.mpr
      ⟨by simp [isFloatModelCharM, show isAsciiDigitModel c0 = true from hd0],
       fun ch hch => (hpfx ch hch).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelCharM, hd]⟩
    have hcases : afterE = '+' :: c0 :: r0 ∨ afterE = '-' :: c0 :: r0 ∨ afterE = c0 :: r0 := by
      split at heq <;> dsimp only at heq <;> rw [heq] <;> simp
    rcases hcases with rfl | rfl | rfl <;> first | exact List.forall_mem_cons.mpr ⟨rfl, hbody⟩ | exact hbody

/-- Character-level invariants for any token accepted by `NumParse.Model.parseFloatModelChars`. -/
theorem parseFloatModelChars_propsM (cs : List Char) (f : Float)
    (h : NumParse.Model.parseFloatModelChars cs = .ok f) :
    (∃ c0 rest, cs = c0 :: rest ∧ (c0 = '+' ∨ c0 = '-' ∨ c0 = 'i' ∨ c0 = 'n' ∨ isAsciiDigitModel c0 = true)) ∧
    (∀ c ∈ cs, isFloatModelCharM c = true) := by
  unfold NumParse.Model.parseFloatModelChars at h; split at h
  · cases h
  · split at h; rename_i _ _ _ neg body hsign
    have hcases : cs = '+' :: body ∨ cs = '-' :: body ∨ cs = body := by
      split at hsign <;> (injection hsign with _ hb; subst hb; simp)
    have hbody : (∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigitModel b0 = true)) ∧
        (∀ c ∈ body, isFloatModelCharM c = true) := by
      split at h
      · split at h <;> first | exact ⟨⟨'i', ['n', 'f'], rfl, Or.inl rfl⟩, by decide⟩ | cases h
      · split at h <;> first | exact ⟨⟨'n', ['a', 'n'], rfl, Or.inr (Or.inl rfl)⟩, by decide⟩ | cases h
      · split at h <;> try cases h
        rename_i intVal afterInt hip
        obtain ⟨pfx, d0, ptail, hbody_eq, hpfx_eq, hd0, hpfx_ch⟩ := parseFloatIntPart_propsM body intVal afterInt hip
        have hpfx_fmc : ∀ c ∈ pfx, isFloatModelCharM c = true :=
          fun c hc => (hpfx_ch c hc).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelCharM, hd]
        have hhead : ∃ b0 br, body = b0 :: br ∧ (b0 = 'i' ∨ b0 = 'n' ∨ isAsciiDigitModel b0 = true) :=
          ⟨d0, ptail ++ afterInt, by rw [hbody_eq, hpfx_eq, List.cons_append], Or.inr (Or.inr hd0)⟩
        split at h <;> try cases h
        · rename_i afterDot; split at h <;> try cases h
          rename_i c1 r1 _; split at h <;> try cases h
          rename_i hd1; split at h <;> try cases h
          rename_i _ _ afterFrac hcf
          obtain ⟨fpfx, hr1, hfpfx⟩ := consumeDecFloatDigits_propsM _ _ _ _ _ _ hcf
          have hfpfx_fmc : ∀ c ∈ fpfx, isFloatModelCharM c = true :=
            fun c hc => (hfpfx c hc).elim (fun e => e ▸ rfl) fun hd => by simp [isFloatModelCharM, hd]
          have haf_fmc : ∀ c ∈ afterFrac, isFloatModelCharM c = true := by
            split at h <;> first | exact List.forall_mem_cons.mpr ⟨rfl, parseFloatExpSuffix_charsM _ _ f h⟩ | (cases h; simp; done) | cases h
          exact ⟨hhead, by
            rw [hbody_eq, hr1]; simp only [List.forall_mem_append, List.forall_mem_cons]
            exact ⟨hpfx_fmc, rfl, by simp [isFloatModelCharM, show isAsciiDigitModel c1 = true from hd1], hfpfx_fmc, haf_fmc⟩⟩
        · rename_i afterE
          exact ⟨hhead, by rw [hbody_eq]; simp only [List.forall_mem_append, List.forall_mem_cons]; exact ⟨hpfx_fmc, rfl, parseFloatExpSuffix_charsM afterE _ f h⟩⟩
        · rename_i afterE
          exact ⟨hhead, by rw [hbody_eq]; simp only [List.forall_mem_append, List.forall_mem_cons]; exact ⟨hpfx_fmc, rfl, parseFloatExpSuffix_charsM afterE _ f h⟩⟩
    obtain ⟨⟨b0, br, hb_eq, hb0⟩, hfmc⟩ := hbody
    rcases hcases with rfl | rfl | rfl
    · exact ⟨⟨'+', body, rfl, Or.inl rfl⟩, List.forall_mem_cons.mpr ⟨rfl, hfmc⟩⟩
    · exact ⟨⟨'-', body, rfl, Or.inr (Or.inl rfl)⟩, List.forall_mem_cons.mpr ⟨rfl, hfmc⟩⟩
    · exact ⟨⟨b0, br, hb_eq, hb0.elim (Or.inr ∘ Or.inr ∘ Or.inl) fun h => h.elim (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr)⟩, hfmc⟩

/-- Two `Float` values with identical IEEE-754 bit patterns are equal. -/
theorem float_eq_of_toBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  cases a with | ofModel am => cases b with | ofModel bm => cases am with | mk _ _ => cases bm with | mk _ _ => cases h; rfl

theorem float_beq_props (a b : Float) (h : (a == b) = true) :
    (b == a) = true ∧ a.isNaN = false ∧ b.isNaN = false := by
  have hna : a.isNaN = false := by
    have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h
    change a.toModel.unpack.isNaN = false
    cases ha : a.toModel.unpack <;> simp [ha, Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] at hbeq ⊢
  have hnb : b.isNaN = false := by
    have hbeq : (a.toModel.unpack.compare b.toModel.unpack == some .eq) = true := h
    change b.toModel.unpack.isNaN = false
    cases ha : a.toModel.unpack <;> cases hb : b.toModel.unpack <;> simp [ha, hb, Float.Model.UnpackedFloat.compare, Float.Model.UnpackedFloat.isNaN] at hbeq ⊢
  exact ⟨(NumParse.Model.floatEquiv_nonNaN_iff_beq (by simp [hnb]) (by simp [hna])).mp (NumParse.Model.floatEquiv_symm (Or.inr h)), hna, hnb⟩

/-- Special-value canonical `Float` tokens satisfy `isValidFloatLex`. -/
theorem canonicalFloat_isValidFloatLex (f : Float) :
    (f.isNaN = true → isValidFloatLex "nan" f = true) ∧
    ((f == Float.inf) = true → isValidFloatLex "inf" f = true) ∧
    ((f == -Float.inf) = true → isValidFloatLex "-inf" f = true) ∧
    (f.toBits = (0.0 : Float).toBits → isValidFloatLex "0.0" f = true) ∧
    (f.toBits = (-0.0 : Float).toBits → isValidFloatLex "-0.0" f = true) := by
  refine ⟨fun hnan => ?_, fun hinf => ?_, fun hninf => ?_, fun hbits => ?_, fun hbits => ?_⟩
  · have hp : NumParse.Model.parseFloatModel "nan" = .ok Float.nan := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    simp [isValidFloatLex, hp, hnan, show Float.nan.isNaN = true by decide]; decide
  · have hp : NumParse.Model.parseFloatModel "inf" = .ok Float.inf := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    simp [isValidFloatLex, hp, (float_beq_props f Float.inf hinf).1]; decide
  · have hp : NumParse.Model.parseFloatModel "-inf" = .ok (-Float.inf) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars]
    simp [isValidFloatLex, hp, (float_beq_props f (-Float.inf) hninf).1]; decide
  · obtain rfl := float_eq_of_toBits_eq hbits
    have hp : NumParse.Model.parseFloatModel "0.0" = .ok (0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_zero]
    simp [isValidFloatLex, hp, show ((0.0 : Float) == (0.0 : Float)) = true by decide]; decide
  · obtain rfl := float_eq_of_toBits_eq hbits
    have hp : NumParse.Model.parseFloatModel "-0.0" = .ok (-0.0 : Float) := by
      simp [NumParse.Model.parseFloatModel, NumParse.Model.parseFloatModelChars,
        NumParse.Model.parseFloatIntPart, NumParse.Model.consumeDecFloatDigits,
        NumParse.Model.isDecDigit, NumParse.Model.evalFloat_neg_zero]
    simp [isValidFloatLex, hp, show ((-0.0 : Float) == (-0.0 : Float)) = true by decide]; decide

/-- Any string satisfying `FloatFormatSpec f s` is a valid TOML float lexeme for `f`. -/
theorem floatFormatSpec_isValidFloatLex (f : Float) (s : String)
    (hs : NumParse.Model.FloatFormatSpec f s) : isValidFloatLex s f = true := by
  simp only [NumParse.Model.FloatFormatSpec] at hs
  if hnan : f.isNaN = true then simp only [hnan, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).1 hnan else
  simp only [hnan] at hs
  if hinf : (f == Float.inf) = true then simp only [hinf, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).2.1 hinf else
  simp only [hinf] at hs
  if hninf : (f == -Float.inf) = true then simp only [hninf, ite_true] at hs; subst hs; exact (canonicalFloat_isValidFloatLex f).2.2.1 hninf else
  simp only [hninf] at hs; rcases hs with ⟨_, hsep, hmatch⟩
  cases hp : NumParse.Model.parseFloatModel s with
  | error => rw [hp] at hmatch; cases hmatch
  | ok y =>
    rw [hp] at hmatch; obtain rfl := float_eq_of_toBits_eq hmatch
    obtain ⟨_, hfmc⟩ := parseFloatModelChars_propsM s.toList y (by simpa [NumParse.Model.parseFloatModel] using hp)
    have hnoTerm : (s.toList.all fun c => !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c) = true :=
      List.all_eq_true.mpr fun c hc => (isFloatModelCharM_props c (hfmc c hc)).2.2.2.1
    have hmark : (s.contains '.' || s.contains 'e' || s.contains 'E' || s == "inf" || s == "+inf" || s == "-inf" || s == "nan" || s == "+nan" || s == "-nan") = true := by
      rcases hsep with h1 | h1 | h1 <;> simp only [String.contains_char_eq, decide_eq_true_eq] at h1 <;> simp [h1]
    simp only [isValidFloatLex]; rw [hmark, hnoTerm, hp]
    simp [(NumParse.Model.floatEquiv_nonNaN_iff_beq hnan hnan).mp (NumParse.Model.floatEquiv_refl y)]

end LeanSwe.Toml.Proofs

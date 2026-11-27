import LeanSwe.NumParse.Model

namespace LeanSwe.NumParse.Model

/-- Render positive natural `n` as big-endian ASCII decimal digits prepended onto `acc`. -/
def natToDecCharsPosModel (n : Nat) (acc : List Char) : List Char :=
  match n with
  | 0 => acc
  | m + 1 =>
    natToDecCharsPosModel ((m + 1) / 10) (Char.ofNat ('0'.toNat + (m + 1) % 10) :: acc)
termination_by n

/-- Render signed integer `n` as canonical base-10 characters without underscores. -/
def formatIntCharsModel : Int → List Char
  | .ofNat 0 => ['0']
  | .ofNat (m + 1) => natToDecCharsPosModel (m + 1) []
  | .negSucc m => '-' :: natToDecCharsPosModel (m + 1) []

/-- Pure mathematical reference integer formatter producing canonical signed decimal strings. -/
def witnessFormatInt (n : Int) : String :=
  String.ofList (formatIntCharsModel n)

/-- Single decimal accumulation step over ASCII digit characters. -/
def decStepModel (acc : Nat) (c : Char) : Nat :=
  acc * 10 + (c.toNat - '0'.toNat)

/-- Any decimal digit differs from any non-decimal character. -/
theorem decDigit_ne_of_false_model {c x : Char} (hc : isDecDigit c = true) (hx : isDecDigit x = false) :
    c ≠ x := by
  intro h; subst h; rw [hx] at hc; cases hc

private theorem char_ofNat_decDigit_model (d : Nat) (hd : d < 10) :
    isDecDigit (Char.ofNat ('0'.toNat + d)) = true ∧
      (Char.ofNat ('0'.toNat + d)).toNat - '0'.toNat = d :=
  (by decide : ∀ x : Fin 10,
    isDecDigit (Char.ofNat ('0'.toNat + x.1)) = true ∧
      (Char.ofNat ('0'.toNat + x.1)).toNat - '0'.toNat = x.1) ⟨d, hd⟩

private theorem natToDecCharsPosModel_append (n : Nat) (acc : List Char) :
    natToDecCharsPosModel n acc = natToDecCharsPosModel n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [natToDecCharsPosModel.eq_1]
    | succ m =>
      rw [natToDecCharsPosModel.eq_2, natToDecCharsPosModel.eq_2]
      have hlt : (m + 1) / 10 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [ih _ hlt (Char.ofNat ('0'.toNat + (m + 1) % 10) :: acc),
          ih _ hlt [Char.ofNat ('0'.toNat + (m + 1) % 10)]]
      simp [List.append_assoc]

/-- Folding `decStepModel` over `natToDecCharsPosModel n []` shifts `acc` and adds `n`. -/
theorem natToDecCharsPosModel_eval (n acc : Nat) :
    (natToDecCharsPosModel n []).foldl decStepModel acc =
      acc * 10 ^ (natToDecCharsPosModel n []).length + n := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    cases n with
    | zero => simp [natToDecCharsPosModel.eq_1]
    | succ m =>
      rw [natToDecCharsPosModel.eq_2, natToDecCharsPosModel_append, List.foldl_append,
          ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) acc]
      have hd := (char_ofNat_decDigit_model ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2
      simp only [List.foldl_cons, List.foldl_nil, decStepModel, List.length_append, List.length_singleton, hd]
      rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]; omega

/-- Every character emitted by `natToDecCharsPosModel` is a decimal digit. -/
theorem natToDecCharsPosModel_all_dec (n : Nat) :
    ∀ c ∈ natToDecCharsPosModel n [], isDecDigit c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [natToDecCharsPosModel.eq_1]
    | succ m =>
      rw [natToDecCharsPosModel.eq_2, natToDecCharsPosModel_append]
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) c h1
      · simp only [List.mem_singleton] at h2; subst h2
        exact (char_ofNat_decDigit_model _ (Nat.mod_lt _ (by decide))).1

/-- `natToDecCharsPosModel` is non-empty for positive `n`. -/
theorem natToDecCharsPosModel_nonempty {n : Nat} (hn : 0 < n) :
    natToDecCharsPosModel n [] ≠ [] := by
  cases n with
  | zero => omega
  | succ m => rw [natToDecCharsPosModel.eq_2, natToDecCharsPosModel_append]; simp

/-- `natToDecCharsPosModel` never emits a leading `'0'` for positive `n`. -/
theorem natToDecCharsPosModel_head_ne_zero {n : Nat} (hn : 0 < n) :
    (natToDecCharsPosModel n []).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [natToDecCharsPosModel.eq_2, natToDecCharsPosModel_append]
      by_cases hq : (m + 1) / 10 = 0
      · rw [hq, natToDecCharsPosModel.eq_1, List.nil_append]
        intro heq
        have hsub := congrArg (fun x : Char => x.toNat - '0'.toNat) (Option.some.inj heq)
        rw [(char_ofNat_decDigit_model ((m + 1) % 10) (Nat.mod_lt _ (by decide))).2,
            show '0'.toNat - '0'.toNat = 0 from rfl] at hsub
        omega
      · have hqpos : 0 < (m + 1) / 10 := Nat.pos_of_ne_zero hq
        cases hql : natToDecCharsPosModel ((m + 1) / 10) [] with
        | nil => exact absurd hql (natToDecCharsPosModel_nonempty hqpos)
        | cons x xs =>
          simpa [hql] using ih _ (Nat.div_lt_self (Nat.succ_pos m) (by decide)) hqpos

/-- `formatIntCharsModel` never contains an underscore `'_'`. -/
theorem formatIntCharsModel_ne_underscore (e : Int) :
    ∀ c ∈ formatIntCharsModel e, c ≠ '_' := by
  unfold formatIntCharsModel
  cases e with
  | ofNat n =>
    cases n with
    | zero => intro c hc; simp at hc; subst hc; decide
    | succ m => intro c hc; exact decDigit_ne_of_false_model (natToDecCharsPosModel_all_dec (m + 1) c hc) (by decide)
  | negSucc n =>
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact decDigit_ne_of_false_model (natToDecCharsPosModel_all_dec (n + 1) c hc) (by decide)

private theorem consumeIntDigits_dec_digits_model (cs : List Char)
    (hdigits : ∀ c ∈ cs, isDecDigit c = true) (acc : Nat) :
    consumeIntDigits .dec acc cs = .ok (cs.foldl decStepModel acc) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    have hc := hdigits c (by simp)
    have hne : c ≠ '_' := decDigit_ne_of_false_model hc (by decide)
    have hdv : digitVal? .dec c = some (c.toNat - '0'.toNat) := by simp only [digitVal?, isDecDigit] at hc ⊢; simp [hc]
    rw [consumeIntDigits.eq_4 _ _ _ _ (fun _ _ h _ => hne h) (fun h _ => hne h)]
    simpa [NumBase.radix, hdv, decStepModel] using ih (fun x hx => hdigits x (by simp [hx])) _

private theorem parseIntModel_formatPosModel (neg : Bool) (m : Nat) :
    let cs := (if neg then ['-'] else []) ++ natToDecCharsPosModel (m + 1) []
    !(String.ofList cs).contains '_' ∧
      (String.ofList cs).toList.all (fun c => isDecDigit c || c == '-') = true ∧
      parseIntModel (String.ofList cs) = .ok (if neg then Int.negSucc m else Int.ofNat (m + 1)) := by
  have hall := natToDecCharsPosModel_all_dec (m + 1)
  have hhd := natToDecCharsPosModel_head_ne_zero (Nat.succ_pos m)
  have hev := natToDecCharsPosModel_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hcs : natToDecCharsPosModel (m + 1) [] with
  | nil => exact absurd hcs (natToDecCharsPosModel_nonempty (Nat.succ_pos m))
  | cons c rest =>
    rw [hcs] at hall hhd hev
    have hc := hall c (by simp)
    have hne0 : c ≠ '0' := fun h => hhd (by simp [h])
    have hcU : c ≠ '_' := decDigit_ne_of_false_model hc (by decide)
    have hdv : digitVal? .dec c = some (c.toNat - '0'.toNat) := by simp only [digitVal?, isDecDigit] at hc ⊢; simp [hc]
    have hpd : parseDecAfterSign neg (c :: rest) = .ok (if neg then Int.negSucc m else Int.ofNat (m + 1)) := by
      rw [parseDecAfterSign.eq_5 _ _ _ hcU hne0]
      simp only [hdv, consumeIntDigits_dec_digits_model rest (fun r hr => hall r (by simp [hr])),
        show rest.foldl decStepModel (c.toNat - '0'.toNat) = (c :: rest).foldl decStepModel 0 by simp [decStepModel], hev]
      cases neg <;> rfl
    cases neg with
    | false =>
      refine ⟨?_, ?_, ?_⟩
      · have hnu : '_' ∉ c :: rest := fun hm => decDigit_ne_of_false_model (hall '_' hm) (by decide) rfl
        simp [String.contains_char_eq, String.toList_ofList, hnu]
      · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, String.toList_ofList]
        exact List.all_eq_true.mpr fun x hx => Bool.or_eq_true_iff.mpr (Or.inl (hall x hx))
      · simp only [parseIntModel, String.toList_ofList, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        rw [parseIntModelChars.eq_7]
        · exact hpd
        · intro h; cases h
        · intro _ _ h; cases h; exact decDigit_ne_of_false_model hc (by decide) rfl
        · intro _ _ h; cases h; exact decDigit_ne_of_false_model hc (by decide) rfl
        · intro _ h; cases h; exact decDigit_ne_of_false_model hc (by decide) rfl
        · intro _ h; cases h; exact decDigit_ne_of_false_model hc (by decide) rfl
        · intro _ _ h; cases h; exact hne0 rfl
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · have hnu : '_' ∉ '-' :: c :: rest := fun hm =>
          (List.mem_cons.mp hm).elim (fun h => absurd h (by decide))
            (fun h => decDigit_ne_of_false_model (hall '_' h) (by decide) rfl)
        simp [String.contains_char_eq, String.toList_ofList, hnu]
      · simp only [↓reduceIte, List.singleton_append, String.toList_ofList]
        refine List.all_eq_true.mpr fun x hx => ?_
        rcases List.mem_cons.mp hx with rfl | hx'
        · decide
        · exact Bool.or_eq_true_iff.mpr (Or.inl (hall x hx'))
      · simp only [parseIntModel, String.toList_ofList, ↓reduceIte, List.singleton_append]
        rw [parseIntModelChars.eq_5 _ (fun _ _ h => by cases h; exact hne0 rfl)]; exact hpd

/-- `witnessFormatInt` satisfies `allowedFormatInt` for every `Int`. -/
theorem allowedFormatInt_witnessFormatInt (n : Int) :
    allowedFormatInt n (witnessFormatInt n) := by
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      refine ⟨?_, ?_, rfl⟩
      · simp only [witnessFormatInt, formatIntCharsModel, String.contains_char_eq, String.toList_ofList]; decide
      · simp only [witnessFormatInt, formatIntCharsModel, String.toList_ofList]; decide
    | succ m => exact parseIntModel_formatPosModel false m
  | negSucc m => exact parseIntModel_formatPosModel true m

end LeanSwe.NumParse.Model

import LeanSwe.CmdLine.Model
import LeanSwe.CmdLine.Impl
namespace LeanSwe.CmdLine.Proofs.Shared
open LeanSwe.CmdLine
@[simp] theorem internal_isAsciiWhitespace_eq (c : Char) : Internal.isAsciiWhitespace c = Model.isAsciiWhitespace c := rfl
@[simp] theorem internal_dropLeadingWhitespace_eq : ∀ cs, Internal.dropLeadingWhitespace cs = Model.dropLeadingWhitespace cs
  | [] => rfl
  | c :: cs => by simp only [Internal.dropLeadingWhitespace, Model.dropLeadingWhitespace, internal_isAsciiWhitespace_eq, internal_dropLeadingWhitespace_eq cs]
@[simp] theorem internal_trimAscii_eq (s : String) : Internal.trimAscii s = Model.trimAscii s := by
  simp [Internal.trimAscii, Model.trimAscii, Internal.trimAsciiChars, Model.trimAsciiChars]
@[simp] theorem internal_asciiLower_eq (s : String) : Internal.asciiLower s = Model.asciiLower s := rfl
@[simp] theorem internal_allDistinct_eq {α : Type} [BEq α] : ∀ xs : List α, Internal.allDistinct xs = Model.allDistinct xs
  | [] => rfl
  | x :: xs => by simp only [Internal.allDistinct, Model.allDistinct, internal_allDistinct_eq xs]
@[simp] theorem internal_validArgOrder_eq : ∀ b1 b2 xs, Internal.validArgOrder b1 b2 xs = Model.validArgOrder b1 b2 xs
  | _, _, [] => rfl
  | b1, b2, a :: rest => by
    unfold Internal.validArgOrder Model.validArgOrder
    repeat (split; · rfl)
    exact internal_validArgOrder_eq _ _ rest
@[simp] theorem internal_parseBoolString_eq (s : String) : Internal.parseBoolString s = Model.parseBoolString s := rfl
@[simp] theorem internal_validateCustomValue_eq (k : ValueKind) (s : String) (vs : CustomValidators) :
    Internal.validateCustomValue k s vs = Model.validateCustomValue k s vs := rfl
@[simp] theorem internal_isValidCommandName_eq (n : String) : Internal.isValidCommandName n = Model.isValidCommandName n := rfl
@[simp] theorem internal_isValidValueKind_eq (k : ValueKind) : Internal.isValidValueKind k = Model.isValidValueKind k := by
  cases k <;> simp [Internal.isValidValueKind, Model.isValidValueKind]
@[simp] theorem internal_startsWithDash_eq (s : String) : Internal.startsWithDash s = Model.startsWithDash s := rfl
@[simp] theorem internal_startsWithNoDash_eq (s : String) : Internal.startsWithNoDash s = Model.startsWithNoDash s := rfl
/-- Check whether `c` is an ASCII decimal digit `'0'..'9'`. -/
def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private theorem digitChar_prop (k : Nat) (hk : k < 10) : isAsciiDigit (Nat.digitChar k) = true ∧ (Nat.digitChar k).toNat - 48 = k := by
  match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
private theorem toDigitsCore_acc (fuel n : Nat) (acc : List Char) : Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => rfl
  | succ fuel ih =>
    unfold Nat.toDigitsCore; dsimp only
    by_cases h : n / 10 = 0
    · simp [h]
    · simp only [h, ↓reduceIte]; rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc), ih (n / 10) [Nat.digitChar (n % 10)]]; simp
private theorem toDigitsCore_props (fuel n : Nat) (hf : n < fuel) :
    let ds := Nat.toDigitsCore 10 fuel n []
    ds.isEmpty = false ∧ ds.all isAsciiDigit = true ∧ ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold Nat.toDigitsCore; dsimp only; have hd := digitChar_prop (n % 10) (Nat.mod_lt n (by decide))
    by_cases h : n / 10 = 0
    · simp only [h, ↓reduceIte, List.isEmpty_cons, List.all_cons, List.all_nil, Bool.and_true, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      exact ⟨trivial, hd.1, by omega⟩
    · simp only [h, ↓reduceIte]; rw [toDigitsCore_acc]; have ⟨_, hall, hfold⟩ := ih (n / 10) (by omega)
      refine ⟨by cases Nat.toDigitsCore 10 fuel (n / 10) [] <;> simp, by simp [List.all_append, hall, hd.1], ?_⟩
      rw [List.foldl_append, hfold]; simp only [List.foldl_cons, List.foldl_nil, hd.2]; omega
/-- Parsing the `toString` of a `Nat` recovers it. -/
theorem parseNatChars_toString (n : Nat) : Model.parseNatChars (toString n).toList = some n := by
  change Model.parseNatChars (Nat.repr n).toList = some n
  rw [Nat.repr, String.toList_ofList, Nat.toDigits]; unfold Model.parseNatChars
  have ⟨hne, hall, hfold⟩ := toDigitsCore_props (n + 1) n (Nat.lt_succ_self n)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, show (Nat.toDigitsCore 10 (n + 1) n []).all (fun c => '0' ≤ c && c ≤ '9') = true from hall]
  exact congrArg some hfold
/-- Parsing the `toString` of an `Int` recovers it. -/
theorem parseIntChars_toString (i : Int) : Model.parseIntChars (toString i).toList = some i := by
  change Model.parseIntChars (Int.repr i).toList = some i
  cases i with
  | ofNat n =>
    simp only [Int.repr]
    have hchars : (Nat.repr n).toList = Nat.toDigitsCore 10 (n + 1) n [] := by rw [Nat.repr, String.toList_ofList, Nat.toDigits]
    have ⟨hne, hall, _⟩ := toDigitsCore_props (n + 1) n (Nat.lt_succ_self n)
    cases hc : (Nat.repr n).toList with
    | nil => rw [← hchars, hc] at hne; cases hne
    | cons c cs =>
      have hc0 : isAsciiDigit c = true := by rw [← hchars, hc, List.all_cons, Bool.and_eq_true] at hall; exact hall.1
      have hneDash : c ≠ '-' := fun hd => by subst hd; revert hc0; decide
      have hpc : Model.parseIntChars (c :: cs) = (Model.parseNatChars (c :: cs)).map Int.ofNat := by unfold Model.parseIntChars; cases c; split <;> first | (rename_i hm; injection hm with h1; exact absurd h1 hneDash) | rfl
      rw [hpc, ← hc]; change (Model.parseNatChars (toString n).toList).map Int.ofNat = some (Int.ofNat n); rw [parseNatChars_toString n]; rfl
  | negSucc k =>
    simp only [Int.repr, String.toList_append, show "-".toList = ['-'] from rfl, List.cons_append, List.nil_append, Model.parseIntChars]
    have hnat : Model.parseNatChars (Nat.repr (k + 1)).toList = some (k + 1) := parseNatChars_toString (k + 1)
    change (Model.parseNatChars (Nat.repr (k + 1)).toList).map (fun n => -(Int.ofNat n)) = some (Int.negSucc k); rw [hnat]; rfl
private def foldNatChunks (acc : Nat) : List (Nat × Nat) → Nat
  | [] => acc
  | (v, b) :: rest => foldNatChunks (acc * b + v) rest
private theorem foldNatChunks_append (acc : Nat) (xs ys : List (Nat × Nat)) : foldNatChunks acc (xs ++ ys) = foldNatChunks (foldNatChunks acc xs) ys := by
  induction xs generalizing acc with | nil => rfl | cons p _ ih => exact ih (acc * p.2 + p.1)
private theorem mergeNatChunksTR_eq (acc : Nat) (accRev ps : List (Nat × Nat)) : foldNatChunks acc (Internal.mergeNatChunksTR accRev ps) = foldNatChunks (foldNatChunks acc accRev.reverse) ps := by
  match ps with
  | [] => rfl
  | [_] => simp [Internal.mergeNatChunksTR, foldNatChunks_append, foldNatChunks]
  | (v1, b1) :: (v2, b2) :: rest => rw [Internal.mergeNatChunksTR, mergeNatChunksTR_eq acc ((v1 * b2 + v2, b1 * b2) :: accRev) rest]; simp [List.reverse_cons, foldNatChunks_append, foldNatChunks, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
private theorem foldl_natChunks_eq (acc : Nat) (ps : List (Nat × Nat)) : ps.foldl (fun a p => a * p.2 + p.1) acc = foldNatChunks acc ps := by
  induction ps generalizing acc with | nil => rfl | cons p _ ih => simp [List.foldl_cons, foldNatChunks, ih]
private theorem reduceNatChunks_eq (fuel : Nat) (ps : List (Nat × Nat)) : Internal.reduceNatChunks fuel ps = foldNatChunks 0 ps := by
  induction fuel generalizing ps with
  | zero => cases ps with | nil => rfl | cons p ps' => cases ps' <;> simp [Internal.reduceNatChunks, foldNatChunks, foldl_natChunks_eq]
  | succ fuel ih => cases ps with | nil => rfl | cons p ps' => cases ps' <;> simp [Internal.reduceNatChunks, foldNatChunks, ih, mergeNatChunksTR_eq]
private theorem parseNatCharsFast_go_eq (cs : List Char) (curVal curBase count : Nat) (chunksRev : List (Nat × Nat)) :
    Internal.parseNatCharsFast.go cs curVal curBase count chunksRev = if cs.all (fun c => '0' ≤ c && c ≤ '9') then some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) (foldNatChunks 0 chunksRev.reverse * curBase + curVal)) else none := by
  induction cs generalizing curVal curBase count chunksRev with
  | nil => simp [Internal.parseNatCharsFast.go, reduceNatChunks_eq, foldNatChunks_append, foldNatChunks]
  | cons c rest ih =>
    unfold Internal.parseNatCharsFast.go; by_cases hd : ('0' ≤ c && c ≤ '9') = true
    · simp only [hd, ↓reduceIte, List.all_cons, Bool.true_and, List.foldl_cons]; by_cases hc : count + 1 == 18
      · simp only [hc, ↓reduceIte, ih]; split <;> first | (congr 2; simp only [List.reverse_cons, foldNatChunks_append, foldNatChunks, Nat.mul_one, Nat.add_zero, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]) | rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, ih]; split <;> first | (congr 2; simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]) | rfl
    · have hdf : ('0' ≤ c && c ≤ '9') = false := Bool.eq_false_iff.mpr hd; simp [hdf]
/-- `Internal.parseNatCharsFast` equals `Model.parseNatChars`. -/
theorem parseNatCharsFast_eq (cs : List Char) : Internal.parseNatCharsFast cs = Model.parseNatChars cs := by
  unfold Internal.parseNatCharsFast Model.parseNatChars; cases h : cs.isEmpty <;> simp [parseNatCharsFast_go_eq, foldNatChunks]
/-- `Internal.parseIntCharsFast` equals `Model.parseIntChars`. -/
theorem parseIntCharsFast_eq (cs : List Char) : Internal.parseIntCharsFast cs = Model.parseIntChars cs := by
  unfold Internal.parseIntCharsFast Model.parseIntChars; cases cs with | nil => simp [parseNatCharsFast_eq] | cons c rest => by_cases h : c = '-' <;> first | (subst h; simp [parseNatCharsFast_eq]) | simp [h, parseNatCharsFast_eq]
/-- `Internal.parseOptValueFast` equals `Model.parseOptValue`. -/
theorem parseOptValueFast_eq (k : ValueKind) (s : String) : Internal.parseOptValueFast k s = Model.parseOptValue k s := by
  cases k <;> simp [Internal.parseOptValueFast, Model.parseOptValue, parseNatCharsFast_eq, parseIntCharsFast_eq] <;> rfl
@[simp] theorem internal_isValidOptLocal_eq (opt : OptSpec) : Internal.isValidOptLocal opt = Model.isValidOptLocal opt := by
  unfold Internal.isValidOptLocal Model.isValidOptLocal
  have h1 : Internal.isValidLookupName opt.name = Model.isValidLookupName opt.name := rfl
  have h2 : ∀ l, Internal.isValidLongName l = Model.isValidLongName l := fun _ => rfl
  have h3 : ∀ c, Internal.isValidShortChar c = Model.isValidShortChar c := fun _ => rfl
  have h4 : ∀ k, Internal.isValidEnvKey k = Model.isValidEnvKey k := fun _ => rfl
  simp only [h1, h2, h3, h4, internal_startsWithNoDash_eq, internal_isValidValueKind_eq, parseOptValueFast_eq]; rfl
@[simp] theorem internal_isValidArg_eq (arg : ArgSpec) : Internal.isValidArg arg = Model.isValidArg arg := by
  unfold Internal.isValidArg Model.isValidArg
  have h1 : Internal.isValidLookupName arg.name = Model.isValidLookupName arg.name := rfl
  simp only [h1, internal_isValidValueKind_eq, parseOptValueFast_eq]; rfl
/-- `Internal.parseOptValueWithFast` equals `Model.parseOptValueWith`. -/
theorem parseOptValueWithFast_eq (k : ValueKind) (s : String) (vs : CustomValidators) : Internal.parseOptValueWithFast k s vs = Model.parseOptValueWith k s vs := by
  unfold Internal.parseOptValueWithFast Model.parseOptValueWith; rw [parseOptValueFast_eq, internal_validateCustomValue_eq]
/-- `Internal.resolveOptDefaultFast` equals `Model.resolveOptDefault`. -/
theorem resolveOptDefaultFast_eq (opt : OptSpec) (vs : CustomValidators) : Internal.resolveOptDefaultFast opt vs = Model.resolveOptDefault opt vs := by
  unfold Internal.resolveOptDefaultFast Model.resolveOptDefault; simp only [parseOptValueWithFast_eq]; rfl
/-- `Internal.resolveSingleOptionFast` equals `Model.resolveSingleOption`. -/
theorem resolveSingleOptionFast_eq {m : Type → Type} [Monad m] (getEnv : String → m (Except CmdLineError (Option String))) (opt : OptSpec) (cliVals : List OptValue) (vs : CustomValidators) :
    Internal.resolveSingleOptionFast getEnv opt cliVals vs = Model.resolveSingleOption getEnv opt cliVals vs := by
  unfold Internal.resolveSingleOptionFast Model.resolveSingleOption; simp only [resolveOptDefaultFast_eq, parseOptValueWithFast_eq]; rfl
/-- `ValueKind` boolean equality implies propositional equality. -/
theorem valueKind_eq_of_beq {a b : ValueKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h | (rename_i x y; have h' : (x == y) = true := h; rw [beq_iff_eq.mp h'])
/-- Propositional inequality of `ValueKind` implies `==` is `false`. -/
theorem valueKind_beq_false_of_ne {a b : ValueKind} (h : a ≠ b) : (a == b) = false := by
  cases heq : a == b <;> first | rfl | exact absurd (valueKind_eq_of_beq heq) h
/-- Predicate asserting an `OptValue` has the constructor matching `ValueKind`. -/
def OptValueMatchesKind : ValueKind → OptValue → Prop
  | .string, .string _ => True
  | .bool, .bool _ => True
  | .nat, .nat _ => True
  | .int, .int _ => True
  | .choice opts, .choice s => s ∈ opts
  | .custom _, .custom _ => True
  | _, _ => False
/-- `parseOptValueWith` with empty validators reduces to `parseOptValue`. -/
theorem parseOptValueWith_nil (k : ValueKind) (s : String) : Model.parseOptValueWith k s [] = Model.parseOptValue k s := by
  unfold Model.parseOptValueWith Model.validateCustomValue
  cases Model.parseOptValue k s with | error _ => rfl | ok _ => cases k <;> simp [Bind.bind, Except.bind, pure, Except.pure]
/-- Successful `parseOptValue` outputs match their `ValueKind`. -/
theorem parseOptValue_ok_matchesKind {k : ValueKind} {s : String} {v : OptValue} (h : Model.parseOptValue k s = .ok v) : OptValueMatchesKind k v := by
  cases k <;> simp only [Model.parseOptValue] at h
  · injection h with h; subst h; trivial
  · cases hb : Model.parseBoolString s <;> simp [hb] at h; subst h; trivial
  · cases hn : Model.parseNatChars s.toList <;> simp [hn] at h; subst h; trivial
  · cases hi : Model.parseIntChars s.toList <;> simp [hi] at h; subst h; trivial
  · rename_i opts; by_cases hc : s ∈ opts <;> simp [hc] at h; subst h; exact hc
  · injection h with h; subst h; trivial
/-- Successful `parseOptValueWith` outputs match their `ValueKind` for any validators. -/
theorem parseOptValueWith_ok_matchesKind {k : ValueKind} {s : String} {vs : CustomValidators} {v : OptValue}
    (h : Model.parseOptValueWith k s vs = .ok v) : OptValueMatchesKind k v := by
  unfold Model.parseOptValueWith at h
  cases hp : Model.parseOptValue k s with
  | error _ => rw [hp] at h; cases h
  | ok v0 =>
    rw [hp] at h; dsimp only [Bind.bind, Except.bind] at h
    cases hvc : Model.validateCustomValue k s vs with
    | error _ => rw [hvc] at h; cases h
    | ok _ => rw [hvc] at h; injection h with hv; subst hv; exact parseOptValue_ok_matchesKind hp
/-- `parseOptValue` round-trips `optValueToString` on well-typed values. -/
theorem parseOptValue_optValueToString {k : ValueKind} {v : OptValue} (hv : OptValueMatchesKind k v) : Model.parseOptValue k (Model.optValueToString v) = .ok v := by
  cases k <;> cases v <;> simp only [OptValueMatchesKind] at hv
  case string.string => rfl
  case bool.bool b => cases b <;> rfl
  case nat.nat => simp only [Model.parseOptValue, Model.optValueToString, parseNatChars_toString]
  case int.int => simp only [Model.parseOptValue, Model.optValueToString, parseIntChars_toString]
  case choice.choice => simp only [Model.parseOptValue, Model.optValueToString, List.contains_iff_mem.mpr hv, ↓reduceIte]
  case custom.custom => rfl
private theorem splitFirstEq_go_none (rev cs : List Char) (hno : '=' ∉ cs) : Internal.splitFirstEq.go (String.ofList (rev.reverse ++ cs)) rev cs = (String.ofList (rev.reverse ++ cs), none) := by
  induction cs generalizing rev with | nil => simp [Internal.splitFirstEq.go] | cons c cs ih =>
    have hne : c ≠ '=' := fun h => hno (by simp [h])
    simp only [Internal.splitFirstEq.go, beq_iff_eq, hne, ↓reduceIte]; simpa [List.append_assoc] using ih (c :: rev) (fun h => hno (by simp [h]))
/-- `splitFirstEq` splits `l ++ "=" ++ val` cleanly when `'=' ∉ l.toList`. -/
theorem splitFirstEq_append (l val : String) (hno : '=' ∉ l.toList) : Internal.splitFirstEq (l ++ "=" ++ val) = (l, some val) := by
  unfold Internal.splitFirstEq
  have aux : ∀ rev cs vs, '=' ∉ cs → Internal.splitFirstEq.go (String.ofList (rev.reverse ++ cs ++ ('=' :: vs))) rev (cs ++ ('=' :: vs)) = (String.ofList (rev.reverse ++ cs), some (String.ofList vs)) := by
    intro rev cs vs hcs; induction cs generalizing rev with | nil => simp [Internal.splitFirstEq.go] | cons c cs ih =>
      have hne : c ≠ '=' := fun h => hcs (by simp [h])
      simp only [List.cons_append, Internal.splitFirstEq.go, beq_iff_eq, hne, ↓reduceIte]; simpa [List.append_assoc] using ih (c :: rev) (fun h => hcs (by simp [h]))
  have heq : (l ++ "=" ++ val).toList = l.toList ++ ('=' :: val.toList) := by simp [String.toList_append]
  have h := aux [] l.toList val.toList hno; simp only [List.reverse_nil, List.nil_append, ← heq, String.ofList_toList] at h
  rw [heq]; simpa [String.ofList_toList] using h
/-- `splitFirstEq` returns `(l, none)` when `'=' ∉ l.toList`. -/
theorem splitFirstEq_none (l : String) (hno : '=' ∉ l.toList) : Internal.splitFirstEq l = (l, none) := by
  unfold Internal.splitFirstEq; simpa [String.ofList_toList] using splitFirstEq_go_none [] l.toList hno
/-- `Model.allDistinct` implies `List.Nodup`. -/
theorem allDistinct_nodup {α : Type} [BEq α] [LawfulBEq α] {xs : List α} (h : Model.allDistinct xs = true) : xs.Nodup := by
  induction xs with | nil => exact List.nodup_nil | cons x xs ih =>
    simp only [Model.allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h; refine List.nodup_cons.mpr ⟨fun hx => ?_, ih h.2⟩
    have hc := List.contains_iff_mem.mpr hx; rw [h.1] at hc; cases hc
/-- Unique key lookup in `find?` when `filterMap key` is `Nodup`. -/
theorem find?_unique_key {α β : Type} [BEq β] [LawfulBEq β] (key : α → Option β) (xs : List α) (hnd : (xs.filterMap key).Nodup) (x : α) (hx : x ∈ xs) (b : β) (hk : key x = some b) : xs.find? (fun y => key y == some b) = some x := by
  induction xs with | nil => cases hx | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp [hk]
    · cases hyk : key y with | none => simp only [List.filterMap_cons, hyk] at hnd; simp [hyk, ih hnd hmem] | some by' =>
        simp only [List.filterMap_cons, hyk, List.nodup_cons] at hnd
        have hne : by' ≠ b := fun heq => hnd.1 (heq ▸ List.mem_filterMap.mpr ⟨x, hmem, hk⟩); simp [hyk, hne, ih hnd.2 hmem]
/-- Long flag names contributed by a single `OptSpec`. -/
def optLongs (opt : OptSpec) : List String :=
  match opt.long with | none => [] | some l => if opt.kind == .bool && !opt.repeatable then [l, "no-" ++ l] else [l]
/-- `collectVisibleLongs` equals `opts.flatMap optLongs`. -/
theorem collectVisibleLongs_eq_flatMap (opts : List OptSpec) : Model.collectVisibleLongs opts = opts.flatMap optLongs := by
  induction opts with | nil => rfl | cons y ys ih =>
    have hstep : Model.collectVisibleLongs (y :: ys) = match y.long with | none => Model.collectVisibleLongs ys | some l => if y.kind == .bool && !y.repeatable then l :: ("no-" ++ l) :: Model.collectVisibleLongs ys else l :: Model.collectVisibleLongs ys := rfl
    rw [hstep, ih]; unfold optLongs; cases hyl : y.long with | none => simp [hyl, List.flatMap_cons] | some l =>
      dsimp only; by_cases hb : (y.kind == .bool && !y.repeatable) <;> simp only [hyl, hb, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.cons_append, List.nil_append]
private theorem mem_collectVisibleLongs_of (opts : List OptSpec) {o : OptSpec} {l : String} (ho : o ∈ opts) (hl : o.long = some l) :
    l ∈ Model.collectVisibleLongs opts ∧ (o.kind = .bool → o.repeatable = false → ("no-" ++ l) ∈ Model.collectVisibleLongs opts) := by
  rw [collectVisibleLongs_eq_flatMap]
  refine ⟨List.mem_flatMap.mpr ⟨o, ho, by unfold optLongs; rw [hl]; dsimp only; split <;> simp⟩, fun hk hnr => List.mem_flatMap.mpr ⟨o, ho, by have hb : (o.kind == .bool && !o.repeatable) = true := by { simp [hk, hnr]; try rfl }; unfold optLongs; rw [hl]; dsimp only; rw [hb]; simp⟩⟩
private theorem filterMap_long_sublist (opts : List OptSpec) : (opts.filterMap (·.long)).Sublist (Model.collectVisibleLongs opts) := by
  rw [collectVisibleLongs_eq_flatMap]; induction opts with | nil => simp | cons y ys ih =>
    simp only [List.filterMap_cons, List.flatMap_cons, optLongs]; cases y.long with | none => exact ih | some l => dsimp only; split <;> first | exact .cons_cons l (.cons _ ih) | exact .cons_cons l ih
private theorem no_opt_with_neg_long (opts : List OptSpec) (h : (Model.collectVisibleLongs opts).Nodup) {o : OptSpec} (ho : o ∈ opts) (hk : o.kind = .bool) (hnr : o.repeatable = false) {l : String} (hl : o.long = some l) :
    ∀ x ∈ opts, x.long ≠ some ("no-" ++ l) := by
  induction opts with | nil => cases ho | cons y ys ih =>
    rw [collectVisibleLongs_eq_flatMap, List.flatMap_cons] at h; intro x hx hxl
    rcases List.mem_cons.mp ho with rfl | hoy
    · have hy : optLongs o = [l, "no-" ++ l] := by unfold optLongs; rw [hl]; simp [hk, hnr]; rfl
      rw [hy] at h; have h2 := (List.nodup_cons.mp (List.nodup_cons.mp h).2).1
      rcases List.mem_cons.mp hx with rfl | hxy
      · rw [hl] at hxl; injection hxl with heq; have := congrArg String.length heq; simp at this
      · rw [← collectVisibleLongs_eq_flatMap] at h2; exact absurd (mem_collectVisibleLongs_of ys hxy hxl).1 h2
    · rcases List.mem_cons.mp hx with rfl | hxy
      · have hdisj := (List.nodup_append.mp h).2.2; rw [← collectVisibleLongs_eq_flatMap] at hdisj
        have hmemNeg := (mem_collectVisibleLongs_of ys hoy hl).2 hk hnr; unfold optLongs at hdisj; rw [hxl] at hdisj; dsimp only at hdisj; split at hdisj <;> exact hdisj _ (by simp) _ hmemNeg rfl
      · rw [← collectVisibleLongs_eq_flatMap] at h; exact ih (List.nodup_append.mp h).2.1 hoy x hxy hxl
/-- Lookup a positive long option under `collectVisibleLongs` uniqueness. -/
theorem lookupLongOpt_pos (opts : List OptSpec) (hnd : (Model.collectVisibleLongs opts).Nodup) {o : OptSpec} (ho : o ∈ opts) {l : String} (hl : o.long = some l) : Internal.lookupLongOpt opts l = some (o, false) := by
  unfold Internal.lookupLongOpt; rw [find?_unique_key (·.long) opts (hnd.sublist (filterMap_long_sublist opts)) o ho l hl]
/-- Lookup a negated boolean long option `--no-<l>` under `collectVisibleLongs` uniqueness. -/
theorem lookupLongOpt_neg (opts : List OptSpec) (hnd : (Model.collectVisibleLongs opts).Nodup) {o : OptSpec} (ho : o ∈ opts) (hk : o.kind = .bool) (hnr : o.repeatable = false) {l : String} (hl : o.long = some l) : Internal.lookupLongOpt opts ("no-" ++ l) = some (o, true) := by
  have hno := no_opt_with_neg_long opts hnd ho hk hnr hl
  have hnone : opts.find? (fun x => x.long == some ("no-" ++ l)) = none := by
    clear hnd ho hl; induction opts with | nil => rfl | cons x xs ih => simp [List.find?, beq_eq_false_iff_ne.mpr (hno x (by simp)), ih (fun y hy => hno y (by simp [hy]))]
  have hsnd : Model.startsWithNoDash ("no-" ++ l) = true := by unfold Model.startsWithNoDash; rw [String.toList_append]; rfl
  have hdrop : String.ofList (("no-" ++ l).toList.drop 3) = l := by rw [String.toList_append, show "no-".toList = ['n', 'o', '-'] from rfl]; simp [String.ofList_toList]
  have hf := find?_unique_key (·.long) opts (hnd.sublist (filterMap_long_sublist opts)) o ho l hl
  have hpred : opts.find? (fun x => x.kind == .bool && !x.repeatable && x.long == some l) = some o := by
    clear hnone hno hnd ho hl; induction opts with | nil => cases hf | cons y ys ih =>
      simp only [List.find?] at hf ⊢; cases hyl : (y.long == some l) with | false => rw [hyl] at hf; simp only [Bool.and_false]; exact ih hf | true => rw [hyl] at hf; injection hf with hyo; subst hyo; simp [hk, hnr]; rfl
  unfold Internal.lookupLongOpt; rw [hnone, internal_startsWithNoDash_eq, hsnd, hdrop]; simp [hpred]
/-- Membership and boolean invariant for `lookupLongOpt` results. -/
theorem lookupLongOpt_mem {opts : List OptSpec} {namePart : String} {opt : OptSpec} {isNeg : Bool} (h : Internal.lookupLongOpt opts namePart = some (opt, isNeg)) :
    opt ∈ opts ∧ opt.long.isNone = false ∧ (isNeg = true → opt.kind = .bool ∧ opt.repeatable = false) := by
  unfold Internal.lookupLongOpt at h; cases hf : opts.find? (fun o => o.long == some namePart) with
  | some o => rw [hf] at h; injection h with hp; injection hp with ho hn; subst ho hn; have hps := beq_iff_eq.mp (List.find?_some (p := fun (o : OptSpec) => o.long == some namePart) hf); exact ⟨List.mem_of_find?_eq_some hf, by rw [hps]; rfl, fun hc => by cases hc⟩
  | none =>
    rw [hf] at h; dsimp only at h; split at h
    · cases hf2 : opts.find? (fun o => o.kind == .bool && !o.repeatable && o.long == some _) with
      | none => rw [hf2] at h; cases h
      | some o => rw [hf2] at h; injection h with hp; injection hp with ho hn; subst ho hn; have hps := List.find?_some (p := fun (o : OptSpec) => o.kind == .bool && !o.repeatable && o.long == some _) hf2; simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hps; exact ⟨List.mem_of_find?_eq_some hf2, by rw [hps.2]; rfl, fun _ => ⟨valueKind_eq_of_beq hps.1.1, hps.1.2⟩⟩
    · cases h
/-- Node well-formedness invariant under inherited global options and version. -/
def NodeInv (node : CommandSpec) (g : List OptSpec) (v : Option String) : Prop :=
  Model.isValidCommandNode node g v = true ∧ g.all Model.isValidOptLocal = true
/-- Unpacked structural guarantees extracted from `NodeInv`. -/
structure NodeProps (node : CommandSpec) (g : List OptSpec) (v : Option String) : Prop where
  /-- Valid command name. -/
  validName : Model.isValidCommandName node.name = true
  /-- Every visible option is locally valid. -/
  validOpts : ∀ o ∈ g ++ node.options, Model.isValidOptLocal o = true
  /-- Visible option names are duplicate-free. -/
  nodupNames : ((g ++ node.options).map (·.name)).Nodup
  /-- Visible long flags are duplicate-free. -/
  nodupLongs : (Model.collectVisibleLongs (g ++ node.options)).Nodup
  /-- Visible short flags are duplicate-free. -/
  nodupShorts : ((g ++ node.options).filterMap (·.short)).Nodup
  /-- `'h'` is unused when `shortHelp` is enabled. -/
  noShortHelp : node.shortHelp = true → 'h' ∉ (g ++ node.options).filterMap (·.short)
  /-- `'V'` is unused when `shortVersion` and an effective version are active. -/
  noShortVer : (node.shortVersion && (node.version <|> v).isSome) = true → 'V' ∉ (g ++ node.options).filterMap (·.short)
  /-- Subcommand names are duplicate-free. -/
  nodupSubs : (node.subcommands.map (·.name)).Nodup
private theorem isValidSubcommandList_mem {subs : List CommandSpec} {ng : List OptSpec} {nv : Option String}
    (h : Model.isValidSubcommandList subs ng nv = true) {sub : CommandSpec} (hs : sub ∈ subs) : Model.isValidCommandNode sub ng nv = true := by
  induction subs with
  | nil => cases hs
  | cons _ _ ih => unfold Model.isValidSubcommandList at h; simp only [Bool.and_eq_true] at h; rcases List.mem_cons.mp hs with rfl | hm <;> first | exact h.1 | exact ih h.2 hm
/-- `NodeInv` propagates to any child subcommand. -/
theorem nodeInv_sub {node : CommandSpec} {g : List OptSpec} {v : Option String} (h : NodeInv node g v) {sub : CommandSpec} (hs : sub ∈ node.subcommands) :
    NodeInv sub (g ++ node.options) (node.version <|> v) := by
  rcases node with ⟨name, version, about, shortHelp, shortVersion, options, args, subcommands⟩; rcases h with ⟨hvalid, hg⟩
  unfold Model.isValidCommandNode at hvalid; dsimp only at hvalid; simp only [Bool.and_eq_true] at hvalid
  have ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hopts⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hsub⟩ := hvalid
  exact ⟨isValidSubcommandList_mem hsub hs, by rw [List.all_append, hg, hopts]; rfl⟩
/-- Extract `NodeProps` from `NodeInv`. -/
theorem nodeInv_props {node : CommandSpec} {g : List OptSpec} {v : Option String} (h : NodeInv node g v) : NodeProps node g v := by
  rcases node with ⟨name, version, about, shortHelp, shortVersion, options, args, subcommands⟩; rcases h with ⟨hvalid, hg⟩
  unfold Model.isValidCommandNode at hvalid; dsimp only at hvalid; simp only [Bool.and_eq_true] at hvalid
  have ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcmd, hopts⟩, hnames⟩, hlongs⟩, hshorts⟩, _⟩, hh⟩, hV⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hsubs⟩, _⟩ := hvalid
  refine ⟨hcmd, ?_, allDistinct_nodup hnames, allDistinct_nodup hlongs, allDistinct_nodup hshorts, ?_, ?_, allDistinct_nodup hsubs⟩
  · intro o ho; rcases List.mem_append.mp ho with ho | ho <;> first | exact List.all_eq_true.mp hg o ho | exact List.all_eq_true.mp hopts o ho
  · intro hsh hmem; dsimp only at hsh hmem; rw [hsh] at hh; simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hh; have hc := List.contains_iff_mem.mpr hmem; rw [hh] at hc; cases hc
  · intro hsv hmem; dsimp only at hsv hmem; rw [hsv] at hV; simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hV; have hc := List.contains_iff_mem.mpr hmem; rw [hV] at hc; cases hc
/-- Lookup collected CLI values for option `name`. -/
def lookupCli (cliOpts : List (String × List OptValue)) (name : String) : List OptValue :=
  match cliOpts.find? (fun p => p.1 == name) with | some p => p.2 | none => []
private def recordCliOptSpec : List (String × List OptValue) → String → OptValue → List (String × List OptValue)
  | [], name, v => [(name, [v])]
  | (k, vs) :: rest, name, v => if k == name then (k, v :: vs) :: rest else (k, vs) :: recordCliOptSpec rest name v
private theorem recordCliOpt_go_eq (name : String) (v : OptValue) (accRev xs : List (String × List OptValue)) :
    Internal.recordCliOpt.go name v accRev xs = accRev.reverse ++ recordCliOptSpec xs name v := by
  induction xs generalizing accRev with
  | nil => simp [Internal.recordCliOpt.go, recordCliOptSpec]
  | cons p _ ih => rcases p with ⟨k, vs⟩; unfold Internal.recordCliOpt.go recordCliOptSpec; by_cases hk : k == name <;> simp [hk, ih]
/-- `recordCliOpt` prepends `v` under `name`. -/
theorem recordCliOpt_lookupCli_same (cliOpts : List (String × List OptValue)) (name : String) (v : OptValue) :
    lookupCli (Internal.recordCliOpt cliOpts name v) name = v :: lookupCli cliOpts name := by
  change lookupCli (Internal.recordCliOpt.go name v [] cliOpts) name = _; rw [recordCliOpt_go_eq]; simp only [List.reverse_nil, List.nil_append]
  induction cliOpts with
  | nil => simp [recordCliOptSpec, lookupCli]
  | cons p _ ih => rcases p with ⟨k, vs⟩; unfold recordCliOptSpec; by_cases hk : k == name <;> simp [hk, lookupCli] <;> exact ih
/-- `recordCliOpt` leaves unrelated keys unchanged. -/
theorem recordCliOpt_lookupCli_ne (cliOpts : List (String × List OptValue)) (name k' : String) (v : OptValue) (hne : k' ≠ name) :
    lookupCli (Internal.recordCliOpt cliOpts name v) k' = lookupCli cliOpts k' := by
  change lookupCli (Internal.recordCliOpt.go name v [] cliOpts) k' = _; rw [recordCliOpt_go_eq]; simp only [List.reverse_nil, List.nil_append]
  induction cliOpts with
  | nil => simp [recordCliOptSpec, lookupCli, hne.symm]
  | cons p _ ih =>
    rcases p with ⟨k, vs⟩; unfold recordCliOptSpec
    by_cases hk : k == name
    · have hk' : (k == k') = false := by simp only [beq_iff_eq] at hk; simp [beq_eq_false_iff_ne, hk, hne.symm]
      simp [hk, lookupCli, hk']
    · by_cases hk' : k == k' <;> simp [hk, lookupCli, hk'] <;> exact ih
/-- Reversing per-key value lists commutes with `lookupCli`. -/
theorem lookupCli_map_rev (cliOpts : List (String × List OptValue)) (k : String) :
    lookupCli (cliOpts.map (fun p => (p.1, p.2.reverse))) k = (lookupCli cliOpts k).reverse := by
  induction cliOpts with
  | nil => rfl
  | cons p _ ih => rcases p with ⟨k', vs⟩; unfold lookupCli; by_cases hk : k' == k <;> simp [hk, lookupCli] at ih ⊢; exact ih
/-- Fold `recordCliOpt` across a list of `OptValue`s. -/
def recordCliOptMany (cliOpts : List (String × List OptValue)) (name : String) (vals : List OptValue) : List (String × List OptValue) :=
  vals.foldl (fun acc v => Internal.recordCliOpt acc name v) cliOpts
/-- `recordCliOptMany` prepends `vals.reverse` under `name`. -/
theorem recordCliOptMany_lookupCli_same (cliOpts : List (String × List OptValue)) (name : String) (vals : List OptValue) :
    lookupCli (recordCliOptMany cliOpts name vals) name = vals.reverse ++ lookupCli cliOpts name := by
  induction vals generalizing cliOpts with
  | nil => simp [recordCliOptMany]
  | cons v vs ih => simp only [recordCliOptMany, List.foldl_cons]; change lookupCli (recordCliOptMany (Internal.recordCliOpt cliOpts name v) name vs) name = _; rw [ih, recordCliOpt_lookupCli_same]; simp [List.append_assoc]
/-- `recordCliOptMany` leaves unrelated keys unchanged. -/
theorem recordCliOptMany_lookupCli_ne (cliOpts : List (String × List OptValue)) (name k' : String) (vals : List OptValue) (hne : k' ≠ name) :
    lookupCli (recordCliOptMany cliOpts name vals) k' = lookupCli cliOpts k' := by
  induction vals generalizing cliOpts with
  | nil => simp [recordCliOptMany]
  | cons v vs ih => simp only [recordCliOptMany, List.foldl_cons]; change lookupCli (recordCliOptMany (Internal.recordCliOpt cliOpts name v) name vs) k' = _; rw [ih, recordCliOpt_lookupCli_ne _ _ _ _ hne]
/-- Invariant on collected `cliOpts` against `visibleOpts`. -/
def CliOptsInv (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) : Prop :=
  (∀ k, lookupCli cliOpts k ≠ [] → ∃ opt ∈ visibleOpts, opt.name = k) ∧
  (∀ opt ∈ visibleOpts, ∀ v ∈ lookupCli cliOpts opt.name,
    OptValueMatchesKind opt.kind v ∧ (opt.kind == .bool && opt.repeatable → v = .bool true) ∧ (opt.kind == .bool && opt.long.isNone → v = .bool true))
/-- Recording a well-typed option value preserves `CliOptsInv`. -/
theorem cliOptsInv_record {visibleOpts : List OptSpec} {cliOpts : List (String × List OptValue)}
    (hnd : (visibleOpts.map (·.name)).Nodup) (hinv : CliOptsInv visibleOpts cliOpts) {opt : OptSpec} (ho : opt ∈ visibleOpts)
    {v : OptValue} (hm : OptValueMatchesKind opt.kind v) (hrep : opt.kind == .bool && opt.repeatable → v = .bool true) (hnl : opt.kind == .bool && opt.long.isNone → v = .bool true) :
    CliOptsInv visibleOpts (Internal.recordCliOpt cliOpts opt.name v) := by
  refine ⟨fun k hk => ?_, fun o ho' v' hv' => ?_⟩
  · by_cases hko : k = opt.name
    · exact ⟨opt, ho, hko.symm⟩
    · rw [recordCliOpt_lookupCli_ne _ _ _ _ hko] at hk; exact hinv.1 k hk
  · by_cases hoo : o.name = opt.name
    · have heq : o = opt := by
        clear hinv hv'; induction visibleOpts with
        | nil => cases ho
        | cons _ _ ih => simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd; rcases List.mem_cons.mp ho with rfl | ho1 <;> rcases List.mem_cons.mp ho' with rfl | ho2 <;> first | rfl | exact absurd ⟨_, by assumption, hoo⟩ hnd.1 | exact absurd ⟨_, by assumption, hoo.symm⟩ hnd.1 | exact ih hnd.2 ho1 ho2
      subst heq; rw [recordCliOpt_lookupCli_same, List.mem_cons] at hv'; rcases hv' with rfl | hv' <;> first | exact ⟨hm, hrep, hnl⟩ | exact hinv.2 o ho' v' hv'
    · rw [recordCliOpt_lookupCli_ne _ _ _ _ hoo] at hv'; exact hinv.2 o ho' v' hv'
private theorem cliOptsInv_weaken_sub {visibleOpts subOpts : List OptSpec} {cliOpts : List (String × List OptValue)}
    (hnd : ((visibleOpts ++ subOpts).map (·.name)).Nodup) (hinv : CliOptsInv visibleOpts cliOpts) : CliOptsInv (visibleOpts ++ subOpts) cliOpts := by
  refine ⟨fun k hk => ?_, fun o ho v hv => ?_⟩
  · rcases hinv.1 k hk with ⟨opt, hmem, hname⟩; exact ⟨opt, List.mem_append_left subOpts hmem, hname⟩
  · rcases List.mem_append.mp ho with ho | ho
    · exact hinv.2 o ho v hv
    · have hne : lookupCli cliOpts o.name = [] := Classical.byContradiction fun hne => by
        rcases hinv.1 o.name hne with ⟨opt, hmem, hname⟩; rw [List.map_append, List.nodup_append] at hnd
        exact hnd.2.2 opt.name (List.mem_map.mpr ⟨opt, hmem, rfl⟩) o.name (List.mem_map.mpr ⟨o, ho, rfl⟩) hname
      rw [hne] at hv; cases hv
private theorem cliOptsInv_record_nonBool {visibleOpts : List OptSpec} {cliOpts : List (String × List OptValue)}
    (hnd : (visibleOpts.map (·.name)).Nodup) (hinv : CliOptsInv visibleOpts cliOpts) {opt : OptSpec} (ho : opt ∈ visibleOpts) (hnk : opt.kind ≠ .bool) {v : OptValue} (hm : OptValueMatchesKind opt.kind v) :
    CliOptsInv visibleOpts (Internal.recordCliOpt cliOpts opt.name v) :=
  cliOptsInv_record hnd hinv ho hm (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk) (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk)
private theorem parseShortBundle_inv (visibleOpts : List OptSpec) (shortHelp shortVersion : Bool)
    (rootName : String) (subPath : List String) (effVer : Option String) (curSpec : CommandSpec) (validators : CustomValidators) (hnd : (visibleOpts.map (·.name)).Nodup)
    (cliOpts : List (String × List OptValue)) (hinv : CliOptsInv visibleOpts cliOpts) (cs : List Char) {nextCli : List (String × List OptValue)} {nextPend : Option OptSpec}
    (h : Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath effVer curSpec validators cliOpts cs = .ok (nextCli, nextPend)) :
    CliOptsInv visibleOpts nextCli ∧ (∀ o, nextPend = some o → o ∈ visibleOpts ∧ o.kind ≠ .bool) := by
  induction cs generalizing cliOpts with
  | nil => unfold Internal.parseShortBundle at h; injection h with hp; injection hp with hc hp'; subst hc hp'; exact ⟨hinv, fun _ hc => by cases hc⟩
  | cons c rest ih =>
    unfold Internal.parseShortBundle at h
    split at h; · cases h
    · split at h; · cases effVer <;> cases h
      · cases hf : visibleOpts.find? (fun o => o.short == some c) with
        | none => simp [hf] at h
        | some opt =>
          simp only [hf] at h; have ho : opt ∈ visibleOpts := List.mem_of_find?_eq_some hf
          by_cases hbool : opt.kind == .bool
          · simp only [hbool, ↓reduceIte] at h; exact ih _ (cliOptsInv_record hnd hinv ho (by rw [valueKind_eq_of_beq hbool]; trivial) (fun _ => rfl) (fun _ => rfl)) h
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h; have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
            cases hr : rest.isEmpty with
            | false =>
              simp only [show (!rest.isEmpty) = true by simp [hr], ↓reduceIte, parseOptValueWithFast_eq] at h
              cases hp : Model.parseOptValueWith opt.kind (String.ofList rest) validators with
              | error _ => simp [hp, Bind.bind, Except.bind] at h
              | ok v => simp only [hp, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨hc, hnp⟩; subst hc hnp; exact ⟨cliOptsInv_record_nonBool hnd hinv ho hnk (parseOptValueWith_ok_matchesKind hp), fun _ hc => by cases hc⟩
            | true =>
              simp only [show (!rest.isEmpty) = false by simp [hr], Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨hc, hnp⟩; subst hc hnp; exact ⟨hinv, fun o heq => by injection heq with ho'; subst ho'; exact ⟨ho, hnk⟩⟩
private theorem findSubcommandPath_go_step_aux (g : List OptSpec) (v : Option String) (cur sub : CommandSpec) (path : List String)
    (hfind : cur.subcommands.find? (fun s => s.name == sub.name) = some sub) :
    ∀ g0 v0 node, Model.findSubcommandPath.go g0 v0 node path = .ok (g, v, cur) → Model.findSubcommandPath.go g0 v0 node (path ++ [sub.name]) = .ok (g ++ cur.options, sub.version <|> v, sub) := by
  intro g0 v0 node; induction path generalizing g0 v0 node with
  | nil => intro hp0; unfold Model.findSubcommandPath.go at hp0; injection hp0 with hp'; injection hp' with hg ht; injection ht with hv hc; subst hg hv hc; simp [Model.findSubcommandPath.go, hfind]
  | cons p _ ih =>
    intro hp0; unfold Model.findSubcommandPath.go at hp0
    cases hfp : node.subcommands.find? (fun s => s.name == p) with
    | none => simp [hfp] at hp0
    | some next => simp only [hfp] at hp0; simp only [List.cons_append, Model.findSubcommandPath.go, hfp]; exact ih _ _ next hp0
/-- Advancing `findSubcommandPath.go` by one child subcommand step. -/
theorem findSubcommandPath_go_step (g : List OptSpec) (v : Option String) (root cur sub : CommandSpec) (path : List String)
    (hp : Model.findSubcommandPath.go [] none root path = .ok (g, v, cur)) (hfind : cur.subcommands.find? (fun s => s.name == sub.name) = some sub) :
    Model.findSubcommandPath.go [] none root (path ++ [sub.name]) = .ok (g ++ cur.options, sub.version <|> v, sub) :=
  findSubcommandPath_go_step_aux g v cur sub path hfind [] none root hp
/-- Loop invariant threaded across `parseTokensLoop`. -/
def ParseStateInv (rootSpec : CommandSpec) (st : Internal.ParseState) : Prop :=
  (∃ verParent, NodeInv st.curSpec st.inheritedGlobals verParent ∧ st.effectiveVersion = (st.curSpec.version <|> verParent)) ∧
  Model.findSubcommandPath rootSpec st.subPath = .ok (st.inheritedGlobals, st.effectiveVersion, st.curSpec) ∧
  CliOptsInv (st.inheritedGlobals ++ st.curSpec.options) st.cliOpts ∧
  (∀ o, st.pendingOpt = some o → o ∈ st.inheritedGlobals ++ st.curSpec.options ∧ o.kind ≠ .bool)
private theorem stepToken_sound (rootSpec : CommandSpec) {validators : CustomValidators} (st nextSt : Internal.ParseState) (tok : String)
    (hinv : ParseStateInv rootSpec st) (h : Internal.stepToken rootSpec.name validators st tok = .ok nextSt) : ParseStateInv rootSpec nextSt := by
  rcases hinv with ⟨⟨vp, hnode, heff⟩, hpath, hcli, hpend⟩
  have hprops := nodeInv_props hnode; have hndNames := hprops.nodupNames; unfold Internal.stepToken at h
  cases hp : st.pendingOpt with
  | some opt =>
    rw [hp] at h; dsimp only at h; rw [parseOptValueWithFast_eq] at h
    cases hpv : Model.parseOptValueWith opt.kind tok validators with
    | error _ => simp [hpv, Bind.bind, Except.bind] at h
    | ok v => simp only [hpv, Bind.bind, Except.bind, Except.ok.injEq] at h; subst h; rcases hpend opt hp with ⟨ho, hnk⟩; exact ⟨⟨vp, hnode, heff⟩, hpath, cliOptsInv_record_nonBool hndNames hcli ho hnk (parseOptValueWith_ok_matchesKind hpv), fun _ hc => by cases hc⟩
  | none =>
    rw [hp] at h; dsimp only at h
    by_cases had : st.afterDashDash
    · simp only [had, ↓reduceIte, Except.ok.injEq] at h; subst h; exact ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩
    · simp only [had, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hdd : tok == "--"
      · simp only [hdd, ↓reduceIte, Except.ok.injEq] at h; subst h; exact ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩
      · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hhelp : tok == "--help"; · simp [hhelp] at h
        · simp only [hhelp, Bool.false_eq_true, ↓reduceIte] at h; by_cases hver : (tok == "--version" && st.effectiveVersion.isSome)
          · simp only [hver, ↓reduceIte] at h; cases hev : st.effectiveVersion <;> simp [hev] at h
          · simp only [hver, Bool.false_eq_true, ↓reduceIte] at h; split at h
            · split at h; · cases h
              · split at h; · cases h
                · rename_i longRest _ _ _; cases hlkp : Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) (Internal.splitFirstEq (String.ofList longRest)).fst with | none => simp [hlkp] at h | some p =>
                    rcases p with ⟨opt, isNeg⟩; simp only [hlkp] at h; rcases lookupLongOpt_mem hlkp with ⟨ho, hln, hneg⟩; by_cases hin : isNeg
                    · simp only [hin, ↓reduceIte] at h; cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with | some _ => rw [heqv] at h; cases h | none =>
                        rw [heqv] at h; injection h with hst; subst hst; rcases hneg hin with ⟨hk, hnr⟩
                        exact ⟨⟨vp, hnode, heff⟩, hpath, cliOptsInv_record hndNames hcli ho (v := .bool false) (by rw [hk]; trivial) (fun hb => by rw [hnr, Bool.and_false] at hb; cases hb) (fun hb => by rw [hln, Bool.and_false] at hb; cases hb), fun _ hc => by cases hc⟩
                    · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h; by_cases hbool : opt.kind == .bool
                      · simp only [hbool, ↓reduceIte] at h; have hk := valueKind_eq_of_beq hbool; cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                        | none => rw [heqv] at h; injection h with hst; subst hst; exact ⟨⟨vp, hnode, heff⟩, hpath, cliOptsInv_record hndNames hcli ho (v := .bool true) (by rw [hk]; trivial) (fun _ => rfl) (fun _ => rfl), fun _ hc => by cases hc⟩
                        | some rawVal => rw [heqv] at h; dsimp only at h; rw [parseOptValueFast_eq] at h; cases hpv : Model.parseOptValue .bool rawVal with | error _ => rw [hpv] at h; cases h | ok ov => cases ov with
                          | bool b =>
                            rw [hpv] at h; dsimp only at h; split at h; · cases h
                            · rename_i hnb; injection h with hst; subst hst; exact ⟨⟨vp, hnode, heff⟩, hpath, cliOptsInv_record hndNames hcli ho (v := .bool b) (by rw [hk]; trivial) (fun hb => by cases hb' : b <;> first | rfl | (rw [hb'] at hnb; simp [(Bool.and_eq_true _ _).mp hb |>.2] at hnb)) (fun hnl => by rw [hln, Bool.and_false] at hnl; cases hnl), fun _ hc => by cases hc⟩
                          | _ => rw [hpv] at h; cases h
                      · simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h; have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
                        cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                        | some rawVal => rw [heqv] at h; dsimp only at h; rw [parseOptValueWithFast_eq] at h; cases hpv : Model.parseOptValueWith opt.kind rawVal validators with | error _ => rw [hpv] at h; cases h | ok v => rw [hpv] at h; simp only [Bind.bind, Except.bind, Except.ok.injEq] at h; subst h; exact ⟨⟨vp, hnode, heff⟩, hpath, cliOptsInv_record_nonBool hndNames hcli ho hnk (parseOptValueWith_ok_matchesKind hpv), fun _ hc => by cases hc⟩
                        | none => rw [heqv] at h; injection h with hst; subst hst; exact ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun o ho' => by injection ho' with heq; subst heq; exact ⟨ho, hnk⟩⟩
            · rename_i c shortRest _ _; cases hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c :: shortRest) with | error _ => rw [hsb] at h; cases h | ok p =>
                rcases p with ⟨nextCli, nextPend⟩; rw [hsb] at h; simp only [Bind.bind, Except.bind, Except.ok.injEq] at h; subst h
                rcases parseShortBundle_inv (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators hndNames st.cliOpts hcli (c :: shortRest) hsb with ⟨hcli', hpend'⟩; exact ⟨⟨vp, hnode, heff⟩, hpath, hcli', hpend'⟩
            · split at h
              · cases hfs : st.curSpec.subcommands.find? (fun s => s.name == tok) with | none => simp [hfs] at h | some sub =>
                  simp only [hfs, Except.ok.injEq] at h; subst h; have hs := List.mem_of_find?_eq_some hfs; have hsubNode := nodeInv_sub hnode hs; rw [← heff] at hsubNode; have hsubProps := nodeInv_props hsubNode
                  have hfm : st.curSpec.subcommands.filterMap (fun s => some s.name) = st.curSpec.subcommands.map (·.name) := by clear hsubNode hsubProps hs hfs; induction st.curSpec.subcommands <;> simp [*]
                  have hfind := find?_unique_key (fun s => some s.name) st.curSpec.subcommands (by rw [hfm]; exact hprops.nodupSubs) sub hs sub.name rfl
                  exact ⟨⟨st.effectiveVersion, hsubNode, rfl⟩, findSubcommandPath_go_step st.inheritedGlobals st.effectiveVersion rootSpec st.curSpec sub st.subPath hpath hfind, cliOptsInv_weaken_sub hsubProps.nodupNames hcli, fun _ hc => by cases hc⟩
              · injection h with hst; subst hst; exact ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩
/-- `parseTokensLoop` preserves `ParseStateInv`. -/
theorem parseTokensLoop_sound (rootSpec : CommandSpec) {validators : CustomValidators} (st : Internal.ParseState) (hinv : ParseStateInv rootSpec st) (toks : List String) {finalState : Internal.ParseState} (h : Internal.parseTokensLoop rootSpec.name validators st toks = .ok finalState) : ParseStateInv rootSpec finalState := by
  induction toks generalizing st with | nil => unfold Internal.parseTokensLoop at h; injection h with hs; subst hs; exact hinv | cons t _ ih => unfold Internal.parseTokensLoop at h; cases hs : Internal.stepToken rootSpec.name validators st t with | error _ => simp [hs, Bind.bind, Except.bind] at h | ok st' => simp only [hs, Bind.bind, Except.bind] at h; exact ih st' (stepToken_sound rootSpec st st' t hinv hs) h
/-- `parseTokens` preserves `ParseStateInv` and clears `pendingOpt`. -/
theorem parseTokens_sound (rootSpec : CommandSpec) {validators : CustomValidators} (st : Internal.ParseState) (hinv : ParseStateInv rootSpec st) (toks : List String) {finalState : Internal.ParseState} (h : Internal.parseTokens rootSpec.name validators st toks = .ok finalState) : ParseStateInv rootSpec finalState ∧ finalState.pendingOpt = none := by
  unfold Internal.parseTokens at h; cases hl : Internal.parseTokensLoop rootSpec.name validators st toks with | error _ => simp [hl, Bind.bind, Except.bind] at h | ok fs =>
    simp only [hl, Bind.bind, Except.bind] at h; cases hp : fs.pendingOpt with | some _ => simp [hp] at h | none =>
      simp only [hp, Except.ok.injEq] at h; subst h; have ⟨h1, h2, ⟨h3a, h3b⟩, _⟩ := parseTokensLoop_sound rootSpec st hinv toks hl
      refine ⟨⟨h1, h2, ⟨fun k hk => ?_, fun opt ho v hv => ?_⟩, fun _ hc => by cases hc⟩, rfl⟩
      · rw [lookupCli_map_rev] at hk; exact h3a k (fun hnil => hk (by rw [hnil]; rfl))
      · rw [lookupCli_map_rev, List.mem_reverse] at hv; exact h3b opt ho v hv
/-- Concatenation law for `parseTokensLoop`. -/
theorem parseTokensLoop_append (rootName : String) (validators : CustomValidators) (toks1 toks2 : List String) (st st1 : Internal.ParseState) (h1 : Internal.parseTokensLoop rootName validators st toks1 = .ok st1) : Internal.parseTokensLoop rootName validators st (toks1 ++ toks2) = Internal.parseTokensLoop rootName validators st1 toks2 := by
  induction toks1 generalizing st with | nil => unfold Internal.parseTokensLoop at h1; injection h1 with hs; subst hs; rfl | cons t _ ih =>
    simp only [List.cons_append]; unfold Internal.parseTokensLoop at h1; conv => lhs; unfold Internal.parseTokensLoop
    cases hs : Internal.stepToken rootName validators st t with | error _ => simp [hs, Bind.bind, Except.bind] at h1 | ok st' => simp only [hs, Bind.bind, Except.bind] at h1 ⊢; exact ih st' h1
/-- `isValidOptLocal` properties for a long option. -/
theorem isValidOptLocal_long_props {opt : OptSpec} (h : Model.isValidOptLocal opt = true) {l : String} (hl : opt.long = some l) :
    l.toList ≠ [] ∧ l ≠ "help" ∧ l ≠ "version" ∧ '=' ∉ l.toList ∧ (∀ cs, l.toList ≠ '-' :: cs) ∧ (opt.kind = .bool → Model.startsWithNoDash l = false) := by
  unfold Model.isValidOptLocal at h; rw [hl] at h; simp only [Bool.and_eq_true] at h; have hln := h.1.1.1.1.1.1.2.1; have hnb := h.1.1.1.1.1.1.2.2; unfold Model.isValidLongName at hln
  split at hln <;> first | cases hln | (
    rename_i hne1 hne2; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hln; have hneq : '=' ∉ l.toList := fun hm => by have hp := List.all_eq_true.mp hln.1.1 '=' hm; simp [Model.isForbiddenIdentChar] at hp
    refine ⟨hne1, hln.1.2, hln.2, hneq, hne2, fun hk => ?_⟩; rw [hk] at hnb; have hvb : (ValueKind.bool == ValueKind.bool) = true := rfl; rw [hvb] at hnb; simp only [↓reduceIte, Bool.not_eq_true'] at hnb; exact hnb)
/-- `isValidOptLocal` guarantees short flag char is not `'-'`. -/
theorem isValidOptLocal_short_ne_dash {opt : OptSpec} (h : Model.isValidOptLocal opt = true) {c : Char} (hs : opt.short = some c) : c ≠ '-' := by
  unfold Model.isValidOptLocal at h; rw [hs] at h; simp only [Bool.and_eq_true] at h
  have hsc := h.1.1.1.1.1.2; unfold Model.isValidShortChar at hsc; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsc; exact hsc.1.1.1.1
/-- `isValidCommandName` ensures non-empty and not starting with `'-'`. -/
theorem isValidCommandName_props {name : String} (h : Model.isValidCommandName name = true) : name.toList ≠ [] ∧ ∀ cs, name.toList ≠ '-' :: cs := by
  unfold Model.isValidCommandName at h
  cases htl : name.toList with
  | nil => rw [htl] at h; cases h
  | cons c _ => refine ⟨by simp, fun _ hcon => ?_⟩; have : c = '-' := (List.cons.inj hcon).1; subst this; rw [htl] at h; cases h
/-- Any token whose `toList` differs from `"--"`, `"--help"`, `"--version"` is unequal to all three. -/
theorem ne_special_of_toList (s : String) (h1 : s.toList ≠ ['-', '-']) (h2 : s.toList ≠ ['-', '-', 'h', 'e', 'l', 'p']) (h3 : s.toList ≠ ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n']) :
    s ≠ "--" ∧ s ≠ "--help" ∧ s ≠ "--version" := ⟨fun h => h1 (congrArg String.toList h), fun h => h2 (congrArg String.toList h), fun h => h3 (congrArg String.toList h)⟩
private theorem resolveOptionsTR_go_id (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) (validators : CustomValidators) (accRev : List (String × List OptValue)) :
    Internal.resolveOptionsTR.go (m := Id) Internal.pureNoEnvOps.getEnv cliOpts validators visibleOpts accRev =
      match Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators with | .error e => .error e | .ok tail => .ok (accRev.reverse ++ tail) := by
  induction visibleOpts generalizing accRev with
  | nil => simp [Internal.resolveOptionsTR.go, Model.resolveOptions, pure]
  | cons opt rest ih =>
    unfold Internal.resolveOptionsTR.go Model.resolveOptions; dsimp only [bind, pure]; rw [resolveSingleOptionFast_eq]
    cases Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) validators with
    | error _ => rfl
    | ok res? => cases res? <;> (dsimp only; rw [ih]; cases Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts validators <;> simp [List.append_assoc])
/-- `Internal.resolveOptionsTR` under `pureNoEnvOps` equals `Model.resolveOptions`. -/
theorem resolveOptionsTR_id_eq (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) (validators : CustomValidators) :
    Internal.resolveOptionsTR (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators = Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators := by
  unfold Internal.resolveOptionsTR; rw [resolveOptionsTR_go_id]; cases Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators <;> simp
private theorem resolveArgsTR_parseMany_eq (validators : CustomValidators) (arg : ArgSpec) (xs : List String) (accRev : List OptValue) :
    Internal.resolveArgsTR.parseManyTR validators arg accRev xs =
      match Model.resolveArgs.parseMany validators arg xs with | .error e => .error e | .ok vs => .ok (accRev.reverse ++ vs) := by
  induction xs generalizing accRev with
  | nil => simp [Internal.resolveArgsTR.parseManyTR, Model.resolveArgs.parseMany]
  | cons s ss ih =>
    unfold Internal.resolveArgsTR.parseManyTR Model.resolveArgs.parseMany; dsimp only [bind, pure, Except.bind, Except.pure]; rw [parseOptValueWithFast_eq]
    cases Model.parseOptValueWith arg.kind s validators with | error _ => rfl | ok _ => dsimp only; rw [ih]; cases Model.resolveArgs.parseMany validators arg ss <;> simp [List.append_assoc]
private theorem resolveArgsTR_go_eq (validators : CustomValidators) (argSpecs : List ArgSpec) (rawPos : List String) (accRev : List (String × List OptValue)) :
    Internal.resolveArgsTR.go validators argSpecs rawPos accRev =
      match Model.resolveArgs.go validators argSpecs rawPos with | .error e => .error e | .ok tail => .ok (accRev.reverse ++ tail) := by
  induction argSpecs generalizing rawPos accRev with
  | nil => cases rawPos <;> simp [Internal.resolveArgsTR.go, Model.resolveArgs.go]
  | cons arg restArgs ih =>
    unfold Internal.resolveArgsTR.go Model.resolveArgs.go; dsimp only [bind, pure, Except.bind, Except.pure]; simp only [parseOptValueWithFast_eq]
    split
    · split
      · split
        · rfl
        · cases arg.default with | none => exact ih [] accRev | some _ => dsimp only; cases Model.parseOptValueWith arg.kind _ validators <;> first | rfl | (dsimp only; rw [ih]; cases Model.resolveArgs.go validators restArgs [] <;> simp [List.append_assoc])
      · rw [resolveArgsTR_parseMany_eq]; cases Model.resolveArgs.parseMany validators arg rawPos <;> first | rfl | (dsimp only; rw [ih]; cases Model.resolveArgs.go validators restArgs [] <;> simp [List.append_assoc])
    · cases rawPos with
      | cons _ remPos => dsimp only; cases Model.parseOptValueWith arg.kind _ validators <;> first | rfl | (dsimp only; rw [ih]; cases Model.resolveArgs.go validators restArgs remPos <;> simp [List.append_assoc])
      | nil =>
        dsimp only; split
        · rfl
        · cases arg.default with | none => exact ih [] accRev | some _ => dsimp only; cases Model.parseOptValueWith arg.kind _ validators <;> first | rfl | (dsimp only; rw [ih]; cases Model.resolveArgs.go validators restArgs [] <;> simp [List.append_assoc])
/-- `Internal.resolveArgsTR` equals `Model.resolveArgs`. -/
theorem resolveArgsTR_eq (argSpecs : List ArgSpec) (rawPos : List String) (validators : CustomValidators) :
    Internal.resolveArgsTR argSpecs rawPos validators = Model.resolveArgs argSpecs rawPos validators := by
  unfold Internal.resolveArgsTR Model.resolveArgs; rw [resolveArgsTR_go_eq]; cases Model.resolveArgs.go validators argSpecs rawPos <;> simp
private theorem collectLongsTR_go_eq (opts : List OptSpec) (accRev : List String) : Internal.collectLongsTR.go accRev opts = accRev.reverse ++ Model.collectVisibleLongs opts := by
  induction opts generalizing accRev with | nil => simp [Internal.collectLongsTR.go, Model.collectVisibleLongs] | cons opt rest ih =>
    unfold Internal.collectLongsTR.go Model.collectVisibleLongs; simp only [List.foldr_cons]; cases opt.long with | none => exact ih accRev | some _ => cases opt.kind == .bool <;> cases opt.repeatable <;> simp [ih, Model.collectVisibleLongs, List.append_assoc]
private theorem collectLongsTR_eq (opts : List OptSpec) : Internal.collectLongsTR opts = Model.collectVisibleLongs opts := by unfold Internal.collectLongsTR; rw [collectLongsTR_go_eq]; simp
private theorem allDistinct_eq_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : Model.allDistinct xs = true ↔ xs.Nodup := by
  induction xs with | nil => simp [Model.allDistinct] | cons _ _ ih => simp [Model.allDistinct, List.nodup_cons, ih]
private theorem allDistinct_append {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α) : Model.allDistinct (xs ++ ys) = (Model.allDistinct xs && Model.allDistinct ys && ys.all (fun y => !xs.contains y)) := by
  apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, allDistinct_eq_nodup, List.nodup_append, List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, List.contains_iff_mem, ne_eq]
  exact ⟨fun ⟨h1, h2, hd⟩ => ⟨⟨h1, h2⟩, fun y hy hm => hd y hm y hy rfl⟩, fun ⟨⟨h1, h2⟩, hd⟩ => ⟨h1, h2, fun _ hx _ hy heq => hd _ hy (heq ▸ hx)⟩⟩
private theorem insert_mem_cons {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (seen : Std.HashSet α) (base : List α) (y : α) (hm : ∀ a, seen.contains a = base.contains a) :
    ∀ a, (seen.insert y).contains a = (y :: base).contains a := fun a => by
  rw [Std.HashSet.contains_insert, hm a, List.contains_cons]; exact Bool.eq_iff_iff.mpr (by simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]; exact or_congr_left eq_comm)
private theorem insertDistinctSet_isSome {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (seen : Std.HashSet α) (base ys : List α) (hm : ∀ a, seen.contains a = base.contains a) :
    (Internal.insertDistinctSet seen ys).isSome = (Model.allDistinct ys && ys.all (fun y => !base.contains y)) := by
  induction ys generalizing seen base with
  | nil => simp [Internal.insertDistinctSet, Model.allDistinct]
  | cons y rest ih =>
    unfold Internal.insertDistinctSet Model.allDistinct; rw [hm y]
    by_cases h : base.contains y
    · simp only [h, ↓reduceIte, Option.isSome_none, List.all_cons, Bool.not_true, Bool.false_and, Bool.and_false]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.not_false, List.all_cons, Bool.true_and, ih _ (y :: base) (insert_mem_cons seen base y hm)]
      have hall : rest.all (fun z => !(y :: base).contains z) = (!rest.contains y && rest.all (fun z => !base.contains z)) := by
        clear ih; induction rest with | nil => rfl | cons z _ ihr =>
          have hzy : (z == y) = (y == z) := Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
          simp only [List.all_cons, List.contains_cons, Bool.not_or] at ihr ⊢; rw [ihr]; simp only [hzy]; ac_rfl
      rw [hall]; ac_rfl
private theorem insertDistinctSet_some_mem {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (seen s' : Std.HashSet α) (base ys : List α) (hm : ∀ a, seen.contains a = base.contains a)
    (hs : Internal.insertDistinctSet seen ys = some s') : ∀ a, s'.contains a = (base ++ ys).contains a := by
  induction ys generalizing seen base with
  | nil => simp [Internal.insertDistinctSet] at hs; subst hs; simpa using hm
  | cons _ _ ih =>
    unfold Internal.insertDistinctSet at hs; split at hs
    · cases hs
    · intro a; rw [ih _ _ (insert_mem_cons seen base _ hm) hs a]; apply Bool.eq_iff_iff.mpr; simp only [List.contains_iff_mem, List.mem_append, List.mem_cons]
      exact ⟨fun h => by rcases h with (rfl | hb) | hr <;> simp [*], fun h => by rcases h with hb | rfl | hr <;> simp [*]⟩
private def ValidCtxInv (ctx : Internal.ValidCtx) (baseOpts : List OptSpec) : Prop :=
  Model.allDistinct (baseOpts.map (·.name)) = true ∧ (∀ a, ctx.optNames.contains a = (baseOpts.map (·.name)).contains a) ∧
  Model.allDistinct (Model.collectVisibleLongs baseOpts) = true ∧ (∀ a, ctx.longs.contains a = (Model.collectVisibleLongs baseOpts).contains a) ∧
  Model.allDistinct (baseOpts.filterMap (·.short)) = true ∧ (∀ a, ctx.shorts.contains a = (baseOpts.filterMap (·.short)).contains a) ∧
  Model.allDistinct (baseOpts.filterMap (·.envVar)) = true ∧ (∀ a, ctx.envKeys.contains a = (baseOpts.filterMap (·.envVar)).contains a)
private theorem validCtxInv_empty : ValidCtxInv {} [] :=
  ⟨rfl, fun _ => Std.HashSet.contains_empty, rfl, fun _ => Std.HashSet.contains_empty, rfl, fun _ => Std.HashSet.contains_empty, rfl, fun _ => Std.HashSet.contains_empty⟩
private theorem collectVisibleLongs_append (xs ys : List OptSpec) :
    Model.collectVisibleLongs (xs ++ ys) = Model.collectVisibleLongs xs ++ Model.collectVisibleLongs ys := by
  have hgen : ∀ (zs : List OptSpec) (init : List String),
      List.foldr (fun (opt : OptSpec) (acc : List String) => match opt.long with | none => acc | some l => if opt.kind == .bool && !opt.repeatable then l :: ("no-" ++ l) :: acc else l :: acc) init zs =
      List.foldr (fun (opt : OptSpec) (acc : List String) => match opt.long with | none => acc | some l => if opt.kind == .bool && !opt.repeatable then l :: ("no-" ++ l) :: acc else l :: acc) [] zs ++ init := by
    intro zs init; induction zs with | nil => rfl | cons z r ih =>
      simp only [List.foldr_cons]; cases z.long with | none => exact ih | some l => by_cases hb : (z.kind == .bool && !z.repeatable) = true <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, ih, List.cons_append]
  unfold Model.collectVisibleLongs; rw [List.foldr_append]; exact hgen xs _
private theorem optStepMatches {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (seen : Std.HashSet α) (base add : List α) (hm : ∀ a, seen.contains a = base.contains a) (hBase : Model.allDistinct base = true)
    (emptyCond : Bool) (hEmp : emptyCond = true → add = []) :
    let res? := if emptyCond then some seen else Internal.insertDistinctSet seen add
    res?.isSome = Model.allDistinct (base ++ add) ∧
      (∀ s', res? = some s' → Model.allDistinct (base ++ add) = true ∧ ∀ a, s'.contains a = (base ++ add).contains a) := by
  by_cases he : emptyCond = true
  · have hadd := hEmp he; subst hadd; simp only [he, ↓reduceIte, Option.isSome_some, List.append_nil, hBase, Option.some.injEq]
    exact ⟨trivial, fun s' hs => ⟨trivial, fun a => hs ▸ hm a⟩⟩
  · have hm' : (Internal.insertDistinctSet seen add).isSome = Model.allDistinct (base ++ add) := by
      rw [insertDistinctSet_isSome seen base add hm, allDistinct_append, hBase, Bool.true_and]
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hm', fun s' hs => ⟨?_, insertDistinctSet_some_mem seen s' base add hm hs⟩⟩; rw [← hm', hs]; rfl
private theorem isValidSubcommandList_iff_all (subs : List CommandSpec) (opts : List OptSpec) (ver : Option String) : Model.isValidSubcommandList subs opts ver = true ↔ ∀ s ∈ subs, Model.isValidCommandNode s opts ver = true := by
  induction subs with | nil => simp [Model.isValidSubcommandList] | cons s rest ih => simp [Model.isValidSubcommandList, ih]
private theorem checkCommandNodeStep_iff (node : CommandSpec) (ctx : Internal.ValidCtx) (baseOpts : List OptSpec) (hInv : ValidCtxInv ctx baseOpts) :
    (∀ nextCtx, Internal.checkCommandNodeStep node ctx = some nextCtx → ValidCtxInv nextCtx (baseOpts ++ node.options) ∧ nextCtx.effVer = (node.version <|> ctx.effVer) ∧ Model.isValidCommandNode node baseOpts ctx.effVer = Model.isValidSubcommandList node.subcommands (baseOpts ++ node.options) (node.version <|> ctx.effVer)) ∧
    (Internal.checkCommandNodeStep node ctx = none → Model.isValidCommandNode node baseOpts ctx.effVer = false) := by
  rcases hInv with ⟨h1d, h1m, h2d, h2m, h3d, h3m, h4d, h4m⟩; cases node with | mk name version about shortHelp shortVersion options args subcommands =>
    have ho1 := optStepMatches ctx.optNames (baseOpts.map (·.name)) (options.map (·.name)) h1m h1d options.isEmpty (by intro h; simp [List.isEmpty_iff.mp h])
    have ho2 := optStepMatches ctx.longs (Model.collectVisibleLongs baseOpts) (Model.collectVisibleLongs options) h2m h2d options.isEmpty (by intro h; simp [List.isEmpty_iff.mp h, Model.collectVisibleLongs])
    have ho3 := optStepMatches ctx.shorts (baseOpts.filterMap (·.short)) (options.filterMap (·.short)) h3m h3d options.isEmpty (by intro h; simp [List.isEmpty_iff.mp h])
    have ho4 := optStepMatches ctx.envKeys (baseOpts.filterMap (·.envVar)) (options.filterMap (·.envVar)) h4m h4d options.isEmpty (by intro h; simp [List.isEmpty_iff.mp h])
    unfold Internal.checkCommandNodeStep Model.isValidCommandNode; dsimp only; simp only [List.map_append, List.filterMap_append, collectVisibleLongs_append, collectLongsTR_eq]
    cases hR1 : (if options.isEmpty then some ctx.optNames else Internal.insertDistinctSet ctx.optNames (options.map (·.name))) with
    | none => simp [show Model.allDistinct (baseOpts.map (·.name) ++ options.map (·.name)) = false by rw [← ho1.1, hR1]; rfl]
    | some s1 => have hs1 := ho1.2 s1 hR1; cases hR2 : (if options.isEmpty then some ctx.longs else Internal.insertDistinctSet ctx.longs (Model.collectVisibleLongs options)) with
      | none => simp [hs1.1, show Model.allDistinct (Model.collectVisibleLongs baseOpts ++ Model.collectVisibleLongs options) = false by rw [← ho2.1, hR2]; rfl]
      | some s2 => have hs2 := ho2.2 s2 hR2; cases hR3 : (if options.isEmpty then some ctx.shorts else Internal.insertDistinctSet ctx.shorts (options.filterMap (·.short))) with
        | none => simp [hs1.1, hs2.1, show Model.allDistinct (baseOpts.filterMap (·.short) ++ options.filterMap (·.short)) = false by rw [← ho3.1, hR3]; rfl]
        | some s3 => have hs3 := ho3.2 s3 hR3; cases hR4 : (if options.isEmpty then some ctx.envKeys else Internal.insertDistinctSet ctx.envKeys (options.filterMap (·.envVar))) with
          | none => simp [hs1.1, hs2.1, hs3.1, show Model.allDistinct (baseOpts.filterMap (·.envVar) ++ options.filterMap (·.envVar)) = false by rw [← ho4.1, hR4]; rfl]
          | some s4 =>
            have hs4 := ho4.2 s4 hR4
            have hargD : (Internal.insertDistinctSet ({} : Std.HashSet String) (args.map (·.name))).isSome = Model.allDistinct (args.map (·.name)) := by rw [insertDistinctSet_isSome _ [] _ (fun _ => Std.HashSet.contains_empty)]; simp [List.all_eq_true]
            have hsubD : (Internal.insertDistinctSet ({} : Std.HashSet String) (subcommands.map (·.name))).isSome = Model.allDistinct (subcommands.map (·.name)) := by rw [insertDistinctSet_isSome _ [] _ (fun _ => Std.HashSet.contains_empty)]; simp [List.all_eq_true]
            have hargDisj : args.all (fun a => !s1.contains a.name) = (args.map (·.name)).all (fun a => !(baseOpts.map (·.name) ++ options.map (·.name)).contains a) := by rw [List.all_map]; congr 1; funext a; rw [hs1.2 a.name]; rfl
            have hOptEq : Internal.isValidOptLocal = Model.isValidOptLocal := funext internal_isValidOptLocal_eq
            have hArgEq : Internal.isValidArg = Model.isValidArg := funext internal_isValidArg_eq
            simp only [hs1.1, hs2.1, hs3.1, hs4.1, hs3.2 'h', hs3.2 'V', hargD, hsubD, hargDisj, Bool.and_true, internal_isValidCommandName_eq, hOptEq, hArgEq, internal_validArgOrder_eq]
            by_cases hok : (Model.isValidCommandName name && options.all Model.isValidOptLocal && (!shortHelp || !(baseOpts.filterMap (·.short) ++ options.filterMap (·.short)).contains 'h') && (!(shortVersion && (version <|> ctx.effVer).isSome) || !(baseOpts.filterMap (·.short) ++ options.filterMap (·.short)).contains 'V') && args.all Model.isValidArg && Model.allDistinct (args.map (·.name)) && (args.map (·.name)).all (fun a => !(baseOpts.map (·.name) ++ options.map (·.name)).contains a) && Model.validArgOrder false false args && (if subcommands.isEmpty then true else args.isEmpty && options.all (·.global)) && Model.allDistinct (subcommands.map (·.name))) = true
            · simp only [hok, ↓reduceIte, ValidCtxInv, List.map_append, List.filterMap_append, collectVisibleLongs_append, Bool.true_and]; exact ⟨fun _ hnc => by injection hnc with he; subst he; exact ⟨⟨hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2⟩, rfl, trivial⟩, fun hc => (by cases hc)⟩
            · have hokf : _ = false := Bool.eq_false_iff.mpr hok; simp only [hokf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]; exact ⟨fun _ hc => (by cases hc), fun _ => trivial⟩
private theorem mem_pushValidChildren {subs : List CommandSpec} {ctx : Internal.ValidCtx} {acc : List (CommandSpec × Internal.ValidCtx)} {p : CommandSpec × Internal.ValidCtx} : p ∈ Internal.pushValidChildren subs ctx acc ↔ (∃ s ∈ subs, p = (s, ctx)) ∨ p ∈ acc := by
  unfold Internal.pushValidChildren; induction subs generalizing acc with | nil => simp | cons s _ ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]; exact ⟨by rintro (⟨t, ht, hpt⟩ | (rfl | ha)); exact Or.inl ⟨t, Or.inr ht, hpt⟩; exact Or.inl ⟨s, Or.inl rfl, rfl⟩; exact Or.inr ha, by rintro (⟨t, rfl | ht, hpt⟩ | ha); exact Or.inr (Or.inl hpt); exact Or.inl ⟨t, ht, hpt⟩; exact Or.inr (Or.inr ha)⟩
private theorem isValidCommandNode_congr (node : CommandSpec) (ctx : Internal.ValidCtx) (b1 b2 : List OptSpec) (h1 : ValidCtxInv ctx b1) (h2 : ValidCtxInv ctx b2) : Model.isValidCommandNode node b1 ctx.effVer = Model.isValidCommandNode node b2 ctx.effVer := by
  have hs1 := checkCommandNodeStep_iff node ctx b1 h1; have hs2 := checkCommandNodeStep_iff node ctx b2 h2
  cases hChk : Internal.checkCommandNodeStep node ctx with | none => rw [hs1.2 hChk, hs2.2 hChk] | some nextCtx =>
    have hA := hs1.1 nextCtx hChk; have hB := hs2.1 nextCtx hChk; rw [hA.2.2, hB.2.2, Bool.eq_iff_iff, isValidSubcommandList_iff_all, isValidSubcommandList_iff_all]
    have ih : ∀ s ∈ node.subcommands, Model.isValidCommandNode s (b1 ++ node.options) (node.version <|> ctx.effVer) = Model.isValidCommandNode s (b2 ++ node.options) (node.version <|> ctx.effVer) := fun s hs => by have hSub := isValidCommandNode_congr s nextCtx (b1 ++ node.options) (b2 ++ node.options) hA.1 hB.1; rwa [hA.2.1] at hSub
    exact ⟨fun h s hs => ih s hs ▸ h s hs, fun h s hs => (ih s hs).symm ▸ h s hs⟩
termination_by sizeOf node
decreasing_by have hmem := List.sizeOf_lt_of_mem hs; have hlt := Internal.sizeOf_subcommands_lt_node node; omega
private theorem isValidSpecWorklist_iff (wl : List (CommandSpec × Internal.ValidCtx)) (hInvAll : ∀ p ∈ wl, ∃ baseOpts, ValidCtxInv p.2 baseOpts) :
    Internal.isValidSpecWorklist wl = true ↔ ∀ p ∈ wl, ∀ baseOpts, ValidCtxInv p.2 baseOpts → Model.isValidCommandNode p.1 baseOpts p.2.effVer = true := by
  induction hM : Internal.validWorklistMeasure wl using Nat.strongRecOn generalizing wl with | _ m ih => cases wl with | nil => simp [Internal.isValidSpecWorklist] | cons hd rest =>
    rcases hd with ⟨node, ctx⟩; unfold Internal.isValidSpecWorklist; rcases hInvAll (node, ctx) List.mem_cons_self with ⟨base0, hCtx0⟩; have hStep0 := checkCommandNodeStep_iff node ctx base0 hCtx0
    cases hChk : Internal.checkCommandNodeStep node ctx with
    | none => simp only [Bool.false_eq_true, false_iff]; intro h; have hf := h (node, ctx) List.mem_cons_self base0 hCtx0; rw [hStep0.2 hChk] at hf; cases hf
    | some nextCtx =>
      rcases hStep0.1 nextCtx hChk with ⟨hNextInv, hEff, hEqNode⟩
      have hInvPush : ∀ p ∈ Internal.pushValidChildren node.subcommands nextCtx rest, ∃ baseOpts, ValidCtxInv p.2 baseOpts := by
        intro p hp; rw [mem_pushValidChildren] at hp; rcases hp with ⟨_, _, rfl⟩ | hpr; exact ⟨base0 ++ node.options, hNextInv⟩; exact hInvAll p (List.mem_cons_of_mem _ hpr)
      have hLt : Internal.validWorklistMeasure (Internal.pushValidChildren node.subcommands nextCtx rest) < m := by
        rw [← hM]; have ha := Internal.validWorklistMeasure_pushChildren node.subcommands nextCtx rest; have hb := Internal.validWorklistMeasure_cons (node, ctx) rest; have hc := Internal.sizeOf_subcommands_lt_node node; dsimp only at hb; omega
      dsimp only; rw [ih _ hLt _ hInvPush rfl]; constructor
      · intro hRec p hp b hCb; rcases List.mem_cons.mp hp with rfl | hpr
        · rcases (checkCommandNodeStep_iff node ctx b hCb).1 nextCtx hChk with ⟨hNb, hEb, hEqB⟩; rw [hEqB, isValidSubcommandList_iff_all]; intro s hs
          have hsT := hRec (s, nextCtx) (mem_pushValidChildren.mpr (Or.inl ⟨s, hs, rfl⟩)) (b ++ node.options) hNb; rwa [hEb] at hsT
        · exact hRec p (mem_pushValidChildren.mpr (Or.inr hpr)) b hCb
      · intro hAll p hp b hCb; rw [mem_pushValidChildren] at hp; rcases hp with ⟨s, hs, rfl⟩ | hpr
        · have hN := hAll (node, ctx) List.mem_cons_self base0 hCtx0; rw [hEqNode, isValidSubcommandList_iff_all] at hN; have hS := hN s hs; rw [← hEff] at hS; rwa [isValidCommandNode_congr s nextCtx b (base0 ++ node.options) hCb hNextInv]
        · exact hAll p (List.mem_cons_of_mem _ hpr) b hCb
/-- `Internal.isValidSpecTR` equals `Model.isValidSpec`. -/
theorem isValidSpecTR_eq (spec : CommandSpec) : Internal.isValidSpecTR spec = Model.isValidSpec spec := by
  unfold Internal.isValidSpecTR Model.isValidSpec; apply Bool.eq_iff_iff.mpr
  have hInv : ∀ p ∈ [(spec, ({} : Internal.ValidCtx))], ∃ baseOpts, ValidCtxInv p.2 baseOpts := fun p hp => by rcases List.mem_singleton.mp hp with rfl; exact ⟨[], validCtxInv_empty⟩
  rw [isValidSpecWorklist_iff _ hInv]; exact ⟨fun h => h (spec, {}) List.mem_cons_self [] validCtxInv_empty, fun h p hp b hCb => by rcases List.mem_singleton.mp hp with rfl; rwa [isValidCommandNode_congr spec {} b [] hCb validCtxInv_empty]⟩
private theorem rep_add (a b : Nat) (c : Char) : List.replicate a c ++ List.replicate b c = List.replicate (a + b) c := by
  induction a with | zero => simp | succ a ih => simp [List.replicate_succ, Nat.succ_add, ih]
private theorem toDigits10_zero_pow (q : Nat) (hq : 0 < q) : ∀ k : Nat, Nat.toDigits 10 (q * 10 ^ k) = Nat.toDigits 10 q ++ List.replicate k '0'
  | 0 => by simp
  | k + 1 => by
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 10, ← Nat.add_zero (10 * (q * 10 ^ k)),
      ← Nat.toDigits_append_toDigits (by decide) (Nat.mul_pos hq (Nat.pow_pos (by decide))) (by decide),
      toDigits10_zero_pow q hq k, show Nat.toDigits 10 0 = ['0'] from rfl, List.replicate_succ', List.append_assoc]
private theorem toDigits10_split : ∀ w q r : Nat, 0 < w → 0 < q → r < 10 ^ w →
    Nat.toDigits 10 (q * 10 ^ w + r) = Nat.toDigits 10 q ++ List.replicate (w - (Nat.toDigits 10 r).length) '0' ++ Nat.toDigits 10 r
  | 0, _, _, hw, _, _ => by omega
  | 1, q, r, _, hq, hr => by
    have hr10 : r < 10 := by simpa using hr
    have hlen : (Nat.toDigits 10 r).length = 1 := Nat.le_antisymm ((Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by simpa using hr10)) Nat.length_toDigits_pos
    rw [hlen]; simp only [Nat.pow_one, Nat.sub_self, List.replicate_zero, List.append_nil]; rw [Nat.mul_comm q 10]; exact (Nat.toDigits_append_toDigits (by decide) hq hr10).symm
  | w + 2, q, r, _, hq, hr => by
    have hpow : q * 10 ^ (w + 2) = 10 * (q * 10 ^ (w + 1)) := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 10]
    by_cases hr10 : r < 10
    · have hlen : (Nat.toDigits 10 r).length = 1 := Nat.le_antisymm ((Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by simpa using hr10)) Nat.length_toDigits_pos
      rw [hpow, ← Nat.toDigits_append_toDigits (by decide) (Nat.mul_pos hq (Nat.pow_pos (by decide))) hr10, toDigits10_zero_pow q hq (w + 1), hlen]; simp [List.append_assoc]
    · have hrq : 0 < r / 10 := Nat.div_pos (Nat.le_of_not_lt hr10) (by decide)
      have hrlt : r / 10 < 10 ^ (w + 1) := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using hr)
      rw [show q * 10 ^ (w + 2) + r = 10 * (q * 10 ^ (w + 1) + r / 10) + r % 10 from by rw [hpow]; omega,
        ← Nat.toDigits_append_toDigits (by decide) (Nat.add_pos_right _ hrq) (Nat.mod_lt r (by decide)), toDigits10_split (w + 1) q (r / 10) (by omega) hq hrlt]
      have hlenMod : (Nat.toDigits 10 (r % 10)).length = 1 := Nat.le_antisymm ((Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by simpa using Nat.mod_lt r (by decide))) Nat.length_toDigits_pos
      have hrD : Nat.toDigits 10 r = Nat.toDigits 10 (r / 10) ++ Nat.toDigits 10 (r % 10) := ((Nat.toDigits_append_toDigits (by decide) hrq (Nat.mod_lt r (by decide))).trans (congrArg (Nat.toDigits 10) (by omega))).symm
      have hlenLe : (Nat.toDigits 10 (r / 10)).length ≤ w + 1 := (Nat.length_toDigits_le_iff (by decide) (by omega)).mpr hrlt
      rw [hrD, List.length_append, hlenMod]; simp only [List.append_assoc]; congr 2; rw [show w + 1 - (Nat.toDigits 10 (r / 10)).length = w + 2 - ((Nat.toDigits 10 (r / 10)).length + 1) from by omega]
private def ladderW : List (Nat × Nat) → Nat | [] => 18 | _ :: rest => 2 * ladderW rest
private def ladderOk : List (Nat × Nat) → Prop | [] => True | (b, _) :: rest => b = 10 ^ ladderW rest ∧ ladderOk rest
private def padZeroList (w n : Nat) : List Char := List.replicate (w - (Nat.toDigits 10 n).length) '0' ++ Nat.toDigits 10 n
private theorem buildPow10Ladder_ok (n fuel b w : Nat) (acc : List (Nat × Nat)) (hb : b = 10 ^ w) (hw : w = ladderW acc) (ha : ladderOk acc) : ladderOk (Internal.buildPow10Ladder n fuel b w acc) := by
  induction fuel generalizing b w acc with
  | zero => exact ha
  | succ _ ih => unfold Internal.buildPow10Ladder; split <;> first | exact ha | exact ih (b * b) (w + w) ((b, w) :: acc) (by rw [hb, ← Nat.pow_add]) (by simp [ladderW, hw]; omega) ⟨hb.trans (congrArg (10 ^ ·) hw), ha⟩
private theorem padZeroList_split (w q r : Nat) (hw : 0 < w) (hq : q < 10 ^ w) (hr : r < 10 ^ w) : padZeroList w q ++ padZeroList w r = padZeroList (2 * w) (q * 10 ^ w + r) := by
  unfold padZeroList; have hlenR : (Nat.toDigits 10 r).length ≤ w := (Nat.length_toDigits_le_iff (by decide) hw).mpr hr
  have hlenQ : (Nat.toDigits 10 q).length ≤ w := (Nat.length_toDigits_le_iff (by decide) hw).mpr hq
  by_cases hq0 : q = 0
  · subst hq0; simp only [Nat.zero_mul, Nat.zero_add, show Nat.toDigits 10 0 = ['0'] from rfl, List.length_cons, List.length_nil, Nat.zero_add]
    rw [← List.append_assoc, show List.replicate (w - 1) '0' ++ ['0'] = List.replicate w '0' from by rw [← List.replicate_succ', Nat.sub_add_cancel hw], rep_add]
    have hlen1 : 1 ≤ (Nat.toDigits 10 r).length := Nat.length_toDigits_pos; congr 2; omega
  · rw [toDigits10_split w q r hw (Nat.pos_of_ne_zero hq0) hr, List.length_append, List.length_append, List.length_replicate,
      show 2 * w - ((Nat.toDigits 10 q).length + (w - (Nat.toDigits 10 r).length) + (Nat.toDigits 10 r).length) = w - (Nat.toDigits 10 q).length from by omega]; simp only [List.append_assoc]
private theorem ladderW_pos (l : List (Nat × Nat)) : 0 < ladderW l := by induction l with | nil => simp [ladderW] | cons _ _ ih => simp [ladderW]; omega
private theorem pushNatChunks_eq (l : List (Nat × Nat)) (hl : ladderOk l) :
    ∀ pad n acc, (pad = false → Internal.pushNatChunks l false n acc = acc ++ toString n) ∧ (pad = true → n < 10 ^ ladderW l → Internal.pushNatChunks l true n acc = acc ++ String.ofList (padZeroList (ladderW l) n)) := by
  induction l with
  | nil =>
    intro pad n acc; constructor
    · intro _; simp [Internal.pushNatChunks]
    · intro _ _; simp only [Internal.pushNatChunks, ladderW, Bool.true_and, padZeroList, Nat.toString_eq_ofList_toDigits, String.length_ofList]
      by_cases hlt : (Nat.toDigits 10 n).length < 18
      · simp [hlt, String.append_assoc, String.ofList_append]
      · simp [hlt, show 18 - (Nat.toDigits 10 n).length = 0 from by omega]
  | cons hd rest ih =>
    rcases hd with ⟨bHalf, _⟩; rcases hl with ⟨hb, hrest⟩; intro pad n acc; constructor
    · intro _; unfold Internal.pushNatChunks; simp only [Bool.not_false, Bool.true_and]
      by_cases hlt : n < bHalf
      · simp only [hlt, decide_true, ↓reduceIte]; exact (ih hrest false n acc).1 rfl
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hpos : 0 < n / bHalf := Nat.div_pos (Nat.le_of_not_lt hlt) (hb ▸ Nat.pow_pos (by decide))
        have hmod : n % bHalf < 10 ^ ladderW rest := hb ▸ Nat.mod_lt n (hb ▸ Nat.pow_pos (by decide))
        rw [(ih hrest false (n / bHalf) acc).1 rfl, (ih hrest true (n % bHalf) _).2 rfl hmod, String.append_assoc]; congr 1
        unfold padZeroList; simp only [Nat.toString_eq_ofList_toDigits, ← String.ofList_append, ← List.append_assoc]
        rw [← toDigits10_split (ladderW rest) (n / bHalf) (n % bHalf) (ladderW_pos rest) hpos hmod, ← hb, Nat.div_add_mod']
    · intro _ hnlt; unfold Internal.pushNatChunks; simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hdivlt : n / bHalf < 10 ^ ladderW rest := by rw [hb]; rw [ladderW, Nat.two_mul, Nat.pow_add] at hnlt; exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr hnlt
      have hmodlt : n % bHalf < 10 ^ ladderW rest := hb ▸ Nat.mod_lt n (hb ▸ Nat.pow_pos (by decide))
      rw [(ih hrest true (n / bHalf) acc).2 rfl hdivlt, (ih hrest true (n % bHalf) _).2 rfl hmodlt, String.append_assoc]; congr 1
      rw [← String.ofList_append, padZeroList_split (ladderW rest) (n / bHalf) (n % bHalf) (ladderW_pos rest) hdivlt hmodlt]; simp only [ladderW]; rw [← hb, Nat.div_add_mod']
private theorem natToStringFast_eq (n : Nat) : Internal.natToStringFast n = toString n := by
  unfold Internal.natToStringFast; dsimp only; split <;> first | rfl | (rw [(pushNatChunks_eq _ (buildPow10Ladder_ok n 32 1000000000000000000 18 [] rfl rfl trivial) false n "").1 rfl]; simp)
private theorem optValueToStringFast_eq (v : OptValue) : Internal.optValueToStringFast v = Model.optValueToString v := by
  cases v with | nat _ => simp [Internal.optValueToStringFast, Model.optValueToString, natToStringFast_eq] | int z => cases z <;> simp [Internal.optValueToStringFast, Model.optValueToString, natToStringFast_eq] <;> rfl | _ => rfl
private theorem revFoldl_cons_eq {α : Type} (xs acc : List α) : xs.reverse.foldl (fun a x => x :: a) acc = xs ++ acc := by
  have h : ∀ (ys a : List α), ys.foldl (fun a x => x :: a) a = ys.reverse ++ a := fun ys => by induction ys with | nil => simp | cons _ _ ih => intro a; simp [ih, List.append_assoc]
  rw [h, List.reverse_reverse]
private theorem flattenChunksRev_eq (chunksRev : List (List OptSpec)) : Internal.flattenChunksRev chunksRev = chunksRev.reverse.flatten := by
  unfold Internal.flattenChunksRev
  suffices h : ∀ acc, chunksRev.foldl (fun a xs => xs.reverse.foldl (fun r x => x :: r) a) acc = chunksRev.reverse.flatten ++ acc by have h0 := h []; simp only [List.append_nil] at h0; exact h0
  induction chunksRev with | nil => intro acc; simp | cons c cs ih =>
    intro acc; rw [List.foldl_cons]; change cs.foldl (fun a xs => xs.reverse.foldl (fun r x => x :: r) a) (c.reverse.foldl (fun r x => x :: r) acc) = _
    rw [revFoldl_cons_eq c acc, ih (c ++ acc)]; simp [List.reverse_cons, List.flatten_append, List.append_assoc]
/-- `Internal.findSubcommandPathTR` equals `Model.findSubcommandPath`. -/
theorem findSubcommandPathTR_eq (spec : CommandSpec) (path : List String) : Internal.findSubcommandPathTR spec path = Model.findSubcommandPath spec path := by
  unfold Internal.findSubcommandPathTR Model.findSubcommandPath
  have hgo : ∀ (gRev : List (List OptSpec)) (prevVer : Option String) (cur : CommandSpec) (p : List String),
      Internal.findSubcommandPathTR.go gRev (cur.version <|> prevVer) cur p = Model.findSubcommandPath.go (Internal.flattenChunksRev gRev) prevVer cur p := by
    intro gRev prevVer cur p; induction p generalizing gRev prevVer cur with
    | nil => simp [Internal.findSubcommandPathTR.go, Model.findSubcommandPath.go]
    | cons name rest ih =>
      unfold Internal.findSubcommandPathTR.go Model.findSubcommandPath.go
      cases cur.subcommands.find? (fun s => s.name == name) with
      | none => rfl
      | some sub => dsimp only; rw [ih (cur.options :: gRev) (cur.version <|> prevVer) sub, flattenChunksRev_eq, List.reverse_cons, List.flatten_append, ← flattenChunksRev_eq]; simp
  have h0 := hgo [] none spec path; rwa [show (spec.version <|> none) = spec.version from by cases spec.version <;> rfl, flattenChunksRev_eq] at h0
private theorem buildParsedOptMap_lookup (opts : List (String × List OptValue)) (k : String) : (Internal.buildParsedOptMap opts)[k]? = (opts.find? (fun p => p.1 == k)).map (·.2) := by
  unfold Internal.buildParsedOptMap
  have hfold : ∀ (xs : List (String × List OptValue)) (m : Std.HashMap String (List OptValue)), (xs.reverse.foldl (fun a p => a.insert p.1 p.2) m)[k]? = (((xs.find? (fun p => p.1 == k)).map (·.2)) <|> m[k]?) := by
    intro xs; induction xs with | nil => intro m; simp | cons p _ ih =>
      intro m; rcases p with ⟨pk, _⟩; simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.getElem?_insert, List.find?_cons]
      by_cases hpk : pk == k
      · simp [hpk]
      · simp only [hpk, Bool.false_eq_true, ↓reduceIte]; exact ih m
  simpa using hfold opts {}
private theorem renderValueListTR_eq (opt : OptSpec) (vals : List OptValue) (accRev : List String) : Internal.renderValueListTR opt vals accRev = match Model.renderSingleOpt.renderValueList opt vals with | .error e => .error e | .ok tail => .ok (accRev.reverse ++ tail) := by
  induction vals generalizing accRev with | nil => simp [Internal.renderValueListTR, Model.renderSingleOpt.renderValueList] | cons v vs ih =>
    unfold Internal.renderValueListTR Model.renderSingleOpt.renderValueList; dsimp only; by_cases hneg : (opt.kind == .bool && v != .bool true) = true; · simp [hneg]
    · simp only [hneg, Bool.false_eq_true, ↓reduceIte, optValueToStringFast_eq]; cases opt.long with
      | some _ => by_cases hb : (opt.kind == .bool) = true <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, ih] <;> cases Model.renderSingleOpt.renderValueList opt vs <;> simp [List.append_assoc]
      | none => cases opt.short with | none => rfl | some _ => by_cases hb : (opt.kind == .bool) = true <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, ih] <;> cases Model.renderSingleOpt.renderValueList opt vs <;> simp [List.append_assoc]
private theorem renderSingleOptTR_eq (opt : OptSpec) (vals : List OptValue) : Internal.renderSingleOptTR opt vals = Model.renderSingleOpt opt vals := by
  unfold Internal.renderSingleOptTR Model.renderSingleOpt; split <;> first | rfl | (split <;> first | rfl | (rw [renderValueListTR_eq]; cases Model.renderSingleOpt.renderValueList opt vals <;> simp))
private theorem renderOptsTR_eq (optMap : Std.HashMap String (List OptValue)) (parsed : ParsedCmd) (hMap : ∀ k, optMap[k]? = (parsed.options.find? (fun p => p.1 == k)).map (·.2)) (opts : List OptSpec) (accRev : List String) : Internal.renderOptsTR optMap opts accRev = match Model.renderArgs.renderOpts parsed opts with | .error e => .error e | .ok tail => .ok (accRev.reverse ++ tail) := by
  induction opts generalizing accRev with | nil => simp [Internal.renderOptsTR, Model.renderArgs.renderOpts] | cons opt rest ih =>
    unfold Internal.renderOptsTR Model.renderArgs.renderOpts; dsimp only [Bind.bind, Except.bind]
    have hEq : optMap[opt.name]?.getD [] = match parsed.options.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => [] := by rw [hMap opt.name]; cases parsed.options.find? (fun p => p.1 == opt.name) <;> rfl
    rw [hEq, renderSingleOptTR_eq]
    cases Model.renderSingleOpt opt (match parsed.options.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) with | error _ => rfl | ok _ => dsimp only; rw [ih]; cases Model.renderArgs.renderOpts parsed rest <;> simp [List.append_assoc]
/-- `Internal.renderArgsTR` equals `Model.renderArgs`. -/
theorem renderArgsTR_eq (spec : CommandSpec) (parsed : ParsedCmd) : Internal.renderArgsTR spec parsed = Model.renderArgs spec parsed := by
  unfold Internal.renderArgsTR Model.renderArgs; rw [isValidSpecTR_eq, findSubcommandPathTR_eq]; dsimp only [Bind.bind, Except.bind]
  split <;> first | rfl | (cases Model.findSubcommandPath spec parsed.subcommandPath with | error _ => rfl | ok _ => dsimp only; split <;> first | rfl | (rw [renderOptsTR_eq _ parsed (buildParsedOptMap_lookup parsed.options)]; cases Model.renderArgs.renderOpts parsed _ <;> simp))
private theorem find?_eq_none_of_any_false {α : Type} (p : α → Bool) (xs : List α) (h : xs.any p = false) : xs.find? p = none := by
  induction xs with | nil => rfl | cons x xs ih => simp only [List.any_cons, Bool.or_eq_false_iff] at h; simp [h.1, ih h.2]
private theorem find?_isSome_of_any_true {α : Type} (p : α → Bool) (xs : List α) (h : xs.any p = true) : (xs.find? p).isSome = true := by
  induction xs with | nil => cases h | cons x xs ih => simp only [List.any_cons, Bool.or_eq_true] at h; unfold List.find?; rcases h with hx | hxs <;> first | simp [hx] | by_cases hx : p x <;> simp [hx, ih hxs]
private theorem lookupCli_recordCliOpt (cliOpts : List (String × List OptValue)) (name k : String) (v : OptValue) :
    lookupCli (Internal.recordCliOpt cliOpts name v) k = if name == k then v :: lookupCli cliOpts k else lookupCli cliOpts k := by
  unfold Internal.recordCliOpt
  have hgo : ∀ accRev, lookupCli (Internal.recordCliOpt.go name v accRev cliOpts) k =
      if accRev.reverse.any (fun p => p.1 == k) then lookupCli accRev.reverse k else if name == k then v :: lookupCli cliOpts k else lookupCli cliOpts k := by
    induction cliOpts with
    | nil =>
      intro accRev; simp only [Internal.recordCliOpt.go, lookupCli, List.find?_append]
      by_cases ha : accRev.reverse.any (fun p => p.1 == k)
      · have hs := find?_isSome_of_any_true (fun p => p.1 == k) accRev.reverse ha; cases hf : accRev.reverse.find? (fun p => p.1 == k) <;> simp_all
      · have hn := find?_eq_none_of_any_false (fun p => p.1 == k) accRev.reverse (Bool.eq_false_iff.mpr ha)
        simp only [ha, Bool.false_eq_true, ↓reduceIte, hn]; by_cases hnk : name == k <;> simp [hnk]
    | cons p rest ih =>
      intro accRev; rcases p with ⟨pk, pvs⟩; unfold Internal.recordCliOpt.go
      by_cases hpn : pk == name
      · simp only [hpn, ↓reduceIte, lookupCli, List.find?_append, List.find?_cons]
        by_cases ha : accRev.reverse.any (fun q => q.1 == k)
        · have hs := find?_isSome_of_any_true (fun q => q.1 == k) accRev.reverse ha; cases hf : accRev.reverse.find? (fun q => q.1 == k) <;> simp_all
        · have hn := find?_eq_none_of_any_false (fun q => q.1 == k) accRev.reverse (Bool.eq_false_iff.mpr ha)
          simp only [ha, Bool.false_eq_true, ↓reduceIte, hn]; rw [beq_iff_eq.mp hpn]; by_cases hnk : name == k <;> simp [hnk]
      · simp only [hpn, Bool.false_eq_true, ↓reduceIte]; rw [ih ((pk, pvs) :: accRev)]
        simp only [List.reverse_cons, List.any_append, List.any_cons, List.any_nil, Bool.or_false, lookupCli, List.find?_append, List.find?_cons]
        by_cases ha : accRev.reverse.any (fun q => q.1 == k)
        · have hs := find?_isSome_of_any_true (fun q => q.1 == k) accRev.reverse ha; cases hf : accRev.reverse.find? (fun q => q.1 == k) <;> simp_all
        · have hn := find?_eq_none_of_any_false (fun q => q.1 == k) accRev.reverse (Bool.eq_false_iff.mpr ha)
          simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_or, hn]
          by_cases hpk : pk == k
          · have hne : (name == k) = false := beq_eq_false_iff_ne.mpr fun h => hpn (beq_iff_eq.mpr (h ▸ (beq_iff_eq.mp hpk))); simp [hpk, hne]
          · simp [hpk]
  simpa [lookupCli] using hgo []
private theorem recordCliFast_matches (cliMap : Std.HashMap String (List OptValue)) (cliOpts : List (String × List OptValue)) (hm : ∀ k, cliMap[k]?.getD [] = lookupCli cliOpts k) (name : String) (v : OptValue) :
    ∀ k, (Internal.recordCliFast cliMap name v)[k]?.getD [] = lookupCli (Internal.recordCliOpt cliOpts name v) k := by
  intro k; unfold Internal.recordCliFast; rw [Std.HashMap.getElem?_alter, lookupCli_recordCliOpt]
  by_cases hnk : name == k
  · simp only [hnk, ↓reduceIte]; rw [beq_iff_eq.mp hnk]; have hmk := hm k; cases hcm : cliMap[k]? <;> simp_all
  · simp only [hnk, Bool.false_eq_true, ↓reduceIte]; exact hm k
private theorem addOptOne_matches (vis : List OptSpec) (opt : OptSpec) (hLongNd : (Model.collectVisibleLongs (vis ++ [opt])).Nodup) (hShortNd : ((vis ++ [opt]).filterMap (·.short)).Nodup)
    (lm : Std.HashMap String (OptSpec × Bool)) (sm : Std.HashMap Char OptSpec) (hlm : ∀ k, lm[k]? = Internal.lookupLongOpt vis k) (hsm : ∀ c, sm[c]? = vis.find? (fun o => o.short == some c)) :
    let lm1 := match opt.long with | none => lm | some l => let lm0 := lm.insert l (opt, false); if opt.kind == ValueKind.bool && !opt.repeatable then lm0.insert ("no-" ++ l) (opt, true) else lm0
    let sm1 := match opt.short with | none => sm | some c => sm.insert c opt
    (∀ k, lm1[k]? = Internal.lookupLongOpt (vis ++ [opt]) k) ∧ (∀ c, sm1[c]? = (vis ++ [opt]).find? (fun o => o.short == some c)) := by
  constructor
  · intro k; rw [collectVisibleLongs_eq_flatMap, List.flatMap_append] at hLongNd; cases hl : opt.long with
    | none => dsimp only; rw [hlm k]; unfold Internal.lookupLongOpt; rw [internal_startsWithNoDash_eq]; simp only [List.find?_append, List.find?_cons, List.find?_nil, hl]; cases vis.find? (fun o => o.long == some k) with | some _ => simp | none => by_cases hnd : Model.startsWithNoDash k = true <;> simp [hnd]
    | some l =>
      dsimp only; by_cases hBool : (opt.kind == ValueKind.bool && !opt.repeatable)
      · simp only [hBool, ↓reduceIte]
        by_cases hkNeg : k == ("no-" ++ l)
        · rw [beq_iff_eq.mp hkNeg]; simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
          have hkBool : opt.kind = .bool := valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hBool).1
          have hnr : opt.repeatable = false := by have := ((Bool.and_eq_true _ _).mp hBool).2; simpa using this
          exact (lookupLongOpt_neg (vis ++ [opt]) (by rw [collectVisibleLongs_eq_flatMap, List.flatMap_append]; exact hLongNd) (by simp) hkBool hnr hl).symm
        · simp only [Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr (fun h => hkNeg (beq_iff_eq.mpr h.symm)), Bool.false_eq_true, ↓reduceIte]
          by_cases hkPos : l == k
          · simp only [hkPos, ↓reduceIte]; rw [← beq_iff_eq.mp hkPos]; exact (lookupLongOpt_pos (vis ++ [opt]) (by rw [collectVisibleLongs_eq_flatMap, List.flatMap_append]; exact hLongNd) (by simp) hl).symm
          · have hkPos' : (l == k) = false := Bool.eq_false_iff.mpr hkPos; simp only [hkPos', Bool.false_eq_true, ↓reduceIte, hlm k]
            have hneNeg : k ≠ "no-" ++ l := fun h => hkNeg (beq_iff_eq.mpr h)
            unfold Internal.lookupLongOpt; simp only [List.find?_append, List.find?_cons, List.find?_nil, hl]
            cases hf1 : vis.find? (fun o => o.long == some k) with
            | some _ => simp
            | none =>
              simp only; split
              · cases hf2 : vis.find? (fun o => o.kind == .bool && !o.repeatable && o.long == some (String.ofList (k.toList.drop 3))) with
                | some _ => simp [hkPos']
                | none =>
                  simp only [Option.none_or]
                  have hneBase : (l == String.ofList (k.toList.drop 3)) = false := beq_eq_false_iff_ne.mpr fun heq => by
                    rename_i hsnd; rw [internal_startsWithNoDash_eq] at hsnd; unfold Model.startsWithNoDash at hsnd; have ht : k.toList.take 3 = ['n', 'o', '-'] := by simpa using hsnd
                    have hlen : k.toList = ['n', 'o', '-'] ++ k.toList.drop 3 := by rw [← ht, List.take_append_drop]
                    have hkStr : "no-" ++ String.ofList (k.toList.drop 3) = k := by rw [show "no-" = String.ofList ['n', 'o', '-'] from rfl, ← String.ofList_append]; simpa [String.ofList_toList] using congrArg String.ofList hlen.symm
                    exact hneNeg (hkStr ▸ congrArg ("no-" ++ ·) heq.symm)
                  simp [hkPos', hneBase]
              · simp [hkPos']
      · simp only [hBool, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_insert]
        by_cases hkPos : l == k
        · simp only [hkPos, ↓reduceIte]; rw [← beq_iff_eq.mp hkPos]; exact (lookupLongOpt_pos (vis ++ [opt]) (by rw [collectVisibleLongs_eq_flatMap, List.flatMap_append]; exact hLongNd) (by simp) hl).symm
        · have hkPos' : (l == k) = false := Bool.eq_false_iff.mpr hkPos; simp only [hkPos', Bool.false_eq_true, ↓reduceIte, hlm k]
          unfold Internal.lookupLongOpt; simp only [List.find?_append, List.find?_cons, List.find?_nil, hl]; cases hf1 : vis.find? (fun o => o.long == some k) with | some _ => simp | none => simp only; split <;> simp [hkPos', hBool]
  · intro c; rw [List.filterMap_append] at hShortNd; have hDisj := (List.nodup_append.mp hShortNd).2.2
    cases hs : opt.short with
    | none => dsimp only; rw [hsm c]; simp [List.find?_append, hs]
    | some sc =>
      dsimp only; rw [Std.HashMap.getElem?_insert]; by_cases hsc : sc == c
      · simp only [hsc, ↓reduceIte]; rw [← beq_iff_eq.mp hsc]
        have hf : vis.find? (fun o => o.short == some sc) = none := List.find?_eq_none.mpr fun o ho h => by rw [beq_iff_eq] at h; exact hDisj sc (List.mem_filterMap.mpr ⟨o, ho, h⟩) sc (by simp [hs]) rfl
        simp [List.find?_append, hf, hs]
      · have hsc' : (sc == c) = false := Bool.eq_false_iff.mpr hsc; simp only [hsc', Bool.false_eq_true, ↓reduceIte, hsm c, List.find?_append, List.find?_cons, List.find?_nil, hs]; cases vis.find? (fun o => o.short == some c) <;> simp [hsc']
private theorem addOptsMaps_matches (vis opts : List OptSpec) (hLongNd : (Model.collectVisibleLongs (vis ++ opts)).Nodup) (hShortNd : ((vis ++ opts).filterMap (·.short)).Nodup)
    (lm : Std.HashMap String (OptSpec × Bool)) (sm : Std.HashMap Char OptSpec) (hlm : ∀ k, lm[k]? = Internal.lookupLongOpt vis k) (hsm : ∀ c, sm[c]? = vis.find? (fun o => o.short == some c)) :
    let res := Internal.addOptsMaps lm sm opts; (∀ k, res.1[k]? = Internal.lookupLongOpt (vis ++ opts) k) ∧ (∀ c, res.2[c]? = (vis ++ opts).find? (fun o => o.short == some c)) := by
  induction opts generalizing vis lm sm with | nil => simpa [Internal.addOptsMaps] using ⟨hlm, hsm⟩ | cons opt rest ih =>
    unfold Internal.addOptsMaps
    have hSubL : (Model.collectVisibleLongs (vis ++ [opt])).Nodup := by rw [collectVisibleLongs_eq_flatMap] at hLongNd ⊢; rw [List.flatMap_append] at hLongNd ⊢; exact hLongNd.sublist (List.Sublist.append (List.Sublist.refl _) (by simp [List.flatMap_cons]))
    have hSubS : ((vis ++ [opt]).filterMap (·.short)).Nodup := by rw [List.filterMap_append] at hShortNd ⊢; exact hShortNd.sublist (List.Sublist.append (List.Sublist.refl _) (by simp only [List.filterMap_cons]; cases opt.short <;> simp))
    have ⟨hl1, hs1⟩ := addOptOne_matches vis opt hSubL hSubS lm sm hlm hsm
    have hRes := ih (vis ++ [opt]) (by simpa [List.append_assoc] using hLongNd) (by simpa [List.append_assoc] using hShortNd) _ _ hl1 hs1
    rw [List.append_assoc] at hRes; exact hRes
private def FastStateInv (stF : Internal.FastParseState) (st : Internal.ParseState) : Prop :=
  stF.curSpec = st.curSpec ∧ stF.subPathRev = st.subPath.reverse ∧ Internal.flattenChunksRev stF.visibleChunksRev = st.inheritedGlobals ++ st.curSpec.options ∧
  stF.effectiveVersion = st.effectiveVersion ∧ stF.afterDashDash = st.afterDashDash ∧ stF.pendingOpt = st.pendingOpt ∧ stF.rawPositionalsRev = st.rawPositionals ∧
  (∀ k, (stF.cliMap[k]?.getD []) = lookupCli st.cliOpts k) ∧ (∀ k, stF.longMap[k]? = Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) k) ∧
  (∀ c, stF.shortMap[c]? = (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some c))
private theorem parseShortBundleFast_eq (rootName : String) (validators : CustomValidators)
    (stF : Internal.FastParseState) (st : Internal.ParseState) (hF : FastStateInv stF st)
    (cliMap : Std.HashMap String (List OptValue)) (cliOpts : List (String × List OptValue))
    (hcli : ∀ k, cliMap[k]?.getD [] = lookupCli cliOpts k) (cs : List Char) :
    (match Internal.parseShortBundleFast stF.shortMap stF.curSpec.shortHelp stF.curSpec.shortVersion rootName stF validators cliMap cs,
           Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath st.effectiveVersion st.curSpec validators cliOpts cs with
     | .error e1, .error e2 => e1 = e2
     | .ok (m1, p1), .ok (c2, p2) => p1 = p2 ∧ ∀ k, m1[k]?.getD [] = lookupCli c2 k
     | _, _ => False) := by
  rcases hF with ⟨hCur, hPath, hVis, hEff, _, _, _, _, _, hShort⟩
  induction cs generalizing cliMap cliOpts with
  | nil => simp [Internal.parseShortBundleFast, Internal.parseShortBundle, hcli]
  | cons c rest ih =>
    unfold Internal.parseShortBundleFast Internal.parseShortBundle
    rw [hCur, hEff]
    by_cases hh : (c == 'h' && st.curSpec.shortHelp)
    · simp [hh, hPath, hVis, List.reverse_reverse]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte]
      by_cases hv : (c == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome)
      · simp only [hv, ↓reduceIte]; cases st.effectiveVersion <;> rfl
      · simp only [hv, Bool.false_eq_true, ↓reduceIte, hShort c]
        cases (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some c) with
        | none => rfl
        | some opt =>
          dsimp only
          by_cases hbool : opt.kind == .bool
          · simp only [hbool, ↓reduceIte]
            have hih := ih _ _ (recordCliFast_matches cliMap cliOpts hcli opt.name (.bool true))
            rw [hCur] at hih; exact hih
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte]
            by_cases hne : !rest.isEmpty
            · simp only [hne, ↓reduceIte, bind, Except.bind]
              cases Internal.parseOptValueWithFast opt.kind (String.ofList rest) validators with
              | error _ => rfl
              | ok v => exact ⟨rfl, recordCliFast_matches cliMap cliOpts hcli opt.name v⟩
            · simp only [hne, Bool.false_eq_true, ↓reduceIte]; simp [hcli]
private theorem stepSubOrPos_eq {vp : Option String} (stF : Internal.FastParseState) (st : Internal.ParseState) (tok : String)
    (hNode : NodeInv st.curSpec st.inheritedGlobals vp) (hF : FastStateInv stF st) :
    (match (if !stF.curSpec.subcommands.isEmpty && stF.rawPositionalsRev.isEmpty then
              match stF.curSpec.subcommands.find? (fun s => s.name == tok) with
              | some sub =>
                let p := Internal.addOptsMaps stF.longMap stF.shortMap sub.options
                Except.ok
                  ({ curSpec := sub
                     subPathRev := sub.name :: stF.subPathRev
                     visibleChunksRev := sub.options :: stF.visibleChunksRev
                     effectiveVersion := sub.version <|> stF.effectiveVersion
                     afterDashDash := false
                     pendingOpt := none
                     cliMap := stF.cliMap
                     rawPositionalsRev := []
                     longMap := p.1
                     shortMap := p.2 } : Internal.FastParseState)
              | none =>
                let hint := match Internal.bestSuggestion tok (stF.curSpec.subcommands.map (·.name)) with | some cand => s!"; did you mean '{cand}'?" | none => ""
                (Except.error ({ kind := .unknownSubcommand, message := s!"unknown subcommand '{tok}'{hint}", target := some tok } : CmdLineError) : Except CmdLineError Internal.FastParseState)
            else Except.ok { stF with afterDashDash := false, pendingOpt := none, rawPositionalsRev := tok :: stF.rawPositionalsRev }),
           (if !st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty then
              match st.curSpec.subcommands.find? (fun s => s.name == tok) with
              | some sub =>
                Except.ok
                  ({ curSpec := sub
                     subPath := st.subPath ++ [sub.name]
                     inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options
                     effectiveVersion := sub.version <|> st.effectiveVersion
                     afterDashDash := false
                     pendingOpt := none
                     cliOpts := st.cliOpts
                     rawPositionals := [] } : Internal.ParseState)
              | none =>
                let hint := match Internal.bestSuggestion tok (st.curSpec.subcommands.map (·.name)) with | some cand => s!"; did you mean '{cand}'?" | none => ""
                (Except.error ({ kind := .unknownSubcommand, message := s!"unknown subcommand '{tok}'{hint}", target := some tok } : CmdLineError) : Except CmdLineError Internal.ParseState)
            else Except.ok { st with afterDashDash := false, pendingOpt := none, rawPositionals := tok :: st.rawPositionals }) with
     | .error e1, .error e2 => e1 = e2
     | .ok stF', .ok st' => FastStateInv stF' st'
     | _, _ => False) := by
  rcases hF with ⟨hCur, hPath, hVis, hEff, hAdd, hPend, hPos, hCli, hLong, hShort⟩
  rw [hCur, hPos, hEff]
  by_cases hsp : (!st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty)
  · simp only [hsp, ↓reduceIte]
    cases hfs : st.curSpec.subcommands.find? (fun s => s.name == tok) with
    | none => rfl
    | some sub =>
      dsimp only
      have hs := List.mem_of_find?_eq_some hfs
      have hsubProps := nodeInv_props (nodeInv_sub hNode hs)
      have ⟨hLM, hSM⟩ := addOptsMaps_matches (st.inheritedGlobals ++ st.curSpec.options) sub.options hsubProps.nodupLongs hsubProps.nodupShorts stF.longMap stF.shortMap hLong hShort
      refine ⟨rfl, by simp [hPath], ?_, rfl, rfl, rfl, rfl, hCli, ?_, ?_⟩
      · rw [flattenChunksRev_eq, List.reverse_cons, List.flatten_append, ← flattenChunksRev_eq, hVis]; simp [List.append_assoc]
      · simpa [List.append_assoc] using hLM
      · simpa [List.append_assoc] using hSM
  · simp only [hsp, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hPath, hVis, rfl, rfl, rfl, by simp, hCli, hLong, hShort⟩
private theorem stepTokenFast_eq (rootSpec : CommandSpec) (validators : CustomValidators) (stF : Internal.FastParseState) (st : Internal.ParseState)
    (hInv : ParseStateInv rootSpec st) (hF : FastStateInv stF st) (tok : String) :
    (match Internal.stepTokenFast rootSpec.name validators stF tok, Internal.stepToken rootSpec.name validators st tok with
     | .error e1, .error e2 => e1 = e2 | .ok stF', .ok st' => FastStateInv stF' st' | _, _ => False) := by
  have hF0 := hF; rcases hInv with ⟨⟨vp, hNode, hEffNode⟩, _, _, _⟩; rcases hF with ⟨hCur, hPath, hVis, hEff, hAdd, hPend, hPos, hCli, hLong, hShort⟩
  cases hp : st.pendingOpt with
  | some opt =>
    have hpF : stF.pendingOpt = some opt := hPend.trans hp; unfold Internal.stepTokenFast Internal.stepToken; rw [hpF, hp]; dsimp only [bind, Except.bind]
    cases Internal.parseOptValueWithFast opt.kind tok validators with | error _ => rfl | ok v => exact ⟨hCur, hPath, hVis, hEff, hAdd, rfl, hPos, recordCliFast_matches stF.cliMap st.cliOpts hCli opt.name v, hLong, hShort⟩
  | none =>
    have hpF : stF.pendingOpt = none := hPend.trans hp
    by_cases had : st.afterDashDash
    · unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hAdd.trans had, had, ↓reduceIte]; exact ⟨hCur, hPath, hVis, hEff, rfl, rfl, by simp [hPos], hCli, hLong, hShort⟩
    · have hadF : (stF.afterDashDash = false) := by rw [hAdd]; exact Bool.eq_false_iff.mpr had
      have hadS : (st.afterDashDash = false) := Bool.eq_false_iff.mpr had
      by_cases hdd : tok == "--"
      · unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd, Bool.false_eq_true, ↓reduceIte]; exact ⟨hCur, hPath, hVis, hEff, rfl, rfl, hPos, hCli, hLong, hShort⟩
      · have hdd' : (tok == "--") = false := Bool.eq_false_iff.mpr hdd
        by_cases hh : tok == "--help"
        · unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd', hh, Bool.false_eq_true, ↓reduceIte]; simp [hCur, hPath, hVis, hEff, List.reverse_reverse]
        · have hh' : (tok == "--help") = false := Bool.eq_false_iff.mpr hh
          by_cases hv : (tok == "--version" && st.effectiveVersion.isSome)
          · unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd', hh', (by rw [hEff]; exact hv : (tok == "--version" && stF.effectiveVersion.isSome) = true), hv, Bool.false_eq_true, ↓reduceIte]; rw [hEff]; cases st.effectiveVersion <;> rfl
          · have hv' : (tok == "--version" && st.effectiveVersion.isSome) = false := Bool.eq_false_iff.mpr hv
            have hvF' : (tok == "--version" && stF.effectiveVersion.isSome) = false := by rw [hEff]; exact hv'
            cases htl : tok.toList with
            | nil => unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd', hh', hvF', hv', Bool.false_eq_true, ↓reduceIte, htl]; exact stepSubOrPos_eq stF st tok hNode hF0
            | cons c1 rest1 =>
              by_cases hc1 : c1 = '-'
              · subst hc1; cases hrest : rest1 with
                | nil => unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd', hh', hvF', hv', Bool.false_eq_true, ↓reduceIte, htl, hrest]; exact stepSubOrPos_eq stF st tok hNode hF0
                | cons c2 rest2 =>
                  by_cases hc2 : c2 = '-'
                  · subst hc2; unfold Internal.stepTokenFast Internal.stepToken; simp only [hpF, hp, hadF, hadS, hdd', hh', hvF', hv', Bool.false_eq_true, ↓reduceIte, htl, hrest]
                    by_cases hne : (Internal.splitFirstEq (String.ofList rest2)).fst.isEmpty
                    · simp [hne]
                    · simp only [hne, Bool.false_eq_true, ↓reduceIte, hEff]
                      by_cases hbi : ((Internal.splitFirstEq (String.ofList rest2)).fst == "help" || ((Internal.splitFirstEq (String.ofList rest2)).fst == "version" && st.effectiveVersion.isSome))
                      · simp [hbi]
                      · simp only [hbi, Bool.false_eq_true, ↓reduceIte, hLong]
                        cases Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) (Internal.splitFirstEq (String.ofList rest2)).fst with | none => simp [hVis] | some p =>
                          rcases p with ⟨opt, isNeg⟩; dsimp only; by_cases hin : isNeg
                          · simp only [hin, ↓reduceIte]; cases (Internal.splitFirstEq (String.ofList rest2)).snd with | some _ => rfl | none => exact ⟨hCur, hPath, hVis, rfl, rfl, rfl, hPos, recordCliFast_matches stF.cliMap st.cliOpts hCli opt.name (.bool false), hLong, hShort⟩
                          · simp only [hin, Bool.false_eq_true, ↓reduceIte]; by_cases hbool : opt.kind == .bool
                            · simp only [hbool, ↓reduceIte]; cases (Internal.splitFirstEq (String.ofList rest2)).snd with
                              | none => exact ⟨hCur, hPath, hVis, rfl, rfl, rfl, hPos, recordCliFast_matches stF.cliMap st.cliOpts hCli opt.name (.bool true), hLong, hShort⟩
                              | some rv => dsimp only; rw [parseOptValueFast_eq]; cases Model.parseOptValue .bool rv with | error _ => rfl | ok ov => cases ov with
                                | bool b =>
                                  dsimp only; by_cases hrep : (opt.repeatable && !b)
                                  · simp [hrep]
                                  · simp only [hrep, Bool.false_eq_true, ↓reduceIte]; exact ⟨hCur, hPath, hVis, rfl, rfl, rfl, hPos, recordCliFast_matches stF.cliMap st.cliOpts hCli opt.name (.bool b), hLong, hShort⟩
                                | _ => rfl
                            · simp only [hbool, Bool.false_eq_true, ↓reduceIte]; cases (Internal.splitFirstEq (String.ofList rest2)).snd with
                              | some rv => dsimp only [bind, Except.bind]; cases Internal.parseOptValueWithFast opt.kind rv validators with | error _ => rfl | ok v => exact ⟨hCur, hPath, hVis, rfl, rfl, rfl, hPos, recordCliFast_matches stF.cliMap st.cliOpts hCli opt.name v, hLong, hShort⟩
                              | none => exact ⟨hCur, hPath, hVis, rfl, rfl, rfl, hPos, hCli, hLong, hShort⟩
                  · have hStepF : Internal.stepTokenFast rootSpec.name validators stF tok = (match Internal.parseShortBundleFast stF.shortMap stF.curSpec.shortHelp stF.curSpec.shortVersion rootSpec.name stF validators stF.cliMap (c2 :: rest2) with | .error e => .error e | .ok (nextCliMap, nextPending) => .ok { stF with afterDashDash := false, cliMap := nextCliMap, pendingOpt := nextPending }) := by
                      unfold Internal.stepTokenFast; simp only [hpF, hadF, hdd', hh', hvF', Bool.false_eq_true, ↓reduceIte, htl, hrest]
                      split <;> first | (exfalso; rename_i heq; exact hc2 (List.cons.inj (List.cons.inj heq).2).1) | rfl | (rename_i heq; rw [heq])
                    have hStepS : Internal.stepToken rootSpec.name validators st tok = (do let (nextCliOpts, nextPending) ← Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2); .ok { st with afterDashDash := false, cliOpts := nextCliOpts, pendingOpt := nextPending }) := by
                      unfold Internal.stepToken; simp only [hp, hadS, hdd', hh', hv', Bool.false_eq_true, ↓reduceIte, htl, hrest]
                    rw [hStepF, hStepS]; have hsb := parseShortBundleFast_eq rootSpec.name validators stF st hF0 stF.cliMap st.cliOpts hCli (c2 :: rest2)
                    cases h1 : Internal.parseShortBundleFast stF.shortMap stF.curSpec.shortHelp stF.curSpec.shortVersion rootSpec.name stF validators stF.cliMap (c2 :: rest2) with
                    | error _ => cases h2 : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2) <;> rw [h1, h2] at hsb <;> first | (dsimp only [bind, Except.bind]; exact hsb) | cases hsb
                    | ok p1 => cases h2 : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2) with
                      | error _ => rw [h1, h2] at hsb; cases hsb
                      | ok p2 => rw [h1, h2] at hsb; dsimp only [bind, Except.bind]; exact ⟨hCur, hPath, hVis, hEff, rfl, hsb.1, hPos, hsb.2, hLong, hShort⟩
              · have hStepF : Internal.stepTokenFast rootSpec.name validators stF tok = (if !stF.curSpec.subcommands.isEmpty && stF.rawPositionalsRev.isEmpty then match stF.curSpec.subcommands.find? (fun s => s.name == tok) with | some sub => let p := Internal.addOptsMaps stF.longMap stF.shortMap sub.options; Except.ok ({ curSpec := sub, subPathRev := sub.name :: stF.subPathRev, visibleChunksRev := sub.options :: stF.visibleChunksRev, effectiveVersion := sub.version <|> stF.effectiveVersion, afterDashDash := false, pendingOpt := none, cliMap := stF.cliMap, rawPositionalsRev := [], longMap := p.1, shortMap := p.2 } : Internal.FastParseState) | none => let hint := match Internal.bestSuggestion tok (stF.curSpec.subcommands.map (·.name)) with | some cand => s!"; did you mean '{cand}'?" | none => ""; Except.error { kind := .unknownSubcommand, message := s!"unknown subcommand '{tok}'{hint}", target := some tok } else Except.ok { stF with afterDashDash := false, pendingOpt := none, rawPositionalsRev := tok :: stF.rawPositionalsRev }) := by
                  unfold Internal.stepTokenFast; simp only [hpF, hadF, hdd', hh', hvF', Bool.false_eq_true, ↓reduceIte, htl]; split <;> first | (exfalso; rename_i heq; exact hc1 (List.cons.inj heq).1) | rfl
                have hStepS : Internal.stepToken rootSpec.name validators st tok = (if !st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty then match st.curSpec.subcommands.find? (fun s => s.name == tok) with | some sub => Except.ok ({ curSpec := sub, subPath := st.subPath ++ [sub.name], inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options, effectiveVersion := sub.version <|> st.effectiveVersion, afterDashDash := false, pendingOpt := none, cliOpts := st.cliOpts, rawPositionals := [] } : Internal.ParseState) | none => let hint := match Internal.bestSuggestion tok (st.curSpec.subcommands.map (·.name)) with | some cand => s!"; did you mean '{cand}'?" | none => ""; Except.error { kind := .unknownSubcommand, message := s!"unknown subcommand '{tok}'{hint}", target := some tok } else Except.ok { st with afterDashDash := false, pendingOpt := none, rawPositionals := tok :: st.rawPositionals }) := by
                  unfold Internal.stepToken; simp only [hp, hadS, hdd', hh', hv', Bool.false_eq_true, ↓reduceIte, htl]; split <;> first | (exfalso; rename_i heq; exact hc1 (List.cons.inj heq).1) | rfl
                rw [hStepF, hStepS]; exact stepSubOrPos_eq stF st tok hNode hF0
private theorem parseTokensLoopFast_eq (rootSpec : CommandSpec) (validators : CustomValidators) (stF : Internal.FastParseState) (st : Internal.ParseState) (hInv : ParseStateInv rootSpec st) (hF : FastStateInv stF st) (tokens : List String) :
    (match Internal.parseTokensLoopFast rootSpec.name validators stF tokens, Internal.parseTokensLoop rootSpec.name validators st tokens with | .error e1, .error e2 => e1 = e2 | .ok stF', .ok st' => FastStateInv stF' st' | _, _ => False) := by
  induction tokens generalizing stF st with | nil => simpa [Internal.parseTokensLoopFast, Internal.parseTokensLoop] using hF | cons tok rest ih =>
    unfold Internal.parseTokensLoopFast Internal.parseTokensLoop; dsimp only [Bind.bind, Except.bind]; have hStep := stepTokenFast_eq rootSpec validators stF st hInv hF tok
    cases h1 : Internal.stepTokenFast rootSpec.name validators stF tok with
    | error _ => cases h2 : Internal.stepToken rootSpec.name validators st tok <;> rw [h1, h2] at hStep <;> first | exact hStep | cases hStep
    | ok stF1 => cases h2 : Internal.stepToken rootSpec.name validators st tok with | error _ => rw [h1, h2] at hStep; cases hStep | ok st1 => rw [h1, h2] at hStep; exact ih stF1 st1 (stepToken_sound rootSpec st st1 tok hInv h2) hStep
private theorem parseTokensFast_eq (rootSpec : CommandSpec) (validators : CustomValidators) (stF : Internal.FastParseState) (st : Internal.ParseState) (hInv : ParseStateInv rootSpec st) (hF : FastStateInv stF st) (tokens : List String) :
    (match Internal.parseTokensFast rootSpec.name validators stF tokens, Internal.parseTokens rootSpec.name validators st tokens with
     | .error e1, .error e2 => e1 = e2 | .ok stF', .ok st' => stF'.curSpec = st'.curSpec ∧ stF'.subPathRev = st'.subPath.reverse ∧ Internal.flattenChunksRev stF'.visibleChunksRev = st'.inheritedGlobals ++ st'.curSpec.options ∧ stF'.rawPositionalsRev.reverse = st'.rawPositionals ∧ (∀ k, (stF'.cliMap[k]?.getD []).reverse = lookupCli st'.cliOpts k) | _, _ => False) := by
  unfold Internal.parseTokensFast Internal.parseTokens; dsimp only [Bind.bind, Except.bind]; have hLoop := parseTokensLoopFast_eq rootSpec validators stF st hInv hF tokens
  cases h1 : Internal.parseTokensLoopFast rootSpec.name validators stF tokens with
  | error _ => cases h2 : Internal.parseTokensLoop rootSpec.name validators st tokens <;> rw [h1, h2] at hLoop <;> first | exact hLoop | cases hLoop
  | ok stF1 => cases h2 : Internal.parseTokensLoop rootSpec.name validators st tokens with | error _ => rw [h1, h2] at hLoop; cases hLoop | ok st1 =>
    rw [h1, h2] at hLoop; rcases hLoop with ⟨hCur, hPath, hVis, _, _, hPend, hPos, hCli, _, _⟩; dsimp only; rw [hPend]; cases st1.pendingOpt with | some _ => rfl | none => exact ⟨hCur, hPath, hVis, by simp [hPos], fun k => by rw [lookupCli_map_rev, hCli k]⟩
private theorem resolveOptionsTRWith_eq_resolveOptionsTR {m : Type → Type} [Monad m] (getEnv : String → m (Except CmdLineError (Option String))) (visibleOpts : List OptSpec) (f1 : String → List OptValue) (cliOpts : List (String × List OptValue)) (hf : ∀ name, f1 name = lookupCli cliOpts name) (validators : CustomValidators) :
    Internal.resolveOptionsTRWith getEnv visibleOpts f1 validators = Internal.resolveOptionsTR getEnv visibleOpts cliOpts validators := by
  unfold Internal.resolveOptionsTRWith Internal.resolveOptionsTR
  have hgo : ∀ vis accRev, Internal.resolveOptionsTRWith.go getEnv f1 validators vis accRev = Internal.resolveOptionsTR.go getEnv cliOpts validators vis accRev := fun vis => by
    induction vis with | nil => intro accRev; rfl | cons opt _ ih =>
      intro accRev; unfold Internal.resolveOptionsTRWith.go Internal.resolveOptionsTR.go; rw [hf opt.name]; dsimp only [lookupCli]; congr 1; funext x; cases x <;> first | rfl | (dsimp only; split <;> first | rfl | exact ih _)
  exact hgo visibleOpts []
/-- `Internal.parseWithEnvM` is observationally equal to `Internal.parseWithEnvSpecM` for every monad `m`. -/
theorem parseWithEnvM_eq_spec {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec) (args : List String) (validators : CustomValidators) :
    Internal.parseWithEnvM ops spec args validators = Internal.parseWithEnvSpecM ops spec args validators := by
  unfold Internal.parseWithEnvM Internal.parseWithEnvSpecM
  by_cases hv : Internal.isValidSpecTR spec
  · have hValid : Model.isValidSpec spec = true := by rw [← isValidSpecTR_eq]; exact hv
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; have hv0 : spec.version = (spec.version <|> none) := by cases spec.version <;> rfl
    have hInitInv : ParseStateInv spec { curSpec := spec, effectiveVersion := spec.version } := by
      refine ⟨⟨none, ⟨by simpa [Model.isValidSpec] using hValid, rfl⟩, hv0⟩, ?_, ?_, fun _ hc => by cases hc⟩
      · unfold Model.findSubcommandPath Model.findSubcommandPath.go; exact congrArg (fun v => Except.ok ([], v, spec)) hv0.symm
      · exact ⟨(fun _ hk => absurd rfl hk), (fun _ _ _ hv => by cases hv)⟩
    have hNodeProps := nodeInv_props ⟨by simpa [Model.isValidSpec] using hValid, rfl⟩
    have hInitMaps := addOptsMaps_matches [] spec.options hNodeProps.nodupLongs hNodeProps.nodupShorts {} {} (fun k => by unfold Internal.lookupLongOpt; simp [Model.startsWithNoDash]) (fun _ => by simp)
    have hInitFast : FastStateInv (Internal.initFastState spec) { curSpec := spec, effectiveVersion := spec.version } := by
      refine ⟨rfl, rfl, by simp [Internal.initFastState, flattenChunksRev_eq], rfl, rfl, rfl, rfl, (fun k => by simp [Internal.initFastState, lookupCli, Option.getD]), ?_, ?_⟩
      · intro k; unfold Internal.initFastState; exact hInitMaps.1 k
      · intro c; unfold Internal.initFastState; exact hInitMaps.2 c
    have hTok := parseTokensFast_eq spec validators (Internal.initFastState spec) { curSpec := spec, effectiveVersion := spec.version } hInitInv hInitFast args
    cases h1 : Internal.parseTokensFast spec.name validators (Internal.initFastState spec) args with
    | error _ => cases h2 : Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args <;> rw [h1, h2] at hTok <;> first | (dsimp only; rw [hTok]) | cases hTok
    | ok stF' => cases h2 : Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
      | error _ => rw [h1, h2] at hTok; cases hTok
      | ok st' =>
        rw [h1, h2] at hTok; rcases hTok with ⟨hCur, hPath, hVis, hPos, hCli⟩; dsimp only; rw [hCur, hPos]
        split <;> first | rfl | (rw [hVis, resolveOptionsTRWith_eq_resolveOptionsTR ops.getEnv (st'.inheritedGlobals ++ st'.curSpec.options) _ _ hCli validators]; simp [hPath, List.reverse_reverse])
  · have hvn : (!Internal.isValidSpecTR spec) = true := by simp [hv]
    simp [hvn]
end LeanSwe.CmdLine.Proofs.Shared

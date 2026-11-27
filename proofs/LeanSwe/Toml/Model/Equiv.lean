import LeanSwe.Toml.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Model

open LeanSwe.Toml
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Look up the first value associated with `k` in an association list. -/
def lookupKeyList (k : String) : List (String × TomlValue) → Option TomlValue
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupKeyList k rest

/-- Look up the first value associated with `k` in a `TomlTable`. -/
def lookupKey (k : String) (t : TomlTable) : Option TomlValue :=
  lookupKeyList k t.toList

/-- Check whether `k` appears as a key in an association list. -/
def hasKeyList (k : String) : List (String × TomlValue) → Bool
  | [] => false
  | (k', _) :: rest => k == k' || hasKeyList k rest

/-- Check that all keys in an association list are pairwise distinct. -/
def noDupKeysBool : List (String × TomlValue) → Bool
  | [] => true
  | (k, _) :: rest => !hasKeyList k rest && noDupKeysBool rest

/-- Check that a list of strings has pairwise distinct elements. -/
def noDupStringsBool : List String → Bool
  | [] => true
  | k :: rest => !rest.contains k && noDupStringsBool rest

/-- Propositional predicate asserting pairwise distinct keys in an association list. -/
def NoDupKeys (entries : List (String × TomlValue)) : Prop :=
  noDupKeysBool entries = true

/-- Helper relating `hasKeyList` to membership in `entries.map Prod.fst`. -/
theorem hasKeyList_eq_true_iff (k : String) (entries : List (String × TomlValue)) :
    hasKeyList k entries = true ↔ k ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [hasKeyList]
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    simp only [hasKeyList, Bool.or_eq_true, beq_iff_eq, List.map_cons, List.mem_cons]
    rw [ih]

/-- `NoDupKeys` holds iff the key list is `List.Nodup`. -/
theorem noDupKeys_iff_nodup (entries : List (String × TomlValue)) :
    NoDupKeys entries ↔ (entries.map Prod.fst).Nodup := by
  unfold NoDupKeys
  induction entries with
  | nil => simp [noDupKeysBool]
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true', List.map_cons, List.nodup_cons]
    rw [ih, ← hasKeyList_eq_true_iff]
    constructor
    · rintro ⟨hk, hrest⟩
      refine ⟨?_, hrest⟩
      intro htrue
      rw [htrue] at hk
      cases hk
    · rintro ⟨hnot, hrest⟩
      refine ⟨?_, hrest⟩
      cases h : hasKeyList k tl
      · rfl
      · exact False.elim (hnot h)

/-- Check RFC 3339 4-digit year bounds (`0000..9999`) for a `Std.Time.PlainDate`. -/
def validTomlDate (d : Std.Time.PlainDate) : Bool :=
  decide (0 ≤ d.year ∧ d.year ≤ 9999)

/-- Check TOML 1.0 second bounds (`00..59`) for a `Std.Time.PlainTime`. -/
def validTomlTime (t : Std.Time.PlainTime) : Bool :=
  decide (t.second.val ≤ 59)

/-- Check TOML 1.0 bounds for a `Std.Time.PlainDateTime`. -/
def validTomlDateTime (dt : Std.Time.PlainDateTime) : Bool :=
  validTomlDate dt.date && validTomlTime dt.time

/-- Check RFC 3339 minute-granularity offset bounds (`±23:59`, multiple of 60 seconds). -/
def validTomlOffset (o : Std.Time.TimeZone.Offset) : Bool :=
  decide (o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340)

/-- Check TOML 1.0 bounds for a `TomlOffsetDateTime`. -/
def validTomlOffsetDateTime (odt : TomlOffsetDateTime) : Bool :=
  validTomlDateTime odt.dateTime && validTomlOffset odt.offset

/-- Computable structural well-formedness check on a `TomlValue`. -/
def wellFormedValueBool : TomlValue → Bool
  | .string _ => true
  | .int _ => true
  | .float _ => true
  | .bool _ => true
  | .offsetDateTime odt => validTomlOffsetDateTime odt
  | .localDateTime dt => validTomlDateTime dt
  | .localDate d => validTomlDate d
  | .localTime t => validTomlTime t
  | .array xs => wellFormedListBool xs.toList
  | .table t => noDupKeysBool t.toList && wellFormedTableListBool t.toList
where
  /-- Computable well-formedness check on a list of `TomlValue` elements. -/
  wellFormedListBool : List TomlValue → Bool
    | [] => true
    | x :: xs => wellFormedValueBool x && wellFormedListBool xs
  /-- Computable well-formedness check on a list of table entries. -/
  wellFormedTableListBool : List (String × TomlValue) → Bool
    | [] => true
    | (_, v) :: rest => wellFormedValueBool v && wellFormedTableListBool rest

/-- Computable structural well-formedness check on a `TomlTable`. -/
def wellFormedTableBool (t : TomlTable) : Bool :=
  noDupKeysBool t.toList && wellFormedValueBool.wellFormedTableListBool t.toList

/-- Well-formedness predicate for a `TomlValue` (distinct table keys and RFC 3339 datetime bounds). -/
def WellFormedValue (v : TomlValue) : Prop :=
  wellFormedValueBool v = true

/-- Well-formedness predicate for a `TomlTable` (distinct table keys and well-formed values). -/
def WellFormedTable (t : TomlTable) : Prop :=
  wellFormedTableBool t = true

/-- Equivalence between `WellFormedTable t` and `WellFormedValue (.table t)`. -/
theorem wellFormedTable_iff_value (t : TomlTable) :
    WellFormedTable t ↔ WellFormedValue (.table t) := Iff.rfl

/-- Looking up a key in an association list yields a strictly smaller value under `sizeOf`. -/
theorem lookupKeyList_sizeOf {k : String} {entries : List (String × TomlValue)} {v : TomlValue}
    (h : lookupKeyList k entries = some v) : sizeOf v < sizeOf entries := by
  induction entries with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [lookupKeyList] at h
    split at h
    · cases h
      simp +arith
    · exact Nat.lt_trans (ih h) (by simp +arith)

/-- Helper lemma bounding `sizeOf entries.toList` by `sizeOf entries` for arrays. -/
theorem sizeOf_toList_lt_array {α : Type} [SizeOf α] (xs : Array α) : sizeOf xs.toList < sizeOf xs := by
  cases xs
  simp +arith

mutual
  /-- Semantic equivalence on `TomlValue`, ignoring table key order and comparing floats via `FloatEquiv`. -/
  def TomlEquiv (a b : TomlValue) : Prop :=
    match a, b with
    | .string s1, .string s2 => s1 = s2
    | .int n1, .int n2 => n1 = n2
    | .float f1, .float f2 => FloatEquiv f1 f2
    | .bool b1, .bool b2 => b1 = b2
    | .offsetDateTime d1, .offsetDateTime d2 => d1 = d2
    | .localDateTime d1, .localDateTime d2 => d1 = d2
    | .localDate d1, .localDate d2 => d1 = d2
    | .localTime t1, .localTime t2 => t1 = t2
    | .array xs, .array ys => TomlListEquiv xs.toList ys.toList
    | .table t1, .table t2 => TomlTableEquivList t1.toList t2.toList
    | _, _ => False
  termination_by sizeOf a
  decreasing_by
    · exact Nat.lt_trans (sizeOf_toList_lt_array _) (by simp +arith)
    · exact Nat.lt_trans (sizeOf_toList_lt_array _) (by simp +arith)

  /-- Element-wise semantic equivalence on `List TomlValue`. -/
  def TomlListEquiv (xs ys : List TomlValue) : Prop :=
    match xs, ys with
    | [], [] => True
    | x :: xr, y :: yr => TomlEquiv x y ∧ TomlListEquiv xr yr
    | _, _ => False
  termination_by sizeOf xs
  decreasing_by
    · simp +arith
    · simp +arith

  /-- Lookup-based semantic equivalence on table association lists. -/
  def TomlTableEquivList (t1 t2 : List (String × TomlValue)) : Prop :=
    (∀ (k : String), lookupKeyList k t1 = none → lookupKeyList k t2 = none) ∧
    (∀ (k : String) (v1 : TomlValue), (h1 : lookupKeyList k t1 = some v1) →
      ∃ v2 : TomlValue, lookupKeyList k t2 = some v2 ∧ TomlEquiv v1 v2)
  termination_by sizeOf t1
  decreasing_by
    exact lookupKeyList_sizeOf h1
end

/-- Semantic equivalence on `TomlTable`, ignoring key order and comparing values via `TomlEquiv`. -/
def TomlTableEquiv (t1 t2 : TomlTable) : Prop :=
  TomlTableEquivList t1.toList t2.toList

/-- Reflexivity, symmetry, and transitivity proved jointly by strong induction on `sizeOf`. -/
theorem tomlEquiv_properties :
    (∀ (n : Nat) (a : TomlValue), sizeOf a ≤ n → TomlEquiv a a) ∧
    (∀ (n : Nat) (a b : TomlValue), sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b a) ∧
    (∀ (n : Nat) (a b c : TomlValue), sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b c → TomlEquiv a c) := by
  have hMain : ∀ (n : Nat),
      (∀ a : TomlValue, sizeOf a ≤ n → TomlEquiv a a) ∧
      (∀ a b : TomlValue, sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b a) ∧
      (∀ a b c : TomlValue, sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b c → TomlEquiv a c) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have hrefl : ∀ a : TomlValue, sizeOf a ≤ n → TomlEquiv a a := by
        intro a ha
        cases a with
        | string _ | int _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
          simp [TomlEquiv]
        | float f =>
          simp [TomlEquiv, floatEquiv_refl]
        | array xs =>
          simp only [TomlEquiv]
          have hsub : ∀ l : List TomlValue, sizeOf l < sizeOf (TomlValue.array xs) → TomlListEquiv l l := by
            intro l hl
            induction l with
            | nil => simp [TomlListEquiv]
            | cons x xr ihl =>
              simp only [TomlListEquiv]
              have hxr : sizeOf xr < sizeOf (x :: xr) := by simp +arith
              have hx : sizeOf x < sizeOf (x :: xr) := by simp +arith
              have hxn : sizeOf x < n := Nat.lt_of_lt_of_le (Nat.lt_trans hx hl) ha
              exact ⟨(ih (sizeOf x) hxn).1 x (Nat.le_refl _), ihl (Nat.lt_trans hxr hl)⟩
          exact hsub xs.toList (Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith))
        | table t =>
          simp only [TomlEquiv, TomlTableEquivList]
          refine ⟨fun _ hk => hk, fun k v hk => ⟨v, hk, ?_⟩⟩
          have hv : sizeOf v < sizeOf t.toList := lookupKeyList_sizeOf hk
          have ht : sizeOf t.toList < sizeOf (TomlValue.table t) :=
            Nat.lt_trans (sizeOf_toList_lt_array t) (by simp +arith)
          exact (ih (sizeOf v) (by omega)).1 v (Nat.le_refl _)
      have hsymm : ∀ a b : TomlValue, sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b a := by
        intro a b ha hab
        cases a with
        | string s1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | int n1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | float f1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact floatEquiv_symm hab
        | bool b1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | offsetDateTime d1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | localDateTime d1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | localDate d1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | localTime t1 =>
          cases b <;> simp [TomlEquiv] at hab ⊢
          exact hab.symm
        | array xs =>
          cases b with
          | array ys =>
            simp only [TomlEquiv] at hab ⊢
            have hlist : ∀ l1 l2 : List TomlValue,
                sizeOf l1 < sizeOf (TomlValue.array xs) → TomlListEquiv l1 l2 → TomlListEquiv l2 l1 := by
              intro l1 l2 hl1 h12
              induction l1 generalizing l2 with
              | nil =>
                cases l2 with
                | nil => simp [TomlListEquiv]
                | cons _ _ => simp [TomlListEquiv] at h12
              | cons x xr ihl =>
                cases l2 with
                | nil => simp [TomlListEquiv] at h12
                | cons y yr =>
                  simp only [TomlListEquiv] at h12 ⊢
                  have hx : sizeOf x < sizeOf (x :: xr) := by simp +arith
                  have hxr : sizeOf xr < sizeOf (x :: xr) := by simp +arith
                  have hxn : sizeOf x < n := Nat.lt_of_lt_of_le (Nat.lt_trans hx hl1) ha
                  exact ⟨(ih (sizeOf x) hxn).2.1 x y (Nat.le_refl _) h12.1,
                    ihl yr (Nat.lt_trans hxr hl1) h12.2⟩
            exact hlist xs.toList ys.toList (Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)) hab
          | _ => simp [TomlEquiv] at hab
        | table t1 =>
          cases b with
          | table t2 =>
            simp only [TomlEquiv, TomlTableEquivList] at hab ⊢
            rcases hab with ⟨hnone, hsome⟩
            constructor
            · intro k hk2
              cases hk1 : lookupKeyList k t1.toList with
              | none => rfl
              | some v1 =>
                obtain ⟨v2, hv2, _⟩ := hsome k v1 hk1
                rw [hk2] at hv2
                cases hv2
            · intro k v2 hk2
              cases hk1 : lookupKeyList k t1.toList with
              | none =>
                have h2n := hnone k hk1
                rw [hk2] at h2n
                cases h2n
              | some v1 =>
                obtain ⟨v2', hv2', heq⟩ := hsome k v1 hk1
                rw [hk2] at hv2'
                cases hv2'
                have hv1 : sizeOf v1 < sizeOf t1.toList := lookupKeyList_sizeOf hk1
                have ht1 : sizeOf t1.toList < sizeOf (TomlValue.table t1) :=
                  Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
                exact ⟨v1, rfl, (ih (sizeOf v1) (by omega)).2.1 v1 v2 (Nat.le_refl _) heq⟩
          | _ => simp [TomlEquiv] at hab
      have htrans : ∀ a b c : TomlValue, sizeOf a ≤ n → TomlEquiv a b → TomlEquiv b c → TomlEquiv a c := by
        intro a b c ha hab hbc
        cases a with
        | string s1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | int n1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | float f1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact floatEquiv_trans hab hbc
        | bool b1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | offsetDateTime d1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | localDateTime d1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | localDate d1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | localTime t1 =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          exact hab.trans hbc
        | array xs =>
          cases b <;> cases c <;> simp [TomlEquiv] at hab hbc ⊢
          rename_i ys zs
          have hlist : ∀ l1 l2 l3 : List TomlValue,
              sizeOf l1 < sizeOf (TomlValue.array xs) →
              TomlListEquiv l1 l2 → TomlListEquiv l2 l3 → TomlListEquiv l1 l3 := by
            intro l1 l2 l3 hl1 h12 h23
            induction l1 generalizing l2 l3 with
            | nil =>
              cases l2 with
              | nil =>
                cases l3 with
                | nil => simp [TomlListEquiv]
                | cons _ _ => simp [TomlListEquiv] at h23
              | cons _ _ => simp [TomlListEquiv] at h12
            | cons x xr ihl =>
              cases l2 with
              | nil => simp [TomlListEquiv] at h12
              | cons y yr =>
                cases l3 with
                | nil => simp [TomlListEquiv] at h23
                | cons z zr =>
                  simp only [TomlListEquiv] at h12 h23 ⊢
                  have hx : sizeOf x < sizeOf (x :: xr) := by simp +arith
                  have hxr : sizeOf xr < sizeOf (x :: xr) := by simp +arith
                  have hxn : sizeOf x < n := Nat.lt_of_lt_of_le (Nat.lt_trans hx hl1) ha
                  exact ⟨(ih (sizeOf x) hxn).2.2 x y z (Nat.le_refl _) h12.1 h23.1,
                    ihl yr zr (Nat.lt_trans hxr hl1) h12.2 h23.2⟩
          exact hlist xs.toList ys.toList zs.toList
            (Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith)) hab hbc
        | table t1 =>
          cases b <;> cases c <;> simp [TomlEquiv, TomlTableEquivList] at hab hbc ⊢
          rename_i t2 t3
          rcases hab with ⟨h12n, h12s⟩
          rcases hbc with ⟨h23n, h23s⟩
          constructor
          · intro k hk1
            exact h23n k (h12n k hk1)
          · intro k v1 hk1
            obtain ⟨v2, hk2, heq12⟩ := h12s k v1 hk1
            obtain ⟨v3, hk3, heq23⟩ := h23s k v2 hk2
            have hv1 : sizeOf v1 < sizeOf t1.toList := lookupKeyList_sizeOf hk1
            have ht1 : sizeOf t1.toList < sizeOf (TomlValue.table t1) :=
              Nat.lt_trans (sizeOf_toList_lt_array t1) (by simp +arith)
            exact ⟨v3, hk3, (ih (sizeOf v1) (by omega)).2.2 v1 v2 v3 (Nat.le_refl _) heq12 heq23⟩
      exact ⟨hrefl, hsymm, htrans⟩
  exact
    ⟨fun n a h => (hMain n).1 a h,
     fun n a b h => (hMain n).2.1 a b h,
     fun n a b c h => (hMain n).2.2 a b c h⟩

/-- Reflexivity of `TomlEquiv`. -/
theorem tomlEquiv_refl (a : TomlValue) : TomlEquiv a a :=
  tomlEquiv_properties.1 (sizeOf a) a (Nat.le_refl _)

/-- Symmetry of `TomlEquiv`. -/
theorem tomlEquiv_symm {a b : TomlValue} (h : TomlEquiv a b) : TomlEquiv b a :=
  tomlEquiv_properties.2.1 (sizeOf a) a b (Nat.le_refl _) h

/-- Transitivity of `TomlEquiv`. -/
theorem tomlEquiv_trans {a b c : TomlValue} (hab : TomlEquiv a b) (hbc : TomlEquiv b c) :
    TomlEquiv a c :=
  tomlEquiv_properties.2.2 (sizeOf a) a b c (Nat.le_refl _) hab hbc

/-- `TomlEquiv` is a mathematical equivalence relation. -/
theorem equivalence_tomlEquiv : Equivalence TomlEquiv :=
  ⟨tomlEquiv_refl, @tomlEquiv_symm, @tomlEquiv_trans⟩

/-- Reflexivity of `TomlTableEquiv`. -/
theorem tomlTableEquiv_refl (t : TomlTable) : TomlTableEquiv t t := by
  have h := tomlEquiv_refl (.table t)
  simpa [TomlEquiv, TomlTableEquiv] using h

/-- Symmetry of `TomlTableEquiv`. -/
theorem tomlTableEquiv_symm {t1 t2 : TomlTable} (h : TomlTableEquiv t1 t2) : TomlTableEquiv t2 t1 := by
  have h' : TomlEquiv (.table t1) (.table t2) := by simpa [TomlEquiv, TomlTableEquiv] using h
  simpa [TomlEquiv, TomlTableEquiv] using tomlEquiv_symm h'

/-- Transitivity of `TomlTableEquiv`. -/
theorem tomlTableEquiv_trans {t1 t2 t3 : TomlTable}
    (h12 : TomlTableEquiv t1 t2) (h23 : TomlTableEquiv t2 t3) : TomlTableEquiv t1 t3 := by
  have h12' : TomlEquiv (.table t1) (.table t2) := by simpa [TomlEquiv, TomlTableEquiv] using h12
  have h23' : TomlEquiv (.table t2) (.table t3) := by simpa [TomlEquiv, TomlTableEquiv] using h23
  simpa [TomlEquiv, TomlTableEquiv] using tomlEquiv_trans h12' h23'

/-- `TomlTableEquiv` is a mathematical equivalence relation. -/
theorem equivalence_tomlTableEquiv : Equivalence TomlTableEquiv :=
  ⟨tomlTableEquiv_refl, @tomlTableEquiv_symm, @tomlTableEquiv_trans⟩

/-- `TomlTableEquiv` preserves key presence and `TomlEquiv` of looked-up values. -/
theorem tomlTableEquiv_lookup {t1 t2 : TomlTable} (h : TomlTableEquiv t1 t2) (k : String) :
    match lookupKey k t1, lookupKey k t2 with
    | none, none => True
    | some v1, some v2 => TomlEquiv v1 v2
    | _, _ => False := by
  unfold TomlTableEquiv TomlTableEquivList at h
  rcases h with ⟨hnone, hsome⟩
  cases h1 : lookupKey k t1 with
  | none =>
    have h2 := hnone k h1
    change lookupKey k t2 = none at h2
    simp [h2]
  | some v1 =>
    obtain ⟨v2, h2, heq⟩ := hsome k v1 h1
    change lookupKey k t2 = some v2 at h2
    simp [h2, heq]

end LeanSwe.Toml.Model

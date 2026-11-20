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

/-- Choice of TOML key surface syntax in `render`. -/
inductive KeyStyle where
  /-- Unquoted ASCII bare key `[A-Za-z0-9_-]+`. -/
  | bare
  /-- Basic quoted key `"..."`. -/
  | basic
  /-- Literal quoted key `'...'`. -/
  | literal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of TOML string literal surface syntax in `render`. -/
inductive StringStyle where
  /-- Single-line basic string `"..."`. -/
  | basic
  /-- Multiline basic string `"""..."""`. -/
  | multilineBasic
  /-- Single-line literal string `'...'`. -/
  | literal
  /-- Multiline literal string `'''...'''`. -/
  | multilineLiteral
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of RFC 3339 date-time separator in `render`. -/
inductive DateTimeSep where
  /-- Uppercase `'T'` separator. -/
  | upperT
  /-- Lowercase `'t'` separator. -/
  | lowerT
  /-- Single ASCII space `' '` separator. -/
  | space
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Choice of RFC 3339 UTC offset formatting in `render`. -/
inductive OffsetStyle where
  /-- Uppercase `'Z'` when offset is `0` (otherwise `±HH:MM`). -/
  | upperZ
  /-- Lowercase `'z'` when offset is `0` (otherwise `±HH:MM`). -/
  | lowerZ
  /-- Explicit numeric `±HH:MM` offset even when offset is `0`. -/
  | numeric
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Nondeterministic choices for rendering a leaf or nested value in `render`. -/
inductive ValueTape where
  /-- Rendering choice for `.string`. -/
  | string (style : StringStyle := .basic)
  /-- Rendering choice for `.int` (optional custom TOML integer literal validated by `parseInt64Model`). -/
  | int (lex : Option String := none)
  /-- Rendering choice for `.float` (optional custom TOML float literal validated by `parseFloatModel`). -/
  | float (lex : Option String := none)
  /-- Rendering choice for `.bool`. -/
  | bool
  /-- Rendering choice for `.offsetDateTime`. -/
  | offsetDateTime (sep : DateTimeSep := .upperT) (offsetStyle : OffsetStyle := .upperZ) (fracDigits : Nat := 0)
  /-- Rendering choice for `.localDateTime`. -/
  | localDateTime (sep : DateTimeSep := .upperT) (fracDigits : Nat := 0)
  /-- Rendering choice for `.localDate`. -/
  | localDate
  /-- Rendering choice for `.localTime`. -/
  | localTime (fracDigits : Nat := 0)
  /-- Rendering choice for `.array` (per-element inline `ValueTape`). -/
  | array (elems : List ValueTape)
  /-- Rendering choice for inline `.table` (`{ ... }`, with ordered key choices). -/
  | inlineTable (entries : List (String × KeyStyle × ValueTape))
  deriving Repr, Inhabited

/-- Placement mode for an entry in a table section during `render`. -/
inductive EntryPlacement where
  /-- Emit as `key = value` (or inline `{ ... }` / `[ ... ]`) in the current section. -/
  | direct (keyStyle : KeyStyle := .bare) (valTape : ValueTape) (comment : Option String := none)
  /-- Emit a nested table by flattening its leaves into dotted keys `k.sub = val`. -/
  | dotted (keyStyle : KeyStyle := .bare) (subEntries : List (String × EntryPlacement))
  /-- Emit a nested table as `[path.k]` header section (optionally emitting child sections before `[path.k]`). -/
  | tableSection (keyStyle : KeyStyle := .bare) (subtableFirst : Bool := false)
      (subEntries : List (String × EntryPlacement)) (comment : Option String := none)
  /-- Emit a non-empty array of tables as repeated `[[path.k]]` sections. -/
  | aotSection (keyStyle : KeyStyle := .bare) (elems : List (List (String × EntryPlacement)))
      (comment : Option String := none)
  deriving Repr, Inhabited

/-- Root rendering tape specifying ordered entries and optional header comment for `render`. -/
structure RenderTape where
  /-- Ordered rendering instructions for the root `TomlTable`. -/
  entries : List (String × EntryPlacement)
  /-- Optional leading `# ...` comment line. -/
  headerComment : Option String := none
  deriving Repr, Inhabited

/-- Check whether `c` is an ASCII bare-key character `[A-Za-z0-9_-]`. -/
def isBareKeyChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-'

/-- Check whether `c` is a disallowed TOML 1.0 control character (`U+0000..U+0008`, `U+000B`, `U+000C`, `U+000E..U+001F`, `U+007F`). -/
def isDisallowedControl (c : Char) : Bool :=
  let n := c.toNat
  n ≤ 0x08 || n == 0x0B || n == 0x0C || (0x0E ≤ n && n ≤ 0x1F) || n == 0x7F

/-- Check whether `s` contains no disallowed control chars, no `\n`, and no `\r`. -/
def isSingleLineClean (s : String) : Bool :=
  s.toList.all fun c => !isDisallowedControl c && c != '\n' && c != '\r'

/-- Check whether `s` contains `sub` as a substring. -/
def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check whether `s` is a valid non-empty ASCII bare key. -/
def isValidBareKey (s : String) : Bool :=
  !s.isEmpty && s.toList.all isBareKeyChar

/-- Encode a single byte `n < 16` as an uppercase hexadecimal character. -/
def hexDigitUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + (n - 10))

/-- Escape a single character for TOML basic strings/keys (always escaping disallowed controls and `\r`). -/
def escapeBasicChar (allowNewline : Bool) (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\x08' then "\\b"
  else if c == '\t' then "\\t"
  else if c == '\n' then if allowNewline then "\n" else "\\n"
  else if c == '\x0c' then "\\f"
  else if c == '\r' then "\\r"
  else if isDisallowedControl c then
    let n := c.toNat
    "\\u00" ++ String.ofList [hexDigitUpper (n / 16), hexDigitUpper (n % 16)]
  else String.singleton c

/-- Render a basic string body (`allowNewline = false` for `"..."`, `true` for `"""..."""`). -/
def escapeBasicBody (allowNewline : Bool) (s : String) : String :=
  String.join (s.toList.map (escapeBasicChar allowNewline))

/-- Render a TOML key according to `KeyStyle`, returning `none` if invalid for that style. -/
def renderKey (k : String) : KeyStyle → Option String
  | .bare => if isValidBareKey k then some k else none
  | .basic => some ("\"" ++ escapeBasicBody false k ++ "\"")
  | .literal =>
    if isSingleLineClean k && !k.contains '\'' then some ("'" ++ k ++ "'") else none

/-- Render a dotted path of already-rendered key segments. -/
def joinRenderedPath : List String → String
  | [] => ""
  | [k] => k
  | k :: rest => k ++ "." ++ joinRenderedPath rest

/-- Format an optional `# ...` comment suffix (single-line, free of `\n`/`\r`/disallowed controls). -/
def renderCommentSuffix : Option String → Option String
  | none => some ""
  | some c => if isSingleLineClean c then some (" #" ++ c) else none

/-- Render a TOML string literal according to `StringStyle`, returning `none` if invalid for that style. -/
def renderStringLiteral (s : String) : StringStyle → Option String
  | .basic => some ("\"" ++ escapeBasicBody false s ++ "\"")
  | .multilineBasic =>
    some ("\"\"\"\n" ++ escapeBasicBody true s ++ "\"\"\"")
  | .literal =>
    if isSingleLineClean s && !s.contains '\'' then some ("'" ++ s ++ "'") else none
  | .multilineLiteral =>
    let clean := s.toList.all fun c => !isDisallowedControl c && c != '\r'
    if clean && !containsSubstr s "'''" && !s.endsWith "'" then
      some ("'''\n" ++ s ++ "'''")
    else
      none

/-- Check whether `s` is a valid lowercase-prefixed or decimal integer token with no terminators. -/
def isValidIntLex (s : String) (n : Int64) : Bool :=
  let noBadPrefix :=
    !(s.startsWith "0X" || s.startsWith "0O" || s.startsWith "0B" ||
      s.startsWith "+0X" || s.startsWith "+0O" || s.startsWith "+0B" ||
      s.startsWith "-0X" || s.startsWith "-0O" || s.startsWith "-0B")
  let noTerm := s.toList.all fun c =>
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' &&
      c != '.' && !isDisallowedControl c
  let noExpUnlessHex :=
    if s.startsWith "0x" then true else !(s.contains 'e' || s.contains 'E')
  noBadPrefix && noTerm && noExpUnlessHex &&
    (match parseInt64Model s with
     | .ok parsed => parsed == n
     | .error _ => false)

/-- Format an `Int64` in canonical base-10 decimal. -/
def formatInt64Canonical (n : Int64) : String :=
  toString n.toInt

/-- Check whether `s` is a valid TOML 1.0 float token evaluating via `parseFloatModel` to a `FloatEquiv` float. -/
def isValidFloatLex (s : String) (f : Float) : Bool :=
  let hasFloatMarker :=
    s.contains '.' || s.contains 'e' || s.contains 'E' ||
    s == "inf" || s == "+inf" || s == "-inf" ||
    s == "nan" || s == "+nan" || s == "-nan"
  let noTerm := s.toList.all fun c =>
    !c.isWhitespace && c != '#' && c != ',' && c != ']' && c != '}' && !isDisallowedControl c
  hasFloatMarker && noTerm &&
    (match parseFloatModel s with
     | .ok g => (g.isNaN && f.isNaN) || (g == f)
     | .error _ => false)

/-- Pad a natural number with leading zeros to width `w`. -/
def padNatZero (w : Nat) (n : Nat) : String :=
  let s := toString n
  if s.length ≥ w then s else String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Compute `10^k` for `k : Nat`. -/
def pow10Nat : Nat → Nat
  | 0 => 1
  | k + 1 => 10 * pow10Nat k

/-- Format `nanosecond` with exact `fracDigits` (`0..9`), returning `none` if precision would be lost. -/
def formatNanosExact (nano : Nat) (fracDigits : Nat) : Option String :=
  if fracDigits > 9 then none
  else if fracDigits == 0 then
    if nano == 0 then some "" else none
  else
    let divisor := pow10Nat (9 - fracDigits)
    if nano % divisor != 0 then none
    else some ("." ++ padNatZero fracDigits (nano / divisor))

/-- Render `Std.Time.PlainDate` as `YYYY-MM-DD`, returning `none` if out of `0000..9999`. -/
def renderDate (d : Std.Time.PlainDate) : Option String :=
  if validTomlDate d then
    some (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat)
  else none

/-- Render `Std.Time.PlainTime` as `HH:MM:SS(.frac)?`, returning `none` if invalid. -/
def renderTime (t : Std.Time.PlainTime) (fracDigits : Nat) : Option String :=
  if !validTomlTime t then none
  else
    match formatNanosExact t.nanosecond.val.toNat fracDigits with
    | none => none
    | some frac =>
      some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
        padNatZero 2 t.second.val.toNat ++ frac)

/-- Render `Std.Time.TimeZone.Offset` according to `OffsetStyle`. -/
def renderOffset (o : Std.Time.TimeZone.Offset) (style : OffsetStyle) : Option String :=
  if !validTomlOffset o then none
  else if o.second.val == 0 then
    match style with
    | .upperZ => some "Z"
    | .lowerZ => some "z"
    | .numeric => some "+00:00"
  else
    let sign := if o.second.val < 0 then "-" else "+"
    let absMin := o.second.val.natAbs / 60
    some (sign ++ padNatZero 2 (absMin / 60) ++ ":" ++ padNatZero 2 (absMin % 60))

/-- Render a `DateTimeSep` as a single-character string. -/
def renderDateTimeSep : DateTimeSep → String
  | .upperT => "T"
  | .lowerT => "t"
  | .space => " "

/-- Render a `TomlValue` inline (`key = <this>`, inside `{ ... }`, or inside `[ ... ]`). -/
def renderValueInline (v : TomlValue) (tape : ValueTape) : Option String :=
  match v, tape with
  | .string s, .string style => renderStringLiteral s style
  | .int n, .int none => some (formatInt64Canonical n)
  | .int n, .int (some lex) => if isValidIntLex lex n then some lex else none
  | .float f, .float none =>
    if f.isNaN then some "nan"
    else if f == Float.inf then some "inf"
    else if f == -Float.inf then some "-inf"
    else if f.toBits == (0.0 : Float).toBits then some "0.0"
    else if f.toBits == (-0.0 : Float).toBits then some "-0.0"
    else none
  | .float f, .float (some lex) => if isValidFloatLex lex f then some lex else none
  | .bool b, .bool => some (if b then "true" else "false")
  | .offsetDateTime odt, .offsetDateTime sep oStyle fracDigits => do
    let ds ← renderDate odt.dateTime.date
    let ts ← renderTime odt.dateTime.time fracDigits
    let os ← renderOffset odt.offset oStyle
    some (ds ++ renderDateTimeSep sep ++ ts ++ os)
  | .localDateTime dt, .localDateTime sep fracDigits => do
    let ds ← renderDate dt.date
    let ts ← renderTime dt.time fracDigits
    some (ds ++ renderDateTimeSep sep ++ ts)
  | .localDate d, .localDate => renderDate d
  | .localTime t, .localTime fracDigits => renderTime t fracDigits
  | .array xs, .array elemTapes => do
    let strs ← renderArrayElems xs.toList elemTapes
    some ("[" ++ String.intercalate ", " strs ++ "]")
  | .table t, .inlineTable entryTapes =>
    if !noDupKeysBool t.toList then none
    else do
      let kvs ← renderInlineTableEntries t.toList entryTapes
      some ("{" ++ String.intercalate ", " kvs ++ "}")
  | _, _ => none
where
  /-- Render array elements paired 1-to-1 with `ValueTape` instructions. -/
  renderArrayElems : List TomlValue → List ValueTape → Option (List String)
    | [], [] => some []
    | x :: xs, tp :: tps => do
      let s ← renderValueInline x tp
      let rest ← renderArrayElems xs tps
      some (s :: rest)
    | _, _ => none
  /-- Check that `entryTapes` covers a permutation of `tableEntries`'s keys and render each `k = v`. -/
  renderInlineTableEntries (tableEntries : List (String × TomlValue)) :
      List (String × KeyStyle × ValueTape) → Option (List String)
    | [] => if tableEntries.isEmpty then some [] else none
    | (k, ks, vt) :: rest =>
      match lookupKeyList k tableEntries with
      | none => none
      | some v => do
        let rk ← renderKey k ks
        let rv ← renderValueInline v vt
        let remaining := tableEntries.filter (fun p => p.1 != k)
        let tail ← renderInlineTableEntries remaining rest
        some ((rk ++ " = " ++ rv) :: tail)

/-- Classify whether an `EntryPlacement` emits in the active header scope vs opens new `[...]`/`[[...]]` sections. -/
def EntryPlacement.isInlineScope : EntryPlacement → Bool
  | .direct _ _ _ => true
  | .dotted _ _ => true
  | .tableSection _ _ _ _ => false
  | .aotSection _ _ _ => false

/-- Verify that `plan` keys have no duplicates and form a bijection with `tableEntries` keys. -/
def isPlanPermutation (tableEntries : List (String × TomlValue))
    (plan : List (String × EntryPlacement)) : Bool :=
  noDupKeysBool tableEntries &&
  noDupStringsBool (plan.map Prod.fst) &&
  plan.length == tableEntries.length &&
  plan.all (fun p => hasKeyList p.1 tableEntries)

mutual
  /-- Render all entries of a `TomlTable` at rendered header path `revPath` (empty at root), emitting inline entries before sections. -/
  def renderTablePlan (revPrefix : List String) (tableEntries : List (String × TomlValue))
      (plan : List (String × EntryPlacement)) : Option (List String) :=
    if !isPlanPermutation tableEntries plan then none
    else do
      let inlineLines ← renderInlineEntries revPrefix tableEntries plan
      let sectionLines ← renderSectionEntries revPrefix tableEntries plan
      some (inlineLines ++ sectionLines)
  termination_by sizeOf plan + 1
  decreasing_by
    all_goals simp +arith

  /-- Flatten a nested `dotted` table into `key = val` lines with no child `[...]` sections. -/
  def renderDottedSub (revPrefix : List String) (tableEntries : List (String × TomlValue))
      (subPlan : List (String × EntryPlacement)) : Option (List String) :=
    if !isPlanPermutation tableEntries subPlan then none
    else renderDottedList revPrefix tableEntries subPlan
  termination_by sizeOf subPlan + 1
  decreasing_by
    all_goals simp +arith

  /-- Render each entry of a `dotted` plan sequentially. -/
  def renderDottedList (revPrefix : List String) (tableEntries : List (String × TomlValue)) :
      List (String × EntryPlacement) → Option (List String)
    | [] => some []
    | (k, ep) :: rest =>
      match lookupKeyList k tableEntries with
      | none => none
      | some v => do
        let lines ←
          match ep with
          | .direct ks vt comment => do
            let rk ← renderKey k ks
            let rv ← renderValueInline v vt
            let rc ← renderCommentSuffix comment
            let lhs := joinRenderedPath (rk :: revPrefix).reverse
            some [lhs ++ " = " ++ rv ++ rc]
          | .dotted ks subPlan =>
            match v with
            | .table sub =>
              if sub.isEmpty then none
              else do
                let rk ← renderKey k ks
                renderDottedSub (rk :: revPrefix) sub.toList subPlan
            | _ => none
          | .tableSection _ _ _ _ => none
          | .aotSection _ _ _ => none
        let tail ← renderDottedList revPrefix tableEntries rest
        some (lines ++ tail)
  termination_by subPlan => sizeOf subPlan
  decreasing_by
    all_goals simp +arith

  /-- Render only the inline-scoped (`direct`/`dotted`) entries from `plan`. -/
  def renderInlineEntries (revPrefix : List String) (tableEntries : List (String × TomlValue)) :
      List (String × EntryPlacement) → Option (List String)
    | [] => some []
    | (k, ep) :: rest => do
      let lines ←
        if !ep.isInlineScope then some []
        else
          match lookupKeyList k tableEntries with
          | none => none
          | some v =>
            match ep with
            | .direct ks vt comment => do
              let rk ← renderKey k ks
              let rv ← renderValueInline v vt
              let rc ← renderCommentSuffix comment
              some [rk ++ " = " ++ rv ++ rc]
            | .dotted ks subPlan =>
              match v with
              | .table sub =>
                if sub.isEmpty then none
                else do
                  let rk ← renderKey k ks
                  renderDottedSub [rk] sub.toList subPlan
              | _ => none
            | .tableSection _ _ _ _ => some []
            | .aotSection _ _ _ => some []
      let tail ← renderInlineEntries revPrefix tableEntries rest
      some (lines ++ tail)
  termination_by plan => sizeOf plan
  decreasing_by
    all_goals simp +arith

  /-- Render only the section-scoped (`tableSection`/`aotSection`) entries from `plan`. -/
  def renderSectionEntries (revPrefix : List String) (tableEntries : List (String × TomlValue)) :
      List (String × EntryPlacement) → Option (List String)
    | [] => some []
    | (k, ep) :: rest => do
      let lines ←
        if ep.isInlineScope then some []
        else
          match lookupKeyList k tableEntries with
          | none => none
          | some v =>
            match ep with
            | .tableSection ks subtableFirst subPlan comment =>
              match v with
              | .table sub => do
                let rk ← renderKey k ks
                let rc ← renderCommentSuffix comment
                let nextRev := rk :: revPrefix
                let hdr := "[" ++ joinRenderedPath nextRev.reverse ++ "]" ++ rc
                if subtableFirst then
                  if !isPlanPermutation sub.toList subPlan then none
                  else if subPlan.all (fun p => p.2.isInlineScope) then none
                  else do
                    let secLines ← renderSectionEntries nextRev sub.toList subPlan
                    let inlLines ← renderInlineEntries nextRev sub.toList subPlan
                    some (secLines ++ [hdr] ++ inlLines)
                else do
                  let bodyLines ← renderTablePlan nextRev sub.toList subPlan
                  some (hdr :: bodyLines)
              | _ => none
            | .aotSection ks elemPlans comment =>
              match v with
              | .array xs =>
                if xs.isEmpty then none
                else do
                  let rk ← renderKey k ks
                  let rc ← renderCommentSuffix comment
                  renderAotElems (rk :: revPrefix) rc xs.toList elemPlans
              | _ => none
            | .direct _ _ _ => some []
            | .dotted _ _ => some []
      let tail ← renderSectionEntries revPrefix tableEntries rest
      some (lines ++ tail)
  termination_by plan => sizeOf plan
  decreasing_by
    all_goals simp +arith

  /-- Render each element of an `[[array_of_tables]]` section. -/
  def renderAotElems (revTarget : List String) (rc : String) :
      List TomlValue → List (List (String × EntryPlacement)) → Option (List String)
    | [], [] => some []
    | .table elem :: xs, ep :: eps => do
      let hdr := "[[" ++ joinRenderedPath revTarget.reverse ++ "]]" ++ rc
      let body ← renderTablePlan revTarget elem.toList ep
      let tail ← renderAotElems revTarget rc xs eps
      some (hdr :: body ++ tail)
    | _, _ => none
  termination_by _ eps => sizeOf eps + 1
  decreasing_by
    all_goals simp +arith
end

/-- Nondeterministic generative specification rendering a `WellFormedTable` according to `RenderTape`. -/
def render (doc : TomlTable) (tape : RenderTape) : Option String :=
  if !wellFormedTableBool doc then none
  else do
    let hdrLines ←
      match tape.headerComment with
      | none => some []
      | some c => if isSingleLineClean c then some ["#" ++ c] else none
    let bodyLines ← renderTablePlan [] doc.toList tape.entries
    some (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n")

/-- Allowed outcome relation for `Toml.parse` against `WellFormedTable`, `render`, and `TomlTableEquiv`. -/
def allowedParse (raw : String) (out : Except TomlError TomlTable) : Prop :=
  match out with
  | .ok parsed =>
    WellFormedTable parsed ∧
      ∀ doc tape, render doc tape = some raw → TomlTableEquiv doc parsed
  | .error e =>
    !e.message.isEmpty = true ∧
      ∀ doc tape, render doc tape ≠ some raw

/-- Check whether `sub` occurs as a contiguous character slice within `cs`. -/
def hasCharSublist (sub : List Char) : List Char → Bool
  | [] => sub.isEmpty
  | c :: cs => sub.isPrefixOf (c :: cs) || hasCharSublist sub cs

/-- Allowed outcome relation for `Toml.format` across all `TomlTable` inputs: empty tables format to `""`; non-empty well-formed tables emit a comment-free `render` output under some `RenderTape`; ill-formed non-empty tables still emit newline-terminated text containing every top-level rendered key. -/
def allowedFormat (doc : TomlTable) (out : String) : Prop :=
  if doc.toList.isEmpty then
    out = ""
  else if wellFormedTableBool doc then
    ∃ tape : RenderTape, tape.headerComment = none ∧ render doc tape = some out
  else
    out.toList.reverse.head? = some '\n' ∧
      ∀ k v, (k, v) ∈ doc.toList →
        ∃ rk, renderKey k (if isValidBareKey k then .bare else .basic) = some rk ∧
          hasCharSublist rk.toList out.toList = true

/-- Allowed outcome relation for `Toml.getTable`. -/
def allowedGetTable (v : TomlValue) (out : Except TomlError TomlTable) : Prop :=
  match v, out with
  | .table t, .ok res => res = t
  | .table _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.getArray`. -/
def allowedGetArray (v : TomlValue) (out : Except TomlError (Array TomlValue)) : Prop :=
  match v, out with
  | .array xs, .ok res => res = xs
  | .array _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.decode` over `[FromToml α]`. -/
def allowedDecode {α : Type} [FromToml α] (v : TomlValue) (out : Except TomlError α) : Prop :=
  match FromToml.fromToml (α := α) v, out with
  | .ok a, .ok b => b = a
  | .error _, .error e => e.kind = .decodeError ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Reference model for `Toml.encode` over `[ToToml α]`. -/
def encodeModel {α : Type} [ToToml α] (x : α) : TomlValue :=
  ToToml.toToml x

/-- Allowed outcome relation for `Toml.getField` over `[FromToml α]`. -/
def allowedGetField {α : Type} [FromToml α] (t : TomlTable) (key : String)
    (out : Except TomlError α) : Prop :=
  match lookupKey key t, out with
  | none, .error e => e.kind = .missingField ∧ e.path = some key ∧ !e.message.isEmpty = true
  | some v, .ok a => FromToml.fromToml v = .ok a
  | some v, .error e =>
    (FromToml.fromToml (α := α) v).isOk = false ∧
      e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Allowed outcome relation for `Toml.getOptField` over `[FromToml α]`. -/
def allowedGetOptField {α : Type} [FromToml α] (t : TomlTable) (key : String)
    (out : Except TomlError (Option α)) : Prop :=
  match lookupKey key t, out with
  | none, .ok none => True
  | some v, .ok (some a) => FromToml.fromToml v = .ok a
  | some v, .error e =>
    (FromToml.fromToml (α := α) v).isOk = false ∧
      e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Recursively specify nested table path lookup and `FromToml` decoding along `keys`. -/
def allowedGetPathAux {α : Type} [FromToml α] (revPrefix : List String) (t : TomlTable) :
    List String → Except TomlError α → Prop
  | [], out =>
    match FromToml.fromToml (α := α) (.table t), out with
    | .ok a, .ok b => b = a
    | .error _, .error e => e.kind = .decodeError ∧ e.path = none ∧ !e.message.isEmpty = true
    | _, _ => False
  | [k], out =>
    let full := String.intercalate "." (revPrefix.reverse ++ [k])
    match lookupKey k t, out with
    | none, .error e => e.kind = .missingField ∧ e.path = some full ∧ !e.message.isEmpty = true
    | some v, .ok a => FromToml.fromToml v = .ok a
    | some v, .error e =>
      (FromToml.fromToml (α := α) v).isOk = false ∧
        e.kind = .decodeError ∧ e.path = some full ∧ !e.message.isEmpty = true
    | _, _ => False
  | k :: k' :: rest, out =>
    let full := String.intercalate "." (revPrefix.reverse ++ [k])
    match lookupKey k t with
    | none => ∃ e, out = .error e ∧ e.kind = .missingField ∧ e.path = some full ∧ !e.message.isEmpty = true
    | some (.table sub) => allowedGetPathAux (k :: revPrefix) sub (k' :: rest) out
    | some _ => ∃ e, out = .error e ∧ e.kind = .typeMismatch ∧ e.path = some full ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.getPath` over `[FromToml α]`. -/
def allowedGetPath {α : Type} [FromToml α] (t : TomlTable) (keys : List String)
    (out : Except TomlError α) : Prop :=
  allowedGetPathAux [] t keys out

end LeanSwe.Toml.Model

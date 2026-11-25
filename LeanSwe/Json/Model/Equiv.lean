import Lean.Data.Json.Basic

namespace LeanSwe.Json.Model

/-- Flatten a `Std.DTreeMap` internal tree into its in-order association list of `(key, value)` pairs. -/
def treeEntries : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → List (String × Lean.Json)
  | .leaf => []
  | .inner _ k v l r => treeEntries l ++ (k, v) :: treeEntries r

/-- Extract the in-order association list of `(key, value)` pairs from a raw JSON object map. -/
def objEntries (kvs : Std.TreeMap.Raw String Lean.Json compare) : List (String × Lean.Json) :=
  treeEntries kvs.inner.inner

/-- Look up the first value associated with `k` in a JSON object association list. -/
def lookupKeyList (k : String) : List (String × Lean.Json) → Option Lean.Json
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupKeyList k rest

/-- Look up `k` in a JSON object map via its in-order association list. -/
def lookupObj (k : String) (kvs : Std.TreeMap.Raw String Lean.Json compare) : Option Lean.Json :=
  lookupKeyList k (objEntries kvs)

/-- Check whether `k` appears as a key in a JSON object association list. -/
def hasKeyList (k : String) : List (String × Lean.Json) → Bool
  | [] => false
  | (k', _) :: rest => k == k' || hasKeyList k rest

/-- Check that all keys in an association list are pairwise distinct. -/
def noDupKeysBool : List (String × Lean.Json) → Bool
  | [] => true
  | (k, _) :: rest => !hasKeyList k rest && noDupKeysBool rest

/-- Check that a list of strings has pairwise distinct elements. -/
def noDupStringsBool : List String → Bool
  | [] => true
  | k :: rest => !rest.contains k && noDupStringsBool rest

/-- Check that keys in an association list are strictly increasing under `compare`. -/
def isStrictlySortedKeys : List (String × Lean.Json) → Bool
  | [] => true
  | [_] => true
  | (k1, _) :: (k2, v2) :: rest =>
    (compare k1 k2 == .lt) && isStrictlySortedKeys ((k2, v2) :: rest)

mutual
  /-- Computable structural well-formedness check on `Lean.Json` (strictly ordered unique BST keys at every `.obj`). -/
  def wellFormedJsonBool : Lean.Json → Bool
    | .null | .bool _ | .num _ | .str _ => true
    | .arr xs => wellFormedJsonListBool xs.toList
    | .obj kvs => isStrictlySortedKeys (objEntries kvs) && wellFormedJsonTreeBool kvs.inner.inner
  termination_by j => sizeOf j
  decreasing_by
    · cases xs; simp +arith
    · cases kvs with | mk inner => cases inner; simp +arith

  /-- Computable well-formedness check across a list of `Lean.Json` values. -/
  def wellFormedJsonListBool : List Lean.Json → Bool
    | [] => true
    | x :: xs => wellFormedJsonBool x && wellFormedJsonListBool xs
  termination_by xs => sizeOf xs

  /-- Computable well-formedness check across values stored in a `Std.DTreeMap` internal tree. -/
  def wellFormedJsonTreeBool : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → Bool
    | .leaf => true
    | .inner _ _ v l r =>
      wellFormedJsonTreeBool l && wellFormedJsonBool v && wellFormedJsonTreeBool r
  termination_by t => sizeOf t
end

/-- Structural well-formedness predicate for `Lean.Json` values. -/
def WellFormedJson (j : Lean.Json) : Prop :=
  wellFormedJsonBool j = true

/-- Exact decimal value equivalence on `Lean.JsonNumber` (`a.mantissa * 10^(-a.exponent) = b.mantissa * 10^(-b.exponent)`). -/
def numEquiv (a b : Lean.JsonNumber) : Prop :=
  a.mantissa * ((10 : Int) ^ b.exponent) = b.mantissa * ((10 : Int) ^ a.exponent)

/-- Computable Boolean check for exact decimal equivalence of two `Lean.JsonNumber` values. -/
def numEquivBool (a b : Lean.JsonNumber) : Bool :=
  decide (a.mantissa * ((10 : Int) ^ b.exponent) = b.mantissa * ((10 : Int) ^ a.exponent))

/-- `numEquivBool a b = true` holds iff `numEquiv a b`. -/
theorem numEquivBool_iff (a b : Lean.JsonNumber) :
    numEquivBool a b = true ↔ numEquiv a b := by
  unfold numEquivBool numEquiv
  exact decide_eq_true_iff

/-- Reflexivity of `numEquiv`. -/
theorem numEquiv_refl (a : Lean.JsonNumber) : numEquiv a a := rfl

/-- Symmetry of `numEquiv`. -/
theorem numEquiv_symm {a b : Lean.JsonNumber} (h : numEquiv a b) : numEquiv b a := h.symm

/-- Helper proving `(10 : Int) ^ n ≠ 0` for all `n : Nat`. -/
theorem int_pow10_ne_zero (n : Nat) : ((10 : Int) ^ n) ≠ 0 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    intro h
    rcases Int.mul_eq_zero.mp h with h1 | h2
    · exact ih h1
    · cases h2

/-- Transitivity of `numEquiv`. -/
theorem numEquiv_trans {a b c : Lean.JsonNumber} (hab : numEquiv a b) (hbc : numEquiv b c) :
    numEquiv a c := by
  unfold numEquiv at *
  have h1 : (a.mantissa * (10 : Int) ^ c.exponent) * (10 : Int) ^ b.exponent =
      (c.mantissa * (10 : Int) ^ a.exponent) * (10 : Int) ^ b.exponent := by
    calc
      (a.mantissa * (10 : Int) ^ c.exponent) * (10 : Int) ^ b.exponent
          = (a.mantissa * (10 : Int) ^ b.exponent) * (10 : Int) ^ c.exponent := by
            rw [Int.mul_assoc, Int.mul_comm ((10 : Int) ^ c.exponent), ← Int.mul_assoc]
      _ = (b.mantissa * (10 : Int) ^ a.exponent) * (10 : Int) ^ c.exponent := by rw [hab]
      _ = (b.mantissa * (10 : Int) ^ c.exponent) * (10 : Int) ^ a.exponent := by
            rw [Int.mul_assoc, Int.mul_comm ((10 : Int) ^ a.exponent), ← Int.mul_assoc]
      _ = (c.mantissa * (10 : Int) ^ b.exponent) * (10 : Int) ^ a.exponent := by rw [hbc]
      _ = (c.mantissa * (10 : Int) ^ a.exponent) * (10 : Int) ^ b.exponent := by
            rw [Int.mul_assoc, Int.mul_comm ((10 : Int) ^ b.exponent), ← Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right (int_pow10_ne_zero b.exponent) h1

mutual
  /-- Additive structural rank of a `Lean.Json` value for recursion over `objEntries`. -/
  def jsonRank : Lean.Json → Nat
    | .null | .bool _ | .num _ | .str _ => 1
    | .arr xs => 1 + jsonListRank xs.toList
    | .obj kvs => 1 + jsonTreeRank kvs.inner.inner
  termination_by j => sizeOf j
  decreasing_by
    · cases xs; simp +arith
    · cases kvs with | mk inner => cases inner; simp +arith

  /-- Additive structural rank of a list of `Lean.Json` values. -/
  def jsonListRank : List Lean.Json → Nat
    | [] => 0
    | x :: xs => jsonRank x + 1 + jsonListRank xs
  termination_by xs => sizeOf xs

  /-- Additive structural rank of a `Std.DTreeMap` internal tree of `Lean.Json` values. -/
  def jsonTreeRank : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → Nat
    | .leaf => 0
    | .inner _ _ v l r => jsonTreeRank l + (jsonRank v + 1) + jsonTreeRank r
  termination_by t => sizeOf t
end

/-- Additive structural rank of an association list of `(String × Lean.Json)` entries. -/
def jsonAssocRank : List (String × Lean.Json) → Nat
  | [] => 0
  | (_, v) :: rest => jsonRank v + 1 + jsonAssocRank rest

/-- `jsonAssocRank` distributes additively over list concatenation. -/
theorem jsonAssocRank_append (xs ys : List (String × Lean.Json)) :
    jsonAssocRank (xs ++ ys) = jsonAssocRank xs + jsonAssocRank ys := by
  induction xs with
  | nil => simp [jsonAssocRank]
  | cons hd tl ih =>
    rcases hd with ⟨_, v⟩
    simp only [List.cons_append, jsonAssocRank, ih]
    omega

/-- `jsonAssocRank (treeEntries t)` equals `jsonTreeRank t`. -/
theorem jsonAssocRank_treeEntries (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    jsonAssocRank (treeEntries t) = jsonTreeRank t := by
  induction t with
  | leaf => simp [treeEntries, jsonAssocRank, jsonTreeRank]
  | inner _ k v l r ihl ihr =>
    simp only [treeEntries, jsonAssocRank_append, jsonAssocRank, jsonTreeRank, ihl, ihr]
    omega

/-- Looking up a key in an association list yields a value of strictly smaller `jsonRank`. -/
theorem lookupKeyList_rank_lt {k : String} {entries : List (String × Lean.Json)} {v : Lean.Json}
    (h : lookupKeyList k entries = some v) : jsonRank v < jsonAssocRank entries := by
  induction entries with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [lookupKeyList] at h
    split at h
    · cases h; simp [jsonAssocRank]; omega
    · have hlt := ih h; simp [jsonAssocRank]; omega

mutual
  /-- Semantic equivalence on `Lean.Json` (decimal `numEquiv` on numbers, key-order-insensitive lookup equivalence on objects). -/
  def JsonEquiv (a b : Lean.Json) : Prop :=
    match a, b with
    | .null, .null => True
    | .bool b1, .bool b2 => b1 = b2
    | .num n1, .num n2 => numEquiv n1 n2
    | .str s1, .str s2 => s1 = s2
    | .arr xs, .arr ys => JsonListEquiv xs.toList ys.toList
    | .obj kvs1, .obj kvs2 => JsonObjEquivList (objEntries kvs1) (objEntries kvs2)
    | _, _ => False
  termination_by jsonRank a * 2 + 1
  decreasing_by
    · simp [jsonRank]; omega
    · simp [jsonRank, objEntries, jsonAssocRank_treeEntries]; omega

  /-- Element-wise `JsonEquiv` on `List Lean.Json`. -/
  def JsonListEquiv (xs ys : List Lean.Json) : Prop :=
    match xs, ys with
    | [], [] => True
    | x :: xr, y :: yr => JsonEquiv x y ∧ JsonListEquiv xr yr
    | _, _ => False
  termination_by jsonListRank xs * 2 + 2
  decreasing_by
    · simp [jsonListRank]; try omega
    · simp [jsonListRank]; try omega

  /-- Lookup-extensional `JsonEquiv` on object association lists. -/
  def JsonObjEquivList (t1 t2 : List (String × Lean.Json)) : Prop :=
    (∀ (k : String), lookupKeyList k t1 = none → lookupKeyList k t2 = none) ∧
    (∀ (k : String) (v1 : Lean.Json), (h1 : lookupKeyList k t1 = some v1) →
      ∃ v2 : Lean.Json, lookupKeyList k t2 = some v2 ∧ JsonEquiv v1 v2)
  termination_by jsonAssocRank t1 * 2 + 2
  decreasing_by
    have hlt := lookupKeyList_rank_lt h1
    omega
end

/-- Reflexivity, symmetry, and transitivity of `JsonEquiv` proved jointly by strong induction on `jsonRank`. -/
theorem jsonEquiv_properties :
    (∀ (n : Nat) (a : Lean.Json), jsonRank a ≤ n → JsonEquiv a a) ∧
    (∀ (n : Nat) (a b : Lean.Json), jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b a) ∧
    (∀ (n : Nat) (a b c : Lean.Json), jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b c → JsonEquiv a c) := by
  have hMain : ∀ (n : Nat),
      (∀ a : Lean.Json, jsonRank a ≤ n → JsonEquiv a a) ∧
      (∀ a b : Lean.Json, jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b a) ∧
      (∀ a b c : Lean.Json, jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b c → JsonEquiv a c) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have hrefl : ∀ a : Lean.Json, jsonRank a ≤ n → JsonEquiv a a := by
        intro a ha
        cases a with
        | null | bool _ | str _ => simp [JsonEquiv]
        | num x => simp [JsonEquiv, numEquiv_refl]
        | arr xs =>
          simp only [JsonEquiv]
          have hsub : ∀ l : List Lean.Json, jsonListRank l < jsonRank (.arr xs) → JsonListEquiv l l := by
            intro l hl
            induction l with
            | nil => simp [JsonListEquiv]
            | cons x xr ihl =>
              simp only [JsonListEquiv]
              have hx : jsonRank x < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
              have hxr : jsonListRank xr < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
              exact ⟨(ih (jsonRank x) (by omega)).1 x (Nat.le_refl _), ihl (by omega)⟩
          exact hsub xs.toList (by simp [jsonRank])
        | obj kvs =>
          simp only [JsonEquiv, JsonObjEquivList]
          refine ⟨fun _ hk => hk, fun k v hk => ⟨v, hk, ?_⟩⟩
          have hv : jsonRank v < jsonAssocRank (objEntries kvs) := lookupKeyList_rank_lt hk
          have ht : jsonAssocRank (objEntries kvs) < jsonRank (.obj kvs) := by
            simp [objEntries, jsonAssocRank_treeEntries, jsonRank]
          exact (ih (jsonRank v) (by omega)).1 v (Nat.le_refl _)
      have hsymm : ∀ a b : Lean.Json, jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b a := by
        intro a b ha hab
        cases a with
        | null => cases b <;> simp [JsonEquiv] at hab ⊢
        | bool b1 => cases b <;> simp [JsonEquiv] at hab ⊢; exact hab.symm
        | num n1 => cases b <;> simp [JsonEquiv] at hab ⊢; exact numEquiv_symm hab
        | str s1 => cases b <;> simp [JsonEquiv] at hab ⊢; exact hab.symm
        | arr xs =>
          cases b with
          | arr ys =>
            simp only [JsonEquiv] at hab ⊢
            have hlist : ∀ l1 l2 : List Lean.Json,
                jsonListRank l1 < jsonRank (.arr xs) → JsonListEquiv l1 l2 → JsonListEquiv l2 l1 := by
              intro l1 l2 hl1 h12
              induction l1 generalizing l2 with
              | nil => cases l2 <;> simp [JsonListEquiv] at h12 ⊢
              | cons x xr ihl =>
                cases l2 with
                | nil => simp [JsonListEquiv] at h12
                | cons y yr =>
                  simp only [JsonListEquiv] at h12 ⊢
                  have hx : jsonRank x < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
                  have hxr : jsonListRank xr < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
                  exact ⟨(ih (jsonRank x) (by omega)).2.1 x y (Nat.le_refl _) h12.1, ihl yr (by omega) h12.2⟩
            exact hlist xs.toList ys.toList (by simp [jsonRank]) hab
          | _ => simp [JsonEquiv] at hab
        | obj kvs1 =>
          cases b with
          | obj kvs2 =>
            simp only [JsonEquiv, JsonObjEquivList] at hab ⊢
            rcases hab with ⟨hnone, hsome⟩
            constructor
            · intro k hk2
              cases hk1 : lookupKeyList k (objEntries kvs1) with
              | none => rfl
              | some v1 =>
                obtain ⟨v2, hv2, _⟩ := hsome k v1 hk1
                rw [hk2] at hv2; cases hv2
            · intro k v2 hk2
              cases hk1 : lookupKeyList k (objEntries kvs1) with
              | none =>
                have h2n := hnone k hk1
                rw [hk2] at h2n; cases h2n
              | some v1 =>
                obtain ⟨v2', hv2', heq⟩ := hsome k v1 hk1
                rw [hk2] at hv2'; cases hv2'
                have hv1 : jsonRank v1 < jsonAssocRank (objEntries kvs1) := lookupKeyList_rank_lt hk1
                have ht1 : jsonAssocRank (objEntries kvs1) < jsonRank (.obj kvs1) := by
                  simp [objEntries, jsonAssocRank_treeEntries, jsonRank]
                exact ⟨v1, rfl, (ih (jsonRank v1) (by omega)).2.1 v1 v2 (Nat.le_refl _) heq⟩
          | _ => simp [JsonEquiv] at hab
      have htrans : ∀ a b c : Lean.Json, jsonRank a ≤ n → JsonEquiv a b → JsonEquiv b c → JsonEquiv a c := by
        intro a b c ha hab hbc
        cases a with
        | null => cases b <;> cases c <;> simp [JsonEquiv] at hab hbc ⊢
        | bool b1 => cases b <;> cases c <;> simp [JsonEquiv] at hab hbc ⊢; exact hab.trans hbc
        | num n1 => cases b <;> cases c <;> simp [JsonEquiv] at hab hbc ⊢; exact numEquiv_trans hab hbc
        | str s1 => cases b <;> cases c <;> simp [JsonEquiv] at hab hbc ⊢; exact hab.trans hbc
        | arr xs =>
          cases b <;> cases c <;> simp [JsonEquiv] at hab hbc ⊢
          rename_i ys zs
          have hlist : ∀ l1 l2 l3 : List Lean.Json,
              jsonListRank l1 < jsonRank (.arr xs) →
              JsonListEquiv l1 l2 → JsonListEquiv l2 l3 → JsonListEquiv l1 l3 := by
            intro l1 l2 l3 hl1 h12 h23
            induction l1 generalizing l2 l3 with
            | nil =>
              cases l2 with
              | nil => cases l3 <;> simp [JsonListEquiv] at h23 ⊢
              | cons _ _ => simp [JsonListEquiv] at h12
            | cons x xr ihl =>
              cases l2 with
              | nil => simp [JsonListEquiv] at h12
              | cons y yr =>
                cases l3 with
                | nil => simp [JsonListEquiv] at h23
                | cons z zr =>
                  simp only [JsonListEquiv] at h12 h23 ⊢
                  have hx : jsonRank x < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
                  have hxr : jsonListRank xr < jsonListRank (x :: xr) := by simp [jsonListRank]; try omega
                  exact ⟨(ih (jsonRank x) (by omega)).2.2 x y z (Nat.le_refl _) h12.1 h23.1,
                    ihl yr zr (by omega) h12.2 h23.2⟩
          exact hlist xs.toList ys.toList zs.toList (by simp [jsonRank]) hab hbc
        | obj kvs1 =>
          cases b <;> cases c <;> simp [JsonEquiv, JsonObjEquivList] at hab hbc ⊢
          rename_i kvs2 kvs3
          rcases hab with ⟨h12n, h12s⟩
          rcases hbc with ⟨h23n, h23s⟩
          refine ⟨fun k hk1 => h23n k (h12n k hk1), fun k v1 hk1 => ?_⟩
          obtain ⟨v2, hk2, heq12⟩ := h12s k v1 hk1
          obtain ⟨v3, hk3, heq23⟩ := h23s k v2 hk2
          have hv1 : jsonRank v1 < jsonAssocRank (objEntries kvs1) := lookupKeyList_rank_lt hk1
          have ht1 : jsonAssocRank (objEntries kvs1) < jsonRank (.obj kvs1) := by
            simp [objEntries, jsonAssocRank_treeEntries, jsonRank]
          exact ⟨v3, hk3, (ih (jsonRank v1) (by omega)).2.2 v1 v2 v3 (Nat.le_refl _) heq12 heq23⟩
      exact ⟨hrefl, hsymm, htrans⟩
  exact ⟨fun n a h => (hMain n).1 a h, fun n a b h => (hMain n).2.1 a b h, fun n a b c h => (hMain n).2.2 a b c h⟩

/-- Reflexivity of `JsonEquiv`. -/
theorem jsonEquiv_refl (a : Lean.Json) : JsonEquiv a a :=
  jsonEquiv_properties.1 (jsonRank a) a (Nat.le_refl _)

/-- Symmetry of `JsonEquiv`. -/
theorem jsonEquiv_symm {a b : Lean.Json} (h : JsonEquiv a b) : JsonEquiv b a :=
  jsonEquiv_properties.2.1 (jsonRank a) a b (Nat.le_refl _) h

/-- Transitivity of `JsonEquiv`. -/
theorem jsonEquiv_trans {a b c : Lean.Json} (hab : JsonEquiv a b) (hbc : JsonEquiv b c) :
    JsonEquiv a c :=
  jsonEquiv_properties.2.2 (jsonRank a) a b c (Nat.le_refl _) hab hbc

/-- `JsonEquiv` is a mathematical equivalence relation. -/
theorem equivalence_jsonEquiv : Equivalence JsonEquiv :=
  ⟨jsonEquiv_refl, @jsonEquiv_symm, @jsonEquiv_trans⟩

end LeanSwe.Json.Model

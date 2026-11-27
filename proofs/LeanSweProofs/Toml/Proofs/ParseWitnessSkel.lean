import LeanSweProofs.Toml.Proofs.ParseWitnessScalar

/-!
# Builder-to-Skeleton Projection & Monotonicity (`entriesToSkel`, `EntriesExtend`)

Establishes `nodeToSkel`/`entriesToSkel`, monotonic builder extension (`NodeExtends`,
`EntriesExtend`, `AotExtends`), `skelMatchesEntries_entriesToSkel`, and `insertDottedEntries_witness`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

mutual
  /-- Project an `Impl.Node` builder node to its pure `Model.SkeletonNode` provenance shape. -/
  def nodeToSkel : Node → SkeletonNode
    | .leaf (.table _) => .inlineTable
    | .leaf _ => .leaf
    | .table .inline _ => .inlineTable
    | .table .explicit sub => .table .explicit (entriesToSkel sub)
    | .table .subtableImplicit sub => .table .subtableImplicit (entriesToSkel sub)
    | .table .dotted sub => .table .dotted (entriesToSkel sub)
    | .aot elems => .aot (aotToSkel elems)
  termination_by n => sizeOf n
  decreasing_by all_goals simp +arith

  /-- Project a builder association list to `List (String × SkeletonNode)`. -/
  def entriesToSkel : List (String × Node) → List (String × SkeletonNode)
    | [] => []
    | (k, n) :: rest => (k, nodeToSkel n) :: entriesToSkel rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp +arith

  /-- Project `[[aot]]` element builders to skeleton lists. -/
  def aotToSkel : List (List (String × Node)) → List (List (String × SkeletonNode))
    | [] => []
    | e :: rest => entriesToSkel e :: aotToSkel rest
  termination_by elems => sizeOf elems
  decreasing_by all_goals simp +arith
end

theorem assocLookupNode_sizeOf_lt {k : String} {n : Node} :
    ∀ es : List (String × Node), assocLookupNode k es = some n → sizeOf n < sizeOf es
  | [], h => nomatch h
  | (_, vh) :: tl, h => by
    simp only [assocLookupNode] at h
    split at h
    · obtain rfl := Option.some.inj h; simp +arith
    · have ih := assocLookupNode_sizeOf_lt tl h; simp +arith at ih ⊢; omega

@[simp] theorem entriesToSkel_nil : entriesToSkel [] = [] := by
  simp [entriesToSkel]

@[simp] theorem aotToSkel_nil : aotToSkel [] = [] := by
  simp [aotToSkel]

theorem assocLookupSkel_entriesToSkel (k : String) :
    ∀ es : List (String × Node), assocLookupSkel k (entriesToSkel es) = (assocLookupNode k es).map nodeToSkel
  | [] => by simp [assocLookupSkel, assocLookupNode]
  | (kh, nh) :: tl => by
    simp only [entriesToSkel, assocLookupSkel, assocLookupNode]
    by_cases h : (k == kh) = true <;> simp [h, assocLookupSkel_entriesToSkel k tl]

theorem entriesToSkel_assocSetNode (k : String) (n : Node) :
    ∀ es : List (String × Node), entriesToSkel (assocSetNode k n es) = assocSetSkel k (nodeToSkel n) (entriesToSkel es)
  | [] => by simp [assocSetNode, entriesToSkel, assocSetSkel]
  | (kh, nh) :: tl => by
    simp only [assocSetNode, entriesToSkel, assocSetSkel]
    by_cases h : (k == kh) = true <;> simp [h, entriesToSkel, entriesToSkel_assocSetNode k n tl]

theorem lookupKeyList_entriesToTomlList (k : String) :
    ∀ es : List (String × Node), lookupKeyList k (entriesToTomlList es) = (assocLookupNode k es).map nodeToTomlValue
  | [] => rfl
  | (kh, nh) :: tl => by
    simp only [entriesToTomlList, lookupKeyList, assocLookupNode]
    by_cases h : (k == kh) = true <;> simp [h, lookupKeyList_entriesToTomlList k tl]

theorem assocLookupNode_assocSetNode (q k : String) (v : Node) :
    ∀ es : List (String × Node),
      assocLookupNode q (assocSetNode k v es) = if q == k then some v else assocLookupNode q es
  | [] => by simp [assocSetNode, assocLookupNode]
  | (kh, vh) :: tl => by
    simp only [assocSetNode]
    by_cases h : (k == kh) = true
    · have hk := eq_of_beq h; subst hk
      by_cases hq : (q == k) = true <;> simp [assocLookupNode, hq]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, assocLookupNode]
      by_cases hqh : (q == kh) = true
      · have hqk : (q == k) = false := by
          have e1 := eq_of_beq hqh; subst e1
          cases h2 : (q == k)
          · rfl
          · have e2 := eq_of_beq h2; subst e2; simp at h
        simp [hqh, hqk]
      · simp [hqh, assocLookupNode_assocSetNode q k v tl]

mutual
  theorem nodeToTomlValue_valueToInlineNode : (v : TomlValue) → nodeToTomlValue (valueToInlineNode v) = v
    | .table t => by
      simp only [valueToInlineNode, nodeToTomlValue, entriesToTomlList_inlineListToNodes t.toList, Array.toArray_toList]
    | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ | .array _ => rfl
  termination_by v => sizeOf v
  decreasing_by exact Nat.lt_trans (sizeOf_toList_lt_array t) (by simp +arith)

  theorem entriesToTomlList_inlineListToNodes :
      (l : List (String × TomlValue)) → entriesToTomlList (inlineListToNodes l) = l
    | [] => rfl
    | (k, v) :: tl => by
      simp [inlineListToNodes, entriesToTomlList, nodeToTomlValue_valueToInlineNode v,
        entriesToTomlList_inlineListToNodes tl]
  termination_by l => sizeOf l
  decreasing_by all_goals simp +arith
end

theorem nodeToSkel_valueToInlineNode (v : TomlValue) :
    nodeToSkel (valueToInlineNode v) = (match v with | .table _ => SkeletonNode.inlineTable | _ => SkeletonNode.leaf) := by
  cases v <;> simp [valueToInlineNode, nodeToSkel]

mutual
  /-- Monotonic builder growth relation preserving assigned leaves/inline tables and extending open tables/AoTs. -/
  def NodeExtends : Node → Node → Prop
    | .leaf v, n2 => n2 = .leaf v
    | .table .inline sub, n2 => n2 = .table .inline sub
    | .table .explicit s1, .table k2 s2 => k2 ≠ .inline ∧ EntriesExtend s1 s2
    | .table .subtableImplicit s1, .table k2 s2 => k2 ≠ .inline ∧ EntriesExtend s1 s2
    | .table .dotted s1, .table k2 s2 => k2 ≠ .inline ∧ EntriesExtend s1 s2
    | .aot es1, .aot es2 => AotExtends es1 es2
    | _, _ => False
  termination_by n1 _ => sizeOf n1 * 2
  decreasing_by all_goals simp +arith

  /-- Every entry present in `e1` remains present in `e2` with an extended `Node`. -/
  def EntriesExtend (e1 e2 : List (String × Node)) : Prop :=
    ∀ k n1, assocLookupNode k e1 = some n1 → ∃ n2, assocLookupNode k e2 = some n2 ∧ NodeExtends n1 n2
  termination_by sizeOf e1 * 2 + 1
  decreasing_by
    have := assocLookupNode_sizeOf_lt e1 ‹_›
    omega

  /-- Prefix-wise `EntriesExtend` on `[[aot]]` element lists (allowing later `[[aot]]` appends). -/
  def AotExtends : List (List (String × Node)) → List (List (String × Node)) → Prop
    | [], _ => True
    | e1 :: r1, e2 :: r2 => EntriesExtend e1 e2 ∧ AotExtends r1 r2
    | _ :: _, [] => False
  termination_by es1 _ => sizeOf es1 * 2
  decreasing_by all_goals simp +arith
end

theorem EntriesExtend.lookup {e1 e2 : List (String × Node)} (h : EntriesExtend e1 e2)
    {k : String} {n1 : Node} (hlu : assocLookupNode k e1 = some n1) :
    ∃ n2, assocLookupNode k e2 = some n2 ∧ NodeExtends n1 n2 := by
  rw [EntriesExtend] at h; exact h k n1 hlu

theorem entriesExtend_nil (e : List (String × Node)) : EntriesExtend [] e := by
  rw [EntriesExtend]; intro _ _ h; nomatch h

mutual
  theorem nodeExtends_refl : (n : Node) → NodeExtends n n
    | .leaf _ => by simp only [NodeExtends]
    | .table kind sub => by
      cases kind <;> simp only [NodeExtends]
      · exact ⟨by decide, entriesExtend_refl sub⟩
      · exact ⟨by decide, entriesExtend_refl sub⟩
      · exact ⟨by decide, entriesExtend_refl sub⟩
    | .aot es => by simp only [NodeExtends]; exact aotExtends_refl es
  termination_by n => sizeOf n * 2
  decreasing_by all_goals simp +arith

  theorem entriesExtend_refl (e : List (String × Node)) : EntriesExtend e e := by
    rw [EntriesExtend]
    intro k n1 hlu
    exact ⟨n1, hlu, nodeExtends_refl n1⟩
  termination_by sizeOf e * 2 + 1
  decreasing_by
    have := assocLookupNode_sizeOf_lt e ‹_›
    omega

  theorem aotExtends_refl : (es : List (List (String × Node))) → AotExtends es es
    | [] => by simp [AotExtends]
    | e :: r => by simp only [AotExtends]; exact ⟨entriesExtend_refl e, aotExtends_refl r⟩
  termination_by es => sizeOf es * 2
  decreasing_by all_goals simp +arith
end

mutual
  theorem nodeExtends_trans : {n1 n2 n3 : Node} → NodeExtends n1 n2 → NodeExtends n2 n3 → NodeExtends n1 n3
    | .leaf _, _, _, h12, h23 => by simp only [NodeExtends] at h12 ⊢; subst h12; simpa only [NodeExtends] using h23
    | .table .inline _, _, _, h12, h23 => by simp only [NodeExtends] at h12 ⊢; subst h12; simpa only [NodeExtends] using h23
    | .table .explicit s1, .table k2 s2, .table k3 s3, h12, h23 => by
      simp only [NodeExtends] at h12
      cases k2 with
      | inline => exact absurd rfl h12.1
      | explicit | subtableImplicit | dotted =>
        simp only [NodeExtends] at h23 ⊢; exact ⟨h23.1, entriesExtend_trans h12.2 h23.2⟩
    | .table .explicit _, .table k2 _, .leaf _, h12, h23
    | .table .explicit _, .table k2 _, .aot _, h12, h23 => by
      simp only [NodeExtends] at h12; cases k2 <;> simp [NodeExtends] at h12 h23
    | .table .explicit _, .leaf _, _, h12, _
    | .table .explicit _, .aot _, _, h12, _ => by simp only [NodeExtends] at h12
    | .table .subtableImplicit s1, .table k2 s2, .table k3 s3, h12, h23 => by
      simp only [NodeExtends] at h12
      cases k2 with
      | inline => exact absurd rfl h12.1
      | explicit | subtableImplicit | dotted =>
        simp only [NodeExtends] at h23 ⊢; exact ⟨h23.1, entriesExtend_trans h12.2 h23.2⟩
    | .table .subtableImplicit _, .table k2 _, .leaf _, h12, h23
    | .table .subtableImplicit _, .table k2 _, .aot _, h12, h23 => by
      simp only [NodeExtends] at h12; cases k2 <;> simp [NodeExtends] at h12 h23
    | .table .subtableImplicit _, .leaf _, _, h12, _
    | .table .subtableImplicit _, .aot _, _, h12, _ => by simp only [NodeExtends] at h12
    | .table .dotted s1, .table k2 s2, .table k3 s3, h12, h23 => by
      simp only [NodeExtends] at h12
      cases k2 with
      | inline => exact absurd rfl h12.1
      | explicit | subtableImplicit | dotted =>
        simp only [NodeExtends] at h23 ⊢; exact ⟨h23.1, entriesExtend_trans h12.2 h23.2⟩
    | .table .dotted _, .table k2 _, .leaf _, h12, h23
    | .table .dotted _, .table k2 _, .aot _, h12, h23 => by
      simp only [NodeExtends] at h12; cases k2 <;> simp [NodeExtends] at h12 h23
    | .table .dotted _, .leaf _, _, h12, _
    | .table .dotted _, .aot _, _, h12, _ => by simp only [NodeExtends] at h12
    | .aot es1, .aot es2, .aot es3, h12, h23 => by
      simp only [NodeExtends] at h12 h23 ⊢; exact aotExtends_trans h12 h23
    | .aot _, .aot _, .leaf _, _, h23
    | .aot _, .aot _, .table _ _, _, h23 => by simp only [NodeExtends] at h23
    | .aot _, .leaf _, _, h12, _
    | .aot _, .table _ _, _, h12, _ => by simp only [NodeExtends] at h12
  termination_by n1 _ _ => sizeOf n1 * 2
  decreasing_by all_goals simp +arith

  theorem entriesExtend_trans {e1 e2 e3 : List (String × Node)}
      (h12 : EntriesExtend e1 e2) (h23 : EntriesExtend e2 e3) : EntriesExtend e1 e3 := by
    rw [EntriesExtend]
    intro k n1 hlu1
    obtain ⟨n2, hlu2, hn12⟩ := h12.lookup hlu1
    obtain ⟨n3, hlu3, hn23⟩ := h23.lookup hlu2
    exact ⟨n3, hlu3, nodeExtends_trans hn12 hn23⟩
  termination_by sizeOf e1 * 2 + 1
  decreasing_by
    have := assocLookupNode_sizeOf_lt e1 ‹_›
    omega

  theorem aotExtends_trans {a1 a2 a3 : List (List (String × Node))}
      (h12 : AotExtends a1 a2) (h23 : AotExtends a2 a3) : AotExtends a1 a3 := by
    cases a1 with
    | nil => simp [AotExtends]
    | cons e1 r1 =>
      cases a2 with
      | nil => simp [AotExtends] at h12
      | cons e2 r2 =>
        cases a3 with
        | nil => simp [AotExtends] at h23
        | cons e3 r3 =>
          simp only [AotExtends] at h12 h23 ⊢
          exact ⟨entriesExtend_trans h12.1 h23.1, aotExtends_trans h12.2 h23.2⟩
  termination_by sizeOf a1 * 2
  decreasing_by all_goals (subst_vars; simp +arith)
end

theorem nodeExtends_valueToInlineNode {v : TomlValue} {n : Node}
    (h : NodeExtends (valueToInlineNode v) n) : n = valueToInlineNode v := by
  cases v <;> simpa [valueToInlineNode, NodeExtends] using h

theorem entriesExtend_assocSet_none {k : String} {v : Node} {es : List (String × Node)}
    (hnone : assocLookupNode k es = none) : EntriesExtend es (assocSetNode k v es) := by
  rw [EntriesExtend]
  intro q n1 hlu
  have hqk : (q == k) = false := by
    cases h2 : (q == k)
    · rfl
    · rw [eq_of_beq h2, hnone] at hlu; nomatch hlu
  rw [assocLookupNode_assocSetNode, hqk]
  exact ⟨n1, hlu, nodeExtends_refl n1⟩

theorem entriesExtend_assocSet_some {k : String} {old v : Node} {es : List (String × Node)}
    (hold : assocLookupNode k es = some old) (hext : NodeExtends old v) :
    EntriesExtend es (assocSetNode k v es) := by
  rw [EntriesExtend]
  intro q n1 hlu
  rw [assocLookupNode_assocSetNode]
  by_cases hqk : (q == k) = true
  · rw [eq_of_beq hqk, hold] at hlu; obtain rfl := Option.some.inj hlu
    simp [hqk, hext]
  · simp [hqk, hlu, nodeExtends_refl n1]

mutual
  /-- Recursive key-uniqueness on openable tables and `[[aot]]` elements. -/
  def NodeKeyNoDup : Node → Bool
    | .leaf _ => true
    | .table .inline _ => true
    | .table .explicit sub => EntriesKeyNoDup sub
    | .table .subtableImplicit sub => EntriesKeyNoDup sub
    | .table .dotted sub => EntriesKeyNoDup sub
    | .aot elems => AotKeyNoDup elems
  termination_by n => sizeOf n * 2
  decreasing_by all_goals simp +arith

  /-- Pairwise distinct keys at this level and recursively on openable children. -/
  def EntriesKeyNoDup (es : List (String × Node)) : Bool :=
    entriesNoDup es && EntriesChildrenKeyNoDup es
  termination_by sizeOf es * 2 + 1
  decreasing_by simp +arith

  /-- Check `NodeKeyNoDup` on every entry in `es`. -/
  def EntriesChildrenKeyNoDup : List (String × Node) → Bool
    | [] => true
    | (_, n) :: rest => NodeKeyNoDup n && EntriesChildrenKeyNoDup rest
  termination_by es => sizeOf es * 2
  decreasing_by all_goals simp +arith

  /-- Check `EntriesKeyNoDup` on every element of an `[[aot]]` list. -/
  def AotKeyNoDup : List (List (String × Node)) → Bool
    | [] => true
    | e :: rest => EntriesKeyNoDup e && AotKeyNoDup rest
  termination_by elems => sizeOf elems * 2
  decreasing_by all_goals simp +arith
end

@[simp] theorem entriesKeyNoDup_nil : EntriesKeyNoDup [] = true := by
  simp [EntriesKeyNoDup, entriesNoDup, EntriesChildrenKeyNoDup]

@[simp] theorem aotKeyNoDup_nil : AotKeyNoDup [] = true := by
  simp [AotKeyNoDup]

private theorem assocHasKey_assocSet_key (k k' : String) (v : Node) :
    ∀ es : List (String × Node), assocHasKey k (assocSetNode k' v es) = (k == k' || assocHasKey k es)
  | [] => by simp [assocSetNode, assocHasKey]
  | (kh, _) :: tl => by
    simp only [assocSetNode]
    by_cases h : (k' == kh) = true
    · rw [eq_of_beq h]; simp [assocHasKey]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, assocHasKey, assocHasKey_assocSet_key k k' v tl]
      cases (k == kh) <;> cases (k == k') <;> rfl

theorem entriesKeyNoDup_assocSet {k : String} {v : Node} {es : List (String × Node)}
    (hes : EntriesKeyNoDup es = true) (hv : NodeKeyNoDup v = true) :
    EntriesKeyNoDup (assocSetNode k v es) = true := by
  have hnd : ∀ l, entriesNoDup l = true → entriesNoDup (assocSetNode k v l) = true := by
    intro l hl; induction l with
    | nil => simp [assocSetNode, entriesNoDup, assocHasKey]
    | cons hd tl ih =>
      rcases hd with ⟨kh, _⟩; simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at hl
      simp only [assocSetNode]
      by_cases heq : (k == kh) = true
      · simpa [heq, entriesNoDup] using hl
      · have hkh : (kh == k) = false := by
          cases h2 : (kh == k) with
          | false => rfl
          | true => exfalso; apply heq; rw [eq_of_beq h2]; exact beq_self_eq_true _
        simp [heq, entriesNoDup, assocHasKey_assocSet_key, hkh, hl.1, ih hl.2]
  have hch : ∀ l, EntriesChildrenKeyNoDup l = true → EntriesChildrenKeyNoDup (assocSetNode k v l) = true := by
    intro l hl; induction l with
    | nil => simp [assocSetNode, EntriesChildrenKeyNoDup, hv]
    | cons hd tl ih =>
      rcases hd with ⟨_, _⟩
      simp only [EntriesChildrenKeyNoDup, Bool.and_eq_true] at hl
      simp only [assocSetNode]; split <;> simp [EntriesChildrenKeyNoDup, hv, hl.1, hl.2, ih hl.2]
  rw [EntriesKeyNoDup] at hes ⊢
  simp only [Bool.and_eq_true] at hes ⊢
  exact ⟨hnd es hes.1, hch es hes.2⟩

theorem assocLookupNode_keyNoDup {k : String} {es : List (String × Node)} {n : Node}
    (hes : EntriesKeyNoDup es = true) (hlu : assocLookupNode k es = some n) :
    NodeKeyNoDup n = true := by
  rw [EntriesKeyNoDup] at hes; have hch := (Bool.and_eq_true_iff.mp hes).2; clear hes
  revert hch
  induction es with
  | nil => intro _; nomatch hlu
  | cons hd tl ih =>
    intro hch
    rcases hd with ⟨_, _⟩
    simp only [EntriesChildrenKeyNoDup, Bool.and_eq_true] at hch
    simp only [assocLookupNode] at hlu
    split at hlu
    · obtain rfl := Option.some.inj hlu; exact hch.1
    · exact ih hlu hch.2

theorem entriesNoDup_to_noDupKeysBool (es : List (String × Node)) (h : entriesNoDup es = true) :
    noDupKeysBool (entriesToTomlList es) = true := by
  have heq : ∀ q l, hasKeyList q (entriesToTomlList l) = assocHasKey q l := by
    intro q l; induction l with | nil => rfl | cons _ _ ih => simp [entriesToTomlList, hasKeyList, assocHasKey, ih]
  induction es with
  | nil => rfl
  | cons _ tl ih =>
    simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [entriesToTomlList, noDupKeysBool, heq, h.1, ih h.2]

private theorem assocLookupNode_of_noDup_mem {es : List (String × Node)} (hnd : entriesNoDup es = true) :
    ∀ k n, (k, n) ∈ es → assocLookupNode k es = some n := by
  induction es with
  | nil => intro _ _ hm; nomatch hm
  | cons hd tl ih =>
    rcases hd with ⟨kh, nh⟩; simp only [entriesNoDup, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    intro k n hm; rcases List.mem_cons.mp hm with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead; simp [assocLookupNode]
    · have hne : (k == kh) = false := by
        cases h2 : (k == kh)
        · rfl
        · have heq := eq_of_beq h2; subst heq
          have hhas : assocHasKey k tl = true := by
            clear ih hnd hm; induction tl with
            | nil => nomatch htail
            | cons p r ihr =>
              rcases p with ⟨kp, np⟩
              rcases List.mem_cons.mp htail with e | ht
              · obtain ⟨rfl, _⟩ := Prod.mk.inj e; simp [assocHasKey]
              · simp [assocHasKey, ihr ht]
          rw [hhas] at hnd; nomatch hnd.1
      simp [assocLookupNode, hne, ih hnd.2 k n htail]

mutual
  private theorem skelNodeMatches_nodeToSkel :
      (n : Node) → NodeKeyNoDup n = true → skelNodeMatchesValue (nodeToSkel n) (nodeToTomlValue n) = true
    | .leaf (.table _), _ => by simp [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue]
    | .leaf (.string _), _ | .leaf (.int _), _ | .leaf (.float _), _ | .leaf (.bool _), _
    | .leaf (.offsetDateTime _), _ | .leaf (.localDateTime _), _ | .leaf (.localDate _), _
    | .leaf (.localTime _), _ | .leaf (.array _), _ => by simp [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue]
    | .table .inline _, _ => by simp [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue]
    | .table .explicit sub, h => by
      simp only [NodeKeyNoDup] at h; simpa [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue] using skelMatchesEntries_entriesToSkel sub h
    | .table .subtableImplicit sub, h => by
      simp only [NodeKeyNoDup] at h; simpa [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue] using skelMatchesEntries_entriesToSkel sub h
    | .table .dotted sub, h => by
      simp only [NodeKeyNoDup] at h; simpa [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue] using skelMatchesEntries_entriesToSkel sub h
    | .aot elems, h => by
      simp only [NodeKeyNoDup] at h; simpa [nodeToSkel, nodeToTomlValue, skelNodeMatchesValue] using skelMatchesAot_aotToSkel elems h
  termination_by n => sizeOf n * 2
  decreasing_by all_goals simp +arith

  theorem skelMatchesEntries_entriesToSkel (es : List (String × Node)) (hes : EntriesKeyNoDup es = true) :
      skelMatchesEntries (entriesToSkel es) (entriesToTomlList es) = true := by
    rw [EntriesKeyNoDup] at hes; obtain ⟨hnd, hch⟩ := Bool.and_eq_true_iff.mp hes
    have hall1 : ((entriesToTomlList es).all fun p => (assocLookupSkel p.1 (entriesToSkel es)).isSome) = true := by
      apply List.all_eq_true.mpr; rintro ⟨k, _⟩ hm
      have hex : ∃ n, (k, n) ∈ es := by
        clear hes hnd hch; induction es with
        | nil => simp [entriesToTomlList] at hm
        | cons hd tl ih =>
          rcases hd with ⟨kh, nh⟩; simp only [entriesToTomlList, List.mem_cons] at hm
          rcases hm with e | ht
          · obtain ⟨rfl, _⟩ := Prod.mk.inj e; exact ⟨nh, List.mem_cons_self⟩
          · obtain ⟨n, hn⟩ := ih ht; exact ⟨n, List.mem_cons_of_mem _ hn⟩
      obtain ⟨n, hn⟩ := hex
      rw [assocLookupSkel_entriesToSkel, assocLookupNode_of_noDup_mem hnd k n hn]; rfl
    rw [skelMatchesEntries, hall1, Bool.true_and]
    exact skelMatchesAll_aux es es (assocLookupNode_of_noDup_mem hnd) hch
  termination_by sizeOf es * 2 + 1
  decreasing_by simp +arith

  private theorem skelMatchesAll_aux (full : List (String × Node)) :
      (sub : List (String × Node)) →
      (∀ k n, (k, n) ∈ sub → assocLookupNode k full = some n) →
      EntriesChildrenKeyNoDup sub = true →
      skelMatchesEntriesAll (entriesToSkel sub) (entriesToTomlList full) = true
    | [], _, _ => by simp [skelMatchesEntriesAll]
    | (k, n) :: tl, hsub, hch => by
      simp only [EntriesChildrenKeyNoDup, Bool.and_eq_true] at hch
      have hlu : lookupKeyList k (entriesToTomlList full) = some (nodeToTomlValue n) := by
        rw [lookupKeyList_entriesToTomlList, hsub k n List.mem_cons_self]; rfl
      simp only [entriesToSkel, skelMatchesEntriesAll, hlu, Bool.and_eq_true]
      exact ⟨skelNodeMatches_nodeToSkel n hch.1,
        skelMatchesAll_aux full tl (fun k' n' hm => hsub k' n' (List.mem_cons_of_mem _ hm)) hch.2⟩
  termination_by sub => sizeOf sub * 2
  decreasing_by all_goals simp +arith

  private theorem skelMatchesAot_aotToSkel :
      (elems : List (List (String × Node))) → AotKeyNoDup elems = true →
      skelMatchesAot (aotToSkel elems) (aotElemsToToml elems) = true
    | [], _ => by simp [aotElemsToToml, skelMatchesAot]
    | e :: rest, h => by
      simp only [AotKeyNoDup, Bool.and_eq_true] at h
      simp only [aotToSkel, aotElemsToToml, skelMatchesAot, Bool.and_eq_true]
      exact ⟨skelMatchesEntries_entriesToSkel e h.1, skelMatchesAot_aotToSkel rest h.2⟩
  termination_by elems => sizeOf elems * 2
  decreasing_by all_goals simp +arith
end

/-- `insertDottedEntries` extends `entries` and matches `Model.insertDottedAndLookup` on any `finalEntries`. -/
theorem insertDottedEntries_witness (fullPath : List String) (v : TomlValue) :
    ∀ (relPath : List String) (entries nextEntries : List (String × Node)),
      EntriesKeyNoDup entries = true →
      insertDottedEntries fullPath entries relPath (valueToInlineNode v) = .ok nextEntries →
      EntriesKeyNoDup nextEntries = true ∧
      EntriesExtend entries nextEntries ∧
      ∀ finalEntries, EntriesExtend nextEntries finalEntries →
        insertDottedAndLookup (entriesToTomlList finalEntries) (entriesToSkel entries) relPath =
          some (entriesToSkel nextEntries, v)
  | [], _, _, _, h => nomatch h
  | [k], entries, nextEntries, hnd, h => by
    unfold insertDottedEntries at h
    cases hlu : assocLookupNode k entries with
    | none =>
      rw [hlu] at h; injection h with heq; subst heq
      have hvin_nd : NodeKeyNoDup (valueToInlineNode v) = true := by cases v <;> simp [valueToInlineNode, NodeKeyNoDup]
      refine ⟨entriesKeyNoDup_assocSet hnd hvin_nd, entriesExtend_assocSet_none hlu, fun finalEntries hfin => ?_⟩
      have hself : assocLookupNode k (assocSetNode k (valueToInlineNode v) entries) = some (valueToInlineNode v) := by
        simp [assocLookupNode_assocSetNode]
      obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
      rw [nodeExtends_valueToInlineNode hextFin] at hluFin
      cases v <;> simp [insertDottedAndLookup, assocLookupSkel_entriesToSkel, hlu,
        lookupKeyList_entriesToTomlList, hluFin, valueToInlineNode, nodeToTomlValue,
        entriesToTomlList_inlineListToNodes, Array.toArray_toList,
        entriesToSkel_assocSetNode, nodeToSkel]
    | some n =>
      rw [hlu] at h
      cases n with
      | table kind _ => cases kind <;> nomatch h
      | leaf lv => cases lv <;> nomatch h
      | aot _ => nomatch h
  | k :: k' :: rest, entries, nextEntries, hnd, h => by
    unfold insertDottedEntries at h
    cases hlu : assocLookupNode k entries with
    | none =>
      rw [hlu] at h; simp only [bind, Except.bind] at h
      cases hsub : insertDottedEntries fullPath [] (k' :: rest) (valueToInlineNode v) with
      | error _ => rw [hsub] at h; nomatch h
      | ok sub =>
        rw [hsub] at h; injection h with heq; subst heq
        obtain ⟨hsub_nd, _, hsub_lu⟩ := insertDottedEntries_witness fullPath v (k' :: rest) [] sub entriesKeyNoDup_nil hsub
        refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hsub_nd),
          entriesExtend_assocSet_none hlu, fun finalEntries hfin => ?_⟩
        have hself : assocLookupNode k (assocSetNode k (.table .dotted sub) entries) = some (.table .dotted sub) := by
          simp [assocLookupNode_assocSetNode]
        obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
        cases nFin with
        | leaf _ | aot _ => simp [NodeExtends] at hextFin
        | table kFin subFin =>
          simp only [NodeExtends] at hextFin
          have hi := hsub_lu subFin hextFin.2
          simp only [entriesToSkel_nil] at hi
          simp [insertDottedAndLookup, assocLookupSkel_entriesToSkel, hlu, lookupKeyList_entriesToTomlList,
            hluFin, nodeToTomlValue, entriesToSkel_assocSetNode, nodeToSkel, hi]
    | some n =>
      rw [hlu] at h
      cases n with
      | leaf lv => cases lv <;> nomatch h
      | aot _ => nomatch h
      | table kind sub =>
        have hsub_nd0 : EntriesKeyNoDup sub = true := by
          have hn := assocLookupNode_keyNoDup hnd hlu
          cases kind with
          | inline | explicit => nomatch h
          | subtableImplicit | dotted => simpa [NodeKeyNoDup] using hn
        cases kind with
        | inline | explicit => nomatch h
        | subtableImplicit =>
          simp only [bind, Except.bind] at h
          cases hsub : insertDottedEntries fullPath sub (k' :: rest) (valueToInlineNode v) with
          | error _ => rw [hsub] at h; nomatch h
          | ok nextSub =>
            rw [hsub] at h; injection h with heq; subst heq
            obtain ⟨hnsub_nd, hsub_ext, hsub_lu⟩ := insertDottedEntries_witness fullPath v (k' :: rest) sub nextSub hsub_nd0 hsub
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hnsub_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact hsub_ext),
              fun finalEntries hfin => ?_⟩
            have hself : assocLookupNode k (assocSetNode k (.table .dotted nextSub) entries) = some (.table .dotted nextSub) := by
              simp [assocLookupNode_assocSetNode]
            obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
            cases nFin with
            | leaf _ | aot _ => simp [NodeExtends] at hextFin
            | table kFin subFin =>
              simp only [NodeExtends] at hextFin
              have hi := hsub_lu subFin hextFin.2
              simp [insertDottedAndLookup, assocLookupSkel_entriesToSkel, hlu, lookupKeyList_entriesToTomlList,
                hluFin, nodeToTomlValue, entriesToSkel_assocSetNode, nodeToSkel, hi]
        | dotted =>
          simp only [bind, Except.bind] at h
          cases hsub : insertDottedEntries fullPath sub (k' :: rest) (valueToInlineNode v) with
          | error _ => rw [hsub] at h; nomatch h
          | ok nextSub =>
            rw [hsub] at h; injection h with heq; subst heq
            obtain ⟨hnsub_nd, hsub_ext, hsub_lu⟩ := insertDottedEntries_witness fullPath v (k' :: rest) sub nextSub hsub_nd0 hsub
            refine ⟨entriesKeyNoDup_assocSet hnd (by simpa [NodeKeyNoDup] using hnsub_nd),
              entriesExtend_assocSet_some hlu (by simp [NodeExtends]; exact hsub_ext),
              fun finalEntries hfin => ?_⟩
            have hself : assocLookupNode k (assocSetNode k (.table .dotted nextSub) entries) = some (.table .dotted nextSub) := by
              simp [assocLookupNode_assocSetNode]
            obtain ⟨nFin, hluFin, hextFin⟩ := hfin.lookup hself
            cases nFin with
            | leaf _ | aot _ => simp [NodeExtends] at hextFin
            | table kFin subFin =>
              simp only [NodeExtends] at hextFin
              have hi := hsub_lu subFin hextFin.2
              simp [insertDottedAndLookup, assocLookupSkel_entriesToSkel, hlu, lookupKeyList_entriesToTomlList,
                hluFin, nodeToTomlValue, entriesToSkel_assocSetNode, nodeToSkel, hi]

end LeanSwe.Toml.Proofs
